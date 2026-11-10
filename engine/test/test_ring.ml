open Engine.Ir
open Ring

let () = assert (List.length ring.threads = 2)
let orders prog =
  Engine.Solve.infer
    (Engine.Wf.program_labels prog)
    (Engine.Check.check_program prog)
let with_params n k prog = { prog with params = [ ("N", n); ("K", k) ] }

(* The orderings from the hand proof. *)
let () =
  assert (
    orders ring
    = [
        ("c.head_load", Engine.Ord.Rlx);
        ("c.head_store", Engine.Ord.Rel);
        ("c.tail_await", Engine.Ord.Acq);
        ("p.head_await", Engine.Ord.Acq);
        ("p.tail_load", Engine.Ord.Rlx);
        ("p.tail_store", Engine.Ord.Rel);
      ])

(* With K <= N no slot is reused, so the producer never needs the acquire. *)
let () =
  let o = orders (with_params 2 2 ring) in
  assert (List.assoc "p.head_await" o = Engine.Ord.Rlx);
  assert (List.assoc "c.head_store" o = Engine.Ord.Rel);
  assert (List.assoc "c.tail_await" o = Engine.Ord.Acq)

(* The acquire comes from slot reuse alone: only i = 2 needs it. *)
let () =
  let acq =
    List.filter
      (fun (r : Engine.Check.requirement) ->
        r.label = "p.head_await" && r.at_least = Engine.Ord.Acq)
      (Engine.Check.check_program ring)
  in
  assert (
    List.map (fun (r : Engine.Check.requirement) -> r.loops) acq
    = [ [ ("i", 2) ] ])

(* Other bounds are accepted, and give the same answer once K > N. *)
let () =
  assert (orders (with_params 1 3 ring) = orders ring);
  assert (orders (with_params 3 7 ring) = orders ring)

(* Broken variants: each raises Type_error. *)
let rejects prog =
  match Engine.Check.check_program prog with
  | _ -> false
  | exception Engine.Check.Type_error _ -> true

let replace_body th body =
  match th.body with
  | [ For f ] -> { th with body = [ For { f with body } ] }
  | _ -> assert false

let loop_body th = match th.body with [ For f ] -> f.body | _ -> assert false

let () =
  (* the producer starts with no slots *)
  assert (
    rejects { ring with threads = [ { producer with owns = [] }; consumer ] });
  (* tail promises a different value from the one the producer writes *)
  let off_by_one =
    {
      binder = "v";
      payload =
        [
          PointsTo
            {
              arr = "slots";
              idx = Mod (Sub (v "v", i 1), p "N");
              value = Add (v "v", i 1);
            };
        ];
    }
  in
  assert (
    rejects
      {
        ring with
        atomics =
          List.map
            (fun d ->
              if d.atom_name = "tail" then { d with protocol = off_by_one }
              else d)
            ring.atomics;
      });
  (* the consumer reads the slot before awaiting it *)
  let no_await =
    List.filter (function Await _ -> false | _ -> true) (loop_body consumer)
  in
  assert (
    rejects { ring with threads = [ producer; replace_body consumer no_await ] });
  (* the producer waits for too little space, so it reuses a slot it gave away *)
  let early =
    List.map
      (function
        | Await a -> Await { a with bound = Sub (v "t", p "N") } | s -> s)
      (loop_body producer)
  in
  assert (
    rejects { ring with threads = [ replace_body producer early; consumer ] });
  (* the consumer asserts the wrong value *)
  let wrong_assert =
    List.map
      (function Assert a -> Assert { a with rhs = Add (v "h", i 2) } | s -> s)
      (loop_body consumer)
  in
  assert (
    rejects
      { ring with threads = [ producer; replace_body consumer wrong_assert ] })

(* Declaration checks: rejected for the stated reason, before any thread runs. *)
let contains s sub =
  let n = String.length sub in
  let rec go i =
    i + n <= String.length s && (String.sub s i n = sub || go (i + 1))
  in
  go 0

let rejects_with reason prog =
  match Engine.Check.check_program prog with
  | _ -> false
  | exception Engine.Check.Type_error m -> contains m reason

let owns_slots lo hi = [ { owned_arr = "slots"; from_idx = lo; to_idx = hi } ]

let () =
  (* the consumer also starts with every slot *)
  assert (
    rejects_with "initially owned by both producer and consumer"
      {
        ring with
        threads = [ producer; { consumer with owns = producer.owns } ];
      });
  (* one shared cell is enough *)
  assert (
    rejects_with "slots[1] is initially owned by both"
      {
        ring with
        threads = [ producer; { consumer with owns = owns_slots (i 1) (i 2) } ];
      });
  (* adjacent ranges don't overlap, since ranges are half-open *)
  Engine.Check.check_disjoint_ownership
    {
      ring with
      threads =
        [
          { producer with owns = owns_slots (i 0) (i 1) };
          { consumer with owns = owns_slots (i 1) (i 2) };
        ];
    }

let () =
  assert (
    rejects_with "thread producer is declared twice"
      {
        ring with
        threads = [ producer; { consumer with thread_name = "producer" } ];
      });
  assert (
    rejects_with "atomic tail is declared twice"
      { ring with atomics = ring.atomics @ [ List.hd ring.atomics ] });
  assert (
    rejects_with "array slots is declared twice"
      { ring with arrays = ring.arrays @ ring.arrays })

(* Owned ranges must lie inside a declared array. *)
let () =
  assert (
    rejects
      {
        ring with
        threads = [ { producer with owns = owns_slots (i 0) (i 5) }; consumer ];
      });
  assert (
    rejects
      {
        ring with
        threads =
          [ { producer with owns = owns_slots (i (-1)) (p "N") }; consumer ];
      });
  assert (
    rejects
      {
        ring with
        threads =
          [
            {
              producer with
              owns =
                [ { owned_arr = "sloots"; from_idx = i 0; to_idx = p "N" } ];
            };
            consumer;
          ];
      })

(* test.c as a program: the producer publishes slots[0] |-> 1 at tail = 1,
   then stores 1 again. The consumer may read the second store, so under
   C++20 release sequences both stores need rel. *)
let () =
  let redundant =
    {
      thread_name = "producer";
      owns = owns_slots (i 0) (p "N");
      body =
        [
          NaWrite { arr = "slots"; idx = i 0; value = i 1 };
          Store { acc = { label = "first"; atom = "tail" }; value = i 1 };
          Store { acc = { label = "again"; atom = "tail" }; value = i 1 };
        ];
    }
  in
  let reader =
    {
      thread_name = "consumer";
      owns = [];
      body =
        [
          Await { acc = { label = "wait"; atom = "tail" }; bound = i 1 };
          NaRead { dst = "x"; arr = "slots"; idx = i 0 };
          Assert { lhs = v "x"; rhs = i 1 };
        ];
    }
  in
  let o = orders { ring with threads = [ redundant; reader ] } in
  assert (List.assoc "first" o = Engine.Ord.Rel);
  assert (List.assoc "again" o = Engine.Ord.Rel);
  (* the redundant store's reason names the atomic and value it re-stores *)
  let again =
    List.find
      (fun (r : Engine.Check.requirement) ->
        r.label = "again" && r.at_least = Engine.Ord.Rel)
      (Engine.Check.check_program { ring with threads = [ redundant; reader ] })
  in
  assert (again.reason = "a reader of tail = 1 may gain an earlier payload");
  assert (List.assoc "wait" o = Engine.Ord.Acq)
