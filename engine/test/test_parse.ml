open Engine

(* The same text as corpus/spsc_ring.sexp. *)
let ring_src =
  {|; SPSC ring: N slots, K items. The producer starts owning every slot; tail
; hands each filled slot to the consumer, and head hands it back.
(params (N 2) (K 3))
(array slots N)

(atomic tail 0 (writer producer) (reader consumer)
  (protocol v (points-to slots (% (- v 1) N) v)))
(atomic head 0 (writer consumer) (reader producer)
  (protocol v (own slots (% (- v 1) N))))

(thread producer (owns slots 0 N)
  (for i 0 K
    (load t p.tail_load tail)
    (await p.head_await head (+ (- t N) 1))
    (write slots (% t N) (+ t 1))
    (store p.tail_store tail (+ t 1))))

(thread consumer
  (for i 0 K
    (load h c.head_load head)
    (await c.tail_await tail (+ h 1))
    (read x slots (% h N))
    (assert x (+ h 1))
    (store c.head_store head (+ h 1))))
|}

(* Round trip: the parsed ring is exactly the hand-built one. *)
let () = assert (Parse.parse_program ring_src = Ring.ring)

(* ...so it checks, infers and generates the same way. *)
let () =
  let prog = Parse.parse_program ring_src in
  let reqs = Check.check_program prog in
  assert (
    Solve.infer (Wf.program_labels prog) reqs
    = Solve.infer (Wf.program_labels Ring.ring) (Check.check_program Ring.ring))

let error src =
  match Parse.parse_program src with
  | _ -> None
  | exception Parse.Parse_error (line, msg) -> Some (line, msg)

let contains s sub =
  let n = String.length sub in
  let rec go i =
    i + n <= String.length s && (String.sub s i n = sub || go (i + 1))
  in
  go 0

let fails_with line sub src =
  match error src with
  | Some (l, m) -> l = line && contains m sub
  | None -> false

(* The reader: parentheses and comments. *)
let () =
  assert (fails_with 1 "unclosed (" "(array slots N");
  assert (fails_with 2 "unclosed (" "(params (N 2))\n(thread t\n  (let x 1)");
  assert (fails_with 1 "unexpected )" "(array slots 2))");
  assert (
    Parse.parse_program "; only a comment\n"
    = { Ir.params = []; arrays = []; atomics = []; threads = [] })

(* Statements: wrong shapes and unknown names, at the right line. *)
let thread_with body =
  "(atomic a 0 (writer t) (protocol v))\n(thread t\n" ^ body ^ ")"

let () =
  assert (
    fails_with 3 "expected (store label atom value)" (thread_with "(store a 1)"));
  assert (
    fails_with 3 "unknown statement frobnicate" (thread_with "(frobnicate x)"));
  assert (
    fails_with 3 "expected (load dst label atom)" (thread_with "(load (x) l a)"));
  assert (
    fails_with 4 "expected a number, a name" (thread_with "(let x\n (* 2 3))"))

(* Declarations. *)
let () =
  assert (fails_with 1 "unknown declaration arrray" "(arrray slots 2)");
  assert (fails_with 1 "needs a writer" "(atomic a 0 (protocol v))");
  assert (fails_with 1 "needs a protocol" "(atomic a 0 (writer t))");
  assert (
    fails_with 1 "has two writer parts"
      "(atomic a 0 (writer t) (writer u) (protocol v))");
  assert (
    fails_with 1 "expected a number, got zero"
      "(atomic a zero (writer t) (protocol v))");
  assert (fails_with 2 "params declared twice" "(params (N 1))\n(params (K 2))");
  assert (fails_with 1 "expected (name value) in params" "(params (N))")

(* Optional and reordered parts. *)
let () =
  let p =
    Parse.parse_program
      "(atomic a 5 (protocol w (own s w)) (writer t))\n\
       (thread t (owns s 0 1) (owns s 2 3))"
  in
  match (p.atomics, p.threads) with
  | [ a ], [ t ] ->
      assert (a.init = 5 && a.writer = "t" && a.reader = None);
      assert (a.protocol.binder = "w");
      assert (t.body = []);
      (* owns ranges keep their order *)
      assert (
        List.map (fun (r : Ir.owned_range) -> r.from_idx) t.owns
        = [ Ir.Int 0; Ir.Int 2 ])
  | _ -> assert false

(* A name is a Param only if it is declared in params. *)
let () =
  let p = Parse.parse_program "(params (N 2))\n(array a N)\n(array b M)" in
  match p.arrays with
  | [ a; b ] -> assert (a.size = Ir.Param "N" && b.size = Ir.Var "M")
  | _ -> assert false
