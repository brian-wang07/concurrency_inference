open Engine.Ir
open Engine.Check

let prog =
  { params = [ ("N", 2); ("K", 3) ]; arrays = []; atomics = []; threads = [] }

let env = StringMap.(empty |> add "t" (Known 5) |> add "u" Unknown)
let ev e = eval prog env e

(* True if running f raises Type_error. *)
let raises_type_error f =
  match f () with _ -> false | exception Type_error _ -> true

let () =
  assert (ev (Int 7) = Known 7);
  assert (ev (Int (-3)) = Known (-3));
  assert (ev (Param "N") = Known 2);
  assert (ev (Var "t") = Known 5);
  assert (ev (Var "u") = Unknown)

(* Arithmetic, including the ring's expressions. *)
let () =
  assert (ev (Add (Int 2, Int 3)) = Known 5);
  assert (ev (Sub (Int 2, Int 3)) = Known (-1));
  assert (ev (Sub (Int 3, Int 2)) = Known 1);
  (* t - N + 1 = 5 - 2 + 1 *)
  assert (ev (Add (Sub (Var "t", Param "N"), Int 1)) = Known 4);
  (* t % N = 5 mod 2 *)
  assert (ev (Mod (Var "t", Param "N")) = Known 1)

(* Mod is Euclidean: never negative, unlike OCaml's mod. *)
let () =
  assert (ev (Mod (Int 4, Int 2)) = Known 0);
  assert (ev (Mod (Int (-1), Int 2)) = Known 1);
  assert (ev (Mod (Int (-2), Int 2)) = Known 0);
  assert (ev (Mod (Int (-3), Int 2)) = Known 1);
  (* the producer's first await bound: (0 - 2 + 1) % 2 *)
  assert (ev (Mod (Add (Sub (Int 0, Param "N"), Int 1), Param "N")) = Known 1)

(* Unknown spreads through every operator, on either side. *)
let () =
  List.iter
    (fun e -> assert (ev e = Unknown))
    [
      Add (Var "u", Int 1);
      Add (Int 1, Var "u");
      Sub (Var "u", Int 1);
      Sub (Int 1, Var "u");
      Mod (Var "u", Int 2);
      Mod (Int 2, Var "u");
      Add (Sub (Var "u", Param "N"), Int 1);
    ]

(* Errors. *)
let () =
  assert (raises_type_error (fun () -> ev (Param "M")));
  assert (raises_type_error (fun () -> ev (Var "missing")));
  assert (raises_type_error (fun () -> ev (Mod (Int 1, Int 0))));
  assert (raises_type_error (fun () -> ev (Mod (Int 1, Int (-2)))))

(* eval_known returns a plain int, and rejects Unknown. *)
let () =
  assert (eval_known prog env (Add (Var "t", Int 1)) = 6);
  assert (raises_type_error (fun () -> eval_known prog env (Var "u")))

(* The ring's protocols, with N = 2 from prog. *)
let slot_of_v = Mod (Sub (Var "v", Int 1), Param "N")

let head_protocol =
  { binder = "v"; payload = [ Own { arr = "slots"; idx = slot_of_v } ] }

let tail_protocol =
  {
    binder = "v";
    payload = [ PointsTo { arr = "slots"; idx = slot_of_v; value = Var "v" } ];
  }

(* Two resources, a binder other than v, and a param in a value. *)
let two_protocol =
  {
    binder = "w";
    payload =
      [
        Own { arr = "a"; idx = Var "w" };
        PointsTo { arr = "b"; idx = Int 0; value = Add (Var "w", Param "K") };
      ];
  }

(* instantiate *)
let () =
  assert (instantiate prog head_protocol 1 = [ (("slots", 0), Unknown) ]);
  assert (instantiate prog head_protocol 2 = [ (("slots", 1), Unknown) ]);
  assert (instantiate prog head_protocol 3 = [ (("slots", 0), Unknown) ]);
  assert (instantiate prog tail_protocol 1 = [ (("slots", 0), Known 1) ]);
  assert (instantiate prog tail_protocol 3 = [ (("slots", 0), Known 3) ]);
  assert (
    instantiate prog two_protocol 4
    = [ (("a", 4), Unknown); (("b", 0), Known 7) ]);
  assert (instantiate prog { binder = "v"; payload = [] } 1 = [])

(* A payload sees only its binder and the params, never a thread's variables. *)
let () =
  let uses_t =
    { binder = "v"; payload = [ Own { arr = "a"; idx = Var "t" } ] }
  in
  assert (raises_type_error (fun () -> instantiate prog uses_t 1))

(* delta covers values from + 1 through to_, in order. *)
let () =
  assert (
    delta prog tail_protocol 0 3
    = [
        (("slots", 0), Known 1); (("slots", 1), Known 2); (("slots", 0), Known 3);
      ]);
  (* the same cell twice: delta reports it, and Await decides it is an error *)
  assert (
    delta prog head_protocol 0 3
    = [
        (("slots", 0), Unknown); (("slots", 1), Unknown); (("slots", 0), Unknown);
      ]);
  assert (delta prog head_protocol 1 2 = [ (("slots", 1), Unknown) ]);
  assert (
    delta prog two_protocol 0 2
    = [
        (("a", 1), Unknown);
        (("b", 0), Known 4);
        (("a", 2), Unknown);
        (("b", 0), Known 5);
      ])

(* No new values gives nothing, including when to_ is below from. *)
let () =
  assert (delta prog head_protocol 2 2 = []);
  assert (delta prog head_protocol 3 1 = [])

(* check_stmt on single atomic statements, with hand-built contexts. *)
let slots_n = [ { arr_name = "slots"; size = Param "N" } ]

let tail_decl =
  {
    atom_name = "tail";
    init = 0;
    writer = "p";
    reader = Some "c";
    protocol = tail_protocol;
  }

let head_decl =
  {
    atom_name = "head";
    init = 0;
    writer = "c";
    reader = Some "p";
    protocol = head_protocol;
  }

let ring_like =
  { prog with arrays = slots_n; atomics = [ tail_decl; head_decl ] }

let ctx_with ?(cells = []) ?(env = []) roles =
  {
    cells = CellMap.of_seq (List.to_seq cells);
    roles = StringMap.of_seq (List.to_seq roles);
    env = StringMap.of_seq (List.to_seq env);
    loops = [];
    reqs = [];
  }

let step ctx s = check_stmt ring_like ctx s

let last_req ctx =
  match ctx.reqs with r :: _ -> r.at_least | [] -> assert false

let tail_acc = { label = "p.tail_store"; atom = "tail" }
let head_acc = { label = "p.head_await"; atom = "head" }

(* Load: a writer knows its own value; anyone else does not. *)
let () =
  let load =
    Load { dst = "t"; acc = { label = "p.tail_load"; atom = "tail" } }
  in
  let c = step (ctx_with [ ("tail", Writer { current = 4 }) ]) load in
  assert (StringMap.find "t" c.env = Known 4);
  assert (last_req c = Engine.Ord.Rlx);
  let c = step (ctx_with [ ("tail", Reader { claimed = 0 }) ]) load in
  assert (StringMap.find "t" c.env = Unknown)

(* Store: publishing gives up the cell and needs release. *)
let () =
  let c =
    step
      (ctx_with
         ~cells:[ (("slots", 0), Known 1) ]
         [ ("tail", Writer { current = 0 }) ])
      (Store { acc = tail_acc; value = Int 1 })
  in
  assert (CellMap.is_empty c.cells);
  assert (StringMap.find "tail" c.roles = Writer { current = 1 });
  assert (last_req c = Engine.Ord.Rel);
  (* storing the same value transfers nothing *)
  let c =
    step
      (ctx_with [ ("tail", Writer { current = 1 }) ])
      (Store { acc = tail_acc; value = Int 1 })
  in
  assert (last_req c = Engine.Ord.Rlx)

let () =
  let store_from cells role v =
   fun () ->
    step
      (ctx_with ~cells [ ("tail", role) ])
      (Store { acc = tail_acc; value = Int v })
  in
  let w0 = Writer { current = 0 } in
  assert (raises_type_error (store_from [] w0 1));
  assert (raises_type_error (store_from [ (("slots", 0), Known 2) ] w0 1));
  assert (raises_type_error (store_from [ (("slots", 0), Unknown) ] w0 1));
  assert (raises_type_error (store_from [] (Writer { current = 3 }) 1));
  assert (raises_type_error (store_from [] (Reader { claimed = 0 }) 1))

(* Await: a reader gains what the protocol publishes, and claims up to the bound. *)
let () =
  let await b ctx = step ctx (Await { acc = head_acc; bound = Int b }) in
  let r0 = ctx_with [ ("head", Reader { claimed = 0 }) ] in
  let c = await 2 r0 in
  assert (
    CellMap.bindings c.cells
    = [ (("slots", 0), Unknown); (("slots", 1), Unknown) ]);
  assert (StringMap.find "head" c.roles = Reader { claimed = 2 });
  assert (last_req c = Engine.Ord.Acq);
  (* nothing new below or at the claimed value *)
  let c = await (-1) r0 in
  assert (CellMap.is_empty c.cells && last_req c = Engine.Ord.Rlx);
  let c = await 2 (await 2 r0) in
  assert (last_req c = Engine.Ord.Rlx);
  (* PointsTo payloads carry their value *)
  let c =
    step
      (ctx_with [ ("tail", Reader { claimed = 0 }) ])
      (Await { acc = { label = "c.tail_await"; atom = "tail" }; bound = Int 1 })
  in
  assert (CellMap.find ("slots", 0) c.cells = Known 1);
  (* a bystander gains nothing *)
  let c = await 1 (ctx_with [ ("head", Bystander) ]) in
  assert (CellMap.is_empty c.cells && last_req c = Engine.Ord.Rlx)

let () =
  let await_from cells role b =
   fun () ->
    step
      (ctx_with ~cells [ ("head", role) ])
      (Await { acc = head_acc; bound = Int b })
  in
  (* gaining a cell twice: already owned, or twice in one delta *)
  assert (
    raises_type_error
      (await_from [ (("slots", 0), Unknown) ] (Reader { claimed = 0 }) 1));
  assert (raises_type_error (await_from [] (Reader { claimed = 0 }) 3));
  assert (raises_type_error (await_from [] (Writer { current = 0 }) 1))

(* For: runs the body once per iteration, records the iteration, then restores env. *)
let () =
  let body =
    [ Load { dst = "t"; acc = { label = "p.tail_load"; atom = "tail" } } ]
  in
  let c =
    step
      (ctx_with ~env:[ ("x", Known 9) ] [ ("tail", Writer { current = 0 }) ])
      (For { var = "i"; lo = Int 0; hi = Param "K"; body })
  in
  assert (List.length c.reqs = 3);
  assert (
    List.rev_map (fun (r : requirement) -> r.loops) c.reqs
    = [ [ ("i", 0) ]; [ ("i", 1) ]; [ ("i", 2) ] ]);
  assert (StringMap.bindings c.env = [ ("x", Known 9) ]);
  assert (c.loops = [])

(* initial: owned ranges become cells, and every atomic gets a role. *)
let () =
  let th =
    {
      thread_name = "p";
      owns = [ { owned_arr = "slots"; from_idx = Int 0; to_idx = Param "N" } ];
      body = [];
    }
  in
  let c = initial ring_like th in
  assert (
    CellMap.bindings c.cells
    = [ (("slots", 0), Unknown); (("slots", 1), Unknown) ]);
  assert (StringMap.find "tail" c.roles = Writer { current = 0 });
  assert (StringMap.find "head" c.roles = Reader { claimed = 0 });
  let c = initial ring_like { th with thread_name = "q"; owns = [] } in
  assert (CellMap.is_empty c.cells);
  assert (StringMap.find "tail" c.roles = Bystander)

(* An atomic with an empty payload carries nothing, so awaiting it needs only
   rlx even when the bound is new. *)
let () =
  let flag_decl =
    {
      atom_name = "flag";
      init = 0;
      writer = "p";
      reader = Some "c";
      protocol = { binder = "v"; payload = [] };
    }
  in
  let c =
    check_stmt
      { ring_like with atomics = [ flag_decl ] }
      (ctx_with [ ("flag", Reader { claimed = 0 }) ])
      (Await { acc = { label = "c.flag_await"; atom = "flag" }; bound = Int 3 })
  in
  assert (last_req c = Engine.Ord.Rlx);
  assert (StringMap.find "flag" c.roles = Reader { claimed = 3 })

(* check_thread returns requirements in program order. *)
let () =
  let th =
    {
      thread_name = "p";
      owns = [ { owned_arr = "slots"; from_idx = Int 0; to_idx = Param "N" } ];
      body =
        [
          Load { dst = "t"; acc = { label = "first"; atom = "tail" } };
          NaWrite { arr = "slots"; idx = Int 0; value = Int 1 };
          Store { acc = { label = "second"; atom = "tail" }; value = Int 1 };
          Await { acc = { label = "third"; atom = "head" }; bound = Int 1 };
        ];
    }
  in
  assert (
    List.map (fun (r : requirement) -> r.label) (check_thread ring_like th)
    = [ "first"; "second"; "third" ])
