open Engine
open Ring

let req label at_least loops : Check.requirement =
  { label; at_least; loops; reason = "test" }

let reqs = Check.check_program ring
let labels = Wf.program_labels ring
let sigma = Solve.infer labels reqs

(* infer: the hand proof's table, sorted by label. *)
let () =
  assert (
    sigma
    = [
        ("c.head_load", Ord.Rlx);
        ("c.head_store", Ord.Rel);
        ("c.tail_await", Ord.Acq);
        ("p.head_await", Ord.Acq);
        ("p.tail_load", Ord.Rlx);
        ("p.tail_store", Ord.Rel);
      ])

(* infer joins in the lattice: acq and rel on one label give acq_rel. *)
let () =
  assert (Solve.infer [] [] = []);
  assert (Solve.infer [ "a" ] [ req "a" Ord.Rlx [] ] = [ ("a", Ord.Rlx) ]);
  assert (
    Solve.infer [ "a" ]
      [ req "a" Ord.Acq []; req "a" Ord.Rel []; req "a" Ord.Rlx [] ]
    = [ ("a", Ord.AcqRel) ]);
  assert (
    Solve.infer [ "a"; "b" ]
      [ req "b" Ord.Rel []; req "a" Ord.Rlx []; req "b" Ord.Rlx [] ]
    = [ ("a", Ord.Rlx); ("b", Ord.Rel) ])

(* infer: a label with no requirements (an access that never runs) is rlx,
   and every label appears exactly once. *)
let () =
  assert (Solve.infer [ "a" ] [] = [ ("a", Ord.Rlx) ]);
  assert (
    Solve.infer [ "b"; "a"; "c" ] [ req "a" Ord.Acq [] ]
    = [ ("a", Ord.Acq); ("b", Ord.Rlx); ("c", Ord.Rlx) ]);
  assert (Solve.infer [ "a"; "a" ] [ req "a" Ord.Rel [] ] = [ ("a", Ord.Rel) ])

(* The program that found the bug: a store in a loop with no iterations. *)
let () =
  let prog =
    Parse.parse_program
      "(atomic a 0 (writer t) (protocol v))\n(thread t (for i 0 0 (store l a 1)))"
  in
  let reqs = Check.check_program prog in
  let labels = Wf.program_labels prog in
  assert (reqs = []);
  assert (Solve.infer labels reqs = [ ("l", Ord.Rlx) ]);
  (* it can be pinned, and nothing requires more than rlx *)
  assert (Solve.check labels reqs [ ("l", Ord.Rlx) ] = []);
  assert (Solve.check labels reqs [ ("l", Ord.Sc) ] = []);
  (* so codegen has an ordering for it *)
  ignore (Codegen.emit prog (Solve.infer labels reqs) reqs)

(* check: a pin is fine when it is at least what every requirement needs. *)
let () =
  assert (Solve.check labels reqs [] = []);
  assert (Solve.check labels reqs sigma = []);
  assert (Solve.check labels reqs [ ("p.tail_store", Ord.Rel) ] = []);
  assert (Solve.check labels reqs [ ("p.tail_store", Ord.Sc) ] = []);
  assert (Solve.check labels reqs [ ("p.tail_store", Ord.AcqRel) ] = []);
  assert (Solve.check labels reqs [ ("p.tail_load", Ord.Rlx) ] = [])

(* check: too weak a pin is a violation naming what it needs, and why. *)
let () =
  match Solve.check labels reqs [ ("p.tail_store", Ord.Rlx) ] with
  | [ v ] ->
      assert (v.label = "p.tail_store");
      assert (v.pinned = Ord.Rlx);
      assert (v.needed = Ord.Rel);
      (* one unmet requirement per iteration, starting at i = 0 *)
      assert (
        List.map (fun (r : Check.requirement) -> r.loops) v.because
        = [ [ ("i", 0) ]; [ ("i", 1) ]; [ ("i", 2) ] ])
  | _ -> assert false

(* check: acq and rel are incomparable, so rel does not satisfy acq. *)
let () =
  match Solve.check labels reqs [ ("p.head_await", Ord.Rel) ] with
  | [ v ] ->
      assert (v.needed = Ord.Acq);
      (* only i = 2 reuses a slot *)
      assert (
        List.map (fun (r : Check.requirement) -> r.loops) v.because
        = [ [ ("i", 2) ] ])
  | _ -> assert false

(* check: one violation per bad pin, in pin order; good pins add none. *)
let () =
  let vs =
    Solve.check labels reqs
      [
        ("c.tail_await", Ord.Rlx);
        ("p.tail_store", Ord.Rel);
        ("c.head_store", Ord.Acq);
      ]
  in
  assert (
    List.map (fun (v : Solve.violation) -> (v.label, v.needed)) vs
    = [ ("c.tail_await", Ord.Acq); ("c.head_store", Ord.Rel) ])

(* check: a pin naming no access is an error, not silently accepted. *)
let () =
  match Solve.check labels reqs [ ("p.tail_stor", Ord.Rel) ] with
  | _ -> assert false
  | exception Solve.Bad_pin _ -> ()

(* apply_pins: only pinned labels change, and order is kept. *)
let () =
  assert (Solve.apply_pins sigma [] = sigma);
  let weakened = Solve.apply_pins sigma [ ("p.tail_store", Ord.Rlx) ] in
  assert (List.assoc "p.tail_store" weakened = Ord.Rlx);
  assert (
    List.remove_assoc "p.tail_store" weakened
    = List.remove_assoc "p.tail_store" sigma);
  assert (List.map fst weakened = List.map fst sigma);
  let two =
    Solve.apply_pins sigma
      [ ("p.tail_store", Ord.Sc); ("c.head_load", Ord.Acq) ]
  in
  assert (List.assoc "p.tail_store" two = Ord.Sc);
  assert (List.assoc "c.head_load" two = Ord.Acq);
  assert (List.assoc "p.head_await" two = Ord.Acq)

(* check: needed joins every unmet requirement, not just the first. *)
let mixed = [ req "a" Ord.Acq [ ("i", 0) ]; req "a" Ord.Rel [ ("i", 1) ] ]

let () =
  match Solve.check [ "a" ] mixed [ ("a", Ord.Rlx) ] with
  | [ v ] ->
      assert (v.needed = Ord.AcqRel);
      assert (List.length v.because = 2)
  | _ -> assert false

(* a pin of acq meets the first requirement but not the second *)
let () =
  match Solve.check [ "a" ] mixed [ ("a", Ord.Acq) ] with
  | [ v ] ->
      assert (v.needed = Ord.Rel);
      assert (
        List.map (fun (r : Check.requirement) -> r.loops) v.because
        = [ [ ("i", 1) ] ])
  | _ -> assert false

(* reason: the first requirement that forced a label above rlx. *)
let () =
  (match Solve.reason reqs "p.head_await" with
  | Some r ->
      assert (r.at_least = Ord.Acq);
      (* the first iteration that reuses a slot *)
      assert (r.loops = [ ("i", 2) ])
  | None -> assert false);
  (match Solve.reason reqs "p.tail_store" with
  | Some r ->
      assert (r.at_least = Ord.Rel);
      assert (r.loops = [ ("i", 0) ])
  | None -> assert false);
  match Solve.reason reqs "c.tail_await" with
  | Some r -> assert (r.at_least = Ord.Acq && r.loops = [ ("i", 0) ])
  | None -> assert false

(* reason: nothing to explain for rlx labels, or for labels that don't exist. *)
let () =
  assert (Solve.reason reqs "p.tail_load" = None);
  assert (Solve.reason reqs "c.head_load" = None);
  assert (Solve.reason reqs "p.tail_stor" = None)

(* reason: skips rlx requirements and other labels to find the first that
   counts. *)
let () =
  let rs =
    [
      req "a" Ord.Rlx [ ("i", 0) ];
      req "b" Ord.Rel [ ("i", 0) ];
      req "a" Ord.Acq [ ("i", 1) ];
      req "a" Ord.Acq [ ("i", 2) ];
    ]
  in
  match Solve.reason rs "a" with
  | Some r -> assert (r.label = "a" && r.loops = [ ("i", 1) ])
  | None -> assert false

(* The reason text says what each ordering protects. *)
let reason_text label =
  match Solve.reason reqs label with Some r -> r.reason | None -> ""

let () =
  assert (reason_text "p.tail_store" = "publishes slots[0] = 1");
  assert (reason_text "p.head_await" = "gains slots[0]");
  assert (reason_text "c.tail_await" = "gains slots[0] = 1");
  assert (reason_text "c.head_store" = "publishes slots[0]")
