open Engine.Ord

let for_all2 f = List.iter (fun a -> List.iter (fun b -> f a b) all) all
let for_all3 f = List.iter (fun c -> for_all2 (fun a b -> f a b c)) all

(* Lattice laws for join. *)
let () =
  List.iter (fun a -> assert (join a a = a)) all;
  for_all2 (fun a b -> assert (join a b = join b a));
  for_all3 (fun a b c -> assert (join (join a b) c = join a (join b c)))

(* Bottom and top. *)
let () =
  List.iter
    (fun a ->
      assert (leq Rlx a);
      assert (leq a Sc);
      assert (join Rlx a = a);
      assert (join Sc a = Sc))
    all

(* The full leq table, written independently of join: each ordering maps to
   exactly the orderings at least as strong as it. *)
let stronger_or_equal = function
  | Rlx -> [ Rlx; Acq; Rel; AcqRel; Sc ]
  | Acq -> [ Acq; AcqRel; Sc ]
  | Rel -> [ Rel; AcqRel; Sc ]
  | AcqRel -> [ AcqRel; Sc ]
  | Sc -> [ Sc ]

let () =
  for_all2 (fun a b -> assert (leq a b = List.mem b (stronger_or_equal a)))

(* join is the least upper bound: it covers both arguments, and anything else
   that covers both is at least as strong as it. *)
let () =
  for_all2 (fun a b ->
      assert (leq a (join a b));
      assert (leq b (join a b)));
  for_all3 (fun a b c -> if leq a c && leq b c then assert (leq (join a b) c))

(* Acq and Rel are incomparable, which is why this is not a chain. *)
let () =
  assert (not (leq Acq Rel));
  assert (not (leq Rel Acq));
  assert (join Acq Rel = AcqRel);
  assert (join AcqRel Acq = AcqRel);
  assert (not (leq AcqRel Acq))

(* Each name is a separate hand-typed string, so check them directly. *)
let () =
  assert (List.map to_string all = [ "rlx"; "acq"; "rel"; "acq_rel"; "sc" ]);
  assert (
    List.map to_cpp all
    = [
        "std::memory_order_relaxed";
        "std::memory_order_acquire";
        "std::memory_order_release";
        "std::memory_order_acq_rel";
        "std::memory_order_seq_cst";
      ])
