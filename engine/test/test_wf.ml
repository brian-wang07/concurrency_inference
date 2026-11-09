open Engine

(* is_identifier: a letter or _, then letters, digits or _. *)
let () =
  List.iter
    (fun s -> assert (Wf.is_identifier s))
    [ "tail"; "slots"; "N"; "_x"; "t2"; "a_b"; "_"; "x"; "ABC123" ];
  List.iter
    (fun s -> assert (not (Wf.is_identifier s)))
    [ ""; "2t"; "9"; "p.tail"; "a-b"; "a b"; "x!"; "tab\t"; "é" ]

(* reserved: C++ keywords, plus the names Codegen defines itself. *)
let () =
  List.iter
    (fun s -> assert (List.mem s Wf.reserved))
    [ "int"; "for"; "class"; "return"; "while"; "main"; "emod" ];
  List.iter
    (fun s -> assert (not (List.mem s Wf.reserved)))
    [ "tail"; "head"; "slots"; "producer"; "N" ]

(* fail raises Wf_error with the formatted message. *)
let () =
  match Wf.fail "label %s is used %d times" "p.tail_store" 2 with
  | () -> assert false
  | exception Wf.Wf_error msg ->
      assert (msg = "label p.tail_store is used 2 times")

(* check_names, on small programs written as s-expressions. *)
let contains s sub =
  let n = String.length sub in
  let rec go i =
    i + n <= String.length s && (String.sub s i n = sub || go (i + 1))
  in
  go 0

let names_error src =
  match Wf.check_names (Parse.parse_program src) with
  | () -> None
  | exception Wf.Wf_error msg -> Some msg

let rejects_with sub src =
  match names_error src with Some msg -> contains msg sub | None -> false

let accepts src = names_error src = None

(* An atomic needs a writer and a protocol to parse. *)
let atomic name writer =
  Printf.sprintf "(atomic %s 0 (writer %s) (protocol v))" name writer

let () =
  Wf.check_names Ring.ring;
  (* an atomic with no reader is fine *)
  assert (accepts (atomic "flag" "t" ^ "\n(thread t)"))

(* Names share one global scope, across kinds. *)
let () =
  assert (
    rejects_with "array N clashes with param N" "(params (N 2))\n(array N 2)");
  assert (
    rejects_with "thread tail clashes with atomic tail"
      (atomic "tail" "tail" ^ "\n(thread tail)"));
  assert (rejects_with "array a clashes with array a" "(array a 2)\n(array a 3)");
  assert (rejects_with "thread t clashes with thread t" "(thread t)\n(thread t)")

(* Reserved names and identifiers. *)
let () =
  assert (rejects_with "thread main uses a reserved name" "(thread main)");
  assert (rejects_with "array int uses a reserved name" "(array int 2)");
  assert (
    rejects_with "atomic emod uses a reserved name"
      (atomic "emod" "t" ^ "\n(thread t)"));
  assert (
    rejects_with "array p.slots is not a valid C++ identifier"
      "(array p.slots 2)");
  assert (
    rejects_with "param 2x is not a valid C++ identifier" "(params (2x 1))")

(* Writers and readers must be declared threads. *)
let () =
  assert (
    rejects_with "atomic tail has writer prodcer, which is not a thread"
      (atomic "tail" "prodcer" ^ "\n(thread producer)"));
  assert (
    rejects_with "atomic tail has reader nobody"
      "(atomic tail 0 (writer t) (reader nobody) (protocol v))\n(thread t)");
  (* a writer that names an atomic, not a thread *)
  assert (
    rejects_with "atomic a has writer b, which is not a thread"
      (atomic "a" "b" ^ "\n" ^ atomic "b" "t" ^ "\n(thread t)"))

(* labels: every access's label, in order, including inside loops. *)
let () =
  assert (
    Wf.labels Ring.producer.body
    = [ "p.tail_load"; "p.head_await"; "p.tail_store" ]);
  assert (
    Wf.labels Ring.consumer.body
    = [ "c.head_load"; "c.tail_await"; "c.head_store" ]);
  let body =
    match
      (Parse.parse_program
         "(thread t (let x 1) (load a la y) (for i 0 2 (read r s 0) (for j 0 2 \
          (await lw y 1))) (store ls y 1))")
        .threads
    with
    | [ th ] -> th.body
    | _ -> assert false
  in
  assert (Wf.labels body = [ "la"; "lw"; "ls" ]);
  assert (Wf.labels [] = [])

(* check_labels: each label names exactly one access. *)
let labels_error src =
  match Wf.check_labels (Parse.parse_program src) with
  | () -> None
  | exception Wf.Wf_error msg -> Some msg

let () =
  Wf.check_labels Ring.ring;
  (* the same label in two threads *)
  assert (
    labels_error "(thread a (load x l y))\n(thread b (store l y 1))"
    = Some "label l is used in a and in b");
  (* twice in one thread, once inside a loop *)
  assert (
    match labels_error "(thread a (load x l y) (for i 0 2 (await l y 1)))" with
    | Some msg -> contains msg "label l is used"
    | None -> false);
  (* distinct labels on the same atomic are fine *)
  assert (
    labels_error "(thread a (load x l1 y) (store l2 y 1) (await l3 y 1))" = None)

(* constant: no Var anywhere; Param and Int are constant. *)
let () =
  assert (Wf.constant (Ir.Int 3));
  assert (Wf.constant (Ir.Param "N"));
  assert (Wf.constant (Ir.Mod (Ir.Add (Ir.Param "N", Ir.Int 1), Ir.Param "N")));
  assert (not (Wf.constant (Ir.Var "i")));
  assert (not (Wf.constant (Ir.Sub (Ir.Int 1, Ir.Add (Ir.Param "N", Ir.Var "i")))));
  assert (not (Wf.constant (Ir.Mod (Ir.Var "i", Ir.Int 2))))

(* check_loops: constant bounds, no assigning a loop variable, and locals
   that are valid, unreserved and don't hide a global. *)
let loops_error src =
  match Wf.check_loops (Parse.parse_program src) with
  | () -> None
  | exception Wf.Wf_error msg -> Some msg

let loops_rejects_with sub src =
  match loops_error src with Some msg -> contains msg sub | None -> false

let () =
  Wf.check_loops Ring.ring;
  (* bounds from params and ints are fine *)
  assert (
    loops_error "(params (N 2))\n(thread t (for i 0 (+ N 1) (let x i)))" = None)

(* Loop bounds must be constant. *)
let () =
  assert (
    loops_error "(thread t (let x 2) (for i 0 x (let y i)))"
    = Some "upper loop bound x in thread 't' is not a constant");
  assert (
    loops_rejects_with "lower loop bound i + 1 in thread 't'"
      "(thread t (for i 0 2 (for j (+ i 1) 3 (let y j))))");
  (* a Var nested inside the bound *)
  assert (
    loops_rejects_with "upper loop bound N + x"
      "(params (N 2))\n(thread t (let x 1) (for i 0 (+ N x) (let y i)))")

(* No statement assigns an enclosing loop variable. *)
let () =
  assert (
    loops_error "(thread t (for i 0 2 (let i 1)))"
    = Some "thread 't' assigns loop variable i");
  assert (
    loops_rejects_with "assigns loop variable i"
      "(thread t (for i 0 2 (load i l a)))");
  assert (
    loops_rejects_with "assigns loop variable i"
      "(array s 2)\n(thread t (for i 0 2 (read i s 0)))");
  (* from inside a nested loop *)
  assert (
    loops_rejects_with "assigns loop variable i"
      "(thread t (for i 0 2 (for j 0 2 (let i j))))");
  (* the same name in a nested loop *)
  assert (
    loops_rejects_with "loop variable i in thread 't'"
      "(thread t (for i 0 2 (for i 0 2 (let x i))))");
  (* after the loop closes, i is an ordinary local again *)
  assert (loops_error "(thread t (for i 0 2 (let x i)) (let i 3))" = None);
  (* sibling loops can reuse a name *)
  assert (
    loops_error "(thread t (for i 0 2 (let x i)) (for i 0 2 (let y i)))" = None);
  (* the scope is per thread *)
  assert (
    loops_error "(thread a (for i 0 2 (let x i)))\n(thread b (let i 1))" = None)

(* Locals are valid, unreserved, and don't hide a global. *)
let () =
  assert (
    loops_error "(params (N 2))\n(thread t (let N 1))"
    = Some "local N in thread 't' clashes with param N");
  assert (
    loops_rejects_with "clashes with array s"
      "(array s 2)\n(thread t (for s 0 2 (let x 1)))");
  assert (
    loops_rejects_with "clashes with atomic a"
      (atomic "a" "t" ^ "\n(thread t (load a l a))"));
  assert (
    loops_rejects_with "clashes with thread u" "(thread t (let u 1))\n(thread u)");
  assert (loops_rejects_with "int in thread 't'" "(thread t (let int 1))");
  assert (loops_rejects_with "main in thread 't'" "(thread t (for main 0 2))");
  assert (loops_rejects_with "1x in thread 't'" "(thread t (let 1x 1))")

(* check: runs every check, names first. *)
let check_error src =
  match Wf.check (Parse.parse_program src) with
  | () -> None
  | exception Wf.Wf_error msg -> Some msg

let () =
  Wf.check Ring.ring;
  (* each check is reached *)
  assert (
    check_error "(params (N 2))\n(array N 2)"
    = Some "array N clashes with param N");
  assert (
    check_error "(thread a (load x l y))\n(thread b (store l y 1))"
    = Some "label l is used in a and in b");
  assert (
    check_error "(thread t (for i 0 2 (let i 1)))"
    = Some "thread 't' assigns loop variable i");
  (* names before loops: both fail, the names error is reported *)
  assert (
    check_error "(params (N 2))\n(array N 2)\n(thread t (let N 1))"
    = Some "array N clashes with param N");
  (* labels before loops *)
  assert (
    check_error "(thread t (load x l y) (for i 0 2 (store l y 1) (let i 1)))"
    = Some "label l is used in t and in t")
