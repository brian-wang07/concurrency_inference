open Engine
open Engine.Ir
open Ring

let contains s sub =
  let n = String.length sub in
  let rec go i =
    i + n <= String.length s && (String.sub s i n = sub || go (i + 1))
  in
  go 0

let reqs = Check.check_program ring
let sigma = Solve.infer (Wf.program_labels ring) reqs
let generate pins = Codegen.emit ring (Solve.apply_pins sigma pins) reqs

(* Run with --print [label] to write the generated C++ to stdout, with label
   weakened to rlx if given:
     dune exec engine/test/test_codegen.exe -- --print > ring.cpp
     dune exec engine/test/test_codegen.exe -- --print p.tail_store > w.cpp *)
let () =
  match Sys.argv with
  | [| _; "--print" |] -> print_string (generate [])
  | [| _; "--print"; label |] -> print_string (generate [ (label, Ord.Rlx) ])
  | _ -> ()

(* expr_to_cpp: Mod becomes emod, and operands keep their grouping. *)
let () =
  let cpp = Codegen.expr_to_cpp in
  assert (cpp (Int 3) = "3");
  assert (cpp (Param "N") = "N");
  assert (cpp (Mod (Var "t", Param "N")) = "emod(t, N)");
  assert (cpp (Mod (Sub (Var "v", Int 1), Param "N")) = "emod(v - 1, N)");
  assert (cpp (Add (Sub (Var "t", Param "N"), Int 1)) = "(t - N) + 1");
  assert (cpp (Sub (Var "t", Add (Param "N", Int 1))) = "t - (N + 1)");
  assert (cpp (Add (Mod (Var "t", Param "N"), Int 1)) = "emod(t, N) + 1");
  assert (cpp (Sub (Var "t", Int (-1))) = "t - (-1)");
  assert (cpp (Mod (Mod (Var "a", Int 3), Int 2)) = "emod(emod(a, 3), 2)")

(* locals: every assigned variable, once, including inside loops. *)
let () =
  assert (Codegen.locals producer.body = [ "t" ]);
  assert (Codegen.locals consumer.body = [ "h"; "x" ]);
  let nested =
    [
      Let { dst = "b"; value = Int 0 };
      For
        {
          var = "i";
          lo = Int 0;
          hi = Int 2;
          body =
            [
              Let { dst = "b"; value = Int 1 };
              For
                {
                  var = "j";
                  lo = Int 0;
                  hi = Int 2;
                  body = [ NaRead { dst = "a"; arr = "slots"; idx = Int 0 } ];
                };
            ];
        };
      NaWrite { arr = "slots"; idx = Int 0; value = Int 1 };
    ]
  in
  assert (Codegen.locals nested = [ "a"; "b" ])

(* emit: the ring's declarations, accesses and threads. *)
let out = generate []

let () =
  List.iter
    (fun s -> assert (contains out s))
    [
      "#include <atomic>";
      "#include <cassert>";
      "#include <pthread.h>";
      "constexpr int N = 2;";
      "constexpr int K = 3;";
      "int slots[N];";
      "std::atomic<int> tail{0};";
      "std::atomic<int> head{0};";
      "static int emod(int a, int b) {";
      (* every access, with its inferred ordering *)
      "t = tail.load(std::memory_order_relaxed);";
      "while (head.load(std::memory_order_acquire) < (t - N) + 1) {}";
      "slots[emod(t, N)] = t + 1;";
      "tail.store(t + 1, std::memory_order_release);";
      "h = head.load(std::memory_order_relaxed);";
      "while (tail.load(std::memory_order_acquire) < h + 1) {}";
      "x = slots[emod(h, N)];";
      "assert(x == h + 1);";
      "head.store(h + 1, std::memory_order_release);";
      (* each thread *)
      "void *producer(void *) {\n  int t = 0;";
      "void *consumer(void *) {\n  int h = 0;\n  int x = 0;";
      "  return nullptr;\n}";
      "pthread_create(&threads[0], nullptr, producer, nullptr);";
      "pthread_create(&threads[1], nullptr, consumer, nullptr);";
      "pthread_join(threads[k], nullptr);";
    ]

(* Comments carry each access's label, ordering and reason. *)
let () =
  assert (contains out "// p.tail_load: rlx\n");
  assert (contains out "// p.head_await: acq, gains slots[0] (i=2)");
  assert (contains out "// p.tail_store: rel, publishes slots[0] = 1 (i=0)");
  assert (contains out "// c.tail_await: acq, gains slots[0] = 1 (i=0)")

(* Braces balance, and both threads return. *)
let () =
  let count c =
    String.fold_left (fun n x -> if x = c then n + 1 else n) 0 out
  in
  assert (count '{' = count '}');
  let returns =
    List.length
      (String.split_on_char '\n' out |> List.filter (( = ) "  return nullptr;"))
  in
  assert (returns = 2)

(* A pin changes exactly that access's memory order. *)
let () =
  let weak = generate [ ("p.tail_store", Ord.Rlx) ] in
  assert (contains weak "tail.store(t + 1, std::memory_order_relaxed);");
  assert (not (contains weak "tail.store(t + 1, std::memory_order_release);"));
  (* the consumer's store is untouched *)
  assert (contains weak "head.store(h + 1, std::memory_order_release);")

(* If g++ is installed, the generated code must compile cleanly. *)
let () =
  if Sys.command "command -v g++ > /dev/null 2>&1" = 0 then begin
    let file = Filename.temp_file "ring" ".cpp" in
    let oc = open_out file in
    output_string oc out;
    close_out oc;
    let cmd =
      Printf.sprintf
        "g++ -std=c++17 -Wall -Wextra -Werror -pthread -fsyntax-only %s"
        (Filename.quote file)
    in
    let status = Sys.command cmd in
    Sys.remove file;
    assert (status = 0)
  end

(* Loops: a half-open bound, and the body one level deeper than the header. *)
let () =
  assert (contains out "\n  for (int i = 0; i < K; ++i) {\n    t = tail.load(");
  assert (contains out "\n  for (int i = 0; i < K; ++i) {\n    h = head.load(")

(* An atomic's initial value is carried over. *)
let () =
  let started =
    { ring with atomics = List.map (fun d -> { d with init = 7 }) ring.atomics }
  in
  let s = Codegen.emit started sigma reqs in
  assert (contains s "std::atomic<int> tail{7};");
  assert (contains s "std::atomic<int> head{7};")
