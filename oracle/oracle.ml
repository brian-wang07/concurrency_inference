(* Checks the engine against GenMC. For each program: the inferred orderings
   must give no GenMC errors, and weakening any one ordering by one step must
   give an error. *)
open Engine

type expected = Clean | Broken
type outcome = Ok | Unsound | Imprecise | Timeout | Harness_error of int

let genmc_path =
  match Sys.getenv_opt "GENMC" with Some path -> path | None -> "genmc"

let run_genmc cpp =
  Sys.command
    (Printf.sprintf "timeout 60 %s --disable-estimation %s > %s 2>&1"
       (Filename.quote genmc_path)
       (Filename.quote cpp)
       (Filename.quote (cpp ^ ".out")))

(* genmc exit code 42 means fail: with expected being broken this is fine *)
let classify e code =
  match (e, code) with
  | Clean, 0 | Broken, 42 -> Ok
  | Clean, 42 -> Unsound
  | Broken, 0 -> Imprecise
  | _, 124 -> Timeout
  | _, n -> Harness_error n

let emit (r : Pipeline.t) sigma cpp =
  let text = Codegen.emit r.prog sigma r.reqs in
  Out_channel.with_open_bin cpp (fun oc -> Out_channel.output_string oc text)

let check_file path =
  match Pipeline.run path with
  | Error msg -> [ (msg, Harness_error 0, "") ]
  | Ok r ->
      let baseline =
        let cpp = Filename.temp_file "oracle" ".cpp" in
        emit r r.sigma cpp;
        (path ^ ": inferred", classify Clean (run_genmc cpp), cpp)
      in
      let weakenings =
        List.concat_map
          (fun (label, o) ->
            List.map
              (fun w ->
                let pin = [ (label, w) ] in
                assert (Solve.check (Wf.program_labels r.prog) r.reqs pin <> []);
                let cpp = Filename.temp_file "oracle" ".cpp" in
                emit r (Solve.apply_pins r.sigma pin) cpp;
                let what =
                  Printf.sprintf "%s: %s %s -> %s" path label (Ord.to_string o)
                    (Ord.to_string w)
                in
                (what, classify Broken (run_genmc cpp), cpp))
              (Ord.weaker o))
          r.sigma
      in
      baseline :: weakenings

let outcome_to_string = function
  | Ok -> "ok"
  | Unsound -> "UNSOUND"
  | Imprecise -> "IMPRECISE"
  | Timeout -> "TIMEOUT"
  | Harness_error n -> Printf.sprintf "ERROR %d" n

let () =
  let paths = List.tl (Array.to_list Sys.argv) in
  if paths = [] then (
    prerr_endline "usage: oracle FILE...";
    exit 2);
  let results = List.concat_map check_file paths in
  List.iter
    (fun (what, outcome, cpp) ->
      Printf.printf "%-10s %s\n" (outcome_to_string outcome) what;
      if outcome <> Ok && cpp <> "" then
        Printf.printf "            see %s.out\n" cpp)
    results;
  let failed = List.filter (fun (_, o, _) -> o <> Ok) results in
  Printf.printf "%d runs, %d failed\n" (List.length results)
    (List.length failed);
  exit (if failed = [] then 0 else 1)
