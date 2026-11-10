(* The engine command: parse a program, check it, infer its orderings, and
   print them or emit C++.

     engine infer FILE
     engine emit FILE [-o OUT] [--pin LABEL=ORD]...

   Exit codes: 0 success, 1 the program was rejected, 2 bad usage. *)
open Engine

let usage =
  "usage: engine infer FILE\n\
  \       engine emit FILE [-o OUT] [--pin LABEL=ORD]..."

exception Usage of string

let usage_error fmt = Printf.ksprintf (fun msg -> raise (Usage msg)) fmt

(* A failure in the program being processed, already formatted for the user. *)
exception Rejected of string

(* Runs every stage up to inference, or rejects the program. *)
let analyse path =
  match Pipeline.run path with Ok r -> r | Error msg -> raise (Rejected msg)

(* " (i=0, j=2)", or "" outside any loop *)
let with_loops loops =
  match loops with
  | [] -> ""
  | _ ->
      Printf.sprintf " (%s)"
        (String.concat ", "
           (List.map (fun (x, k) -> Printf.sprintf "%s=%d" x k) loops))

(* One line per label: its ordering, and why when it is stronger than rlx. *)
let infer path =
  let { Pipeline.reqs; sigma; _ } = analyse path in
  let width =
    List.fold_left (fun w (label, _) -> max w (String.length label)) 0 sigma
  in
  List.iter
    (fun (label, o) ->
      let o = Ord.to_string o in
      match Solve.reason reqs label with
      | None -> Printf.printf "%-*s  %s\n" width label o
      | Some r ->
          Printf.printf "%-*s  %-7s  %s%s\n" width label o r.reason
            (with_loops r.loops))
    sigma

let parse_pin s =
  match String.index_opt s '=' with
  | None -> usage_error "--pin expects LABEL=ORD, got %s" s
  | Some i -> (
      let label = String.sub s 0 i in
      let name = String.sub s (i + 1) (String.length s - i - 1) in
      match Ord.of_string name with
      | Some o -> (label, o)
      | None ->
          usage_error "unknown ordering %s in --pin %s (expected %s)" name s
            (String.concat ", " (List.map Ord.to_string Ord.all)))

(* Writes C++ with the inferred orderings, overridden by any pins. A pin below
   what is required is reported, but the file is still written: emitting
   deliberately weakened programs for GenMC is what pins are for. *)
let emit path out pins =
  let { Pipeline.prog; reqs; sigma } = analyse path in
  let violations =
    match Solve.check (Wf.program_labels prog) reqs pins with
    | v -> v
    | exception Solve.Bad_pin msg -> raise (Rejected (path ^ ": " ^ msg))
  in
  List.iter
    (fun (v : Solve.violation) ->
      Printf.eprintf "warning: %s pinned to %s, but needs at least %s\n" v.label
        (Ord.to_string v.pinned) (Ord.to_string v.needed);
      List.iter
        (fun (r : Check.requirement) ->
          Printf.eprintf "  %s: %s%s\n" (Ord.to_string r.at_least) r.reason
            (with_loops r.loops))
        v.because)
    violations;
  let cpp = Codegen.emit prog (Solve.apply_pins sigma pins) reqs in
  match out with
  | None -> print_string cpp
  | Some file -> (
      match Out_channel.with_open_bin file (fun oc -> output_string oc cpp) with
      | () -> ()
      | exception Sys_error msg -> raise (Rejected msg))

let run argv =
  match Array.to_list argv with
  | _ :: "infer" :: [ path ] -> infer path
  | _ :: "infer" :: _ -> usage_error "infer takes exactly one FILE"
  | _ :: "emit" :: _ ->
      let file = ref None and out = ref None and pins = ref [] in
      let specs =
        [
          ("-o", Arg.String (fun f -> out := Some f), "OUT write C++ to OUT");
          ( "--pin",
            Arg.String (fun s -> pins := parse_pin s :: !pins),
            "LABEL=ORD force LABEL's ordering (repeatable)" );
        ]
      in
      let anon f =
        match !file with
        | None -> file := Some f
        | Some _ -> usage_error "emit takes exactly one FILE"
      in
      (match Arg.parse_argv ~current:(ref 1) argv specs anon usage with
      | () -> ()
      | exception Arg.Bad msg -> raise (Usage (String.trim msg))
      | exception Arg.Help msg ->
          print_string msg;
          exit 0);
      let path =
        match !file with Some f -> f | None -> usage_error "emit needs a FILE"
      in
      emit path !out (List.rev !pins)
  | [ _ ] -> usage_error "missing command"
  | _ :: cmd :: _ -> usage_error "unknown command %s" cmd
  | [] -> usage_error "missing command"

let () =
  match run Sys.argv with
  | () -> ()
  | exception Usage msg ->
      Printf.eprintf "engine: %s\n%s\n" msg usage;
      exit 2
  | exception Rejected msg ->
      Printf.eprintf "%s\n" msg;
      exit 1
