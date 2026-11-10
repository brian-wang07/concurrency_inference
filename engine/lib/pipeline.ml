(* Runs every stage up to inference on one source file: parse, check
   well-formedness, type-check, infer. Shared by the engine command and the
   oracle. *)

type t = {
  prog : Ir.program;
  reqs : Check.requirement list;
  sigma : Solve.sigma;
}

(* Error carries a message for the user that names the file, and the line for
   parse errors. *)
let run path : (t, string) result =
  let error fmt = Printf.ksprintf (fun msg -> Error msg) fmt in
  match
    let prog =
      Parse.parse_program (In_channel.with_open_bin path In_channel.input_all)
    in
    Wf.check prog;
    let reqs = Check.check_program prog in
    { prog; reqs; sigma = Solve.infer (Wf.program_labels prog) reqs }
  with
  | result -> Ok result
  | exception Sys_error msg -> error "%s" msg
  | exception Parse.Parse_error (line, msg) -> error "%s:%d: %s" path line msg
  | exception Wf.Wf_error msg -> error "%s: %s" path msg
  | exception Check.Type_error msg -> error "%s: type error: %s" path msg
