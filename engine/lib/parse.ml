(* s-expression parser *)

(* int is line number *)
type sexp = Atom of string * int | List of sexp list * int

exception Parse_error of int * string

type token = LParen | RParen | Atom_tok of string

let is_delimiter c =
  match c with ' ' | '\t' | '\r' | '\n' | '(' | ')' | ';' -> true | _ -> false

let lex src =
  let n = String.length src in
  let rec skip_comment i =
    if i < n && src.[i] <> '\n' then skip_comment (i + 1) else i
  in
  let rec atom_end i =
    if i < n && not (is_delimiter src.[i]) then atom_end (i + 1) else i
  in
  let rec go i line acc =
    if i >= n then List.rev acc
    else
      match src.[i] with
      | '\n' -> go (i + 1) (line + 1) acc
      | ' ' | '\t' | '\r' -> go (i + 1) line acc
      | ';' -> go (skip_comment i) line acc
      | '(' -> go (i + 1) line ((LParen, line) :: acc)
      | ')' -> go (i + 1) line ((RParen, line) :: acc)
      | _ ->
          let j = atom_end i in
          go j line ((Atom_tok (String.sub src i (j - i)), line) :: acc)
  in
  go 0 1 []

let rec parse_one tokens =
  match tokens with
  | (Atom_tok s, line) :: rest -> (Atom (s, line), rest)
  | (LParen, line) :: rest ->
      let items, rest = parse_items line rest in
      (List (items, line), rest)
  | (RParen, line) :: _ -> raise (Parse_error (line, "unexpected )"))
  | [] -> raise (Parse_error (0, "unexpected EOF"))

and parse_items open_line tokens =
  match tokens with
  | (RParen, _) :: rest -> ([], rest)
  | [] -> raise (Parse_error (open_line, "unclosed ("))
  | _ ->
      let item, rest = parse_one tokens in
      let items, rest = parse_items open_line rest in
      (item :: items, rest)

let read src =
  let rec forms tokens =
    match tokens with
    | [] -> []
    | _ ->
        let form, rest = parse_one tokens in
        form :: forms rest
  in
  forms (lex src)

let rec expr params s =
  match s with
  | Atom (a, _) -> (
      match int_of_string_opt a with
      | Some n -> Ir.Int n
      | None -> if List.mem a params then Ir.Param a else Ir.Var a)
  | List ([ Atom ("+", _); a; b ], _) -> Ir.Add (expr params a, expr params b)
  | List ([ Atom ("-", _); a; b ], _) -> Ir.Sub (expr params a, expr params b)
  | List ([ Atom ("%", _); a; b ], _) -> Ir.Mod (expr params a, expr params b)
  | List (_, line) ->
      raise
        (Parse_error
           ( line,
             "expected a number, a name, or one of: (+ a b), (- a b), (% a b)"
           ))

let stmt_usage name =
  match name with
  | "load" -> Some "(load dst label atom)"
  | "store" -> Some "(store label atom value)"
  | "await" -> Some "(await label atom bound)"
  | "read" -> Some "(read dst arr idx)"
  | "write" -> Some "(write arr idx value)"
  | "let" -> Some "(let dst value)"
  | "assert" -> Some "(assert lhs rhs)"
  | "for" -> Some "(for var lo hi stmt ...)"
  | _ -> None

let rec stmt params s =
  let e = expr params in
  match s with
  | List
      ([ Atom ("load", _); Atom (dst, _); Atom (label, _); Atom (atom, _) ], _)
    ->
      Ir.Load { dst; acc = { label; atom } }
  | List ([ Atom ("store", _); Atom (label, _); Atom (atom, _); value ], _) ->
      Ir.Store { acc = { label; atom }; value = e value }
  | List ([ Atom ("await", _); Atom (label, _); Atom (atom, _); bound ], _) ->
      Ir.Await { acc = { label; atom }; bound = e bound }
  | List ([ Atom ("read", _); Atom (dst, _); Atom (arr, _); idx ], _) ->
      Ir.NaRead { dst; arr; idx = e idx }
  | List ([ Atom ("write", _); Atom (arr, _); idx; value ], _) ->
      Ir.NaWrite { arr; idx = e idx; value = e value }
  | List ([ Atom ("let", _); Atom (dst, _); value ], _) ->
      Ir.Let { dst; value = e value }
  | List ([ Atom ("assert", _); lhs; rhs ], _) ->
      Ir.Assert { lhs = e lhs; rhs = e rhs }
  | List (Atom ("for", _) :: Atom (var, _) :: lo :: hi :: body, _) ->
      Ir.For { var; lo = e lo; hi = e hi; body = List.map (stmt params) body }
  | List (Atom (name, _) :: _, line) -> (
      match stmt_usage name with
      | Some usage -> raise (Parse_error (line, "expected " ^ usage))
      | None -> raise (Parse_error (line, "unknown statement " ^ name)))
  | Atom (_, line) | List (_, line) ->
      raise (Parse_error (line, "expected a statement"))

let line_of s = match s with Atom (_, line) | List (_, line) -> line
let fail s msg = raise (Parse_error (line_of s, msg))

let int_atom s =
  match s with
  | Atom (a, _) -> (
      match int_of_string_opt a with
      | Some n -> n
      | None -> fail s ("expected a number, got " ^ a))
  | List _ -> fail s "expected a number"

let name_atom what s =
  match s with Atom (a, _) -> a | List _ -> fail s ("expected " ^ what)

(* (own arr idx) or (points-to arr idx value) *)
let res params s =
  let e = expr params in
  match s with
  | List ([ Atom ("own", _); Atom (arr, _); idx ], _) ->
      Ir.Own { arr; idx = e idx }
  | List ([ Atom ("points-to", _); Atom (arr, _); idx; value ], _) ->
      Ir.PointsTo { arr; idx = e idx; value = e value }
  | _ -> fail s "expected (own arr idx) or (points-to arr idx value)"

(* (protocol binder res ...) *)
let protocol params s =
  match s with
  | List (Atom ("protocol", _) :: Atom (binder, _) :: payload, _) ->
      { Ir.binder; payload = List.map (res params) payload }
  | _ -> fail s "expected (protocol binder res ...)"

(* (params (N 2) (K 3)) *)
let params_form s =
  match s with
  | List (Atom ("params", _) :: entries, _) ->
      List.map
        (fun entry ->
          match entry with
          | List ([ Atom (name, _); value ], _) -> (name, int_atom value)
          | _ -> fail entry "expected (name value) in params")
        entries
  | _ -> fail s "expected (params (name value) ...)"

(* (array name size) *)
let array_decl params s =
  match s with
  | List ([ Atom ("array", _); Atom (arr_name, _); size ], _) ->
      { Ir.arr_name; size = expr params size }
  | _ -> fail s "expected (array name size)"

let atomic_decl params s =
  match s with
  | List (Atom ("atomic", _) :: Atom (atom_name, _) :: init :: parts, _) ->
      let init = int_atom init in
      let writer = ref None and reader = ref None and proto = ref None in
      let set slot what part value =
        match !slot with
        | Some _ ->
            fail part
              (Printf.sprintf "atomic %s has two %s parts" atom_name what)
        | None -> slot := Some value
      in
      List.iter
        (fun part ->
          match part with
          | List ([ Atom ("writer", _); t ], _) ->
              set writer "writer" part (name_atom "a thread name" t)
          | List ([ Atom ("reader", _); t ], _) ->
              set reader "reader" part (name_atom "a thread name" t)
          | List (Atom ("protocol", _) :: _, _) ->
              set proto "protocol" part (protocol params part)
          | _ -> fail part "expected (writer t), (reader t) or (protocol ...)")
        parts;
      let required what slot =
        match !slot with
        | Some v -> v
        | None -> fail s (Printf.sprintf "atomic %s needs a %s" atom_name what)
      in
      {
        Ir.atom_name;
        init;
        writer = required "writer" writer;
        reader = !reader;
        protocol = required "protocol" proto;
      }
  | _ -> fail s "expected (atomic name init (writer t) (protocol ...))"

let owned_range params s =
  match s with
  | List ([ Atom ("owns", _); Atom (owned_arr, _); lo; hi ], _) ->
      { Ir.owned_arr; from_idx = expr params lo; to_idx = expr params hi }
  | _ -> fail s "expected (owns arr lo hi)"

let thread params s =
  match s with
  | List (Atom ("thread", _) :: Atom (thread_name, _) :: rest, _) ->
      let rec split owns forms =
        match forms with
        | (List (Atom ("owns", _) :: _, _) as o) :: more ->
            split (owned_range params o :: owns) more
        | body -> (List.rev owns, body)
      in
      let owns, body = split [] rest in
      { Ir.thread_name; owns; body = List.map (stmt params) body }
  | _ -> fail s "expected (thread name (owns ...) ... stmt ...)"

let head s =
  match s with List (Atom (name, _) :: _, _) -> Some name | _ -> None

let program forms =
  let params =
    match List.filter (fun f -> head f = Some "params") forms with
    | [] -> []
    | [ f ] -> params_form f
    | _ :: f :: _ -> fail f "params declared twice"
  in
  let names = List.map fst params in
  let empty = { Ir.params; arrays = []; atomics = []; threads = [] } in
  let add (p : Ir.program) f =
    match head f with
    | Some "params" -> p
    | Some "array" -> { p with arrays = array_decl names f :: p.arrays }
    | Some "atomic" -> { p with atomics = atomic_decl names f :: p.atomics }
    | Some "thread" -> { p with threads = thread names f :: p.threads }
    | Some name -> fail f ("unknown declaration " ^ name)
    | None -> fail f "expected a declaration"
  in
  let p = List.fold_left add empty forms in
  {
    p with
    arrays = List.rev p.arrays;
    atomics = List.rev p.atomics;
    threads = List.rev p.threads;
  }

let parse_program src = program (read src)
