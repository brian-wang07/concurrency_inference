(* verifies if a given ir is well-formed. *)
open Ir
module StringMap = Map.Make (String)

exception Wf_error of string

let fail fmt = Printf.ksprintf (fun msg -> raise (Wf_error msg)) fmt

let cpp_keywords =
  [
    "alignas";
    "alignof";
    "and";
    "and_eq";
    "asm";
    "auto";
    "bitand";
    "bitor";
    "bool";
    "break";
    "case";
    "catch";
    "char";
    "char8_t";
    "char16_t";
    "char32_t";
    "class";
    "compl";
    "concept";
    "const";
    "consteval";
    "constexpr";
    "constinit";
    "const_cast";
    "continue";
    "co_await";
    "co_return";
    "co_yield";
    "decltype";
    "default";
    "delete";
    "do";
    "double";
    "dynamic_cast";
    "else";
    "enum";
    "explicit";
    "export";
    "extern";
    "false";
    "float";
    "for";
    "friend";
    "goto";
    "if";
    "inline";
    "int";
    "long";
    "mutable";
    "namespace";
    "new";
    "noexcept";
    "not";
    "not_eq";
    "nullptr";
    "operator";
    "or";
    "or_eq";
    "private";
    "protected";
    "public";
    "register";
    "reinterpret_cast";
    "requires";
    "return";
    "short";
    "signed";
    "sizeof";
    "static";
    "static_assert";
    "static_cast";
    "struct";
    "switch";
    "template";
    "this";
    "thread_local";
    "throw";
    "true";
    "try";
    "typedef";
    "typeid";
    "typename";
    "union";
    "unsigned";
    "using";
    "virtual";
    "void";
    "volatile";
    "wchar_t";
    "while";
    "xor";
    "xor_eq";
  ]

let reserved = "emod" :: "main" :: cpp_keywords

let is_identifier s =
  let is_start c =
    match c with 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false
  in
  let is_rest r =
    match r with
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
    | _ -> false
  in
  match s with "" -> false | _ -> is_start s.[0] && String.for_all is_rest s

let globals prog =
  List.map (fun (name, _) -> ("param", name)) prog.params
  @ List.map (fun d -> ("array", d.arr_name)) prog.arrays
  @ List.map (fun d -> ("atomic", d.atom_name)) prog.atomics
  @ List.map (fun th -> ("thread", th.thread_name)) prog.threads

let check_names prog =
  List.iter
    (fun (kind, name) ->
      if not (is_identifier name) then
        fail "%s %s is not a valid C++ identifier" kind name;
      if List.mem name reserved then fail "%s %s uses a reserved name" kind name)
    (globals prog);
  ignore
    (List.fold_left
       (fun seen (kind, name) ->
         match StringMap.find_opt name seen with
         | Some earlier ->
             fail "%s %s clashes with %s %s" kind name earlier name
         | None -> StringMap.add name kind seen)
       StringMap.empty (globals prog));
  let threads = List.map (fun th -> th.thread_name) prog.threads in
  List.iter
    (fun d ->
      if not (List.mem d.writer threads) then
        fail "atomic %s has writer %s, which is not a thread" d.atom_name
          d.writer;
      match d.reader with
      | Some r ->
          if not (List.mem r threads) then
            fail "atomic %s has reader %s which is not a thread" d.atom_name r
      | None -> ())
    prog.atomics

let rec labels body =
  List.concat_map
    (fun s ->
      match s with
      | Load { acc; _ } | Store { acc; _ } | Await { acc; _ } -> [ acc.label ]
      | For { body; _ } -> labels body
      | NaRead _ | NaWrite _ | Let _ | Assert _ -> [])
    body

(* every access label in the program, thread by thread *)
let program_labels prog =
  List.concat_map (fun th -> labels th.body) prog.threads

let check_labels prog =
  let uses =
    List.concat_map
      (fun th -> List.map (fun l -> (th.thread_name, l)) (labels th.body))
      prog.threads
  in
  ignore
    (List.fold_left
       (fun seen (thread, label) ->
         match StringMap.find_opt label seen with
         | Some earlier ->
             fail "label %s is used in %s and in %s" label earlier thread
         | None -> StringMap.add label thread seen)
       StringMap.empty uses)

let rec constant e =
  match e with
  | Int _ | Param _ -> true
  | Var _ -> false
  | Add (lhs, rhs) | Sub (lhs, rhs) | Mod (lhs, rhs) ->
      constant lhs && constant rhs

let check_loops prog =
  let lookup = globals prog in
  let check_local thread name =
    if not (is_identifier name) then
      fail "local variable %s in thread '%s' is not a valid identifier" name
        thread;
    if List.mem name reserved then
      fail "local %s in thread '%s' is a reserved name" name thread;
    match List.find_opt (fun (_, g) -> g = name) lookup with
    | Some (kind, _) ->
        fail "local %s in thread '%s' clashes with %s %s" name thread kind name
    | None -> ()
  in
  let rec walk thread scope body =
    List.iter
      (fun s ->
        match s with
        | For { var; lo; hi; body = inner } ->
            if not (constant lo) then
              fail "lower loop bound %s in thread '%s' is not a constant"
                (expr_to_string lo) thread;
            if not (constant hi) then
              fail "upper loop bound %s in thread '%s' is not a constant"
                (expr_to_string hi) thread;
            if List.mem var scope then
              fail
                "loop variable %s in thread '%s' has already been defined by \
                 an enclosing loop"
                var thread;
            check_local thread var;
            walk thread (var :: scope) inner
        | Let { dst; _ } | Load { dst; _ } | NaRead { dst; _ } ->
            if List.mem dst scope then
              fail "thread '%s' assigns loop variable %s" thread dst;
            check_local thread dst
        | NaWrite _ | Store _ | Await _ | Assert _ -> ())
      body
  in
  List.iter (fun th -> walk th.thread_name [] th.body) prog.threads

let check prog =
  check_names prog;
  check_labels prog;
  check_loops prog
