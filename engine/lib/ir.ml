(* The AST: a program with its protocols. Every atomic access is an ordering
   hole identified by its label; the orderings themselves live in Solve. *)

type expr =
  | Int of int
  | Param of string
  | Var of string
  | Add of expr * expr
  | Sub of expr * expr
  | Mod of expr * expr (* euclidean mod *)

type res =
  | Own of { arr : string; idx : expr }
  | PointsTo of { arr : string; idx : expr; value : expr }

type protocol = { binder : string; payload : res list }
type access = { label : string; atom : string }

type stmt =
  | NaRead of { dst : string; arr : string; idx : expr }
  | NaWrite of { arr : string; idx : expr; value : expr }
  | Load of { dst : string; acc : access }
  | Store of { acc : access; value : expr }
  | Await of { acc : access; bound : expr }
  | Let of { dst : string; value : expr }
  | Assert of { lhs : expr; rhs : expr }
  | For of { var : string; lo : expr; hi : expr; body : stmt list }

type array_decl = { arr_name : string; size : expr }

type atomic_decl = {
  atom_name : string;
  init : int;
  writer : string;
  reader : string option;
  protocol : protocol;
}

(* half open range *)
type owned_range = { owned_arr : string; from_idx : expr; to_idx : expr }

type thread = {
  thread_name : string;
  owns : owned_range list;
  body : stmt list;
}

type program = {
  params : (string * int) list;
  arrays : array_decl list;
  atomics : atomic_decl list;
  threads : thread list;
}
