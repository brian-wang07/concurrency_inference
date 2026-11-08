(* walks each thread with some resource context and applies a typing rule. Outputs requirements that describe the required ordering for a given label. Ownership mistakes raise a type error. *)
open Ir

exception Type_error of string

type value = Known of int | Unknown

module StringMap = Map.Make (String)

module CellMap = Map.Make (struct
  type t = string * int

  let compare = compare
end)

type role =
  | Writer of { current : int }
  | Reader of { claimed : int }
  | Bystander

(* constraint is a reserved kw *)
type requirement = {
  label : string;
  at_least : Ord.t;
  loops : (string * int) list;
  reason : string;
}

type ctx = {
  cells : value CellMap.t;
  roles : role StringMap.t;
  env : value StringMap.t;
  loops : (string * int) list;
  reqs : requirement list;
}

(* euclidean mod helper *)
let emod a b =
  let r = a mod b in
  if r < 0 then r + b else r

(* evaluates expression e given a program and environment state *)
let rec eval prog env e =
  match e with
  | Int n -> Known n
  | Param x -> (
      match List.assoc_opt x prog.params with
      | Some n -> Known n
      | None -> raise (Type_error ("Unknown parameter " ^ x)))
  | Var x -> (
      match StringMap.find_opt x env with
      | Some v -> v
      | None -> raise (Type_error ("Unknown variable " ^ x)))
  | Add (a, b) -> (
      match (eval prog env a, eval prog env b) with
      | Known x, Known y -> Known (x + y)
      | _ -> Unknown)
  | Sub (a, b) -> (
      match (eval prog env a, eval prog env b) with
      | Known x, Known y -> Known (x - y)
      | _ -> Unknown)
  | Mod (a, b) -> (
      match (eval prog env a, eval prog env b) with
      | Known x, Known y ->
          if y <= 0 then raise (Type_error "mod by non-positive number")
          else Known (emod x y)
      | _ -> Unknown)

let eval_known prog env e =
  match eval prog env e with
  | Known n -> n
  | Unknown -> raise (Type_error "value not statically known")

(* turn a protocol into concrete resources that get published *)
let instantiate prog proto v =
  let env = StringMap.singleton proto.binder (Known v) in
  List.map
    (fun r ->
      match r with
      | Own { arr; idx } -> ((arr, eval_known prog env idx), Unknown)
      | PointsTo { arr; idx; value } ->
          ((arr, eval_known prog env idx), Known (eval_known prog env value)))
    proto.payload

let delta prog proto from to_ =
  let values = List.init (max 0 (to_ - from)) (fun k -> from + 1 + k) in
  List.concat_map (instantiate prog proto) values

let atomic prog name =
  match List.find_opt (fun d -> d.atom_name = name) prog.atomics with
  | Some d -> d
  | None -> raise (Type_error ("Unknown atomic " ^ name))

let size prog arr =
  match List.find_opt (fun d -> d.arr_name = arr) prog.arrays with
  | Some d -> eval_known prog StringMap.empty d.size
  | None -> raise (Type_error ("Unknown array " ^ arr))

let require ctx label at_least reason =
  let r = { label; at_least; loops = ctx.loops; reason } in
  { ctx with reqs = r :: ctx.reqs }

let cell prog env arr idx =
  let i = eval_known prog env idx in
  let n = size prog arr in
  if i < 0 || i >= n then
    raise (Type_error (Printf.sprintf "%s[%d] out of bounds (size %d)" arr i n));
  (arr, i)

let value_to_string v =
  match v with Known n -> string_of_int n | Unknown -> "unknown"

let role ctx atom =
  match StringMap.find_opt atom ctx.roles with
  | Some r -> r
  | None -> raise (Type_error ("Unknown atomic " ^ atom))

let rec check_stmt prog ctx s =
  match s with
  | Let { dst; value } ->
      { ctx with env = StringMap.add dst (eval prog ctx.env value) ctx.env }
  | NaRead { dst; arr; idx } -> (
      let c = cell prog ctx.env arr idx in
      match CellMap.find_opt c ctx.cells with
      | Some v -> { ctx with env = StringMap.add dst v ctx.env }
      | None ->
          raise
            (Type_error
               (Printf.sprintf "read %s[%d] without ownership" arr (snd c))))
  | NaWrite { arr; idx; value } -> (
      let c = cell prog ctx.env arr idx in
      match CellMap.find_opt c ctx.cells with
      | Some _ ->
          { ctx with cells = CellMap.add c (eval prog ctx.env value) ctx.cells }
      | None ->
          raise
            (Type_error
               (Printf.sprintf "write %s[%d] without ownership" arr (snd c))))
  | Assert { lhs; rhs } ->
      let l = eval_known prog ctx.env lhs in
      let r = eval_known prog ctx.env rhs in
      if l = r then ctx
      else
        raise
          (Type_error
             (Printf.sprintf "assertion '%s = %s' failed (%d vs %d)"
                (expr_to_string lhs) (expr_to_string rhs) l r))
  | Load { dst; acc } ->
      let v =
        match role ctx acc.atom with
        | Writer { current } -> Known current
        | Reader _ | Bystander -> Unknown
      in
      let ctx = { ctx with env = StringMap.add dst v ctx.env } in
      require ctx acc.label Ord.Rlx "load"
  | Store { acc; value } -> (
      match role ctx acc.atom with
      | Writer { current } ->
          let v = eval_known prog ctx.env value in
          if v < current then
            raise
              (Type_error
                 (Printf.sprintf
                    "%s stored %d after %d, but counters must be monotone"
                    acc.atom v current))
          else
            let d = delta prog (atomic prog acc.atom).protocol current v in
            let publish cells (c, expected) =
              match (CellMap.find_opt c cells, expected) with
              | None, _ ->
                  raise
                    (Type_error
                       (Printf.sprintf
                          "store to %s publishes %s[%d] without owning it"
                          acc.atom (fst c) (snd c)))
              | Some got, Known e when got <> Known e ->
                  raise
                    (Type_error
                       (Printf.sprintf
                          "store to %s publishes %s[%d] = %s, but the protocol \
                           promises %d"
                          acc.atom (fst c) (snd c) (value_to_string got) e))
              | Some _, _ -> CellMap.remove c cells
            in
            let cells = List.fold_left publish ctx.cells d in
            let roles =
              StringMap.add acc.atom (Writer { current = v }) ctx.roles
            in
            let ctx = { ctx with cells; roles } in
            if d = [] then require ctx acc.label Ord.Rlx "store"
            else require ctx acc.label Ord.Rel "store"
      | Reader _ | Bystander ->
          raise (Type_error ("store to " ^ acc.atom ^ " by a non-writer")))
  | Await { acc; bound } -> (
      match role ctx acc.atom with
      | Writer _ ->
          raise (Type_error ("writer awaits its own atomic " ^ acc.atom))
      | Bystander -> require ctx acc.label Ord.Rlx "bystander"
      | Reader { claimed } ->
          let b = eval_known prog ctx.env bound in
          if b <= claimed then require ctx acc.label Ord.Rlx "nothing new"
          else
            let d = delta prog (atomic prog acc.atom).protocol claimed b in
            let gain cells (c, v) =
              if CellMap.mem c cells then
                raise
                  (Type_error
                     (Printf.sprintf
                        "await on %s gains %s[%d], which it already owns"
                        acc.atom (fst c) (snd c)))
              else CellMap.add c v cells
            in
            let cells = List.fold_left gain ctx.cells d in
            let roles =
              StringMap.add acc.atom (Reader { claimed = b }) ctx.roles
            in
            let ctx = { ctx with cells; roles } in
            if d = [] then require ctx acc.label Ord.Rlx "await"
            else require ctx acc.label Ord.Acq "await")
  | For { var; lo; hi; body } ->
      let lo = eval_known prog ctx.env lo in
      let hi = eval_known prog ctx.env hi in
      let outer_env = ctx.env in
      let outer_loops = ctx.loops in
      let rec iterate ctx k =
        if k >= hi then ctx
        else
          let ctx =
            {
              ctx with
              env = StringMap.add var (Known k) ctx.env;
              loops = (var, k) :: outer_loops;
            }
          in
          iterate (List.fold_left (check_stmt prog) ctx body) (k + 1)
      in
      let ctx = iterate ctx lo in
      { ctx with env = outer_env; loops = outer_loops }

(* builds an initial context that a thread starts with *)
let initial prog th =
  let add_range cells r =
    let lo = eval_known prog StringMap.empty r.from_idx in
    let hi = eval_known prog StringMap.empty r.to_idx in
    if 0 > lo || hi > size prog r.owned_arr then
      raise
        (Type_error
           (Printf.sprintf "%s owns %s[%d..%d) but %s has size %d"
              th.thread_name r.owned_arr lo hi r.owned_arr
              (size prog r.owned_arr)))
    else
      let indicies = List.init (max 0 (hi - lo)) (fun j -> lo + j) in
      List.fold_left
        (fun cells k -> CellMap.add (r.owned_arr, k) Unknown cells)
        cells indicies
  in
  let role_of d =
    if d.writer = th.thread_name then Writer { current = d.init }
    else if d.reader = Some th.thread_name then Reader { claimed = d.init }
    else Bystander
  in
  {
    cells = List.fold_left add_range CellMap.empty th.owns;
    roles =
      List.fold_left
        (fun roles d -> StringMap.add d.atom_name (role_of d) roles)
        StringMap.empty prog.atomics;
    env = StringMap.empty;
    loops = [];
    reqs = [];
  }

let check_thread prog th =
  let ctx = List.fold_left (check_stmt prog) (initial prog th) th.body in
  (* require adds each requirement to the front of the list so reverse to restore program order *)
  List.rev ctx.reqs

module StringSet = Set.Make (String)

(* ensure unique thread and atomic names *)
let check_unique kind names =
  ignore
    (List.fold_left
       (fun seen n ->
         if StringSet.mem n seen then
           raise (Type_error (Printf.sprintf "%s %s is declared twice" kind n))
         else StringSet.add n seen)
       StringSet.empty names)

(* ensure initial ownership is disjoint *)
let check_disjoint_ownership prog =
  let claim owners th =
    let cells = (initial prog th).cells in
    CellMap.fold
      (fun c _ owners ->
        match CellMap.find_opt c owners with
        | Some other ->
            raise
              (Type_error
                 (Printf.sprintf "%s[%d] is initially owned by both %s and %s"
                    (fst c) (snd c) other th.thread_name))
        | None -> CellMap.add c th.thread_name owners)
      cells owners
  in
  ignore (List.fold_left claim CellMap.empty prog.threads)

let check_program prog =
  check_unique "thread" (List.map (fun th -> th.thread_name) prog.threads);
  check_unique "atomic" (List.map (fun d -> d.atom_name) prog.atomics);
  check_unique "array" (List.map (fun d -> d.arr_name) prog.arrays);
  check_disjoint_ownership prog;
  List.concat_map (check_thread prog) prog.threads
