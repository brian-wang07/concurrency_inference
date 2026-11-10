type t = Rlx | Acq | Rel | AcqRel | Sc

let all = [ Rlx; Acq; Rel; AcqRel; Sc ]

let to_string = function
  | Rlx -> "rlx"
  | Acq -> "acq"
  | Rel -> "rel"
  | AcqRel -> "acq_rel"
  | Sc -> "sc"

let of_string = function
  | "rlx" -> Some Rlx
  | "acq" -> Some Acq
  | "rel" -> Some Rel
  | "acq_rel" -> Some AcqRel
  | "sc" -> Some Sc
  | _ -> None

let to_cpp = function
  | Rlx -> "std::memory_order_relaxed"
  | Acq -> "std::memory_order_acquire"
  | Rel -> "std::memory_order_release"
  | AcqRel -> "std::memory_order_acq_rel"
  | Sc -> "std::memory_order_seq_cst"

(** returns the stronger ordering between a and b *)
let join a b =
  match (a, b) with
  | Rlx, x | x, Rlx -> x
  | Sc, _ | _, Sc -> Sc
  | Acq, Acq -> Acq
  | Rel, Rel -> Rel
  | _ -> AcqRel

(** returns true if a is at most as strong as b *)
let leq a b = join a b = b
