(* turns check.ml's requirements into a concrete ordering per label and checks existing orderings against them. each requirement suggested is a lower bound *)

type sigma = (string * Ord.t) list

type violation = {
  label : string;
  pinned : Ord.t;
  needed : Ord.t;
  because : Check.requirement list;
}

exception Bad_pin of string

let infer (reqs : Check.requirement list) : sigma =
  let joined =
    List.fold_left
      (fun acc (r : Check.requirement) ->
        let cur = Option.value ~default:Ord.Rlx (List.assoc_opt r.label acc) in
        (r.label, Ord.join cur r.at_least) :: List.remove_assoc r.label acc)
      [] reqs
  in
  List.sort compare joined

let check (reqs : Check.requirement list) (pins : sigma) : violation list =
  List.concat_map
    (fun (label, pinned) ->
      let mine =
        List.filter (fun (r : Check.requirement) -> r.label = label) reqs
      in
      if mine = [] then raise (Bad_pin ("no access labelled " ^ label));
      let unmet =
        List.filter
          (fun (r : Check.requirement) -> not (Ord.leq r.at_least pinned))
          mine
      in
      if unmet = [] then []
      else
        let needed =
          List.fold_left
            (fun acc (r : Check.requirement) -> Ord.join acc r.at_least)
            Ord.Rlx unmet
        in
        [ { label; pinned; needed; because = unmet } ])
    pins

let apply_pins (sigma : sigma) (pins : sigma) =
  List.map
    (fun (label, inferred) ->
      match List.assoc_opt label pins with
      | Some pinned -> (label, pinned)
      | None -> (label, inferred))
    sigma

let reason (reqs : Check.requirement list) (label : string) :
    Check.requirement option =
  List.find_opt
    (fun (r : Check.requirement) -> r.label = label && r.at_least <> Ord.Rlx)
    reqs
