module M = struct
  type t =
    | Pos
    | Neg
    | Invar
    | Bivar
  [@@deriving eq, ord]
end
include M
type variance = t

let neg = function
  | Pos -> Neg
  | Neg -> Pos
  | Invar -> Invar
  | Bivar -> Bivar
let merge v1 v2 = match v1, v2 with
  | Bivar, v
  | v, Bivar -> v
  | Pos, Pos -> Pos
  | Neg, Neg -> Neg
  | Invar, _
  | Neg, Pos
  | Pos, Neg
  | _, Invar -> Invar


module Map = struct
  type t = variance Name.Map.t
  let empty = Name.Map.empty
  let get (m : t) k = CCOpt.get_or ~default:Bivar @@ Name.Map.find_opt k m
  let find (m : t) k = Name.Map.find_opt k m
  let mem (m : t) k = Name.Map.mem k m
  let add (m : t) k v =
    Name.Map.update k (function None -> Some v | Some v' -> Some (merge v v')) m
  let merge = Name.Map.union (fun _ v1 v2 -> Some (merge v1 v2))
end
