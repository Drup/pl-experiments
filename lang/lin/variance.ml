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
  let get (m : t) k = CCOpt.get_or ~default:Bivar @@ Name.Map.find_opt k m
  let add (m : t) k v =
    Name.Map.update k (function None -> Some v | Some v' -> Some (merge v v')) m
  let merge = Name.Map.union (fun _ v1 v2 -> Some (merge v1 v2))
  let add_set m set var =
    Name.Set.fold (fun name m -> Name.Map.add name var m) set m
end

open Types
type bimap = { ty : Map.t ; kind : Map.t }
let add_ty m ty v = { m with ty = Map.add m.ty ty v }
let add_kinds m k v = { m with kind = Map.add_set m.kind k v }
let rec types var m = function
  | GenericVar name ->
    add_ty m name var
  | Var { contents = Link t } ->
    types var  m t
  | Var { contents = Unbound (name, _) } ->
    add_ty m name var
  | App (_, args) ->
    List.fold_left (fun x t ->
        types var  x t
      ) m args
  | Arrow (ty1, k, ty2) ->
    let m = types (neg var) m ty1 in
    let m = add_kinds m (Free_vars.kind k) var in
    let m = types var m ty2 in
    m
  | Tuple tys ->
    let aux x ty = types var  x ty in
    List.fold_left aux m tys
  | Borrow (_, k, ty) ->
    let m = types var m ty in
    let m = add_kinds m (Free_vars.kind k) var in
    m
