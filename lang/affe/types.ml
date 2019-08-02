type level = int


module Borrow = struct
  type t = Syntax.borrow =  Immutable | Mutable
  let equal b1 b2 = match b1, b2 with
    | Immutable, Immutable
    | Mutable, Mutable
      -> true
    | _
      -> false
  let max b1 b2 = match b1, b2 with
    | _, Mutable | Mutable, _ -> Mutable
    | Immutable, Immutable
      -> Immutable
end

type kind = Kinds.t

type typ =
  | App : Name.t * typ list -> typ
  | Arrow : typ * kind * typ -> typ
  | GenericVar : Name.t -> typ
  | Var : tyvar ref -> typ
  | Borrow : Borrow.t * kind * typ -> typ
  | Tuple of typ list

and tyvar =
  | Unbound of Name.t * level
  | Link of typ

type constr =
  | TypeLeq of typ * typ
  | KindLeq of kind * kind
  | HasKind of typ * kind
  | And of constr list

type normalized_constr =
  | KindLeq of kind * kind
  | HasKind of Name.t * typ * kind
  | And of normalized_constr list

type scheme = {
  kvars : Name.t list ;
  tyvars : Name.t list ;
  constr : normalized_constr ;
  ty : typ ;
}

type kscheme = {
  kvars : Name.t list ;
  constr : normalized_constr ;
  args : kind list ;
  kind : kind ;
}


let var ?name level =
  let n = Name.create ?name () in
  n, Var (ref (Unbound(n, level)))
let kind ?name level =
  let n = Name.create ?name () in
  n, Kinds.Var (ref (Kinds.Unbound(n, level)))
let gen_var () = let n = Name.create () in n, GenericVar n
let gen_kind_var () = let n = Name.create () in n, Kinds.GenericVar n

let tyscheme ?(constr=And []) ?(kvars=[]) ?(tyvars=[]) ty =
  { constr ; kvars ; tyvars ; ty }

let kscheme ?(constr=And []) ?(kvars=[]) ?(args=[]) kind =
  { constr ; kvars ; args ; kind }

let rec repr = function
  | Var { contents = Link t } -> repr t
  | _ as t -> t

module Fold = struct
  
  let (++) = Name.Set.union

  let rec kind (++) z = function
    | Kinds.GenericVar n -> (`Kind n) ++ z
    | Var { contents = Link t } -> kind (++) z t
    | Var { contents = Unbound (n, _) } -> (`Kind n) ++ z
    | Un _ | Aff _ | Lin _ -> z

  let kinds (++) z l =
    List.fold_left
      (fun e k -> kind (++) e k)
      z l

  let rec types (++) z = function
    | GenericVar n ->
      `Ty n ++ z
    | Var { contents = Link t } ->
      types (++) z t
    | Var { contents = Unbound (n, _) } ->
      `Ty n ++ z
    | App (_, args) ->
      List.fold_left (fun x t ->
          types (++) x t
        ) z args
    | Arrow (ty1, k, ty2) ->
      types (++) ( kind (++) (types (++) z ty2) k) ty1
    | Tuple tys ->
      let aux x ty = types (++) x ty in
      List.fold_left aux z tys
    | Borrow (_, k, t) ->
      kind (++) (types (++) z t) k 

  let rec normalized_constr (++) z = function
    | KindLeq (k1,k2) -> kind (++) (kind (++) z k1) k2
    | HasKind (_, t, k) -> kind (++) (types (++) z t) k
    | And l -> List.fold_left (normalized_constr (++)) z l

  let scheme (++) z { tyvars ; ty ; constr ; _ } =
    let z' = types (++) z ty in
    let fv, _ = normalized_constr (++) z' constr in
    Name.Set.diff fv (Name.Set.of_list tyvars)
end

module Free_vars = struct

  let fv_zero = Name.Set.empty
  let fv_red x kfv = match x with
    | `Kind x -> Name.Set.add x kfv
  let kind k = Fold.kind fv_red fv_zero k
  let kinds ks = Fold.kinds fv_red fv_zero ks

  let fv_zero = (Name.Set.empty, Name.Set.empty)
  let fv_red x (fv, kfv) = match x with
    | `Ty x -> Name.Set.add x fv, kfv
    | `Kind x -> fv, Name.Set.add x kfv
  let normalized_constr c = Fold.normalized_constr fv_red fv_zero c
  let types ty = Fold.types fv_red fv_zero ty
  let scheme s = Fold.scheme fv_red fv_zero s
  let schemes l =
    List.fold_left
      (fun e sch -> Name.Set.union e @@ scheme sch)
      Name.Set.empty
      l
end

module Use = struct
  
  type t =
    | Shadow of Borrow.t
    | Borrow of (Borrow.t * kind list)
    | Normal of kind list

end
