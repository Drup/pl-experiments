type level = int

module Region = struct
  type t = Global | Region of int | Never
  let compare r1 r2 = match r1, r2 with
    | Region r1, Region r2 -> CCInt.compare r1 r2
    | Global, Global | Never, Never -> 0
    | Global, _ | _, Never -> -1
    | _, Global | Never, _ -> 1
  let equal r1 r2 = compare r1 r2 = 0
  let biggest = Never
  let smallest = Global
  let max l1 l2 = match l1, l2 with
    | Region r1, Region r2 -> Region (CCInt.max r1 r2)
    | Never, _ | _, Never -> Never
    | Global, l | l, Global -> l
  let min l1 l2 = match l1, l2 with
    | Region r1, Region r2 -> Region (CCInt.min r1 r2)
    | Never, l | l, Never -> l
    | Global, _ | _, Global -> Global
end
type region = Region.t

module Borrow = struct
  type t = Syntax.borrow = Read | Write
  let equal b1 b2 = match b1, b2 with
    | Read, Read | Write, Write -> true
    | Read, Write | Write, Read -> false
  let max a b = match a, b with
    | Read, Read -> Read
    | Write, _ | _, Write -> Write
end

type kind =
  | Un : region -> kind
  | Aff : region -> kind
  | KGenericVar : Name.t -> kind
  | KVar : kuvar ref -> kind

and kuvar =
  | KUnbound of Name.t * level
  | KLink of kind

type typ =
  | App : Name.t * typ list -> typ
  | Arrow : typ * kind * typ -> typ
  | GenericVar : Name.t -> typ
  | Var : uvar ref -> typ
  | Borrow : Borrow.t * kind * typ -> typ
  | Tuple of typ list

and uvar =
  | Unbound of Name.t * level
  | Link of typ

type constr =
  | True
  | Eq of typ * typ
  | KindLeq of kind * kind
  | And of constr list

type normalized_constr = (kind * kind) list

type scheme = {
  kvars : Name.t list ;
  tyvars : (Name.t * kind) list ;
  constr : normalized_constr ;
  ty : typ ;
}

type kscheme = {
  kvars : Name.t list ;
  constr : normalized_constr ;
  args : kind list ;
  kind : kind ;
}


let var ~name level =
  let n = Name.create ~name () in
  n, Var (ref (Unbound(n, level)))
let kind ~name level =
  let n = Name.create ~name () in
  n, KVar (ref (KUnbound(n, level)))
let gen_var () = let n = Name.create () in n, GenericVar n
let gen_kind_var () = let n = Name.create () in n, KGenericVar n

let tyscheme ?(constr=[]) ?(kvars=[]) ?(tyvars=[]) ty =
  { constr ; kvars ; tyvars ; ty }

let kscheme ?(constr=[]) ?(kvars=[]) ?(args=[]) kind =
  { constr ; kvars ; args ; kind }


module Fold = struct
  
  let (++) = Name.Set.union

  let rec kind (++) z = function
    | KGenericVar n -> (`Kind n) ++ z
    | KVar { contents = KLink t } -> kind (++) z t
    | KVar { contents = KUnbound (n, _) } -> (`Kind n) ++ z
    | Un _ | Aff _ -> z

  let kinds (++) z l =
    List.fold_left
      (fun e k -> kind (++) e k)
      z l

  let constrs (++) z l =
    List.fold_left
      (fun z (k1, k2) -> kind (++) (kind (++) z k1) k2)
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

  let scheme (++) z { tyvars ; ty ; _ } =
    let fv, _ = types (++) z ty in
    Name.Set.diff fv (Name.Set.of_list @@ List.map fst tyvars)

end

module Free_vars = struct

  let fv_zero = Name.Set.empty
  let fv_red x kfv = match x with
    | `Kind x -> Name.Set.add x kfv
  let kind k = Fold.kind fv_red fv_zero k
  let kinds ks = Fold.kinds fv_red fv_zero ks
  let constrs c = Fold.constrs fv_red fv_zero c

  let fv_zero = (Name.Set.empty, Name.Set.empty)
  let fv_red x (fv, kfv) = match x with
    | `Ty x -> Name.Set.add x fv, kfv
    | `Kind x -> fv, Name.Set.add x kfv
  let types ty = Fold.types fv_red fv_zero ty
  let scheme s = Fold.scheme fv_red fv_zero s
end
