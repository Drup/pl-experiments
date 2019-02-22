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
  | Borrow : Borrow.t * typ -> typ

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


let rec free_vars = function
  | App (_, l) ->
    List.fold_left (fun s e -> Name.Set.union s @@ free_vars e) Name.Set.empty l
  | Arrow (ty1, _, ty2) -> Name.Set.union (free_vars ty1) (free_vars ty2)
  | GenericVar n -> Name.Set.singleton n
  | Var { contents = Link t } -> free_vars t
  | Var { contents = Unbound (n, _) } -> Name.Set.singleton n
  | Borrow (_, t) -> free_vars t

let free_vars_scheme { tyvars ; ty ; _ } =
  Name.Set.diff (free_vars ty) (Name.Set.of_list @@ List.map fst tyvars) 
