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

module Lattice = struct
  type t =
    | Un of Region.t
    | Aff of Region.t
    | Lin of Region.t
  let leq l1 l2 = match l1, l2 with
    | Lin r1, Lin r2
    | Aff r1, Aff r2
    | Un r1, Un r2 -> Region.compare r1 r2 <= 0
    | _, Lin Never -> true
    | Un Global, _ -> true
    | Un r1, Aff r2 | Un r1, Lin r2 | Aff r1, Lin r2 ->
      Region.compare r1 r2 <= 0
    | _ -> false
  let equal l1 l2 = match l1, l2 with
    | Lin r1, Lin r2
    | Aff r1, Aff r2
    | Un r1, Un r2 -> Region.equal r1 r2
    | _ -> false
  let smallest = Un Region.smallest
  let biggest = Lin Region.biggest
  let max l1 l2 = match l1, l2 with
    | Un r1, Un r2 -> Un (Region.max r1 r2)
    | Aff r1, Aff r2 -> Aff (Region.max r1 r2)
    | Lin r1, Lin r2 -> Lin (Region.max r1 r2)
    | Un _, (Aff _ as r)
    | (Un _ | Aff _), (Lin _ as r)
    | (Lin _ as r), (Un _ | Aff _)
    | (Aff _ as r), Un _ -> r
  let min l1 l2 = match l1, l2 with
    | Un r1, Un r2 -> Un (Region.min r1 r2)
    | Aff r1, Aff r2 -> Aff (Region.min r1 r2)
    | Lin r1, Lin r2 -> Lin (Region.min r1 r2)
    | (Aff _ | Lin _), (Un _ as r)
    | Lin _, (Aff _ as r)
    | (Un _ as r), (Aff _ | Lin _) 
    | (Aff _ as r), Lin _
      -> r
  let least_upper_bound = List.fold_left max smallest
  let greatest_lower_bound = List.fold_left min biggest
  let constants =
    [ Un Global ; Un Never ;
      Aff Global ; Aff Never ;
      Lin Global ; Lin Never ;
    ]
  let relations consts =
    let consts = constants @ consts in
    CCList.product (fun l r -> l, r) consts consts
    |> CCList.filter (fun (l, r) -> leq l r)
end


type level = int

type kind =
  | Un : region -> kind
  | Aff : region -> kind
  | Lin : region -> kind
  | GenericVar : Name.t -> kind
  | Var : var ref -> kind

and var =
  | Unbound of Name.t * level
  | Link of kind

let un r = Un r
let aff r = Aff r
let lin r = Lin r


(** Immutable impl, without embedded union find *)
(* module K = struct
 *   type t =
 *     | Var of Name.t * level option
 *     | Constant of Lattice.t
 *   let equal l1 l2 = match l1, l2 with
 *     | Var (n1,_), Var (n2,_) -> Name.equal n1 n2
 *     | Constant l1, Constant l2 -> Lattice.(l1 = l2)
 *     | _ -> false
 *   let hash = Hashtbl.hash
 *   let compare l1 l2 = if equal l1 l2 then 0 else compare l1 l2
 * end
 * 
 * (\** Utilities for the lattice solver *\)
 * 
 * type constant = Lattice.t
 * let classify = function
 *   | Constant c -> `Constant c
 *   | Var _ -> `Var
 * let constant c = Constant c *)


module K = struct
  type t = kind

  let rec repr = function
    | Var {contents = Link k} -> repr k
    | Un _ | Aff _ | Lin _ | GenericVar _
    | Var {contents = Unbound _} as k -> k

  let equal a b = repr a = repr b
  let hash x = Hashtbl.hash (repr x)
  let compare a b = compare (repr a) (repr b)

  type constant = Lattice.t
  let rec classify = function
    | Var { contents = Link k } -> classify k
    | Var { contents = Unbound (n,_) }
    | GenericVar n -> `Var n
    | Lin r -> `Constant (Lattice.Lin r)
    | Aff r -> `Constant (Lattice.Aff r)
    | Un r -> `Constant (Lattice.Un r)
  let constant = function
    | Lattice.Lin r -> Lin r
    | Lattice.Aff r -> Aff r
    | Lattice.Un r -> Un r

end

include K
module Map = Map.Make(K)
module Set = Set.Make(K)
