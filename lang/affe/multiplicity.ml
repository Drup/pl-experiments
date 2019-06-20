open Types
open Use

type t = Use.t Name.Map.t
let empty = Name.Map.empty
let var x k = Name.Map.singleton x (Normal [k])
let borrow x r k = Name.Map.singleton x (Borrow (r, [k]))

exception Fail of Name.t * Use.t * Use.t
exception FailRegion of Name.t * Use.t
let fail n u1 u2 = raise (Fail (n, u1, u2))

let constr_all_kinds ~bound ks =
  List.map (fun k -> Constraint.(k <= bound)) ks
let bound_all_kinds f n ks =
  CCList.flat_map
    (fun k -> Constraint.[f (Region.Region n) <= k; k <= f Region.Never])
    ks

let merge (e1 : t) (e2 : t) =
  let constr = ref [] in
  let bound = Un Never in
  let constr_kinds ks =
    constr := (constr_all_kinds ~bound ks) @ !constr
  in
  let aux x u1 u2 = match u1, u2 with
    | Shadow _, u -> Some u
    | Borrow (Immutable, k1), Borrow (Immutable, k2)
      ->
      Some (Borrow (Immutable, k1@k2))
    | Normal l1, Normal l2 ->
      let l = l1 @ l2 in
      constr_kinds l ;
      Some (Normal l)
    | Borrow _, Borrow _
    | _, Shadow _
    | Borrow _, Normal _
    | Normal _, Borrow _ -> fail x u1 u2
  in
  let m = Name.Map.union aux e1 e2 in
  m, Constraint.cand !constr

let parallel_merge  (e1 : t) (e2 : t) =
  (* let constr = ref [] in
   * let constr_kinds ~bound ks =
   *   constr := (constr_all_kinds ~bound ks) @ !constr
   * in *)
  let aux x u1 u2 = match u1, u2 with
    | Shadow r1, Shadow r2 ->
      Some (Shadow (Borrow.max r1 r2))
    | Shadow r', Borrow (r,l)
    | Borrow (r, l), Shadow r'
      ->
      (* constr_kinds ~bound:(Aff Never) l ; *)
      Some (Borrow (Borrow.max r r', l))
    | Borrow (Immutable as r, k1), Borrow (Immutable, k2)
    | Borrow (Mutable as r, k1), Borrow (Mutable, k2)
      ->
      Some (Borrow (r, k1@k2))
    | Normal l1, Normal l2 ->
      let l = l1 @ l2 in
      Some (Normal l)
    | Shadow _, Normal l
    | Normal l, Shadow _
      ->
      (* constr_kinds ~bound:(Aff Never) l ; *)
      Some (Normal l)
    | Borrow _, Borrow _
    | Borrow _, Normal _
    | Normal _, Borrow _ -> fail x u1 u2
  in
  let m = Name.Map.union aux e1 e2 in
  m, Constraint.T.True

let constraint_all (e : t) bound : constr =
  let aux _ ks l = match ks with
    | Normal ks -> constr_all_kinds ~bound ks @ l
    | Borrow _ | Shadow _ -> []
  in
  let l = Name.Map.fold aux e [] in
  Constraint.cand l

let exit_region x0 n (m : t) =
  let constr = ref [] in
  let constr_kinds ks f =
    constr := (bound_all_kinds f n ks) @ !constr
  in
  let m = Name.Map.update x0 (function
      | None -> None
      | Some Borrow (Mutable, ks) ->
        constr_kinds ks (fun r -> Aff r);
        Some (Shadow Mutable)
      | Some Borrow (Immutable, ks) ->
        Fmt.epr "%a@." (Fmt.list Printer.kind) ks ;
        constr_kinds ks (fun r -> Un r);
        Some (Shadow Immutable)
      | Some b -> raise (FailRegion (x0,b)))
      m
  in
  m, Constraint.cand !constr

let exit_binder (e : t) x k : constr * t =
  let constr = match Name.Map.find_opt x e with
    | Some Shadow _
    | Some Borrow _
    | Some Normal [_]
      -> True
    | None | Some Normal [] | Some Normal _ ->
      Constraint.(k <= Aff Never)
  in
  constr, Name.Map.remove x e
