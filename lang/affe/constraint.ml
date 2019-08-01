module T = Types

let fail fmt =
  Zoo.error ~kind:"Type error" fmt

module Normal = struct

  type t = T.normalized_constr =
    | KindLeq of T.kind * T.kind
    | HasKind of T.typ * T.kind
    | And of t list

  let rec flatten' = function
    | And l -> flattenL l
    | c -> [c]
  and flattenL l = CCList.flat_map flatten' l
  let cand l : t = match flattenL l with
    | [c] -> c
    | l -> And l
  let flatten c = cand [c]

  let ctrue : t = And []
  let cleq k1 k2 : t = KindLeq (k1, k2)
  let hasKind ty k : t = HasKind (ty, k)
  let (<=) a b : t = KindLeq (a, b)
  let (&&&) c1 c2 : t = And [c1;c2]

end

module KindLeq = struct

  let mk k1 k2 = Normal.KindLeq (k1, k2)

end

module HasKind = struct

  let rec constraint_kind ~level ~env typ expected_kind = match typ with
    | T.App (f, args) ->
      let constrs, args =
        constraint_kinds ~level ~env args in
      let constr', kind =
        Instantiate.kind_scheme ~level ~args @@ Env.find_constr f env
      in
      Normal.(constr' &&& constrs &&& (kind <= expected_kind))
    | T.Tuple args ->
      let constrs, ks =
        constraint_kinds ~level ~env args
      in
      let constr_tup =
        Normal.cand @@ List.map (fun k -> Normal.cleq k expected_kind) ks
      in
      Normal.(constr_tup &&& constrs)
    | T.Arrow (_, k, _) ->
      Normal.(k <= expected_kind)
    | T.Borrow (_, k, _) ->
      Normal.(k <= expected_kind)
    | T.GenericVar _ ->
      assert false
    | T.Var { contents = T.Unbound (_, _) } ->
      Normal.hasKind typ expected_kind
    | T.Var { contents = T.Link ty } ->
      constraint_kind ~level ~env ty expected_kind

  and constraint_kinds ~level ~env l = 
    List.fold_right
      (fun ty (constrs, args) ->
         let _, k = T.kind level in
         let constr = constraint_kind ~level ~env ty k in
         Normal.(constr &&& constrs) , k::args)
      l (Normal.ctrue, [])

  let mk = constraint_kind
end
  
module TypeLeq = struct

  exception Fail of T.typ * T.typ

  let occurs_check_adjust_levels tvar_id tvar_level ty =
    let rec f : T.typ -> _ = function
      | T.Var {contents = T.Link ty} -> f ty
      | T.GenericVar _ -> assert false
      | T.Var ({contents = T.Unbound(other_id, other_level)} as other_tvar) ->
        if other_id = tvar_id then
          fail "Recursive types"
        else
          other_tvar := Unbound(other_id, min tvar_level other_level)
      | T.App(_, ty_args)
      | T.Tuple ty_args ->
        List.iter f ty_args
      | T.Arrow(param_ty, _,return_ty) ->
        f param_ty ;
        f return_ty
      | T.Borrow (_, _, ty) -> f ty
    in
    f ty

  let rec unify ~level ~env ty1 ty2 = match ty1, ty2 with
    | _, _ when ty1 == ty2 -> Normal.ctrue

    | T.App(ty1, ty_arg1), T.App(ty2, ty_arg2) when Name.equal ty1 ty2 ->
      Normal.cand (List.map2 (unify ~level ~env) ty_arg1 ty_arg2)

    | T.Borrow (r1, k1, ty1), T.Borrow (r2, k2, ty2) when T.Borrow.equal r1 r2 ->
      Normal.cand [
        KindLeq.mk k1 k2 ;
        unify ~level ~env ty1 ty2 ;
      ]

    | T.Arrow(param_ty1, k1, return_ty1), T.Arrow(param_ty2, k2, return_ty2) ->
      Normal.cand [
        KindLeq.mk k1 k2;
        unify ~level ~env param_ty2 param_ty1;
        unify ~level ~env return_ty1 return_ty2;
      ]
    | T.Tuple tys1, Tuple tys2 ->
      Normal.cand @@ List.map2 (unify ~level ~env) tys1 tys2

    | T.Var {contents = Link ty1}, ty2 -> unify ~level ~env ty1 ty2
    | ty1, T.Var {contents = Link ty2} -> unify ~level ~env ty1 ty2

    | T.Var {contents = Unbound(id1, _)},
      T.Var {contents = Unbound(id2, _)} when id1 = id2 ->
      (* There is only a single instance of a particular type variable. *)
      assert false

    | (T.Var ({contents = Unbound(id, level)} as tvar) as _ty1), (ty as _ty2)
    | (ty as _ty1), (T.Var ({contents = Unbound(id, level)} as tvar) as _ty2) ->
      occurs_check_adjust_levels id level ty ;
      (* let constr1, k1 = infer_kind ~env ~level ty1 in
       * let constr2, k2 = infer_kind ~env ~level ty2 in *)
      tvar := Link ty ;
      (* Normal.cand [constr1; constr2; KindLeq.mk k1 k2; KindLeq.mk k2 k1] *)
      Normal.ctrue

    | _, _ ->
      raise (Fail (ty1, ty2))

  let mk = unify
end



module LatSolve = struct
  
  exception Fail of T.kind * T.kind

  (* let adjust_levels tvar_id tvar_level kind =
   *   let rec f : T.kind -> _ = function
   *     | T.KVar {contents = T.KLink k} -> f k
   *     | T.KGenericVar _ -> assert false
   *     | T.KVar ({contents = T.KUnbound(other_id, other_level)} as other_tvar) ->
   *       if other_id = tvar_id then
   *         fail "Recursive types"
   *       else
   *         other_tvar := KUnbound(other_id, min tvar_level other_level)
   *     | T.Un _ | T.Aff _ | T.Lin _ -> ()
   *   in
   *   f kind
   * 
   * let rec unify k1 k2 = match k1, k2 with
   *   | _, _ when k1 == k2
   *     -> ()
   * 
   *   | T.Un r1, T.Un r2
   *   | T.Aff r1, T.Aff r2
   *   | T.Lin r1, T.Lin r2
   *     -> if T.Region.equal r1 r2 then () else raise (Fail (k1, k2))
   * 
   *   | T.KVar {contents = KUnbound(id1, _)},
   *     T.KVar {contents = KUnbound(id2, _)} when Name.equal id1 id2 ->
   *     (\* There is only a single instance of a particular type variable. *\)
   *     assert false
   * 
   *   | T.KVar {contents = KLink k1}, k2
   *   | k1, T.KVar {contents = KLink k2} -> unify k1 k2
   * 
   *   | T.KVar ({contents = KUnbound (id, level)} as tvar), ty
   *   | ty, T.KVar ({contents = KUnbound (id, level)} as tvar) ->
   *     adjust_levels id level ty ;
   *     tvar := KLink ty ;
   *     ()
   * 
   *   | _, T.KGenericVar _ | T.KGenericVar _, _ ->
   *     (\* Should always have been instantiated before *\)
   *     assert false
   * 
   *   | (T.Aff _ | T.Un _ | T.Lin _),
   *     (T.Aff _ | T.Un _ | T.Lin _)
   *     -> raise (Fail (k1, k2))
   *          
   *   
   * (\* TOFIX: Use an immutable reasonable representation. *\)
   * module K = struct
   *   (\* type t = Var of Name.t | Constant of Lat.t
   *    * let equal l1 l2 = match l1, l2 with
   *    *   | Var n1, Var n2 -> Name.equal n1 n2
   *    *   | Constant l1, Constant l2 -> Lat.equal l1 l2
   *    *   | _ -> false
   *    * let hash = Hashtbl.hash
   *    * let compare l1 l2 = if equal l1 l2 then 0 else compare l1 l2 *\)
   *   type t = T.kind
   *              
   *   let rec shorten = function
   *     | Types.KVar {contents = KLink k} -> shorten k
   *     | Types.Un _ | Types.Aff _ | Types.Lin _ | Types.KGenericVar _
   *     | Types.KVar {contents = KUnbound _} as k -> k
   * 
   *   let equal a b = shorten a = shorten b
   *   let hash x = Hashtbl.hash (shorten x)
   *   let compare a b = Pervasives.compare (shorten a) (shorten b)
   * 
   *   type constant = Lattice.t
   *   let rec classify = function
   *     | T.KVar { contents = KLink k } -> classify k
   *     | T.KVar { contents = KUnbound _ }
   *     | T.KGenericVar _ -> `Var
   *     | T.Lin r -> `Constant (Lattice.Lin r)
   *     | T.Aff r -> `Constant (Lattice.Aff r)
   *     | T.Un r -> `Constant (Lattice.Un r)
   *   let constant = function
   *     | Lattice.Lin r -> T.Lin r
   *     | Lattice.Aff r -> T.Aff r
   *     | Lattice.Un r -> T.Un r
   *   let unify = function
   *     | [] -> assert false
   *     | [ x ] -> x
   *     | h :: t -> List.fold_left (fun k1 k2 -> unify k1 k2; k1) h t
   * 
   * end *)
  
  include Lattice_solver.Make(Kinds.Lattice)(Kinds)

  let solve ?keep_vars c =
    try solve ?keep_vars c with
    | IllegalEdge (k1, k2) -> raise (Fail (Kinds.constant k1, Kinds.constant k2))
    | IllegalBounds (k1, v, k2) ->
      let env = Printer.create_naming_env () in
      fail "The kind inequality %a < %a < %a is not satisfiable."
        (Printer.kind env) (Kinds.constant k1)
        (Printer.kind env) v
        (Printer.kind env) (Kinds.constant k2)

end


(* module Simplification = struct
 *   open Variance
 * 
 *   module PosMap = struct
 *     type bimap = { ty : Variance.Map.t ; kind : variance Kind.Map.t }
 *     let empty = { ty = Variance.Map.empty ; kind = Kind.Map.empty }
 *     let add_ty m ty v =
 *       { m with ty = Variance.Map.add m.ty ty v }
 *     let add_kind m k v =
 *       let add m k v =
 *         Kind.Map.update
 *           k (function None -> Some v | Some v' -> Some (merge v v')) m
 *       in { m with kind = add m.kind k v }
 *     let add_kinds m k v =
 *       let f m set var =
 *         Kind.Set.fold (fun name m -> Kind.Map.add name var m) set m
 *       in { m with kind = f m.kind k v }
 *   end
 * 
 *   let rec collect_kind ~level ~variance map = function
 *     | T.KVar {contents = KUnbound(_, other_level)} as k
 *       when other_level > level ->
 *       PosMap.add_kind map k variance
 *     | T.KVar {contents = KLink ty} -> collect_kind ~level ~variance map ty
 *     | ( T.KGenericVar _
 *       | T.KVar {contents = KUnbound _}
 *       | T.Un _ | T.Aff _ | T.Lin _
 *       ) -> map
 *   
 *   let rec collect_type ~level ~variance map = function
 *     | T.GenericVar _ -> map
 *     | T.Var { contents = Link t } ->
 *       collect_type ~level ~variance map t
 *     | T.Var {contents = Unbound(name, other_level)} ->
 *       if other_level > level
 *       then PosMap.add_ty map name variance
 *       else map
 *     | T.App (_, args) ->
 *       List.fold_left (fun map t ->
 *           collect_type ~level ~variance:Invar map t
 *         ) map args
 *     | T.Arrow (ty1, k, ty2) ->
 *       let map = collect_type ~level ~variance:(neg variance) map ty1 in
 *       let map = collect_kind ~level ~variance map k in
 *       let map = collect_type ~level ~variance map ty2 in
 *       map
 *     | T.Tuple tys ->
 *       let aux map ty = collect_type ~level ~variance map ty in
 *       List.fold_left aux map tys
 *     | T.Borrow (_, k, ty) ->
 *       let map = collect_type ~level ~variance map ty in
 *       let map = collect_kind ~level ~variance map k in
 *       map
 * 
 *   
 *   let collect_kscheme ~level ~variance map = function
 *     | {T. kvars = []; constr = _; args = [] ; kind } ->
 *       collect_kind ~level ~variance map kind
 *     | ksch ->
 *       fail "Trying to generalize kinda %a. \
 *             This kind has already been generalized."
 *         Printer.kscheme ksch
 * 
 *   let collect_kschemes ~env ~level map =
 *     Name.Map.fold
 *       (fun ty variance map -> 
 *          collect_kscheme ~level ~variance map (Env.find_ty ty env))
 *       map.PosMap.ty map
 * 
 *   let go ~env ~level ~constr tys kinds =
 *     let map = PosMap.empty in
 *     let map =
 *       List.fold_left
 *         (fun map (k,variance) -> collect_kind ~level ~variance map k)
 *         map kinds
 *     in
 *     let map =
 *       List.fold_left (collect_type ~level ~variance:Pos) map tys
 *     in
 *     let map = collect_kschemes ~env ~level map in
 *     Kind.solve ~keep_vars:map.kind constr
 * end *)

module Collect = struct

  type t = {
    kindleq : LatSolve.G.t ;
    haskind : (T.typ * T.kind) list ;
  }

  let empty = {
    kindleq = LatSolve.G.empty ;
    haskind = [] ;
  }
  let kindleq c (k1,k2) =
    { c with kindleq = LatSolve.G.add_edge c.kindleq k1 k2 }
  let kindleqs c l = List.fold_left kindleq c l

  let haskind c (t,k) =
    { c with haskind = (t,k) :: c.haskind }
  let haskinds c l = List.fold_left haskind c l

  let rec normal c = function
    | Normal.KindLeq (k1,k2) -> kindleq c (k1,k2)
    | Normal.HasKind (t,k) -> haskind c (t,k)
    | And l -> List.fold_left normal c l

  let as_constraint { haskind ; kindleq } =
    let c = Normal.cand @@ List.map (fun (t,k) -> Normal.hasKind t k) haskind in
    LatSolve.G.fold_edges
      (fun k1 k2 l -> Normal.(cleq k1 k2 &&& l) )
      kindleq
      c
end


let desugar ~level ~env c =
  let rec aux acc = function
    | T.TypeLeq (t1, t2) ->
      Collect.normal acc @@ TypeLeq.mk ~level ~env t1 t2
    | T.KindLeq (k1, k2) ->
      Collect.normal acc @@ KindLeq.mk k1 k2
    | T.HasKind (ty, k) -> 
      Collect.normal acc @@ HasKind.mk ~level ~env ty k
    | T.And l ->
      List.fold_left aux acc l
  in
  aux Collect.empty c

let normalize ~level ~env l =
  let {Collect. haskind ; kindleq } = desugar ~level ~env @@ And l in
  let kindleq = LatSolve.solve kindleq in
  let t = {Collect. haskind ; kindleq } in
  Collect.as_constraint t

let rec denormalize : Normal.t -> T.constr = function
  | And l -> And (List.map denormalize l)
  | KindLeq (k1,k2) -> KindLeq (k1, k2)
  | HasKind (ty,k) -> HasKind (ty, k)

let ctrue : T.constr = And []
let cleq k1 k2 : T.constr = KindLeq (k1, k2)
let hasKind ty k : T.constr = HasKind (ty, k)
let (<=) a b : T.constr = KindLeq (a, b)
let (<==) a b : T.constr = T.TypeLeq (a, b)
let (&&&) c1 c2 : T.constr = And [c1;c2]

let rec flatten': T.constr -> T.constr list = function
  | And l -> flattenL l
  | c -> [c]
and flattenL l = CCList.flat_map flatten' l
let cand l : T.constr = match flattenL l with
  | [c] -> c
  | l -> And l
let flatten c = cand [c]
