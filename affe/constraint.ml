module T = Types

let fail fmt =
  Zoo.error ~kind:"Type error" fmt

module Normal = struct

  type t = T.normalized_constr =
    | KindLeq of T.kind * T.kind
    | HasKind of Name.t * T.typ * T.kind
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
  let hasKind n ty k : t = HasKind (n, ty, k)
  let (<=) a b : t = KindLeq (a, b)
  let (&&&) c1 c2 : t = And [c1;c2]
  let (=~) a b : t = (a <= b) &&& (b <= a)

end

module KindLeq = struct

  let mk k1 k2 = Normal.KindLeq (k1, k2)

end

module HasKind = struct

  let rec constraint_kind ~level ~env typ expected_kind = match typ with
    | T.App (f, args) ->
      (* TODO This assumes everything is covariant, which is wrong *)
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
        Normal.cand @@ List.map (fun k -> Normal.(k <= expected_kind)) ks
      in
      Normal.(constr_tup &&& constrs)
    | T.Arrow (_, k, _) ->
      Normal.(k =~ expected_kind)
    | T.Borrow (_, k, _) ->
      Normal.(k =~ expected_kind)
    | T.GenericVar _ ->
      assert false
    | T.Var { contents = T.Unbound (id, _) } ->
      Normal.hasKind id typ expected_kind
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
        if Name.equal other_id tvar_id then
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
      T.Var {contents = Unbound(id2, _)} when Name.equal id1 id2 ->
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

module KindUnif = struct
  include Kinds
      
  exception Fail of T.kind * T.kind

  let adjust_levels tvar_id tvar_level kind =
    let rec f : kind -> _ = function
      | Var {contents = Link k} -> f k
      | GenericVar _ -> assert false
      | Var ({contents = Unbound(other_id, other_level)} as other_tvar) ->
        if Name.equal other_id tvar_id then
          fail "Recursive types"
        else
          other_tvar := Unbound(other_id, min tvar_level other_level)
      | Un _ | Aff _ | Lin _ -> ()
    in
    f kind

  let rec unify k1 k2 = match k1, k2 with
    | _, _ when k1 == k2
      -> ()

    | Un r1, Un r2
    | Aff r1, Aff r2
    | Lin r1, Lin r2
      -> if Region.equal r1 r2 then () else raise (Fail (k1, k2))

    | Var {contents = Unbound(id1, _)},
      Var {contents = Unbound(id2, _)} when Name.equal id1 id2 ->
      (* There is only a single instance of a particular type variable. *)
      assert false

    | Var {contents = Link k1}, k2
    | k1, Var {contents = Link k2} -> unify k1 k2

    | Var ({contents = Unbound (id, level)} as tvar), ty
    | ty, Var ({contents = Unbound (id, level)} as tvar) ->
      adjust_levels id level ty ;
      tvar := Link ty ;
      ()

    | _, GenericVar _ | GenericVar _, _ ->
      (* Should always have been instantiated before *)
      assert false

    | (Aff _ | Un _ | Lin _),
      (Aff _ | Un _ | Lin _)
      -> raise (Fail (k1, k2))

  let unify = function
    | [] -> assert false
    | [ x ] -> x
    | h :: t -> List.fold_left (fun k1 k2 -> unify k1 k2; Kinds.repr k1) h t
end

module Solver = struct
  
  include Lattice_solver.Make(Kinds.Lattice)(KindUnif)

  let solve ?keep_vars c =
    try solve ?keep_vars c with
    | IllegalEdge (k1, k2) ->
      raise (KindUnif.Fail (Kinds.constant k1, Kinds.constant k2))
    | IllegalBounds (k1, v, k2) ->
      let env = Printer.create_naming_env () in
      fail "The kind inequality %a < %a < %a is not satisfiable."
        (Printer.kind env) (Kinds.constant k1)
        (Printer.kind env) v
        (Printer.kind env) (Kinds.constant k2)

end

module Collect = struct

  type t = {
    kindleq : Solver.G.t ;
    haskind : (T.typ * T.kind list) Name.Map.t ;
  }

  let empty = {
    kindleq = Solver.G.empty ;
    haskind = Name.Map.empty ;
  }
  let kindleq c (k1,k2) =
    { c with kindleq = Solver.G.add_edge c.kindleq k1 k2 }
  let kindleqs c l = List.fold_left kindleq c l

  let haskind c (n,t,k) =
    let haskind = Name.Map.update n (function
        | None -> Some (Types.repr t,[k])
        | Some (t',ks) ->
          assert (CCEqual.physical t (Types.repr t'));
          Some (t, k::ks))
        c.haskind
    in
    {c with haskind }
  let haskinds c l = List.fold_left haskind c l

  let rec normal c = function
    | Normal.KindLeq (k1,k2) -> kindleq c (k1,k2)
    | Normal.HasKind (id,t,k) -> haskind c (id,t,k)
    | And l -> List.fold_left normal c l

  let desugar ~level ~env (c : T.constr) =
    let rec aux acc = function
      | T.TypeLeq (t1, t2) ->
        normal acc @@ TypeLeq.mk ~level ~env t1 t2
      | T.KindLeq (k1, k2) ->
        normal acc @@ KindLeq.mk k1 k2
      | T.HasKind (ty, k) -> 
        normal acc @@ HasKind.mk ~level ~env ty k
      | T.And l ->
        List.fold_left aux acc l
    in
    aux empty c

  let from_normal ~level ~env (c : T.normalized_constr) =
    let rec aux acc = function
      | T.KindLeq (k1, k2) ->
        normal acc @@ KindLeq.mk k1 k2
      | T.HasKind (_, ty, k) -> 
        normal acc @@ HasKind.mk ~level ~env ty k
      | T.And l ->
        List.fold_left aux acc l
    in
    aux empty c 

end

let extract {Collect. haskind ; kindleq } =
  let add_cycle g0 l0 =
    let rec add_edges g = function
      | [] | [_] -> g
      | k1::k2::l -> add_edges (Solver.G.add_edge g k1 k2) (k2::l)
    in
    match l0 with 
      | [] -> g0
      | [k] -> Solver.G.add_vertex g0 k
      | k::_ -> add_edges g0 (l0@[k])
  in
  let kinds_clusters, remaining_haskind =
    let aux n (t,ks) (ls, cstrs) =
      (ks::ls, (n,t,ks)::cstrs)
    in
    Name.Map.fold aux haskind ([],[])
  in
  let g =
    List.fold_left add_cycle kindleq kinds_clusters
  in
  g, remaining_haskind

let normalize ~level ~env l =
  let t = Collect.desugar ~level ~env @@ And l in
  let g, haskind_raw = extract t in
  let g = Solver.solve g in
  let kindleq_constr =
    Normal.cand @@
    Solver.G.fold_edges (fun k1 k2 l -> Normal.(k1 <= k2) :: l) g []      
  in
  let haskind_constr =
    Normal.cand @@
    List.map (fun (n,t,k) -> Normal.hasKind n t @@ List.hd k) haskind_raw
  in
  Normal.(kindleq_constr &&& haskind_constr)

module Simplification = struct
  open Variance

  module PosMap = struct
    type bimap = {
      ty : Variance.Map.t ;
      kind : (Kinds.t * variance) Name.Map.t ;
    }
    let empty = { ty = Variance.Map.empty ; kind = Name.Map.empty }
    let get_ty m ty = Variance.Map.get m.ty ty
    let mem_ty m ty = Variance.Map.mem m.ty ty
    let mem_kind m k = Name.Map.mem k m.kind
    let add_ty m ty v =
      { m with ty = Variance.Map.add m.ty ty v }
    let add_kind m n k v =
      let newkindmap =
        Name.Map.update
          n (function None -> Some (k,v) | Some (k,v') -> Some (k,merge v v'))
          m.kind
      in { m with kind = newkindmap }
    let add_kinds m k v =
      let f m set var =
        Name.Set.fold (fun name m -> Name.Map.add name var m) set m
      in { m with kind = f m.kind k v }
  end

  let rec collect_kind ~level ~variance map = function
    | Kinds.Var {contents = Unbound(n, other_level)} as k
      when other_level > level ->
      PosMap.add_kind map n k variance
    | Var {contents = Link ty} -> collect_kind ~level ~variance map ty
    | ( GenericVar _
      | Var {contents = Unbound _}
      | Un _ | Aff _ | Lin _
      ) -> map
  
  let rec collect_type ~level ~variance map = function
    | T.GenericVar _ -> map
    | T.Var { contents = Link t } ->
      collect_type ~level ~variance map t
    | T.Var {contents = Unbound(name, other_level)} ->
      if other_level > level
      then PosMap.add_ty map name variance
      else map
    | T.App (_, args) ->
      List.fold_left (fun map t ->
          collect_type ~level ~variance:Invar map t
        ) map args
    | T.Arrow (ty1, k, ty2) ->
      let map = collect_type ~level ~variance:(neg variance) map ty1 in
      let map = collect_kind ~level ~variance map k in
      let map = collect_type ~level ~variance map ty2 in
      map
    | T.Tuple tys ->
      let aux map ty = collect_type ~level ~variance map ty in
      List.fold_left aux map tys
    | T.Borrow (_, k, ty) ->
      let map = collect_type ~level ~variance map ty in
      let map = collect_kind ~level ~variance map k in
      map

  let collect_haskinds ~level map l =
    let f map (n, _ty, ks) =
      if PosMap.mem_ty map n then 
        List.fold_left
          (collect_kind ~level ~variance:(PosMap.get_ty map n)) map ks
      else
        map
    in
    List.fold_left f map l
  
  let collect ~env:_ ~level tys kinds haskinds =
    let map = PosMap.empty in
    let map =
      List.fold_left
        (fun map (k,variance) -> collect_kind ~level ~variance map k)
        map kinds
    in
    let map =
      List.fold_left (collect_type ~level ~variance:Pos) map tys
    in
    let map = collect_haskinds ~level map haskinds in      
    map
end

let simplify ~level ~env l tys kinds =
  let t = Collect.from_normal ~level ~env @@ And l in
  let g, haskind_raw = extract t in
  let posmap = Simplification.collect ~level ~env tys kinds haskind_raw in
  let g = Solver.solve ~keep_vars:posmap.kind g in
  let kindleq_constr =
    Normal.cand @@
    Solver.G.fold_edges (fun k1 k2 l -> Normal.(k1 <= k2) :: l) g []      
  in
  let haskind_constr =
    let is_relevant_constr n k =
      let is_relevant_type = Simplification.PosMap.mem_ty posmap n in
      let is_relevant_kind = Simplification.PosMap.mem_ty posmap n in
      let is_kindconst =
          match Kinds.classify k with
          | `Var _ -> false
          | `Constant _ -> true
      in
      let constrained_kindvar =
        match Kinds.classify k with
        | `Var _ ->
          Solver.G.mem_vertex g k &&
          Solver.G.out_degree g k + Solver.G.in_degree g k > 0
        | `Constant _ -> false
      in
      is_relevant_type && (is_relevant_kind || is_kindconst) || constrained_kindvar
    in
    Normal.cand @@
    CCList.filter_map
      (fun (n,t,ks) ->
         let k = List.hd ks in
         if is_relevant_constr n k
         then Some (Normal.hasKind n t k)
         else None
      )
      haskind_raw
  in
  Normal.(haskind_constr &&& kindleq_constr)

let rec denormalize : Normal.t -> T.constr = function
  | And l -> And (List.map denormalize l)
  | KindLeq (k1,k2) -> KindLeq (k1, k2)
  | HasKind (_,ty,k) -> HasKind (ty, k)

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
