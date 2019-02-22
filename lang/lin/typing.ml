open Syntax
module T = Types
module Region = T.Region
module C = Constraint
module Normal = Constraint.Normal


let fail fmt =
  Zoo.error ~kind:"Type error" fmt

let is_var = function
  | Var _ -> true
  | _ -> false

let rec is_nonexpansive = function
  | Constant _
  | Lambda _
  | Constructor _
  | Var _
  | Borrow _
  | Array []
    -> true
  | Tuple l
  | App (Constructor _, l) ->
    List.for_all is_nonexpansive l
  | Region e -> is_nonexpansive e
  | Let (_, e1, e2) ->
    is_nonexpansive e1 && is_nonexpansive e2
  | Match (_, _, e1, e2) ->
    is_nonexpansive e1 && is_nonexpansive e2
  | App (_, _)
  | Array _
    -> false

(** Instance *)
module Instantiate = struct

  let rec instance_kind ~level ~ktbl = function
    | T.KVar {contents = KLink k} as korig ->
      let knew = instance_kind ~level ~ktbl k in
      if korig = knew then korig else knew
    | T.KVar {contents = KUnbound _} as k -> k
    | T.KGenericVar id ->
      begin try
          snd @@ Hashtbl.find ktbl id
        with Not_found ->
          let name, var = T.kind ~name:id.name level in
          Hashtbl.add ktbl id (name, var) ;
          var
      end
    | T.Un _ | T.Aff _ as k -> k

  let rec instance_type ~level ~tbl ~ktbl = function
    | T.Var {contents = Link ty} -> instance_type ~level ~tbl ~ktbl ty
    | T.GenericVar id ->
      begin try
          snd @@ Hashtbl.find tbl id
        with Not_found ->
          let name, var = T.var ~name:id.name level in
          Hashtbl.add tbl id (name, var) ;
          var
      end
    | T.Var {contents = Unbound _} as ty -> ty
    | T.App(ty, args) ->
      let args = List.map (instance_type ~level ~tbl ~ktbl) args in
      App(ty, args)
    | T.Tuple args ->
      let args = List.map (instance_type ~level ~tbl ~ktbl) args in
      Tuple args
    | T.Borrow (r, k, ty) ->
      let k = instance_kind ~level ~ktbl k in
      let ty = instance_type ~level ~tbl ~ktbl ty in
      Borrow (r, k, ty)
    | T.Arrow(param_ty, k, return_ty) ->
      Arrow(instance_type ~level ~tbl ~ktbl param_ty,
            instance_kind ~level ~ktbl k,
            instance_type ~level ~tbl ~ktbl return_ty)


  let instance_constr ~level ~ktbl l =
    let f = instance_kind ~level ~ktbl in
    List.map (fun (k1,k2) -> (f k1, f k2)) l

  let kind_scheme ~level ~kargs ~ktbl {T. kvars; constr; args; kind } =
    let kl = List.length kargs and l = List.length args in
    if kl <> l then
      fail
        "This type constructor is applied to %i types \
         but has only %i parameters." l kl;
    let constr =
      List.fold_left2 (fun l k1 k2 -> (k1, k2) :: l)
        constr
        kargs
        args
    in
    let constr = instance_constr ~level ~ktbl constr in
    let kind = instance_kind ~level ~ktbl kind in
    assert (List.for_all (Hashtbl.mem ktbl) kvars) ;
    (constr, kind)

  let typ_scheme ~level ~env ~tbl ~ktbl {T. constr ; tyvars; kvars; ty } =
    let c = instance_constr ~level ~ktbl constr in
    let ty = instance_type ~level ~tbl ~ktbl ty in
    let env =
      List.fold_left
        (fun env (t,k) ->
           let ty = fst @@ Hashtbl.find tbl t in
           Env.add_ty ty (T.kscheme (instance_kind ~level ~ktbl k)) env)
        env
        tyvars
    in
    assert (List.for_all (Hashtbl.mem ktbl) kvars) ;
    assert (List.for_all (fun (k,_) -> Hashtbl.mem tbl k) tyvars) ;
    (env, c, ty)

  let constr level constr =
    let ktbl = Hashtbl.create 10 in
    instance_constr ~level ~ktbl constr
  let go_kind ?(args=[]) level k =
    let ktbl = Hashtbl.create 10 in
    kind_scheme ~level ~kargs:args ~ktbl k
  let go level env ty =
    let tbl = Hashtbl.create 10 in
    let ktbl = Hashtbl.create 10 in
    typ_scheme ~level ~env ~tbl ~ktbl ty

end
let instantiate = Instantiate.go

(** Unification *)
module Kind = struct

  exception Fail of T.kind * T.kind

  let did_unify_kind = ref false

  let adjust_levels tvar_id tvar_level kind =
    let rec f : T.kind -> _ = function
      | T.KVar {contents = T.KLink k} -> f k
      | T.KGenericVar _ -> assert false
      | T.KVar ({contents = T.KUnbound(other_id, other_level)} as other_tvar) ->
        if other_id = tvar_id then
          fail "Recursive types"
        else
          other_tvar := KUnbound(other_id, min tvar_level other_level)
      | T.Un _ | T.Aff _ -> ()
    in
    f kind

  let rec unify k1 k2 = match k1, k2 with
    | _, _ when k1 == k2
      -> ()

    | T.Un r1, T.Un r2
    | T.Aff r1, T.Aff r2
      -> if Region.equal r1 r2 then () else raise (Fail (k1, k2))

    | T.KVar {contents = KUnbound(id1, _)},
      T.KVar {contents = KUnbound(id2, _)} when Name.equal id1 id2 ->
      (* There is only a single instance of a particular type variable. *)
      assert false

    | T.KVar {contents = KLink k1}, k2
    | k1, T.KVar {contents = KLink k2} -> unify k1 k2

    | T.KVar ({contents = KUnbound (id, level)} as tvar), ty
    | ty, T.KVar ({contents = KUnbound (id, level)} as tvar) ->
      adjust_levels id level ty ;
      tvar := KLink ty ;
      did_unify_kind := true ;
      ()

    | _, T.KGenericVar _ | T.KGenericVar _, _ ->
      (* Should always have been instantiated before *)
      assert false

    | (T.Aff _ | T.Un _),
      (T.Aff _ | T.Un _)
      -> raise (Fail (k1, k2))

  module Lat = struct
    type t =
      | Un of Region.t
      | Aff of Region.t
    let (<) l1 l2 = match l1, l2 with
      | Aff r1, Aff r2 | Un r1, Un r2 -> Region.compare r1 r2 <= 0
      | _, Aff Never -> true
      | Un Global, _ -> true
      | Un r1, Aff r2 -> Region.equal r1 r2
      | _ -> false
    let (=) l1 l2 = match l1, l2 with
      | Aff r1, Aff r2 | Un r1, Un r2 -> Region.equal r1 r2
      | Un _, Aff _ 
      | Aff _, Un _ -> false
    let smallest = Un Region.smallest
    let biggest = Aff Region.biggest
    let max l1 l2 = match l1, l2 with
      | Un r1, Un r2 -> Un (Region.max r1 r2)
      | Aff r1, Aff r2 -> Aff (Region.max r1 r2)
      | Un _, (Aff _ as r) | (Aff _ as r), Un _ -> r
    let min l1 l2 = match l1, l2 with
      | Un r1, Un r2 -> Un (Region.min r1 r2)
      | Aff r1, Aff r2 -> Aff (Region.min r1 r2)
      | Aff _, (Un _ as r) | (Un _ as r), Aff _ -> r
    let least_upper_bound = List.fold_left min biggest
    let greatest_lower_bound = List.fold_left max smallest
    let relations consts =
      let consts = smallest :: biggest :: consts in
      CCList.product (fun l r -> l, r) consts consts
      |> CCList.filter (fun (l, r) -> l < r)
  end
    
  module K = struct
    (* type t = Var of Name.t | Constant of Lat.t
     * let equal l1 l2 = match l1, l2 with
     *   | Var n1, Var n2 -> Name.equal n1 n2
     *   | Constant l1, Constant l2 -> Lat.equal l1 l2
     *   | _ -> false
     * let hash = Hashtbl.hash
     * let compare l1 l2 = if equal l1 l2 then 0 else compare l1 l2 *)
    type t = T.kind
    let equal = Pervasives.(=)
    let hash = Hashtbl.hash
    let compare = Pervasives.compare

    type constant = Lat.t
    let classify = function
      | T.KVar _ | T.KGenericVar _ -> `Var
      | T.Aff r -> `Constant (Lat.Aff r)
      | T.Un r -> `Constant (Lat.Un r)
    let constant = function
      | Lat.Aff r -> T.Aff r
      | Lat.Un r -> T.Un r
    let unify = function
      | [] -> assert false
      | h :: t -> List.fold_left (fun k1 k2 -> unify k1 k2; k1) h t

  end
  include Constraint.Make(Lat)(K)

  let solve ?keep_vars c =
    try solve ?keep_vars c with
    | FailLattice (k1, k2) -> raise (Fail (k1, k2))
  let un = T.Un Global
  let aff = T.Aff Global
  let constr = Normal.cleq
  let first_class k = C.(k <= T.Aff Global)
end

(** Generalization *)
module Generalize = struct

  let neg = function `Pos -> `Neg | `Neg -> `Pos | `Invar -> `Invar
  let merge_var pos orig_pos = match orig_pos, pos with
    | None, (`Neg | `Pos | `Invar as pos) -> Some pos
    | Some `Pos, `Pos
    | Some `Neg, `Neg
    | Some `Invar, _ -> orig_pos
    | Some `Neg, `Pos
    | Some `Pos, `Neg
    | Some _, `Invar -> Some `Invar
  let update_kind ~kenv ~pos k =
    kenv := Kind.Map.update k (merge_var pos) !kenv
  let update_type ~tyenv ~pos k =
    tyenv := Name.Map.update k (merge_var pos) !tyenv
  
  let rec gen_kind ~level ~kenv ~pos = function
    | T.KVar {contents = KUnbound(id, other_level)} as k
      when other_level > level ->
      update_kind ~kenv ~pos k ;
      T.KGenericVar id
    | T.KVar {contents = KLink ty} -> gen_kind ~level ~kenv ~pos ty
    | ( T.KGenericVar _
      | T.KVar {contents = KUnbound _}
      | T.Un _ | T.Aff _
      ) as ty -> ty

  let rec gen_ty ~env ~level ~tyenv ~kenv ~pos = function
    | T.Var {contents = Unbound(id, other_level)} when other_level > level ->
      update_type ~tyenv ~pos id ;
      T.GenericVar id
    | T.App(ty, ty_args) ->
      App(ty, List.map (gen_ty ~env ~level ~tyenv ~kenv ~pos) ty_args)
    | T.Tuple ty_args ->
      Tuple (List.map (gen_ty ~env ~level ~tyenv ~kenv ~pos) ty_args)
    | T.Borrow (r, k, ty) ->
      Borrow (r, gen_kind ~level ~kenv ~pos k, gen_ty ~env ~level ~tyenv ~kenv ~pos ty)
    | T.Arrow(param_ty, k, return_ty) ->
      Arrow(gen_ty ~env ~level ~tyenv ~kenv ~pos:(neg pos) param_ty,
            gen_kind ~level ~kenv ~pos k,
            gen_ty ~env ~level ~tyenv ~kenv ~pos return_ty)
    | T.Var {contents = Link ty} -> gen_ty ~env ~level ~tyenv ~kenv ~pos ty
    | ( T.GenericVar _
      | T.Var {contents = Unbound _}
      ) as ty -> ty

  let gen_kscheme ~level ~kenv ~pos = function
    | {T. kvars = []; constr = []; args = [] ; kind } ->
      gen_kind ~level ~kenv ~pos kind
    | ksch ->
      fail "Trying to generalize kinda %a. \
            This kind has already been generalized."
        Printer.kscheme ksch

  let gen_kschemes ~env ~level ~kenv tyset =
    let get_kind (env : Env.t) id pos =
      gen_kscheme ~level ~kenv ~pos (Env.find_ty id env)
    in
    Name.Map.fold (fun ty pos l -> (ty, get_kind env ty pos)::l) tyset []

  let rec gen_constraint ~level = function
    | [] -> Normal.ctrue, Normal.ctrue
    | (k1, k2) :: rest ->
      let kenv = ref Kind.Map.empty in
      let k1 = gen_kind ~level ~kenv ~pos:`Pos k1 in
      let k2 = gen_kind ~level ~kenv ~pos:`Pos k2 in
      let constr = Normal.cleq k1 k2 in
      let c1, c2 =
        if Kind.Map.is_empty !kenv
        then constr, Normal.ctrue
        else Normal.ctrue, constr
      in
      let no_vars, vars = gen_constraint ~level rest in
      Normal.(c1 @ no_vars , c2 @ vars)

  let collect_gen_vars ~kenv l =
    let add_if_gen = function
      | T.KGenericVar _ as k ->
        update_kind ~kenv ~pos:`Pos k
      | _ -> ()
    in
    List.iter (fun (k1, k2) -> add_if_gen k1; add_if_gen k2) l

  let kinds_as_vars l =
    Name.Set.elements @@ T.Free_vars.kinds l
  
  let typ ~env ~level constr ty =
    let tyenv = ref Name.Map.empty in
    let kenv = ref Kind.Map.empty in

    (* We built the type skeleton and collect the kindschemes *)
    let ty = gen_ty ~env ~level ~tyenv ~kenv ~pos:`Pos ty in
    let tyvars = gen_kschemes ~env ~level ~kenv !tyenv in

    (* We simplify the constraints using the set of kind variables *)
    let constr = Kind.simplify ~keep_vars:!kenv constr in

    (* Split the constraints that are actually generalized *)
    let constr_no_var, constr = gen_constraint ~level constr in
    let constr_all = Normal.(constr_no_var @ constr) in

    collect_gen_vars ~kenv constr ;
    let kvars = kinds_as_vars @@ List.map fst @@ Kind.Map.bindings !kenv in
    let env = Name.Map.fold (fun ty _ env -> Env.rm_ty ty env) !tyenv env in

    env, constr_all, T.tyscheme ~constr ~tyvars ~kvars ty

  (** The real generalization function that is aware of the value restriction. *)
  let go env level constr ty exp =
    if is_nonexpansive exp then
      typ ~env ~level constr ty
    else
      env, constr, T.tyscheme ty

end
let generalize = Generalize.go

let rec infer_kind ~level ~env = function
  | T.App (f, args) ->
    let constrs, args = infer_kind_many ~level ~env args in
    let constr', kind =
      Instantiate.go_kind level ~args @@ Env.find_constr f env
    in
    Normal.(constr' @ constrs), kind
  | T.Tuple args ->
    let constrs, args = infer_kind_many ~level ~env args in
    let _, return_kind = T.kind ~name:"t" level in
    let constr_tup =
      Normal.cand @@ List.map (fun k -> Normal.cleq k return_kind) args
    in
    Normal.(constr_tup @ constrs), return_kind
  | T.Arrow (_, k, _) -> Normal.ctrue, k
  | T.GenericVar n -> Instantiate.go_kind level @@ Env.find_ty n env
  | T.Var { contents = T.Unbound (n, _) } ->
    Instantiate.go_kind level @@ Env.find_ty n env
  | T.Var { contents = T.Link ty } ->
    infer_kind ~level ~env ty
  | T.Borrow (Read, k, _) ->
    Normal.ctrue, k
  | T.Borrow (Write, k, _) ->
    Normal.ctrue, k

and infer_kind_many ~level ~env l = 
  List.fold_right
    (fun ty (constrs, args) ->
       let constr, k = infer_kind ~level ~env ty in
       Normal.(constr @ constrs) , k::args)
    l ([], [])

module Unif = struct

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

  let rec unify env ty1 ty2 = match ty1, ty2 with
    | _, _ when ty1 == ty2 -> Normal.ctrue

    | T.App(ty1, ty_arg1), T.App(ty2, ty_arg2) when Name.equal ty1 ty2 ->
      Normal.cand (List.map2 (unify env) ty_arg1 ty_arg2)

    | T.Borrow (r1, k1, ty1), T.Borrow (r2, k2, ty2) when r1 = r2 ->
      Normal.cand [
        unify env ty1 ty2 ;
        Kind.constr k1 k2 ;
      ]

    | T.Arrow(param_ty1, k1, return_ty1), T.Arrow(param_ty2, k2, return_ty2) ->
      Normal.cand [
        Kind.constr k1 k2;
        unify env param_ty2 param_ty1;
        unify env return_ty1 return_ty2;
      ]
    | T.Tuple tys1, Tuple tys2 ->
      List.flatten @@ List.map2 (unify env) tys1 tys2

    | T.Var {contents = Link ty1}, ty2 -> unify env ty1 ty2
    | ty1, T.Var {contents = Link ty2} -> unify env ty1 ty2

    | T.Var {contents = Unbound(id1, _)},
      T.Var {contents = Unbound(id2, _)} when id1 = id2 ->
      (* There is only a single instance of a particular type variable. *)
      assert false

    | (T.Var ({contents = Unbound(id, level)} as tvar) as ty1), (ty as ty2)
    | (ty as ty1), (T.Var ({contents = Unbound(id, level)} as tvar) as ty2) ->
      occurs_check_adjust_levels id level ty ;
      let constr1, k1 = infer_kind ~env ~level ty1 in
      let constr2, k2 = infer_kind ~env ~level ty2 in
      tvar := Link ty ;
      Normal.cand [constr1; constr2; Normal.cleq k1 k2 ; Normal.cleq k2 k1]

    | _, _ ->
      raise (Fail (ty1, ty2))

  let constr env t t' = unify env t t'

end

let normalize_constr env l =
  let rec unify_all = function
    | T.Eq (t, t') -> Unif.constr env t t'
    | T.KindLeq (k, k') -> Kind.constr k k'
    | T.And l -> Normal.cand (List.map unify_all l)
    | T.True -> Normal.ctrue
  in
  Kind.solve @@ unify_all (T.And l)

let normalize (env, constr, ty) = env, normalize_constr env [constr], ty

module Multiplicity = struct
  type use =
    | Shadow
    | Borrow of (T.Borrow.t * T.kind list)
    | Normal of T.kind list
  type t = use Name.Map.t
  let empty = Name.Map.empty
  let var x k = Name.Map.singleton x (Normal [k])
  let borrow x r k = Name.Map.singleton x (Borrow (r, [k]))

  exception Fail of use * use
  let fail u1 u2 = raise (Fail (u1, u2))

  let constr_all_kinds ~bound ks =
    List.map (fun k -> C.(k <= bound)) ks
  
  let merge (e1 : t) (e2 : t) =
    let constr = ref [] in
    let bound = T.Un Never in
    let constr_kinds ks =
      constr := (constr_all_kinds ~bound ks) @ !constr
    in
    let aux _x u1 u2 = match u1, u2 with
      | Shadow, u -> Some u
      | Borrow (r1, k1), Borrow (r2, k2) ->
        if T.Borrow.equal r1 r2 then
          Some (Borrow (r1, k1@k2))
        else
          fail u1 u2
      | Normal l1, Normal l2 ->
        let l = l1 @ l2 in
        constr_kinds l ;
        Some (Normal l)
      | _, Shadow
      | Borrow _, Normal _
      | Normal _, Borrow _ -> fail u1 u2
    in
    let m = Name.Map.union aux e1 e2 in
    m, C.cand !constr

  let constraint_all (e : t) bound : T.constr =
    let aux _ ks l = match ks with
      | Normal ks -> constr_all_kinds ~bound ks @ l
      | Borrow _ | Shadow -> []
    in
    let l = Name.Map.fold aux e [] in
    C.cand l
  let drop (e : t) x = Name.Map.remove x e

  let exit_scope (e : t) =
    let aux u = match u with
      | Borrow _ -> Shadow
      | _ -> u
    in
    Name.Map.map aux e

  let weaken (e : t) v k : T.constr =
    match Name.Map.find_opt v e with
    | Some Shadow
    | Some Borrow _
    | Some Normal [_]
      -> T.True
    | None | Some Normal [] | Some Normal _ ->
      C.(k <= T.Aff Never)
end


let constant_scheme = let open T in function
    | Int _ -> tyscheme Builtin.int
    | Plus  -> tyscheme Builtin.(int @-> int @-> int)
    | Alloc ->
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Kind.un] Builtin.(a @-> array a)
    | Free -> 
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Kind.un] Builtin.(array a @-> unit_ty)
    | Get ->
      let name, a = T.gen_var () in
      let kname, k = T.gen_kind_var () in
      let kname_borrow, k_borrow = T.gen_kind_var () in
      tyscheme
        ~kvars:[kname; kname_borrow]
        ~tyvars:[name, k]
        ~constr:[(k, T.Un Never)]
        Builtin.(Tuple [Borrow (Read, k_borrow, array a); int] @-> a )
    | Set ->
      let name, a = T.gen_var () in
      let kname, k = T.gen_kind_var () in
      let kname_borrow, k_borrow = T.gen_kind_var () in
      tyscheme
        ~kvars:[kname; kname_borrow]
        ~tyvars:[name, k]
        ~constr:[(k, T.Aff Never)]
        Builtin.(Tuple [Borrow (Write, k_borrow, array a); int; a] @-> unit_ty)
    | Y ->
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Kind.un] Builtin.((a @-> a) @-> a)

let constant level env c =
  let e, constr, ty =
    instantiate level env @@ constant_scheme c
  in
  Multiplicity.empty, e, constr, ty


let with_binding env x ty f =
  let env = Env.add x ty env in
  let multis, env, constr, ty = f env in
  let env = Env.rm x env in
  multis, env, constr, ty

let with_type ~name ~env ~level f =
  let var_name, ty = T.var ~name level in
  let _, kind = T.kind ~name level in
  let kind_scheme = T.kscheme kind in
  let env = Env.add_ty var_name kind_scheme env in
  f env ty kind

let rec infer (env : Env.t) level = function
  | Constant c -> constant level env c
  | Lambda(param, body_expr) ->
    let _, arrow_k = T.kind ~name:"a" level in
    with_type ~name:param.name ~env ~level @@ fun env param_ty param_kind ->
    let param_scheme = T.tyscheme param_ty in
    with_binding env param param_scheme @@ fun env ->
    let mults, env, constr, return_ty =
      infer env level body_expr
    in
    let constr = normalize_constr env [
        C.denormal constr;
        Multiplicity.constraint_all mults arrow_k;
        Multiplicity.weaken mults param param_kind;
      ]
    in
    Multiplicity.drop mults param, env, constr,
    T.Arrow (param_ty, arrow_k, return_ty)
  | Array elems -> 
    with_type ~name:"v" ~level ~env @@ fun env array_ty _ ->
    let mults, env, constrs, tys = 
      infer_many env level Multiplicity.empty elems
    in 
    let f elem_ty = C.(elem_ty === array_ty) in
    let elem_constr = CCList.map f tys in
    let constr = normalize_constr env [
        constrs ;
        C.cand elem_constr ;
      ]
    in
    mults, env, constr, Builtin.array array_ty
  | Tuple elems -> 
    let mults, env, constrs, tys =
      infer_many env level Multiplicity.empty elems
    in
    let constr = normalize_constr env [
        constrs ;
      ]
    in
    mults, env, constr, T.Tuple tys
  | Constructor name ->
    let env, constr1, t = instantiate level env @@ Env.find name env in
    let constr2, k = infer_kind ~level ~env t in
    assert (k = Kind.un) ;
    let constr = normalize_constr env [C.denormal constr1; C.denormal constr2] in
    Multiplicity.empty, env, constr, t

  | Var name ->
    let (name, k), env, constr, ty = infer_var env level name in
    Multiplicity.var name k, env, constr, ty

  | Borrow (r, name) ->
    let _, borrow_k = T.kind ~name:"b" level in
    let (name, _), env, constr, borrow_ty = infer_var env level name in
    let mults = Multiplicity.borrow name r borrow_k in
    mults, env, constr, T.Borrow (r, borrow_k, borrow_ty)

  | Let(var_name, value_expr, body_expr) ->
    let mults1, env, var_constr, var_ty =
      infer env (level + 1) value_expr
    in
    let env, generalized_constr, generalized_scheme =
      generalize env level var_constr var_ty value_expr
    in
    with_binding env var_name generalized_scheme @@ fun env ->
    let mults2, env, body_constr, body_ty = infer env level body_expr in
    let mults, constr_merge = Multiplicity.merge mults1 mults2 in
    let constr = normalize_constr env [
        C.denormal @@ Instantiate.constr level generalized_constr ;
        C.denormal body_constr ;
        constr_merge ;
      ]
    in
    mults, env, constr, body_ty
  | Match(constructor, param_name, expr, body) ->
    let mults1, env, expr_constr, expr_ty =
      infer env (level + 1) expr
    in
    let env, constructor_constr, constructor_ty =
      instantiate level env @@ Env.find constructor env
    in
    let param_ty, output_ty = match constructor_ty with
      | Types.Arrow (ty1, T.Un Global, ty2) -> ty1, ty2
      | _ -> assert false
    in
    let constr = normalize_constr env [
         C.(expr_ty === output_ty) ;
        C.denormal expr_constr ;
        C.denormal constructor_constr ;
      ]
    in
    let env, generalized_constr, generalized_scheme =
      generalize env level expr_constr param_ty (Var param_name)
    in
    with_binding env param_name generalized_scheme @@ fun env ->
    let mults2, env, body_constr, body_ty = infer env level body in
    let mults, constr_merge = Multiplicity.merge mults1 mults2 in
    let constr = normalize_constr env [
        C.denormal constr ;
        C.denormal @@ Instantiate.constr level generalized_constr ;
        C.denormal body_constr ;
        constr_merge ;
      ]
    in
    mults, env, constr, body_ty
  | App(fn_expr, arg) ->
    infer_app env level fn_expr arg

  | Region expr ->
    with_type ~name:"r" ~env ~level @@ fun env return_ty return_kind ->
    let mults, env, constr, infered_ty = infer env level expr in
    let mults = Multiplicity.exit_scope mults in 
    let constr = normalize_constr env [
        C.denormal constr;
        C.(return_ty === infered_ty);
        Kind.first_class return_kind;
      ]
    in
    mults, env, constr, return_ty

and infer_var env level name =
  let env, constr1, t = instantiate level env @@ Env.find name env in
  let constr2, k = infer_kind ~level ~env t in
  let constr = normalize_constr env [C.denormal constr1; C.denormal constr2] in
  (name, k), env, constr, t

and infer_many (env : Env.t) level mult l =
  let rec aux mults0 env0 constr0 tys = function
    | [] -> (mults0, env0, constr0, List.rev tys)
    | expr :: rest ->
      let mults, env, constr, ty = infer env level expr in
      let mults, constr_merge = Multiplicity.merge mults mults0 in
      let constr = C.cand [
          C.denormal constr;
          constr0;
          constr_merge;
        ]
      in
      aux mults env constr (ty :: tys) rest
  in aux mult env True [] l

and infer_app (env : Env.t) level fn_expr args =
  let f (f_ty, env) param_ty =
    let _, k = T.kind ~name:"a" level in
    with_type ~name:"a" ~level ~env @@ fun env return_ty _ ->
    let constr = C.(T.Arrow (param_ty, k, return_ty) === f_ty) in
    (return_ty, env), constr
  in
  let mults, env, fn_constr, fn_ty = infer env level fn_expr in
  let mults, env, arg_constr, tys = infer_many env level mults args in
  let (return_ty, env), app_constr = CCList.fold_map f (fn_ty, env) tys in
  let constr = normalize_constr env [
      C.denormal fn_constr ;
      arg_constr ;
      C.cand app_constr ;
    ]
  in
  mults, env, constr, return_ty

let infer_top env0 e =
  let _, env, constr, ty = infer env0 1 e in
  let env, constr, scheme = generalize env 0 constr ty e in

  (* Check that the residual constraints are satisfiable. *)
  let constr = normalize_constr env [C.denormal @@ Instantiate.constr 0 constr] in

  (* Remove unused variables in the environment *)
  let free_vars =
    Name.Map.fold
      (fun _ sch e -> Name.Set.union e @@ T.Free_vars.scheme sch)
      env.vars
      (T.Free_vars.scheme scheme)
  in
  let env = Env.filter_ty (fun n _ -> Name.Set.mem n free_vars) env in

  (* assert (constr = C.True) ; *)
  constr, env, scheme
