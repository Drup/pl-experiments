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

  let instance_kvar ~level ~ktbl id =
    try
      Name.Tbl.find ktbl id
    with Not_found ->
      let b = T.kind ~name:id.name level in
      Name.Tbl.add ktbl id b ;
      b
  let instance_tyvar ~level ~tbl id =
    try
      Name.Tbl.find tbl id
    with Not_found ->
      let b = T.var ~name:id.name level in
      Name.Tbl.add tbl id b ;
      b

  let rec instance_kind ~level ~ktbl = function
    | T.KVar {contents = KLink k} as korig ->
      let knew = instance_kind ~level ~ktbl k in
      if korig = knew then korig else knew
    | T.KVar {contents = KUnbound _} as k -> k
    | T.KGenericVar id -> snd @@ instance_kvar ~level ~ktbl id
    | T.Un _ | T.Aff _ | T.Lin _ as k -> k

  let rec instance_type ~level ~tbl ~ktbl = function
    | T.Var {contents = Link ty} -> instance_type ~level ~tbl ~ktbl ty
    | T.GenericVar id -> snd @@ instance_tyvar ~level ~tbl id
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

  let included tbl vars = 
    Name.Tbl.keys tbl
    |> Sequence.for_all
      (fun x -> CCList.mem ~eq:Name.equal x vars)

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
    assert (included ktbl kvars);
    (constr, kind)

  let typ_scheme ~level ~env ~tbl ~ktbl {T. constr ; tyvars; kvars; ty } =
    let c = instance_constr ~level ~ktbl constr in
    let ty = instance_type ~level ~tbl ~ktbl ty in
    let env =
      List.fold_left
        (fun env (t,k) ->
           let ty = fst @@ Name.Tbl.find tbl t in
           let kind = T.kscheme (instance_kind ~level ~ktbl k) in
           Env.add_ty ty kind env)
        env
        tyvars
    in
    assert (included ktbl kvars);
    assert (included tbl @@ List.map fst tyvars);
    (env, c, ty)

  let go_constr level constr =
    let ktbl = Name.Tbl.create 10 in
    instance_constr ~level ~ktbl constr
  let go_kscheme ?(args=[]) level k =
    let ktbl = Name.Tbl.create 10 in
    kind_scheme ~level ~kargs:args ~ktbl k
  let go level env ty =
    let tbl = Name.Tbl.create 10 in
    let ktbl = Name.Tbl.create 10 in
    typ_scheme ~level ~env ~tbl ~ktbl ty

end
let instantiate = Instantiate.go

(** Unification *)
module Kind = struct

  exception Fail of T.kind * T.kind

  let adjust_levels tvar_id tvar_level kind =
    let rec f : T.kind -> _ = function
      | T.KVar {contents = T.KLink k} -> f k
      | T.KGenericVar _ -> assert false
      | T.KVar ({contents = T.KUnbound(other_id, other_level)} as other_tvar) ->
        if other_id = tvar_id then
          fail "Recursive types"
        else
          other_tvar := KUnbound(other_id, min tvar_level other_level)
      | T.Un _ | T.Aff _ | T.Lin _ -> ()
    in
    f kind

  let rec unify k1 k2 = match k1, k2 with
    | _, _ when k1 == k2
      -> ()

    | T.Un r1, T.Un r2
    | T.Aff r1, T.Aff r2
    | T.Lin r1, T.Lin r2
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
      ()

    | _, T.KGenericVar _ | T.KGenericVar _, _ ->
      (* Should always have been instantiated before *)
      assert false

    | (T.Aff _ | T.Un _ | T.Lin _),
      (T.Aff _ | T.Un _ | T.Lin _)
      -> raise (Fail (k1, k2))

  (* let unify k1 k2 =
   *   Format.eprintf "Unifying %a and %a@." Printer.kind k1 Printer.kind k2 ;
   *   unify k1 k2 *)
  
  module Lat = struct
    type t =
      | Un of Region.t
      | Aff of Region.t
      | Lin of Region.t
    let (<) l1 l2 = match l1, l2 with
      | Lin r1, Lin r2
      | Aff r1, Aff r2
      | Un r1, Un r2 -> Region.compare r1 r2 <= 0
      | _, Lin Never -> true
      | Un Global, _ -> true
      | Un r1, Aff r2 | Un r1, Lin r2 | Aff r1, Lin r2 -> Region.equal r1 r2
      | _ -> false
    let (=) l1 l2 = match l1, l2 with
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
    let relations consts =
      let consts = smallest :: biggest :: consts in
      CCList.product (fun l r -> l, r) consts consts
      |> CCList.filter (fun (l, r) -> l < r)
  end
    
  (* TOFIX: Use an immutable reasonable representation. *)
  module K = struct
    (* type t = Var of Name.t | Constant of Lat.t
     * let equal l1 l2 = match l1, l2 with
     *   | Var n1, Var n2 -> Name.equal n1 n2
     *   | Constant l1, Constant l2 -> Lat.equal l1 l2
     *   | _ -> false
     * let hash = Hashtbl.hash
     * let compare l1 l2 = if equal l1 l2 then 0 else compare l1 l2 *)
    type t = T.kind
               
    let rec shorten = function
      | Types.KVar {contents = KLink k} -> shorten k
      | Types.Un _ | Types.Aff _ | Types.Lin _ | Types.KGenericVar _
      | Types.KVar {contents = KUnbound _} as k -> k

    let equal a b = shorten a = shorten b
    let hash x = Hashtbl.hash (shorten x)
    let compare a b = Pervasives.compare (shorten a) (shorten b)

    type constant = Lat.t
    let rec classify = function
      | T.KVar { contents = KLink k } -> classify k
      | T.KVar { contents = KUnbound _ }
      | T.KGenericVar _ -> `Var
      | T.Lin r -> `Constant (Lat.Lin r)
      | T.Aff r -> `Constant (Lat.Aff r)
      | T.Un r -> `Constant (Lat.Un r)
    let constant = function
      | Lat.Lin r -> T.Lin r
      | Lat.Aff r -> T.Aff r
      | Lat.Un r -> T.Un r
    let unify = function
      | [] -> assert false
      | [ x ] -> x
      | h :: t -> List.fold_left (fun k1 k2 -> unify k1 k2; k1) h t

  end
  include Constraint.Make(Lat)(K)

  let solve ?keep_vars c =
    try solve ?keep_vars c with
    | FailLattice (k1, k2) -> raise (Fail (k1, k2))

  (* let solve ?keep_vars l =
   *   Format.eprintf "@[<2>Solving:@ %a@]@."
   *     Printer.constrs l ;
   *   let l' = solve ?keep_vars l in
   *   Format.eprintf "@[<2>To:@ %a@]@."
   *     Printer.constrs l' ;
   *   l' *)
  
  let un = T.Un Global
  let aff = T.Aff Global
  let constr = Normal.cleq
  let first_class k = C.(k <= T.Aff Global)
end

module Simplification = struct
  open Variance

  module PosMap = struct
    type bimap = { ty : Variance.Map.t ; kind : variance Kind.Map.t }
    let empty = { ty = Variance.Map.empty ; kind = Kind.Map.empty }
    let add_ty m ty v =
      { m with ty = Variance.Map.add m.ty ty v }
    let add_kind m k v =
      let add m k v =
        Kind.Map.update
          k (function None -> Some v | Some v' -> Some (merge v v')) m
      in { m with kind = add m.kind k v }
    let add_kinds m k v =
      let f m set var =
        Kind.Set.fold (fun name m -> Kind.Map.add name var m) set m
      in { m with kind = f m.kind k v }
  end

  let rec collect_kind ~level ~variance map = function
    | T.KVar {contents = KUnbound(_, other_level)} as k
      when other_level > level ->
      PosMap.add_kind map k variance
    | T.KVar {contents = KLink ty} -> collect_kind ~level ~variance map ty
    | ( T.KGenericVar _
      | T.KVar {contents = KUnbound _}
      | T.Un _ | T.Aff _ | T.Lin _
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
      (* TOFIX : This assumes that constructors are covariant. This is wrong *)
      List.fold_left (fun map t ->
          collect_type ~level ~variance map t
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

  
  let collect_kscheme ~level ~variance map = function
    | {T. kvars = []; constr = []; args = [] ; kind } ->
      collect_kind ~level ~variance map kind
    | ksch ->
      fail "Trying to generalize kinda %a. \
            This kind has already been generalized."
        Printer.kscheme ksch

  let collect_kschemes ~env ~level map =
    Name.Map.fold
      (fun ty variance map -> 
         collect_kscheme ~level ~variance map (Env.find_ty ty env))
      map.PosMap.ty map

  let go ~env ~level ~constr tys kinds =
    let map = PosMap.empty in
    let map =
      List.fold_left
        (fun map (k,variance) -> collect_kind ~level ~variance map k)
        map kinds
    in
    let map =
      List.fold_left (collect_type ~level ~variance:Pos) map tys
    in
    let map = collect_kschemes ~env ~level map in
    Kind.solve ~keep_vars:map.kind constr
end

(** Generalization *)
module Generalize = struct

  let update_kind ~kenv k =
    kenv := Kind.Set.add k !kenv
  let update_type ~tyenv k =
    tyenv := Name.Set.add k !tyenv
  
  let rec gen_kind ~level ~kenv = function
    | T.KVar {contents = KUnbound(id, other_level)} as k
      when other_level > level ->
      update_kind ~kenv k ;
      T.KGenericVar id
    | T.KVar {contents = KLink ty} -> gen_kind ~level ~kenv ty
    | ( T.KGenericVar _
      | T.KVar {contents = KUnbound _}
      | T.Un _ | T.Aff _ | T.Lin _
      ) as ty -> ty

  let rec gen_ty ~env ~level ~tyenv ~kenv = function
    | T.Var {contents = Unbound(id, other_level)} when other_level > level ->
      update_type ~tyenv id ;
      T.GenericVar id
    | T.App(ty, ty_args) ->
      App(ty, List.map (gen_ty ~env ~level ~tyenv ~kenv) ty_args)
    | T.Tuple ty_args ->
      Tuple (List.map (gen_ty ~env ~level ~tyenv ~kenv) ty_args)
    | T.Borrow (r, k, ty) ->
      Borrow (r, gen_kind ~level ~kenv k, gen_ty ~env ~level ~tyenv ~kenv ty)
    | T.Arrow(param_ty, k, return_ty) ->
      Arrow(gen_ty ~env ~level ~tyenv ~kenv param_ty,
            gen_kind ~level ~kenv k,
            gen_ty ~env ~level ~tyenv ~kenv return_ty)
    | T.Var {contents = Link ty} -> gen_ty ~env ~level ~tyenv ~kenv ty
    | ( T.GenericVar _
      | T.Var {contents = Unbound _}
      ) as ty -> ty

  let gen_kscheme ~level ~kenv = function
    | {T. kvars = []; constr = []; args = [] ; kind } ->
      gen_kind ~level ~kenv kind
    | ksch ->
      fail "Trying to generalize kinda %a. \
            This kind has already been generalized."
        Printer.kscheme ksch

  let gen_kschemes ~env ~level ~kenv tyset =
    let get_kind (env : Env.t) id =
      gen_kscheme ~level ~kenv (Env.find_ty id env)
    in
    Name.Set.fold (fun ty l -> (ty, get_kind env ty)::l) tyset []

  let rec gen_constraint ~level = function
    | [] -> Normal.ctrue, Normal.ctrue
    | (k1, k2) :: rest ->
      let kenv = ref Kind.Set.empty in
      let k1 = gen_kind ~level ~kenv k1 in
      let k2 = gen_kind ~level ~kenv k2 in
      let constr = Normal.cleq k1 k2 in
      let c1, c2 =
        if Kind.Set.is_empty !kenv
        then constr, Normal.ctrue
        else Normal.ctrue, constr
      in
      let no_vars, vars = gen_constraint ~level rest in
      Normal.(c1 @ no_vars , c2 @ vars)

  let collect_gen_vars ~kenv l =
    let add_if_gen = function
      | T.KGenericVar _ as k ->
        update_kind ~kenv k
      | _ -> ()
    in
    List.iter (fun (k1, k2) -> add_if_gen k1; add_if_gen k2) l

  let kinds_as_vars l =
    Name.Set.elements @@ T.Free_vars.kinds l

  let typ ~env ~level constr ty =
    let constr = Simplification.go ~env ~level ~constr [ty] [] in

    let tyenv = ref Name.Set.empty in
    let kenv = ref Kind.Set.empty in

    (* We built the type skeleton and collect the kindschemes *)
    let ty = gen_ty ~env ~level ~tyenv ~kenv ty in
    let tyvars = gen_kschemes ~env ~level ~kenv !tyenv in

    (* Split the constraints that are actually generalized *)
    let constr_no_var, constr = gen_constraint ~level constr in
    let constr_all = Normal.(constr_no_var @ constr) in

    collect_gen_vars ~kenv constr ;
    let kvars = kinds_as_vars @@ Kind.Set.elements !kenv in
    let env = Name.Set.fold (fun ty env -> Env.rm_ty ty env) !tyenv env in

    env, constr_all, T.tyscheme ~constr ~tyvars ~kvars ty

  
  let kind ~env ~level constr args k =
    let constr =
      let l = List.map (fun k -> (k, Variance.Neg)) args @ [k, Variance.Pos] in
      Simplification.go ~env ~level ~constr [] l
    in

    let tyenv = ref Name.Set.empty in
    let kenv = ref Kind.Set.empty in

    (* We built the type skeleton and collect the kindschemes *)
    let k = gen_kind ~level ~kenv k in
    let args = List.map (gen_kind ~level ~kenv) args in

    (* Split the constraints that are actually generalized *)
    let constr_no_var, constr = gen_constraint ~level constr in
    let constr_all = Normal.(constr_no_var @ constr) in

    collect_gen_vars ~kenv constr ;
    let kvars = kinds_as_vars @@ Kind.Set.elements !kenv in
    let env = Name.Set.fold (fun ty env -> Env.rm_ty ty env) !tyenv env in

    env, constr_all,
    T.kscheme ~constr ~kvars ~args k

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
      Instantiate.go_kscheme level ~args @@ Env.find_constr f env
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
  | T.GenericVar n -> Instantiate.go_kscheme level @@ Env.find_ty n env
  | T.Var { contents = T.Unbound (n, _) } ->
    Instantiate.go_kscheme level @@ Env.find_ty n env
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
        Kind.constr k1 k2 ;
        unify env ty1 ty2 ;
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
      Normal.cand [constr1; constr2; Kind.constr k1 k2; Kind.constr k2 k1]

    | _, _ ->
      raise (Fail (ty1, ty2))

end

let normalize_constr env l =
  let rec unify_all = function
    | T.Eq (t1, t2) -> Unif.unify env t1 t2
    | T.KindLeq (k1, k2) -> Kind.constr k1 k2
    | T.And l -> Normal.cand (List.map unify_all l)
    | T.True -> Normal.ctrue
  in
  Kind.solve @@ unify_all (T.And l)

let normalize (env, constr, ty) = env, normalize_constr env [constr], ty

let constant_scheme = let open T in function
    | Int _ -> tyscheme Builtin.int
    | Y ->
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Kind.un] Builtin.((a @-> a) @-> a)
    | Primitive s ->
      Builtin.(PrimMap.find s primitives)

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
    let _, arrow_k = T.kind ~name:"ar" level in
    with_type ~name:param.name ~env ~level @@ fun env param_ty param_kind ->
    let param_scheme = T.tyscheme param_ty in
    with_binding env param param_scheme @@ fun env ->
    let mults, env, constr, return_ty =
      infer env level body_expr
    in
    let param_constr, mults = Multiplicity.weaken mults param param_kind in
    let constr = normalize_constr env [
        C.denormal constr;
        Multiplicity.constraint_all mults arrow_k;
        param_constr
      ]
    in
    mults, env, constr,
    T.Arrow (param_ty, arrow_k, return_ty)
  | Array elems -> 
    with_type ~name:"v" ~level ~env @@ fun env array_ty _ ->
    let mults, env, constrs, tys = 
      infer_many env level Multiplicity.empty elems
    in 
    let f elem_ty = C.(elem_ty <== array_ty) in
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
    let env, remaining_constr, generalized_scheme =
      generalize env level var_constr var_ty value_expr
    in
    with_binding env var_name generalized_scheme @@ fun env ->
    let mults2, env, body_constr, body_ty = infer env level body_expr in
    let mults, constr_merge = Multiplicity.merge mults1 mults2 in
    let constr = normalize_constr env [
        C.denormal @@ Instantiate.go_constr level remaining_constr ;
        C.denormal body_constr ;
        constr_merge ;
      ]
    in
    Multiplicity.drop mults var_name, env, constr, body_ty
  | Match(constructor, param_name, expr, body) ->
    let mults1, env, expr_constr, expr_ty =
      infer env (level + 1) expr
    in
    let env, constructor_constr, constructor_ty =
      instantiate level env @@ Env.find constructor env
    in
    let param_ty, top_ty = match constructor_ty with
      | Types.Arrow (ty1, T.Un Global, ty2) -> ty1, ty2
      | _ -> assert false
    in
    let constr = normalize_constr env [
        C.(expr_ty <== top_ty) ;
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
        C.denormal @@ Instantiate.go_constr level generalized_constr ;
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
        C.(infered_ty <== return_ty);
        Kind.first_class return_kind;
      ]
    in
    mults, env, constr, return_ty

and infer_var env level name =
  let env, constr1, t = instantiate level env @@ Env.find name env in
  let constr2, k = infer_kind ~level ~env t in
  let constr = normalize_constr env [C.denormal constr1; C.denormal constr2] in
  (name, k), env, constr, t

and infer_many (env0 : Env.t) level mult l =
  let rec aux mults0 env0 constr0 tys = function
    | [] -> (mults0, env0, constr0, List.rev tys)
    | expr :: rest ->
      let mults, env, constr, ty = infer env0 level expr in
      let mults, constr_merge = Multiplicity.merge mults mults0 in
      let constr = C.cand [
          C.denormal constr;
          constr0;
          constr_merge;
        ]
      in
      aux mults env constr (ty :: tys) rest
  in aux mult env0 True [] l

and infer_app (env : Env.t) level fn_expr args =
  let f (f_ty, env) param_ty =
    let _, k = T.kind ~name:"a" level in
    with_type ~name:"a" ~level ~env @@ fun env return_ty _ ->
    let constr = C.(f_ty <== T.Arrow (param_ty, k, return_ty)) in
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
  let constr = normalize_constr env [C.denormal @@ Instantiate.go_constr 0 constr] in

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

let make_type_decl ~env ~constr kargs kind typ =
  let constructor_constr =
    match typ with
    | None -> T.True
    | Some typ ->
      let constr', inferred_k = infer_kind ~env ~level:1 typ in
      C.cand [C.denormal constr' ; C.( inferred_k <= kind ) ]
  in
  (* Format.eprintf "%a@." Printer.kind inferred_k ; *)
  let constr = normalize_constr env [
      C.denormal constr ;
      constructor_constr ;
    ]
  in

  (* Format.eprintf "%a@." Printer.constrs constr ; *)
  let env, leftover_constr, kscheme =
    Generalize.kind ~env ~level:0 constr kargs kind
  in
  
  (* Check that the residual constraints are satisfiable. *)
  let _ = normalize_constr env
      [C.denormal @@ Instantiate.go_constr 0 leftover_constr] in

  (* assert (constr = C.True) ; *)
  env, kscheme

let make_type_scheme ~env ~constr typ =
  let constr = normalize_constr env [C.denormal constr ] in
  let env, leftover_constr, tyscheme =
    Generalize.typ ~env ~level:0 constr typ
  in
  (* Check that the residual constraints are satisfiable. *)
  let _ = normalize_constr env
      [C.denormal @@ Instantiate.go_constr 0 leftover_constr] in

  (* assert (constr = C.True) ; *)
  env, tyscheme
