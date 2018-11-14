open Syntax
module T = Types
module C = Constraint
module Normal = Constraint.Normal


let fail fmt =
  Zoo.error ~kind:"Type error" fmt

let rec is_nonexpansive = function
  | V (Constant _)
  | V (Lambda _)
  | V (Constructor (_, None))
  | Var _ -> true
  | Let (_, e1, e2) ->
    is_nonexpansive e1 && is_nonexpansive e2
  | Match (_, _, e1, e2) ->
    is_nonexpansive e1 && is_nonexpansive e2
  | App (V (Constructor (_, None)), [e]) ->
    is_nonexpansive e
  | _ -> false

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
    | T.Un | T.Lin as k -> k

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


(** Generalization *)
module Generalize = struct

  let rec gen_kind ~level ~kenv = function
    | T.KVar {contents = KUnbound(id, other_level)} when other_level > level ->
      kenv := Name.Set.add id !kenv ;
      T.KGenericVar id
    | T.KVar {contents = KLink ty} -> gen_kind ~level ~kenv ty
    | ( T.KGenericVar _
      | T.KVar {contents = KUnbound _}
      | T.Un | T.Lin
      ) as ty -> ty

  let rec gen_ty ~env ~level ~tyenv ~kenv = function
    | T.Var {contents = Unbound(id, other_level)} when other_level > level ->
      tyenv := Name.Set.add id !tyenv ;
      T.GenericVar id
    | T.App(ty, ty_args) ->
      App(ty, List.map (gen_ty ~env ~level ~tyenv ~kenv) ty_args)
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
      let kenv = ref Name.Set.empty in
      let k1 = gen_kind ~level ~kenv k1 in
      let k2 = gen_kind ~level ~kenv k2 in
      let constr = Normal.cleq k1 k2 in
      let c1, c2 =
        if Name.Set.is_empty !kenv
        then constr, Normal.ctrue
        else Normal.ctrue, constr
      in
      let no_vars, vars = gen_constraint ~level rest in
      Normal.(c1 @ no_vars , c2 @ vars)

  let collect_gen_vars ~kenv l =
    let add_if_gen = function
      | T.KGenericVar n -> kenv := Name.Set.add n !kenv
      | _ -> ()
    in
    List.iter (fun (k1, k2) -> add_if_gen k1; add_if_gen k2) l

  let typ ~env ~level constr ty =
    let tyenv = ref Name.Set.empty in
    let kenv = ref Name.Set.empty in

    let ty = gen_ty ~env ~level ~tyenv ~kenv ty in
    let tyvars = gen_kschemes ~env ~level ~kenv !tyenv in

    let constr_no_var, constr = gen_constraint ~level constr in
    let constr = Normal.simplify_solved ~keep_vars:!kenv constr in
    let constr_all = Normal.(constr_no_var @ constr) in

    collect_gen_vars ~kenv constr ;
    let kvars = Name.Set.elements !kenv in
    let env = Name.Set.fold (fun ty env -> Env.rm_ty ty env) !tyenv env in

    env, constr_all, T.tyscheme ~constr ~tyvars ~kvars ty

  (** The real generalization function that is aware of the value restriction. *)
  let go env level constr ty exp =
    if is_nonexpansive exp then
      typ ~env ~level constr ty
    else
      env, constr, T.tyscheme ty

end
let generalize = Generalize.go


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
      | T.Un | T.Lin -> ()
    in
    f kind

  let rec unify k1 k2 = match k1, k2 with
    | _, _ when k1 == k2
      -> Normal.ctrue

    | T.Un, T.Un
    | T.Lin, T.Lin
      -> Normal.ctrue

    | T.KVar {contents = KUnbound(id1, _)},
      T.KVar {contents = KUnbound(id2, _)} when id1 = id2 ->
      (* There is only a single instance of a particular type variable. *)
      assert false

    | T.KVar {contents = KLink k1}, k2
    | k1, T.KVar {contents = KLink k2} -> unify k1 k2

    | T.KVar ({contents = KUnbound (id, level)} as tvar), ty
    | ty, T.KVar ({contents = KUnbound (id, level)} as tvar) ->
      adjust_levels id level ty ;
      tvar := KLink ty ;
      did_unify_kind := true ;
      Normal.ctrue

    | _, T.KGenericVar _ | T.KGenericVar _, _ ->
      (* Should always have been instantiated before *)
      assert false

    | T.Un, T.Lin | T.Lin, T.Un -> raise (Fail (k1, k2))


  let rec leq k1 k2 = match k1, k2 with
    | _, _ when k1 == k2
      -> Normal.ctrue
    | T.Un, _
    | _, T.Lin
      -> Normal.ctrue

    | T.Lin, T.Un
      -> raise (Fail (k1, k2))

    | T.KVar {contents = KUnbound(id1, _)},
      T.KVar {contents = KUnbound(id2, _)} when id1 = id2 ->
      (* There is only a single instance of a particular type variable. *)
      assert false

    | T.KVar {contents = KLink k1}, k2
    | k1, T.KVar {contents = KLink k2} -> leq k1 k2

    | T.KVar ({contents = KUnbound (id, level)} as tvar), (T.Un as ty)
    | (T.Lin as ty), T.KVar ({contents = KUnbound (id, level)} as tvar) ->
      adjust_levels id level ty ;
      tvar := KLink ty ;
      did_unify_kind := true ;
      Normal.ctrue

    | _, T.KGenericVar _ | T.KGenericVar _, _ ->
      (* Should always have been instantiated before *)
      Normal.cleq k1 k2

    | T.KVar {contents = KUnbound _}, T.KVar {contents = KUnbound _} ->
      Normal.cleq k1 k2

  let constr = leq
end

let rec infer_kind ~level ~env = function
  | T.App (f, args) ->
    let constrs, args =
      List.fold_right
        (fun ty (constrs, args) ->
           let constr, k = infer_kind ~level ~env ty in
           Normal.(constr @ constrs) , k::args)
        args ([], [])
    in
    let constr', kind =
      Instantiate.go_kind level ~args @@ Env.find_constr f env
    in
    Normal.(constr' @ constrs), kind
  | T.Arrow (_, k, _) -> Normal.ctrue, k
  | T.GenericVar n -> Instantiate.go_kind level @@ Env.find_ty n env
  | T.Var { contents = T.Unbound (n, _) } ->
    Instantiate.go_kind level @@ Env.find_ty n env
  | T.Var { contents = T.Link ty } ->
    infer_kind ~level ~env ty

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
      | T.App(_ty, ty_arg) ->
        List.iter f ty_arg
      | T.Arrow(param_ty, _,return_ty) ->
        f param_ty ;
        f return_ty
    in
    f ty

  let rec unify env ty1 ty2 = match ty1, ty2 with
    | _, _ when ty1 == ty2 -> Normal.ctrue

    | T.App(ty1, ty_arg1), T.App(ty2, ty_arg2) when Name.equal ty1 ty2 ->
      Normal.cand (List.map2 (unify env) ty_arg1 ty_arg2)

    | T.Arrow(param_ty1, k1, return_ty1), T.Arrow(param_ty2, k2, return_ty2) ->
      Normal.cand [
        Kind.constr k1 k2;
        Kind.constr k2 k1;
        unify env param_ty2 param_ty1;
        unify env return_ty1 return_ty2;
      ]

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
  let simplify l : Normal.t =
    let l = List.flatten @@ List.map (fun (k1, k2) -> Kind.constr k1 k2) l in
    let l_eq, l_rest = Normal.split_equals l in
    (List.flatten @@ List.map (fun (k1, k2) -> Kind.unify k1 k2) l_eq)
    @ l_rest
  in
  let rec loop l =
    Kind.did_unify_kind := false ;
    let l = simplify l in
    if !Kind.did_unify_kind then
      loop l
    else
      l
  in
  loop @@ unify_all (T.And l)

let normalize (env, constr, ty) = env, normalize_constr env [constr], ty

module Multiplicity = struct
  type t = (T.kind list) Name.Map.t
  let empty = Name.Map.empty
  let var x k = Name.Map.singleton x [k]
  let union e1 e2 =
    Name.Map.merge (fun _ v1 v2 -> match v1,v2 with
        | None, None -> None
        | b, None | None, b -> b
        | Some k1, Some k2 -> Some (k1 @ k2)
      ) e1 e2
  let inter e1 e2 =
    Name.Map.merge (fun _ v1 v2 -> match v1,v2 with
        | Some k1, Some k2 -> Some (k1 @ k2)
        | _ -> None
      ) e1 e2
  let constraint_all e k0 : T.constr =
    let l =
      let aux _ ks l = List.map (fun k -> C.(k <= k0)) ks @ l in
      Name.Map.fold aux e []
    in
    C.cand l
  let drop e x = Name.Map.remove x e
  let constraint_inter e1 e2 =
    constraint_all (inter e1 e2) Un

  let weaken e v k0 : T.constr =
    match Name.Map.find_opt v e with
    | Some [_] -> T.True
    | None | Some [] -> T.KindLeq (k0, Un)
    | Some ks ->
      C.cand @@ List.map (fun k -> C.(k <= k0)) ks
end


let constant_scheme = let open T in function
    | Int _ -> tyscheme Builtin.int
    | Plus  -> tyscheme Builtin.(int @-> int @-> int)
    | NewRef ->
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Un] Builtin.(a @-> ref a)
    | Get ->
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Un] Builtin.((ref a) @-> a )
    | Set ->
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Un] Builtin.( (ref a) @-> a @-> a )
    | Y ->
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Un] Builtin.((a @-> a) @-> a)

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

let rec infer_value (env : Env.t) level = function
  | Constant c -> constant level env c
  | Lambda(param, body_expr) ->
    let _, arrow_k = T.kind ~name:"r" level in
    with_type ~name:param.name ~env ~level @@ fun env param_ty param_kind ->
    let param_scheme = T.tyscheme param_ty in
    with_binding env param param_scheme @@ fun env ->
    let mults, env, constr, return_ty = infer env level body_expr in
    let mults_no_param = Multiplicity.drop mults param in
    let constr = normalize_constr env [
        C.denormal constr;
        Multiplicity.constraint_all mults_no_param arrow_k;
        Multiplicity.weaken mults param param_kind;
      ]
    in
    mults_no_param, env, constr, T.Arrow (param_ty, arrow_k, return_ty)
  | Ref v ->
    let mults, env, constr, ty = infer_value env level !v in
    mults, env, constr, (Builtin.ref ty)
  | Constructor (_name, Some _) -> assert false
  | Constructor (name, None) ->
    let env, constr1, t = instantiate level env @@ Env.find name env in
    let constr2, k = infer_kind ~level ~env t in
    assert (k = Un) ;
    let constr = normalize_constr env [C.denormal constr1; C.denormal constr2] in
    Multiplicity.empty, env, constr, t

and infer (env : Env.t) level = function
  | V v ->
    infer_value env level v

  | Var name ->
    let env, constr1, t = instantiate level env @@ Env.find name env in
    let constr2, k = infer_kind ~level ~env t in
    let constr = normalize_constr env [C.denormal constr1; C.denormal constr2] in
    (Multiplicity.var name k), env, constr, t

  | Let(var_name, value_expr, body_expr) ->
    let mults1, env, var_constr, var_ty =
      infer env (level + 1) value_expr
    in
    let env, generalized_constr, generalized_scheme =
      generalize env level var_constr var_ty value_expr
    in
    with_binding env var_name generalized_scheme @@ fun env ->
    let mults2, env, body_constr, body_ty = infer env level body_expr in
    let constr = normalize_constr env [
        C.denormal @@ Instantiate.constr level generalized_constr ;
        C.denormal body_constr ;
        Multiplicity.constraint_inter mults1 mults2 ;
      ]
    in
    let mults = Multiplicity.union mults1 mults2 in
    mults, env, constr, body_ty
  | Match(constructor, param_name, expr, body) ->
    let mults1, env, expr_constr, expr_ty =
      infer env (level + 1) expr
    in
    let env, constructor_constr, constructor_ty =
      instantiate level env @@ Env.find constructor env
    in
    let param_ty, output_ty = match constructor_ty with
      | Types.Arrow (ty1, Un, ty2) -> ty1, ty2
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
    let constr = normalize_constr env [
        C.denormal constr ;
        C.denormal @@ Instantiate.constr level generalized_constr ;
        C.denormal body_constr ;
        Multiplicity.constraint_inter mults1 mults2 ;
      ]
    in
    let mults = Multiplicity.union mults1 mults2 in
    mults, env, constr, body_ty
  | App(fn_expr, arg) ->
    let mults, env, f_constr, f_ty = infer env level fn_expr in
    infer_app env level mults (C.denormal f_constr) f_ty arg

and infer_app (env : Env.t) level mults constr f_ty = function
  | [] -> mults, env, normalize_constr env [constr], f_ty
  | arg :: rest ->
    let mults', env, param_constr, param_ty = infer env level arg in
    let _, k = T.kind ~name:"a" level in
    with_type ~name:"a" ~level ~env @@ fun env return_ty _ ->
    let constr = C.cand [
        Multiplicity.constraint_inter mults mults';
        C.denormal param_constr;
        C.(T.Arrow (param_ty, k, return_ty) === f_ty);
        constr;
      ]
    in
    let mults = Multiplicity.union mults mults' in
    infer_app env level mults constr return_ty rest

let infer_top env0 e =
  let _, env, constr, ty = infer env0 1 e in
  let env, constr, scheme = generalize env 0 constr ty e in

  (* Check that the residual constraints are satisfiable. *)
  let constr = normalize_constr env [C.denormal @@ Instantiate.constr 0 constr] in

  (* Remove unused variables in the environment *)
  let free_vars =
    Name.Map.fold
      (fun _ sch e -> Name.Set.union e @@ T.free_vars_scheme sch)
      env.vars
      (T.free_vars_scheme scheme)
  in
  let env = Env.filter_ty (fun n _ -> Name.Set.mem n free_vars) env in

  (* assert (constr = C.True) ; *)
  constr, env, scheme
