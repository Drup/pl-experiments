open Syntax
module T = Types
module Region = Kinds.Region
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
  | ReBorrow _
  | Array []
    -> true
  | Tuple l
  | App (Constructor _, l) ->
    List.for_all is_nonexpansive l
  | Region (_, e) -> is_nonexpansive e
  | Let (_, _, e1, e2) ->
    is_nonexpansive e1 && is_nonexpansive e2
  | Match (_, e, l) ->
    is_nonexpansive e &&
    List.for_all (fun (_, e) -> is_nonexpansive e) l
  | App (_, _)
  | Array _
    -> false

let kind_first_class n k = C.(k <= Kinds.constant @@ Lin (Region n))

(** Generalization *)
module Generalize = struct

  let update_kind ~kenv k =
    kenv := Name.Set.add k !kenv
  let update_type ~tyenv k =
    tyenv := Name.Set.add k !tyenv
  
  let rec gen_kind ~level ~kenv = function
    | Kinds.Var {contents = Unbound(id, other_level)} when other_level > level ->
      update_kind ~kenv id ;
      Kinds.GenericVar id
    | Var {contents = Link k} -> gen_kind ~level ~kenv k
    | ( GenericVar _
      | Var {contents = Unbound _}
      ) as ty -> ty
    | (Un _ | Lin _ | Aff _ ) as k -> k

  let rec gen_ty ~level ~tyenv ~kenv = function
    | T.Var {contents = Unbound(id, other_level)} when other_level > level ->
      update_type ~tyenv id ;
      T.GenericVar id
    | T.App(ty, ty_args) ->
      App(ty, List.map (gen_ty ~level ~tyenv ~kenv) ty_args)
    | T.Tuple ty_args ->
      Tuple (List.map (gen_ty ~level ~tyenv ~kenv) ty_args)
    | T.Borrow (r, k, ty) ->
      Borrow (r, gen_kind ~level ~kenv k, gen_ty ~level ~tyenv ~kenv ty)
    | T.Arrow(param_ty, k, return_ty) ->
      Arrow(gen_ty ~level ~tyenv ~kenv param_ty,
            gen_kind ~level ~kenv k,
            gen_ty ~level ~tyenv ~kenv return_ty)
    | T.Var {contents = Link ty} -> gen_ty ~level ~tyenv ~kenv ty
    | ( T.GenericVar _
      | T.Var {contents = Unbound _}
      ) as ty -> ty
  
  let gen_kscheme ~level ~kenv = function
    | {T. kvars = []; constr = _; args = [] ; kind } ->
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

  let rec gen_constraint ~level ~tyenv ~kenv = function
    | Normal.KindLeq (k1, k2) ->
      let old_kenv = !kenv in
      let k1 = gen_kind ~level ~kenv k1 in
      let k2 = gen_kind ~level ~kenv k2 in
      let constr = Normal.cleq k1 k2 in
      let c1, c2 =
        if Name.Set.equal old_kenv !kenv
        then constr, Normal.ctrue
        else Normal.ctrue, constr
      in
      (c1 , c2)
    | HasKind (t, k) ->
      let old_kenv = !kenv in
      let old_tyenv = !tyenv in
      let t = gen_ty ~level ~kenv ~tyenv t in
      let k = gen_kind ~level ~kenv k in
      let constr = Normal.hasKind t k in
      let c1, c2 =
        if Name.Set.equal old_kenv !kenv && Name.Set.equal old_tyenv !tyenv
        then constr, Normal.ctrue
        else Normal.ctrue, constr
      in
      (c1 , c2)
    | And l ->
      List.fold_left
        (fun (c1,c2) c -> let c1',c2' = gen_constraint ~level ~tyenv ~kenv c in
          Normal.(c1 &&& c1' , c2 &&& c2'))
        Normal.(ctrue, ctrue)
        l

  (* let collect_gen_vars ~kenv l =
   *   let add_if_gen = function
   *     | Kinds.Var (_, None) as k ->
   *       update_kind ~kenv k
   *     | _ -> ()
   *   in
   *   let rec aux = function
   *     | Normal.HasKind (_,k) -> add_if_gen k
   *   List.iter (fun (k1, k2) -> add_if_gen k1; add_if_gen k2) l *)

  (* let kinds_as_vars l =
   *   Name.Set.elements @@ T.Free_vars.kinds l *)

  let typs ~env ~level constr tys =
    let constr = C.simplify ~env ~level [constr] tys [] in

    let tyenv = ref Name.Set.empty in
    let kenv = ref Name.Set.empty in

    (* We built the type skeleton and collect the kindschemes *)
    let tys = List.map (gen_ty ~level ~tyenv ~kenv) tys in
    let tyvars = gen_kschemes ~env ~level ~kenv !tyenv in

    (* Split the constraints that are actually generalized *)
    let constr_no_var, constr = gen_constraint ~level ~tyenv ~kenv constr in
    let constr_all = Normal.(constr_no_var &&& constr) in

    (* collect_gen_vars ~kenv constr ; *)
    let kvars = Name.Set.elements !kenv in
    let env = Name.Set.fold (fun ty env -> Env.rm_ty ty env) !tyenv env in

    env, constr_all, List.map (T.tyscheme ~constr ~tyvars ~kvars) tys

  let typ ~env ~level constr ty =
    let env, constrs, tys = typs ~env ~level constr [ty] in
    match tys with
    | [ ty ] -> env, constrs, ty
    | _ -> assert false
  
  let kind ~env ~level constr args k =
    let constr =
      let l = List.map (fun k -> (k, Variance.Neg)) args @ [k, Variance.Pos] in
      C.simplify ~env ~level [constr] [] l
    in

    let tyenv = ref Name.Set.empty in
    let kenv = ref Name.Set.empty in

    (* We built the type skeleton and collect the kindschemes *)
    let k = gen_kind ~level ~kenv k in
    let args = List.map (gen_kind ~level ~kenv) args in

    (* Split the constraints that are actually generalized *)
    let constr_no_var, constr = gen_constraint ~level ~kenv ~tyenv constr in
    let constr_all = Normal.(constr_no_var &&& constr) in

    (* collect_gen_vars ~kenv constr ; *)
    let kvars = Name.Set.elements !kenv in
    let env = Name.Set.fold (fun ty env -> Env.rm_ty ty env) !tyenv env in

    env, constr_all,
    T.kscheme ~constr ~kvars ~args k

  (** The real generalization function that is aware of the value restriction. *)
  let typ env level generalize constr ty =
    if generalize then
      typ ~env ~level constr ty
    else
      env, constr, T.tyscheme ty
  let typs env level generalize constr tys =
    if generalize then
      typs ~env ~level constr tys
    else
      env, constr, List.map T.tyscheme tys

end


module Pat_modifier = struct

  type t =
    | Direct
    | Borrow of borrow * T.kind

  let app m t = match m with
    | Direct -> t
    | Borrow (b, k0) -> T.Borrow (b,k0,t)

  let with_kind m (t,k) = match m with
    | Direct -> (t,k)
    | Borrow (b, k0) -> T.Borrow (b,k0,t), k0

  let from_match_spec ~level : Syntax.match_spec -> _ = function
    | None -> Direct
    | Some b ->
      let _, k = T.kind level in
      Borrow (b,k)
  
end

let constant_scheme = let open T in function
    | Int _ -> tyscheme Builtin.int
    | Y ->
      let name, a = T.gen_var () in
      tyscheme ~tyvars:[name, Kinds.un Global] Builtin.((a @-> a) @-> a)
    | Primitive s ->
      Builtin.(PrimMap.find s primitives)

let constant level env c =
  let e, constr, ty =
    Instantiate.typ_scheme ~level ~env @@ constant_scheme c
  in
  Multiplicity.empty, e, constr, ty

let with_binding env x ty f =
  let env = Env.add x ty env in
  let multis, env, constr, ty = f env in
  let env = Env.rm x env in
  multis, env, constr, ty

let with_type ~env ~level f =
  let var_name, ty = T.var level in
  let _, kind = T.kind level in
  let kind_scheme = T.kscheme kind in
  let env = Env.add_ty var_name kind_scheme env in
  f env ty kind

let rec infer_pattern env level = function
  | PUnit ->
    env, C.ctrue, [], Builtin.unit_ty
  | PAny ->
    with_type ~env ~level @@ fun env ty k ->
    let constr = C.cand [
        C.(k <= Kinds.aff Never) ;
      ]
    in
    env, constr, [], ty
  | PVar n ->
    with_type ~env ~level @@ fun env ty k ->
    env, C.ctrue, [n, ty, k], ty
  | PConstr (constructor, None) ->
    let env, constructor_constr, constructor_ty =
      Instantiate.typ_scheme ~level ~env @@ Env.find constructor env
    in
    let top_ty = constructor_ty in
    let constr = C.cand [
        C.denormalize constructor_constr ;
      ]
    in
    env, constr, [], top_ty
  | PConstr (constructor, Some pat) ->
    let env, constructor_constr, constructor_ty =
      Instantiate.typ_scheme ~level ~env @@ Env.find constructor env
    in
    let param_ty, top_ty = match constructor_ty with
      | Types.Arrow (ty1, Un Global, ty2) -> ty1, ty2
      | _ -> assert false
    in
    let env, constr, params, ty = infer_pattern env level pat in
    let constr = C.cand [
        C.(ty <== param_ty) ;
        constr;
        C.denormalize constructor_constr ;
      ]
    in
    env, constr, params, top_ty
  | PTuple l ->
    let rec gather_pats (env, constrs, params, tys) = function
      | [] -> env, constrs, List.rev params, List.rev tys
      | pat :: t ->
        let env, constr, param, ty = infer_pattern env level pat in
        gather_pats (env, C.(constr &&& constrs), param@params, ty::tys) t
    in
    let env, constrs, params, tys = gather_pats (env, C.ctrue, [], []) l in
    let ty = T.Tuple tys in
    env, constrs, params, ty

and with_pattern
    ?(pat_modifier=Pat_modifier.Direct) env level generalize pat kont =
  let env, constr, params, pat_ty = infer_pattern env level pat in
  let constr = Constraint.normalize ~level ~env [constr] in
  let input_ty = Pat_modifier.app pat_modifier pat_ty in
  let params =
    let f (n,t,k) =
      let (t,k) = Pat_modifier.with_kind pat_modifier (t,k) in (n, t, k)
    in List.map f params
  in
  let tys = List.map (fun (_,t,_) -> t) params in
  let env, constr, schemes = Generalize.typs env level generalize constr tys in
  let rec with_bindings env (params, schemes) kont = match (params, schemes) with
    | [],[] -> kont env constr input_ty
    | (name, _, _)::params, scheme::schemes ->
      with_binding env name scheme @@ fun env ->
      with_bindings env (params, schemes) kont
    | _ -> assert false
  in
  let mults, env, constrs, ty = with_bindings env (params, schemes) kont in
  let mults, weaken_consts =
    List.fold_left (fun (m, c') (n,_,k) ->
        let c, m = Multiplicity.exit_binder m n k in m, C.(c &&& c'))
      (mults, C.ctrue) params
  in
  let constrs = Constraint.normalize ~level ~env [
      C.denormalize constrs;
      weaken_consts;
    ]
  in
  mults, env, constrs, ty



let rec infer (env : Env.t) level = function
  | Constant c -> constant level env c
  | Lambda(param, body) ->
    let _, arrow_k = T.kind level in
    let mults, env, constr, (param_ty, return_ty) =
      infer_lambda env level (param, body)
    in
    let constr = Constraint.normalize ~level ~env  [
        C.denormalize constr;
        Multiplicity.constraint_all mults arrow_k;
      ]
    in
    let ty = T.Arrow (param_ty, arrow_k, return_ty) in
    mults, env, constr, ty
    
  | Array elems -> 
    with_type ~level ~env @@ fun env array_ty _ ->
    let mults, env, constrs, tys = 
      infer_many env level Multiplicity.empty elems
    in 
    let f elem_ty = C.(elem_ty <== array_ty) in
    let elem_constr = CCList.map f tys in
    let constr = Constraint.normalize ~level ~env [
        constrs ;
        C.cand elem_constr ;
      ]
    in
    mults, env, constr, Builtin.array array_ty
  | Tuple elems -> 
    let mults, env, constrs, tys =
      infer_many env level Multiplicity.empty elems
    in
    let constr = Constraint.normalize ~level ~env [
        constrs ;
      ]
    in
    mults, env, constr, T.Tuple tys
  | Constructor name ->
    let env, constr1, t =
      Instantiate.typ_scheme ~level ~env @@ Env.find name env
    in
    (* let constr2, k = infer_kind ~level ~env t in
     * assert (k = Kinds.un) ; *)
    let constr = Constraint.normalize ~level ~env [
        C.hasKind t @@ Kinds.un Global ;
        C.denormalize constr1;
        (* C.denormalize constr2 *)
      ]
    in
    Multiplicity.empty, env, constr, t

  | Var name ->
    let (name, k), env, constr, ty = infer_var env level name in
    Multiplicity.var name k, env, constr, ty

  | Borrow (r, name) ->
    let _, borrow_k = T.kind level in
    let (name, _), env, constr, var_ty = infer_var env level name in
    let mults = Multiplicity.borrow name r borrow_k in 
    let constr = Constraint.normalize ~level ~env [
        C.denormalize constr;
      ]
    in
    mults, env, constr, T.Borrow (r, borrow_k, var_ty)
  | ReBorrow (r, name) ->
    let _, var_k = T.kind level in
    let _, borrow_k = T.kind level in
    let (name, _), env, constr, var_ty = infer_var env level name in
    with_type ~env ~level @@ fun env ty _ ->
    let borrow_ty = T.Borrow (Mutable, var_k, ty) in
    let mults = Multiplicity.borrow name r borrow_k in
    let constr = Constraint.normalize ~level ~env [
        C.denormalize constr;
        C.(var_ty <== borrow_ty);
      ]
    in
    mults, env, constr, T.Borrow (r, borrow_k, ty)
  | Let (NonRec, pattern, expr, body) ->
    let mults1, env, expr_constr, expr_ty =
      infer env (level + 1) expr
    in
    let generalize = is_nonexpansive expr in
    with_pattern env level generalize pattern @@ fun env pat_constr pat_ty ->
    let mults2, env, body_constr, body_ty = infer env level body in
    let mults, constr_merge = Multiplicity.merge mults1 mults2 in
    let constr = Constraint.normalize ~level ~env [
        C.(expr_ty <== pat_ty) ;
        C.denormalize expr_constr ;
        C.denormalize pat_constr ;
        C.denormalize body_constr ;
        constr_merge ;
      ]
    in
    mults, env, constr, body_ty
  | Let (Rec, PVar n, expr, body) ->
    with_type ~env ~level:(level + 1) @@ fun env ty k ->
    with_binding env n (T.tyscheme ty) @@ fun env ->
    let mults1, env, expr_constr, expr_ty =
      infer env (level + 1) expr
    in
    let expr_constr = Constraint.normalize ~level ~env [
        C.(k <= Kinds.un Never) ;
        C.(expr_ty <== ty) ;
        C.denormalize expr_constr
      ]
    in
    let generalize = is_nonexpansive expr in
    let env, remaining_constr, scheme =
      Generalize.typ env level generalize expr_constr ty
    in
    with_binding env n scheme @@ fun env ->
    let mults2, env, body_constr, body_ty = infer env level body in
    let mults, constr_merge = Multiplicity.merge mults1 mults2 in
    let constr = Constraint.normalize ~level ~env [
        C.denormalize expr_constr ;
        C.denormalize remaining_constr ;
        C.denormalize body_constr ;
        constr_merge ;
      ]
    in
    mults, env, constr, body_ty
  | Let (Rec, p, _, _) ->
    fail "Such patterns are not allowed on the left hand side of a let rec@ %a"
      Printer.pattern p

  | Match (match_spec, expr, cases) ->
    let mults, env, expr_constrs, match_ty = infer env level expr in
    with_type ~env ~level @@ fun env return_ty _ ->
    let pat_modifier = Pat_modifier.from_match_spec ~level match_spec in
    let aux env case =
      let mults, env, constrs, (pattern, body_ty) =
        infer_lambda ~pat_modifier env level case
      in
      let constrs = Constraint.normalize ~level ~env [
          C.denormalize constrs;
          C.(match_ty <== pattern);
          C.(body_ty <== return_ty);
        ]
      in
      env, (mults, constrs)
    in
    let env, l = CCList.fold_map aux env cases in
    let reduce (m1,c1) (m2,c2) =
      let mults, mult_c = Multiplicity.parallel_merge m1 m2 in
      let constrs = C.cand [mult_c; c1; C.denormalize c2] in
      mults, constrs
    in 
    let mults, match_constrs = List.fold_left reduce (mults, C.ctrue) l in
    let constrs = Constraint.normalize ~level ~env [
        C.denormalize expr_constrs;
        match_constrs ;
      ]
    in
    mults, env, constrs, return_ty
    
  | App(fn_expr, arg) ->
    infer_app env level fn_expr arg

  | Region (vars, expr) ->
    with_type ~env ~level @@ fun env return_ty return_kind ->
    let mults, env, constr, infered_ty = infer env (level+1) expr in
    let mults, exit_constr = Multiplicity.exit_region vars (level+1) mults in 
    let constr = Constraint.normalize ~level ~env [
        C.denormalize constr;
        C.(infered_ty <== return_ty);
        kind_first_class level return_kind;
        exit_constr;
      ]
    in
    mults, env, constr, return_ty

and infer_lambda ?pat_modifier env level (pattern, body_expr) =
  with_pattern ?pat_modifier env level false pattern @@
  fun env param_constr input_ty ->
  let mults, env, constr, return_ty =
    infer env level body_expr
  in
  let constr = Constraint.normalize ~level ~env [
      C.denormalize constr;
      C.denormalize param_constr;
    ]
  in
  mults, env, constr, (input_ty, return_ty)
  
and infer_var env level name =
  let env, constr1, t =
    Instantiate.typ_scheme ~level ~env @@ Env.find name env
  in
  let _, k = T.kind level in
  (* let constr2, k = infer_kind ~level ~env t in *)
  let constr = Constraint.normalize ~level ~env [
      C.hasKind t k;
      C.denormalize constr1;
      (* C.denormalize constr2; *)
    ]
  in
  (name, k), env, constr, t

and infer_many (env0 : Env.t) level mult l =
  let rec aux mults0 env0 constr0 tys = function
    | [] -> (mults0, env0, constr0, List.rev tys)
    | expr :: rest ->
      let mults, env, constr, ty = infer env0 level expr in
      let mults, constr_merge = Multiplicity.merge mults mults0 in
      let constr = C.cand [
          C.denormalize constr;
          constr0;
          constr_merge;
        ]
      in
      aux mults env constr (ty :: tys) rest
  in aux mult env0 C.ctrue [] l

and infer_app (env : Env.t) level fn_expr args =
  let f (f_ty, env) param_ty =
    let _, k = T.kind level in
    with_type ~level ~env @@ fun env return_ty _ ->
    let constr = C.(f_ty <== T.Arrow (param_ty, k, return_ty)) in
    (return_ty, env), constr
  in
  let mults, env, fn_constr, fn_ty = infer env level fn_expr in
  let mults, env, arg_constr, tys = infer_many env level mults args in
  let (return_ty, env), app_constr = CCList.fold_map f (fn_ty, env) tys in
  let constr = Constraint.normalize ~level ~env [
      C.denormalize fn_constr ;
      arg_constr ;
      C.cand app_constr ;
    ]
  in
  mults, env, constr, return_ty

let infer_top env _rec_flag n e =
  let _, env, constr, ty =
    let level = 1 in
    with_type ~env ~level @@ fun env ty _k ->
    with_binding env n (T.tyscheme ty) @@ fun env ->
    infer env level e
  in
  let g = is_nonexpansive e in
  let env, constr, scheme = Generalize.typ env 0 g constr ty in

  (* Check that the residual constraints are satisfiable. *)
  let constr = Constraint.normalize ~level:0 ~env [
      C.denormalize @@ Instantiate.constr 0 constr
    ]
  in

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

let make_type_decl ~env ~constr kargs kind typs =
  let constructor_constrs =
    List.map (fun typ -> C.hasKind typ kind) typs
  in
  (* Format.eprintf "%a@." Printer.kind inferred_k ; *)
  let constr = Constraint.normalize ~level:0 ~env [
      constr ;
      C.cand constructor_constrs ;
    ]
  in

  (* Format.eprintf "%a@." Printer.constrs constr ; *)
  let env, leftover_constr, kscheme =
    Generalize.kind ~env ~level:0 constr kargs kind
  in
  
  (* Check that the residual constraints are satisfiable. *)
  let _ = Constraint.normalize ~level:0 ~env
      [C.denormalize @@ Instantiate.constr 0 leftover_constr] in

  (* assert (constr = C.True) ; *)
  env, kscheme

let make_type_scheme ~env ~constr typ =
  let constr = Constraint.normalize ~level:0 ~env [constr] in
  let env, leftover_constr, tyscheme =
    Generalize.typ env 0 true constr typ
  in
  (* Check that the residual constraints are satisfiable. *)
  let _ = Constraint.normalize ~level:0 ~env
      [C.denormalize @@ Instantiate.constr 0 leftover_constr] in

  (* assert (constr = C.True) ; *)
  env, tyscheme
