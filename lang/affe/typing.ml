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
  | Let (_, _, e1, e2)
  | Sequence (e1, e2) ->
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

  let rec gen_constraint ~level ~tyenv ~kenv = function
    | Normal.KindLeq (k1, k2) ->
      let k1 = gen_kind ~level ~kenv k1 in
      let k2 = gen_kind ~level ~kenv k2 in
      Normal.cleq k1 k2
    | HasKind (n, t, k) ->
      let t = gen_ty ~level ~kenv ~tyenv t in
      let k = gen_kind ~level ~kenv k in
      Normal.hasKind n t k
    | And l ->
      Normal.cand @@
      List.map (gen_constraint ~level ~tyenv ~kenv) l

  let disjoinct s1 s2 = Name.Set.(is_empty @@ inter s1 s2)
  
  let filter_constraints ~tyenv ~kenv c =
    let cs = Normal.flatten' c in
    let has_genvars c =
      let fv, kfv = T.Free_vars.normalized_constr c in
      not (disjoinct fv !tyenv && disjoinct kfv !kenv)
    in
    Normal.cand @@ List.filter has_genvars cs
    
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

    (* We built the type skeleton *)
    let tys = List.map (gen_ty ~level ~tyenv ~kenv) tys in

    (* Split the constraints that are actually generalized *)
    let constr_all = gen_constraint ~level ~tyenv ~kenv constr in
    let constr = filter_constraints ~kenv ~tyenv constr_all in

    let kvars = Name.Set.elements !kenv in
    let tyvars = Name.Set.elements !tyenv in

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
    let constr_all = gen_constraint ~level ~tyenv ~kenv constr in
    let constr = filter_constraints ~kenv ~tyenv constr_all in

    let kvars = Name.Set.elements !kenv in

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
      tyscheme
        ~tyvars:[name]
        ~constr:(C.Normal.hasKind name a (Kinds.un Global))
        Builtin.((a @-> a) @-> a)
    | Primitive s ->
      Builtin.(PrimMap.find s primitives)

let constant ~level c =
  let constr, ty =
    Instantiate.typ_scheme ~level @@ constant_scheme c
  in
  Multiplicity.empty, constr, ty

let with_binding ~env x ty f =
  let env = Env.add x ty env in
  let multis, env, constr, ty = f env in
  let env = Env.rm x env in
  multis, env, constr, ty

let with_type ~env:_ ~level f =
  let _, ty = T.var level in
  let _, kind = T.kind level in
  let constr = C.hasKind ty kind in
  (* let env = Env.add_ty var_name kind_scheme env in *)
  f constr ty kind

let rec infer_pattern env level = function
  | PUnit ->
    env, C.ctrue, [], Builtin.unit_ty
  | PAny ->
    with_type ~env ~level @@ fun constr_ty ty k ->
    let constr = C.cand [
        C.(k <= Kinds.aff Never) ;
        constr_ty;
      ]
    in
    env, constr, [], ty
  | PVar n ->
    with_type ~env ~level @@ fun constr_ty ty k ->
    env, constr_ty, [n, ty, k], ty
  | PConstr (constructor, None) ->
    let constructor_constr, constructor_ty =
      Instantiate.typ_scheme ~level @@ Env.find constructor env
    in
    let top_ty = constructor_ty in
    let constr = C.cand [
        C.denormalize constructor_constr ;
      ]
    in
    env, constr, [], top_ty
  | PConstr (constructor, Some pat) ->
    let constructor_constr, constructor_ty =
      Instantiate.typ_scheme ~level @@ Env.find constructor env
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
  let rec with_bindings ~env (params, schemes) kont = match (params, schemes) with
    | [],[] -> kont env constr input_ty
    | (name, _, _)::params, scheme::schemes ->
      with_binding ~env name scheme @@ fun env ->
      with_bindings ~env (params, schemes) kont
    | _ -> assert false
  in
  let mults, env, constrs, ty = with_bindings ~env (params, schemes) kont in
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
  | Constant c ->
    let mults, constr, ty = constant ~level c in
    mults, env, constr, ty
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
    with_type ~level ~env @@ fun constr_ty array_ty _ ->
    let mults, env, constrs, tys =
      infer_many env level Multiplicity.empty elems
    in 
    let f elem_ty = C.(elem_ty <== array_ty) in
    let elem_constr = CCList.map f tys in
    let constr = Constraint.normalize ~level ~env [
        constrs ;
        C.cand elem_constr ;
        constr_ty ;
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
    let constr1, t =
      Instantiate.typ_scheme ~level @@ Env.find name env
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
    with_type ~env ~level @@ fun constr_ty ty _ ->
    let borrow_ty = T.Borrow (Mutable, var_k, ty) in
    let mults = Multiplicity.borrow name r borrow_k in
    let constr = Constraint.normalize ~level ~env [
        C.denormalize constr;
        C.(var_ty <== borrow_ty);
        constr_ty;
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
  | Sequence (expr1, expr2) ->
    let mults1, env, expr1_constr, expr1_ty =
      infer env level expr1
    in
    let mults2, env, expr2_constr, expr2_ty =
      infer env level expr2 in
    let mults, constr_merge = Multiplicity.merge mults1 mults2 in
    let constr = Constraint.normalize ~level ~env [
        C.(expr1_ty <== Builtin.unit_ty) ;
        C.denormalize expr1_constr ;
        C.denormalize expr2_constr ;
        constr_merge ;
      ]
    in
    mults, env, constr, expr2_ty
  | Let (Rec, PVar n, expr, body) ->
    with_type ~env ~level:(level + 1) @@ fun constr_ty ty k ->
    with_binding ~env n (T.tyscheme ty) @@ fun env ->
    let mults1, env, expr_constr, expr_ty =
      infer env (level + 1) expr
    in
    let expr_constr = Constraint.normalize ~level ~env [
        C.(k <= Kinds.un Never) ;
        C.(expr_ty <== ty) ;
        C.denormalize expr_constr ;
        constr_ty ;
      ]
    in
    let generalize = is_nonexpansive expr in
    let env, remaining_constr, scheme =
      Generalize.typ env level generalize expr_constr ty
    in
    with_binding ~env n scheme @@ fun env ->
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
    with_type ~env ~level @@ fun constr_ty return_ty _ ->
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
        constr_ty ;
      ]
    in
    mults, env, constrs, return_ty
    
  | App(fn_expr, arg) ->
    infer_app env level fn_expr arg

  | Region (vars, expr) ->
    with_type ~env ~level @@ fun constr_ty return_ty return_kind ->
    let mults, env, constr, infered_ty = infer env (level+1) expr in
    let mults, exit_constr = Multiplicity.exit_region vars (level+1) mults in 
    let constr = Constraint.normalize ~level ~env [
        C.denormalize constr;
        C.(infered_ty <== return_ty);
        kind_first_class level return_kind;
        exit_constr;
        constr_ty;
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
  let constr1, t =
    Instantiate.typ_scheme ~level @@ Env.find name env
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
  let f f_ty param_ty =
    let _, k = T.kind level in
    with_type ~level ~env @@ fun constr_ty return_ty _ ->
    let constr = C.((f_ty <== T.Arrow (param_ty, k, return_ty)) &&& constr_ty) in
    return_ty, constr
  in
  let mults, env, fn_constr, fn_ty = infer env level fn_expr in
  let mults, env, arg_constr, tys = infer_many env level mults args in
  let return_ty, app_constr = CCList.fold_map f fn_ty tys in
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
    with_type ~env ~level @@ fun constr_ty ty _k ->
    with_binding ~env n (T.tyscheme ty) @@ fun env ->
    let mult, env, constr, ty = infer env level e in
    let constr = C.normalize ~level ~env [
        C.denormalize constr;
        constr_ty;
      ]
    in
    mult, env, constr, ty
  in
  let g = is_nonexpansive e in
  let env, constr, scheme = Generalize.typ env 0 g constr ty in

  (* Check that the residual constraints are satisfiable. *)
  let constr = Constraint.normalize ~level:0 ~env [
      C.denormalize @@ Instantiate.constr 0 constr
    ]
  in

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
