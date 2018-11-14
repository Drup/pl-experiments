module STy = Syntax.Ty

let transl_kind = function
  | STy.KVar n -> Types.KGenericVar n
  | Un -> Un
  | Lin -> Lin

let transl_constr l =
  List.map (fun (k1, k2) -> (transl_kind k1, transl_kind k2)) l

let rec transl_type = function
  | STy.Var n -> Types.GenericVar n
  | App (t, l) ->
    let tyargs = List.map transl_type l in
    App (t, tyargs)
  | Arrow (t1, k, t2) -> Arrow (transl_type t1, transl_kind k, transl_type t2)

let transl_type_instance ~level ty = 
  let ty = transl_type ty in
  let tbl = Hashtbl.create 10 in
  let ktbl = Hashtbl.create 10 in
  Typing.Instantiate.instance_type ~level ~tbl ~ktbl ty

let (+++) = Name.Set.union

let free_vars_kind = function
  | Types.KGenericVar n -> Name.Set.singleton n
  | Types.KVar _ -> assert false
  | Types.Un | Types.Lin -> Name.Set.empty

let free_vars_kinds l =
  List.fold_left
    (fun e k -> free_vars_kind k +++ e)
    Name.Set.empty l

let free_vars_constrs l =
  List.fold_left
    (fun e (k1, k2) -> free_vars_kind k1 +++ free_vars_kind k2 +++ e)
    Name.Set.empty l

let rec free_vars = function
  | Types.GenericVar n -> Name.Set.singleton n, Name.Set.empty
  | Types.Var _ -> assert false
  | Types.App (_, args) ->
    List.fold_left (fun (et, ek) t ->
        let et', ek' = free_vars t in
        et +++ et', ek +++ ek'
      ) Name.Set.(empty, empty) args
  | Types.Arrow (ty1, k, ty2) ->
    let et1, ek1 = free_vars ty1 and et2, ek2 = free_vars ty2 in
    et1 +++ et2, ek1 +++ free_vars_kind k +++ ek2

let transl_decl ~env {STy. name ; params ; constraints; constructor ; typ } =
  let env, kargs, tyargs =
    List.fold_right (fun (var, kind) (env, kargs, tyargs) ->
        let k = transl_kind kind in
        let schm = Types.kscheme k in
        Env.add_ty var schm env, k::kargs, (var, k)::tyargs)
      params
      (env, [], [])
  in
  let constrs1 = transl_constr constraints in
  let constr_typ = transl_type typ in
  let constrs2, k = Typing.infer_kind ~level:1 ~env constr_typ in
  let constr = Typing.normalize_constr env
      Constraint.[denormal constrs1; denormal constrs2]
  in
    
  let kschm =
    let kvars = free_vars_kind k +++ free_vars_kinds kargs in
    let constr = Constraint.Normal.simplify_solved ~keep_vars:kvars constr in
    let kvars = free_vars_constrs constr +++ kvars in
    Types.kscheme ~constr ~kvars:(Name.Set.elements kvars) ~args:kargs k
  in
  let tyschm =
    let ty : Types.typ =
      Arrow (constr_typ, Un,
             App (name, List.map (fun (x, _) -> Types.GenericVar x) tyargs))
    in
    let tyvars, kvars = free_vars ty in
    assert Name.Set.(subset tyvars @@ of_list @@ List.map fst tyargs) ;
    let kvars = free_vars_kinds kargs +++ kvars in
    let constr = Constraint.Normal.simplify_solved ~keep_vars:kvars constr in
    Types.tyscheme ~constr ~tyvars:tyargs ~kvars:(Name.Set.elements kvars) ty
  in
  (name, kschm, constructor, tyschm)
