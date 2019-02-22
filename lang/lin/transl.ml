module STy = Syntax.Ty

let transl_kind = function
  | STy.KVar n -> Types.KGenericVar n
  | Un -> Un Global
  | Aff -> Aff Global

let transl_constr l =
  List.map (fun (k1, k2) -> (transl_kind k1, transl_kind k2)) l

let rec transl_type = function
  | STy.Var n -> Types.GenericVar n
  | App (t, l) ->
    let tyargs = List.map transl_type l in
    App (t, tyargs)
  | Arrow (t1, k, t2) -> Arrow (transl_type t1, transl_kind k, transl_type t2)
  | Borrow (r, k, t) -> Borrow (r, transl_kind k, transl_type t)

let transl_type_instance ~level ty = 
  let ty = transl_type ty in
  let tbl = Hashtbl.create 10 in
  let ktbl = Hashtbl.create 10 in
  Typing.Instantiate.instance_type ~level ~tbl ~ktbl ty

module FV = Types.Free_vars
let (+++) = Name.Set.union
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
    let kvars = FV.kind k +++ FV.kinds kargs in
    let constr = Typing.Kind.simplify constr in
    let kvars = FV.constrs constr +++ kvars in
    Types.kscheme ~constr ~kvars:(Name.Set.elements kvars) ~args:kargs k
  in
  let tyschm =
    let ty : Types.typ =
      Arrow (constr_typ, Un Global,
             App (name, List.map (fun (x, _) -> Types.GenericVar x) tyargs))
    in
    let tyvars, kvars = FV.types ty in
    assert Name.Set.(subset tyvars @@ of_list @@ List.map fst tyargs) ;
    let kvars = FV.kinds kargs +++ kvars in
    let constr = Typing.Kind.simplify constr in
    Types.tyscheme ~constr ~tyvars:tyargs ~kvars:(Name.Set.elements kvars) ty
  in
  (name, kschm, constructor, tyschm)
