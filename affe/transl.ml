open Syntax

let transl_kind ~ienv = function
  | K.KVar n ->
    snd @@ Instantiate.kvar ~ienv n
  | Unknown -> snd @@ Types.kind @@ Instantiate.level ienv
  | Un -> Un Global
  | Aff -> Aff Global
  | Lin -> Lin Global

let rec transl_type ~ienv = function
  | T.Var n -> 
    snd @@ Instantiate.tyvar ~ienv n
  | App (t, l) ->
    let tyargs = List.map (transl_type ~ienv) l in
    App (t, tyargs)
  | Tuple l ->
    let tyargs = List.map (transl_type ~ienv) l in
    Tuple tyargs
  | Arrow (t1, k, t2) ->
    Arrow (transl_type ~ienv t1,
           transl_kind ~ienv k,
           transl_type ~ienv t2)
  | Borrow (r, k, t) ->
    Borrow (r,
            transl_kind ~ienv k,
            transl_type ~ienv t)

let rec transl_constr ~ienv = function
  | C.KindLEq (k1,k2) ->
    Constraint.cleq (transl_kind ~ienv k1) (transl_kind ~ienv k2)
  | HasKind (t,k) ->
    Constraint.hasKind (transl_type ~ienv t) (transl_kind ~ienv k)
  | And l ->
    Constraint.cand @@ List.map (transl_constr ~ienv) l
       
let transl_params ~ienv params = 
  let constrs, params =
    List.fold_right (fun (var, kind) (constrs, params) ->
        let k = transl_kind ~ienv kind in
        let var, ty = Instantiate.tyvar ~ienv var in
        Constraint.(hasKind ty k &&& constrs), (var, ty, k)::params)
      params
      (Constraint.ctrue, [])
  in
  constrs, ienv, params

let transl_type_scheme ~env (schm : T.scheme) =
  let level = 1 in
  let ienv = Instantiate.create level in
  let constr_params, ienv, _tyvars = transl_params ~ienv schm.tyvars in
  let constr_lit = transl_constr ~ienv schm.constraints in
  let constr = Constraint.(constr_lit &&& constr_params) in
  let typ = transl_type ~ienv schm.typ in
  let env, scheme = Typing.make_type_scheme ~env ~constr typ in
  env, scheme

let transl_type_constructor
    ~env ~ienv params typname constraints (constructor : T.constructor)
  =
  let name = constructor.name in
  let typarams = List.map (fun (_,ty,_) -> ty) params in
  let constr =
    transl_constr ~ienv (C.And [constraints; constructor.constraints])
  in
  let constructor_typ = transl_type ~ienv constructor.typ in
  let typ = Types.Arrow (constructor_typ, Un Global, App (typname, typarams)) in
  let _env, scheme = Typing.make_type_scheme ~env ~constr typ in
  name, scheme

let transl_decl ~env
    {T. name ; params ; constraints; constructor ; kind } =
  
  let level = 1 in
  let ienv = Instantiate.create level in
  let constr_params, ienv, params = transl_params ~ienv params in
  let constructor_schemes =
    List.map
      (transl_type_constructor ~env ~ienv params name constraints)
      constructor
  in
  
  let kargs = List.map (fun (_,_,k) -> k) params in
  let ret_kind = transl_kind ~ienv kind in
  let constr_lit = transl_constr ~ienv constraints in
  let constr = Constraint.(constr_lit &&& constr_params) in

  let typs =
    List.map (fun {T. typ; _} -> transl_type ~ienv typ) constructor
  in

  let _env, kscheme =
    Typing.make_type_decl ~env ~constr kargs ret_kind typs
  in

  name, kscheme, constructor_schemes
