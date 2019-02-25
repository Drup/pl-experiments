module STy = Syntax.Ty
module Skind = Syntax.Kind

let transl_kind ~ktbl ~level = function
  | Skind.KVar n ->
    snd @@ Typing.Instantiate.instance_kvar ~ktbl ~level n
  | Unknown -> snd @@ Types.kind ~name:"r" level
  | Un -> Un Global
  | Aff -> Aff Global

let transl_constr ~ktbl ~level l =
  List.map
    (fun (k1, k2) -> (transl_kind ~ktbl ~level k1, transl_kind ~ktbl ~level k2))
    l

let rec transl_type ~ktbl ~tbl ~level = function
  | STy.Var n -> 
    snd @@ Typing.Instantiate.instance_tyvar ~tbl ~level n
  | App (t, l) ->
    let tyargs = List.map (transl_type ~ktbl ~tbl ~level) l in
    App (t, tyargs)
  | Tuple l ->
    let tyargs = List.map (transl_type ~ktbl ~tbl ~level) l in
    Tuple tyargs
  | Arrow (t1, k, t2) ->
    Arrow (transl_type ~ktbl ~tbl ~level t1,
           transl_kind ~ktbl ~level k,
           transl_type ~ktbl ~tbl ~level t2)
  | Borrow (r, k, t) ->
    Borrow (r,
            transl_kind ~ktbl ~level k,
            transl_type ~ktbl ~tbl ~level t)

module FV = Types.Free_vars
let (+++) = Name.Set.union

let transl_params ~env ~level params = 
  let tbl = Name.Tbl.create 10 in
  let ktbl = Name.Tbl.create 10 in

  let env, params =
    List.fold_right (fun (var, kind) (env, params) ->
        let k = transl_kind ~ktbl ~level kind in
        let var, ty = Typing.Instantiate.instance_tyvar ~tbl ~level var in
        let schm = Types.kscheme k in
        Env.add_ty var schm env, (var, ty, k)::params)
      params
      (env, [])
  in
  env, tbl, ktbl, params

let transl_type_scheme ~env (schm : STy.scheme) =
  let level = 1 in
  let env, tbl, ktbl, _params = transl_params ~env ~level schm.params in
  let constr = transl_constr ~ktbl ~level schm.constraints in
  let typ = transl_type ~ktbl ~tbl ~level schm.typ in
  let env, scheme = Typing.make_type_scheme ~env ~constr typ in
  env, scheme

let transl_type_constructor
    ~env ~level params typname constraints (constructor : STy.constructor)
  =
  let name = constructor.name in
  let env, tbl, ktbl, params = transl_params ~env ~level params in
  let typarams = List.map (fun (_,ty,_) -> ty) params in
  let constr =
    transl_constr ~ktbl ~level (constraints @ constructor.constraints)
  in
  let constructor_typ = transl_type ~ktbl ~tbl ~level constructor.typ in
  let typ = Types.Arrow (constructor_typ, Un Global, App (typname, typarams)) in
  let _env, scheme = Typing.make_type_scheme ~env ~constr typ in
  name, scheme

let transl_decl ~env
    {STy. name ; params ; constraints; constructor ; kind } =
  
  let level = 1 in

  let constructor_scheme =
    CCOpt.map
      (transl_type_constructor ~env ~level params name constraints)
      constructor
  in
  
  let env, tbl, ktbl, params = transl_params ~env ~level params in
  let kargs = List.map (fun (_,_,k) -> k) params in
  let ret_kind = transl_kind ~ktbl ~level kind in
  let constr = transl_constr ~ktbl ~level constraints in

  let typ =
    CCOpt.map (fun {STy. typ; _} -> transl_type ~ktbl ~tbl ~level typ) constructor
  in

  let _env, kscheme =
    Typing.make_type_decl ~env ~constr kargs ret_kind typ
  in

  name, kscheme, constructor_scheme
