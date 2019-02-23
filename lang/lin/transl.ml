module STy = Syntax.Ty

let transl_kind ~ktbl ~level = function
  | STy.KVar n ->
    snd @@ Typing.Instantiate.instance_kvar ~ktbl ~level n
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

let transl_decl ~env {STy. name ; params ; constraints; constructor ; typ ; ret_kind } =
  
  let level = 1 in
  let tbl = Name.Tbl.create 10 in
  let ktbl = Name.Tbl.create 10 in
  
  let env, kargs, _tyargs, typarams =
    List.fold_right (fun (var, kind) (env, kargs, tyargs, typarams) ->
        let k = transl_kind ~ktbl ~level kind in
        let var, ty = Typing.Instantiate.instance_tyvar ~tbl ~level var in
        let schm = Types.kscheme k in
        Env.add_ty var schm env, k::kargs, (var, k)::tyargs, ty::typarams)
      params
      (env, [], [], [])
  in
  let ret_kind = match ret_kind with
    | Some kind -> transl_kind ~ktbl ~level kind
    | None -> snd @@ Types.kind ~name:"r" 1
  in
  let constr = transl_constr ~ktbl ~level constraints in

  let typ = transl_type ~ktbl ~tbl ~level typ in
  let constructor_typ =
    Types.Arrow (typ, Un Global, App (name, typarams))
  in

  let env, kscheme, tyscheme =
    Typing.make_type_decl ~env ~constr kargs ret_kind typ constructor_typ
  in

  (* let tyschm =
   *   let tyvars, kvars = FV.types ty in
   *   assert Name.Set.(subset tyvars @@ of_list @@ List.map fst tyargs) ;
   *   let kvars = FV.kinds kargs +++ kvars in
   *   Types.tyscheme ~constr ~tyvars:tyargs ~kvars:(Name.Set.elements kvars) ty
   * in *)
  env, name, kscheme, constructor, tyscheme
