module T = Types

type ienv = {
  kinds : (Name.t * T.kind) Name.Tbl.t;
  types : (Name.t * T.typ) Name.Tbl.t;
  level : int;
}
let create level = {
  kinds = Name.Tbl.create 17;
  types = Name.Tbl.create 17;
  level;
}

let instance_kvar ~ienv id =
  try
    Name.Tbl.find ienv.kinds id
  with Not_found ->
    let b = T.kind ?name:id.name ienv.level in
    Name.Tbl.add ienv.kinds id b ;
    b
let instance_tyvar ~ienv id =
  try
    Name.Tbl.find ienv.types id
  with Not_found ->
    let b = T.var ?name:id.name ienv.level in
    Name.Tbl.add ienv.types id b ;
    b

let instance_kind ~ienv = function
  | Kinds.Var (_, Some _) as k -> k
  | Var (id, None) -> snd @@ instance_kvar ~ienv id
  | Constant _ as k -> k

let rec instance_type ~ienv = function
  | T.Var {contents = Link ty} -> instance_type ~ienv ty
  | T.GenericVar id -> snd @@ instance_tyvar ~ienv id
  | T.Var {contents = Unbound _} as ty -> ty
  | T.App(ty, args) ->
    let args = List.map (instance_type ~ienv) args in
    App(ty, args)
  | T.Tuple args ->
    let args = List.map (instance_type ~ienv) args in
    Tuple args
  | T.Borrow (r, k, ty) ->
    let k = instance_kind ~ienv k in
    let ty = instance_type ~ienv ty in
    Borrow (r, k, ty)
  | T.Arrow(param_ty, k, return_ty) ->
    Arrow(instance_type ~ienv param_ty,
          instance_kind ~ienv k,
          instance_type ~ienv return_ty)


let instance_constr ~ienv c =
  let rec aux (c : T.normalized_constr) = match c with
    | And l -> T.And (List.map aux l)
    | KindLeq (k1, k2) ->
      KindLeq (instance_kind ~ienv k1,
               instance_kind ~ienv k2)
    | HasKind (t, k) ->
      HasKind (instance_type ~ienv t,
               instance_kind ~ienv k)
  in 
  aux c

let included tbl vars = 
  Name.Tbl.keys tbl
  |> Iter.for_all
    (fun x -> CCList.mem ~eq:Name.equal x vars)

(** Exported functions *)

let constr level constr =
  let ienv = create level in
  instance_constr ~ienv constr

let kind_scheme ?args:(kargs=[]) ~level {T. kvars; constr; args; kind } =
  let ienv = create level in
  let kl = List.length kargs and l = List.length args in
  if kl <> l then
    Zoo.error ~kind:"Type error"
      "This type constructor is applied to %i types \
       but has only %i parameters." l kl;
  let constr =
    List.fold_left2 (fun l k1 k2 -> T.(And [KindLeq (k1,k2); l]))
      constr
      kargs
      args
  in
  let constr = instance_constr ~ienv constr in
  let kind = instance_kind ~ienv kind in
  assert (included ienv.kinds kvars);
  (constr, kind)

let typ_scheme ~level ~env {T. constr ; tyvars; kvars; ty } =
  let ienv = create level in
  let c = instance_constr ~ienv constr in
  let ty = instance_type ~ienv ty in
  let env =
    List.fold_left
      (fun env (t,k) ->
         let ty = fst @@ Name.Tbl.find ienv.types t in
         let kind = T.kscheme (instance_kind ~ienv k) in
         Env.add_ty ty kind env)
      env
      tyvars
  in
  assert (included ienv.kinds kvars);
  assert (included ienv.types @@ List.map fst tyvars);
  (env, c, ty)
