type constant =
  | Int of int
  | Primitive of string
  | Y

type borrow = Immutable | Mutable

type match_spec = borrow option

type rec_flag =
  | Rec
  | NonRec

type pattern =
  | PUnit
  | PAny
  | PVar of Name.t
  | PConstr of Name.t * pattern option
  | PTuple of pattern list

type lambda = pattern * expr

and expr =
  | Constant of constant
  | Lambda of lambda
  | Array of expr list
  | Constructor of Name.t
  | Var of Name.t
  | Borrow of borrow * Name.t
  | ReBorrow of borrow * Name.t
  | App of expr * expr list
  | Let of rec_flag * pattern * expr * expr
  | Match of match_spec * expr * lambda list
  | Region of borrow Name.Map.t * expr
  | Tuple of expr list


module Kind = struct
  type kind =
    | Unknown
    | Un
    | Aff
    | Lin
    | KVar of Name.t
  
  type constraints = (kind * kind) list

  type scheme = {
    kvars : Name.t list ;
    constraints : constraints ;
    params : kind list ;
    kind : kind ;
  }
end

module Ty = struct

  type typ =
    | App of Name.t * typ list
    | Arrow of typ * Kind.kind * typ
    | Tuple of typ list
    | Var of Name.t
    | Borrow of borrow * Kind.kind * typ

  type scheme = { 
    kvars : Name.t list ;
    tyvars : (Name.t * Kind.kind) list ;
    constraints : Kind.constraints ;
    typ : typ ;
  }

  type constructor = {
    name : Name.t ;
    constraints : Kind.constraints ;
    typ : typ ;
  }

  type decl = {
    name : Name.t ;
    params : (Name.t * Kind.kind) list ;
    kind : Kind.kind ;
    constraints : Kind.constraints ;
    constructor : constructor list ;
  }

end

type decl = {
  rec_flag : rec_flag ;
  name : Name.t ;
  expr : expr ;
}

type def = {
  name : Name.t ;
  typ : Ty.scheme ;
}

type command =
  | ValueDecl of decl
  | TypeDecl of Ty.decl
  | ValueDef of def

module Rename = struct
  [@@@warning "-9"]
  
  module SMap = Map.Make(String)

  type env = {
    env : Name.t SMap.t ;
    tyenv : Name.t SMap.t ;
  }

  let find x env =
    match x with
    | None -> Name.create ()
    | Some x -> 
      if SMap.mem x env then
        SMap.find x env
      else
        Zoo.error "Unbound variable %s" x

  let add n k env = match n with
    | None -> assert false
    | Some n -> SMap.add n k env

  let maps env ns =
    Name.Map.fold
      (fun {name} k m -> Name.Map.add (find name env) k m)
      ns Name.Map.empty
  
  let rec pattern env = function
    | PUnit -> env, PUnit
    | PAny -> env, PAny
    | PVar {name} ->
      let new_name = Name.create ?name () in
      let env = add name new_name env in
      env, PVar new_name
    | PConstr (constr, None) ->
      let constr = find constr.name env in
      env, PConstr (constr, None)
    | PConstr (constr, Some p) ->
      let constr = find constr.name env in
      let env, p = pattern env p in
      env, PConstr (constr, Some p)
    | PTuple l ->
      let env, l = CCList.fold_map pattern env l in
      env, PTuple l
  
  let rec expr env = function
    | Lambda (pat, e) ->
      let pat, e = lambda env (pat, e) in
      Lambda (pat, e)
    | Constructor ({name}) -> Constructor (find name env)
    | Constant _ as e -> e
    | Array l  -> Array (List.map (expr env) l)
    | Tuple l  -> Tuple (List.map (expr env) l)
    | Region (ns, e) -> Region (maps env ns, expr env e)
    | Var { name } -> Var (find name env)
    | Borrow (r, {name}) -> Borrow (r, find name env)
    | ReBorrow (r, {name}) -> ReBorrow (r, find name env)
    | App (f, l) -> App (expr env f, List.map (expr env) l)
    | Let (b, pat, e1, e2) ->
      let env', pat = pattern env pat in
      let e1 = expr (if b = Rec then env' else env) e1 in
      let e2 = expr env' e2 in
      Let (b, pat, e1, e2)
    | Match (b, e, l) ->
      let e = expr env e in
      let l = List.map (lambda env) l in
      Match (b, e, l)

  and lambda env (pat, e) = 
    let env, pat = pattern env pat in
    let e = expr env e in
    (pat, e)

  let kind_expr ~kvarenv = function
    | Kind.KVar {name} -> Kind.KVar (find name kvarenv)
    | Kind.Un | Kind.Aff | Kind.Lin | Kind.Unknown as k -> k
  let constrs ~kvarenv l =
    List.map (fun (k1, k2) -> (kind_expr ~kvarenv k1, kind_expr ~kvarenv k2)) l
  let rec type_expr ~kvarenv ~tyenv ~tyvarenv = function
    | Ty.Arrow (ty1, k, ty2) ->
      Ty.Arrow (type_expr ~kvarenv ~tyenv ~tyvarenv ty1,
                kind_expr ~kvarenv k,
                type_expr ~kvarenv ~tyenv ~tyvarenv ty2)
    | Ty.App ({name}, args) ->
      Ty.App (find name tyenv, List.map (type_expr ~kvarenv ~tyenv ~tyvarenv) args)
    | Ty.Tuple (args) ->
      Ty.Tuple (List.map (type_expr ~kvarenv ~tyenv ~tyvarenv) args)
    | Ty.Var {name} ->
      Ty.Var (find name tyvarenv)
    | Ty.Borrow (r, k, ty) ->
      Ty.Borrow (r, kind_expr ~kvarenv k, type_expr ~kvarenv ~tyenv ~tyvarenv ty)

  let add_kind_var kvarenv {Name. name} =
    match name with
    | Some n when SMap.mem n kvarenv ->
      kvarenv, find name kvarenv
    | _ ->
      let n = Name.create ?name () in
      add name n kvarenv, n
  let add_kind_expr kvarenv = function
    | Kind.KVar name ->
      let kenv, n = add_kind_var kvarenv name in
      kenv, Kind.KVar n
    | Kind.Un | Kind.Aff | Kind.Lin | Kind.Unknown as k -> kvarenv, k
  let add_type_param (kvarenv, varenv) (({name} : Name.t), k) =
    let kenv, k = add_kind_expr kvarenv k in
    let n = Name.create ?name () in
    let venv = add name n varenv in
    (kenv, venv), (n,k)

  let kind_scheme {Kind. kvars; params; constraints; kind } =
    let kenv = SMap.empty in
    let kenv, kvars = CCList.fold_map add_kind_var kenv kvars in
    let kvarenv, params = CCList.fold_map add_kind_expr kenv params in
    let constraints = constrs ~kvarenv constraints in
    let kind = kind_expr ~kvarenv kind in
    {Kind. kvars; params; constraints; kind }

  let type_scheme tyenv {Ty. kvars; tyvars; constraints; typ } =
    let kenv = SMap.empty and venv = SMap.empty in
    let kenv, kvars = CCList.fold_map add_kind_var kenv kvars in
    let (kvarenv, tyvarenv), tyvars =
      CCList.fold_map add_type_param (kenv, venv) tyvars
    in
    let constraints = constrs ~kvarenv constraints in
    let typ = type_expr ~kvarenv ~tyenv ~tyvarenv typ in
    {Ty. kvars; tyvars; constraints; typ}

  let rename_constructor
      ~tyenv ~kvarenv ~tyvarenv  {Ty. name = {name}; constraints; typ} =
    let name = Name.create ?name () in
    let typ = type_expr ~kvarenv ~tyenv ~tyvarenv typ in
    let constraints = constrs ~kvarenv constraints in
    {Ty. name; constraints; typ}
  
  let command { env ; tyenv } = function
    | ValueDecl { rec_flag; name = {name} ; expr = e } ->
      let e = expr env e in
      let name = Name.create ?name () in
      ValueDecl { rec_flag; name ; expr = e }
    | TypeDecl {
        name = {name}; params; kind; constraints; constructor; 
      }  ->
      let name = Name.create ?name () in

      let kvarenv = SMap.empty and tyvarenv = SMap.empty in
      let (kvarenv, tyvarenv), params =
        CCList.fold_map add_type_param (kvarenv, tyvarenv) params
      in
      let constructor =
        List.map (rename_constructor ~kvarenv ~tyenv ~tyvarenv) constructor
      in
      let constraints = constrs ~kvarenv constraints in
      let kind = kind_expr ~kvarenv kind in
      TypeDecl { name ; params ; constructor ; constraints ; kind }
    | ValueDef { name = {name} ; typ } ->
      let typ = type_scheme tyenv typ in
      let name = Name.create ?name () in
      ValueDef { name ; typ }

end
