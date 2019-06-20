type constant =
  | Int of int
  | Primitive of string
  (* | Plus
   * | Alloc
   * | Free
   * | Get
   * | Set *)
  | Y

type borrow = Immutable | Mutable

type rec_flag =
  | Rec
  | NonRec

type pattern =
  | PUnit
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
  (* | Let of Name.t * expr * expr *)
  | Let of rec_flag * pattern * expr * expr
  | Match of expr * lambda list
  | Region of Name.t * expr
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
    vars : Name.t list ;
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
    kparams : Name.t list ;
    params : (Name.t * Kind.kind) list ;
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
    if SMap.mem x env then
      SMap.find x env
    else
      Zoo.error "Unbound variable %s" x

  let add n k env = SMap.add n k env

  let rec pattern env = function
    | PUnit -> env, PUnit
    | PVar {name} ->
      let new_name = Name.create ~name () in
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
    | Region ({name},e) -> Region (find name env, expr env e)
    | Var { name } -> Var (find name env)
    | Borrow (r, {name}) -> Borrow (r, find name env)
    | ReBorrow (r, {name}) -> ReBorrow (r, find name env)
    | App (f, l) -> App (expr env f, List.map (expr env) l)
    | Let (b, pat, e1, e2) ->
      let env', pat = pattern env pat in
      let e1 = expr (if b = Rec then env' else env) e1 in
      let e2 = expr env' e2 in
      Let (b, pat, e1, e2)
    | Match (e, l) ->
      let e = expr env e in
      let l = List.map (lambda env) l in
      Match (e, l)
    (* | Let ({name}, e1, e2) ->
     *   let e1 = expr env e1 in
     *   let new_name = Name.create ~name () in
     *   let env = add name new_name env in
     *   let e2 = expr env e2 in
     *   Let (new_name, e1, e2) *)

  and lambda env (pat, e) = 
    let env, pat = pattern env pat in
    let e = expr env e in
    (pat, e)

  let kind_expr ~kenv = function
    | Kind.KVar {name} -> Kind.KVar (find name kenv)
    | Kind.Un | Kind.Aff | Kind.Lin | Kind.Unknown as k -> k
  let constrs ~kenv l =
    List.map (fun (k1, k2) -> (kind_expr ~kenv k1, kind_expr ~kenv k2)) l
  let rec type_expr ~kenv ~tyenv ~venv = function
    | Ty.Arrow (ty1, k, ty2) ->
      Ty.Arrow (type_expr ~kenv ~tyenv ~venv ty1,
                kind_expr ~kenv k,
                type_expr ~kenv ~tyenv ~venv ty2)
    | Ty.App ({name}, args) ->
      Ty.App (find name tyenv, List.map (type_expr ~kenv ~tyenv ~venv) args)
    | Ty.Tuple (args) ->
      Ty.Tuple (List.map (type_expr ~kenv ~tyenv ~venv) args)
    | Ty.Var {name} ->
      Ty.Var (find name venv)
    | Ty.Borrow (r, k, ty) ->
      Ty.Borrow (r, kind_expr ~kenv k, type_expr ~kenv ~tyenv ~venv ty)

  let add_kind_var kenv {Name. name} = 
    if SMap.mem name kenv then
      kenv, find name kenv
    else
      let n = Name.create ~name () in
      add name n kenv, n
  let add_kind_expr kenv = function
    | Kind.KVar name ->
      let kenv, n = add_kind_var kenv name in
      kenv, Kind.KVar n
    | Kind.Un | Kind.Aff | Kind.Lin | Kind.Unknown as k -> kenv, k
  let add_type_param (kenv, venv) (({name} : Name.t), k) =
    let kenv, k = add_kind_expr kenv k in
    let n = Name.create ~name () in
    let venv = add name n venv in
    (kenv, venv), (n,k)

  let kind_scheme {Kind. vars; params; constraints; kind } =
    let kenv = SMap.empty in
    let kenv, vars = CCList.fold_map add_kind_var kenv vars in
    let kenv, params = CCList.fold_map add_kind_expr kenv params in
    let constraints = constrs ~kenv constraints in
    let kind = kind_expr ~kenv kind in
    {Kind. vars; params; constraints; kind }

  let type_scheme tyenv {Ty. kparams; params; constraints; typ } =
    let kenv = SMap.empty and venv = SMap.empty in
    let kenv, kparams = CCList.fold_map add_kind_var kenv kparams in
    let (kenv, venv), params =
      CCList.fold_map add_type_param (kenv, venv) params
    in
    let constraints = constrs ~kenv constraints in
    let typ = type_expr ~kenv ~tyenv ~venv typ in
    {Ty. kparams; params; constraints; typ}

  let rename_constructor ~tyenv ~kenv ~venv  {Ty. name = {name}; constraints; typ} =
    let name = Name.create ~name () in
    let typ = type_expr ~kenv ~tyenv ~venv typ in
    let constraints = constrs ~kenv constraints in
    {Ty. name; constraints; typ}
  
  let command { env ; tyenv } = function
    | ValueDecl { rec_flag; name = {name} ; expr = e } ->
      let e = expr env e in
      let name = Name.create ~name () in
      ValueDecl { rec_flag; name ; expr = e }
    | TypeDecl {
        name = {name}; params; kind; constraints; constructor; 
      }  ->
      let name = Name.create ~name () in

      let kenv = SMap.empty and venv = SMap.empty in
      let (kenv, venv), params =
        CCList.fold_map add_type_param (kenv, venv) params
      in
      let constructor = List.map (rename_constructor ~kenv ~tyenv ~venv) constructor in
      let constraints = constrs ~kenv constraints in
      let kind = kind_expr ~kenv kind in
      TypeDecl { name ; params ; constructor ; constraints ; kind }
    | ValueDef { name = {name} ; typ } ->
      let typ = type_scheme tyenv typ in
      let name = Name.create ~name () in
      ValueDef { name ; typ }

end
