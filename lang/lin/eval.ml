open Syntax

type address = Name.t
type value =
  | Array of value array
  | Constant of constant
  | Closure of env * Name.t * expr
  | Address of address
  | Constructor of Name.t * value list
  | Borrow of borrow * address
and env = value Name.Map.t

(** Global Environment *)

let initial_env = Name.Map.empty
let add = Name.Map.add
let find x env =
  if Name.Map.mem x env then
    Name.Map.find x env
  else
    Zoo.error "Unbound variable %a" Printer.name x

(** Substitutions *)

let rec subst_value x v = function
  | Constructor c -> Constructor c
  | Constructor (c, Some v') -> Constructor (c, Some (subst_value x v v'))
  | Constant c -> Constant c
  | Lambda (y,e) when not @@ Name.equal x y ->
    (Lambda (y, subst x v e))
  | Lambda (_, _)
  | Array _
  | Unit
    as v -> v

(** e[x -> v] *)
and subst x v e = match e with
  | Var y when Name.equal x y -> V v
  | Var n -> Var n
  | V v' -> V (subst_value x v v')
  | App (f,e) -> App (subst x v f, List.map (subst x v) e)
  | Let (y,e1,e2) when not @@ Name.equal x y ->
    Let (y, subst x v e1, subst x v e2)
  | Match (constr, y,e1,e2) when not @@ Name.equal x y ->
    Match (constr, y, subst x v e1, subst x v e2)
  | Let (y,e1,e2) ->
    Let (y, subst x v e1, e2)
  | Match (constr, y, e1, e2) ->
    Match (constr, y, subst x v e1, e2)
  | Borrow (r, e) -> Borrow (r, subst x v e)

let subst_env = Name.Map.fold subst

(** Evaluation *)

let value x = V x
let lambda n b = V (Lambda (n, b))
let const x = V (Constant x)
let delta c v = match c,v with
  | Int _, [] -> None
    
  | Plus, [ Constant (Int i) ; Constant (Int j) ] ->
    Some (V (Constant (Int (i + j))))
  | Plus, [ Constant (Int i) ] ->
    let n = Name.create ~name:"i" () in
    Some (V (Lambda (n, App (const Plus, [const @@ Int i; Var n]))))

  (* | Alloc, [ Constant (Int i) ; v ] -> Some (V (Array (Array.make i v))) *)
  | Get, [ Array r ; Constant (Int i) ] -> Some (V r.(i))
  (* | Set, [ Array r ] ->
   *   let n = Name.create ~name:"r" () in
   *   Some (V (Lambda (n, App (const Set, [V (Ref r); Var n])))) *)
  | Set, [ Array r ; Constant (Int i) ; v ] -> r.(i) <- v ; Some (V Unit)

  | Y, ve::t ->
    let n = Name.create ~name:"Y" () in
    let args = List.map value t in
    Some (App (V ve, lambda n (App(const Y, [V ve; Var n])) :: args))
    
  | _ -> None

exception Not_reducible : expr -> exn

let log_eval i = Format.printf "%s< %a@." (String.make i ' ') Printer.expr
let log_val i = Format.printf "%s> %a@." (String.make i ' ') Printer.value

let reduction_failure e = 
  Zoo.error ~kind:"Execution error"
    "The following expression can not be reduced:@.%a" Printer.expr e

let rec eval i e = match e with
  | V v -> v
  | Borrow (_,e) -> eval i e
  | Var _ -> reduction_failure e
  | Let (x,e1,e2) ->
    (* log_eval i e ; *)
    let v = eval (i+1) e1 in
    let v' = eval (i+1) @@ subst x v e2 in
    (* log_val i v' ; *)
    v'
  | App(f,l) ->
    (* log_eval i e ; *)
    let vf = eval (i+1) f in
    let ve = List.map (eval @@ i+1) l in
    let v = eval_app (i+1) e vf ve in
    (* log_val i v ; *)
    v
  | Match (constr, x, e1, e2) ->
    let v = eval (i+1) e1 in
    match v with
    | Constructor (constr', Some param) when Name.equal constr constr' ->
      eval (i+1) @@ subst x param e2
    | _ -> reduction_failure e

and eval_app i eorig f l = match f, l with
  | _, [] -> f
  | Constructor (x, None), [param] -> Constructor (x, Some param)
  | Constructor (_, _), _ -> reduction_failure eorig
  | Array _, _ -> reduction_failure eorig
  | Unit, _ -> reduction_failure eorig
  | Lambda(x, body), (v :: t) ->
    eval_app i eorig (eval (i+1) @@ subst x v body) t
  | Constant c, l ->
    begin match delta c l with
      | Some x -> eval (i+1) x
      | None -> reduction_failure eorig
    end

let execute env p = eval 0 @@ subst_env env p
