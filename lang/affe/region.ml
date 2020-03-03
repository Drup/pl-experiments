(** Automatic region annotation *)

open Syntax
module S = Name.Set
module M = Name.Map

type use =
  | Borrow of borrow
  | Shadow of borrow
  | Full

let get_borrows m =
  M.fold (fun k v m -> match v with
      | Borrow b -> M.add k b m
      | Full | Shadow _ -> m
    ) m M.empty
let region ns e =
  let m = get_borrows ns in
  if M.is_empty m then e else Region (m, e)

let get_vars m = M.keys m |> S.of_iter
let add_opt m k b = match b with
  | None -> m
  | Some v -> M.add k v m
let update_all f m =
  M.fold (fun k v m -> match f k (Some v) with
      | None -> m
      | Some v' -> M.add k v' m
    ) m M.empty

let rec vars_in_pattern (p : pattern) = match p with
  | PUnit | PAny -> S.empty
  | PVar v -> S.singleton v
  | PConstr (_, None) -> S.empty
  | PConstr (_, Some p) -> vars_in_pattern p
  | PTuple l ->
    List.fold_left (fun s p -> S.union s @@ vars_in_pattern p) S.empty l

let mergeL l =
  let classify (state : 'a) i e : 'a = match state, e with
    | `None, None -> `None
    | `None, Some (Borrow Immutable | Shadow Immutable) -> `Immutable
    | `Immutable,
      (None | Some (Borrow Immutable | Shadow Immutable))
      -> `Immutable
    | (`None | `Immutable),
      Some (Borrow Mutable | Shadow Mutable)
      -> `OneMutable i
    | `OneMutable i, None -> `OneMutable i
    | `OneMutable _, Some _ -> `Many
    | `Many, _ -> `Many
    | `Full, _ | _, Some Full -> `Full
  in
  let get_status k =
    let l = Iter.map (M.find_opt k) @@ Iter.of_list l in
    Iter.foldi classify `None l
  in
  let all_vars = List.fold_left S.union S.empty @@ List.map get_vars l in
  let status = S.fold (fun k m -> M.add k (get_status k) m) all_vars M.empty in
  let final_vars =
    M.fold (fun k b m -> match b with
        | `None -> m
        | `Immutable -> M.add k (Borrow Immutable) m
        | `OneMutable _ -> M.add k (Borrow Mutable) m
        | `Full -> M.add k Full m
        | `Many -> m
      ) status M.empty
  in
  let update_one i k b =
    match M.find k status, b with
    | _, None -> None
    | `None, b -> b
    | `Immutable,
      Some (Borrow Immutable | Shadow Immutable)
      -> None
    | `Immutable,
      Some (Borrow Mutable | Shadow Mutable | Full)
      -> assert false
    | `OneMutable _, Some (Shadow Mutable) -> None
    | `OneMutable j, b ->
      if i < j then b
      else if i = j then None
      else assert false
    | `Many, Some Shadow _ -> None
    | `Many, b -> b
    | `Full, Some Full -> None
    | `Full, Some Shadow _ -> None
    | `Full, b -> b
  in
  let update_all i (e, m) = region (update_all (update_one i) m) e in
  final_vars, update_all

let get_vars vars1 vars2 =
  let f b1 b2 = match b1, b2 with
    | None, b | b, None ->
      None, b, None
    | Some Full, _ ->
      None, b1, b2
    | _, Some Full ->
      b1, b2, None
    | Some Borrow Immutable, Some Borrow Immutable
    | Some Shadow Immutable, Some Borrow Immutable
    | Some Borrow Immutable, Some Shadow Immutable
      -> None, Some (Borrow Immutable), None
    | Some Shadow Immutable, Some Shadow Immutable
      -> None, Some (Shadow Immutable), None
    | Some Borrow Immutable, Some (Borrow Mutable | Shadow Mutable) ->
      b1, b2, None
    | Some (Borrow Mutable | Shadow Mutable), Some Borrow Immutable  ->
      None, b1, b2
    | Some Shadow Immutable, (Some (Borrow Mutable | Shadow Mutable) as b)
    | (Some (Borrow Mutable | Shadow Mutable) as b), Some Shadow Immutable
      -> None, b, None
    | Some Shadow Mutable, Some Shadow Mutable
      -> None, b1, None
    | Some Borrow Mutable, _
    | _, Some Borrow Mutable
      -> b1, Some (Shadow Mutable), b2
  in
  let all_vars = S.union (get_vars vars1) (get_vars vars2) in
  S.fold (fun k (ml, mc, mr) ->
      let bl, bc, br = f (M.find_opt k vars1) (M.find_opt k vars2) in
      add_opt ml k bl, add_opt mc k bc, add_opt mr k br
    )
    all_vars
    (M.empty, M.empty, M.empty)

let merge2 (e1, vars1) (e2, vars2) =
  let vars1, vars, vars2 = get_vars vars1 vars2 in
  let e1 = region vars1 e1 in
  let e2 = region vars2 e2 in
  e1, vars, e2

let mergeCase (e1, vars1) aCases =
  (* TODO: This is not as careful as it should be, we should
     treat the case where case disagree on borrow specially *)
  let f _ b1 b2 = match b1, b2 with
    | Full, _ | _, Full -> Some Full
    | Borrow b1, Borrow b2 -> Some (Borrow (Types.Borrow.max b1 b2))
    | Shadow b1, Shadow b2 -> Some (Shadow (Types.Borrow.max b1 b2))
    | Shadow Mutable, Borrow _ | Borrow _, Shadow Mutable
      -> Some (Borrow Mutable)
    | Borrow b, Shadow Immutable | Shadow Immutable, Borrow b
      -> Some (Borrow b)
  in
  let cases, vars2 =
    let on_cases (cases, vars) (p,e,vars') =
      (p,e)::cases, M.union f vars vars'
    in
    List.fold_left on_cases ([],M.empty) aCases
  in
  let vars1, vars, vars2 = get_vars vars1 vars2 in
  let e1 = region vars1 e1 in
  let cases = List.map (fun (p,e) -> (p, region vars2 e)) cases in
  e1, vars, cases


let foldAccumInt i0 f l0 =
  let _, l = List.fold_left (fun (i,l) a -> i+1, (f i a :: l)) (i0, []) l0 in
  List.rev l

let rec annotate (e0 : expr) = match e0 with
  | Constant _
  | Constructor _
    ->
    e0, M.empty
  | Var x ->
    e0, M.singleton x Full
  | Borrow (b, x)
  | ReBorrow (b, x) ->
    e0, M.singleton x (Borrow b)
  | Lambda (pat , e) ->
    let e, vars = annotate_with_pat pat e in
    Lambda (pat, e), vars
  | Let (recflag, pat, e1, e2) ->
    let a1 = annotate e1 in
    let a2 = annotate_with_pat pat e2 in
    let e1, vars, e2 = merge2 a1 a2 in
    Let (recflag, pat, e1, e2), vars    
  | App (e, l) ->
    let e, vars = annotate e in
    let al = List.map annotate l in
    let final_vars, aux = mergeL (vars:: List.map snd al) in
    let e = aux 0 (e, vars) in
    let l = foldAccumInt 1 aux al in
    App (e, l), final_vars
  | Array l ->
    let al = List.map annotate l in
    let final_vars, aux = mergeL (List.map snd al) in
    let l = foldAccumInt 0 aux al in
    Array l, final_vars
  | Tuple l ->
    let al = List.map annotate l in
    let final_vars, aux = mergeL (List.map snd al) in
    let l = foldAccumInt 0 aux al in
    Tuple l, final_vars
  | Region (_orig_vars, e) ->
    (* assert (M.is_empty _orig_vars); *)
    let e, vars = annotate e in
    region vars e, M.empty
  | Match (spec, e, cases) ->
    let a = annotate e in
    let a_cases =
      let on_cases (p,e) =
        let e, vars' = annotate_with_pat p e in (p,e,vars')
      in
      List.map on_cases cases
    in
    let e, vars, cases = mergeCase a a_cases in
    Match (spec, e, cases), vars

and annotate_with_pat pat e = 
  let e, vars = annotate e in
  let bset = vars_in_pattern pat in
  let is_bound k _ = S.mem k bset in
  let bound_vars, unbound_vars = M.partition is_bound vars in
  let e = region bound_vars e in
  e, unbound_vars

let annotate_command (c : command) = match c with
  | ValueDecl { rec_flag; name; expr } ->
    let expr, vars = annotate expr in
    let expr = region vars expr in 
    ValueDecl { rec_flag; name; expr }
  | TypeDecl _
  | ValueDef _ -> c
   
