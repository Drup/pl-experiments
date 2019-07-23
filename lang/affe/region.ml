(** Automatic region annotation *)

open Syntax
module S = Name.Set
module M = Name.Map

let region ns e =
  if M.is_empty ns then e else Region (ns, e)

let get_vars m = M.keys m |> S.of_seq
let add_opt m k b = match b with
  | None -> m
  | Some v -> M.add k v m
let update_all f m =
  M.fold (fun k v m -> match f k (Some v) with
      | None -> m
      | Some v' -> M.add k v' m
    ) m M.empty

let rec vars_in_pattern (p : pattern) = match p with
  | PUnit -> S.empty
  | PVar v -> S.singleton v
  | PConstr (_, None) -> S.empty
  | PConstr (_, Some p) -> vars_in_pattern p
  | PTuple l ->
    List.fold_left (fun s p -> S.union s @@ vars_in_pattern p) S.empty l

let mergeL l =
  let classify (state : 'a) i e : 'a = match state, e with
    | `None, None -> `None
    | `None, Some Immutable -> `Immutable
    | (`None | `Immutable), Some Mutable -> `OneMutable i
    | `Immutable, (None | Some Immutable) -> `Immutable
    | `OneMutable i, None -> `OneMutable i
    | `OneMutable _, Some _ -> `Many
    | `Many, _ -> `Many
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
        | `Immutable -> M.add k Immutable m
        | `OneMutable _ -> M.add k Mutable m
        | `Many -> m
      ) status M.empty
  in
  let update_one i k b =
    match M.find_opt k status, b with
    | None, _ -> assert false
    | _, None -> None
    | Some `None, b -> b
    | Some `Immutable, Some Immutable -> None
    | Some `Immutable, Some Mutable -> assert false
    | Some `OneMutable j, b ->
      if i < j then b else assert false
    | Some `Many, b -> b
  in
  let update_all i (e, m) = region (update_all (update_one i) m) e in
  final_vars, update_all

let merge2 (e1, vars1) (e2, vars2) =
  let f b1 b2 = match b1, b2 with
    | None, b | b, None -> None, b, None
    | Some Immutable, Some Immutable -> None, Some Immutable, None
    | Some Immutable, Some Mutable -> Some Immutable, Some Mutable, None
    | Some Mutable, Some b -> Some Mutable, None, Some b
  in
  let all_vars = S.union (get_vars vars1) (get_vars vars2) in
  let vars1, vars, vars2 =
    S.fold (fun k (ml, mc, mr) ->
        let bl, bc, br = f (M.find_opt k vars1) (M.find_opt k vars2) in
        add_opt ml k bl, add_opt mc k bc, add_opt mr k br
      )
      all_vars
      (M.empty, M.empty, M.empty)
  in
  let e1 = region vars1 e1 in
  let e2 = region vars2 e2 in
  e1, vars, e2

let foldAccumInt i0 f l0 =
  let _, l = List.fold_left (fun (i,l) a -> i+1, (f i a :: l)) (i0, []) l0 in
  List.rev l

let rec annotate (e0 : expr) = match e0 with
  | Constant _
  | Var _
  | Constructor _
    ->
    e0, M.empty
  | Borrow (b, x)
  | ReBorrow (b, x) -> 
    e0, M.singleton x b
  | Lambda (pat , e) ->
    let e, vars = annotate_with_pat pat e in
    Lambda (pat, e), vars
  | Let (recflag, pat, e1, e2) ->
    let a1 = annotate_with_pat pat e1 in
    let a2 = annotate e2 in
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
  | Match (_, _, _) -> assert false

and annotate_with_pat pat e = 
  let e, vars = annotate e in
  let bset = vars_in_pattern pat in
  let bound_vars, unbound_vars = M.partition (fun k _ -> S.mem k bset) vars in
  let e = region bound_vars e in
  e, unbound_vars

let annotate_command (c : command) = match c with
  | ValueDecl { rec_flag; name; expr } ->
    let expr, vars = annotate expr in
    let expr = region vars expr in 
    ValueDecl { rec_flag; name; expr }
  | TypeDecl _
  | ValueDef _ -> c
   
