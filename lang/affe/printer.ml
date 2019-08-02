open Syntax
module T = Types

let debug = ref false

let bold =
  if !debug then
    fun fmt s -> Format.fprintf fmt "@<0>%s%s@<0>%s" "\027[1m" s "\027[0m"
  else
    Fmt.string

let constant fmt = function
  | Int i -> Format.pp_print_int fmt i
  | Primitive s -> Fmt.pf fmt "%%%a" bold s
  | Y -> bold fmt "Y" 

let indice_array = [|"₀";"₁";"₂";"₃";"₄";"₅";"₆";"₇";"₈";"₉"|]
let rec digits fmt i =
  if i < 0 then
    Format.pp_print_string fmt "₋"
  else if i < 10 then
    Format.pp_print_string fmt indice_array.(i)
  else begin
    digits fmt (i/10) ;
    Format.pp_print_string fmt indice_array.(i mod 10)
  end

let name_with_digits fmt {Name. name ; id } =
  Format.fprintf fmt "%s%a" (CCOpt.get_or ~default:"_" name)  digits id
let name_no_digits fmt {Name. name ; _ } =
  Format.fprintf fmt "%s" (CCOpt.get_or ~default:"_" name)

let name = if !debug then name_with_digits else name_no_digits

(** Expressions and Patterns *)

let borrow = function Immutable -> "" | Mutable -> "!"

let rec pattern fmt = function
  | PAny -> Fmt.pf fmt "_"
  | PUnit -> Fmt.pf fmt "()"
  | PVar n -> name fmt n
  | PConstr (constr, None) ->
    Format.fprintf fmt "%a" name constr
  | PConstr (constr, Some pat) ->
    Format.fprintf fmt "%a (%a)" name constr pattern pat
  | PTuple l -> 
    Format.fprintf fmt "@[(@ %a@ )@]" Fmt.(list ~sep:(unit ",@ ") pattern) l

let binop = [ "+"; "-"; "*"; "/"; "<"; ">"; "=" ]

let rec expr
  = fun fmt -> function
    | Constant c -> constant fmt c
    | Constructor c -> name fmt c
    | Lambda (n,e) ->
      Format.fprintf fmt "@[%a %a %a@ %a@]"
        bold "fun"
        pattern n
        bold "->"
        expr e
    | Array a ->
      Format.fprintf fmt "@[[|@ %a@ |]@]" Fmt.(list ~sep:(unit ";@ ") expr) a
    | Tuple a ->
      Format.fprintf fmt "@[(@ %a@ )@]" Fmt.(list ~sep:(unit ",@ ") expr) a
    | App (Constant (Primitive s), [e1; e2]) when List.mem s binop ->
      Format.fprintf fmt "@[<2>@[%a@]@ %s @[%a@]@]"
        expr_with_paren e1
        s
        expr_with_paren e2
    | Var v -> name fmt v
    | Borrow (r,v) ->
      Format.fprintf fmt "&%s%a" (borrow r) name v
    | ReBorrow (r,v) ->
      Format.fprintf fmt "&&%s%a" (borrow r) name v
    | App (f,e) ->
      Format.fprintf fmt "@[<2>@[%a@]@ %a@]"
        expr_with_paren f
        Format.(pp_print_list ~pp_sep:pp_print_space expr_with_paren) e
    | Let (b,pat,e1,e2) ->
      Format.fprintf fmt "@[@[<2>%a %a %a@ %a@]@ %a@ %a@]"
        bold (if b = Rec then "let rec" else "let")
        pattern pat
        bold "=" expr e1
        bold "in" expr e2
    | Match (b, e, l) ->
      let sep = Fmt.cut in
      let case fmt (p, e) =
        Fmt.pf fmt "@[<2>| %a ->@ %a@]" pattern p expr e
      in
      let s = match b with
        | None -> ""
        | Some Immutable -> "&"
        | Some Mutable -> "&!"
      in
      Fmt.pf fmt "@[<v2>@[%a@ %a@ %a@]@ %a@]"
        bold ("match"^s) expr e bold "in"
        (Fmt.list ~sep case) l
    | Region (ns, e) ->
      let pp fmt () =
        Fmt.pf fmt "%a | %a"
          Fmt.(iter_bindings ~sep:sp Name.Map.iter (pair name nop)) ns expr e
      in
      Fmt.braces pp fmt ()

and expr_with_paren fmt x =
  let must_have_paren = match x with
    | App _
    | Let _
    | Match _
    | Lambda _
      -> true
    | Constant _
    | Array _
    | Tuple _
    | Constructor _
    | Var _
    | Borrow (_, _)
    | ReBorrow (_, _)
    | Region _
      -> false
  in
  Format.fprintf fmt
    (if must_have_paren then "@[(%a@])" else "%a") expr x 

(** Types *)

module UsedNames = CCHashtbl.Make(CCString)
type naming_env = {
  tbl : string Name.Tbl.t;
  used : int UsedNames.t;
}
let create_naming_env () = {
  tbl = Name.Tbl.create 4;
  used = UsedNames.create 4;
}

let fresh_name pool used =
  let l = String.length pool in
  let rec mk_string i = 
    if i < l then
      pool.[i] :: []
    else
      pool.[i mod l] :: mk_string (i / l)
  in
  let rec try_all i =
    let s = CCString.of_list @@ mk_string i in
    match UsedNames.find_opt used s with
    | Some _ -> try_all (i+1)
    | None -> s
  in
  try_all 0

let get_print_name env pool n =
  match Name.Tbl.find_opt env.tbl n with
  | Some n -> n
  | None ->
    begin
      match n.name with
      | None ->
        let name = fresh_name pool env.used in
        Name.Tbl.add env.tbl n name;
        UsedNames.add env.used name 1;
        name
      | Some name ->
        begin match UsedNames.find_opt env.used name with
          | None ->
            Name.Tbl.add env.tbl n name;
            UsedNames.add env.used name 1;
            name
          | Some i ->
            UsedNames.add env.used name (i+1);
            name ^ string_of_int i
        end
    end 

let typool = "abcdef"
let tyname ?(unbound=false) env fmt n = 
  Format.fprintf fmt "'%s%s" (if unbound then "_" else "")
    (get_print_name env typool n)
let kpool = "klmn"
let kname ?(unbound=false) env fmt n =
  Format.fprintf fmt "^%s%s" (if unbound then "_" else "")
    (get_print_name env kpool n)

let region fmt = function
  | Kinds.Region.Region i -> digits fmt i
  | Never -> Fmt.string fmt "ₙ"
  | Global -> ()

let rec kvar
  = fun env fmt -> function
  | Kinds.Unbound (n,_) -> kname ~unbound:true env fmt n
  | Link t -> kind env fmt t

and kind env fmt = function
  | Kinds.Un r -> Format.fprintf fmt "un%a" region r
  | Aff r -> Format.fprintf fmt "aff%a" region r
  | Lin r -> Format.fprintf fmt "lin%a" region r
  | Var { contents = x } -> kvar env fmt x
  | GenericVar n -> kname env fmt n

let use env fmt (u : Types.Use.t) = match u with
  | Shadow _ -> Fmt.pf fmt "Shadow"
  | Borrow (b, ks) -> Fmt.pf fmt "&%s(%a)" (borrow b) (Fmt.list @@ kind env) ks
  | Normal ks -> Fmt.pf fmt "Use(%a)" (Fmt.list @@ kind env) ks

let rec tyvar
  = fun env fmt -> function
  | T.Unbound (n,_) -> tyname ~unbound:true env fmt n
  | T.Link t -> typ_with_paren env fmt t

and typ
  = fun env fmt -> function
  | T.App (f,[]) ->
    name fmt f
  | T.Borrow (r, k, t) ->
    Format.fprintf fmt "&%s(%a,%a)" (borrow r) (kind env) k (typ env) t
  | T.Tuple l ->
    let pp_sep fmt () = Format.fprintf fmt " *@ " in
    Format.fprintf fmt "@[<2>%a@]"
      (Format.pp_print_list ~pp_sep @@ typ env) l
  | T.App (f,e) ->
    let pp_sep fmt () = Format.fprintf fmt ",@ " in
    Format.fprintf fmt "@[<2>(%a)@ %a@]"
      (Format.pp_print_list ~pp_sep @@ typ env) e  name f
  | T.Arrow (a, Un Global,b) ->
    Format.fprintf fmt "%a -> %a" (typ_with_paren env) a  (typ env) b
  | T.Arrow (a,k,b) ->
    Format.fprintf fmt "%a -{%a}> %a"
      (typ_with_paren env) a (kind env) k  (typ env) b
  | T.Var { contents = x } -> tyvar env fmt x
  | T.GenericVar n -> tyname env fmt n

and typ_with_paren env fmt x =
  let must_have_paren = match x with
    | T.Arrow _ -> true
    | _ -> false
  in
  Format.fprintf fmt
    (if must_have_paren then "@[(%a@])" else "%a") (typ env) x

(** Constraints *)


let rec flatten' = function
  | T.And l -> flattenL l
  | c -> [c]
and flattenL l = CCList.flat_map flatten' l

let rec constrs env fmt (x: Types.normalized_constr) = match x with
  | KindLeq (k1, k2) ->
    Format.fprintf fmt "(%a < %a)" (kind env) k1 (kind env) k2
  | HasKind (ty, k) -> 
    Format.fprintf fmt "(%a : %a)" (typ env) ty (kind env) k
  | And l ->
    let l = flattenL l in
    let pp_sep fmt () = Format.fprintf fmt " &@ " in
    Format.fprintf fmt "%a" Format.(pp_print_list ~pp_sep @@ constrs env) l

(** Schemes *)

let kscheme fmt {T. constr = c ; kvars ; args ; kind = k } =
  let env = create_naming_env () in
  let pp_sep fmt () = Format.fprintf fmt ", " in
  let pp_arrow fmt () = Format.fprintf fmt "@ ->@ " in
  Format.pp_open_box fmt 2 ;
  begin
    if kvars <> [] then
      Format.fprintf fmt "∀%a.@ "
        Format.(pp_print_list ~pp_sep @@ kname ~unbound:false env) kvars
  end;
  begin
    if c <> T.And [] then
      Format.fprintf fmt "%a =>@ " (constrs env) c
  end;
  Format.fprintf fmt "%a"
    Format.(pp_print_list ~pp_sep:pp_arrow @@ kind env) (args@[k]);
  Format.pp_close_box fmt ();
  ()

and scheme fmt {T. constr = c ; tyvars ; kvars ; ty } =
  let env = create_naming_env () in
  let pp_sep fmt () = Format.fprintf fmt ",@ " in
  Format.pp_open_box fmt 0 ;
  begin
    let has_kinds = not @@ CCList.is_empty kvars in
    let has_types = not @@ CCList.is_empty tyvars in
    if has_kinds || has_types then begin
      Fmt.pf fmt "∀@[";
      Format.(pp_print_list ~pp_sep (kname ~unbound:false env)) fmt kvars ;
      if has_kinds && has_types then pp_sep fmt () ;
      Format.(pp_print_list ~pp_sep (tyname ~unbound:false env)) fmt tyvars;
      Fmt.pf fmt "@].@ ";
    end;
  end;
  begin
    if c <> T.And [] then
      Format.fprintf fmt "@[%a@] =>@ " (constrs env) c
  end;
  Fmt.box (typ env) fmt ty;
  Format.pp_close_box fmt ();
  ()

let env fmt env =
  let print_env pp_key pp_val fmt e =
    Format.pp_print_list
      ~pp_sep:Format.pp_print_cut
      (fun fmt (k,ty) ->
         Format.fprintf fmt "%a: %a" pp_key k  pp_val ty)
      fmt
    @@ Name.Map.bindings e
  in
  let print_env prefix pp_key pp_val fmt e =
    if Name.Map.is_empty e then () else
      Format.fprintf fmt "%s:@;<1 2>@[<v>%a@]@."
        prefix (print_env pp_key pp_val) e
  in
  Format.fprintf fmt "%a%a%a"
    (print_env "Variables:" name scheme) env.Env.vars
    (print_env "Type Constructors:" name kscheme) env.Env.constr
