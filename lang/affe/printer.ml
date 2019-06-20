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
  Format.fprintf fmt "%s%a" name  digits id
let name_no_digits fmt {Name. name ; _ } =
  Format.fprintf fmt "%s" name

let name = if !debug then name_with_digits else name_no_digits

let tyname ?(unbound=false) fmt n =
  Format.fprintf fmt "'%s%a" (if unbound then "_" else "")
    name_with_digits n
let kname ?(unbound=false) fmt n =
  Format.fprintf fmt "^%s%a" (if unbound then "_" else "")
    name_with_digits n
(* let rname ?(unbound=false) fmt n =
 *   Format.fprintf fmt "^%s%a" (if unbound then "_" else "") name n *)

let borrow = function Immutable -> "" | Mutable -> "!"

let rec pattern fmt = function
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
    | Match (e, l) ->
      let sep = Fmt.cut in
      let case fmt (p, e) =
        Fmt.pf fmt "@[<2>| %a ->@ %a@]" pattern p expr e
      in
      Fmt.pf fmt "@[<v2>@[%a@ %a@ %a@]@ %a@]"
        bold "match" expr e bold "in"
        (Fmt.list ~sep case) l
    | Region (v, e) ->
      let pp fmt (v, e) = Fmt.pf fmt "%a | %a" name v expr e in
      Fmt.braces pp fmt (v,e)

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

let rec typ_need_paren = function
  | T.Arrow _ -> true
  | T.Var { contents = Link t } -> typ_need_paren t
  | _ -> false

(* let rec rvar
 *   = fun fmt -> function
 *   | T.RUnbound (n,_) -> kname ~unbound:true fmt n
 *   | T.RLink t -> region fmt t
 * 
 * and region fmt = function
 *   | T.RVar { contents = x } -> rvar fmt x
 *   | T.RGenericVar n -> rname fmt n *)

let region fmt = function
  | T.Region.Region i -> digits fmt i
  | Never -> Fmt.string fmt "ₙ"
  | Global -> ()

let rec kvar
  = fun fmt -> function
  | T.KUnbound (n,_) -> kname ~unbound:true fmt n
  | T.KLink t -> kind fmt t

and kind fmt = function
  | T.Un r -> Format.fprintf fmt "un%a" region r
  | T.Aff r -> Format.fprintf fmt "aff%a" region r
  | T.Lin r -> Format.fprintf fmt "lin%a" region r
  | T.KVar { contents = x } -> kvar fmt x
  | T.KGenericVar n -> kname fmt n

let use fmt (u : Types.Use.t) = match u with
  | Shadow _ -> Fmt.pf fmt "Shadow"
  | Borrow (b, ks) -> Fmt.pf fmt "&%s(%a)" (borrow b) (Fmt.list kind) ks
  | Normal ks -> Fmt.pf fmt "Use(%a)" (Fmt.list kind) ks

let rec tyvar
  = fun fmt -> function
  | T.Unbound (n,_) -> tyname ~unbound:true fmt n
  | T.Link t -> typ_with_paren fmt t

and typ
  = fun fmt -> function
  | T.App (f,[]) ->
    name fmt f
  | T.Borrow (r, k, t) ->
    Format.fprintf fmt "&%s(%a,%a)" (borrow r) kind k typ t
  | T.Tuple l ->
    let pp_sep fmt () = Format.fprintf fmt " *@ " in
    Format.fprintf fmt "@[<2>%a@]"
      (Format.pp_print_list ~pp_sep typ) l
  | T.App (f,e) ->
    let pp_sep fmt () = Format.fprintf fmt ",@ " in
    Format.fprintf fmt "@[<2>(%a)@ %a@]"
      (Format.pp_print_list ~pp_sep typ) e  name f
  | T.Arrow (a,T.Un Global,b) ->
    Format.fprintf fmt "%a -> %a" typ_with_paren a  typ b
  | T.Arrow (a,k,b) -> Format.fprintf fmt "%a -{%a}> %a" typ_with_paren a kind k  typ b
  | T.Var { contents = x } -> tyvar fmt x
  | T.GenericVar n -> tyname fmt n

and typ_with_paren fmt x =
  let must_have_paren = match x with
    | T.Arrow _ -> true
    | _ -> false
  in
  Format.fprintf fmt
    (if must_have_paren then "@[(%a@])" else "%a") typ x

let constr fmt (k1, k2) =
  Format.fprintf fmt "(%a < %a)" kind k1 kind k2
let constrs fmt l =
  let pp_sep fmt () = Format.fprintf fmt " &@ " in
  Format.fprintf fmt "%a" Format.(pp_print_list ~pp_sep constr) l

let kscheme fmt {T. constr = c ; kvars ; args ; kind = k } =
  let pp_sep fmt () = Format.fprintf fmt "," in
  let pp_arrow fmt () = Format.fprintf fmt "@ ->@ " in
  Format.pp_open_box fmt 2 ;
  begin
    if kvars <> [] then
      Format.fprintf fmt "∀%a.@ "
        Format.(pp_print_list ~pp_sep name) kvars
  end;
  begin
    if c <> [] then
      Format.fprintf fmt "%a =>@ " constrs c
  end;
  Format.fprintf fmt "%a"
    Format.(pp_print_list ~pp_sep:pp_arrow kind) (args@[k]);
  Format.pp_close_box fmt ();
  ()

and scheme fmt {T. constr = c ; tyvars ; kvars ; ty } =
  let pp_sep fmt () = Format.fprintf fmt ",@ " in
  let binding fmt (ty,k) =
    Format.fprintf fmt "(%a:%a)" (tyname ~unbound:false) ty kind k
  in
  Format.pp_open_box fmt 0 ;
  begin
    let has_kinds = not @@ CCList.is_empty kvars in
    let has_types = not @@ CCList.is_empty tyvars in
    if has_kinds || has_types then begin
      Fmt.pf fmt "∀@[";
      Format.(pp_print_list ~pp_sep (kname ~unbound:false)) fmt kvars ;
      if has_kinds && has_types then pp_sep fmt () ;
      Format.(pp_print_list ~pp_sep binding) fmt tyvars;
      Fmt.pf fmt "@].@ ";
    end;
  end;
  begin
    if c <> [] then
      Format.fprintf fmt "@[%a@] =>@ " constrs c
  end;
  Fmt.box typ fmt ty;
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
    (print_env "Type Variables:" (tyname ~unbound:false) kscheme) env.Env.types
