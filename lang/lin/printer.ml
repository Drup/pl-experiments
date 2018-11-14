open Syntax
module T = Types

let bold fmt s = Format.fprintf fmt "@<0>%s%s@<0>%s" "\027[1m" s "\027[0m"

let constant fmt = function
  | Int i -> Format.pp_print_int fmt i
  | Plus -> bold fmt "+"
  | NewRef -> bold fmt "new"
  | Get -> bold fmt "!"
  | Set -> bold fmt ":="
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

let name fmt {Name. name ; id } =
  Format.fprintf fmt "%s%a" name  digits id

let tyname ?(unbound=false) fmt n =
  Format.fprintf fmt "'%s%a" (if unbound then "_" else "") name n
let kname ?(unbound=false) fmt n =
  Format.fprintf fmt "'%s%a" (if unbound then "_" else "") name n

let rec value
  = fun fmt -> function
    | Constant c -> constant fmt c
    | Constructor (c, None) -> name fmt c
    | Constructor (c, Some v) ->
      Format.fprintf fmt "@[<2>%a (%a)]" name c value v
    | Lambda (n,e) ->
      Format.fprintf fmt "@[<2>%a %a %a@ %a@]"
        bold "fun"
        name n
        bold "->"
        expr e
    | Ref { contents } -> Format.fprintf fmt "{%a}" value contents

and expr
  = fun fmt -> function
    | V v -> value fmt v
    | Var v -> name fmt v
    | App (f,e) ->
      Format.fprintf fmt "@[<2>@[%a@]@ %a@]"
        expr_with_paren f
        Format.(pp_print_list ~pp_sep:pp_print_space expr_with_paren) e
    | Let (n,e1,e2) ->
      Format.fprintf fmt "@[@[<2>%a %a %a@ %a@]@ %a@ %a@]"
        bold "let" name n
        bold "=" expr e1
        bold "in" expr e2
    | Match (constr,n,e1,e2) ->
      Format.fprintf fmt "@[@[<2>%a %a %a %a@ %a@]@ %a@ %a@]"
        bold "let" name constr name n
        bold "=" expr e1
        bold "in" expr e2

and expr_with_paren fmt x =
  let must_have_paren = match x with
    | App _ -> true
    | Let _ -> true
    | V (Lambda _) -> true
    | _ -> false
  in
  Format.fprintf fmt
    (if must_have_paren then "@[(%a@])" else "%a") expr x 

let rec typ_need_paren = function
  | T.Arrow _ -> true
  | T.Var { contents = Link t } -> typ_need_paren t
  | _ -> false

let rec kvar
  = fun fmt -> function
  | T.KUnbound (n,_) -> kname ~unbound:true fmt n
  | T.KLink t -> kind fmt t

and kind fmt = function
  | T.Un -> Format.fprintf fmt "un"
  | T.Lin -> Format.fprintf fmt "lin"
  | T.KVar { contents = x } -> kvar fmt x
  | T.KGenericVar n -> kname fmt n

let rec tyvar
  = fun fmt -> function
  | T.Unbound (n,_) -> tyname ~unbound:true fmt n
  | T.Link t -> typ_with_paren fmt t

and typ
  = fun fmt -> function
  | T.App (f,[]) ->
    name fmt f
  | T.App (f,e) ->
    let pp_sep fmt () = Format.fprintf fmt ",@ " in
    Format.fprintf fmt "@[<2>(%a)@ %a@]"
      (Format.pp_print_list ~pp_sep typ) e  name f
  | T.Arrow (a,Un,b) -> Format.fprintf fmt "%a -> %a" typ_with_paren a  typ b
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
      Format.fprintf fmt "∀%a. "
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
  let pp_sep fmt () = Format.fprintf fmt "," in
  let binding fmt (ty,k) =
    Format.fprintf fmt "(%a:%a)" (tyname ~unbound:false) ty kind k
  in
  Format.pp_open_box fmt 2 ;
  begin
    if kvars <> [] || tyvars <> [] then
      Format.fprintf fmt "∀%a%a. "
        Format.(pp_print_list ~pp_sep (kname ~unbound:false)) kvars
        Format.(pp_print_list ~pp_sep binding) tyvars
  end;
  begin
    if c <> [] then
      Format.fprintf fmt "%a =>@ " constrs c
  end;
  typ fmt ty;
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
