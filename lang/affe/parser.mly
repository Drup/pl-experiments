%{
open Syntax

let mk_lambda l body = List.fold_right (fun n e -> Lambda (n, e)) l body
let mk_let name args e1 e2 =
  let e1 = match args with [] -> e1 | l -> mk_lambda l e1 in
  Let (PVar name, e1, e2)
let mk_decl name args e =
  let expr = match args with [] -> e | l -> mk_lambda l e in
  ValueDecl {name; expr}

let mk_binop op a b = App (op, [a;b])

let mk_var s = Var (Name.dummy s)
let mk_get a i = App (mk_var "array_get", [Tuple [a;i]])
let mk_set a i x = App (mk_var "array_set", [Tuple [a;i;x]])
%}

%token EOF SEMISEMI
%token YTOK
%token <string> IDENT
%token <string> TYIDENT
%token <string> UIDENT
%token <int> INT
%token UN AFF LIN
%token UNDERSCORE
%token DOT
%token STAR
%token EQUAL PLUS MINUS
%token LPAREN RPAREN
%token LACCO RACCO
%token LBRACKPIPE PIPERBRACK
%token LET IN
%token SEMI
%token TYPE VAL CONSTRAINTS
%token RIGHTARROW LEFTARROW FUN BIGRIGHTARROW
%token COMMA DOUBLECOLON OF
%token LESS GREATER
%token DASHLACCO RACCOGREATER
%token AND
%token PERCENT
%token ANDBANG


%nonassoc IN
%nonassoc LEFTARROW
%right RIGHTARROW DASHLACCO RACCOGREATER
%nonassoc FUN
/* %left FUNAPP */
%left PLUS MINUS
%right STAR
/* %nonassoc below_DOT */
/* %nonassoc DOT */
%nonassoc
  /* AND ANDBANG INT */ IDENT /* UIDENT LPAREN LACCO LBRACKPIPE YTOK ALLOC */

%start file
%type <Syntax.command list> file

%start toplevel
%type <Syntax.command> toplevel

%%
file: list(command) EOF { $1 }
toplevel: command SEMISEMI { $1 }

command:
  | LET name=name args=list(name) EQUAL expr=expr
    { mk_decl name args expr }
  | VAL name=name DOUBLECOLON typ=type_scheme
    { ValueDef { name ; typ } }
  | typdecl=type_decl { typdecl }


expr:
  | e=simple_expr /* %prec below_DOT */
    { e }
  | f=simple_expr l=list_expr /* %prec FUNAPP */
     { App (f,List.rev l) }
  | e1=expr op=binop e2=expr
    { mk_binop op e1 e2 }
  | LET name=name args=nonempty_list(name) EQUAL e1=expr IN e2=expr
    { mk_let name args e1 e2 }
  | LET p=pattern EQUAL e1=expr IN e2=expr
    { Let (p, e1, e2) }
  | FUN l=list(name) RIGHTARROW body=expr
    { mk_lambda l body }
  | s=simple_expr DOT LPAREN i=expr RPAREN LEFTARROW e=expr
    { mk_set s i e }

simple_expr:
  | c=constant { Constant c }
  | name=uname { Constructor (name) }
  | name=name { Var name }
  | LPAREN RPAREN { Builtin.unit }
  | LPAREN l=separated_nonempty_list(COMMA,expr) RPAREN
    { match l with
      | [e] -> e
      | l -> Tuple l
    }
  | LACCO e=expr RACCO { Region e }
  | LBRACKPIPE l=separated_list(SEMI, expr) PIPERBRACK { Array l }
  | b=borrow name=name { Borrow (b, name) }
  | s=simple_expr DOT LPAREN i=expr RPAREN { mk_get s i }

%inline binop:
  | PLUS {Constant (Primitive "plus")}
  | MINUS {Constant (Primitive "minus")}
  | STAR {Constant (Primitive "mult")}

pattern:
  | v=name { PVar v }
  | constr=uname p=pattern { PConstr (constr, p) }
  | LPAREN l=separated_nontrivial_llist(COMMA,pattern) RPAREN { PTuple l }

%inline borrow:
  | AND { Read }
  | ANDBANG { Write}

list_expr:
  | simple_expr  { [$1] }
  | list_expr simple_expr { $2 :: $1 }

constant:
  | i=INT { Int i }
  | PERCENT s=IDENT { Primitive s }
  | YTOK { Y }

name:
  | name=IDENT { Name.dummy name }
uname:
  | name=UIDENT { Name.dummy name }
type_var:
  | name=TYIDENT { Name.dummy name }
kind_var:
  | name=TYIDENT { Name.dummy name }

type_decl:
  | TYPE
     params=type_var_bindings name=name kind=kind_annot
     constructor=maybe_constructor constraints=maybe_constraints
    { TypeDecl {name; params; constructor ; constraints ; kind} }

maybe_constructor:
  | { None }
  | EQUAL name=uname OF e=type_expr_with_constraint
    { let constraints, typ = e in
      Some {Ty. name; constraints; typ}
    }

maybe_constraints:
  | { [] }
  | CONSTRAINTS c=constraints { c }

type_scheme:
  | kparams=list(kind_var) params=list(type_quantifier) DOT
    e=type_expr_with_constraint
    { let constraints, typ = e in
      {Ty. kparams; params; constraints; typ}
    }

type_expr_with_constraint:
  | t=type_expr { ([], t) }
  | c=constraints BIGRIGHTARROW t=type_expr { (c, t) }

type_expr:
  | t=simple_type_expr { t }
  | l=separated_nontrivial_llist(STAR, simple_type_expr) { Ty.Tuple l }
  | t1=type_expr k=arrow t2=type_expr { Ty.Arrow (t1, k, t2) }
simple_type_expr:
  | t=simple_type_expr_no_paren { t }
  | LPAREN e=type_expr RPAREN %prec FUN
    { e }
simple_type_expr_no_paren:
  | n=type_var { Ty.Var n }
  | n=name { Ty.App (n, []) }
  | t=simple_type_expr n=name { Ty.App (n, [t]) }
  | b=borrow LPAREN k=kind_expr COMMA t=type_expr RPAREN
    { Ty.Borrow (b,k,t) }
  | LPAREN p=type_list RPAREN n=name
    { Ty.App (n, p) }

%inline type_list:
  tys = inline_reversed_separated_nonempty_llist(COMMA, type_expr) { List.rev tys }
  
%inline arrow:
  | RIGHTARROW { Kind.Un }
  | DASHLACCO k=kind_expr RACCOGREATER { k }

kind_annot:
  | { Kind.Unknown }
  | DOUBLECOLON k=kind_expr { k }

kind_expr:
  | n=kind_var { Kind.KVar n }
  | UN { Kind.Un }
  | AFF { Kind.Aff }
  | LIN { Kind.Lin }
  | UNDERSCORE { Kind.Unknown }

constraints: l=separated_nonempty_list (COMMA, constr) { l }
constr:
  | k1=kind_expr LESS k2=kind_expr { (k1, k2) }
  | k1=kind_expr GREATER k2=kind_expr { (k2, k1) }

type_quantifier:
  | LPAREN t=type_var_binding RPAREN {t}

type_var_bindings:
  | { [] }
  | LPAREN
    l=inline_reversed_separated_nonempty_llist(COMMA,type_var_binding)
    RPAREN
      { List.rev l }
type_var_binding:
  | ty=type_var DOUBLECOLON k=kind_expr { (ty, k) }


(* Generic parsing rules *)

reversed_separated_nonempty_llist(separator, X):
  xs = inline_reversed_separated_nonempty_llist(separator, X) { xs }

%inline inline_reversed_separated_nonempty_llist(separator, X):
  x = X
    { [ x ] }
| xs = reversed_separated_nonempty_llist(separator, X)
  separator
  x = X
    { x :: xs }

reversed_separated_nontrivial_llist(separator, X):
  xs = reversed_separated_nontrivial_llist(separator, X)
  separator
  x = X
    { x :: xs }
| x1 = X
  separator
  x2 = X
    { [ x2; x1 ] }

%inline separated_nontrivial_llist(separator, X):
  xs = rev(reversed_separated_nontrivial_llist(separator, X))
    { xs }
