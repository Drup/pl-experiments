%{
open Syntax

let mk_lambda l body = List.fold_right (fun n e -> Lambda (n, e)) l body
let mk_let name args e1 e2 =
  let e1 = match args with [] -> e1 | l -> mk_lambda l e1 in
  Let (name, e1, e2)
let mk_def name args e =
  let expr = match args with [] -> e | l -> mk_lambda l e in
  Def {name; expr}
%}

%token EOF SEMISEMI
%token YTOK
%token <string> IDENT
%token <string> TYIDENT
%token <string> UIDENT
%token <int> INT
%token UN AFF
%token DOT
%token EQUAL PLUS
%token LPAREN RPAREN
%token LACCO RACCO
%token LBRACK RBRACK
%token LBRACKPIPE PIPERBRACK
%token LET IN
%token SEMI
%token TYPE
%token ALLOC FREE
%token RIGHTARROW LEFTARROW FUN BIGRIGHTARROW
%token COMMA DOUBLECOLON OF
%token LESS GREATER
%token DASHLACCO RACCOGREATER
%token AND
%token ANDBANG


%nonassoc IN
%nonassoc LEFTARROW
%right RIGHTARROW DASHLACCO RACCOGREATER
%nonassoc FUN
/* %left FUNAPP */
%left PLUS
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
    { mk_def name args expr }
  | TYPE params=type_var_bindings name=name EQUAL constructor=uname OF e=type_expr_with_constraint
    { Type {name; params; constructor ; constraints = fst e ; typ = snd e} }

expr:
  | e=simple_expr /* %prec below_DOT */
    { e }
  | f=simple_expr l=list_expr /* %prec FUNAPP */
     { App (f,List.rev l) }
  | e1=expr PLUS e2=expr
    { App (Constant Plus, [e1;e2]) }
  | LET name=name args=list(name) EQUAL e1=expr IN e2=expr
    { mk_let name args e1 e2 }
  | LET constr=uname p=name EQUAL e1=expr IN e2=expr { Match (constr, p, e1, e2) }
  | FUN l=list(name) RIGHTARROW body=expr
    { mk_lambda l body }
  | s=simple_expr DOT LBRACK i=expr RBRACK LEFTARROW e=expr
    { App (Constant Set, [s; i; e]) }

simple_expr:
  | c=constant { Constant c }
  | name=uname { Constructor (name) }
  | name=name { Var name }
  | LPAREN RPAREN { Builtin.unit }
  | LPAREN e=expr RPAREN { e }
  | LACCO e=expr RACCO { Region e }
  | LBRACKPIPE l=separated_list(SEMI, expr) PIPERBRACK { Array l }
  | AND name=name { Borrow (Read, name) }
  | ANDBANG name=name { Borrow (Write, name) }
  | s=simple_expr DOT LBRACK i=expr RBRACK { App (Constant Get, [s; i]) }


list_expr:
  | simple_expr  { [$1] }
  | list_expr simple_expr { $2 :: $1 }

constant:
  | i=INT { Int i }
  | ALLOC { Alloc }
  | FREE { Free }
  | YTOK { Y }

name:
  | name=IDENT { Name.dummy name }
uname:
  | name=UIDENT { Name.dummy name }
type_var:
  | name=TYIDENT { Name.dummy name }
kind_var:
  | name=TYIDENT { Name.dummy name }

type_expr_with_constraint:
  | t=type_expr { ([], t) }
  | c=constraints BIGRIGHTARROW t=type_expr { (c, t) }

type_expr:
  | t=simple_type_expr { t }
  | t1=type_expr k=arrow t2=type_expr { Ty.Arrow (t1, k, t2) }
simple_type_expr:
  | t=simple_type_expr_no_paren { t }
  | LPAREN t=type_expr RPAREN %prec FUN { t }
simple_type_expr_no_paren:
  | n=type_var { Ty.Var n }
  | n=name { Ty.App (n, []) }
  | t=simple_type_expr n=name { Ty.App (n, [t]) }
  | LPAREN p=simple_type_list RPAREN n=name
    { Ty.App (n, p) }

%inline simple_type_list:
  tys = inline_reversed_separated_nonempty_llist(COMMA, type_expr) { List.rev tys }
  

%inline arrow:
  | RIGHTARROW { Ty.Un }
  | DASHLACCO k=kind_expr RACCOGREATER { k }

kind_expr:
  | n=kind_var { Ty.KVar n }
  | UN { Ty.Un }
  | AFF { Ty.Aff }

constraints: l=separated_nonempty_list (COMMA, constr) { l }
constr:
  | k1=kind_expr LESS k2=kind_expr { (k1, k2) }
  | k1=kind_expr GREATER k2=kind_expr { (k2, k1) }

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
