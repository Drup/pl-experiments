%{
open Syntax
%}

%token EOF SEMISEMI
%token YTOK
%token <string> IDENT
%token <string> TYIDENT
%token <string> UIDENT
%token <int> INT
%token UN LIN
%token EQUAL PLUS
%token LPAREN RPAREN
%token LET IN
%token TYPE
%token RIGHTARROW FUN BIGRIGHTARROW
%token COMMA DOUBLECOLON OF
%token REF BANG COLONEQUAL
%token LESS GREATER
%token DASHLACCO RACCOGREATER

%right RIGHTARROW DASHLACCO RACCOGREATER
%nonassoc FUN
%left FUNAPP
%nonassoc INT IDENT UIDENT LPAREN YTOK PLUS REF BANG COLONEQUAL

%start file
%type <Syntax.command list> file

%start toplevel
%type <Syntax.command> toplevel

%%
file: list(command) EOF { $1 }
toplevel: command SEMISEMI { $1 }

command:
  | LET name=name EQUAL expr=expr { Def {name; expr} }
  | TYPE params=type_var_bindings name=name EQUAL constructor=uname OF e=type_expr_with_constraint
    { Type {name; params; constructor ; constraints = fst e ; typ = snd e} }

expr:
  | e=simple_expr %prec FUN { e }
  | f=simple_expr l=list_expr %prec FUNAPP
     { App (f,List.rev l) }
  | LET name=name EQUAL e1=expr IN e2=expr { Let (name, e1, e2) }
  | LET constr=uname p=name EQUAL e1=expr IN e2=expr { Match (constr, p, e1, e2) }

simple_expr:
  | v=value { V v }
  | name=name { Var name }
  | LPAREN e=expr RPAREN { e }

list_expr:
  | simple_expr  { [$1] }
  | list_expr simple_expr { $2 :: $1 }

%inline value:
  | FUN name=name RIGHTARROW e=expr { Lambda (name, e) }
  | c=constant { Constant c }
  | name=uname { Constructor (name, None) }

constant:
  | i=INT { Int i }
  | PLUS { Plus }
  | REF { NewRef }
  | BANG { Get }
  | COLONEQUAL { Set }
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
  | LIN { Ty.Lin }

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
