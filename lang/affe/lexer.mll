{
open Parser
}

rule token = parse
  | [' ' '\t']     { token lexbuf }     (* skip blanks *)
  | '\n' { Lexing.new_line lexbuf ; token lexbuf }
  | '-'?[ '0'-'9' ]+ as x	{INT (int_of_string x)}
  | "Y" { YTOK }
  | "let" { LET }
  | "+" { PLUS }
  | "in" { IN }
  | "=" { EQUAL }
  | "fun" { FUN }
  | "%" { PERCENT }
  | ">" { GREATER }
  | "." { DOT }
  | "->" { RIGHTARROW }
  | "<-" { LEFTARROW }
  | "-{" { DASHLACCO }
  | "<" { LESS }
  | "&!" { ANDBANG }
  | "&" { AND }
  | "}>" { RACCOGREATER }
  | '('	{ LPAREN }
  | ')'	{ RPAREN }
  | '{'	{ LACCO }
  | '}'	{ RACCO }
  | "[|"	{ LBRACKPIPE }
  | "|]"	{ PIPERBRACK }
  | "type" { TYPE }
  | "=>" { BIGRIGHTARROW }
  | "of" { OF }
  | ":" { DOUBLECOLON }
  | "," { COMMA }
  | "un" { UN }
  | "aff" { AFF }
  | ';' { SEMI }
  | ";;"	{ SEMISEMI }
  | eof	{ EOF }
  | "'" ([ 'A'-'Z' 'a'-'z' '0'-'9' '_' '\'' ]+ as s)  { TYIDENT s }
  | ([ 'a'-'z' ] [ 'A'-'Z' 'a'-'z' '0'-'9' '_' '\'' ]*) as s  { IDENT s }
  | ([ 'A'-'Z' ] [ 'A'-'Z' 'a'-'z' '0'-'9' '_' '\'' ]*) as s  { UIDENT s }
