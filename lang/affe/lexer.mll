{
open Parser
}

rule token = parse
  | [' ' '\t']     { token lexbuf }     (* skip blanks *)
  | '#' [^ '\n']* '\n' 
  | '\n' { Lexing.new_line lexbuf ; token lexbuf } 
  | '-'?[ '0'-'9' ]+ as x	{INT (int_of_string x)}
  | "Y" { YTOK }
  | "let" { LET }
  | "+" { PLUS }
  | "-" { PLUS }
  | "*" { STAR }
  | "|" { BAR }
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
  | "_" { UNDERSCORE }
  | "}>" { RACCOGREATER }
  | '('	{ LPAREN }
  | ')'	{ RPAREN }
  | '{'	{ LACCO }
  | '}'	{ RACCO }
  | "[|"	{ LBRACKPIPE }
  | "|]"	{ PIPERBRACK }
  | "type" { TYPE }
  | "val" { VAL }
  | "constraints" { CONSTRAINTS }
  | "=>" { BIGRIGHTARROW }
  | "of" { OF }
  | ":" { DOUBLECOLON }
  | "," { COMMA }
  | "un" { UN }
  | "aff" { AFF }
  | "lin" { LIN }
  | ';' { SEMI }
  | ";;"	{ SEMISEMI }
  | eof	{ EOF }
  | "'" ( '_'? [ 'A'-'Z' 'a'-'z' '0'-'9' '_' '\'' ]+ as s)  { TYIDENT s }
  | ( '_'? [ 'a'-'z' ] [ 'A'-'Z' 'a'-'z' '0'-'9' '_' '\'' ]*) as s  { IDENT s }
  | ( '_'? [ 'A'-'Z' ] [ 'A'-'Z' 'a'-'z' '0'-'9' '_' '\'' ]*) as s  { UIDENT s }
