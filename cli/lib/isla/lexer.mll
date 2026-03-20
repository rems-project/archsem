{
  open Parser
}

let digit = ['0'-'9']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']
let alpha = ['a'-'z' 'A'-'Z' '_']
let alnum = alpha | digit

rule token = parse
  | [' ' '\t' '\n']+ { token lexbuf }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '&' { AND }
  | '|' { OR }
  | '~' { NOT }
  | '=' { EQ }
  | '*' { STAR }
  | ':' { COLON }
  | "true" { TRUE }
  | "false" { FALSE }
  | '0' ['x' 'X'] hex+ as s { NUM (Z.of_string s) }
  | '0' ['b' 'B'] ['0' '1']+ as s { NUM (Z.of_string s) }
  | digit+ as s { NUM (Z.of_string s) }
  | alpha alnum* as s { IDENT s }
  | eof { EOF }
  | _ as c {
      Litmus.Error.raise_error Parser
        "assertion lexer: unexpected character '%c' at position %d"
        c (Lexing.lexeme_start lexbuf)
    }
