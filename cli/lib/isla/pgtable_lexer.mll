{
  open Pgtable_parser
}

let digit = ['0'-'9']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']
let alpha = ['a'-'z' 'A'-'Z' '_']
let alnum = alpha | digit

rule token = parse
  | [' ' '\t' '\n']+ { token lexbuf }
  | "|->"      { MAPS_TO }
  | "?->"      { OPT_MAPS_TO }
  | "=="       { EQEQ }
  | "!="       { BANGEQ }
  | ".."       { DOTDOT }
  | '('        { LPAREN }
  | ')'        { RPAREN }
  | '['        { LBRACKET }
  | ']'        { RBRACKET }
  | '{'        { LBRACE }
  | '}'        { RBRACE }
  | ','        { COMMA }
  | ';'        { SEMICOLON }
  | '='        { EQ }
  | '*'        { STAR }
  | "physical"     { PHYSICAL }
  | "virtual"      { VIRTUAL }
  | "intermediate" { INTERMEDIATE }
  | "aligned"      { ALIGNED }
  | "identity"     { IDENTITY }
  | "invalid"      { INVALID }
  | "with"         { WITH }
  | "at"           { AT }
  | "level"        { LEVEL }
  | "as"           { AS }
  | "default"      { DEFAULT }
  | "code"         { CODE }
  | "and"          { AND_KW }
  | "s1table"      { S1TABLE }
  | "s2table"      { S2TABLE }
  | "option"       { OPTION }
  | "true"         { TRUE }
  | "false"        { FALSE }
  | "assert"       { ASSERT }
  | '0' ['x' 'X'] hex+ as s { NUM (Z.of_string s) }
  | '0' ['b' 'B'] ['0' '1']+ as s { NUM (Z.of_string s) }
  | digit+ as s { NUM (Z.of_string s) }
  | alpha alnum* as s { IDENT s }
  | eof        { EOF }
  | _ as c {
      failwith (Printf.sprintf
        "pgt_lexer: unexpected character '%c' at position %d"
        c (Lexing.lexeme_start lexbuf))
    }
