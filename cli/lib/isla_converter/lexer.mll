{
open Parser
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*
let hex = "0x" ['0'-'9' 'a'-'f' 'A'-'F']+
let bin = "0b" ['0' '1']+
let int = ['0'-'9']+

rule read = parse
  | white { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | ':' { read lexbuf } (* Ignore colons *)
  | '#' { read_comment lexbuf }
  | "physical" { KW_PHYSICAL }
  | "intermediate" { KW_INTERMEDIATE }
  | "virtual" { KW_VIRTUAL }
  | "aligned" { KW_ALIGNED }
  | "option" { KW_OPTION }
  | "s1table" { KW_S1TABLE }
  | "s2table" { KW_S2TABLE }
  | "table" { KW_TABLE }
  | "identity" { KW_IDENTITY }
  | "assert" { KW_ASSERT }
  | "with" { KW_WITH }
  | "code" { KW_CODE }
  | "default" { KW_DEFAULT }
  | "invalid" { KW_INVALID }
  | "raw" { KW_RAW }
  | "at" { KW_AT }
  | "level" { KW_LEVEL }
  | "as" { KW_AS }
  | "and" { KW_AND }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | ";" { SEMI }
  | "," { COMMA }
  | "==" { EQEQ }
  | "=" { EQ }
  | "!=" { NEQ }
  | "*" { STAR }
  | "|->" { ARROW }
  | "?->" { VAR_ARROW }
  | ".." { DOTDOT }
  | hex as s { HEX s }
  | bin as s { BIN s }
  | int as s { INT s }
  | id as s { ID s }
  | eof { EOF }
  | _ { failwith ("Unexpected char: " ^ Lexing.lexeme lexbuf) }

and read_comment = parse
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | eof { EOF }
  | _ { read_comment lexbuf }
