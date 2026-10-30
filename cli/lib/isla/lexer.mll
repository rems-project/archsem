(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

{
  open Parser

  exception Error of string

  let keywords =
    Hashtbl.of_seq
      (List.to_seq
         [ ("aligned", ALIGNED);
           ("option", OPTION);
           ("virtual", VIRTUAL);
           ("physical", PHYSICAL);
           ("identity", IDENTITY);
           ("assert", ASSERT);
           ("with", WITH);
           ("and", AND_KW);
           ("default", DEFAULT);
           ("code", CODE);
           ("invalid", INVALID);
           ("s1table", S1TABLE);
           ("s2table", S2TABLE);
           ("at", AT);
           ("level", LEVEL);
           ("true", TRUE);
           ("false", FALSE) ])
}

let digit = ['0'-'9']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']
let ident_start = ['a'-'z' 'A'-'Z' '_']
let ident_char = ident_start | digit
let ident = ident_start ident_char*

rule token = parse
  | [' ' '\t']+ { token lexbuf }
  | "\r\n" { Lexing.new_line lexbuf; token lexbuf }
  | ['\n' '\r'] { Lexing.new_line lexbuf; token lexbuf }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '&' { AND }
  | "|->" { MAPS_TO }
  | "?->" { MAYBE_MAPS_TO }
  | '|' { OR }
  | "==" { EQEQ }
  | "!=" { NEQ }
  | '~' { NOT }
  | '=' { EQ }
  | '*' { STAR }
  | ':' { COLON }
  | ';' { SEMICOLON }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | ".." { DOTDOT }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | ',' { COMMA }
  | '-' { MINUS }
  | '+' { PLUS }
  | '0' ['x' 'X'] hex+ as s { NUM (Z.of_string s) }
  | '0' ['b' 'B'] ['0' '1']+ as s { NUM (Z.of_string s) }
  | digit+ as s { NUM (Z.of_string s) }
  | ident as s
      { match Hashtbl.find_opt keywords s with Some kw -> kw | None -> IDENT s }
  | eof { EOF }
  | _ as c {
      raise (Error (Printf.sprintf
        "assertion lexer: unexpected character '%c' at position %d"
        c (Lexing.lexeme_start lexbuf)))
    }

and ident_only = parse
  | (ident as s) eof { not (Hashtbl.mem keywords s) }
  | _ { false }
  | eof { false }

{
  (** [is_ident s] holds iff [s] lexes as a single [IDENT] token: it starts
      with a letter or '_', contains only letters, digits and '_', and is not
      a keyword. *)
  let is_ident s = ident_only (Lexing.from_string s)
}
