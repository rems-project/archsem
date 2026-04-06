(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
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
  open Pgtable_parser
}

let digit = ['0'-'9']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']
let alpha = ['a'-'z' 'A'-'Z' '_']
let alnum = alpha | digit

rule token = parse
  | [' ' '\t' '\r' '\n']+ { token lexbuf }
  | ';'        { SEMICOLON }
  | '='        { EQ }
  | '('        { LPAREN }
  | ')'        { RPAREN }
  | ','        { COMMA }
  | '['        { LBRACKET }
  | ']'        { RBRACKET }
  | '*'        { STAR }
  | "|->"      { MAPS_TO }
  | "physical"     { PHYSICAL }
  | "virtual"      { VIRTUAL }
  | "with"         { WITH }
  | "default"      { DEFAULT }
  | "code"         { CODE }
  | "and"          { AND }
  | '0' ['x' 'X'] hex+ as s { NUM (Z.of_string s) }
  | '0' ['b' 'B'] ['0' '1']+ as s { NUM (Z.of_string s) }
  | digit+ as s { NUM (Z.of_string s) }
  | alpha alnum* as s { IDENT s }
  | eof { EOF }
  | _ as c {
      failwith (Printf.sprintf
        "pgtable lexer: unexpected character '%c' at position %d"
        c (Lexing.lexeme_start lexbuf))
    }
