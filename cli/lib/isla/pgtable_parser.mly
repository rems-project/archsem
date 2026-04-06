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

%{
  open Pgtable
%}

%token <Z.t> NUM
%token <string> IDENT
%token SEMICOLON ";"
%token EQ "="
%token LPAREN "("
%token RPAREN ")"
%token COMMA ","
%token LBRACKET "["
%token RBRACKET "]"
%token STAR "*"
%token MAPS_TO "|->"
%token PHYSICAL VIRTUAL
%token WITH DEFAULT CODE AND
%token EOF

%start <Pgtable.stmt list> program

%%

program:
  | ss = list(stmt) EOF { ss }

stmt:
  | s = stmt_inner ";" { s }

stmt_inner:
  | PHYSICAL; names = separated_nonempty_list(COMMA, IDENT)
    { AddrDecl { kind = Physical; names } }
  | VIRTUAL; names = separated_nonempty_list(COMMA, IDENT)
    { AddrDecl { kind = Virtual; names } }
  | va = IDENT; "|->"; pa = IDENT; ws = opt_with_spec
    { Mapping { va; pa; with_spec = ws } }
  | "*"; addr = IDENT; "="; v = value_expr
    { MemInit { addr; value = v } }

opt_with_spec:
  | (* empty *) { [WsDefault] }
  | WITH; ws = with_spec { ws }

with_spec:
  | DEFAULT { [WsDefault] }
  | CODE { [WsCode] }
  | "["; attrs = separated_nonempty_list(COMMA, attr); "]"
    { [WsAttrs attrs] }
  | "["; attrs = separated_nonempty_list(COMMA, attr); "]"; AND; rest = with_spec
    { WsAttrs attrs :: rest }
  | DEFAULT; AND; rest = with_spec { WsDefault :: rest }
  | CODE; AND; rest = with_spec { WsCode :: rest }

attr:
  | k = IDENT; "="; v = value_expr { (k, v) }

value_expr:
  | v = NUM { Term.Const v }
  | f = IDENT; "("; args = separated_list(",", value_expr); ")" { Term.Fn (f, args) }
  | f = IDENT; "("; kw = separated_nonempty_list(",", kw_arg); ")" { Term.KwFn (f, kw) }
  | s = IDENT { Term.LocVal (Mem s) }

kw_arg:
  | k = IDENT; "="; v = value_expr { (k, v) }
