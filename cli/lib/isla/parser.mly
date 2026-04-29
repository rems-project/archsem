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

%{
  open Assertion
%}

%token <Z.t> NUM
%token <string> IDENT
%token LPAREN "("
%token RPAREN ")"
%token AND "&"
%token OR "|"
%token NOT "~"
%token EQ "="
%token STAR "*"
%token COLON ":"
%token TRUE
%token FALSE EOF

%left OR
%left AND
%nonassoc NOT

%start <Assertion.expr> assertion

%%

assertion:
  | e = prop; EOF { e }

prop:
  | e1 = prop; "|"; e2 = prop { Or (e1, e2) }
  | e1 = prop; "&"; e2 = prop { And (e1, e2) }
  | "~"; e = prop { Not e }
  | "("; e = prop; ")" { e }
  | a = atom { Atom a }
  | TRUE { True }
  | FALSE { False }

atom:
  | l = loc; "="; v = NUM {
      match l with
      | Reg _ -> CmpCst (l, Eq, v)
      | Mem _ -> failwith "assertion: use *sym = value for memory comparisons"
    }
  | l1 = loc; "="; l2 = loc { CmpLoc (l1, Eq, l2) }
  | "*"; s = IDENT; "="; v = NUM { CmpCst (Mem s, Eq, v) }

loc:
  | tid = NUM; ":"; r = IDENT { Reg (Z.to_int tid, r) }
  | s = IDENT { Mem s }
