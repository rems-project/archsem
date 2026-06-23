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
  open Litmus.Assertion
%}

%token <Z.t> NUM
%token <string> IDENT
%token LPAREN "("
%token RPAREN ")"
%token COMMA ","
%token AND "&"
%token OR "|"
%token NOT "~"
%token EQ "="
%token STAR "*"
%token COLON ":"
%token MINUS "-"
%token SEMICOLON ";"
%token LBRACKET "["
%token RBRACKET "]"
%token MAPS_TO "|->"
%token MAYBE_MAPS_TO "?->"
%token PHYSICAL
%token IDENTITY
%token WITH
%token DEFAULT
%token AND_KW
%token CODE
%token DATA
%token TRUE
%token FALSE EOF

%left OR
%left AND
%nonassoc NOT

%start <Term.t Litmus.Assertion.expr> assertion
%start <Term.t> binding
%start <Page_table_ast.stmt list> page_table_setup
%type <Page_table_ast.stmt> page_table_stmt page_table_stmt_inner
%type <Page_table_ast.attr> page_table_attr
%type <Page_table_ast.descriptor_field list> page_table_descriptor_attrs

%%

assertion:
  | e = prop; EOF { e }

binding:
  | v = term; EOF { v }

page_table_setup:
  | ss = nonempty_list(page_table_stmt); EOF { ss }

page_table_stmt:
  | s = page_table_stmt_inner; ";" { s }

page_table_stmt_inner:
  | PHYSICAL; names = nonempty_list(IDENT)
    { Page_table_ast.Physical names }
  | va_name = IDENT; "|->"; pa_name = IDENT;
    attrs = option(page_table_descriptor_attrs)
    { Page_table_ast.Mapping
        {va_name; pa_name; attrs = Option.value ~default:[] attrs}
    }
  | va_name = IDENT; "?->"; pa_name = IDENT;
    attrs = option(page_table_descriptor_attrs)
    { Page_table_ast.MaybeMapping
        {va_name; pa_name; attrs = Option.value ~default:[] attrs}
    }
  | "*"; pa_name = IDENT; "="; value = NUM
    { Page_table_ast.DataInit {pa_name; value} }
  | IDENTITY; addr = NUM; WITH; attr = page_table_attr
    { Page_table_ast.IdentityMapping {addr; attr} }

page_table_descriptor_attrs:
  | WITH; "[";
    attrs = separated_nonempty_list(",", page_table_descriptor_attr);
    "]"; AND_KW; DEFAULT
    { attrs }

%inline page_table_descriptor_attr:
  | name = IDENT; "="; value = NUM
    { Page_table_ast.{name; value} }

page_table_attr:
  | CODE { Page_table_ast.Code }
  | DATA { Page_table_ast.Data }

prop:
  | e1 = prop; "|"; e2 = prop { Or [e1; e2] }
  | e1 = prop; "&"; e2 = prop { And [e1; e2] }
  | "~"; e = prop { Not e }
  | "("; e = prop; ")" { e }
  | a = atom { Atom a }
  | TRUE { True }
  | FALSE { False }

atom:
  | lhs = loc; "="; rhs = term { CmpCst (lhs, rhs) }
  | lhs = loc; "="; rhs = loc { CmpLoc (lhs, rhs) }

loc:
  | tid = NUM; ":"; r = IDENT { Reg (Z.to_int tid, r) }
  | "*"; s = IDENT { Mem s }

term:
  | v = NUM { Term.Const v }
  | "-"; v = NUM { Term.Const (Z.neg v) }
  | f = IDENT; "("; args = separated_list(",", term); ")" { Term.Fn (f, args) }
  | f = IDENT; "("; kw = separated_nonempty_list(",", kw_arg); ")" { Term.KwFn (f, kw) }
  | s = IDENT { Term.Sym s }

kw_arg:
  | k = IDENT; "="; v = term { (k, v) }
