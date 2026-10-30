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

(** Evaluate Isla expressions against the current test state, and print them. *)

include Term_ast

(** {1 Evaluation} *)

let eval ~state term =
  let positional_functions =
    Bv_fns.functions @ Page_table_fns.positional_functions ~state
  in
  let keyword_functions = Page_table_fns.keyword_functions in
  let rec eval_term = function
    | Const z -> z
    | Sym sym -> Z.of_int (Eval_state.lookup_addr state sym)
    | Binary (lhs, op, rhs) ->
        let lhs = eval_term lhs in
        let rhs = eval_term rhs in
        ( match op with
        | Add -> Z.add
        | Sub -> Z.sub
        | Bit_and -> Z.logand
        | Bit_or -> Z.logor
        )
          lhs rhs
    | Negate value -> Z.neg (eval_term value)
    | Extract (value, hi, lo) ->
        Litmus.Assertion.extract_bits ~hi ~lo (eval_term value)
    | Fn (name, args) ->
        let evaluated = List.map eval_term args in
        Fn_registry.eval ~fns:positional_functions name evaluated
    | KwFn (name, kwargs) ->
        let evaluated = List.map (fun (k, v) -> (k, eval_term v)) kwargs in
        Fn_registry.eval ~fns:keyword_functions name evaluated
  in
  eval_term term

(** {1 Printing} *)

let binary_op_to_string = function
  | Add -> "+"
  | Sub -> "-"
  | Bit_and -> "&"
  | Bit_or -> "|"

(** Precedence levels, from the loosest to the tightest binding. The binary
    operators follow the precedence declarations of [parser.mly] *)
let binary_op_prec = function Bit_or -> 0 | Bit_and -> 1 | Add | Sub -> 2

(** Negations, negative constants and bit slices, whose operand must be closed *)
let unary_prec = 3

(** Terms that never need parentheses *)
let closed_prec = 4

let int_to_string = Litmus.Toml.Numbers.int_to_string

(** Print [term] in parenthesis if its precedence is lower than [prec] *)
let rec to_string_prec prec term =
  let (str, term_prec) =
    match term with
    | Const z when Z.sign z < 0 -> ("-" ^ int_to_string (Z.neg z), unary_prec)
    | Const z -> (int_to_string z, closed_prec)
    | Sym sym -> (sym, closed_prec)
    | Fn (name, args) ->
        let args = List.map to_string args in
        (Printf.sprintf "%s(%s)" name (String.concat ", " args), closed_prec)
    | KwFn (name, kwargs) ->
        let kwargs = List.map (fun (k, v) -> k ^ " = " ^ to_string v) kwargs in
        (Printf.sprintf "%s(%s)" name (String.concat ", " kwargs), closed_prec)
    | Binary (lhs, op, rhs) ->
        let prec = binary_op_prec op in
        ( Printf.sprintf "%s %s %s" (to_string_prec prec lhs)
            (binary_op_to_string op)
            (to_string_prec (prec + 1) rhs),
          prec
        )
    | Negate value -> ("-" ^ to_string_prec closed_prec value, unary_prec)
    | Extract (value, hi, lo) ->
        let slice =
          if Z.equal hi lo then Printf.sprintf "[%s]" (Z.to_string hi)
          else Printf.sprintf "[%s..%s]" (Z.to_string hi) (Z.to_string lo)
        in
        (to_string_prec closed_prec value ^ slice, unary_prec)
  in
  if term_prec < prec then "(" ^ str ^ ")" else str

(** Print a term in the Isla term syntax, with the minimal parentheses.
    Parsing the result gives back [term] for any term produced by the parser.
    Top-level [&] and [|] still need parentheses in assertions. *)
and to_string term = to_string_prec 0 term
