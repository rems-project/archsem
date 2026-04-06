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

(** Bitvector terms: AST and evaluator. *)

type loc =
  | Reg of int * string
  | Mem of string

type t =
  | Const of Z.t
  | LocVal of loc
  | Deref of loc
  | Fn of string * t list
  | KwFn of string * (string * t) list

let functions = Bv_fns.functions @ Pgtable_fns.functions

let eval_fn ?(td = []) name args =
  Fn_registry.eval_fn ~fns:functions ~td name args

let string_of_loc = function
  | Reg (tid, reg) -> Printf.sprintf "%d:%s" tid reg
  | Mem sym -> sym

let rec eval ?(td = []) ~env = function
  | Const z -> z
  | LocVal loc -> (
    match env loc with
    | Some z -> z
    | None -> failwith (Printf.sprintf "term: unbound %s" (string_of_loc loc))
  )
  | Deref loc ->
      failwith
        (Printf.sprintf "term: cannot evaluate deref *%s statically"
           (string_of_loc loc)
        )
  | Fn (name, args) ->
      let evaluated = List.map (eval ~td ~env) args in
      Fn_registry.eval_fn ~fns:functions ~td name evaluated
  | KwFn (name, kwargs) ->
      let evaluated = List.map (fun (k, v) -> (k, eval ~td ~env v)) kwargs in
      Fn_registry.eval_kwfn ~fns:functions ~td name evaluated
