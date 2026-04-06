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

(** Function registry for isla term evaluation.

    Defines the [fn_spec] type and lookup/evaluation helpers.
    Concrete function lists are provided by [Bv_fns] (and later
    [Pgtable_fns]); callers pass the assembled list via [~fns]. *)

type table_data = (int * Bytes.t) list

type fn_spec =
  { params : string list;
    eval : table_data -> Z.t list -> Z.t
  }

let arity_error name n =
  failwith (Printf.sprintf "function %s: expected %d args" name n)

let find fns name = List.assoc_opt name fns

let eval_fn ~fns ?(td = []) name args =
  match find fns name with
  | Some spec -> spec.eval td args
  | None ->
      failwith (Printf.sprintf "function: unknown %s/%d" name (List.length args))

let align_kwargs ~fns name kwargs =
  match find fns name with
  | Some spec ->
      List.map
        (fun param ->
           match List.assoc_opt param kwargs with
           | Some v -> v
           | None ->
               failwith
                 (Printf.sprintf "function %s: missing argument %s" name param)
         )
        spec.params
  | None -> failwith (Printf.sprintf "function: unknown keyword function %s" name)

let eval_kwfn ~fns ?(td = []) name kwargs =
  let args = align_kwargs ~fns name kwargs in
  eval_fn ~fns ~td name args
