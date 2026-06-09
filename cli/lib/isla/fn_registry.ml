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

(** Registry for evaluating named functions in Isla terms.
    Defines the [fn_spec] type and lookup/evaluation helpers.

    Any error during evaluation should be reported with [Failure] which will be
    converted into a [eval_error] in [Term.eval] *)

type fn_spec =
  { params : string list;
    defaults : (string * Z.t) list;
    eval : Z.t list -> Z.t
  }

let arity_error name expected actual =
  Litmus.Error.failwith "function: %s: expected %d arguments, got %d" name
    expected actual

let eval_fn ~fns name args =
  match List.assoc_opt name fns with
  | Some spec -> spec.eval args
  | None -> Litmus.Error.failwith "function: unknown %s/%d" name (List.length args)

let align_kwargs name spec kwargs =
  let bindings =
    List.fold_left
      (fun bindings (arg, value) ->
         if not (List.mem arg spec.params) then
           Litmus.Error.failwith "function: %s: unknown argument %s" name arg
         else if List.mem_assoc arg bindings then
           Litmus.Error.failwith "function: %s: duplicate argument %s" name arg
         else (arg, value) :: bindings
       )
      [] kwargs
  in
  List.map
    (fun param ->
       match List.assoc_opt param bindings with
       | Some value -> value
       | None -> (
         match List.assoc_opt param spec.defaults with
         | Some default -> default
         | None ->
             Litmus.Error.failwith "function: %s: missing argument %s" name param
       )
     )
    spec.params

let eval_kwfn ~fns name kwargs =
  match List.assoc_opt name fns with
  | Some spec -> spec.eval (align_kwargs name spec kwargs)
  | None ->
      Litmus.Error.failwith "function: unknown %s/%d" name (List.length kwargs)
