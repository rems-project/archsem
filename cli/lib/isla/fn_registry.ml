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
    Positional and keyword calls are kept as separate databases.

    Any error during evaluation should be reported with [Failure] which will be
    converted into a [eval_error] in [Term.eval] *)

type positional_fn = string * (Z.t list -> Z.t)

type keyword_fn = string * ((string * Z.t) list -> Z.t)

(** Raise a function-scoped evaluation error. *)
let error fmt = Litmus.Error.failwith ("function: " ^^ fmt)

(** Convert a Zarith argument to an OCaml [int], preserving function context. *)
let int_arg name arg value =
  match Z.to_int value with
  | n -> n
  | exception Z.Overflow -> error "%s: argument %s is too large" name arg

(** Report a positional arity mismatch for [name]. *)
let arity_error name expected actual =
  error "%s: expected %d arguments, got %d" name expected actual

(** Check that only allowed kwarg are present, and not duplicated. *)
let check_kwargs name allowed_args kwargs =
  List.fold_left
    (fun seen (arg, _) ->
       if not (List.mem arg allowed_args) then
         error "%s: unknown argument %s" name arg
       else if List.mem arg seen then error "%s: duplicate argument %s" name arg
       else arg :: seen
     )
    [] kwargs
  |> ignore

(** Extract a required argument from an argument list *)
let required_kwarg name arg kwargs =
  match List.assoc_opt arg kwargs with
  | Some value -> value
  | None -> error "%s: missing argument %s" name arg

(** Extract an optional named argumen from a list, otherwise gives a default
    value *)
let optional_kwarg arg default kwargs =
  match List.assoc_opt arg kwargs with Some value -> value | None -> default

(** Evaluates a named isla function given a registry and arguments *)
let eval ~fns name args =
  match List.assoc_opt name fns with
  | Some eval -> eval args
  | None -> error "unknown function %s" name
