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

(** Raise a function-scoped evaluation error. *)
let error fmt = Litmus.Error.failwith ("function: " ^^ fmt)

(** Report a positional arity mismatch for [name]. *)
let arity_error name expected actual =
  error "%s: expected %d arguments, got %d" name expected actual

(** Convert a Zarith argument to an OCaml [int], preserving function context. *)
let int_arg name arg value =
  match Z.to_int value with
  | n -> n
  | exception Z.Overflow -> error "%s: argument %s is too large" name arg

(** Return arguments in parameter order, filling missing values from defaults. *)
let align name spec bindings =
  List.map
    (fun param ->
       match List.assoc_opt param bindings with
       | Some value -> value
       | None -> (
         match List.assoc_opt param spec.defaults with
         | Some value -> value
         | None -> error "%s: missing argument %s" name param
       )
     )
    spec.params

(** Pair positional arguments with their parameter names. *)
let bind_args name spec args =
  let rec bind params args =
    match (params, args) with
    | (_, []) -> []
    | (param :: params, arg :: args) -> (param, arg) :: bind params args
    | ([], _ :: _) ->
        let expected = List.length spec.params in
        let actual = List.length args in
        arity_error name expected actual
  in
  bind spec.params args

(** Evaluate a positional call, normalizing only functions with defaults. *)
let eval_fn ~fns name args =
  match List.assoc_opt name fns with
  | Some spec ->
      if spec.defaults = [] then spec.eval args
      else spec.eval (align name spec (bind_args name spec args))
  | None -> error "unknown %s" name

(** Validate keyword arguments and bind them by name before default filling. *)
let align_kwargs name spec kwargs =
  let bindings =
    List.fold_left
      (fun bindings (arg, value) ->
         if not (List.mem arg spec.params) then
           error "%s: unknown argument %s" name arg
         else if List.mem_assoc arg bindings then
           error "%s: duplicate argument %s" name arg
         else (arg, value) :: bindings
       )
      [] kwargs
  in
  align name spec bindings

(** Evaluate a keyword call after selecting a matching function spec. *)
let eval_kwfn ~fns name kwargs =
  let specs =
    List.filter_map
      (fun (fn_name, spec) -> if fn_name = name then Some spec else None)
      fns
  in
  match specs with
  | [] -> error "unknown %s" name
  | [spec] -> spec.eval (align_kwargs name spec kwargs)
  | specs -> (
      (* Filter among overloaded functions *)
      let accepts_kwargs spec =
        List.for_all (fun (arg, _) -> List.mem arg spec.params) kwargs
      in
      match List.find_opt accepts_kwargs specs with
      | Some spec -> spec.eval (align_kwargs name spec kwargs)
      | None -> error "no matching overload for %s" name
    )
