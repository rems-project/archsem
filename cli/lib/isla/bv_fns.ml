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

(** Bitvector functions: bvand, bvor, bvxor, bvshl, bvlshr, extz, exts. *)

let check_non_negative_arg name arg value =
  if Z.sign value < 0 then
    Litmus.Error.failwith "function: %s: argument %s must be non-negative" name
      arg

let int_of_bit_arg name arg value =
  check_non_negative_arg name arg value;
  match Z.to_int value with
  | n -> n
  | exception Z.Overflow ->
      Litmus.Error.failwith "function: %s: argument %s is too large" name arg

(** List of bitvector primitive functions

    Any error during evaluation should be reported with [Failure] which will be
    converted into a [eval_error] in [Term.eval] *)
let functions : (string * Fn_registry.fn_spec) list =
  [ ( "bvand",
      { params = ["a"; "b"];
        defaults = [];
        eval =
          (fun args ->
            match args with
            | [a; b] -> Z.logand a b
            | _ -> Fn_registry.arity_error "bvand" 2 (List.length args)
          )
      }
    );
    ( "bvor",
      { params = ["a"; "b"];
        defaults = [];
        eval =
          (fun args ->
            match args with
            | [a; b] -> Z.logor a b
            | _ -> Fn_registry.arity_error "bvor" 2 (List.length args)
          )
      }
    );
    ( "bvxor",
      { params = ["a"; "b"];
        defaults = [];
        eval =
          (fun args ->
            match args with
            | [a; b] -> Z.logxor a b
            | _ -> Fn_registry.arity_error "bvxor" 2 (List.length args)
          )
      }
    );
    ( "bvshl",
      { params = ["a"; "b"];
        defaults = [];
        eval =
          (fun args ->
            match args with
            | [a; b] -> Z.shift_left a (int_of_bit_arg "bvshl" "b" b)
            | _ -> Fn_registry.arity_error "bvshl" 2 (List.length args)
          )
      }
    );
    ( "bvlshr",
      { params = ["a"; "b"];
        defaults = [];
        eval =
          (fun args ->
            match args with
            | [a; b] ->
                check_non_negative_arg "bvlshr" "a" a;
                Z.shift_right a (int_of_bit_arg "bvlshr" "b" b)
            | _ -> Fn_registry.arity_error "bvlshr" 2 (List.length args)
          )
      }
    );
    ( "extz",
      { params = ["bits"; "len"];
        defaults = [];
        eval =
          (fun args ->
            match args with
            | [bits; len] ->
                check_non_negative_arg "extz" "bits" bits;
                ignore (int_of_bit_arg "extz" "len" len);
                bits
            | _ -> Fn_registry.arity_error "extz" 2 (List.length args)
          )
      }
    );
    ( "exts",
      { params = ["bits"; "len"];
        defaults = [];
        eval =
          (fun _ ->
            Litmus.Error.failwith
              "exts is not support because of integer semantics"
          )
      }
    )
  ]
