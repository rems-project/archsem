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

(* Supporting functions *)

let list_get i l = List.nth l (Z.to_int i)

let list_set i v l =
  let rec aux i v l =
    match (i, l) with
    | (_, []) -> raise (Invalid_argument "list_set out of bounds")
    | (0, _ :: tl) -> v :: tl
    | (n, hd :: tl) -> hd :: aux (n - 1) v tl
  in
  aux (Z.to_int i) v l

let rec list_last l =
  match l with
  | [] -> raise (Invalid_argument "list_last on empty list")
  | [x] -> x
  | _ :: tl -> list_last tl

let fin_case f0 fS n = if Z.sign n > 0 then fS (Z.pred n) else f0 ()

let fin0_magic _ = raise (Failure "Got a value of type fin 0")

let vec_eqdep_dec eq_dec _ _ v1 v2 = List.equal eq_dec v1 v2

let lengthZ l = Z.of_int (List.length l)

(** Code for Rocq's BinaryString.Raw.to_N *)
let bin_str_to_N s z = Z.((z lsl String.length s) lor of_string_base 2 s)

let hex_str_to_N s z =
  Z.((z lsl Stdlib.(4 * String.length s)) lor of_string_base 16 s)

let hex_str_of_Z z = Z.format "#x" z
