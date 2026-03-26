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

(* Proxy to access ZArith module from coq extracted code *)
include Z

(** Pred on natural numbers *)
let pred_nat n = if n == zero then zero else pred n

(** Pred on strictly positive numbers *)
let pred_pos n = if n == one then one else pred n

(** sub on natural numbers *)
let sub_nat n m =
  let s = n - m in
  if sign s == -1 then zero else s

(** sub on strictly positive numbers *)
let sub_pos n m =
  let s = n - m in
  if sign s == 1 then s else one

(** [Z.compare] but into Rocq comparison datatype *)
let compare_rocq n m : Datatypes.comparison =
  match compare n m with 0 -> Eq | 1 -> Gt | _ -> Lt

(** [pow] between Z.

    If the exponent is negative then sends to zero as Rocq version. In addition
    in case the exponent is too large, this still solves the 1, 0, and -1 cases *)
let powZ n m =
  if sign m < 0 then zero
  else
    try pow n (to_int m)
    with Overflow ->
      if n == zero then zero
      else if n == one then one
      else if n == minus_one then if is_odd m then minus_one else one
      else raise Overflow

let to_nat n = if sign n == -1 then zero else n

let signZ z = z |> sign |> of_int

let ediv_rem_z a b = if b == zero then (zero, a) else ediv_rem a b

let ediv_z a b = if b == zero then zero else ediv a b

let erem_z a b = if b == zero then a else erem a b

let shiftl a b =
  let b = to_int b in
  if b < 0 then a asr Stdlib.(-b) else a lsl b

let shiftr a b =
  let b = to_int b in
  if b < 0 then a lsl Stdlib.(-b) else a asr b
