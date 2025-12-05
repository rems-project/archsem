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

From Stdlib Require Import ZArith.
From Stdlib Require Import Vector.
From Stdlib Require Import Extraction.

Require Import Options.
Require Import Common HVec.



(** * Base defaults *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlZBigInt.
From Stdlib Require Import ExtrOcamlNatBigInt.

(* Bool.eqb extraction *)
Extract Inlined Constant Bool.eqb => "(=)".

(* Extract Constant BinNums.PosDef.Pos.add => "Big_int_Z.add_big_int". *)

Extract Inlined Constant map => "Stdlib.List.map".

Extraction Blacklist String.
Extraction Blacklist List.

Extract Inlined Constant Decision => "bool".
Extract Inlined Constant Bool.eqb => "(=)".

Extract Inductive fin => "ZO.t"
  [ "ZO.zero" "ZO.succ" ]
  "Support.fin_case".

Extraction Implicit Fin.F1 [n].
Extraction Implicit Fin.FS [n].

Extraction Implicit fin_dec [n].
Extract Constant fin_dec => "ZO.equal".

Extraction Implicit fin_to_nat [n].
Extract Inlined Constant fin_to_nat => "(fun x -> x)".

Extract Inlined Constant fin0_magic => "Support.fin0_magic".

(** * Vector

Extracted as lists for now *)

Extract Inductive vec => list [ "[]" "( :: )" ].
Extraction Implicit vnil [A].
Extraction Implicit vcons [A n].
Extraction Implicit vmap [A B n].
Extract Inlined Constant vmap => "List.map".
Extract Inlined Constant list_to_vec  => "(fun x -> x)".

Extraction Implicit Vector.last [A n].
Extract Inlined Constant Vector.last => "Support.list_last".
Extraction Implicit Vector.append [A n p].
Extract Inlined Constant Vector.append => "List.append".

Extraction Implicit vector_lookup_total [A m].
Extract Inlined Constant vector_lookup_total => "Support.list_get".

Extraction Implicit vinsert [A n].
Extract Inlined Constant vinsert => "Support.list_set".

Extraction Implicit vec_to_list [A n].
Extract Inlined Constant vec_to_list => "(fun x -> x)".

Extraction Implicit cprodn [A n].
Extraction Implicit vmapM [A B n].

Extract Inlined Constant vec_eqdep_dec => "Support.vec_eqdep_dec".

Extraction Implicit Vector.rect2 [A B n].
Extract Constant Vector.rect2 =>
  "(fun base step v1 v2 ->
    let rec aux l1 l2 = match l1, l2 with
      | [], [] -> (Z.zero, base)
      | x :: xs, y :: ys ->
          let (n, res) = aux xs ys in
          (Z.succ n, step n xs ys res x y)
      | _, _ -> failwith ""Vector.rect2: vector length mismatch""
    in snd (aux v1 v2))".

(** * HVec *)
Extraction Implicit hget [n].
Extraction Implicit hset [n].

(** * Result *)

(* Extract Inductive result => result [ "Ok" "Error"]. *)

(** * CTrans

Extract transport to identity function *)


Extract Inlined Constant ctrans => "(fun x -> x)".
Extraction Implicit ctrans [CTrans x y].
