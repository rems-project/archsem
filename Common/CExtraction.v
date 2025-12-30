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
From Stdlib Require Import Extraction.

Require Import Options.
Require Import Common.



(** * Base defaults *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlZBigInt.
From Stdlib Require Import ExtrOcamlNatBigInt.

(* Extract Constant BinNums.PosDef.Pos.add => "Big_int_Z.add_big_int". *)

Extract Inlined Constant map => "Stdlib.List.map".

Extraction Blacklist String.
Extraction Blacklist List.

Extract Inlined Constant Decision => "bool".

Extract Inductive fin => "ZO.t"
  [ "ZO.zero" "ZO.succ" ]
  "(fun _fO _fS _n -> garbage___garbage)".

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
Extraction Implicit vcons [A n].
Extraction Implicit vmap [A B n].
Extract Inlined Constant vmap => "List.map".
Extract Inlined Constant list_to_vec  => "(fun x -> x)".


Extraction Implicit vector_lookup_total [A m].
Extract Inlined Constant vector_lookup_total => "Support.list_get".

Extraction Implicit vinsert [A n].
Extract Inlined Constant vinsert => "Support.list_set".

(** * Result *)

(* Extract Inductive result => result [ "Ok" "Error"]. *)

(** * CTrans

Extract transport to identity function *)


Extract Inlined Constant ctrans => "(fun x -> x)".
Extraction Implicit ctrans [CTrans x y].
