(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  All files except SailArmInstTypes.v are distributed under the             *)
(*  license below (BSD-2-Clause). The former is distributed                   *)
(*  under a mix of BSD-2-Clause and BSD-3-Clause Clear, as described          *)
(*  in the file header.                                                       *)
(*                                                                            *)
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

(** This file is the top level of most the ASCommon library. Most users should
    just Require Import ASCommon.Common.
 *)

From Hammer Require Export Tactics.
From stdpp Require Export strings.
From stdpp Require Export fin.
From stdpp Require Export pretty.
From stdpp Require Export vector.
From stdpp Require Export finite.
From stdpp Require Export relations.
From stdpp Require Export propset.
From stdpp Require Export listset.
From stdpp.bitvector Require Export bitvector tactics.

Require Import Options.
Require Export CBase.
Require Export CDestruct.
Require Export CMonads.
Require Export CArith.
Require Export CBool.
Require Export CList.
Require Export CVec.
Require Export COption.
Require Export CResult.
Require Export CBitvector.
Require Export CSets.
Require Export CMaps.
Require Export CInduction.

(** * Utility functions ***)

(** Update a function at a specific value *)
Definition fun_add {A B} `{EqDecision A} (k : A) (v : B) (f : A → B) :=
  λ x, if k =? x then v else f x.

Definition dfun_add `{EqDecision A} `{CTrans A B}  (k : A) (v : B k) (f : ∀ a, B a) :=
  λ x, match decide (k = x) with
       | left e => ctrans e v
       | _ => f x
       end.


(** countable for sigT, copied from prod_countable *)
#[global] Program Instance sigT_countable `{Countable A} (P : A → Type)
  `{EqDecision (sigT P)}
  `{∀ a : A, EqDecision (P a)} `{∀ a : A, Countable (P a)} : Countable (sigT P)
  := {|
    encode xy := prod_encode (encode (xy.T1)) (encode (xy.T2));
    decode p :=
      x ← prod_decode_fst p ≫= decode;
      y ← prod_decode_snd p ≫= decode; Some (existT x y)
  |}.
Next Obligation.
  intros ??????? [x y]. cbn.
  rewrite prod_decode_encode_fst, prod_decode_encode_snd; cbn.
  by repeat (rewrite decode_encode; cbn).
Qed.


(** * Finite decidable quantifiers ***)

(* TODO maybe express with a decidable instance instead : There are consequences
   for extraction though
   TODO: That is the new plan now: move everything to Decision.
 *)

Definition fforallb `{Finite A} (P : A -> bool) : bool :=
  forallb P (enum A).

Global Instance fforallb_unfold `{Finite A} (P : A -> bool) Q:
  (forall a : A, BoolUnfold (P a) (Q a)) ->
  BoolUnfold (fforallb P) (forall a : A, Q a).
Proof.
  tcclean.
  unfold fforallb.
  rewrite bool_unfold.
  sauto lq:on dep:on.
Qed.

Definition fexistsb `{Finite A} (P : A -> bool) : bool :=
  existsb P (enum A).

Global Instance fexistsb_unfold `{Finite A} (P : A -> bool) Q:
  (forall a : A, BoolUnfold (P a) (Q a)) ->
  BoolUnfold (fexistsb P) (exists a : A, Q a).
Proof.
  tcclean.
  unfold fexistsb.
  rewrite bool_unfold.
  sauto lq:on dep:on.
Qed.


(** * Finite number utilities ***)

Global Instance pretty_fin (n : nat) : Pretty (fin n)  :=
  (fun n => pretty (n : nat)).
Global Hint Mode Pretty ! : typeclass_instances.

Definition fin_to_N {n : nat} : fin n → N := N.of_nat ∘ fin_to_nat.
Coercion fin_to_N : fin >-> N.
