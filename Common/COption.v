(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aarhus University                                       *)
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

Require Import CBase CBool CDestruct.
Require Import Options.
From stdpp Require Import base.
From stdpp Require Export option.

(** Unpack an option into a monad by throwing an error for None *)
Definition othrow `{MThrow E M} `{MRet M} {A} (err : E) (v : option A) : M A :=
  match v with
  | None => mthrow err
  | Some x => mret x
  end.

Notation ofail := (othrow ()).

(** * EqSomeUnfold *)

Class EqSomeUnfold {A} (oa : option A) (a : A) (P : Prop) :=
  {eq_some_unfold : oa = Some a ↔ P}.
Global Hint Mode EqSomeUnfold + + - - : typeclass_instances.

Global Instance eq_some_unfold_default {A} (oa : option A) (a : A):
  EqSomeUnfold oa a (oa = Some a) | 1000.
Proof. tcclean. reflexivity. Qed.

Global Instance eq_some_unfold_Some {A} (a b : A):
  EqSomeUnfold (Some a) b (a = b).
Proof. tcclean. naive_solver. Qed.

Global Instance eq_some_unfold_None {A} (a : A):
  EqSomeUnfold None a False.
Proof. tcclean. naive_solver. Qed.

Global Instance eq_some_unfold_mret {A} (a b : A):
  EqSomeUnfold (mret a) b (a = b).
Proof. tcclean. unfold mret. unfold option_ret. naive_solver. Qed.

Global Instance eq_some_unfold_mfail {A} (a b : A):
  EqSomeUnfold mfail b False.
Proof. tcclean. unfold mfail. unfold option_mfail. naive_solver. Qed.

Global Instance eq_some_unfold_fmap {A B} (f : A → B) ma b P:
  (∀ a, EqSomeUnfold ma a (P a)) →
  EqSomeUnfold (f <$> ma) b (∃ a : A, P a ∧ b = f a).
Proof. tcclean. apply fmap_Some. Qed.

Global Instance eq_some_unfold_bind {A B} (f : A → option B) ma b P Q:
  (∀ a, EqSomeUnfold ma a (P a)) →
  (∀ a, EqSomeUnfold (f a) b (Q a)) →
  EqSomeUnfold (ma ≫= f) b (∃ a : A, P a ∧ Q a) | 20.
Proof. tcclean. apply bind_Some. Qed.

Global Instance eq_some_unfold_bind_guard `{Decision P} {A} (oa : option A) a Q:
  EqSomeUnfold oa a Q →
  EqSomeUnfold (guard P;; oa) a (P ∧ Q) | 10.
Proof. tcclean. case_guard; rewrite eq_some_unfold; naive_solver. Qed.


(** * CDestrEqSome *)

(** To enable unfolding of some equality, use this *)
Class CDestrEqSome := cdestr_eq_some {}.

#[export] Instance cdestr_eq_some_dir `{CDestrEqSome} `{EqSomeUnfold T oa a P}
  `{∀ x, Unconvertible (option T) oa (Some x)}
  `{Unconvertible Prop (oa = Some a) P} :
  CDestrSimpl (oa = Some a) P :=
  cdestr_simpl (@eq_some_unfold T oa a P _).

#[export] Instance cdestr_eq_some_rev `{CDestrEqSome} `{EqSomeUnfold T oa a P}
  `{∀ x, Unconvertible (option T) oa (Some x)}
  `{Unconvertible Prop (oa = Some a) P} :
    CDestrSimpl (Some a = oa) P.
Proof. sfirstorder. Qed.

(** * Hint database for options *)
Hint Extern 5 (_ = Some _) => progress (apply eq_some_unfold) : option.
Hint Extern 5 (Some _ = _) => progress (apply eq_some_unfold) : option.

Global Instance incomptible_None_Some {A} (a : option A) (b : A) :
  Incompatible (a = None) (a = Some b).
Proof. tcclean. cdestruct a |- **. Qed.
