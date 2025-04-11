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

Require Import Options.
Require Import CBase CBool CDestruct.
From stdpp Require Import base.
From stdpp Require Export option.

(** Unpack an option into a monad by throwing an error for None *)
Definition othrow `{MThrow E M} `{MRet M} {A} (err : E) (v : option A) : M A :=
  match v with
  | None => mthrow err
  | Some x => mret x
  end.

Notation ofail := (othrow ()).

Definition unfold_if_Some {A} {o : option A} : (if o then True else False) → A :=
  match o as o0 return ((if o0 then True else False) → A) with
  | Some a => λ _ : True, a
  | None => λ H : False, match H with end
  end.

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


(** * EqNoneUnfold *)

Class EqNoneUnfold {A} (oa : option A) (P : Prop) :=
  {eq_none_unfold : oa = None ↔ P}.
Global Hint Mode EqNoneUnfold + + - : typeclass_instances.

Global Instance eq_none_unfold_default {A} (oa : option A):
  EqNoneUnfold oa (oa = None) | 1000.
Proof. by tcclean. Qed.

Global Instance eq_none_unfold_Some {A} (a : A):
  EqNoneUnfold (Some a) False.
Proof. by tcclean. Qed.

Global Instance eq_none_unfold_None {A}:
  EqNoneUnfold (@None A) True.
Proof. by tcclean. Qed.

Global Instance eq_none_unfold_mret {A} (a : A):
  EqNoneUnfold (mret a) False.
Proof. tcclean. unfold mret. unfold option_ret. done. Qed.

Global Instance eq_none_unfold_mfail {A} (a : A):
  @EqNoneUnfold A mfail True.
Proof. tcclean. unfold mfail. unfold option_mfail. done. Qed.

Global Instance eq_none_unfold_fmap {A B} (f : A → B) ma P:
  EqNoneUnfold ma P →
  EqNoneUnfold (f <$> ma) P.
Proof. tcclean. apply fmap_None. Qed.

Global Instance incomptible_None_Some {A} (a : option A) (b : A) :
  Incompatible (a = None) (a = Some b).
Proof. tcclean. cdestruct a |- **. Qed.


(* TODO figure out how to do the bind case in a nice way *)
#[local] Instance eq_none_unfold_bind {A B} (f : A → option B) ma P Q:
  (∀ a, EqSomeUnfold ma a (P a)) →
  (∀ a, EqNoneUnfold (f a) (Q a)) →
  EqNoneUnfold (ma ≫= f) (∀ a, P a → Q a) | 20.
Proof.
  tcclean. rewrite bind_None. cdestruct |- *** # CDestrSplitGoal.
  + congruence.
  + classical_right.
    rewrite not_eq_None_Some in H2.
    unfold is_Some in H2.
    cdestruct H2.
    naive_solver.
Qed.

Global Instance eq_none_unfold_bind_guard `{Decision P} {A} (oa : option A) Q:
  EqNoneUnfold oa Q →
  EqNoneUnfold (guard P;; oa) (¬ P ∨ Q) | 10.
Proof. tcclean. case_guard; rewrite eq_none_unfold; naive_solver. Qed.


(** * CDestrEqSome *)

(** To enable unfolding of option equality, use this *)
Class CDestrEqOpt := cdestr_eq_opt {}.

Tactic Notation "eunify" open_constr(x) open_constr(y) "with" ident(h) :=
  unify x y with h.


Class TCNotSome {T} (o : option T) := {}.
Global Hint Extern 1 (TCNotSome ?o) =>
         (assert_fails (eunify o (Some _) with typeclass_instances); constructor)
         : typeclass_instances.

Notation TCNotNone T o := (Unconvertible (option T) None o).

#[export] Instance cdestr_eq_some_order g `{CDestrEqOpt} {T} a
  `{TCNotSome T oa}:
  CDestrSimpl g (Some a = oa) (oa = Some a).
Proof. tcclean. naive_solver. Qed.

#[export] Instance cdestr_eq_none_order g `{CDestrEqOpt} {T}
  `{TCNotNone T oa}:
  CDestrSimpl g (None = oa) (oa = None).
Proof. tcclean. naive_solver. Qed.

(* TODO, This set of 4 instances is not very efficient, and not general enough *)

#[export] Instance cdestr_eq_some_clean_l g `{CDestrEqOpt} {T} (ob : option T)
  `{TCNotSome T oa}
  `{TCFastDone (oa = Some b)} :
  CDestrSimpl g (oa = ob) (ob = Some b).
Proof. tcclean. naive_solver. Qed.

#[export] Instance cdestr_eq_some_clean_r g `{CDestrEqOpt} {T} (oa : option T)
  `{TCNotSome T ob}
  `{TCFastDone (ob = Some b)} :
  CDestrSimpl g (oa = ob) (oa = Some b).
Proof. tcclean. naive_solver. Qed.

#[export] Instance cdestr_eq_nome_clean_l g `{CDestrEqOpt} {T} (ob : option T)
  `{TCNotNone T oa}
  `{TCFastDone (oa = None)} :
  CDestrSimpl g (oa = ob) (ob = None).
Proof. tcclean. naive_solver. Qed.

#[export] Instance cdestr_eq_none_clean_r g `{CDestrEqOpt} {T} (oa : option T)
  `{TCNotNone T ob}
  `{TCFastDone (ob = None)} :
  CDestrSimpl g (oa = ob) (oa = None).
Proof. tcclean. naive_solver. Qed.

#[export] Instance cdestr_eq_some_unfold g `{CDestrEqOpt}
  `{TCNotSome T oa}
  `{EqSomeUnfold T oa a P}
  `{Unconvertible Prop (oa = Some a) P} :
  CDestrSimpl g (oa = Some a) P :=
  cdestr_simpl g (@eq_some_unfold T oa a P _).

#[export] Instance cdestr_eq_none_unfold g `{CDestrEqOpt}
  `{TCNotNone T oa}
  `{EqNoneUnfold T oa P}
  `{Unconvertible Prop (oa = None) P} :
  CDestrSimpl g (oa = None) P :=
  cdestr_simpl g (@eq_none_unfold T oa P _).


(** * Hint database for options *)
Hint Extern 5 (_ = Some _) => progress (apply eq_some_unfold) : option.
Hint Extern 5 (Some _ = _) => progress (apply eq_some_unfold) : option.
Hint Extern 5 (_ = None) => progress (apply eq_none_unfold) : option.
Hint Extern 5 (None = _) => progress (apply eq_none_unfold) : option.
