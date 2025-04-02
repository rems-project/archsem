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

From stdpp Require Export sets.
From stdpp Require Export gmap. (* <- contains gset *)
From stdpp Require Export finite.

Require Import Options.
Require Import CBase.
Require Import CBool.
Require Import COption.
Require Import CList.
Require Import CInduction.
Require Import CDestruct.

(** This file provide utility for dealing with sets. *)

(** * Utilities ***)

Lemma elements_singleton_iff `{FinSet A C} (s : C) (a : A) :
  elements s = [a] <-> s ≡ {[a]}.
Proof.
  rewrite <- Permutation_singleton_r.
  assert (NoDup [a]). { sauto lq:on. }
  assert (NoDup (elements s)). { sfirstorder. }
  set_solver.
Qed.


(** The size of a finite set. *)
Definition set_size `{Elements A C} (s : C) : nat := length (elements s).

Global Instance proper_set_size_equiv `{FinSet A C} :
  Proper (equiv ==> eq) (set_size : C -> nat).
Proof. solve_proper2_funcs. Qed.

Lemma set_size_zero `{FinSet A C} (s : C) :
  set_size s = 0 <-> s ≡ ∅.
Proof.
  unfold set_size.
  rewrite length_zero_iff_nil.
  apply elements_empty_iff.
Qed.

Lemma set_size_zero_L `{FinSet A C} {lei : LeibnizEquiv C} (s : C) :
  set_size s = 0 <-> s = ∅.
Proof. rewrite set_size_zero. hauto l:on. Qed.

Lemma set_size_one `{FinSet A C} (s : C) :
  set_size s = 1 <-> exists x : A, s ≡ {[x]}.
Proof.
  unfold set_size.
  rewrite length_one_iff_singleton.
  hauto lq:on use:elements_singleton_iff.
Qed.

Lemma set_size_one_L `{FinSet A C} {lei : LeibnizEquiv C} (s : C) :
  set_size s = 1 <-> exists x : A, s = {[x]}.
Proof. rewrite set_size_one. set_solver. Qed.

Lemma set_size_le1 `{FinSet A C} (s : C) :
  set_size s ≤ 1 ↔ (∀ y z : A, y ∈ s → z ∈ s → y = z).
Proof.
  unfold set_size.
  setoid_rewrite <- elem_of_elements.
  assert (NoDup (elements s)). { sfirstorder. }
  generalize dependent (elements s). intros l ND.
  do 2 (destruct ND;[sauto lq:on rew:off|]).
  split.
  - sauto q:on.
  - set_solver.
Qed.

Definition set_forallb `{Elements A C} (P : A -> bool) (s : C) :=
  forallb P (elements s).

Definition option_to_set (C : Type) `{Empty C} `{Singleton A C} (o : option A) : C :=
  match o with
  | None => ∅
  | Some a => {[a]}
  end.

Global Instance set_unfold_option_to_set `{SemiSet A C} (o : option A) x:
  SetUnfoldElemOf x (option_to_set C o) (o = Some x).
Proof. tcclean. unfold option_to_set. sauto lq:on. Qed.

Global Instance forall_gset_decision `{Countable A} P (S : gset A):
  (∀ x : A, Decision (P x)) → Decision (∀ x ∈ S, P x).
Proof.
  intro.
  (* setoid_rewrite should do that in one go *)
  eapply Proper_Decision. {setoid_rewrite <- elem_of_elements. reflexivity. }
  solve_decision.
Defined.

Definition mset_omap {E} `{MonadSet E} {A B} (f : A → option B) (S : E A) : E B :=
  x ← S; othrow () (f x).
#[global] Typeclasses Transparent mset_omap.

(** * Simplification ***)

(** Automation for set simplifications *)
Tactic Notation "set_simp" "in" "|-*" :=
  rewrite_strat topdown hints set.

Tactic Notation "set_simp" "in" hyp(H) :=
  rewrite_strat topdown hints set in H.

Tactic Notation "set_simp" :=
  progress (try set_simp in |-*;
  repeat match goal with
         | [H : _ |- _ ] => rewrite_strat topdown hints set in H
         end).

#[global] Hint Rewrite @set_fold_empty using typeclasses eauto : set.
#[global] Hint Rewrite @set_fold_singleton using typeclasses eauto : set.
#[global] Hint Rewrite @empty_union_L using typeclasses eauto : set.


Section SetSimp.
  Context {A C : Type}.
  Context `{SS : SemiSet A C}.
  Context {lei : LeibnizEquiv C}.

  Lemma set_left_id_union (s : C) : ∅ ∪ s = s.
  Proof using SS lei. apply leibniz_equiv. set_unfold. naive_solver. Qed.

  Lemma set_right_id_union (s : C) : s ∪ ∅ = s.
  Proof using SS lei. apply leibniz_equiv. set_unfold. naive_solver. Qed.
End SetSimp.
#[global] Hint Rewrite @set_left_id_union using typeclasses eauto : set.
#[global] Hint Rewrite @set_right_id_union using typeclasses eauto : set.



(** * Set Unfolding ***)

(** This section is mostly about improving the set_unfold tactic *)

(** Allows [set_unfold] and related tactics to unfold through match case (and
    thus also let binding with patterns) *)
Class SetUnfoldMatch := {}.

(** To enable that option file wide, use
    [#[local] Existing Instance set_unfold_match] *)
Definition set_unfold_match : SetUnfoldMatch := ltac:(constructor).

(** This unfold [x ∈ match exp with pat1 => exp1 | pat2 => exp2 end] into [match
exp with | pat1 => x ∈ exp1 | pat2 => x ∈ exp2] *)
#[export] Hint Extern 5 (SetUnfoldElemOf ?x (match ?b with _ => _ end) ?G) =>
  has_option SetUnfoldMatch;
  let H := fresh in
  match G with
  | ?Q => is_evar Q; unshelve eassert (SetUnfoldElemOf x _ _) as H
  | ?Q ?y => is_evar Q; unshelve eassert (SetUnfoldElemOf x _ (_ y)) as H
  | ?Q ?x ?y => is_evar Q; unshelve eassert (SetUnfoldElemOf x _ (_ x y)) as H
  | ?Q ?x ?y ?z => is_evar Q; unshelve eassert (SetUnfoldElemOf x _ (_ x y z)) as H
  end;
  [.. | apply H];
  [intros; destruct b; shelve | ..];
  destruct b; cbn zeta match : typeclass_instances.

#[export] Hint Extern 5 (SetUnfold (match ?b with _ => _ end) ?G) =>
  has_option SetUnfoldMatch;
  let H := fresh in
  match G with
  | ?Q => is_evar Q; unshelve eassert (SetUnfold _ _) as H
  | ?Q ?y => is_evar Q; unshelve eassert (SetUnfold _ (_ y)) as H
  | ?Q ?x ?y => is_evar Q; unshelve eassert (SetUnfold _ (_ x y)) as H
  | ?Q ?x ?y ?z => is_evar Q; unshelve eassert (SetUnfold _ (_ x y z)) as H
  end;
  [.. | apply H];
  [destruct b; shelve | ..];
  destruct b; cbn zeta match : typeclass_instances.


(** [set unfold] on [if bool_decide ...]. This is redundant with the above but enable
    systematically without option *)
Global Instance set_unfold_elem_of_if_bool_decide `{ElemOf A C} `{Decision P}
  (x : A) (X Y : C) Q R:
  SetUnfoldElemOf x X Q -> SetUnfoldElemOf x Y R ->
  SetUnfoldElemOf x (if bool_decide P then X else Y) (if bool_decide P then Q else R).
Proof. sauto q:on. Qed.

Global Instance set_unfold_elem_of_if_decide `{ElemOf A C} `{Decision P}
  (x : A) (X Y : C) Q R:
  SetUnfoldElemOf x X Q -> SetUnfoldElemOf x Y R ->
  SetUnfoldElemOf x (if decide P then X else Y) (if decide P then Q else R).
Proof. sauto lq:on. Qed.

(* TODO delete, this had noting to do with sets *)
Global Instance set_unfold_Some A Q (x y : A) :
  SetUnfold (x = y) Q -> SetUnfold (Some x = Some y) Q.
Proof. sauto lq:on. Qed.

Global Instance set_unfold_enum `{Finite A} a :
  SetUnfoldElemOf a (enum A) True.
Proof. tcclean. sauto. Qed.

Global Instance set_unfold_elem_of_filter `{FinSet A B}
  `{∀ x : A, Decision (P x)} x (a : B) Q:
  SetUnfoldElemOf x a Q ->
  SetUnfoldElemOf x (filter P a) (P x ∧ Q).
Proof. tcclean. apply elem_of_filter. Qed.


(** Import this module so that set_unfold unfold X = Y into
    (x,y) ∈ X  <-> (x,y) ∈ Y if X and Y are sets of pairs *)
(* TODO use a tactic option instead of a module *)
Module SetUnfoldPair.
Section SUP.
  Context `{SS: SemiSet (A * B) C}.
  Variable (P Q : A → B → Prop).
  Variable (X Y : C).

  #[export] Instance set_unfold_equiv_pair:
    (∀ x y, SetUnfoldElemOf (x, y) X (P x y)) →
    (∀ x y, SetUnfoldElemOf (x, y) Y (Q x y)) →
    SetUnfold (X ≡ Y) (∀ x y, P x y ↔ Q x y) | 9.
  Proof using SS. tcclean. set_unfold. hauto. Qed.

  #[export] Instance set_unfold_subseteq_pair :
    (∀ x y, SetUnfoldElemOf (x, y) X (P x y)) →
    (∀ x y, SetUnfoldElemOf (x, y) Y (Q x y)) →
    SetUnfold (X ⊆ Y) (∀ x y, P x y → Q x y) | 1.
  Proof using SS. tcclean. set_unfold. hauto. Qed.

  #[export] Instance set_unfold_equiv_empty_r_pair:
    (∀ x y, SetUnfoldElemOf (x,y) X (P x y)) →
    SetUnfold (X ≡ ∅) (∀ x y, ¬P x y) | 4.
  Proof using SS. clear Q. tcclean. set_unfold. hauto. Qed.

  #[export] Instance set_unfold_equiv_empty_l_pair:
    (∀ x y, SetUnfoldElemOf (x,y) X (P x y)) →
    SetUnfold (∅ ≡ X) (∀ x y, ¬P x y) | 4.
  Proof using SS. clear Q. tcclean. set_unfold. hauto. Qed.

  Context {l : LeibnizEquiv C}.
  #[export] Instance set_unfold_equiv_L_pair:
    (∀ x y, SetUnfoldElemOf (x, y) X (P x y)) →
    (∀ x y, SetUnfoldElemOf (x, y) Y (Q x y)) →
    SetUnfold (X = Y) (∀ x y, P x y ↔ Q x y) | 9.
  Proof using SS l. tcclean. set_unfold. hauto. Qed.

  #[export] Instance set_unfold_equiv_empty_r_L_pair:
    (∀ x y, SetUnfoldElemOf (x,y) X (P x y)) →
    SetUnfold (X = ∅) (∀ x y, ¬P x y) | 4.
  Proof using SS l. clear Q. tcclean. set_unfold. hauto. Qed.

  #[export] Instance set_unfold_equiv_empty_l_L_pair:
    (∀ x y, SetUnfoldElemOf (x,y) X (P x y)) →
    SetUnfold (∅ = X) (∀ x y, ¬P x y) | 4.
  Proof using SS l. clear Q. tcclean. set_unfold. hauto. Qed.

End SUP.
End SetUnfoldPair.

(** Import this module to make CDestruct do set unfolding automatically. For now
    only in the [x ∈ C] case *)
Module CDestrUnfoldElemOf.
  Instance cdestr_unfold_elem_of b `{ElemOf A C} (x : A) (S : C) P:
    SetUnfoldElemOf x S P →
    Unconvertible Prop (x ∈ S) P →
    CDestrSimpl b (x ∈ S) P.
  Proof. by tcclean. Qed.
  Hint Mode SetUnfoldElemOf + + + + ! - : typeclass_instances.
End CDestrUnfoldElemOf.



(** * Set Induction ***)

(* There are some case where both instances can apply, but they both give the
   same result so we don't really care which one is chosen *)

Program Global Instance set_cind `{FinSet A C} (X : C) (P : C -> Prop)
  {pr: Proper (equiv ==> impl) P} : CInduction X (P X) :=
  {|
    induction_requirement :=
      (P ∅) /\ (forall x X, x ∉ X -> P X -> P ({[x]} ∪ X))
  |}.
Solve All Obligations with intros; apply set_ind; naive_solver.

Program Global Instance set_cind_L `{FinSet A C} {lei : LeibnizEquiv C}
  (X : C) (P : C -> Prop) : CInduction X (P X) :=
  {|
    induction_requirement :=
      (P ∅) /\ (forall x X, x ∉ X -> P X -> P ({[x]} ∪ X))
  |}.
Solve All Obligations with intros; apply set_ind_L; naive_solver.

(* Implement funelim on [set_fold].

In general, the order of parameters needs to be:
   - Fixed parameters that are not changing in the induction
   - The induction property P
   - The induction cases
   - The arguments that are being inducted upon
   - The conclusion, which is P applied to the arguments in function order,
     then the function application
 *)
Lemma set_fold_ind_L' `{FinSet A C} `{!LeibnizEquiv C}
  {B} (f : A → B → B) (b : B) (P : C → B → Prop) :
  P ∅ b → (∀ x X r, x ∉ X → P X r → P ({[ x ]} ∪ X) (f x r)) →
  ∀ X, P X (set_fold f b X).
Proof. eapply (set_fold_ind_L (flip P)). Qed.

(* Then when instantiating the typeclass, all the non-inductive parameters
   should be instance parameters, and the magic integer should be 1 (for P) +
   the number of induction cases (here 2)

WARN: FinSet (and LeibnizEquiv) typeclass needs to be either resolvable from
   constants (e.g. with a concrete C type like gset) or be a section variable,
   otherwise funelim gets confused if it's just a local lemma variable. *)
#[global] Instance FunctionalElimination_set_fold_L
  `{FinSet A C} `{!LeibnizEquiv C} {B} f b :
  FunctionalElimination (@set_fold A C _ B f b) _ 3 :=
  set_fold_ind_L' (A := A) (C := C) f b.
