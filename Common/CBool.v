(** This module cover all thing related to uses of boolean, mainly as decidable
    proposition.

    In particular it will cover boolean reflection and decidable generic
    operations like equality. *)
From stdpp Require Import base.
From stdpp Require Export decidable.
From stdpp Require Export sets.
From Hammer Require Import Tactics.
Require Export DecidableClass.

Require Import CBase.

From Hammer Require Reflect.


(*** Bool unfold ***)

(* This an attempt to have a custom boolean unfolding, to not need to handle the
   mess with having both is_true and Is_true coercion. *)

Class BoolUnfold (b : bool) (P : Prop) :=
  {bool_unfold : b <-> P }.
Global Hint Mode BoolUnfold + - : typeclass_instances.

Global Instance BoolUnfold_proper :
  Proper (eq ==> iff ==> iff) BoolUnfold.
Proof.
  unfold Proper.
  unfold respectful.
  intros.
  split; destruct 1; constructor; sfirstorder.
Qed.


(* Explain to coq hammer tactic how to use Is_true and BoolUnfold *)
#[export] Hint Rewrite @bool_unfold using typeclasses eauto : brefl.

Lemma true_is_true (b : bool) : b <-> is_true b.
  Proof. destruct b; naive_solver. Qed.
#[export] Hint Rewrite <- true_is_true : brefl.

Lemma true_eq_true (b : bool) : b <-> b = true.
  Proof. destruct b; naive_solver. Qed.
#[export] Hint Rewrite <- true_eq_true : brefl.


(* Basic implementation of BoolUnfold *)
Global Instance bool_unfold_default (b : bool) :
  BoolUnfold b b | 1000.
Proof. done. Qed.

Global Instance bool_unfold_false : BoolUnfold false False.
Proof. done. Qed.

Global Instance bool_unfold_true : BoolUnfold true True.
Proof. done. Qed.

Global Instance bool_unfold_and (b b' : bool) P Q :
  BoolUnfold b P -> BoolUnfold b' Q ->
  BoolUnfold (b && b') (P /\ Q).
Proof. tcclean. destruct b; destruct b'; naive_solver. Qed.

Global Instance bool_unfold_or (b b' : bool) P Q :
  BoolUnfold b P -> BoolUnfold b' Q ->
  BoolUnfold (b || b') (P \/ Q).
Proof. tcclean. destruct b; destruct b'; naive_solver. Qed.

Global Instance bool_unfold_not (b : bool) P :
  BoolUnfold b P ->
  BoolUnfold (negb b) (¬ P).
Proof. tcclean. destruct b; naive_solver. Qed.

Global Instance bool_unfold_implb (b b' : bool) P Q :
  BoolUnfold b P -> BoolUnfold b' Q ->
  BoolUnfold (implb b b') (P -> Q).
Proof. tcclean. destruct b; destruct b'; naive_solver. Qed.

Global Instance bool_unfold_iff (b b' : bool) P Q :
  BoolUnfold b P -> BoolUnfold b' Q ->
  BoolUnfold (eqb b b') (P <-> Q).
Proof. tcclean. destruct b; destruct b'; naive_solver. Qed.

Global Instance bool_unfold_bool_decide `{Decision P} :
  BoolUnfold (bool_decide P) P.
Proof. tcclean. destruct (decide P); naive_solver. Qed.



(*** Decidable propositions ***)

(** Decidable equality notation that use the Decision type class from stdpp*)
Notation "x =? y" := (bool_decide (x = y)) (at level 70, no associativity)
    : stdpp_scope.

(** Convert automatical a Decidable instance (Coq standard library) to
    a Decision instance (stdpp)

    TODO: Decide (no pun intended) if we actually want to use Decidable or
    Decision in this development. *)
Global Instance Decidable_to_Decision P `{dec : Decidable P} : Decision P :=
  match dec with
  | {| Decidable_witness := true; Decidable_spec := spec |} =>
   left ((iffLR spec) eq_refl)
  | {| Decidable_witness := false; Decidable_spec := spec |} =>
   right (fun HP => match (iffRL spec HP) with end)
  end.
