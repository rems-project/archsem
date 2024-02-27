(** This module cover all thing related to uses of boolean, mainly as decidable
    proposition.

    In particular it will cover boolean reflection and decidable generic
    operations like equality. *)
From stdpp Require Import base.
From stdpp Require Export decidable.
From stdpp Require Export sets.
From Hammer Require Import Tactics.
Require Import DecidableClass.

Require Import CBase.
Require Import Options.

From Hammer Require Reflect.


(** * Bool unfold ***)

(* This an attempt to have a custom boolean unfolding, to not need to handle the
   mess with having both is_true and Is_true coercion. *)

Class BoolUnfold (b : bool) (P : Prop) :=
  {bool_unfold : b <-> P }.
Global Hint Mode BoolUnfold + - : typeclass_instances.

Global Instance BoolUnfold_proper :
  Proper (eq ==> iff ==> iff) BoolUnfold.
Proof. solve_proper2_tc. Qed.


(* Explain to coq hammer tactic how to use Is_true and BoolUnfold *)
#[export] Hint Rewrite @bool_unfold using typeclasses eauto : brefl.

Lemma true_is_true (b : bool) : b ↔ is_true b.
  Proof. destruct b; naive_solver. Qed.
#[export] Hint Rewrite <- true_is_true : brefl.

Lemma true_eq_true (b : bool) : b ↔ b = true.
  Proof. destruct b; naive_solver. Qed.
#[export] Hint Rewrite <- true_eq_true : brefl.

Lemma not_eq_false (b : bool) : ¬ b ↔ b = false.
  Proof. destruct b; naive_solver. Qed.
#[export] Hint Rewrite <- not_eq_false : brefl.



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

Global Instance bool_unfold_pair A B c (b : A → B → bool) P:
  (∀ x y, BoolUnfold (b x y) (P x y)) →
  BoolUnfold (let '(x, y) := c in b x y) (let '(x, y) := c in P x y).
Proof. by destruct c. Qed.


(** * Decidable propositions ***)

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
#[global] Hint Mode Decidable + : typeclass_instances.

#[global] Instance proof_irrel_eq_decision (P : Prop) (PI : ProofIrrel P):
  EqDecision P :=
  λ x y, left (PI x y).

Section ProperDecision.
  Import CMorphisms.

  (** Magic that allow rewriting in decision instances using ↔
      Might be slow, so you might need to use it by hand
   *)
  Global Instance Proper_Decision :
    Proper (iff ==> (flip arrow)) Decision.
  Proof using.
    intros x y H []; [left | right]; naive_solver.
  Defined.
End ProperDecision.

Ltac pair_let_clean_Decision :=
  match goal with
    |- context G [(let '(x, y) := _ in _)] =>
      eapply Proper_Decision;[
        pair_let_clean; reflexivity
      |]
  end.
#[export] Hint Extern 10 (Decision _) =>
  pair_let_clean_Decision : typeclass_instances.

Tactic Notation "decide_field" constr(a) constr(b) :=
  tryif unify a b then idtac else
  (odestruct (@decide (a = b));
  [ try (apply _) |
    subst |
    let H := fresh "H" in
    right; intro H; inversion H; naive_solver
  ]).

Ltac decide_eq :=
  lazymatch goal with
  | |- Decision (?f ?a ?b ?c ?d ?e ?f ?g = ?f ?a' ?b' ?c' ?d' ?e' ?f' ?g') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      decide_field d d'; [ .. |
      decide_field e e'; [ .. |
      decide_field f f'; [ .. |
      decide_field g g'; [ .. |
      left; reflexivity]]]]]]]
  | |- Decision (?f ?a ?b ?c ?d ?e ?f = ?f ?a' ?b' ?c' ?d' ?e' ?f') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      decide_field d d'; [ .. |
      decide_field e e'; [ .. |
      decide_field f f'; [ .. |
      left; reflexivity]]]]]]
  | |- Decision (?f ?a ?b ?c ?d ?e = ?f ?a' ?b' ?c' ?d' ?e') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      decide_field d d'; [ .. |
      decide_field e e'; [ .. |
      left; reflexivity]]]]]
  | |- Decision (?f ?a ?b ?c ?d = ?f ?a' ?b' ?c' ?d') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      decide_field d d'; [ .. |
      left; reflexivity]]]]
  | |- Decision (?f ?a ?b ?c = ?f ?a' ?b' ?c') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      left; reflexivity]]]
  | |- Decision (?f ?a ?b = ?f ?a' ?b') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      left; reflexivity]]
  | |- Decision (?f ?a = ?f ?a') =>
      decide_field a a'; [ .. |
      left; reflexivity]
  | |- Decision (?f = ?f) => left; reflexivity
  | |- Decision (_ = _) => right; discriminate
  end.

(** Hint database to decide equality *)
Create HintDb eqdec discriminated.


#[global] Hint Extern 3 => progress cbn : eqdec.
#[global] Hint Extern 10 (Decision (_ = _)) => decide_eq : eqdec.
#[global] Hint Extern 4 (Decision (?a =@{_ * _} _)) => is_var a; destruct a : eqdec.
#[global] Hint Extern 4 (Decision (_ =@{_ * _} ?b)) => is_var b; destruct b : eqdec.
#[global] Hint Extern 4 (Decision (?a =@{option _} _)) => is_var a; destruct a : eqdec.
#[global] Hint Extern 4 (Decision (_ =@{option _} ?b)) => is_var b; destruct b : eqdec.

(** EqDecision on sigT *)
Lemma eqdec_existT `{EqDecision A} {P : A -> Type} (p : A) (x y : P p) :
  existT p x = existT p y <-> x = y.
  Proof. hauto q:on use: Eqdep_dec.inj_pair2_eq_dec. Qed.
#[global] Hint Rewrite @eqdec_existT using typeclasses eauto : core.

Global Instance sigT_dec `{EqDecision A} (P : A -> Type)
  `{forall a: A, EqDecision (P a)} : EqDecision (sigT P).
  unfold EqDecision.
  intros [x p] [y q].
  destruct (decide (x = y)) as [e | e].
  - destruct e.
    destruct (decide (p = q)) as [e | e].
    + destruct e.
      left.
      reflexivity.
    + right.
      intro.
      apply e.
      apply eqdec_existT.
      assumption.
  - right.
    intro.
    apply e.
    eapply eq_sigT_fst.
    eassumption.
Defined.

(* Add a hint for resolving Decision of matches*)
#[export] Hint Extern 10 (Decision match ?x with _ => _ end) =>
  destruct x : typeclass_instances.

#[export] Hint Extern 3 (Decision _) => progress cbn : typeclass_instances.
