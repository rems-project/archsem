(** This module cover all thing related to uses of boolean, mainly as decidable
    proposition.

    In particular it will cover boolean reflection and decidable generic
    operations like equality. *)
From stdpp Require Import base.
From stdpp Require Export decidable.
From Hammer Require Import Tactics.
Require Export DecidableClass.

Require Import CBase.

(********** Boolean reflection **********)

(* This is a hack to make CoqHammer boolean reflection use the Is_true coercion
    from stdpp*)

(* Using a plain Require and not Require Import is critical to not import the
   is_true coercion since stdpp already uses the Is_true coercion.

   TODO: In Coq 8.15 replace by Require Import -(coercion) Reflect. *)
From Hammer Require Reflect.

(** The breflect tactic copy-pasted from Hammer.Reflect because it cannot be *)
(*     imported without coercion conflict prior to Coq 8.15 *)
Tactic Notation "breflect" :=
  try rewrite_strat topdown hints brefl.

Tactic Notation "breflect" "in" hyp(H) :=
  try rewrite_strat topdown hints brefl in H.

Tactic Notation "breflect" "in" "*" :=
  breflect;
  repeat match goal with
         | [H : _ |- _ ] => rewrite_strat topdown hints brefl in H
         end.


(* Convert the stdpp Is_True coercion to the is_true one that CoqHammer
expects. *)
Lemma true_is_true (b : bool) : b <-> is_true b.
  Proof. sauto lq:on. Qed.
#[global] Hint Rewrite -> true_is_true : brefl.
#[global] Hint Rewrite <- true_is_true : breif.

Lemma eq_true_is_true (b : bool) : b = true <-> is_true b.
  Proof. sauto lq:on. Qed.
#[global] Hint Rewrite -> eq_true_is_true : brefl.

Lemma eq_false_is_not_true (b : bool) : b = false <-> ¬ is_true b.
  Proof. sauto lq:on. Qed.
#[global] Hint Rewrite -> eq_false_is_not_true : brefl.


(* Unfortunately all boolean reflection lemmas will thus need be written with
   is_true instead of the default coercion Is_True for now. When this project
   start using Coq 8.15, this might change *)

(********** Decidable propositions **********)

(** Decidable equality notation that use the Decision type class from stdpp*)
Notation "x =? y" := (bool_decide (x = y)) (at level 70, no associativity)
    : stdpp_scope.

(** Boolean reflection of decidable equality. *)
Lemma bool_decide_is_true (P : Prop) {dec : Decision P} :
  is_true (bool_decide P) <-> P.
Proof. unfold is_true. apply bool_decide_eq_true. Qed.
#[global] Hint Rewrite bool_decide_is_true : brefl.

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
