Require Import CBase CBool.
From stdpp Require Import base.
From stdpp Require Export list.

(********** List automation **********)

(** Automation for list simplifications *)
Tactic Notation "list_simp" "in" "|-*" :=
  rewrite_strat topdown hints list.

Tactic Notation "list_simp" "in" hyp(H) :=
  rewrite_strat topdown hints list in H.

Tactic Notation "list_simp" :=
  progress (try list_simp in |-*;
  repeat match goal with
         | [H : _ |- _ ] => rewrite_strat topdown hints list in H
         end).

Lemma elem_of_app {A} (l l' : list A) (a : A) :
  a ∈ l ++ l' <-> a ∈ l \/ a ∈ l'.
Proof. repeat rewrite elem_of_list_In. apply in_app_iff. Qed.
#[global] Hint Rewrite @elem_of_app : list.

(** Simple type class instance should be systematically simplfied *)
Arguments list_subseteq _ _ _ /.

Lemma Forall_forall_elem_of {A} (P : A -> Prop) (l : list A) :
    Forall P l <-> ∀' x ∈ l, P x.
Proof.
  rewrite Forall_forall.
  unfold forall_elem_of.
  setoid_rewrite elem_of_list_In.
  reflexivity.
Qed.
#[global] Hint Rewrite @Forall_forall_elem_of : list.

Lemma elem_of_map {A B} (f : A → B) (l : list A) (x : A):
  x ∈ l → (f x) ∈ (map f l).
Proof. setoid_rewrite elem_of_list_In. apply in_map. Qed.
#[global] Hint Resolve elem_of_map : list.



(********** List boolean reflection **********)

(** existsb boolean reflection *)
Lemma existsb_brefl A (f : A → bool) (l : list A):
  is_true (existsb f l) ↔ ∃' x ∈ l, is_true(f x).
Proof.
  unfold is_true.
  rewrite existsb_exists.
  unfold exists_elem_of.
  setoid_rewrite elem_of_list_In.
  reflexivity.
Qed.
#[global] Hint Rewrite existsb_brefl : brefl.

(** forallb boolean reflection *)
Lemma forallb_brefl A (f : A → bool) (l : list A):
  is_true (forallb f l) ↔ ∀' x ∈ l, is_true(f x).
Proof.
  unfold is_true.
  rewrite forallb_forall.
  unfold forall_elem_of.
  setoid_rewrite elem_of_list_In.
  reflexivity.
Qed.
#[global] Hint Rewrite forallb_brefl : brefl.
