Require Import CBase CBool.
From stdpp Require Import base.
From stdpp Require Export list.
From stdpp Require Export listset.

(********** List simplification **********)

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

#[global] Hint Rewrite <- app_assoc : list.
#[global] Hint Rewrite map_app : list.

Lemma elem_of_app {A} (l l' : list A) (a : A) :
  a ∈ l ++ l' <-> a ∈ l \/ a ∈ l'.
Proof. repeat rewrite elem_of_list_In. apply in_app_iff. Qed.
#[global] Hint Rewrite @elem_of_app : list.

(** Simple type class instance should be systematically simplfied *)
Arguments list_subseteq _ _ _ /.

#[global] Hint Rewrite @Forall_forall : list.

Lemma elem_of_map {A B} (f : A → B) (l : list A) (x : A):
  x ∈ l → (f x) ∈ (map f l).
Proof. setoid_rewrite elem_of_list_In. apply in_map. Qed.
#[global] Hint Resolve elem_of_map : list.

Lemma elem_of_map_iff {A B} (f : A -> B) (l : list A) (x : B):
  x ∈ map f l <-> ∃'y ∈ l, x = f y.
Proof.
  setoid_rewrite elem_of_list_In.
  rewrite in_map_iff.
  firstorder.
Qed.
(* #[global] Hint Rewrite @elem_of_map_iff : list. *)

Lemma forall_elem_of_map {A B} (f : A -> B) (l : list A) (P : B -> Prop) :
  (∀'x ∈ map f l, P x) <-> ∀'y ∈ l, P (f y).
Proof.
  setoid_rewrite elem_of_map_iff.
  hauto lq:on.
Qed.
#[global] Hint Rewrite @forall_elem_of_map : list.

(********** List lookup with different keys **********)

Global Instance list_lookupPos {A} : Lookup positive A (list A) :=
  fun p l => l !! (Pos.to_nat p).

Global Instance list_lookupN {A} : Lookup N A (list A) :=
  fun n l => l !! (N.to_nat n).

Global Instance list_lookupZ {A} : Lookup Z A (list A) :=
  fun z l =>
    match z with
    | Zpos p => l !! p
    | Z0 => head l
    | Zneg _ => None
    end.

(********** List boolean reflection **********)

(** existsb boolean reflection *)
Lemma existsb_brefl A (f : A → bool) (l : list A):
  is_true (existsb f l) ↔ ∃'x ∈ l, is_true(f x).
Proof.
  unfold is_true.
  rewrite existsb_exists.
  setoid_rewrite elem_of_list_In.
  reflexivity.
Qed.
#[global] Hint Rewrite existsb_brefl : brefl.

(** forallb boolean reflection *)
Lemma forallb_brefl A (f : A → bool) (l : list A):
  is_true (forallb f l) ↔ ∀'x ∈ l, is_true(f x).
Proof.
  unfold is_true.
  rewrite forallb_forall.
  setoid_rewrite elem_of_list_In.
  reflexivity.
Qed.
#[global] Hint Rewrite forallb_brefl : brefl.



(********** List as sets **********)

(* TODO make a PR to stdpp with this: *)
Global Instance list_omap : OMap listset := λ A B f '(Listset l),
    Listset (omap f l).

Global Instance list_Empty {A} : Empty (list A) := [].


(********** List utility functions **********)

Fixpoint list_from_func_aux {A} (f : nat -> A) (len : nat) (acc : list A) :=
  match len with
  | 0 => acc
  | S len => list_from_func_aux f len ((f len) :: acc)
  end.

Definition list_from_func (len : nat) {A} (f : nat -> A) :=
  list_from_func_aux f len [].

Lemma list_from_func_aux_eq {A} (f : nat -> A) n acc :
  list_from_func_aux f n acc = list_from_func n f ++ acc.
Proof.
  generalize dependent acc.
  induction n.
  - sfirstorder.
  - sauto db:list simp+:cbn;rewrite IHn.
Qed.

Lemma seq_end n l : seq n (S l) = seq n l ++ [n + l].
Proof.
  generalize dependent n.
  induction l; sauto db:list.
Qed.

Lemma list_from_func_map {A} (f : nat -> A) n :
  list_from_func n f = map f (seq 0 n).
Proof.
  induction n; sauto lq:on db:list use:seq_end,list_from_func_aux_eq.
Qed.
