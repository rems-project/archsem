From stdpp Require Export sets.
From stdpp Require Export gmap. (* <- contains gset *)
From stdpp Require Export finite.

Require Import CBase.
Require Import CBool.
Require Import CInduction.

(** This file provide utility for dealing with sets. *)

(*** Simplification ***)

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
  Context `{SemiSet A C}.
  Context {lei : LeibnizEquiv C}.

  Lemma set_left_id_union (s : C) : ∅ ∪ s = s.
  Proof. apply leibniz_equiv. set_unfold. naive_solver. Qed.

  Lemma set_right_id_union (s : C) : s ∪ ∅ = s.
  Proof. apply leibniz_equiv. set_unfold. naive_solver. Qed.
End SetSimp.
#[global] Hint Rewrite @set_left_id_union using typeclasses eauto : set.
#[global] Hint Rewrite @set_right_id_union using typeclasses eauto : set.



(*** Set Unfolding ***)

(** This section is mostly about improving the set_unfold tactic *)

(* TODO make solve_proper work *)
(* TODO upstream to stdpp *)
Global Instance SetUnfold_proper :
  Proper (iff ==> iff ==> iff) SetUnfold.
Proof.
  unfold Proper.
  unfold respectful.
  intros.
  split; destruct 1; constructor; sfirstorder.
Qed.

Global Instance SetUnfoldElemOf_proper `{ElemOf A C}  :
  Proper ((=@{A}) ==> (≡@{C}) ==> iff ==> iff) SetUnfoldElemOf.
Proof.
  unfold Proper.
  unfold respectful.
  intros.
  split; destruct 1; constructor; sfirstorder.
Qed.


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

Global Instance set_unfold_Some A Q (x y : A) :
  SetUnfold (x = y) Q -> SetUnfold (Some x = Some y) Q.
Proof. sauto lq:on. Qed.

Global Instance set_unfold_enum `{Finite A} a :
  SetUnfoldElemOf a (enum A) True.
Proof. tcclean. sauto. Qed.

(** Import this module so that set_unfold unfold X = Y into
    (x,y) ∈ X  <-> (x,y) ∈ Y if X and Y are sets of pairs *)
Module SetUnfoldPair.

  #[export] Instance set_unfold_equiv_pair `{ElemOf (A * B) C}
  (P Q : A -> B → Prop) (X Y : C) :
  (∀ x y, SetUnfoldElemOf (x, y) X (P x y)) →
  (∀ x y, SetUnfoldElemOf (x, y) Y (Q x y)) →
  SetUnfold (X ≡ Y) (∀ x y, P x y ↔ Q x y) | 9.
  Proof. tcclean. set_unfold. hauto. Qed.

  #[export] Instance set_unfold_equiv_L_pair `{ElemOf (A * B) C} {l : LeibnizEquiv C}
  (P Q : A -> B → Prop) (X Y : C) :
  (∀ x y, SetUnfoldElemOf (x, y) X (P x y)) →
  (∀ x y, SetUnfoldElemOf (x, y) Y (Q x y)) →
  SetUnfold (X = Y) (∀ x y, P x y ↔ Q x y) | 9.
  Proof. tcclean. unfold_leibniz. set_unfold. hauto. Qed.
End SetUnfoldPair.


(*** Set Induction ***)

(* There are some case where both instances can apply, but they both give the
   same result so we don't really care which one is chosen *)

Program Global Instance set_cind `{FinSet A C} (X : C) (P : C -> Prop)
  {pr: Proper (equiv ==> iff) P} : CInduction X (P X) :=
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

(** Induction principles over set_fold *)
Program Definition set_fold_cind `{FinSet A C} B (X : C)
  (b : B) (f : A -> B -> B) (P : C -> B -> Prop)
  {pr: Proper (equiv ==> eq ==> iff) P} : CInduction X (P X (set_fold f b X)) :=
  {|
    induction_requirement :=
      (P ∅ b) /\ (forall x X r, x ∉ X -> P X r -> P ({[x]} ∪ X) (f x r))
  |}.
Solve All Obligations with
  intros; apply (set_fold_ind (fun x y => P y x)); [solve_proper | hauto..].
Arguments set_fold_cind : clear implicits.

Program Definition set_fold_cind_L `{FinSet A C} B (X : C)
  {lei : LeibnizEquiv C} (b : B) (f : A -> B -> B) (P : C -> B -> Prop)
   : CInduction X (P X (set_fold f b X)) :=
  {|
    induction_requirement :=
      (P ∅ b) /\ (forall x X r, x ∉ X -> P X r -> P ({[x]} ∪ X) (f x r))
  |}.
Solve All Obligations with
  intros; apply (set_fold_ind_L (fun x y => P y x)); hauto.

Arguments set_fold_cind_L : clear implicits.


(*** GSet Cartesian product ***)


Section GSetProduct.
  Context `{Countable A}.
  Context `{Countable B}.

  Definition gset_product (sa : gset A) (sb : gset B) : gset (A * B) :=
    set_fold (fun e1 res => res ∪ set_map (e1,.) sb) ∅ sa.

  (** × must be left associative because the * of types is left associative.
      Thus if you have sa : gset A, sb : gset B and sc : gset C, then
      sa × sb × sc : gset (A * B * C) *)
  Infix "×" := gset_product (at level 44, left associativity) : stdpp_scope.

  Lemma gset_product_spec (sa : gset A) (sb : gset B) a b :
    (a, b) ∈ sa × sb <-> a ∈ sa /\ b ∈ sb.
  Proof using.
    unfold gset_product.
    cinduction sa using set_fold_cind_L; set_solver.
  Qed.

  Global Instance set_unfold_gset_product (sa : gset A) (sb : gset B) x P Q :
    SetUnfoldElemOf x.1 sa P -> SetUnfoldElemOf x.2 sb Q ->
    SetUnfoldElemOf x (sa × sb) (P /\ Q).
  Proof using. tcclean. destruct x. apply gset_product_spec. Qed.
End GSetProduct.
Infix "×" := gset_product (at level 44, left associativity) : stdpp_scope.
