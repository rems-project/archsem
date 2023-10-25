From stdpp Require Export sets.
From stdpp Require Export gmap. (* <- contains gset *)
From stdpp Require Export finite.

Require Import CBase.
Require Import Options.
Require Import CBool.
Require Import CList.
Require Import CInduction.

(** This file provide utility for dealing with sets. *)

(*** Utilities ***)

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
  (∀ x : A, Decision (P x)) → Decision (∀'x ∈ S, P x).
Proof.
  intro.
  (* setoid_rewrite should do that in one go *)
  eapply Proper_Decision. {setoid_rewrite <- elem_of_elements. reflexivity. }
  solve_decision.
Defined.

Definition mset_omap {E} `{MonadSet E} {A B} (f : A → option B) (S : E A) : E B :=
  x ← S; othrow () (f x).

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
  Context `{SS : SemiSet A C}.
  Context {lei : LeibnizEquiv C}.

  Lemma set_left_id_union (s : C) : ∅ ∪ s = s.
  Proof using SS lei. apply leibniz_equiv. set_unfold. naive_solver. Qed.

  Lemma set_right_id_union (s : C) : s ∪ ∅ = s.
  Proof using SS lei. apply leibniz_equiv. set_unfold. naive_solver. Qed.
End SetSimp.
#[global] Hint Rewrite @set_left_id_union using typeclasses eauto : set.
#[global] Hint Rewrite @set_right_id_union using typeclasses eauto : set.



(*** Set Unfolding ***)

(** This section is mostly about improving the set_unfold tactic *)



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

Global Instance set_unfold_elem_of_filter `{FinSet A B}
  `{∀ x : A, Decision (P x)} x (a : B) Q:
  SetUnfoldElemOf x a Q ->
  SetUnfoldElemOf x (filter P a) (P x ∧ Q).
Proof. tcclean. apply elem_of_filter. Qed.



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

  #[export] Instance set_elem_of_let_pair A B `{ElemOf D C} (S : A → B → C)
    (c : A * B) P (x : D):
    SetUnfoldElemOf x (S c.1 c.2) P →
    SetUnfoldElemOf x (let '(a, b) := c in S a b) P.
  Proof. tcclean. hauto l:on. Qed.
End SetUnfoldPair.


(*** Set Induction ***)

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

(** Induction principles over set_fold *)
Program Definition set_fold_cind `{FinSet A C} B (X : C)
  (b : B) (f : A -> B -> B) (P : C -> B -> Prop)
  {pr: Proper (equiv ==> eq ==> impl) P} : CInduction X (P X (set_fold f b X)) :=
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
