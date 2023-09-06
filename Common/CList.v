Require Import CBase CBool CMaps.
From stdpp Require Import base.
From stdpp Require Export list.
From stdpp Require Export listset.

Global Instance proper_list_mbind A B :
  Proper (pointwise_relation A (=) ==> (=@{list A}) ==> (=@{list B})) mbind.
Proof.
  intros x y H ? l ->.
  unfold pointwise_relation in H.
  induction l; hauto q:on.
Qed.


(*** List simplification ***)

(* TODO all list simplification about x ∈ l should be superseded by set_unfold *)

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

Lemma Permutation_elem_of A (l l' : list A) x: l ≡ₚ l' → x ∈ l → x ∈ l'.
Proof. setoid_rewrite elem_of_list_In. apply Permutation_in. Qed.

(* TODO add some standard proof search for NoDup *)
Global Instance set_unfold_list_permutation A (l l' : list A) P Q:
  TCFastDone (NoDup l) ->
  TCFastDone (NoDup l') ->
  (forall x, SetUnfoldElemOf x l (P x)) ->
  (forall x, SetUnfoldElemOf x l' (Q x)) ->
  SetUnfold (l ≡ₚ l') (forall x, P x <-> Q x).
Proof.
  tcclean.
  split.
  - sfirstorder use:Permutation_elem_of use:Permutation_sym.
  - sfirstorder use:NoDup_Permutation.
Qed.

(*** List lookup with different keys ***)

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

(*** List boolean unfolding ***)

Global Instance bool_unfold_existsb A (f : A -> bool) (l : list A) (P : A -> Prop) :
  (forall a, BoolUnfold (f a) (P a)) ->
  BoolUnfold (existsb f l) (∃'x ∈ l, P x).
Proof.
  tcclean.
  setoid_rewrite true_is_true.
  unfold is_true.
  rewrite existsb_exists.
  setoid_rewrite elem_of_list_In.
  reflexivity.
Qed.

Global Instance bool_unfold_forallb A (f : A -> bool) (l : list A) (P : A -> Prop) :
  (forall a, BoolUnfold (f a) (P a)) ->
  BoolUnfold (forallb f l) (∀'x ∈ l, P x).
Proof.
  tcclean.
  setoid_rewrite true_is_true.
  unfold is_true.
  rewrite forallb_forall.
  setoid_rewrite elem_of_list_In.
  reflexivity.
Qed.


(*** List as sets ***)

(* TODO make a PR to stdpp with this: *)
Global Instance list_omap : OMap listset := λ A B f '(Listset l),
    Listset (omap f l).

Global Instance list_Empty {A} : Empty (list A) := [].

Global Instance set_unfold_elem_of_filter_list A
  `{∀ x : A, Decision (P x)} x (a : list A) Q:
  SetUnfoldElemOf x a Q ->
  SetUnfoldElemOf x (filter P a) (P x ∧ Q).
Proof. tcclean. apply elem_of_list_filter. Qed.

(*** List utility functions ***)

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

Definition is_emptyb {A} (l : list A) :=
  match l with
  | [] => true
  | _ => false
  end.

Lemma is_emptyb_eq_nil {A} (l : list A) : is_true (is_emptyb l) <-> l = [].
Proof. sauto lq:on. Qed.
#[global] Hint Rewrite @is_emptyb_eq_nil: brefl.

Definition enumerate {A} (l : list A) : list (nat * A) :=
  zip_with pair (seq 0 (length l)) l.
#[global] Typeclasses Opaque enumerate.
#[global] Typeclasses Opaque zip_with.


Global Instance set_elem_of_zip_with A B C (x : C) (f : A → B → C) l1 l2:
  SetUnfoldElemOf x (zip_with f l1 l2)
    (∃ (n : nat) y z, l1 !! n = Some y ∧ l2 !! n = Some z ∧ f y z = x) | 10.
Proof. tcclean. rewrite elem_of_lookup_zip_with. naive_solver. Qed.

Global Instance set_elem_of_zip A B (x : A * B) l1 l2:
  SetUnfoldElemOf x (zip l1 l2)
    (∃ (n : nat), l1 !! n = Some x.1 ∧ l2 !! n = Some x.2).
Proof. tcclean. set_unfold. hauto lq:on. Qed.

Global Instance lookup_seq n i l:
  LookupUnfold n (seq i l) (if decide (n < l) then Some (n + i) else None)%nat.
Proof.
  tcclean.
  generalize dependent i.
  generalize dependent n.
  induction l; intros n i.
  - compute_done.
  - destruct n; cbn; try reflexivity.
    rewrite IHl.
    hauto l:on.
Qed.

Lemma lookup_seq_success (n i l m : nat):
  (seq i l) !! n = Some m → m = (n + i)%nat.
Proof. rewrite lookup_unfold. case_decide; naive_solver. Qed.

Lemma lookup_length A (l : list A) n x :
  l !! n = Some x → (n < length l)%nat.
Proof. rewrite <- lookup_lt_is_Some. naive_solver. Qed.

Ltac list_saturate :=
  match goal with
  | H : _ !! _ = Some _ |- _ => learn_hyp (lookup_length _ _ _ _ H)
  | H : _ !! _ = Some _ |- _ => learn_hyp (elem_of_list_lookup_2 _ _ _ H)
  end.

Global Instance set_elem_of_enumerate A (x : nat * A) l:
  SetUnfoldElemOf x (enumerate l) (l !! x.1 = Some x.2).
Proof.
  tcclean.
  unfold enumerate.
  set_unfold.
  setoid_rewrite lookup_unfold.
  hauto l:on simp+:eexists simp+:list_saturate.
Qed.

Section FilterMap.
  Context {A B : Type}.
  Variable f : A -> option B.
  Fixpoint list_filter_map (l : list A) :=
    match l with
    | [] => []
    | hd :: tl =>
        match f hd with
        | Some b => b :: (list_filter_map tl)
        | None => list_filter_map tl
        end
    end.

  Lemma list_filter_map_mbind (l : list A) :
    list_filter_map l = a ← l; f a |> option_list.
  Proof using. induction l; hauto lq:on. Qed.
End FilterMap.

(*** List lemmas ***)

Lemma length_one_iff_singleton A (l : list A) :
  length l = 1 <-> exists a, l = [a].
Proof. sauto lq: on rew:off. Qed.


(*** Fmap Unfold ***)
Class FMapUnfold {M : Type → Type} {fm : FMap M}
  {A B} (f : A → B) (ma : M A) (mb : M B) := {fmap_unfold : f <$> ma = mb }.
Global Hint Mode FMapUnfold + + + + + + - : typeclass_instances.

Global Instance fmap_unfold_default `{FMap M} {A B} (f : A → B) (l : M A):
  FMapUnfold f l (f <$> l) | 1000.
Proof. tcclean. reflexivity. Qed.

Global Instance fmap_unfold_list_app {A B} (f : A → B) l l' l2 l2':
  FMapUnfold f l l2 → FMapUnfold f l' l2' →
  FMapUnfold f (app l l') (app l2 l2').
Proof. tcclean. apply fmap_app. Qed.

Lemma list_bind_fmap A B C (l : list A) (f : A → list B) (g : B -> C):
  g <$> (x ← l; f x) = x ← l; g <$> (f x).
Proof.
  induction l. { done. }
  cbn.
  rewrite fmap_unfold.
  rewrite <- IHl.
  reflexivity.
Qed.
Global Instance fmap_unfold_list_mbind {A B C} (f : B → C) (g : A → list B)  l l2:
  (∀ x, FMapUnfold f (g x) (l2 x)) →
  FMapUnfold f (x ← l; g x) (x ← l; l2 x).
Proof. tcclean. apply list_bind_fmap. Qed.

Global Instance fmap_unfold_let_pair {A B C D} (f : C → D) x
  (l : A → B → list C) l2:
  (∀ a b, FMapUnfold f (l a b) (l2 a b)) →
  FMapUnfold f (let '(a, b) := x in l a b) (let '(a, b) := x in l2 a b).
Proof. tcclean. destruct x. done. Qed.


(*** NoDup management ***)

Global Hint Resolve NoDup_nil_2 : nodup.
Global Hint Resolve NoDup_cons_2 : nodup.
Global Hint Rewrite @list.NoDup_cons : nodup.
Global Hint Resolve NoDup_singleton : nodup.


Lemma NoDup_zip_with_l {A B C} (f : A → B → C) l l':
  (∀ x y x' y', f x x' = f y y' → x = y) → NoDup l →
  NoDup (zip_with f l l').
Proof.
  intros Hinj HND.
  generalize dependent l'.
  induction l;
    destruct l';
    hauto l:on db:nodup simp+:list_saturate simp+:set_unfold.
Qed.

Lemma NoDup_zip_with_r {A B C} (f : A → B → C) l l':
  (∀ x y x' y', f x x' = f y y' → x' = y') → NoDup l' →
  NoDup (zip_with f l l').
Proof.
  intros Hinj HND.
  generalize dependent l.
  induction l';
    destruct l;
    hauto l:on db:nodup simp+:list_saturate simp+:set_unfold.
Qed.

Lemma NoDup_zip_l {A B} (l : list A) (l' : list B):
  NoDup l → NoDup (zip l l').
Proof. intro. apply NoDup_zip_with_l; naive_solver. Qed.

Lemma NoDup_zip_r {A B} (l : list A) (l' : list B):
  NoDup l' → NoDup (zip l l').
Proof. intro. apply NoDup_zip_with_r; naive_solver. Qed.

Lemma NoDup_enumerate A (l : list A) : NoDup (enumerate l).
Proof.
  unfold enumerate.
  apply NoDup_zip_l.
  apply NoDup_seq.
Qed.
Global Hint Resolve NoDup_enumerate : nodup.
