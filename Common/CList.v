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

Require Import CBase CBool CMaps CArith.
Require Import Options.
From stdpp Require Import base.
From stdpp Require Export list.
From stdpp Require Import finite.
From stdpp Require Import sets.
From stdpp Require Export listset.

Global Instance proper_list_mbind A B :
  Proper (pointwise_relation A (=) ==> (=@{list A}) ==> (=@{list B})) mbind.
Proof.
  intros x y H ? l ->.
  unfold pointwise_relation in H.
  induction l; hauto q:on.
Qed.

#[global] Instance set_unfold_list_map
  {A B : Type} (f : A → B) (l : list A) (P : A → Prop) (y : B) :
  (∀ x : A, SetUnfoldElemOf x l (P x)) →
  SetUnfoldElemOf y (map f l) (∃ x : A, y = f x ∧ P x) := ltac:(apply set_unfold_list_fmap).

#[global] Instance set_unfold_list_mret {A : Type} x y :
  SetUnfoldElemOf x (mret y : list A) (x = y).
Proof. tcclean. unfold mret, list_ret. set_solver. Qed.


#[export] Instance list_elements {A} : Elements A (list A) := λ x, x.

(** * List simplification *)

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
  x ∈ map f l <-> ∃ y ∈ l, x = f y.
Proof.
  setoid_rewrite elem_of_list_In.
  rewrite in_map_iff.
  firstorder.
Qed.
(* #[global] Hint Rewrite @elem_of_map_iff : list. *)

Lemma forall_elem_of_map {A B} (f : A -> B) (l : list A) (P : B -> Prop) :
  (∀ x ∈ map f l, P x) <-> ∀ y ∈ l, P (f y).
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

#[global] Instance set_unfold_elem_of_imap {A B : Type} (f : nat → A → B)
  (l : list A) (y : B) :
  SetUnfoldElemOf y (imap f l) (∃ i x, y = f i x ∧ l !! i = Some x).
Proof. tcclean. rewrite elem_of_lookup_imap. naive_solver. Qed.

Global Instance set_unfold_elem_of_filter_list A
  `{∀ x : A, Decision (P x)} x (a : list A) Q:
  SetUnfoldElemOf x a Q →
  SetUnfoldElemOf x (filter P a) (P x ∧ Q).
Proof. tcclean. apply elem_of_list_filter. Qed.

Global Instance set_unfold_elem_of_singleton_list {A : Type} (x a : A) :
  SetUnfoldElemOf x [a] (x = a).
Proof. tcclean. set_solver. Qed.


(** * List lookup with different keys *)

Global Instance list_lookupPos {A} : Lookup positive A (list A) | 100 :=
  fun p l => l !! (Pos.to_nat p).

Global Instance list_lookupN {A} : Lookup N A (list A) | 100 :=
  fun n l => l !! (N.to_nat n).

Global Instance list_lookupZ {A} : Lookup Z A (list A) | 100 :=
  fun z l =>
    match z with
    | Zpos p => l !! p
    | Z0 => head l
    | Zneg _ => None
    end.


(** * List lookup unfold *)

Global Instance list_lookup_nil {A} (i : nat) : LookupUnfold i (@nil A) None.
Proof. tcclean. apply lookup_nil. Qed.

Global Instance list_lookup_cons {A} (i : nat) (x : A) l o :
  TCFastDone (0 < i) → LookupUnfold (pred i) l o →  LookupUnfold i (x :: l) o.
Proof. tcclean. apply lookup_cons_ne_0. lia. Qed.

(** * List boolean unfolding *)

Global Instance bool_unfold_existsb A (f : A -> bool) (l : list A) (P : A -> Prop) :
  (forall a, BoolUnfold (f a) (P a)) ->
  BoolUnfold (existsb f l) (∃ x ∈ l, P x).
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
  BoolUnfold (forallb f l) (∀ x ∈ l, P x).
Proof.
  tcclean.
  setoid_rewrite true_is_true.
  unfold is_true.
  rewrite forallb_forall.
  setoid_rewrite elem_of_list_In.
  reflexivity.
Qed.

(** * Decisions *)

Global Existing Instance list_forall_dec.
Global Existing Instance list_exist_dec.

(** * List cartesian product *)

Lemma list_cprod_spec A B a b (la : list A) (lb : list B):
  (a,b) ∈ la × lb ↔ a ∈ la ∧ b ∈ lb.
Proof.
  setoid_rewrite elem_of_list_In.
  unfold cprod, list_cprod.
  apply in_prod_iff.
Qed.

#[export] Instance set_unfold_elem_of_list_cprod A B x (la : list A) (lb : list B) Pa Pb:
  SetUnfoldElemOf x.1 la Pa →
  SetUnfoldElemOf x.2 lb Pb →
  SetUnfoldElemOf x (la × lb) (Pa ∧ Pb).
Proof. tcclean. destruct x. apply list_cprod_spec. Qed.

(** * List utility functions *)

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

Global Instance set_elem_of_seq x n l:
  SetUnfoldElemOf x (seq n l) (n ≤ x < n + l).
Proof. tcclean. apply elem_of_seq. Qed.


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

(** ** seqN *)

Definition seqN (s l : N) := seq (N.to_nat s) (N.to_nat l) |$> N.of_nat.

Global Instance set_elem_of_seqN x n l:
  SetUnfoldElemOf x (seqN n l) (n ≤ x < n + l)%N.
Proof.
  tcclean. unfold seqN. set_unfold. split.
  - intros []. lia.
  - intros. exists (N.to_nat x). lia.
Qed.

(** * List lemmas *)

Lemma length_one_iff_singleton A (l : list A) :
  length l = 1 <-> exists a, l = [a].
Proof. sauto lq: on rew:off. Qed.

(** ** Forall2 Lemmas *)

Lemma Forall2_map_l {A B C} (f : A → B) (P : B → C → Prop) l l' :
  Forall2 P (map f l) l' ↔ Forall2 (λ x y, P (f x) y) l l'.
Proof. revert l'; induction l; intro l'; sauto lq:on. Qed.

Lemma Forall2_map_r {A B C} (f : B → C) (P : A → C → Prop) l l' :
  Forall2 P l (map f l') ↔ Forall2 (λ x y, P x (f y)) l l'.
Proof. revert l; induction l'; intro l; sauto lq:on. Qed.

Lemma Forall2_diag A (P : A → A → Prop) l:
  Forall2 P l l ↔ ∀ x ∈ l, P x x.
Proof. induction l; sauto lq:on. Qed.

(** ** fold_left invariant proofs *)

(** Proofs along fold_left using an invariant.
    The invariant takes as a parameter the value produced so far and the
    remaining elements of the list. *)
Lemma fold_left_inv {C B} (I : C → list B → Prop) (f : C → B → C)
    (l : list B) (i : C) :
  (I i l)
  → (∀ (a : C) (x : B) (tl : list B), x ∈ l → I a (x :: tl) → I (f a x) tl)
  → I (fold_left f l i) [].
  generalize dependent i.
  induction l; sauto lq:on.
Qed.

(** Tries to find a fold_left in the goal and pose the proofs of the
[fold_left_inv] on that one *)
Tactic Notation "fold_left_inv_pose" uconstr(I) "as" simple_intropattern(pat) :=
  match goal with
  | |- context [fold_left ?f ?l ?i] =>
      opose proof (fold_left_inv I f l i _ _) as pat
  end.
Tactic Notation "fold_left_inv_pose" uconstr(I) :=
  let H := fresh "H" in fold_left_inv_pose I as H.

(** The same as [fold_left_inv], but add the assumption that there is no
    duplicate and gives the information that at each loop, the element being
    processes is not in the remaining tail of the list *)
Lemma fold_left_inv_ND {C B} (I : C → list B → Prop) (f : C → B → C)
    (l : list B) (i : C) :
  NoDup l
  → (I i l)
  → (∀ (a : C) (x : B) (t : list B), x ∈ l → x ∉ t → I a (x :: t) → I (f a x) t)
  → I (fold_left f l i) [].
  generalize dependent i.
  induction l; sauto lq:on.
Qed.

(** Same as [fold_left_inv_pose] but for [fold_left_inv_ND] *)
Tactic Notation "fold_left_inv_ND_pose" uconstr(I) "as" simple_intropattern(pat) :=
  match goal with
  | |- context [fold_left ?f ?l ?i] =>
      opose proof (fold_left_inv_ND I f l i _ _ _) as pat
  end.
Tactic Notation "fold_left_inv_ND_pose" uconstr(I) :=
  let H := fresh "H" in fold_left_inv_ND_pose I as H.


(** * Fmap Unfold *)

(** Typeclass for pushing an fmapped function into the structure. For now only
    on lists *)
Class FMapUnfold {M : Type → Type} {fm : FMap M}
  {A B} (f : A → B) (ma : M A) (mb : M B) := {fmap_unfold : f <$> ma = mb }.
Global Hint Mode FMapUnfold + + + + + + - : typeclass_instances.

Global Instance fmap_unfold_default `{FMap M} {A B} (f : A → B) (l : M A):
  FMapUnfold f l (f <$> l) | 1000.
Proof. tcclean. reflexivity. Qed.

Global Instance fmap_unfold_list_nil {A B} (f : A → B) :
  FMapUnfold f [] [].
Proof. by tcclean. Qed.

Global Instance fmap_unfold_list_cons {A B} (f : A → B) h t t2:
  FMapUnfold f t t2 → FMapUnfold f (h :: t) (f h :: t2).
Proof. by tcclean. Qed.

Global Instance fmap_unfold_list_id {A} (l : list A):
  FMapUnfold id l l | 10.
Proof. tcclean. apply list_fmap_id. Qed.

Global Instance fmap_unfold_list_id_simpl {A} (f : A → A) (l : list A):
  TCSimpl f (λ x, x) → FMapUnfold f l l | 20.
Proof. tcclean. apply list_fmap_id. Qed.

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

(* TODO do a generic unfolding over match like set unfold *)
Global Instance fmap_unfold_let_pair {A B C D} (f : C → D) x
  (l : A → B → list C) l2:
  (∀ a b, FMapUnfold f (l a b) (l2 a b)) →
  FMapUnfold f (let '(a, b) := x in l a b) (let '(a, b) := x in l2 a b).
Proof. tcclean. by destruct x. Qed.

(** Option to enable unfolding a fmap into a fmap *)
Class FMapUnfoldFmap := {}.

Global Instance fmap_unfold_list_fmap_id_simpl `{FMapUnfoldFmap} {A B}
    (f : B → A) (g : A → B) (l : list A):
  TCSimpl (λ x, f (g x)) (λ x, x) →
  FMapUnfold f (g <$> l) l | 10 .
Proof. tcclean. rewrite <- list_fmap_compose. hauto l:on use:list_fmap_id. Qed.

Global Instance fmap_unfold_list_fmap `{FMapUnfoldFmap} {A B C}
    (f : B → C) (g : A → B) (l : list A):
  FMapUnfold f (g <$> l) ((λ x, f (g x)) <$> l) | 20.
Proof. tcclean. by rewrite <- list_fmap_compose. Qed.


(** * NoDup management *)

Create HintDb nodup discriminated.

Global Hint Resolve NoDup_nil_2 : nodup.
Global Hint Resolve NoDup_singleton : nodup.
Global Hint Resolve NoDup_seq : nodup.

#[global] Hint Extern 10 (NoDup (_ :: _)) =>
  apply NoDup_cons_2; [shelve | ..] : nodup.
#[global] Hint Extern 10 (NoDup (_ ≫= _)) =>
  apply NoDup_bind; [shelve | ..] : nodup.
#[global] Hint Extern 10 (NoDup (fmap _ _)) => apply NoDup_fmap_2 : nodup.
#[global] Hint Extern 20 (NoDup (fmap _ _)) =>
  apply NoDup_fmap_2_strong; [shelve | ..] : nodup.
#[global] Hint Extern 20 (NoDup (match ?x with _ => _ end)) =>
  destruct x : nodup.
#[global] Hint Extern 1000 (NoDup _) => shelve : nodup.

#[global] Lemma NoDup_mret {T} (x : T) : NoDup (mret x).
Proof. apply NoDup_singleton. Qed.

#[global] Hint Resolve NoDup_mret : nodup.

Ltac solve_NoDup := unshelve (typeclasses eauto with nodup).

Lemma NoDup_seqN n l : NoDup (seqN n l).
Proof. unfold seqN. solve_NoDup. lia. Qed.
#[global] Hint Resolve NoDup_seqN : nodup.


Lemma NoDup_zip_with_l {A B C} (f : A → B → C) l l':
  (∀ x y x' y', f x x' = f y y' → x = y) → NoDup l →
  NoDup (zip_with f l l').
Proof.
  intros Hinj HND.
  generalize dependent l'.
  induction l.
  all: destruct l'.
  all: try rewrite NoDup_cons in *.
  all: hauto l:on simp+:solve_NoDup simp+:list_saturate simp+:set_unfold.
Qed.

Lemma NoDup_zip_with_r {A B C} (f : A → B → C) l l':
  (∀ x y x' y', f x x' = f y y' → x' = y') → NoDup l' →
  NoDup (zip_with f l l').
Proof.
  intros Hinj HND.
  generalize dependent l.
  induction l'.
  all: destruct l.
  all: try rewrite NoDup_cons in *.
  all: hauto l:on simp+:solve_NoDup simp+:list_saturate simp+:set_unfold.
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
  solve_NoDup.
Qed.
Global Hint Resolve NoDup_enumerate : nodup.




(** * InT

   When doing manual induction rules on inductives that recurse through list,
   such as [Inductive TreeList A := Node (a : A) (subtrees : list (TreeList A))]
   then you what the inductive property to look like
   [(∀x, x ∈ l → P x) → P (Node a l)]. However if you want to recurse on
   [TreeList] in [Type], you need [x ∈ l] to be in [Type], hence [InT]. *)

(** [InT a l] is a proof that a is in l in a way that can be used in a regular
    computable program. A program can receive a value of Type [InT] and branch
    on whether the element is the head of the list or is in the tail to do a
    computation. *)
Inductive InT {A} (a : A) : list A → Type :=
| InT_here l : InT a (a :: l)
| InT_further y l : InT a l → InT a (y :: l).

(** Trivially [InT x l] implies [x ∈ l], but the reverse is not true. [x] could
    be in multiple places in [l], in which case an irrelevant proof of [x ∈ l]
    cannot be used to construct a value of type [InT x l] as multiple values are
    possible *)
Lemma InT_elem_of {A} (x : A) l : InT x l → x ∈ l.
Proof. intro H. induction H; sauto lq:on. Qed.
#[global] Hint Resolve InT_elem_of : list.


(** When working on type that recurse trough list, we need to manipulate [InT] as
    part of the proof of [EqDecision] *)
#[global] Hint Constructors InT : eqdec.

(** More precise version than [list_eq_dec] *)
Lemma list_InT_eq_dec A (l l' : list A) :
  (∀x y, InT x l → InT y l' → Decision (x = y)) → Decision (l = l').
Proof. revert l'. induction l; destruct l'; auto with eqdec. Defined.
#[global] Hint Extern 8 (Decision (?a =@{list _} ?b)) =>
  is_var a; is_var b; apply list_InT_eq_dec : eqdec.

(** Additional helper lemmas for [EqDecision] on types that recurse to themselve
    as a member of a list of pair *)
Lemma InT_fmap_fst A B a b (l : list (A * B)) : InT (a, b) l → InT a l.*1.
Proof. intro H. induction H; auto with eqdec. Defined.
#[global] Hint Resolve InT_fmap_fst : eqdec.
Lemma InT_fmap_snd A B a b (l : list (A * B)) : InT (a, b) l → InT b l.*2.
Proof. intro H. induction H; auto with eqdec. Defined.
#[global] Hint Resolve InT_fmap_snd : eqdec.
