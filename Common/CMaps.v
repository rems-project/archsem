(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2022                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aahrus Univeristy                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aahrus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, Univeristy of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, Univeristy of Cambridge                                 *)
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
(*  1. Redistributions of source code must retain the above copyright         *)
(*     notice, this list of conditions and the following disclaimer.          *)
(*                                                                            *)
(*  2. Redistributions in binary form must reproduce the above copyright      *)
(*     notice, this list of conditions and the following disclaimer in the    *)
(*     documentation and/or other materials provided with the distribution.   *)
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

From stdpp Require Export gmap.
From stdpp Require Export fin_maps.

Require Import CBase.
Require Import Options.
Require Import CBool.
Require Import CInduction.

(** This file provide utilities to deal with stdpp maps.

    In particular it provide a way of automatically unfolding a
    lookup accross various map operations *)


(** * Lookup Unfold ***)

Class LookupUnfold {K A M : Type} {lk : Lookup K A M}
  (k : K) (m : M) (oa : option A) :=
  {lookup_unfold : m !! k = oa }.
Global Hint Mode LookupUnfold + + + + + + - : typeclass_instances.

Global Instance lookup_unfold_default `{Lookup K A M} (k : K) (m : M) :
  LookupUnfold k m (m !! k) | 1000.
Proof. done. Qed.

Global Instance lookup_unfold_empty `{FinMap K M} A (k : K) :
  LookupUnfold k (∅ : M A) (None : option A).
Proof. sfirstorder. Qed.

Global Instance lookup_unfold_partial_alter_same `{FinMap K M}
    A f (m : M A) o (k : K) :
  LookupUnfold k m o ->
  LookupUnfold k (partial_alter f k m) (f o) | 10.
Proof. tcclean. sfirstorder. Qed.

Global Instance lookup_unfold_partial_alter_different
  `{FinMap K M} A f (m : M A) o (k k' : K):
  TCFastDone (k ≠ k') ->
  LookupUnfold k m o ->
  LookupUnfold k (partial_alter f k' m) o | 15.
Proof. tcclean. sauto. Qed.

Global Instance lookup_unfold_partial_alter `{FinMap K M} A f
    (m : M A) o (k k' : K) :
  LookupUnfold k m o ->
  LookupUnfold k (partial_alter f k' m) (if k =? k' then f o else o) | 20.
Proof. tcclean. sauto. Qed.

Global Instance lookup_unfold_fmap `{FinMap K M} A B
    (f : A -> B) (m : M A) (o : option A) (k : K) :
  LookupUnfold k m o ->
  LookupUnfold k (f <$> m) (f <$> o).
Proof. tcclean. sfirstorder. Qed.

Global Instance lookup_unfold_omap `{FinMap K M} A B
    (f : A -> option B) (m : M A) (o : option A) (k : K) :
  LookupUnfold k m o ->
  LookupUnfold k (omap f m) (o ≫= f).
Proof. tcclean. sfirstorder. Qed.

Global Instance lookup_unfold_merge `{FinMap K M} A B C
  (f : option A -> option B -> option C) (ma : M A) (mb : M B)
  (oa : option A) (ob : option B) (k : K) :
  LookupUnfold k ma oa -> LookupUnfold k mb ob ->
  LookupUnfold k (merge f ma mb) (diag_None f oa ob) | 20.
Proof. tcclean. sfirstorder. Qed.

Global Instance lookup_unfold_merge_simpl `{FinMap K M} A B C
  (f : option A -> option B -> option C) (ma : M A) (mb : M B)
  (oa : option A) (ob : option B) (k : K) :
  TCSimpl (f None None) None -> LookupUnfold k ma oa -> LookupUnfold k mb ob ->
  LookupUnfold k (merge f ma mb) (f oa ob) | 10.
Proof.
  tcclean.
  rewrite lookup_unfold.
  hauto unfold:diag_None lq:on.
Qed.



(** * Lookup Total Unfold ***)

Class LookupTotalUnfold {K A M : Type} {lk : LookupTotal K A M}
  (k : K) (m : M) (a : A) := {lookup_total_unfold : m !!! k = a }.
Global Hint Mode LookupTotalUnfold + + + + + + - : typeclass_instances.

Lemma lookup_total_lookup `{FinMap K M} `{Inhabited A} (m : M A) (k : K) :
  m !!! k = default inhabitant (m !! k).
Proof. sfirstorder. Qed.

Lemma lookup_lookup_total `{FinMap K M} `{Inhabited A} (m : M A) (k : K) g :
  m !! k = Some g -> m !! k = Some (m !!! k).
Proof. rewrite lookup_total_lookup. hauto lq:on. Qed.

Lemma lookup_lookup_total' `{FinMap K M} `{Inhabited A} (m : M A) (k : K) g :
  m !! k = Some g → g = m !!! k.
Proof. rewrite lookup_total_lookup. hauto lq:on. Qed.

(** When there is a [m !! k = Some v] in the context, where [v] is a variable,
    this will replace [v] by [m !!! k] if possible. *)
Ltac lookup_lookup_total :=
  match goal with
  | H : ?m !! ?k = Some ?v |- _ =>
      is_var v;
      let H2 := fresh "H" in
      pose proof H as H2;
      apply lookup_lookup_total' in H2;
      subst v
  end.

Global Instance lookup_total_unfold_default
  `{LookupTotal K A M} (k : K) (m : M) :
  LookupTotalUnfold k m (m !!! k) | 1000.
Proof. done. Qed.

Global Instance lookup_total_unfold_empty `{FinMap K M} `{Inhabited A} (k : K) :
  LookupTotalUnfold k (∅ : M A) inhabitant | 20.
Proof.
  tcclean.
  rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  naive_solver.
Qed.

Global Instance lookup_total_unfold_empty_empty
  `{FinMap K M} `{Empty A} (k : K) :
  LookupTotalUnfold k (∅ : M A) ∅ | 10.
Proof.
  tcclean.
  rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  naive_solver.
Qed.

(* TODO remove and instances in LookupUnfold *)
#[global] Typeclasses Transparent map_singleton.
#[global] Typeclasses Transparent singletonM.
#[global] Typeclasses Transparent insert.
#[global] Typeclasses Transparent map_insert.

Global Instance lookup_total_unfold_singleton_same
  `{FinMap K M} `{Empty A} (k : K) (a : A) :
  LookupTotalUnfold k ({[k := a]} : M A) a | 10.
Proof.
  tcclean.
  rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  naive_solver.
Qed.

Global Instance lookup_total_unfold_singleton_different
  `{FinMap K M} `{Empty A} (k k' : K) (a : A) :
  TCFastDone (k ≠ k') ->
  LookupTotalUnfold k ({[k' := a]} : M A) ∅ | 15.
Proof.
  tcclean.
  rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  hauto.
Qed.

Global Instance lookup_total_unfold_singleton
  `{FinMap K M} `{Empty A} (k k' : K) (a : A) :
  LookupTotalUnfold k ({[k' := a]} : M A) (if k =? k' then a else ∅) | 20.
Proof.
  tcclean.
  rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  hauto.
Qed.

Global Instance lookup_total_unfold_insert_same
  `{FinMap K M} `{Empty A} (k : K) (a : A) (m : M A) :
  LookupTotalUnfold k (<[k := a]> m) a | 10.
Proof.
  tcclean.
  rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  naive_solver.
Qed.

Global Instance lookup_total_unfold_insert_different
  `{FinMap K M} `{Empty A} (k k' : K) (a a' : A) (m : M A) :
  TCFastDone (k ≠ k') ->
  LookupTotalUnfold k m a' ->
  LookupTotalUnfold k (<[k' := a]> m) a' | 15.
Proof.
  tcclean.
  rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  hauto.
Qed.

Global Instance lookup_total_unfold_insert
  `{FinMap K M} `{Empty A} (k k' : K) (a a' : A) (m : M A) :
  LookupTotalUnfold k m a' ->
  LookupTotalUnfold k (<[k' := a]> m) (if k =? k' then a else a') | 20.
Proof.
  tcclean.
  rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  hauto.
Qed.

(** * Map related Set unfoldings ***)

Global Instance set_unfold_elem_of_map_to_list `{Countable A} B (x : A * B)
    (m : gmap A B) me :
  LookupUnfold x.1 m me →
  SetUnfoldElemOf x (map_to_list m) (me = Some x.2).
Proof. tcclean. destruct x. apply elem_of_map_to_list. Qed.


(** * Map induction ***)

Program Global Instance map_cind `{FinMap K M} A (m : M A) (P : M A -> Prop) :
  CInduction m (P m) :=
  {|
    induction_requirement :=
      (P ∅) /\ (forall i x m, m !! i = None -> P m -> P (<[i := x]>m))
  |}.
Solve All Obligations with intros; apply map_ind; naive_solver.

(* See CSets induction for set_fold for explanation of funelim instances *)
Lemma map_fold_ind' `{FinMap K M} {A B}
  (f : K → A → B → B) (b : B) (P : M A → B → Prop) :
  P ∅ b → (∀ i x m r, m !! i = None → P m r → P (<[i:=x]> m) (f i x r)) →
  ∀ m, P m (map_fold f b m).
Proof. eapply (map_fold_ind (flip P)). Qed.

(* Same Warning as set_unfold: FinMap needs to be resolvable from global context
or section variable, not local variable *)
#[global] Instance FunctionalElimination_map_fold
  `{FinMap K M} {A B} f b :
  FunctionalElimination (@map_fold K A (M A) _ B f b) _ 3 :=
  map_fold_ind' (K := K) (M := M) (A:= A) (B := B) f b.


(** * FinMap reduce ***)

Section FinMapReduce.
  Context `{FM: FinMap K M}.
  Context {A B : Type}.

  (** This take a mapping function, an operator, and a neutral (or starting)
      element and then reduce using the operator after applying a conversion
      function to the key and value *)
  Definition finmap_reduce  (f : K → A → B)
    (op : B → B → B) : B → M A → B :=
    map_fold (λ (k : K) (v : A) (acc : B), op acc (f k v)).

  Context `{SS : SemiSet X B}.

  (** Reduce each element of a map to a set, and then union all the sets *)
  Definition finmap_reduce_union (f : K → A → B)
    : M A → B := finmap_reduce f (∪) ∅.

  Global Instance set_unfold_elem_of_finmap_reduce_union
    (m : M A) (f : K → A → B) (x : X) P:
    (∀ k v, SetUnfoldElemOf x (f k v) (P k v)) →
    SetUnfoldElemOf x (finmap_reduce_union f m) (∃ k v, m !! k = Some v ∧ P k v).
  Proof using FM SS.
    tcclean. clear dependent P.
    unfold finmap_reduce_union, finmap_reduce.
    funelim (map_fold _ _ _).
    - setoid_rewrite lookup_unfold.
      set_solver.
    - do 7 deintro. intros i v m r Hn Hxr.
      set_unfold.
      setoid_rewrite Hxr; clear Hxr.
      split.
      + intros [(k&v'&?) | ?].
        * exists k.
          exists v'.
          rewrite lookup_unfold.
          hauto l:on.
        * sfirstorder.
      + hauto lq:on rew:off simp+:rewrite lookup_unfold in *.
  Qed.
End FinMapReduce.


(** * FinMap setter *)

#[global] Instance Setter_finmap `{FinMap K M} {A} (k : K) :
    @Setter (M A) _ (lookup k) := λ f, partial_alter f k.

#[global] Program Instance Setter_finmap_wf `{FinMap K M} {A} (k : K) :
  @SetterWf (M A) _ (lookup k) :=
  { set_wf := Setter_finmap k }.
Next Obligation.
  sauto lq:on rew:off.
Qed.
Next Obligation.
  intros.
  apply map_eq.
  intro i.
  destruct decide subst i k; sauto.
Qed.
