(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
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

From stdpp Require Export gmap.
From stdpp Require Export fin_maps.
From stdpp Require Import pretty.

Require Import Strings.String.

Require Import Options.
Require Import CBase.
Require Import CBool.
Require Import COption.
Require Import CInduction.
Require Import CDestruct.

(** This file provide utilities to deal with stdpp maps.

    In particular it provide a way of automatically unfolding a
    lookup accross various map operations *)


(** * Map utilities ***)

Section MapRestrict.
  Context `{Empty M, Insert K A M, MapFold K A M}.
  Context `{ElemOf K C}.
  Context `{∀ (k : K) (s : C), Decision (k ∈ s)}.

  Definition map_restrict (m : M) (s : C) : M:=
    filter (λ '(k, _), k ∈ s) m.

  (* TODO lemmas *)
End MapRestrict.

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

Global Instance lookup_unfold_difference `{FinMap K M} A
  (m1 m2 : M A) (o o' : option A) (k : K) :
  LookupUnfold k m1 o ->
  LookupUnfold k m2 o' ->
  LookupUnfold k (m1 ∖ m2) (if o' is Some _ then None else o).
Proof. tcclean. apply lookup_difference. Qed.

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

(** Use [LookupUnfold] with [EqSomeUnfold] and [EqNoneUnfold] *)
Module LookupUnfoldEqOpt.
  #[export] Instance lookup_unfold_eq_some {K A M : Type} {lk : Lookup K A M}
    (k : K) (m : M) (oa : option A) (a : A) P :
  LookupUnfold k m oa →
  Unconvertible _ (m !! k) oa →
  EqSomeUnfold oa a P →
  EqSomeUnfold (m !! k) a P.
  Proof. by tcclean. Qed.

  #[export] Instance lookup_unfold_eq_none {K A M : Type} {lk : Lookup K A M}
    (k : K) (m : M) (oa : option A) P :
    LookupUnfold k m oa →
    Unconvertible _ (m !! k) oa →
    EqNoneUnfold oa P →
    EqNoneUnfold (m !! k) P.
  Proof. by tcclean. Qed.
End LookupUnfoldEqOpt.



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
#[global] Typeclasses Transparent delete.
#[global] Typeclasses Transparent map_delete.

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
Proof. eapply (map_fold_weak_ind (flip P)). Qed.

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


(** * DMap : Dependant map *)


Section DMap.
  Context {K : Type}.
  Context {K_eq_dec : EqDecision K}.
  Context {K_countable : Countable K}.
  Context {F : K → Type}.
  Context {ctrans_F : CTrans F}.
  Context {ctrans_F_simpl : CTransSimpl F}.

  Definition gmap_is_dmap (g : gmap K (sigT F)):=
    ∀ k f, g !! k = Some f → f.T1 = k.

  (* TODO should I hide dmap_wf in a bool like bv? *)
  Record dmap := DMap
    {dmap_car : gmap K (sigT F); dmap_wf : gmap_is_dmap dmap_car}.

  (** ** DMap methods *)

  #[export] Program Instance dmap_empty : Empty dmap := DMap ∅ _.
  Next Obligation.
    unfold gmap_is_dmap.
    setoid_rewrite lookup_unfold.
    cdestruct |- **.
  Qed.

  Definition dmap_lookup (k : K) (m : dmap) : option (F k) :=
    match inspect ((dmap_car m) !! k) with
    | Some f eq:e => Some (ctrans (dmap_wf m k f e) f.T2)
    | None eq:_ => None
    end.
  #[global] Arguments dmap_lookup : simpl never.
  Notation "m !d! k" := (dmap_lookup k m) (at level 20).

  Program Definition dmap_insert (k : K) (f : F k) (m : dmap) :=
    DMap (insert k (existT k f) (dmap_car m)) _.
  Next Obligation.
    unfold gmap_is_dmap.
    setoid_rewrite lookup_unfold.
    cdestruct |- *** # CDestrMatch.
    naive_solver ## dmap_wf.
  Qed.

  Program Definition dmap_delete (k : K) (m : dmap) :=
    DMap (delete k (dmap_car m)) _.
  Next Obligation.
    unfold gmap_is_dmap.
    setoid_rewrite lookup_delete_Some.
    cdestruct |- *** # CDestrMatch.
    naive_solver ## dmap_wf.
  Qed.

  Definition dmap_singleton k f := dmap_insert k f ∅.

  Definition dmap_alter (k : K) (f : F k → F k) (m : dmap) :=
    match dmap_lookup k m with
    | Some fk => dmap_insert k (f fk) m
    | None => m
    end.

  Definition dmap_partial_alter (k : K) (f : option (F k) → option (F k))
    (m : dmap) :=
    match f (dmap_lookup k m) with
    | Some fk => dmap_insert k fk m
    | None => dmap_delete k m
    end.

  #[export] Instance dmap_dom : Dom dmap (gset K) := λ m, dom (dmap_car m).


  (** ** DMap lemmas *)
  Lemma dmap_eq_car m m': dmap_car m = dmap_car m' → m = m'.
  Proof.
    intro H.
    destruct m, m'.
    cbn in *.
    subst.
    f_equal.
    apply proof_irrelevance.
  Qed.

  Lemma dmap_eq m m': (∀ k : K, m !d! k = m' !d! k) → m = m'.
  Proof using ctrans_F_simpl.
    intro H.
    apply dmap_eq_car.
    apply map_eq.
    intros i.
    specialize (H i).
    unfold dmap_lookup in H.
    cdestruct H |- *** # CDestrMatch # CDestrSplitGoal # CDestrEqOpt.
  Qed.

  Lemma dmap_lookup_empty k : ∅ !d! k = None.
  Proof. reflexivity. Qed.

  Import LookupUnfoldEqOpt.

  Lemma dmap_lookup_insert m k v :
    dmap_insert k v m !d! k = Some v.
  Proof using ctrans_F_simpl.
    unfold dmap_lookup, dmap_insert.
    cdestruct |- *** # CDestrMatch # CDestrEqOpt.
  Qed.

  Lemma dmap_lookup_insert_ne m k k' v :
    k ≠ k' →
    dmap_insert k v m !d! k' = m !d! k'.
  Proof using ctrans_F_simpl.
    unfold dmap_lookup, dmap_insert.
    cdestruct |- *** # CDestrMatch # CDestrEqOpt.
  Qed.

  Lemma dmap_lookup_insert_case m k k' v :
    dmap_insert k v m !d! k' = if decide (k = k') is left e then Some (ctrans e v) else m !d! k'.
  Proof using ctrans_F_simpl.
    cdestruct k' |- *** # CDestrMatch.
    all: rewrite dmap_lookup_insert || rewrite dmap_lookup_insert_ne.
    all: done.
  Qed.

  Lemma dmap_lookup_delete m k :
    dmap_delete k m !d! k = None.
  Proof using ctrans_F_simpl.
    unfold dmap_lookup, dmap_delete.
    cdestruct |- *** # CDestrMatch # CDestrEqOpt.
  Qed.

  Lemma dmap_lookup_delete_ne m k k' :
    k ≠ k' →
    dmap_delete k m !d! k' = m !d! k'.
  Proof using ctrans_F_simpl.
    unfold dmap_lookup, dmap_delete.
    cdestruct |- *** # CDestrMatch # CDestrEqOpt.
  Qed.


  Lemma dmap_lookup_partial_alter m k f :
    dmap_partial_alter k f m !d! k = f (m !d! k).
  Proof using ctrans_F_simpl.
    unfold dmap_lookup, dmap_partial_alter, dmap_insert, dmap_delete.
    cdestruct |- *** # CDestrMatch # CDestrEqOpt.
  Qed.

  Lemma dmap_lookup_partial_alter_ne m k k' f :
    k ≠ k' →
    dmap_partial_alter k f m !d! k' = m !d! k'.
  Proof using ctrans_F_simpl.
    unfold dmap_lookup, dmap_partial_alter, dmap_insert, dmap_delete.
    cdestruct |- *** # CDestrMatch # CDestrEqOpt.
  Qed.

  Section DmapFold.
    Context {B} (f : sigT F → B → B) (init : B).
    Definition dmap_fold (m : dmap) : B :=
      map_fold (λ _, f) init m.(dmap_car).

    Context (P : dmap → B → Prop) (Hi : P ∅ init)
      (Hr : ∀ k v m r,
         dmap_lookup k m = None → P m r →
         P (dmap_insert k v m) (f (existT k v) r)).
    Lemma dmap_fold_ind : ∀ m, P m (dmap_fold m).
    Proof using Hi Hr ctrans_F.
      intro m.
      unfold dmap_fold.
      funelim (map_fold _ _ _).
      - enough (∅ = m) as <- by done.
      by apply dmap_eq_car.
      - do 8 deintro. intros k [k' v] mold b Hknew HInd mnew Hmnew.
        assert (k' = k). {
          enough (dmap_car mnew !! k = Some (existT k' v)) as H'' by
              by apply dmap_wf in H''.
          rewrite <- Hmnew.
          cdestruct |- *** # CDestrEqOpt. }
        subst.
        assert (gmap_is_dmap mold) as mold_wf. {
          destruct mnew as [mnew mnew_wf].
          unfold gmap_is_dmap in *.
          intros.
          apply mnew_wf.
          cdestruct mnew,k0 |- *** # CDestrEqOpt #CDestrMatch. }
        assert (mnew = dmap_insert k v (DMap mold mold_wf)). {
          unfold dmap_insert.
          by apply dmap_eq_car.
        }
        subst.
        apply Hr.
        + unfold dmap_lookup. cdestruct |- *** #CDestrMatch.
        + naive_solver.
    Qed.
  End DmapFold.

  #[export] Instance FunctionalElimination_dmap_fold {B} f b :
    FunctionalElimination (dmap_fold f b) _ 3 :=
    dmap_fold_ind (B := B) f b.

  Definition dmap_to_list (d : dmap) : list (sigT F) :=
    dmap_fold (::) [] d.

  Import CDestrUnfoldElemOf.

  #[export] Instance elem_of_dmap_to_list r m : SetUnfoldElemOf r (dmap_to_list m) (m !d! r.T1 = Some r.T2).
  Proof using ctrans_F_simpl.
    constructor.
    unfold dmap_to_list.
    funelim (dmap_fold _ _ _).
    - set_solver.
    - rewrite dmap_lookup_insert_case.
      do 4 deintro.
      cdestruct |- *** #CDestrMatch #CDestrSplitGoal; naive_solver.
  Qed.

  Definition dmap_of_list : list (sigT F) → dmap :=
    foldr (λ '(existT k v), dmap_insert k v) ∅.

  #[export] Instance dmap_filter : Filter (sigT F) dmap := λ P PD,
      dmap_fold (λ '(existT k v) m,
          if decide (P (existT k v)) then dmap_insert k v m else m) ∅.

  Section DMapRestrict.
    Context `{ElemOf K C}.
    Context `{∀ (k : K) (s : C), Decision (k ∈ s)}.
    Definition dmap_restrict (m : dmap) (s : C) : dmap:=
      filter (λ '(existT k _), k ∈ s) m.
  End DMapRestrict.

End DMap.
Arguments dmap _ {_ _} _.
Notation "m !d! k" := (dmap_lookup k m) (at level 20).

Section DMapMap.
  Context {K : Type}.
  Context {K_eq_dec : EqDecision K}.
  Context {K_countable : Countable K}.
  Context {F : K → Type}.
  Context {ctrans_F : CTrans F}.
  Context {ctrans_F_simpl : CTransSimpl F}.
  Context {F' : K → Type}.
  Context {ctrans_F' : CTrans F'}.
  Context {ctrans_F'_simpl : CTransSimpl F'}.

  (** DMap utility functions *)
  Definition dmap_map (f: ∀ k, F k → F' k) (m : dmap K F) : dmap K F' :=
    dmap_fold (λ '(existT k v) res, dmap_insert k (f k v) res) ∅ m.

  Lemma dmap_lookup_map (f: ∀ k, F k → F' k) (m : dmap K F) k :
    (dmap_map f m) !d! k = f k <$> m !d! k.
  Proof using ctrans_F'_simpl ctrans_F_simpl.
    unfold dmap_map.
    funelim (dmap_fold _ _ _).
    - by rewrite ?dmap_lookup_empty.
    - destruct decide subst k k0.
      + by rewrite ?dmap_lookup_insert.
      + by rewrite ?dmap_lookup_insert_ne.
  Qed.
End DMapMap.

(* * Pretty printing maps *)

Fixpoint intercalate (sep : string) (xs : list string) : string :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: xs' => x ++ sep ++ intercalate sep xs'
  end.

Definition pretty_kv {K V : Type} `{Pretty K} `{Pretty V} (kv : K * V) : string :=
  let '(k, v) := kv in (pretty k ++ " ↦ " ++ pretty v)%string.

Section PrettyDMap.
  Context {K : Type}.
  Context {K_eq_dec : EqDecision K}.
  Context {K_countable : Countable K}.
  Context {F : K → Type}.
  Context {ctrans_F : CTrans F}.
  Context {ctrans_F_simpl : CTransSimpl F}.

  Context `{Pretty K}.
  Context `{forall k : K, Pretty (F k)}.

  Definition string_of_dmap (m : dmap K F) : string :=
    let entries := List.map
      (λ '(existT k v), pretty_kv (k, v))
      (dmap_to_list m) in
    "{" ++ intercalate ", " entries ++ "}".

  #[global] Instance pretty_dmap : Pretty (dmap K F) :=
    λ m, string_of_dmap m.

End PrettyDMap.

Section PrettyGMap.
  Context {K A : Type}.
  Context `{EqDecision K, Countable K}.
  Context `{Pretty K}.
  Context `{Pretty A}.

  Definition string_of_gmap (m : gmap K A) : string :=
    let entries := List.map pretty_kv (map_to_list m) in
    "{" ++ intercalate ", " entries ++ "}".

  #[global] Instance pretty_gmap : Pretty (gmap K A) :=
    λ m, string_of_gmap m.

End PrettyGMap.
