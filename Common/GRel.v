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

(** This file define a relation using a gset from stdpp that is entirely
    computable and whose standard relational operators are also computable. The
    type is [grel A]

    All relations in this file are finite, which means that any notions in this
    file related to reflexivity require the type on which we are doing relations
    to also be finite. For that reason, this library prefer to define a
    transitive closure (r⁺) but no reflexive transitive closure. If the type if
    finite (implement the Finite typeclass from stdpp), there is a reflexive
    closure (r?) and thus the reflexive transitive closure can be obtained with:
    r?⁺

    Since relation are just gset of pair, the usual && and | operation on
    relation can just be obtained with the standard ∪ and ∩.

    Sequence is obtained with r⨾r' and a set s is converted to a diagonal
    relation with ⦗s⦘. *)

Require Import Wellfounded.

Require Import Options.
From stdpp Require Export option fin_maps.
Require Import Common.

(* For some reason some typeclass instance defined in CSets is missing even if
   Common export CSets *)
Require Import CSets.

Import SetUnfoldPair.

(** * Maps of sets utilities ***)

(** Union of set options, that merge two options, using the union in case of two
Some. Useful for map of set merging *)
Definition option_union `{Union A} (ov1 ov2 : option A) : option A :=
  match ov1 with
  | None => ov2
  | Some v1 =>
      match ov2 with
      | None => Some v1
      | Some v2 => Some (v1 ∪ v2)
      end
  end.

Infix "∪ₒ" := option_union (at level 50, left associativity) : stdpp_scope.
Notation "(∪ₒ)" := option_union (only parsing) : stdpp_scope.
Notation "( x ∪ₒ.)" := (option_union x) (only parsing) : stdpp_scope.
Notation "(.∪ₒ x )" := (λ y, option_union y x) (only parsing) : stdpp_scope.

Lemma option_union_None `{Union A} (ov1 ov2 : option A) :
  ov1 ∪ₒ ov2 = None ↔ ov1 = None ∧ ov2 = None.
Proof. destruct ov1; destruct ov2; sfirstorder. Qed.


(** Define a pointwise union of map of sets. If both maps contains a set for a given key, then the
    result contains the unions of the sets for that key. *)
Definition pointwise_union `{FinMap K M} `{Union A} : M A -> M A -> M A :=
  merge (∪ₒ).

Infix "∪ₘ" := pointwise_union (at level 50, left associativity) : stdpp_scope.
Notation "(∪ₘ)" := pointwise_union (only parsing) : stdpp_scope.
Notation "( x ∪ₘ.)" := (pointwise_union x) (only parsing) : stdpp_scope.
Notation "(.∪ₘ x )" := (λ y, pointwise_union y x) (only parsing) : stdpp_scope.

Global Instance lookup_unfold_pointwise_union `{FinMap K M} `{Union A}
   (k : K) (m1 m2 : M A) (o1 o2 : option A) :
  LookupUnfold k m1 o1 -> LookupUnfold k m2 o2 ->
  LookupUnfold k (m1 ∪ₘ m2) (o1 ∪ₒ o2).
Proof. tcclean. unfold pointwise_union. by rewrite lookup_unfold. Qed.

Global Instance lookup_total_unfold_pointwise_union `{FinMap K M} `{SemiSet A C}
  {lei : LeibnizEquiv C} (k : K) (m1 m2 : M C) (s1 s2 : C) :
  LookupTotalUnfold k m1 s1 -> LookupTotalUnfold k m2 s2 ->
  LookupTotalUnfold k (m1 ∪ₘ m2) (s1 ∪ s2).
Proof.
  tcclean.
  setoid_rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  cbn.
  unfold option_union.
  case_splitting; set_solver.
Qed.

(** Import this module to make set_unfold use the LookupTotalUnfold typeclass
    when unfolding a set that is the result of a total lookup. *)
Module SetUnfoldLookupTotal.
  #[export] Instance set_unfold_lookup_total `{ElemOf A C} `{LookupTotal K C M}
    x a (m : M) (s : C) Q:
    LookupTotalUnfold a m s ->
    Unconvertible C (m !!! a) s ->
    SetUnfoldElemOf x s Q ->
    SetUnfoldElemOf x (m !!! a) Q.
  Proof. tcclean. reflexivity. Qed.

End SetUnfoldLookupTotal.

(* This is not automatically imported by any file importing this file but might
be useful *)
Import SetUnfoldLookupTotal.



(** * Grels ***)

Section GRel.
  Context {A : Type}.
  Context {eqA : EqDecision A}.
  Context {countA : Countable A}.

  Definition grel := gset (A * A).
  #[global] Typeclasses Transparent grel.

  Definition grel_to_relation (r : grel) : relation A := fun x y => (x, y) ∈ r.

  Definition grel_map := gmap A (gset A).
  #[global] Typeclasses Transparent grel_map.

  Definition grel_to_map (r : grel) : grel_map :=
    set_fold (fun '(e1, e2) res => res ∪ₘ {[e1 := {[e2]}]}) ∅ r.

  Definition gmap_to_rel (rm : grel_map) : grel :=
    map_fold (fun e1 se2 res => res ∪ (set_map (e1,.) se2)) ∅ rm.

  Definition grel_map_wf (rm : grel_map) := forall a : A, rm !! a ≠ Some ∅.

  (** Hack to add to sauto when rewrite just fails for no reason *)
  Local Ltac auto_setoid_rewrite :=
    repeat (match goal with | H : _ = _ |- _ => setoid_rewrite H end).


  Lemma grel_map_eq_wf (rm rm' : grel_map):
    grel_map_wf rm -> grel_map_wf rm' -> (forall a : A, rm !!! a = rm' !!! a) -> rm = rm'.
  Proof using.
    intros WF WF' P.
    apply map_eq.
    intro i.
    pose proof (P i) as P.
    unfold grel_map_wf in *.
    setoid_rewrite lookup_total_lookup in P.
    unfold default in *.
    case_splitting; naive_solver.
  Qed.

  Lemma grel_to_map_spec r e1 e2:
    e2 ∈ (grel_to_map r !!! e1) <-> (e1, e2) ∈ r.
  Proof using.
    unfold grel_to_map.
    funelim (set_fold _ _ _).
    - set_solver.
    - destruct x as [e3 e4].
      set_unfold.
      case_split; naive_solver.
  Qed.
  Hint Rewrite @grel_to_map_spec : grel.

  Global Instance set_unfold_elem_of_grel_to_map r x y P :
    SetUnfoldElemOf (y, x) r P ->
    SetUnfoldElemOf x (grel_to_map r !!! y) P.
  Proof using. tcclean. apply grel_to_map_spec. Qed.

  Lemma grel_to_map_wf r: grel_map_wf (grel_to_map r).
  Proof using.
    unfold grel_map_wf.
    intro a.
    unfold grel_to_map.
    funelim (set_fold _ _ _).
    - rewrite lookup_unfold. congruence.
    - destruct x as [e3 e4].
      rewrite lookup_unfold.
      unfold option_union.
      unfold grel_map in *.
      case_splitting; (congruence || set_solver).
  Qed.
  Hint Resolve grel_to_map_wf : grel.


  Lemma grel_map_wf_union rm rm':
    grel_map_wf rm -> grel_map_wf rm' -> grel_map_wf (rm ∪ₘ rm').
  Proof using.
    intros H H' a Hc.
    setoid_rewrite lookup_unfold in Hc.
    unfold option_union in Hc.
    unfold grel_map_wf in *.
    hauto db:set lq:on.
  Qed.
  Hint Resolve grel_map_wf_union : grel.

  Lemma gmap_to_rel_spec rm e1 e2:
    (e1, e2) ∈ gmap_to_rel rm <-> e2 ∈ (rm !!! e1).
  Proof using.
    unfold gmap_to_rel.
    funelim (map_fold _ _ _).
    - rewrite lookup_total_unfold.
      set_solver.
    - assert (m !!! i = ∅). {rewrite lookup_total_lookup. hauto lq:on. }
      setoid_rewrite lookup_total_unfold.
      set_unfold. hauto q:on.
  Qed.
  Hint Rewrite gmap_to_rel_spec : grel.

  Global Instance set_unfold_elem_of_gmap_to_rel rm x s P :
    LookupTotalUnfold x.1 rm s ->
    SetUnfoldElemOf x.2 s P ->
    SetUnfoldElemOf x (gmap_to_rel rm) P.
  Proof using. tcclean. apply gmap_to_rel_spec. Qed.


  Lemma grel_to_map_empty :
    grel_to_map ∅ = ∅.
  Proof using. sfirstorder. Qed.
  Hint Rewrite grel_to_map_empty : grel.

  Lemma grel_to_map_union (r1 r2 : grel) :
    grel_to_map (r1 ∪ r2) = grel_to_map r1 ∪ₘ grel_to_map r2.
  Proof using.
    apply grel_map_eq_wf; [auto with grel .. |].
    intro a.
    setoid_rewrite lookup_total_unfold.
    set_unfold.
    hauto lq:on db:grel.
  Qed.
  Hint Rewrite grel_to_map_union : grel.

  Lemma grel_to_map_to_rel (r : grel) :
    r |> grel_to_map |> gmap_to_rel = r.
  Proof using. set_unfold. hauto lq:on.  Qed.
  Hint Rewrite grel_to_map_to_rel : grel.


  Lemma gmap_to_rel_to_map (rm : grel_map) :
    grel_map_wf rm -> rm |> gmap_to_rel |> grel_to_map = rm.
  Proof using.
    intro H.
    apply grel_map_eq_wf; [auto with grel .. |].
    set_solver.
  Qed.
  Hint Rewrite gmap_to_rel_to_map using auto with grel : grel.


  (** ** Domain and range ***)

  Definition grel_dom (r : grel) : gset A := set_map fst r.
  Definition grel_rng (r : grel) : gset A := set_map snd r.

  Global Instance set_unfold_elem_of_grel_dom (r : grel) (x : A) P:
    (forall y, SetUnfoldElemOf (x, y) r (P y)) ->
    SetUnfoldElemOf x (grel_dom r) (exists z, P z).
  Proof using. tcclean. unfold grel_dom. set_unfold. hauto db:pair. Qed.

  Global Instance set_unfold_elem_of_grel_rng (r : grel) (x : A) P:
    (forall y, SetUnfoldElemOf (y, x) r (P y)) ->
    SetUnfoldElemOf x (grel_rng r) (exists z, P z).
  Proof using. tcclean. unfold grel_rng. set_unfold. hauto db:pair. Qed.

  Typeclasses Opaque grel_dom.
  Typeclasses Opaque grel_rng.


  (** ** Sequence ***)

  Definition grel_seq (r r' : grel) : grel :=
    let rm := grel_to_map r' in
    set_fold (fun '(e1, e2) res => res ∪ set_map (e1,.) (rm !!! e2)) ∅ r.
  Infix "⨾" := grel_seq (at level 39, left associativity) : stdpp_scope.

  Lemma grel_seq_spec r r' e1 e2 :
    (e1, e2) ∈ (r ⨾ r') <-> exists e3, (e1, e3) ∈ r /\ (e3, e2) ∈ r'.
  Proof using.
    unfold grel_seq.
    funelim (set_fold _ _ _).
    - set_solver.
    - case_split.
      set_unfold.
      hauto q:on.
  Qed.

  Global Instance set_unfold_elem_of_grel_seq r r' x P Q:
    (forall z, SetUnfoldElemOf (x.1, z) r (P z)) →
    (forall z, SetUnfoldElemOf (z, x.2) r' (Q z)) →
    SetUnfoldElemOf x (r ⨾ r') (∃ z, P z ∧ Q z) | 20.
  Proof using. tcclean. apply grel_seq_spec. Qed.

  Typeclasses Opaque grel_seq.

  Lemma grel_seq_union_r (r1 r2 r2' : grel):
    r1 ⨾ (r2 ∪ r2') = (r1 ⨾ r2) ∪ (r1 ⨾ r2').
  Proof. set_solver. Qed.
  Lemma grel_seq_union_l (r1 r1' r2 : grel):
    (r1 ∪ r1') ⨾ r2 = (r1 ⨾ r2) ∪ (r1' ⨾ r2).
  Proof. set_solver. Qed.

  Global Instance grel_seq_assoc : Assoc (=) grel_seq.
  Proof. unfold Assoc. set_solver. Qed.

  (** ** Inversion ***)

  Definition grel_inv : grel -> grel := set_map (fun x => (x.2, x.1)).
  Notation "r ⁻¹" := (grel_inv r) (at level 1) : stdpp_scope.

  Lemma grel_inv_spec r e1 e2 : (e1, e2) ∈ r⁻¹ <-> (e2, e1) ∈ r.
  Proof using. unfold grel_inv. set_unfold. hauto db:pair. Qed.

  Global Instance set_unfold_elem_of_grel_inv r x P:
    SetUnfoldElemOf (x.2, x.1) r P -> SetUnfoldElemOf x r⁻¹ P.
  Proof using. tcclean. apply grel_inv_spec. Qed.

  Lemma grel_inv_inv (r : grel) : (r⁻¹)⁻¹ = r.
  Proof using. set_solver. Qed.
  Hint Rewrite grel_inv_inv : grel.

  Typeclasses Opaque grel_inv.


  (** ** Set into rel ***)

  Definition grel_from_set (s : gset A) : grel := set_map (fun x => (x, x)) s.

  Notation "⦗ a ⦘" := (grel_from_set a) (format "⦗ a ⦘") : stdpp_scope.

  Lemma grel_from_set_spec (s : gset A) x y : (x, y) ∈ ⦗s⦘ <-> x ∈ s /\ x = y.
  Proof using. unfold grel_from_set. set_solver. Qed.

  Global Instance set_unfold_elem_of_grel_from_set s x P:
    SetUnfoldElemOf x.1 s P →
    SetUnfoldElemOf x ⦗s⦘ (P ∧ x.1 = x.2) | 20.
  Proof using. tcclean. apply grel_from_set_spec. Qed.

  Typeclasses Opaque grel_from_set.

  Global Instance set_unfold_elem_of_grel_from_set_seq s r x P Q:
    SetUnfoldElemOf x.1 s P →
    SetUnfoldElemOf x r Q →
    SetUnfoldElemOf x (⦗s⦘⨾r) (P ∧ Q) | 10.
  Proof using. tcclean. destruct x. set_solver. Qed.

  Global Instance set_unfold_elem_of_grel_seq_from_set r s x P Q:
    SetUnfoldElemOf x r P →
    SetUnfoldElemOf x.2 s Q →
    SetUnfoldElemOf x (r⨾⦗s⦘) (P ∧ Q) | 10.
  Proof using. tcclean. destruct x. set_solver. Qed.


  (** ** Transitive closure ***)

  (** Decides if there exists a path between x and y in r that goes only through
      points in l. x and y themselves don't need to be in l *)
  Fixpoint exists_path (r : grel) (l : list A) (x y : A) : bool :=
    match l with
    | [] => bool_decide ((x,y) ∈ r)
    | a :: t =>
        exists_path r t x y || (exists_path r t x a && exists_path r t a y)
    end.

  (** State that l is a path between x and y in r *)
  Fixpoint is_path (r : grel) (x y : A) (l : list A) : Prop :=
    match l with
    | [] => (x, y) ∈ r
    | a :: t => (x, a) ∈ r /\ is_path r a y t
    end.

  (* Existence of a path implies being in the transitive closure *)
  Lemma is_path_tc r x y path :
    is_path r x y path -> tc (grel_to_relation r) x y.
  Proof using.
    generalize dependent x.
    induction path; sauto lq:on rew:off.
  Qed.

  Lemma is_path_start_dom r x y path :
    is_path r x y path → x ∈ grel_dom r.
  Proof. destruct path; set_solver. Qed.

  Lemma is_path_path_dom r x y path :
    is_path r x y path → ∀ x ∈ path, x ∈ grel_dom r.
  Proof.
    generalize dependent x. induction path; set_solver ##is_path_start_dom.
  Qed.

  Lemma is_path_rng r x y path :
    is_path r x y path → ∀ x ∈ path, x ∈ grel_rng r.
  Proof. generalize dependent x. induction path; set_solver. Qed.

  Lemma is_path_end_rng r x y path :
    is_path r x y path → y ∈ grel_rng r.
  Proof. generalize dependent x. induction path; set_solver. Qed.

  (** Equivalent definition of exists_path using is_path, and in Prop *)
  Definition exists_path' (r : grel) (l : list A) (x y : A) :=
    exists path : list A,
      is_path r x y path /\ NoDup path /\ ∀ p ∈ path, p ∈ l.

  (* If a list contains an element it can be splitted on that element *)
  Lemma list_split (l : list A) x :
    x ∈ l -> exists left right, l = left ++ [x] ++ right.
  Proof using.
    intros H.
    induction l. { set_solver. }
    set_unfold in H.
    destruct H as [H | H].
    - exists [].
      exists l.
      set_solver.
    - apply IHl in H as [left [right H]].
      clear IHl.
      exists (a :: left).
      exists right.
      set_solver.
  Qed.

  (* Split a path on a point *)
  Lemma is_path_split r x y a left right :
    is_path r x y (left ++ [a] ++ right) <->
      is_path r x a left /\ is_path r a y right.
  Proof using.
    generalize dependent x.
    induction left.
    - naive_solver.
    - cbn in *.
      intro x.
      rewrite IHleft.
      naive_solver.
  Qed.

  (* Induction on list length, very convenient *)
  Definition length_ind := (well_founded_ind
                                   (wf_inverse_image (list A) nat _ (@length _)
          lt_wf)).

  (* If there is a path, there a path without duplicate that is a subpath.
     Technically this asserts only subset *)
  Lemma is_path_NoDup r x y path :
    is_path r x y path -> exists npath, is_path r x y npath /\ NoDup npath /\ npath ⊆ path.
  Proof using.
    generalize dependent x.
    induction path using length_ind.
    intros x IP.
    destruct path. {exists []. sauto lq:on simp+:set_unfold. }
    cbn in *.
    destruct (decide (a ∈ path)).
    - apply list_split in e as (left & right & ->).
      rewrite is_path_split in IP.
      opose proof (H (a :: right) _) as H'. {rewrite length_app. cbn. lia. }
      destruct (H' x) as [npath H'']. { naive_solver. }
      exists npath. set_solver.
    - opose proof (H path _) as H'; [lia |].
      destruct (H' a) as [npath H'']. { naive_solver. }
      exists (a :: npath).
      rewrite NoDup_cons.
      set_solver.
  Qed.



  (* Proof that exists_path' satisfies the equation defining exists_path *)
  Lemma exists_path'_add_one r l a x y :
    exists_path' r (a :: l) x y <->
      exists_path' r l x y \/ (exists_path' r l x a /\ exists_path' r l a y).
  Proof using.
    split.
    - intros [path [Hip [HND Hl]]].
      destruct (decide (a ∈ path)).
      + right.
        destruct (list_split _ _ e) as (left & right & ->).
        rewrite is_path_split in *.
        rewrite NoDup_app in HND. cbn in HND. rewrite NoDup_cons in HND.
        split.
        * exists left. set_unfold. sfirstorder.
        * exists right. set_solver.
      + left.
        exists path. set_solver.
    - intros [[path H] | [[left Hl] [right Hr]]].
      + exists path. set_solver.
      + destruct (is_path_NoDup r x y (left ++ [a] ++ right)) as [npath H].
        { rewrite is_path_split. naive_solver. }
        exists npath. set_solver.
  Qed.

  (* Equivalence between the two exists_path versions *)
  Lemma exists_path_spec (r : grel) (l : list A) (x y : A) :
    exists_path r l x y <-> exists_path' r l x y.
  Proof using.
    generalize dependent y.
    generalize dependent x.
    induction l.
    - cbn. setoid_rewrite bool_unfold.
      split.
      + sfirstorder.
      + intros [[] H]; set_solver.
    - cbn. setoid_rewrite bool_unfold.
      repeat setoid_rewrite IHl.
      setoid_rewrite exists_path'_add_one.
      reflexivity.
  Qed.


  Lemma exists_path_dom_rng_l r l x y:
    exists_path r l x y -> x ∉ grel_dom r -> x ∉ grel_rng r -> False.
  Proof using.
    generalize x y.
    induction l; cbn; setoid_rewrite bool_unfold; set_unfold; naive_solver.
  Qed.

  Lemma exists_path_dom_rng_r r l x y:
    exists_path r l x y -> y ∉ grel_dom r -> y ∉ grel_rng r -> False.
  Proof using.
    generalize x y.
    induction l; cbn; setoid_rewrite bool_unfold; set_unfold; naive_solver.
  Qed.

  (* Implementation of computational transitive closure using Floyd-Warshall
     algorithm *)
  Definition grel_plus (r : grel) :=
    let lA := elements (grel_dom r ∪ grel_rng r) in
    foldr
      (fun k =>
         fold_left
           (fun s i =>
              fold_left
                (fun s j =>
                   if bool_decide ((i, k) ∈ s /\ (k, j) ∈ s)
                   then s ∪ {[(i, j)]}
                   else s
                ) lA s
           ) lA
      ) r lA.
  Notation "a ⁺" := (grel_plus a) (at level 1, format "a ⁺") : stdpp_scope.


  Lemma grel_plus_spec' x y r :
    (x, y) ∈ r⁺ <-> exists_path r (elements (grel_dom r ∪ grel_rng r)) x y.
  Proof using.
    unfold grel_plus.
    set (lA := (elements (grel_dom r ∪ grel_rng r))).
    generalize dependent y.
    generalize dependent x.
    generalize lA at 3 4 as l.
    induction l. { cbn. setoid_rewrite bool_unfold. reflexivity. }
    intros x y.
    cbn - [exists_path].
    orewrite* (fold_left_inv_ND
                     (fun (c : grel) (t : list A) =>
                        forall i j, (i,j) ∈ c <->
                                 exists_path r (a :: l) i j /\
                                   (i ∈ t -> exists_path r l i j))).
    - apply NoDup_elements.
    - clear x y. intros x y.
      rewrite IHl. clear IHl.
      destruct (decide (x ∈ lA)).
      + set_solver.
      + cbn.
        setoid_rewrite bool_unfold.
        pose proof exists_path_dom_rng_l.
        set_unfold.
        hauto lq:on.
    - clear x y IHl.
      intros ri i ti _ Hti Hri x y.
      cbn - [exists_path].
      orewrite* (fold_left_inv_ND
                       (fun (c : grel) (tj : list A) =>
                          forall i' j, (i',j) ∈ c <->
                                    exists_path r (a :: l) i' j /\
                                      (i' ∈ ti -> exists_path r l i' j) /\
                                      (i' = i -> j ∈ tj -> exists_path r l i j))).
      + apply NoDup_elements.
      + clear x y. intros x y.
        rewrite Hri. clear ri Hri.
        destruct (decide (y ∈ lA)).
        * set_solver.
        * cbn.
          setoid_rewrite bool_unfold.
          pose proof exists_path_dom_rng_r.
          set_solver.
      + clear x y Hri ri.
        intros rj j tj _ Htj Hrj x y.
        cbn in *.
        setoid_rewrite bool_unfold.
        setoid_rewrite bool_unfold in Hrj.
        destruct (decide (x = i)) as [-> | Hx].
        * destruct (decide (y = j)) as [-> | Hy].
           ++ case_split.
              ** set_unfold.
                 destruct H as [Hia Haj].
                 rewrite Hrj in *.
                 naive_solver.
              ** rewrite Hrj in *.
                 naive_solver.
           ++ case_split; set_unfold; naive_solver.
        * case_split; set_unfold; naive_solver.
      + set_solver.
    - set_solver.
  Qed.

  Lemma grel_plus_spec (r : grel) x y :
    (x, y) ∈ r⁺ <-> tc (grel_to_relation r) x y.
  Proof using.
    rewrite grel_plus_spec'.
    rewrite exists_path_spec.
    split.
    - intros (? & ? & _).
      eapply is_path_tc.
      eassumption.
    - induction 1.
      + exists []. cbn.  set_solver ## @NoDup_nil_2.
      + destruct IHtc as [path ?].
        destruct (is_path_NoDup r x z (y :: path)) as [npath ?].
        * set_solver.
        * exists npath. set_unfold. intuition. naive_solver.
  Qed.

  Lemma grel_plus_path_spec (r : grel) x y :
    (x, y) ∈ r⁺ ↔ ∃ path, is_path r x y path.
  Proof using.
    rewrite grel_plus_spec'.
    rewrite exists_path_spec.
    unfold exists_path'.
    split.
    - naive_solver.
    - intros [path [npath (?&?&?)]%is_path_NoDup].
      set_solver ##is_path_path_dom.
  Qed.



  Typeclasses Opaque grel_plus.
  Opaque grel_plus.

  Lemma grel_plus_once (r : grel) x y : (x, y) ∈ r -> (x, y) ∈ r⁺.
  Proof using. rewrite grel_plus_spec. sauto lq:on. Qed.
  Hint Resolve grel_plus_once: grel.

  Lemma grel_plus_trans (r : grel) x y z :
    (x, y) ∈ r⁺ -> (y, z) ∈ r⁺ -> (x, z) ∈ r⁺.
  Proof using.
    setoid_rewrite grel_plus_spec.
    sauto lq:on use:tc_transitive.
  Qed.
  Hint Resolve grel_plus_trans: grel.

  Lemma grel_plus_ind (r : grel) (P : A -> A -> Prop)
    (RPOnce : forall x y : A, (x, y) ∈ r -> P x y)
    (RPStep : forall x y z : A, (x, y) ∈ r -> (y, z) ∈ r⁺ -> P y z -> P x z) :
    forall x y, (x, y) ∈ r⁺ -> P x y.
  Proof using.
    intros x y H.
    rewrite grel_plus_spec in H.
    induction H.
    - naive_solver.
    - eapply RPStep.
      + apply H.
      + rewrite grel_plus_spec. assumption.
      + assumption.
  Qed.

  Program Global Instance grel_plus_cind (r : grel) (x y : A) (H : (x, y) ∈ r⁺)
    (P : A -> A -> Prop) : CInduction H (P x y) :=
    {|
      induction_requirement :=
        (forall x y : A, (x, y) ∈ r -> P x y) /\
          (forall x y z : A, (x, y) ∈ r -> (y, z) ∈ r⁺ -> P y z -> P x z)
    |}.
  Solve All Obligations with intros; eapply grel_plus_ind; hauto.


  Lemma grel_plus_inv (r : grel) : (r⁻¹)⁺ = (r⁺)⁻¹.
  Proof using.
    set_unfold.
    intros x y.
    #[local] Hint Extern 4 => set_unfold : setu.
    split; intro H; cinduction H; eauto with grel setu.
  Qed.

  Lemma grel_plus_ind_r (r : grel) (P : A -> A -> Prop)
    (RPOnce : forall x y : A, (x, y) ∈ r -> P x y)
    (RPStep : forall x y z : A, (x, y) ∈ r⁺ -> (y, z) ∈ r -> P x y -> P x z) :
    forall x y, (x, y) ∈ r⁺ -> P x y.
  Proof using.
    intros x y H.
    rewrite <- grel_inv_inv in H.
    rewrite <- grel_plus_inv in H.
    set_unfold in H; simpl in H.
    cinduction H.
    - hauto db:grel simp+:set_unfold.
    - rewrite grel_plus_inv in *.
      hauto db:grel simp+:set_unfold.
  Qed.

  Program Definition grel_plus_cind_r (r : grel) (x y : A) (H : (x, y) ∈ r⁺)
    (P : A -> A -> Prop) : CInduction H (P x y) :=
    {|
      induction_requirement :=
        (forall x y : A, (x, y) ∈ r -> P x y) /\
          (forall x y z : A, (x, y) ∈ r⁺ -> (y, z) ∈ r -> P x y -> P x z)
    |}.
  Solve All Obligations with intros; eapply grel_plus_ind_r; hauto.

  Lemma grel_plus_plus (r : grel) : (r⁺)⁺ = r⁺.
  Proof using.
    set_unfold.
    intros x y.
    split.
    - intro H; cinduction H; qauto db:grel.
    - hauto db:grel.
  Qed.
  Hint Rewrite grel_plus_plus: grel.

  Lemma grel_dom_plus (r : grel) : grel_dom r⁺ = grel_dom r.
  Proof using.
    set_unfold.
    intro.
    split.
    - intros [? H].
      cinduction H; naive_solver.
    - hauto lq:on db:grel.
  Qed.
  Hint Rewrite grel_dom_plus: grel.

  Lemma grel_rng_plus (r : grel) : grel_rng r⁺ = grel_rng r.
  Proof using.
    set_unfold.
    intro.
    split.
    - intros [? H].
      cinduction H; naive_solver.
    - hauto lq:on db:grel.
  Qed.
  Hint Rewrite grel_rng_plus: grel.

  Lemma grel_plus_subseteq (r r' : grel) : r ⊆ r' → r⁺ ⊆ r'⁺.
  Proof.
    set_unfold.
    intros ??? H.
    cinduction H; set_solver ##grel_plus_trans ##grel_plus_once.
  Qed.


  (*** Symmetric ***)

  Definition grel_symmetric (r : grel) : Prop := r⁻¹ = r.

  #[export] Instance grel_symmetric_decision r : Decision (grel_symmetric r).
  Proof. unfold_decide. Defined.

  #[export] Instance grel_symmetric_unfold r P:
    (∀ x y, SetUnfoldElemOf (x, y) r (P x y)) →
    SetUnfold (grel_symmetric r) (∀ x y, P x y ↔ P y x).
  Proof. tcclean. unfold grel_symmetric. set_solver. Qed.

  Definition grel_symmetric_spec (r : grel) :
    grel_symmetric r ↔ ∀ x y, (x, y) ∈ r → (y, x) ∈ r.
  Proof. set_solver. Qed.

  (*** Irreflexive ***)

  Definition grel_irreflexive (r : grel) := ∀ x, (x, x) ∉ r.

  Lemma grel_irreflexive_spec (r : grel) :
    grel_irreflexive r ↔ ∀'(x, y) ∈ r, x ≠ y.
  Proof using. unfold grel_irreflexive. hauto q:on db:pair. Qed.

  Global Instance grel_irreflexive_decision r : Decision (grel_irreflexive r).
  Proof using. rewrite grel_irreflexive_spec. solve_decision. Defined.

  Global Instance set_unfold_grel_irreflexive (r : grel) P :
    (∀ x y, SetUnfoldElemOf (x, y) r (P x y)) →
    SetUnfold (grel_irreflexive r) (∀ x, ¬ P x x).
  Proof using. tcclean. naive_solver. Qed.

  Definition grel_acyclic (r : grel) := grel_irreflexive (r⁺).

  #[global] Instance grel_acyclic_decision r : Decision (grel_acyclic r).
  Proof using. unfold grel_acyclic. solve_decision. Qed.

  (*** Transitive ***)

  Definition grel_transitive (r : grel) := r⁺ = r.

  Lemma grel_transitive_spec (r : grel) :
    grel_transitive r ↔ ∀ x y z, (x, y) ∈ r → (y, z) ∈ r → (x, z) ∈ r.
  Proof using.
    unfold grel_transitive.
    split; intro H.
    - rewrite <- H. hauto lq:on db:grel.
    - set_unfold.
      intros x y.
      split; intro Hr.
      + cinduction Hr; hauto db:grel.
      + hauto db:grel.
  Qed.

  Global Instance grel_transitive_decision r : Decision (grel_transitive r).
  Proof using. unfold grel_transitive. solve_decision. Qed.

  Lemma grel_transitive_rew (r : grel) :
    grel_transitive r → r⁺ = r.
  Proof using. naive_solver. Qed.
  Hint Rewrite grel_transitive_rew using done : grel.

  Lemma grel_transitive_relation_spec (r : grel) :
    grel_transitive r ↔ transitive A (grel_to_relation r).
  Proof using. apply grel_transitive_spec. Qed.

  Lemma grel_transitive_plus (r : grel) : grel_transitive (r⁺).
  Proof using. apply <- grel_transitive_spec. hauto db:grel. Qed.
  Hint Resolve grel_transitive_plus : grel.

  (*** Functional ***)

  Definition grel_functional (r : grel) :=
    ∀ x y z : A, (x, y) ∈ r → (x, z) ∈ r → y = z.

  Definition grel_functional_set_size r:
    grel_functional r ↔ ∀ a : A, set_size (grel_to_map r !!! a) ≤ 1.
  Proof using. setoid_rewrite set_size_le1. set_solver. Qed.

  Definition grel_functional_set_size_list r:
    grel_functional r ↔
      ∀ s ∈ (map_to_list (grel_to_map r)).*2, set_size s ≤ 1 .
  Proof using.
    rewrite grel_functional_set_size.
    set_unfold.
    setoid_rewrite lookup_total_lookup.
    unfold default.
    setoid_rewrite exists_pair.
    hfcrush. (* aka magic *)
  Qed.

  Global Instance grel_functional_decision r : Decision (grel_functional r).
  Proof using. rewrite grel_functional_set_size_list. solve_decision. Defined.

  (*** Equivalence ***)

  Definition grel_equiv_on (s : gset A) (r : grel) :=
    grel_symmetric r ∧ grel_transitive r ∧ ⦗s⦘ ⊆ r.

  (*** Reflexivivity ***)

  (** We need to know that A is finite do deal with reflexivity. **)
  Context {finA : Finite A}.

  Definition grel_rc (r : grel) : grel := r ∪ ⦗fin_to_set A⦘.
  Notation "a ?" := (grel_rc a) (at level 1, format "a ?") : stdpp_scope.

  Lemma grel_rc_spec (r : grel) x y : (x, y) ∈ r? ↔ (x, y) ∈ r ∨ x = y.
  Proof using. unfold grel_rc. set_solver. Qed.

  Global Instance set_unfold_elem_of_grel_rc r x P :
    SetUnfoldElemOf x r P ->
    SetUnfoldElemOf x (r?) (P ∨ x.1 = x.2).
  Proof using. tcclean. destruct x. apply grel_rc_spec. Qed.

  Definition grel_reflexive (r : grel) := ∀ x, (x, x) ∈ r.

  Lemma grel_reflexive_incl (r : grel) :
    grel_reflexive r ↔ ⦗fin_to_set A⦘ ⊆ r.
  Proof using. unfold grel_reflexive. set_unfold. hauto. Qed.

  Global Instance grel_reflexive_decision r: Decision (grel_reflexive r).
  Proof using finA. rewrite grel_reflexive_incl. solve_decision. Qed.

  Lemma grel_reflexive_rew (r : grel) :
    grel_reflexive r → r? = r.
  Proof using. unfold grel_reflexive. set_unfold. hauto lq:on. Qed.
  Hint Rewrite grel_reflexive_rew using done : grel.

  Lemma grel_reflexive_rc (r : grel) :
    grel_reflexive r?.
  Proof using. unfold grel_reflexive. set_solver. Qed.
  Hint Resolve grel_reflexive_rc : grel.

End GRel.


Arguments grel _ {_ _}.
Arguments grel_plus_cind : clear implicits.
Arguments grel_plus_cind_r : clear implicits.

(* Notations need to be redefined out of the section. *)
(* TODO maybe grel scope would be better *)
Notation "⦗ a ⦘" := (grel_from_set a) (format "⦗ a ⦘") : stdpp_scope.

Infix "⨾" := grel_seq (at level 37, left associativity) : stdpp_scope.
Infix "⨾@{ K }" := (@grel_seq K _ _) (at level 37, left associativity, only parsing) : stdpp_scope.
Notation "(⨾)" := grel_seq (only parsing) : stdpp_scope.
Notation "(⨾@{ K } )" := (@grel_seq K _ _) (only parsing) : stdpp_scope.
Notation "( r ⨾.)" := (grel_seq r) (only parsing) : stdpp_scope.
Notation "(.⨾ r )" := (λ r', r' ≡ r) (only parsing) : stdpp_scope.

Notation "r ⁻¹" := (grel_inv r) (at level 1) : stdpp_scope.
Notation "a ⁺" := (grel_plus a) (at level 1, format "a ⁺") : stdpp_scope.

(** Users might not want the reflexive notation from finite type. Sometimes you
work on an infinite type with an context-dependent finite set of value of that
type. You could then want to define [a ?] as the reflexive closure on that set.
Import this module if you want the general reflexivity notation for finite types
*)
Module GRelReflNot.
  Notation "a ?" := (grel_rc a) (at level 1, format "a ?") : stdpp_scope.
End GRelReflNot.
