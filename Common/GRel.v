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

From stdpp Require Export option.
Require Import Common.

(* For some reason some typeclass instance defined in CSets is missing even if
   Common export CSets *)
Require Import CSets.

Import SetUnfoldPair.


(* Obviously not complete but useful *)
Lemma iff_forall_swap A P Q :
  (forall a : A, P a <-> Q a) -> (forall a, P a) <-> (forall a, Q a).
Proof. sfirstorder. Qed.
#[global] Hint Resolve iff_forall_swap : core.


(*** Maps of sets utilities ***)

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
Proof. tcclean. rewrite lookup_unfold. reflexivity. Qed.

Global Instance lookup_total_unfold_pointwise_union `{FinMap K M} `{SemiSet A C}
  {lei : LeibnizEquiv C} (k : K) (m1 m2 : M C) (s1 s2 : C) :
  LookupTotalUnfold k m1 s1 -> LookupTotalUnfold k m2 s2 ->
  LookupTotalUnfold k (m1 ∪ₘ m2) (s1 ∪ s2).
Proof.
  tcclean.
  setoid_rewrite lookup_total_lookup.
  rewrite lookup_unfold.
  hauto unfold:option_union lq:on simp+:set_simp.
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



(*** Grels ***)

Section GRel.
  Context {A : Type}.
  Context {eqA : EqDecision A}.
  Context {countA : Countable A}.

  Definition grel := gset (A * A).

  Definition grel_to_relation (r : grel) : relation A := fun x y => (x, y) ∈ r.

  Definition grel_map := gmap A (gset A).

  Definition grel_to_map (r : grel) : grel_map :=
    set_fold (fun '(e1, e2) res => res ∪ₘ {[e1 := {[e2]}]}) ∅ r.

  Definition gmap_to_rel (rm : grel_map) : grel :=
    map_fold (fun e1 se2 res => res ∪ (set_map (e1,.) se2)) ∅ rm.

  Definition grel_map_wf (rm : grel_map) := forall a : A, rm !! a ≠ Some ∅.

  (** Hack to add to sauto when rewrite just fails for no reason *)
  Local Ltac auto_setoid_rewrite :=
    repeat (match goal with | H : _ = _ |- _ => setoid_rewrite H end).


  (* Set Printing All. *)

  Lemma grel_map_eq_wf (rm rm' : grel_map):
    grel_map_wf rm -> grel_map_wf rm' -> (forall a : A, rm !!! a = rm' !!! a) -> rm = rm'.
  Proof using.
    intros WF WF' P.
    apply map_eq.
    unfold grel_map_wf in *.
    setoid_rewrite lookup_total_lookup in P.
    unfold default in *.
    hfcrush.
  Qed.

  Lemma grel_to_map_spec r e1 e2:
    e2 ∈ (grel_to_map r !!! e1) <-> (e1, e2) ∈ r.
  Proof using.
    unfold grel_to_map.
    cinduction r using set_fold_cind_L.
    - set_solver.
    - destruct x as [e3 e4].
      set_unfold.
      hauto q:on.
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
    cinduction r using set_fold_cind_L.
    - rewrite lookup_unfold. congruence.
    - destruct x as [e3 e4].
      rewrite lookup_unfold.
      unfold option_union.
      unfold grel_map in *.
      case_split; case_split; (congruence || set_solver).
  Qed.
  Hint Resolve grel_to_map_wf : grel.


  Lemma grel_map_wf_union rm rm':
    grel_map_wf rm -> grel_map_wf rm' -> grel_map_wf (rm ∪ₘ rm').
  Proof using.
    intros H H' a Hc.
    setoid_rewrite lookup_unfold in Hc.
    unfold option_union in Hc.
    unfold grel_map_wf in *.
    case_split; try case_split; qauto db:set lq:on.
  Qed.
  Hint Resolve grel_map_wf_union : grel.

  Lemma gmap_to_rel_spec rm e1 e2:
    (e1, e2) ∈ gmap_to_rel rm <-> e2 ∈ (rm !!! e1).
  Proof using.
    unfold gmap_to_rel.
    cinduction rm using map_fold_cind.
    - rewrite lookup_total_unfold.
      set_solver.
    - assert (m !!! i = ∅). rewrite lookup_total_lookup. hauto lq:on.
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
    sauto lq:on db:grel simp+:set_unfold.
  Qed.
  Hint Rewrite grel_to_map_union : grel.

  Lemma grel_to_map_to_rel (r : grel) :
    r |> grel_to_map |> gmap_to_rel = r.
  Proof using. hauto simp+:set_unfold. Qed.
  Hint Rewrite grel_to_map_to_rel : grel.


  Lemma gmap_to_rel_to_map (rm : grel_map) :
    grel_map_wf rm -> rm |> gmap_to_rel |> grel_to_map = rm.
  Proof using.
    intro H.
    apply grel_map_eq_wf; [auto with grel .. |].
    set_solver.
  Qed.
  Hint Rewrite gmap_to_rel_to_map using auto with grel : grel.

  (*** Sequence ***)

  Definition grel_dom (r : grel) : gset A := set_map fst r.
  Definition grel_rng (r : grel) : gset A := set_map snd r.

  Global Instance set_unfold_elem_of_grel_dom (r : grel) (x : A) P:
    (forall y, SetUnfoldElemOf (x, y) r (P y)) ->
    SetUnfoldElemOf x (grel_dom r) (exists z, P z).
  Proof using. tcclean. set_unfold. hauto db:core. Qed.

  Global Instance set_unfold_elem_of_grel_rng (r : grel) (x : A) P:
    (forall y, SetUnfoldElemOf (y, x) r (P y)) ->
    SetUnfoldElemOf x (grel_rng r) (exists z, P z).
  Proof using. tcclean. set_unfold. hauto db:core. Qed.

  Typeclasses Opaque grel_dom.
  Typeclasses Opaque grel_rng.

  (*** Sequence ***)

  Definition grel_seq (r r' : grel) : grel :=
    let rm := grel_to_map r' in
    set_fold (fun '(e1, e2) res => res ∪ set_map (e1,.) (rm !!! e2)) ∅ r.
  Infix "⨾" := grel_seq (at level 44, left associativity) : stdpp_scope.

  Lemma grel_seq_spec r r' e1 e2 :
    (e1, e2) ∈ (r ⨾ r') <-> exists e3, (e1, e3) ∈ r /\ (e3, e2) ∈ r'.
  Proof using.
    unfold grel_seq.
    cinduction r using set_fold_cind_L.
    - set_solver.
    - destruct x.
      set_unfold.
      hauto q:on.
  Qed.

  Global Instance set_unfold_elem_of_grel_seq r r' x P Q:
    (forall z, SetUnfoldElemOf (x.1, z) r (P z)) ->
    (forall z, SetUnfoldElemOf (z, x.2) r' (Q z)) ->
    SetUnfoldElemOf x (r ⨾ r') (exists z, P z /\ Q z).
  Proof using. tcclean. apply grel_seq_spec. Qed.

  (*** Inversion ***)

  Definition grel_inv : grel -> grel := set_map (fun x => (x.2, x.1)).
  Notation "r ⁻¹" := (grel_inv r) (at level 1) : stdpp_scope.

  Lemma grel_inv_spec r e1 e2 : (e1, e2) ∈ r⁻¹ <-> (e2, e1) ∈ r.
  Proof using. unfold grel_inv. set_unfold. hauto db:core. Qed.

  Global Instance set_unfold_elem_of_grel_inv r x P:
    SetUnfoldElemOf (x.2, x.1) r P -> SetUnfoldElemOf x r⁻¹ P.
  Proof using. tcclean. apply grel_inv_spec. Qed.

  Lemma grel_inv_inv (r : grel) : (r⁻¹)⁻¹ = r.
  Proof using. set_solver. Qed.
  Hint Rewrite grel_inv_inv : grel.

  Typeclasses Opaque grel_inv.


  (*** Set into rel ***)

  Definition grel_from_set (s : gset A) : grel := set_map (fun x => (x, x)) s.

  Notation "⦗ a ⦘" := (grel_from_set a) (format "⦗ a ⦘") : stdpp_scope.

  Lemma grel_from_set_spec (s : gset A) x y : (x, y) ∈ ⦗s⦘ <-> x ∈ s /\ x = y.
  Proof using. unfold grel_from_set. set_solver. Qed.

  Global Instance set_unfold_elem_of_grel_from_set s x P:
    SetUnfoldElemOf x.1 s P ->
    SetUnfoldElemOf x ⦗s⦘ (P /\ x.1 = x.2).
  Proof using. tcclean. apply grel_from_set_spec. Qed.

  Typeclasses Opaque grel_from_set.


  (*** Plus operation ***)

  (** Compute the set of all point reachable through rm from a point of r *)
  Definition reachable_from (r : gset A) (rm : grel_map) : gset A :=
    set_fold (fun x res => res ∪ rm !!! x) ∅ r.

  Lemma reachable_from_spec r rm x :
     x ∈ reachable_from r rm <-> ∃' y ∈ r, x ∈ rm !!! y.
  Proof using.
    unfold reachable_from.
    cinduction r using set_fold_cind_L; set_solver.
  Qed.

  Global Instance set_unfold_elem_of_reachable_from x r rm P Q:
    (forall y, SetUnfoldElemOf x (rm !!! y) (Q y)) ->
    (forall y, SetUnfoldElemOf y r (P y)) ->
    SetUnfoldElemOf x (reachable_from r rm) (exists y, P y /\ Q y).
  Proof using. tcclean. apply reachable_from_spec. Qed.

  (** Add point a to all the set associated in rm to the keys in r *)
  Definition add_to_all (a : A) (rm : grel_map) (r : gset A) : grel_map :=
    set_fold (fun x res => <[x := {[a]} ∪ (res !!! x)]> res) rm r.

  Lemma add_to_all_spec (a : A) (rm : grel_map) (r : gset A) (x y : A) :
    x ∈ (add_to_all a rm r) !!! y <->
      x ∈ rm !!! y \/ x = a /\ y ∈ r.
  Proof using.
    unfold add_to_all.
    cinduction r using set_fold_cind_L.
    - set_solver.
    - setoid_rewrite (lookup_total_unfold). set_unfold. hauto q:on.
  Qed.

  Global Instance set_unfold_elem_of_add_to_all x y r rm a P Q:
    SetUnfoldElemOf y r Q ->
    SetUnfoldElemOf x (rm !!! y) P ->
    SetUnfoldElemOf x (add_to_all a rm r !!! y) (P \/ x = a /\ Q).
  Proof using. tcclean. apply add_to_all_spec. Qed.



  Fixpoint grel_plus_aux (l : list A) (rm rminv : grel_map)
    : grel_map * grel_map :=
    match l with
    | [] => (∅, ∅)
    | a :: t =>
        let '(rmp, rmpinv) := grel_plus_aux t rm rminv in
        let reachable_from_a := reachable_from (rm !!! a) rmp in
        let can_reach_a := reachable_from (rminv !!! a) rmpinv in
        let rmp := <[ a := reachable_from_a]> rmp in
        let rmp := add_to_all a rmp can_reach_a in
        let rmpinv := <[ a := can_reach_a]> rmpinv in
        let rmpinv := add_to_all a rmpinv reachable_from_a in
        if reachable_from_a ∩ can_reach_a =? ∅ then
          (rmp, rmpinv)
        else
          let rmp := <[a := {[a]} ∪ rmp !!! a ]> rmp in
          let rmpinv := <[a := {[a]} ∪ rmpinv !!! a]> rmpinv in
          (rmp, rmpinv)
    end.

  Definition grel_plus (r : grel) :=
    let lA := elements (grel_dom r ∪ grel_rng r) in
    let '(rmp, rmpinv) :=
      grel_plus_aux lA (grel_to_map r) (grel_to_map r⁻¹)
    in
    gmap_to_rel rmp.

  Notation "a ⁺" := (grel_plus a) (at level 1, format "a ⁺") : stdpp_scope.

  (** Otherwise set_unfold fails to deal with filter for some cases  *)
  Typeclasses Transparent Decision.

  Lemma grel_plus_aux_spec l rm rminv :
    NoDup l ->
    let r := gmap_to_rel rm in (gmap_to_rel rminv)⁻¹ = r ->
    let rmpp := grel_plus_aux l rm rminv in
    let rp := gmap_to_rel rmpp.1 in (gmap_to_rel rmpp.2)⁻¹ = rp /\
    forall x y : A,
    (x, y) ∈ rp <->
      tc (grel_to_relation (filter (fun x => x.1 ∈ l /\ x.2 ∈ l) r)) x y.
  Proof using.
    intros ND r Hrinv.
    induction l.
    - simpl.
      split.
      + set_solver.
      + intros x y.
        set_unfold.
        split. firstorder.
        intro H.
        induction H; [| assumption].
        unfold grel_to_relation in H.
        repeat set_unfold; naive_solver.
    - intro rmpp.
      destruct rmpp as [rmp rmpinv] eqn:H.
      cbv [rmpp] in *. clear rmpp.
      cbn.
      cbn in H.
      case_split.
      cbn in *.
      inversion_clear ND as [|? ? Ha tmp].
      apply IHl in tmp; clear IHl; destruct tmp as [IHl1 IHl2].
      do 2 set_unfold.
      assert (forall x y : A, x ∈ g !!! y -> x ≠ a /\ y ≠ a) as Hna. {
        clear H.
        intros x y H.
        rewrite IHl2 in H.
        induction H; unfold grel_to_relation in H; set_solver.
      }
      case_split. (* Case split on whether the a -> a edge should exist *)
      + injection H as Hrmp Hrmpinv.
        split.
        * rewrite <- Hrmp; clear Hrmp.
          rewrite <- Hrmpinv; clear Hrmpinv.
          intros x y.
          clear IHl2 H0.
          set_unfold; case_split; case_split; naive_solver.
        * intros x y.
          admit.
      + (* Case where the edge a -> a should exist *)
        injection H as Hrmp Hrmpinv.
        split.
        * rewrite <- Hrmp; clear Hrmp.
          rewrite <- Hrmpinv; clear Hrmpinv.
          intros x y.
          clear IHl2 H0.
          set_unfold; case_split; case_split; naive_solver.
        * intros x y.
          admit.
  Admitted.

  Lemma grel_plus_spec (r : grel) x y :
    (x, y) ∈ r⁺ <-> tc (grel_to_relation r) x y.
  Proof using.
    unfold grel_plus.
    destruct (grel_plus_aux _ _ _) eqn: H.
    epose (S := grel_plus_aux_spec _ _ _).
    rewrite H in S.
    simpl in S.
    feed pose proof S as S; [apply NoDup_elements | set_unfold; hauto |].
    destruct S as [_ S].
    setoid_rewrite S. clear S.
    split; apply (tc_congruence id);
    hauto unfold:grel_to_relation simp+:set_unfold l:on.
  Qed.

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
          (forall x y z : A, (x, y) ∈ r⁺ -> (y, z) ∈ r -> P y z -> P x z)
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


  (*** Symmetric ***)

  Definition grel_symmetric (r : grel) : bool := r =? r⁻¹.

  Definition grel_symmetric_rew (r : grel) :
    grel_symmetric r -> r⁻¹ = r.
  Proof using. unfold grel_symmetric. sauto b:on. Qed.

  Definition grel_symmetric_spec (r : grel) :
    grel_symmetric r -> forall x y, (x, y) ∈ r -> (y, x) ∈ r.
  Proof using.
    unfold grel_symmetric.
    breflect in *.
    set_solver.
  Qed.

  (*** Irreflexive ***)

  Definition grel_irreflexive (r : grel) : bool :=
    forallb (fun x : A * A => negb (x.1 =? x.2)) (elements r).

  Lemma grel_irreflexive_spec (r : grel) :
    grel_irreflexive r <-> ∀''(x, y) ∈ r, x ≠ y.
  Proof using.
    unfold grel_irreflexive.
    repeat breflect in *.
    set_unfold.
    hauto db:core.
  Qed.

  Lemma grel_irreflexive_spec' (r : grel) :
    grel_irreflexive r <-> ∀ x : A, (x, x) ∉ r.
  Proof using.
    rewrite grel_irreflexive_spec.
    hauto db:core.
  Qed.

  Global Instance set_unfold_grel_irreflexive (r : grel) P :
    (forall x y, SetUnfoldElemOf (x, y) r (P x y)) ->
    SetUnfold (grel_irreflexive r) (forall x y, P x y -> x ≠ y).
  Proof using. tcclean. hauto use:grel_irreflexive_spec db:core. Qed.

  Definition grel_acyclic (r : grel) := grel_irreflexive (r⁺).


  (*** Transitive ***)

  Definition grel_transitive (r : grel) : bool := r =? r⁺.

  Lemma grel_transitive_spec (r : grel) :
    grel_transitive r <-> forall x y z, (x, y) ∈ r -> (y, z) ∈ r -> (x, z) ∈ r.
  Proof using.
    unfold grel_transitive.
    repeat breflect in *.
    split; intro H.
    - rewrite H. hauto lq:on db:grel.
    - set_unfold.
      intros x y.
      split; intro Hr.
      + hauto db:grel.
      + cinduction Hr; hauto db:grel.
  Qed.

  Lemma grel_transitive_rew (r : grel) :
    grel_transitive r -> r⁺ = r.
  Proof using. hauto qb:on unfold:grel_transitive. Qed.
  Hint Rewrite grel_transitive_rew using done : grel.

  Lemma grel_transitive_relation_spec (r : grel) :
    grel_transitive r <-> transitive A (grel_to_relation r).
  Proof using.
    unfold transitive.
    unfold grel_to_relation.
    apply grel_transitive_spec.
  Qed.

  Lemma grel_transitive_plus (r : grel) : grel_transitive (r⁺).
  Proof using.
    apply <- grel_transitive_spec.
    hauto db:grel.
  Qed.
  Hint Resolve grel_transitive_plus : grel.

  (*** Functional ***)

  Definition grel_map_functional (rm : grel_map) : bool :=
    map_fold (fun k s b => b && bool_decide (set_size s <= 1)) true rm.

  Lemma grel_map_functional_basic_spec (rm : grel_map) :
    grel_map_functional rm <-> forall a : A, set_size (rm !!! a) <= 1.
  Proof using.
    unfold grel_map_functional.
    cinduction rm using map_fold_cind with [> | intros i s m r Hi Hr].
    - sauto lq:on.
    - breflect in *.
      rewrite Hr; clear Hr.
      setoid_rewrite lookup_total_unfold.
      assert (set_size (m !!! i) <= 1).
      { rewrite lookup_total_lookup. hauto. }
      hfcrush.
  Qed.

  Lemma grel_map_functional_spec (rm : grel_map) :
    grel_map_functional rm <->
      forall a y z : A, y ∈ (rm !!! a) -> z ∈ (rm !!! a) -> y = z.
  Proof using.
    rewrite grel_map_functional_basic_spec.
    setoid_rewrite set_size_le1.
    reflexivity.
  Qed.

  Definition grel_functional (r : grel) :=
    grel_map_functional (grel_to_map r).

  Lemma grel_functional_spec (r : grel) :
    grel_functional r <->
      forall x y z : A, (x, y) ∈ r -> (x, z) ∈ r -> y = z.
  Proof using.
    unfold grel_functional.
    rewrite grel_map_functional_spec.
    set_solver.
  Qed.

  (*** Equivalence ***)

  Definition grel_equiv_on (s : gset A) (r : grel) :=
    grel_symmetric r && grel_transitive r && bool_decide (⦗s⦘ ⊆ r).

  (*** Reflexivivity ***)

  (** We need to know that A is finite do deal with reflexivity. **)
  Context {finA : Finite A}.

  Definition grel_rc (r : grel) : grel := r ∪ ⦗fin_to_set A⦘.
  Notation "a ?" := (grel_rc a) (at level 1, format "a ?") : stdpp_scope.

  Lemma grel_rc_spec (r : grel) x y : (x, y) ∈ r? <-> (x, y) ∈ r \/ x = y.
  Proof using. unfold grel_rc. set_solver. Qed.

  Definition grel_reflexive (r : grel) := r =? r?.

  Lemma grel_reflexive_spec (r : grel) :
    grel_reflexive r <-> forall x : A, (x, x) ∈ r.
  Proof using.
    unfold grel_reflexive.
    breflect in *.
    split; intro H.
    - rewrite H. hauto lq:on use:grel_rc_spec.
    - set_unfold. hauto lq:on.
  Qed.

End GRel.


Arguments grel _ {_ _}.
Arguments grel_plus_cind : clear implicits.
Arguments grel_plus_cind_r : clear implicits.


(* Notations need to be redefined out of the section. *)
Infix "⨾" := grel_seq (at level 44, left associativity) : stdpp_scope.
Notation "r ⁻¹" := (grel_inv r) (at level 1) : stdpp_scope.
Notation "⦗ a ⦘" := (grel_from_set a) (format "⦗ a ⦘") : stdpp_scope.
Notation "a ⁺" := (grel_plus a) (at level 1, format "a ⁺") : stdpp_scope.
Notation "a ?" := (grel_rc a) (at level 1, format "a ?") : stdpp_scope.
