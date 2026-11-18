(******************************************************************************)
(* Entry lookup after removing a foreign TLBI                                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMCacheOrder PromiseFirstSailVMSwapRemoveRun.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

(** Exact entry-result transport includes a window starting at the removed
    timestamp. Ordered histories, positive TLBI markers and [event_allowed]
    are the entry-level premises; the thread simulation must establish them.
    The nonempty-window condition on exact transport excludes the interval
    collapsed by [unshift]. Forward transport also covers empty windows. *)
Module VMSwapRemoveEvents.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun.

Lemma events_empty tid ifetch ttbr path events tmin tmax inv : tmax < tmin →
  TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv = [].
Proof.
  intro H. destruct events; cbn [TLB.get_results_from_events]; rewrite decide_True by exact H; reflexivity.
Qed.

Lemma ordered_map_unshift p events : VMCacheOrder.ordered events →
  VMCacheOrder.ordered (map_evs (unshift p) events).
Proof.
  induction events as [|[ev t] events IH]; [exact id|].
  destruct events as [|[ev' t'] events]; cbn [VMCacheOrder.ordered map_evs map fst snd];
    [exact id|]. intros [[Hle Hload] Hord]. split; [split|apply IH, Hord].
  - apply unshift_mono, Hle.
  - exact Hload.
Qed.

(** A load no later than the lower bound supplies the current interval,
    including when equal-time own invalidations are coalesced. *)
Lemma load_at_window tid ifetch ttbr path events : ∀ t tmin tmax inv,
  VMCacheOrder.ordered ((TLB.Entry.Load, t) :: events) → t ≤ tmin → tmin ≤ tmax →
  TLB.Result.make ttbr path tmin tmax inv ∈
    TLB.get_results_from_events tid ifetch ttbr path
      ((TLB.Entry.Load, t) :: events) tmin tmax inv.
Proof.
  induction events as [events IH] using (induction_ltof1 _ (@length _)). unfold ltof in IH.
  intros t tmin tmax inv Hord Hlo Hhi. cbn [TLB.get_results_from_events].
  rewrite !decide_False by lia. destruct (decide (t < tmin)) as [Hlt|Hge].
  - apply elem_of_cons; left; reflexivity.
  - assert (t = tmin) by lia. subst t.
    destruct events as [|[[|issuer] stamp] rest];
      try (apply elem_of_cons; left; reflexivity).
    destruct (decide (tmin = stamp ∧ (ifetch ∨ issuer = tid)));
      [|apply elem_of_cons; left; reflexivity].
    destruct rest as [|[[|issuer'] stamp'] rest'];
      try (apply elem_of_cons; left; reflexivity).
    cbn [VMCacheOrder.ordered] in Hord.
    destruct Hord as [[Hstamp _] [[Hstamp' _] Hrest]].
    apply (IH rest' ltac:(cbn; lia) stamp' tmin tmax inv); [exact Hrest|lia|exact Hhi].
Qed.

Lemma load_at_window_exact tid ifetch ttbr path events : ∀ t tmin tmax inv,
  VMCacheOrder.ordered ((TLB.Entry.Load, t) :: events) → Forall tpos events →
  t ≤ tmin → tmin ≤ tmax →
  TLB.get_results_from_events tid ifetch ttbr path
    ((TLB.Entry.Load, t) :: events) tmin tmax inv = [TLB.Result.make ttbr path tmin tmax inv].
Proof.
  induction events as [events IH] using (induction_ltof1 _ (@length _)). unfold ltof in IH.
  intros t tmin tmax inv Hord Hpos Hlo Hhi. cbn [TLB.get_results_from_events].
  rewrite !decide_False by lia. destruct (decide (t < tmin)); [reflexivity|].
  assert (t = tmin) by lia. subst t.
  destruct events as [|[[|issuer] stamp] rest].
  - cbn [TLB.get_results_from_events]. rewrite decide_False by lia. reflexivity.
  - cbn [VMCacheOrder.ordered] in Hord. exfalso. tauto.
  - apply list.Forall_cons in Hpos as [Hstamp Hpos]. cbn [tpos fst snd] in Hstamp.
    assert (Hle : stamp ≤ tmin) by (exact (proj1 (proj1 Hord))).
    assert (Hnormal : TLB.get_results_from_events tid ifetch ttbr path
        ((TLB.Entry.Tlbi issuer, stamp) :: rest) tmin tmax inv = []).
    { cbn [TLB.get_results_from_events]. rewrite decide_False by lia. apply events_empty. lia. }
    destruct (decide (tmin = stamp ∧ (ifetch ∨ issuer = tid))); [|rewrite Hnormal; reflexivity].
    destruct rest as [|[[|issuer'] stamp'] rest']; try (rewrite Hnormal; reflexivity).
    cbn [VMCacheOrder.ordered] in Hord.
    destruct Hord as [[_ _] [[Hstamp' _] Hrest]].
    apply list.Forall_cons in Hpos as [_ Hpos].
    apply (IH rest' ltac:(cbn; lia) stamp' tmin tmax inv); assumption || lia.
Qed.

Section Removed.
Context (p : nat) (Hp : 0 < p) (tid : nat) (ifetch : bool) (ttbr : bv 64) (path : list (bv 64)).
Local Notation g := (unshift p).

Definition no_tlbi_at (et : TLB.Entry.event * nat) :=
  ∀ issuer, et.1 = TLB.Entry.Tlbi issuer → et.2 ≠ p.

Lemma load_before_removed events t tmax inv :
  VMCacheOrder.ordered ((TLB.Entry.Load, t) :: events) →
  Forall no_tlbi_at events → t ≤ p → p ≤ tmax →
  TLB.get_results_from_events tid ifetch ttbr path
    ((TLB.Entry.Load, t) :: events) p tmax inv = [TLB.Result.make ttbr path p tmax inv].
Proof using Hp.
  intros Hord Hno Ht Hmax. cbn [TLB.get_results_from_events].
  rewrite !decide_False by lia. destruct (decide (t < p)); [reflexivity|].
  assert (t = p) by lia. subst t.
  destruct events as [|[[|issuer] stamp] rest].
  - cbn [TLB.get_results_from_events]. rewrite decide_False by lia. reflexivity.
  - cbn [VMCacheOrder.ordered] in Hord. exfalso. tauto.
  - apply list.Forall_cons in Hno as [Hstamp _]. specialize (Hstamp issuer eq_refl). cbn in Hstamp.
    cbn [VMCacheOrder.ordered] in Hord. destruct Hord as [[Hle _] _].
    rewrite decide_False by (intros [H _]; lia).
    cbn [TLB.get_results_from_events]. rewrite decide_False by lia.
    rewrite events_empty by lia. reflexivity.
Qed.
Lemma get_results_from_events_remove_at events : ∀ tmax inv x,
  VMCacheOrder.ordered events → Forall no_tlbi_at events →
  x ∈ TLB.get_results_from_events tid ifetch ttbr path events p tmax inv →
  res_map g x ∈ TLB.get_results_from_events tid ifetch ttbr path
    (map_evs g events) (g p) (g tmax) (g <$> inv).
Proof using Hp.
  induction events as [events IH] using (induction_ltof1 _ (@length _)). unfold ltof in IH.
  intros tmax inv x Hord Hno Hx.
  destruct (decide (tmax < p)) as [Hempty|Hrange].
  { rewrite events_empty in Hx by exact Hempty. inversion Hx. }
  assert (Hmaprange : ¬ g tmax < g p) by (pose proof (unshift_mono p p tmax ltac:(lia)); lia).
  destruct events as [|[ev t] events].
  { cbn [TLB.get_results_from_events] in Hx. rewrite decide_False in Hx by exact Hrange. inversion Hx. }
  apply list.Forall_cons in Hno as [Ht Hev].
  assert (Htail : VMCacheOrder.ordered events) by (destruct events; exact (proj2 Hord)).
  destruct ev as [|issuer].
  - destruct (decide (t ≤ p)) as [Hle|Hgt].
    + rewrite load_before_removed in Hx by (try assumption; lia). apply elem_of_cons in Hx as [->|Hx];
        [|inversion Hx].
      change (TLB.Result.make ttbr path (g p) (g tmax) (g <$> inv) ∈
        TLB.get_results_from_events tid ifetch ttbr path
          ((TLB.Entry.Load, g t) :: map_evs g events) (g p) (g tmax) (g <$> inv)).
      apply load_at_window; [exact (ordered_map_unshift p _ Hord)|apply unshift_mono, Hle|].
      apply unshift_mono. lia.
    + assert (Htp : t ≠ p) by lia.
      assert (Hlt : g tmax < g t ↔ tmax < t) by (apply unshift_lt_iff_ne; assumption).
      cbn [TLB.get_results_from_events map_evs map fst snd] in Hx |- *.
      rewrite decide_False in Hx by exact Hrange. rewrite decide_False by exact Hmaprange.
      destruct (decide (tmax < t)) as [Hmax|Hmax];
        destruct (decide (g tmax < g t)) as [Hmax'|Hmax']; try (exfalso; tauto).
      * eapply IH; [cbn; lia|exact Htail|exact Hev|exact Hx].
      * rewrite decide_False in Hx by lia.
        rewrite decide_False by (pose proof (unshift_mono p p t ltac:(lia)); lia).
        destruct events as [|[[|issuer'] t'] events']; cbn [map_evs map fst snd] in *.
        -- apply elem_of_cons in Hx as [->|Hx].
           ++ apply elem_of_cons; left; reflexivity.
           ++ apply elem_of_cons; right. exact (IH [] ltac:(cbn; lia) tmax inv x Htail Hev Hx).
        -- apply elem_of_cons in Hx as [->|Hx].
           ++ apply elem_of_cons; left; reflexivity.
           ++ apply elem_of_cons; right.
              exact (IH ((TLB.Entry.Load, t') :: events') ltac:(cbn; lia) tmax inv x Htail Hev Hx).
        -- apply list.Forall_cons in Hev as [Ht' Hev'].
           assert (Ht'p : t' ≠ p) by (apply (Ht' issuer'); reflexivity).
           pose proof (unshift_eq_ne p t t' Htp Ht'p) as Heq.
           destruct (decide (t = t' ∧ (ifetch ∨ issuer' = tid))) as [Hc|Hc];
             destruct (decide (g t = g t' ∧ (ifetch ∨ issuer' = tid))) as [Hc'|Hc'];
             try (exfalso; tauto).
           ++ destruct events' as [|[[|issuer''] t''] events'']; cbn [map_evs map fst snd] in *.
              ** apply elem_of_cons in Hx as [->|Hx].
                 --- apply elem_of_cons; left; reflexivity.
                 --- apply elem_of_cons; right. eapply (IH [(TLB.Entry.Tlbi issuer', t')]);
                       [cbn; lia|exact Htail|constructor; assumption|exact Hx].
              ** eapply (IH ((TLB.Entry.Load, t'') :: events''));
                   [cbn; lia|exact (proj2 Htail)|exact Hev'|exact Hx].
              ** apply elem_of_cons in Hx as [->|Hx].
                 --- apply elem_of_cons; left; reflexivity.
                 --- apply elem_of_cons; right.
                     eapply (IH ((TLB.Entry.Tlbi issuer', t') :: (TLB.Entry.Tlbi issuer'', t'') :: events''));
                       [cbn; lia|exact Htail|constructor; assumption|exact Hx].
           ++ apply elem_of_cons in Hx as [->|Hx].
              ** apply elem_of_cons; left; reflexivity.
              ** apply elem_of_cons; right. eapply (IH ((TLB.Entry.Tlbi issuer', t') :: events'));
                   [cbn; lia|exact Htail|constructor; assumption|exact Hx].
  - assert (Htp : t ≠ p) by (apply (Ht issuer); reflexivity).
    assert (Hm : g (tmax `min` pred t) = g tmax `min` pred (g t)).
    { rewrite unshift_min, unshift_pred by exact Htp. reflexivity. }
    cbn [TLB.get_results_from_events map_evs map fst snd] in Hx |- *.
    rewrite decide_False in Hx by exact Hrange. rewrite decide_False by exact Hmaprange.
    rewrite <- Hm. destruct (decide (ifetch ∨ issuer = tid)).
    + eapply IH; [cbn; lia|exact Htail|exact Hev|exact Hx].
    + change (Some (g t)) with (g <$> Some t). eapply IH; [cbn; lia|exact Htail|exact Hev|exact Hx].
Qed.

Lemma unshift_lower_lt tmax : tmax ≠ pred p → g tmax < g p ↔ tmax < p.
Proof using Hp. unfold unshift. repeat case_decide; lia. Qed.

Lemma cut_avoids_lower tmax t : tmax ≠ pred p → 0 < t → t ≠ p →
  tmax `min` pred t ≠ pred p.
Proof using Hp. intros. lia. Qed.

Lemma map_tpos events : Forall no_tlbi_at events → Forall tpos events →
  Forall tpos (map_evs g events).
Proof using Hp.
  intros Hno Hpos. induction Hpos as [|[ev t] events Ht Hpos IH]; [constructor|].
  apply list.Forall_cons in Hno as [Hne Hno]. cbn [map_evs map fst snd]. constructor; [|apply IH, Hno].
  destruct ev as [|issuer]; [exact I|]. specialize (Hne issuer eq_refl).
  cbn [tpos fst snd] in Ht, Hne |- *. unfold unshift. repeat case_decide; lia.
Qed.

Lemma get_results_from_events_remove_exact_at events : ∀ tmax inv,
  tmax ≠ pred p → VMCacheOrder.ordered events → Forall no_tlbi_at events → Forall tpos events →
  TLB.get_results_from_events tid ifetch ttbr path (map_evs g events) (g p) (g tmax) (g <$> inv) =
    map (res_map g) (TLB.get_results_from_events tid ifetch ttbr path events p tmax inv).
Proof using Hp.
  induction events as [events IH] using (induction_ltof1 _ (@length _)). unfold ltof in IH.
  intros tmax inv Hbound Hord Hno Hpos.
  destruct (decide (tmax < p)) as [Hempty|Hrange].
  { rewrite !events_empty; [reflexivity|exact Hempty|apply (proj2 (unshift_lower_lt tmax Hbound)), Hempty]. }
  assert (Hmaprange : ¬ g tmax < g p) by (pose proof (unshift_mono p p tmax ltac:(lia)); lia).
  destruct events as [|[ev t] events].
  { cbn [TLB.get_results_from_events map_evs map]. rewrite !decide_False by assumption. reflexivity. }
  apply list.Forall_cons in Hno as [Ht Hev]. apply list.Forall_cons in Hpos as [Hpos Hposev].
  assert (Htail : VMCacheOrder.ordered events) by (destruct events; exact (proj2 Hord)).
  destruct ev as [|issuer].
  - destruct (decide (t ≤ p)) as [Hle|Hgt].
    + rewrite load_before_removed by (try assumption; lia).
      change (TLB.get_results_from_events tid ifetch ttbr path
        ((TLB.Entry.Load, g t) :: map_evs g events) (g p) (g tmax) (g <$> inv) =
        [TLB.Result.make ttbr path (g p) (g tmax) (g <$> inv)]).
      apply load_at_window_exact; [exact (ordered_map_unshift p _ Hord)|apply map_tpos; assumption|
        apply unshift_mono, Hle|apply unshift_mono; lia].
    + assert (Htp : t ≠ p) by lia.
      assert (Hlt : g tmax < g t ↔ tmax < t) by (apply unshift_lt_iff_ne; assumption).
      cbn [TLB.get_results_from_events map_evs map fst snd].
      rewrite (decide_False (P := tmax < p)), (decide_False (P := g tmax < g p)) by assumption.
      destruct (decide (tmax < t)) as [Hmax|Hmax];
        destruct (decide (g tmax < g t)) as [Hmax'|Hmax']; try (exfalso; tauto).
      * apply (IH events ltac:(cbn; lia)); assumption.
      * rewrite (decide_False (P := t < p)), (decide_False (P := g t < g p))
          by (try lia; pose proof (unshift_mono p p t ltac:(lia)); lia).
        destruct events as [|[[|issuer'] t'] events']; cbn [map_evs map fst snd].
        -- cbn [map]. f_equal. apply (IH [] ltac:(cbn; lia)); assumption.
        -- cbn [map]. f_equal. apply (IH ((TLB.Entry.Load, t') :: events') ltac:(cbn; lia)); assumption.
        -- apply list.Forall_cons in Hev as [Ht' Hev']. apply list.Forall_cons in Hposev as [Hpos' Hposev'].
           assert (Ht'p : t' ≠ p) by (apply (Ht' issuer'); reflexivity).
           pose proof (unshift_eq_ne p t t' Htp Ht'p) as Heq.
           destruct (decide (t = t' ∧ (ifetch ∨ issuer' = tid))) as [Hc|Hc];
             destruct (decide (g t = g t' ∧ (ifetch ∨ issuer' = tid))) as [Hc'|Hc'];
             try (exfalso; tauto).
           ++ pose proof (IH events' ltac:(cbn; lia) tmax inv Hbound (proj2 Htail) Hev' Hposev') as Hmerge.
              pose proof (IH ((TLB.Entry.Tlbi issuer', t') :: events') ltac:(cbn; lia)
                tmax inv Hbound Htail ltac:(constructor; assumption) ltac:(constructor; assumption)) as Hnormal.
              destruct events' as [|[[|issuer''] t''] events'']; cbn [map_evs map fst snd].
              2: exact Hmerge.
              all: cbn [map]; f_equal; exact Hnormal.
           ++ cbn [map]. f_equal. apply (IH ((TLB.Entry.Tlbi issuer', t') :: events') ltac:(cbn; lia));
                [exact Hbound|exact Htail|constructor; assumption|constructor; assumption].
  - assert (Htp : t ≠ p) by (apply (Ht issuer); reflexivity).
    assert (Hm : g (tmax `min` pred t) = g tmax `min` pred (g t)).
    { rewrite unshift_min, unshift_pred by exact Htp. reflexivity. }
    cbn [TLB.get_results_from_events map_evs map fst snd].
    rewrite (decide_False (P := tmax < p)), (decide_False (P := g tmax < g p)) by assumption.
    rewrite <- Hm. destruct (decide (ifetch ∨ issuer = tid)).
    + apply (IH events ltac:(cbn; lia)); [apply cut_avoids_lower; assumption|assumption..].
    + change (Some (g t)) with (g <$> Some t).
      apply (IH events ltac:(cbn; lia)); [apply cut_avoids_lower; assumption|assumption..].
Qed.
End Removed.

(** A load at the removed timestamp is harmless once the query starts there
    or later. Earlier queries require that timestamp to be absent. *)
Definition event_allowed p tmin (et : TLB.Entry.event * nat) : Prop :=
  et.2 ≠ p ∨ (et.1 = TLB.Entry.Load ∧ p ≤ tmin).

Theorem get_results_from_events_remove_forward p tid ifetch ttbr path events tmin tmax inv x :
  0 < p → VMCacheOrder.ordered events → Forall (event_allowed p tmin) events →
  x ∈ TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv →
  res_map (unshift p) x ∈ TLB.get_results_from_events tid ifetch ttbr path
    (map_evs (unshift p) events) (unshift p tmin) (unshift p tmax) (unshift p <$> inv).
Proof.
  intros Hp Hord Hev Hx. destruct (decide (tmin = p)) as [->|Hne].
  - eapply get_results_from_events_remove_at; [exact Hp|exact Hord| |exact Hx].
    eapply list.Forall_impl; [exact Hev|]. intros [event time] [Ht|[Hload _]] issuer Heq;
      [exact Ht|cbn in Hload, Heq; congruence].
  - rewrite (get_results_from_events_remove p Hp tid ifetch ttbr path events tmax inv tmin Hne).
    + apply list_elem_of_fmap. exists x. auto.
    + eapply list.Forall_impl; [exact Hev|]. intros et [Ht|[Hload Hle]].
      * left. exact Ht.
      * right. split; [exact Hload|lia].
Qed.
Theorem get_results_from_events_remove_exact p tid ifetch ttbr path events tmin tmax inv :
  0 < p → tmin ≤ tmax → VMCacheOrder.ordered events → Forall tpos events →
  Forall (event_allowed p tmin) events →
  TLB.get_results_from_events tid ifetch ttbr path (map_evs (unshift p) events)
    (unshift p tmin) (unshift p tmax) (unshift p <$> inv) =
  map (res_map (unshift p)) (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof.
  intros Hp Hrange Hord Hpos Hev. destruct (decide (tmin = p)) as [->|Hne].
  - apply get_results_from_events_remove_exact_at; [exact Hp|lia|exact Hord| |exact Hpos].
    eapply list.Forall_impl; [exact Hev|]. intros [event time] [Ht|[Hload _]] issuer Heq;
      [exact Ht|cbn in Hload, Heq; congruence].
  - apply get_results_from_events_remove; [exact Hp|exact Hne|].
    eapply list.Forall_impl; [exact Hev|]. intros et [Ht|[Hload Hle]].
    + left. exact Ht.
    + right. split; [exact Hload|lia].
Qed.
End VMSwapRemoveEvents.
