(******************************************************************************)
(* TLBI materialization and recipient iteration after foreign TLBI removal   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemove
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveLocal
  PromiseFirstSailVMSwapRemoveRead PromiseFirstSailVMSwapRemoveEffects PromiseFirstSailVMSwapRemoveTimes
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMViews PromiseFirstVMExecutionCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveTLBISim.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome VMSwapRemoveEffects.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Section Removed.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation R := (effect_rel r tlbi rc epoch).
Local Notation VR := (λ x y : nat * bool, y.1 = g x.1 ∧ y.2 = x.2 ∧ x.1 ≠ p).

Theorem materialize_sim l pre event recipient a b : R a b → PPState.mem a = l ++ e :: r →
  ts_inv imem r tlbi rc epoch l (PPState.state a) →
  VMSwapInsert.esim_at R VR
    (materialize_tlbi_for_recipient tid imem pre event recipient)
    (materialize_tlbi_for_recipient tid imem (g pre) event recipient) a b.
Proof.
  intros Hrel Hmem Hcache. unfold materialize_tlbi_for_recipient.
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  pose proof Hrel as [[[prefix [Hm Hm']] [Ht Hi]] [Hstamps Hii]].
  assert (Hprefix : prefix = l) by (rewrite Hmem in Hm; apply (app_inv_tail _ _ _) in Hm; symmetry; exact Hm).
  subst prefix. rewrite Hmem, Hm'.
  assert (Hepoch : TState.dsb_epoch (PPState.state b) = TState.dsb_epoch (PPState.state a)).
  { rewrite (proj1 Ht). reflexivity. }
  rewrite Hepoch.
  eapply (VMSwapInsert.esim_at_bind _ VR).
  - pose proof (proj1 Ht) as Hshape. rewrite Hshape.
    change (TState.prom_tlbi (setv TState.tlb (TState.tlb (PPState.state b)) (ts_map g (PPState.state a))))
      with (map g (TState.prom_tlbi (PPState.state a))).
    rewrite (fulfill_remove r tlbi rc epoch l _ _ (VMSwapRemoveStamps.ok_prom_tlbi _ _ Hstamps)).
    destruct (Memory.fulfill _ _ (l ++ e :: r)) as [time|] eqn:Hfulfill; cbn [fmap option_fmap option_map].
    + apply VMSwapInsert.esim_at_of; [|exact Hrel]. apply esim_ret.
      split; [reflexivity|]. split; [reflexivity|].
      eapply VMSwapRemoveTimes.fulfill_avoids; [exact (VMSwapRemoveStamps.ok_prom_tlbi _ _ Hstamps)|exact Hfulfill].
    + rewrite <- Hshape. eapply fresh_event_map;
        [intros t Htime; cbn; split; [reflexivity|split; [reflexivity|exact Htime]]|exact Hrel|exact Hmem|exact Hcache].
  - intros a' b' [time fresh] [time' fresh'] Ha Hb Hr [Htime [Hfresh Hne]].
    cbn in Htime, Hfresh, Hne. subst time' fresh'.
    apply VMSwapInsert.esim_at_of; [|exact Hr].
    eapply esim_bind; [apply esim_guard_discard; apply (proj2 (unshift_lt_iff_ne p pre time Hne ltac:(lia)))|].
    intros ? ? _.
    eapply (esim_bind _ eq).
    + change (esim R eq (mset PPState.state (set TState.prom_tlbi (filter (λ t, t ≠ time))))
        (mset PPState.state (set TState.prom_tlbi (filter (λ t, t ≠ g time))))).
      apply VMSwapRemoveEffects.update_state.
      * intros ts Hts. symmetry. apply (VMSwapRemoveMap.map_filter_prom_tlbi p ltac:(lia)); [exact Hne|apply Hts].
      * intros; reflexivity.
      * intro; reflexivity.
      * intros; apply VMSwapRemoveStamps.filter_prom_tlbi; assumption.
    + intros ? ? _. apply esim_ret. split; [reflexivity|split; [reflexivity|exact Hne]].
Qed.

#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_mem VMViews.mem_set_mem VMViews.iis_set_mem : pp_remove_tlbi_sim.
Ltac simpl_pp := unfold setv in *; autorewrite with pp_remove_tlbi_sim in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Lemma materialize_cache l pre event recipient a b a' value :
  R a b → PPState.mem a = l ++ e :: r → ts_inv imem r tlbi rc epoch l (PPState.state a) →
  Exec.elem_of_results (a', value) (materialize_tlbi_for_recipient tid imem pre event recipient a) →
  ∃ l', PPState.mem a' = l' ++ e :: r ∧ ts_inv imem r tlbi rc epoch l' (PPState.state a').
Proof.
  destruct a as [ts mem iis]. cbn. intros [[Hm [Ht Hi]] Hstamps] -> Hcache Hrun.
  unfold materialize_tlbi_for_recipient in Hrun. VMViews.invert; subst; simpl_pp.
  all: try match goal with H : TState.process_event tid imem (?ev :: ?prefix ++ e :: r) ?ev ?before = Ok ?after |- _ =>
    destruct (process_event_remove tid imem r tlbi rc epoch prefix ev before (PPState.state b) after Ht Hcache H)
      as (short & Hshort & Hrel' & Hcache') end.
  all: match goal with H : ts_inv imem r tlbi rc epoch ?prefix ?ts |- _ =>
    exists prefix; split; [reflexivity|exact H] end.
Qed.
Definition accum_map (x : (nat * nat) * bool) := ((g x.1.1, g x.1.2), x.2).

Lemma recipient_sim l pre event recipient acc a b : R a b → PPState.mem a = l ++ e :: r →
  ts_inv imem r tlbi rc epoch l (PPState.state a) →
  VMSwapInsert.esim_at R (λ x y, y = accum_map x)
    (VMMemoryGrowth.tlbi_recipient_step tid imem pre event acc recipient)
    (VMMemoryGrowth.tlbi_recipient_step tid imem (g pre) event (accum_map acc) recipient) a b.
Proof.
  intros Hrel Hmem Hcache. destruct acc as [[self other] created].
  unfold VMMemoryGrowth.tlbi_recipient_step, accum_map; cbn [fst snd].
  eapply (VMSwapInsert.esim_at_bind _ VR); [eapply materialize_sim; eassumption|].
  intros a' b' [time fresh] [time' fresh'] Ha Hb Hr [Htime [Hfresh Hne]].
  cbn in Htime, Hfresh, Hne. subst time' fresh'.
  apply VMSwapInsert.esim_at_of; [|exact Hr]. apply esim_ret.
  cbn [fst snd]. destruct (decide (recipient = tid)); rewrite unshift_max; reflexivity.
Qed.

Lemma recipient_cache l pre event recipient acc a b a' value :
  R a b → PPState.mem a = l ++ e :: r → ts_inv imem r tlbi rc epoch l (PPState.state a) →
  Exec.elem_of_results (a', value) (VMMemoryGrowth.tlbi_recipient_step tid imem pre event acc recipient a) →
  ∃ l', PPState.mem a' = l' ++ e :: r ∧ ts_inv imem r tlbi rc epoch l' (PPState.state a').
Proof.
  intros Hrel Hmem Hcache Hrun. destruct acc as [[self other] created].
  unfold VMMemoryGrowth.tlbi_recipient_step in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [[time fresh] [Hmat Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> _]. eapply materialize_cache; eassumption.
Qed.

Theorem recipients_sim pre event recipients : ∀ l acc a b,
  R a b → PPState.mem a = l ++ e :: r → ts_inv imem r tlbi rc epoch l (PPState.state a) →
  VMSwapInsert.esim_at R (λ x y, y = accum_map x)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre event) acc recipients)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem (g pre) event) (accum_map acc) recipients) a b.
Proof.
  induction recipients as [|recipient recipients IH]; intros l acc a b Hrel Hmem Hcache; cbn [foldlM].
  - apply VMSwapInsert.esim_at_of; [apply esim_ret; reflexivity|exact Hrel].
  - eapply (VMSwapInsert.esim_at_bind _ (λ x y, y = accum_map x)); [eapply recipient_sim; eassumption|].
    intros a' b' x y Ha Hb Hr ->.
    destruct (recipient_cache l pre event recipient acc a b a' x Hrel Hmem Hcache Ha) as [l' [Hm' Hc']].
    eapply IH; eassumption.
Qed.

Theorem run_tlbi_sim n l viio info a b : R a b → PPState.mem a = l ++ e :: r →
  ts_inv imem r tlbi rc epoch l (PPState.state a) →
  VMSwapInsert.esim_at R (λ x y : option nat, y = g <$> x)
    (run_tlbi n tid imem viio info) (run_tlbi n tid imem (g viio) info) a b.
Proof.
  intros Hrel Hmem Hcache. unfold run_tlbi.
  eapply (VMSwapInsert.esim_at_bind _ (λ _ _, True)).
  { apply VMSwapInsert.esim_at_of; [apply esim_guard_or; tauto|exact Hrel]. }
  intros a' b' x y Ha Hb Hr Hxy.
  apply Exec.elem_of_guard_or_inv in Ha as ->.
  apply Exec.elem_of_guard_or_inv in Hb as ->.
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  pose proof (proj1 (proj2 (proj1 Hrel))) as Hts.
  pose proof (proj2 (proj2 (proj1 Hrel))) as Hiis.
  rewrite Hiis, (proj1 Hts).
  change (TState.vcse (setv TState.tlb (TState.tlb (PPState.state b)) (ts_map g (PPState.state a))))
    with (g (TState.vcse (PPState.state a))).
  change (TState.vdsb (setv TState.tlb (TState.tlb (PPState.state b)) (ts_map g (PPState.state a))))
    with (g (TState.vdsb (PPState.state a))).
  change (TState.vspec (setv TState.tlb (TState.tlb (PPState.state b)) (ts_map g (PPState.state a))))
    with (g (TState.vspec (PPState.state a))).
  change (IIS.strict (iis_map g (PPState.iis a))) with (g (IIS.strict (PPState.iis a))).
  unfold join, join_nat. rewrite <- !unshift_max.
  destruct (TLBIRecord_op (TLBIInfo_rec info));
    try solve [apply VMSwapInsert.esim_at_of; [apply esim_throw_bind|exact Hrel]].
  all: eapply (VMSwapInsert.esim_at_bind _ eq);
    [apply VMSwapInsert.esim_at_of; [apply esim_ret; reflexivity|exact Hrel]|].
  all: intros a0 b0 ev ev' Ha0 Hb0 Hrel0 Hev;
    apply Exec.elem_of_mret_inv in Ha0 as [-> ->];
    apply Exec.elem_of_mret_inv in Hb0 as [-> ->].
  all: eapply (VMSwapInsert.esim_at_bind _ (λ x y, y = accum_map x));
    [change ((0, 0), false) with (accum_map ((0, 0), false)) at 2;
     eapply recipients_sim; [exact Hrel|exact Hmem|exact Hcache]|].
  all: intros a' b' [[self other] created] acc' Ha Hb Hr' ->;
    cbn [accum_map fst snd]; apply VMSwapInsert.esim_at_of; [|exact Hr'].
  all: eapply (esim_bind _ eq).
  all: try (apply VMSwapRemoveEffects.update_state;
    [intros; unfold compose; symmetry; rewrite (VMSwapRemoveMap.map_vtlbi_other p ltac:(lia)),
       (VMSwapRemoveMap.map_vtlbi_self p ltac:(lia)); reflexivity
    |intros; reflexivity|intro; reflexivity
    |intros; apply VMSwapRemoveStamps.update_vtlbi_other, VMSwapRemoveStamps.update_vtlbi_self; assumption]).
  all: intros ? ? _; eapply (esim_bind _ eq).
  all: try (rewrite <- unshift_max; apply VMSwapRemoveEffects.set_iis;
    [intro; symmetry; apply VMSwapRemoveRead.iis_add|intros; apply VMSwapRemoveStamps.iis_add; assumption]).
  all: intros ? ? _; apply esim_ret; destruct created; reflexivity.
Qed.
End Removed.
End VMSwapRemoveTLBISim.
