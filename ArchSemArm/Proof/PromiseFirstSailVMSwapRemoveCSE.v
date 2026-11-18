(******************************************************************************)
(* CSE, barriers and exception entry after removing a foreign TLBI             *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemove
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveLocal
  PromiseFirstSailVMSwapRemoveRead PromiseFirstSailVMViews PromiseFirstSailVMPageWrites.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveCSE.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Section Removed.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation R := (related r tlbi rc epoch).

Lemma set_state a b : ts_rel r a b → esim R eq (msetv PPState.state a) (msetv PPState.state b).
Proof.
  intro Ht. apply esim_msetv. intros [ta ma ia] [tb mb ib] [Hm [_ Hi]].
  unfold related; cbn in *. split; [exact Hm|split; assumption].
Qed.
Lemma update_state f1 f2 : (∀ ts, f2 (ts_map g ts) = ts_map g (f1 ts)) →
  (∀ ts cache, f2 (setv TState.tlb cache ts) = setv TState.tlb cache (f2 ts)) →
  (∀ ts, TState.tlb (f2 ts) = TState.tlb ts) →
  esim R eq (mset PPState.state f1) (mset PPState.state f2).
Proof.
  intros Hmap Hcomm Htlb. apply esim_mset. intros [ta ma ia] [tb mb ib] [Hm [Ht Hi]].
  unfold related; cbn in *. split; [exact Hm|]. split; [|exact Hi].
  unfold ts_rel. rewrite <- Hmap. destruct Ht as [Hshape Hsim]. split.
  - rewrite Htlb. transitivity (f2 (setv TState.tlb (TState.tlb tb) (ts_map g ta))).
    + apply f_equal, Hshape.
    + apply Hcomm.
  - rewrite !Htlb. exact Hsim.
Qed.
Lemma add v : esim R eq (mset PPState.iis (IIS.add v)) (mset PPState.iis (IIS.add (g v))).
Proof.
  apply esim_mset. intros [ta ma ia] [tb mb ib] [Hm [Ht Hi]]. unfold related; cbn in *.
  split; [exact Hm|]. split; [exact Ht|rewrite Hi; symmetry; apply VMSwapRemoveRead.iis_add].
Qed.

Theorem run_cse_sim l vmax vmax' a b : R a b → PPState.mem a = l ++ e :: r →
  ts_inv imem r tlbi rc epoch l (PPState.state a) →
  VMSwapRemoveMap.promises_avoid p (PPState.state a) → VMPageWrites.ok a →
  vmax ≤ length (PPState.mem a) → g vmax ≤ vmax' →
  VMSwapInsert.esim_at R eq (run_cse tid imem vmax) (run_cse tid imem vmax') a b.
Proof using Hrc.
  intros Hrel Hmem Hcache Hprom Hevents Hb Hmax. unfold run_cse.
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_of; [|exact Hrel].
  destruct a as [ta ma ia], b as [tb mb ib]. cbn in *.
  destruct Hrel as [[prefix [Hm Hm']] [Ht Hi]]. cbn in *.
  assert (Hprefix : prefix = l) by (rewrite Hmem in Hm; apply (app_inv_tail _ _ _) in Hm; symmetry; exact Hm).
  subst prefix ma mb ib.
  pose proof (proj1 Ht) as Hshape. rewrite Hshape.
  cbn [ts_map TState.vspec TState.vcse TState.vdsb TState.vmsr iis_map IIS.strict].
  unfold join, join_nat. repeat rewrite <- unshift_max.
  eapply esim_bind.
  { apply esim_guard_discard. apply (VMSwapRemoveMap.map_no_promises_until p ltac:(lia)); exact Hprom. }
  intros ? ? _.
  match goal with |- context [TState.cse_candidates ?pre vmax ta] => set (vpre := pre) in * end.
  eapply (esim_bind _ (λ x y : nat, y = g x ∧ x ∈ TState.cse_candidates vpre vmax ta)).
  { split; [|apply eerr_nil; reflexivity].
    intros s1 s2 s1' value Hrel Hrun. apply Exec.elem_of_mchoosel_inv in Hrun as [-> Hin].
    exists s2, (g value). split.
    - apply Exec.elem_of_mchoosel. eapply (VMSwapRemoveMap.cse_candidates_map p ltac:(lia)); eassumption.
    - split; [exact Hrel|split; [reflexivity|exact Hin]]. }
  intros value value' [-> Hin].
  pose proof (VMViews.cse_candidate_le vpre vmax ta value Hin) as Hvalue.
  assert (Hpre : vpre ≤ value) by (unfold TState.cse_candidates in Hin; apply elem_of_seq in Hin; lia).
  eapply (esim_bind _ (ts_rel r)).
  { apply esim_lift_result.
    - intros ta' Hrun.
      destruct (cse_remove tid imem r tlbi rc epoch Hrc l value ta tb ta' Ht Hcache
        ltac:(unfold vpre in Hpre; lia) ltac:(lia) Hrun) as (tb' & Hrun' & Hrel' & Hcache').
      exists tb'. split; [rewrite <- Hshape; exact Hrun'|exact Hrel'].
    - intros err Hrun. destruct (VMPageWrites.cse_remove_error tid imem l r tlbi rc epoch value ta tb err Ht Hevents Hrun)
        as [err' Hrun']. exists err'. rewrite <- Hshape. exact Hrun'. }
  intros ta' tb' Hrel'. eapply (esim_bind _ eq); [apply set_state, Hrel'|intros ? ? _]. apply add.
Qed.
Theorem run_barrier_sim l barrier vmax vmax' a b : R a b → PPState.mem a = l ++ e :: r →
  ts_inv imem r tlbi rc epoch l (PPState.state a) →
  VMSwapRemoveMap.promises_avoid p (PPState.state a) → VMPageWrites.ok a →
  vmax ≤ length (PPState.mem a) → g vmax ≤ vmax' →
  VMSwapInsert.esim_at R eq (run_barrier tid imem barrier vmax) (run_barrier tid imem barrier vmax') a b.
Proof using Hrc.
  intros Hrel Hmem Hcache Hprom Hevents Hb Hmax. unfold run_barrier.
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  destruct barrier as [bar|bar|[]| | | ];
    try solve [apply VMSwapInsert.esim_at_of; [apply esim_throw|exact Hrel]];
    try solve [eapply run_cse_sim; eassumption].
  all: apply VMSwapInsert.esim_at_of; [|exact Hrel].
  all: destruct a as [ta ma ia], b as [tb mb ib]; cbn in *;
    destruct Hrel as [Hm [Ht Hi]]; cbn in *; pose proof (proj1 Ht) as Hshape; rewrite Hshape.
  all: destruct (DxB_types bar).
  all: try (match goal with |- context[if ?choice then _ else _] => destruct choice end).
  all: cbn [ts_map TState.vrd TState.vwr TState.vcse TState.vdsb TState.vdmb TState.vdmbst
    TState.vtlbi_self TState.vtlbi_other]; unfold join, join_nat; repeat rewrite <- unshift_max.
  all: eapply esim_bind.
  all: try solve [apply esim_guard_discard;
    first [apply (VMSwapRemoveMap.map_no_promises_until p ltac:(lia)); exact Hprom
    |apply (VMSwapRemoveMap.map_no_write_promises_until p ltac:(lia)); apply Forall_app in Hprom; apply Hprom]].
  all: intros ? ? _.
  all: repeat (eapply (esim_bind _ eq); [apply update_state;
      [intro; symmetry; first [apply (VMSwapRemoveMap.map_vdmb p ltac:(lia))
      |apply (VMSwapRemoveMap.map_vdmbst p ltac:(lia))|apply (VMSwapRemoveMap.map_vdsb p ltac:(lia))
      |apply (VMSwapRemoveMap.map_next_epoch p ltac:(lia))]
      |intros; reflexivity|intro; reflexivity]|intros ? ? _]).
  all: apply add.
Qed.

Theorem run_take_exception_sim l fault vmax vmax' a b : R a b → PPState.mem a = l ++ e :: r →
  ts_inv imem r tlbi rc epoch l (PPState.state a) → VMViews.ok a →
  VMSwapRemoveMap.promises_avoid p (PPState.state a) → VMPageWrites.ok a →
  vmax ≤ length (PPState.mem a) → g vmax ≤ vmax' →
  VMSwapInsert.esim_at R eq (run_take_exception tid imem fault vmax) (run_take_exception tid imem fault vmax') a b.
Proof using Hrc.
  intros Hrel Hmem Hcache Hbound Hprom Hevents Hb Hmax. unfold run_take_exception.
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  pose proof (proj2 (proj2 Hrel)) as Hi. cbn [compose]. rewrite Hi. cbn [iis_map IIS.inv_time].
  destruct (IIS.inv_time (PPState.iis a)) as [time|] eqn:Htime; cbn.
  - eapply run_cse_sim; try eassumption; [exact (VMViews.ok_inv_time _ _ (proj2 Hbound) time Htime)|lia].
  - eapply run_cse_sim; eassumption.
Qed.
End Removed.
End VMSwapRemoveCSE.
