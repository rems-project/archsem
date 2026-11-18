(******************************************************************************)
(* Validated local finals under removal of a foreign TLBI from history       *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstExecutionCurrent
  PromiseFirstVMExecutionCurrent PromiseFirstSailSerialization PromiseFirstSailCertification
  PromiseFirstSailVMCacheSim PromiseFirstSailVMNormalization PromiseFirstSailVMSwapRemoveInit
  PromiseFirstSailVMSwapRemoveOutcome PromiseFirstSailVMSwapRemoveCertification
  PromiseFirstSailVMSwapRemoveTrace PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapBBMRemove PromiseFirstSailVMSwapBBMCache PromiseFirstSailVMSwapFinal
  PromiseFirstSailVMSwapInitial PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMSwapRemove PromiseFirstSailVMSwapRemoveEvents PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMViews PromiseFirstSailVMInstructionReplay.
From ArchSemArm.Proof Require Import PromiseFirstSailVMEnumCacheTransport.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module VMCacheReturn.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis Memory.t.
Section Sail.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n) (tid : fin n).
Local Notation prom := (VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation good := (@VMSwapRemoveInit.state_ok n).
Definition final_at fuel (st : state) ts :=
  ts ∈ CPState.final_states prom (CPState.enumerate_results isem prom term tid
    (PState.initmem st) fuel (PState.tstate tid st) (PState.events st)).

Lemma final_execution fuel st ts : final_at fuel st ts →
  ThreadInstructionExecution prom tid (PState.initmem st) isem term (PState.events st)
    (PState.tstate tid st) ts.
Proof.
  intro Hin. eapply enumerated_final_thread_execution;
    [apply VMMemoryGrowth.outcome_memory_growth|exact Hin].
Qed.

Lemma final_good fuel st ts : good st → final_at fuel st ts →
  VMCacheTransport.thread_good (PState.events st) ts.
Proof.
  intros Hok Hin. pose proof (final_execution fuel st ts Hin) as Hthread.
  assert (Hgood : VMCacheTransport.thread_good (PState.events st) (PState.tstate tid st)).
  { split; [apply Hok|]. split; apply Hok. }
  clear -Hgood Hthread. induction Hthread as [start Hterm|start mid last iis Hterm Hinst Htail IH];
    [exact Hgood|].
  apply IH. exact (VMCacheTransport.fixed_instruction_good isem tid (PState.initmem st)
    (PState.events st) start mid iis Hgood Hinst).
Qed.

Lemma remove_final fuel (a b : state) tlbi rc epoch ts :
  good a → fin_to_nat tid ≠ rc → fin_to_nat tid ≠ TLBI.tid tlbi →
  PState.promise prom (Ev.Tlbi tlbi rc epoch) a = Ok b → final_at fuel b ts →
  ∃ old, final_at fuel a old ∧ VMSwapRemoveRun.ts_rel (PState.events a) ts old.
Proof.
  intros Hok Hrc Hissuer Hpromise Hfinal.
  destruct (PromiseFirstCurrent.promise_success prom _ a b Hpromise) as [Himem [Hmem _]].
  destruct (VMSwapRemoveInit.promise_foreign_initial bbm tid tlbi rc epoch a b
    Hrc Hissuer Hok Hpromise) as [Hr Hi].
  apply (proj1 (enumerate_results_final_state_witness isem term tid _ fuel _ _ ts)) in Hfinal
    as (last & Hstate & Hrun).
  rewrite Himem in Hrun. pose proof (VMSwapRemoveOutcome.mem_length _ _ _ _ _ _ Hr) as Hlen.
  cbn in Hlen. pose proof (VMSwapRemoveCertification.run_to_termination_sim
    (PState.events a) tlbi rc epoch bbm isem term tid (PState.initmem a) (length (PState.events b))
    Hrc ltac:(rewrite Hmem; cbn; lia) fuel
    ([], PPState.Make (PState.tstate tid b) (PState.events b) IIS.init)
    ([], PPState.Make (PState.tstate tid a) (PState.events a) IIS.init)
    (conj eq_refl Hr) Hi) as [Hsim _].
  destruct (Hsim ([], last) CPState.Terminated Hrun)
    as ([msgs endpoint] & ending & Hrun' & [Hmsgs [_ [Hts _]]] & Hend).
  cbn in Hmsgs, Hts. subst msgs ending. rewrite Hstate in Hts.
  exists (PPState.state endpoint). split; [|exact Hts].
  apply (proj2 (enumerate_results_final_state_witness isem term tid _ fuel _ _ _)).
  exists endpoint. split; [reflexivity|]. rewrite Hlen in Hrun'. exact Hrun'.
Qed.
End Sail.

Section Validation.
Local Notation g r := (VMSwapSim.unshift (S (length r))).

Lemma bbm_remove imem (r : Memory.t) tlbi rc epoch ts old :
  VMSwapRemoveOutcome.ok imem r tlbi rc epoch
    (PPState.Make ts (Ev.Tlbi tlbi rc epoch :: r) IIS.init) →
  VMSwapRemoveRun.ts_rel r ts old → VMViews.ts_ok (length r) old →
  BBM.check imem (Ev.Tlbi tlbi rc epoch :: r) ts = Ok false →
  BBM.check imem r old = Ok false.
Proof.
  intros [[[Hbounds _] [[[Htime Hcache] _] _]] _] Hrel Hbound' Hcheck.
  unfold BBM.check in *. destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (VMSwapRemoveRun.ts_rel_tlb r _ _ c Hrel Hc) as [d [Hd Hsim]].
    rewrite Hd. pose proof (VMViews.ok_cache _ _ Hbounds c Hc) as Hgood.
    pose proof (VMViews.ok_cache _ _ Hbound' d Hd) as Hgood'.
    pose proof (VMSwapBBMRemove.check_tlb_remove imem [] r (Ev.Tlbi tlbi rc epoch) _ c
      eq_refl (VMSwapFinal.cache_rows _ _ _ _ Hgood (Hcache c Hc)) Hcheck) as Hremoved.
    apply (VMBBMTransport.check_tlb_equiv imem r (elements (dom imem))
      (VMSwapSim.tlb_map (g r) c) d);
      [apply Hsim|apply Hsim| | |apply Hsim|exact Hremoved].
    + intro fe. rewrite VMSwapRemove.history_tlb_map.
      apply VMSwapRemoveEvents.ordered_map_unshift. apply Hgood.
    + intro fe. apply Hgood'.
  - rewrite (VMSwapRemoveRun.ts_rel_tlb_none r _ _ Hrel Hc). reflexivity.
Qed.

Lemma bbm_insert imem (r : Memory.t) tlbi rc epoch ts :
  VMCacheTransport.thread_good r ts → BBM.check imem r ts = Ok false →
  BBM.check imem (Ev.Tlbi tlbi rc epoch :: r) ts = Ok false.
Proof.
  intros [Hbound [Hroots _]] Hcheck.
  pose proof (VMSwapInitial.shift_initial r ts Hbound Hroots) as Hfixed.
  rewrite <- Hfixed. unfold BBM.check in *. rewrite VMSwapLookup.ts_map_tlb.
  destruct (TState.tlb ts) as [c|]; [|reflexivity]. cbn [fmap option_fmap].
  exact (VMSwapBBMCache.check_tlb_insert imem [] r (Ev.Tlbi tlbi rc epoch) _ c eq_refl Hcheck).
Qed.
End Validation.

Section Observation.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n) (tid : fin n).
Local Notation prom := (VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation good := (@VMSwapRemoveInit.state_ok n).
Local Notation enum := (final_at bbm nondet term tid).
Definition local_valid (st : state) ts :=
  is_emptyb (TState.prom_wr ts ++ TState.prom_tlbi ts) = true ∧
  (bbm = true → BBM.check (PState.initmem st) (PState.events st) ts = Ok false).

Lemma remove_valid fuel (a b : state) ev ts : good a →
  Ev.affects ev tid = false → PState.promise prom ev a = Ok b → enum fuel b ts →
  local_valid b ts → ∃ old, enum fuel a old ∧ local_valid a old ∧
    TState.reg_map old = TState.reg_map ts ∧ TState.pc old = TState.pc ts.
Proof.
  intros Hok Hignore Hpromise Hfinal [Hempty Hbbm].
  destruct (VMCacheTransport.ignored ev tid Hignore) as (tlbi & rc & epoch & -> & Hrc & Hissuer).
  destruct (remove_final bbm nondet term tid fuel a b tlbi rc epoch ts
    Hok Hrc Hissuer Hpromise Hfinal) as (old & Henum & Hrel).
  destruct (PromiseFirstCurrent.promise_success prom _ a b Hpromise) as [Himem [Hmem _]].
  pose proof (final_good bbm nondet term tid fuel a old Hok Henum) as Hgood.
  assert (Hreach : rtc (VMNormalization.Mixed bbm nondet term) b (replace_thread prom b tid ts)).
  { apply VMNormalization.inst_rtc_mixed.
    eapply one_thread_serializes; [apply (final_execution bbm nondet term tid fuel b ts), Hfinal|reflexivity..]. }
  pose proof (VMSwapRemoveTrace.initial bbm tid (PState.events a) tlbi rc epoch Hrc a b
    eq_refl Hissuer Hok Hpromise) as Hinit.
  pose proof (VMSwapRemoveTrace.mixed_rtc_ok bbm tid (PState.events a) tlbi rc epoch Hrc
    nondet term _ _ Hinit Hreach) as Hlast.
  pose proof (VMSwapRemoveTrace.pp_ok tid (PState.events a) tlbi rc epoch _ Hlast) as Hlocal.
  change (VMSwapRemoveOutcome.ok (PState.initmem b) (PState.events a) tlbi rc epoch
    (PPState.Make (PState.tstate tid (replace_thread prom b tid ts)) (PState.events b) IIS.init)) in Hlocal.
  rewrite (replace_thread_same prom b tid ts) in Hlocal.
  rewrite Himem, Hmem in Hlocal. exists old. split; [exact Henum|].
  pose proof (VMSwapRemoveRun.ts_rel_frame _ _ _ Hrel) as Hframe.
  split.
  - split.
    + pose proof (f_equal TState.prom_wr Hframe) as Hwr.
      pose proof (f_equal TState.prom_tlbi Hframe) as Htlbi.
      change (TState.prom_wr old = map (VMSwapSim.unshift (S (length (PState.events a))))
        (TState.prom_wr ts)) in Hwr.
      change (TState.prom_tlbi old = map (VMSwapSim.unshift (S (length (PState.events a))))
        (TState.prom_tlbi ts)) in Htlbi.
      rewrite Hwr, Htlbi. destruct (TState.prom_wr ts), (TState.prom_tlbi ts); exact Hempty.
    + intro Henabled. specialize (Hbbm Henabled). rewrite Himem, Hmem in Hbbm.
      eapply bbm_remove; [exact Hlocal|exact Hrel|apply Hgood|exact Hbbm].
  - destruct Hrel as [Hshape _]. split; rewrite Hshape.
    + change (TState.reg_map (VMSwapLookup.ts_map (VMSwapSim.unshift (S (length (PState.events a)))) ts) = TState.reg_map ts).
      apply VMSwapLookup.ts_map_reg_map.
    + change (TState.pc (VMSwapLookup.ts_map (VMSwapSim.unshift (S (length (PState.events a)))) ts) = TState.pc ts).
      apply VMSwapLookup.ts_map_pc.
Qed.

Lemma return_trace fuel (a b : state) ts : good a →
  rtc (VMCacheTransport.IgnoredStep bbm tid) a b → enum fuel b ts → local_valid b ts →
  ∃ old, enum fuel a old ∧ local_valid a old ∧
    TState.reg_map old = TState.reg_map ts ∧ TState.pc old = TState.pc ts.
Proof.
  intros Hok Htrace. induction Htrace as [a|a mid b [ev [Hignore Hpromise]] Htail IH];
    intros Hfinal Hvalid.
  - exists ts. auto.
  - destruct (IH (VMSwapRemoveInit.promise_ok bbm ev a mid Hok Hpromise) Hfinal Hvalid)
      as (prev & Hprev & Hvalid' & Hregs & Hpc).
    destruct (remove_valid fuel a mid ev prev Hok Hignore Hpromise Hprev Hvalid')
      as (old & Hold & Hvalid'' & Hregs' & Hpc').
    exists old. split; [exact Hold|]. split; [exact Hvalid''|]. split; congruence.
Qed.

Lemma lift_valid (a b : state) ts : VMCacheTransport.thread_good (PState.events a) ts →
  rtc (VMCacheTransport.IgnoredStep bbm tid) a b → local_valid a ts → local_valid b ts.
Proof.
  intros Hgood Htrace. induction Htrace as [a|a mid b [ev [Hignore Hpromise]] Htail IH];
    intros [Hempty Hvalid]; [split; assumption|].
  destruct (VMCacheTransport.ignored ev tid Hignore) as (tlbi & rc & epoch & -> & Hrc & Hissuer).
  destruct (PromiseFirstCurrent.promise_success prom _ a mid Hpromise) as [Himem [Hmem _]].
  apply IH.
  - rewrite Hmem. destruct Hgood as [Hv [Hr Hp]]. split; [eapply VMViews.ts_ok_mono; [|exact Hv]|].
    + cbn; lia.
    + split; [eapply VMRoots.roots_ok_mono; [|exact Hr]; cbn; lia|exact Hp].
  - split; [exact Hempty|]. intro Henabled. rewrite Himem, Hmem.
    apply bbm_insert; [exact Hgood|apply Hvalid, Henabled].
Qed.
End Observation.
End VMCacheReturn.
