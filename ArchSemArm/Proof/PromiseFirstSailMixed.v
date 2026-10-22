(******************************************************************************)
(* Moving UM certification before an instruction prefix with fixed history   *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent
  PromiseFirstSailExecution PromiseFirstSailSequence PromiseFirstSailThread
  PromiseFirstSailThreadCertification PromiseFirstSailCertification
  PromiseFirstSailInterleaving PromiseFirstSailScheduling.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module UMMixedCertification.
Import UMPromising UMContinuation UMThreadReplay UMThreadCertification.
#[local] Typeclasses Transparent Memory.t UMPromising
  Promising.mEvent Promising.tState Promising.iis.

Lemma thread_min_view_monotone {n} (tid : fin n) imem bps isem
    count ts mem fin finmem :
  thread_steps tid imem bps isem count ts mem fin finmem →
  TState.min_new_prom_view ts ≤ TState.min_new_prom_view fin.
Proof.
  intro Hsteps. induction Hsteps; [lia|].
  eapply Nat.le_trans; [|exact IHHsteps].
  exact (instruction_min_view_monotone tid imem isem _ _ _ H0).
Qed.



Lemma candidate_bounds {n} (tid : fin n) imem (term : terminationCondition n)
    isem fuel ts mem msg :
  msg ∈ (CPState.enumerate_results isem UMPromising term tid imem fuel ts mem)
    .(CPState.promises UMPromising) →
  0 < fuel ∧ TState.min_new_prom_view ts ≤ length mem ∧
    CPState.terminated_ts UMPromising (term !!! tid) ts = false.
Proof.
  intro Hin.
  assert (Hterm : CPState.terminated_ts UMPromising (term !!! tid) ts = false).
  { destruct (CPState.terminated_ts UMPromising (term !!! tid) ts) eqn:Hterm;
      [|reflexivity].
    rewrite (enumerate_results_terminated_promises isem term tid imem
      fuel ts mem Hterm) in Hin. inversion Hin. }
  assert (Hbound : TState.min_new_prom_view ts ≤ length mem).
  { destruct (decide (length mem < TState.min_new_prom_view ts)) as [Hstop|Hstop];
      [|lia].
    unfold CPState.enumerate_results in Hin.
    destruct fuel; cbn [CPState.run_to_termination] in Hin;
      unfold mget, mGet, mcall, mbind, fmap,
        Exec.mbind_inst, Exec.fmap_inst, Exec.st_call_MState,
        Exec.res_mbind_inst, Exec.res_fmap_inst in Hin;
      cbn in Hin; rewrite decide_True in Hin by exact Hstop; cbn in Hin;
      inversion Hin. }
  split; [|split; assumption].
  destruct fuel; [|lia].
  unfold CPState.enumerate_results in Hin.
  cbn [CPState.run_to_termination] in Hin.
  unfold mget, mGet, mcall, mbind, fmap,
    Exec.mbind_inst, Exec.fmap_inst, Exec.st_call_MState,
    Exec.res_mbind_inst, Exec.res_fmap_inst in Hin.
  cbn -[CPState.terminated_ts] in Hin.
  rewrite (decide_False (P := length mem < TState.min_new_prom_view ts)) in Hin
    by (apply Nat.le_ngt; exact Hbound).
  rewrite Hterm in Hin.
  cbn in Hin. inversion Hin.
Qed.

(** Certification can execute a prefix that adds no messages, then continue
    certifying from its endpoint. Fulfillments of older promises are allowed. *)
Lemma fixed_prefix_truncated {n} (tid : fin n) imem (term : terminationCondition n)
    isem count ts mem fin finmem :
  thread_steps tid imem (term !!! tid) isem count ts mem fin finmem →
  finmem = mem →
  TState.min_new_prom_view fin ≤ length mem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = false →
  ∀ iis0, ∃ iis,
    Exec.elem_of_results (([], PPState.Make fin mem iis), CPState.OutOfFuel)
      (CPState.run_to_termination isem UMPromising term tid imem count
        (length mem) ([], PPState.Make ts mem iis0)).
Proof.
  intro Hsteps.
  induction Hsteps as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intros Hsame Hbound Hfinalterm iis0.
  - exists iis0. cbn [CPState.run_to_termination].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn -[CPState.terminated_ts]. rewrite decide_False by lia.
    rewrite Hfinalterm. apply Exec.elem_of_mret.
  - assert (Hmidmem : midmem = mem).
    { exact (proj1 (thread_steps_middle_memory tid imem (term !!! tid) isem
        _ _ _ _ _ _ _ _ Hinst Htail) Hsame). }
    subst midmem.
    pose proof (thread_min_view_monotone tid imem (term !!! tid) isem
      _ _ _ _ _ Htail) as Hmidview.
    pose proof (instruction_min_view_monotone tid imem isem _ _ _ Hinst) as Hview.
    cbn in Hview.
    destruct (IH Hsame Hbound Hfinalterm iis) as [last Hcert].
    exists last. cbn [CPState.run_to_termination].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn -[CPState.terminated_ts]. rewrite decide_False by lia. rewrite Hterm.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    eapply Exec.elem_of_bind_intro; [|exact Hcert].
    exact (collect_unchanged_instruction tid imem isem []
      (PPState.Make ts mem IIS.init) (PPState.Make mid mem iis) () Hinst eq_refl).
Qed.

Lemma certification_initial_iis_irrelevant {n} (tid : fin n) imem
    (term : terminationCondition n) isem fuel ts mem iis iis' :
  TState.min_new_prom_view ts ≤ length mem →
  CPState.terminated_ts UMPromising (term !!! tid) ts = false →
  CPState.run_to_termination isem UMPromising term tid imem (S fuel)
    (length mem) ([], PPState.Make ts mem iis) =
  CPState.run_to_termination isem UMPromising term tid imem (S fuel)
    (length mem) ([], PPState.Make ts mem iis').
Proof.
  intros Hbound Hterm. cbn [CPState.run_to_termination].
  unfold mget, mGet, mcall, mbind, fmap,
    Exec.mbind_inst, Exec.fmap_inst, Exec.st_call_MState,
    Exec.res_mbind_inst, Exec.res_fmap_inst.
  cbn -[CPState.terminated_ts].
  rewrite (decide_False (P := length mem < TState.min_new_prom_view ts))
    by (apply Nat.le_ngt; exact Hbound).
  rewrite Hterm.
  reflexivity.
Qed.

Lemma out_of_fuel_error_continue nondet {n} (term : terminationCondition n)
    (tid : fin n) imem fuel extra base proms ppst proms_mid ppst_mid proms' ppst' err :
  Exec.elem_of_results ((proms_mid, ppst_mid), CPState.OutOfFuel)
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) UMPromising
      term tid imem fuel base (proms, ppst)) →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) UMPromising
      term tid imem extra base (proms_mid, ppst_mid)) →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) UMPromising
      term tid imem (fuel + extra) base (proms, ppst)).
Proof.
  revert proms ppst.
  induction fuel as [|fuel IH]; intros proms [ts mem iis] Hprefix Hsuffix.
  - cbn [CPState.run_to_termination] in Hprefix.
    apply Exec.elem_of_bind_elim in Hprefix as [mid [ts0 [Hget Hprefix]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    cbn -[CPState.terminated_ts] in Hprefix.
    destruct (decide (base < TState.min_new_prom_view ts)).
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    destruct (CPState.terminated_ts UMPromising (term !!! tid) ts) eqn:Hterm;
      rewrite Hterm in Hprefix.
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    apply Exec.elem_of_mret_inv in Hprefix as [Heq _].
    injection Heq as <- <-. exact Hsuffix.
  - cbn [CPState.run_to_termination] in Hprefix |- *.
    apply Exec.elem_of_bind_elim in Hprefix as [mid [ts0 [Hget Hprefix]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply exec_error_bind; right.
    exists (proms, PPState.Make ts mem iis), ts. split.
    { exact (Exec.elem_of_mget (proms, PPState.Make ts mem iis) (PPState.state ∘ snd)). }
    cbn -[CPState.terminated_ts] in Hprefix |- *.
    destruct (decide (base < TState.min_new_prom_view ts)).
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    destruct (CPState.terminated_ts UMPromising (term !!! tid) ts) eqn:Hterm;
      rewrite Hterm in Hprefix |- *.
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    apply Exec.elem_of_bind_elim in Hprefix as [reset [[] [Hreset Hprefix]]].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply exec_error_bind; right. eexists _, (). split; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_bind_elim in Hprefix
      as [[proms_next ppst_next] [[] [Hinst Hprefix]]].
    apply exec_error_bind; right. exists (proms_next, ppst_next), ().
    split; [exact Hinst|]. eapply IH; eassumption.
Qed.

(** A promise certified after a fixed-history thread prefix was already
    certifiable before it. The larger budget includes that prefix. *)
Theorem candidate_before_fixed_prefix nondet {n} (term : terminationCondition n)
    (tid : fin n) imem count ts mem fin fuel msg :
  thread_steps tid imem (term !!! tid) (sail_tiny_arm_sem nondet)
    count ts mem fin mem →
  msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid imem fuel fin mem).(CPState.promises UMPromising) →
  msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid imem (count + fuel) ts mem).(CPState.promises UMPromising).
Proof.
  intros Hprefix Hcandidate.
  destruct (candidate_bounds tid imem term (sail_tiny_arm_sem nondet)
    fuel fin mem msg Hcandidate) as [Hfuel [Hbound Hterm]].
  destruct fuel as [|fuel]; [lia|].
  destruct (fixed_prefix_truncated tid imem term (sail_tiny_arm_sem nondet)
    count ts mem fin mem Hprefix eq_refl Hbound Hterm IIS.init) as [iis Htruncated].
  pose proof (certification_initial_iis_irrelevant tid imem term
    (sail_tiny_arm_sem nondet) fuel fin mem iis IIS.init Hbound Hterm) as Hiis.
  destruct (enumerate_results_promise_witness (prom := UMPromising) (sail_tiny_arm_sem nondet)
    term tid imem (S fuel) fin mem msg ltac:(intros; assumption) Hcandidate)
    as [proms [ppst [Hin [[ending Hcert]|[err Hcert]]]]].
  - unfold CPState.enumerate_results. cbn [CPState.promises Promising.filter_promises].
    eapply collected_promise_in_raw_candidates; [exact Hin|].
    eapply out_of_fuel_certification_continue; [exact Htruncated|].
    rewrite Hiis. exact Hcert.
  - assert (Herror : ((proms, ppst), err) ∈ Exec.errors
      (CPState.run_to_termination (sail_tiny_arm_sem nondet) UMPromising
        term tid imem (count + S fuel) (length mem)
        ([], PPState.Make ts mem IIS.init))).
    { eapply out_of_fuel_error_continue; [exact Htruncated|].
      rewrite Hiis. exact Hcert. }
    unfold CPState.enumerate_results. cbn [CPState.promises Promising.filter_promises].
    apply elem_of_remove_dups, list_elem_of_In, List.in_concat.
    exists proms. split; [|apply list_elem_of_In; exact Hin].
    apply list_elem_of_In, elem_of_app. right.
    apply list_elem_of_fmap. exists (proms, ppst). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((proms, ppst), err). split; [reflexivity|exact Herror].
Qed.

Theorem stable_candidate_before_fixed_prefix nondet {n} (term : terminationCondition n)
    (tid : fin n) imem count ts mem fin msg :
  thread_steps tid imem (term !!! tid) (sail_tiny_arm_sem nondet)
    count ts mem fin mem →
  StablePromiseCandidate UMPromising nondet term tid imem fin mem msg →
  StablePromiseCandidate UMPromising nondet term tid imem ts mem msg.
Proof.
  intros Hprefix [threshold Hcandidate].
  exists (count + threshold). intros fuel Hfuel.
  replace fuel with (count + (fuel - count)) by lia.
  eapply candidate_before_fixed_prefix; [exact Hprefix|].
  apply Hcandidate. lia.
Qed.

End UMMixedCertification.

(** Other threads in a prefix can be omitted from certification while the
    shared history is fixed. This covers a direct promise made after a
    nonempty interleaving of instructions. *)
Theorem UMSail_interleaved_candidate_before_prefix nondet {n}
    (term : terminationCondition n) st before (tid : fin n) fuel msg :
  rtc (FixedHistoryInstructionStep nondet term) st before →
  msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid (PState.initmem before) fuel (PState.tstate tid before)
    (PState.events before)).(CPState.promises UMPromising) →
  ∃ count, msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid (PState.initmem st) (count + fuel) (PState.tstate tid st)
    (PState.events st)).(CPState.promises UMPromising).
Proof.
  intros Hprefix Hcandidate.
  destruct (fixed_history_trace_projection nondet term st before Hprefix)
    as [Himem [Hmem Hthreads]].
  destruct (Hthreads tid) as [count Hthread].
  rewrite Hmem in Hthread. rewrite Himem, Hmem in Hcandidate.
  exists count. eapply UMMixedCertification.candidate_before_fixed_prefix; eassumption.
Qed.

Theorem UMSail_interleaved_complete_promise_before_prefix nondet {n}
    (term : terminationCondition n) st before (tid : fin n) fuel msg :
  rtc (FixedHistoryInstructionStep nondet term) st before →
  (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid (PState.initmem before) fuel (PState.tstate tid before)
    (PState.events before)).(CPState.out_of_fuel UMPromising) = false →
  msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid (PState.initmem before) fuel (PState.tstate tid before)
    (PState.events before)).(CPState.promises UMPromising) →
  ∃ next, PState.promise UMPromising msg st = Ok next ∧
    StableCertifiedPromiseStep UMPromising nondet term st next.
Proof.
  intros Hprefix Hcomplete Hcandidate.
  destruct (fixed_history_trace_projection nondet term st before Hprefix)
    as [Himem [Hmem Hthreads]].
  destruct (Hthreads tid) as [count Hthread].
  pose proof (fully_explored_candidate_is_stable UMPromising nondet term tid
    (PState.initmem before) fuel (PState.tstate tid before) (PState.events before)
    msg ltac:(intros; assumption) UM_filter_retains_membership Hcomplete Hcandidate)
    as Hstable.
  rewrite Himem, Hmem in Hstable. rewrite Hmem in Hthread.
  pose proof (UMMixedCertification.stable_candidate_before_fixed_prefix nondet
    term tid (PState.initmem st) count (PState.tstate tid st) (PState.events st)
    (PState.tstate tid before) msg Hthread Hstable) as Hearly.
  destruct (UMPromising_promise_exists msg st) as [next Hpromise].
  exists next. split; [exact Hpromise|].
  exists tid, msg. split; assumption.
Qed.
