(******************************************************************************)
(* Moving UM certification before an instruction prefix with fixed history   *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent
  PromiseFirstSailExecution PromiseFirstSailSequence PromiseFirstSailThread
  PromiseFirstSailThreadCertification PromiseFirstSailCertification
  PromiseFirstSailInterleaving PromiseFirstSailScheduling PromiseFirstSailCurrent
  PromiseFirstEquivCurrent PromiseFirstSailState PromiseFirstSailForeign
  PromiseFirstSailSerialization PromiseFirstSailOwnership.

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

(** Moving an own-thread promise before an unchanged-history prefix preserves
    that prefix. Its new pending timestamp remains pending at the endpoint.
    The endpoint view bound is supplied by [candidate_bounds] when the promise
    is certified there. *)
Lemma fixed_prefix_pending_replay {n} (tid : fin n) imem bps isem msg
    count ts mem fin finmem :
  thread_steps tid imem bps isem count ts mem fin finmem →
  finmem = mem →
  pending_bounded (PPState.Make ts mem IIS.init) →
  thread_fetches tid imem bps isem msg ts mem →
  TState.min_new_prom_view fin ≤ length mem →
  thread_steps tid imem bps isem count
    (TState.promise (S (length mem)) ts) (msg :: mem)
    (TState.promise (S (length mem)) fin) (msg :: finmem).
Proof.
  intro Htrace.
  induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intros Hmem Hpending Hfetch Hbound; [constructor|].
  assert (Hmidmem : midmem = mem).
  { exact (proj1 (thread_steps_middle_memory tid imem bps isem
      _ _ _ _ _ _ _ _ Hinst Htail) Hmem). }
  subst midmem.
  pose proof (thread_min_view_monotone tid imem bps isem _ _ _ _ _ Htail) as Hmidview.
  econstructor.
  - rewrite promise_terminated. exact Hterm.
  - apply (unchanged_instruction_replay tid imem msg isem
      (PPState.Make ts mem IIS.init) (PPState.Make mid mem iis) ()).
    + exact Hpending.
    + apply (Hfetch 0 ts mem); [constructor|exact Hterm].
    + exact Hinst.
    + reflexivity.
    + cbn. lia.
  - apply IH; [exact Hmem| | |exact Hbound].
    + exact (instruction_pending_bounded tid imem isem
        (PPState.Make ts mem IIS.init) (PPState.Make mid mem iis) () Hpending Hinst).
    + intros steps next nextmem Hsteps Hnextterm.
      eapply Hfetch; [econstructor; eassumption|exact Hnextterm].
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

#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.
#[local] Typeclasses Transparent UMPromising.Memory.t.

Theorem UMSail_own_message_fixed_thread_replay nondet {n}
    (term : terminationCondition n) initMs code (tid : fin n) st next
    msg count fin :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  event_misses_code Msg.read_byte code msg →
  Msg.tid msg = (tid : nat) →
  PState.promise UMPromising msg st = Ok next →
  UMPromising.TState.min_new_prom_view fin ≤ length (PState.events st) →
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid) (sail_tiny_arm_sem nondet)
    count (PState.tstate tid st) (PState.events st) fin (PState.events st) →
  UMThreadReplay.thread_steps tid (PState.initmem next) (term !!! tid) (sail_tiny_arm_sem nondet)
    count (PState.tstate tid next) (PState.events next)
    (UMPromising.TState.promise (length (PState.events next)) fin) (PState.events next).
Proof.
  intros Hsafe Hreach Hmiss Howner Hpromise Hbound Hsteps.
  destruct (UMPromising_promise_success msg st next Hpromise) as [Himem [Hmem Hstates]].
  specialize (Hstates tid).
  rewrite UMPromising_emit_promise_ok, bool_decide_true in Hstates by exact Howner.
  injection Hstates as Hstate.
  rewrite Himem, Hmem, <- Hstate. cbn [length].
  eapply UMMixedCertification.fixed_prefix_pending_replay;
    [exact Hsteps|reflexivity| | |exact Hbound].
  - intros p Hin. exact (proj2 (UMSail_promise_first_pending_bounds
      nondet term initMs st tid p Hreach Hin)).
  - intros steps ts mem Hprefix Hterm.
    assert (Hsource : CPState.terminated_ts UMPromising (term !!! tid)
      (PState.tstate tid st) = false).
    { eapply UMThreadReplay.thread_steps_source_nonterminated; eassumption. }
    eapply (UMThreadReplay.actual_thread_fetches nondet term initMs code tid
      (PState.initmem st) msg (PState.tstate tid st) (PState.events st) Hsafe Hmiss).
    + eapply SailThreadPrefix_start; eassumption.
    + exact Hprefix.
    + exact Hterm.
Qed.

(** The entire interleaving can be replayed after moving a promise to its
    beginning. The final state is the actual result of promising at the old
    endpoint, so this lemma can be composed with a remaining mixed trace. *)
Theorem UMSail_fixed_prefix_promise_replay nondet {n}
    (term : terminationCondition n) initMs code st before next after (tid : fin n) msg :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  event_misses_code Msg.read_byte code msg →
  Msg.tid msg = (tid : nat) →
  UMPromising.TState.min_new_prom_view (PState.tstate tid before) ≤ length (PState.events st) →
  rtc (FixedHistoryInstructionStep nondet term) st before →
  PState.promise UMPromising msg st = Ok next →
  PState.promise UMPromising msg before = Ok after →
  rtc (InstructionTransition UMPromising nondet term) next after.
Proof.
  intros Hsafe Hreach Hmiss Howner Hbound Hprefix Hpromise Hlate.
  destruct (fixed_history_trace_projection nondet term st before Hprefix)
    as [Himem_before [Hmem_before Hthreads]].
  destruct (UMPromising_promise_success msg st next Hpromise)
    as [Himem_next [Hmem_next Hstates_next]].
  destruct (UMPromising_promise_success msg before after Hlate)
    as [Himem_after [Hmem_after Hstates_after]].
  apply finite_all_threads_serialize.
  - rewrite Himem_after, Himem_before, Himem_next. reflexivity.
  - rewrite Hmem_after, Hmem_before, Hmem_next. reflexivity.
  - intro other. destruct (Hthreads other) as [count Hthread].
    rewrite Hmem_before in Hthread. exists count.
    specialize (Hstates_after other).
    destruct (decide (tid = other)) as [<-|Hne].
    + rewrite UMPromising_emit_promise_ok, bool_decide_true in Hstates_after by exact Howner.
      injection Hstates_after as Hstate_after. rewrite <- Hstate_after, Hmem_before.
      replace (S (length (PState.events st))) with (length (PState.events next))
        by (rewrite Hmem_next; reflexivity).
      eapply UMSail_own_message_fixed_thread_replay; eassumption.
    + assert (Hforeign : Msg.tid msg ≠ (other : nat)).
      { rewrite Howner. intro Heq. apply Hne. apply fin_to_nat_inj, Heq. }
      rewrite UMPromising_emit_promise_ok, bool_decide_false in Hstates_after by exact Hforeign.
      injection Hstates_after as Hstate_after. rewrite <- Hstate_after.
      eapply UMSail_foreign_message_thread_replay; eassumption.
Qed.

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

(** A completed certificate can be moved across the whole fixed-history
    interleaving and replayed up to the same endpoint. Ownership follows from
    certification, including candidates collected from failing searches. *)
Theorem UMSail_interleaved_complete_promise_replay nondet {n}
    (term : terminationCondition n) initMs code st before after (tid : fin n) fuel msg :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  rtc (FixedHistoryInstructionStep nondet term) st before →
  (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid (PState.initmem before) fuel (PState.tstate tid before)
    (PState.events before)).(CPState.out_of_fuel UMPromising) = false →
  msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) UMPromising
    term tid (PState.initmem before) fuel (PState.tstate tid before)
    (PState.events before)).(CPState.promises UMPromising) →
  PState.promise UMPromising msg before = Ok after →
  ∃ next, PState.promise UMPromising msg st = Ok next ∧
    StableCertifiedPromiseStep UMPromising nondet term st next ∧
    PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true next ∧
    rtc (InstructionTransition UMPromising nondet term) next after.
Proof.
  intros Hsafe Hreach Hprefix Hcomplete Hcandidate Hlate.
  pose proof (UMCollectedOwnership.enumerated_promise_owner tid
    (PState.initmem before) (sail_tiny_arm_sem nondet) term fuel
    (PState.tstate tid before) (PState.events before) msg Hcandidate) as Howner.
  destruct (UMSail_interleaved_complete_promise_before_prefix nondet term st before
    tid fuel msg Hprefix Hcomplete Hcandidate) as [next [Hpromise Hstable]].
  destruct (UMSail_interleaved_candidate_before_prefix nondet term st before
    tid fuel msg Hprefix Hcandidate) as [count Hearly].
  assert (Hstep : Exec.elem_of_results (next, None)
    (CPState.run_transition_promise_first (sail_tiny_arm_sem nondet) UMPromising
      term (count + fuel) st)).
  { eapply run_transition_promise_first_none_intro with (tid := tid) (ev := msg) (nst := next).
    - rewrite promise_first_execution_results_lookup. exact Hearly.
    - exact Hpromise.
    - reflexivity. }
  pose proof (UMPromising_enumerated_promise_misses_code (sail_tiny_arm_sem nondet)
    term initMs code true st tid (count + fuel) msg
    (sail_observed_code_immutable _ _ _ _ _ _ Hsafe) Hreach Hearly) as Hmiss.
  destruct (UMMixedCertification.candidate_bounds tid (PState.initmem before) term
    (sail_tiny_arm_sem nondet) fuel (PState.tstate tid before) (PState.events before)
    msg Hcandidate) as [_ [Hbound _]].
  destruct (fixed_history_trace_projection nondet term st before Hprefix) as [_ [Hmem _]].
  rewrite Hmem in Hbound.
  exists next. split; [exact Hpromise|]. split; [exact Hstable|]. split.
  - eapply PromiseFirstReachable_step; eassumption.
  - eapply UMSail_fixed_prefix_promise_replay; eassumption.
Qed.

Section MixedFulfillment.
Context (nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation state := (PState.t UMPromising.TState.t Msg.t n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation fixed_step := (FixedHistoryInstructionStep nondet term).
Local Notation promise_step := (StableCertifiedPromiseStep UMPromising nondet term).

(** Instructions may read and fulfill old promises. Every event added to the
    shared history in this trace comes from an explicit certified promise. *)
Definition MixedFulfillmentStep (st next : state) : Prop :=
  fixed_step st next ∨ promise_step st next.

Lemma stable_promise_before_fixed_prefix initMs code st before after :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc fixed_step st before → promise_step before after →
  ∃ next, promise_step st next ∧
    PromiseFirstReachable UMPromising isem term initMs true next ∧
    rtc fixed_step next after.
Proof.
  intros Hsafe Hreach Hprefix [tid [msg [Hstable Hlate]]].
  destruct (fixed_history_trace_projection nondet term st before Hprefix)
    as [Himem [Hmem Hthreads]].
  destruct (Hthreads tid) as [count Hthread]. rewrite Hmem in Hthread.
  assert (Hstable_early : StablePromiseCandidate UMPromising nondet term tid
    (PState.initmem st) (PState.tstate tid st) (PState.events st) msg).
  { eapply UMMixedCertification.stable_candidate_before_fixed_prefix;
      [exact Hthread|]. rewrite Himem, Hmem in Hstable. exact Hstable. }
  destruct Hstable as [fuel Hcandidate]. specialize (Hcandidate fuel ltac:(lia)).
  pose proof (UMCollectedOwnership.enumerated_promise_owner tid
    (PState.initmem before) isem term fuel (PState.tstate tid before)
    (PState.events before) msg Hcandidate) as Howner.
  destruct (UMMixedCertification.candidate_bounds tid (PState.initmem before) term
    isem fuel (PState.tstate tid before) (PState.events before) msg Hcandidate)
    as [_ [Hbound _]]. rewrite Hmem in Hbound.
  destruct (UMPromising_promise_exists msg st) as [next Hpromise].
  assert (Hstable_step : promise_step st next).
  { exists tid, msg. auto. }
  destruct (stable_promise_first_step_fuel UMPromising nondet term st next Hstable_step)
    as [threshold Hstep]. specialize (Hstep threshold ltac:(lia)).
  destruct (UMSail_interleaved_candidate_before_prefix nondet term st before
    tid fuel msg Hprefix Hcandidate) as [prefix_count Hearly].
  pose proof (UMPromising_enumerated_promise_misses_code isem term initMs code true
    st tid (prefix_count + fuel) msg (sail_observed_code_immutable _ _ _ _ _ _ Hsafe)
    Hreach Hearly) as Hmiss.
  exists next. split; [exact Hstable_step|]. split.
  - eapply PromiseFirstReachable_step; eassumption.
  - apply instruction_trace_fixed_history.
    + eapply UMSail_fixed_prefix_promise_replay; eassumption.
    + destruct (UMPromising_promise_success msg st next Hpromise) as [_ [Hnext _]].
      destruct (UMPromising_promise_success msg before after Hlate) as [_ [Hafter _]].
      rewrite Hafter, Hnext, Hmem. reflexivity.
Qed.

Lemma mixed_fulfillment_memory_suffix st final :
  rtc MixedFulfillmentStep st final →
  ∃ extra, PState.events final = (extra ++ PState.events st)%list.
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail [extra Hextra]].
  - exists []. reflexivity.
  - destruct Hstep as [[_ Hmem]|[tid [msg [_ Hpromise]]]].
    + exists extra. rewrite Hextra, Hmem. reflexivity.
    + destruct (UMPromising_promise_success msg st mid Hpromise) as [_ [Hmem _]].
      exists (extra ++ [msg])%list. rewrite Hextra, Hmem, <- app_assoc. reflexivity.
Qed.

Lemma mixed_fulfillment_fixed_history st final :
  rtc MixedFulfillmentStep st final → PState.events final = PState.events st →
  rtc fixed_step st final.
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail IH]; intro Hmem.
  - apply rtc_refl.
  - destruct Hstep as [Hfixed|[tid [msg [_ Hpromise]]]].
    + eapply rtc_l; [exact Hfixed|]. apply IH. rewrite (proj2 Hfixed). exact Hmem.
    + destruct (mixed_fulfillment_memory_suffix mid final Htail) as [extra Hextra].
      destruct (UMPromising_promise_success msg st mid Hpromise) as [_ [Hnew _]].
      rewrite Hnew, Hmem in Hextra. apply (f_equal length) in Hextra.
      rewrite length_app in Hextra. cbn in Hextra. lia.
Qed.

Lemma first_mixed_promise st final :
  rtc MixedFulfillmentStep st final → PState.events final ≠ PState.events st →
  ∃ before after, rtc fixed_step st before ∧ promise_step before after ∧
    rtc MixedFulfillmentStep after final.
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail IH]; intro Hnew;
    [contradiction|].
  destruct Hstep as [Hfixed|Hpromise].
  - destruct (IH ltac:(rewrite (proj2 Hfixed); exact Hnew))
      as [before [after [Hprefix [Hpromise Hsuffix]]]].
    exists before, after. split; [eapply rtc_l; eassumption|auto].
  - exists st, mid. split; [apply rtc_refl|auto].
Qed.

Local Lemma normalize_mixed_fulfillment_bounded initMs code final budget :
  ∀ st,
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc MixedFulfillmentStep st final →
  length (PState.events final) ≤ budget + length (PState.events st) →
  ∃ before, rtc promise_step st before ∧
    PromiseFirstReachable UMPromising isem term initMs true before ∧
    rtc fixed_step before final.
Proof.
  induction budget as [|budget IH]; intros st Hsafe Hreach Htrace Hbound.
  - destruct (mixed_fulfillment_memory_suffix st final Htrace) as [extra Hextra].
    assert (Hnil : extra = []).
    { rewrite Hextra, length_app in Hbound. destruct extra; [reflexivity|cbn in Hbound; lia]. }
    subst extra. cbn in Hextra.
    exists st. split; [apply rtc_refl|]. split; [exact Hreach|].
    apply mixed_fulfillment_fixed_history; assumption.
  - destruct (decide (PState.events final = PState.events st)) as [Hsame|Hnew].
    + exists st. split; [apply rtc_refl|]. split; [exact Hreach|].
      apply mixed_fulfillment_fixed_history; assumption.
    + destruct (first_mixed_promise st final Htrace Hnew)
        as [before [after [Hprefix [Hpromise Hsuffix]]]].
      destruct (stable_promise_before_fixed_prefix initMs code st before after
        Hsafe Hreach Hprefix Hpromise) as [next [Hearly [Hreach_next Hreplay]]].
      assert (Htrace_next : rtc MixedFulfillmentStep next final).
      { eapply rtc_trans; [|exact Hsuffix].
        clear -Hreplay.
        induction Hreplay; [apply rtc_refl|]. eapply rtc_l; [left; eassumption|exact IHHreplay]. }
      assert (Hbound_next : length (PState.events final) ≤ budget + length (PState.events next)).
      { destruct Hearly as [tid [msg [_ Hemit]]].
        destruct (UMPromising_promise_success msg st next Hemit) as [_ [Hmem _]].
        rewrite Hmem. cbn [length]. rewrite Nat.add_succ_r. exact Hbound. }
      destruct (IH next Hsafe Hreach_next Htrace_next Hbound_next)
        as [last [Hpromises [Hreach_last Hfinal]]].
      exists last. split; [eapply rtc_l; eassumption|auto].
Qed.

(** A complete mixed trace whose instructions only fulfill existing promises
    is transformed into a stable promise prefix and an instruction suffix.
    The full endpoint is preserved, including memory and all thread states. *)
Theorem UMSail_mixed_fulfillment_normalization initMs code st final :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc MixedFulfillmentStep st final →
  ∃ before, rtc promise_step st before ∧
    PromiseFirstReachable UMPromising isem term initMs true before ∧
    rtc fixed_step before final.
Proof.
  intros Hsafe Hreach Htrace.
  eapply (normalize_mixed_fulfillment_bounded initMs code final
    (length (PState.events final))); try eassumption. lia.
Qed.
End MixedFulfillment.
