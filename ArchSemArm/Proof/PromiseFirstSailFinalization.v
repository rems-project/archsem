(******************************************************************************)
(* Turning fixed-history UM instruction executions into a final batch        *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstExecutionCurrent
  PromiseFirstSailSequence PromiseFirstSailThread PromiseFirstSailThreadCertification
  PromiseFirstSailCertification PromiseFirstSailInterleaving
  PromiseFirstSailSerialization PromiseFirstSailScheduling.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.
#[local] Typeclasses Transparent UMPromising.Memory.t.

Section ThreadFinalization.
Context {n : nat} (tid : fin n) (imem : memoryMap) (isem : iMon ())
  (term : terminationCondition n) (mem : list Msg.t).

Lemma fixed_execution_min_view ts fin :
  ThreadInstructionExecution UMPromising tid imem isem term mem ts fin →
  UMPromising.TState.min_new_prom_view ts ≤ UMPromising.TState.min_new_prom_view fin.
Proof.
  intro Htrace. induction Htrace; [lia|].
  eapply Nat.le_trans; [|exact IHHtrace].
  exact (UMContinuation.instruction_min_view_monotone tid imem isem _ _ _ H0).
Qed.

(** The bound discharges the executable early-stop check at every instruction
    boundary: the minimum new-promise view is monotone along the suffix. *)
Lemma fixed_execution_collects_final ts fin :
  ThreadInstructionExecution UMPromising tid imem isem term mem ts fin →
  UMPromising.TState.min_new_prom_view fin ≤ length mem →
  ∃ fuel, ∀ iis, ∃ final_iis,
    Exec.elem_of_results (([], PPState.Make fin mem final_iis), CPState.Terminated)
      (CPState.run_to_termination isem UMPromising term tid imem fuel (length mem)
        ([], PPState.Make ts mem iis)).
Proof.
  intro Htrace. induction Htrace as [ts Hterm|ts mid fin step_iis Hterm Hinst Htail IH];
    intro Hbound.
  - exists 0. intro iis. exists iis.
    apply (run_to_termination_terminated_initial (prom := UMPromising)); assumption.
  - destruct (IH Hbound) as [fuel Hrun].
    assert (Hstart : UMPromising.TState.min_new_prom_view ts ≤ length mem).
    { pose proof (fixed_execution_min_view mid fin Htail) as Hmono.
      pose proof (UMContinuation.instruction_min_view_monotone tid imem isem _ _ _ Hinst)
        as Hinst_mono. cbn in Hinst_mono. lia. }
    exists (S fuel). intro iis.
    destruct (Hrun step_iis) as [final_iis Hfinal]. exists final_iis.
    cbn [CPState.run_to_termination].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn -[CPState.terminated_ts]. rewrite decide_False by lia. rewrite Hterm.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    eapply Exec.elem_of_bind_intro with
      (st' := ([], PPState.Make mid mem step_iis)) (a := ()).
    + exact (UMThreadCertification.collect_unchanged_instruction tid imem isem []
        (PPState.Make ts mem UMPromising.IIS.init)
        (PPState.Make mid mem step_iis) () Hinst eq_refl).
    + exact Hfinal.
Qed.

Lemma fixed_execution_final_candidate ts fin :
  ThreadInstructionExecution UMPromising tid imem isem term mem ts fin →
  UMPromising.TState.min_new_prom_view fin ≤ length mem →
  ∃ fuel, fin ∈ (CPState.enumerate_results isem UMPromising term tid imem
    fuel ts mem).(CPState.final_states UMPromising).
Proof.
  intros Htrace Hbound.
  destruct (fixed_execution_collects_final ts fin Htrace Hbound) as [fuel Hrun].
  destruct (Hrun UMPromising.IIS.init) as [iis Hfinal].
  exists fuel. apply (enumerate_results_final_state_witness (prom := UMPromising)).
  exists (PPState.Make fin mem iis). split; [reflexivity|exact Hfinal].
Qed.
End ThreadFinalization.

Section FinalBatch.
Context (nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t UMPromising.TState.t Msg.t n).

Definition UMFinalViewBound (final : state) : Prop :=
  ∀ tid, UMPromising.TState.min_new_prom_view (PState.tstate tid final) ≤
    length (PState.events final).

Lemma final_candidates_common_fuel (st final : state) :
  (∀ tid, ∃ fuel, PState.tstate tid final ∈
    (CPState.enumerate_results isem UMPromising term tid (PState.initmem st)
      fuel (PState.tstate tid st) (PState.events st)).(CPState.final_states UMPromising)) →
  ∃ fuel, ∀ tid, PState.tstate tid final ∈
    (CPState.enumerate_results isem UMPromising term tid (PState.initmem st)
      fuel (PState.tstate tid st) (PState.events st)).(CPState.final_states UMPromising).
Proof.
  intro Hcandidates.
  assert (Hfinite : ∀ tids : list (fin n), ∃ fuel, ∀ tid, tid ∈ tids →
    PState.tstate tid final ∈
    (CPState.enumerate_results isem UMPromising term tid (PState.initmem st)
      fuel (PState.tstate tid st) (PState.events st)).(CPState.final_states UMPromising)).
  { intro tids. induction tids as [|tid tids [fuel Htail]].
    - exists 0. intros tid Hin. inversion Hin.
    - destruct (Hcandidates tid) as [head_fuel Hhead].
      exists (Nat.max head_fuel fuel). intros other Hin.
      apply elem_of_cons in Hin as [->|Hin].
      + eapply final_candidate_more_fuel; [apply Nat.le_max_l|exact Hhead].
      + eapply final_candidate_more_fuel; [apply Nat.le_max_r|apply Htail, Hin]. }
  destruct (Hfinite (enum (fin n))) as [fuel Hfuel].
  exists fuel. intro tid. apply Hfuel, elem_of_enum.
Qed.

Lemma UMSail_thread_executions_final_batch (st final returned : state)
    (pt : CPState.terminated UMPromising term final) :
  PState.initmem final = PState.initmem st →
  PState.events final = PState.events st →
  (∀ tid, ThreadInstructionExecution UMPromising tid (PState.initmem st)
    isem term (PState.events st) (PState.tstate tid st) (PState.tstate tid final)) →
  UMFinalViewBound final →
  Exec.elem_of_results (returned, ()) (CPState.validate_final UMPromising final final) →
  ∃ fuel, Exec.elem_of_results
    (st, Some (CPState.to_final_archState (CPState.make_final UMPromising term final pt)))
    (CPState.run_transition_promise_first isem UMPromising term fuel st).
Proof.
  intros Himem Hmem Hthreads Hbound Hvalid.
  assert (Hcandidates : ∀ tid, ∃ fuel, PState.tstate tid final ∈
    (CPState.enumerate_results isem UMPromising term tid (PState.initmem st)
      fuel (PState.tstate tid st) (PState.events st)).(CPState.final_states UMPromising)).
  { intro tid. eapply fixed_execution_final_candidate; [apply Hthreads|].
    rewrite <- Hmem. apply Hbound. }
  destruct (final_candidates_common_fuel st final Hcandidates) as [fuel Hfuel].
  exists fuel.
  destruct final as [targets final_imem final_mem].
  cbn in Himem, Hmem. subst final_imem final_mem.
  eapply (run_transition_promise_first_some_intro (prom := UMPromising)).
  - apply Exec.elem_of_mchoosel, (proj2 (cprodn_spec _ _)). intro tid.
    rewrite vlookup_map, promise_first_execution_results_lookup. apply Hfuel.
  - eapply validate_final_transport. exact Hvalid.
Qed.

Lemma UMSail_fixed_history_final_batch (st final returned : state)
    (pt : CPState.terminated UMPromising term final) :
  rtc (FixedHistoryInstructionStep nondet term) st final →
  UMFinalViewBound final →
  Exec.elem_of_results (returned, ()) (CPState.validate_final UMPromising final final) →
  ∃ fuel, Exec.elem_of_results
    (st, Some (CPState.to_final_archState (CPState.make_final UMPromising term final pt)))
    (CPState.run_transition_promise_first isem UMPromising term fuel st).
Proof.
  intros Htrace Hbound Hvalid.
  destruct (fixed_history_trace_projection nondet term st final Htrace)
    as [Himem [Hmem Hthreads]].
  eapply UMSail_thread_executions_final_batch; try eassumption.
  intro tid. destruct (Hthreads tid) as [count Hthread].
  eapply UMThreadReplay.fixed_thread_steps_execution; [exact Hthread|exact Hmem|].
  unfold CPState.terminated, fforallb in pt.
  apply true_eq_true in pt.
  apply (proj1 (@List.forallb_forall (fin n)
    (CPState.terminated_tid UMPromising term final) (enum (fin n))) pt).
  apply list_elem_of_In, elem_of_enum.
Qed.
End FinalBatch.
