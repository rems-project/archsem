(******************************************************************************)
(* Direct-to-promise-first for UM fulfillment traces and single threads       *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent
  PromiseFirstEquivCurrent PromiseFirstSailCurrent PromiseFirstSailInterleaving
  PromiseFirstSailSerialization PromiseFirstSailScheduling PromiseFirstSailNoFuel
  PromiseFirstSailMixed PromiseFirstSailFinalization PromiseFirstSailCertification
  PromiseFirstExecutionCurrent
  PromiseFirstSailThread PromiseFirstSailThreadNormalization.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.

Section DirectFulfillment.
Context (nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t UMPromising.TState.t Msg.t n).
Local Notation final_result := ({s & archState.is_terminated term s}).

(** A witness for one successful direct-runner path. Instructions can read and
    fulfill old promises; explicit promise steps add all new history entries.
    Only the selected promise searches require completeness, at the runner's
    actual decreasing budget. The final view bound rules out early stopping
    before the final-state check during the reconstructed certification. *)
Inductive CompleteFulfillmentDirectExecution : nat → state → state → final_result → Prop :=
| fulfillment_execution_final fuel st returned fsig :
    UMFinalViewBound st →
    Exec.elem_of_results (returned, Some fsig)
      (CPState.run_transition isem UMPromising term (S fuel) st) →
    CompleteFulfillmentDirectExecution (S fuel) st returned fsig
| fulfillment_execution_instruction fuel st next returned fsig :
    FixedHistoryInstructionStep nondet term st next →
    CompleteFulfillmentDirectExecution fuel next returned fsig →
    CompleteFulfillmentDirectExecution (S fuel) st returned fsig
| fulfillment_execution_promise fuel st next returned fsig :
    CertificationCompleteAt UMPromising nondet term (S fuel) st →
    Exec.elem_of_results (next, None)
      (CPState.run_transition_promise_first isem UMPromising term (S fuel) st) →
    CompleteFulfillmentDirectExecution fuel next returned fsig →
    CompleteFulfillmentDirectExecution (S fuel) st returned fsig.

Lemma fulfillment_execution_is_direct_run initMs fuel st returned fsig :
  CompleteFulfillmentDirectExecution fuel st returned fsig →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem UMPromising n) fuel term initMs st).
Proof.
  intro Hrun. induction Hrun; cbn [opModel.run].
  - eapply Exec.elem_of_bind_intro; [eassumption|apply Exec.elem_of_mret].
  - eapply Exec.elem_of_bind_intro with (st' := next) (a := None); [|exact IHHrun].
    exact (instruction_transition_any_fuel UMPromising nondet term (S fuel) st next (proj1 H)).
  - eapply Exec.elem_of_bind_intro with (st' := next) (a := None); [|exact IHHrun].
    change (Exec.elem_of_results (next, None)
      (CPState.run_transition isem UMPromising term (S fuel) st)).
    apply (promise_first_none_to_direct_none (prom := UMPromising));
      [intros; assumption|exact H0].
Qed.

Lemma fulfillment_execution_trace fuel st returned fsig :
  CompleteFulfillmentDirectExecution fuel st returned fsig →
  ∃ final (pt : CPState.terminated UMPromising term final),
    rtc (MixedFulfillmentStep nondet term) st final ∧
    UMFinalViewBound final ∧
    Exec.elem_of_results (returned, ()) (CPState.validate_final UMPromising final final) ∧
    fsig = CPState.to_final_archState (CPState.make_final UMPromising term final pt).
Proof.
  intro Hrun. induction Hrun as
    [fuel st returned fsig Hbound Hfinal|
     fuel st next returned fsig Hstep Htail IH|
     fuel st next returned fsig Hcomplete Hstep Htail IH].
  - destruct (run_transition_some_inv (prom := UMPromising) isem term
      (S fuel) st returned fsig Hfinal)
      as [pt [Hvalid Hsig]].
    exists st, pt. split; [apply rtc_refl|auto].
  - destruct IH as [final [pt [Htrace Hrest]]].
    exists final, pt. split; [eapply rtc_l; [left; exact Hstep|exact Htrace]|exact Hrest].
  - destruct IH as [final [pt [Htrace Hrest]]].
    exists final, pt. split; [|exact Hrest].
    eapply rtc_l; [right|exact Htrace].
    eapply complete_promise_step_stable;
      [intros; assumption|exact UM_filter_retains_membership|exact Hcomplete|exact Hstep].
Qed.

(** This conclusion uses the executable promise-first runner with one fuel
    budget and preserves the exact architectural result of the direct path. *)
Theorem UMSail_complete_fulfillment_direct_to_promise_first initMs code fuel st returned fsig :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  CompleteFulfillmentDirectExecution fuel st returned fsig →
  ∃ before cost, ∀ pf_fuel, cost < pf_fuel →
    Exec.elem_of_results (before, fsig)
      (opModel.run (@CPState.opmodel_pf isem UMPromising n) pf_fuel term initMs st).
Proof.
  intros Hsafe Hreach Hrun.
  destruct (fulfillment_execution_trace fuel st returned fsig Hrun)
    as [final [pt [Htrace [Hbound [Hvalid Hsig]]]]].
  destruct (UMSail_mixed_fulfillment_normalization nondet term initMs code st final
    Hsafe Hreach Htrace) as [before [Hprefix [_ Hsuffix]]].
  destruct (UMSail_fixed_history_final_batch nondet term before final returned pt
    Hsuffix Hbound Hvalid) as [cert_fuel Hbatch].
  rewrite <- Hsig in Hbatch.
  destruct (stable_prefix_promise_first_run UMPromising nondet term initMs st
    before before cert_fuel fsig Hprefix Hbatch) as [cost Hpf].
  exists before, cost. exact Hpf.
Qed.

Corollary UMSail_complete_fulfillment_final_inclusion initMs code fuel initPs returned
    fs (pt : archState.is_terminated term fs) :
  UMSailNoSelfModifying nondet term initMs code →
  PState.from_archState UMPromising initMs = Ok initPs →
  CompleteFulfillmentDirectExecution fuel initPs returned (existT fs pt) →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc UMPromising isem fuel n term initMs ∧
  ∃ cost, ∀ pf_fuel, cost < pf_fuel →
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf UMPromising isem pf_fuel n term initMs.
Proof.
  intros Hsafe Hinit Hrun. split.
  - eapply (direct_final_state_intro (prom := UMPromising)); [exact Hinit|].
    apply fulfillment_execution_is_direct_run, Hrun.
  - destruct (UMSail_complete_fulfillment_direct_to_promise_first initMs code fuel
      initPs returned (existT fs pt) Hsafe
      (PromiseFirstReachable_init _ _ _ _ _ _ Hinit) Hrun) as [before [cost Hpf]].
    exists cost. intros pf_fuel Hfuel.
    eapply (promise_first_final_state_intro (prom := UMPromising));
      [exact Hinit|apply Hpf, Hfuel].
Qed.
End DirectFulfillment.

(** A terminating execution of a single actual Sail thread may create fresh
    writes. Its terminating suffix makes the extracted promise certificates
    stable, so no OutOfFuel-completeness assumption is needed for this case. *)
Theorem UMSail_single_thread_common_final_result nondet (term : terminationCondition 1)
    initMs code st final returned count (pt : CPState.terminated UMPromising term final) :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  PState.initmem final = PState.initmem st →
  UMThreadReplay.thread_steps (0%fin : fin 1) (PState.initmem st) (term !!! 0%fin)
    (sail_tiny_arm_sem nondet) count (PState.tstate 0%fin st) (PState.events st)
    (PState.tstate 0%fin final) (PState.events final) →
  UMFinalViewBound final →
  Exec.elem_of_results (returned, ()) (CPState.validate_final UMPromising final final) →
  ∃ direct_returned before cost, ∀ fuel, cost < fuel →
    Exec.elem_of_results
      (direct_returned, CPState.to_final_archState (CPState.make_final UMPromising term final pt))
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) UMPromising 1)
        fuel term initMs st) ∧
    Exec.elem_of_results
      (before, CPState.to_final_archState (CPState.make_final UMPromising term final pt))
      (opModel.run (@CPState.opmodel_pf (sail_tiny_arm_sem nondet) UMPromising 1)
        fuel term initMs st).
Proof.
  intros Hsafe Hreach Himem Hthread Hbound Hvalid.
  assert (Hterm : CPState.terminated_ts UMPromising (term !!! 0%fin)
    (PState.tstate 0%fin final) = true).
  { unfold CPState.terminated, fforallb in pt. apply true_eq_true in pt.
    apply (proj1 (@List.forallb_forall (fin 1)
      (CPState.terminated_tid UMPromising term final) (enum (fin 1))) pt).
    apply list_elem_of_In, elem_of_enum. }
  destruct (UMSail_terminating_thread_normalization nondet term initMs code 0%fin
    (PState.tstate 0%fin final) (PState.events final) st count Hsafe Hreach Hthread Hterm)
    as [before [Hprefix [Himem_before [Hmem_before Hsuffix]]]].
  assert (Hthreads : ∀ tid, ThreadInstructionExecution UMPromising tid
    (PState.initmem before) (sail_tiny_arm_sem nondet) term (PState.events before)
    (PState.tstate tid before) (PState.tstate tid final)).
  { intro tid. assert (Htid : tid = 0%fin).
    { apply fin_to_nat_inj. pose proof (fin_to_nat_lt tid). cbn. lia. }
    subst tid. exact Hsuffix. }
  destruct (UMSail_thread_executions_final_batch nondet term before final returned pt
    (eq_trans Himem (eq_sym Himem_before)) (eq_sym Hmem_before)
    Hthreads Hbound Hvalid) as [cert_fuel Hbatch].
  destruct (stable_prefix_common_fuel UMPromising nondet term initMs st before before
    cert_fuel _ UMMemoryGrowth.outcome_memory_growth ltac:(intros; assumption)
    Hprefix Hbatch) as [last [cost Hboth]].
  exists last, before, cost. exact Hboth.
Qed.
