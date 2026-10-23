(******************************************************************************)
(* An actual Sail store inhabiting the direct fulfillment execution witness  *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstExecutionCurrent
  PromiseFirstSailCertification PromiseFirstSailScheduling PromiseFirstSailNoFuel
  PromiseFirstSailInterleaving PromiseFirstSailFinalization PromiseFirstSailDirect.

Open Scope stdpp.
Open Scope bv.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.

Module UMSailStore.
Definition regs : registerMap :=
  ∅ |> reg_insert _PC 0x3000 |> reg_insert R0 0 |> reg_insert R1 42
    |> reg_insert SCTLR_EL1 0 |> reg_insert CurrentEL 1.
Definition imem : memoryMap := ∅ |> mem_insert 0x3000 4 0xf9000001.
Definition initial : archState 1 :=
  {| archState.regs := [# regs]; archState.memory := imem;
     archState.address_space := PAS_NonSecure |}.
Definition term : terminationCondition 1 := [# [0x3004]].
Definition isem := sail_tiny_arm_sem false.
Definition event := Msg.make 0 0 8 42.
Definition init_ps : PState.t UMPromising.TState.t Msg.t 1 :=
  PState.Make [# UMPromising.TState.init imem regs] imem [].
Definition promised :=
  match PState.promise UMPromising event init_ps with Ok st => st | Error _ => init_ps end.
Definition final :=
  match Exec.results (PState.run_tid isem UMPromising 0%fin promised) with
  | (st, ()) :: _ => st
  | [] => promised
  end.

Lemma initialization : PState.from_archState UMPromising initial = Ok init_ps.
Proof. reflexivity. Qed.

Lemma promise_succeeds : PState.promise UMPromising event init_ps = Ok promised.
Proof.
  assert (Hok : (match PState.promise UMPromising event init_ps with
    | Ok _ => true | Error _ => false end) = true) by (vm_compute; reflexivity).
  unfold promised. destruct (PState.promise UMPromising event init_ps);
    [reflexivity|discriminate].
Qed.

Lemma initial_certification_complete : CertificationCompleteAt UMPromising false term 1%nat init_ps.
Proof.
  intro tid. inv_fin tid; [vm_compute; reflexivity|intro tid; inv_fin tid].
Qed.

Lemma initial_candidate : event ∈
  (CPState.enumerate_results isem UMPromising term 0%fin imem 1
    (PState.tstate 0%fin init_ps) []).(CPState.promises UMPromising).
Proof.
  assert (Hlist : (CPState.enumerate_results isem UMPromising term 0%fin imem 1
    (PState.tstate 0%fin init_ps) []).(CPState.promises UMPromising) = [event]).
  { vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. }
  rewrite Hlist. left; reflexivity.
Qed.

Lemma initial_promise_step : Exec.elem_of_results (promised, None)
  (CPState.run_transition_promise_first isem UMPromising term 1 init_ps).
Proof.
  eapply (run_transition_promise_first_none_intro (prom := UMPromising))
    with (tid := 0%fin) (ev := event) (nst := promised).
  - rewrite promise_first_execution_results_lookup. exact initial_candidate.
  - exact promise_succeeds.
  - reflexivity.
Qed.

Lemma instruction_result : Exec.elem_of_results (final, ())
  (PState.run_tid isem UMPromising 0%fin promised).
Proof.
  assert (Hcount : length (Exec.results (PState.run_tid isem UMPromising 0%fin promised)) = 1%nat)
    by (vm_compute; reflexivity).
  unfold final, Exec.elem_of_results.
  destruct (Exec.results (PState.run_tid isem UMPromising 0%fin promised))
    as [|[st []] rest]; [discriminate|left; reflexivity].
Qed.

Lemma instruction_fulfills : FixedHistoryInstructionStep false term promised final.
Proof.
  split.
  - exists 0%fin. split; [vm_compute; reflexivity|exact instruction_result].
  - vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
Qed.

Lemma final_view_bound : UMFinalViewBound final.
Proof.
  intro tid. inv_fin tid; [vm_compute; lia|intro tid; inv_fin tid].
Qed.

Lemma final_terminated : CPState.terminated UMPromising term final.
Proof. vm_compute. exact I. Qed.

Lemma final_valid : Exec.elem_of_results (final, ())
  (CPState.validate_final UMPromising final final).
Proof.
  assert (Hnone : CPState.nopromises UMPromising final) by (vm_compute; exact I).
  assert (Hvalid : CPState.check_valid_end UMPromising final = []) by (vm_compute; reflexivity).
  unfold CPState.validate_final. rewrite Hvalid.
  destruct (Exec.elem_of_guard_discard (E := string) final Hnone) as [pt Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|apply Exec.elem_of_mret].
Qed.

Definition result := CPState.to_final_archState
  (CPState.make_final UMPromising term final final_terminated).

(** Promise the store, execute it by fulfillment, then validate the endpoint.
    The witness uses budgets 3, 2, and 1 of the actual direct runner. *)
Theorem complete_fulfillment_execution :
  CompleteFulfillmentDirectExecution false term 3%nat init_ps final result.
Proof.
  eapply fulfillment_execution_promise.
  - exact (certification_complete_more_fuel UMPromising false term 1%nat 3%nat
      init_ps ltac:(lia) initial_certification_complete).
  - rewrite <- (complete_transition_fuel_irrelevant UMPromising false term 1%nat 3%nat
      init_ps ltac:(lia) initial_certification_complete). exact initial_promise_step.
  - eapply fulfillment_execution_instruction; [exact instruction_fulfills|].
    apply fulfillment_execution_final; [exact final_view_bound|].
    apply (run_transition_some_intro (prom := UMPromising)). exact final_valid.
Qed.

Theorem common_final_result : ∃ direct_returned cost, ∀ fuel, (cost < fuel)%nat →
  Exec.elem_of_results (direct_returned, result)
    (opModel.run (@CPState.opmodel isem UMPromising 1) fuel term initial init_ps) ∧
  Exec.elem_of_results (promised, result)
    (opModel.run (@CPState.opmodel_pf isem UMPromising 1) fuel term initial init_ps).
Proof.
  destruct (UMSail_fixed_history_final_batch false term promised final final final_terminated
    (rtc_once _ _ instruction_fulfills) final_view_bound final_valid) as [cert_fuel Hbatch].
  eapply stable_prefix_common_fuel; [exact UMMemoryGrowth.outcome_memory_growth|intros; assumption| |exact Hbatch].
  apply rtc_once. eapply complete_promise_step_stable;
    [intros; assumption|exact UM_filter_retains_membership|
     exact initial_certification_complete|exact initial_promise_step].
Qed.
End UMSailStore.
