(******************************************************************************)
(* Two actual Sail threads: a fresh store followed by a promised store        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstSailCertification
  PromiseFirstSailScheduling PromiseFirstSailNoFuel PromiseFirstSailSerialization
  PromiseFirstSailInterleaving PromiseFirstSailFinalization.

Open Scope stdpp.
Open Scope bv.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.

Module UMSailTwoThread.
Local Lemma register_maps_equal (xs ys : registerMap) :
  (∀ r, bool_decide (xs !d! r = ys !d! r) = true) → xs = ys.
Proof. intro H. apply dmap_eq. intro r. exact (bool_decide_eq_true_1 _ (H r)). Qed.
Definition regs (value : bv 64) : registerMap :=
  ∅ |> reg_insert _PC 0x3000 |> reg_insert R0 0 |> reg_insert R1 value
    |> reg_insert SCTLR_EL1 0 |> reg_insert CurrentEL 1.
Definition imem : memoryMap := ∅ |> mem_insert 0x3000 4 0xf9000001.
Definition initial : archState 2 :=
  {| archState.regs := [# regs 42; regs 43]; archState.memory := imem;
     archState.address_space := PAS_NonSecure |}.
Definition term : terminationCondition 2 := [# [0x3004]; [0x3004]].
Definition isem := sail_tiny_arm_sem false.
Definition event0 := Msg.make 0 0 8 42.
Definition event1 := Msg.make 1 0 8 43.
Definition init_ps : PState.t TState.t Msg.t 2 :=
  PState.Make [# TState.init imem (regs 42); TState.init imem (regs 43)] imem [].
Definition issue ev (st : PState.t TState.t Msg.t 2) :=
  match PState.promise UMPromising ev st with Ok next => next | Error _ => st end.
Definition execute tid (st : PState.t TState.t Msg.t 2) :=
  match Exec.results (PState.run_tid isem UMPromising tid st) with
  | (next, ()) :: _ => next | [] => st end.
Definition fresh0 := execute 0%fin init_ps.
Definition mixed1 := issue event1 fresh0.
Definition final := execute 1%fin mixed1.
Definition promised0 := issue event0 init_ps.
Definition promised1 := issue event1 promised0.
Definition fulfilled0 := execute 0%fin promised1.
Definition fulfilled1 := execute 1%fin fulfilled0.

Lemma initialization : PState.from_archState UMPromising initial = Ok init_ps.
Proof. reflexivity. Qed.

Local Lemma issue_success ev st :
  (match PState.promise UMPromising ev st with Ok _ => true | Error _ => false end) = true →
  PState.promise UMPromising ev st = Ok (issue ev st).
Proof. unfold issue. destruct (PState.promise UMPromising ev st); [reflexivity|discriminate]. Qed.
Local Lemma execute_success tid st :
  length (Exec.results (PState.run_tid isem UMPromising tid st)) = 1%nat →
  Exec.elem_of_results (execute tid st, ()) (PState.run_tid isem UMPromising tid st).
Proof.
  unfold execute, Exec.elem_of_results.
  destruct (Exec.results (PState.run_tid isem UMPromising tid st)) as [|[next []] rest] eqn:Hresults;
    [discriminate|intros; rewrite Hresults; left; reflexivity].
Qed.
Local Ltac compute_equal :=
  vm_compute; repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
Local Ltac complete_two_threads :=
  let tid := fresh "tid" in intro tid; inv_fin tid; [vm_compute; reflexivity|];
  let tid := fresh "tid" in intro tid; inv_fin tid;
    [vm_compute; reflexivity|let tid := fresh "tid" in intro tid; inv_fin tid].

Lemma first_fresh_instruction : InstructionTransition UMPromising false term init_ps fresh0.
Proof.
  exists 0%fin. split; [vm_compute; reflexivity|]. apply execute_success. vm_compute; reflexivity.
Qed.
Lemma last_instruction : InstructionTransition UMPromising false term mixed1 final.
Proof.
  exists 1%fin. split; [vm_compute; reflexivity|]. apply execute_success. vm_compute; reflexivity.
Qed.
Lemma mixed_search_complete : CertificationCompleteAt UMPromising false term 1%nat fresh0.
Proof. complete_two_threads. Qed.
Lemma initial_search_complete : CertificationCompleteAt UMPromising false term 1%nat init_ps.
Proof. complete_two_threads. Qed.
Lemma second_search_complete : CertificationCompleteAt UMPromising false term 1%nat promised0.
Proof. complete_two_threads. Qed.

Local Lemma promise_step tid ev st :
  (CPState.enumerate_results isem UMPromising term tid (PState.initmem st) 1
    (PState.tstate tid st) (PState.events st)).(CPState.promises UMPromising) = [ev] →
  PState.promise UMPromising ev st = Ok (issue ev st) →
  Exec.elem_of_results (issue ev st, None)
    (CPState.run_transition_promise_first isem UMPromising term 1 st).
Proof.
  intros Hlist Hemit. eapply (run_transition_promise_first_none_intro (prom := UMPromising))
    with (tid := tid) (ev := ev) (nst := issue ev st).
  - rewrite promise_first_execution_results_lookup, Hlist. left; reflexivity.
  - exact Hemit.
  - reflexivity.
Qed.
Lemma mixed_promise_step : Exec.elem_of_results (mixed1, None)
  (CPState.run_transition_promise_first isem UMPromising term 1 fresh0).
Proof. apply (promise_step 1%fin event1 fresh0); [compute_equal|apply issue_success; vm_compute; reflexivity]. Qed.
Lemma first_promise_step : Exec.elem_of_results (promised0, None)
  (CPState.run_transition_promise_first isem UMPromising term 1 init_ps).
Proof. apply (promise_step 0%fin event0 init_ps); [compute_equal|apply issue_success; vm_compute; reflexivity]. Qed.
Lemma second_promise_step : Exec.elem_of_results (promised1, None)
  (CPState.run_transition_promise_first isem UMPromising term 1 promised0).
Proof. apply (promise_step 1%fin event1 promised0); [compute_equal|apply issue_success; vm_compute; reflexivity]. Qed.

Local Lemma execute_initial_memory tid st : PState.initmem (execute tid st) = PState.initmem st.
Proof.
  unfold execute.
  destruct (Exec.results (PState.run_tid isem UMPromising tid st)) as [|[next []] rest] eqn:Hresults;
    [reflexivity|].
  assert (Hrun : Exec.elem_of_results (next, ()) (PState.run_tid isem UMPromising tid st)).
  { unfold Exec.elem_of_results. rewrite Hresults. left; reflexivity. }
  destruct (run_tid_decompose UMPromising isem tid st next Hrun) as [ts [mem [iis [_ ->]]]].
  reflexivity.
Qed.
Local Lemma issue_initial_memory ev st : PState.initmem (issue ev st) = PState.initmem st.
Proof.
  unfold issue. destruct (PState.promise UMPromising ev st) as [next|err] eqn:Hpromise; [|reflexivity].
  exact (proj1 (PromiseFirstCurrent.promise_success UMPromising ev st next Hpromise)).
Qed.
Lemma same_architecture : PState.to_archState UMPromising fulfilled1 = PState.to_archState UMPromising final.
Proof.
  unfold PState.to_archState. apply f_equal3.
  - apply f_equal2.
    + transitivity (PState.initmem init_ps).
      * exact (eq_trans (execute_initial_memory 1%fin fulfilled0)
          (eq_trans (execute_initial_memory 0%fin promised1)
            (eq_trans (issue_initial_memory event1 promised0) (issue_initial_memory event0 init_ps)))).
      * symmetry. exact (eq_trans (execute_initial_memory 1%fin mixed1)
          (eq_trans (issue_initial_memory event1 fresh0) (execute_initial_memory 0%fin init_ps))).
    + compute_equal.
  - reflexivity.
  - apply vec_eq. intro tid. inv_fin tid.
    + rewrite vlookup_map, vlookup_map. apply register_maps_equal.
      intros [r|r|r|r]; destruct r; vm_compute; reflexivity.
    + intro tid. inv_fin tid; [|intro tid; inv_fin tid].
      rewrite vlookup_map, vlookup_map. apply register_maps_equal.
      intros [r|r|r|r]; destruct r; vm_compute; reflexivity.
Qed.
Lemma final_terminated : CPState.terminated UMPromising term final.
Proof. vm_compute; exact I. Qed.
Lemma final_view_bound : UMFinalViewBound final.
Proof.
  intro tid. inv_fin tid; [vm_compute; lia|].
  intro tid. inv_fin tid; [vm_compute; lia|intro tid; inv_fin tid].
Qed.
Lemma final_valid : Exec.elem_of_results (final, ()) (CPState.validate_final UMPromising final final).
Proof.
  assert (Hnone : CPState.nopromises UMPromising final) by (vm_compute; exact I).
  assert (Hvalid : CPState.check_valid_end UMPromising final = []) by (vm_compute; reflexivity).
  unfold CPState.validate_final. rewrite Hvalid.
  destruct (Exec.elem_of_guard_discard (E := string) final Hnone) as [pt Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|apply Exec.elem_of_mret].
Qed.
Definition result := CPState.to_final_archState
  (CPState.make_final UMPromising term final final_terminated).

Lemma fulfilled_terminated : CPState.terminated UMPromising term fulfilled1.
Proof. vm_compute; exact I. Qed.
Lemma fulfilled_view_bound : UMFinalViewBound fulfilled1.
Proof.
  intro tid. inv_fin tid; [vm_compute; lia|].
  intro tid. inv_fin tid; [vm_compute; lia|intro tid; inv_fin tid].
Qed.
Lemma fulfilled_valid : Exec.elem_of_results (fulfilled1, ())
  (CPState.validate_final UMPromising fulfilled1 fulfilled1).
Proof.
  assert (Hnone : CPState.nopromises UMPromising fulfilled1) by (vm_compute; exact I).
  assert (Hvalid : CPState.check_valid_end UMPromising fulfilled1 = []) by (vm_compute; reflexivity).
  unfold CPState.validate_final. rewrite Hvalid.
  destruct (Exec.elem_of_guard_discard (E := string) fulfilled1 Hnone) as [pt Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|apply Exec.elem_of_mret].
Qed.
Lemma fulfilled_signature (pt : CPState.terminated UMPromising term fulfilled1) :
  CPState.to_final_archState (CPState.make_final UMPromising term fulfilled1 pt) = result.
Proof.
  unfold result, CPState.to_final_archState, CPState.make_final.
  cbn -[PState.to_archState final fulfilled1].
  generalize (CPState.terminated_to_archState UMPromising term fulfilled1 pt).
  rewrite same_architecture. intro p. f_equal; apply proof_irrelevance.
Qed.

(** Both stores target address zero: thread 0 writes freshly, then thread 1
    promises and fulfills its store. The runner uses budgets 4, 3, 2, 1. *)
Theorem mixed_direct_run : Exec.elem_of_results (final, result)
  (opModel.run (@CPState.opmodel isem UMPromising 2) 4 term initial init_ps).
Proof.
  cbn [opModel.run].
  eapply Exec.elem_of_bind_intro with (st' := fresh0) (a := None).
  - exact (instruction_transition_any_fuel UMPromising false term 4 init_ps fresh0 first_fresh_instruction).
  - eapply Exec.elem_of_bind_intro with (st' := mixed1) (a := None).
    + apply (promise_first_none_to_direct_none (prom := UMPromising)); [intros; assumption|].
      rewrite <- (complete_transition_fuel_irrelevant UMPromising false term 1%nat 3%nat
        fresh0 ltac:(lia) mixed_search_complete). exact mixed_promise_step.
    + eapply Exec.elem_of_bind_intro with (st' := final) (a := None).
      * exact (instruction_transition_any_fuel UMPromising false term 2 mixed1 final last_instruction).
      * eapply Exec.elem_of_bind_intro.
        -- apply (run_transition_some_intro (prom := UMPromising)). exact final_valid.
        -- apply Exec.elem_of_mret.
Qed.

Lemma stable_prefix : rtc (StableCertifiedPromiseStep UMPromising false term) init_ps promised1.
Proof.
  eapply rtc_l with (y := promised0).
  - eapply complete_promise_step_stable;
      [intros; assumption|exact UM_filter_retains_membership|exact initial_search_complete|exact first_promise_step].
  - apply rtc_once. eapply complete_promise_step_stable;
      [intros; assumption|exact UM_filter_retains_membership|exact second_search_complete|exact second_promise_step].
Qed.
Lemma fulfillment_suffix : rtc (FixedHistoryInstructionStep false term) promised1 fulfilled1.
Proof.
  eapply rtc_l with (y := fulfilled0).
  - split.
    + exists 0%fin. split; [vm_compute; reflexivity|]. apply execute_success. vm_compute; reflexivity.
    + compute_equal.
  - apply rtc_once. split.
    + exists 1%fin. split; [vm_compute; reflexivity|]. apply execute_success. vm_compute; reflexivity.
    + compute_equal.
Qed.

(** All selected certification searches are complete by evaluation. Both
    promises can precede both instructions while preserving the architectural result. *)
Theorem mixed_direct_to_promise_first :
  Exec.elem_of_results (final, result)
    (opModel.run (@CPState.opmodel isem UMPromising 2) 4 term initial init_ps) ∧
  ∃ cost, ∀ fuel, (cost < fuel)%nat →
    Exec.elem_of_results (promised1, result)
      (opModel.run (@CPState.opmodel_pf isem UMPromising 2) fuel term initial init_ps).
Proof.
  split; [exact mixed_direct_run|].
  destruct (UMSail_fixed_history_final_batch false term promised1 fulfilled1 fulfilled1 fulfilled_terminated
    fulfillment_suffix fulfilled_view_bound fulfilled_valid) as [cert_fuel Hbatch].
  rewrite fulfilled_signature in Hbatch.
  eapply stable_prefix_promise_first_run; [exact stable_prefix|exact Hbatch].
Qed.
End UMSailTwoThread.
