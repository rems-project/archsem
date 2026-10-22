(******************************************************************************)
(* Successful promise-first executions with complete certification searches   *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent
  PromiseFirstExecutionCurrent PromiseFirstVMExecutionCurrent PromiseFirstSailCertification
  PromiseFirstSailSerialization PromiseFirstSailScheduling.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Lemma execution_bind_ext {St E A B} (e : Exec.t St E A)
    (k k' : A → Exec.t St E B) st :
  (∀ mid a, Exec.elem_of_results (mid, a) (e st) → k a mid = k' a mid) →
  (e ≫= k) st = (e ≫= k') st.
Proof.
  intro H. unfold mbind, Exec.mbind_inst.
  unfold mbind, Exec.res_mbind_inst.
  apply f_equal. apply List.map_ext_in. intros [mid a] Hin. apply H.
  apply list_elem_of_In. exact Hin.
Qed.

Section Saturation.
Context (prom : Promising.Model) (isem : iMon ()) {n : nat}
  (term : terminationCondition n) (tid : fin n) (imem : memoryMap).
Local Notation ppState :=
  (list prom.(Promising.mEvent) *
    PPState.t prom.(Promising.tState) prom.(Promising.mEvent) prom.(Promising.iis))%type.

(** Once no branch ends in OutOfFuel, larger budgets give exactly the same
    successes and errors. This includes discarded branches and requires no
    syntactic restriction on the instruction semantics. *)
Lemma completed_search_fuel_irrelevant fuel fuel' base (st : ppState) :
  fuel ≤ fuel' →
  (∀ next, ¬ Exec.elem_of_results (next, CPState.OutOfFuel)
    (CPState.run_to_termination isem prom term tid imem fuel base st)) →
  CPState.run_to_termination isem prom term tid imem fuel base st =
  CPState.run_to_termination isem prom term tid imem fuel' base st.
Proof.
  revert fuel' st.
  induction fuel as [|fuel IH]; intros [|fuel'] [proms [ts mem iis]] Hfuel Hcomplete;
    try lia; [reflexivity| |].
  all: cbn [CPState.run_to_termination] in Hcomplete |- *.
  all: apply execution_bind_ext; intros mid ts0 Hget;
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
  all: cbn -[CPState.terminated_ts] in Hcomplete |- *.
  all: destruct (decide (base < prom.(Promising.tState_min_new_prom_view) ts))
    as [Hstop|Hstop]; [reflexivity|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
    rewrite Hterm; [reflexivity|].
  - exfalso. apply (Hcomplete (proms, PPState.Make ts mem iis)).
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn -[CPState.terminated_ts]. rewrite decide_False by exact Hstop.
    rewrite Hterm.
    apply Exec.elem_of_mret.
  - apply execution_bind_ext. intros reset [] Hreset.
    apply execution_bind_ext. intros after [] Hinst.
    apply IH; [lia|]. intros next Hout. apply (Hcomplete next).
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn -[CPState.terminated_ts]. rewrite decide_False by exact Hstop.
    rewrite Hterm.
    eapply Exec.elem_of_bind_intro; [exact Hreset|].
    eapply Exec.elem_of_bind_intro; [exact Hinst|exact Hout].
Qed.

Lemma complete_enumeration_fuel_irrelevant fuel fuel' ts mem :
  fuel ≤ fuel' →
  (CPState.enumerate_results isem prom term tid imem fuel ts mem)
    .(CPState.out_of_fuel prom) = false →
  CPState.enumerate_results isem prom term tid imem fuel ts mem =
  CPState.enumerate_results isem prom term tid imem fuel' ts mem.
Proof.
  intros Hfuel Hcomplete. unfold CPState.enumerate_results in *.
  rewrite (completed_search_fuel_irrelevant fuel fuel' (length mem)
    ([], PPState.Make ts mem prom.(Promising.iis_init)) Hfuel); [reflexivity|].
  intros next Hout. cbn in Hcomplete.
  apply bool_decide_eq_false in Hcomplete. apply Hcomplete.
  exists CPState.OutOfFuel. split; [|exact I].
  apply list_elem_of_fmap. exists (next, CPState.OutOfFuel).
  split; [reflexivity|exact Hout].
Qed.
End Saturation.

Section CompleteExecution.
Context (prom : Promising.Model) (nondet : bool) {n : nat}
  (term : terminationCondition n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t prom.(Promising.tState) prom.(Promising.mEvent) n).
Local Notation final := ({s & archState.is_terminated term s}).

(** Completeness is checked at the budget actually used by the runner. It is
    not required at every natural-number budget, in particular at fuel zero. *)
Definition CertificationCompleteAt (fuel : nat) (st : state) : Prop :=
  ∀ tid, (CPState.enumerate_results isem prom term tid (PState.initmem st)
    fuel (PState.tstate tid st) (PState.events st)).(CPState.out_of_fuel prom) = false.

Lemma certification_complete_more_fuel fuel fuel' st :
  fuel ≤ fuel' → CertificationCompleteAt fuel st → CertificationCompleteAt fuel' st.
Proof.
  intros Hfuel Hcomplete tid.
  rewrite <- (complete_enumeration_fuel_irrelevant prom isem term tid
    (PState.initmem st) fuel fuel' (PState.tstate tid st) (PState.events st)
    Hfuel (Hcomplete tid)).
  apply Hcomplete.
Qed.

Lemma complete_transition_fuel_irrelevant fuel fuel' st :
  fuel ≤ fuel' → CertificationCompleteAt fuel st →
  CPState.run_transition_promise_first isem prom term fuel st =
  CPState.run_transition_promise_first isem prom term fuel' st.
Proof.
  intros Hfuel Hcomplete. unfold CPState.run_transition_promise_first.
  apply execution_bind_ext. intros mid st0 Hget.
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  assert (Henum : promise_first_execution_results isem term fuel st =
    promise_first_execution_results isem term fuel' st).
  { apply vec_eq. intro tid. rewrite !promise_first_execution_results_lookup.
    apply complete_enumeration_fuel_irrelevant; [exact Hfuel|apply Hcomplete]. }
  fold (promise_first_execution_results isem term fuel st).
  fold (promise_first_execution_results isem term fuel' st).
  rewrite Henum. reflexivity.
Qed.

(** A witness for an actual successful run, recording that its certification
    searches do not return OutOfFuel. Initialization is handled by the caller.
    Failed/discarded alternative runner paths are outside this witness. *)
Inductive CompletePromiseFirstExecution : nat → state → state → final → Prop :=
| complete_execution_final fuel st returned fsig :
    CertificationCompleteAt (S fuel) st →
    Exec.elem_of_results (returned, Some fsig)
      (CPState.run_transition_promise_first isem prom term (S fuel) st) →
    CompletePromiseFirstExecution (S fuel) st returned fsig
| complete_execution_promise fuel st next returned fsig :
    CertificationCompleteAt (S fuel) st →
    Exec.elem_of_results (next, None)
      (CPState.run_transition_promise_first isem prom term (S fuel) st) →
    CompletePromiseFirstExecution fuel next returned fsig →
    CompletePromiseFirstExecution (S fuel) st returned fsig.

(** No certification search reached with this concrete runner budget reports
    OutOfFuel. Later states use the runner's decreasing budget. *)
Fixpoint PromiseFirstSearchesComplete (fuel : nat) (st : state) : Prop :=
  match fuel with
  | 0 => True
  | S fuel => CertificationCompleteAt (S fuel) st ∧
      ∀ next, Exec.elem_of_results (next, None)
        (CPState.run_transition_promise_first isem prom term (S fuel) st) →
        PromiseFirstSearchesComplete fuel next
  end.

Lemma successful_run_complete initMs fuel st returned fsig :
  PromiseFirstSearchesComplete fuel st →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs st) →
  CompletePromiseFirstExecution fuel st returned fsig.
Proof.
  revert st. induction fuel as [|fuel IH]; intros st Hcomplete Hrun.
  - cbn [opModel.run] in Hrun.
    change ((returned, fsig) ∈ []) in Hrun. inversion Hrun.
  - destruct Hcomplete as [Hcomplete Htail].
    cbn [opModel.run] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [next [res [Hstep Hrun]]].
    destruct res as [final|].
    + apply Exec.elem_of_mret_inv in Hrun as [-> ->].
      eapply complete_execution_final; eassumption.
    + eapply complete_execution_promise; [exact Hcomplete|exact Hstep|].
      apply IH; [apply Htail, Hstep|exact Hrun].
Qed.

Lemma complete_execution_is_run initMs fuel st returned fsig :
  CompletePromiseFirstExecution fuel st returned fsig →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs st).
Proof.
  intro Hrun. induction Hrun; cbn [opModel.run].
  - eapply Exec.elem_of_bind_intro; [eassumption|apply Exec.elem_of_mret].
  - eapply Exec.elem_of_bind_intro; eassumption.
Qed.

Lemma complete_promise_step_stable fuel st next :
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  FilterRetainsMembership prom →
  CertificationCompleteAt fuel st →
  Exec.elem_of_results (next, None)
    (CPState.run_transition_promise_first isem prom term fuel st) →
  StableCertifiedPromiseStep prom nondet term st next.
Proof.
  intros Hsubset Hfilter Hcomplete Hstep.
  destruct (run_transition_promise_first_none_inv isem term fuel st next Hstep)
    as [tid [ev [nst [Hcandidate [Hpromise Hnext]]]]].
  subst nst. rewrite promise_first_execution_results_lookup in Hcandidate.
  exists tid, ev. split; [|exact Hpromise].
  eapply fully_explored_candidate_is_stable; [|exact Hfilter|apply Hcomplete|exact Hcandidate].
  intros. eapply Hsubset; eassumption.
Qed.

(** This is the promise-first-to-direct direction for the concrete runners.
    It preserves the architectural final result and constructs one decreasing
    direct-runner budget. No execution transformation is assumed. *)
Theorem complete_execution_sound initMs fuel st returned fsig :
  OutcomeMemoryGrowth prom →
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  FilterRetainsMembership prom →
  CompletePromiseFirstExecution fuel st returned fsig →
  ∃ final cost, ∀ direct_fuel, cost < direct_fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel isem prom n) direct_fuel term initMs st).
Proof.
  intros Hgrowth Hsubset Hfilter Hrun.
  induction Hrun as [fuel st returned fsig Hcomplete Hstep|
    fuel st next returned fsig Hcomplete Hstep Htail IH].
  - destruct (sail_final_batch_to_direct_run prom nondet term initMs (S fuel)
      st returned fsig Hgrowth Hstep) as [final [cost [_ Hdirect]]].
    exists final, cost. exact Hdirect.
  - destruct IH as [final [cost Hdirect]].
    pose proof (complete_promise_step_stable (S fuel) st next
      Hsubset Hfilter Hcomplete Hstep) as Hstable.
    destruct (stable_promise_step_fuel prom nondet term st next Hsubset Hstable)
      as [threshold Hcert].
    exists final, (Nat.max threshold (S cost)).
    intros [|direct_fuel] Hfuel; [lia|]. cbn [opModel.run].
    eapply Exec.elem_of_bind_intro.
    + apply Hcert. lia.
    + apply Hdirect. lia.
Qed.
End CompleteExecution.

(** The no-exhaustion condition applies to the chosen top-level fuel and the
    states explored below it. Failed initialization has no final results. *)
Definition PromiseFirstSearchesCompleteFromInitial prom nondet {n}
    (term : terminationCondition n) initMs fuel : Prop :=
  ∀ initPs, PState.from_archState prom initMs = Ok initPs →
    PromiseFirstSearchesComplete prom nondet term fuel initPs.

Theorem complete_promise_first_final_sound prom nondet {n}
    (term : terminationCondition n) initMs fuel fs (pt : archState.is_terminated term fs) :
  OutcomeMemoryGrowth prom →
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  FilterRetainsMembership prom →
  PromiseFirstSearchesCompleteFromInitial prom nondet term initMs fuel →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc_pf prom (sail_tiny_arm_sem nondet) fuel n term initMs →
  ∃ cost, ∀ direct_fuel, cost < direct_fuel →
    ∃ pt', archModel.Res.FinalState fs pt' ∈
      Promising_to_Modelc prom (sail_tiny_arm_sem nondet) direct_fuel n term initMs.
Proof.
  intros Hgrowth Hsubset Hfilter Hcomplete Hfinal.
  destruct (promise_first_final_state_inv (sail_tiny_arm_sem nondet)
    term initMs fuel fs pt Hfinal)
    as [initPs [Hinit [returned [[fs' pt'] [Hrun Hfs]]]]].
  cbn in Hfs. subst fs'.
  pose proof (successful_run_complete prom nondet term initMs fuel initPs
    returned _ (Hcomplete initPs Hinit) Hrun) as Hcompleted.
  destruct (complete_execution_sound prom nondet term initMs fuel initPs
    returned _ Hgrowth Hsubset Hfilter Hcompleted) as [last [cost Hdirect]].
  exists cost. intros direct_fuel Hfuel. exists pt'.
  eapply direct_final_state_intro; [exact Hinit|apply Hdirect, Hfuel].
Qed.

Corollary UMSail_complete_promise_first_final_sound nondet {n}
    (term : terminationCondition n) initMs fuel fs (pt : archState.is_terminated term fs) :
  PromiseFirstSearchesCompleteFromInitial UMPromising nondet term initMs fuel →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc_pf UMPromising (sail_tiny_arm_sem nondet) fuel n term initMs →
  ∃ cost, ∀ direct_fuel, cost < direct_fuel →
    ∃ pt', archModel.Res.FinalState fs pt' ∈
      Promising_to_Modelc UMPromising (sail_tiny_arm_sem nondet) direct_fuel n term initMs.
Proof.
  apply complete_promise_first_final_sound.
  - exact UMMemoryGrowth.outcome_memory_growth.
  - intros. eapply UMPromising_filter_promises_subset; eassumption.
  - exact UM_filter_retains_membership.
Qed.

Corollary VMSail_complete_promise_first_final_sound bbm nondet {n}
    (term : terminationCondition n) initMs fuel fs (pt : archState.is_terminated term fs) :
  PromiseFirstSearchesCompleteFromInitial (VMPromising.VMPromising bbm) nondet
    term initMs fuel →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc_pf (VMPromising.VMPromising bbm)
      (sail_tiny_arm_sem nondet) fuel n term initMs →
  ∃ cost, ∀ direct_fuel, cost < direct_fuel →
    ∃ pt', archModel.Res.FinalState fs pt' ∈
      Promising_to_Modelc (VMPromising.VMPromising bbm)
        (sail_tiny_arm_sem nondet) direct_fuel n term initMs.
Proof.
  apply complete_promise_first_final_sound.
  - exact (VMMemoryGrowth.outcome_memory_growth bbm).
  - intros. eapply VMPromising_filter_promises_subset; eassumption.
  - exact (VM_filter_retains_membership bbm).
Qed.

Theorem UMSail_complete_execution_sound nondet {n} (term : terminationCondition n)
    initMs fuel st returned fsig :
  CompletePromiseFirstExecution UMPromising nondet term fuel st returned fsig →
  ∃ final cost, ∀ direct_fuel, cost < direct_fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) UMPromising n)
        direct_fuel term initMs st).
Proof.
  apply complete_execution_sound.
  - exact UMMemoryGrowth.outcome_memory_growth.
  - intros. eapply UMPromising_filter_promises_subset; eassumption.
  - exact UM_filter_retains_membership.
Qed.

Theorem VMSail_complete_execution_sound bbm nondet {n} (term : terminationCondition n)
    initMs fuel st returned fsig :
  CompletePromiseFirstExecution (VMPromising.VMPromising bbm) nondet term
    fuel st returned fsig →
  ∃ final cost, ∀ direct_fuel, cost < direct_fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet)
        (VMPromising.VMPromising bbm) n) direct_fuel term initMs st).
Proof.
  apply complete_execution_sound.
  - exact (VMMemoryGrowth.outcome_memory_growth bbm).
  - intros. eapply VMPromising_filter_promises_subset; eassumption.
  - exact (VM_filter_retains_membership bbm).
Qed.
