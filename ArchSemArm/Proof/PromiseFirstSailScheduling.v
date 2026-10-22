(******************************************************************************)
(* Fuel scheduling for sail-tiny-arm promise-first runs *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstExecutionCurrent PromiseFirstVMExecutionCurrent PromiseFirstConcreteCurrent
  PromiseFirstSailCertification PromiseFirstSailSerialization.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Section Scheduling.
Context (prom : Promising.Model) (nondet : bool) {n : nat}
  (term : terminationCondition n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t prom.(Promising.tState) prom.(Promising.mEvent) n).

Definition StableCertifiedPromiseStep (st st' : state) : Prop :=
  ∃ tid ev,
    StablePromiseCandidate prom nondet term tid (PState.initmem st)
      (PState.tstate tid st) (PState.events st) ev ∧
    PState.promise prom ev st = Ok st'.

Lemma final_batch_more_fuel fuel fuel' st returned fsig :
  fuel ≤ fuel' →
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first isem prom term fuel st) →
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first isem prom term fuel' st).
Proof.
  intros Hfuel Hstep.
  destruct (run_transition_promise_first_some_inv isem term fuel st returned fsig Hstep)
    as [targets [final [pt [Hfinal [Hstates [Hvalid Hsig]]]]]].
  subst final. rewrite Hsig.
  eapply run_transition_promise_first_some_intro; [|exact Hvalid].
  apply Exec.elem_of_mchoosel, (proj2 (cprodn_spec _ _)).
  intro tid. rewrite vlookup_map, promise_first_execution_results_lookup.
  specialize (Hstates tid). rewrite promise_first_execution_results_lookup in Hstates.
  eapply final_candidate_more_fuel; eassumption.
Qed.

Lemma stable_promise_first_step_fuel st next :
  StableCertifiedPromiseStep st next →
  ∃ threshold, ∀ fuel, threshold ≤ fuel →
    Exec.elem_of_results (next, None)
      (CPState.run_transition_promise_first isem prom term fuel st).
Proof.
  intros [tid [ev [[threshold Hcandidate] Hpromise]]].
  exists threshold. intros fuel Hfuel.
  eapply run_transition_promise_first_none_intro with (tid := tid) (ev := ev) (nst := next).
  - rewrite promise_first_execution_results_lookup. apply Hcandidate, Hfuel.
  - exact Hpromise.
  - reflexivity.
Qed.

(** The same decreasing runner budget covers certification of every prefix
    step and the final batch. This construction applies to UM and VM. *)
Lemma stable_prefix_promise_first_run initMs st before returned cert_fuel fsig :
  rtc StableCertifiedPromiseStep st before →
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first isem prom term cert_fuel before) →
  ∃ cost, ∀ fuel, cost < fuel →
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs st).
Proof.
  intros Hprefix Hfinal. induction Hprefix as [st|st mid before Hstep Htail IH].
  - exists cert_fuel. intros [|fuel] Hfuel; [lia|]. cbn [opModel.run].
    eapply Exec.elem_of_bind_intro.
    + eapply final_batch_more_fuel; [|exact Hfinal]. lia.
    + apply Exec.elem_of_mret.
  - destruct (IH Hfinal) as [cost Hrun].
    destruct (stable_promise_first_step_fuel st mid Hstep) as [threshold Hcert].
    exists (Nat.max threshold (S cost)). intros [|fuel] Hfuel; [lia|].
    cbn [opModel.run]. eapply Exec.elem_of_bind_intro.
    + apply Hcert. lia.
    + apply Hrun. lia.
Qed.

Lemma stable_promise_step_fuel st st' :
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  StableCertifiedPromiseStep st st' →
  ∃ threshold, ∀ fuel, threshold ≤ fuel →
    Exec.elem_of_results (st', None) (CPState.run_transition isem prom term fuel st).
Proof.
  intros Hfilter [tid [ev [[threshold Hcandidate] Hpromise]]].
  exists threshold. intros fuel Hfuel.
  apply promise_first_none_to_direct_none.
  - intros. eapply Hfilter. eassumption.
  - eapply run_transition_promise_first_none_intro with (tid := tid) (ev := ev) (nst := st').
    + rewrite promise_first_execution_results_lookup. apply Hcandidate, Hfuel.
    + exact Hpromise.
    + reflexivity.
Qed.

(** Each promise step has its own certification threshold. Taking a maximum
    while prepending the steps supplies one decreasing fuel budget for the
    actual runner, including the final instruction suffix. *)
Lemma stable_promise_prefix_run initMs st before final
    (fsig : {s & archState.is_terminated term s}) :
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  rtc StableCertifiedPromiseStep st before →
  ∀ tail_cost,
    (∀ fuel, tail_cost < fuel → Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel isem prom n) fuel term initMs before)) →
    ∃ cost, ∀ fuel, cost < fuel → Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel isem prom n) fuel term initMs st).
Proof.
  intros Hfilter Hsteps. induction Hsteps as [st|st mid before Hstep Hsteps IH];
    intros tail_cost Htail.
  - exists tail_cost. exact Htail.
  - destruct (IH tail_cost Htail) as [cost Hrun].
    destruct (stable_promise_step_fuel st mid Hfilter Hstep) as [threshold Hnone].
    exists (Nat.max threshold (S cost)). intros [|fuel] Hfuel; [lia|].
    cbn [opModel.run]. eapply Exec.elem_of_bind_intro.
    + apply Hnone. lia.
    + apply Hrun. lia.
Qed.

Lemma stable_prefix_final_batch initMs start before returned cert_fuel
    (fsig : {s & archState.is_terminated term s}) :
  OutcomeMemoryGrowth prom →
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  rtc StableCertifiedPromiseStep start before →
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first isem prom term cert_fuel before) →
  ∃ final cost, ∀ fuel, cost < fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel isem prom n) fuel term initMs start).
Proof.
  intros Hgrowth Hfilter Hprefix Hfinal.
  destruct (sail_final_batch_to_direct_run prom nondet term initMs cert_fuel
    before returned fsig Hgrowth Hfinal) as [final [tail_cost [_ Htail]]].
  destruct (stable_promise_prefix_run initMs start before final fsig Hfilter
    Hprefix tail_cost Htail) as [cost Hrun].
  exists final, cost. exact Hrun.
Qed.

(** A single bound suffices for both concrete runners once every selected
    certificate persists. The final architectural result is shared. *)
Lemma stable_prefix_common_fuel initMs start before returned cert_fuel fsig :
  OutcomeMemoryGrowth prom →
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  rtc StableCertifiedPromiseStep start before →
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first isem prom term cert_fuel before) →
  ∃ final cost, ∀ fuel, cost < fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel isem prom n) fuel term initMs start) ∧
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs start).
Proof.
  intros Hgrowth Hfilter Hprefix Hfinal.
  destruct (stable_prefix_final_batch initMs start before returned cert_fuel fsig
    Hgrowth Hfilter Hprefix Hfinal) as [final [direct_cost Hdirect]].
  destruct (stable_prefix_promise_first_run initMs start before returned cert_fuel fsig
    Hprefix Hfinal) as [pf_cost Hpf].
  exists final, (Nat.max direct_cost pf_cost). intros fuel Hfuel.
  split; [apply Hdirect|apply Hpf]; lia.
Qed.

(** This decomposition is unconditional apart from the concrete model laws.
    It preserves the successful final state and realizes the final batch by
    the actual direct runner. Converting the preceding reachability witness
    to one fuel budget still requires stable promise certificates. *)
Lemma sail_success_direct_suffix initMs fuel initPs returned
    (fsig : {s & archState.is_terminated term s}) :
  OutcomeMemoryGrowth prom →
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  PState.from_archState prom initMs = Ok initPs →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs initPs) →
  ∃ before final cost,
    PromiseFirstReachable prom isem term initMs false before ∧
    ∀ direct_fuel, cost < direct_fuel →
      Exec.elem_of_results (final, fsig)
        (opModel.run (@CPState.opmodel isem prom n) direct_fuel term initMs before).
Proof.
  intros Hgrowth Hfilter Hinit Hrun.
  assert (Hinitial : PromiseFirstReachable prom isem term initMs true initPs).
  { apply PromiseFirstReachable_init. exact Hinit. }
  destruct (promise_first_run_final_prefix prom isem term initMs fuel initPs returned fsig
    Hinitial Hrun) as [cert_fuel [before [Hbefore Hstep]]].
  destruct (sail_final_batch_to_direct_run prom nondet term initMs cert_fuel
    before returned fsig Hgrowth Hstep) as [final [cost [_ Hsuffix]]].
  exists before, final, cost. split; [|exact Hsuffix].
  apply promise_first_reachable_to_direct; assumption.
Qed.
End Scheduling.

Corollary VMSail_stable_prefix_common_fuel bbm nondet {n}
    (term : terminationCondition n) initMs start before returned cert_fuel fsig :
  rtc (StableCertifiedPromiseStep (VMPromising.VMPromising bbm) nondet term) start before →
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first (sail_tiny_arm_sem nondet)
      (VMPromising.VMPromising bbm) term cert_fuel before) →
  ∃ final cost, ∀ fuel, cost < fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet)
        (VMPromising.VMPromising bbm) n) fuel term initMs start) ∧
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel_pf (sail_tiny_arm_sem nondet)
        (VMPromising.VMPromising bbm) n) fuel term initMs start).
Proof.
  apply stable_prefix_common_fuel.
  - exact (VMMemoryGrowth.outcome_memory_growth bbm).
  - intros. eapply VMPromising_filter_promises_subset. eassumption.
Qed.

Lemma UMSail_success_direct_suffix nondet {n} (term : terminationCondition n)
    initMs fuel initPs returned fsig :
  PState.from_archState UMPromising initMs = Ok initPs →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf (sail_tiny_arm_sem nondet) UMPromising n)
      fuel term initMs initPs) →
  ∃ before final cost,
    PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs false before ∧
    ∀ direct_fuel, cost < direct_fuel → Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) UMPromising n)
        direct_fuel term initMs before).
Proof.
  apply sail_success_direct_suffix.
  - exact UMMemoryGrowth.outcome_memory_growth.
  - intros. eapply UMPromising_filter_promises_subset. eassumption.
Qed.

Lemma VMSail_success_direct_suffix bbm nondet {n} (term : terminationCondition n)
    initMs fuel initPs returned fsig :
  PState.from_archState (VMPromising.VMPromising bbm) initMs = Ok initPs →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf (sail_tiny_arm_sem nondet)
      (VMPromising.VMPromising bbm) n) fuel term initMs initPs) →
  ∃ before final cost,
    PromiseFirstReachable (VMPromising.VMPromising bbm) (sail_tiny_arm_sem nondet)
      term initMs false before ∧
    ∀ direct_fuel, cost < direct_fuel → Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet)
        (VMPromising.VMPromising bbm) n) direct_fuel term initMs before).
Proof.
  apply sail_success_direct_suffix.
  - exact (VMMemoryGrowth.outcome_memory_growth bbm).
  - intros. eapply VMPromising_filter_promises_subset. eassumption.
Qed.

Local Opaque sail_tiny_arm_sem.

Section FuelObstruction.
Context (prom : Promising.Model) (nondet : bool) {n : nat}
  (term : terminationCondition n) (initMs : archState n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t prom.(Promising.tState) prom.(Promising.mEvent) n).

(** A candidate selected on a successful promise-first continuation which has
    no persistent certificate. The witness records its truncated exploration;
    it does not assert that a direct execution is impossible. *)
Definition UnstablePromiseOnSuccessfulRun (returned : state)
    (fsig : {s & archState.is_terminated term s}) : Prop :=
  ∃ before next fuel tid ev proms ppst,
    PromiseFirstReachable prom isem term initMs true before ∧
    ev ∈ (CPState.enumerate_results isem prom term tid (PState.initmem before)
      (S fuel) (PState.tstate tid before) (PState.events before)).(CPState.promises prom) ∧
    PState.promise prom ev before = Ok next ∧
    ¬ StablePromiseCandidate prom nondet term tid (PState.initmem before)
      (PState.tstate tid before) (PState.events before) ev ∧
    ev ∈ proms ∧
    Exec.elem_of_results ((proms, ppst), CPState.OutOfFuel)
      (CPState.run_to_termination isem prom term tid (PState.initmem before)
        (S fuel) (length (PState.events before))
        ([], PPState.Make (PState.tstate tid before) (PState.events before)
          prom.(Promising.iis_init))) ∧
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs next).

Lemma sail_promise_first_direct_or_unstable fuel (start returned : state)
    (fsig : {s & archState.is_terminated term s}) :
  OutcomeMemoryGrowth prom →
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  FilterRetainsMembership prom →
  PromiseFirstReachable prom isem term initMs true start →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs start) →
  (∃ final cost, ∀ direct_fuel, cost < direct_fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel isem prom n) direct_fuel term initMs start)) ∨
  UnstablePromiseOnSuccessfulRun returned fsig.
Proof.
  intros Hgrowth Hsubset Hfilter. revert start returned fsig.
  induction fuel as [|fuel IH]; intros start returned fsig Hreach Hrun.
  - cbn [opModel.run] in Hrun.
    unfold mthrow, Exec.throw_inst, Exec.res_throw_inst, Exec.elem_of_results in Hrun.
    cbn in Hrun. inversion Hrun.
  - cbn [opModel.run] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [next [res [Hstep Htail]]].
    destruct res as [final_sig|].
    + apply Exec.elem_of_mret_inv in Htail as [Hreturned Hsig]. subst next final_sig.
      left. destruct (sail_final_batch_to_direct_run prom nondet term initMs
        (S fuel) start returned fsig Hgrowth Hstep) as [final [cost [_ Hdirect]]].
      exists final, cost. exact Hdirect.
    + destruct (run_transition_promise_first_none_inv isem term (S fuel)
        start next Hstep) as [tid [ev [nst [Hcandidate [Hpromise Hnext]]]]].
      subst nst. rewrite promise_first_execution_results_lookup in Hcandidate.
      destruct (classic (StablePromiseCandidate prom nondet term tid
        (PState.initmem start) (PState.tstate tid start) (PState.events start) ev))
        as [Hstable|Hunstable].
      * assert (Hnext_reach : PromiseFirstReachable prom isem term initMs true next).
        { eapply PromiseFirstReachable_step with (fuel := S fuel); eassumption. }
        destruct (IH next returned fsig Hnext_reach Htail)
          as [[final [cost Hdirect]]|Hbad]; [|right; exact Hbad].
        left. exists final.
        eapply stable_promise_prefix_run; [exact Hsubset| |exact Hdirect].
        eapply rtc_l; [|apply rtc_refl]. exists tid, ev. split; assumption.
      * destruct (candidate_stable_or_out_of_fuel prom nondet term tid
          (PState.initmem start) (S fuel) (PState.tstate tid start) (PState.events start) ev
          (Hsubset tid (PState.events start)) Hfilter Hcandidate)
          as [Hstable|[proms [ppst [Hev Hcert]]]]; [contradiction|].
        right. exists start, next, fuel, tid, ev, proms, ppst.
        repeat split; assumption.
Qed.
End FuelObstruction.

Lemma UMSail_promise_first_direct_or_unstable nondet {n} (term : terminationCondition n)
    initMs fuel initPs returned fsig :
  PState.from_archState UMPromising initMs = Ok initPs →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf (sail_tiny_arm_sem nondet) UMPromising n)
      fuel term initMs initPs) →
  (∃ final cost, ∀ direct_fuel, cost < direct_fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) UMPromising n)
        direct_fuel term initMs initPs)) ∨
  UnstablePromiseOnSuccessfulRun UMPromising nondet term initMs returned fsig.
Proof.
  intros Hinit Hrun. eapply sail_promise_first_direct_or_unstable.
  - exact UMMemoryGrowth.outcome_memory_growth.
  - intros. eapply UMPromising_filter_promises_subset. eassumption.
  - exact UM_filter_retains_membership.
  - apply PromiseFirstReachable_init. exact Hinit.
  - exact Hrun.
Qed.

Lemma VMSail_promise_first_direct_or_unstable bbm nondet {n} (term : terminationCondition n)
    initMs fuel initPs returned fsig :
  PState.from_archState (VMPromising.VMPromising bbm) initMs = Ok initPs →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf (sail_tiny_arm_sem nondet)
      (VMPromising.VMPromising bbm) n) fuel term initMs initPs) →
  (∃ final cost, ∀ direct_fuel, cost < direct_fuel →
    Exec.elem_of_results (final, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet)
        (VMPromising.VMPromising bbm) n) direct_fuel term initMs initPs)) ∨
  UnstablePromiseOnSuccessfulRun (VMPromising.VMPromising bbm) nondet term initMs returned fsig.
Proof.
  intros Hinit Hrun. eapply sail_promise_first_direct_or_unstable.
  - exact (VMMemoryGrowth.outcome_memory_growth bbm).
  - intros. eapply VMPromising_filter_promises_subset. eassumption.
  - exact (VM_filter_retains_membership bbm).
  - apply PromiseFirstReachable_init. exact Hinit.
  - exact Hrun.
Qed.
