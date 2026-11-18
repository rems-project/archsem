(******************************************************************************)
(* General VM final-state normalization for the direct and uncached runners  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstConcreteCurrent
  PromiseFirstSailCurrent PromiseFirstSailCertification PromiseFirstSailScheduling
  PromiseFirstSailSerialization PromiseFirstVMExecutionCurrent PromiseFirstSailVMNormalization
  PromiseFirstSailVMCreatingWalk PromiseFirstSailVMWalkShape
  PromiseFirstSailVMWalkShapeReachable PromiseFirstSailVMSwapReplay.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module VMFinal.
Import VMPromising VMNormalization.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

Section Final.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).
Local Notation prom := (VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t TState.t Ev.t n).

Theorem instruction_replay : VMInstructionPromiseReplay bbm nondet term initMs code.
Proof.
  apply (VMCreatingWalk.instruction_promise_replay_walks bbm nondet term initMs code
    (@VMWalkShape.CShape n) (VMWalkShapeReachable.cshape_invariant bbm nondet term initMs));
    [apply VMWalkShapeReachable.cshape_start|apply VMWalkShapeReachable.cshape_start_own].
Qed.

(** Each promise step chooses its own finite certification budget. This
    trace theorem covers fresh instruction events and unreduced promises;
    final validation includes BBM when enabled. It has no search-completeness
    premise. The runner theorem below then arranges a single decreasing fuel budget. *)
Theorem mixed_normalization (start final : state) fs :
  VMSailNoSelfModifying bbm nondet term initMs code →
  PromiseFirstReachable prom isem term initMs true start →
  rtc (Mixed bbm nondet term) start final → FinalResult bbm term final fs →
  ∃ before final', PromiseFirstReachable prom isem term initMs true before ∧
    rtc (Fixed bbm nondet term) before final' ∧ FinalResult bbm term final' fs.
Proof.
  apply (VMSail_full_mixed_normalization bbm nondet term initMs code instruction_replay),
    VMSwapReplay.replay.
Qed.

Definition MixedFinal (fs : archState n) : Prop :=
  ∃ init final, PState.from_archState prom initMs = Ok init ∧
    rtc (Mixed bbm nondet term) init final ∧ FinalResult bbm term final fs.

Definition PromiseFirstFinal (fs : archState n) : Prop :=
  ∃ before final, PromiseFirstReachable prom isem term initMs true before ∧
    rtc (Fixed bbm nondet term) before final ∧ FinalResult bbm term final fs.

Theorem trace_final_state_equiv :
  VMSailNoSelfModifying bbm nondet term initMs code →
  ∀ fs, MixedFinal fs ↔ PromiseFirstFinal fs.
Proof.
  intros Hsafe fs. split.
  - intros (init & final & Hinit & Htrace & Hfinal).
    eapply mixed_normalization; [exact Hsafe|apply PromiseFirstReachable_init; exact Hinit|
      exact Htrace|exact Hfinal].
  - intros (before & final & Hbefore & Hsuffix & Hfinal).
    destruct (reachable_prom_trace bbm nondet term initMs before Hbefore)
      as (init & Hinit & Hprefix).
    exists init, final. split; [exact Hinit|]. split; [|exact Hfinal].
    eapply rtc_trans with (y := before); [|apply fixed_rtc_mixed, Hsuffix].
    clear -Hprefix. induction Hprefix; [apply rtc_refl|].
    eapply rtc_l; [right; apply promstep_raw; exact H|exact IHHprefix].
Qed.

Lemma promise_first_run_trace fuel (start returned : state) fsig :
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf_uncached isem prom n) fuel term initMs start) →
  ∃ final, rtc (FMixed bbm nondet term) start final ∧
    FinalResult bbm term final (projT1 fsig).
Proof.
  revert start. induction fuel as [|fuel IH]; intros start Hrun.
  - cbn [opModel.run] in Hrun. change ((returned, fsig) ∈ []) in Hrun. inversion Hrun.
  - cbn [opModel.run] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as (next & res & Hstep & Htail).
    destruct res as [fsig'|].
    + apply Exec.elem_of_mret_inv in Htail as [Hreturned Hsig]. subst next fsig'.
      destruct (sail_final_batch_to_direct_run prom nondet term initMs (S fuel)
        start returned fsig (VMMemoryGrowth.outcome_memory_growth bbm) Hstep)
        as (final & cost & Htrace & Hdirect).
      destruct (direct_run_mixed_trace bbm nondet term initMs (S cost) start final fsig
        (Hdirect (S cost) ltac:(lia))) as (last & pt & Hmixed & Hvalid & Hsig).
      pose proof (validate_final_preserves_state prom last last final Hvalid) as Heq.
      subst last. exists final. split.
      * clear -Htrace. induction Htrace; [apply rtc_refl|].
        eapply rtc_l; [left; exact H|exact IHHtrace].
      * exists pt. split; [exact Hvalid|subst fsig; reflexivity].
    + destruct (IH next Htail) as (final & Htrace & Hfinal).
      exists final. split; [|exact Hfinal].
      eapply rtc_l; [right; exists (S fuel); exact Hstep|exact Htrace].
Qed.

(** Persistence is needed only for candidates whose emission admits a valid
    final continuation. Unrelated infinite certification branches may keep
    reporting OutOfFuel; unsuccessful prefixes are outside this condition. *)
Definition CompletingCandidatesStable : Prop :=
  ∀ before next fuel tid ev,
    PromiseFirstReachable prom isem term initMs true before →
    ev ∈ (CPState.enumerate_results_filtered isem prom term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.promises prom) →
    PState.promise prom ev before = Ok next →
    (∃ final fs, rtc (FMixed bbm nondet term) next final ∧ FinalResult bbm term final fs) →
    StablePromiseCandidate prom nondet term tid (PState.initmem before)
      (PState.tstate tid before) (PState.events before) ev.

Lemma completing_candidates_stable : CompletingCandidatesStable.
Proof.
  intros before next budget tid ev _ Hcandidate _ _.
  eapply enumerated_candidate_is_stable; [|apply VM_filter_retains_membership|exact Hcandidate].
  intros. eapply VMPromising_filter_promises_subset; eassumption.
Qed.

Theorem runner_final_state_equiv :
  VMSailNoSelfModifying bbm nondet term initMs code →
  VMPromisingFinalStateEquiv bbm isem term initMs.
Proof.
  intros Hsafe fs. pose proof completing_candidates_stable as Hstable. split.
  - intros (fuel & pt & Hfinal).
    destruct (direct_final_state_inv (prom := prom) isem term initMs fuel fs pt Hfinal)
      as (init & Hinit & returned & fsig & Hrun & Hfs).
    destruct (VMSail_direct_to_promise_first_or_truncated bbm nondet term initMs code
      instruction_replay fuel init returned fsig (VMSwapReplay.replay bbm nondet term initMs code)
      Hsafe Hinit Hrun) as [(before & cost & [fs' pt'] & Hpf & Heq)|Hbad].
    + cbn in Heq. rewrite Hfs in Heq. subst fs'. exists (S cost), pt'.
      eapply (promise_first_final_state_intro (prom := prom)); [exact Hinit|apply Hpf; lia].
    + destruct Hbad as (before & next & budget & tid & ev & Hreach & Hcandidate &
        Hpromise & Hcont & Hunstable & Hout).
      exfalso. apply Hunstable. eapply Hstable; [exact Hreach|exact Hcandidate|exact Hpromise|].
      destruct Hcont as (final & Htrace & Hvalid). exists final, (projT1 fsig). auto.
  - intros (fuel & pt & Hfinal).
    destruct (promise_first_final_state_inv (prom := prom) isem term initMs fuel fs pt Hfinal)
      as (init & Hinit & returned & fsig & Hrun & Hfs).
    destruct (VMSail_promise_first_direct_or_unstable bbm nondet term initMs fuel init returned
      fsig Hinit Hrun) as [(final & cost & Hdirect)|Hbad].
    + destruct fsig as [fs' pt']. cbn in Hfs. subst fs'. exists (S cost), pt'.
      eapply (direct_final_state_intro (prom := prom)); [exact Hinit|apply Hdirect; lia].
    + destruct Hbad as (before & next & budget & tid & ev & proms & ppst & Hreach &
        Hcandidate & Hpromise & Hunstable & Hev & Hcert & Htail).
      exfalso. apply Hunstable. eapply Hstable; [exact Hreach|exact Hcandidate|exact Hpromise|].
      destruct (promise_first_run_trace budget next returned fsig Htail)
        as (final & Htrace & Hvalid). exists final, (projT1 fsig). auto.
Qed.
End Final.
Theorem promise_first_normalization : VMSailPromiseFirstClaim.
Proof. exact (@runner_final_state_equiv). Qed.
End VMFinal.
