(******************************************************************************)
(* Certifying actual Sail VM instruction suffixes at a fixed shared history  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstExecutionCurrent PromiseFirstVMExecutionCurrent
  PromiseFirstSailCertification PromiseFirstSailSerialization
  PromiseFirstSailScheduling PromiseFirstSailInterleaving.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Typeclasses Transparent VMPromising.VMPromising Promising.mEvent
  Promising.tState Promising.iis VMPromising.Memory.t.

Module VMFinalCertification.
Import VMPromising.

Lemma instruction_memory_suffix {n A} (tid : fin n) imem (mon : iMon A) ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' n tid imem) mon ppst) →
  ∃ extra, PPState.mem ppst' = (extra ++ PPState.mem ppst)%list.
Proof.
  revert ppst ppst' ret. induction mon as [a|call k IH]; intros ppst ppst' ret Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exists []; reflexivity.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (IH r mid ppst' ret Htail) as [rest Hrest].
      destruct (VMMemoryGrowth.outcome_memory_growth false n tid imem out ppst mid r pre Hout)
        as [Hsame|[extra [_ [_ [Hnew _]]]]].
      * exists rest. rewrite Hrest, Hsame. reflexivity.
      * exists (rest ++ extra)%list. rewrite Hrest, Hnew, app_assoc. reflexivity.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

Lemma collect_unchanged_instruction bbm {n A} (tid : fin n) imem (mon : iMon A)
    proms ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' n tid imem) mon ppst) →
  PPState.mem ppst' = PPState.mem ppst →
  Exec.elem_of_results ((proms, ppst'), ret)
    (cinterp (CPState.run_outcome_with_promise (VMPromising bbm) tid imem
      (length (PPState.mem ppst))) mon (proms, ppst)).
Proof.
  revert proms ppst ppst' ret.
  induction mon as [a|call k IH]; intros proms ppst ppst' ret Hrun Hmem.
  - cbn in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->]. apply Exec.elem_of_mret.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (instruction_memory_suffix tid imem (k r) mid ppst' ret Htail)
        as [extra Hsuffix].
      assert (Hmid : PPState.mem mid = PPState.mem ppst).
      { destruct (VMMemoryGrowth.outcome_memory_growth bbm n tid imem out ppst mid r pre Hout)
          as [Hsame|[added [_ [Hnonempty [Hadded _]]]]]; [exact Hsame|].
        rewrite Hadded, Hmem in Hsuffix. apply (f_equal length) in Hsuffix.
        rewrite !length_app in Hsuffix. destruct added; [contradiction|cbn in Hsuffix; lia]. }
      pose proof (collect_outcome_intro (VMPromising bbm) tid imem
        (length (PPState.mem ppst)) out proms ppst mid r pre Hout) as Hcollect.
      rewrite Hmid, Nat.sub_diag in Hcollect. cbn [take app] in Hcollect.
      assert (Hcollect' : Exec.elem_of_results ((proms, mid), r)
        (CPState.run_outcome_with_promise (VMPromising bbm) tid imem
          (length (PPState.mem ppst)) out (proms, ppst))).
      { destruct pre as [pre|]; [destruct (decide (pre ≤ length (PPState.mem ppst)))|]; exact Hcollect. }
      eapply Exec.elem_of_bind_intro; [exact Hcollect'|].
      rewrite <- Hmid. eapply IH; [exact Htail|congruence].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|]. eapply IH; eassumption.
Qed.

Section Thread.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (tid : fin n) (imem : memoryMap) (mem : list Ev.t).
Local Notation prom := (VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).

(** Bounds are checked at instruction boundaries, where the executable
    certification checks for early stopping. Translation, CSE, MSR, reads,
    and fulfillment use their actual handlers without a syntactic restriction. *)
Inductive BoundedThreadExecution : TState.t → TState.t → Prop :=
| bounded_thread_done ts :
    TState.min_new_prom_view ts ≤ length mem →
    CPState.terminated_ts prom (term !!! tid) ts = true →
    BoundedThreadExecution ts ts
| bounded_thread_step ts mid fin iis :
    TState.min_new_prom_view ts ≤ length mem →
    CPState.terminated_ts prom (term !!! tid) ts = false →
    Exec.elem_of_results (PPState.Make mid mem iis, ())
      (cinterp (run_outcome' n tid imem) isem (PPState.Make ts mem IIS.init)) →
    BoundedThreadExecution mid fin →
    BoundedThreadExecution ts fin.

Lemma bounded_thread_final_candidate ts fin :
  BoundedThreadExecution ts fin →
  ∃ fuel, fin ∈ (CPState.enumerate_results isem prom term tid imem fuel ts mem)
    .(CPState.final_states prom).
Proof.
  intro Htrace.
  assert (Hrun : ∃ fuel, ∀ iis, ∃ final_iis,
    Exec.elem_of_results (([], PPState.Make fin mem final_iis), CPState.Terminated)
      (CPState.run_to_termination isem prom term tid imem fuel (length mem)
        ([], PPState.Make ts mem iis))).
  { induction Htrace as [ts Hbound Hterm|ts mid fin step_iis Hbound Hterm Hinst Htail IH].
    - exists 0. intro iis. exists iis.
      apply (run_to_termination_terminated_initial (prom := prom)); assumption.
    - destruct IH as [fuel Hrun]. exists (S fuel). intro iis.
      destruct (Hrun step_iis) as [last Hlast]. exists last.
      cbn [CPState.run_to_termination].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn -[CPState.terminated_ts]. rewrite decide_False by lia. rewrite Hterm.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
      eapply Exec.elem_of_bind_intro with (st' := ([], PPState.Make mid mem step_iis)) (a := ()).
      + exact (collect_unchanged_instruction bbm tid imem isem []
          (PPState.Make ts mem IIS.init) (PPState.Make mid mem step_iis) () Hinst eq_refl).
      + exact Hlast. }
  destruct Hrun as [fuel Hrun]. destruct (Hrun IIS.init) as [iis Hlast].
  exists fuel. apply (enumerate_results_final_state_witness (prom := prom)).
  exists (PPState.Make fin mem iis). split; [reflexivity|exact Hlast].
Qed.
End Thread.
End VMFinalCertification.

Section VMDirect.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation prom := (VMPromising.VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t VMPromising.TState.t Ev.t n).

Definition VMViewBound (st : state) : Prop :=
  ∀ tid, VMPromising.TState.min_new_prom_view (PState.tstate tid st) ≤ length (PState.events st).
Definition VMBoundedFixedHistoryStep (st next : state) : Prop :=
  InstructionTransition prom nondet term st next ∧
  PState.events next = PState.events st ∧ VMViewBound st.

Lemma bounded_fixed_history_projection st final :
  rtc VMBoundedFixedHistoryStep st final →
  CPState.terminated prom term final → VMViewBound final →
  PState.initmem final = PState.initmem st ∧ PState.events final = PState.events st ∧
  ∀ tid, VMFinalCertification.BoundedThreadExecution bbm nondet term tid
    (PState.initmem st) (PState.events st) (PState.tstate tid st) (PState.tstate tid final).
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail IH]; intros Hterm Hbound.
  - split; [reflexivity|]. split; [reflexivity|]. intro tid. constructor; [apply Hbound|].
    unfold CPState.terminated, fforallb in Hterm. apply true_eq_true in Hterm.
    apply (proj1 (@List.forallb_forall (fin n)
      (CPState.terminated_tid prom term st) (enum (fin n))) Hterm).
    apply list_elem_of_In, elem_of_enum.
  - destruct (IH Hterm Hbound) as [Himem [Hmem Hthreads]].
    destruct Hstep as [[owner [Hnot Hrun]] [Hsame Hstart]].
    destruct (run_tid_decompose prom isem owner st mid Hrun)
      as [ts [mem [iis [Hinst Hmid]]]]. subst mid. cbn in Hsame. subst mem.
    split; [exact Himem|]. split; [exact Hmem|]. intro tid.
    specialize (Hthreads tid). cbn in Hthreads.
    destruct (decide (owner = tid)) as [<-|Hne].
    + unfold PState.tstate, compose in Hthreads. cbn in Hthreads.
      rewrite vlookup_insert in Hthreads.
      econstructor; [apply Hstart|exact Hnot|exact Hinst|exact Hthreads].
    + unfold PState.tstate, compose in Hthreads. cbn in Hthreads.
      rewrite vlookup_insert_ne in Hthreads by exact Hne. exact Hthreads.
Qed.

Lemma VMSail_fixed_history_final_batch st final returned
    (pt : CPState.terminated prom term final) :
  rtc VMBoundedFixedHistoryStep st final → VMViewBound final →
  Exec.elem_of_results (returned, ()) (CPState.validate_final prom final final) →
  ∃ fuel, Exec.elem_of_results
    (st, Some (CPState.to_final_archState (CPState.make_final prom term final pt)))
    (CPState.run_transition_promise_first isem prom term fuel st).
Proof.
  intros Htrace Hbound Hvalid.
  destruct (bounded_fixed_history_projection st final Htrace pt Hbound)
    as [Himem [Hmem Hthreads]].
  assert (Hcandidates : ∀ tid, ∃ fuel, PState.tstate tid final ∈
    (CPState.enumerate_results isem prom term tid (PState.initmem st)
      fuel (PState.tstate tid st) (PState.events st)).(CPState.final_states prom)).
  { intro tid. apply VMFinalCertification.bounded_thread_final_candidate, Hthreads. }
  assert (Hfinite : ∀ tids : list (fin n), ∃ fuel, ∀ tid, tid ∈ tids →
    PState.tstate tid final ∈ (CPState.enumerate_results isem prom term tid (PState.initmem st)
      fuel (PState.tstate tid st) (PState.events st)).(CPState.final_states prom)).
  { intro tids. induction tids as [|tid tids [fuel Htail]].
    - exists 0. intros tid Hin. inversion Hin.
    - destruct (Hcandidates tid) as [head_fuel Hhead].
      exists (Nat.max head_fuel fuel). intros other Hin.
      apply elem_of_cons in Hin as [->|Hin].
      + eapply final_candidate_more_fuel; [apply Nat.le_max_l|exact Hhead].
      + eapply final_candidate_more_fuel; [apply Nat.le_max_r|apply Htail, Hin]. }
  destruct (Hfinite (enum (fin n))) as [fuel Hfuel]. exists fuel.
  destruct final as [targets final_imem final_mem]. cbn in Himem, Hmem. subst final_imem final_mem.
  eapply (run_transition_promise_first_some_intro (prom := prom)).
  - apply Exec.elem_of_mchoosel, (proj2 (cprodn_spec _ _)). intro tid.
    rewrite vlookup_map, promise_first_execution_results_lookup. apply Hfuel, elem_of_enum.
  - eapply validate_final_transport. exact Hvalid.
Qed.

(** A concrete VM direct path with its promises already issued can serialize
    its interleaved instruction suffix into a promise-first final batch.
    The result includes the current BBM validation. *)
Theorem VMSail_preissued_direct_to_promise_first initMs st before final returned
    (pt : CPState.terminated prom term final) :
  rtc (StableCertifiedPromiseStep prom nondet term) st before →
  rtc VMBoundedFixedHistoryStep before final → VMViewBound final →
  Exec.elem_of_results (returned, ()) (CPState.validate_final prom final final) →
  ∃ direct_returned cost, ∀ fuel, cost < fuel →
    Exec.elem_of_results
      (direct_returned, CPState.to_final_archState (CPState.make_final prom term final pt))
      (opModel.run (@CPState.opmodel isem prom n) fuel term initMs st) ∧
    Exec.elem_of_results
      (before, CPState.to_final_archState (CPState.make_final prom term final pt))
      (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs st).
Proof.
  intros Hprefix Hsuffix Hbound Hvalid.
  destruct (VMSail_fixed_history_final_batch before final returned pt Hsuffix Hbound Hvalid)
    as [cert_fuel Hbatch].
  eapply VMSail_stable_prefix_common_fuel; eassumption.
Qed.
End VMDirect.
