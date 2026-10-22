(******************************************************************************)
(* Serializing the final sail-tiny-arm promise-first batch *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstExecutionCurrent PromiseFirstVMExecutionCurrent
  PromiseFirstConcreteCurrent PromiseFirstSailCurrent.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Existing Instance PState.PState_PPState_set.

Section Serialization.
Context (prom : Promising.Model) (nondet : bool) {n : nat}
  (term : terminationCondition n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t prom.(Promising.tState) prom.(Promising.mEvent) n).

Definition replace_thread (st : state) (tid : fin n) (ts : prom.(Promising.tState)) : state :=
  PState.Make (vinsert tid ts (PState.tstates st)) (PState.initmem st) (PState.events st).

Lemma replace_thread_same st tid ts :
  PState.tstate tid (replace_thread st tid ts) = ts.
Proof. unfold PState.tstate, compose, replace_thread. cbn. apply vlookup_insert. Qed.
Lemma replace_thread_other st tid other ts : tid ≠ other →
  PState.tstate other (replace_thread st tid ts) = PState.tstate other st.
Proof.
  intro Hne. unfold PState.tstate, compose, replace_thread. cbn.
  apply vlookup_insert_ne. exact Hne.
Qed.
Lemma replace_thread_self st tid : replace_thread st tid (PState.tstate tid st) = st.
Proof.
  destruct st as [states imem mem]. unfold replace_thread, PState.tstate, compose.
  cbn. rewrite vlookup_insert_self. reflexivity.
Qed.
Lemma replace_thread_twice st tid ts ts' :
  replace_thread (replace_thread st tid ts) tid ts' = replace_thread st tid ts'.
Proof.
  unfold replace_thread. cbn. f_equal. apply vec_eq. intro i.
  destruct (decide (tid = i)) as [->|Hne].
  - rewrite !vlookup_insert. reflexivity.
  - rewrite !vlookup_insert_ne by exact Hne. reflexivity.
Qed.

Lemma run_tid_fixed_history (st : state) (tid : fin n) ts' iis :
  Exec.elem_of_results (PPState.Make ts' (PState.events st) iis, ())
    (cinterp (λ out, prom.(Promising.handle_outcome) n tid (PState.initmem st) out |$> fst)
      isem (PPState.Make (PState.tstate tid st) (PState.events st) prom.(Promising.iis_init))) →
  Exec.elem_of_results (replace_thread st tid ts', ())
    (PState.run_tid isem prom tid st).
Proof.
  intro Hrun. unfold PState.run_tid.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  pose proof (Exec.elem_of_liftSt st
    (PPState.Make ts' (PState.events st) iis) ()
    (PState.PState_PPState prom tid)
    (cinterp (λ out, prom.(Promising.handle_outcome) n tid (PState.initmem st) out |$> fst)
      isem) Hrun) as Hlift.
  exact Hlift.
Qed.

Definition InstructionTransition (st st' : state) : Prop :=
  ∃ tid, CPState.terminated_tid prom term st tid = false ∧
    Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st).

Lemma one_thread_serializes tid imem mem ts ts' :
  ThreadInstructionExecution prom tid imem isem term mem ts ts' →
  ∀ st : state,
    PState.initmem st = imem → PState.events st = mem → PState.tstate tid st = ts →
    rtc InstructionTransition st (replace_thread st tid ts').
Proof.
  intro Htrace. induction Htrace as [ts Hterm|ts mid fin iis Hterm Hinst Htail IH];
    intros st Himem Hmem Hts.
  - rewrite <- Hts, replace_thread_self. apply rtc_refl.
  - eapply rtc_l with (y := replace_thread st tid mid).
    + exists tid. split.
      * unfold CPState.terminated_tid. rewrite Hts. exact Hterm.
      * apply (run_tid_fixed_history st tid mid iis).
        rewrite Himem, Hmem, Hts. exact Hinst.
    + rewrite <- (replace_thread_twice st tid mid fin).
      apply IH; [exact Himem|exact Hmem|apply replace_thread_same].
Qed.

Lemma serialize_thread_list (tids : list (fin n))
    (targets : vec prom.(Promising.tState) n) (st : state) :
  NoDup tids →
  (∀ tid, tid ∈ tids →
    ThreadInstructionExecution prom tid (PState.initmem st) isem term
      (PState.events st) (PState.tstate tid st) (targets !!! tid)) →
  ∃ st', rtc InstructionTransition st st' ∧
    PState.initmem st' = PState.initmem st ∧ PState.events st' = PState.events st ∧
    (∀ tid, tid ∈ tids → PState.tstate tid st' = targets !!! tid) ∧
    (∀ tid, tid ∉ tids → PState.tstate tid st' = PState.tstate tid st).
Proof.
  revert st. induction tids as [|tid tids IH]; intros st Hnodup Htraces.
  - exists st. repeat split; try reflexivity; [apply rtc_refl|]. intros i Hi. inversion Hi.
  - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
    set (mid := replace_thread st tid (targets !!! tid)).
    assert (Hfirst : rtc InstructionTransition st mid).
    { unfold mid. eapply one_thread_serializes; [apply Htraces; left; reflexivity|..]; reflexivity. }
    assert (Htail : ∀ i, i ∈ tids →
      ThreadInstructionExecution prom i (PState.initmem mid) isem term
        (PState.events mid) (PState.tstate i mid) (targets !!! i)).
    { intros i Hi. unfold mid. rewrite replace_thread_other by set_solver.
      apply Htraces. right. exact Hi. }
    destruct (IH mid Hnodup Htail) as [last [Hsteps [Himem [Hmem [Hdone Hframe]]]]].
    exists last. split; [eapply rtc_trans; eassumption|].
    split; [exact Himem|]. split; [exact Hmem|]. split.
    + intros i Hi. apply elem_of_cons in Hi as [->|Hi].
      * rewrite Hframe by exact Hnotin. apply replace_thread_same.
      * apply Hdone, Hi.
    + intros i Hi. rewrite Hframe by set_solver.
      unfold mid. apply replace_thread_other. set_solver.
Qed.

Lemma serialize_all_threads (st final : state) :
  PState.initmem final = PState.initmem st → PState.events final = PState.events st →
  (∀ tid, ThreadInstructionExecution prom tid (PState.initmem st) isem term
    (PState.events st) (PState.tstate tid st) (PState.tstate tid final)) →
  rtc InstructionTransition st final.
Proof.
  intros Himem Hmem Htraces.
  destruct (serialize_thread_list (enum (fin n)) (PState.tstates final) st
    (NoDup_enum (fin n)) (λ tid _, Htraces tid))
    as [last [Hsteps [Himem' [Hmem' [Hdone _]]]]].
  assert (Hstates : PState.tstates last = PState.tstates final).
  { apply vec_eq. intro i. apply Hdone. apply elem_of_enum. }
  assert (last = final).
  { destruct last, final. cbn in *. congruence. }
  subst last. exact Hsteps.
Qed.

Lemma instruction_transition_any_fuel fuel st st' :
  InstructionTransition st st' →
  Exec.elem_of_results (st', None) (CPState.run_transition isem prom term fuel st).
Proof.
  intros [tid [Htid Hrun]]. unfold CPState.run_transition.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  destruct (decide (CPState.terminated prom term st)) as [Hall|Hnot].
  - exfalso. unfold CPState.terminated, fforallb in Hall.
    apply true_eq_true in Hall.
    pose proof (proj1 (@List.forallb_forall (fin n)
      (CPState.terminated_tid prom term st) (enum (fin n))) Hall) as Hall'.
    assert (Hin : List.In tid (enum (fin n))).
    { apply list_elem_of_In, elem_of_enum. }
    specialize (Hall' tid Hin). rewrite Htid in Hall'. discriminate.
  - eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
    eapply run_step_intro; [exact Htid|right; exact Hrun].
Qed.

Lemma instruction_trace_run initMs st final
    (pt : CPState.terminated prom term final) :
  Exec.elem_of_results (final, ()) (CPState.validate_final prom final final) →
  rtc InstructionTransition st final →
  ∃ cost, ∀ fuel, cost < fuel →
    Exec.elem_of_results
      (final, CPState.to_final_archState (CPState.make_final prom term final pt))
      (opModel.run (@CPState.opmodel isem prom n) fuel term initMs st).
Proof.
  intros Hvalid Htrace. induction Htrace as [st|st mid final Hstep Htail IH].
  - exists 0. intros [|fuel] Hfuel; [lia|]. cbn [opModel.run].
    eapply Exec.elem_of_bind_intro.
    + apply run_transition_some_intro. exact Hvalid.
    + apply Exec.elem_of_mret.
  - destruct (IH pt Hvalid) as [cost Hrun].
    exists (S cost). intros [|fuel] Hfuel; [lia|]. cbn [opModel.run].
    eapply Exec.elem_of_bind_intro.
    + apply instruction_transition_any_fuel. exact Hstep.
    + apply Hrun. lia.
Qed.
End Serialization.

Lemma validate_final_transport (prom : Promising.Model) {n}
    (final ambient ambient' returned : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n) :
  Exec.elem_of_results (returned, ()) (CPState.validate_final prom final ambient) →
  Exec.elem_of_results (ambient', ()) (CPState.validate_final prom final ambient').
Proof.
  unfold CPState.validate_final. intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [pt [Hguard Htail]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  destruct (CPState.check_valid_end prom final) as [|err errs].
  - destruct (Exec.elem_of_guard_discard (E:=string) ambient' pt) as [pt' Hguard'].
    eapply Exec.elem_of_bind_intro; [exact Hguard'|apply Exec.elem_of_mret].
  - apply Exec.elem_of_bind_elim in Htail as [last [e [_ Hthrow]]].
    unfold mthrow, Exec.throw_inst, Exec.res_throw_inst, Exec.elem_of_results in Hthrow.
    cbn in Hthrow. inversion Hthrow.
Qed.

Lemma sail_final_batch_to_direct_run prom nondet {n}
    (term : terminationCondition n) initMs cert_fuel
    (before returned : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n)
    (fsig : {s & archState.is_terminated term s}) :
  OutcomeMemoryGrowth prom →
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first (sail_tiny_arm_sem nondet) prom
      term cert_fuel before) →
  ∃ final cost,
    rtc (InstructionTransition prom nondet term) before final ∧
    ∀ fuel, cost < fuel →
      Exec.elem_of_results (final, fsig)
        (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) prom n)
          fuel term initMs before).
Proof.
  intros Hgrowth Hstep.
  destruct (run_transition_promise_first_some_inv
    (sail_tiny_arm_sem nondet) term cert_fuel before returned fsig Hstep)
    as [targets [final [pt [Hfinal [Hstates [Hvalid Hfsig]]]]]].
  assert (Htrace : rtc (InstructionTransition prom nondet term) before final).
  { apply serialize_all_threads.
    - rewrite Hfinal. reflexivity.
    - rewrite Hfinal. reflexivity.
    - intro tid. specialize (Hstates tid).
      rewrite promise_first_execution_results_lookup in Hstates.
      rewrite Hfinal. cbn [PState.tstate].
      apply enumerated_final_thread_execution with (fuel := cert_fuel); assumption. }
  assert (Hvalid' : Exec.elem_of_results (final, ())
    (CPState.validate_final prom final final)).
  { eapply validate_final_transport. exact Hvalid. }
  destruct (instruction_trace_run prom nondet term initMs before final pt Hvalid' Htrace)
    as [cost Hrun].
  exists final, cost. split; [exact Htrace|].
  rewrite Hfsig. exact Hrun.
Qed.

Lemma UMSail_final_batch_to_direct_run nondet {n}
    (term : terminationCondition n) initMs cert_fuel before returned fsig :
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first (sail_tiny_arm_sem nondet) UMPromising
      term cert_fuel before) →
  ∃ final cost,
    rtc (InstructionTransition UMPromising nondet term) before final ∧
    ∀ fuel, cost < fuel →
      Exec.elem_of_results (final, fsig)
        (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) UMPromising n)
          fuel term initMs before).
Proof.
  apply sail_final_batch_to_direct_run.
  exact UMMemoryGrowth.outcome_memory_growth.
Qed.

Lemma VMSail_final_batch_to_direct_run bbm nondet {n}
    (term : terminationCondition n) initMs cert_fuel before returned fsig :
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first (sail_tiny_arm_sem nondet)
      (VMPromising.VMPromising bbm) term cert_fuel before) →
  ∃ final cost,
    rtc (InstructionTransition (VMPromising.VMPromising bbm) nondet term) before final ∧
    ∀ fuel, cost < fuel →
      Exec.elem_of_results (final, fsig)
        (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet)
          (VMPromising.VMPromising bbm) n) fuel term initMs before).
Proof.
  apply sail_final_batch_to_direct_run.
  exact (VMMemoryGrowth.outcome_memory_growth bbm).
Qed.
