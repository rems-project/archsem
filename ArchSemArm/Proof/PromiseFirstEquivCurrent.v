(******************************************************************************)
(* Current result-valued promise-first statement                              *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromisingExec VMPromising VMPromisingExec.
From ArchSemArm.Proof Require Import PromiseFirstCurrent.

#[local] Open Scope stdpp.

(** Prefix states of one of the two runners.  A prefix starts at this program's
    successful initialization and follows successful non-final transitions.
    The mode remains fixed throughout the prefix. *)
Inductive PromiseFirstReachable
    (prom : Promising.Model) (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n)
    (use_pf : bool) :
    PState.t prom.(Promising.tState) prom.(Promising.mEvent) n → Prop :=
| PromiseFirstReachable_init st :
    PState.from_archState prom initMs = Ok st →
    PromiseFirstReachable prom isem term initMs use_pf st
| PromiseFirstReachable_step fuel st st' :
    PromiseFirstReachable prom isem term initMs use_pf st →
    Exec.elem_of_results (st', None)
      ((if use_pf then CPState.run_transition_promise_first isem prom term fuel
        else CPState.run_transition isem prom term fuel) st) →
    PromiseFirstReachable prom isem term initMs use_pf st'.

Lemma promise_first_reachable_to_direct
    prom isem {n} (term : terminationCondition n) initMs :
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  ∀ st, PromiseFirstReachable prom isem term initMs true st →
    PromiseFirstReachable prom isem term initMs false st.
Proof.
  intros Hfilter st Hreach.
  induction Hreach as [st Hinit|fuel st st' Hreach IH Hstep].
  - apply PromiseFirstReachable_init. exact Hinit.
  - eapply PromiseFirstReachable_step with (fuel := fuel).
    + exact IH.
    + eapply promise_first_none_to_direct_none; [|exact Hstep].
      intros. eapply Hfilter. eassumption.
Qed.

Lemma promise_first_run_final_prefix
    prom isem {n} (term : terminationCondition n) initMs fuel
    (st st_fin : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n)
    (fsig : {s & archState.is_terminated term s}) :
  PromiseFirstReachable prom isem term initMs true st →
  Exec.elem_of_results (st_fin, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs st) →
  ∃ final_fuel before,
    PromiseFirstReachable prom isem term initMs true before ∧
    Exec.elem_of_results (st_fin, Some fsig)
      (CPState.run_transition_promise_first isem prom term final_fuel before).
Proof.
  revert st st_fin fsig.
  induction fuel as [|fuel IH]; intros st st_fin fsig Hreach Hrun.
  - cbn [opModel.run] in Hrun.
    unfold mthrow, Exec.throw_inst, Exec.res_throw_inst,
      Exec.elem_of_results in Hrun. cbn in Hrun. inversion Hrun.
  - cbn [opModel.run] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [next [res [Hstep Htail]]].
    destruct res as [final|].
    + apply Exec.elem_of_mret_inv in Htail as [-> ->].
      exists (S fuel), st. split; assumption.
    + eapply IH; [|exact Htail].
      eapply PromiseFirstReachable_step with (fuel := S fuel);
        eassumption.
Qed.

(** A successful promise-first run reaches a state reproducible by direct
    promise steps, then selects one terminating exploration per thread.  The
    prefix uses a separate fuel for each transition. Reproducing it with the
    actual direct runner also requires one decreasing fuel budget, in addition
    to serializing the final explorations while preserving the shared history. *)
Lemma promise_first_run_decompose
    prom isem {n} (term : terminationCondition n) initMs fuel
    (initPs st_fin : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n)
    (fsig : {s & archState.is_terminated term s}) :
  (∀ (tid : fin n) mem candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem candidates → ev ∈ candidates) →
  PState.from_archState prom initMs = Ok initPs →
  Exec.elem_of_results (st_fin, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs initPs) →
  ∃ before final_fuel finalPs (pt : CPState.terminated prom term finalPs),
    PromiseFirstReachable prom isem term initMs false before ∧
    PState.initmem finalPs = PState.initmem before ∧
    PState.events finalPs = PState.events before ∧
    (∀ tid, ∃ ppst,
      PPState.state ppst = PState.tstate tid finalPs ∧
      Exec.elem_of_results (([], ppst), CPState.Terminated)
        (CPState.run_to_termination isem prom term tid (PState.initmem before)
          final_fuel (length (PState.events before))
          ([], PPState.Make (PState.tstate tid before) (PState.events before)
            prom.(Promising.iis_init)))) ∧
    Exec.elem_of_results (st_fin, ()) (CPState.validate_final prom finalPs before) ∧
    fsig = CPState.to_final_archState (CPState.make_final prom term finalPs pt).
Proof.
  intros Hfilter Hinit Hrun.
  assert (Hreach : PromiseFirstReachable prom isem term initMs true initPs).
  { apply PromiseFirstReachable_init. exact Hinit. }
  destruct (promise_first_run_final_prefix prom isem term initMs fuel
    initPs st_fin fsig Hreach Hrun) as [final_fuel [before [Hbefore Hfinal]]].
  destruct (run_transition_promise_first_some_inv isem term final_fuel
    before st_fin fsig Hfinal)
    as [tstates [finalPs [pt [Hstate [Hstates [Hvalidate Hfsig]]]]]].
  exists before, final_fuel, finalPs, pt.
  split.
  - eapply promise_first_reachable_to_direct; eassumption.
  - split; [rewrite Hstate; reflexivity|].
    split; [rewrite Hstate; reflexivity|].
    split.
    + intro tid. specialize (Hstates tid).
      rewrite promise_first_execution_results_lookup in Hstates.
      rewrite Hstate. cbn [PState.tstate].
      apply (proj1 (enumerate_results_final_state_witness isem term tid
        (PState.initmem before) final_fuel (PState.tstate tid before)
        (PState.events before) (tstates !!! tid))).
      exact Hstates.
    + split; assumption.
Qed.

(** Histories inspected by the runners include certification exploration.
    Error branches matter here: enumeration also extracts promise candidates
    from executions ending in an error.  Collected events and the explored
    memory are both included. *)
Inductive PromiseFirstObservedHistory
    (prom : Promising.Model) (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n) :
    list prom.(Promising.mEvent) → Prop :=
| PromiseFirstObservedHistory_prefix use_pf st :
    PromiseFirstReachable prom isem term initMs use_pf st →
    PromiseFirstObservedHistory prom isem term initMs (PState.events st)
| PromiseFirstObservedHistory_success use_pf st tid fuel new_proms ppst ending :
    PromiseFirstReachable prom isem term initMs use_pf st →
    Exec.elem_of_results ((new_proms, ppst), ending)
      (CPState.run_to_termination isem prom term tid (PState.initmem st)
        fuel (length (PState.events st))
        ([], PPState.Make (PState.tstate tid st) (PState.events st)
          prom.(Promising.iis_init))) →
    PromiseFirstObservedHistory prom isem term initMs
      (new_proms ++ PPState.mem ppst)
| PromiseFirstObservedHistory_error use_pf st tid fuel new_proms ppst err :
    PromiseFirstReachable prom isem term initMs use_pf st →
    ((new_proms, ppst), err) ∈ Exec.errors
      (CPState.run_to_termination isem prom term tid (PState.initmem st)
        fuel (length (PState.events st))
        ([], PPState.Make (PState.tstate tid st) (PState.events st)
          prom.(Promising.iis_init))) →
    PromiseFirstObservedHistory prom isem term initMs
      (new_proms ++ PPState.mem ppst).

(** Code immutability is a property of the given program's histories.  The
    reader is tied to the model's event type; unrelated events cannot be used
    to discharge this premise. *)
Definition PromiseFirstNoSelfModifying
    (prom : Promising.Model) (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n)
    (read_byte : address → prom.(Promising.mEvent) → option (bv 8))
    (code : code_region) : Prop :=
  ∀ events, PromiseFirstObservedHistory prom isem term initMs events →
    no_self_modifying_history read_byte code events.

Lemma no_self_modifying_reachable
    prom isem {n} (term : terminationCondition n) initMs read_byte code
    use_pf st :
  PromiseFirstNoSelfModifying prom isem term initMs read_byte code →
  PromiseFirstReachable prom isem term initMs use_pf st →
  no_self_modifying_history read_byte code (PState.events st).
Proof.
  intros Hsafe Hreach.
  apply Hsafe.
  eapply PromiseFirstObservedHistory_prefix. exact Hreach.
Qed.

Lemma no_self_modifying_enumerated_promise
    prom isem {n} (term : terminationCondition n) initMs read_byte code
    use_pf st (tid : fin n) fuel ev :
  (∀ candidates event,
    event ∈ prom.(Promising.filter_promises) n tid (PState.events st) candidates →
    event ∈ candidates) →
  PromiseFirstNoSelfModifying prom isem term initMs read_byte code →
  PromiseFirstReachable prom isem term initMs use_pf st →
  ev ∈ (CPState.enumerate_results isem prom term tid (PState.initmem st)
    fuel (PState.tstate tid st) (PState.events st)).(CPState.promises prom) →
  event_misses_code read_byte code ev.
Proof.
  intros Hfilter Hsafe Hreach Hev.
  destruct (enumerate_results_promise_witness isem term tid
    (PState.initmem st) fuel (PState.tstate tid st) (PState.events st)
    ev Hfilter Hev) as [new_proms [ppst [Hin Hrun]]].
  assert (Hobserved : PromiseFirstObservedHistory prom isem term initMs
    (new_proms ++ PPState.mem ppst)).
  {
    destruct Hrun as [[ending Hrun]|[err Hrun]].
    - eapply PromiseFirstObservedHistory_success; eauto.
    - eapply PromiseFirstObservedHistory_error; eauto.
  }
  apply (Hsafe _ Hobserved).
  apply elem_of_app. left. exact Hin.
Qed.

(** This predicate fixes the program and termination condition.  Fuel may
    differ between runners; only successful architectural final states are
    compared. *)
Definition PromiseFirstFinalStateEquiv
    (prom : Promising.Model) (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n) : Prop :=
  ∀ fs : archState n,
    (∃ fuel pt, archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc prom isem fuel n term initMs) ↔
    (∃ fuel pt, archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf prom isem fuel n term initMs).

(** These are execution obligations, not instances for UM or VM.
    [PromiseFirstCounterexampleCurrent] proves that code immutability alone
    cannot discharge them for arbitrary [iMon] semantics: discarded
    exploration paths can lose promise candidates as fuel increases.
    A proof for the current runner therefore needs a justified restriction on
    instruction semantics, or the candidate-collection algorithm must change. *)
Record PromiseFirstExecutionTransforms
    (prom : Promising.Model) (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n) : Prop := {
  direct_run_to_promise_first :
    ∀ initPs fuel st (fsig : {s & archState.is_terminated term s}),
      PState.from_archState prom initMs = Ok initPs →
      Exec.elem_of_results (st, fsig)
        (opModel.run (@CPState.opmodel isem prom n) fuel term initMs initPs) →
      ∃ fuel_pf st_pf fsig_pf,
        Exec.elem_of_results (st_pf, fsig_pf)
          (opModel.run (@CPState.opmodel_pf isem prom n)
            fuel_pf term initMs initPs) ∧
        projT1 fsig_pf = projT1 fsig;
  promise_first_run_to_direct :
    ∀ initPs fuel_pf st_pf (fsig_pf : {s & archState.is_terminated term s}),
      PState.from_archState prom initMs = Ok initPs →
      Exec.elem_of_results (st_pf, fsig_pf)
        (opModel.run (@CPState.opmodel_pf isem prom n)
          fuel_pf term initMs initPs) →
      ∃ fuel st fsig,
        Exec.elem_of_results (st, fsig)
          (opModel.run (@CPState.opmodel isem prom n) fuel term initMs initPs) ∧
        projT1 fsig = projT1 fsig_pf
}.

Lemma promise_first_equiv_from_execution_transforms
    prom isem {n} (term : terminationCondition n) initMs
    (Hexec : PromiseFirstExecutionTransforms prom isem term initMs) :
  PromiseFirstFinalStateEquiv prom isem term initMs.
Proof.
  intro fs. split.
  - intros [fuel [pt Hfinal]].
    destruct (direct_final_state_inv isem term initMs fuel fs pt Hfinal)
      as [initPs [Hinit [st [fsig [Hrun Hfs]]]]].
    destruct
      (@direct_run_to_promise_first prom isem n term initMs Hexec
        initPs fuel st fsig Hinit Hrun)
      as [fuel_pf [st_pf [fsig_pf [Hrun_pf Hfsig]]]].
    destruct fsig_pf as [fs_pf pt_pf].
    cbn in Hfsig. rewrite Hfs in Hfsig. subst fs_pf.
    exists fuel_pf, pt_pf.
    eapply promise_first_final_state_intro; eauto.
  - intros [fuel_pf [pt_pf Hfinal]].
    destruct (promise_first_final_state_inv isem term initMs fuel_pf fs pt_pf Hfinal)
      as [initPs [Hinit [st_pf [fsig_pf [Hrun_pf Hfsig_pf]]]]].
    destruct
      (@promise_first_run_to_direct prom isem n term initMs Hexec
        initPs fuel_pf st_pf fsig_pf Hinit Hrun_pf)
      as [fuel [st [fsig [Hrun Hfsig]]]].
    destruct fsig as [fs_direct pt_direct].
    cbn in Hfsig. rewrite Hfsig_pf in Hfsig. subst fs_direct.
    exists fuel, pt_direct.
    eapply direct_final_state_intro; eauto.
Qed.

Definition VMPromisingReadByte : address → Ev.t → option (bv 8) :=
  λ addr ev,
    match Ev.get_msg ev with
    | Some msg => Msg.read_byte addr msg
    | None => None
    end.

Definition UMPromisingNoSelfModifying isem {n}
    (term : terminationCondition n) initMs code : Prop :=
  PromiseFirstNoSelfModifying UMPromising.UMPromising isem term initMs
    Msg.read_byte code.

Definition VMPromisingNoSelfModifying bbm isem {n}
    (term : terminationCondition n) initMs code : Prop :=
  PromiseFirstNoSelfModifying (VMPromising.VMPromising bbm) isem term initMs
    VMPromisingReadByte code.

Definition UMPromisingFinalStateEquiv isem {n}
    (term : terminationCondition n) initMs : Prop :=
  PromiseFirstFinalStateEquiv UMPromising.UMPromising isem term initMs.

Definition VMPromisingFinalStateEquiv bbm isem {n}
    (term : terminationCondition n) initMs : Prop :=
  PromiseFirstFinalStateEquiv (VMPromising.VMPromising bbm) isem term initMs.

Definition UMPromisingExecutionTransforms isem {n}
    (term : terminationCondition n) initMs : Prop :=
  PromiseFirstExecutionTransforms UMPromising.UMPromising isem term initMs.

Definition VMPromisingExecutionTransforms bbm isem {n}
    (term : terminationCondition n) initMs : Prop :=
  PromiseFirstExecutionTransforms (VMPromising.VMPromising bbm) isem term initMs.
