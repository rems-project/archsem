(******************************************************************************)
(* Projecting interleaved UM instructions before the next memory event        *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstConcreteCurrent
  PromiseFirstExecutionCurrent PromiseFirstSailCurrent PromiseFirstSailReplay
  PromiseFirstSailSequence PromiseFirstSailThread PromiseFirstSailSerialization
  PromiseFirstSailThreadCertification PromiseFirstSailForeign.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Existing Instance PState.PState_PPState_set.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.
#[local] Typeclasses Transparent UMPromising.Memory.t.

Lemma run_tid_decompose (prom : Promising.Model) isem {n} (tid : fin n)
    (st st' : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n) :
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) →
  ∃ ts mem iis,
    Exec.elem_of_results (PPState.Make ts mem iis, ())
      (cinterp (λ out, prom.(Promising.handle_outcome) n tid (PState.initmem st) out |$> fst)
        isem (PPState.Make (PState.tstate tid st) (PState.events st) prom.(Promising.iis_init))) ∧
    st' = PState.Make (vinsert tid ts (PState.tstates st)) (PState.initmem st) mem.
Proof.
  unfold PState.run_tid. intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [st0 [Hget Hrun]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  apply Exec.elem_of_liftSt_inv in Hrun as [[ts mem iis] [Hstate Hinst]].
  exists ts, mem, iis. split; [exact Hinst|].
  destruct st. exact Hstate.
Qed.

Section Interleaving.
Context (nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t UMPromising.TState.t Msg.t n).
Local Notation instruction_step := (InstructionTransition UMPromising nondet term).

Definition FixedHistoryInstructionStep (st st' : state) : Prop :=
  instruction_step st st' ∧ PState.events st' = PState.events st.

Lemma fixed_history_step_projection st st' :
  FixedHistoryInstructionStep st st' →
  PState.initmem st' = PState.initmem st ∧
  ∀ tid : fin n, ∃ count,
    UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid) isem
      count (PState.tstate tid st) (PState.events st)
      (PState.tstate tid st') (PState.events st').
Proof.
  intros [[owner [Hterm Hrun]] Hmem].
  destruct (run_tid_decompose UMPromising isem owner st st' Hrun)
    as [ts [mem [iis [Hinst Hstate]]]].
  subst st'. cbn in Hmem. subst mem.
  split; [reflexivity|]. intro tid.
  destruct (decide (owner = tid)) as [->|Hne].
  - exists 1. unfold PState.tstate, compose in *. cbn in *.
    rewrite vlookup_insert.
    econstructor; [exact Hterm|exact Hinst|constructor].
  - exists 0. unfold PState.tstate, compose. cbn.
    rewrite vlookup_insert_ne by exact Hne. constructor.
Qed.

Lemma fixed_history_trace_projection st final :
  rtc FixedHistoryInstructionStep st final →
  PState.initmem final = PState.initmem st ∧
  PState.events final = PState.events st ∧
  ∀ tid : fin n, ∃ count,
    UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid) isem
      count (PState.tstate tid st) (PState.events st)
      (PState.tstate tid final) (PState.events final).
Proof.
  intro Htrace.
  induction Htrace as [st|st mid final Hstep Htail [Himem [Hmem Hthreads]]].
  - split; [reflexivity|]. split; [reflexivity|].
    intro tid. exists 0. constructor.
  - destruct (fixed_history_step_projection st mid Hstep) as [Himem_mid Hprefix].
    split; [rewrite Himem; exact Himem_mid|]. split.
    + rewrite Hmem. exact (proj2 Hstep).
    + intro tid. destruct (Hprefix tid) as [prefix_count Hprefix_tid].
      destruct (Hthreads tid) as [suffix_count Hsuffix_tid].
      rewrite Himem_mid in Hsuffix_tid.
      exists (prefix_count + suffix_count).
      eapply UMThreadReplay.thread_steps_trans; eassumption.
Qed.

(** Finite local prefixes can be serialized without requiring termination. *)
Lemma finite_thread_serializes tid imem mem count ts fin :
  UMThreadReplay.thread_steps tid imem (term !!! tid) isem count ts mem fin mem →
  ∀ st : state,
    PState.initmem st = imem → PState.events st = mem → PState.tstate tid st = ts →
    rtc instruction_step st (replace_thread UMPromising st tid fin).
Proof.
  intro Htrace. remember mem as finalmem eqn:Hsame in Htrace at 2.
  revert Hsame.
  induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intros Hsame st Himem Hmem Hts.
  - rewrite <- Hts, replace_thread_self. apply rtc_refl.
  - destruct (UMContinuation.instruction_facts tid imem isem _ _ _ Hinst)
      as [_ [_ [first Hfirst]]].
    destruct (UMThreadReplay.thread_steps_suffix tid imem (term !!! tid) isem _ _ _ _ _ Htail)
      as [rest Hrest].
    cbn in Hfirst.
    assert (Hnil : first = []).
    { rewrite Hfirst, Hsame in Hrest. apply (f_equal length) in Hrest.
      rewrite !length_app in Hrest. destruct first; [reflexivity|cbn in Hrest; lia]. }
    subst first. cbn in Hfirst. subst midmem.
    eapply rtc_l with (y := replace_thread UMPromising st tid mid).
    + exists tid. split.
      * unfold CPState.terminated_tid. rewrite Hts. exact Hterm.
      * apply (run_tid_fixed_history UMPromising nondet st tid mid iis).
        rewrite Himem, Hmem, Hts. exact Hinst.
    + rewrite <- (replace_thread_twice UMPromising st tid mid fin).
      apply IH; [exact Hsame|exact Himem|exact Hmem|exact (replace_thread_same UMPromising st tid mid)].
Qed.

Lemma finite_threads_serialize (tids : list (fin n))
    (targets : vec UMPromising.TState.t n) (st : state) :
  NoDup tids →
  (∀ tid, tid ∈ tids → ∃ count,
    UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid) isem
      count (PState.tstate tid st) (PState.events st) (targets !!! tid) (PState.events st)) →
  ∃ last, rtc instruction_step st last ∧
    PState.initmem last = PState.initmem st ∧ PState.events last = PState.events st ∧
    (∀ tid, tid ∈ tids → PState.tstate tid last = targets !!! tid) ∧
    (∀ tid, tid ∉ tids → PState.tstate tid last = PState.tstate tid st).
Proof.
  revert st. induction tids as [|tid tids IH]; intros st Hnodup Htraces.
  - exists st. repeat split; try reflexivity; [apply rtc_refl|]. intros i Hi. inversion Hi.
  - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
    set (mid := replace_thread UMPromising st tid (targets !!! tid)).
    destruct (Htraces tid ltac:(left; reflexivity)) as [count Hthread].
    assert (Hfirst : rtc instruction_step st mid).
    { unfold mid. eapply finite_thread_serializes; [exact Hthread|..]; reflexivity. }
    assert (Htail : ∀ i, i ∈ tids → ∃ count,
      UMThreadReplay.thread_steps i (PState.initmem mid) (term !!! i) isem
        count (PState.tstate i mid) (PState.events mid) (targets !!! i) (PState.events mid)).
    { intros i Hi. unfold mid. rewrite replace_thread_other by set_solver.
      apply Htraces. right. exact Hi. }
    destruct (IH mid Hnodup Htail) as [last [Hsteps [Himem [Hmem [Hdone Hframe]]]]].
    exists last. split; [eapply rtc_trans; eassumption|].
    split; [exact Himem|]. split; [exact Hmem|]. split.
    + intros i Hi. apply elem_of_cons in Hi as [->|Hi].
      * rewrite Hframe by exact Hnotin. exact (replace_thread_same UMPromising st tid (targets !!! tid)).
      * apply Hdone, Hi.
    + intros i Hi. rewrite Hframe by set_solver.
      unfold mid. apply (replace_thread_other UMPromising). set_solver.
Qed.

Lemma finite_all_threads_serialize (st final : state) :
  PState.initmem final = PState.initmem st → PState.events final = PState.events st →
  (∀ tid, ∃ count,
    UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid) isem
      count (PState.tstate tid st) (PState.events st)
      (PState.tstate tid final) (PState.events st)) →
  rtc instruction_step st final.
Proof.
  intros Himem Hmem Htraces.
  destruct (finite_threads_serialize (enum (fin n)) (PState.tstates final) st
    (NoDup_enum (fin n)) (λ tid _, Htraces tid))
    as [last [Hsteps [Himem' [Hmem' [Hdone _]]]]].
  assert (Hstates : PState.tstates last = PState.tstates final).
  { apply vec_eq. intro i. apply Hdone. apply elem_of_enum. }
  assert (last = final).
  { destruct last, final. cbn in *. congruence. }
  subst last. exact Hsteps.
Qed.

Lemma instruction_step_memory st st' :
  instruction_step st st' →
  PState.initmem st' = PState.initmem st ∧
  (PState.events st' = PState.events st ∨
   ∃ msg, PState.events st' = msg :: PState.events st).
Proof.
  intros [tid [Hterm Hrun]].
  destruct (run_tid_decompose UMPromising isem tid st st' Hrun)
    as [ts [mem [iis [Hinst Hstate]]]].
  subst st'. split; [reflexivity|]. cbn.
  destruct (decide (mem = PState.events st)) as [Hsame|Hnew]; [left; exact Hsame|].
  right.
  destruct (UMSail_instruction_updating_outcome_replay nondet tid (PState.initmem st)
    (PPState.Make (PState.tstate tid st) (PState.events st) UMPromising.IIS.init)
    (PPState.Make ts mem iis) Hinst Hnew)
    as [msg [out [before [after [ret [pre [_ [Hmem _]]]]]]]].
  exists msg. exact Hmem.
Qed.

Lemma first_new_global_message st final :
  rtc instruction_step st final →
  PState.events final ≠ PState.events st →
  ∃ before after msg,
    rtc FixedHistoryInstructionStep st before ∧
    instruction_step before after ∧
    PState.events after = msg :: PState.events st ∧
    rtc instruction_step after final.
Proof.
  intro Htrace.
  induction Htrace as [st|st mid final Hstep Htail IH]; intro Hnew; [contradiction|].
  destruct (instruction_step_memory st mid Hstep) as [_ [Hsame|[msg Hmem]]].
  - destruct (IH ltac:(rewrite Hsame; exact Hnew))
      as [before [after [msg [Hprefix [Hwrite [Hmem Hsuffix]]]]]].
    exists before, after, msg. split.
    + eapply rtc_l; [split; eassumption|exact Hprefix].
    + split; [exact Hwrite|]. split; [rewrite Hmem, Hsame; reflexivity|exact Hsuffix].
  - exists st, mid, msg. split; [apply rtc_refl|].
    split; [exact Hstep|]. split; assumption.
Qed.

(** Instructions of other threads before the first memory event can be
    omitted when certifying its issuing thread: the shared history is fixed
    throughout that prefix. The suffix retains the original interleaving. *)
Theorem UMSail_interleaved_first_message_projection st final :
  rtc instruction_step st final →
  PState.events final ≠ PState.events st →
  ∃ before after (tid : fin n) msg count,
    rtc FixedHistoryInstructionStep st before ∧
    instruction_step before after ∧
    rtc instruction_step after final ∧
    PState.events after = msg :: PState.events st ∧
    (∀ other, tid ≠ other → PState.tstate other after = PState.tstate other before) ∧
    UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid) isem
      count (PState.tstate tid st) (PState.events st)
      (PState.tstate tid after) (msg :: PState.events st).
Proof.
  intros Htrace Hnew.
  destruct (first_new_global_message st final Htrace Hnew)
    as [before [after [msg [Hprefix [Hwrite [Hmem Hsuffix]]]]]].
  destruct (fixed_history_trace_projection st before Hprefix)
    as [Himem_before [Hmem_before Hthreads]].
  destruct Hwrite as [tid [Hterm Hrun]].
  destruct (Hthreads tid) as [count Hthread].
  destruct (run_tid_decompose UMPromising isem tid before after Hrun)
    as [ts [mem [iis [Hinst Hstate]]]].
  assert (Hts : PState.tstate tid after = ts).
  { rewrite Hstate. unfold PState.tstate, compose. cbn. apply vlookup_insert. }
  assert (Hmem' : mem = msg :: PState.events st).
  { rewrite Hstate in Hmem. exact Hmem. }
  subst mem.
  exists before, after, tid, msg, (count + 1).
  split; [exact Hprefix|]. split; [exists tid; split; assumption|].
  split; [exact Hsuffix|]. split; [exact Hmem|]. split.
  - intros other Hne. rewrite Hstate. unfold PState.tstate, compose. cbn.
    apply vlookup_insert_ne. exact Hne.
  - eapply UMThreadReplay.thread_steps_trans; [exact Hthread|].
    rewrite Hts. econstructor.
    + exact Hterm.
    + rewrite <- Himem_before. exact Hinst.
    + constructor.
Qed.

(** This supplies an actual promise-first transition for the first message of
    an interleaved instruction execution and replays the issuing thread's
    prefix. It uses the extracted prefix's fuel; stability at larger fuel and
    replay of the other threads require further arguments. *)
Theorem UMSail_interleaved_first_message_promise initMs code st final :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc instruction_step st final →
  PState.events final ≠ PState.events st →
  ∃ before after (tid : fin n) msg count next,
    rtc FixedHistoryInstructionStep st before ∧
    instruction_step before after ∧
    rtc instruction_step after final ∧
    PState.promise UMPromising msg st = Ok next ∧
    PState.events after = msg :: PState.events st ∧
    Msg.tid msg = (tid : nat) ∧ event_misses_code Msg.read_byte code msg ∧
    (∀ other, tid ≠ other → PState.tstate other after = PState.tstate other before) ∧
    Exec.elem_of_results (next, None)
      (CPState.run_transition_promise_first isem UMPromising term count st) ∧
    PromiseFirstReachable UMPromising isem term initMs true next ∧
    UMThreadReplay.thread_steps tid (PState.initmem next) (term !!! tid) isem
      count (PState.tstate tid next) (PState.events next)
      (PState.tstate tid after) (PState.events after).
Proof.
  intros Hsafe Hreach Htrace Hnew.
  destruct (UMSail_interleaved_first_message_projection st final Htrace Hnew)
    as [before [after [tid [msg [count [Hprefix [Hwrite [Hsuffix [Hmem [Hframe Hthread]]]]]]]]]].
  pose proof (UMThreadCertification.first_new_message_enumerated tid (PState.initmem st)
    term isem count (PState.tstate tid st) (PState.events st)
    (PState.tstate tid after) msg Hthread) as Hcandidate.
  pose proof (UMThreadReplay.first_new_message_owner nondet tid (PState.initmem st)
    (term !!! tid) count (PState.tstate tid st) (PState.events st)
    (PState.tstate tid after) (msg :: PState.events st) Hthread msg eq_refl) as Howner.
  pose proof (UMThreadReplay.UMSail_first_new_message_thread_replay nondet term initMs code
    tid st count (PState.tstate tid after) msg Hsafe Hreach Hthread) as Hreplay.
  destruct (UMPromising_promise_exists msg st) as [next Hpromise].
  assert (Hstep : Exec.elem_of_results (next, None)
    (CPState.run_transition_promise_first isem UMPromising term count st)).
  { eapply run_transition_promise_first_none_intro with (tid := tid) (ev := msg) (nst := next).
    - rewrite promise_first_execution_results_lookup. exact Hcandidate.
    - exact Hpromise.
    - reflexivity. }
  pose proof (UMPromising_enumerated_promise_misses_code isem term initMs code true
    st tid count msg (sail_observed_code_immutable _ _ _ _ _ _ Hsafe) Hreach Hcandidate) as Hmiss.
  exists before, after, tid, msg, count, next.
  split; [exact Hprefix|]. split; [exact Hwrite|]. split; [exact Hsuffix|].
  split; [exact Hpromise|]. split; [exact Hmem|]. split; [exact Howner|].
  split; [exact Hmiss|]. split; [exact Hframe|]. split; [exact Hstep|]. split.
  - eapply PromiseFirstReachable_step; eassumption.
  - destruct (UMPromising_promise_success msg st next Hpromise) as [Himem [Hmem_next Hstates]].
    specialize (Hstates tid).
    rewrite UMPromising_emit_promise_ok, bool_decide_true in Hstates by exact Howner.
    injection Hstates as Hstate.
    rewrite Himem, Hmem_next, <- Hstate, Hmem. exact Hreplay.
Qed.

(** Moving the first event to a promise preserves the entire state reached
    just after that event, including every other thread's executed prefix. *)
Theorem UMSail_interleaved_first_message_replay initMs code st final :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc instruction_step st final →
  PState.events final ≠ PState.events st →
  ∃ msg count next after,
    PState.promise UMPromising msg st = Ok next ∧
    Exec.elem_of_results (next, None)
      (CPState.run_transition_promise_first isem UMPromising term count st) ∧
    PromiseFirstReachable UMPromising isem term initMs true next ∧
    PState.events after = PState.events next ∧
    rtc instruction_step next after ∧ rtc instruction_step after final.
Proof.
  intros Hsafe Hreach Htrace Hnew.
  destruct (UMSail_interleaved_first_message_promise initMs code st final
    Hsafe Hreach Htrace Hnew)
    as [before [after [tid [msg [count [next
      [Hprefix [Hwrite [Hsuffix [Hpromise [Hmem [Howner [Hmiss
        [Hframe [Hstep [Hreach_next Hissuer]]]]]]]]]]]]]]]].
  destruct (fixed_history_trace_projection st before Hprefix)
    as [Himem_before [Hmem_before Hthreads]].
  destruct (UMPromising_promise_success msg st next Hpromise)
    as [Himem_next [Hmem_next Hstates]].
  assert (Hsame : PState.events after = PState.events next).
  { rewrite Hmem, Hmem_next. reflexivity. }
  exists msg, count, next, after.
  split; [exact Hpromise|]. split; [exact Hstep|]. split; [exact Hreach_next|].
  split; [exact Hsame|]. split; [|exact Hsuffix].
  apply finite_all_threads_serialize; [|exact Hsame|].
  - destruct (instruction_step_memory before after Hwrite) as [Himem _]. rewrite Himem, Himem_before, Himem_next. reflexivity.
  - intro other. destruct (decide (tid = other)) as [<-|Hne].
    + exists count. rewrite Hsame in Hissuer. exact Hissuer.
    + destruct (Hthreads other) as [steps Hthread].
      exists steps. rewrite Hframe by exact Hne.
      eapply (UMSail_foreign_message_thread_replay nondet term initMs code other st next
        msg steps (PState.tstate other before)); try eassumption.
      * rewrite Howner. intro Heq. apply Hne. apply fin_to_nat_inj. exact Heq.
      * rewrite Hmem_before in Hthread. exact Hthread.
Qed.

Lemma instruction_trace_memory_suffix st final :
  rtc instruction_step st final →
  ∃ extra, PState.events final = (extra ++ PState.events st)%list.
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail [extra Hextra]].
  - exists []. reflexivity.
  - destruct (instruction_step_memory st mid Hstep) as [_ [Hsame|[msg Hnew]]].
    + exists extra. rewrite Hextra, Hsame. reflexivity.
    + exists (extra ++ [msg])%list. rewrite Hextra, Hnew, <- app_assoc. reflexivity.
Qed.

Lemma instruction_trace_fixed_history st final :
  rtc instruction_step st final →
  PState.events final = PState.events st →
  rtc FixedHistoryInstructionStep st final.
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail IH]; intro Hsame.
  - apply rtc_refl.
  - destruct (instruction_step_memory st mid Hstep) as [_ [Hmem|[msg Hmem]]].
    + eapply rtc_l; [split; eassumption|]. apply IH. congruence.
    + destruct (instruction_trace_memory_suffix mid final Htail) as [extra Hextra].
      rewrite Hmem, Hsame in Hextra. apply (f_equal length) in Hextra.
      rewrite length_app in Hextra. cbn in Hextra. lia.
Qed.

Definition EnumeratedPromiseStep (st next : state) : Prop :=
  ∃ msg fuel, PState.promise UMPromising msg st = Ok next ∧
    Exec.elem_of_results (next, None)
      (CPState.run_transition_promise_first isem UMPromising term fuel st).

Local Lemma normalize_interleaving_bounded initMs code final budget :
  ∀ st,
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc instruction_step st final →
  length (PState.events final) ≤ budget + length (PState.events st) →
  ∃ before,
    rtc EnumeratedPromiseStep st before ∧
    PromiseFirstReachable UMPromising isem term initMs true before ∧
    PState.events before = PState.events final ∧
    rtc instruction_step before final.
Proof.
  induction budget as [|budget IH]; intros st Hsafe Hreach Htrace Hbound.
  - destruct (instruction_trace_memory_suffix st final Htrace) as [extra Hextra].
    assert (Hnil : extra = []).
    { rewrite Hextra, length_app in Hbound. destruct extra; [reflexivity|cbn in Hbound; lia]. }
    subst extra. cbn in Hextra.
    exists st. split; [apply rtc_refl|]. split; [exact Hreach|].
    split; [symmetry; exact Hextra|exact Htrace].
  - destruct (decide (PState.events final = PState.events st)) as [Hsame|Hnew].
    + exists st. split; [apply rtc_refl|]. split; [exact Hreach|].
      split; [symmetry; exact Hsame|exact Htrace].
    + destruct (UMSail_interleaved_first_message_replay initMs code st final
        Hsafe Hreach Htrace Hnew)
        as [msg [fuel [next [after [Hpromise [Hstep [Hreach_next [Hmem [Hprefix Hsuffix]]]]]]]]].
      destruct (UMPromising_promise_success msg st next Hpromise) as [_ [Hnext _]].
      assert (Hbound_next : length (PState.events final) ≤ budget + length (PState.events next)).
      { rewrite Hnext.
        change (length (PState.events final) ≤ budget + S (length (PState.events st))). lia. }
      assert (Htrace_next : rtc instruction_step next final).
      { eapply rtc_trans; eassumption. }
      destruct (IH next Hsafe Hreach_next Htrace_next Hbound_next)
        as [before [Hpromises [Hreach_before [Hfinalmem Hfinaltrace]]]].
      exists before. split.
      * eapply rtc_l; [exists msg, fuel; split; eassumption|exact Hpromises].
      * split; [exact Hreach_before|]. split; assumption.
Qed.

(** All messages in an interleaved instruction trace can be promised before
    replaying its instructions. Each promise uses its own extracted fuel;
    this theorem does not assert one common fuel bound for the whole run. *)
Theorem UMSail_interleaved_message_normalization initMs code st final :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc instruction_step st final →
  ∃ before,
    rtc EnumeratedPromiseStep st before ∧
    PromiseFirstReachable UMPromising isem term initMs true before ∧
    PState.events before = PState.events final ∧
    rtc instruction_step before final.
Proof.
  intros Hsafe Hreach Htrace.
  eapply (normalize_interleaving_bounded initMs code final (length (PState.events final)));
    try eassumption. lia.
Qed.

Theorem UMSail_terminating_interleaved_normalization initMs code st final :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc instruction_step st final →
  (∀ tid, CPState.terminated_ts UMPromising (term !!! tid) (PState.tstate tid final) = true) →
  ∃ before,
    rtc EnumeratedPromiseStep st before ∧
    PromiseFirstReachable UMPromising isem term initMs true before ∧
    PState.initmem before = PState.initmem final ∧
    PState.events before = PState.events final ∧
    (∀ tid, ThreadInstructionExecution UMPromising tid (PState.initmem before) isem term
      (PState.events before) (PState.tstate tid before) (PState.tstate tid final)).
Proof.
  intros Hsafe Hreach Htrace Hterm.
  destruct (UMSail_interleaved_message_normalization initMs code st final Hsafe Hreach Htrace)
    as [before [Hpromises [Hreach_before [Hmem Hfinal]]]].
  pose proof (instruction_trace_fixed_history before final Hfinal (eq_sym Hmem)) as Hfixed.
  destruct (fixed_history_trace_projection before final Hfixed) as [Himem [_ Hthreads]].
  exists before. split; [exact Hpromises|]. split; [exact Hreach_before|].
  split; [symmetry; exact Himem|]. split; [exact Hmem|].
  intro tid. destruct (Hthreads tid) as [count Hthread].
  eapply UMThreadReplay.fixed_thread_steps_execution; [exact Hthread|symmetry; exact Hmem|apply Hterm].
Qed.
End Interleaving.
