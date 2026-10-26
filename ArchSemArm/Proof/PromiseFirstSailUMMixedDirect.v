(******************************************************************************)
(* Normalizing complete mixed UM traces, including fresh instruction writes  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent
  PromiseFirstEquivCurrent PromiseFirstSailCurrent PromiseFirstSailOwnership
  PromiseFirstSailInterleaving PromiseFirstSailMixed PromiseFirstSailSerialization
  PromiseFirstSailScheduling PromiseFirstSailCertification PromiseFirstSailNoFuel
  PromiseFirstSailFinalization.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.

Section MixedDirect.
Context (nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t UMPromising.TState.t Msg.t n).
Local Notation instruction := (InstructionTransition UMPromising nondet term).
Local Notation fixed := (FixedHistoryInstructionStep nondet term).
Local Notation promise := (EnumeratedPromiseStep nondet term).

Definition UMMixedStep (st next : state) : Prop := instruction st next ∨ promise st next.

Lemma enumerated_promise_before_fixed_prefix initMs code st before after :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc fixed st before → promise before after →
  ∃ next, promise st next ∧
    PromiseFirstReachable UMPromising isem term initMs true next ∧ rtc fixed next after.
Proof.
  intros Hsafe Hreach Hprefix [msg [fuel [Hlate Hstep]]].
  destruct (run_transition_promise_first_none_inv (prom := UMPromising) isem term
    fuel before after Hstep) as [tid [ev [nst [Hcandidate [Hpromise Hstate]]]]].
  subst nst. rewrite promise_first_execution_results_lookup in Hcandidate.
  destruct (UMPromising_promise_success msg before after Hlate) as [_ [Hmsg _]].
  destruct (UMPromising_promise_success ev before after Hpromise) as [_ [Hev _]].
  rewrite Hmsg in Hev. injection Hev as Heq. subst ev.
  destruct (UMSail_interleaved_candidate_before_prefix nondet term st before
    tid fuel msg Hprefix Hcandidate) as [count Hearly].
  destruct (UMPromising_promise_exists msg st) as [next Hemit].
  assert (Hearly_step : Exec.elem_of_results (next, None)
    (CPState.run_transition_promise_first isem UMPromising term (count + fuel) st)).
  { eapply (run_transition_promise_first_none_intro (prom := UMPromising))
      with (tid := tid) (ev := msg) (nst := next).
    - rewrite promise_first_execution_results_lookup. exact Hearly.
    - exact Hemit.
    - reflexivity. }
  pose proof (UMCollectedOwnership.enumerated_promise_owner tid
    (PState.initmem before) isem term fuel (PState.tstate tid before)
    (PState.events before) msg Hcandidate) as Howner.
  destruct (UMMixedCertification.candidate_bounds tid (PState.initmem before) term
    isem fuel (PState.tstate tid before) (PState.events before) msg Hcandidate)
    as [_ [Hbound _]].
  destruct (fixed_history_trace_projection nondet term st before Hprefix) as [_ [Hmem _]].
  rewrite Hmem in Hbound.
  pose proof (UMPromising_enumerated_promise_misses_code isem term initMs code true
    st tid (count + fuel) msg (sail_observed_code_immutable _ _ _ _ _ _ Hsafe)
    Hreach Hearly) as Hmiss.
  exists next. split; [exists msg, (count + fuel); auto|]. split.
  - eapply PromiseFirstReachable_step; eassumption.
  - apply instruction_trace_fixed_history.
    + eapply UMSail_fixed_prefix_promise_replay; eassumption.
    + destruct (UMPromising_promise_success msg st next Hemit) as [_ [Hnext _]].
      rewrite Hmsg, Hnext, Hmem. reflexivity.
Qed.

Lemma mixed_step_memory st next : UMMixedStep st next →
  PState.events next = PState.events st ∨ ∃ msg, PState.events next = msg :: PState.events st.
Proof.
  intros [Hinst|[msg [fuel [Hpromise _]]]].
  - exact (proj2 (instruction_step_memory nondet term st next Hinst)).
  - right. exists msg. exact (proj1 (proj2 (UMPromising_promise_success msg st next Hpromise))).
Qed.

Lemma mixed_memory_suffix st final : rtc UMMixedStep st final →
  ∃ extra, PState.events final = (extra ++ PState.events st)%list.
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail [extra Hextra]].
  - exists []; reflexivity.
  - destruct (mixed_step_memory st mid Hstep) as [Hsame|[msg Hnew]].
    + exists extra. rewrite Hextra, Hsame. reflexivity.
    + exists (extra ++ [msg])%list. rewrite Hextra, Hnew, <- app_assoc. reflexivity.
Qed.

Lemma mixed_step_fixed st next : UMMixedStep st next →
  PState.events next = PState.events st → fixed st next.
Proof.
  intros [Hinst|[msg [fuel [Hpromise _]]]] Hsame; [split; assumption|].
  destruct (UMPromising_promise_success msg st next Hpromise) as [_ [Hnew _]].
  rewrite Hsame in Hnew. apply (f_equal length) in Hnew. cbn in Hnew. lia.
Qed.

Lemma mixed_fixed_history st final : rtc UMMixedStep st final →
  PState.events final = PState.events st → rtc fixed st final.
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail IH]; intro Hsame.
  - apply rtc_refl.
  - destruct (mixed_step_memory st mid Hstep) as [Hmem|[msg Hnew]].
    + eapply rtc_l; [apply mixed_step_fixed; eassumption|]. apply IH. rewrite Hmem; exact Hsame.
    + destruct (mixed_memory_suffix mid final Htail) as [extra Hextra].
      rewrite Hnew, Hsame in Hextra. apply (f_equal length) in Hextra.
      rewrite length_app in Hextra. cbn in Hextra. lia.
Qed.

Lemma first_mixed_event st final : rtc UMMixedStep st final →
  PState.events final ≠ PState.events st →
  ∃ before after, rtc fixed st before ∧ UMMixedStep before after ∧
    PState.events after ≠ PState.events before ∧ rtc UMMixedStep after final.
Proof.
  intro Htrace. induction Htrace as [st|st mid final Hstep Htail IH]; intro Hnew;
    [contradiction|].
  destruct (decide (PState.events mid = PState.events st)) as [Hsame|Hdifferent].
  - destruct (IH ltac:(rewrite Hsame; exact Hnew)) as [before [after [Hprefix Hrest]]].
    exists before, after. split; [|exact Hrest].
    eapply rtc_l; [apply mixed_step_fixed; eassumption|exact Hprefix].
  - exists st, mid. split; [apply rtc_refl|auto].
Qed.

Lemma first_mixed_event_replay initMs code st before after :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc fixed st before → UMMixedStep before after →
  PState.events after ≠ PState.events before →
  ∃ next, promise st next ∧
    PromiseFirstReachable UMPromising isem term initMs true next ∧ rtc fixed next after.
Proof.
  intros Hsafe Hreach Hprefix [Hinst|Hpromise] Hnew.
  - assert (Htrace : rtc instruction st after).
    { eapply rtc_trans with (y := before).
      - clear -Hprefix. induction Hprefix; [apply rtc_refl|].
        eapply rtc_l; [exact (proj1 H)|exact IHHprefix].
      - apply rtc_once. exact Hinst. }
    destruct (fixed_history_trace_projection nondet term st before Hprefix) as [_ [Hmem _]].
    assert (Hchanged : PState.events after ≠ PState.events st) by (rewrite <- Hmem; exact Hnew).
    destruct (UMSail_interleaved_first_message_replay nondet term initMs code st after
      Hsafe Hreach Htrace Hchanged)
      as [msg [fuel [next [middle [Hemit [Hstep [Hreach_next [Hmiddle [Hreplay Hsuffix]]]]]]]]].
    exists next. split; [exists msg, fuel; auto|]. split; [exact Hreach_next|].
    apply instruction_trace_fixed_history; [eapply rtc_trans; eassumption|].
    destruct (instruction_step_memory nondet term before after Hinst) as [_ [Hsame|[other Hafter]]];
      [contradiction|].
    destruct (UMPromising_promise_success msg st next Hemit) as [_ [Hnext _]].
    destruct (instruction_trace_memory_suffix nondet term middle after Hsuffix) as [extra Hextra].
    rewrite Hmiddle, Hnext, Hafter, Hmem in Hextra.
    assert (Hempty : extra = []).
    { apply (f_equal length) in Hextra. rewrite length_app in Hextra.
      destruct extra; [reflexivity|cbn in Hextra; lia]. }
    subst extra. cbn in Hextra. rewrite Hafter, Hmem, Hnext. exact Hextra.
  - eapply enumerated_promise_before_fixed_prefix; eassumption.
Qed.

Local Lemma normalize_mixed_bounded initMs code final budget : ∀ st,
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc UMMixedStep st final →
  length (PState.events final) ≤ budget + length (PState.events st) →
  ∃ before, rtc promise st before ∧
    PromiseFirstReachable UMPromising isem term initMs true before ∧ rtc fixed before final.
Proof.
  induction budget as [|budget IH]; intros st Hsafe Hreach Htrace Hbound.
  - destruct (mixed_memory_suffix st final Htrace) as [extra Hextra].
    assert (Hnil : extra = []).
    { rewrite Hextra, length_app in Hbound. destruct extra; [reflexivity|cbn in Hbound; lia]. }
    subst extra. cbn in Hextra. exists st. split; [apply rtc_refl|]. split; [exact Hreach|].
    apply mixed_fixed_history; assumption.
  - destruct (decide (PState.events final = PState.events st)) as [Hsame|Hnew].
    + exists st. split; [apply rtc_refl|]. split; [exact Hreach|]. apply mixed_fixed_history; assumption.
    + destruct (first_mixed_event st final Htrace Hnew)
        as [before [after [Hprefix [Hstep [Hchanged Hsuffix]]]]].
      destruct (first_mixed_event_replay initMs code st before after Hsafe Hreach Hprefix Hstep Hchanged)
        as [next [Hpromise [Hreach_next Hreplay]]].
      assert (Hnext_trace : rtc UMMixedStep next final).
      { eapply rtc_trans; [|exact Hsuffix]. clear -Hreplay.
        induction Hreplay; [apply rtc_refl|]. eapply rtc_l; [left; exact (proj1 H)|exact IHHreplay]. }
      assert (Hnext_bound : length (PState.events final) ≤ budget + length (PState.events next)).
      { destruct Hpromise as [msg [fuel [Hemit _]]].
        destruct (UMPromising_promise_success msg st next Hemit) as [_ [Hmem _]].
        rewrite Hmem. cbn [length]. rewrite Nat.add_succ_r. exact Hbound. }
      destruct (IH next Hsafe Hreach_next Hnext_trace Hnext_bound)
        as [last [Hpromises [Hreach_last Hfixed]]].
      exists last. split; [eapply rtc_l; eassumption|auto].
Qed.

(** Both fresh instruction writes and explicit promise steps are moved into
    the prefix. The endpoint, including all threads and memory, is unchanged.
    This stage records the actual certification fuel of each promise step. *)
Theorem UMSail_full_mixed_normalization initMs code st final :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc UMMixedStep st final →
  ∃ before, rtc promise st before ∧
    PromiseFirstReachable UMPromising isem term initMs true before ∧ rtc fixed before final.
Proof.
  intros Hsafe Hreach Htrace.
  eapply (normalize_mixed_bounded initMs code final (length (PState.events final)));
    try eassumption. lia.
Qed.

Lemma direct_run_mixed_trace initMs fuel st returned fsig :
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem UMPromising n) fuel term initMs st) →
  ∃ final (pt : CPState.terminated UMPromising term final),
    rtc UMMixedStep st final ∧
    Exec.elem_of_results (returned, ()) (CPState.validate_final UMPromising final final) ∧
    fsig = CPState.to_final_archState (CPState.make_final UMPromising term final pt).
Proof.
  revert st. induction fuel as [|fuel IH]; intros st Hrun.
  - cbn [opModel.run] in Hrun. change ((returned, fsig) ∈ []) in Hrun. inversion Hrun.
  - cbn [opModel.run] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [next [res [Hstep Htail]]].
    destruct res as [result|].
    + apply Exec.elem_of_mret_inv in Htail as [Hreturned Hsig]. subst next result.
      destruct (run_transition_some_inv (prom := UMPromising) isem term (S fuel)
        st returned fsig Hstep) as [pt [Hvalid Hsig]].
      exists st, pt. split; [apply rtc_refl|auto].
    + destruct (IH next Htail) as [final [pt [Htrace Hrest]]].
      exists final, pt. split; [|exact Hrest]. eapply rtc_l; [|exact Htrace].
      destruct (direct_none_to_promise_first_none_or_run_tid (prom := UMPromising)
        isem term (S fuel) st next Hstep) as [Hpromise|Hinst]; [right|left; exact Hinst].
      destruct (run_transition_promise_first_none_inv (prom := UMPromising) isem term
        (S fuel) st next Hpromise) as [tid [msg [nst [_ [Hemit Hnext]]]]].
      subst nst. exists msg, (S fuel). auto.
Qed.

(** A certificate exposed by normalization which does not persist at larger
    fuel. Its enumeration really reports OutOfFuel, and emitting the candidate
    leaves a mixed continuation to the same final state. *)
Definition UMTruncatedNormalizationCandidate initMs (final : state) : Prop :=
  ∃ before next fuel tid msg,
    PromiseFirstReachable UMPromising isem term initMs true before ∧
    msg ∈ (CPState.enumerate_results isem UMPromising term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.promises UMPromising) ∧
    PState.promise UMPromising msg before = Ok next ∧
    rtc UMMixedStep next final ∧
    ¬ StablePromiseCandidate UMPromising nondet term tid (PState.initmem before)
      (PState.tstate tid before) (PState.events before) msg ∧
    (CPState.enumerate_results isem UMPromising term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.out_of_fuel UMPromising) = true.

Lemma normalized_prefix_stable_or_truncated initMs final st before :
  rtc promise st before →
  PromiseFirstReachable UMPromising isem term initMs true st →
  rtc fixed before final →
  rtc (StableCertifiedPromiseStep UMPromising nondet term) st before ∨
  UMTruncatedNormalizationCandidate initMs final.
Proof.
  intro Hprefix. induction Hprefix as [st|st next before Hstep Htail IH];
    intros Hreach Hsuffix.
  - left; apply rtc_refl.
  - destruct Hstep as [event [fuel [Hemit Hstep]]].
    destruct (run_transition_promise_first_none_inv (prom := UMPromising) isem term
      fuel st next Hstep) as [tid [msg [nst [Hcandidate [Hpromise Hnext]]]]].
    subst nst. rewrite promise_first_execution_results_lookup in Hcandidate.
    destruct (classic (StablePromiseCandidate UMPromising nondet term tid
      (PState.initmem st) (PState.tstate tid st) (PState.events st) msg))
      as [Hstable|Hunstable].
    + assert (Hreach_next : PromiseFirstReachable UMPromising isem term initMs true next).
      { eapply PromiseFirstReachable_step; eassumption. }
      destruct (IH Hreach_next Hsuffix) as [Hstable_tail|Hbad]; [left|right; exact Hbad].
      eapply rtc_l; [exists tid, msg; split; [exact Hstable|exact Hpromise]|exact Hstable_tail].
    + right. exists st, next, fuel, tid, msg.
      split; [exact Hreach|]. split; [exact Hcandidate|]. split; [exact Hpromise|]. split.
      * eapply rtc_trans with (y := before).
        -- clear -Htail. induction Htail; [apply rtc_refl|].
           eapply rtc_l; [right; exact H|exact IHHtail].
        -- clear -Hsuffix. induction Hsuffix; [apply rtc_refl|].
           eapply rtc_l; [left; exact (proj1 H)|exact IHHsuffix].
      * split; [exact Hunstable|].
        destruct (candidate_stable_or_out_of_fuel UMPromising nondet term tid
          (PState.initmem st) fuel (PState.tstate tid st) (PState.events st) msg
          ltac:(intros; assumption) UM_filter_retains_membership Hcandidate)
          as [Hstable|[proms [ppst [_ Hout]]]]; [contradiction|].
        eapply out_of_fuel_certification_flag; exact Hout.
Qed.

(** No completeness premise is needed for this alternative. It applies to
    successful actual direct runs of any finite number of Sail UM threads,
    including fresh writes and explicit promises in any interleaving. *)
Theorem UMSail_direct_to_promise_first_or_truncated initMs code fuel st returned fsig :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem UMPromising n) fuel term initMs st) →
  UMFinalViewBound returned →
  (∃ before cost, ∀ pf_fuel, cost < pf_fuel →
    Exec.elem_of_results (before, fsig)
      (opModel.run (@CPState.opmodel_pf isem UMPromising n) pf_fuel term initMs st)) ∨
  UMTruncatedNormalizationCandidate initMs returned.
Proof.
  intros Hsafe Hreach Hrun Hbound.
  destruct (direct_run_mixed_trace initMs fuel st returned fsig Hrun)
    as [final [pt [Htrace [Hvalid Hsig]]]].
  pose proof (validate_final_preserves_state UMPromising final final returned Hvalid) as Heq.
  subst returned.
  destruct (UMSail_full_mixed_normalization initMs code st final Hsafe Hreach Htrace)
    as [before [Hprefix [_ Hsuffix]]].
  destruct (normalized_prefix_stable_or_truncated initMs final st before Hprefix Hreach Hsuffix)
    as [Hstable|Hbad]; [left|right; exact Hbad].
  destruct (UMSail_fixed_history_final_batch nondet term before final final pt
    Hsuffix Hbound Hvalid) as [cert_fuel Hbatch].
  rewrite <- Hsig in Hbatch.
  destruct (stable_prefix_promise_first_run UMPromising nondet term initMs st
    before before cert_fuel fsig Hstable Hbatch) as [cost Hpf].
  exists before, cost. exact Hpf.
Qed.

(** Completeness is required only for candidate-bearing searches admitting
    a continuation to this endpoint. These include searches constructed by
    normalization, not just those performed by the original direct runner.
    This is an explicit additional premise; completeness at one larger fuel
    does not establish it for smaller searches. *)
Definition UMNormalizationSearchesComplete initMs (final : state) : Prop :=
  ∀ before next fuel tid msg,
    PromiseFirstReachable UMPromising isem term initMs true before →
    msg ∈ (CPState.enumerate_results isem UMPromising term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.promises UMPromising) →
    PState.promise UMPromising msg before = Ok next →
    rtc UMMixedStep next final →
    (CPState.enumerate_results isem UMPromising term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.out_of_fuel UMPromising) = false.

Theorem UMSail_full_mixed_direct_to_promise_first initMs code fuel st returned fsig :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising isem term initMs true st →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem UMPromising n) fuel term initMs st) →
  UMFinalViewBound returned → UMNormalizationSearchesComplete initMs returned →
  ∃ before cost, ∀ pf_fuel, cost < pf_fuel →
    Exec.elem_of_results (before, fsig)
      (opModel.run (@CPState.opmodel_pf isem UMPromising n) pf_fuel term initMs st).
Proof.
  intros Hsafe Hreach Hrun Hbound Hcomplete.
  destruct (UMSail_direct_to_promise_first_or_truncated initMs code fuel st returned fsig
    Hsafe Hreach Hrun Hbound) as [Hpf|[before [next [search_fuel [tid [msg
      [Hbefore [Hcandidate [Hpromise [Hsuffix [_ Hout]]]]]]]]]]]; [exact Hpf|].
  specialize (Hcomplete before next search_fuel tid msg Hbefore Hcandidate Hpromise Hsuffix).
  congruence.
Qed.

Corollary UMSail_full_mixed_final_inclusion initMs code fuel initPs returned
    fs (pt : archState.is_terminated term fs) :
  UMSailNoSelfModifying nondet term initMs code →
  PState.from_archState UMPromising initMs = Ok initPs →
  Exec.elem_of_results (returned, existT fs pt)
    (opModel.run (@CPState.opmodel isem UMPromising n) fuel term initMs initPs) →
  UMFinalViewBound returned → UMNormalizationSearchesComplete initMs returned →
  ∃ cost, ∀ pf_fuel, cost < pf_fuel →
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf UMPromising isem pf_fuel n term initMs.
Proof.
  intros Hsafe Hinit Hrun Hbound Hcomplete.
  destruct (UMSail_full_mixed_direct_to_promise_first initMs code fuel initPs returned
    (existT fs pt) Hsafe (PromiseFirstReachable_init _ _ _ _ _ _ Hinit)
    Hrun Hbound Hcomplete) as [before [cost Hpf]].
  exists cost. intros pf_fuel Hfuel.
  eapply (promise_first_final_state_intro (prom := UMPromising));
    [exact Hinit|apply Hpf, Hfuel].
Qed.
End MixedDirect.
