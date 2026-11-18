(******************************************************************************)
(* VM enumeration cache validity under promise insertion                    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstExecutionCurrent
  PromiseFirstVMExecutionCurrent PromiseFirstSailVMNormalization PromiseFirstSailVMSwapRemoveInit
  PromiseFirstSailCertification PromiseFirstConcreteCurrent PromiseFirstEquivCurrent
  PromiseFirstSailSerialization PromiseFirstSailVMCacheSim PromiseFirstSailVMFinal.
From ArchSemArm.Proof Require Import PromiseFirstSailVMEnumCacheTransport PromiseFirstSailVMEnumCacheSteps.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMDirect PromiseFirstSailScheduling.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module VMCacheValidity.
Import VMPromising VMEnumCacheSteps.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.
Section Cache.
Context (bbm : bool) {n : nat} (isem : iMon ()) (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation pfstate := (@CPState.pf_t prom n).
Local Notation good := (@VMSwapRemoveInit.state_ok n).
Local Notation ignore_step := (VMCacheTransport.IgnoredStep bbm).

(** A cached enumeration remembers the state and budget where it was made.
    Every intervening promise was ignored by this thread's cache. *)
Definition entry (lower : nat) (tid : fin n) (st : state) (res : CPState.EnumerationResult prom) : Prop :=
  ∃ before fuel, lower ≤ fuel ∧ good before ∧ rtc (ignore_step tid) before st ∧
    res = CPState.enumerate_results isem prom term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before).
Definition valid lower (pst : pfstate) : Prop := good (CPState.pstate prom pst) ∧
  ∀ tid res, CPState.enum_cache prom pst !!! tid = Some res → entry lower tid (CPState.pstate prom pst) res.

Lemma entry_current lower tid st fuel : lower ≤ fuel → good st → entry lower tid st
  (CPState.enumerate_results isem prom term tid (PState.initmem st) fuel
    (PState.tstate tid st) (PState.events st)).
Proof. intros Hfuel Hok. exists st, fuel. split; [exact Hfuel|]. split; [exact Hok|]. split; [apply rtc_refl|reflexivity]. Qed.

Lemma entry_advance lower tid st next res ev : entry lower tid st res → Ev.affects ev tid = false →
  PState.promise prom ev st = Ok next → entry lower tid next res.
Proof.
  intros (before & fuel & Hfuel & Hok & Htrace & Hres) Hignore Hpromise.
  exists before, fuel. split; [exact Hfuel|]. split; [exact Hok|]. split; [|exact Hres].
  eapply rtc_r; [exact Htrace|exists ev; auto].
Qed.

Lemma effective_entry lower fuel pst tid : lower ≤ fuel → valid lower pst → entry lower tid (CPState.pstate prom pst)
  (effective bbm isem term fuel pst !!! tid).
Proof.
  intros Hfuel [Hok Hcache]. unfold effective, vimap. rewrite lookup_fun_to_vec.
  destruct (CPState.enum_cache prom pst !!! tid) as [res|] eqn:Hres.
  - apply Hcache, Hres.
  - apply entry_current; assumption.
Qed.

Lemma empty_valid lower st : good st → valid lower (CPState.PFMake prom st (vreplicate n None)).
Proof.
  intro Hok. split; [exact Hok|]. intros tid res Hcache.
  cbn [CPState.enum_cache] in Hcache. rewrite vlookup_replicate in Hcache. discriminate.
Qed.

Lemma valid_weaken lower upper pst : lower ≤ upper → valid upper pst → valid lower pst.
Proof.
  intros Hle [Hok Hentries]. split; [exact Hok|]. intros tid res Hin.
  destruct (Hentries tid res Hin) as (before & fuel & Hfuel & Hstate & Hsteps & Hres).
  exists before, fuel. split; [lia|]. auto.
Qed.

Theorem advance_valid lower fuel pst ev next : lower ≤ fuel → valid lower pst →
  PState.promise prom ev (CPState.pstate prom pst) = Ok next → valid lower (advance bbm isem term fuel pst ev next).
Proof.
  intros Hfuel Hvalid Hpromise. split.
  - eapply VMSwapRemoveInit.promise_ok; [apply Hvalid|exact Hpromise].
  - intros tid res Hcache. unfold advance in Hcache. cbn [CPState.enum_cache] in Hcache.
    unfold vimap in Hcache. rewrite lookup_fun_to_vec in Hcache.
    destruct (Ev.affects ev tid) eqn:Hignore; [discriminate|]. injection Hcache as <-.
    eapply entry_advance; [apply effective_entry; assumption|exact Hignore|exact Hpromise].
Qed.

Theorem entry_candidate lower tid st res candidate : entry lower tid st res →
  candidate ∈ CPState.promises prom res → ∃ fuel,
  candidate ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid
    (PState.initmem st) fuel (PState.tstate tid st) (PState.events st)).
Proof.
  intros (before & fuel & _ & Hok & Htrace & ->) Hin. exists fuel.
  apply (proj1 (VMCacheTransport.ignored_trace_candidates bbm isem term tid before st
    fuel candidate Hok Htrace)), Hin.
Qed.

Theorem entry_final lower tid st res final : entry lower tid st res →
  final ∈ CPState.final_states prom res →
  ThreadInstructionExecution prom tid (PState.initmem st) isem term (PState.events st)
    (PState.tstate tid st) final.
Proof.
  intros (before & fuel & _ & Hok & Htrace & ->) Hin.
  apply (VMCacheTransport.ignored_trace_execution bbm isem term tid before st final Hok Htrace).
  apply (enumerated_final_thread_execution prom isem term tid (PState.initmem before)
    fuel (PState.tstate tid before) (PState.events before) final
    (VMMemoryGrowth.outcome_memory_growth bbm)). exact Hin.
Qed.

(** Cache hits may use an earlier budget. They still supply an actual
    promise-first step at some finite budget in the current history. *)
Theorem none_sound fuel pst pst' : valid 0 pst →
  Exec.elem_of_results (pst', None) (CPState.run_transition_promise_first isem prom term fuel pst) →
  valid 0 pst' ∧ ∃ budget, Exec.elem_of_results (CPState.pstate prom pst', None)
    (CPState.run_transition_promise_first_uncached isem prom term budget (CPState.pstate prom pst)).
Proof.
  intros Hvalid Hrun. destruct (none_inv bbm isem term fuel pst pst' Hrun)
    as (tid & ev & next & Hcandidate & Hpromise & ->).
  split; [apply advance_valid; [lia|exact Hvalid|exact Hpromise]|].
  pose proof (VMPromising_filter_promises_subset bbm n tid _ _ ev Hcandidate) as Hraw.
  destruct (entry_candidate 0 tid (CPState.pstate prom pst) (effective bbm isem term fuel pst !!! tid) ev
    (effective_entry 0 fuel pst tid (Nat.le_0_l _) Hvalid) Hraw) as [budget Hcurrent].
  exists budget. cbn [advance CPState.pstate].
  eapply (run_transition_promise_first_none_intro (prom := prom))
    with (tid := tid) (ev := ev) (nst := next); [|exact Hpromise|reflexivity].
  rewrite promise_first_execution_results_lookup.
  unfold CPState.enumerate_results_filtered.
  eapply (VM_filter_retains_membership bbm); [exact Hcandidate|exact Hcurrent].
Qed.
End Cache.

Section Sail.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation pfstate := (@CPState.pf_t prom n).

(** An earlier cache fill may have a larger budget than the transition
    using it. A candidate that persists above [lower] is available in both. *)
Lemma stable_entry lower (pst : pfstate) fuel tid ev :
  lower ≤ fuel → valid bbm isem term lower pst →
  (∀ budget, lower ≤ budget → ev ∈ CPState.promises prom
    (CPState.enumerate_results_filtered isem prom term tid (PState.initmem (CPState.pstate prom pst))
      budget (PState.tstate tid (CPState.pstate prom pst)) (PState.events (CPState.pstate prom pst)))) →
  ev ∈ prom.(Promising.filter_promises) n tid (PState.events (CPState.pstate prom pst))
    (CPState.promises prom (effective bbm isem term fuel pst !!! tid)).
Proof.
  intros Hfuel Hvalid Hstable.
  destruct (effective_entry bbm isem term lower fuel pst tid Hfuel Hvalid)
    as (before & saved & Hsaved & Hok & Htrace & Hres).
  rewrite Hres. specialize (Hstable saved Hsaved).
  eapply (VM_filter_retains_membership bbm); [exact Hstable|].
  apply (proj2 (VMCacheTransport.ignored_trace_candidates bbm isem term tid before
    (CPState.pstate prom pst) saved ev Hok Htrace)).
  eapply VMPromising_filter_promises_subset. exact Hstable.
Qed.

(** A cached terminating transition supplies one concrete instruction trace
    per thread. Serializing them preserves the history used for validation. *)
Lemma some_sound fuel (pst pst' : pfstate) fsig :
  valid bbm isem term 0 pst →
  Exec.elem_of_results (pst', Some fsig) (CPState.run_transition_promise_first isem prom term fuel pst) →
  ∃ final, rtc (VMNormalization.Fixed bbm nondet term) (CPState.pstate prom pst) final ∧
    VMNormalization.FinalResult bbm term final (projT1 fsig).
Proof.
  intros Hv Hrun. destruct (some_inv bbm isem term fuel pst pst' fsig Hrun)
    as (states & pt & Hstates & Hvalid & ->).
  exists (PState.Make states (PState.initmem (CPState.pstate prom pst))
    (PState.events (CPState.pstate prom pst))). split.
  - apply VMNormalization.mixed_rtc_fixed; [|reflexivity].
    apply VMNormalization.inst_rtc_mixed, serialize_all_threads; [reflexivity|reflexivity|].
    intro tid. eapply (entry_final bbm isem term 0 tid _ (effective bbm isem term fuel pst !!! tid));
      [apply effective_entry; [lia|exact Hv]|apply Hstates].
  - exists pt. split; [apply validate_result, Hvalid|reflexivity].
Qed.

Lemma run_trace initMs fuel (pst returned : pfstate) fsig :
  valid bbm isem term 0 pst →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs pst) →
  ∃ before final,
    rtc (VMNormalization.PromStep bbm nondet term) (CPState.pstate prom pst) before ∧
    rtc (VMNormalization.Fixed bbm nondet term) before final ∧
    VMNormalization.FinalResult bbm term final (projT1 fsig).
Proof.
  revert pst. induction fuel as [|fuel IH]; intros pst Hv Hrun.
  - cbn [opModel.run] in Hrun. inversion Hrun.
  - cbn [opModel.run] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as (mid & res & Hstep & Htail).
    destruct res as [result|].
    + apply Exec.elem_of_mret_inv in Htail as [_ Hsig]. subst result.
      destruct (some_sound (S fuel) pst mid fsig Hv Hstep) as (final & Hi & Hf).
      exists (CPState.pstate prom pst), final. split; [apply rtc_refl|auto].
    + destruct (none_sound bbm isem term (S fuel) pst mid Hv Hstep) as [Hmid Hprom].
      destruct (IH mid Hmid Htail) as (before & final & Hprefix & Hi & Hf).
      exists before, final. split; [eapply rtc_l; eassumption|auto].
Qed.

Theorem cached_final_trace initMs fuel fs (pt : archState.is_terminated term fs) :
  archModel.Res.FinalState fs pt ∈ Promising_to_Modelc_pf prom isem fuel n term initMs →
  VMFinal.PromiseFirstFinal bbm nondet term initMs fs.
Proof.
  unfold Promising_to_Modelc_pf, opModel.to_archModel. cbn.
  destruct (PState.from_archState prom initMs) as [init|err] eqn:Hinit.
  - intro Hin. destruct (final_state_from_exec_inv
      (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs)
      (CPState.PFMake prom init (vreplicate n None)) fs pt Hin) as (returned & fsig & Hrun & Hfs).
    destruct (run_trace initMs fuel _ returned fsig
      (empty_valid bbm isem term 0 init (VMSwapRemoveInit.from_archState_ok bbm initMs init Hinit)) Hrun)
      as (before & final & Hprefix & Hi & Hf).
    exists before, final. split.
    + eapply VMNormalization.prom_rtc_reachable; [apply PromiseFirstReachable_init, Hinit|exact Hprefix].
    + rewrite <- Hfs. auto.
  - intro Hin. change ((archModel.Res.FinalState fs pt : archModel.res ∅ n term) ∈ [archModel.Res.Error err]) in Hin.
    apply list_elem_of_singleton in Hin. discriminate.
Qed.

(** A validated normalized trace supplies a stable prefix and one terminating
    enumeration of the final fixed-history suffix. *)
Lemma normalized_batch initMs fs :
  VMFinal.PromiseFirstFinal bbm nondet term initMs fs →
  ∃ init before budget (sig : {s & archState.is_terminated term s}),
    PState.from_archState prom initMs = Ok init ∧
    rtc (StableCertifiedPromiseStep prom nondet term) init before ∧ projT1 sig = fs ∧
    Exec.elem_of_results (before, Some sig) (CPState.run_transition_promise_first_uncached
      isem prom term budget before).
Proof.
  intros (before & final & Hreach & Hsuffix & Hvalid).
  destruct (VMNormalization.reachable_prom_trace bbm nondet term initMs before Hreach)
    as (init & Hinit & Hprefix).
  destruct (VMNormalization.normalized_prefix_stable_or_truncated bbm nondet term initMs fs
    init before final Hprefix (PromiseFirstReachable_init _ _ _ _ _ _ Hinit) Hsuffix Hvalid)
    as [Hsteps|(start & next & budget & tid & ev & Hr & Hcandidate & Hev & Hcont & Hunstable & _)].
  - pose proof (VMViews.reachable_ok bbm isem term initMs true before Hreach) as Hok.
    pose proof (VMNormalization.fixed_rtc_ok bbm nondet term before final Hok Hsuffix) as Hfinal.
    destruct Hvalid as [pt [Hcheck Hfs]].
    destruct (VMSail_fixed_history_final_batch bbm nondet term before final final pt
      (VMNormalization.fixed_rtc_bounded bbm nondet term before final Hok Hsuffix)
      (λ tid, VMNormalization.ts_ok_min_view _ _ (Hfinal tid)) Hcheck) as [budget Hbatch].
    exists init, before, budget, (CPState.to_final_archState (CPState.make_final prom term final pt)).
    auto.
  - exfalso. apply Hunstable. eapply (VMFinal.completing_candidates_stable bbm nondet term initMs); [exact Hr|exact Hcandidate|exact Hev|].
    destruct Hcont as (last & Hmixed & Hf). exists last, fs. auto.
Qed.

(** Replay a cached final through its certified prefix in the direct runner. *)
Theorem cached_to_direct initMs fuel fs (pt : archState.is_terminated term fs) :
  archModel.Res.FinalState fs pt ∈ Promising_to_Modelc_pf prom isem fuel n term initMs →
  ∃ direct_fuel (pt' : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt' ∈ Promising_to_Modelc prom isem direct_fuel n term initMs.
Proof.
  intro Hrun. destruct (normalized_batch initMs fs (cached_final_trace initMs fuel fs pt Hrun))
    as (init & before & budget & [fs' pt'] & Hinit & Hsteps & Hfs & Hbatch).
  cbn in Hfs. subst fs'. destruct (VMSail_stable_prefix_common_fuel bbm nondet term initMs
    init before before budget _ Hsteps Hbatch) as (last & cost & Hboth).
  destruct (Hboth (S cost) ltac:(lia)) as [Hdirect _]. exists (S cost), pt'.
  eapply (direct_final_state_intro (prom := prom)); eassumption.
Qed.
End Sail.
End VMCacheValidity.
