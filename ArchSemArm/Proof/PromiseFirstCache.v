From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent.

Open Scope stdpp.

Section Cache.
Context (prom : Promising.Model) (isem : iMon ()) {n : nat}
  (term : terminationCondition n).
Local Notation state := (PState.t prom.(Promising.tState) prom.(Promising.mEvent) n).
Definition empty_cache (st : state) := CPState.PFMake prom st (vreplicate n None).
Definition raw_results fuel (st : state) :=
  vimap (λ tid ts, CPState.enumerate_results isem prom term tid
    (PState.initmem st) fuel ts (PState.events st)) (PState.tstates st).

Lemma empty_cache_results fuel st :
  vimap (λ tid ts,
    if CPState.enum_cache prom (empty_cache st) !!! tid is Some res then res
    else CPState.enumerate_results isem prom term tid (PState.initmem st)
      fuel ts (PState.events st)) (PState.tstates st) = raw_results fuel st.
Proof using All.
  apply vec_eq. intro tid. unfold vimap. rewrite !lookup_fun_to_vec.
  cbn [empty_cache CPState.enum_cache]. rewrite vlookup_replicate. reflexivity.
Qed.

Lemma raw_filtered_promises fuel st (tid : fin n) :
  prom.(Promising.filter_promises) n tid (PState.events st)
    (CPState.promises prom (raw_results fuel st !!! tid)) =
  CPState.promises prom (promise_first_execution_results isem term fuel st !!! tid).
Proof using All.
  rewrite promise_first_execution_results_lookup.
  unfold raw_results. unfold vimap. rewrite lookup_fun_to_vec.
  reflexivity.
Qed.

Lemma raw_filtered_final_states fuel st :
  vmap (CPState.final_states prom) (raw_results fuel st) =
  vmap (CPState.final_states prom) (promise_first_execution_results isem term fuel st).
Proof using All.
  apply vec_eq. intro tid. rewrite vlookup_map, vlookup_map, promise_first_execution_results_lookup.
  unfold raw_results. unfold vimap. rewrite lookup_fun_to_vec. reflexivity.
Qed.

Lemma validate_final_state_success (st st0 st' : state) :
  Exec.elem_of_results (st', ()) (CPState.validate_final_state prom st0 st) →
  st' = st ∧ Exec.elem_of_results () (CPState.validate_final prom st0).
Proof using All.
  unfold CPState.validate_final_state, CPState.validate_final.
  intro H. apply Exec.elem_of_bind_elim in H as [mid [pt [Hguard Htail]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  destruct (CPState.check_valid_end prom st0) as [|err errs].
  - apply Exec.elem_of_mret_inv in Htail as [-> _]. split; [reflexivity|].
    eapply Exec.elem_of_res_bind_intro with (a := pt).
    + unfold guard_discard. destruct (decide (CPState.nopromises prom st0)) as [p|Hp].
      * replace pt with p by apply proof_irrelevance. apply list_elem_of_singleton. reflexivity.
      * contradiction.
    + apply list_elem_of_singleton. reflexivity.
  - apply Exec.elem_of_bind_elim in Htail as [mid [e [_ Hthrow]]].
    inversion Hthrow.
Qed.

Hypothesis affects_all : ∀ ev tid, prom.(Promising.mEvent_affects) ev tid = true.

Lemma cache_none fuel st st' :
  Exec.elem_of_results (st', None)
    (CPState.run_transition_promise_first_uncached isem prom term fuel st) →
  Exec.elem_of_results (empty_cache st', None)
    (CPState.run_transition_promise_first isem prom term fuel (empty_cache st)).
Proof using All.
  intro H. destruct (run_transition_promise_first_none_inv isem term fuel st st' H)
    as [tid [ev [nst [Hev [Hpromise ->]]]]].
  unfold CPState.run_transition_promise_first.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  cbn [empty_cache CPState.pstate]. rewrite empty_cache_results.
  eapply Exec.elem_of_bind_intro with (a := 0%nat);
    [apply Exec.elem_of_mchoosel; cbn; set_solver|].
  eapply Exec.elem_of_bind_intro with (a := tid).
  { unfold mchoosef. apply Exec.elem_of_mchoosel. apply Exec.elem_of_fin_enum. }
  eapply Exec.elem_of_bind_intro with (a := ev).
  { apply Exec.elem_of_lift_res. unfold CPState.choose_promise.
    apply Exec.elem_of_res_mchoosel. rewrite raw_filtered_promises. exact Hev. }
  eapply Exec.elem_of_bind_intro with (a := nst).
  { apply (proj2 (PromiseFirstCurrent.lift_result_success _ _ _ _)). auto. }
  assert (Hcache : vimap (λ tid res,
    if prom.(Promising.mEvent_affects) ev tid then None else Some res)
    (raw_results fuel st) = vreplicate n None).
  { apply vec_eq. intro i. unfold vimap. rewrite lookup_fun_to_vec, vlookup_replicate, affects_all. reflexivity. }
  rewrite Hcache.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mSetv|apply Exec.elem_of_mret].
Qed.

Lemma cache_some fuel st st' fsig :
  Exec.elem_of_results (st', Some fsig)
    (CPState.run_transition_promise_first_uncached isem prom term fuel st) →
  Exec.elem_of_results (empty_cache st', Some fsig)
    (CPState.run_transition_promise_first isem prom term fuel (empty_cache st)).
Proof using All.
  intro H. destruct (run_transition_promise_first_some_inv isem term fuel st st' fsig H)
    as [ts [st0 [pt [-> [Hstates [Hvalidate ->]]]]]].
  apply validate_final_state_success in Hvalidate as [-> Hvalidate].
  unfold CPState.run_transition_promise_first.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  cbn [empty_cache CPState.pstate]. rewrite empty_cache_results.
  eapply Exec.elem_of_bind_intro with (a := 1%nat);
    [apply Exec.elem_of_mchoosel; cbn; set_solver|].
  eapply Exec.elem_of_bind_intro with (a := ts).
  { apply Exec.elem_of_mchoosel. rewrite raw_filtered_final_states.
    apply cprodn_spec. intro tid. rewrite vlookup_map. apply Hstates. }
  eapply Exec.elem_of_bind_intro with (a := pt).
  { destruct (Exec.elem_of_guard_discard (E := string) (empty_cache st) pt) as [pt' Hguard].
    assert (pt' = pt) by apply proof_irrelevance. subst pt'. exact Hguard. }
  eapply Exec.elem_of_bind_intro.
  { apply Exec.elem_of_lift_res. exact Hvalidate. }
  apply Exec.elem_of_mret.
Qed.

Theorem uncached_run_to_cached fuel init st returned fsig :
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf_uncached isem prom n) fuel term init st) →
  Exec.elem_of_results (empty_cache returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom n) fuel term init (empty_cache st)).
Proof using All.
  revert st returned. induction fuel as [|fuel IH]; intros st returned Hrun.
  - inversion Hrun.
  - cbn [opModel.run] in Hrun |- *.
    apply Exec.elem_of_bind_elim in Hrun as [next [res [Hstep Htail]]].
    destruct res as [final|].
    + apply Exec.elem_of_mret_inv in Htail as [-> ->].
      eapply Exec.elem_of_bind_intro; [apply cache_some; exact Hstep|apply Exec.elem_of_mret].
    + eapply Exec.elem_of_bind_intro; [apply cache_none; exact Hstep|].
      apply IH. exact Htail.
Qed.
End Cache.

Corollary UM_uncached_run_to_cached (isem : iMon ()) {n} (term : terminationCondition n)
    fuel init st returned fsig :
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf_uncached isem UMPromising n) fuel term init st) →
  Exec.elem_of_results (empty_cache UMPromising returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem UMPromising n) fuel term init
      (empty_cache UMPromising st)).
Proof. apply uncached_run_to_cached. reflexivity. Qed.

Corollary UM_uncached_final_state_to_cached (isem : iMon ()) {n}
    (term : terminationCondition n) fuel init fs (pt : archState.is_terminated term fs) :
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc_pf_uncached UMPromising isem fuel n term init →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc_pf UMPromising isem fuel n term init.
Proof.
  intro H. destruct (promise_first_final_state_inv isem term init fuel fs pt H)
    as [start [Hinit [returned [sig [Hrun Hfs]]]]].
  pose proof (UM_uncached_run_to_cached isem term fuel init start returned sig Hrun) as Hcached.
  unfold Promising_to_Modelc_pf, opModel.to_archModel. cbn. rewrite Hinit. cbn.
  eapply final_state_from_exec_intro.
  destruct sig as [fs' pt']. cbn in Hfs. subst fs'.
  replace pt' with pt in Hcached by apply proof_irrelevance. exact Hcached.
Qed.
