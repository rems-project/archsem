(******************************************************************************)
(* Realizing normalized VM executions with the per-thread enumeration cache  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstCache PromiseFirstConcreteCurrent
  PromiseFirstSailCurrent PromiseFirstSailCertification PromiseFirstSailScheduling PromiseFirstSailSerialization
  PromiseFirstSailVMFinal PromiseFirstSailVMDirect PromiseFirstSailVMViews
  PromiseFirstSailVMNormalization PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapRemoveInit
  PromiseFirstSailVMEnumCacheSteps PromiseFirstSailVMEnumCacheTransport
  PromiseFirstSailVMEnumCacheValidity PromiseFirstSailVMEnumCacheFinal.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module VMEnumCacheEquiv.
Import VMPromising VMEnumCacheSteps VMCacheValidity VMCacheReturn.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis Memory.t.

Section Runner.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation pfstate := (@CPState.pf_t prom n).
Local Notation result := {s & archState.is_terminated term s}.

Lemma check_each (st : state) :
  PState.check_valid_end prom st = [] ↔ ∀ tid, PState.check_valid_end_tid prom st tid = [].
Proof.
  unfold PState.check_valid_end. split.
  - intros H tid. apply List.concat_nil_Forall in H.
    apply (proj1 (List.Forall_forall _ _) H), in_map, list_elem_of_In, elem_of_enum.
  - intro H. apply List.concat_nil_Forall, List.Forall_forall.
    intros errs Hin. apply in_map_iff in Hin as (tid & <- & _). apply H.
Qed.

Lemma local_check (st : state) ts (tid : fin n) :
  prom.(Promising.check_valid_end) tid (PState.initmem st) ts (PState.events st) = [] ↔
  (bbm = true → BBM.check (PState.initmem st) (PState.events st) ts = Ok false).
Proof.
  cbn [VMPromising Promising.check_valid_end]. destruct bbm; [|split; congruence].
  destruct (BBM.check (PState.initmem st) (PState.events st) ts) as [[|]|err];
    split; intros H; try reflexivity; try discriminate; specialize (H eq_refl); discriminate.
Qed.

Lemma valid_threads (st : state) :
  Exec.elem_of_results (st, ()) (CPState.validate_final_state prom st st) ↔
  ∀ tid, local_valid bbm st (PState.tstate tid st).
Proof.
  split.
  - intro H. destruct (VMCacheSimOutcome.validate_final_state_inv bbm st st st H)
      as [_ [Hnone Hcheck]].
    unfold CPState.nopromises, PState.nopromises, fforallb in Hnone. apply true_eq_true in Hnone.
    intro tid. split.
    + apply (proj1 (List.forallb_forall _ _) Hnone tid), list_elem_of_In, elem_of_enum.
    + apply (proj1 (local_check st _ tid)), (proj1 (check_each st) Hcheck).
  - intro Hall. apply VMCacheSimOutcome.validate_final_state_intro.
    + unfold CPState.nopromises, PState.nopromises, fforallb. apply true_eq_true.
      apply List.forallb_forall. intros tid _. apply (Hall tid).
    + apply check_each. intro tid. apply (proj2 (local_check st _ tid)), (Hall tid).
Qed.

Lemma effective_final (pst : pfstate) lower fuel tid ts :
  lower ≤ fuel → valid bbm isem term lower pst →
  final_at bbm nondet term tid lower (CPState.pstate prom pst) ts →
  local_valid bbm (CPState.pstate prom pst) ts →
  ∃ old, old ∈ CPState.final_states prom (effective bbm isem term fuel pst !!! tid) ∧
    local_valid bbm (CPState.pstate prom pst) old ∧
    TState.reg_map old = TState.reg_map ts ∧ TState.pc old = TState.pc ts.
Proof.
  intros Hfuel Hvalid Hcurrent Hlocal.
  destruct (effective_entry bbm isem term lower fuel pst tid Hfuel Hvalid)
    as (before & saved & Hsaved & Hok & Htrace & Hres).
  assert (Hlarge : final_at bbm nondet term tid saved (CPState.pstate prom pst) ts).
  { eapply (final_candidate_more_fuel prom nondet term tid); [exact Hsaved|exact Hcurrent]. }
  destruct (return_trace bbm nondet term tid saved before (CPState.pstate prom pst) ts
    Hok Htrace Hlarge Hlocal) as (old & Hold & Hvalid' & Hregs & Hpc).
  exists old. rewrite Hres. split; [exact Hold|]. split; [|auto].
  apply (lift_valid bbm tid before (CPState.pstate prom pst) old);
    [exact (final_good bbm nondet term tid saved before old Hok Hold)|exact Htrace|exact Hvalid'].
Qed.

Lemma batch_transfer (pst : pfstate) lower fuel returned fsig :
  lower ≤ fuel → valid bbm isem term lower pst →
  Exec.elem_of_results (returned, Some fsig) (CPState.run_transition_promise_first_uncached
    isem prom term lower (CPState.pstate prom pst)) →
  ∃ final : result, projT1 final = projT1 fsig ∧ Exec.elem_of_results (pst, Some final)
    (CPState.run_transition_promise_first isem prom term fuel pst).
Proof.
  intros Hfuel Hv Hbatch.
  destruct (run_transition_promise_first_some_inv isem term lower (CPState.pstate prom pst)
    returned fsig Hbatch) as (targets & final & pt & Hfinal & Htargets & Hval & ->).
  assert (Hthreads : ∀ tid, local_valid bbm final (PState.tstate tid final)).
  { apply valid_threads. eapply validate_final_transport. exact Hval. }
  subst final.
  destruct (VMCacheSimOutcome.vec_choice (λ tid old,
    old ∈ CPState.final_states prom (effective bbm isem term fuel pst !!! tid) ∧
    local_valid bbm (CPState.pstate prom pst) old ∧
    TState.reg_map old = TState.reg_map (targets !!! tid) ∧
    TState.pc old = TState.pc (targets !!! tid)))
    as (states & Hstates).
  { intro tid. apply (effective_final pst lower fuel tid (targets !!! tid) Hfuel Hv).
    - specialize (Htargets tid). rewrite promise_first_execution_results_lookup in Htargets. exact Htargets.
    - apply (Hthreads tid). }
  set (chosen := PState.Make states (PState.initmem (CPState.pstate prom pst))
    (PState.events (CPState.pstate prom pst))).
  assert (pt' : CPState.terminated prom term chosen).
  { unfold CPState.terminated, PState.terminated, fforallb in pt |- *.
    erewrite VMCacheSimOutcome.forallb_ext'; [exact pt|]. intro tid.
    unfold CPState.terminated_tid, CPState.terminated_ts.
    change (pc_terminated (term !!! tid) (TState.pc (states !!! tid)) =
      pc_terminated (term !!! tid) (TState.pc (targets !!! tid))).
    now rewrite (proj2 (proj2 (proj2 (Hstates tid)))). }
  exists (CPState.to_final_archState (CPState.make_final prom term chosen pt')). split.
  - cbn [CPState.to_final_archState CPState.make_final projT1 proj1_sig].
    unfold chosen, PState.to_archState. cbn [PState.events PState.initmem PState.tstates].
    f_equal. apply vec_eq. intro tid. rewrite !vlookup_map. apply (Hstates tid).
  - apply cached_batch; [intro tid; apply (Hstates tid)|].
    assert (Hcheck : Exec.elem_of_results (chosen, ()) (CPState.validate_final_state prom chosen chosen)).
    { apply valid_threads. intro tid. apply (Hstates tid). }
    exact (proj2 (validate_final_state_success prom isem term chosen chosen chosen Hcheck)).
Qed.

(** A single starting budget bounds both the remaining run and every cache
    fill inherited along it. A fill made before a promise can therefore
    supply candidates needed at later transitions. *)
Lemma stable_prefix_run initMs start before batch_fuel returned fsig :
  rtc (StableCertifiedPromiseStep prom nondet term) start before →
  Exec.elem_of_results (returned, Some fsig)
    (CPState.run_transition_promise_first_uncached isem prom term batch_fuel before) →
  ∃ cost, ∀ fuel pst, cost < fuel → CPState.pstate prom pst = start →
    valid bbm isem term cost pst → ∃ last final, projT1 final = projT1 fsig ∧
      Exec.elem_of_results (last, final) (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs pst).
Proof.
  intros Hprefix Hbatch. induction Hprefix as [start|start mid before [tid [ev [[threshold Hcand] Hpromise]]] Htail IH].
  - exists batch_fuel. intros [|fuel] pst Hfuel Hst Hv; [lia|].
    rewrite <- Hst in Hbatch.
    destruct (batch_transfer pst batch_fuel (S fuel) returned fsig ltac:(lia) Hv Hbatch)
      as (final & Hsig & Hstep). exists pst, final. split; [exact Hsig|].
    cbn [opModel.run]. eapply Exec.elem_of_bind_intro; [exact Hstep|apply Exec.elem_of_mret].
  - destruct (IH Hbatch) as [cost Hrun].
    exists (Nat.max threshold (S cost)). intros [|fuel] pst Hfuel Hst Hv; [lia|].
    rewrite <- Hst in Hcand, Hpromise.
    pose proof (stable_entry bbm nondet term threshold pst (S fuel) tid ev ltac:(lia)
      (valid_weaken bbm isem term threshold (Nat.max threshold (S cost)) pst ltac:(lia) Hv) Hcand) as Henum.
    pose proof (cached_promise bbm isem term (S fuel) pst tid ev mid Henum Hpromise) as Hstep.
    assert (Hnext : valid bbm isem term cost (advance bbm isem term (S fuel) pst ev mid)).
    { apply advance_valid; [lia|eapply valid_weaken; [|exact Hv]; lia|exact Hpromise]. }
    destruct (Hrun fuel (advance bbm isem term (S fuel) pst ev mid) ltac:(lia) eq_refl Hnext)
      as (last & final & Hsig & Hrest).
    exists last, final. split; [exact Hsig|]. cbn [opModel.run].
    eapply Exec.elem_of_bind_intro; [exact Hstep|exact Hrest].
Qed.
Theorem trace_to_cached initMs fs :
  VMFinal.PromiseFirstFinal bbm nondet term initMs fs →
  ∃ fuel (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈ Promising_to_Modelc_pf prom isem fuel n term initMs.
Proof.
  intro Htrace. destruct (normalized_batch bbm nondet term initMs fs Htrace)
    as (init & before & batch & sig & Hinit & Hsteps & Hfs & Hbatch).
  destruct (stable_prefix_run initMs init before batch before sig Hsteps Hbatch) as [cost Hrun].
  destruct (Hrun (S cost) (CPState.PFMake prom init (vreplicate n None)) ltac:(lia) eq_refl
    (empty_valid bbm isem term cost init (VMSwapRemoveInit.from_archState_ok bbm initMs init Hinit)))
    as (last & [fs' pt'] & Hsig & Hcached).
  cbn in Hsig. rewrite Hfs in Hsig. subst fs'.
  exists (S cost), pt'. unfold Promising_to_Modelc_pf, opModel.to_archModel.
  cbn. rewrite Hinit. cbn. eapply final_state_from_exec_intro. exact Hcached.
Qed.

(** The production promise-first model keeps results for threads unaffected
    by a TLBI. The final-state comparison includes that cache and BBM. *)
Theorem final_state_equiv initMs code :
  VMSailNoSelfModifying bbm nondet term initMs code →
  ∀ fs : archState n,
    (∃ fuel pt, archModel.Res.FinalState fs pt ∈ Promising_to_Modelc prom isem fuel n term initMs) ↔
    (∃ fuel pt, archModel.Res.FinalState fs pt ∈ Promising_to_Modelc_pf prom isem fuel n term initMs).
Proof.
  intros Hsafe fs. split.
  - intros (fuel & pt & Hdirect). apply trace_to_cached.
    apply (proj1 (VMFinal.trace_final_state_equiv bbm nondet term initMs code Hsafe fs)).
    destruct (direct_final_state_inv (prom := prom) isem term initMs fuel fs pt Hdirect)
      as (init & Hinit & returned & fsig & Hrun & Hfs).
    destruct (VMNormalization.direct_run_mixed_trace bbm nondet term initMs fuel init returned fsig Hrun)
      as (final & pf & Htrace & Hvalid & Hsig).
    exists init, final. split; [exact Hinit|]. split; [exact Htrace|]. exists pf. split.
    + eapply validate_final_transport; exact Hvalid.
    + rewrite <- Hsig. exact Hfs.
  - intros (fuel & pt & Hcached). eapply cached_to_direct; eassumption.
Qed.
End Runner.
End VMEnumCacheEquiv.
