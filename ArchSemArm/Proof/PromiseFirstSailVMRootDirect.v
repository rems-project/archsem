(******************************************************************************)
(* Direct-to-promise-first inclusion for the actual Sail root-PTE store       *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstConcreteCurrent
  PromiseFirstSailCertification PromiseFirstSailScheduling PromiseFirstSailNoFuel
  PromiseFirstSailSerialization PromiseFirstSailInterleaving
  PromiseFirstSailVMDirect PromiseFirstSailVMRootWrite.

Open Scope stdpp.
Open Scope bv.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis.

Module VMSailRootDirect.
Import VMSailRootWrite.

Local Lemma register_maps_equal (xs ys : registerMap) :
  (∀ r, bool_decide (xs !d! r = ys !d! r) = true) → xs = ys.
Proof. intro H. apply dmap_eq. intro r. exact (bool_decide_eq_true_1 _ (H r)). Qed.

Definition after_instruction (st : PState.t TState.t Ev.t 1) :=
  match Exec.results (PState.run_tid isem prom 0%fin st) with
  | (next, ()) :: _ => next
  | [] => st
  end.
Definition fresh_final := after_instruction init_ps.
Definition fulfilled_final := after_instruction promised.

Lemma instruction_initial_memory st : PState.initmem (after_instruction st) = PState.initmem st.
Proof.
  unfold after_instruction.
  destruct (Exec.results (PState.run_tid isem prom 0%fin st)) as [|[next []] rest] eqn:Hresults;
    [reflexivity|].
  assert (Hrun : Exec.elem_of_results (next, ()) (PState.run_tid isem prom 0%fin st)).
  { unfold Exec.elem_of_results. rewrite Hresults. left; reflexivity. }
  destruct (run_tid_decompose prom isem 0%fin st next Hrun) as [ts [mem [iis [_ ->]]]].
  reflexivity.
Qed.

Lemma fresh_instruction_results :
  Exec.results (PState.run_tid isem prom 0%fin init_ps) = [(fresh_final, ())].
Proof.
  assert (Hcount : length (Exec.results (PState.run_tid isem prom 0%fin init_ps)) = 1%nat)
    by (vm_compute; reflexivity).
  unfold fresh_final, after_instruction.
  destruct (Exec.results (PState.run_tid isem prom 0%fin init_ps)) as [|[st []] rest];
    [discriminate|]. destruct rest; [reflexivity|discriminate].
Qed.

Lemma fulfilled_instruction_results :
  Exec.results (PState.run_tid isem prom 0%fin promised) = [(fulfilled_final, ())].
Proof.
  assert (Hcount : length (Exec.results (PState.run_tid isem prom 0%fin promised)) = 1%nat)
    by (vm_compute; reflexivity).
  unfold fulfilled_final, after_instruction.
  destruct (Exec.results (PState.run_tid isem prom 0%fin promised)) as [|[st []] rest];
    [discriminate|]. destruct rest; [reflexivity|discriminate].
Qed.

Lemma fresh_terminated : CPState.terminated prom term fresh_final.
Proof. vm_compute; exact I. Qed.
Lemma fulfilled_terminated : CPState.terminated prom term fulfilled_final.
Proof. vm_compute; exact I. Qed.
Lemma fresh_valid : Exec.elem_of_results (fresh_final, ())
  (CPState.validate_final prom fresh_final fresh_final).
Proof.
  assert (Hnone : CPState.nopromises prom fresh_final) by (vm_compute; exact I).
  assert (Hvalid : CPState.check_valid_end prom fresh_final = []) by (vm_compute; reflexivity).
  unfold CPState.validate_final. rewrite Hvalid.
  destruct (Exec.elem_of_guard_discard (E := string) fresh_final Hnone) as [pt Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|apply Exec.elem_of_mret].
Qed.
Lemma fulfilled_valid : Exec.elem_of_results (fulfilled_final, ())
  (CPState.validate_final prom fulfilled_final fulfilled_final).
Proof.
  assert (Hnone : CPState.nopromises prom fulfilled_final) by (vm_compute; exact I).
  assert (Hvalid : CPState.check_valid_end prom fulfilled_final = []) by (vm_compute; reflexivity).
  unfold CPState.validate_final. rewrite Hvalid.
  destruct (Exec.elem_of_guard_discard (E := string) fulfilled_final Hnone) as [pt Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|apply Exec.elem_of_mret].
Qed.

Definition result := CPState.to_final_archState
  (CPState.make_final prom term fresh_final fresh_terminated).

Lemma same_architecture :
  PState.to_archState prom fulfilled_final = PState.to_archState prom fresh_final.
Proof.
  unfold PState.to_archState. apply f_equal3.
  - apply f_equal2.
    + unfold fulfilled_final, fresh_final. rewrite !instruction_initial_memory.
      exact (proj1 (PromiseFirstCurrent.promise_success prom event init_ps promised promise_succeeds)).
    + vm_compute.
      repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
  - reflexivity.
  - apply vec_eq. intro tid. inv_fin tid; [|intro tid; inv_fin tid].
    rewrite vlookup_map, vlookup_map. apply register_maps_equal. intros [r|r|r|r]; destruct r; vm_compute; reflexivity.
Qed.

Lemma fulfilled_signature (pt : CPState.terminated prom term fulfilled_final) :
  CPState.to_final_archState (CPState.make_final prom term fulfilled_final pt) = result.
Proof.
  unfold result, CPState.to_final_archState, CPState.make_final.
  cbn -[PState.to_archState fresh_final fulfilled_final].
  generalize (CPState.terminated_to_archState prom term fulfilled_final pt).
  rewrite same_architecture. intro p. f_equal; apply proof_irrelevance.
Qed.

Lemma promised_has_no_candidates :
  (CPState.enumerate_results isem prom term 0%fin (PState.initmem promised) 1
    (PState.tstate 0%fin promised) (PState.events promised)).(CPState.promises prom) = [].
Proof. vm_compute; reflexivity. Qed.

Lemma promised_no_promise_step fuel next :
  ¬ Exec.elem_of_results (next, None)
    (CPState.run_transition_promise_first isem prom term (S fuel) promised).
Proof.
  rewrite <- (complete_transition_fuel_irrelevant prom false term 1%nat (S fuel)
    promised ltac:(lia) promised_certification_complete).
  intro Hstep.
  destruct (run_transition_promise_first_none_inv (prom := prom) isem term 1%nat
    promised next Hstep) as [tid [ev [nst [Hcandidate _]]]].
  assert (Htid : tid = 0%fin) by (inv_fin tid; [reflexivity|intro tid; inv_fin tid]).
  subst tid. rewrite promise_first_execution_results_lookup, promised_has_no_candidates in Hcandidate.
  inversion Hcandidate.
Qed.

Lemma initial_not_terminated : ¬ CPState.terminated prom term init_ps.
Proof. vm_compute; tauto. Qed.
Lemma promised_not_terminated : ¬ CPState.terminated prom term promised.
Proof. vm_compute; tauto. Qed.

Local Opaque init_ps promised fresh_final fulfilled_final isem.

Definition ReachableState (st : PState.t TState.t Ev.t 1) :=
  st = init_ps ∨ st = promised ∨ st = fresh_final ∨ st = fulfilled_final.

Local Lemma terminated_no_direct_step fuel st next :
  CPState.terminated prom term st →
  ¬ Exec.elem_of_results (next, None) (CPState.run_transition isem prom term fuel st).
Proof.
  intros Hterm Hstep. unfold CPState.run_transition in Hstep.
  apply Exec.elem_of_bind_elim in Hstep as [mid [s [Hget Hstep]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  destruct (decide (CPState.terminated prom term st)) as [pt|Hnot]; [|contradiction].
  cbn in Hstep.
  apply Exec.elem_of_bind_elim in Hstep as [mid [u [_ Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [_ Hnone]. discriminate.
Qed.

Lemma direct_step_closed fuel st next :
  ReachableState st →
  Exec.elem_of_results (next, None) (CPState.run_transition isem prom term (S fuel) st) →
  ReachableState next.
Proof.
  intros [H | [H | [H | H]]] Hstep; subst st.
  - destruct (direct_none_to_promise_first_none_or_run_tid (prom := prom) isem term
      (S fuel) init_ps next Hstep) as [Hpromise|[tid [_ Hinst]]].
    + destruct (initial_step_positive fuel next None Hpromise) as [-> _]. right; left; reflexivity.
    + assert (Htid : tid = 0%fin) by (inv_fin tid; [reflexivity|intro tid; inv_fin tid]).
      subst tid. unfold Exec.elem_of_results in Hinst. rewrite fresh_instruction_results in Hinst. apply list_elem_of_singleton in Hinst.
      right; right; left. exact (f_equal fst Hinst).
  - destruct (direct_none_to_promise_first_none_or_run_tid (prom := prom) isem term
      (S fuel) promised next Hstep) as [Hpromise|[tid [_ Hinst]]].
    + exfalso. eapply promised_no_promise_step; exact Hpromise.
    + assert (Htid : tid = 0%fin) by (inv_fin tid; [reflexivity|intro tid; inv_fin tid]).
      subst tid. unfold Exec.elem_of_results in Hinst. rewrite fulfilled_instruction_results in Hinst.
      apply list_elem_of_singleton in Hinst.
      right; right; right. exact (f_equal fst Hinst).
  - exfalso. eapply terminated_no_direct_step; [exact fresh_terminated|exact Hstep].
  - exfalso. eapply terminated_no_direct_step; [exact fulfilled_terminated|exact Hstep].
Qed.

Lemma reachable_final_signature st (pt : CPState.terminated prom term st) :
  ReachableState st →
  CPState.to_final_archState (CPState.make_final prom term st pt) = result.
Proof.
  intros [H|[H|[H|H]]]; subst st.
  - contradiction initial_not_terminated.
  - contradiction promised_not_terminated.
  - unfold result. f_equal. f_equal. apply proof_irrelevance.
  - apply fulfilled_signature.
Qed.

(** The finite state invariant is closed under every successful direct step.
    Induction on arbitrary runner fuel therefore covers every direct result,
    including the path that performs the store without an explicit promise. *)
Lemma direct_result_unique fuel st returned fsig :
  ReachableState st →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem prom 1) fuel term initial st) → fsig = result.
Proof.
  exact (direct_run_invariant prom isem term initial ReachableState (λ sig, sig = result)
    direct_step_closed reachable_final_signature fuel st returned fsig).
Qed.

Local Transparent init_ps promised fresh_final fulfilled_final isem.

Lemma fresh_direct_run : Exec.elem_of_results (fresh_final, result)
  (opModel.run (@CPState.opmodel isem prom 1) 2 term initial init_ps).
Proof.
  cbn [opModel.run].
  eapply Exec.elem_of_bind_intro with (st' := fresh_final) (a := None).
  - apply (instruction_transition_any_fuel prom false term 2 init_ps fresh_final).
    exists 0%fin. split; [vm_compute; reflexivity|].
    unfold Exec.elem_of_results. rewrite fresh_instruction_results. left; reflexivity.
  - eapply Exec.elem_of_bind_intro.
    + apply (run_transition_some_intro (prom := prom)). exact fresh_valid.
    + apply Exec.elem_of_mret.
Qed.

Lemma fulfilled_suffix : VMBoundedFixedHistoryStep false false term promised fulfilled_final.
Proof.
  split.
  - exists 0%fin. split; [vm_compute; reflexivity|].
    unfold Exec.elem_of_results. rewrite fulfilled_instruction_results. left; reflexivity.
  - split.
    + vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
    + intro tid. inv_fin tid; [vm_compute; lia|intro tid; inv_fin tid].
Qed.

Lemma promise_first_result : ∃ cost, ∀ fuel, (cost < fuel)%nat →
  Exec.elem_of_results (promised, result)
    (opModel.run (@CPState.opmodel_pf isem prom 1) fuel term initial init_ps).
Proof.
  assert (Hpromise : Exec.elem_of_results (promised, None)
    (CPState.run_transition_promise_first isem prom term 1 init_ps)).
  { eapply (run_transition_promise_first_none_intro (prom := prom))
      with (tid := 0%fin) (ev := event) (nst := promised).
    - rewrite promise_first_execution_results_lookup, initial_candidates. left; reflexivity.
    - exact promise_succeeds.
    - reflexivity. }
  assert (Hstable : rtc (StableCertifiedPromiseStep prom false term) init_ps promised).
  { apply rtc_once. eapply complete_promise_step_stable;
      [intros; eapply VMPromising_filter_promises_subset; eassumption|
       exact (VM_filter_retains_membership false)|exact initial_certification_complete|exact Hpromise]. }
  assert (Hbound : VMViewBound fulfilled_final).
  { intro tid. inv_fin tid; [vm_compute; lia|intro tid; inv_fin tid]. }
  destruct (VMSail_preissued_direct_to_promise_first false false term initial init_ps
    promised fulfilled_final fulfilled_final fulfilled_terminated Hstable
    (rtc_once _ _ fulfilled_suffix) Hbound fulfilled_valid) as [returned [cost Hboth]].
  rewrite fulfilled_signature in Hboth. exists cost. intros fuel Hfuel. exact (proj2 (Hboth fuel Hfuel)).
Qed.

Theorem direct_to_promise_first fuel returned fsig :
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem prom 1) fuel term initial init_ps) →
  ∃ cost, ∀ pf_fuel, (cost < pf_fuel)%nat →
    Exec.elem_of_results (promised, fsig)
      (opModel.run (@CPState.opmodel_pf isem prom 1) pf_fuel term initial init_ps).
Proof.
  intro Hrun. rewrite (direct_result_unique fuel init_ps returned fsig (or_introl eq_refl) Hrun).
  exact promise_first_result.
Qed.

Local Opaque initial init_ps promised isem term.

Corollary final_state_inclusion fuel fs (pt : archState.is_terminated term fs) :
  archModel.Res.FinalState fs pt ∈ Promising_to_Modelc prom isem fuel 1%nat term initial →
  ∃ cost, ∀ pf_fuel, (cost < pf_fuel)%nat →
    archModel.Res.FinalState fs pt ∈ Promising_to_Modelc_pf prom isem pf_fuel 1%nat term initial.
Proof.
  intro Hfinal.
  destruct (direct_final_state_inv (prom := prom) isem term initial fuel fs pt Hfinal)
    as [start [Hinit [returned [[fs' pt'] [Hrun Hfs]]]]].
  rewrite initialization in Hinit. injection Hinit as Heq. subst start.
  cbn in Hfs. subst fs'.
  assert (Hproof : pt' = pt) by apply proof_irrelevance. subst pt'.
  destruct (direct_to_promise_first fuel returned (existT fs pt) Hrun) as [cost Hpf].
  exists cost. intros pf_fuel Hfuel.
  exact (promise_first_final_state_intro (prom := prom) isem term initial pf_fuel
    init_ps initialization promised fs pt (Hpf pf_fuel Hfuel)).
Qed.
End VMSailRootDirect.
