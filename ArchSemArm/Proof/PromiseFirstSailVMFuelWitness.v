(******************************************************************************)
(* A finite Sail program need not satisfy all-budget search completeness    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent PromiseFirstEquivCurrent PromiseFirstSailCertification
  PromiseFirstSailSerialization PromiseFirstSailVMNormalization PromiseFirstSailVMCacheSim
  PromiseFirstSailNoFuel PromiseFirstSailVMFinal.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.
Open Scope stdpp.
Open Scope bv.
Module VMFuelWitness.
Definition imem : memoryMap :=
  ∅ |> mem_insert 0 8 0x1003 |> mem_insert 0x1000 8 0x401
    |> mem_insert 0x5000 4 0xf9000020 (* STR X0, [X1] *)
    |> mem_insert 0x5004 4 0xd503201f (* NOP *)
    |> mem_insert 0x6000 8 0.
Definition regs : registerMap :=
  ∅ |> reg_insert pc_reg 0x5000 |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
    |> reg_insert SCTLR_EL1 1 |> reg_insert CurrentEL 1 |> reg_insert ID_AA64MMFR1_EL1 0
    |> reg_insert R0 42 |> reg_insert R1 0x6000.
Definition initial : archState 1 :=
  {| archState.regs := [# regs]; archState.memory := imem;
     archState.address_space := PAS_NonSecure |}.
Definition term : terminationCondition 1 := [# [0x5008]].
Definition ev := Ev.Msg (Msg.make 0 0x6000 8 42).
Definition state := PState.t TState.t Ev.t 1.
Definition blank : TState.t :=
  {| TState.prom_wr := []; TState.prom_tlbi := []; TState.regs := ∅;
    TState.levs := []; TState.coh := ∅; TState.tcoh := ∅;
    TState.vrd := 0%nat; TState.vwr := 0%nat; TState.vdmbst := 0%nat;
    TState.vdmb := 0%nat; TState.vdsb := 0%nat; TState.vspec := 0%nat;
    TState.vcse := 0%nat; TState.vtlbi_self := 0%nat; TState.vtlbi_other := 0%nat;
    TState.vmsr := 0%nat; TState.vacq := 0%nat; TState.vrel := 0%nat;
    TState.fwdb := ∅; TState.xclb := None; TState.dsb_epoch := 0%nat; TState.tlb := None |}.
Definition init : state := match PState.from_archState (VMPromising true) initial with
  | Ok st => st | Error _ => PState.Make [# blank] imem [] end.
Definition after_promise : state := match PState.promise (VMPromising true) ev init with
  | Ok st => st | Error _ => init end.
Definition step (st : state) :=
  PState.run_tid (sail_tiny_arm_sem false) (VMPromising true) 0%fin st.
Definition after_store : state := match Exec.results (step after_promise) with
  | (st, ()) :: _ => st | [] => after_promise end.
Definition final : state := match Exec.results (step after_store) with
  | (st, ()) :: _ => st | [] => after_store end.
Definition enum fuel := CPState.enumerate_results_filtered (sail_tiny_arm_sem false)
  (VMPromising true) term 0%fin imem fuel (PState.tstate 0%fin init) [].
Lemma initialization : PState.from_archState (VMPromising true) initial = Ok init.
Proof.
  assert (H : match PState.from_archState (VMPromising true) initial with
    | Ok _ => true | Error _ => false end = true) by (vm_compute; reflexivity).
  unfold init. destruct (PState.from_archState (VMPromising true) initial); [reflexivity|discriminate].
Qed.
Lemma promise : PState.promise (VMPromising true) ev init = Ok after_promise.
Proof.
  assert (H : match PState.promise (VMPromising true) ev init with
    | Ok _ => true | Error _ => false end = true) by (vm_compute; reflexivity).
  unfold after_promise. destruct (PState.promise (VMPromising true) ev init); [reflexivity|discriminate].
Qed.
Lemma one_candidate : ev ∈ (enum 1).(CPState.promises (VMPromising true)).
Proof. apply (proj1 (bool_decide_eq_true _)). vm_compute. reflexivity. Qed.
Lemma one_truncated : (enum 1).(CPState.out_of_fuel (VMPromising true)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma two_complete : (enum 2).(CPState.out_of_fuel (VMPromising true)) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma two_candidate : ev ∈ (enum 2).(CPState.promises (VMPromising true)).
Proof. apply (proj1 (bool_decide_eq_true _)). vm_compute. reflexivity. Qed.
Lemma candidate_stable : StablePromiseCandidate (VMPromising true) false term 0%fin
    imem (PState.tstate 0%fin init) [] ev.
Proof.
  eapply fully_explored_candidate_is_stable.
  - intros. eapply VMPromising_filter_promises_subset; eassumption.
  - apply VM_filter_retains_membership.
  - exact two_complete.
  - exact two_candidate.
Qed.
Lemma store_step : InstructionTransition (VMPromising true) false term after_promise after_store.
Proof.
  exists 0%fin. split; [vm_compute; reflexivity|].
  assert (H : match Exec.results (step after_promise) with [] => false | _ => true end = true)
    by (vm_compute; reflexivity).
  unfold after_store, Exec.elem_of_results. fold (step after_promise).
  destruct (Exec.results (step after_promise)) as [|[st []] rest]; [discriminate|].
  left; reflexivity.
Qed.
Lemma nop_step : InstructionTransition (VMPromising true) false term after_store final.
Proof.
  exists 0%fin. split; [vm_compute; reflexivity|].
  assert (H : match Exec.results (step after_store) with [] => false | _ => true end = true)
    by (vm_compute; reflexivity).
  unfold final, Exec.elem_of_results. fold (step after_store).
  destruct (Exec.results (step after_store)) as [|[st []] rest]; [discriminate|].
  left; reflexivity.
Qed.
Lemma terminated : CPState.terminated (VMPromising true) term final.
Proof. vm_compute. reflexivity. Qed.
Definition result := projT1 (CPState.to_final_archState
  (CPState.make_final (VMPromising true) term final terminated)).
Lemma validated : VMNormalization.FinalResult true term final result.
Proof.
  exists terminated. split; [|reflexivity].
  apply VMCacheSimOutcome.validate_final_state_intro; vm_compute; reflexivity.
Qed.
Lemma completes : ∃ final', rtc (VMNormalization.FMixed true false term) after_promise final' ∧
  VMNormalization.FinalResult true term final' result.
Proof.
  exists final. split; [|exact validated].
  eapply rtc_l; [left; exact store_step|].
  eapply rtc_l; [left; exact nop_step|apply rtc_refl].
Qed.
Theorem not_all_budgets_complete :
  ¬ VMNormalization.VMNormalizationSearchesComplete true false term initial result.
Proof.
  intro H. specialize (H init after_promise 1%nat 0%fin ev
    (PromiseFirstReachable_init _ _ _ _ _ _ initialization) one_candidate promise completes).
  change ((enum 1).(CPState.out_of_fuel (VMPromising true)) = false) in H.
  rewrite one_truncated in H. discriminate.
Qed.
(** Both concrete runners have successful final results. The failed premise
    above is therefore a restriction of that theorem, not a normalization
    counterexample or a program that cannot finish. *)
Definition is_final (r : archModel.res ∅ 1 term) : bool :=
  match r with archModel.Res.FinalState _ _ => true | _ => false end.
Lemma direct_has_result : existsb is_final
  (listset_car (Promising_to_Modelc (VMPromising true) (sail_tiny_arm_sem false) 3%nat 1%nat term initial)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma promise_first_has_result : existsb is_final
  (listset_car (Promising_to_Modelc_pf_uncached (VMPromising true) (sail_tiny_arm_sem false) 3%nat 1%nat term initial)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_candidates fuel candidate :
  candidate ∈ (enum fuel).(CPState.promises (VMPromising true)) → candidate = ev.
Proof.
  assert (Hzero : (enum 0).(CPState.promises (VMPromising true)) = [])
    by (vm_compute; reflexivity).
  assert (Hone : (enum 1).(CPState.promises (VMPromising true)) = [ev])
    by (apply (proj1 (bool_decide_eq_true _)); vm_compute; reflexivity).
  assert (Htwo : (enum 2).(CPState.promises (VMPromising true)) = [ev])
    by (apply (proj1 (bool_decide_eq_true _)); vm_compute; reflexivity).
  destruct fuel as [|[|fuel]].
  - rewrite Hzero. inversion 1.
  - rewrite Hone. intro H. apply elem_of_cons in H as [H|H]; [exact H|inversion H].
  - unfold enum. rewrite <- (complete_enumeration_fuel_irrelevant (VMPromising true)
      (sail_tiny_arm_sem false) term 0%fin imem 2%nat (S (S fuel))
      (PState.tstate 0%fin init) [] ltac:(lia) two_complete).
    change (candidate ∈ (enum 2).(CPState.promises (VMPromising true)) → candidate = ev).
    rewrite Htwo. intro H. apply elem_of_cons in H as [H|H]; [exact H|inversion H].
Qed.

Definition enum_after fuel := CPState.enumerate_results_filtered (sail_tiny_arm_sem false)
  (VMPromising true) term 0%fin (PState.initmem after_promise) fuel
  (PState.tstate 0%fin after_promise) (PState.events after_promise).
Lemma after_candidates fuel : (enum_after fuel).(CPState.promises (VMPromising true)) = [].
Proof.
  assert (Hzero : (enum_after 0).(CPState.promises (VMPromising true)) = [])
    by (vm_compute; reflexivity).
  assert (Hone : (enum_after 1).(CPState.promises (VMPromising true)) = [])
    by (vm_compute; reflexivity).
  assert (Htwo : (enum_after 2).(CPState.promises (VMPromising true)) = [])
    by (vm_compute; reflexivity).
  assert (Hcomplete : (enum_after 2).(CPState.out_of_fuel (VMPromising true)) = false)
    by (vm_compute; reflexivity).
  destruct fuel as [|[|fuel]]; [exact Hzero|exact Hone|].
  unfold enum_after. rewrite <- (complete_enumeration_fuel_irrelevant (VMPromising true)
    (sail_tiny_arm_sem false) term 0%fin (PState.initmem after_promise) 2%nat (S (S fuel))
    (PState.tstate 0%fin after_promise) (PState.events after_promise) ltac:(lia) Hcomplete).
  exact Htwo.
Qed.

Lemma reachable_states st : PromiseFirstReachable (VMPromising true)
  (sail_tiny_arm_sem false) term initial true st → st = init ∨ st = after_promise.
Proof.
  induction 1 as [st Hinit|fuel st st' Hreach IH Hstep].
  - rewrite initialization in Hinit.
    pose proof (f_equal (λ r : CResult.result string state,
      match r with Ok s => s | Error _ => st end) Hinit) as Heq.
    change (init = st) in Heq. left. symmetry. exact Heq.
  - apply (run_transition_promise_first_none_inv (prom := VMPromising true)) in Hstep
      as (tid & candidate & next & Hcandidate & Hpromise & Hnext).
    subst next. rewrite promise_first_execution_results_lookup in Hcandidate.
    assert (Htid : tid = 0%fin) by (inv_fin tid; [reflexivity|intro tid; inv_fin tid]).
    subst tid.
    destruct IH as [-> | ->].
    + change (candidate ∈ (enum fuel).(CPState.promises (VMPromising true))) in Hcandidate.
      apply init_candidates in Hcandidate. subst candidate.
      rewrite promise in Hpromise.
      pose proof (f_equal (λ r : CResult.result string state,
        match r with Ok s => s | Error _ => st' end) Hpromise) as Heq.
      change (after_promise = st') in Heq. right. symmetry. exact Heq.
    + change (candidate ∈ (enum_after fuel).(CPState.promises (VMPromising true))) in Hcandidate.
      rewrite after_candidates in Hcandidate. inversion Hcandidate.
Qed.

(** The weaker runner condition holds for this entire reachable program. *)
Theorem completing_candidates_stable : VMFinal.CompletingCandidatesStable true false term initial.
Proof.
  intros before next fuel tid candidate Hreach Hcandidate Hpromise Hcont.
  assert (Htid : tid = 0%fin) by (inv_fin tid; [reflexivity|intro tid; inv_fin tid]).
  subst tid.
  destruct (reachable_states before Hreach) as [-> | ->].
  - change (candidate ∈ (enum fuel).(CPState.promises (VMPromising true))) in Hcandidate.
    apply init_candidates in Hcandidate. subst candidate. exact candidate_stable.
  - change (candidate ∈ (enum_after fuel).(CPState.promises (VMPromising true))) in Hcandidate.
    rewrite after_candidates in Hcandidate. inversion Hcandidate.
Qed.
End VMFuelWitness.
