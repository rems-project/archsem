(******************************************************************************)
(* A Sail page-table write lost by the current promise-first VM runner        *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising VMPromisingExec.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstSailNoFuel.

Open Scope stdpp.
Open Scope bv.

Module VMSailRootWrite.

Local Lemma ok_injective {E A} (x y : A) : @Ok E A x = Ok y → x = y.
Proof. injection 1. trivial. Qed.

(** STR X1,[X0] at 0x3000 writes a new L0 descriptor at physical address zero.
    Initially L0 points to the mapped L1 block at 0x1000. The new descriptor
    points to an unmapped table at 0x2000. The instruction bytes are disjoint
    from the write. BBM checking is disabled; the instruction semantics is the
    actual sail-tiny-arm semantics, with its optional nondeterminism disabled. *)
Definition regs : registerMap :=
  ∅ |> reg_insert _PC 0x3000 |> reg_insert R0 0 |> reg_insert R1 8195
    |> reg_insert SCTLR_EL1 1 |> reg_insert TCR_EL1 0
    |> reg_insert TTBR0_EL1 0 |> reg_insert ID_AA64MMFR1_EL1 0
    |> reg_insert CurrentEL 1.
Definition imem : memoryMap :=
  ∅ |> mem_insert 0 8 4099 |> mem_insert 4096 8 1025
    |> mem_insert 0x3000 4 0xf9000001.
Definition initial : archState 1 :=
  {| archState.regs := [# regs]; archState.memory := imem;
     archState.address_space := PAS_NonSecure |}.
Definition term : terminationCondition 1 := [# [0x3004]].
Definition prom := VMPromising false.
Definition isem := sail_tiny_arm_sem false.
Definition event := Ev.Msg (Msg.make 0 0 8 8195).

(** The fallback is unreachable, as [initialization] and [promise_succeeds]
    establish. Keeping the result-valued operations here avoids storing large
    evaluated state terms in the source. *)
Local Definition fallback := TState.make [] [] ∅ [] ∅ ∅
  0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat ∅ None None.
Definition init_ps : PState.t TState.t Ev.t 1 :=
  match PState.from_archState prom initial with
  | Ok st => st
  | Error _ => PState.Make [# fallback] imem []
  end.
Definition promised : PState.t TState.t Ev.t 1 :=
  match PState.promise prom event init_ps with Ok st => st | Error _ => init_ps end.

Lemma initialization : PState.from_archState prom initial = Ok init_ps.
Proof.
  assert (Hok : (match PState.from_archState prom initial with
    | Ok _ => true | Error _ => false end) = true) by (vm_compute; reflexivity).
  unfold init_ps. destruct (PState.from_archState prom initial); [reflexivity|discriminate].
Qed.
Lemma promise_succeeds : PState.promise prom event init_ps = Ok promised.
Proof.
  assert (Hok : (match PState.promise prom event init_ps with
    | Ok _ => true | Error _ => false end) = true) by (vm_compute; reflexivity).
  unfold promised. destruct (PState.promise prom event init_ps); [reflexivity|discriminate].
Qed.

Lemma initial_certification_complete :
  CertificationCompleteAt prom false term 1%nat init_ps.
Proof.
  intro tid. inv_fin tid.
  - vm_compute. reflexivity.
  - intro tid. inv_fin tid.
Qed.
Lemma promised_certification_complete :
  CertificationCompleteAt prom false term 1%nat promised.
Proof.
  intro tid. inv_fin tid.
  - vm_compute. reflexivity.
  - intro tid. inv_fin tid.
Qed.

Lemma initial_candidates :
  (CPState.enumerate_results isem prom term 0%fin (PState.initmem init_ps)
    1 (PState.tstate 0%fin init_ps) (PState.events init_ps)).(CPState.promises prom) = [event].
Proof.
  vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
Qed.
Lemma initial_finals :
  (CPState.enumerate_results isem prom term 0%fin (PState.initmem init_ps)
    1 (PState.tstate 0%fin init_ps) (PState.events init_ps)).(CPState.final_states prom) = [].
Proof. vm_compute. reflexivity. Qed.
Lemma promised_step_one :
  Exec.results (CPState.run_transition_promise_first isem prom term 1 promised) = [].
Proof. apply (proj1 (length_zero_iff_nil _)). vm_compute. reflexivity. Qed.

Lemma initial_step_positive fuel next res :
  Exec.elem_of_results (next, res)
    (CPState.run_transition_promise_first isem prom term (S fuel) init_ps) →
  next = promised ∧ res = None.
Proof.
  rewrite <- (complete_transition_fuel_irrelevant prom false term 1%nat (S fuel)
    init_ps ltac:(lia) initial_certification_complete).
  intro Hstep. destruct res as [fsig|].
  - destruct (run_transition_promise_first_some_inv (prom := prom) isem term 1%nat
      init_ps next fsig Hstep) as [states [finPs [pt [Hstate [Hstates _]]]]].
    specialize (Hstates 0%fin). rewrite promise_first_execution_results_lookup in Hstates.
    rewrite initial_finals in Hstates. inversion Hstates.
  - destruct (run_transition_promise_first_none_inv (prom := prom) isem term 1%nat
      init_ps next Hstep) as [tid [ev [nst [Hcandidate [Hpromise Hnext]]]]].
    rewrite promise_first_execution_results_lookup in Hcandidate.
    assert (Htid : tid = 0%fin).
    { inv_fin tid; [reflexivity|intro tid; inv_fin tid]. }
    subst tid. rewrite initial_candidates in Hcandidate.
    apply list_elem_of_singleton in Hcandidate. subst ev.
    rewrite promise_succeeds in Hpromise. apply ok_injective in Hpromise.
    split; [rewrite Hnext; symmetry; exact Hpromise|reflexivity].
Qed.
Lemma promised_step_positive fuel :
  Exec.results (CPState.run_transition_promise_first isem prom term (S fuel) promised) = [].
Proof.
  rewrite <- (complete_transition_fuel_irrelevant prom false term 1%nat (S fuel)
    promised ltac:(lia) promised_certification_complete).
  exact promised_step_one.
Qed.

Local Lemma no_results_bind {St E A B} (e : Exec.t St E A)
    (k : A → Exec.t St E B) st :
  Exec.results (e st) = [] → Exec.results ((e ≫= k) st) = [].
Proof.
  intro H. unfold mbind, Exec.mbind_inst.
  unfold mbind, Exec.res_mbind_inst. rewrite H. reflexivity.
Qed.

Lemma promised_run_no_results fuel :
  Exec.results (opModel.run (@CPState.opmodel_pf isem prom 1)
    fuel term initial promised) = [].
Proof.
  destruct fuel; [reflexivity|]. cbn [opModel.run].
  apply no_results_bind, promised_step_positive.
Qed.

Theorem promise_first_no_results fuel :
  Exec.results (opModel.run (@CPState.opmodel_pf isem prom 1)
    fuel term initial init_ps) = [].
Proof.
  destruct fuel as [|fuel]; [reflexivity|].
  destruct (Exec.results (opModel.run (@CPState.opmodel_pf isem prom 1)
    (S fuel) term initial init_ps)) as [|[returned fsig] rest] eqn:Hresults;
    [reflexivity|].
  exfalso.
  assert (Hrun : Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom 1) (S fuel) term initial init_ps)).
  { unfold Exec.elem_of_results. rewrite Hresults. left; reflexivity. }
  cbn [opModel.run] in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [next [res [Hstep Htail]]].
  apply initial_step_positive in Hstep as [-> ->].
  unfold Exec.elem_of_results in Htail. rewrite promised_run_no_results in Htail.
  inversion Htail.
Qed.

Lemma direct_result_count :
  length (Exec.results (opModel.run (@CPState.opmodel isem prom 1)
    3 term initial init_ps)) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma direct_has_result :
  ∃ st fsig, Exec.elem_of_results (st, fsig)
    (opModel.run (@CPState.opmodel isem prom 1) 3 term initial init_ps).
Proof.
  pose proof direct_result_count as Hcount.
  destruct (Exec.results (opModel.run (@CPState.opmodel isem prom 1)
    3 term initial init_ps)) as [|[st fsig] rest] eqn:Hresults;
    [discriminate|].
  exists st, fsig. unfold Exec.elem_of_results. rewrite Hresults. left; reflexivity.
Qed.

(** This failure holds for every promise-first runner budget, although both
    nonterminal promise-first states have complete certification at fuel one. *)
Theorem not_final_state_equivalent :
  ¬ VMPromisingFinalStateEquiv false isem term initial.
Proof.
  intros Hequiv. destruct direct_has_result as [st [[fs pt] Hrun]].
  assert (Hin : archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc prom isem 3%nat 1%nat term initial).
  { eapply direct_final_state_intro; [exact initialization|exact Hrun]. }
  destruct (proj1 (Hequiv fs) ltac:(exists 3%nat, pt; exact Hin))
    as [fuel [pt_pf Hpf]].
  destruct (promise_first_final_state_inv isem term initial fuel fs pt_pf Hpf)
    as [initPs [Hinit [st_pf [fsig [Hrun_pf Hfs]]]]].
  rewrite initialization in Hinit. apply ok_injective in Hinit. subst initPs.
  unfold Exec.elem_of_results in Hrun_pf.
  rewrite promise_first_no_results in Hrun_pf. inversion Hrun_pf.
Qed.

Theorem no_exhaustion_does_not_restore_equivalence :
  (∀ fuel, CertificationCompleteAt prom false term (S fuel) init_ps ∧
           CertificationCompleteAt prom false term (S fuel) promised) ∧
  ¬ VMPromisingFinalStateEquiv false isem term initial.
Proof.
  split; [|exact not_final_state_equivalent]. intro fuel. split.
  - eapply certification_complete_more_fuel with (fuel := 1%nat);
      [lia|exact initial_certification_complete].
  - eapply certification_complete_more_fuel with (fuel := 1%nat);
      [lia|exact promised_certification_complete].
Qed.

Definition instruction_bytes : code_region :=
  λ addr, addr ∈ [0x3000; 0x3001; 0x3002; 0x3003].

Lemma root_write_misses_instruction_bytes :
  event_misses_code VMPromisingReadByte instruction_bytes event.
Proof.
  intros addr Hcode. unfold instruction_bytes in Hcode.
  assert (Hcases : addr = 0x3000 ∨ addr = 0x3001 ∨ addr = 0x3002 ∨ addr = 0x3003)
    by set_solver.
  destruct Hcases as [H|[H|[H|H]]]; subst addr; vm_compute; reflexivity.
Qed.

End VMSailRootWrite.
