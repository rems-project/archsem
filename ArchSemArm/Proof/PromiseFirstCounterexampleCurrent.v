(******************************************************************************)
(* A counterexample to unrestricted promise-first final-state equivalence     *)
(******************************************************************************)

(** This uses the actual UMPromising handlers and the current computational
    runners.  The instruction semantics is a small abstract [iMon], not Sail
    ARM: each thread stores 1, then reads the other thread's location and
    discards if it reads 0.  Direct execution interleaves the two stores before
    the reads.  Thread-local exploration from the initial history discards
    after its second instruction, losing its previously collected promise.

    At fuel 1 each thread offers its store as a candidate, but the overall
    runner then has no fuel left.  At every fuel >= 2 the initial promise-first
    transition has no successful result.  Thus increasing the overall fuel
    cannot recover the direct final states.

    This abstract semantics performs no instruction fetch; its code region is
    empty, and its control flow is fixed by [sem].  All stores target data at
    addresses 100 and 200.  The counterexample disproves the statement for an
    arbitrary [iMon] under the current code-immutability predicate.  It does
    not establish a counterexample for [sail_tiny_arm_sem]. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent.
Module DiscardCounterexample.
Open Scope stdpp.
Open Scope bv.

Definition access : mem_acc.
Proof.
  refine {| AccessDescriptor_acctype := AccessType_GPR;
    AccessDescriptor_acqsc := false; AccessDescriptor_acqpc := false;
    AccessDescriptor_relsc := false; AccessDescriptor_exclusive := false;
    AccessDescriptor_atomicop := false |}; exact inhabitant.
Defined.
Definition req (addr : address) := MemReq.make access addr PAS_NonSecure 1 0.
Definition setpc (pc : bv 64) : iMon () := mcall (RegWrite pc_reg None pc).
Definition store (addr : address) (pc : bv 64) : iMon () :=
  mcall (MemWrite (req addr) 1 0);; setpc pc.
Definition read_one (addr : address) (pc : bv 64) : iMon () :=
  r ← mcall (MemRead (req addr));
  match r with
  | Ok (v, _) => if decide (v = 1%bv) then setpc pc else mdiscard
  | Error _ => mdiscard
  end.
Definition sem : iMon () :=
  pc ← mcall (RegRead pc_reg None);
  if decide (pc = 0%bv) then store 100 1 else
  if decide (pc = 10%bv) then store 200 11 else
  if decide (pc = 1%bv) then read_one 200 2 else
  if decide (pc = 11%bv) then read_one 100 12 else mdiscard.
Definition imem : memoryMap := ∅ |> mem_insert 100 1 0 |> mem_insert 200 1 0.
Definition regs (pc : bv 64) : registerMap := ∅ |> reg_insert _PC pc.
Definition init_ps : PState.t TState.t Msg.t 2 :=
  PState.Make [# TState.init imem (regs 0); TState.init imem (regs 10)] imem [].
Definition term : terminationCondition 2 := [# [2]; [12]].
Definition init_ms : archState 2 :=
  {| archState.regs := [# regs 0; regs 10]; archState.memory := imem;
     archState.address_space := PAS_NonSecure |}.
Definition enum (fuel : nat) (tid : fin 2) :=
  CPState.enumerate_results sem UMPromising term tid imem fuel
    (PState.tstate tid init_ps) [].

Example candidate_count_fuel_one :
  length (enum 1 0%fin).(CPState.promises UMPromising) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example candidate_count_fuel_two :
  length (enum 2 0%fin).(CPState.promises UMPromising) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma initialization_exact :
  PState.from_archState UMPromising init_ms = Ok init_ps.
Proof. reflexivity. Qed.

Lemma direct_result_count :
  length (Exec.results
    (opModel.run (@CPState.opmodel sem UMPromising 2) 5 term init_ms init_ps)) = 4%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma thread_zero_empty fuel :
  CPState.run_to_termination sem UMPromising term 0%fin imem (S (S fuel)) 0
    ([], PPState.Make (PState.tstate 0%fin init_ps) [] IIS.init) =
  Exec.make [] [].
Proof.
  cbn [CPState.run_to_termination].
  generalize (CPState.run_to_termination sem UMPromising term 0%fin imem fuel 0).
  intro tail. vm_compute. reflexivity.
Qed.

Lemma thread_one_empty fuel :
  CPState.run_to_termination sem UMPromising term 1%fin imem (S (S fuel)) 0
    ([], PPState.Make (PState.tstate 1%fin init_ps) [] IIS.init) =
  Exec.make [] [].
Proof.
  cbn [CPState.run_to_termination].
  generalize (CPState.run_to_termination sem UMPromising term 1%fin imem fuel 0).
  intro tail. vm_compute. reflexivity.
Qed.

Definition empty_enum : CPState.EnumerationResult UMPromising :=
  {| CPState.promises := []; CPState.final_states := [];
     CPState.errors := []; CPState.out_of_fuel := false |}.

Lemma enum_empty fuel tid : enum (S (S fuel)) tid = empty_enum.
Proof.
  inv_fin tid.
  - unfold enum, CPState.enumerate_results.
    rewrite thread_zero_empty. reflexivity.
  - intro tid. inv_fin tid.
    + unfold enum, CPState.enumerate_results.
      rewrite thread_one_empty. reflexivity.
    + intro tid. inv_fin tid.
Qed.

Lemma promise_first_initial_no_result fuel st res :
  Exec.elem_of_results (st, res)
    (CPState.run_transition_promise_first sem UMPromising term
      (S (S fuel)) init_ps) → False.
Proof.
  intro Hstep. destruct res as [fsig|].
  - destruct (run_transition_promise_first_some_inv (prom := UMPromising) sem term (S (S fuel))
      init_ps st fsig Hstep)
      as [states [finPs [pt [Hstate [Hstates _]]]]].
    specialize (Hstates 0%fin).
    rewrite promise_first_execution_results_lookup in Hstates.
    change (states !!! 0%fin ∈
      (enum (S (S fuel)) 0%fin).(CPState.final_states UMPromising)) in Hstates.
    rewrite enum_empty in Hstates. inversion Hstates.
  - destruct (run_transition_promise_first_none_inv (prom := UMPromising) sem term (S (S fuel))
      init_ps st Hstep) as [tid [ev [nst [Hev _]]]].
    rewrite promise_first_execution_results_lookup in Hev.
    change (ev ∈ (enum (S (S fuel)) tid).(CPState.promises UMPromising)) in Hev.
    rewrite enum_empty in Hev. inversion Hev.
Qed.

Lemma promise_first_initial_no_results fuel :
  Exec.results
    (CPState.run_transition_promise_first sem UMPromising term
      (S (S fuel)) init_ps) = [].
Proof.
  destruct (Exec.results
    (CPState.run_transition_promise_first sem UMPromising term
      (S (S fuel)) init_ps)) as [|[st res] rest] eqn:Hresults; [reflexivity|].
  exfalso. eapply promise_first_initial_no_result.
  unfold Exec.elem_of_results. rewrite Hresults. left; reflexivity.
Qed.

Lemma no_results_bind {St E A B} (e : Exec.t St E A)
    (k : A → Exec.t St E B) st :
  Exec.results (e st) = [] → Exec.results ((e ≫= k) st) = [].
Proof.
  intro H. unfold mbind, Exec.mbind_inst.
  unfold mbind, Exec.res_mbind_inst.
  rewrite H. reflexivity.
Qed.

Lemma promise_first_no_results fuel :
  Exec.results
    (opModel.run (@CPState.opmodel_pf sem UMPromising 2) fuel term init_ms init_ps) = [].
Proof.
  destruct fuel as [|[|fuel]].
  - reflexivity.
  - apply (proj1 (length_zero_iff_nil _)). vm_compute. reflexivity.
  - cbn [opModel.run]. apply no_results_bind.
    apply promise_first_initial_no_results.
Qed.

Lemma direct_has_result :
  ∃ st fsig, Exec.elem_of_results (st, fsig)
    (opModel.run (@CPState.opmodel sem UMPromising 2) 5 term init_ms init_ps).
Proof.
  pose proof direct_result_count as Hcount.
  destruct (Exec.results
    (opModel.run (@CPState.opmodel sem UMPromising 2) 5 term init_ms init_ps))
    as [|[st fsig] rest] eqn:Hresults; [discriminate|].
  exists st, fsig. unfold Exec.elem_of_results. rewrite Hresults.
  left; reflexivity.
Qed.

Lemma no_self_modifying :
  UMPromisingNoSelfModifying sem term init_ms (λ _, False).
Proof. intros events Hobs ev Hin addr Hcode. contradiction. Qed.

(** Unlike a check at finitely many fuel values, this theorem uses
    [promise_first_no_results] for every natural-number fuel. *)
Theorem not_final_state_equivalent :
  ¬ UMPromisingFinalStateEquiv sem term init_ms.
Proof.
  intros Hequiv.
  destruct direct_has_result as [st [[fs pt] Hrun]].
  assert (Hin : archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc UMPromising sem 5%nat 2%nat term init_ms).
  { eapply direct_final_state_intro; [exact initialization_exact|exact Hrun]. }
  destruct (proj1 (Hequiv fs) ltac:(exists 5%nat, pt; exact Hin))
    as [fuel [pt_pf Hpf]].
  destruct (promise_first_final_state_inv sem term init_ms fuel fs pt_pf Hpf)
    as [initPs [Hinit [st_pf [fsig [Hrun_pf Hfs]]]]].
  rewrite initialization_exact in Hinit. inversion Hinit; subst initPs.
  unfold Exec.elem_of_results in Hrun_pf.
  rewrite promise_first_no_results in Hrun_pf. inversion Hrun_pf.
Qed.

Theorem no_self_modification_is_insufficient :
  UMPromisingNoSelfModifying sem term init_ms (λ _, False) ∧
  ¬ UMPromisingFinalStateEquiv sem term init_ms.
Proof. split; [exact no_self_modifying|exact not_final_state_equivalent]. Qed.

End DiscardCounterexample.
