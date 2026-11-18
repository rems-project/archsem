(******************************************************************************)
(* Promise search after a discarded continuation     *)
(******************************************************************************)

(** Each thread stores 1 and then discards unless it reads the other thread's
    store. The common explorer must retain both stores as promise candidates
    before either read can succeed. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent.
Open Scope stdpp.
Module TwoThreadFinals.
(** Encode each field before comparing concrete results.  Register-map
    well-formedness proofs are omitted by [dmap_car]; [state_code_inj] ensures
    that this still compares complete architectural states. *)
Definition state_code (s : archState 2) : positive * positive * vec positive 2 :=
  (encode s.(archState.memory), encode s.(archState.address_space),
    vmap (λ regs, encode (dmap_car regs)) s.(archState.regs)).

Lemma state_code_inj s s' : state_code s = state_code s' → s = s'.
Proof.
  destruct s as [mem space regs], s' as [mem' space' regs'].
  unfold state_code. cbn. intro H.
  injection H as Hmem Hspace Hregs.
  apply encode_inj in Hmem. apply encode_inj in Hspace.
  assert (Hregisters : regs = regs').
  { apply vec_eq. intro tid. apply dmap_eq_car. apply encode_inj.
    pose proof (f_equal (λ v : vec positive 2, v !!! tid) Hregs) as Hlookup.
    cbn beta in Hlookup.
    rewrite !vlookup_map in Hlookup. exact Hlookup. }
  subst. reflexivity.
Qed.

End TwoThreadFinals.

Module DiscardCounterexample.
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
  CPState.enumerate_results_filtered sem UMPromising term tid imem fuel
    (PState.tstate tid init_ps) [].

Example candidate_count_fuel_one :
  length (enum 1 0%fin).(CPState.promises UMPromising) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example store_survives_discard :
  let result := enum 2 0%fin in
  result.(CPState.promises UMPromising) = [Msg.make 0 100 1 1] ∧
  result.(CPState.final_states UMPromising) = [] ∧
  result.(CPState.errors UMPromising) = [] ∧ result.(CPState.out_of_fuel UMPromising) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma initialization_exact :
  PState.from_archState UMPromising init_ms = Ok init_ps.
Proof. reflexivity. Qed.

Lemma direct_result_count :
  length (Exec.results
    (opModel.run (@CPState.opmodel sem UMPromising 2) 5 term init_ms init_ps)) = 4%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma candidates_after_discard fuel tid :
  (enum (S (S fuel)) tid).(CPState.promises UMPromising) =
    (enum 1 tid).(CPState.promises UMPromising).
Proof.
  unfold enum, CPState.enumerate_results_filtered, CPState.enumerate_results.
  inv_fin tid.
  - cbn [CPState.run_to_termination].
    generalize (CPState.run_to_termination sem UMPromising term 0%fin imem fuel 0).
    intro tail. vm_compute. reflexivity.
  - intro tid. inv_fin tid.
    + cbn [CPState.run_to_termination].
      generalize (CPState.run_to_termination sem UMPromising term 1%fin imem fuel 0).
      intro tail. vm_compute. reflexivity.
    + intro tid. inv_fin tid.
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

End DiscardCounterexample.
