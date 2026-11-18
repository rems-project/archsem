(******************************************************************************)
(* A completing TLBI candidate persists after certification runs to completion *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstConcreteCurrent
  PromiseFirstSailCertification PromiseFirstSailVMNormalization PromiseFirstSailVMCacheSim.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.
Open Scope stdpp.
Open Scope bv.
Module VMCompletingFuelWitness.
Local Notation prom := (VMPromising true).
Local Notation isem := (sail_tiny_arm_sem false).

(** Thread 1 writes a branch selector at 0x6000 and can later populate the
    initially unmapped word at 0x6030. Thread 0's two control paths execute
    the same local TLBI. On the fall-through path a DSB cannot pass its
    pending write at 0x6010. On the taken path it fulfills that write and
    loads 0x6030 before the TLBI. *)
Definition mem : memoryMap :=
  ∅ |> mem_insert 0 8 0x1003 |> mem_insert 0x1000 8 0x401
    |> mem_insert 0x5000 4 0xf9400022 (* LDR X2,[X1] *)
    |> mem_insert 0x5004 4 0xb5000082 (* CBNZ X2,0x5014 *)
    |> mem_insert 0x5008 4 0xd5088764 (* TLBI VAAE1,X4 *)
    |> mem_insert 0x500c 4 0xd5033f9f (* DSB SY *)
    |> mem_insert 0x5014 4 0xf9000060 (* STR X0,[X3] *)
    |> mem_insert 0x5018 4 0xf90000a0 (* STR X0,[X5] *)
    |> mem_insert 0x501c 4 0xd5033fbf (* DMB SY *)
    |> mem_insert 0x5020 4 0xf94000c7 (* LDR X7,[X6] *)
    |> mem_insert 0x5024 4 0xd5088764 (* TLBI VAAE1,X4 *)
    |> mem_insert 0x5100 4 0xf9000020 (* STR X0,[X1] *)
    |> mem_insert 0x5104 4 0xf90000c0 (* STR X0,[X6] *)
    |> mem_insert 0x6000 8 0 |> mem_insert 0x6010 8 0 |> mem_insert 0x6020 8 0.
Definition regs pc : registerMap :=
  ∅ |> reg_insert pc_reg pc |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
    |> reg_insert SCTLR_EL1 1 |> reg_insert CurrentEL 1 |> reg_insert ID_AA64MMFR1_EL1 0
    |> reg_insert R0 1 |> reg_insert R1 0x6000 |> reg_insert R2 0 |> reg_insert R3 0x6010
    |> reg_insert R4 0x10 |> reg_insert R5 0x6020 |> reg_insert R6 0x6030 |> reg_insert R7 0.
Definition initial : archState 2 := {| archState.regs := [#regs 0x5000;regs 0x5100];
  archState.memory := mem; archState.address_space := PAS_NonSecure |}.
Definition term : terminationCondition 2 := [# [0x5010;0x5028];[0x5108]].
Definition b := Ev.Msg (Msg.make 1 0x6000 8 1).
Definition p := Ev.Msg (Msg.make 0 0x6010 8 1).
Definition q := Ev.Tlbi (TLBI.Vaa 0 false 0x10 false) 0 0.
Definition state := PState.t TState.t Ev.t 2.
Definition enum (st : state) tid fuel := CPState.enumerate_results_filtered isem prom term
  tid (PState.initmem st) fuel (PState.tstate tid st) (PState.events st).
Definition candidate st tid fuel ev := bool_decide (ev ∈ CPState.promises prom (enum st tid fuel)).
Definition reached := PromiseFirstReachable prom isem term initial true.

Definition emit tid fuel ev (r : CResult.result string state) :=
  st ← r;
  if candidate st tid fuel ev then PState.promise prom ev st else Error "candidate absent".
Definition start := PState.from_archState prom initial.
Definition prefix := emit 0%fin 3 p (emit 1%fin 2 b start).

Lemma emit_reached tid fuel ev r st :
  (∀ earlier, r = Ok earlier → reached earlier) →
  emit tid fuel ev r = Ok st → reached st.
Proof.
  intros Hr. destruct r as [earlier|err]; [|discriminate].
  unfold emit. change ((if candidate earlier tid fuel ev then PState.promise prom ev earlier
    else Error "candidate absent") = Ok st → reached st).
  destruct (candidate earlier tid fuel ev) eqn:Hcandidate; [|discriminate]. intro Hpromise.
  eapply PromiseFirstReachable_step with (fuel := fuel); [apply Hr; reflexivity|].
  eapply run_transition_promise_first_none_intro with (tid := tid) (ev := ev) (nst := st);
    [|exact Hpromise|reflexivity].
  rewrite promise_first_execution_results_lookup. apply (proj1 (bool_decide_eq_true _)), Hcandidate.
Qed.

Lemma prefix_reached st : prefix = Ok st → reached st.
Proof.
  apply emit_reached. intros mid. apply emit_reached.
  intros init Hinit. apply PromiseFirstReachable_init, Hinit.
Qed.

Fixpoint run (schedule : list (fin 2)) (st : state) : list state :=
  match schedule with
  | [] => [st]
  | tid :: rest => if CPState.terminated_tid prom term st tid then [] else
      (Exec.results (PState.run_tid isem prom tid st)) ≫= λ step, run rest step.1
  end.
Lemma run_trace schedule (st final : state) : final ∈ run schedule st →
  rtc (VMNormalization.FMixed true false term) st final.
Proof.
  revert st. induction schedule as [|tid rest IH]; intros st Hrun.
  - apply list_elem_of_singleton in Hrun. subst. apply rtc_refl.
  - cbn [run] in Hrun. destruct (CPState.terminated_tid prom term st tid) eqn:Hterm; [inversion Hrun|].
    apply list_elem_of_bind in Hrun as ([next []] & Htail & Hstep).
    eapply rtc_l; [left; exists tid; split; [exact Hterm|exact Hstep]|]. apply IH, Htail.
Qed.

Definition schedule : list (fin 2) := [1%fin;1%fin;0%fin;0%fin;0%fin;0%fin;0%fin;0%fin;0%fin].
Definition valid (st : state) :=
  (bool_decide (CPState.terminated prom term st) && bool_decide (CPState.nopromises prom st))
    && bool_decide (PState.check_valid_end prom st = []).
Lemma valid_result st : valid st = true → ∃ fs, VMNormalization.FinalResult true term st fs.
Proof.
  unfold valid. intro H. apply andb_true_iff in H as [H Hbbm].
  apply andb_true_iff in H as [pt Hempty].
  apply bool_decide_eq_true in pt, Hempty, Hbbm.
  exists (projT1 (CPState.to_final_archState (CPState.make_final prom term st pt))), pt.
  split; [apply VMCacheSimOutcome.validate_final_state_intro; assumption|reflexivity].
Qed.

Definition check (st : state) :=
  (((candidate st 0%fin 3 q && CPState.out_of_fuel prom (enum st 0%fin 3))
  && candidate st 0%fin 9 q) && negb (CPState.out_of_fuel prom (enum st 0%fin 9)))
  && match PState.promise prom q st with
     | Ok next => existsb valid (run schedule next) | Error _ => false end.

Lemma checked : match prefix with Ok st => check st | Error _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

(** The short and completed searches expose the same TLBI. Emitting it
    permits the nine scheduled instructions and the final BBM check. *)
Theorem completing_tlbi_survives :
  ∃ st next final fs, reached st ∧
    (∀ fuel, 3 ≤ fuel → candidate st 0%fin fuel q = true)%nat ∧
    PState.promise prom q st = Ok next ∧
    rtc (VMNormalization.FMixed true false term) next final ∧
    VMNormalization.FinalResult true term final fs.
Proof.
  pose proof checked as Hcheck. destruct prefix as [st|err] eqn:Hprefix; [|discriminate].
  unfold check in Hcheck. apply andb_true_iff in Hcheck as [Hcheck Hfinish].
  apply andb_true_iff in Hcheck as [Hcheck _]. apply andb_true_iff in Hcheck as [Hcheck _].
  apply andb_true_iff in Hcheck as [Hthree _].
  destruct (PState.promise prom q st) as [next|err] eqn:Hpromise; [|discriminate].
  apply existsb_exists in Hfinish as (final & Hin & Hvalid).
  destruct (valid_result final Hvalid) as (fs & Hfs). exists st, next, final, fs.
  split; [apply prefix_reached, Hprefix|]. split.
  - intros fuel Hfuel. unfold candidate, enum in Hthree |- *.
    apply bool_decide_eq_true in Hthree. apply bool_decide_eq_true_2.
    eapply (enumerated_candidate_more_fuel prom false term 0%fin _ 3 fuel);
      [intros; eapply VMPromising_filter_promises_subset; eassumption|
       apply VM_filter_retains_membership|exact Hfuel|exact Hthree].
  - split; [exact Hpromise|]. split; [apply run_trace with (schedule := schedule); apply list_elem_of_In, Hin|exact Hfs].
Qed.
End VMCompletingFuelWitness.
