(******************************************************************************)
(* Same-emitter TLBI order affects BBM validation                              *)
(******************************************************************************)
From ASCommon Require Import Options Common CResult CList Exec.
From ArchSemArm Require Import ArmInst VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.tState Promising.mEvent Promising.iis Memory.t.
Open Scope stdpp.
Open Scope bv.

(** Thread 1 invalidates the old PTE, executes a local TLBI, switches to a
    second root, reads 42, then broadcasts another TLBI. Thread 0 executes a
    NOP. Both mappings are global. The local TLBI lets the first ISB advance
    past the old mapping before the second root is loaded.

    Moving the later remote TLBI before the local one holds back that ISB:
    the remote promise remains outstanding until the final instruction.
    BBM then sees overlapping old and new mappings. Every event of both
    promise prefixes is certified; neither certification exhausts its fuel.
    A common emitter and DSB epoch therefore do not justify exchanging TLBIs. *)
Module BBMSwapWitness.
Definition imem : memoryMap :=
  ∅ |> mem_insert 0 8 0x1003
    |> mem_insert 0x1000 8 0x401 |> mem_insert 0x1008 8 0x80000401
    |> mem_insert 0x2000 8 0x3003
    |> mem_insert 0x3000 8 0x401 |> mem_insert 0x3008 8 0x40000401
    |> mem_insert 0x40000000 8 42 |> mem_insert 0x80000000 8 84
    |> mem_insert 0x5000 4 0xf90000a0 (* STR X0, [X5] *)
    |> mem_insert 0x5004 4 0xd5088764 (* TLBI VAAE1, X4 *)
    |> mem_insert 0x5008 4 0xd5033fdf (* ISB *)
    |> mem_insert 0x500c 4 0xd5182001 (* MSR TTBR0_EL1, X1 *)
    |> mem_insert 0x5010 4 0xd5033fdf (* ISB *)
    |> mem_insert 0x5014 4 0xf9400043 (* LDR X3, [X2] *)
    |> mem_insert 0x5018 4 0xd5088364 (* TLBI VAAE1IS, X4 *)
    |> mem_insert 0x6000 4 0xd503201f. (* NOP *)
Definition regs pc : registerMap :=
  ∅ |> reg_insert pc_reg pc |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
    |> reg_insert SCTLR_EL1 1 |> reg_insert CurrentEL 1 |> reg_insert ID_AA64MMFR1_EL1 0
    |> reg_insert R0 0 |> reg_insert R1 0x2000 |> reg_insert R2 0x40000000
    |> reg_insert R3 0 |> reg_insert R4 0x40000 |> reg_insert R5 0x1008
    |> reg_insert R6 0x7008 |> reg_insert R7 0x40000
    |> reg_insert ESR_EL1 0 |> reg_insert FAR_EL1 0 |> reg_insert ELR_EL1 0
    |> reg_insert VBAR_EL1 0 |> reg_insert SPSel 0 |> reg_insert SPSR_EL1 0
    |> reg_insert NZCV 0 |> reg_insert DAIF 0.
Definition initial : archState 2 :=
  {| archState.regs := [# regs 0x6000; regs 0x5000]; archState.memory := imem;
     archState.address_space := PAS_NonSecure |}.
Definition term : terminationCondition 2 := [# [0x6004]; [0x501c]].
Definition write := Ev.Msg (Msg.make 1 0x1008 8 0).
Definition own := Ev.Tlbi (TLBI.Vaa 1 false 0x40000 false) 1 0.
Definition remote := Ev.Tlbi (TLBI.Vaa 1 false 0x40000 false) 0 0.
Definition original := [write; own; remote; own].
Definition swapped := [write; remote; own; own].
Example common_emitter_order_retained :
  filter_commuting_promises 2 1 [own; write] [remote] = [remote].
Proof. vm_compute. reflexivity. Qed.
Example disjoint_order_reduced :
  filter_commuting_promises 4 1 [Ev.Tlbi (TLBI.All 3) 3 0]
    [Ev.Tlbi (TLBI.All 1) 1 0] = [].
Proof. vm_compute. reflexivity. Qed.
Definition promised (evs : list Ev.t) : CResult.result string (PState.t TState.t Ev.t 2) :=
  init ← PState.from_archState (VMPromising true) initial;
  foldlM (λ st ev, PState.promise (VMPromising true) ev st) init evs.
Definition count_valid evs :=
  st ← promised evs;
  let en := CPState.enumerate_results (sail_tiny_arm_sem false) (VMPromising true) term 1%fin
    (PState.initmem st) 25 (PState.tstate 1%fin st) (PState.events st) in
  mret (length (filter (λ ts, TState.prom_wr ts = [] ∧ TState.prom_tlbi ts = [] ∧
      BBM.check (PState.initmem st) (PState.events st) ts = Ok false)
    (CPState.final_states (VMPromising true) en))).
Fixpoint certify (st : PState.t TState.t Ev.t 2) (evs : list Ev.t) : bool :=
  match evs with
  | [] => true
  | ev :: rest =>
      let en := CPState.enumerate_results (sail_tiny_arm_sem false) (VMPromising true) term 1%fin
        (PState.initmem st) 25 (PState.tstate 1%fin st) (PState.events st) in
      bool_decide (ev ∈ CPState.promises (VMPromising true) en) &&
      negb (CPState.out_of_fuel (VMPromising true) en) &&
      match PState.promise (VMPromising true) ev st with
      | Ok next => certify next rest
      | Error _ => false
      end
  end.
Definition certified evs := st ← promised []; mret (certify st evs).
Definition direct_finals :=
  init ← promised [];
  let states := foldl (λ states tid, states ≫= λ st,
    (Exec.results (PState.run_tid (sail_tiny_arm_sem false) (VMPromising true) tid st)).*1)
    [init] ([1%fin;1%fin;1%fin;1%fin;1%fin;1%fin;1%fin;0%fin] : list (fin 2)) in
  mret (filter (λ st,
    PState.terminated (VMPromising true) term st ∧
    PState.nopromises (VMPromising true) st ∧
    PState.check_valid_end (VMPromising true) st = []) states).
Definition observations : result string (list (option Z)) :=
  finals ← direct_finals;
  mret (map (λ st, match reg_lookup R3 (TState.reg_map (PState.tstate 1%fin st)) with
    | Some value => Some (@bv_unsigned 64 value) | None => None end) finals).
Lemma original_certified : certified original = Ok true.
Proof. vm_compute. reflexivity. Qed.
Lemma swapped_certified : certified swapped = Ok true.
Proof. vm_compute. reflexivity. Qed.
Lemma original_valid : count_valid original = Ok 2%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma swapped_invalid : count_valid swapped = Ok 0%nat.
Proof. vm_compute. reflexivity. Qed.
(** The direct instruction model reaches the same result without promises. *)
Lemma direct_observations : observations = Ok [Some 42%Z; Some 42%Z].
Proof. vm_compute. reflexivity. Qed.
End BBMSwapWitness.
