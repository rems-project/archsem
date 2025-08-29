From ASCommon Require Import Options Common.
From ArchSemArm Require Import ArmInst IslaInit.
From ASCommon Require Import CResult.



Open Scope stdpp.
Open Scope bv.

(** Extract R0 in a Z on success to have something printable by Coq *)
Definition r0_extract (a : Model.Res.t ∅ 1) : result string Z :=
  match a with
  | Model.Res.FinalState fs =>
      let regs : registerMap := fs.(MState.regs) !!! 0%fin in
      if reg_lookup R0 regs is Some r0
      then Ok (bv_unsigned r0)
      else Error "R0 not in state"
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => match e with end
  end.

Definition regs_extract (a : Model.Res.t ∅ 1) : result string (list (sigT reg_type)) :=
  match a with
  | Model.Res.FinalState fs =>
      let regs : registerMap := fs.(MState.regs) !!! 0%fin in
      Ok (dmap_to_list regs)
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => match e with end
  end.

(** Common configuration from Isla config files to run at EL0 in AArch64 mode *)
Definition common_init_regs :=
  isla_init_regs
  |> reg_insert PCUpdated false
  |> reg_insert EDESR 0x0
  |> reg_insert ShouldAdvanceIT false
  |> reg_insert ShouldAdvanceSS false
  |> reg_insert BTypeCompatible false
  |> reg_insert __InstructionStep false
  |> reg_insert SPESampleInFlight false
  |> reg_insert InGuardedPage false
  |> reg_insert __supported_pa_size 52%Z
  |> reg_insert __tlb_enabled false
  |> reg_insert __ExclusiveMonitorSet false
  |> reg_insert __ThisInstrEnc inhabitant
  |> reg_insert __ThisInstr 0x0
  |> reg_insert __currentCond 0x0
  |> reg_insert SEE 0x0%Z
  |> reg_insert BTypeNext 0x0

  (* Registers that get read due to extra supported features, but which are irrelevant
     because the feature isn't used. *)
  |> reg_insert MAIR2_EL1 inhabitant
  |> reg_insert PIR_EL1 inhabitant
  |> reg_insert PIRE0_EL1 inhabitant
  |> reg_insert S2PIR_EL2 inhabitant
.

(** We test against the sail-arm semantic, with non-determinism disabled *)
Definition arm_sem := sail_arm_sem false.

Module STRLDR. (* STR X2, [X1, X0]; LDR X0, [X1, X0] at 0x500, using address 0x1100 *)
  Definition init_reg : registerMap :=
    common_init_regs
    |> reg_insert PC 0x400000
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x100
    |> reg_insert R2 0x2a.

  Definition init_mem : memoryMap:=
    isla_init_mem
    |> mem_insert 0x1100 8 0x0. (* Memory need to exists to be written to *)

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup PC rm =? Some (0x400008 : bv 64)).

  Definition initState :=
    {|MState.state :=
        {|MState.memory := init_mem;
          MState.regs := [# init_reg];
          MState.address_space := PAS_NonSecure |};
      MState.termCond := termCond |}.
  Definition test_results := sequential_modelc None 2 arm_sem 1%nat initState.

  Goal r0_extract <$> test_results = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End STRLDR.

