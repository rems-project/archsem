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
Definition add_common_regs pre :=
  pre
  |> reg_insert PCUpdated false
  |> reg_insert SPESampleInFlight false
  |> reg_insert InGuardedPage false
  |> reg_insert __supported_pa_size 52%Z
  |> reg_insert SEE 0x0%Z
.

(** We test against the sail-arm semantic, with non-determinism disabled *)
Definition arm_sem := sail_arm_sem false.

Module STRLDR. (* STR X2, [X1, X0]; LDR X0, [X1, X0] with address in x1, zero in x0 *)
  Definition init_reg : registerMap :=
    nth 0 isla_threads_init_regs dmap_empty
    |> add_common_regs.

  Definition init_mem : memoryMap:=
    isla_init_mem.

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

