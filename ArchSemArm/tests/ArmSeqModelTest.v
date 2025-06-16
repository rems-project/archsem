From ASCommon Require Import Options Common.
From ArchSemArm Require Import ArmInst ArmSeqModel.
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


(* Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020 *)
Module EOR.

Definition init_reg : registerMap :=
  ∅
  |> reg_insert _PC 0x500
  |> reg_insert R0 0x0
  |> reg_insert R1 0x11
  |> reg_insert R2 0x101.

Definition init_mem : memoryMap:=
  ∅
  |> mem_insert 0x500 4 0xca020020. (* EOR X0, X1, X2 *)

Definition termCond : terminationCondition 1 :=
  (λ tid rm, reg_lookup _PC rm =? Some (0x504 : bv 64)).

Definition initState :=
  {|MState.state :=
      {|MState.memory := init_mem;
        MState.regs := [# init_reg];
        MState.address_space := () |};
    MState.termCond := termCond |}.
Definition test_results := sequential_modelc None 2 sail_tiny_arm_sem 1%nat initState.


Goal r0_extract <$> test_results = Listset [Ok 0x110%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End EOR.

Module LDR. (* LDR X0, [X1, X0] at 0x500, loading from 0x1000 *)
Definition init_reg : registerMap :=
  ∅
  |> reg_insert _PC 0x500
  |> reg_insert R0 0x1000
  |> reg_insert R1 0x0.

Definition init_mem : memoryMap:=
  ∅
  |> mem_insert 0x500 4 0xf8606820 (* LDR X0, [X1, X0] *)
  |> mem_insert 0x1000 8 0x2a. (* data to be read *)

Definition termCond : terminationCondition 1 :=
  (λ tid rm, reg_lookup _PC rm =? Some (0x504 : bv 64)).

Definition initState :=
  {|MState.state :=
      {|MState.memory := init_mem;
        MState.regs := [# init_reg];
        MState.address_space := () |};
    MState.termCond := termCond |}.
Definition test_results := sequential_modelc None 2 sail_tiny_arm_sem 1%nat initState.

Goal r0_extract <$> test_results = Listset [Ok 0x2a%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End LDR.

Module STRLDR. (* STR X2, [X1, X0]; LDR X0, [X1, X0] at 0x500, using address 0x1100 *)
  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x500
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x100
    |> reg_insert R2 0x2a.

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 4 0xf8206822 (* STR X2, [X1, X0] *)
    |> mem_insert 0x504 4 0xf8606820 (* LDR X0, [X1, X0] *)
    |> mem_insert 0x1100 8 0x0. (* Memory need to exists to be written to *)

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x508 : bv 64)).

  Definition initState :=
    {|MState.state :=
        {|MState.memory := init_mem;
          MState.regs := [# init_reg];
          MState.address_space := () |};
      MState.termCond := termCond |}.
  Definition test_results := sequential_modelc None 2 sail_tiny_arm_sem 1%nat initState.

  Goal r0_extract <$> test_results = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End STRLDR.
