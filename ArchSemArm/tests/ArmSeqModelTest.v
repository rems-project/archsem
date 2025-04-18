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
      let r0 : bv 64 := regs R0 in
      Ok (bv_unsigned r0)
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => match e with end
  end.


(* Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020 *)
Module EOR.
Equations init_reg : registerMap:=
  init_reg (GReg (R_bitvector_64 _PC)) := 0x500;
  init_reg (GReg (R_bitvector_64 R0)) := 0x0;
  init_reg (GReg (R_bitvector_64 R1)) := 0x11;
  init_reg (GReg (R_bitvector_64 R2)) := 0x101;
  init_reg _ := 0x0.

Equations init_mem : memoryMap:=
  init_mem 0x500 := 0x20;
  init_mem 0x501 := 0x00;
  init_mem 0x502 := 0x02;
  init_mem 0x503 := 0xca;
  init_mem _ := 0x00.

Definition termCond : terminationCondition 1 := (λ tid rm, rm _PC =? (0x504 : bv 64)).

Definition initState :=
  {| MState.state := {| MState.memory := init_mem; MState.regs := [# init_reg] |};
    MState.termCond := termCond |}.
Definition test_results := sequential_modelc None 2 sail_tiny_arm_sem 1%nat initState.


Goal r0_extract <$> test_results = Listset [Ok 0x110%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End EOR.

Module LDR. (* LDR X0, [X1, X0] at 0x500, loading from 0x1000 *)
Equations init_reg : registerMap:=
  init_reg (GReg (R_bitvector_64 _PC)) := 0x500;
  init_reg (GReg (R_bitvector_64 R0)) := 0x1000;
  init_reg _ := 0x0.

Equations init_mem : memoryMap:=
  init_mem 0x500 := 0x20; (* 0010 0000 *)
  init_mem 0x501 := 0x68; (* 0110 1000 *)
  init_mem 0x502 := 0x60; (* 0110 0000 *)
  init_mem 0x503 := 0xF8; (* 1111 1000 *)
  init_mem 0x1000 := 0x2a;
  init_mem _ := 0x00.

Definition termCond : terminationCondition 1 := (λ tid rm, rm _PC =? (0x504 : bv 64)).

Definition initState :=
  {| MState.state := {| MState.memory := init_mem; MState.regs := [# init_reg] |};
    MState.termCond := termCond |}.
Definition test_results := sequential_modelc None 2 sail_tiny_arm_sem 1%nat initState.

Goal r0_extract <$> test_results = Listset [Ok 0x2a%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End LDR.

Module STRLDR. (* STR X2, [X1, X0]; LDR X0, [X1, X0] at 0x500, using address 0x1100 *)
  Equations init_reg : registerMap:=
    init_reg (GReg (R_bitvector_64 _PC)) := 0x500;
    init_reg (GReg (R_bitvector_64 R0)) := 0x1000;
    init_reg (GReg (R_bitvector_64 R1)) := 0x100;
    init_reg (GReg (R_bitvector_64 R2)) := 0x2a;
    init_reg _ := 0x0.

  Equations init_mem : memoryMap:=
    init_mem 0x500 := 0x22; (* 0010 0010 *)
    init_mem 0x501 := 0x68; (* 0110 1000 *)
    init_mem 0x502 := 0x20; (* 0010 0000 *)
    init_mem 0x503 := 0xF8; (* 1111 1000 *)
    init_mem 0x504 := 0x20; (* 0010 0000 *)
    init_mem 0x505 := 0x68; (* 0110 1000 *)
    init_mem 0x506 := 0x60; (* 0110 0000 *)
    init_mem 0x507 := 0xF8; (* 1111 1000 *)
    init_mem _ := 0x00.

  Definition termCond : terminationCondition 1 := (λ tid rm, rm _PC =? (0x508 : bv 64)).

  Definition initState :=
    {| MState.state := {| MState.memory := init_mem; MState.regs := [# init_reg] |};
      MState.termCond := termCond |}.
  Definition test_results := sequential_modelc None 2 sail_tiny_arm_sem 1%nat initState.

  Goal r0_extract <$> test_results = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End STRLDR.
