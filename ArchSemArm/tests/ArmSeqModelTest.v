From ASCommon Require Import Options Common.
From ArchSemArm Require Import ArmInst ArmSeqModel.
From ASCommon Require Import CResult.



(* Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020 *)
Open Scope stdpp.
Open Scope bv.

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

(** Extract R0 on success to have something printable by Coq *)
Definition result_extract (a : Model.Res.t ∅ 1) : result string Z :=
  match a with
  | Model.Res.FinalState fs =>
      let x := (fs.(MState.regs)) in
      let y : registerMap := x !!! 0%fin in
      let z : bv 64 := y R0 in
      Ok (bv_unsigned z)
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => Error "hey"
  end.

Goal result_extract <$> test_results = Listset [Ok 0x110%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
