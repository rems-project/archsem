(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the above copyright             *)
(*  notice, this list of conditions and the following disclaimer.              *)
(*                                                                            *)
(******************************************************************************)

From ASCommon Require Import Options Common CResult.
From ArchSemRiscV Require Import RiscVInst UMPromisingRiscV.
From ArchSemRiscV.tests Require Import RiscVSeqModelTest.

Open Scope stdpp.
Open Scope bv.

Definition riscv_promising_sem := sail_riscv_sem false.

Definition check_regs (r : register_bitvector_64) (regs : registerMap) :
    result string Z :=
  if reg_lookup r regs is Some rv
  then Ok (bv_unsigned rv)
  else Error "register not in state".

Definition reg_extract {n} (r : register_bitvector_64) (tid : fin n)
    `(a : archModel.res ∅ n term) : result string Z :=
  match a with
  | archModel.Res.FinalState fs _ =>
      check_regs r (fs.(archState.regs) !!! tid)
  | archModel.Res.Error s => Error s
  | archModel.Res.Flagged e => match e with end
  end.

Module EOR.
  Definition init_reg : registerMap :=
    RiscVSeqModelTest.common_init_regs
    |> reg_insert PC 0x500
    |> reg_insert x1 0x0
    |> reg_insert x2 0x11
    |> reg_insert x3 0x101.

  Definition init_mem : memoryMap :=
    ∅ |> mem_insert 0x500 4 0x003140b3. (* xor x1, x2, x3 *)

  Definition termCond : terminationCondition 1 :=
    [# [(0x504 : bv 64)]].

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := tt |}.

  Definition test_results :=
    UMPromisingRiscV_exe riscv_promising_sem 2%nat 1%nat termCond initState.

  Goal reg_extract x1 0%fin <$> test_results = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End EOR.

Module LDR.
  Definition init_reg : registerMap :=
    RiscVSeqModelTest.common_init_regs
    |> reg_insert PC 0x500
    |> reg_insert x1 0x0
    |> reg_insert x2 0x1000.

  Definition init_mem : memoryMap :=
    ∅
    |> mem_insert 0x500 4 0x00013083 (* ld x1, 0(x2) *)
    |> mem_insert 0x1000 8 0x2a.

  Definition termCond : terminationCondition 1 :=
    [# [(0x504 : bv 64)]].

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := tt |}.

  Definition test_results :=
    UMPromisingRiscV_exe riscv_promising_sem 2%nat 1%nat termCond initState.

  Goal reg_extract x1 0%fin <$> test_results = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End LDR.

Module FENCE.
  Definition init_reg : registerMap :=
    RiscVSeqModelTest.common_init_regs
    |> reg_insert PC 0x500
    |> reg_insert x1 0x1100
    |> reg_insert x2 0x2a
    |> reg_insert x3 0x0.

  Definition init_mem : memoryMap :=
    ∅
    |> mem_insert 0x500 4 0x0020b023 (* sd x2, 0(x1) *)
    |> mem_insert 0x504 4 0x0ff0000f (* fence rw,rw *)
    |> mem_insert 0x508 4 0x0000b183 (* ld x3, 0(x1) *)
    |> mem_insert 0x1100 8 0x0.

  Definition termCond : terminationCondition 1 :=
    [# [(0x50c : bv 64)]].

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := tt |}.

  Definition test_results :=
    UMPromisingRiscV_exe riscv_promising_sem 6%nat 1%nat termCond initState.

  Goal reg_extract x3 0%fin <$> test_results ≡ Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    set_solver.
  Qed.
End FENCE.
