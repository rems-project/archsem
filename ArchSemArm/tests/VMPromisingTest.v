(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  All files except SailArmInstTypes.v are distributed under the             *)
(*  license below (BSD-2-Clause). The former is distributed                   *)
(*  under a mix of BSD-2-Clause and BSD-3-Clause Clear, as described          *)
(*  in the file header.                                                       *)
(*                                                                            *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

From ASCommon Require Import Options Common.
From ArchSemArm Require Import ArmInst.
From ASCommon Require Import CResult CList.

From ArchSemArm Require Import VMPromising.

Open Scope stdpp.
Open Scope bv.

(** * Helper functions for register checks *)

Definition check_regs (reg : register_bitvector_64) (regs : registerMap)
  : result string Z :=
    if reg_lookup reg regs is Some r0 then
      Ok (bv_unsigned r0)
    else
      Error ((pretty (GReg reg)) +:+ " not in the thread state").

Definition reg_extract {n} (reg : register_bitvector_64) (tid : fin n)
    (a : Model.Res.t ∅ n) : result string Z :=
  match a with
  | Model.Res.FinalState fs =>
    let regs : registerMap := fs.(MState.regs) !!! tid in
    check_regs reg regs
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => match e with end
  end.

Definition regs_extract {n} (regs : list (fin n * register_bitvector_64))
  (a : Model.Res.t ∅ n) : result string (list Z) :=
  match a with
  | Model.Res.FinalState fs =>
      for (tid, reg) in regs do
        let regmap : registerMap := fs.(MState.regs) !!! tid in
        check_regs reg regmap
      end
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => match e with end
  end.


(** * Helper functions for page table setup *)
Definition table_desc (next_pa : Z) : Z :=
    Z.lor (Z.land next_pa (Z.lnot 0xFFF%Z)) 0x3%Z. (* Valid=1, Table=1 *)

Definition page_desc (out_pa : Z) : Z :=
  Z.lor (Z.lor (Z.land out_pa (Z.lnot 0xFFF%Z)) 0x400%Z) 0x3%Z.  (* Valid=1, Page=1, AF=1 *)

(** We test against the sail-tiny-arm semantic, with non-determinism enabled *)
Definition arm_sem := sail_tiny_arm_sem true.

(* Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020.
   MMU is off on this test. *)
Module EORMMUOFF.
  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x500
    |> reg_insert R0 0x0
    |> reg_insert R1 0x11
    |> reg_insert R2 0x101
    |> reg_insert SCTLR_EL1 0x0.

  Definition init_mem : memoryMap :=
    ∅
    |> mem_insert 0x500 4 0xca020020. (* EOR X0, X1, X2 *)

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x504 : bv 64)).

  Definition initState :=
    {|MState.state :=
        {|MState.memory := init_mem;
          MState.regs := [# init_reg];
          MState.address_space := PAS_NonSecure |};
      MState.termCond := termCond |}.

  Definition fuel := 2%nat.

  Definition test_results := VMPromising_cert_c arm_sem fuel n_threads initState.

  Goal reg_extract R0 0%fin <$> test_results = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End EORMMUOFF.

(* Run EOR X0, X1, X2 at PC.

   This test includes address translation from a virtual address to a physical address.
   PAs of the page table is set up as follows:
   - Level 0: 0x80000
   - Level 1: 0x81000
   - Level 2: 0x82000
   - Level 3: 0x82000

   The VA of the PC is 0x8000000500. Aligning this into 48 bits, we get
   0b 0000_0000 1000_0000 0000_0000 0000_0000 0000_0101 0000_0000.
   The VA is decomposed as:
   - Level 0 index: 000000001
   - Level 1 index: 000000000
   - Level 2 index: 000000000
   - Level 3 index: 000000000
   - Page offset: 010100000000 => 0x500.

   So the PA of that VA should be 0x500.
*)
Module EOR.
  Definition L0 := 0x80000%Z.
  Definition L1 := 0x81000%Z.
  Definition L2 := 0x82000%Z.
  Definition L3 := 0x82000%Z.

  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x0
    |> reg_insert R1 0x11
    |> reg_insert R2 0x101
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0.

  Definition init_mem : memoryMap :=
    ∅
    |> mem_insert 0x500 4 0xca020020 (* EOR X0, X1, X2 *)
    (* L0[1] -> L1  (for VA_PC path: L0 index = 1) *)
    |> mem_insert 0x80008 8 0x81003
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82003
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x82003
    (* L3[0] : map VA_PC page -> PA page 0x0000 (executable) *)
    |> mem_insert 0x83000 8 0x3.

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x8000000504 : bv 64)).

  Definition initState :=
    {|MState.state :=
        {|MState.memory := init_mem;
          MState.regs := [# init_reg];
          MState.address_space := PAS_NonSecure |};
      MState.termCond := termCond |}.

  Definition fuel := 2%nat.

  Definition test_results := VMPromising_cert_c arm_sem fuel n_threads initState.

  Goal reg_extract R0 0%fin <$> test_results = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End EOR.
