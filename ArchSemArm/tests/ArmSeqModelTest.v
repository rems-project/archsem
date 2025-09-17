(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
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

Fixpoint FeatureImpl_from_features (l : list Feature) : vec bool 259 :=
  match l with
  | [] => vector_init 259%Z false
  | x :: tl => vec_update_dec (FeatureImpl_from_features tl) (num_of_Feature x) true
  end.

(** Common configuration from Isla config files to run at EL0 in AArch64 mode *)
Definition common_init_regs :=
  ∅
  |> reg_insert _PC 0x0
  |> reg_insert PCUpdated false
  |> reg_insert _EDSCR 0x0
  |> reg_insert MDCCSR_EL0 0x0
  |> reg_insert EDESR 0x0
  |> reg_insert PSTATE inhabitant
  |> reg_insert ShouldAdvanceIT false
  |> reg_insert ShouldAdvanceSS false
  |> reg_insert FeatureImpl $
       FeatureImpl_from_features [FEAT_AA64EL0; FEAT_EL0]
  (* Bit 1 is NS for Non-Secure mode below EL3
     Bit 10 is RW for AArch64 mode below EL3 *)
  |> reg_insert SCR_EL3 0x401
  |> reg_insert _MPAM3_EL3 0x0
  |> reg_insert MPAM2_EL2 0x0
  |> reg_insert BTypeCompatible false
  |> reg_insert MDCR_EL2 0x0
  |> reg_insert HCR_EL2 0x0000000080000000 (* rw flag, AArch64 below EL2 *)
  |> reg_insert OSLSR_EL1 0x0
  |> reg_insert __InstructionStep false
  |> reg_insert SPESampleInFlight false
  |> reg_insert _VTTBR_EL2 0x0
  |> reg_insert VTTBR 0x0
  |> reg_insert TCR_EL1 0x0
  |> reg_insert _TTBR0_EL1 0x0
  |> reg_insert TTBR0_NS 0x0
  (* Bit 1 being unset allows unaligned accesses
     Bit 9 being set allows DAIF bits to be set at EL0
     Bit 26 being set allows cache-maintenance ops in EL0 *)
  |> reg_insert SCTLR_EL1 0x0000000004000200
  |> reg_insert MAIR_EL1 0x0
  |> reg_insert InGuardedPage false
  |> reg_insert __supported_pa_size 52%Z
  |> reg_insert VTCR_EL2 0x0
  |> reg_insert SCTLR_EL2 0x0
  |> reg_insert __emulator_termination_opcode None
  |> reg_insert PMCR_EL0 0x0
  |> reg_insert __BranchTaken false
  |> reg_insert __ExclusiveMonitorSet false
  |> reg_insert __ThisInstrEnc inhabitant
  |> reg_insert __ThisInstr 0x0
  |> reg_insert __currentCond 0x0
  |> reg_insert SEE 0x0%Z
  |> reg_insert BTypeNext 0x0
  |> reg_insert MDSCR_EL1 0x0
  |> reg_insert Branchtypetaken inhabitant.

(** We test against the sail-arm semantic, with non-determinism disabled *)
Definition arm_sem := sail_arm_sem false.

(* Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020 *)
Module EOR.

Definition init_reg : registerMap :=
  common_init_regs
  |> reg_insert PC 0x500
  |> reg_insert R0 0x0
  |> reg_insert R1 0x11
  |> reg_insert R2 0x101
 .

Definition init_mem : memoryMap:=
  ∅
  |> mem_insert 0x500 4 0xca020020 (* EOR X0, X1, X2 *)
  |> mem_insert 0x504 4 0xca020020. (* EOR X0, X1, X2 *)

Definition termCond : terminationCondition 1 :=
  (λ tid rm, reg_lookup PC rm =? Some (0x504 : bv 64)).

Definition initState :=
  {|MState.state :=
      {|MState.memory := init_mem;
        MState.regs := [# init_reg];
        MState.address_space := PAS_NonSecure |};
    MState.termCond := termCond |}.
Definition test_results := sequential_modelc None 2 arm_sem 1%nat initState.


Goal r0_extract <$> test_results = Listset [Ok 0x110%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End EOR.

Module LDR. (* LDR X0, [X1, X0] at 0x500, loading from 0x1000 *)
Definition init_reg : registerMap :=
  common_init_regs
  |> reg_insert PC 0x500
  |> reg_insert R0 0x1000
  |> reg_insert R1 0x0.

Definition init_mem : memoryMap:=
  ∅
  |> mem_insert 0x500 4 0xf8606820 (* LDR X0, [X1, X0] *)
  |> mem_insert 0x1000 8 0x2a. (* data to be read *)

Definition termCond : terminationCondition 1 :=
  (λ tid rm, reg_lookup PC rm =? Some (0x504 : bv 64)).

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
End LDR.

Module STRLDR. (* STR X2, [X1, X0]; LDR X0, [X1, X0] at 0x500, using address 0x1100 *)
  Definition init_reg : registerMap :=
    common_init_regs
    |> reg_insert PC 0x500
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x100
    |> reg_insert R2 0x2a.

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 4 0xf8206822 (* STR X2, [X1, X0] *)
    |> mem_insert 0x504 4 0xf8606820 (* LDR X0, [X1, X0] *)
    |> mem_insert 0x1100 8 0x0. (* Memory need to exists to be written to *)

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup PC rm =? Some (0x508 : bv 64)).

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

Module Factorial. (* https://godbolt.org/z/rEfMMo5Tv *)
  Definition init_reg : registerMap :=
    common_init_regs
    |> reg_insert PC 0x500
    |> reg_insert R0 5
    |> reg_insert R1 0
    |> reg_insert R30 0x1234.

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 4 0x2a0003e1  (* MOV  W1, W0 *)
    |> mem_insert 0x504 4 0x52800020  (* MOVZ X0, 0x1 *)
    |> mem_insert 0x508 4 0x34000081  (* CBZ  W1, 0x518 (PC relative) *)
    |> mem_insert 0x50c 4 0x1b017c00  (* MUL W0, W0, W1 *)
    |> mem_insert 0x510 4 0x71000421  (* SUBS W1, W1, 1 *)
    |> mem_insert 0x514 4 0x54ffffc1  (* B.NE 0x50c (PC relative) *)
    |> mem_insert 0x518 4 0xD65F03C0. (* RET *)

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup PC rm =? Some (0x1234 : bv 64)).

  Definition initState :=
    {|MState.state :=
        {|MState.memory := init_mem;
          MState.regs := [# init_reg];
          MState.address_space := PAS_NonSecure |};
      MState.termCond := termCond |}.
  Definition test_results := sequential_modelc None 100 arm_sem 1%nat initState.

  Goal r0_extract <$> test_results = Listset [Ok 120%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End Factorial.
