(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
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

(** Initial register values for sail-arm (full ARM model).
    This provides register initialization for all 448+ sail-arm registers. *)

From ASCommon Require Import Options Common CMaps.
From ArchSemArm Require Import ArmInst.

Import SailArm.armv9_types.
Import ArmTM.

(** Re-enable Inhabited instance for register values (removed globally in ArmInst) *)
#[local] Existing Instance Inhabited_register_values.

Open Scope stdpp.
Open Scope bv.

(** Helper to create a sigT entry for the dmap *)
Definition reg_entry (r : register) : sigT type_of_register :=
  @existT register type_of_register r inhabitant.

(** Build a list of (register, default_value) pairs from a typed register list *)
Definition make_reg_entries {R : Type} (wrap : R -> register)
    (regs : list (string * R)) : list (sigT type_of_register) :=
  List.map (fun '(_, r) => reg_entry (wrap r)) regs.

(** Build the full register map from all sail-arm register lists.
    Uses inhabitant (default value) for each register type. *)
Definition sail_arm_all_regs_default : list (sigT type_of_register) :=
  List.concat [
    make_reg_entries R_BranchType register_BranchType_list;
    make_reg_entries R_OpType register_OpType_list;
    make_reg_entries R_ProcState register_ProcState_list;
    make_reg_entries R_Signal register_Signal_list;
    make_reg_entries R_TMState register_TMState_list;
    make_reg_entries R___InstrEnc register___InstrEnc_list;
    make_reg_entries R_bitvector_1 register_bitvector_1_list;
    make_reg_entries R_bitvector_128 register_bitvector_128_list;
    make_reg_entries R_bitvector_16 register_bitvector_16_list;
    make_reg_entries R_bitvector_2 register_bitvector_2_list;
    make_reg_entries R_bitvector_24 register_bitvector_24_list;
    make_reg_entries R_bitvector_256 register_bitvector_256_list;
    make_reg_entries R_bitvector_3 register_bitvector_3_list;
    make_reg_entries R_bitvector_32 register_bitvector_32_list;
    make_reg_entries R_bitvector_4 register_bitvector_4_list;
    make_reg_entries R_bitvector_512 register_bitvector_512_list;
    make_reg_entries R_bitvector_56 register_bitvector_56_list;
    make_reg_entries R_bitvector_64 register_bitvector_64_list;
    make_reg_entries R_bitvector_8 register_bitvector_8_list;
    make_reg_entries R_bitvector_88 register_bitvector_88_list;
    make_reg_entries R_bool register_bool_list;
    make_reg_entries R_int register_int_list;
    make_reg_entries R_option_InterruptID register_option_InterruptID_list;
    make_reg_entries R_option_bitvector_32 register_option_bitvector_32_list;
    make_reg_entries R_vector_16_bitvector_256 register_vector_16_bitvector_256_list;
    make_reg_entries R_vector_16_bitvector_32 register_vector_16_bitvector_32_list;
    make_reg_entries R_vector_16_bitvector_64 register_vector_16_bitvector_64_list;
    make_reg_entries R_vector_16_bool register_vector_16_bool_list;
    make_reg_entries R_vector_256_bitvector_2048 register_vector_256_bitvector_2048_list;
    make_reg_entries R_vector_259_bool register_vector_259_bool_list;
    make_reg_entries R_vector_31_bitvector_32 register_vector_31_bitvector_32_list;
    make_reg_entries R_vector_31_bitvector_64 register_vector_31_bitvector_64_list;
    make_reg_entries R_vector_31_bool register_vector_31_bool_list;
    make_reg_entries R_vector_31_int register_vector_31_int_list;
    make_reg_entries R_vector_32_bitvector_2048 register_vector_32_bitvector_2048_list;
    make_reg_entries R_vector_32_bitvector_64 register_vector_32_bitvector_64_list;
    make_reg_entries R_vector_32_bool register_vector_32_bool_list;
    make_reg_entries R_vector_32_int register_vector_32_int_list;
    make_reg_entries R_vector_4_bitvector_32 register_vector_4_bitvector_32_list;
    make_reg_entries R_vector_4_bitvector_64 register_vector_4_bitvector_64_list;
    make_reg_entries R_vector_5_bitvector_64 register_vector_5_bitvector_64_list;
    make_reg_entries R_vector_64_bitvector_64 register_vector_64_bitvector_64_list;
    make_reg_entries R_vector_64_bitvector_8 register_vector_64_bitvector_8_list;
    make_reg_entries R_vector_7_bitvector_64 register_vector_7_bitvector_64_list
  ].

(** The initial register map with all registers set to default values *)
Definition sail_arm_init_regs : ArmTM.registerMap :=
  dmap_of_list sail_arm_all_regs_default.

(** Count of registers (for verification) *)
Definition num_sail_arm_regs : nat :=
  List.length sail_arm_all_regs_default.

(** Common configuration to run at EL0 in AArch64 mode.
    These registers need to be set for instruction execution to work.

    Important: Tests should always run at EL0 (user mode).
    The default PSTATE has EL=0 via inhabitant.
    SCTLR_EL1.M=0 disables MMU, giving identity VA->PA mapping. *)
Definition add_common_regs (pre : ArmTM.registerMap) : ArmTM.registerMap :=
  pre
  (* Control flags *)
  |> reg_insert (R_bool PCUpdated) false
  |> reg_insert (R_bool SPESampleInFlight) false
  |> reg_insert (R_bool InGuardedPage) false
  |> reg_insert (R_int __supported_pa_size) 52%Z
  |> reg_insert (R_int SEE) 0%Z
  (* SCTLR_EL1: M bit = 0 disables MMU, enables identity mapping *)
  |> reg_insert (R_bitvector_64 SCTLR_EL1) 0x0
  (* SCTLR_EL2: M bit = 0 disables stage 2 translation *)
  |> reg_insert (R_bitvector_64 SCTLR_EL2) 0x0
  (* SCTLR_EL3: M bit = 0 *)
  |> reg_insert (R_bitvector_64 SCTLR_EL3) 0x0
  (* HCR_EL2: TGE=0, DC=0 to not force cacheability *)
  |> reg_insert (R_bitvector_64 HCR_EL2) 0x0
  (* SCR_EL3: NS=1 for non-secure state *)
  |> reg_insert (R_bitvector_64 SCR_EL3) 0x1.

