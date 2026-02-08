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

From SailStdpp Require Import -(notations) Base ConcurrencyInterfaceTypes.

(** Import System_types (NOT Export — we export Arm types instead) *)
From SailTinyArm Require Import System_types.
From SailTinyArm Require Import System.

From ASCommon Require Import Options.
From ASCommon Require Import Common Effects.
From ASCommon Require Import FMon.

From ArchSem Require Import
  Interface TermModels CandidateExecutions GenPromising SeqModel.
From ArchSem Require Export FromSail.

Open Scope stdpp.

(** Export armv9_types — makes all constructors available to downstream files *)
Require Export SailArm.armv9_types.

(******************************************************************************)
(** * Arm module (primary, uses armv9_types.Arch directly)                    *)
(******************************************************************************)

Module Arm.
  Module SA := armv9_types.Arch.
  Module SI := armv9_types.Interface.

  Module ArchExtra <: FromSail.ArchExtra SA.
    Import SA.
    Import ArchSem.Interface.

    Definition pc_reg : reg := R_bitvector_64 _PC.

    Definition reg_of_string (s : string) : option reg :=
      armv9_types.register_of_string s.

    Definition set_ProcState_gen_field (field : string) (val : reg_gen_val)
        (p : ProcState) : result string ProcState :=
      match val with
      | RVNumber z =>
        if String.eqb field "N" then Ok $ setv ProcState_N (Z_to_bv 1 z) p
        else if String.eqb field "Z" then Ok $ setv ProcState_Z (Z_to_bv 1 z) p
        else if String.eqb field "C" then Ok $ setv ProcState_C (Z_to_bv 1 z) p
        else if String.eqb field "V" then Ok $ setv ProcState_V (Z_to_bv 1 z) p
        else if String.eqb field "D" then Ok $ setv ProcState_D (Z_to_bv 1 z) p
        else if String.eqb field "A" then Ok $ setv ProcState_A (Z_to_bv 1 z) p
        else if String.eqb field "I" then Ok $ setv ProcState_I (Z_to_bv 1 z) p
        else if String.eqb field "F" then Ok $ setv ProcState_F (Z_to_bv 1 z) p
        else if String.eqb field "EXLOCK" then Ok $ setv ProcState_EXLOCK (Z_to_bv 1 z) p
        else if String.eqb field "PAN" then Ok $ setv ProcState_PAN (Z_to_bv 1 z) p
        else if String.eqb field "UAO" then Ok $ setv ProcState_UAO (Z_to_bv 1 z) p
        else if String.eqb field "DIT" then Ok $ setv ProcState_DIT (Z_to_bv 1 z) p
        else if String.eqb field "TCO" then Ok $ setv ProcState_TCO (Z_to_bv 1 z) p
        else if String.eqb field "PM" then Ok $ setv ProcState_PM (Z_to_bv 1 z) p
        else if String.eqb field "PPEND" then Ok $ setv ProcState_PPEND (Z_to_bv 1 z) p
        else if String.eqb field "ZA" then Ok $ setv ProcState_ZA (Z_to_bv 1 z) p
        else if String.eqb field "SM" then Ok $ setv ProcState_SM (Z_to_bv 1 z) p
        else if String.eqb field "ALLINT" then Ok $ setv ProcState_ALLINT (Z_to_bv 1 z) p
        else if String.eqb field "SS" then Ok $ setv ProcState_SS (Z_to_bv 1 z) p
        else if String.eqb field "IL" then Ok $ setv ProcState_IL (Z_to_bv 1 z) p
        else if String.eqb field "nRW" then Ok $ setv ProcState_nRW (Z_to_bv 1 z) p
        else if String.eqb field "SP" then Ok $ setv ProcState_SP (Z_to_bv 1 z) p
        else if String.eqb field "Q" then Ok $ setv ProcState_Q (Z_to_bv 1 z) p
        else if String.eqb field "SSBS" then Ok $ setv ProcState_SSBS (Z_to_bv 1 z) p
        else if String.eqb field "J" then Ok $ setv ProcState_J (Z_to_bv 1 z) p
        else if String.eqb field "T" then Ok $ setv ProcState_T (Z_to_bv 1 z) p
        else if String.eqb field "E" then Ok $ setv ProcState_E (Z_to_bv 1 z) p
        else if String.eqb field "BTYPE" then Ok $ setv ProcState_BTYPE (Z_to_bv 2 z) p
        else if String.eqb field "EL" then Ok $ setv ProcState_EL (Z_to_bv 2 z) p
        else if String.eqb field "GE" then Ok $ setv ProcState_GE (Z_to_bv 4 z) p
        else if String.eqb field "M" then Ok $ setv ProcState_M (Z_to_bv 5 z) p
        else if String.eqb field "IT" then Ok $ setv ProcState_IT (Z_to_bv 8 z) p
        else Error ("error setting " ++ field ++ " in PSTATE")%string
      | _ => Error ("error setting " ++ field ++ " in PSTATE: expected number")%string
      end.

    Equations reg_type_of_gen (r : reg) (rv : reg_gen_val) :
        result string (reg_type r) :=
      reg_type_of_gen (R_bitvector_64 _) (RVNumber z) := Ok (Z_to_bv 64 z);
      reg_type_of_gen (R_bitvector_32 _) (RVNumber z) := Ok (Z_to_bv 32 z);
      reg_type_of_gen (R_bitvector_128 _) (RVNumber z) := Ok (Z_to_bv 128 z);
      reg_type_of_gen (R_bitvector_16 _) (RVNumber z) := Ok (Z_to_bv 16 z);
      reg_type_of_gen (R_bitvector_8 _) (RVNumber z) := Ok (Z_to_bv 8 z);
      reg_type_of_gen (R_bitvector_1 _) (RVNumber z) := Ok (Z_to_bv 1 z);
      reg_type_of_gen (R_bitvector_2 _) (RVNumber z) := Ok (Z_to_bv 2 z);
      reg_type_of_gen (R_bitvector_3 _) (RVNumber z) := Ok (Z_to_bv 3 z);
      reg_type_of_gen (R_bitvector_4 _) (RVNumber z) := Ok (Z_to_bv 4 z);
      reg_type_of_gen (R_bitvector_56 _) (RVNumber z) := Ok (Z_to_bv 56 z);
      reg_type_of_gen (R_bitvector_24 _) (RVNumber z) := Ok (Z_to_bv 24 z);
      reg_type_of_gen (R_bitvector_88 _) (RVNumber z) := Ok (Z_to_bv 88 z);
      reg_type_of_gen (R_bitvector_256 _) (RVNumber z) := Ok (Z_to_bv 256 z);
      reg_type_of_gen (R_bitvector_512 _) (RVNumber z) := Ok (Z_to_bv 512 z);
      reg_type_of_gen (R_bool _) (RVNumber z) := Ok (Z.eqb z 1);
      reg_type_of_gen (R_int _) (RVNumber z) := Ok z;
      reg_type_of_gen (R_ProcState _) (RVStruct l) :=
        foldlM (λ ps '(field, val), set_ProcState_gen_field field val ps) inhabitant l;
      reg_type_of_gen r _ := Error ("error decoding " ++ pretty r)%string.

    Equations reg_type_to_gen (r : reg) (rv : reg_type r) : reg_gen_val :=
      reg_type_to_gen (R_bitvector_64 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_32 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_128 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_16 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_8 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_1 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_2 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_3 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_4 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_56 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_24 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_88 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_256 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bitvector_512 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_bool _) b := RVNumber (if b then 1 else 0);
      reg_type_to_gen (R_int _) z := RVNumber z;
      reg_type_to_gen (R_ProcState _) ps :=
        RVStruct [
            ("N", RVNumber (bv_unsigned (ProcState_N ps)));
            ("Z", RVNumber (bv_unsigned (ProcState_Z ps)));
            ("C", RVNumber (bv_unsigned (ProcState_C ps)));
            ("V", RVNumber (bv_unsigned (ProcState_V ps)));
            ("D", RVNumber (bv_unsigned (ProcState_D ps)));
            ("A", RVNumber (bv_unsigned (ProcState_A ps)));
            ("I", RVNumber (bv_unsigned (ProcState_I ps)));
            ("F", RVNumber (bv_unsigned (ProcState_F ps)));
            ("EXLOCK", RVNumber (bv_unsigned (ProcState_EXLOCK ps)));
            ("PAN", RVNumber (bv_unsigned (ProcState_PAN ps)));
            ("UAO", RVNumber (bv_unsigned (ProcState_UAO ps)));
            ("DIT", RVNumber (bv_unsigned (ProcState_DIT ps)));
            ("TCO", RVNumber (bv_unsigned (ProcState_TCO ps)));
            ("PM", RVNumber (bv_unsigned (ProcState_PM ps)));
            ("PPEND", RVNumber (bv_unsigned (ProcState_PPEND ps)));
            ("BTYPE", RVNumber (bv_unsigned (ProcState_BTYPE ps)));
            ("ZA", RVNumber (bv_unsigned (ProcState_ZA ps)));
            ("SM", RVNumber (bv_unsigned (ProcState_SM ps)));
            ("ALLINT", RVNumber (bv_unsigned (ProcState_ALLINT ps)));
            ("SS", RVNumber (bv_unsigned (ProcState_SS ps)));
            ("IL", RVNumber (bv_unsigned (ProcState_IL ps)));
            ("EL", RVNumber (bv_unsigned (ProcState_EL ps)));
            ("nRW", RVNumber (bv_unsigned (ProcState_nRW ps)));
            ("SP", RVNumber (bv_unsigned (ProcState_SP ps)));
            ("Q", RVNumber (bv_unsigned (ProcState_Q ps)));
            ("GE", RVNumber (bv_unsigned (ProcState_GE ps)));
            ("SSBS", RVNumber (bv_unsigned (ProcState_SSBS ps)));
            ("IT", RVNumber (bv_unsigned (ProcState_IT ps)));
            ("J", RVNumber (bv_unsigned (ProcState_J ps)));
            ("T", RVNumber (bv_unsigned (ProcState_T ps)));
            ("E", RVNumber (bv_unsigned (ProcState_E ps)));
            ("M", RVNumber (bv_unsigned (ProcState_M ps)))];
      reg_type_to_gen _ _ := RVString "unimplemented".
  End ArchExtra.

  Module Arch := ArchFromSail SA ArchExtra.
  Module Interface := ArchSem.Interface.Interface Arch.
  Module IMonFromSail := FromSail.IMonFromSail SA SI ArchExtra Arch Interface.
End Arm.

Module ArmNoCHERI.
  Definition no_cheri : ¬ Arm.Arch.CHERI := ltac:(naive_solver).
End ArmNoCHERI.

(** Instantiate the generic parts of ArchSem on Arm (sail-arm) *)
Module ArmTM := TermModels Arm.
Module ArmCand := CandidateExecutions Arm ArmTM ArmNoCHERI.
Module ArmGenPro := GenPromising Arm ArmTM.
Module ArmSeqModel := SequentialModel Arm ArmTM ArmNoCHERI.

(** Export Arm modules — makes armv9_types the default arch types *)
Export Arm.
Export Arm.Arch.
Export Arm.Interface.
Export Arm.IMonFromSail.
Export ArmTM.
Export ArmCand.
Export ArmGenPro.
Export ArmSeqModel.

(** Make type abbreviations transparent *)
#[export] Typeclasses Transparent bits.
#[export] Typeclasses Transparent SA.addr_size.
#[export] Typeclasses Transparent SA.addr_space.
#[export] Typeclasses Transparent SA.sys_reg_id.
#[export] Typeclasses Transparent SA.mem_acc.
#[export] Typeclasses Transparent SA.abort.
#[export] Typeclasses Transparent SA.barrier.
#[export] Typeclasses Transparent SA.cache_op.
#[export] Typeclasses Transparent SA.tlbi.
#[export] Typeclasses Transparent SA.exn.
#[export] Typeclasses Transparent SA.trans_start.
#[export] Typeclasses Transparent SA.trans_end.

(** Since ArchSem only uses register types through [reg_type], there is no need
    for those slow and risky instances *)
#[export] Remove Hints
  Decidable_eq_register_values
  Inhabited_register_values
  Countable_register_values
  : typeclass_instances.

Require SailArm.armv9.

(** The semantics of instructions from [sail-arm] by using the conversion code
    from [ArchSem.FromSail]. [SEE] needs to be reset manually between
    instructions for legacy boring reasons *)
Definition sail_arm_sem (nondet : bool) : iMon () :=
  iMon_from_Sail nondet (armv9.__InstructionExecute ());;
  mcall (RegWrite armv9_types.SEE None 0).

(******************************************************************************)
(** * ArmTiny support (sail-tiny-arm with type conversions to armv9_types)    *)
(******************************************************************************)

(** ArmTiny reuses Arm's Arch and module instantiations since both architectures
    now share types. Only the instruction semantics differ. *)
Module ArmTiny.
  Module SA := Arm.SA.
  Module ArchExtra := Arm.ArchExtra.
  Module Arch := Arm.Arch.
  Module Interface := Arm.Interface.
End ArmTiny.

Module ArmTinyNoCHERI := ArmNoCHERI.
Module ArmTinyTM := ArmTM.
Module ArmTinyCand := ArmCand.
Module ArmTinyGenPro := ArmGenPro.
Module ArmTinySeqModel := ArmSeqModel.

(** ** Register conversions: System_types.register → armv9_types.register.
    sail-tiny-arm only has 2 register variants (R_bitvector_64, R_ProcState),
    so these are small. *)

Definition conv_reg_bv64 (r : System_types.register_bitvector_64)
    : register_bitvector_64 :=
  match r with
  | System_types._PC => _PC
  | System_types.R30 => R30
  | System_types.R29 => R29
  | System_types.R28 => R28
  | System_types.R27 => R27
  | System_types.R26 => R26
  | System_types.R25 => R25
  | System_types.R24 => R24
  | System_types.R23 => R23
  | System_types.R22 => R22
  | System_types.R21 => R21
  | System_types.R20 => R20
  | System_types.R19 => R19
  | System_types.R18 => R18
  | System_types.R17 => R17
  | System_types.R16 => R16
  | System_types.R15 => R15
  | System_types.R14 => R14
  | System_types.R13 => R13
  | System_types.R12 => R12
  | System_types.R11 => R11
  | System_types.R10 => R10
  | System_types.R9 => R9
  | System_types.R8 => R8
  | System_types.R7 => R7
  | System_types.R6 => R6
  | System_types.R5 => R5
  | System_types.R4 => R4
  | System_types.R3 => R3
  | System_types.R2 => R2
  | System_types.R1 => R1
  | System_types.R0 => R0
  | System_types.SP_EL0 => SP_EL0
  | System_types.SP_EL1 => SP_EL1
  | System_types.SP_EL2 => SP_EL2
  | System_types.SP_EL3 => SP_EL3
  | System_types.ELR_EL1 => ELR_EL1
  | System_types.ELR_EL2 => ELR_EL2
  | System_types.ELR_EL3 => ELR_EL3
  | System_types.ESR_EL1 => ESR_EL1
  | System_types.ESR_EL2 => ESR_EL2
  | System_types.ESR_EL3 => ESR_EL3
  | System_types.FAR_EL1 => FAR_EL1
  | System_types.FAR_EL2 => FAR_EL2
  | System_types.FAR_EL3 => FAR_EL3
  (* These 6 registers are bv128 in armv9_types but bv64 in System_types.
     sail-tiny-arm doesn't actually access them, so we map to _PC as a
     dummy bv64 register to keep the type consistent. *)
  | System_types.PAR_EL1 => _PC
  | System_types.TTBR0_EL1 => _PC
  | System_types.TTBR1_EL1 => _PC
  | System_types.TTBR0_EL2 => _PC
  | System_types.TTBR1_EL2 => _PC
  | System_types.VTTBR_EL2 => _PC
  | System_types.TTBR0_EL3 => TTBR0_EL3
  | System_types.VBAR_EL1 => VBAR_EL1
  | System_types.VBAR_EL2 => VBAR_EL2
  | System_types.VBAR_EL3 => VBAR_EL3
  | System_types.SPSR_EL1 => SPSR_EL1
  | System_types.SPSR_EL2 => SPSR_EL2
  | System_types.SPSR_EL3 => SPSR_EL3
  | System_types.ID_AA64MMFR0_EL1 => ID_AA64MMFR0_EL1
  | System_types.ID_AA64MMFR1_EL1 => ID_AA64MMFR1_EL1
  | System_types.ID_AA64MMFR2_EL1 => ID_AA64MMFR2_EL1
  | System_types.ID_AA64MMFR3_EL1 => ID_AA64MMFR3_EL1
  | System_types.ID_AA64MMFR4_EL1 => ID_AA64MMFR4_EL1
  | System_types.TCR_EL1 => TCR_EL1
  | System_types.TCR_EL2 => TCR_EL2
  | System_types.TCR_EL3 => TCR_EL3
  | System_types.VTCR_EL2 => VTCR_EL2
  | System_types.SCTLR_EL1 => SCTLR_EL1
  | System_types.SCTLR_EL2 => SCTLR_EL2
  | System_types.SCTLR_EL3 => SCTLR_EL3
  end.

Definition conv_reg_ps (r : System_types.register_ProcState)
    : register_ProcState :=
  match r with
  | System_types.PSTATE => PSTATE
  end.

Definition conv_reg (r : System_types.register) : reg :=
  match r with
  | System_types.R_bitvector_64 x => R_bitvector_64 (conv_reg_bv64 x)
  | System_types.R_ProcState x => R_ProcState (conv_reg_ps x)
  end.

(** ProcState conversion (structurally identical records in different modules) *)
Definition conv_procstate (ps : System_types.ProcState) : ProcState :=
  {| ProcState_N := System_types.ProcState_N ps;
     ProcState_Z := System_types.ProcState_Z ps;
     ProcState_C := System_types.ProcState_C ps;
     ProcState_V := System_types.ProcState_V ps;
     ProcState_D := System_types.ProcState_D ps;
     ProcState_A := System_types.ProcState_A ps;
     ProcState_I := System_types.ProcState_I ps;
     ProcState_F := System_types.ProcState_F ps;
     ProcState_EXLOCK := System_types.ProcState_EXLOCK ps;
     ProcState_PAN := System_types.ProcState_PAN ps;
     ProcState_UAO := System_types.ProcState_UAO ps;
     ProcState_DIT := System_types.ProcState_DIT ps;
     ProcState_TCO := System_types.ProcState_TCO ps;
     ProcState_PM := System_types.ProcState_PM ps;
     ProcState_PPEND := System_types.ProcState_PPEND ps;
     ProcState_BTYPE := System_types.ProcState_BTYPE ps;
     ProcState_ZA := System_types.ProcState_ZA ps;
     ProcState_SM := System_types.ProcState_SM ps;
     ProcState_ALLINT := System_types.ProcState_ALLINT ps;
     ProcState_SS := System_types.ProcState_SS ps;
     ProcState_IL := System_types.ProcState_IL ps;
     ProcState_EL := System_types.ProcState_EL ps;
     ProcState_nRW := System_types.ProcState_nRW ps;
     ProcState_SP := System_types.ProcState_SP ps;
     ProcState_Q := System_types.ProcState_Q ps;
     ProcState_GE := System_types.ProcState_GE ps;
     ProcState_SSBS := System_types.ProcState_SSBS ps;
     ProcState_IT := System_types.ProcState_IT ps;
     ProcState_J := System_types.ProcState_J ps;
     ProcState_T := System_types.ProcState_T ps;
     ProcState_E := System_types.ProcState_E ps;
     ProcState_M := System_types.ProcState_M ps |}.

Definition conv_procstate_inv (ps : ProcState) : System_types.ProcState :=
  {| System_types.ProcState_N := ProcState_N ps;
     System_types.ProcState_Z := ProcState_Z ps;
     System_types.ProcState_C := ProcState_C ps;
     System_types.ProcState_V := ProcState_V ps;
     System_types.ProcState_D := ProcState_D ps;
     System_types.ProcState_A := ProcState_A ps;
     System_types.ProcState_I := ProcState_I ps;
     System_types.ProcState_F := ProcState_F ps;
     System_types.ProcState_EXLOCK := ProcState_EXLOCK ps;
     System_types.ProcState_PAN := ProcState_PAN ps;
     System_types.ProcState_UAO := ProcState_UAO ps;
     System_types.ProcState_DIT := ProcState_DIT ps;
     System_types.ProcState_TCO := ProcState_TCO ps;
     System_types.ProcState_PM := ProcState_PM ps;
     System_types.ProcState_PPEND := ProcState_PPEND ps;
     System_types.ProcState_BTYPE := ProcState_BTYPE ps;
     System_types.ProcState_ZA := ProcState_ZA ps;
     System_types.ProcState_SM := ProcState_SM ps;
     System_types.ProcState_ALLINT := ProcState_ALLINT ps;
     System_types.ProcState_SS := ProcState_SS ps;
     System_types.ProcState_IL := ProcState_IL ps;
     System_types.ProcState_EL := ProcState_EL ps;
     System_types.ProcState_nRW := ProcState_nRW ps;
     System_types.ProcState_SP := ProcState_SP ps;
     System_types.ProcState_Q := ProcState_Q ps;
     System_types.ProcState_GE := ProcState_GE ps;
     System_types.ProcState_SSBS := ProcState_SSBS ps;
     System_types.ProcState_IT := ProcState_IT ps;
     System_types.ProcState_J := ProcState_J ps;
     System_types.ProcState_T := ProcState_T ps;
     System_types.ProcState_E := ProcState_E ps;
     System_types.ProcState_M := ProcState_M ps |}.

(** Register value conversion (dependent on register variant) *)
Definition conv_regval (r : System_types.register)
    (v : System_types.Arch.reg_type r) : reg_type (conv_reg r) :=
  match r return System_types.Arch.reg_type r → reg_type (conv_reg r) with
  | System_types.R_bitvector_64 _ => λ v, v
  | System_types.R_ProcState _ => λ v, conv_procstate v
  end v.

Definition conv_regval_inv (r : System_types.register)
    (v : reg_type (conv_reg r)) : System_types.Arch.reg_type r :=
  match r return reg_type (conv_reg r) → System_types.Arch.reg_type r with
  | System_types.R_bitvector_64 _ => λ v, v
  | System_types.R_ProcState _ => λ v, conv_procstate_inv v
  end v.

(** ** Shared type conversions: System_types → armv9_types *)

Definition conv_pas (p : System_types.PASpace) : PASpace :=
  match p with
  | System_types.PAS_NonSecure => PAS_NonSecure
  | System_types.PAS_Secure => PAS_Secure
  | System_types.PAS_Root => PAS_Root
  | System_types.PAS_Realm => PAS_Realm
  end.

Definition conv_accesstype (a : System_types.AccessType) : AccessType :=
  match a with
  | System_types.AccessType_IFETCH => AccessType_IFETCH
  | System_types.AccessType_GPR => AccessType_GPR
  | System_types.AccessType_ASIMD => AccessType_ASIMD
  | System_types.AccessType_SVE => AccessType_SVE
  | System_types.AccessType_SME => AccessType_SME
  | System_types.AccessType_IC => AccessType_IC
  | System_types.AccessType_DC => AccessType_DC
  | System_types.AccessType_DCZero => AccessType_DCZero
  | System_types.AccessType_AT => AccessType_AT
  | System_types.AccessType_NV2 => AccessType_NV2
  | System_types.AccessType_SPE => AccessType_SPE
  | System_types.AccessType_GCS => AccessType_GCS
  | System_types.AccessType_GPTW => AccessType_GPTW
  | System_types.AccessType_TTW => AccessType_TTW
  end.

Definition conv_securitystate (s : System_types.SecurityState) : SecurityState :=
  match s with
  | System_types.SS_NonSecure => SS_NonSecure
  | System_types.SS_Root => SS_Root
  | System_types.SS_Realm => SS_Realm
  | System_types.SS_Secure => SS_Secure
  end.

Definition conv_mematomicop (m : System_types.MemAtomicOp) : MemAtomicOp :=
  match m with
  | System_types.MemAtomicOp_GCSSS1 => MemAtomicOp_GCSSS1
  | System_types.MemAtomicOp_ADD => MemAtomicOp_ADD
  | System_types.MemAtomicOp_BIC => MemAtomicOp_BIC
  | System_types.MemAtomicOp_EOR => MemAtomicOp_EOR
  | System_types.MemAtomicOp_ORR => MemAtomicOp_ORR
  | System_types.MemAtomicOp_SMAX => MemAtomicOp_SMAX
  | System_types.MemAtomicOp_SMIN => MemAtomicOp_SMIN
  | System_types.MemAtomicOp_UMAX => MemAtomicOp_UMAX
  | System_types.MemAtomicOp_UMIN => MemAtomicOp_UMIN
  | System_types.MemAtomicOp_SWP => MemAtomicOp_SWP
  | System_types.MemAtomicOp_CAS => MemAtomicOp_CAS
  end.

Definition conv_cacheop_field (c : System_types.CacheOp) : armv9_types.CacheOp :=
  match c with
  | System_types.CacheOp_Clean => CacheOp_Clean
  | System_types.CacheOp_Invalidate => CacheOp_Invalidate
  | System_types.CacheOp_CleanInvalidate => CacheOp_CleanInvalidate
  end.

Definition conv_cacheopscope (c : System_types.CacheOpScope) : CacheOpScope :=
  match c with
  | System_types.CacheOpScope_SetWay => CacheOpScope_SetWay
  | System_types.CacheOpScope_PoU => CacheOpScope_PoU
  | System_types.CacheOpScope_PoC => CacheOpScope_PoC
  | System_types.CacheOpScope_PoE => CacheOpScope_PoE
  | System_types.CacheOpScope_PoP => CacheOpScope_PoP
  | System_types.CacheOpScope_PoDP => CacheOpScope_PoDP
  | System_types.CacheOpScope_PoPA => CacheOpScope_PoPA
  | System_types.CacheOpScope_ALLU => CacheOpScope_ALLU
  | System_types.CacheOpScope_ALLUIS => CacheOpScope_ALLUIS
  end.

Definition conv_cachetype (c : System_types.CacheType) : CacheType :=
  match c with
  | System_types.CacheType_Data => CacheType_Data
  | System_types.CacheType_Tag => CacheType_Tag
  | System_types.CacheType_Data_Tag => CacheType_Data_Tag
  | System_types.CacheType_Instruction => CacheType_Instruction
  end.

Definition conv_varange (v : System_types.VARange) : VARange :=
  match v with
  | System_types.VARange_LOWER => VARange_LOWER
  | System_types.VARange_UPPER => VARange_UPPER
  end.

Definition conv_partidspacetype (p : System_types.PARTIDspaceType) : PARTIDspaceType :=
  match p with
  | System_types.PIdSpace_Secure => PIdSpace_Secure
  | System_types.PIdSpace_Root => PIdSpace_Root
  | System_types.PIdSpace_Realm => PIdSpace_Realm
  | System_types.PIdSpace_NonSecure => PIdSpace_NonSecure
  end.

Definition conv_mpaminfo (m : System_types.MPAMinfo) : MPAMinfo :=
  Build_MPAMinfo
    (conv_partidspacetype (System_types.MPAMinfo_mpam_sp m))
    (System_types.MPAMinfo_partid m)
    (System_types.MPAMinfo_pmg m).

Definition conv_acc (a : System_types.AccessDescriptor) : AccessDescriptor :=
  Build_AccessDescriptor
    (conv_accesstype (System_types.AccessDescriptor_acctype a))
    (System_types.AccessDescriptor_el a)
    (conv_securitystate (System_types.AccessDescriptor_ss a))
    (System_types.AccessDescriptor_acqsc a)
    (System_types.AccessDescriptor_acqpc a)
    (System_types.AccessDescriptor_relsc a)
    (System_types.AccessDescriptor_limitedordered a)
    (System_types.AccessDescriptor_exclusive a)
    (System_types.AccessDescriptor_atomicop a)
    (conv_mematomicop (System_types.AccessDescriptor_modop a))
    (System_types.AccessDescriptor_nontemporal a)
    (System_types.AccessDescriptor_read a)
    (System_types.AccessDescriptor_write a)
    (conv_cacheop_field (System_types.AccessDescriptor_cacheop a))
    (conv_cacheopscope (System_types.AccessDescriptor_opscope a))
    (conv_cachetype (System_types.AccessDescriptor_cachetype a))
    (System_types.AccessDescriptor_pan a)
    (System_types.AccessDescriptor_transactional a)
    (System_types.AccessDescriptor_nonfault a)
    (System_types.AccessDescriptor_firstfault a)
    (System_types.AccessDescriptor_first a)
    (System_types.AccessDescriptor_contiguous a)
    (System_types.AccessDescriptor_streamingsve a)
    (System_types.AccessDescriptor_ls64 a)
    (System_types.AccessDescriptor_mops a)
    (System_types.AccessDescriptor_rcw a)
    (System_types.AccessDescriptor_rcws a)
    (System_types.AccessDescriptor_toplevel a)
    (conv_varange (System_types.AccessDescriptor_varange a))
    (System_types.AccessDescriptor_a32lsmd a)
    (System_types.AccessDescriptor_tagchecked a)
    (System_types.AccessDescriptor_tagaccess a)
    (conv_mpaminfo (System_types.AccessDescriptor_mpam a)).

Definition conv_mbreqdomain (d : System_types.MBReqDomain) : MBReqDomain :=
  match d with
  | System_types.MBReqDomain_Nonshareable => MBReqDomain_Nonshareable
  | System_types.MBReqDomain_InnerShareable => MBReqDomain_InnerShareable
  | System_types.MBReqDomain_OuterShareable => MBReqDomain_OuterShareable
  | System_types.MBReqDomain_FullSystem => MBReqDomain_FullSystem
  end.

Definition conv_mbreqtypes (t : System_types.MBReqTypes) : MBReqTypes :=
  match t with
  | System_types.MBReqTypes_Reads => MBReqTypes_Reads
  | System_types.MBReqTypes_Writes => MBReqTypes_Writes
  | System_types.MBReqTypes_All => MBReqTypes_All
  end.

Definition conv_dxb (d : System_types.DxB) : DxB :=
  Build_DxB
    (conv_mbreqdomain (System_types.DxB_domain d))
    (conv_mbreqtypes (System_types.DxB_types d))
    (System_types.DxB_nXS d).

Definition conv_barrier (b : System_types.Barrier) : armv9_types.Barrier :=
  match b with
  | System_types.Barrier_DSB d => Barrier_DSB (conv_dxb d)
  | System_types.Barrier_DMB d => Barrier_DMB (conv_dxb d)
  | System_types.Barrier_ISB u => Barrier_ISB u
  | System_types.Barrier_SSBB u => Barrier_SSBB u
  | System_types.Barrier_PSSBB u => Barrier_PSSBB u
  | System_types.Barrier_SB u => Barrier_SB u
  end.

(** Fault inverse (armv9_types → System_types), needed for
    MemRead/MemWrite abort return values flowing back to the Sail continuation *)
Definition conv_fault_inv (f : Fault) : System_types.Fault :=
  match f with
  | Fault_None => System_types.Fault_None
  | Fault_AccessFlag => System_types.Fault_AccessFlag
  | Fault_Alignment => System_types.Fault_Alignment
  | Fault_Background => System_types.Fault_Background
  | Fault_Domain => System_types.Fault_Domain
  | Fault_Permission => System_types.Fault_Permission
  | Fault_Translation => System_types.Fault_Translation
  | Fault_AddressSize => System_types.Fault_AddressSize
  | Fault_SyncExternal => System_types.Fault_SyncExternal
  | Fault_SyncExternalOnWalk => System_types.Fault_SyncExternalOnWalk
  | Fault_SyncParity => System_types.Fault_SyncParity
  | Fault_SyncParityOnWalk => System_types.Fault_SyncParityOnWalk
  | Fault_GPCFOnWalk => System_types.Fault_GPCFOnWalk
  | Fault_GPCFOnOutput => System_types.Fault_GPCFOnOutput
  | Fault_AsyncParity => System_types.Fault_AsyncParity
  | Fault_AsyncExternal => System_types.Fault_AsyncExternal
  | Fault_TagCheck => System_types.Fault_TagCheck
  | Fault_Debug => System_types.Fault_Debug
  | Fault_TLBConflict => System_types.Fault_TLBConflict
  | Fault_BranchTarget => System_types.Fault_BranchTarget
  | Fault_HWUpdateAccessFlag => System_types.Fault_HWUpdateAccessFlag
  | Fault_Lockdown => System_types.Fault_Lockdown
  | Fault_Exclusive => System_types.Fault_Exclusive
  | Fault_ICacheMaint => System_types.Fault_ICacheMaint
  end.

(** Fault forward (System_types → armv9_types) *)
Definition conv_fault (f : System_types.Fault) : Fault :=
  match f with
  | System_types.Fault_None => Fault_None
  | System_types.Fault_AccessFlag => Fault_AccessFlag
  | System_types.Fault_Alignment => Fault_Alignment
  | System_types.Fault_Background => Fault_Background
  | System_types.Fault_Domain => Fault_Domain
  | System_types.Fault_Permission => Fault_Permission
  | System_types.Fault_Translation => Fault_Translation
  | System_types.Fault_AddressSize => Fault_AddressSize
  | System_types.Fault_SyncExternal => Fault_SyncExternal
  | System_types.Fault_SyncExternalOnWalk => Fault_SyncExternalOnWalk
  | System_types.Fault_SyncParity => Fault_SyncParity
  | System_types.Fault_SyncParityOnWalk => Fault_SyncParityOnWalk
  | System_types.Fault_GPCFOnWalk => Fault_GPCFOnWalk
  | System_types.Fault_GPCFOnOutput => Fault_GPCFOnOutput
  | System_types.Fault_AsyncParity => Fault_AsyncParity
  | System_types.Fault_AsyncExternal => Fault_AsyncExternal
  | System_types.Fault_TagCheck => Fault_TagCheck
  | System_types.Fault_Debug => Fault_Debug
  | System_types.Fault_TLBConflict => Fault_TLBConflict
  | System_types.Fault_BranchTarget => Fault_BranchTarget
  | System_types.Fault_HWUpdateAccessFlag => Fault_HWUpdateAccessFlag
  | System_types.Fault_Lockdown => Fault_Lockdown
  | System_types.Fault_Exclusive => Fault_Exclusive
  | System_types.Fault_ICacheMaint => Fault_ICacheMaint
  end.

Definition conv_regime (r : System_types.Regime) : Regime :=
  match r with
  | System_types.Regime_EL3 => Regime_EL3
  | System_types.Regime_EL30 => Regime_EL30
  | System_types.Regime_EL2 => Regime_EL2
  | System_types.Regime_EL20 => Regime_EL20
  | System_types.Regime_EL10 => Regime_EL10
  end.

Definition conv_memtype (m : System_types.MemType) : MemType :=
  match m with
  | System_types.MemType_Normal => MemType_Normal
  | System_types.MemType_Device => MemType_Device
  end.

Definition conv_devicetype (d : System_types.DeviceType) : DeviceType :=
  match d with
  | System_types.DeviceType_GRE => DeviceType_GRE
  | System_types.DeviceType_nGRE => DeviceType_nGRE
  | System_types.DeviceType_nGnRE => DeviceType_nGnRE
  | System_types.DeviceType_nGnRnE => DeviceType_nGnRnE
  end.

Definition conv_mematthints (m : System_types.MemAttrHints) : MemAttrHints :=
  Build_MemAttrHints
    (System_types.MemAttrHints_attrs m)
    (System_types.MemAttrHints_hints m)
    (System_types.MemAttrHints_transient m).

Definition conv_shareability (s : System_types.Shareability) : Shareability :=
  match s with
  | System_types.Shareability_NSH => Shareability_NSH
  | System_types.Shareability_ISH => Shareability_ISH
  | System_types.Shareability_OSH => Shareability_OSH
  end.

Definition conv_memtagtype (m : System_types.MemTagType) : MemTagType :=
  match m with
  | System_types.MemTag_Untagged => MemTag_Untagged
  | System_types.MemTag_AllocationTagged => MemTag_AllocationTagged
  | System_types.MemTag_CanonicallyTagged => MemTag_CanonicallyTagged
  end.

Definition conv_tgx (t : System_types.TGx) : TGx :=
  match t with
  | System_types.TGx_4KB => TGx_4KB
  | System_types.TGx_16KB => TGx_16KB
  | System_types.TGx_64KB => TGx_64KB
  end.

Definition conv_gpcf (g : System_types.GPCF) : GPCF :=
  match g with
  | System_types.GPCF_None => GPCF_None
  | System_types.GPCF_AddressSize => GPCF_AddressSize
  | System_types.GPCF_Walk => GPCF_Walk
  | System_types.GPCF_EABT => GPCF_EABT
  | System_types.GPCF_Fail => GPCF_Fail
  end.

Definition conv_errorstate (e : System_types.ErrorState) : ErrorState :=
  match e with
  | System_types.ErrorState_UC => ErrorState_UC
  | System_types.ErrorState_UEU => ErrorState_UEU
  | System_types.ErrorState_UEO => ErrorState_UEO
  | System_types.ErrorState_UER => ErrorState_UER
  | System_types.ErrorState_CE => ErrorState_CE
  | System_types.ErrorState_Uncategorized => ErrorState_Uncategorized
  | System_types.ErrorState_IMPDEF => ErrorState_IMPDEF
  end.

Definition conv_fulladdress (fa : System_types.FullAddress) : FullAddress :=
  Build_FullAddress
    (conv_pas (System_types.FullAddress_paspace fa))
    (System_types.FullAddress_address fa).

Definition conv_memoryattributes (ma : System_types.MemoryAttributes) : MemoryAttributes :=
  Build_MemoryAttributes
    (conv_memtype (System_types.MemoryAttributes_memtype ma))
    (conv_devicetype (System_types.MemoryAttributes_device ma))
    (conv_mematthints (System_types.MemoryAttributes_inner ma))
    (conv_mematthints (System_types.MemoryAttributes_outer ma))
    (conv_shareability (System_types.MemoryAttributes_shareability ma))
    (conv_memtagtype (System_types.MemoryAttributes_tags ma))
    (System_types.MemoryAttributes_notagaccess ma)
    (System_types.MemoryAttributes_xs ma).

Definition conv_gpcfrecord (g : System_types.GPCFRecord) : GPCFRecord :=
  Build_GPCFRecord
    (conv_gpcf (System_types.GPCFRecord_gpf g))
    (System_types.GPCFRecord_level g).

Definition conv_faultrecord (fr : System_types.FaultRecord) : FaultRecord :=
  Build_FaultRecord
    (conv_fault (System_types.FaultRecord_statuscode fr))
    (conv_acc (System_types.FaultRecord_access fr))
    (conv_fulladdress (System_types.FaultRecord_ipaddress fr))
    (conv_gpcfrecord (System_types.FaultRecord_gpcf fr))
    (conv_fulladdress (System_types.FaultRecord_paddress fr))
    (System_types.FaultRecord_gpcfs2walk fr)
    (System_types.FaultRecord_s2fs1walk fr)
    (System_types.FaultRecord_write fr)
    (System_types.FaultRecord_s1tagnotdata fr)
    (System_types.FaultRecord_tagaccess fr)
    (System_types.FaultRecord_level fr)
    (System_types.FaultRecord_extflag fr)
    (System_types.FaultRecord_secondstage fr)
    (System_types.FaultRecord_assuredonly fr)
    (System_types.FaultRecord_toplevel fr)
    (System_types.FaultRecord_overlay fr)
    (System_types.FaultRecord_dirtybit fr)
    (System_types.FaultRecord_domain fr)
    (conv_errorstate (System_types.FaultRecord_merrorstate fr))
    (System_types.FaultRecord_debugmoe fr).

Definition conv_tlbcontext (tc : System_types.TLBContext) : TLBContext :=
  Build_TLBContext
    (conv_securitystate (System_types.TLBContext_ss tc))
    (conv_regime (System_types.TLBContext_regime tc))
    (System_types.TLBContext_vmid tc)
    (System_types.TLBContext_asid tc)
    (System_types.TLBContext_nG tc)
    (conv_pas (System_types.TLBContext_ipaspace tc))
    (System_types.TLBContext_includes_s1_name tc)
    (System_types.TLBContext_includes_s2_name tc)
    (System_types.TLBContext_includes_gpt_name tc)
    (System_types.TLBContext_ia tc)
    (conv_tgx (System_types.TLBContext_tg tc))
    (System_types.TLBContext_cnp tc)
    (System_types.TLBContext_level tc)
    (System_types.TLBContext_isd128 tc)
    (System_types.TLBContext_xs tc).

Definition conv_addressdescriptor (ad : System_types.AddressDescriptor) : AddressDescriptor :=
  Build_AddressDescriptor
    (conv_faultrecord (System_types.AddressDescriptor_fault ad))
    (conv_memoryattributes (System_types.AddressDescriptor_memattrs ad))
    (conv_fulladdress (System_types.AddressDescriptor_paddress ad))
    (conv_tlbcontext (System_types.AddressDescriptor_tlbcontext ad))
    (System_types.AddressDescriptor_s1assured ad)
    (System_types.AddressDescriptor_s2fs1mro ad)
    (System_types.AddressDescriptor_mecid ad)
    (System_types.AddressDescriptor_vaddress ad).

Definition conv_tlbiop (t : System_types.TLBIOp) : TLBIOp :=
  match t with
  | System_types.TLBIOp_DALL => TLBIOp_DALL
  | System_types.TLBIOp_DASID => TLBIOp_DASID
  | System_types.TLBIOp_DVA => TLBIOp_DVA
  | System_types.TLBIOp_IALL => TLBIOp_IALL
  | System_types.TLBIOp_IASID => TLBIOp_IASID
  | System_types.TLBIOp_IVA => TLBIOp_IVA
  | System_types.TLBIOp_ALL => TLBIOp_ALL
  | System_types.TLBIOp_ASID => TLBIOp_ASID
  | System_types.TLBIOp_IPAS2 => TLBIOp_IPAS2
  | System_types.TLBIPOp_IPAS2 => TLBIPOp_IPAS2
  | System_types.TLBIOp_VAA => TLBIOp_VAA
  | System_types.TLBIOp_VA => TLBIOp_VA
  | System_types.TLBIPOp_VAA => TLBIPOp_VAA
  | System_types.TLBIPOp_VA => TLBIPOp_VA
  | System_types.TLBIOp_VMALL => TLBIOp_VMALL
  | System_types.TLBIOp_VMALLS12 => TLBIOp_VMALLS12
  | System_types.TLBIOp_RIPAS2 => TLBIOp_RIPAS2
  | System_types.TLBIPOp_RIPAS2 => TLBIPOp_RIPAS2
  | System_types.TLBIOp_RVAA => TLBIOp_RVAA
  | System_types.TLBIOp_RVA => TLBIOp_RVA
  | System_types.TLBIPOp_RVAA => TLBIPOp_RVAA
  | System_types.TLBIPOp_RVA => TLBIPOp_RVA
  | System_types.TLBIOp_RPA => TLBIOp_RPA
  | System_types.TLBIOp_PAALL => TLBIOp_PAALL
  end.

Definition conv_tlbilevel (t : System_types.TLBILevel) : TLBILevel :=
  match t with
  | System_types.TLBILevel_Any => TLBILevel_Any
  | System_types.TLBILevel_Last => TLBILevel_Last
  end.

Definition conv_tlbimemattr (t : System_types.TLBIMemAttr) : TLBIMemAttr :=
  match t with
  | System_types.TLBI_AllAttr => TLBI_AllAttr
  | System_types.TLBI_ExcludeXS => TLBI_ExcludeXS
  end.

Definition conv_tlbirecord (tr : System_types.TLBIRecord) : TLBIRecord :=
  Build_TLBIRecord
    (conv_tlbiop (System_types.TLBIRecord_op tr))
    (System_types.TLBIRecord_from_aarch64 tr)
    (conv_securitystate (System_types.TLBIRecord_security tr))
    (conv_regime (System_types.TLBIRecord_regime tr))
    (System_types.TLBIRecord_vmid tr)
    (System_types.TLBIRecord_asid tr)
    (conv_tlbilevel (System_types.TLBIRecord_level tr))
    (conv_tlbimemattr (System_types.TLBIRecord_attr tr))
    (conv_pas (System_types.TLBIRecord_ipaspace tr))
    (System_types.TLBIRecord_address tr)
    (System_types.TLBIRecord_end_address_name tr)
    (System_types.TLBIRecord_d64 tr)
    (System_types.TLBIRecord_d128 tr)
    (System_types.TLBIRecord_ttl tr)
    (System_types.TLBIRecord_tg tr).

Definition conv_tlbiinfo (ti : System_types.TLBIInfo) : TLBIInfo :=
  Build_TLBIInfo
    (conv_tlbirecord (System_types.TLBIInfo_rec ti))
    (conv_shareability (System_types.TLBIInfo_shareability ti)).

Definition conv_translationstartinfo (ts : System_types.TranslationStartInfo) : TranslationStartInfo :=
  Build_TranslationStartInfo
    (conv_securitystate (System_types.TranslationStartInfo_ss ts))
    (conv_regime (System_types.TranslationStartInfo_regime ts))
    (System_types.TranslationStartInfo_vmid ts)
    (System_types.TranslationStartInfo_asid ts)
    (System_types.TranslationStartInfo_va ts)
    (System_types.TranslationStartInfo_cnp ts)
    (conv_acc (System_types.TranslationStartInfo_accdesc ts))
    (System_types.TranslationStartInfo_size ts).

(** ** Custom iMon_from_Sail for ArmTiny.
    Converts System_types.Interface.iMon (sail-tiny-arm Sail monad) to the
    exported iMon (using armv9_types via Arm.Interface). *)

Module ArmTinySI := System_types.Interface.

Definition armtiny_MemReq_from_sail (rr : ArmTinySI.MemReq.t) : MemReq.t :=
  {|MemReq.address := rr.(ArmTinySI.MemReq.address);
    MemReq.access_kind := conv_acc rr.(ArmTinySI.MemReq.access_kind);
    MemReq.address_space := conv_pas rr.(ArmTinySI.MemReq.address_space);
    MemReq.size := rr.(ArmTinySI.MemReq.size);
    MemReq.num_tag := rr.(ArmTinySI.MemReq.num_tag);
  |}.

Definition armtiny_Sail_choose (ct : ChooseType) : iMon (choose_type ct) :=
  match ct with
  | ChooseBool => mchoosef
  | ChooseBit => mchoosef
  | ChooseInt => mthrow "Can't choose infinite Int"
  | ChooseNat => mthrow "Can't choose infinite Nat"
  | ChooseReal => mthrow "Can't choose infinite Real"
  | ChooseString => mthrow "Can't choose infinite String"
  | ChooseBitvector n =>
      if decide (n < 8)%Z then mchoosef else
        mthrow "Can't choose bitvector size over 8"
  | ChooseRange lo hi => mchoosel $ seqZ lo (hi - lo + 1)%Z
  end.

Definition armtiny_Sail_nochoose (ct : ChooseType) : iMon (choose_type ct) :=
  match ct with
  | ChooseBool => mret false
  | ChooseBit => mret B0
  | ChooseInt => mret 0%Z
  | ChooseNat => mret 0%Z
  | ChooseReal => mthrow "Can't choose Real"
  | ChooseString => mret ""
  | ChooseBitvector n => mret (bv_0 _)
  | ChooseRange lo hi => mret lo
  end.

Definition armtiny_Sail_outcome_interp (nondet : bool) {A eo}
    (out : ArmTinySI.outcome eo A) : iMon A :=
  match out with
  | ArmTinySI.RegRead r acc =>
      v ← mcall (RegRead (conv_reg r) acc);
      mret (conv_regval_inv r v)
  | ArmTinySI.RegWrite r acc v =>
      mcall (RegWrite (conv_reg r) acc (conv_regval r v))
  | ArmTinySI.MemRead rr =>
      let mr := armtiny_MemReq_from_sail rr in
      mcall (MemRead mr)
        |$> (λ o, match o with
                  | Ok (val, tags) => inl (val, tags)
                  | Error a => inr (conv_fault_inv a)
                  end)
  | ArmTinySI.MemWrite wr val tags =>
      let mr := armtiny_MemReq_from_sail wr in
      mcall (MemWrite mr val tags)
        |$> (λ o, match o with
                  | Ok tt => inl (Some true)
                  | Error a => inr (conv_fault_inv a)
                  end)
  | ArmTinySI.MemAddressAnnounce aa =>
      mcall (MemWriteAddrAnnounce (armtiny_MemReq_from_sail aa))
  | ArmTinySI.InstrAnnounce _ => mret tt
  | ArmTinySI.BranchAnnounce _ _ => mret tt
  | ArmTinySI.Barrier b => mcall (Barrier (conv_barrier b))
  | ArmTinySI.CacheOp _ => mthrow "CacheOp not supported in sail-tiny-arm"
  | ArmTinySI.TlbOp ti => mcall (TlbOp (conv_tlbiinfo ti))
  | ArmTinySI.TakeException _ => mthrow "TakeException not supported in sail-tiny-arm"
  | ArmTinySI.ReturnException => mcall ReturnException
  | ArmTinySI.TranslationStart ts =>
      mcall (TranslationStart (conv_translationstartinfo ts))
  | ArmTinySI.TranslationEnd te =>
      mcall (TranslationEnd (conv_addressdescriptor te))
  | ArmTinySI.GenericFail msg => mthrow msg
  | ArmTinySI.CycleCount => mret tt
  | ArmTinySI.GetCycleCount => mthrow "GetCycleCount not supported"
  | ArmTinySI.Choose ct =>
      if nondet then armtiny_Sail_choose ct else armtiny_Sail_nochoose ct
  | ArmTinySI.Discard => mdiscard
  | ArmTinySI.Message _ => mret tt
  | ArmTinySI.ExtraOutcome e => mthrow "ExtraOutcome not supported"
  end.

Fixpoint armtiny_iMon_from_Sail (nondet : bool) {A eo}
    (smon : ArmTinySI.iMon eo A) : iMon A :=
  match smon with
  | ArmTinySI.Ret a => mret a
  | ArmTinySI.Next out k =>
      r ← armtiny_Sail_outcome_interp nondet out;
      armtiny_iMon_from_Sail nondet (k r)
  end.

(** The semantics of instructions from [sail-tiny-arm] by using the custom
    conversion code above *)
Definition sail_tiny_arm_sem (nondet : bool) : iMon () :=
  armtiny_iMon_from_Sail nondet (System.fetch_and_execute ()).
