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

From SailTinyArm Require Export System_types.
From SailTinyArm Require Import System.

From ASCommon Require Import Options.
From ASCommon Require Import Common Effects.

From ArchSem Require Import
  Interface TermModels CandidateExecutions GenPromising SeqModel.
From ArchSem Require Export FromSail.

(** First we import the sail generated interface modules *)
Module Arm.
  Module SA := System_types.Arch.
  Module SI := System_types.Interface.

  (** Then we need to create a few new things for ArchSem *)
  Module ArchExtra <: FromSail.ArchExtra SA.
    Import SA.

    Definition pc_reg : reg := _PC.
    Definition reg_of_string := register_of_string.

    Equations set_ProcState_gen_field (field : string) (val : reg_gen_val)
        (p : ProcState) : result string ProcState :=
      set_ProcState_gen_field "EL" (RVNumber z) p :=
        Ok $ setv ProcState_EL (Z_to_bv 2 z) p;
      set_ProcState_gen_field "SP" (RVNumber z) p :=
        Ok $ setv ProcState_SP (Z_to_bv 1 z) p;
      set_ProcState_gen_field field _ _ :=
        Error ("error setting " ++ field ++ " in PSTATE")%string.

    Equations reg_type_of_gen (r : reg) (rv : reg_gen_val) :
        result string (reg_type r) :=
      reg_type_of_gen (R_bitvector_64 _) (RVNumber z) := Ok (Z_to_bv 64 z);
      reg_type_of_gen (R_ProcState _) (RVStruct l) :=
        foldlM (λ ps '(field, val), set_ProcState_gen_field field val ps) inhabitant l;
      reg_type_of_gen r _ := Error ("error decoding " ++ pretty r)%string.

    Equations reg_type_to_gen (r : reg) (rv : reg_type r) : reg_gen_val :=
      reg_type_to_gen (R_bitvector_64 _) bv := RVNumber (bv_unsigned bv);
      reg_type_to_gen (R_ProcState _) ps :=
        RVStruct [
            ("EL", RVNumber (bv_unsigned (ProcState_EL ps)));
            ("SP", RVNumber (bv_unsigned (ProcState_SP ps)));
            ("TODO", RVString "other fields")].
  End ArchExtra.

  (** Then we can use this to generate an ArchSem architecture module *)
  Module Arch := ArchFromSail SA ArchExtra.
  (** And an ArchSem interface module *)
  Module Interface := Interface Arch.
  (** Finally we can generate a conversion function from the sail monad to an
      ArchSem's [iMon] *)
  Module IMonFromSail := IMonFromSail SA SI ArchExtra Arch Interface.
End Arm.

Module NoCHERI.
  Definition no_cheri : ¬ Arm.Arch.CHERI := ltac:(naive_solver).
End NoCHERI.

(** We can then instantiate the rest of the generic parts of ArchSem on Arm *)
Module ArmTM := TermModels Arm.
Module ArmCand := CandidateExecutions Arm ArmTM NoCHERI.
Module ArmGenPro := GenPromising Arm ArmTM.
Module ArmSeqModel := SequentialModel Arm ArmTM NoCHERI.

(** We export everything we generated, so the rest of ArchSemArm should
    just import this file *)
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
#[export] Typeclasses Transparent System_types.addr_space.
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

(** The semantics of instructions from system [sail-tiny-arm] by using the
    conversion code from [ArchSem.FromSail] *)
Definition sail_tiny_arm_sem (nondet : bool) : iMon () :=
  iMon_from_Sail nondet (System.fetch_and_execute ()).
