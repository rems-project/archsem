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

From SailTinyX86 Require Export Tiny_x86_types.
From SailTinyX86 Require Import Tiny_x86.

From ASCommon Require Import Options.
From ASCommon Require Import Common FMon.

From ArchSem Require Import
  Interface TermModels CandidateExecutions GenPromising SeqModel ArchInst.
From ArchSem Require Export FromSail.

Module SA := Tiny_x86_types.Arch.
Module SI := Tiny_x86_types.Interface.

Module ArchExtra <: FromSail.ArchExtra SA.
  Import SA.

  Definition pc_reg : reg := RIP.
  Definition reg_of_string := register_of_string.

  Equations reg_type_of_gen (r : reg) (rv : reg_gen_val) :
    result string (reg_type r) :=
    reg_type_of_gen (R_bitvector_64 _) (RVNumber z) := Ok (Z_to_bv 64 z);
    reg_type_of_gen r _ := Error ("error decoding " ++ pretty r)%string.

  Equations reg_type_to_gen (r : reg) (rv : reg_type r) : reg_gen_val :=
    reg_type_to_gen (R_bitvector_64 _) bv := RVNumber (bv_unsigned bv).
End ArchExtra.

(** Then we can use this to generate an ArchSem architecture module *)
Module Arch := ArchFromSail SA ArchExtra.

Module NoCHERI.
  Definition no_cheri : ¬ Arch.CHERI := ltac:(naive_solver).
End NoCHERI.

(** This instantiates all ArchSem arch-generic code, for X86 *)
Module X86 := ArchInst.ArchInst Arch NoCHERI.

Module IMonFromSail := IMonFromSail SA SI ArchExtra Arch X86.Interface.

Export Arch.
Export X86.
Export X86.Interface.
Export X86.TM.
Export X86.Cand.
Export X86.GenPro.
Export X86.SeqModel.
Export X86.ISAManip.
Export IMonFromSail.

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

(** The semantics of instructions from [sail-tiny-x86] by using the conversion code
    from [ArchSem.FromSail]. *)
Definition sail_tiny_x86_sem (nondet : bool) : iMon () :=
  iMon_from_Sail nondet (Tiny_x86.fetch_execute ()).
