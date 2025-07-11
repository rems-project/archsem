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

Require Import Strings.String.
Require Import stdpp.bitvector.bitvector.
Require Import stdpp.strings.
Require Import stdpp.base.
Require Import stdpp.countable.
Require Import stdpp.vector.
Require Import ASCommon.Options.
Require Import SailStdpp.Base.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Export Riscv.rv64d_types.
Require Import Coq.Reals.Rbase.
From RecordUpdate Require Import RecordSet.
From ASCommon Require Import Common Effects CDestruct FMon.
From ArchSem Require Import Interface FromSail TermModels CandidateExecutions GenPromising.


From Equations Require Import Equations.


Require Import stdpp.decidable.
Require Import stdpp.list.

#[global] Open Scope stdpp.

#[global] Typeclasses Transparent bits.

Module RiscV.
  Module SA := rv64d_types.Arch.
  Module SI := rv64d_types.Interface.

  Module PAManip <: FromSail.PAManip SA.
    Import SA.
    Coercion GReg : register >-> greg.

    Definition pc_reg : greg := PC.
  End PAManip.

  Module Arch := ArchFromSail SA PAManip.

  Module Interface := Interface Arch.

  (** Finally we can generate a conversion function from the sail monad to an
      ArchSem's [iMon] *)
  Module IMonFromSail := IMonFromSail SA SI PAManip Arch Interface.
End RiscV.

Module NoCHERI.
  Definition no_cheri : ¬ RiscV.Arch.CHERI := ltac:(naive_solver).
End NoCHERI.

Bind Scope string_scope with RiscV.Arch.reg.

Module RiscVTM := TermModels RiscV.
Module RiscVCand := CandidateExecutions RiscV RiscVTM NoCHERI.
Module RiscVGenPro := GenPromising RiscV RiscVTM.

Export RiscV.
Export RiscV.Arch.
Export RiscV.Interface.
Export RiscV.IMonFromSail.
Export RiscVTM.
Export RiscVCand.
Export RiscVGenPro.

(** Export [GReg] definitions and typeclasses, since it's what we will manipulate *)
Export GRegister.
Coercion GReg : register >-> greg.

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

Require Riscv.rv64d.
(** The semantics of instructions from [sail-riscv] by using the conversion code
    from [ArchSem.FromSail]. *)
Definition sail_riscv_sem : iMon () :=
  r ← iMon_from_Sail (rv64d.try_step 0 true); mret ().

(** Make registers printable *)
Instance pretty_reg : Pretty reg :=
  λ '(GReg reg), string_of_register reg.
