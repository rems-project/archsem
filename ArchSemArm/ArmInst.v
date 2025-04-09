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

Require Export SailStdpp.Base.
Require Export SailStdpp.ConcurrencyInterfaceTypes.
From ASCommon Require Import Options Common Effects.

Require Export SailTinyArm.System_types.
From ArchSem Require Import
  Interface FromSail TermModels CandidateExecutions GenPromising.

Open Scope stdpp.

(** First we import the sail generated interface modules *)
Module Arm.
  Module SA := System_types.Arch.
  Module SI := System_types.Interface.

  (** Then we need to create a few new things for ArchSem, mostly around pas *)
  Module PAManip <: FromSail.PAManip SA.
    Import SA.
    Implicit Type a : pa.
    Coercion GReg : register >-> greg.
    Bind Scope bv_scope with pa.

    (** Unfold pa that are mword 56 to a bv 56 to work nicely with bv tactics*)
    Ltac pa_unfold := change pa with (bv 56) in *.
    Ltac pa_solve := pa_unfold; bv_solve.

    Definition pa_addZ (a : pa) z : pa := ((a : bv 56) `+Z` z).
    Lemma pa_addZ_assoc pa z z' :
      pa_addZ (pa_addZ pa z) z' = pa_addZ pa (z + z')%Z.
    Proof. pa_solve. Qed.
    Lemma pa_addZ_zero a : pa_addZ a 0 = a.
    Proof. pa_solve. Qed.

    Definition pa_diffN (pa' pa : pa) :=
      Some $ Z.to_N $ bv_unsigned ((pa' : bv 56) - pa).
    Lemma pa_diffN_addZ pa pa' n :
      pa_diffN pa' pa = Some n → pa_addZ pa (Z.of_N n) = pa'.
    Proof.
      unfold pa_diffN, pa_addZ. cdestruct n |- ?.
      pa_solve.
    Qed.

    Lemma pa_diffN_existZ pa pa' z :
      pa_addZ pa z = pa' → is_Some (pa_diffN pa' pa).
    Proof. unfold pa_diffN, pa_addZ. hauto q:on. Qed.

    Lemma pa_diffN_minimalZ pa pa' n :
      pa_diffN pa' pa = Some n →
        ∀ z', pa_addZ pa z' = pa' → (z' < 0 ∨ (Z.of_N n) ≤ z')%Z.
    Proof. unfold pa_diffN, pa_addZ. cdestruct pa',n |- ***. pa_solve. Qed.

    Definition pc_reg : greg := _PC.
  End PAManip.

  (** Then we can use this to generate an ArchSem architecture module *)
  Module Arch := ArchFromSail SA PAManip.
  (** And an ArchSem interface module *)
  Module Interface := Interface Arch.
  (** Finally we can generate a conversion function from the sail monad to an
      ArchSem's [iMon] *)
  Module IMonFromSail := IMonFromSail SA SI PAManip Arch Interface.
End Arm.

(** We can then instantiate the rest of the generic parts of ArchSem on Arm *)
Module ArmTM := TermModels Arm.
Module ArmCand := CandidateExecutions Arm ArmTM.
Module ArmGenPro := GenPromising Arm ArmTM.

(** We export everything we generated, so the rest of ArchSemArm should
    just import this file *)
Export Arm.
Export Arm.Arch.
Export Arm.Interface.
Export Arm.IMonFromSail.
Export ArmTM.
Export ArmCand.
Export ArmGenPro.

(** Unfold pa that are mword 56 to a bv 56 to work nicely with bv tactics*)
Ltac pa_unfold := change pa with (bv 56) in *.
Ltac pa_solve := pa_unfold; bv_solve.

(** Export [GReg] definitions and typeclasses, since it's what we will manipulate *)
Export GRegister.
Coercion GReg : register >-> greg.

(** Make type abbreviations transparent *)
#[export] Typeclasses Transparent pa.
#[export] Typeclasses Transparent SA.pa.
#[export] Typeclasses Transparent reg_acc.
#[export] Typeclasses Transparent reg.
#[export] Typeclasses Transparent bits.


(** HACK: For now all register in system sail-tiny arm are [bv 64], this make
    porting some existing models simpler *)
Definition regt_to_bv64 {r} (rv : reg_type r) : bv 64.
  by destruct r as [?[]]. Defined.
Definition regt_of_bv64 {r} (rv : bv 64) : reg_type r.
  by destruct r as [?[]]. Defined.

(** Since ArchSem only uses register types through [reg_type], there is no need
    for those slow and risky instances *)
#[export] Remove Hints
  Decidable_eq_register_values
  Inhabited_register_values
  Countable_register_values
  : typeclass_instances.

Require SailTinyArm.System.


(** The semantics of instructions from system [sail-tiny-arm] by using the
    conversion code from [ArchSem.FromSail] *)
Definition sail_tiny_arm_sem : iMon () := iMon_from_Sail (System.fetch_and_execute ()).
