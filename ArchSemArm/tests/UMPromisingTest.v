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

(** Tests for UMPromising - User-mode Promising model with full sail-arm *)

From ASCommon Require Import Options.
From ASCommon Require Import Common CResult CList Exec.

From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.tests Require Import SailArmRegs.

Import SailArm.armv9_types.
Import ArmTM.

Open Scope stdpp.
Open Scope bv.

(** Helper to check register values in results *)
Definition check_regs (r : register_bitvector_64) (regs : registerMap)
  : result string Z :=
    if reg_lookup (R_bitvector_64 r) regs is Some r0 then
      Ok (bv_unsigned r0)
    else
      Error "register not in the thread state".

Definition reg_extract {n} (reg : register_bitvector_64) (tid : fin n)
    `(a : archModel.res Empty_set n term) : result string Z :=
  match a with
  | archModel.Res.FinalState fs _ =>
    let regs : registerMap := fs.(archState.regs) !!! tid in
    check_regs reg regs
  | archModel.Res.Error s => Error s
  | archModel.Res.Flagged e => match e with end
  end.

(** We test against the full sail-arm semantics.
    Using nondet=false to avoid enumerating large bitvector choices. *)
Definition arm_full_sem := sail_arm_sem false.

(* Run EOR X0, X1, X2 at pc address 0x400000, opcode is 0xca020020 *)
Module EOR.
  Definition init_reg : registerMap :=
    sail_arm_init_regs
    |> add_common_regs
    |> reg_insert (R_bitvector_64 PC) 0x400000
    |> reg_insert (R_bitvector_64 R0) 0x0
    |> reg_insert (R_bitvector_64 R1) 0x11
    |> reg_insert (R_bitvector_64 R2) 0x101.

  Definition init_mem : memoryMap :=
    gmap.gmap_empty
    |> mem_insert 0x400000 4 0xca020020. (* EOR X0, X1, X2 *)

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (fun tid rm => reg_lookup (R_bitvector_64 PC) rm =? Some (0x400004 : bv 64)).

  Definition initState : archState n_threads :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 2%nat.

  Definition test_results :=
    UMPromising_exe arm_full_sem fuel n_threads termCond initState.

  (* Expected: X0 = 0x11 XOR 0x101 = 0x110 *)
  (* Note: This test takes significant time with the full sail-arm model *)
  Goal reg_extract R0 0%fin <$> test_results = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End EOR.
