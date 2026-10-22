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

From ASCommon Require Import Options Common CResult CList Exec.
From ArchSemArm Require Import ArmInst VMPromising.

Open Scope stdpp.
Open Scope bv.

(** Both caches are built through initialization and promise filling. The old
    root points to a valid L1 block; the promised root points to an unmapped
    table. Queries before the promise must not read that new table, and queries
    including it must preserve both the old candidate and the new error. *)
Module Lookup.
  Definition imem : memoryMap :=
    ∅ |> mem_insert 0 8 4099 |> mem_insert 4096 8 1.
  Definition regs : registerMap :=
    ∅ |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
      |> reg_insert ID_AA64MMFR1_EL1 0.
  Definition event := Ev.Msg (Msg.make 1 0 8 8195).
  Definition old : TLB.t :=
    match TLB.init 0 imem regs with
    | Ok cache => cache
    | Error _ => TLB.make TLB.VATLB.init ∅ ∅ [] 0
    end.
  Definition new : TLB.t :=
    match TLB.fill_promise 0 imem [event] event old with
    | Ok (cache, _) => cache
    | Error _ => old
    end.
  Definition candidate tmax := TLB.Result.make 0 [4099; 1] 0 tmax None.

  Goal TLB.init 0 imem regs = Ok old.
  Proof. reflexivity. Qed.

  Goal TLB.fill_promise 0 imem [event] event old = Ok (new, ()).
  Proof. reflexivity. Qed.

  Goal TLB.lookup 0 imem [] old false false 0 0 0 0 0 =
    Exec.make [candidate 0] [].
  Proof.
    vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
  Qed.

  Goal ∀ ifetch, TLB.lookup 0 imem [event] new ifetch false 0 0 0 0 0 =
    Exec.make [candidate 0] [].
  Proof.
    destruct ifetch; vm_compute;
      repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
  Qed.

  Goal ∀ ifetch, TLB.lookup 0 imem [event] new ifetch false 0 0 0 1 0 =
    Exec.make [candidate 1] ["Memory read of unmapped bytes at 0x2000"].
  Proof.
    destruct ifetch; vm_compute;
      repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
  Qed.

  Goal TLB.lookup 0 imem [event] new false false 0 2 2 1 0 = Exec.make [] [].
  Proof. vm_compute. reflexivity. Qed.

  Definition unmapped : memoryMap := ∅ |> mem_insert 0 8 8195.
  Definition broken : TLB.t :=
    match TLB.init 0 unmapped regs with Ok cache => cache | Error _ => old end.

  Goal TLB.init 0 unmapped regs = Ok broken.
  Proof. reflexivity. Qed.

  Goal TLB.lookup 0 unmapped [] broken false false 0 0 0 0 0 =
    Exec.make [] ["Memory read of unmapped bytes at 0x2000"].
  Proof. vm_compute. reflexivity. Qed.

  (** An invalid root descriptor is another translation alternative. It must
      survive an error in a cached table walk too. *)
  Definition invalidation := Ev.Msg (Msg.make 1 0 8 0).
  Definition thread_lookup : result string (Exec.res string TLB.Result.t) :=
    ts ← TState.init 0 imem
      (regs |> reg_insert SCTLR_EL1 1 |> reg_insert CurrentEL 1);
    ts ← TState.emit_promise 0 imem [event] event ts;
    ts ← TState.emit_promise 0 imem [invalidation; event] invalidation ts;
    mret $ TState.tlb_lookup 0 imem [invalidation; event] ts false false 0 0 0 0 0 2.

  Goal thread_lookup = Ok (Exec.make
    [candidate 2; TLB.Result.make 0 [0] 2 2 None]
    ["Memory read of unmapped bytes at 0x2000"]).
  Proof.
    vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
  Qed.
End Lookup.

(** A single STR X1,[X0] changes the root descriptor to point to an unmapped
    table. Its instruction bytes and original mapping remain available.
    BBM checking is disabled for this descriptor replacement. *)
Module RootWrite.
  Definition regs : registerMap :=
    ∅ |> reg_insert _PC 0x3000 |> reg_insert R0 0 |> reg_insert R1 8195
      |> reg_insert SCTLR_EL1 1 |> reg_insert TCR_EL1 0
      |> reg_insert TTBR0_EL1 0 |> reg_insert ID_AA64MMFR1_EL1 0
      |> reg_insert CurrentEL 1.
  Definition imem : memoryMap :=
    ∅ |> mem_insert 0 8 4099 |> mem_insert 4096 8 1025
      |> mem_insert 0x3000 4 0xf9000001.
  Definition initial : archState 1 :=
    {| archState.regs := [# regs]; archState.memory := imem;
       archState.address_space := PAS_NonSecure |}.
  Definition term : terminationCondition 1 := [# [0x3004]].

  Definition pc (r : archModel.res ∅ 1 term) : result string Z :=
    match r with
    | archModel.Res.FinalState fs _ =>
        match reg_lookup _PC (fs.(archState.regs) !!! 0%fin) with
        | Some v => Ok (bv_unsigned v)
        | None => Error "Missing PC"
        end
    | archModel.Res.Error err => Error err
    | archModel.Res.Flagged f => match f with end
    end.
  Definition direct :=
    pc <$> VMPromising_exe false (sail_tiny_arm_sem false) 3%nat 1%nat term initial.
  Definition promise_first :=
    pc <$> VMPromising_pf false (sail_tiny_arm_sem false) 3%nat 1%nat term initial.

  Goal direct ≡ Listset [Ok 0x3004%Z].
  Proof. unfold direct. vm_compute (_ <$> _). set_solver. Qed.

  Goal promise_first ≡ Listset [Ok 0x3004%Z].
  Proof. unfold promise_first. vm_compute (_ <$> _). set_solver. Qed.

  (** With no valid initial mapping, the runner must still report the failed
      walk and produce no successful final state. *)
  Definition bad_initial : archState 1 :=
    {| archState.regs := [# regs];
       archState.memory := mem_insert 0 8 8195 imem;
       archState.address_space := PAS_NonSecure |}.

  Goal pc <$> VMPromising_exe false (sail_tiny_arm_sem false) 3%nat 1%nat term bad_initial ≡
    Listset [Error "Memory read of unmapped bytes at 0x2000"].
  Proof. vm_compute (_ <$> _). set_solver. Qed.
End RootWrite.
