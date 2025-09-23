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

From ArchSemArm Require Import UMPromising.

Open Scope stdpp.
Open Scope bv.

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


(** We test against the sail-tiny-arm semantic, with non-determinism enabled *)
Definition arm_sem := sail_tiny_arm_sem true.


(* Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020 *)
Module EOR.
  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x500
    |> reg_insert R0 0x0
    |> reg_insert R1 0x11
    |> reg_insert R2 0x101.

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

  Definition test_results := UMPromising_cert_c arm_sem fuel n_threads initState.

  Goal reg_extract R0 0%fin <$> test_results = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End EOR.

Module LDR. (* LDR X0, [X1, X0] at 0x500, loading from 0x1000 *)
  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x500
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x0.

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 4 0xf8606820 (* LDR X0, [X1, X0] *)
    |> mem_insert 0x1000 8 0x2a. (* data to be read *)

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

  Definition test_results := UMPromising_cert_c arm_sem fuel n_threads initState.

  Goal reg_extract R0 0%fin <$> test_results = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End LDR.

Module STRLDR. (* STR X2, [X1, X0]; LDR X0, [X1, X0] at 0x500, using address 0x1100 *)
  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x500
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x100
    |> reg_insert R2 0x2a.

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 4 0xf8206822 (* STR X2, [X1, X0] *)
    |> mem_insert 0x504 4 0xf8606820 (* LDR X0, [X1, X0] *)
    |> mem_insert 0x1100 8 0x0. (* Memory need to exists to be written to *)

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x508 : bv 64)).

  Definition initState :=
    {|MState.state :=
        {|MState.memory := init_mem;
          MState.regs := [# init_reg];
          MState.address_space := PAS_NonSecure |};
      MState.termCond := termCond |}.

  Definition fuel := 3%nat.

  Definition test_results := UMPromising_cert_c arm_sem fuel n_threads initState.

  Goal reg_extract R0 0%fin <$> test_results ≡ Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    set_solver.
  Qed.
End STRLDR.

Module MP.
  (* A classic MP litmus test
     Thread 1: STR X2, [X1, X0]; STR X5, [X4, X3]
     Thread 2: LDR X5, [X4, X3]; LDR X2, [X1, X0]

     Expected outcome of R2 at Thread 2: 0x2a or 0x0 *)

  Definition init_reg_t1 : registerMap :=
    ∅
    |> reg_insert _PC 0x500
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x100
    |> reg_insert R3 0x1000
    |> reg_insert R4 0x200
    |> reg_insert R2 0x2a
    |> reg_insert R5 0x1.

  Definition init_reg_t2 : registerMap :=
    ∅
    |> reg_insert _PC 0x600
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x100
    |> reg_insert R3 0x1000
    |> reg_insert R4 0x200
    |> reg_insert R2 0x0
    |> reg_insert R5 0x0.

  Definition init_mem : memoryMap :=
    ∅
    (* Thread 1 @ 0x500 *)
    |> mem_insert 0x500 4 0xf8206822  (* STR X2, [X1, X0] *)
    |> mem_insert 0x504 4 0xf8236885  (* STR X5, [X4, X3] *)
    (* Thread 2 @ 0x600 *)
    |> mem_insert 0x600 4 0xf8636885  (* LDR X5, [X4, X3] *)
    |> mem_insert 0x604 4 0xf8606822  (* LDR X2, [X1, X0] *)
    (* Backing memory so the addresses exist *)
    |> mem_insert 0x1100 8 0x0
    |> mem_insert 0x1200 8 0x0.

  Definition n_threads := 2%nat.

  Definition terminate_at := [# Some (0x508 : bv 64); Some (0x608 : bv 64)].

  (* Each thread’s PC must reach the end of its two instructions *)
  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? terminate_at !!! tid).

  Definition initState :=
    {| MState.state :=
        {| MState.memory := init_mem;
            MState.regs := [# init_reg_t1; init_reg_t2];
            MState.address_space := PAS_NonSecure |};
      MState.termCond := termCond |}.

  Definition fuel := 6%nat.

  Definition test_results :=
    UMPromising_cert_c arm_sem fuel n_threads initState.

  Goal elements (regs_extract [(1%fin, R5); (1%fin, R2)] <$> test_results) ≡ₚ
    [Ok [0x0%Z;0x2a%Z]; Ok [0x0%Z;0x0%Z]; Ok [0x1%Z; 0x2a%Z]; Ok [0x1%Z; 0x0%Z]].
  Proof.
    vm_compute (elements _).
    apply NoDup_Permutation; try solve_NoDup; set_solver.
  Qed.
End MP.

Module MPDMBS.
  (* A classic MP litmus test
     Thread 1: STR X2, [X1, X0]; DMB SY; STR X5, [X4, X3]
     Thread 2: LDR X5, [X4, X3]; DMB SY; LDR X2, [X1, X0]

     Expected outcome of R2 at Thread 2: only 0x2a *)

  Definition init_reg_t1 : registerMap :=
    ∅
    |> reg_insert _PC 0x500
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x100
    |> reg_insert R3 0x1000
    |> reg_insert R4 0x200
    |> reg_insert R2 0x2a
    |> reg_insert R5 0x1.

  Definition init_reg_t2 : registerMap :=
    ∅
    |> reg_insert _PC 0x600
    |> reg_insert R0 0x1000
    |> reg_insert R1 0x100
    |> reg_insert R3 0x1000
    |> reg_insert R4 0x200
    |> reg_insert R2 0x0
    |> reg_insert R5 0x0.

  Definition init_mem : memoryMap :=
    ∅
    (* Thread 1 @ 0x500 *)
    |> mem_insert 0x500 4 0xf8206822  (* STR X2, [X1, X0] *)
    |> mem_insert 0x504 4 0xd5033fbf  (* DMB SY *)
    |> mem_insert 0x508 4 0xf8236885  (* STR X5, [X4, X3] *)
    (* Thread 2 @ 0x600 *)
    |> mem_insert 0x600 4 0xf8636885  (* LDR X5, [X4, X3] *)
    |> mem_insert 0x604 4 0xd5033fbf  (* DMB SY *)
    |> mem_insert 0x608 4 0xf8606822  (* LDR X2, [X1, X0] *)
    (* Backing memory so the addresses exist *)
    |> mem_insert 0x1100 8 0x0
    |> mem_insert 0x1200 8 0x0.

  Definition n_threads := 2%nat.

  Definition terminate_at := [# Some (0x50c : bv 64); Some (0x60c : bv 64)].

  (* Each thread’s PC must reach the end of its three instructions *)
  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? terminate_at !!! tid).

  Definition initState :=
    {| MState.state :=
        {| MState.memory := init_mem;
            MState.regs := [# init_reg_t1; init_reg_t2];
            MState.address_space := PAS_NonSecure |};
      MState.termCond := termCond |}.

  Definition fuel := 8%nat.

  Definition test_results :=
    UMPromising_cert_c arm_sem fuel n_threads initState.

  (** The test is fenced enough, the 0x1;0x0 outcome is impossible*)
  Goal elements (regs_extract [(1%fin, R5); (1%fin, R2)] <$> test_results) ≡ₚ
    [Ok [0x0%Z;0x2a%Z]; Ok [0x0%Z;0x0%Z]; Ok [0x1%Z; 0x2a%Z]].
  Proof.
    vm_compute (elements _).
    apply NoDup_Permutation; try solve_NoDup; set_solver.
  Qed.
End MPDMBS.
