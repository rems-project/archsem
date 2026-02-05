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

From ASCommon Require Import Options.
From ASCommon Require Import Common CResult CList.

From ArchSemArm Require Import ArmInst VMPromising.

Open Scope stdpp.
Open Scope bv.

(** * Helper functions for register checks *)

Definition check_regs (r : register_bitvector_64) (regs : registerMap)
  : result string Z :=
  if reg_lookup r regs is Some r0 then
    Ok (bv_unsigned r0)
  else
    Error ((pretty (r : reg )) +:+ " not in the thread state").

Definition reg_extract {n} (reg : register_bitvector_64) (tid : fin n)
    `(a : archModel.res ∅ n term) : result string Z :=
  match a with
  | archModel.Res.FinalState fs _ =>
    let regs : registerMap := fs.(archState.regs) !!! tid in
    check_regs reg regs
  | archModel.Res.Error s => Error s
  | archModel.Res.Flagged f => match f with end
  end.

Definition regs_extract {n} (regs : list (fin n * register_bitvector_64))
  `(a : archModel.res ∅ n term) : result string (list Z) :=
  match a with
  | archModel.Res.FinalState fs _ =>
      for (tid, reg) in regs do
        let regmap : registerMap := fs.(archState.regs) !!! tid in
        check_regs reg regmap
      end
  | archModel.Res.Error s => Error s
  | archModel.Res.Flagged f => match f with end
  end.

(** * Helper functions for PSTATE setup *)
Definition init_pstate (el : bv 2) (sp : bv 1) : ProcState :=
  inhabitant
  |> set ProcState_EL (λ _, el)
  |> set ProcState_SP (λ _, sp).

(** * Helper functions for page table setup *)

Definition table_desc (next_pa : Z) : Z :=
    Z.lor (Z.land next_pa (Z.lnot 0xFFF%Z)) 0x3%Z. (* Valid=1, Table=1 *)

Definition page_desc (out_pa : Z) : Z :=
  Z.lor (Z.lor (Z.land out_pa (Z.lnot 0xFFF%Z)) 0x400%Z) 0x3%Z.  (* Valid=1, Page=1, AF=1 *)

(** We test against the sail-tiny-arm semantic, with non-determinism enabled *)
Definition arm_sem := sail_tiny_arm_sem true.

(* Run EOR X0, X1, X2 at pc address 0x500, whose opcode is 0xca020020.
   MMU is off on this test. *)
Module EORMMUOFF.
  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x500
    |> reg_insert R0 0x0
    |> reg_insert R1 0x11
    |> reg_insert R2 0x101
    |> reg_insert SCTLR_EL1 0x0
    |> reg_insert PSTATE (init_pstate 0%bv 0%bv).

  Definition init_mem : memoryMap :=
    ∅
    |> mem_insert 0x500 4 0xca020020. (* EOR X0, X1, X2 *)

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x504 : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 2%nat.

  Definition test_results :=
    VMPromising_exe arm_sem fuel n_threads termCond initState.

  Goal reg_extract R0 0%fin <$> test_results = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.

  Definition test_results_pf :=
    VMPromising_pf arm_sem fuel n_threads termCond initState.

  Goal reg_extract R0 0%fin <$> test_results_pf = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End EORMMUOFF.

(* Run EOR X0, X1, X2 at PC.

   This test includes address translation from a virtual address
   to a physical address. PAs of the page table is set up as follows:
   - Level 0: 0x80000
   - Level 1: 0x81000
   - Level 2: 0x82000
   - Level 3: 0x82000

   The VA of the PC is 0x8000000500. Aligning this into 48 bits, we get
   0b 0000_0000 1000_0000 0000_0000 0000_0000 0000_0101 0000_0000.
   The VA is decomposed as:
   - Level 0 index: 000000001
   - Level 1 index: 000000000
   - Level 2 index: 000000000
   - Level 3 index: 000000000
   - Page offset: 010100000000 => 0x500.

   So the PA of that VA should be 0x500.
*)
Module EOR.
  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x0
    |> reg_insert R1 0x11
    |> reg_insert R2 0x101
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 0%bv 0%bv).

  Definition init_mem : memoryMap :=
    ∅
    |> mem_insert 0x500 4 0xca020020 (* EOR X0, X1, X2 *)
    (* L0[1] -> L1  (for VA_PC path: L0 index = 1) *)
    |> mem_insert 0x80008 8 0x81803
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82803
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x83803
    (* L3[0] : map VA_PC page -> PA page 0x0000 (executable) *)
    |> mem_insert 0x83000 8 0x403.

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x8000000504 : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 2%nat.

  Definition test_results :=
    VMPromising_exe arm_sem fuel n_threads termCond initState.

  Goal reg_extract R0 0%fin <$> test_results = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.

  Definition test_results_pf :=
    VMPromising_pf arm_sem fuel n_threads termCond initState.

  Goal reg_extract R0 0%fin <$> test_results_pf = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End EOR.

(* LDR X0, [X1, X0] at VA 0x8000000500, loading from VA 0x8000001000

  VA 0x8000000500 maps to PA 0x500 (instruction)
  VA 0x8000001000 maps to PA 0x1000 (data) *)
Module LDR.

  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x8000001000
    |> reg_insert R1 0x0
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 0%bv 0%bv).

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 4 0xf8606820 (* LDR X0, [X1, X0] *)
    |> mem_insert 0x1000 8 0x2a (* data to be read *)
    (* L0[1] -> L1  (for VA with L0 index = 1) *)
    |> mem_insert 0x80008 8 0x81803
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82803
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x83803
    (* L3[0] : map VA page 0x8000000000 -> PA page 0x0000 (executable, readable) *)
    |> mem_insert 0x83000 8 0x403
    (* L3[1] : map VA page 0x8000001000 -> PA page 0x1000 (data, readable, non-executable) *)
    |> mem_insert 0x83008 8 0x60000000001443.

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x8000000504 : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 2%nat.

  Definition test_results :=
    VMPromising_exe arm_sem fuel n_threads termCond initState.

  Goal reg_extract R0 0%fin <$> test_results = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.

  Definition test_results_pf :=
    VMPromising_pf arm_sem fuel n_threads termCond initState.

  Goal reg_extract R0 0%fin <$> test_results_pf = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End LDR.

(* STR X2, [X1, X0]; LDR X0, [X1, X0] at VA 0x8000000500,
   using VA address 0x8000001100 *)
Module STRLDR.
  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x8000001000
    |> reg_insert R1 0x100
    |> reg_insert R2 0x2a
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 0%bv 0%bv).

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 4 0xf8206822 (* STR X2, [X1, X0] *)
    |> mem_insert 0x504 4 0xf8606820 (* LDR X0, [X1, X0] *)
    |> mem_insert 0x1100 8 0x0 (* Memory need to exists to be written to *)
    (* L0[1] -> L1  (for VA with L0 index = 1) *)
    |> mem_insert 0x80008 8 0x81803
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82803
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x83803
    (* L3[0] : map VA page 0x8000000000 -> PA page 0x0000 (executable, readable) *)
    |> mem_insert 0x83000 8 0x403
    (* L3[1] : map VA page 0x8000001000 -> PA page 0x1000 (data, readable, non-executable) *)
    |> mem_insert 0x83008 8 0x60000000001443.

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x8000000508 : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 4%nat.

  Definition test_results :=
    VMPromising_exe arm_sem fuel n_threads termCond initState.

  Goal reg_extract R0 0%fin <$> test_results ≡ Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    set_solver.
  Qed.

  Definition test_results_pf :=
    VMPromising_pf arm_sem fuel n_threads termCond initState.

  Goal reg_extract R0 0%fin <$> test_results_pf ≡ Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    set_solver.
  Qed.
End STRLDR.

(* Sequential page table modification in single thread *)
Module LDRPT.
  (* Single thread that:
     1. Loads from VA 0x8000001000 (gets 0x2a from PA 0x1000)
     2. Modifies L3[1] to remap VA 0x8000001000 -> PA 0x2000
     3. Loads from VA 0x8000001000 again (gets 0x42 from PA 0x2000)
  *)

  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x8000001000    (* VA to load from *)
    |> reg_insert R1 0x0
    |> reg_insert R2 0x8000010008    (* VA of L3[1] descriptor *)
    |> reg_insert R3 0x2003          (* New descriptor: VA -> PA 0x2000 *)
    |> reg_insert R4 0x8000001000    (* VA to load from (second load) *)
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 1%bv 1%bv).

  Definition init_mem : memoryMap :=
    ∅
    |> mem_insert 0x500 4 0xf8606820  (* LDR X0, [X1, X0] - first load *)
    |> mem_insert 0x504 4 0xf8226823  (* STR X3, [X1, X2] - modify page table *)
    |> mem_insert 0x508 4 0xf8646824  (* LDR X4, [X1, X4] - second load *)
    (* Data at two different physical locations *)
    |> mem_insert 0x1000 8 0x2a       (* Original PA - value 0x2a *)
    |> mem_insert 0x2000 8 0x42       (* New PA - value 0x42 *)
    (* Page tables *)
    (* L0[1] -> L1 *)
    |> mem_insert 0x80008 8 0x81003
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82003
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x83003
    (* L3 entries:
       - L3[0]  -> PA 0x0000 (code page for PC)
       - L3[1]  -> PA 0x1000 (first data page), later updated to 0x2003 by the STR
       - L3[16] -> PA 0x83000 (VA alias to edit L3 via VA 0x8000010000)
    *)
    |> mem_insert 0x83000 8 0x40000000000783
    (* L3[1] : initially map VA page 0x8000001000 -> PA page 0x1000 (data) *)
    |> mem_insert 0x83008 8 0x60000000001783
    (* L3[16] : identity map VA page 0x8000010000 -> PA page 0x83000 (page tables) *)
    |> mem_insert 0x83080 8 0x60000000083703.

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x800000050c : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 5%nat.

  Definition test_results :=
    VMPromising_pf arm_sem fuel n_threads termCond initState.

  (* R0 should be 0x2a (from old mapping), R4 should be 0x42 (from new mapping) *)
  Goal elements (regs_extract [(0%fin, R0); (0%fin, R4)] <$> test_results) ≡ₚ
      [Ok [0x2a%Z; 0x2a%Z]; Ok [0x2a%Z; 0x42%Z]].
  Proof.
    vm_compute (elements _).
    apply NoDup_Permutation; try solve_NoDup; set_solver.
  Qed.
End LDRPT.

Module MP.
  (* A classic MP litmus test with address translation
     Thread 1: STR X2, [X1, X0]; STR X5, [X4, X3]
     Thread 2: LDR X5, [X4, X3]; LDR X2, [X1, X0]

     VAs map to PAs:
     - Instructions: 0x8000000500 -> 0x500, 0x8000000600 -> 0x600
     - Data: 0x8000001100 -> 0x1100, 0x8000001200 -> 0x1200

     Expected outcome of (R5, R2) at Thread 2:
      (0x1, 0x2a), (0x0, 0x2a), (0x0, 0x0), (0x1, 0x0)
  *)

  Definition init_reg_t1 : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x8000001000
    |> reg_insert R1 0x100
    |> reg_insert R3 0x8000001000
    |> reg_insert R4 0x200
    |> reg_insert R2 0x2a
    |> reg_insert R5 0x1
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 0%bv 0%bv).

  Definition init_reg_t2 : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000600
    |> reg_insert R0 0x8000001000
    |> reg_insert R1 0x100
    |> reg_insert R3 0x8000001000
    |> reg_insert R4 0x200
    |> reg_insert R2 0x0
    |> reg_insert R5 0x0
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 0%bv 0%bv).

  Definition init_mem : memoryMap :=
    ∅
    (* Thread 1 @ PA 0x500 *)
    |> mem_insert 0x500 4 0xf8206822  (* STR X2, [X1, X0] *)
    |> mem_insert 0x504 4 0xf8236885  (* STR X5, [X4, X3] *)
    (* Thread 2 @ PA 0x600 *)
    |> mem_insert 0x600 4 0xf8636885  (* LDR X5, [X4, X3] *)
    |> mem_insert 0x604 4 0xf8606822  (* LDR X2, [X1, X0] *)
    (* Backing memory so the addresses exist *)
    |> mem_insert 0x1100 8 0x0
    |> mem_insert 0x1200 8 0x0
    (* L0[1] -> L1  (for VA with L0 index = 1) *)
    |> mem_insert 0x80008 8 0x81803
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82803
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x83803
    (* L3[0] : map VA page 0x8000000000 -> PA page 0x0000 (executable) *)
    |> mem_insert 0x83000 8 0x403
    (* L3[1] : map VA page 0x8000001000 -> PA page 0x1000 (data) *)
    |> mem_insert 0x83008 8 0x1443.

  Definition n_threads := 2%nat.

  Definition terminate_at :=
    [#Some (0x8000000508 : bv 64); Some (0x8000000608 : bv 64)].

  (* Each thread's PC must reach the end of its two instructions *)
  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? terminate_at !!! tid).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg_t1; init_reg_t2];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 8%nat.

  Definition test_results :=
    VMPromising_pf arm_sem fuel n_threads termCond initState.

  Goal elements (regs_extract [(1%fin, R5); (1%fin, R2)] <$> test_results) ≡ₚ
    [Ok [0x0%Z;0x2a%Z]; Ok [0x0%Z;0x0%Z]; Ok [0x1%Z; 0x2a%Z]; Ok [0x1%Z; 0x0%Z]].
  Proof.
    vm_compute (elements _).
    apply NoDup_Permutation; try solve_NoDup; set_solver.
  Qed.
End MP.

Module MPDMBS.
  (* A classic MP litmus test with address translation
     Thread 1: STR X2, [X1, X0]; DMB SY; STR X5, [X4, X3]
     Thread 2: LDR X5, [X4, X3]; DMB SY; LDR X2, [X1, X0]

     VAs map to PAs:
     - Instructions: 0x8000000500 -> 0x500, 0x8000000600 -> 0x600
     - Data: 0x8000001100 -> 0x1100, 0x8000001200 -> 0x1200

     Expected outcome of (R5, R2) at Thread 2:
      (0x1, 0x2a), (0x0, 0x2a), (0x0, 0x0) *)

  Definition init_reg_t1 : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x8000001000
    |> reg_insert R1 0x100
    |> reg_insert R3 0x8000001000
    |> reg_insert R4 0x200
    |> reg_insert R2 0x2a
    |> reg_insert R5 0x1
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 0%bv 0%bv).

  Definition init_reg_t2 : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000600
    |> reg_insert R0 0x8000001000
    |> reg_insert R1 0x100
    |> reg_insert R3 0x8000001000
    |> reg_insert R4 0x200
    |> reg_insert R2 0x0
    |> reg_insert R5 0x0
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 0%bv 0%bv).

  Definition init_mem : memoryMap :=
    ∅
    (* Thread 1 @ PA 0x500 *)
    |> mem_insert 0x500 4 0xf8206822  (* STR X2, [X1, X0] *)
    |> mem_insert 0x504 4 0xd5033fbf  (* DMB SY *)
    |> mem_insert 0x508 4 0xf8236885  (* STR X5, [X4, X3] *)
    (* Thread 2 @ PA 0x600 *)
    |> mem_insert 0x600 4 0xf8636885  (* LDR X5, [X4, X3] *)
    |> mem_insert 0x604 4 0xd5033fbf  (* DMB SY *)
    |> mem_insert 0x608 4 0xf8606822  (* LDR X2, [X1, X0] *)
    (* Backing memory so the addresses exist *)
    |> mem_insert 0x1100 8 0x0
    |> mem_insert 0x1200 8 0x0
    (* L0[1] -> L1  (for VA with L0 index = 1) *)
    |> mem_insert 0x80008 8 0x81003
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82003
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x83003
    (* L3[0] : map VA page 0x8000000000 -> PA page 0x0000 (executable) *)
    |> mem_insert 0x83000 8 0x403
    (* L3[1] : map VA page 0x8000001000 -> PA page 0x1000 (data) *)
    |> mem_insert 0x83008 8 0x60000000001443.

  Definition n_threads := 2%nat.

  Definition terminate_at := [# Some (0x800000050c : bv 64); Some (0x800000060c : bv 64)].

  (* Each thread's PC must reach the end of its three instructions *)
  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? terminate_at !!! tid).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg_t1; init_reg_t2];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 8%nat.

  Definition test_results :=
    VMPromising_pf arm_sem fuel n_threads termCond initState.

  (** The test is fenced enough, the 0x1; 0x0 outcome is impossible*)
  Goal elements (regs_extract [(1%fin, R5); (1%fin, R2)] <$> test_results) ≡ₚ
    [Ok [0x0%Z;0x2a%Z]; Ok [0x0%Z;0x0%Z]; Ok [0x1%Z; 0x2a%Z]].
  Proof.
    vm_compute (elements _).
    apply NoDup_Permutation; try solve_NoDup; set_solver.
  Qed.
End MPDMBS.

(* Sequential page table modification in single thread - BBM violation *)
Module BBMFailure.
  (* Single thread that:
     1. Loads from VA 0x8000001000 (gets 0x2a from PA 0x1000)
     2. Modifies L3[1] to remap VA 0x8000001000 -> PA 0x2000
     3. Loads from VA 0x8000001000 again (gets 0x42 from PA 0x2000)

     This violates BBM because the mapping is changed without proper
     invalidation sequence (DSB, TLBI, DSB).
  *)

  Definition init_reg : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x8000001000    (* VA to load from *)
    |> reg_insert R1 0x0
    |> reg_insert R2 0x8000010008    (* VA of L3[1] descriptor *)
    |> reg_insert R3 0x2003          (* New descriptor: VA -> PA 0x2000 *)
    |> reg_insert R4 0x8000001000    (* VA to load from (second load) *)
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 1%bv 1%bv).

  Definition init_mem : memoryMap :=
    ∅
    |> mem_insert 0x500 4 0xf8606820  (* LDR X0, [X1, X0] - first load *)
    |> mem_insert 0x504 4 0xf8226823  (* STR X3, [X1, X2] - modify page table *)
    |> mem_insert 0x508 4 0xf8646824  (* LDR X4, [X1, X4] - second load *)
    (* Data at two different physical locations *)
    |> mem_insert 0x1000 8 0x2a       (* Original PA - value 0x2a *)
    |> mem_insert 0x2000 8 0x42       (* New PA - value 0x42 *)
    (* Page tables *)
    (* L0[1] -> L1 *)
    |> mem_insert 0x80008 8 0x81003
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82003
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x83003
    (* L3 entries:
       - L3[0]  -> PA 0x0000 (code page for PC)
       - L3[1]  -> PA 0x1000 (first data page), later updated to 0x2003 by the STR
       - L3[16] -> PA 0x83000 (VA alias to edit L3 via VA 0x8000010000)
    *)
    |> mem_insert 0x83000 8 0x40000000000783
    |> mem_insert 0x83008 8 0x60000000001783
    |> mem_insert 0x83080 8 0x60000000083703.

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup _PC rm =? Some (0x800000050c : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 5%nat.

  Definition test_results :=
    VMPromising_pf' MemParam.LaxBBM arm_sem fuel n_threads termCond initState.

  (* BBM failure: two different OAs have different memory contents *)
  Goal elements (regs_extract [(0%fin, R0); (0%fin, R4)] <$> test_results) ≡ₚ
      [Ok [0x2a%Z; 0x2a%Z]; Ok [0x2a%Z; 0x42%Z]; Error "BBM violation detected"].
  Proof.
    vm_compute (elements _).
    apply NoDup_Permutation; try solve_NoDup; set_solver.
  Qed.
End BBMFailure.

(* Break-before-make success case *)
Module BBMSuccess.
  (* Thread 0 updates the last-level PTE for VA 0x8000001000 and then
     executes a simplified break-before-make sequence that only
     invalidates the last-level mapping for that VA:
       DSB ishst; TLBI VALE1IS, X0; DSB ish.
    Thread 1 performs a data access via VA 0x8000001000.
  *)

  Definition init_reg_t1 : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000500
    |> reg_insert R0 0x8000001000    (* VA to load from *)
    |> reg_insert R1 0x0
    |> reg_insert R2 0x8000010008    (* VA of L3[1] descriptor *)
    |> reg_insert R3 0x0
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 1%bv 1%bv).

  Definition init_reg_t2 : registerMap :=
    ∅
    |> reg_insert _PC 0x8000000600
    |> reg_insert R0 0x8000001000    (* VA to load from *)
    |> reg_insert R1 0x0
    |> reg_insert SCTLR_EL1 0x1
    |> reg_insert TCR_EL1 0x0
    |> reg_insert TTBR0_EL1 0x80000
    |> reg_insert ESR_EL1 0x0
    |> reg_insert VBAR_EL1 0x0       (* Exception vector base - needed for fault handling *)
    |> reg_insert ID_AA64MMFR1_EL1 0x0
    |> reg_insert PSTATE (init_pstate 1%bv 1%bv).

  Definition init_mem : memoryMap :=
    ∅
    (* Instructions of T1 *)
    |> mem_insert 0x500 4 0xf8226823  (* STR X3, [X1, X2] - invalidate the PTE *)
    |> mem_insert 0x504 4 0xd5033a9f  (* DSB ISHST *)
    |> mem_insert 0x508 4 0xd5088320  (* TLBI VAE1IS - TLB invalidate by 0x8000001000 *)
    |> mem_insert 0x50C 4 0xd5033b9f  (* DSB ISH *)
    |> mem_insert 0x510 4 0xd5033fdf  (* ISB *)
    (* Instructions of T2 *)
    |> mem_insert 0x600 4 0xf8606820  (* LDR X0, [X1, X0] - read 0x8000001000 *)
    (* Data at two different physical locations *)
    |> mem_insert 0x1000 8 0x2a       (* Original PA - value 0x2a *)
    (* Page tables *)
    (* L0[1] -> L1 *)
    |> mem_insert 0x80008 8 0x81003
    (* L1[0] -> L2 *)
    |> mem_insert 0x81000 8 0x82003
    (* L2[0] -> L3 *)
    |> mem_insert 0x82000 8 0x83003
    (* L3 entries:
       - L3[0]  -> PA 0x0000 (code page for PC)
       - L3[1]  -> PA 0x1000 (first data page)
       - L3[16] -> PA 0x83000 (VA alias to edit L3 via VA 0x8000010000)
    *)
    |> mem_insert 0x83000 8 0x40000000000783
    |> mem_insert 0x83008 8 0x60000000001783
    |> mem_insert 0x83080 8 0x60000000083703.

  Definition n_threads := 2%nat.

  Definition terminate_at_t1 rm : bool :=
    reg_lookup _PC rm =? Some (0x8000000514 : bv 64).

  Definition terminate_at_t2 rm : bool :=
    (* a valid translation *)
    (reg_lookup _PC rm =? Some (0x8000000604 : bv 64))
    (* or a fault *)
    || ((reg_lookup FAR_EL1 rm =? Some (0x8000001000 : bv 64))
        && (reg_lookup ELR_EL1 rm =? Some (0x8000000600 : bv 64))
        && (reg_lookup ESR_EL1 rm =? Some (0x96000007 : bv 64))).

  Definition terminate_at := [# terminate_at_t1; terminate_at_t2].

  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, (terminate_at !!! tid) rm).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg_t1; init_reg_t2];
      archState.address_space := PAS_NonSecure |}.

  Definition fuel := 8%nat.

  Definition test_results_pf :=
    VMPromising_pf' MemParam.LaxBBM arm_sem fuel n_threads termCond initState.

  (* BBM check success *)
  Goal elements (regs_extract [(1%fin, R0)] <$> test_results_pf) ≡ₚ
      [Ok [0x2a%Z]].
  Proof.
    vm_compute (elements _).
    apply NoDup_Permutation; try solve_NoDup; set_solver.
  Qed.
End BBMSuccess.
