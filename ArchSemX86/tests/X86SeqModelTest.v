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
From ASCommon Require Import Common CResult.
From ArchSemX86 Require Import X86Inst.



Open Scope stdpp.
Open Scope bv.

(** Extract RAX in a Z on success to have something printable by Coq *)
Definition RAX_extract `(a : archModel.Res.t ∅ 1 term) : result string Z :=
  match a with
  | archModel.Res.FinalState fs _ =>
      let regs : registerMap := fs.(archState.regs) !!! 0%fin in
      if reg_lookup RAX regs is Some r
      then Ok (bv_unsigned r)
      else Error "RAX not in state"
  | archModel.Res.Error s => Error s
  | archModel.Res.Flagged e => match e with end
  end.

Definition regs_extract `(a : archModel.Res.t ∅ 1 term) :
    result string (list (sigT reg_type)) :=
  match a with
  | archModel.Res.FinalState fs _ =>
      let regs : registerMap := fs.(archState.regs) !!! 0%fin in
      Ok (dmap_to_list regs)
  | archModel.Res.Error s => Error s
  | archModel.Res.Flagged e => match e with end
  end.

(** Standard initial congiguration for user mode *)
Definition common_init_regs :=
  ∅
  |> reg_insert RIP 0x0
  |> reg_insert RFLAGS 0x3000
.

(** We test against the sail-tiny-x86 semantic, with non-determinism disabled *)
Definition x86_sem := sail_tiny_x86_sem false.

(* Run XOR EAX, ECX at RIP address 0x500, which can have opcode 0b11_000_001 @ 0x33 @ 0x48 = 0xc13348 *)
Module EOR.

Definition init_reg : registerMap :=
  common_init_regs
  |> reg_insert RIP 0x500
  |> reg_insert RAX 0x11
  |> reg_insert RCX 0x101
 .

Definition init_mem : memoryMap:=
  ∅
  |> mem_insert 0x500 3 0xc13348. (* xor EAX, ECX *)

Definition termCond : terminationCondition 1 :=
  (λ tid rm, reg_lookup RIP rm =? Some (0x503 : bv 64)).

Definition initState :=
  {|archState.memory := init_mem;
    archState.regs := [# init_reg];
    archState.address_space := () |}.
Definition test_results :=
  sequential_modelc None 2 x86_sem 1%nat termCond initState.

Goal RAX_extract <$> test_results = Listset [Ok 0x110%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End EOR.

Module LDR. (* MOV EAX, [ECX] at 0x500, loading from 0x1000 *)
Definition init_reg : registerMap :=
  common_init_regs
  |> reg_insert RIP 0x500
  |> reg_insert RCX 0x1000
  |> reg_insert RAX 0x0.

Definition init_mem : memoryMap:=
  ∅
  |> mem_insert 0x500 2 0x018b (* MOV EAX, [ECX] = 0b00_000_001 @ 0x8B *)
  |> mem_insert 0x1000 8 0x2a. (* data to be read *)

Definition termCond : terminationCondition 1 :=
  (λ tid rm, reg_lookup RIP rm =? Some (0x502 : bv 64)).

Definition initState :=
  {|archState.memory := init_mem;
    archState.regs := [# init_reg];
    archState.address_space := () |}.
Definition test_results :=
  sequential_modelc None 2 x86_sem 1%nat termCond initState.

Goal RAX_extract <$> test_results = Listset [Ok 0x2a%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End LDR.

Module STRLDR. (* MOV [EAX + 0x100], ECX; MOV EAX, [EAX + 0x100] at 0x500, using address 0x1100 *)
  Definition init_reg : registerMap :=
    common_init_regs
    |> reg_insert RIP 0x500
    |> reg_insert RAX 0x1000
    |> reg_insert RCX 0x2a.

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 6 0x0000_0100_88_89 (* MOV [EAX + 0x100], ECX = 0x0000_0100 @ 0b10_001_000 @ 0x89 *)
    |> mem_insert 0x506 6 0x0000_0100_80_8b (* MOV EAX, [EAX + 0x100] = 0x0000_0100 @ 0b10_000_000 @ 0x8B *)
    |> mem_insert 0x1100 8 0x0. (* Memory need to exist to be written to *)

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup RIP rm =? Some (0x50c : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := () |}.
  Definition test_results :=
    sequential_modelc None 2 x86_sem 1%nat termCond initState.

  Goal RAX_extract <$> test_results = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End STRLDR.

Module Factorial. (* https://godbolt.org/z/GWcWjTrWc, 
  but with opcode 83 instructions changed to opcode 81 instructions,
  and with shifted instruction addresses *)
  Definition init_reg : registerMap :=
    common_init_regs
    |> reg_insert RIP 0x500
    |> reg_insert RDI 5 (* factorial argument *)
    |> reg_insert RCX 0x1234 (* return address *) 
    |> reg_insert RBP 0
    |> reg_insert RSP 0
    |> reg_insert RAX 0.

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 1 0x51              (* push rcx (return address) = 0x5 @ 0b0 @ 0b001 *)
    |> mem_insert 0x501 1 0x55              (* push rbp *)
    |> mem_insert 0x502 3 0xe58948          (* mov rbp, rsp *)
    |> mem_insert 0x505 7 0x00000010ec8148  (* sub rsp, 0x10 *)
    |> mem_insert 0x50c 3 0xfc7d89          (* mov DWORD PTR [rbp-0x4], edi *)
    |> mem_insert 0x50f 7 0x00000000fc7d81  (* cmp DWORD PTR [rbp-0x4], 0x0 *)
    |> mem_insert 0x516 2 0x0775            (* jne 0x51f *)
    |> mem_insert 0x518 5 0x00000001b8      (* mov eax, 0x1 *) 
    |> mem_insert 0x51d 2 0x14eb            (* jmp 0x533 *)
    |> mem_insert 0x51f 3 0xfc458b          (* mov eax, DWORD PTR [rbp-0x4] *) 
    |> mem_insert 0x522 6 0x00000001e881    (* sub eax, 0x1 *) 
    |> mem_insert 0x528 2 0xc789            (* mov edi, eax *)
    |> mem_insert 0x52a 5 0xffffffd2e8      (* call 0x501 (relative RIP change is -2e) *)
    |> mem_insert 0x52f 4 0xfc45af0f        (* imul eax, DWORD PTR [rbp-0x4] *)
    |> mem_insert 0x533 1 0xc9              (* leave *)
    |> mem_insert 0x534 1 0xc3              (* ret *)

    |> mem_insert 0xffff_ffff_ffff_ff00 256 0. (* Memory need to exist to be written to *)

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup RIP rm =? Some (0x1234 : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := () |}.
  Definition test_results :=
    sequential_modelc None 100 x86_sem 1%nat termCond initState.


  Goal RAX_extract <$> test_results = Listset [Ok 120%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End Factorial.
