From ASCommon Require Import Options.
From ASCommon Require Import Common CResult CList Exec.

From ArchSemX86 Require Import X86Inst OperationalX86TSO.

Open Scope stdpp.
Open Scope bv.

(* Helper functions for register checks *)

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
  | archModel.Res.Flagged e => match e with end
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
  | archModel.Res.Flagged e => match e with end
  end.

(** Standard initial configuration for user mode *)
Definition common_init_regs :=
  ∅
  |> reg_insert RIP 0x0
  |> reg_insert RFLAGS 0x3000
.

(** We test against the sail-tiny-x86 semantic, with non-determinism enabled *)
Definition x86_sem := sail_tiny_x86_sem true.

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

  Definition n_threads := 1%nat.

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup RIP rm =? Some (0x503 : bv 64)).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg];
      archState.address_space := () |}.

  Definition test_results :=
    x86_operational_modelc 2 x86_sem 1%nat termCond initState.

  Goal reg_extract RAX 0%fin <$> test_results = Listset [Ok 0x110%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End EOR.

Module MP.
  (* MP litmus test
    Thread 1 : MOV [ECX], 0x1; MOV [EDX], 0x1
    Thread 2 : MOV EAX, [EDX]; MOV EBX, [ECX]

    Expected result : (Thread 1:EAX=1 /\ Thread 1:EBX=0) should be impossible
  *)

  Definition init_reg_t1 : registerMap :=
    common_init_regs
    |> reg_insert RIP 0x500
    |> reg_insert RCX 0x1100
    |> reg_insert RDX 0x1200.

  Definition init_reg_t2 : registerMap :=
    common_init_regs
    |> reg_insert RIP 0x600
    |> reg_insert RAX 0x0
    |> reg_insert RBX 0x0
    |> reg_insert RCX 0x1100
    |> reg_insert RDX 0x1200.

  Definition init_mem : memoryMap :=
    ∅
    (* Thread 1 @ 0x500 *)
    |> mem_insert 0x500 6 0x0000000101c7  (* MOV [ECX], 0x1 = 0x00000001 @ 0b00_000_001 @ 0xC7 *)
    |> mem_insert 0x506 6 0x0000000102c7  (* MOV [EDX], 0x1 = 0x00000001 @ 0b00_000_010 @ 0xC7 *)
    (* Thread 2 @ 0x600 *)
    |> mem_insert 0x600 2 0x028b  (* MOV EAX, [EDX] = 0b00_000_010 @ 0x8B *)
    |> mem_insert 0x602 2 0x198b  (* MOV EBX, [ECX] = 0b00_011_001 @ 0x8B *)
    (* Backing memory so the addresses exist *)
    |> mem_insert 0x1100 8 0x0
    |> mem_insert 0x1200 8 0x0.

  Definition n_threads := 2%nat.

  Definition terminate_at := [# Some (0x50c : bv 64); Some (0x604 : bv 64)].

  (* Each thread’s PC must reach the end of its two instructions *)
  Definition termCond : terminationCondition n_threads :=
    (λ tid rm, reg_lookup RIP rm =? terminate_at !!! tid).

  Definition initState :=
    {|archState.memory := init_mem;
      archState.regs := [# init_reg_t1; init_reg_t2];
      archState.address_space := () |}.

  Definition fuel := 12%nat.

  Definition test_results :=
    x86_operational_modelc fuel x86_sem n_threads termCond initState.
  
  Goal elements (regs_extract [(1%fin, RAX); (1%fin, RBX)] <$> test_results) ≡ₚ
    [Ok [0x0%Z;0x0%Z]; Ok [0x0%Z;0x1%Z]; Ok [0x1%Z; 0x1%Z]].
  Proof.
    vm_compute (elements _).
    apply NoDup_Permutation; try solve_NoDup; set_solver.
  Qed.

End MP.
