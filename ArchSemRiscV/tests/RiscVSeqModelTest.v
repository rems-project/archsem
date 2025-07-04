From ASCommon Require Import Options Common.
From ArchSemRiscV Require Import RiscVInst.
From ASCommon Require Import CResult.



Open Scope stdpp.
Open Scope bv.

(** Extract x1 in a Z on success to have something printable by Coq *)
Definition x1_extract (a : Model.Res.t ∅ 1) : result string Z :=
  match a with
  | Model.Res.FinalState fs =>
      let regs : registerMap := fs.(MState.regs) !!! 0%fin in
      if reg_lookup x1 regs is Some x
      then Ok (bv_unsigned x)
      else Error "x1 not in state"
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => match e with end
  end.

Definition a0_extract (a : Model.Res.t ∅ 1) : result string Z :=
  match a with
  | Model.Res.FinalState fs =>
      let regs : registerMap := fs.(MState.regs) !!! 0%fin in
      if reg_lookup x10 regs is Some x
      then Ok (bv_unsigned x)
      else Error "x10 not in state"
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => match e with end
  end.

Definition regs_extract (a : Model.Res.t ∅ 1) : result string (list (sigT reg_type)) :=
  match a with
  | Model.Res.FinalState fs =>
      let regs : registerMap := fs.(MState.regs) !!! 0%fin in
      Ok (dmap_to_list regs)
  | Model.Res.Error s => Error s
  | Model.Res.Unspecified e => match e with end
  end.

(** Common configuration from Isla config files *)
Definition common_init_regs :=
  ∅
  |> reg_insert PC 0x0
  |> reg_insert satp 0x0
  |> reg_insert misa 0x8000000000001004    (* 64 bits, M, C *)
  |> reg_insert mstatus 0x0000000a00000000 (* 64 bits S / U *)
  |> reg_insert mcountinhibit 0x0
  |> reg_insert mcyclecfg 0x0
  |> reg_insert minstretcfg 0x0
  |> reg_insert mtimecmp 0x0
  |> reg_insert stimecmp 0x0

  |> reg_insert cur_privilege User
  |> reg_insert minstret_increment inhabitant
  |> reg_insert hart_state $ HART_ACTIVE ()
  |> reg_insert mideleg inhabitant
  |> reg_insert medeleg inhabitant
  |> reg_insert mip 0x0  (* no pending interrupts *)
  |> reg_insert mie 0x0  (* no pending interrupts *)
  |> reg_insert mcause inhabitant
  |> reg_insert mtval inhabitant
  |> reg_insert nextPC inhabitant
  |> reg_insert minstret 0x0

  |> reg_insert plat_clint_base 0x0
  |> reg_insert plat_clint_size 0x0

  |> reg_insert plat_rom_base 0x0
  |> reg_insert plat_rom_size 0x0

  |> reg_insert plat_ram_base 0x0
  |> reg_insert plat_ram_size 0x10000

  |> reg_insert pmpcfg_n $ Values.vec_of_list_len $ List.rev (0x0f (* unlocked, TOR, XWR *) :: replicate 63 0x00)
  |> reg_insert pmpaddr_n $ Values.vec_of_list_len $ List.rev (0x20000 :: replicate 63 0x00)
.

(** We test against the sail-riscv semantic, with non-determinism disabled *)
Definition riscv_sem := sail_riscv_sem false.

(* Run xor x1, x2, x3 at pc address 0x500, whose opcode is 0x003140b3 *)
Module EOR.

Definition init_reg : registerMap :=
  common_init_regs
  |> reg_insert PC 0x500
  |> reg_insert x1 0x0
  |> reg_insert x2 0x11
  |> reg_insert x3 0x101
 .

Definition init_mem : memoryMap:=
  ∅
  |> mem_insert 0x500 4 0x003140b3  (* xor x1, x2, x3 *)
  |> mem_insert 0x504 4 0x003140b3. (* xor x1, x2, x3 *)

Definition termCond : terminationCondition 1 :=
  (λ tid rm, reg_lookup PC rm =? Some (0x504 : bv 64)).

Definition initState :=
  {|MState.state :=
      {|MState.memory := init_mem;
        MState.regs := [# init_reg];
        MState.address_space := tt |};
    MState.termCond := termCond |}.
Definition test_results := sequential_modelc None 2 riscv_sem 1%nat initState.

Goal x1_extract <$> test_results = Listset [Ok 0x110%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End EOR.

Module LDR. (* ld x1, 0(x2) at 0x500, loading from 0x1000 *)
Definition init_reg : registerMap :=
  common_init_regs
  |> reg_insert PC 0x500
  |> reg_insert x2 0x1000
  |> reg_insert x1 0x0.

Definition init_mem : memoryMap:=
  ∅
  |> mem_insert 0x500 2 0x6082 (* ld x2, 0(x1) *)
  |> mem_insert 0x1000 8 0x2a. (* data to be read *)

Definition termCond : terminationCondition 1 :=
  (λ tid rm, reg_lookup PC rm =? Some (0x502 : bv 64)).

Definition initState :=
  {|MState.state :=
      {|MState.memory := init_mem;
        MState.regs := [# init_reg];
        MState.address_space := () |};
    MState.termCond := termCond |}.
Definition test_results := sequential_modelc None 2 riscv_sem 1%nat initState.

Goal x1_extract <$> test_results = Listset [Ok 0x2a%Z].
  vm_compute (_ <$> _).
  reflexivity.
Qed.
End LDR.

Module STRLDR. (* sd x2, 0x100(x1); ld x1, 0x100(x1) at 0x500, using address 0x1100 *)
  Definition init_reg : registerMap :=
    common_init_regs
    |> reg_insert PC 0x500
    |> reg_insert x1 0x1000
    |> reg_insert x2 0x2a.

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 4 0x1020b023 (* sd x2, 0x100(x1) *)
    |> mem_insert 0x504 4 0x1000b083 (* ld x1, 0x100(x1) *)
    |> mem_insert 0x1100 8 0x0. (* Memory need to exists to be written to *)

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup PC rm =? Some (0x508 : bv 64)).

  Definition initState :=
    {|MState.state :=
        {|MState.memory := init_mem;
          MState.regs := [# init_reg];
          MState.address_space := () |};
      MState.termCond := termCond |}.
  Definition test_results := sequential_modelc None 2 riscv_sem 1%nat initState.

  Goal x1_extract <$> test_results = Listset [Ok 0x2a%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End STRLDR.

Module Factorial. (* https://godbolt.org/z/fzzajP9nq *)
  Definition init_reg : registerMap :=
    common_init_regs
    |> reg_insert PC 0x500
    |> reg_insert x10 5  (* a0 *)
    |> reg_insert x15 0  (* a5 *)
    |> reg_insert x1 0x1234.  (* ra *)

  Definition init_mem : memoryMap:=
    ∅
    |> mem_insert 0x500 2 0x87aa      (* mv a5, a0 *)
    |> mem_insert 0x502 2 0x4505      (* li a0, 1 *)
    |> mem_insert 0x504 2 0xc789      (* beqz a5, e *)
    |> mem_insert 0x506 4 0x02a7853b  (* mulw a0, a5, a0 *)
    |> mem_insert 0x50a 2 0x37fd      (* addiw a5, a5, -1 *)
    |> mem_insert 0x50c 2 0xffed      (* bnez a5, 6 *)
    |> mem_insert 0x50e 2 0x8082.     (* ret *)

  Definition termCond : terminationCondition 1 :=
    (λ tid rm, reg_lookup PC rm =? Some (0x1234 : bv 64)).

  Definition initState :=
    {|MState.state :=
        {|MState.memory := init_mem;
          MState.regs := [# init_reg];
          MState.address_space := () |};
      MState.termCond := termCond |}.
  Definition test_results := sequential_modelc None 1000 riscv_sem 1%nat initState.

  Goal a0_extract <$> test_results = Listset [Ok 120%Z].
    vm_compute (_ <$> _).
    reflexivity.
  Qed.
End Factorial.
