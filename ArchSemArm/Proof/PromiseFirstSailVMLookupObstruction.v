(******************************************************************************)
(* A future promise can make a bounded VM lookup fail                         *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache
  PromiseFirstSailVMCacheFill.

(** This witnesses an obstruction to unconditional lookup replay. Both caches
    are produced by the actual initialization and promise-filling functions.
    It does not establish a counterexample to the whole Sail execution claim:
    that would also require a certified promise and a terminating execution.

    Initially the root points to a mapped block descriptor at 0x1000. A
    future write changes the root to point to the unmapped page 0x2000. Filling
    succeeds, but lookup at time zero reads the new table's child descriptor
    before testing whether its load time lies in the requested interval. *)
Module VMLookupObstruction.
Import VMPromising.
Open Scope stdpp.
Open Scope bv.

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
Definition lookup mem cache :=
  TLB.lookup 0 imem mem cache false false 0 0 0 0 0.
Definition candidate := TLB.Result.make 0 [4099; 1] 0 0 None.

Lemma initialization : TLB.init 0 imem regs = Ok old.
Proof. reflexivity. Qed.

Lemma promise_succeeds :
  TLB.fill_promise 0 imem [event] event old = Ok (new, ()).
Proof. reflexivity. Qed.

Lemma history_extends :
  VMCacheReplay.extends 0 (TLB.vatlb old) (TLB.vatlb new).
Proof.
  exact (VMCacheFillReplay.fill_promise_extends 0 imem [] event old new
    promise_succeeds).
Qed.

Lemma lookup_before : lookup [] old = Ok [candidate].
Proof.
  vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
Qed.

Lemma lookup_after :
  lookup [event] new = Error "Memory read of unmapped bytes at 0x2000".
Proof. vm_compute. reflexivity. Qed.

(** The failure also occurs when a foreign promise increases the query's
    upper bound to the new history length, including instruction fetches. *)
Lemma lookup_after_full_history ifetch :
  TLB.lookup 0 imem [event] new ifetch false 0 0 0 1 0 =
    Error "Memory read of unmapped bytes at 0x2000".
Proof. destruct ifetch; vm_compute; reflexivity. Qed.

Theorem successful_lookup_not_preserved :
  TLB.init 0 imem regs = Ok old ∧
  TLB.fill_promise 0 imem [event] event old = Ok (new, ()) ∧
  VMCacheReplay.extends 0 (TLB.vatlb old) (TLB.vatlb new) ∧
  lookup [] old = Ok [candidate] ∧
  (∀ candidates, lookup [event] new ≠ Ok candidates).
Proof.
  repeat split; try apply initialization; try apply promise_succeeds;
    try apply history_extends; try apply lookup_before.
  intros candidates. rewrite lookup_after. discriminate.
Qed.
End VMLookupObstruction.
