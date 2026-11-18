(******************************************************************************)
(* A local DSB exchange obstruction cannot reach a validated final result    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMStaleEpoch PromiseFirstSailVMNormalization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMEpochWitness.
Import VMPromising.

Definition ts (pending : list nat) (self : nat) : TState.t :=
  TState.make [] pending ∅ [] ∅ ∅ 0 0 0 0 0 0 0 self 0 0 0 0 ∅ None 0 None.
Definition e1 := Ev.Tlbi (TLBI.All 1) 1 0.
Definition e2 := Ev.Tlbi (TLBI.Asid 1 0%bv) 0 0.
Definition nsh := Barrier_DSB
  {| DxB_domain := MBReqDomain_Nonshareable; DxB_types := MBReqTypes_All; DxB_nXS := false |}.
Definition original := PPState.Make (ts [2] 1) [e2; e1] IIS.init.
Definition exchanged := PPState.Make (ts [1] 2) [e1; e2] IIS.init.
Definition after := PPState.Make
  (setv TState.dsb_epoch 1 (TState.update TState.vdsb 1 (ts [2] 1)))
  [e2; e1] (IIS.add 1 IIS.init).
Definition machine := PState.Make [# ts [] 0; PPState.state after] ∅ [e2; e1].

Example common_emitter_order_preserved : Ev.out_of_order e1 e2 = false.
Proof. vm_compute. reflexivity. Qed.
Example original_nsh_succeeds : Exec.results (run_barrier 1 ∅ nsh 2 original) = [(after, ())].
Proof. vm_compute. reflexivity. Qed.
Example exchanged_nsh_discards : Exec.results (run_barrier 1 ∅ nsh 2 exchanged) = [].
Proof. vm_compute. reflexivity. Qed.
Example old_promise_no_longer_matches :
  Memory.fulfill (Ev.Tlbi (TLBI.Asid 1 0%bv) 0 1) [2] [e2; e1] = None.
Proof. vm_compute. reflexivity. Qed.

(** This state witnesses a failed local guard simulation. It is not claimed
    to be reachable from an architectural initial state. Its continuation
    cannot supply a final-state counterexample, even with arbitrary later
    instructions and promises. *)
Theorem original_continuation_never_valid bbm nondet term final fs :
  rtc (VMNormalization.Mixed bbm nondet term) machine final →
  ¬ VMNormalization.FinalResult bbm term final fs.
Proof.
  eapply (VMStaleEpoch.cannot_complete 2 (TLBI.Asid 1 0%bv) 0 0 bbm 1%fin).
  vm_compute. repeat split; auto.
  left.
Qed.
End VMEpochWitness.
