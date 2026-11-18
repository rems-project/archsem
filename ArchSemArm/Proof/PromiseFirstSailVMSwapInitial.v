(******************************************************************************)
(* Initialize thread replay for a foreign TLBI exchanged with its neighbour   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMInstructionReplay
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveMachine PromiseFirstSailVMSwapRemoveInit
  PromiseFirstSailVMSwapRemoveDelivery PromiseFirstSailVMSwapBridge PromiseFirstSailVMSwapFixed.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapInitial.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun.
#[local] Typeclasses Transparent Memory.t view UMPromising.view.

Lemma shift_initial (r : Memory.t) ts : VMViews.ts_ok (length r) ts → VMRoots.roots_ok (length r) ts →
  ts_map (shift (S (length r))) ts = ts.
Proof.
  intros Hb Hr. apply (VMSwapFixed.thread_fixed _ (length r)); [|exact Hb|exact Hr].
  intros t Ht. apply shift_lt. lia.
Qed.

Lemma removal_initial imem r tlbi rc epoch ts :
  VMViews.ts_ok (length r) ts → VMRoots.roots_ok (length r) ts → ts_inv imem r tlbi rc epoch [] ts.
Proof.
  intros Hb Hr c Hc. apply TI_init; [apply (VMViews.ok_cache _ _ Hb c Hc)|].
  apply proots_nil_of_bound. unfold VMRoots.roots_ok in Hr. rewrite Hc in Hr. exact Hr.
Qed.

Lemma emitted_ok tid imem r ev ts ts' :
  VMViews.ts_ok (length r) ts → VMRoots.roots_ok (length r) ts → ts_pos ts →
  TState.emit_promise tid imem (ev :: r) ev ts = Ok ts' →
  VMViews.ts_ok (length (ev :: r)) ts' ∧ VMRoots.roots_ok (length (ev :: r)) ts' ∧ ts_pos ts'.
Proof.
  intros Hb Hr Hp He. split.
  - eapply VMViews.emit_promise; [|exact Hb|exact He]. cbn; lia.
  - split; [|eapply emit_promise_pos; [|exact Hp|exact He]; cbn; lia].
    eapply VMRoots.roots_ok_mono; [|eapply VMRoots.emit_roots; [exact Hr|exact He]]. cbn; lia.
Qed.

Section Pair.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat) (ev : Ev.t).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Hypothesis Hrc : tid ≠ rc.
Hypothesis Hissuer : tid ≠ TLBI.tid tlbi.

Theorem older_initial ts one long short swapped :
  VMViews.ts_ok (length r) ts → VMRoots.roots_ok (length r) ts → ts_pos ts →
  TState.emit_promise tid imem (e :: r) e ts = Ok one →
  TState.emit_promise tid imem (ev :: e :: r) ev one = Ok long →
  TState.emit_promise tid imem (ev :: r) ev ts = Ok short →
  TState.emit_promise tid imem (e :: ev :: r) e short = Ok swapped →
  VMSwapBridge.thread_related r (ev :: r) (ev :: r) long swapped ∧
  ts_inv imem r tlbi rc epoch [ev] long.
Proof using Hrc Hissuer.
  intros Hb Hr Hp Hone Hlong Hshort Hswapped.
  rewrite VMSwapRemoveMachine.emit_foreign in Hone, Hswapped by assumption.
  injection Hone as <-. injection Hswapped as <-.
  destruct (emitted_ok tid imem r ev ts short Hb Hr Hp Hshort) as [Hb' [Hr' Hp']].
  pose proof (VMSwapRemoveInit.ts_initial r ts Hb Hr) as Hrel.
  pose proof (removal_initial imem r tlbi rc epoch ts Hb Hr) as Hinv.
  destruct (VMSwapRemoveDelivery.emit_remove imem r tlbi rc epoch tid [] ev ts ts long Hrel Hinv Hlong)
    as [mid [Hmid [Hrel' Hinv']]].
  cbn in Hmid. rewrite Hshort in Hmid. injection Hmid as <-.
  split; [|exact Hinv']. exists short. split; [exact Hrel'|].
  split; [symmetry; apply shift_initial; assumption|]. split; assumption.
Qed.

Theorem newer_initial ts one long short swapped :
  VMViews.ts_ok (length r) ts → VMRoots.roots_ok (length r) ts → ts_pos ts →
  TState.emit_promise tid imem (ev :: r) ev ts = Ok one →
  TState.emit_promise tid imem (e :: ev :: r) e one = Ok long →
  TState.emit_promise tid imem (e :: r) e ts = Ok short →
  TState.emit_promise tid imem (ev :: e :: r) ev short = Ok swapped →
  VMSwapBridge.thread_related (ev :: r) r (ev :: r) long swapped ∧
  ts_inv imem (ev :: r) tlbi rc epoch [] long.
Proof using Hrc Hissuer.
  intros Hb Hr Hp Hone Hlong Hshort Hswapped.
  rewrite VMSwapRemoveMachine.emit_foreign in Hlong, Hshort by assumption.
  injection Hlong as <-. injection Hshort as <-.
  destruct (emitted_ok tid imem r ev ts one Hb Hr Hp Hone) as [Hb' [Hr' Hp']].
  assert (Hshift : swapped = ts_map (shift (S (length r))) one).
  { rewrite <- (shift_initial r ts Hb Hr) in Hswapped.
    change (TState.emit_promise tid imem (ev :: [] ++ e :: r) ev
      (ts_map (shift (S (length r))) ts) = Ok swapped) in Hswapped.
    rewrite emit_promise_shifted in Hswapped. cbn in Hswapped. rewrite Hone in Hswapped.
    injection Hswapped as <-. reflexivity. }
  split; [|apply removal_initial; assumption]. exists one. split.
  - apply VMSwapRemoveInit.ts_initial; assumption.
  - split; [exact Hshift|]. split; assumption.
Qed.
End Pair.
End VMSwapInitial.
