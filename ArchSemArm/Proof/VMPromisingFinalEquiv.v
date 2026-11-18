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

From ASCommon Require Import Options.
From ASCommon Require Import Common GRel Exec FMon StateT HVec.

From ArchSem Require Import GenPromising.
From ArchSemArm Require Import ArmInst VMPromising VMPromisingExec.
From ArchSemArm.Proof Require Import VMPromisingFacts.

#[local] Open Scope list.
#[local] Open Scope nat.
#[local] Open Scope stdpp.

(** The model-specific promise-first obligation.  VM replayability is local to
    writes and TLBI outcomes; the remaining global condition is the commutation
    of one direct thread step with the promise-first tail.  For VM this is the
    point where immutable instruction blocks and translation/TLBI stability
    assumptions have to be discharged. *)
Definition VMPromising_pf_tail_lift (bbm_param : BBM.param) {n}
    (isem : iMon ()) (term : terminationCondition n) : Prop :=
  CPState.run_tid_pf_tail_lift_property isem (VMPromising bbm_param) term.

Definition VMPromising_pf_tail_lift_exists (bbm_param : BBM.param) {n}
    (isem : iMon ()) (term : terminationCondition n) : Prop :=
  CPState.run_tid_pf_tail_lift_exists_property
    isem (VMPromising bbm_param) term.

Definition VMPromising_pf_tail_same_thread_promise_stable
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPState.run_tid_pf_tail_same_thread_promise_stable_property
    isem (VMPromising bbm_param) term.

Definition VMPromising_pf_tail_event_shape (bbm_param : BBM.param) {n}
    (isem : iMon ()) (term : terminationCondition n) : Prop :=
  CPState.run_tid_pf_tail_event_shape_property
    isem (VMPromising bbm_param) term.

Definition VMPromising_pf_tail_event_shape_replay
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPState.run_tid_pf_tail_event_shape_replay_property
    isem (VMPromising bbm_param) term.

Definition VMPromising_pf_tail_event_shape_core
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPState.run_tid_pf_tail_event_shape_core_property
    isem (VMPromising bbm_param) term.

Definition VMPromising_pf_tail_at_most_one_promise
    (bbm_param : BBM.param) {n} (isem : iMon ()) : Prop :=
  @CPState.run_tid_at_most_one_promise_property
    isem (VMPromising bbm_param) n.

Definition VMPromising_pf_tail_at_most_one_promise_prefix_stable
    (bbm_param : BBM.param) {n} (isem : iMon ()) : Prop :=
  @CPState.run_tid_at_most_one_promise_prefix_stable_property
    isem (VMPromising bbm_param) n.

Lemma VMPromising_pf_tail_at_most_one_promise_from_Sail
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ()) :
  VMPromising_Sail_at_most_one_promise smon →
  VMPromising_pf_tail_at_most_one_promise
    bbm_param (n:=n) (iMon_from_Sail nondet smon).
Proof.
  intros Hat_most st0 tid.
  apply VMPromising_iMon_from_Sail_at_most_one_promise.
  exact Hat_most.
Qed.

Lemma VMPromising_pf_tail_at_most_one_prefix_stable_from_Sail
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ()) :
  (∀ (tid : fin n) (initmem : memoryMap) (ev : Ev.t),
    VMPromising_Sail_prefix_promised_stable
      bbm_param n (tid : nat) initmem ev nondet smon) →
  VMPromising_pf_tail_at_most_one_promise_prefix_stable
    bbm_param (n:=n) (iMon_from_Sail nondet smon).
Proof.
  intros Hstable st0 tid ev.
  apply VMPromising_iMon_from_Sail_prefix_promised_stable.
  apply Hstable.
Qed.

Local Lemma VMPromising_pf_tail_at_most_one_prefix_stable_from_read_code_translation_impl
    (bbm_param : BBM.param) {n} nondet code :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_at_most_one_promise_prefix_stable
    bbm_param (n:=n) (sail_tiny_arm_sem nondet).
Proof.
  intros Hread.
  unfold sail_tiny_arm_sem.
  apply VMPromising_pf_tail_at_most_one_prefix_stable_from_Sail.
  intros tid initmem ev.
  eapply
    VMPromising_Sail_prefix_promised_stable_fetch_and_execute_from_read_code_translation
    with (code := code).
  apply Hread.
Qed.

Definition VMPromising_no_new_events
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPState.run_tid_no_new_events_property
    isem (VMPromising bbm_param) term.

Lemma VMPromising_pf_tail_lift_ret (bbm_param : BBM.param) {n}
    (term : terminationCondition n) :
  VMPromising_pf_tail_lift bbm_param (Ret tt) term.
Proof.
  unfold VMPromising_pf_tail_lift.
  apply CPState.run_tid_pf_tail_lift_from_noop.
  apply CPState.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_tail_lift
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_pf_tail_lift bbm_param isem term →
  VMPromising_pf_tail_lift_exists bbm_param isem term.
Proof.
  unfold VMPromising_pf_tail_lift, VMPromising_pf_tail_lift_exists.
  apply CPState.run_tid_pf_tail_lift_exists_from_tail_lift.
Qed.

Lemma VMPromising_pf_tail_lift_exists_ret
    (bbm_param : BBM.param) {n} (term : terminationCondition n) :
  VMPromising_pf_tail_lift_exists bbm_param (Ret tt) term.
Proof.
  apply VMPromising_pf_tail_lift_exists_from_tail_lift.
  apply VMPromising_pf_tail_lift_ret.
Qed.

Lemma VMPromising_pf_tail_event_shape_ret
    (bbm_param : BBM.param) {n} (term : terminationCondition n) :
  VMPromising_pf_tail_event_shape bbm_param (Ret tt) term.
Proof.
  unfold VMPromising_pf_tail_event_shape.
  apply CPState.run_tid_pf_tail_event_shape_from_noop.
  apply CPState.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma VMPromising_pf_tail_event_shape_core_ret
    (bbm_param : BBM.param) {n} (term : terminationCondition n) :
  VMPromising_pf_tail_event_shape_core bbm_param (Ret tt) term.
Proof.
  unfold VMPromising_pf_tail_event_shape_core.
  apply CPState.run_tid_pf_tail_event_shape_core_from_noop.
  apply CPState.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma VMPromising_pf_tail_event_shape_core_from_at_most_one_promise
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_pf_tail_at_most_one_promise
    bbm_param (n:=n) isem →
  VMPromising_pf_tail_event_shape_core bbm_param isem term.
Proof.
  intro Hat_most.
  unfold VMPromising_pf_tail_at_most_one_promise,
    VMPromising_pf_tail_event_shape_core in *.
  eapply CPState.run_tid_pf_tail_event_shape_core_from_at_most_one_promise.
  - exact (Promising.replay_none_preserves_mem_explicit
      (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact (Promising.replay_promise_replay_one
      (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact Hat_most.
Qed.

Lemma VMPromising_pf_tail_event_shape_replay_from_at_most_one_prefix
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_pf_tail_at_most_one_promise
    bbm_param (n:=n) isem →
  VMPromising_pf_tail_at_most_one_promise_prefix_stable
    bbm_param (n:=n) isem →
  VMPromising_pf_tail_event_shape_replay bbm_param isem term.
Proof.
  intros Hat_most Hprefix.
  unfold VMPromising_pf_tail_at_most_one_promise,
    VMPromising_pf_tail_at_most_one_promise_prefix_stable,
    VMPromising_pf_tail_event_shape_replay in *.
  eapply CPState.run_tid_pf_tail_event_shape_replay_from_at_most_one_prefix.
  - exact (Promising.replay_none_preserves_mem_explicit
      (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact (Promising.replay_promise_replay_one
      (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact Hat_most.
  - exact Hprefix.
  - intros st tid_p tid ev.
    apply VMPromising_terminated_tid_promise.
Qed.

Local Lemma VMPromising_pf_tail_event_shape_replay_from_read_code_translation_impl
    (bbm_param : BBM.param) {n} nondet code
    (term : terminationCondition n) :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_event_shape_replay
    bbm_param (sail_tiny_arm_sem nondet) term.
Proof.
  intro Hread.
  apply VMPromising_pf_tail_event_shape_replay_from_at_most_one_prefix.
  - unfold sail_tiny_arm_sem.
    apply VMPromising_pf_tail_at_most_one_promise_from_Sail.
    apply VMPromising_Sail_at_most_one_promise_fetch_and_execute.
  - apply
      (VMPromising_pf_tail_at_most_one_prefix_stable_from_read_code_translation_impl
         bbm_param (n:=n) nondet code).
    exact Hread.
Qed.

Lemma VMPromising_pf_tail_at_most_one_prefix_stable_from_read_code_translation
    (bbm_param : BBM.param) {n} nondet code :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_at_most_one_promise_prefix_stable
    bbm_param (n:=n) (sail_tiny_arm_sem nondet).
Proof.
  apply
    VMPromising_pf_tail_at_most_one_prefix_stable_from_read_code_translation_impl.
Qed.

Lemma VMPromising_pf_tail_event_shape_replay_from_read_code_translation
    (bbm_param : BBM.param) {n} nondet code
    (term : terminationCondition n) :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_event_shape_replay
    bbm_param (sail_tiny_arm_sem nondet) term.
Proof.
  apply
    VMPromising_pf_tail_event_shape_replay_from_read_code_translation_impl.
Qed.

Lemma VMPromising_pf_tail_event_shape_replay_ret
    (bbm_param : BBM.param) {n} (term : terminationCondition n) :
  VMPromising_pf_tail_event_shape_replay bbm_param (Ret tt) term.
Proof.
  unfold VMPromising_pf_tail_event_shape_replay.
  apply CPState.run_tid_pf_tail_event_shape_replay_from_noop.
  apply CPState.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma VMPromising_no_new_events_ret
    (bbm_param : BBM.param) {n} (term : terminationCondition n) :
  VMPromising_no_new_events bbm_param (Ret tt) term.
Proof.
  unfold VMPromising_no_new_events.
  apply CPState.run_tid_no_new_events_from_noop.
  apply CPState.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma VMPromising_pf_tail_same_thread_promise_stable_ret
    (bbm_param : BBM.param) {n} (term : terminationCondition n) :
  VMPromising_pf_tail_same_thread_promise_stable
    bbm_param (Ret tt) term.
Proof.
  unfold VMPromising_pf_tail_same_thread_promise_stable.
  apply CPState.run_tid_pf_tail_same_thread_promise_stable_ret.
  reflexivity.
Qed.

Lemma VMPromising_same_thread_promise_stable_property_from_tail_stable
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  CPState.run_tid_same_thread_promise_stable_property (n:=n)
    isem (VMPromising bbm_param).
Proof.
  intros Hstable st tid ev.
  destruct Hstable as [Hsame].
  apply VMPromising_imon_future_promise_stable_promised_to_cmon.
  exact (Hsame tid (CPState.initmem st) ev).
Qed.

Lemma VMPromising_same_thread_promise_stable_property_from_Sail_same
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet smon →
  CPState.run_tid_same_thread_promise_stable_property (n:=n)
    (iMon_from_Sail nondet smon) (VMPromising bbm_param).
Proof.
  intros Hstable st tid ev.
  destruct Hstable as [Hsame].
  apply VMPromising_imon_future_promise_stable_promised_to_cmon.
  apply VMPromising_iMon_from_Sail_promised_stable.
  exact (Hsame tid (CPState.initmem st) ev).
Qed.

Lemma VMPromising_promise_preserves_terminated_tid_property
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  CPState.promise_preserves_terminated_tid_property (n:=n)
    (VMPromising bbm_param) term.
Proof.
  intros st tid ev.
  apply VMPromising_terminated_tid_promise.
Qed.

Lemma VMPromising_pf_tail_same_thread_promise_stable_from_tail_stable
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  VMPromising_pf_tail_same_thread_promise_stable
    bbm_param isem term.
Proof.
  intro Hstable.
  unfold VMPromising_pf_tail_same_thread_promise_stable in *.
  apply CPState.run_tid_pf_tail_same_thread_promise_stable_from_same_thread.
  apply (VMPromising_same_thread_promise_stable_property_from_tail_stable
    bbm_param isem term).
  exact Hstable.
Qed.

Lemma VMPromising_pf_tail_same_thread_promise_stable_from_Sail_same
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet smon →
  VMPromising_pf_tail_same_thread_promise_stable
    bbm_param (iMon_from_Sail nondet smon) term.
Proof.
  intro Hstable.
  unfold VMPromising_pf_tail_same_thread_promise_stable.
  apply CPState.run_tid_pf_tail_same_thread_promise_stable_from_same_thread.
  apply (VMPromising_same_thread_promise_stable_property_from_Sail_same
    bbm_param nondet smon term).
  exact Hstable.
Qed.

Lemma VMPromising_promise_preserves_any_terminated_tid_property
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  CPState.promise_preserves_any_terminated_tid_property (n:=n)
    (VMPromising bbm_param) term.
Proof.
  intros st tid_p tid ev.
  apply VMPromising_terminated_tid_promise.
Qed.

Lemma VMPromising_pf_tail_event_shape_from_core
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  VMPromising_pf_tail_event_shape_core bbm_param isem term →
  VMPromising_pf_tail_event_shape bbm_param isem term.
Proof.
  intros Hstable Hevent_shape_core.
  unfold VMPromising_pf_tail_event_shape_core,
    VMPromising_pf_tail_event_shape in *.
  eapply CPState.run_tid_pf_tail_event_shape_from_core.
  - apply
      (VMPromising_same_thread_promise_stable_property_from_tail_stable
         bbm_param isem term).
    exact Hstable.
  - apply
      (VMPromising_promise_preserves_any_terminated_tid_property
         bbm_param isem term).
  - exact Hevent_shape_core.
Qed.

Lemma VMPromising_pf_tail_event_shape_replay_from_event_shape
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_pf_tail_event_shape bbm_param isem term →
  VMPromising_pf_tail_event_shape_replay bbm_param isem term.
Proof.
  unfold VMPromising_pf_tail_event_shape,
    VMPromising_pf_tail_event_shape_replay in *.
  eapply CPState.run_tid_pf_tail_event_shape_replay_from_event_shape.
  - exact
      (Promising.replay_none_preserves_mem_explicit
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact
      (Promising.replay_promise_replay_one
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_event_shape
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_event_shape bbm_param isem term →
  VMPromising_pf_tail_lift_exists bbm_param isem term.
Proof.
  intros Hlift Hevent_shape.
  unfold VMPromising_pf_tail_lift_exists,
    VMPromising_pf_tail_event_shape in *.
  eapply CPState.run_tid_pf_tail_lift_exists_from_event_shape.
  - exact
      (Promising.replay_none_preserves_mem_explicit
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact
      (Promising.replay_promise_replay_one
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact Hlift.
  - exact Hevent_shape.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_event_shape_replay
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_event_shape_replay bbm_param isem term →
  VMPromising_pf_tail_lift_exists bbm_param isem term.
Proof.
  intros Hlift Hevent_shape.
  unfold VMPromising_pf_tail_lift_exists,
    VMPromising_pf_tail_event_shape_replay in *.
  eapply CPState.run_tid_pf_tail_lift_exists_from_event_shape_replay.
  - exact
      (Promising.replay_none_preserves_mem_explicit
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact
      (Promising.replay_promise_replay_one
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact Hlift.
  - exact Hevent_shape.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_tail_lift_event_shape
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_event_shape bbm_param isem term →
  VMPromising_pf_tail_lift_exists bbm_param isem term.
Proof.
  intros Hstable Hlift Hevent_shape.
  unfold VMPromising_pf_tail_event_shape,
    VMPromising_pf_tail_lift_exists in *.
  eapply CPState.run_tid_pf_tail_lift_exists_from_event_shape_tail_lift.
  - exact
      (Promising.replay_none_preserves_mem_explicit
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact
      (Promising.replay_promise_replay_one
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - apply
      (VMPromising_same_thread_promise_stable_property_from_tail_stable
         bbm_param isem term).
    exact Hstable.
  - apply
      (VMPromising_promise_preserves_terminated_tid_property
         bbm_param isem term).
  - exact Hlift.
  - exact Hevent_shape.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_tail_lift_core
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_event_shape_core bbm_param isem term →
  VMPromising_pf_tail_lift_exists bbm_param isem term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  unfold VMPromising_pf_tail_event_shape_core,
    VMPromising_pf_tail_lift_exists in *.
  eapply CPState.run_tid_pf_tail_lift_exists_from_event_shape_core_tail_lift.
  - exact
      (Promising.replay_none_preserves_mem_explicit
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact
      (Promising.replay_promise_replay_one
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - apply
      (VMPromising_same_thread_promise_stable_property_from_tail_stable
         bbm_param isem term).
    exact Hstable.
  - apply
      (VMPromising_promise_preserves_any_terminated_tid_property
         bbm_param isem term).
  - exact Hlift.
  - exact Hevent_shape_core.
Qed.

Lemma VMPromising_promise_first_tail_compatible
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_pf_tail_lift bbm_param isem term →
  CPState.PromiseFirstTailCompatible isem (VMPromising bbm_param) term.
Proof.
  intro Hlift.
  constructor.
  - apply VMPromising_replayable.
  - exact Hlift.
Qed.

Lemma VMPromising_promise_first_compatible
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) :
  VMPromising_pf_tail_lift bbm_param isem term →
  CPState.PromiseFirstCompatible isem (VMPromising bbm_param) term.
Proof.
  intro Hlift.
  apply CPState.promise_first_compatible_from_tail.
  apply VMPromising_promise_first_tail_compatible.
  exact Hlift.
Qed.

Lemma VMPromising_final_to_pf (bbm_param : BBM.param) {n}
    (isem : iMon ()) fuel fuel_pf (term : terminationCondition n)
    initMs fs pt :
  VMPromising_pf_tail_lift bbm_param isem term →
  (S fuel ≤ fuel_pf)%nat →
  archModel.Res.FinalState fs pt ∈
    VMPromising_exe bbm_param isem fuel n term initMs →
  ∃ pt_pf,
    archModel.Res.FinalState fs pt_pf ∈
      VMPromising_pf bbm_param isem fuel_pf n term initMs.
Proof.
  intros Hlift Hfuel Hdirect.
  eapply Promising_to_Modelc_final_to_pf_with_run_tid_pf_tail_lift.
  - exact Hlift.
  - exact Hfuel.
  - exact Hdirect.
Qed.

Lemma VMPromising_final_to_pf_exists (bbm_param : BBM.param) {n}
    (isem : iMon ()) fuel (term : terminationCondition n) initMs fs pt :
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  archModel.Res.FinalState fs pt ∈
    VMPromising_exe bbm_param isem fuel n term initMs →
  ∃ fuel_pf pt_pf,
    archModel.Res.FinalState fs pt_pf ∈
      VMPromising_pf bbm_param isem fuel_pf n term initMs.
Proof.
  intros Hlift Hdirect.
  eapply Promising_to_Modelc_final_to_pf_exists_with_run_tid_pf_tail_lift.
  - exact Hlift.
  - exact Hdirect.
Qed.

Lemma VMPromising_pf_final_equiv (bbm_param : BBM.param) {n}
    (isem : iMon ()) fuel fuel_pf (term : terminationCondition n)
    initMs fs pt :
  VMPromising_pf_tail_lift bbm_param isem term →
  (S fuel ≤ fuel_pf)%nat →
  (archModel.Res.FinalState fs pt ∈
     VMPromising_exe bbm_param isem fuel n term initMs →
   ∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       VMPromising_pf bbm_param isem fuel_pf n term initMs) ∧
  (archModel.Res.FinalState fs pt ∈
     VMPromising_pf bbm_param isem fuel_pf n term initMs →
   ∃ fuel_direct pt_direct,
     (fuel ≤ fuel_direct)%nat ∧
     archModel.Res.FinalState fs pt_direct ∈
       VMPromising_exe bbm_param isem fuel_direct n term initMs).
Proof.
  intros Hlift Hfuel.
  eapply Promising_to_Modelc_pf_final_equiv_with_run_tid_pf_tail_lift.
  - exact Hlift.
  - exact Hfuel.
Qed.

Lemma VMPromising_pf_final_state_equiv (bbm_param : BBM.param) {n}
    (isem : iMon ()) fuel fuel_pf (term : terminationCondition n)
    initMs fs :
  VMPromising_pf_tail_lift bbm_param isem term →
  (S fuel ≤ fuel_pf)%nat →
  ((∃ pt,
     archModel.Res.FinalState fs pt ∈
       VMPromising_exe bbm_param isem fuel n term initMs) →
   ∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       VMPromising_pf bbm_param isem fuel_pf n term initMs) ∧
  ((∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       VMPromising_pf bbm_param isem fuel_pf n term initMs) →
   ∃ fuel_direct pt_direct,
     (fuel ≤ fuel_direct)%nat ∧
     archModel.Res.FinalState fs pt_direct ∈
       VMPromising_exe bbm_param isem fuel_direct n term initMs).
Proof.
  intros Hlift Hfuel.
  eapply Promising_to_Modelc_pf_final_state_equiv_with_run_tid_pf_tail_lift.
  - exact Hlift.
  - exact Hfuel.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_tail_lift bbm_param isem term →
  VMPromising_final_state bbm_param isem term initMs fs ↔
  VMPromising_pf_final_state bbm_param isem term initMs fs.
Proof.
  intro Hlift.
  eapply
    Promising_to_Modelc_pf_final_state_equiv_unbounded_with_run_tid_pf_tail_lift.
  exact Hlift.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_exists
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_final_state bbm_param isem term initMs fs ↔
  VMPromising_pf_final_state bbm_param isem term initMs fs.
Proof.
  intro Hlift.
  eapply
    Promising_to_Modelc_pf_final_state_equiv_unbounded_with_run_tid_pf_tail_lift_exists.
  exact Hlift.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_from_tail_lift_event_shape
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) initMs fs :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_event_shape bbm_param isem term →
  VMPromising_final_state bbm_param isem term initMs fs ↔
  VMPromising_pf_final_state bbm_param isem term initMs fs.
Proof.
  intros Hstable Hlift Hevent_shape.
  apply VMPromising_pf_final_state_equiv_unbounded_exists.
  eapply VMPromising_pf_tail_lift_exists_from_tail_lift_event_shape; eauto.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_from_tail_lift_core
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) initMs fs :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_event_shape_core bbm_param isem term →
  VMPromising_final_state bbm_param isem term initMs fs ↔
  VMPromising_pf_final_state bbm_param isem term initMs fs.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  apply VMPromising_pf_final_state_equiv_unbounded_exists.
  eapply VMPromising_pf_tail_lift_exists_from_tail_lift_core; eauto.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_from_at_most_one_promise
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) initMs fs :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_at_most_one_promise
    bbm_param (n:=n) isem →
  VMPromising_final_state bbm_param isem term initMs fs ↔
  VMPromising_pf_final_state bbm_param isem term initMs fs.
Proof.
  intros Hstable Hlift Hat_most.
  eapply VMPromising_pf_final_state_equiv_unbounded_from_tail_lift_core.
  - exact Hstable.
  - exact Hlift.
  - apply VMPromising_pf_tail_event_shape_core_from_at_most_one_promise.
    exact Hat_most.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_from_Sail_at_most_one_promise
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) initMs fs :
  VMPromising_Sail_tail_stable bbm_param (n:=n) nondet smon →
  VMPromising_pf_tail_lift_exists
    bbm_param (iMon_from_Sail nondet smon) term →
  VMPromising_Sail_at_most_one_promise smon →
  VMPromising_final_state
    bbm_param (iMon_from_Sail nondet smon) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (iMon_from_Sail nondet smon) term initMs fs.
Proof.
  intros Hstable Hlift Hat_most.
  eapply VMPromising_pf_final_state_equiv_unbounded_from_at_most_one_promise.
  - apply VMPromising_tail_stable_from_Sail.
    exact Hstable.
  - exact Hlift.
  - apply VMPromising_pf_tail_at_most_one_promise_from_Sail.
    exact Hat_most.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_from_event_shape
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_event_shape bbm_param isem term →
  VMPromising_final_state bbm_param isem term initMs fs ↔
  VMPromising_pf_final_state bbm_param isem term initMs fs.
Proof.
  intros Hlift Hevent_shape.
  apply VMPromising_pf_final_state_equiv_unbounded_exists.
  eapply VMPromising_pf_tail_lift_exists_from_event_shape; eauto.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_from_event_shape_replay
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_tail_lift_exists bbm_param isem term →
  VMPromising_pf_tail_event_shape_replay bbm_param isem term →
  VMPromising_final_state bbm_param isem term initMs fs ↔
  VMPromising_pf_final_state bbm_param isem term initMs fs.
Proof.
  intros Hlift Hevent_shape.
  eapply
    Promising_to_Modelc_pf_final_state_equiv_unbounded_from_event_shape_replay.
  - exact (VMPromising_replayable bbm_param).
  - exact Hlift.
  - exact Hevent_shape.
Qed.

Record VMPromising_Sail_pf_compatible (bbm_param : BBM.param)
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) : Prop := {
    VMPromising_Sail_pf_tail_lift :
      VMPromising_pf_tail_lift_exists
        bbm_param (iMon_from_Sail nondet smon) term;
    VMPromising_Sail_pf_event_shape_replay :
      VMPromising_pf_tail_event_shape_replay
        bbm_param (iMon_from_Sail nondet smon) term;
  }.

Lemma VMPromising_Sail_pf_compatible_from_tail_lift_core
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable bbm_param (n:=n) nondet smon →
  VMPromising_pf_tail_lift_exists
    bbm_param (iMon_from_Sail nondet smon) term →
  VMPromising_pf_tail_event_shape_core
    bbm_param (iMon_from_Sail nondet smon) term →
  VMPromising_Sail_pf_compatible bbm_param nondet smon term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  pose proof
    (VMPromising_tail_stable_from_Sail bbm_param nondet smon Hstable)
    as Htail_stable.
  constructor.
  - exact Hlift.
  - apply VMPromising_pf_tail_event_shape_replay_from_event_shape.
    eapply VMPromising_pf_tail_event_shape_from_core.
    + exact Htail_stable.
    + exact Hevent_shape_core.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_Sail_same_tail_lift_core
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet smon →
  VMPromising_pf_tail_lift_exists
    bbm_param (iMon_from_Sail nondet smon) term →
  VMPromising_pf_tail_event_shape_core
    bbm_param (iMon_from_Sail nondet smon) term →
  VMPromising_pf_tail_lift_exists
    bbm_param (iMon_from_Sail nondet smon) term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  unfold VMPromising_pf_tail_event_shape_core,
    VMPromising_pf_tail_lift_exists in *.
  eapply CPState.run_tid_pf_tail_lift_exists_from_event_shape_core_tail_lift.
  - exact
      (Promising.replay_none_preserves_mem_explicit
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - exact
      (Promising.replay_promise_replay_one
         (VMPromising bbm_param) (VMPromising_replayable bbm_param)).
  - apply
      (VMPromising_same_thread_promise_stable_property_from_Sail_same
         bbm_param nondet smon term).
    exact Hstable.
  - apply
      (VMPromising_promise_preserves_any_terminated_tid_property
         bbm_param (iMon_from_Sail nondet smon) term).
  - exact Hlift.
  - exact Hevent_shape_core.
Qed.

Lemma VMPromising_Sail_pf_compatible_from_same_tail_lift_core
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet smon →
  VMPromising_pf_tail_lift_exists
    bbm_param (iMon_from_Sail nondet smon) term →
  VMPromising_pf_tail_event_shape_core
    bbm_param (iMon_from_Sail nondet smon) term →
  VMPromising_Sail_pf_compatible bbm_param nondet smon term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  pose proof
    (VMPromising_same_thread_promise_stable_property_from_Sail_same
       bbm_param nondet smon term Hstable) as Hsame_thread.
  pose proof
    (VMPromising_promise_preserves_any_terminated_tid_property
       bbm_param (iMon_from_Sail nondet smon) term) as Hany_terminated.
  constructor.
  - exact Hlift.
  - apply VMPromising_pf_tail_event_shape_replay_from_event_shape.
    unfold VMPromising_pf_tail_event_shape,
      VMPromising_pf_tail_event_shape_core in *.
    eapply CPState.run_tid_pf_tail_event_shape_from_core; eauto.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_Sail_compatible
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  VMPromising_Sail_pf_compatible bbm_param nondet smon term →
  VMPromising_pf_tail_lift_exists
    bbm_param (iMon_from_Sail nondet smon) term.
Proof.
  intro Hcompat.
  destruct Hcompat as [Hlift Hevent_shape].
  eapply VMPromising_pf_tail_lift_exists_from_event_shape_replay; eauto.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_from_Sail_compatible
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) initMs fs :
  VMPromising_Sail_pf_compatible bbm_param nondet smon term →
  VMPromising_final_state
    bbm_param (iMon_from_Sail nondet smon) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (iMon_from_Sail nondet smon) term initMs fs.
Proof.
  intro Hcompat.
  destruct Hcompat as [Hlift Hevent_shape].
  eapply VMPromising_pf_final_state_equiv_unbounded_from_event_shape_replay;
    eauto.
Qed.

Definition VMPromising_pf_compatible
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) : Prop :=
  VMPromising_Sail_pf_compatible bbm_param nondet
    (System.fetch_and_execute ()) term.

Local Lemma VMPromising_pf_compatible_from_tail_lift_core_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_event_shape_core
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  unfold VMPromising_pf_compatible, sail_tiny_arm_sem in *.
  eapply VMPromising_Sail_pf_compatible_from_tail_lift_core; eauto.
Qed.

Local Lemma VMPromising_pf_compatible_from_Sail_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  intros Hstable Hlift.
  unfold VMPromising_pf_compatible, sail_tiny_arm_sem in *.
  constructor.
  - exact Hlift.
  - apply VMPromising_pf_tail_event_shape_replay_from_event_shape.
    eapply VMPromising_pf_tail_event_shape_from_core.
    + apply VMPromising_tail_stable_from_Sail.
      exact Hstable.
    + apply VMPromising_pf_tail_event_shape_core_from_at_most_one_promise.
      unfold sail_tiny_arm_sem.
      apply VMPromising_pf_tail_at_most_one_promise_from_Sail.
      apply VMPromising_Sail_at_most_one_promise_fetch_and_execute.
Qed.

Local Lemma VMPromising_pf_compatible_from_Sail_tail_lift_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  intros Hstable Hlift.
  eapply VMPromising_pf_compatible_from_tail_lift_core_impl.
  - exact Hstable.
  - exact Hlift.
  - apply VMPromising_pf_tail_event_shape_core_from_at_most_one_promise.
    unfold sail_tiny_arm_sem.
    apply VMPromising_pf_tail_at_most_one_promise_from_Sail.
    apply VMPromising_Sail_at_most_one_promise_fetch_and_execute.
Qed.

Local Lemma VMPromising_pf_compatible_from_same_tail_lift_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  intros Hstable Hlift.
  unfold VMPromising_pf_compatible, sail_tiny_arm_sem in *.
  eapply VMPromising_Sail_pf_compatible_from_same_tail_lift_core.
  - exact Hstable.
  - exact Hlift.
  - apply VMPromising_pf_tail_event_shape_core_from_at_most_one_promise.
    unfold sail_tiny_arm_sem.
    apply VMPromising_pf_tail_at_most_one_promise_from_Sail.
    apply VMPromising_Sail_at_most_one_promise_fetch_and_execute.
Qed.

Local Lemma VMPromising_pf_compatible_from_read_code_translation_impl
    (bbm_param : BBM.param) {n} nondet code
    (term : terminationCondition n) :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  intros Hread Hlift.
  unfold VMPromising_pf_compatible, sail_tiny_arm_sem in *.
  constructor.
  - exact Hlift.
  - eapply VMPromising_pf_tail_event_shape_replay_from_read_code_translation_impl.
    exact Hread.
Qed.

Lemma VMPromising_pf_compatible_from_tail_lift_core
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_event_shape_core
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  apply VMPromising_pf_compatible_from_tail_lift_core_impl.
Qed.

Lemma VMPromising_pf_compatible_from_Sail
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  apply VMPromising_pf_compatible_from_Sail_impl.
Qed.

Lemma VMPromising_pf_compatible_from_Sail_tail_lift
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  apply VMPromising_pf_compatible_from_Sail_tail_lift_impl.
Qed.

Lemma VMPromising_pf_compatible_from_same_tail_lift
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  apply VMPromising_pf_compatible_from_same_tail_lift_impl.
Qed.

Lemma VMPromising_pf_compatible_from_read_code_translation_and_tail_lift
    (bbm_param : BBM.param) {n} nondet code
    (term : terminationCondition n) :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_compatible bbm_param nondet term.
Proof.
  intros Hread Hlift.
  eapply VMPromising_pf_compatible_from_read_code_translation_impl.
  - exact Hread.
  - exact Hlift.
Qed.

Local Lemma VMPromising_pf_tail_lift_exists_from_compatible_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_pf_compatible bbm_param nondet term →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term.
Proof.
  unfold VMPromising_pf_compatible, sail_tiny_arm_sem.
  apply VMPromising_pf_tail_lift_exists_from_Sail_compatible.
Qed.

Local Lemma VMPromising_pf_tail_lift_exists_from_Sail_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term.
Proof.
  intros Hstable Hlift.
  apply VMPromising_pf_tail_lift_exists_from_compatible_impl.
  eapply VMPromising_pf_compatible_from_Sail_impl; eauto.
Qed.

Local Lemma VMPromising_pf_tail_lift_exists_from_read_code_translation_impl
    (bbm_param : BBM.param) {n} nondet code
    (term : terminationCondition n) :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term.
Proof.
  intros Hread Hlift.
  apply VMPromising_pf_tail_lift_exists_from_compatible_impl.
  eapply VMPromising_pf_compatible_from_read_code_translation_impl; eauto.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_compatible
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_pf_compatible bbm_param nondet term →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term.
Proof.
  apply VMPromising_pf_tail_lift_exists_from_compatible_impl.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_Sail
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term.
Proof.
  apply VMPromising_pf_tail_lift_exists_from_Sail_impl.
Qed.

Lemma VMPromising_pf_tail_lift_exists_from_read_code_translation_and_tail_lift
    (bbm_param : BBM.param) {n} nondet code
    (term : terminationCondition n) :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term.
Proof.
  intros _ Hlift.
  exact Hlift.
Qed.

Local Lemma VMPromising_pf_equiv_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_compatible bbm_param nondet term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intro Hcompat.
  apply
    (VMPromising_pf_final_state_equiv_unbounded_from_Sail_compatible
       bbm_param nondet (System.fetch_and_execute ()) term).
  exact Hcompat.
Qed.

Local Lemma VMPromising_pf_equiv_from_obligations_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_event_shape_replay
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hlift Hevent_shape.
  eapply VMPromising_pf_final_state_equiv_unbounded_from_event_shape_replay;
    eauto.
Qed.

Local Lemma VMPromising_pf_equiv_from_read_code_translation_impl
    (bbm_param : BBM.param) {n} nondet code
    (term : terminationCondition n) initMs fs :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hread Hlift.
  apply VMPromising_pf_equiv_impl.
  eapply VMPromising_pf_compatible_from_read_code_translation_impl; eauto.
Qed.

Local Lemma VMPromising_pf_equiv_from_at_most_one_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_tail_stable
    bbm_param (n:=n) (sail_tiny_arm_sem nondet) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_at_most_one_promise
    bbm_param (n:=n) (sail_tiny_arm_sem nondet) →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hstable Hlift Hat_most.
  eapply VMPromising_pf_final_state_equiv_unbounded_from_at_most_one_promise;
    eauto.
Qed.

Local Lemma VMPromising_pf_equiv_from_Sail_at_most_one_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_Sail_at_most_one_promise (System.fetch_and_execute ()) →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hstable Hlift Hat_most.
  unfold sail_tiny_arm_sem in *.
  eapply
    VMPromising_pf_final_state_equiv_unbounded_from_Sail_at_most_one_promise;
    eauto.
Qed.

Local Lemma VMPromising_pf_equiv_from_Sail_impl
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hstable Hlift.
  apply VMPromising_pf_final_state_equiv_unbounded_exists.
  eapply VMPromising_pf_tail_lift_exists_from_Sail_impl.
  - exact Hstable.
  - exact Hlift.
Qed.

Lemma VMPromising_pf_equiv
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_compatible bbm_param nondet term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply VMPromising_pf_equiv_impl.
Qed.

Lemma VMPromising_pf_equiv_from_tail_lift
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply VMPromising_pf_final_state_equiv_unbounded_exists.
Qed.

Lemma VMPromising_pf_equiv_from_obligations
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_event_shape_replay
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply VMPromising_pf_equiv_from_obligations_impl.
Qed.

Lemma VMPromising_pf_equiv_from_read_code_translation_and_tail_lift
    (bbm_param : BBM.param) {n} nondet code
    (term : terminationCondition n) initMs fs :
  (∀ (tid : fin n) initmem ev,
    VMPromising_read_code_translation_stability
      bbm_param n (tid : nat) initmem code ev) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hread Hlift.
  apply VMPromising_pf_equiv_impl.
  eapply VMPromising_pf_compatible_from_read_code_translation_impl.
  - exact Hread.
  - exact Hlift.
Qed.

Lemma VMPromising_pf_equiv_from_at_most_one
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_tail_stable
    bbm_param (n:=n) (sail_tiny_arm_sem nondet) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_pf_tail_at_most_one_promise
    bbm_param (n:=n) (sail_tiny_arm_sem nondet) →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply VMPromising_pf_equiv_from_at_most_one_impl.
Qed.

Lemma VMPromising_pf_equiv_from_Sail_at_most_one
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_Sail_at_most_one_promise (System.fetch_and_execute ()) →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply VMPromising_pf_equiv_from_Sail_at_most_one_impl.
Qed.

Lemma VMPromising_pf_equiv_from_Sail
    (bbm_param : BBM.param) {n} nondet
    (term : terminationCondition n) initMs fs :
  VMPromising_Sail_tail_stable
    bbm_param (n:=n) nondet (System.fetch_and_execute ()) →
  VMPromising_pf_tail_lift_exists
    bbm_param (sail_tiny_arm_sem nondet) term →
  VMPromising_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs ↔
  VMPromising_pf_final_state
    bbm_param (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply VMPromising_pf_equiv_from_Sail_impl.
Qed.

Lemma VMPromising_pf_final_state_equiv_unbounded_ret
    (bbm_param : BBM.param) {n} (term : terminationCondition n)
    initMs fs :
  VMPromising_final_state bbm_param (Ret tt) term initMs fs ↔
  VMPromising_pf_final_state bbm_param (Ret tt) term initMs fs.
Proof.
  apply VMPromising_pf_final_state_equiv_unbounded_from_event_shape_replay.
  - apply VMPromising_pf_tail_lift_exists_from_tail_lift.
    apply VMPromising_pf_tail_lift_ret.
  - apply VMPromising_pf_tail_event_shape_replay_ret.
Qed.
