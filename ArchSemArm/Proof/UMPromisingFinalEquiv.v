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
From ASCommon Require Import Common Exec FMon StateT.

From ArchSem Require Import GenPromising.
From ArchSemArm Require Import ArmInst UMPromising UMPromisingExec.
From ArchSemArm.Proof Require Import GenPromisingProof UMPromisingFacts.

#[local] Open Scope stdpp.

(** The model-specific promise-first obligation.  Replayability is local to
    individual write outcomes and is proved above; this remaining property is
    the global commutation principle saying that one direct thread step can be
    absorbed in front of the promise-first tail. *)
Definition UMPromising_pf_tail_lift {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPStateProof.run_tid_pf_tail_lift_property isem UMPromising term.

Definition UMPromising_pf_tail_lift_exists {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPStateProof.run_tid_pf_tail_lift_exists_property isem UMPromising term.

Lemma UMPromising_filter_promises_mono :
  CPStateProof.filter_promises_mono_property UMPromising.
Proof.
  intros n tid mem xs ys ev Hmono Hin.
  exact (Hmono ev Hin).
Qed.

Definition UMPromising_pf_tail_same_thread_promise_stable {n}
    (isem : iMon ()) (term : terminationCondition n) : Prop :=
  CPStateProof.run_tid_pf_tail_same_thread_promise_stable_property
    isem UMPromising term.

Definition UMPromising_pf_tail_event_shape {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPStateProof.run_tid_pf_tail_event_shape_property isem UMPromising term.

Definition UMPromising_pf_tail_event_shape_replay {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPStateProof.run_tid_pf_tail_event_shape_replay_property isem UMPromising term.

Definition UMPromising_pf_tail_event_shape_core {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPStateProof.run_tid_pf_tail_event_shape_core_property isem UMPromising term.

Definition UMPromising_pf_tail_at_most_one_promise {n}
    (isem : iMon ()) : Prop :=
  @CPStateProof.run_tid_at_most_one_promise_property isem UMPromising n.

Definition UMPromising_pf_tail_at_most_one_promise_prefix_stable {n}
    (isem : iMon ()) : Prop :=
  @CPStateProof.run_tid_at_most_one_promise_prefix_stable_property
    isem UMPromising n.

Lemma UMPromising_pf_tail_at_most_one_promise_from_Sail {n eo}
    nondet (smon : SI.iMon eo ()) :
  UMPromising_Sail_at_most_one_promise smon →
  UMPromising_pf_tail_at_most_one_promise
    (n:=n) (iMon_from_Sail nondet smon).
Proof.
  intros Hat_most st0 tid.
  apply UMPromising_iMon_from_Sail_at_most_one_promise.
  exact Hat_most.
Qed.

Lemma UMPromising_pf_tail_at_most_one_prefix_stable_from_Sail
    {n eo} nondet (smon : SI.iMon eo ()) :
  (∀ (tid : fin n) (initmem : memoryMap) (msg : Msg.t),
    UMPromising_Sail_prefix_promised_stable
      (tid : nat) initmem msg nondet smon) →
  UMPromising_pf_tail_at_most_one_promise_prefix_stable
    (n:=n) (iMon_from_Sail nondet smon).
Proof.
  intros Hstable st0 tid msg.
  apply UMPromising_iMon_from_Sail_prefix_promised_stable.
  apply Hstable.
Qed.

Local Lemma UMPromising_pf_tail_at_most_one_prefix_stable_from_read_code_impl
    {n} nondet code :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_at_most_one_promise_prefix_stable
    (n:=n) (sail_tiny_arm_sem nondet).
Proof.
  intros Hread.
  unfold sail_tiny_arm_sem.
  apply UMPromising_pf_tail_at_most_one_prefix_stable_from_Sail.
  intros tid initmem msg.
  apply UMPromising_Sail_prefix_promised_stable_fetch_and_execute_from_read_code
    with (code := code).
  apply Hread.
Qed.

Definition UMPromising_no_new_events {n} (isem : iMon ())
    (term : terminationCondition n) : Prop :=
  CPStateProof.run_tid_no_new_events_property isem UMPromising term.

Lemma UMPromising_pf_tail_lift_ret {n} (term : terminationCondition n) :
  UMPromising_pf_tail_lift (Ret tt) term.
Proof.
  unfold UMPromising_pf_tail_lift.
  apply CPStateProof.run_tid_pf_tail_lift_from_noop.
  - exact UMPromising_filter_promises_mono.
  - apply CPStateProof.run_tid_noop_ret.
    reflexivity.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_tail_lift {n}
    (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_pf_tail_lift isem term →
  UMPromising_pf_tail_lift_exists isem term.
Proof.
  unfold UMPromising_pf_tail_lift, UMPromising_pf_tail_lift_exists.
  apply CPStateProof.run_tid_pf_tail_lift_exists_from_tail_lift.
Qed.

Lemma UMPromising_pf_tail_lift_exists_ret {n}
    (term : terminationCondition n) :
  UMPromising_pf_tail_lift_exists (Ret tt) term.
Proof.
  apply UMPromising_pf_tail_lift_exists_from_tail_lift.
  apply UMPromising_pf_tail_lift_ret.
Qed.

Lemma UMPromising_pf_tail_event_shape_ret {n}
    (term : terminationCondition n) :
  UMPromising_pf_tail_event_shape (Ret tt) term.
Proof.
  unfold UMPromising_pf_tail_event_shape.
  apply CPStateProof.run_tid_pf_tail_event_shape_from_noop.
  apply CPStateProof.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma UMPromising_pf_tail_event_shape_core_ret {n}
    (term : terminationCondition n) :
  UMPromising_pf_tail_event_shape_core (Ret tt) term.
Proof.
  unfold UMPromising_pf_tail_event_shape_core.
  apply CPStateProof.run_tid_pf_tail_event_shape_core_from_noop.
  apply CPStateProof.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma UMPromising_pf_tail_event_shape_core_from_at_most_one_promise {n}
    (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_pf_tail_at_most_one_promise (n:=n) isem →
  UMPromising_pf_tail_event_shape_core isem term.
Proof.
  intro Hat_most.
  unfold UMPromising_pf_tail_at_most_one_promise,
    UMPromising_pf_tail_event_shape_core in *.
  eapply CPStateProof.run_tid_pf_tail_event_shape_core_from_at_most_one_promise.
  - exact (PromisingProof.replay_none_preserves_mem_explicit
      UMPromising UMPromising_replayable).
  - exact (PromisingProof.replay_promise_replay_one
      UMPromising UMPromising_replayable).
  - exact Hat_most.
Qed.

Lemma UMPromising_pf_tail_event_shape_replay_from_at_most_one_prefix
    {n} (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_pf_tail_at_most_one_promise (n:=n) isem →
  UMPromising_pf_tail_at_most_one_promise_prefix_stable (n:=n) isem →
  UMPromising_pf_tail_event_shape_replay isem term.
Proof.
  intros Hat_most Hprefix.
  unfold UMPromising_pf_tail_at_most_one_promise,
    UMPromising_pf_tail_at_most_one_promise_prefix_stable,
    UMPromising_pf_tail_event_shape_replay in *.
  eapply CPStateProof.run_tid_pf_tail_event_shape_replay_from_at_most_one_prefix.
  - exact (PromisingProof.replay_none_preserves_mem_explicit
      UMPromising UMPromising_replayable).
  - exact (PromisingProof.replay_promise_replay_one
      UMPromising UMPromising_replayable).
  - exact Hat_most.
  - exact Hprefix.
  - intros st tid_p tid msg.
    apply UMPromising_terminated_tid_promise.
Qed.

Local Lemma UMPromising_pf_tail_event_shape_replay_from_read_code_impl
    {n} nondet code (term : terminationCondition n) :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_event_shape_replay (sail_tiny_arm_sem nondet) term.
Proof.
  intro Hread.
  apply UMPromising_pf_tail_event_shape_replay_from_at_most_one_prefix.
  - unfold sail_tiny_arm_sem.
    apply UMPromising_pf_tail_at_most_one_promise_from_Sail.
    apply UMPromising_Sail_at_most_one_promise_fetch_and_execute.
  - apply
      (UMPromising_pf_tail_at_most_one_prefix_stable_from_read_code_impl
         (n:=n) nondet code).
    exact Hread.
Qed.

Lemma UMPromising_pf_tail_at_most_one_prefix_stable_from_read_code
    {n} nondet code :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_at_most_one_promise_prefix_stable
    (n:=n) (sail_tiny_arm_sem nondet).
Proof.
  apply UMPromising_pf_tail_at_most_one_prefix_stable_from_read_code_impl.
Qed.

Lemma UMPromising_pf_tail_event_shape_replay_from_read_code
    {n} nondet code (term : terminationCondition n) :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_event_shape_replay (sail_tiny_arm_sem nondet) term.
Proof.
  apply UMPromising_pf_tail_event_shape_replay_from_read_code_impl.
Qed.

Lemma UMPromising_pf_tail_event_shape_replay_ret {n}
    (term : terminationCondition n) :
  UMPromising_pf_tail_event_shape_replay (Ret tt) term.
Proof.
  unfold UMPromising_pf_tail_event_shape_replay.
  apply CPStateProof.run_tid_pf_tail_event_shape_replay_from_noop.
  apply CPStateProof.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma UMPromising_no_new_events_ret {n}
    (term : terminationCondition n) :
  UMPromising_no_new_events (Ret tt) term.
Proof.
  unfold UMPromising_no_new_events.
  apply CPStateProof.run_tid_no_new_events_from_noop.
  apply CPStateProof.run_tid_noop_ret.
  reflexivity.
Qed.

Lemma UMPromising_pf_tail_same_thread_promise_stable_ret {n}
    (term : terminationCondition n) :
  UMPromising_pf_tail_same_thread_promise_stable (Ret tt) term.
Proof.
  unfold UMPromising_pf_tail_same_thread_promise_stable.
  apply CPStateProof.run_tid_pf_tail_same_thread_promise_stable_ret.
  reflexivity.
Qed.

Lemma UMPromising_same_thread_promise_stable_property_from_tail_stable
    {n} (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_tail_stable (n:=n) isem →
  CPStateProof.run_tid_same_thread_promise_stable_property (n:=n)
    isem UMPromising.
Proof.
  intros Hstable st tid msg.
  destruct Hstable as [Hsame _].
  apply UMPromising_imon_future_promise_stable_promised_to_cmon.
  exact (Hsame tid (CPState.initmem st) msg).
Qed.

Lemma UMPromising_same_thread_promise_stable_property_from_Sail_same
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  UMPromising_Sail_same_promise_stable (n:=n) nondet smon →
  CPStateProof.run_tid_same_thread_promise_stable_property (n:=n)
    (iMon_from_Sail nondet smon) UMPromising.
Proof.
  intros Hstable st tid msg.
  destruct Hstable as [Hsame].
  apply UMPromising_imon_future_promise_stable_promised_to_cmon.
  apply UMPromising_iMon_from_Sail_promised_stable.
  exact (Hsame tid (CPState.initmem st) msg).
Qed.

Lemma UMPromising_promise_preserves_terminated_tid_property {n}
    (isem : iMon ()) (term : terminationCondition n) :
  CPStateProof.promise_preserves_terminated_tid_property (n:=n)
    UMPromising term.
Proof.
  intros st tid msg.
  apply UMPromising_terminated_tid_promise.
Qed.

Lemma UMPromising_pf_tail_same_thread_promise_stable_from_tail_stable
    {n} (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_tail_stable (n:=n) isem →
  UMPromising_pf_tail_same_thread_promise_stable isem term.
Proof.
  intro Hstable.
  unfold UMPromising_pf_tail_same_thread_promise_stable in *.
  apply CPStateProof.run_tid_pf_tail_same_thread_promise_stable_from_same_thread.
  apply (UMPromising_same_thread_promise_stable_property_from_tail_stable
    isem term).
  exact Hstable.
Qed.

Lemma UMPromising_pf_tail_same_thread_promise_stable_from_Sail_same
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  UMPromising_Sail_same_promise_stable (n:=n) nondet smon →
  UMPromising_pf_tail_same_thread_promise_stable
    (iMon_from_Sail nondet smon) term.
Proof.
  intro Hstable.
  unfold UMPromising_pf_tail_same_thread_promise_stable.
  apply CPStateProof.run_tid_pf_tail_same_thread_promise_stable_from_same_thread.
  apply (UMPromising_same_thread_promise_stable_property_from_Sail_same
    nondet smon term).
  exact Hstable.
Qed.

Lemma UMPromising_promise_preserves_any_terminated_tid_property {n}
    (isem : iMon ()) (term : terminationCondition n) :
  CPStateProof.promise_preserves_any_terminated_tid_property (n:=n)
    UMPromising term.
Proof.
  intros st tid_p tid msg.
  apply UMPromising_terminated_tid_promise.
Qed.

Lemma UMPromising_pf_tail_event_shape_from_core {n}
    (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_tail_stable (n:=n) isem →
  UMPromising_pf_tail_event_shape_core isem term →
  UMPromising_pf_tail_event_shape isem term.
Proof.
  intros Hstable Hevent_shape_core.
  unfold UMPromising_pf_tail_event_shape_core,
    UMPromising_pf_tail_event_shape in *.
  eapply CPStateProof.run_tid_pf_tail_event_shape_from_core.
  - apply
      (UMPromising_same_thread_promise_stable_property_from_tail_stable
         isem term).
    exact Hstable.
  - apply
      (UMPromising_promise_preserves_any_terminated_tid_property
         isem term).
  - exact Hevent_shape_core.
Qed.

Lemma UMPromising_pf_tail_event_shape_replay_from_event_shape {n}
    (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_pf_tail_event_shape isem term →
  UMPromising_pf_tail_event_shape_replay isem term.
Proof.
  unfold UMPromising_pf_tail_event_shape,
    UMPromising_pf_tail_event_shape_replay in *.
  eapply CPStateProof.run_tid_pf_tail_event_shape_replay_from_event_shape.
  - exact
      (PromisingProof.replay_none_preserves_mem_explicit
         UMPromising UMPromising_replayable).
  - exact
      (PromisingProof.replay_promise_replay_one
         UMPromising UMPromising_replayable).
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_event_shape {n}
    (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_event_shape isem term →
  UMPromising_pf_tail_lift_exists isem term.
Proof.
  intros Hlift Hevent_shape.
  unfold UMPromising_pf_tail_lift_exists,
    UMPromising_pf_tail_event_shape in *.
  eapply CPStateProof.run_tid_pf_tail_lift_exists_from_event_shape.
  - exact
      (PromisingProof.replay_none_preserves_mem_explicit
         UMPromising UMPromising_replayable).
  - exact
      (PromisingProof.replay_promise_replay_one
         UMPromising UMPromising_replayable).
  - exact Hlift.
  - exact Hevent_shape.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_event_shape_replay {n}
    (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_event_shape_replay isem term →
  UMPromising_pf_tail_lift_exists isem term.
Proof.
  intros Hlift Hevent_shape.
  unfold UMPromising_pf_tail_lift_exists,
    UMPromising_pf_tail_event_shape_replay in *.
  eapply CPStateProof.run_tid_pf_tail_lift_exists_from_event_shape_replay.
  - exact
      (PromisingProof.replay_none_preserves_mem_explicit
         UMPromising UMPromising_replayable).
  - exact
      (PromisingProof.replay_promise_replay_one
         UMPromising UMPromising_replayable).
  - exact Hlift.
  - exact Hevent_shape.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_tail_lift_event_shape {n}
    (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_tail_stable (n:=n) isem →
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_event_shape isem term →
  UMPromising_pf_tail_lift_exists isem term.
Proof.
  intros Hstable Hlift Hevent_shape.
  unfold UMPromising_pf_tail_event_shape,
    UMPromising_pf_tail_lift_exists in *.
  eapply CPStateProof.run_tid_pf_tail_lift_exists_from_event_shape_tail_lift.
  - exact
      (PromisingProof.replay_none_preserves_mem_explicit
         UMPromising UMPromising_replayable).
  - exact
      (PromisingProof.replay_promise_replay_one
         UMPromising UMPromising_replayable).
  - apply
      (UMPromising_same_thread_promise_stable_property_from_tail_stable
         isem term).
    exact Hstable.
  - apply (UMPromising_promise_preserves_terminated_tid_property isem term).
  - exact Hlift.
  - exact Hevent_shape.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_tail_lift_core {n}
    (isem : iMon ()) (term : terminationCondition n) :
  UMPromising_tail_stable (n:=n) isem →
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_event_shape_core isem term →
  UMPromising_pf_tail_lift_exists isem term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  unfold UMPromising_pf_tail_event_shape_core,
    UMPromising_pf_tail_lift_exists in *.
  eapply CPStateProof.run_tid_pf_tail_lift_exists_from_event_shape_core_tail_lift.
  - exact
      (PromisingProof.replay_none_preserves_mem_explicit
         UMPromising UMPromising_replayable).
  - exact
      (PromisingProof.replay_promise_replay_one
         UMPromising UMPromising_replayable).
  - apply
      (UMPromising_same_thread_promise_stable_property_from_tail_stable
         isem term).
    exact Hstable.
  - apply
      (UMPromising_promise_preserves_any_terminated_tid_property isem term).
  - exact Hlift.
  - exact Hevent_shape_core.
Qed.

Lemma UMPromising_promise_first_tail_compatible {n} (isem : iMon ())
    (term : terminationCondition n) :
  UMPromising_pf_tail_lift isem term →
  CPStateProof.PromiseFirstTailCompatible isem UMPromising term.
Proof.
  intro Hlift.
  constructor.
  - apply UMPromising_replayable.
  - exact Hlift.
Qed.

Lemma UMPromising_promise_first_compatible {n} (isem : iMon ())
    (term : terminationCondition n) :
  UMPromising_pf_tail_lift isem term →
  CPStateProof.PromiseFirstCompatible isem UMPromising term.
Proof.
  intro Hlift.
  apply CPStateProof.promise_first_compatible_from_tail.
  apply UMPromising_promise_first_tail_compatible.
  exact Hlift.
Qed.

Lemma UMPromising_final_to_pf {n} (isem : iMon ()) fuel fuel_pf
    (term : terminationCondition n) initMs fs pt :
  UMPromising_pf_tail_lift isem term →
  (S fuel ≤ fuel_pf)%nat →
  archModel.Res.FinalState fs pt ∈
    UMPromising_exe isem fuel n term initMs →
  ∃ pt_pf,
    archModel.Res.FinalState fs pt_pf ∈
      UMPromising_pf isem fuel_pf n term initMs.
Proof.
  intros Hlift Hfuel Hdirect.
  eapply Promising_to_Modelc_final_to_pf_with_run_tid_pf_tail_lift.
  - exact UMPromising_filter_promises_mono.
  - exact Hlift.
  - exact Hfuel.
  - exact Hdirect.
Qed.

Lemma UMPromising_final_to_pf_exists {n} (isem : iMon ()) fuel
    (term : terminationCondition n) initMs fs pt :
  UMPromising_pf_tail_lift_exists isem term →
  archModel.Res.FinalState fs pt ∈
    UMPromising_exe isem fuel n term initMs →
  ∃ fuel_pf pt_pf,
    archModel.Res.FinalState fs pt_pf ∈
      UMPromising_pf isem fuel_pf n term initMs.
Proof.
  intros Hlift Hdirect.
  eapply Promising_to_Modelc_final_to_pf_exists_with_run_tid_pf_tail_lift.
  - exact UMPromising_filter_promises_mono.
  - exact Hlift.
  - exact Hdirect.
Qed.

Lemma UMPromising_pf_final_equiv {n} (isem : iMon ()) fuel fuel_pf
    (term : terminationCondition n) initMs fs pt :
  UMPromising_pf_tail_lift isem term →
  (S fuel ≤ fuel_pf)%nat →
  (archModel.Res.FinalState fs pt ∈
     UMPromising_exe isem fuel n term initMs →
   ∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       UMPromising_pf isem fuel_pf n term initMs) ∧
  (archModel.Res.FinalState fs pt ∈
     UMPromising_pf isem fuel_pf n term initMs →
   ∃ fuel_direct pt_direct,
     (fuel ≤ fuel_direct)%nat ∧
     archModel.Res.FinalState fs pt_direct ∈
       UMPromising_exe isem fuel_direct n term initMs).
Proof.
  intros Hlift Hfuel.
  eapply Promising_to_Modelc_pf_final_equiv_with_run_tid_pf_tail_lift.
  - exact UMPromising_filter_promises_mono.
  - exact Hlift.
  - exact Hfuel.
Qed.

Lemma UMPromising_pf_final_state_equiv {n} (isem : iMon ()) fuel fuel_pf
    (term : terminationCondition n) initMs fs :
  UMPromising_pf_tail_lift isem term →
  (S fuel ≤ fuel_pf)%nat →
  ((∃ pt,
     archModel.Res.FinalState fs pt ∈
       UMPromising_exe isem fuel n term initMs) →
   ∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       UMPromising_pf isem fuel_pf n term initMs) ∧
  ((∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       UMPromising_pf isem fuel_pf n term initMs) →
   ∃ fuel_direct pt_direct,
     (fuel ≤ fuel_direct)%nat ∧
     archModel.Res.FinalState fs pt_direct ∈
       UMPromising_exe isem fuel_direct n term initMs).
Proof.
  intros Hlift Hfuel.
  eapply Promising_to_Modelc_pf_final_state_equiv_with_run_tid_pf_tail_lift.
  - exact UMPromising_filter_promises_mono.
  - exact Hlift.
  - exact Hfuel.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded {n} (isem : iMon ())
    (term : terminationCondition n) initMs fs :
  UMPromising_pf_tail_lift isem term →
  UMPromising_final_state isem term initMs fs ↔
  UMPromising_pf_final_state isem term initMs fs.
Proof.
  intro Hlift.
  eapply
    Promising_to_Modelc_pf_final_state_equiv_unbounded_with_run_tid_pf_tail_lift.
  - exact UMPromising_filter_promises_mono.
  - exact Hlift.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_exists {n}
    (isem : iMon ()) (term : terminationCondition n) initMs fs :
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_final_state isem term initMs fs ↔
  UMPromising_pf_final_state isem term initMs fs.
Proof.
  intro Hlift.
  eapply
    Promising_to_Modelc_pf_final_state_equiv_unbounded_with_run_tid_pf_tail_lift_exists.
  - exact UMPromising_filter_promises_mono.
  - exact Hlift.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_from_tail_lift_event_shape {n}
    (isem : iMon ()) (term : terminationCondition n) initMs fs :
  UMPromising_tail_stable (n:=n) isem →
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_event_shape isem term →
  UMPromising_final_state isem term initMs fs ↔
  UMPromising_pf_final_state isem term initMs fs.
Proof.
  intros Hstable Hlift Hevent_shape.
  apply UMPromising_pf_final_state_equiv_unbounded_exists.
  eapply UMPromising_pf_tail_lift_exists_from_tail_lift_event_shape; eauto.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_from_tail_lift_core {n}
    (isem : iMon ()) (term : terminationCondition n) initMs fs :
  UMPromising_tail_stable (n:=n) isem →
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_event_shape_core isem term →
  UMPromising_final_state isem term initMs fs ↔
  UMPromising_pf_final_state isem term initMs fs.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  apply UMPromising_pf_final_state_equiv_unbounded_exists.
  eapply UMPromising_pf_tail_lift_exists_from_tail_lift_core; eauto.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_from_at_most_one_promise
    {n} (isem : iMon ()) (term : terminationCondition n) initMs fs :
  UMPromising_tail_stable (n:=n) isem →
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_at_most_one_promise (n:=n) isem →
  UMPromising_final_state isem term initMs fs ↔
  UMPromising_pf_final_state isem term initMs fs.
Proof.
  intros Hstable Hlift Hat_most.
  eapply UMPromising_pf_final_state_equiv_unbounded_from_tail_lift_core.
  - exact Hstable.
  - exact Hlift.
  - apply UMPromising_pf_tail_event_shape_core_from_at_most_one_promise.
    exact Hat_most.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_from_Sail_at_most_one_promise
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) initMs fs :
  UMPromising_Sail_tail_stable (n:=n) nondet smon →
  UMPromising_pf_tail_lift_exists
    (iMon_from_Sail nondet smon) term →
  UMPromising_Sail_at_most_one_promise smon →
  UMPromising_final_state (iMon_from_Sail nondet smon) term initMs fs ↔
  UMPromising_pf_final_state
    (iMon_from_Sail nondet smon) term initMs fs.
Proof.
  intros Hstable Hlift Hat_most.
  eapply UMPromising_pf_final_state_equiv_unbounded_from_at_most_one_promise.
  - apply UMPromising_tail_stable_from_Sail.
    exact Hstable.
  - exact Hlift.
  - apply UMPromising_pf_tail_at_most_one_promise_from_Sail.
    exact Hat_most.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_from_event_shape {n}
    (isem : iMon ()) (term : terminationCondition n) initMs fs :
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_event_shape isem term →
  UMPromising_final_state isem term initMs fs ↔
  UMPromising_pf_final_state isem term initMs fs.
Proof.
  intros Hlift Hevent_shape.
  apply UMPromising_pf_final_state_equiv_unbounded_exists.
  eapply UMPromising_pf_tail_lift_exists_from_event_shape; eauto.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_from_event_shape_replay
    {n} (isem : iMon ()) (term : terminationCondition n) initMs fs :
  UMPromising_pf_tail_lift_exists isem term →
  UMPromising_pf_tail_event_shape_replay isem term →
  UMPromising_final_state isem term initMs fs ↔
  UMPromising_pf_final_state isem term initMs fs.
Proof.
  intros Hlift Hevent_shape.
  eapply
    Promising_to_Modelc_pf_final_state_equiv_unbounded_from_event_shape_replay.
  - exact UMPromising_replayable.
  - exact UMPromising_filter_promises_mono.
  - exact Hlift.
  - exact Hevent_shape.
Qed.

Record UMPromising_Sail_pf_compatible {n eo} nondet
    (smon : SI.iMon eo ()) (term : terminationCondition n) : Prop := {
    UMPromising_Sail_pf_tail_lift :
      UMPromising_pf_tail_lift_exists
        (iMon_from_Sail nondet smon) term;
    UMPromising_Sail_pf_event_shape_replay :
      UMPromising_pf_tail_event_shape_replay
        (iMon_from_Sail nondet smon) term;
  }.

Lemma UMPromising_Sail_pf_compatible_from_tail_lift_core
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  UMPromising_Sail_tail_stable (n:=n) nondet smon →
  UMPromising_pf_tail_lift_exists
    (iMon_from_Sail nondet smon) term →
  UMPromising_pf_tail_event_shape_core
    (iMon_from_Sail nondet smon) term →
  UMPromising_Sail_pf_compatible nondet smon term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  pose proof (UMPromising_tail_stable_from_Sail nondet smon Hstable)
    as Htail_stable.
  constructor.
  - exact Hlift.
  - apply UMPromising_pf_tail_event_shape_replay_from_event_shape.
    eapply UMPromising_pf_tail_event_shape_from_core.
    + exact Htail_stable.
    + exact Hevent_shape_core.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_Sail_same_tail_lift_core
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  UMPromising_Sail_same_promise_stable (n:=n) nondet smon →
  UMPromising_pf_tail_lift_exists
    (iMon_from_Sail nondet smon) term →
  UMPromising_pf_tail_event_shape_core
    (iMon_from_Sail nondet smon) term →
  UMPromising_pf_tail_lift_exists (iMon_from_Sail nondet smon) term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  unfold UMPromising_pf_tail_event_shape_core,
    UMPromising_pf_tail_lift_exists in *.
  eapply CPStateProof.run_tid_pf_tail_lift_exists_from_event_shape_core_tail_lift.
  - exact
      (PromisingProof.replay_none_preserves_mem_explicit
         UMPromising UMPromising_replayable).
  - exact
      (PromisingProof.replay_promise_replay_one
         UMPromising UMPromising_replayable).
  - apply
      (UMPromising_same_thread_promise_stable_property_from_Sail_same
         nondet smon term).
    exact Hstable.
  - apply
      (UMPromising_promise_preserves_any_terminated_tid_property
         (iMon_from_Sail nondet smon) term).
  - exact Hlift.
  - exact Hevent_shape_core.
Qed.

Lemma UMPromising_Sail_pf_compatible_from_same_tail_lift_core
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  UMPromising_Sail_same_promise_stable (n:=n) nondet smon →
  UMPromising_pf_tail_lift_exists
    (iMon_from_Sail nondet smon) term →
  UMPromising_pf_tail_event_shape_core
    (iMon_from_Sail nondet smon) term →
  UMPromising_Sail_pf_compatible nondet smon term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  pose proof
    (UMPromising_same_thread_promise_stable_property_from_Sail_same
       nondet smon term Hstable) as Hsame_thread.
  pose proof
    (UMPromising_promise_preserves_any_terminated_tid_property
       (iMon_from_Sail nondet smon) term) as Hany_terminated.
  constructor.
  - exact Hlift.
  - apply UMPromising_pf_tail_event_shape_replay_from_event_shape.
    unfold UMPromising_pf_tail_event_shape,
      UMPromising_pf_tail_event_shape_core in *.
    eapply CPStateProof.run_tid_pf_tail_event_shape_from_core; eauto.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_Sail_compatible
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) :
  UMPromising_Sail_pf_compatible nondet smon term →
  UMPromising_pf_tail_lift_exists (iMon_from_Sail nondet smon) term.
Proof.
  intro Hcompat.
  destruct Hcompat as [Hlift Hevent_shape].
  eapply UMPromising_pf_tail_lift_exists_from_event_shape_replay; eauto.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_from_Sail_compatible
    {n eo} nondet (smon : SI.iMon eo ())
    (term : terminationCondition n) initMs fs :
  UMPromising_Sail_pf_compatible nondet smon term →
  UMPromising_final_state (iMon_from_Sail nondet smon) term initMs fs ↔
  UMPromising_pf_final_state
    (iMon_from_Sail nondet smon) term initMs fs.
Proof.
  intro Hcompat.
  destruct Hcompat as [Hlift Hevent_shape].
  eapply UMPromising_pf_final_state_equiv_unbounded_from_event_shape_replay;
    eauto.
Qed.

Definition UMPromising_pf_compatible {n} nondet
    (term : terminationCondition n) : Prop :=
  UMPromising_Sail_pf_compatible nondet
    (System.fetch_and_execute ()) term.

Local Lemma UMPromising_pf_compatible_from_tail_lift_core_impl
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_event_shape_core
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  intros Hstable Hlift Hevent_shape_core.
  unfold UMPromising_pf_compatible, sail_tiny_arm_sem in *.
  eapply UMPromising_Sail_pf_compatible_from_tail_lift_core; eauto.
Qed.

Local Lemma UMPromising_pf_compatible_from_Sail_impl
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  intros Hstable Hlift.
  unfold UMPromising_pf_compatible, sail_tiny_arm_sem in *.
  constructor.
  - exact Hlift.
  - apply UMPromising_pf_tail_event_shape_replay_from_event_shape.
    eapply UMPromising_pf_tail_event_shape_from_core.
    + apply UMPromising_tail_stable_from_Sail.
      exact Hstable.
    + apply UMPromising_pf_tail_event_shape_core_from_at_most_one_promise.
      unfold sail_tiny_arm_sem.
      apply UMPromising_pf_tail_at_most_one_promise_from_Sail.
      apply UMPromising_Sail_at_most_one_promise_fetch_and_execute.
Qed.

Local Lemma UMPromising_pf_compatible_from_Sail_tail_lift_impl
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  intros Hstable Hlift.
  eapply UMPromising_pf_compatible_from_tail_lift_core_impl.
  - exact Hstable.
  - exact Hlift.
  - apply UMPromising_pf_tail_event_shape_core_from_at_most_one_promise.
    unfold sail_tiny_arm_sem.
    apply UMPromising_pf_tail_at_most_one_promise_from_Sail.
    apply UMPromising_Sail_at_most_one_promise_fetch_and_execute.
Qed.

Local Lemma UMPromising_pf_compatible_from_same_tail_lift_impl
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_same_promise_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  intros Hstable Hlift.
  unfold UMPromising_pf_compatible, sail_tiny_arm_sem in *.
  eapply UMPromising_Sail_pf_compatible_from_same_tail_lift_core.
  - exact Hstable.
  - exact Hlift.
  - apply UMPromising_pf_tail_event_shape_core_from_at_most_one_promise.
    unfold sail_tiny_arm_sem.
    apply UMPromising_pf_tail_at_most_one_promise_from_Sail.
    apply UMPromising_Sail_at_most_one_promise_fetch_and_execute.
Qed.

Local Lemma UMPromising_pf_compatible_from_read_code_impl
    {n} nondet code (term : terminationCondition n) :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  intros Hread Hlift.
  unfold UMPromising_pf_compatible, sail_tiny_arm_sem in *.
  constructor.
  - exact Hlift.
  - eapply UMPromising_pf_tail_event_shape_replay_from_read_code_impl.
    exact Hread.
Qed.

Lemma UMPromising_pf_compatible_from_tail_lift_core
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_event_shape_core
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  apply UMPromising_pf_compatible_from_tail_lift_core_impl.
Qed.

Lemma UMPromising_pf_compatible_from_Sail
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  apply UMPromising_pf_compatible_from_Sail_impl.
Qed.

Lemma UMPromising_pf_compatible_from_Sail_tail_lift
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  apply UMPromising_pf_compatible_from_Sail_tail_lift_impl.
Qed.

Lemma UMPromising_pf_compatible_from_same_tail_lift
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_same_promise_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  apply UMPromising_pf_compatible_from_same_tail_lift_impl.
Qed.

Lemma UMPromising_pf_compatible_from_read_code_and_tail_lift
    {n} nondet code (term : terminationCondition n) :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_compatible nondet term.
Proof.
  intros Hread Hlift.
  eapply UMPromising_pf_compatible_from_read_code_impl.
  - exact Hread.
  - exact Hlift.
Qed.

Local Lemma UMPromising_pf_tail_lift_exists_from_compatible_impl
    {n} nondet (term : terminationCondition n) :
  UMPromising_pf_compatible nondet term →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term.
Proof.
  unfold UMPromising_pf_compatible, sail_tiny_arm_sem.
  apply UMPromising_pf_tail_lift_exists_from_Sail_compatible.
Qed.

Local Lemma UMPromising_pf_tail_lift_exists_from_Sail_impl
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term.
Proof.
  intros Hstable Hlift.
  apply UMPromising_pf_tail_lift_exists_from_compatible_impl.
  eapply UMPromising_pf_compatible_from_Sail_impl; eauto.
Qed.

Local Lemma UMPromising_pf_tail_lift_exists_from_read_code_impl
    {n} nondet code (term : terminationCondition n) :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term.
Proof.
  intros Hread Hlift.
  apply UMPromising_pf_tail_lift_exists_from_compatible_impl.
  eapply UMPromising_pf_compatible_from_read_code_impl; eauto.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_compatible
    {n} nondet (term : terminationCondition n) :
  UMPromising_pf_compatible nondet term →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term.
Proof.
  apply UMPromising_pf_tail_lift_exists_from_compatible_impl.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_Sail
    {n} nondet (term : terminationCondition n) :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term.
Proof.
  apply UMPromising_pf_tail_lift_exists_from_Sail_impl.
Qed.

Lemma UMPromising_pf_tail_lift_exists_from_read_code_and_tail_lift
    {n} nondet code (term : terminationCondition n) :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term.
Proof.
  intros _ Hlift.
  exact Hlift.
Qed.

Local Lemma UMPromising_pf_equiv_impl
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_pf_compatible nondet term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intro Hcompat.
  apply
    (UMPromising_pf_final_state_equiv_unbounded_from_Sail_compatible
       nondet (System.fetch_and_execute ()) term).
  exact Hcompat.
Qed.

Local Lemma UMPromising_pf_equiv_from_obligations_impl
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_event_shape_replay (sail_tiny_arm_sem nondet) term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hlift Hevent_shape.
  eapply UMPromising_pf_final_state_equiv_unbounded_from_event_shape_replay;
    eauto.
Qed.

Local Lemma UMPromising_pf_equiv_from_read_code_impl
    {n} nondet code (term : terminationCondition n) initMs fs :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hread Hlift.
  apply UMPromising_pf_equiv_impl.
  eapply UMPromising_pf_compatible_from_read_code_impl; eauto.
Qed.

Local Lemma UMPromising_pf_equiv_from_at_most_one_impl
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_tail_stable (n:=n) (sail_tiny_arm_sem nondet) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_at_most_one_promise
    (n:=n) (sail_tiny_arm_sem nondet) →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hstable Hlift Hat_most.
  eapply UMPromising_pf_final_state_equiv_unbounded_from_at_most_one_promise;
    eauto.
Qed.

Local Lemma UMPromising_pf_equiv_from_Sail_at_most_one_impl
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_Sail_at_most_one_promise (System.fetch_and_execute ()) →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hstable Hlift Hat_most.
  unfold sail_tiny_arm_sem in *.
  eapply
    UMPromising_pf_final_state_equiv_unbounded_from_Sail_at_most_one_promise;
    eauto.
Qed.

Local Lemma UMPromising_pf_equiv_from_Sail_impl
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hstable Hlift.
  apply UMPromising_pf_final_state_equiv_unbounded_exists.
  eapply UMPromising_pf_tail_lift_exists_from_Sail_impl.
  - exact Hstable.
  - exact Hlift.
Qed.

Lemma UMPromising_pf_equiv
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_pf_compatible nondet term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply UMPromising_pf_equiv_impl.
Qed.

Lemma UMPromising_pf_equiv_from_tail_lift
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply UMPromising_pf_final_state_equiv_unbounded_exists.
Qed.

Lemma UMPromising_pf_equiv_from_obligations
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_event_shape_replay (sail_tiny_arm_sem nondet) term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply UMPromising_pf_equiv_from_obligations_impl.
Qed.

Lemma UMPromising_pf_equiv_from_read_code_and_tail_lift
    {n} nondet code (term : terminationCondition n) initMs fs :
  (∀ tid initmem msg,
    UMPromising_read_code_stability tid initmem code msg) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  intros Hread Hlift.
  apply UMPromising_pf_equiv_impl.
  eapply UMPromising_pf_compatible_from_read_code_impl.
  - exact Hread.
  - exact Hlift.
Qed.

Lemma UMPromising_pf_equiv_from_at_most_one
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_tail_stable (n:=n) (sail_tiny_arm_sem nondet) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_pf_tail_at_most_one_promise
    (n:=n) (sail_tiny_arm_sem nondet) →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply UMPromising_pf_equiv_from_at_most_one_impl.
Qed.

Lemma UMPromising_pf_equiv_from_Sail_at_most_one
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists (sail_tiny_arm_sem nondet) term →
  UMPromising_Sail_at_most_one_promise (System.fetch_and_execute ()) →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply UMPromising_pf_equiv_from_Sail_at_most_one_impl.
Qed.

Lemma UMPromising_pf_equiv_from_Sail
    {n} nondet (term : terminationCondition n) initMs fs :
  UMPromising_Sail_tail_stable
    (n:=n) nondet (System.fetch_and_execute ()) →
  UMPromising_pf_tail_lift_exists
    (sail_tiny_arm_sem nondet) term →
  UMPromising_final_state (sail_tiny_arm_sem nondet) term initMs fs ↔
  UMPromising_pf_final_state (sail_tiny_arm_sem nondet) term initMs fs.
Proof.
  apply UMPromising_pf_equiv_from_Sail_impl.
Qed.

Lemma UMPromising_pf_final_state_equiv_unbounded_ret {n}
    (term : terminationCondition n) initMs fs :
  UMPromising_final_state (Ret tt) term initMs fs ↔
  UMPromising_pf_final_state (Ret tt) term initMs fs.
Proof.
  apply UMPromising_pf_final_state_equiv_unbounded_from_event_shape_replay.
  - apply UMPromising_pf_tail_lift_exists_from_tail_lift.
    apply UMPromising_pf_tail_lift_ret.
  - apply UMPromising_pf_tail_event_shape_replay_ret.
Qed.
