(******************************************************************************)
(* Reachable cache shape and translation replay                               *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From SailStdpp Require Import ConcurrencyInterfaceBuiltinsV2.
From SailTinyArm Require Import System.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstFreshBroadcast
  PromiseFirstSailCurrent PromiseFirstVMExecutionCurrent PromiseFirstSailRead
  PromiseFirstSailVMViews PromiseFirstSailVMCacheSim
  PromiseFirstSailVMCache PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheIndex
  PromiseFirstSailVMCacheIndexed PromiseFirstSailVMCacheLastTLBI
  PromiseFirstSailVMLookup PromiseFirstSailVMRootLookup
  PromiseFirstSailVMDirect PromiseFirstSailVMNormalization PromiseFirstSailNoFuel
  PromiseFirstSailVMInstructionReplay PromiseFirstSailVMCreatingReplay
  PromiseFirstSailVMWalkSail PromiseFirstSailVMWalkReplay PromiseFirstSailVMCreatingWalk
  PromiseFirstSailVMWalkStart PromiseFirstSailVMWalkLookup PromiseFirstSailVMWalkShape.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.


Module VMWalkShapeReachable.
Import VMPromising VMWalkShape.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

Definition state_shape (st : state) := ∀ tid, tok (PState.tstate tid st).

Lemma from_archState_shape ms st : PState.from_archState prom ms = Ok st → state_shape st.
Proof.
  unfold PState.from_archState.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn. injection 1 as <-.
  intro tid. unfold PState.tstate. cbn. eapply init_tok.
  exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid).
Qed.

Lemma promise_shape ev st st' : state_shape st → PState.promise prom ev st = Ok st' → state_shape st'.
Proof.
  intros Hok. unfold PState.promise.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn. injection 1 as <-.
  intro tid. unfold PState.tstate. cbn.
  pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid) as Hts. cbn in Hts.
  eapply emit_tok; [apply Hok|exact Hts].
Qed.

Lemma broadcast_shape (owner : fin n) imem base extra (states states' : vec TState.t n) :
  (∀ i, tok (states !!! i)) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states' →
  ∀ i, tok (states' !!! i).
Proof.
  intro Hpre. revert states'. induction extra as [|ev extra IH]; intros states' Hrun.
  - injection Hrun as <-. exact Hpre.
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid;
      [|discriminate].
    cbn [mbind result_bind] in Hrun. pose proof (IH mid eq_refl) as Hrest.
    intro i. pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun i) as Hlook.
    cbn in Hlook. destruct (decide (i = owner)).
    + injection Hlook as <-. apply Hrest.
    + eapply emit_tok; [apply Hrest|exact Hlook].
Qed.

Theorem run_tid_shape isem (tid : fin n) st st' :
  state_shape st → Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) → state_shape st'.
Proof.
  intros Hr Hrun.
  destruct (run_tid_broadcast_decompose prom isem tid st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  pose proof (instruction_shape n tid (PState.initmem st) isem
    (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init)
    (PPState.Make ts mem iis) () (Hr tid) Hinst) as Hts.
  intro i. unfold PState.tstate. cbn. eapply broadcast_shape; [|exact Hstates].
  intro j. destruct (decide (j = tid)) as [->|Hne].
  - rewrite vlookup_insert. exact Hts.
  - rewrite vlookup_insert_ne by (intro Heq; apply Hne; symmetry; exact Heq). apply Hr.
Qed.

Lemma run_step_shape isem term fuel st st' :
  state_shape st →
  Exec.elem_of_results (st', ()) (@CPState.run_step isem prom n term fuel st) → state_shape st'.
Proof.
  intros Hr Hrun. apply PromiseFirstCurrent.run_step_inv in Hrun
    as [(tid & ev & nst & _ & _ & Hpromise & ->)|(tid & _ & Hrun)].
  - eapply promise_shape; eassumption.
  - eapply run_tid_shape; eassumption.
Qed.

Lemma transition_shape (isem : iMon ()) (term : terminationCondition n) (use_pf : bool) fuel
    (st st' : state) :
  state_shape st → Exec.elem_of_results (st', None)
    ((if use_pf then CPState.run_transition_promise_first_uncached isem prom term fuel
      else CPState.run_transition isem prom term fuel) st) → state_shape st'.
Proof.
  intros Hr Hrun. destruct use_pf.
  - apply (PromiseFirstCurrent.run_transition_promise_first_none_inv (prom := prom)) in Hrun
      as (tid & ev & nst & _ & Hpromise & ->).
    eapply promise_shape; eassumption.
  - apply (PromiseFirstCurrent.run_transition_none_inv (prom := prom)) in Hrun as (next & Hstep & ->).
    eapply run_step_shape; eassumption.
Qed.

Theorem reachable_shape isem term initMs use_pf st :
  PromiseFirstReachable prom isem term initMs use_pf st → state_shape st.
Proof.
  induction 1 as [st Hinit|fuel st st' Hprev IH Hstep].
  - eapply from_archState_shape; eassumption.
  - eapply transition_shape; eassumption.
Qed.
End Machine.

Theorem prefix_shape bbm nondet {n} (term : terminationCondition n) initMs (tid : fin n) imem p mon :
  SailThreadPrefix (VMPromising bbm) nondet term initMs tid imem p mon → pok p.
Proof.
  induction 1 as [use_pf st Hreach _|imem p p' out k ret vpre _ Hr Hout|
    imem p choices k i _ IH|imem p _ Hr _].
  - exact (reachable_shape bbm _ _ _ _ _ Hreach tid).
  - eapply run_outcome_shape; eassumption.
  - exact IH.
  - exact Hr.
Qed.

Theorem cshape_invariant bbm nondet {n} (term : terminationCondition n) initMs :
  VMWalkReplay.ShInvariant bbm nondet term initMs (@CShape n).
Proof.
  split.
  - intros tid imem out p p' r _ Hshape Hrun. eapply run_outcome_shape; eassumption.
  - intros tid imem ts mem Hprefix. eapply prefix_shape; exact Hprefix.
Qed.

Theorem cshape_start {n} : VMWalkReplay.StartReplay (@CShape n).
Proof.
  intros tid imem mem ev Hpositive s p p' r q0 Hok Hroots Hshape Hex Hmem Hemit Hrun.
  eapply (VMWalkStart.step_start_w tid imem mem ev
    (VMWalkLookup.lookup_replay tid imem mem ev false Hpositive));
    [exact Hok|exact Hroots|apply cshape_shape, Hshape|exact Hex|exact Hmem|exact Hemit|exact Hrun].
Qed.

Theorem cshape_start_own {n} : VMCreatingWalk.StartOwnReplayW (@CShape n).
Proof.
  intros tid imem mem ev Hpositive Hown s p p' r q0 Hok Hroots Hshape Hex Hmem Hemit Hrun.
  eapply (VMWalkStart.step_start_own_w tid imem mem ev
    (VMWalkLookup.lookup_replay tid imem mem ev true Hpositive) Hown);
    [exact Hok|exact Hroots|apply cshape_shape, Hshape|exact Hex|exact Hmem|exact Hemit|exact Hrun].
Qed.

(** Translation replay and reachable cache shape are now proved. The final
    equivalence retains TLBI exchange, code immutability and search completeness. *)
Theorem final_state_equiv_shaped (bbm nondet : bool) {n : nat} (term : terminationCondition n)
    (initMs : archState n) (code : code_region) :
  VMNormalization.VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  (∀ initPs fuel returned fsig,
    PState.from_archState (VMPromising bbm) initMs = Ok initPs →
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) (VMPromising bbm) n)
        fuel term initMs initPs) →
    VMNormalization.VMNormalizationSearchesComplete bbm nondet term initMs (projT1 fsig)) →
  (∀ fuel fs (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf_uncached (VMPromising bbm) (sail_tiny_arm_sem nondet)
        fuel n term initMs →
    PromiseFirstSearchesCompleteFromInitial (VMPromising bbm) nondet term initMs fuel) →
  VMPromisingFinalStateEquiv bbm (sail_tiny_arm_sem nondet) term initMs.
Proof.
  apply (VMCreatingWalk.final_state_equiv_walks bbm nondet term initMs code (@CShape n)
    (cshape_invariant bbm nondet term initMs)); [apply cshape_start|apply cshape_start_own].
Qed.

End VMWalkShapeReachable.
