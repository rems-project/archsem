(******************************************************************************)
(* Discharge TLBI exchange in VM promise-first normalization                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstSailCurrent
  PromiseFirstSailNoFuel
  PromiseFirstSailVMSwapMachineBridge PromiseFirstSailVMSwapPair PromiseFirstSailVMSwapRemoveInit
  PromiseFirstSailVMNormalization PromiseFirstSailVMWalkShapeReachable.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapFinal.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.
Module VMSwapReplay.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Theorem simulation bbm nondet {n} (term : terminationCondition n) initMs code :
  VMNormalization.VMTLBISwapSimulation bbm nondet term initMs code.
Proof.
  exists (@VMSwapMachineBridge.related n). split.
  - intros init evs s a b e1 e2 Hsafe Hinit Htrace Hfirst Hsecond Horder.
    eapply VMSwapPair.raw_pair_related; [|exact Horder|exact Hfirst|exact Hsecond].
    eapply VMSwapRemoveInit.raw_trace_ok; [|exact Htrace].
    eapply VMSwapRemoveInit.from_archState_ok; exact Hinit.
  - split.
    + intros x x' ev y Hr Hrun. eapply VMSwapMachineBridge.raw_step_sim; eassumption.
    + split.
      * intros x x' y Hr Hrun. eapply VMSwapMachineBridge.mixed_sim; eassumption.
      * split.
        -- intros x x' Hr. symmetry. apply Hr.
        -- intros x x' fs Hr Hfinal. eapply VMSwapFinal.final_result; eassumption.
Qed.

Theorem replay bbm nondet {n} (term : terminationCondition n) initMs code :
  VMNormalization.VMTLBISwapReplay bbm nondet term initMs code.
Proof. apply VMNormalization.swap_simulation_replay, simulation. Qed.

(** Lookup replay, reachable cache shape, thread/handler simulation and TLBI
    exchange are discharged. The computational runner theorem retains the
    original code restriction and the two certification-completeness premises. *)
Theorem final_state_equiv (bbm nondet : bool) {n : nat} (term : terminationCondition n)
    (initMs : archState n) (code : code_region) :
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
Proof. apply VMWalkShapeReachable.final_state_equiv_shaped, replay. Qed.
End VMSwapReplay.
