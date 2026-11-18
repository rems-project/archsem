(******************************************************************************)
(* Completion constraints on the common emitter of adjacent TLBI promises     *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMStaleEpoch
  PromiseFirstSailVMSwapCompletion PromiseFirstSailVMNormalization PromiseFirstSailVMSwapSim.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapEpoch.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis
  Memory.t view UMPromising.view.

Lemma completing_epoch_bound bbm nondet {n} term (target : fin n) st p tlbi rc epoch :
  VMSwapCompletion.completes bbm nondet term st →
  p ∈ TState.prom_tlbi (PState.tstate target st) →
  VMSwapSim.mlookup (PState.events st) p = Some (Ev.Tlbi tlbi rc epoch) →
  TState.dsb_epoch (PState.tstate target st) ≤ epoch.
Proof.
  intros [final [fs [Hsteps Hfinal]]] Hp Hlookup. apply Nat.nlt_ge. intro Hlt.
  eapply (VMStaleEpoch.cannot_complete p tlbi rc epoch bbm target nondet term st final fs);
    [split; [split; assumption|exact Hlookup]|exact Hsteps|exact Hfinal].
Qed.

Lemma dsb_all_frame tid imem domain nxs vmax pp pp' value :
  Exec.elem_of_results (pp', value)
    (run_barrier tid imem (Barrier_DSB
      {| DxB_domain := domain; DxB_types := MBReqTypes_All; DxB_nXS := nxs |}) vmax pp) →
  PPState.mem pp' = PPState.mem pp ∧
  TState.prom_tlbi (PPState.state pp') = TState.prom_tlbi (PPState.state pp) ∧
  TState.dsb_epoch (PPState.state pp') = S (TState.dsb_epoch (PPState.state pp)).
Proof.
  destruct pp as [ts mem iis]. intro Hrun. unfold run_barrier in Hrun.
  VMViews.invert; subst; cbn in *; try discriminate; repeat split; reflexivity.
Qed.

(** Any promise from the current or an older epoch must be discharged before
    a full DSB in a continuation that reaches a validated final result. *)
Lemma completing_dsb_clears bbm nondet {n} term (target : fin n) st
    imem domain nxs vmax pp pp' value p tlbi rc epoch :
  VMSwapCompletion.completes bbm nondet term st →
  PState.tstate target st = PPState.state pp' → PState.events st = PPState.mem pp' →
  Exec.elem_of_results (pp', value)
    (run_barrier target imem (Barrier_DSB
      {| DxB_domain := domain; DxB_types := MBReqTypes_All; DxB_nXS := nxs |}) vmax pp) →
  VMSwapSim.mlookup (PPState.mem pp) p = Some (Ev.Tlbi tlbi rc epoch) →
  epoch ≤ TState.dsb_epoch (PPState.state pp) → p ∉ TState.prom_tlbi (PPState.state pp).
Proof.
  intros Hcomplete Hts Hmem Hrun Hlookup Hepoch Hp.
  destruct (dsb_all_frame _ _ _ _ _ _ _ _ Hrun) as [Hm [Hp' He]].
  assert (Hpost : TState.dsb_epoch (PState.tstate target st) ≤ epoch).
  { eapply completing_epoch_bound; [exact Hcomplete|rewrite Hts, Hp'; exact Hp|].
    rewrite Hmem, Hm. exact Hlookup. }
  rewrite Hts, He in Hpost. lia.
Qed.
End VMSwapEpoch.
