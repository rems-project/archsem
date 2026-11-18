(******************************************************************************)
(* Exclusion invariant through VM outcomes and instruction interpretation    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstVMExecutionCurrent PromiseFirstSailVMViews
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveThread
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMSwapRemoveStampRun PromiseFirstSailVMSwapRemoveTLBI
  PromiseFirstSailVMSwapRemoveStore PromiseFirstSailVMSwapRemoveTranslation PromiseFirstSailVMSwapRemoveStampHandlers.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveInvariant.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Definition ok p pp := VMViews.ok pp ∧ VMSwapRemoveTLBI.inv p pp.

#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_both VMViews.mem_set_both VMViews.iis_set_both : pp_remove_inv.
Ltac simpl_pp := unfold VMSwapRemoveThread.ok, VMSwapRemoveStampMemory.ok, setv in *;
  autorewrite with pp_remove_inv in *; cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Section Removed.
Context (n : nat) (tid : fin n) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Hypothesis Hrc : fin_to_nat tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation ev := (Ev.Tlbi tlbi rc epoch).

Lemma run_outcome_exclusion l out pp pp' value :
  PPState.mem pp = l ++ ev :: r → ok p pp →
  Exec.elem_of_results (pp', value) (run_outcome n tid imem out pp) → VMSwapRemoveTLBI.inv p pp'.
Proof using Hrc.
  intros Hmem [Hbound [Hviews Hstamps]] H. funelim (run_outcome n tid imem out pp).
  all: rewrite <- Heqcall in H.
  all: VMViews.invert; subst.
  all: try solve [split; assumption].
  all: try solve [eapply VMSwapRemoveStore.write_mem_inv; [exact Hmem|split; assumption|eassumption]].
  all: try solve [eapply VMSwapRemoveTranslation.run_trans_start_inv;
    [exact Hmem|exact Hbound|split; assumption|eassumption]].
  all: try solve [eapply VMSwapRemoveStampMemory.read_mem_explicit_both;
    [exact Hmem|exact Hviews|exact Hstamps|eassumption]].
  all: try solve [eapply VMSwapRemoveTLBI.run_tlbi_inv;
    [lia|rewrite Hmem, length_app; cbn; lia|split; assumption|eassumption]].
  all: try solve [split;
    [eapply VMSwapRemoveThread.run_reg_write_ok; [exact Hrc|exact Hmem|exact Hviews|eassumption]
    |eapply VMSwapRemoveStampHandlers.run_reg_write_ok; eassumption]].
  all: try solve [split;
    [eapply VMSwapRemoveThread.run_barrier_ok; [exact Hrc|exact Hmem|exact Hviews|eassumption]
    |eapply VMSwapRemoveStampHandlers.run_barrier_ok; eassumption]].
  all: try solve [split;
    [eapply VMSwapRemoveThread.run_cse_ok; [exact Hrc|exact Hmem|exact Hviews|eassumption]
    |eapply VMSwapRemoveStampHandlers.run_cse_ok; eassumption]].
  all: try solve [split;
    [eapply VMSwapRemoveThread.run_take_exception_ok; [exact Hrc|exact Hmem|exact Hviews|eassumption]
    |eapply VMSwapRemoveStampHandlers.run_take_exception_ok; eassumption]].
  all: try solve [split;
    [eapply VMSwapRemoveThread.read_pte_ok; eassumption
    |eapply VMSwapRemoveStampHandlers.read_pte_ok; eassumption]].
  all: try solve [match goal with Hread : Exec.elem_of_results (?after, ?value) (run_reg_read ?reg ?racc ?before) |- _ =>
    let ts := constr:(before.1) in let iis := constr:(before.2) in
    destruct after as [ts' iis']; split; simpl_pp;
    [eapply VMSwapRemoveThread.run_reg_read_ok; [lia|exact Hviews|exact Hread]
    |eapply (VMSwapRemoveStampHandlers.run_reg_read_ok p reg racc (ts, iis) (ts', iis') value);
      [apply Hstamps|apply Hstamps|exact Hread]] end].
  all: try solve [match goal with Htrans : Exec.elem_of_results (?after, _) (run_trans_end ?trans ?before) |- _ =>
    split; simpl_pp;
    [eapply (VMSwapRemoveThread.run_trans_end_ok p trans before after); [lia|exact Hviews|exact Htrans]
    |eapply (VMSwapRemoveStampHandlers.run_trans_end_ok p trans before after); [apply Hstamps|apply Hstamps|exact Htrans]] end].
  all: unfold VMSwapRemoveTLBI.inv; simpl_pp.
  all: pose proof Hviews as [[Hts Hcache] Hiis]; pose proof Hstamps as [Hsts Hsiis].
  all: split.
  all: try solve [match type of Hviews with VMSwapRemoveThread.local_ok _ ?ts ?iis =>
    eapply (VMSwapRemoveThread.frame p ts _ iis) end;
    [reflexivity|reflexivity| |exact Hiis|exact Hviews];
    apply VMSwapRemoveViews.update_vspec; [apply VMSwapRemoveState.allowed_max|apply Hiis|exact Hts]].
  all: split; [apply VMSwapRemoveStamps.update_vspec, Hsts|exact Hsiis].
Qed.

Lemma run_outcome_ok l out pp pp' value : PPState.mem pp = l ++ ev :: r → ok p pp →
  Exec.elem_of_results (pp', value) (run_outcome n tid imem out pp) → ok p pp'.
Proof using Hrc.
  intros Hmem Hok Hrun. split.
  - eapply VMViews.run_outcome_ok; [apply Hok|exact Hrun].
  - eapply run_outcome_exclusion; eassumption.
Qed.

Theorem instruction_ok l {A} (mon : iMon A) pp pp' value : PPState.mem pp = l ++ ev :: r → ok p pp →
  Exec.elem_of_results (pp', value) (cinterp (run_outcome' n tid imem) mon pp) →
  ok p pp' ∧ ∃ extra, PPState.mem pp' = extra ++ PPState.mem pp.
Proof using Hrc.
  revert l pp pp' value. induction mon as [a|call k IH]; intros l pp pp' value Hmem Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. split; [exact Hok|exists []; reflexivity].
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[ret pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (VMViews.outcome_memory_growth n tid imem out pp mid (ret, pre) Hout) as [extra Hextra].
      assert (Hmidmem : PPState.mem mid = (extra ++ l) ++ ev :: r) by
        (rewrite Hextra, Hmem, app_assoc; reflexivity).
      destruct (IH ret (extra ++ l) mid pp' value Hmidmem (run_outcome_ok l out pp mid _ Hmem Hok Hout) Htail)
        as [Hfinal [rest Hrest]].
      split; [exact Hfinal|]. exists (rest ++ extra). rewrite Hrest, Hextra, app_assoc. reflexivity.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.
End Removed.
End VMSwapRemoveInvariant.
