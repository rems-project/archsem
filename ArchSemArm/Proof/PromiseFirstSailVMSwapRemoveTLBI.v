(******************************************************************************)
(* View, cache and timestamp exclusion through TLBI materialization           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstVMExecutionCurrent PromiseFirstSailVMViews
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveThread
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMSwapRemoveStampRun.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMSwapRemoveTLBI.
Import VMPromising VMSwapRemoveState VMSwapRemoveViews VMSwapRemoveThread.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

(** This combines the two exclusion components. The full removal relation
    additionally carries TI, msr_inv, view bounds and the related short state. *)
Definition inv p pp := VMSwapRemoveThread.ok p pp ∧ VMSwapRemoveStampMemory.ok p pp.

Lemma filter_tlbi p (P : nat → Prop) `{∀ t, Decision (P t)} ts iis : local_ok p ts iis →
  local_ok p (set TState.prom_tlbi (filter P) ts) iis.
Proof.
  intros [[Hts Hcache] Hiis]. split; [split|].
  - apply VMSwapRemoveViews.filter_prom_tlbi, Hts.
  - exact Hcache.
  - exact Hiis.
Qed.

#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_mem VMViews.mem_set_mem VMViews.iis_set_mem : pp_remove_tlbi.
Ltac simpl_pp := unfold VMSwapRemoveThread.ok, setv in *; autorewrite with pp_remove_tlbi in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Lemma materialize_views p tid imem pre tlbi recipient pp pp' time created :
  p ≤ length (PPState.mem pp) → VMSwapRemoveThread.ok p pp →
  Exec.elem_of_results (pp', (time, created))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient pp) → VMSwapRemoveThread.ok p pp'.
Proof.
  destruct pp as [ts mem iis]. cbn. intros Hb Hok Hrun.
  unfold materialize_tlbi_for_recipient in Hrun. VMViews.invert; subst; simpl_pp.
  all: try match goal with H : TState.process_event ?tid ?imem ?mem ?ev ?before = Ok ?after |- _ =>
    assert (Hafter : local_ok p after iis) by
      (eapply (VMSwapRemoveThread.process_event p tid imem mem ev before after iis);
        [cbn; lia|exact Hok|exact H]) end.
  all: apply filter_tlbi; assumption.
Qed.

Lemma materialize_inv p tid imem pre tlbi recipient pp pp' time created :
  p ≤ length (PPState.mem pp) → inv p pp →
  Exec.elem_of_results (pp', (time, created))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient pp) →
  inv p pp' ∧ time ≠ p ∧ p ≤ length (PPState.mem pp').
Proof.
  intros Hb [Hviews Hstamps] Hrun.
  destruct (VMSwapRemoveStampEvents.materialize_ok p tid imem pre tlbi recipient pp pp' time created
    Hb Hstamps Hrun) as (Hstamps' & Htime & Hbound).
  split; [split|split; assumption].
  - exact (materialize_views p tid imem pre tlbi recipient pp pp' time created Hb Hviews Hrun).
  - exact Hstamps'.
Qed.

Lemma recipients_inv p tid imem pre tlbi recipients vself0 vother0 created0
    pp pp' vself vother created :
  p ≤ length (PPState.mem pp) → inv p pp → vself0 ≠ p → vother0 ≠ p →
  Exec.elem_of_results (pp', ((vself, vother), created))
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi)
      ((vself0, vother0), created0) recipients pp) →
  inv p pp' ∧ vself ≠ p ∧ vother ≠ p ∧ p ≤ length (PPState.mem pp').
Proof.
  revert vself0 vother0 created0 pp.
  induction recipients as [|recipient recipients IH]; intros vself0 vother0 created0 pp Hb Hok Hself Hother Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> Heq]. injection Heq as -> -> ->. auto.
  - cbn [foldlM] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [mid [[[vself1 vother1] created1] [Hstep Htail]]].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time is_new] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> Heq]. injection Heq as Hv1 Hv2 Hc1.
    apply (materialize_inv p) in Hmat as (Hmid & Htime & Hbound); [|exact Hb|exact Hok].
    eapply IH; [exact Hbound|exact Hmid| | |exact Htail]; subst; repeat case_decide; lia.
Qed.

Lemma tlbi_post p self other ts iis : self ≠ p → other ≠ p → local_ok p ts iis →
  local_ok p (TState.update TState.vtlbi_other other (TState.update TState.vtlbi_self self ts))
    (IIS.add (self ⊔ other) iis).
Proof.
  intros Hself Hother Hok. pose proof Hok as [[Hts Hcache] Hiis].
  eapply (frame p ts _ iis); [reflexivity|reflexivity| | |exact Hok].
  - apply update_vtlbi_other; [apply allowed_max|left; exact Hother|].
    apply update_vtlbi_self; [apply allowed_max|left; exact Hself|exact Hts].
  - apply iis_add; [apply allowed_max|apply allowed_max; left; assumption|exact Hiis].
Qed.

Lemma run_tlbi_inv p n tid imem viio tlbi pp pp' value : 0 < p → p ≤ length (PPState.mem pp) → inv p pp →
  Exec.elem_of_results (pp', value) (run_tlbi n tid imem viio tlbi pp) → inv p pp'.
Proof.
  intros Hp Hb Hok Hrun. split.
  - destruct pp as [ts mem iis]. unfold run_tlbi in Hrun. VMViews.invert; subst.
    all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
      apply (recipients_inv p) in H as ([Hmid Hstamps] & Hself & Hother & Hbound);
        [|exact Hb|exact Hok|lia|lia] end.
    all: simpl_pp; unfold compose; apply tlbi_post; assumption.
  - eapply VMSwapRemoveStampEvents.run_tlbi_ok; [exact Hp|exact Hb|apply Hok|exact Hrun].
Qed.
End VMSwapRemoveTLBI.
