(******************************************************************************)
(* View, cache and timestamp exclusion through translation start              *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMGuards
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveThread
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMSwapRemoveStampRun PromiseFirstSailVMSwapRemoveTLBI
  PromiseFirstSailVMSwapRemoveLookupViews.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveTranslation.
Import VMPromising VMSwapRemoveState VMSwapRemoveViews VMSwapRemoveThread.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma tcohs_frame asid offsets v ts :
  TState.vcse (TState.update_tcohs asid offsets v ts) = TState.vcse ts ∧
  TState.tlb (TState.update_tcohs asid offsets v ts) = TState.tlb ts.
Proof.
  induction offsets as [|offset offsets IH]; [split; reflexivity|].
  exact IH.
Qed.

Lemma tcohs_stamps p asid offsets v ts : VMSwapRemoveStamps.ts_ok p ts →
  VMSwapRemoveStamps.ts_ok p (TState.update_tcohs asid offsets v ts).
Proof.
  intro Hts. induction offsets as [|offset offsets IH]; [exact Hts|].
  change (VMSwapRemoveStamps.ts_ok p
    (TState.update_tcoh asid offset v (TState.update_tcohs asid offsets v ts))).
  eapply (VMSwapRemoveStamps.frame p (TState.update_tcohs asid offsets v ts)); try reflexivity; exact IH.
Qed.

#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_both VMViews.mem_set_both VMViews.iis_set_both
  VMViews.fst_set_fst VMViews.snd_set_fst VMViews.fst_set_snd VMViews.snd_set_snd
  VMViews.fst_set_snd_field VMViews.snd_set_snd_field : pp_translation.
Ltac simpl_pp := unfold VMSwapRemoveThread.ok, VMSwapRemoveStampMemory.ok, setv in *;
  autorewrite with pp_translation in *; cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Lemma read_sreg_stamps p reg racc st st' vv : VMSwapRemoveStamps.iis_ok p st.2 →
  Exec.elem_of_results (st', vv) (VMPromising.read_sreg_indirect reg racc st) →
  VMSwapRemoveStamps.iis_ok p st'.2.
Proof.
  destruct st as [ts iis]. intros Hiis Hrun. unfold VMPromising.read_sreg_indirect in Hrun.
  VMViews.invert; subst; simpl_pp; first [exact Hiis|apply VMSwapRemoveStamps.iis_sreg, Hiis].
Qed.

Ltac solve_view :=
  cbn [compose PPState.state PPState.iis fst snd IIS.TransRes.trans_start];
  first [assumption | apply allowed_max; solve_view | apply allowed_zero; lia
    | apply view_if_ok; [apply allowed_zero; lia|solve_view]].

Lemma run_trans_start_inv tid imem l r tlbi rc epoch start pp pp' value :
  PPState.mem pp = l ++ Ev.Tlbi tlbi rc epoch :: r → VMViews.ok pp → VMSwapRemoveTLBI.inv (S (length r)) pp →
  Exec.elem_of_results (pp', value) (run_trans_start tid imem start pp) →
  VMSwapRemoveTLBI.inv (S (length r)) pp'.
Proof.
  destruct pp as [ts mem iis]. cbn. intros Hmem [Hbts Hbiis] [[[Hts Hcache] Hiis] [Hsts Hsiis]] Hrun.
  subst mem. unfold run_trans_start in Hrun.
  pose proof (VMGuardReplay.min_promise_bound (length (l ++ Ev.Tlbi tlbi rc epoch :: r)) ts) as Hmin.
  VMViews.invert; subst; simpl_pp; VMViews.facts Hts; VMViews.facts Hiis.
  all: try (match goal with H : Exec.elem_of_results _ (VMPromising.read_sreg_indirect ?reg ?racc ?st) |- _ =>
    pose proof (read_sreg_stamps (S (length r)) reg racc st _ _ Hsiis H) as Hsiis';
    destruct (VMSwapRemoveViews.read_sreg_indirect_ok (allowed (S (length r)) (TState.vcse ts))
      reg racc st _ _ Hts Hiis H) as (Hst & Hiis' & _)
    end; cbn in Hst).
  all: try (match goal with
    H : Exec.elem_of_results ?x (Exec.make (TLB.Result.merge (Exec.results ?L)) _) |- _ =>
      assert (Hres : VMSwapRemoveLookupViews.result_ok (S (length r)) (TState.vcse ts) x)
        by (eapply VMViews.Forall_elem; [|exact H]; apply VMSwapRemoveLookupViews.merge_ok, VMViews.Forall_results;
            intros found Hfound; eapply (VMSwapRemoveLookupViews.tlb_lookup_ok imem l r tlbi rc epoch tid ts);
            [exact Hbts|split; assumption| | | |exact Hfound]; try solve_view; lia);
      destruct Hres as [Hstart Hinv] end).
  all: unfold VMSwapRemoveTLBI.inv; simpl_pp; try rewrite Hst.
  all: split.
  all: try (eapply (VMSwapRemoveThread.frame (S (length r)) ts _ iis);
    [apply tcohs_frame|apply tcohs_frame| | |split; [split|]; eassumption]).
  all: try solve [apply update_tcohs; [apply allowed_zero; lia|apply allowed_max|solve_view|exact Hts]].
  all: try solve [apply iis_set_inv_time; [intros t Ht; left; first [exact (Hinv t Ht)|discriminate Ht]|];
    apply iis_set_trs; [solve_view|eassumption]].
  all: split; [apply tcohs_stamps, Hsts|apply VMSwapRemoveStamps.iis_inv;
    [first [exact Hinv|discriminate]|unfold IIS.set_trs; apply VMSwapRemoveStamps.iis_trs; eassumption]].
Qed.
End VMSwapRemoveTranslation.
