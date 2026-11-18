(******************************************************************************)
(* Timestamp exclusion through register, ordering and translation handlers    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMSwapRemoveStamps
  PromiseFirstSailVMSwapRemoveStampRun.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMSwapRemoveStampHandlers.
Import VMPromising VMSwapRemoveStamps VMSwapRemoveStampMemory.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.fst_set_fst VMViews.snd_set_fst VMViews.fst_set_snd VMViews.snd_set_snd
  VMViews.fst_set_snd_field VMViews.snd_set_snd_field : pp_stamp_handlers.
Ltac simpl_pp := unfold ok, setv in *; autorewrite with pp_stamp_handlers in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.
Ltac solve_fields := first [assumption
  | apply update_vdmb; solve_fields | apply update_vdmbst; solve_fields
  | apply update_vdsb; solve_fields | apply update_vmsr; solve_fields
  | apply update_vspec; solve_fields | apply next_epoch; solve_fields
  | apply iis_add; solve_fields | apply iis_trs; solve_fields
  | apply iis_sreg; solve_fields
  | eapply cse; [|eassumption]; solve_fields
  | eapply add_wsreg; [|eassumption]; solve_fields
  | eapply set_reg; [|eassumption]; solve_fields].

Lemma run_cse_ok p tid imem vmax pp pp' value : ok p pp →
  Exec.elem_of_results (pp', value) (run_cse tid imem vmax pp) → ok p pp'.
Proof.
  destruct pp as [ts mem iis]. intros [Hts Hiis] Hrun. unfold run_cse in Hrun.
  VMViews.invert; simpl_pp. split; solve_fields.
Qed.

Lemma run_barrier_ok p tid imem barrier vmax pp pp' value : ok p pp →
  Exec.elem_of_results (pp', value) (run_barrier tid imem barrier vmax pp) → ok p pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_barrier in Hrun.
  VMViews.invert.
  all: try solve [eapply run_cse_ok; eassumption].
  all: destruct Hok as [Hts Hiis]; simpl_pp; split; solve_fields.
Qed.

Lemma run_reg_write_ok p tid imem reg racc val pp pp' value : ok p pp →
  Exec.elem_of_results (pp', value) (run_reg_write tid imem reg racc val pp) → ok p pp'.
Proof.
  destruct pp as [ts mem iis]. intros [Hts Hiis] Hrun. unfold run_reg_write in Hrun.
  VMViews.invert; subst; simpl_pp; split; solve_fields.
Qed.

Lemma read_sreg_ok p reg racc st st' vv : ts_ok p st.1 → iis_ok p st.2 →
  Exec.elem_of_results (st', vv) (VMPromising.read_sreg_indirect reg racc st) →
  ts_ok p st'.1 ∧ iis_ok p st'.2.
Proof.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold VMPromising.read_sreg_indirect in Hrun.
  VMViews.invert; subst; simpl_pp; split; solve_fields.
Qed.

Lemma run_reg_trans_read_ok p reg racc trs ts ts' vv : ts_ok p ts →
  Exec.elem_of_results (ts', vv) (run_reg_trans_read reg racc trs ts) → ts_ok p ts'.
Proof.
  intros Hts Hrun. unfold run_reg_trans_read in Hrun. VMViews.invert; subst; exact Hts.
Qed.

Lemma run_reg_general_read_ok p reg racc st st' vv : ts_ok p st.1 → iis_ok p st.2 →
  Exec.elem_of_results (st', vv) (run_reg_general_read reg racc st) →
  ts_ok p st'.1 ∧ iis_ok p st'.2.
Proof.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold run_reg_general_read in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: try solve [eapply (read_sreg_ok p reg racc (ts, iis)); eassumption].
  all: split; solve_fields.
Qed.

Lemma run_reg_read_ok p reg racc st st' vv : ts_ok p st.1 → iis_ok p st.2 →
  Exec.elem_of_results (st', vv) (run_reg_read reg racc st) →
  ts_ok p st'.1 ∧ iis_ok p st'.2.
Proof.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold run_reg_read in Hrun.
  VMViews.invert; subst; simpl_pp.
  - split; [eapply run_reg_trans_read_ok; eassumption|apply iis_add, Hiis].
  - match goal with H : Exec.elem_of_results _ (run_reg_general_read _ _ _) |- _ =>
      apply (run_reg_general_read_ok p) in H as [Hts' Hiis']; [|exact Hts|exact Hiis] end.
    split; [exact Hts'|apply iis_add, Hiis'].
Qed.

Lemma read_pte_ok p pp pp' value : ok p pp → Exec.elem_of_results (pp', value) (read_pte pp) → ok p pp'.
Proof.
  destruct pp as [ts mem iis]. intros [Hts Hiis] Hrun. unfold read_pte in Hrun.
  VMViews.invert; subst; simpl_pp; split; solve_fields.
Qed.

Lemma run_trans_end_ok p trans_end st st' value : ts_ok p st.1 → iis_ok p st.2 →
  Exec.elem_of_results (st', value) (run_trans_end trans_end st) → ts_ok p st'.1 ∧ iis_ok p st'.2.
Proof.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold run_trans_end in Hrun.
  VMViews.invert; subst; simpl_pp; split; solve_fields.
Qed.

Lemma run_take_exception_ok p tid imem fault vmax pp pp' value : ok p pp →
  Exec.elem_of_results (pp', value) (run_take_exception tid imem fault vmax pp) → ok p pp'.
Proof.
  intros Hok Hrun. unfold run_take_exception in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [inv [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [compose] in Hrun.
  destruct (IIS.inv_time (PPState.iis pp)); eapply run_cse_ok; eassumption.
Qed.
End VMSwapRemoveStampHandlers.
