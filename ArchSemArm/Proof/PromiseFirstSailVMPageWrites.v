(******************************************************************************)
(* Histories of threads with a TLB contain only page-local writes             *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstVMExecutionCurrent
  PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstFreshBroadcast PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapRemove PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapPos.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMPageWrites.
Import VMPromising VMSwapRemoveRun.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.
Local Notation ev_ok := VMSwapRemove.SwapFillTotal.ev_ok.

Definition ts_ok mem ts := TState.tlb ts = None ∨ Forall ev_ok mem.
Definition ok (pp : PPState.t TState.t Ev.t IIS.t) := ts_ok (PPState.mem pp) (PPState.state pp).

Lemma empty ts : ts_ok [] ts.
Proof. right. constructor. Qed.
Lemma cache_history mem ts c : ts_ok mem ts → TState.tlb ts = Some c → Forall ev_ok mem.
Proof. intros [Hnone|Hall] Hc; [congruence|exact Hall]. Qed.
Lemma frame mem ts ts' : (TState.tlb ts = None → TState.tlb ts' = None) → ts_ok mem ts → ts_ok mem ts'.
Proof. intros H [Hnone|Hall]; [left; apply H, Hnone|right; exact Hall]. Qed.

Lemma run_tlb_none_after upd ts ts' : TState.tlb ts = None → TState.run_tlb upd ts = Ok ts' → TState.tlb ts' = None.
Proof. intros Hnone Hrun. rewrite (run_tlb_none _ _ Hnone) in Hrun. injection Hrun as <-. exact Hnone. Qed.
Lemma cse_none imem mem tid v ts ts' : TState.tlb ts = None → TState.cse imem mem tid v ts = Ok ts' → TState.tlb ts' = None.
Proof.
  intros Hnone Hrun. unfold TState.cse in Hrun.
  match type of Hrun with context [TState.run_tlb ?upd ?before] =>
    rewrite (run_tlb_none upd before Hnone) in Hrun end.
  injection Hrun as <-. exact Hnone.
Qed.
Lemma add_wsreg_none tid imem mem reg val v ts ts' : TState.tlb ts = None →
  TState.add_wsreg tid imem mem reg val v ts = Ok ts' → TState.tlb ts' = None.
Proof.
  intros Hnone Hrun. rewrite add_wsreg_upd in Hrun.
  rewrite (run_tlb_none _ _ Hnone) in Hrun. injection Hrun as <-. exact Hnone.
Qed.
Lemma set_reg_none reg vv ts ts' : TState.tlb ts = None → TState.set_reg reg vv ts = Some ts' → TState.tlb ts' = None.
Proof.
  intros Hnone Hrun. unfold TState.set_reg in Hrun. destruct (decide _); [|discriminate]. injection Hrun as <-. exact Hnone.
Qed.

Lemma process_event tid imem mem ev ts ts' : ts_ok mem ts →
  TState.process_event tid imem (ev :: mem) ev ts = Ok ts' → ts_ok (ev :: mem) ts'.
Proof.
  intros Hok Hrun. destruct (TState.tlb ts) as [c|] eqn:Hc.
  - right. constructor; [|eapply cache_history; eassumption].
    destruct (run_tlb_some_inv _ _ _ _ Hc Hrun) as [c' [Hfill _]].
    eapply VMSwapRemove.SwapFillTotal.fill_promise_ev_ok; exact Hfill.
  - left. eapply run_tlb_none_after; [exact Hc|exact Hrun].
Qed.

Ltac cache_eq := VMSwapPos.tlb_eq.
Ltac none_frame := match goal with H : TState.tlb ?ts = None |- TState.tlb ?ts' = None =>
  transitivity (TState.tlb ts); [cache_eq|exact H] end.
Ltac none_derive := repeat match goal with
  | H : TState.cse _ _ _ _ ?before = Ok ?after |- _ =>
    let Hn := fresh in assert (Hn : TState.tlb before = None) by none_frame;
    pose proof (cse_none _ _ _ _ _ _ Hn H); clear H Hn
  | H : TState.add_wsreg _ _ _ _ _ _ ?before = Ok ?after |- _ =>
    let Hn := fresh in assert (Hn : TState.tlb before = None) by none_frame;
    pose proof (add_wsreg_none _ _ _ _ _ _ _ _ Hn H); clear H Hn
  | H : TState.set_reg _ _ ?before = Some ?after |- _ =>
    let Hn := fresh in assert (Hn : TState.tlb before = None) by none_frame;
    pose proof (set_reg_none _ _ _ _ Hn H); clear H Hn end.
Ltac none_solve := VMViews.invert; subst; cbn in *; none_derive; none_frame.

Lemma run_cse_none tid imem vmax pp pp' value : TState.tlb (PPState.state pp) = None →
  Exec.elem_of_results (pp', value) (run_cse tid imem vmax pp) → TState.tlb (PPState.state pp') = None.
Proof. destruct pp as [ts mem iis]. intros Hnone Hrun. unfold run_cse in Hrun. none_solve. Qed.
Lemma run_reg_write_none tid imem reg racc val pp pp' value : TState.tlb (PPState.state pp) = None →
  Exec.elem_of_results (pp', value) (run_reg_write tid imem reg racc val pp) → TState.tlb (PPState.state pp') = None.
Proof. destruct pp as [ts mem iis]. intros Hnone Hrun. unfold run_reg_write in Hrun. none_solve. Qed.

Lemma run_cse_ok tid imem vmax pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_cse tid imem vmax pp) → ok pp'.
Proof.
  intros [Hnone|Hall] Hrun.
  - left. eapply run_cse_none; eassumption.
  - right. rewrite (VMMemoryGrowth.cse_preserves_mem _ _ _ _ _ _ Hrun). exact Hall.
Qed.
Lemma run_reg_write_ok tid imem reg racc val pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_reg_write tid imem reg racc val pp) → ok pp'.
Proof.
  intros [Hnone|Hall] Hrun.
  - left. eapply run_reg_write_none; eassumption.
  - right. rewrite (VMMemoryGrowth.reg_write_preserves_mem _ _ _ _ _ _ _ _ Hrun). exact Hall.
Qed.
Lemma same_mem pp pp' : PPState.mem pp' = PPState.mem pp →
  (TState.tlb (PPState.state pp) = None → TState.tlb (PPState.state pp') = None) → ok pp → ok pp'.
Proof. intros Hmem Hnone [Hn|Hall]; [left; apply Hnone, Hn|right; rewrite Hmem; exact Hall]. Qed.

Lemma read_mem_ok imem addr size macc pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (read_mem_explicit imem addr size macc pp) → ok pp'.
Proof.
  intros Hok Hrun. apply (same_mem pp pp'); [eapply VMMemoryGrowth.read_mem_preserves_mem; exact Hrun| |exact Hok].
  destruct pp as [ts mem iis]. intros Hnone. unfold read_mem_explicit in Hrun. none_solve.
Qed.
Lemma read_pte_ok pp pp' value : ok pp → Exec.elem_of_results (pp', value) (read_pte pp) → ok pp'.
Proof.
  intros Hok Hrun. apply (same_mem pp pp'); [eapply VMMemoryGrowth.read_pte_preserves_mem; exact Hrun| |exact Hok].
  destruct pp as [ts mem iis]. intros Hnone. unfold read_pte in Hrun. none_solve.
Qed.
Lemma run_trans_start_ok tid imem start pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_trans_start tid imem start pp) → ok pp'.
Proof.
  intros Hok Hrun. apply (same_mem pp pp'); [eapply VMMemoryGrowth.trans_start_preserves_mem; exact Hrun| |exact Hok].
  destruct pp as [ts mem iis]. intros Hnone. unfold run_trans_start in Hrun.
  VMViews.invert; subst; cbn in *.
  all: try (match goal with H : Exec.elem_of_results _ (read_sreg_indirect _ _ _) |- _ =>
    unfold read_sreg_indirect in H; VMViews.invert; subst; cbn in * end).
  all: none_frame.
Qed.
Lemma run_reg_read_ok mem reg racc st st' value : ts_ok mem st.1 →
  Exec.elem_of_results (st', value) (run_reg_read reg racc st) → ts_ok mem st'.1.
Proof. intros Hok Hrun. rewrite (VMSwapPos.run_reg_read_pos _ _ _ _ _ Hrun). exact Hok. Qed.
Lemma run_trans_end_ok mem trans st st' value : ts_ok mem st.1 →
  Exec.elem_of_results (st', value) (run_trans_end trans st) → ts_ok mem st'.1.
Proof.
  intros Hok Hrun. eapply frame; [|exact Hok]. rewrite (VMSwapPos.run_trans_end_pos _ _ _ _ Hrun). exact id.
Qed.
Lemma run_barrier_ok tid imem barrier vmax pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_barrier tid imem barrier vmax pp) → ok pp'.
Proof.
  intros Hok Hrun. apply (same_mem pp pp'); [eapply VMMemoryGrowth.barrier_preserves_mem; exact Hrun| |exact Hok].
  destruct pp as [ts mem iis]. intros Hnone. unfold run_barrier in Hrun. VMViews.invert.
  all: try solve [eapply run_cse_none; eassumption].
  all: subst; cbn in *; none_frame.
Qed.
Lemma run_take_exception_ok tid imem fault vmax pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_take_exception tid imem fault vmax pp) → ok pp'.
Proof.
  intros Hok Hrun. unfold run_take_exception in Hrun. VMViews.invert.
  all: eapply run_cse_ok; eassumption.
Qed.

#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_both VMViews.mem_set_both VMViews.iis_set_both
  VMViews.state_set_mem VMViews.mem_set_mem VMViews.iis_set_mem : pp_page_writes.
Ltac simpl_pp := unfold ok, setv in *; autorewrite with pp_page_writes in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.
Ltac page_frame := match goal with H : ts_ok ?mem ?ts |- ts_ok ?mem ?ts' =>
  apply (frame mem ts ts'); [intros ?; none_frame|exact H] end.
Ltac process_derive := try match goal with H : TState.process_event ?tid ?imem (?ev :: ?mem) ?ev ?before = Ok ?after |- _ =>
  assert (Hafter : ts_ok (ev :: mem) after) by (eapply process_event; [eassumption|exact H]) end.

Lemma write_mem_ok tid imem addr size macc data pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (write_mem tid imem addr size macc data pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold write_mem in Hrun.
  VMViews.invert; subst; simpl_pp; process_derive; page_frame.
Qed.
Lemma materialize_ok tid imem pre event recipient pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (materialize_tlbi_for_recipient tid imem pre event recipient pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold materialize_tlbi_for_recipient in Hrun.
  VMViews.invert; subst; simpl_pp; process_derive; page_frame.
Qed.
Lemma recipients_ok tid imem pre event recipients : ∀ acc pp pp' value, ok pp →
  Exec.elem_of_results (pp', value) (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre event) acc recipients pp) → ok pp'.
Proof.
  induction recipients as [|recipient recipients IH]; intros acc pp pp' value Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hok.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [acc' [Hstep Htail]]].
    destruct acc as [[self other] created]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time fresh] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _]. eapply IH; [eapply materialize_ok; eassumption|exact Htail].
Qed.
Lemma run_tlbi_ok n tid imem viio info pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_tlbi n tid imem viio info pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_tlbi in Hrun. VMViews.invert; subst.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply recipients_ok in H; [|exact Hok] end.
  all: simpl_pp; page_frame.
Qed.
Lemma run_outcome_ok n tid imem out pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_outcome n tid imem out pp) → ok pp'.
Proof.
  intros Hok H. funelim (run_outcome n tid imem out pp).
  all: rewrite <- Heqcall in H.
  all: VMViews.invert; subst.
  all: try solve [eapply write_mem_ok; eassumption].
  all: try solve [eapply read_mem_ok; eassumption].
  all: try solve [eapply read_pte_ok; eassumption].
  all: try solve [eapply run_reg_write_ok; eassumption].
  all: try solve [eapply run_cse_ok; eassumption].
  all: try solve [eapply run_barrier_ok; eassumption].
  all: try solve [eapply run_take_exception_ok; eassumption].
  all: try solve [eapply run_trans_start_ok; eassumption].
  all: try solve [eapply run_tlbi_ok; eassumption].
  all: simpl_pp.
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_reg_read ?reg ?racc ?before) |- _ =>
    exact (run_reg_read_ok _ reg racc before after result Hok H) end].
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_trans_end ?trans ?before) |- _ =>
    exact (run_trans_end_ok _ trans before after result Hok H) end].
  all: page_frame.
Qed.

Theorem instruction_ok n (tid : fin n) imem {A} (mon : iMon A) pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (cinterp (run_outcome' n tid imem) mon pp) → ok pp'.
Proof.
  revert pp pp' value. induction mon as [a|call k IH]; intros pp pp' value Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hok.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[ret pre] [Heq Hout]]. cbn in Heq. subst res.
      eapply IH; [eapply run_outcome_ok; eassumption|exact Htail].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

Lemma emit_ok tid imem mem ev ts ts' : ts_ok mem ts →
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok ts' → ts_ok (ev :: mem) ts'.
Proof.
  intros Hok Hrun. unfold TState.emit_promise in Hrun. eapply process_event; [|exact Hrun].
  destruct (bool_decide _); [destruct ev|]; page_frame.
Qed.
Theorem cse_remove_error tid imem l r tlbi rc epoch v a b err : ts_rel r a b →
  ts_ok (l ++ Ev.Tlbi tlbi rc epoch :: r) a →
  TState.cse imem (l ++ Ev.Tlbi tlbi rc epoch :: r) tid v a = Error err →
  ∃ err', TState.cse imem (l ++ r) tid (VMSwapSim.unshift (S (length r)) v) b = Error err'.
Proof.
  intros Hrel [Hnone|Hall] Hrun.
  - unfold TState.cse in Hrun.
    match type of Hrun with context [TState.run_tlb ?upd ?before] =>
      rewrite (run_tlb_none upd before Hnone) in Hrun end. discriminate.
  - eapply cse_remove_err; eassumption.
Qed.
Theorem add_wsreg_remove_error tid imem l r tlbi rc epoch reg val v a b err : ts_rel r a b →
  ts_ok (l ++ Ev.Tlbi tlbi rc epoch :: r) a →
  TState.add_wsreg tid imem (l ++ Ev.Tlbi tlbi rc epoch :: r) reg val v a = Error err →
  ∃ err', TState.add_wsreg tid imem (l ++ r) reg val (VMSwapSim.unshift (S (length r)) v) b = Error err'.
Proof.
  intros Hrel [Hnone|Hall] Hrun.
  - rewrite add_wsreg_upd in Hrun. rewrite (run_tlb_none _ _ Hnone) in Hrun. discriminate.
  - eapply add_wsreg_remove_err; eassumption.
Qed.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Definition state_ok (st : state) := VMViews.state_ok st ∧
  ∀ tid, ts_ok (PState.events st) (PState.tstate tid st).

Lemma from_archState_ok ms st : PState.from_archState prom ms = Ok st → state_ok st.
Proof.
  intros Hrun. split; [eapply VMViews.from_archState_ok; exact Hrun|].
  unfold PState.from_archState in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  intro tid. apply empty.
Qed.
Lemma promise_ok ev st st' : state_ok st → PState.promise prom ev st = Ok st' → state_ok st'.
Proof.
  intros [Hbounds Hok] Hrun. split; [eapply VMViews.promise_ok; eassumption|].
  unfold PState.promise in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  intro tid. unfold PState.tstate. cbn.
  eapply emit_ok; [apply Hok|exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid)].
Qed.
Lemma broadcast_ok (owner : fin n) imem base extra (states states' : vec TState.t n) :
  (∀ i, i ≠ owner → ts_ok base (states !!! i)) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states' →
  states' !!! owner = states !!! owner ∧ ∀ i, i ≠ owner → ts_ok (extra ++ base) (states' !!! i).
Proof.
  intro Hpre. revert states'. induction extra as [|ev extra IH]; intros states' Hrun.
  - injection Hrun as <-. split; [reflexivity|exact Hpre].
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid; [|discriminate].
    cbn [mbind result_bind] in Hrun. destruct (IH mid eq_refl) as [Hown Hrest].
    pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun) as Hlook. split.
    + specialize (Hlook owner). cbn in Hlook. rewrite decide_True in Hlook by reflexivity.
      injection Hlook as <-. exact Hown.
    + intros i Hi. specialize (Hlook i). cbn in Hlook. rewrite decide_False in Hlook by exact Hi.
      eapply emit_ok; [apply Hrest, Hi|exact Hlook].
Qed.
Theorem run_tid_ok isem (tid : fin n) st st' : state_ok st →
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) → state_ok st'.
Proof.
  intros [Hbounds Hok] Hrun. split; [eapply VMViews.run_tid_ok; eassumption|].
  destruct (run_tid_broadcast_decompose prom isem tid st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  assert (Hinit : VMViews.ok (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init)).
  { split; [apply Hbounds|]. eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. lia. }
  destruct (VMViews.instruction_ok n tid (PState.initmem st) isem _ _ () Hinit Hinst) as [_ [extra Hextra]].
  pose proof (instruction_ok n tid (PState.initmem st) isem
    (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init)
    (PPState.Make ts mem iis) () (Hok tid) Hinst) as Hts.
  cbn in Hts, Hextra. subst mem. rewrite length_app, Nat.add_sub, take_app_length in Hstates.
  apply broadcast_ok in Hstates as [Hown Hrest];
    [|intros i Hi; rewrite vlookup_insert_ne; [apply Hok|intros ->; contradiction]].
  intro i. unfold PState.tstate. cbn. destruct (decide (i = tid)) as [->|Hne].
  - rewrite Hown, vlookup_insert. exact Hts.
  - apply Hrest, Hne.
Qed.
Lemma run_step_ok isem term fuel st st' : state_ok st →
  Exec.elem_of_results (st', ()) (@CPState.run_step isem prom n term fuel st) → state_ok st'.
Proof.
  intros Hok Hrun. apply PromiseFirstCurrent.run_step_inv in Hrun
    as [(tid & ev & nst & _ & _ & Hpromise & ->)|(tid & _ & Hrun)].
  - eapply promise_ok; eassumption.
  - eapply run_tid_ok; eassumption.
Qed.
Lemma transition_ok (isem : iMon ()) (term : terminationCondition n) (use_pf : bool) fuel (st st' : state) :
  state_ok st → Exec.elem_of_results (st', None)
    ((if use_pf then CPState.run_transition_promise_first_uncached isem prom term fuel
      else CPState.run_transition isem prom term fuel) st) → state_ok st'.
Proof.
  intros Hok Hrun. destruct use_pf.
  - apply (PromiseFirstCurrent.run_transition_promise_first_none_inv (prom := prom)) in Hrun
      as (tid & ev & nst & _ & Hpromise & ->). eapply promise_ok; eassumption.
  - apply (PromiseFirstCurrent.run_transition_none_inv (prom := prom)) in Hrun as (next & Hstep & ->).
    eapply run_step_ok; eassumption.
Qed.
Theorem reachable_ok isem term initMs use_pf st :
  PromiseFirstReachable prom isem term initMs use_pf st → state_ok st.
Proof.
  induction 1 as [st Hinit|fuel st st' _ IH Hstep].
  - eapply from_archState_ok; eassumption.
  - eapply transition_ok; eassumption.
Qed.
Theorem steps_ok nondet term st st' : state_ok st →
  rtc (VMViews.Step bbm nondet term) st st' → state_ok st'.
Proof.
  intros Hok Hsteps. induction Hsteps as [st|st mid fin Hstep _ IH]; [exact Hok|].
  apply IH. destruct Hstep as [(tid & _ & Hrun)|(ev & Hpromise)].
  - eapply run_tid_ok; eassumption.
  - eapply promise_ok; eassumption.
Qed.
End Machine.
End VMPageWrites.
