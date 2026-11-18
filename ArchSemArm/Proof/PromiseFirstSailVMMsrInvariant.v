(******************************************************************************)
(* MSR and TTBR views are bounded by the thread's MSR view                    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstFreshBroadcast PromiseFirstVMExecutionCurrent PromiseFirstSailVMViews
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveCore PromiseFirstSailVMSwapPos.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMMsrInvariant.
Import VMPromising VMSwapRemoveRun.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Definition ok (pp : PPState.t TState.t Ev.t IIS.t) := msr_inv (PPState.state pp).
#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_both VMViews.mem_set_both VMViews.iis_set_both
  VMViews.state_set_mem VMViews.mem_set_mem VMViews.iis_set_mem : pp_msr.
Ltac simpl_pp := unfold ok, setv in *; autorewrite with pp_msr in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.
Ltac proj_eq := first [reflexivity | match goal with
  | |- ?f ?lhs = _ => lazymatch lhs with
    | context [TState.set_fwdbs ?addrs ?data ?time ?vdata ?xcl ?ts] =>
      transitivity (f (TState.set_fwdbs addrs data time vdata xcl ts)); [reflexivity|];
      rewrite (VMSwapRemoveCore.fwdbs_projection f addrs _ data time vdata xcl ts ltac:(intros; reflexivity)); proj_eq
    | context [TState.update_cohs ?avs ?ts] =>
      transitivity (f (TState.update_cohs avs ts)); [reflexivity|];
      rewrite (VMSwapRemoveCore.cohs_projection f avs ts ltac:(intros; reflexivity)); proj_eq
    | context [TState.update_tcohs ?asid ?offs ?v ?ts] =>
      transitivity (f (TState.update_tcohs asid offs v ts)); [reflexivity|];
      rewrite (VMSwapRemoveCore.tcohs_projection f asid offs v ts ltac:(intros; reflexivity)); proj_eq
    end end].
Ltac proj_le := first [apply Nat.le_refl | cbn; lia | match goal with |- ?f ?ts ≤ ?f ?ts' =>
  let H := fresh in assert (H : f ts' = f ts) by proj_eq; rewrite H; apply Nat.le_refl end].
Ltac frame := match goal with H : msr_inv ?ts |- msr_inv ?ts' =>
  apply (msr_inv_frame ts ts');
  [proj_eq|proj_eq|proj_le|exact H] end.
Lemma update_vmsr v ts : msr_inv ts → msr_inv (TState.update TState.vmsr v ts).
Proof. intro H. apply (msr_inv_frame ts); [reflexivity|reflexivity|apply Nat.le_max_r|exact H]. Qed.

Lemma read_pte_ok pp pp' value : ok pp → Exec.elem_of_results (pp', value) (read_pte pp) → ok pp'.
Proof. destruct pp as [ts mem iis]. intros Hok Hrun. unfold read_pte in Hrun. VMViews.invert; subst; simpl_pp; frame. Qed.
Lemma read_mem_ok imem addr size macc pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (read_mem_explicit imem addr size macc pp) → ok pp'.
Proof. destruct pp as [ts mem iis]. intros Hok Hrun. unfold read_mem_explicit in Hrun. VMViews.invert; subst; simpl_pp; frame. Qed.

Ltac process_derive := try match goal with H : TState.process_event _ _ _ _ ?before = Ok ?after |- _ =>
  assert (Hafter : msr_inv after) by (eapply msr_inv_process_event; [eassumption|exact H]) end.

Lemma write_mem_ok tid imem addr size macc data pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (write_mem tid imem addr size macc data pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold write_mem in Hrun.
  VMViews.invert; subst; simpl_pp; process_derive; frame.
Qed.
Lemma materialize_ok tid imem pre event recipient pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (materialize_tlbi_for_recipient tid imem pre event recipient pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold materialize_tlbi_for_recipient in Hrun.
  VMViews.invert; subst; simpl_pp; process_derive; frame.
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
  all: simpl_pp; frame.
Qed.
Lemma run_cse_ok tid imem vmax pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_cse tid imem vmax pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_cse in Hrun. VMViews.invert; subst; simpl_pp.
  eapply msr_inv_cse; eassumption.
Qed.
Lemma run_barrier_ok tid imem barrier vmax pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_barrier tid imem barrier vmax pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_barrier in Hrun. VMViews.invert.
  all: try solve [eapply run_cse_ok; eassumption].
  all: subst; simpl_pp; frame.
Qed.
Lemma run_take_exception_ok tid imem fault vmax pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_take_exception tid imem fault vmax pp) → ok pp'.
Proof. intros Hok Hrun. unfold run_take_exception in Hrun. VMViews.invert; eapply run_cse_ok; eassumption. Qed.
Lemma run_reg_read_ok reg racc st st' value : msr_inv st.1 →
  Exec.elem_of_results (st', value) (run_reg_read reg racc st) → msr_inv st'.1.
Proof. intros Hok Hrun. rewrite (VMSwapPos.run_reg_read_pos _ _ _ _ _ Hrun). exact Hok. Qed.
Lemma run_trans_end_ok trans st st' value : msr_inv st.1 →
  Exec.elem_of_results (st', value) (run_trans_end trans st) → msr_inv st'.1.
Proof.
  destruct st as [ts iis]. intros Hok Hrun. unfold run_trans_end in Hrun. VMViews.invert; subst; simpl_pp; frame.
Qed.
Lemma run_trans_start_ok tid imem start pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_trans_start tid imem start pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_trans_start in Hrun. VMViews.invert; subst; simpl_pp.
  all: try match goal with H : Exec.elem_of_results _ (read_sreg_indirect _ _ _) |- _ =>
    unfold read_sreg_indirect in H; VMViews.invert; subst; simpl_pp end.
  all: frame.
Qed.
Lemma run_reg_write_ok tid imem reg racc val pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_reg_write tid imem reg racc val pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_reg_write in Hrun. VMViews.invert; subst; simpl_pp.
  all: try solve [eapply msr_inv_add_wsreg; eassumption].
  all: match goal with H : TState.set_reg ?reg ?vv ?before = Some ?after |- _ =>
    assert (Hbefore : msr_inv before) by frame;
    assert (Hafter : msr_inv after) by first
      [eapply msr_inv_set_reg_strict; [eassumption|exact Hbefore|exact H]
      |match goal with He : bool_decide (reg = pc_reg) = true |- _ =>
        apply bool_decide_eq_true in He; subst reg; eapply msr_inv_set_reg_pc; eassumption end] end.
  all: first [frame|apply update_vmsr, Hafter].
Qed.

Lemma run_outcome_ok n tid imem out pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_outcome n tid imem out pp) → ok pp'.
Proof.
  intros Hok Hrun. funelim (run_outcome n tid imem out pp).
  all: rewrite <- Heqcall in Hrun; VMViews.invert; subst.
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
    exact (run_reg_read_ok reg racc before after result Hok H) end].
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_trans_end ?trans ?before) |- _ =>
    exact (run_trans_end_ok trans before after result Hok H) end].
  all: frame.
Qed.
Theorem instruction_ok n (tid : fin n) imem {A} (mon : iMon A) pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (cinterp (run_outcome' n tid imem) mon pp) → ok pp'.
Proof.
  revert pp pp' value. induction mon as [ret|call k IH]; intros pp pp' value Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hok.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[ret pre] [Heq Hout]]. cbn in Heq. subst res.
      eapply IH; [eapply run_outcome_ok; eassumption|exact Htail].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.
Lemma emit_ok tid imem mem ev ts ts' : msr_inv ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → msr_inv ts'.
Proof.
  intros Hok Hrun. unfold TState.emit_promise in Hrun. eapply msr_inv_process_event; [|exact Hrun].
  destruct (bool_decide _); [destruct ev|]; frame.
Qed.
Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Definition state_ok (st : state) := VMViews.state_ok st ∧ ∀ tid, msr_inv (PState.tstate tid st).

Lemma from_archState_ok ms st : PState.from_archState prom ms = Ok st → state_ok st.
Proof.
  intros Hrun. split; [eapply VMViews.from_archState_ok; exact Hrun|].
  unfold PState.from_archState in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  intro tid. unfold PState.tstate. cbn. eapply msr_inv_init.
  exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid).
Qed.
Lemma promise_ok ev st st' : state_ok st → PState.promise prom ev st = Ok st' → state_ok st'.
Proof.
  intros [Hbounds Hok] Hrun. split; [eapply VMViews.promise_ok; eassumption|].
  unfold PState.promise in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  intro tid. unfold PState.tstate. cbn. eapply emit_ok;
    [apply Hok|exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid)].
Qed.
Lemma broadcast_ok (owner : fin n) imem base extra (states states' : vec TState.t n) :
  (∀ i, msr_inv (states !!! i)) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states' → ∀ i, msr_inv (states' !!! i).
Proof.
  intro Hpre. revert states'. induction extra as [|ev extra IH]; intros states' Hrun.
  - injection Hrun as <-. exact Hpre.
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid; [|discriminate].
    cbn [mbind result_bind] in Hrun. pose proof (IH mid eq_refl) as Hrest.
    intro i. pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun i) as Hlook. cbn in Hlook.
    destruct (decide (i = owner)); [injection Hlook as <-; apply Hrest|].
    eapply emit_ok; [apply Hrest|exact Hlook].
Qed.
Theorem run_tid_ok isem (tid : fin n) st st' : state_ok st →
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) → state_ok st'.
Proof.
  intros [Hbounds Hok] Hrun. split; [eapply VMViews.run_tid_ok; eassumption|].
  destruct (run_tid_broadcast_decompose prom isem tid st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  pose proof (instruction_ok n tid (PState.initmem st) isem
    (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init)
    (PPState.Make ts mem iis) () (Hok tid) Hinst) as Hts.
  cbn in Hts. unfold PState.tstate. cbn. eapply broadcast_ok; [|exact Hstates].
  intro i. destruct (decide (i = tid)) as [->|Hne].
  - rewrite vlookup_insert. exact Hts.
  - rewrite vlookup_insert_ne; [apply Hok|congruence].
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
End VMMsrInvariant.
