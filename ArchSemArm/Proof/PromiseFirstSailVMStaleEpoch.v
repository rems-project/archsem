(******************************************************************************)
(* A TLBI promise from an earlier DSB epoch cannot be fulfilled                *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstFreshBroadcast
  PromiseFirstSailVMViews PromiseFirstVMExecutionCurrent
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveCore PromiseFirstSailVMSwapPos
  PromiseFirstSailVMTLBINormalization PromiseFirstSailVMCreatingReplay PromiseFirstSailVMSwapSim
  PromiseFirstSailVMDirect PromiseFirstSailVMCacheSim PromiseFirstSailVMNormalization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMStaleEpoch.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma lookup_bound (mem : Memory.t) t ev : VMSwapSim.mlookup mem t = Some ev → t ≤ length mem.
Proof.
  rewrite VMSwapSim.lookup_spec. case_decide; [intros _; lia|discriminate].
Qed.
Lemma lookup_prefix extra (mem : Memory.t) t ev : VMSwapSim.mlookup mem t = Some ev →
  VMSwapSim.mlookup (extra ++ mem) t = Some ev.
Proof.
  intros Hlookup. induction extra as [|ev' extra IH]; [exact Hlookup|].
  unfold VMSwapSim.mlookup. rewrite PromMemory.lookup_cons_old; [exact IH|].
  pose proof (lookup_bound mem t ev Hlookup). rewrite length_app. lia.
Qed.
Lemma fulfill_lookup ev proms (mem : Memory.t) t : Memory.fulfill ev proms mem = Some t →
  VMSwapSim.mlookup mem t = Some ev.
Proof.
  unfold Memory.fulfill, PromMemory.fulfill. rewrite head_reverse. intro H.
  apply last_Some_elem_of in H. apply list_elem_of_filter in H as [H _]. exact H.
Qed.

Section Stale.
Context (p : nat) (oldtlbi : TLBI.t) (recipient epoch : nat).
Local Notation old := (Ev.Tlbi oldtlbi recipient epoch).

Definition ts_ok ts := p ∈ TState.prom_tlbi ts ∧ epoch < TState.dsb_epoch ts.
Definition keep (pp : PPState.t TState.t Ev.t IIS.t) := ts_ok (PPState.state pp).
Definition ok pp := keep pp ∧ VMSwapSim.mlookup (PPState.mem pp) p = Some old.

Lemma ts_frame ts ts' : TState.prom_tlbi ts' = TState.prom_tlbi ts →
  TState.dsb_epoch ts ≤ TState.dsb_epoch ts' → ts_ok ts → ts_ok ts'.
Proof. intros Hp He [Hin Hold]. split; [rewrite Hp; exact Hin|lia]. Qed.
Lemma process_event_keep tid imem mem ev ts ts' : ts_ok ts →
  TState.process_event tid imem mem ev ts = Ok ts' → ts_ok ts'.
Proof.
  intros Hok Hrun. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hrun) as [cache ->]. exact Hok.
Qed.
Lemma filter_keep time ts : p ≠ time → ts_ok ts →
  ts_ok (set TState.prom_tlbi (filter (λ t, t ≠ time)) ts).
Proof.
  intros Hne [Hp He]. split; [apply list_elem_of_filter; split; assumption|exact He].
Qed.
Lemma fulfill_different ts mem tlbi rc time : ts_ok ts → VMSwapSim.mlookup mem p = Some old →
  Memory.fulfill (Ev.Tlbi tlbi rc (TState.dsb_epoch ts)) (TState.prom_tlbi ts) mem = Some time → p ≠ time.
Proof.
  intros [_ He] Hlook Hful ->. apply fulfill_lookup in Hful. rewrite Hlook in Hful.
  injection Hful as Htlbi Hrc Hep. lia.
Qed.

Lemma materialize_ok tid imem pre tlbi rc pp pp' time created : ok pp →
  Exec.elem_of_results (pp', (time, created)) (materialize_tlbi_for_recipient tid imem pre tlbi rc pp) → ok pp'.
Proof.
  destruct pp as [ts mem iis]. intros [Hkeep Hlook] Hrun. cbn in Hkeep, Hlook.
  destruct created.
  - apply VMTLBINormalization.materialize_fresh_inv in Hrun as [Hnone [-> [Hpre [next [Hnext ->]]]]].
    assert (Hp : p ≤ length mem) by (eapply lookup_bound; exact Hlook).
    split.
    + apply filter_keep; [lia|]. eapply process_event_keep; [exact Hkeep|exact Hnext].
    + cbn [PPState.mem]. change (VMSwapSim.mlookup ([Ev.Tlbi tlbi rc (TState.dsb_epoch ts)] ++ mem) p = Some old).
      apply lookup_prefix, Hlook.
  - apply VMCreatingReplay.materialize_fulfilled_inv in Hrun as [Hful [Hpre ->]].
    split; [|exact Hlook]. apply filter_keep; [|exact Hkeep].
    eapply fulfill_different; eassumption.
Qed.

Lemma recipients_ok tid imem pre tlbi recipients : ∀ acc pp pp' value, ok pp →
  Exec.elem_of_results (pp', value)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients pp) → ok pp'.
Proof.
  induction recipients as [|rc recipients IH]; intros acc pp pp' value Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hok.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [acc' [Hstep Htail]]].
    destruct acc as [[self other] created]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time fresh] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _]. eapply IH; [eapply materialize_ok; eassumption|exact Htail].
Qed.

Lemma cse_keep imem mem tid v ts ts' : ts_ok ts → TState.cse imem mem tid v ts = Ok ts' → ts_ok ts'.
Proof.
  intros Hok Hrun. unfold TState.cse in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [cache ->]. exact Hok.
Qed.
Lemma add_wsreg_keep tid imem mem sreg val v ts ts' : ts_ok ts →
  TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → ts_ok (TState.update TState.vmsr v ts').
Proof.
  intros Hok Hrun. rewrite VMSwapRemoveRun.add_wsreg_upd in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [cache ->]. exact Hok.
Qed.
Lemma set_reg_keep reg rv ts ts' : ts_ok ts → TState.set_reg reg rv ts = Some ts' → ts_ok ts'.
Proof.
  intros Hok Hset. unfold TState.set_reg in Hset. destruct (decide _); [|discriminate].
  injection Hset as <-. exact Hok.
Qed.
#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_both VMViews.mem_set_both VMViews.iis_set_both
  VMViews.state_set_mem VMViews.mem_set_mem VMViews.iis_set_mem : pp_epoch.
Ltac simpl_pp := unfold keep, setv in *; autorewrite with pp_epoch in *;
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
Ltac frame := match goal with H : ts_ok ?ts |- ts_ok ?ts' =>
  apply (ts_frame ts ts');
  [proj_eq|proj_le|exact H] end.
Lemma update_vmsr v ts : ts_ok ts → ts_ok (TState.update TState.vmsr v ts).
Proof. intro H. apply (ts_frame ts); [reflexivity|apply Nat.le_refl|exact H]. Qed.

Lemma read_pte_keep pp pp' value : keep pp → Exec.elem_of_results (pp', value) (read_pte pp) → keep pp'.
Proof. destruct pp as [ts mem iis]. intros Hok Hrun. unfold read_pte in Hrun. VMViews.invert; subst; simpl_pp; frame. Qed.
Lemma read_mem_keep imem addr size macc pp pp' value : keep pp →
  Exec.elem_of_results (pp', value) (read_mem_explicit imem addr size macc pp) → keep pp'.
Proof. destruct pp as [ts mem iis]. intros Hok Hrun. unfold read_mem_explicit in Hrun. VMViews.invert; subst; simpl_pp; frame. Qed.

Ltac process_derive := try match goal with H : TState.process_event _ _ _ _ ?before = Ok ?after |- _ =>
  assert (Hafter : ts_ok after) by (eapply process_event_keep; [eassumption|exact H]) end.

Lemma write_mem_keep tid imem addr size macc data pp pp' value : keep pp →
  Exec.elem_of_results (pp', value) (write_mem tid imem addr size macc data pp) → keep pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold write_mem in Hrun.
  VMViews.invert; subst; simpl_pp; process_derive; frame.
Qed.
Lemma run_tlbi_keep n tid imem viio info pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_tlbi n tid imem viio info pp) → keep pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_tlbi in Hrun. VMViews.invert; subst.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply recipients_ok in H as [Hkept Hlookup]; [|exact Hok] end.
  all: simpl_pp; frame.
Qed.
Lemma run_cse_keep tid imem vmax pp pp' value : keep pp →
  Exec.elem_of_results (pp', value) (run_cse tid imem vmax pp) → keep pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_cse in Hrun. VMViews.invert; subst; simpl_pp.
  eapply cse_keep; eassumption.
Qed.
Lemma run_barrier_keep tid imem barrier vmax pp pp' value : keep pp →
  Exec.elem_of_results (pp', value) (run_barrier tid imem barrier vmax pp) → keep pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_barrier in Hrun. VMViews.invert.
  all: try solve [eapply run_cse_keep; eassumption].
  all: subst; simpl_pp; try frame.
  all: destruct Hok as [Hp He]; split; [exact Hp|change (epoch < S (TState.dsb_epoch ts)); lia].
Qed.
Lemma run_take_exception_keep tid imem fault vmax pp pp' value : keep pp →
  Exec.elem_of_results (pp', value) (run_take_exception tid imem fault vmax pp) → keep pp'.
Proof. intros Hok Hrun. unfold run_take_exception in Hrun. VMViews.invert; eapply run_cse_keep; eassumption. Qed.
Lemma run_reg_read_keep reg racc st st' value : ts_ok st.1 →
  Exec.elem_of_results (st', value) (run_reg_read reg racc st) → ts_ok st'.1.
Proof. intros Hok Hrun. rewrite (VMSwapPos.run_reg_read_pos _ _ _ _ _ Hrun). exact Hok. Qed.
Lemma run_trans_end_keep trans st st' value : ts_ok st.1 →
  Exec.elem_of_results (st', value) (run_trans_end trans st) → ts_ok st'.1.
Proof.
  destruct st as [ts iis]. intros Hok Hrun. unfold run_trans_end in Hrun. VMViews.invert; subst; simpl_pp; frame.
Qed.
Lemma run_trans_start_keep tid imem start pp pp' value : keep pp →
  Exec.elem_of_results (pp', value) (run_trans_start tid imem start pp) → keep pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_trans_start in Hrun. VMViews.invert; subst; simpl_pp.
  all: try match goal with H : Exec.elem_of_results _ (read_sreg_indirect _ _ _) |- _ =>
    unfold read_sreg_indirect in H; VMViews.invert; subst; simpl_pp end.
  all: frame.
Qed.
Lemma run_reg_write_keep tid imem reg racc val pp pp' value : keep pp →
  Exec.elem_of_results (pp', value) (run_reg_write tid imem reg racc val pp) → keep pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_reg_write in Hrun. VMViews.invert; subst; simpl_pp.
  all: try solve [eapply add_wsreg_keep; eassumption].
  all: match goal with H : TState.set_reg ?reg ?vv ?before = Some ?after |- _ =>
    assert (Hbefore : ts_ok before) by frame;
    assert (Hafter : ts_ok after) by (eapply set_reg_keep; [exact Hbefore|exact H]) end.
  all: first [frame|apply update_vmsr, Hafter].
Qed.

Lemma run_outcome_keep n tid imem out pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_outcome n tid imem out pp) → keep pp'.
Proof.
  intros Hok Hrun. pose proof (proj1 Hok) as Hkeep. funelim (run_outcome n tid imem out pp).
  all: rewrite <- Heqcall in Hrun; VMViews.invert; subst.
  all: try solve [eapply write_mem_keep; eassumption].
  all: try solve [eapply read_mem_keep; eassumption].
  all: try solve [eapply read_pte_keep; eassumption].
  all: try solve [eapply run_reg_write_keep; eassumption].
  all: try solve [eapply run_cse_keep; eassumption].
  all: try solve [eapply run_barrier_keep; eassumption].
  all: try solve [eapply run_take_exception_keep; eassumption].
  all: try solve [eapply run_trans_start_keep; eassumption].
  all: try solve [eapply run_tlbi_keep; eassumption].
  all: simpl_pp.
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_reg_read ?reg ?racc ?before) |- _ =>
    exact (run_reg_read_keep reg racc before after result Hkeep H) end].
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_trans_end ?trans ?before) |- _ =>
    exact (run_trans_end_keep trans before after result Hkeep H) end].
  all: frame.
Qed.

Theorem run_outcome_ok n (tid : fin n) imem out pp pp' value : ok pp →
  Exec.elem_of_results (pp', value) (run_outcome n tid imem out pp) → ok pp'.
Proof.
  intros Hok Hrun. split; [eapply run_outcome_keep; eassumption|].
  destruct (VMViews.outcome_memory_growth n tid imem out pp pp' value Hrun) as [extra Hextra].
  rewrite Hextra. apply lookup_prefix, Hok.
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
Lemma emit_keep tid imem mem ev ts ts' : ts_ok ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → ts_ok ts'.
Proof.
  intros Hok Hrun. unfold TState.emit_promise in Hrun.
  eapply process_event_keep; [|exact Hrun].
  destruct (bool_decide _); [destruct ev|]; try exact Hok.
  destruct Hok as [Hp He]. split; [apply elem_of_cons; right; exact Hp|exact He].
Qed.

Section Machine.
Context (bbm : bool) {n : nat} (target : fin n).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Definition state_ok (st : state) :=
  ts_ok (PState.tstate target st) ∧ VMSwapSim.mlookup (PState.events st) p = Some old.

Lemma promise_ok ev st st' : state_ok st → PState.promise prom ev st = Ok st' → state_ok st'.
Proof.
  intros [Hts Hlookup] Hrun. unfold PState.promise in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  split.
  - unfold PState.tstate. cbn. eapply emit_keep;
      [exact Hts|exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap target)].
  - change (VMSwapSim.mlookup ([ev] ++ PState.events st) p = Some old).
    apply lookup_prefix, Hlookup.
Qed.

Lemma broadcast_keep (owner : fin n) imem base extra (states states' : vec TState.t n) :
  ts_ok (states !!! target) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states' → ts_ok (states' !!! target).
Proof.
  intro Hpre. revert states'. induction extra as [|ev extra IH]; intros states' Hrun.
  - injection Hrun as <-. exact Hpre.
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid; [|discriminate].
    cbn [mbind result_bind] in Hrun. pose proof (IH mid eq_refl) as Hrest.
    pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun target) as Hlook. cbn in Hlook.
    destruct (decide (target = owner)); [injection Hlook as <-; exact Hrest|].
    eapply emit_keep; [exact Hrest|exact Hlook].
Qed.

Theorem run_tid_ok isem (owner : fin n) st st' : state_ok st →
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom owner st) → state_ok st'.
Proof.
  intros [Hts Hlookup] Hrun.
  destruct (run_tid_broadcast_decompose prom isem owner st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  destruct (VMFinalCertification.instruction_memory_suffix owner _ isem _ _ _ Hinst) as [extra Hextra].
  split.
  - unfold PState.tstate. cbn. eapply broadcast_keep; [|exact Hstates].
    destruct (decide (target = owner)) as [Heq|Hne].
    + rewrite Heq, vlookup_insert.
      assert (Hentry : ok (PPState.Make (PState.tstate owner st) (PState.events st) IIS.init)).
      { split; [rewrite <- Heq; exact Hts|exact Hlookup]. }
      exact (proj1 (instruction_ok n owner (PState.initmem st) isem _ _ () Hentry Hinst)).
    + rewrite vlookup_insert_ne; [exact Hts|congruence].
  - cbn in Hextra |- *. rewrite Hextra. apply lookup_prefix, Hlookup.
Qed.

Theorem mixed_rtc_ok nondet term st st' : state_ok st →
  rtc (VMNormalization.Mixed bbm nondet term) st st' → state_ok st'.
Proof.
  intros Hok Hsteps. induction Hsteps as [st|st mid fin Hstep _ IH]; [exact Hok|].
  apply IH. destruct Hstep as [(tid & _ & Hrun)|(ev & _ & Hpromise)].
  - eapply run_tid_ok; eassumption.
  - eapply promise_ok; eassumption.
Qed.

Lemma final_not_ok term st fs : VMNormalization.FinalResult bbm term st fs → ¬ state_ok st.
Proof.
  intros [pt [Hvalid Hresult]] [[Hp He] Hlookup].
  destruct (VMCacheSimOutcome.validate_final_state_inv bbm st st st Hvalid) as [_ [Hnone _]].
  unfold CPState.nopromises, PState.nopromises, fforallb in Hnone. apply true_eq_true in Hnone.
  pose proof (proj1 (@List.forallb_forall (fin n) (PState.nopromises_tid prom st) (enum (fin n))) Hnone
    target ltac:(apply list_elem_of_In, elem_of_enum)) as Htarget.
  change (is_emptyb (TState.prom_wr (PState.tstate target st) ++
    TState.prom_tlbi (PState.tstate target st)) = true) in Htarget.
  apply is_emptyb_eq_nil in Htarget. apply app_eq_nil in Htarget as [_ Hnil].
  rewrite Hnil in Hp. exact (not_elem_of_nil p Hp).
Qed.

Theorem cannot_complete nondet term st final fs : state_ok st →
  rtc (VMNormalization.Mixed bbm nondet term) st final →
  ¬ VMNormalization.FinalResult bbm term final fs.
Proof. intros Hok Hsteps Hfinal. eapply final_not_ok; [exact Hfinal|]. eapply mixed_rtc_ok; eassumption. Qed.
End Machine.
End Stale.
End VMStaleEpoch.
