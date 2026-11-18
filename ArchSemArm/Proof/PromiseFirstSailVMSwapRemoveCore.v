(******************************************************************************)
(* Cache and MSR invariants through VM outcome and instruction execution      *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMCacheOrder
  PromiseFirstSailVMCacheHistory PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapRemove PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveState
  PromiseFirstSailVMSwapPos PromiseFirstSailVMSwapLookup PromiseFirstVMExecutionCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveCore.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemove VMSwapRemoveRun.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma mapped_self bound r ts : VMViews.ts_ok bound ts → ts_rel r ts (ts_map (unshift (S (length r))) ts).
Proof.
  intro Hb. split; [symmetry; apply VMCacheSim.setv_tlb_same|].
  rewrite ts_map_tlb. destruct (TState.tlb ts) as [c|] eqn:Hc; cbn; [|exact I].
  apply VMCacheSim.cache_sim_refl, wf_tlb_map.
  destruct (VMViews.ok_cache _ _ Hb c Hc) as [_ [Hu Hv]]. split; assumption.
Qed.

Section Removed.
Context (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation e := (Ev.Tlbi tlbi rc epoch).

Definition core l ts := ts_inv imem r tlbi rc epoch l ts ∧ msr_inv ts.

Lemma frame l ts ts' : TState.tlb ts' = TState.tlb ts →
  TState.vcse ts ≤ TState.vcse ts' → TState.vmsr ts ≤ TState.vmsr ts' →
  TState.levs ts' = TState.levs ts → TState.regs ts' = TState.regs ts → core l ts → core l ts'.
Proof.
  intros Htlb Hvc Hvm Hlev Hregs [Hcache Hmsr]. split.
  - intros c Hc. rewrite Htlb in Hc. eapply TI_mono; [exact Hvc|exact Hvm|apply Hcache, Hc].
  - eapply msr_inv_frame; eassumption.
Qed.

Lemma update_vmsr l v ts : core l ts → core l (TState.update TState.vmsr v ts).
Proof. intros H. apply (frame l ts); [reflexivity|apply Nat.le_refl|apply Nat.le_max_r|reflexivity|reflexivity|exact H]. Qed.

Lemma process_event tid l ev ts ts' : core l ts →
  TState.process_event tid imem (ev :: l ++ e :: r) ev ts = Ok ts' → core (ev :: l) ts'.
Proof.
  intros [Hcache Hmsr] Hrun. split; [|eapply msr_inv_process_event; eassumption].
  unfold TState.process_event in Hrun. destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (run_tlb_some_inv _ _ _ _ Hc Hrun) as [c' [Hfill ->]].
    intros c0 Hc0. cbn in Hc0. injection Hc0 as <-.
    destruct (Hcache c Hc) as (Hg & HJ & Hroots). split; [|split].
    + exact (VMCacheOrder.good_fill_promise tid imem (ev :: l ++ e :: r) ev (length (l ++ e :: r))
        c c' ltac:(cbn; lia) Hg Hfill).
    + intros Hlt. exact (J_fill_promise tid imem l r tlbi rc epoch ev c c' (HJ Hlt) Hfill).
    + pose proof (VMCacheRoots.fill_promise _ _ _ _ c c' () Hfill) as Hr.
      unfold VMCacheRoots.config in Hr. unfold proots. rewrite Hr. exact Hroots.
  - rewrite (run_tlb_none _ _ Hc) in Hrun. injection Hrun as <-.
    intros c H. rewrite Hc in H. discriminate.
Qed.

Lemma cse tid l v ts ts' : tid ≠ rc → VMViews.ts_ok (length (l ++ e :: r)) ts → core l ts →
  TState.vcse ts `max` TState.vmsr ts ≤ v → v ≤ length (l ++ e :: r) →
  TState.cse imem (l ++ e :: r) tid v ts = Ok ts' → core l ts'.
Proof.
  intros Hrc Hbound [Hcache Hmsr] Hpre Hv Hrun.
  destruct (cse_remove tid imem r tlbi rc epoch Hrc l v ts _ ts'
    (mapped_self _ r ts Hbound) Hcache Hpre Hv Hrun) as (short & Hshort & Hrel & Hcache').
  split; [exact Hcache'|eapply msr_inv_cse; eassumption].
Qed.

Lemma add_wsreg tid l reg val v ts ts' : tid ≠ rc → VMViews.ts_ok (length (l ++ e :: r)) ts → core l ts →
  TState.vcse ts ≤ v → v ≤ length (l ++ e :: r) →
  TState.add_wsreg tid imem (l ++ e :: r) reg val v ts = Ok ts' →
  core l (TState.update TState.vmsr v ts').
Proof.
  intros Hrc Hbound [Hcache Hmsr] Hpre Hv Hrun.
  destruct (add_wsreg_remove tid imem r tlbi rc epoch Hrc l reg val v ts _ ts'
    (mapped_self _ r ts Hbound) Hcache Hpre Hv
    (ttbr_ok_of_inv _ v ts Hmsr (VMViews.ok_vmsr _ _ Hbound)) Hrun)
    as (short & Hshort & Hrel & Hcache').
  split; [exact Hcache'|eapply msr_inv_add_wsreg; eassumption].
Qed.

Lemma set_reg_strict l reg vv ts ts' : reg ∈ strict_regs → core l ts → TState.set_reg reg vv ts = Some ts' → core l ts'.
Proof.
  intros Hstrict [Hcache Hmsr] Hrun. split.
  - unfold TState.set_reg in Hrun. destruct (decide _); [|discriminate]. injection Hrun as <-. exact Hcache.
  - eapply msr_inv_set_reg_strict; eassumption.
Qed.
Lemma set_reg_pc l vv ts ts' : core l ts → TState.set_reg pc_reg vv ts = Some ts' → core l ts'.
Proof.
  intros [Hcache Hmsr] Hrun. split.
  - unfold TState.set_reg in Hrun. destruct (decide _); [|discriminate]. injection Hrun as <-. exact Hcache.
  - eapply msr_inv_set_reg_pc; eassumption.
Qed.

Lemma cohs_projection {A} (f : TState.t → A) avs ts :
  (∀ a v ts, f (TState.update_coh a v ts) = f ts) → f (TState.update_cohs avs ts) = f ts.
Proof. intros Hf. induction avs as [|[a v] avs IH]; [reflexivity|]. cbn [TState.update_cohs foldr]. rewrite Hf, IH. reflexivity. Qed.
Lemma tcohs_projection {A} (f : TState.t → A) asid offs v ts :
  (∀ o ts, f (TState.update_tcoh asid o v ts) = f ts) → f (TState.update_tcohs asid offs v ts) = f ts.
Proof. intros Hf. induction offs as [|o offs IH]; [reflexivity|]. cbn [TState.update_tcohs foldr]. rewrite Hf, IH. reflexivity. Qed.
Lemma fwdbs_projection {A} (f : TState.t → A) addrs n (data : bv n) time vdata xcl ts :
  (∀ a b ts, f (TState.set_fwdb a (FwdItem.make time vdata b xcl) ts) = f ts) →
  f (TState.set_fwdbs addrs data time vdata xcl ts) = f ts.
Proof.
  intros Hf. unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)) as items.
  intros items. revert ts. induction items as [|[a b] items IH]; intro ts; [reflexivity|]. cbn [foldl]. rewrite IH, Hf. reflexivity.
Qed.

Ltac proj_eq := first [reflexivity | match goal with
  | |- ?f ?lhs = _ => lazymatch lhs with
    | context [TState.set_fwdbs ?addrs ?data ?time ?vdata ?xcl ?ts] =>
      transitivity (f (TState.set_fwdbs addrs data time vdata xcl ts)); [reflexivity|];
      rewrite (fwdbs_projection f addrs _ data time vdata xcl ts ltac:(intros; reflexivity)); proj_eq
    | context [TState.update_cohs ?avs ?ts] =>
      transitivity (f (TState.update_cohs avs ts)); [reflexivity|];
      rewrite (cohs_projection f avs ts ltac:(intros; reflexivity)); proj_eq
    | context [TState.update_tcohs ?asid ?offs ?v ?ts] =>
      transitivity (f (TState.update_tcohs asid offs v ts)); [reflexivity|];
      rewrite (tcohs_projection f asid offs v ts ltac:(intros; reflexivity)); proj_eq
    end
  end].
Ltac proj_le := first [cbn; lia | match goal with |- ?f ?ts ≤ ?f ?ts' =>
  let H := fresh in assert (H : f ts' = f ts) by proj_eq; rewrite H; lia end].
Ltac core_frame := match goal with H : core ?l ?ts |- core ?l ?ts' =>
  apply (frame l ts ts'); [proj_eq|proj_le|proj_le|proj_eq|proj_eq|exact H] end.

#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_both VMViews.mem_set_both VMViews.iis_set_both
  VMViews.state_set_mem VMViews.mem_set_mem VMViews.iis_set_mem : pp_remove_core.
Ltac simpl_pp := unfold setv in *; autorewrite with pp_remove_core in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Lemma read_pte_core l pp pp' value : core l (PPState.state pp) →
  Exec.elem_of_results (pp', value) (read_pte pp) → core l (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold read_pte in Hrun.
  VMViews.invert; subst; simpl_pp; core_frame.
Qed.
Lemma read_mem_core l addr size macc pp pp' value : core l (PPState.state pp) →
  Exec.elem_of_results (pp', value) (read_mem_explicit imem addr size macc pp) → core l (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold read_mem_explicit in Hrun.
  VMViews.invert; subst; simpl_pp; core_frame.
Qed.

Lemma write_mem_core tid l addr size macc data pp pp' value : PPState.mem pp = l ++ e :: r →
  core l (PPState.state pp) → Exec.elem_of_results (pp', value) (write_mem tid imem addr size macc data pp) →
  ∃ l', PPState.mem pp' = l' ++ e :: r ∧ core l' (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold write_mem in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: try match goal with H : TState.process_event ?tid imem (?ev :: ?prefix ++ e :: r) ?ev ?before = Ok ?after |- _ =>
    assert (Hafter : core (ev :: prefix) after) by (eapply process_event; [exact Hok|exact H]) end.
  all: match goal with H : core ?prefix ?before |- _ =>
    exists prefix; split; [reflexivity|core_frame] end.
Qed.
Lemma materialize_core tid l pre event recipient pp pp' value : PPState.mem pp = l ++ e :: r →
  core l (PPState.state pp) →
  Exec.elem_of_results (pp', value) (materialize_tlbi_for_recipient tid imem pre event recipient pp) →
  ∃ l', PPState.mem pp' = l' ++ e :: r ∧ core l' (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold materialize_tlbi_for_recipient in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: try match goal with H : TState.process_event ?tid imem (?ev :: ?prefix ++ e :: r) ?ev ?before = Ok ?after |- _ =>
    assert (Hafter : core (ev :: prefix) after) by (eapply process_event; [exact Hok|exact H]) end.
  all: match goal with H : core ?prefix ?before |- _ =>
    exists prefix; split; [reflexivity|core_frame] end.
Qed.

Lemma recipients_core tid pre event recipients : ∀ l acc pp pp' value,
  PPState.mem pp = l ++ e :: r → core l (PPState.state pp) →
  Exec.elem_of_results (pp', value) (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre event) acc recipients pp) →
  ∃ l', PPState.mem pp' = l' ++ e :: r ∧ core l' (PPState.state pp').
Proof.
  induction recipients as [|recipient recipients IH]; intros l acc pp pp' value Hmem Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exists l; auto.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [acc' [Hstep Htail]]].
    destruct acc as [[self other] created]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time fresh] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    destruct (materialize_core tid l pre event recipient pp mat _ Hmem Hok Hmat) as [l' [Hm' Hc']].
    eapply IH; eassumption.
Qed.

Lemma run_tlbi_core n tid l viio info pp pp' value : PPState.mem pp = l ++ e :: r →
  core l (PPState.state pp) → Exec.elem_of_results (pp', value) (run_tlbi n tid imem viio info pp) →
  ∃ l', PPState.mem pp' = l' ++ e :: r ∧ core l' (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold run_tlbi in Hrun.
  VMViews.invert; subst.
  all: match goal with H : Exec.elem_of_results (?after, ?result) (foldlM _ ?acc ?recipients ?before) |- _ =>
    destruct (recipients_core tid _ _ recipients l acc before after result eq_refl Hok H) as [l' [Hm' Hc']] end.
  all: exists l'; simpl_pp; split; [exact Hm'|core_frame].
Qed.

Lemma run_cse_core tid l vmax pp pp' value : tid ≠ rc → PPState.mem pp = l ++ e :: r →
  VMViews.ok pp → core l (PPState.state pp) → vmax ≤ length (PPState.mem pp) →
  Exec.elem_of_results (pp', value) (run_cse tid imem vmax pp) → core l (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. cbn. intros Hrc -> [Hbound Hiis] Hok Hmax Hrun. unfold run_cse in Hrun.
  VMViews.invert; subst; simpl_pp.
  match goal with H : ?v ∈ TState.cse_candidates ?pre vmax ts |- _ =>
    pose proof (VMViews.cse_candidate_le pre vmax ts v H) as Hv;
    unfold TState.cse_candidates in H; apply elem_of_seq in H end.
  eapply cse; [exact Hrc|exact Hbound|exact Hok| | |eassumption]; unfold join, join_nat in *; lia.
Qed.

Lemma run_barrier_core tid l barrier vmax pp pp' value : tid ≠ rc → PPState.mem pp = l ++ e :: r →
  VMViews.ok pp → core l (PPState.state pp) → vmax ≤ length (PPState.mem pp) →
  Exec.elem_of_results (pp', value) (run_barrier tid imem barrier vmax pp) → core l (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. cbn. intros Hrc -> Hbound Hok Hmax Hrun. unfold run_barrier in Hrun.
  VMViews.invert.
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_cse _ _ ?v ?before) |- _ =>
    exact (run_cse_core tid l v before after result Hrc eq_refl Hbound Hok Hmax H) end].
  all: subst; simpl_pp; core_frame.
Qed.

Lemma run_take_exception_core tid l fault vmax pp pp' value : tid ≠ rc → PPState.mem pp = l ++ e :: r →
  VMViews.ok pp → core l (PPState.state pp) → vmax ≤ length (PPState.mem pp) →
  Exec.elem_of_results (pp', value) (run_take_exception tid imem fault vmax pp) → core l (PPState.state pp').
Proof.
  intros Hrc Hmem Hbound Hok Hmax Hrun. unfold run_take_exception in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [inv [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [compose] in Hrun.
  destruct (IIS.inv_time (PPState.iis pp)) as [time|] eqn:Hinv.
  all: eapply run_cse_core; [exact Hrc|exact Hmem|exact Hbound|exact Hok| |exact Hrun].
  - eapply VMViews.ok_inv_time; [apply Hbound|exact Hinv].
  - exact Hmax.
Qed.
Lemma run_reg_read_core l reg racc st st' value : core l st.1 →
  Exec.elem_of_results (st', value) (run_reg_read reg racc st) → core l st'.1.
Proof. intros Hok Hrun. rewrite (VMSwapPos.run_reg_read_pos _ _ _ _ _ Hrun). exact Hok. Qed.

Lemma run_trans_end_core l trans st st' value : core l st.1 →
  Exec.elem_of_results (st', value) (run_trans_end trans st) → core l st'.1.
Proof.
  destruct st as [ts iis]. intros Hok Hrun. unfold run_trans_end in Hrun.
  VMViews.invert; subst; simpl_pp; core_frame.
Qed.

Lemma run_trans_start_core tid l start pp pp' value : core l (PPState.state pp) →
  Exec.elem_of_results (pp', value) (run_trans_start tid imem start pp) → core l (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. intros Hok Hrun. unfold run_trans_start in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: try (match goal with H : Exec.elem_of_results _ (read_sreg_indirect _ _ _) |- _ =>
    unfold read_sreg_indirect in H; VMViews.invert; subst; simpl_pp end).
  all: core_frame.
Qed.

Lemma run_reg_write_core tid l reg racc val pp pp' value : tid ≠ rc → PPState.mem pp = l ++ e :: r →
  VMViews.ok pp → core l (PPState.state pp) →
  Exec.elem_of_results (pp', value) (run_reg_write tid imem reg racc val pp) → core l (PPState.state pp').
Proof.
  destruct pp as [ts mem iis]. cbn. intros Hrc -> [Hbound Hiis] Hok Hrun. unfold run_reg_write in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: VMViews.facts Hbound; VMViews.facts Hiis.
  all: try match goal with H : TState.read_sreg_direct _ _ = Some ?vv |- _ =>
    pose proof (VMViews.read_sreg_direct_ok _ _ _ _ Hbound H) as Hview; cbn [snd] in Hview end.
  all: try solve [match goal with H : TState.add_wsreg _ _ _ ?reg ?val ?v ?before = Ok ?after |- _ =>
    eapply (add_wsreg _ _ reg val v before after); [exact Hrc|exact Hbound|exact Hok| | |exact H];
      unfold join, join_nat in *; lia end].
  all: match goal with H : TState.set_reg ?reg ?vv ?before = Some ?after |- _ =>
    assert (Hbefore : core l before) by core_frame;
    assert (Hafter : core l after) by
      first [eapply set_reg_strict; [eassumption|exact Hbefore|exact H]
      |match goal with He : bool_decide (reg = pc_reg) = true |- _ =>
        apply bool_decide_eq_true in He; subst reg; eapply set_reg_pc; eassumption end] end.
  all: first [core_frame|apply update_vmsr, Hafter].
Qed.
Lemma run_outcome_core n (tid : fin n) l out pp pp' value : fin_to_nat tid ≠ rc →
  PPState.mem pp = l ++ e :: r → VMViews.ok pp → core l (PPState.state pp) →
  Exec.elem_of_results (pp', value) (run_outcome n tid imem out pp) →
  ∃ l', PPState.mem pp' = l' ++ e :: r ∧ core l' (PPState.state pp').
Proof.
  intros Hrc Hmem Hbound Hok H. funelim (run_outcome n tid imem out pp).
  all: rewrite <- Heqcall in H.
  all: VMViews.invert; subst.
  all: try solve [eapply write_mem_core; eassumption].
  all: try solve [eapply run_tlbi_core; eassumption].
  all: exists l; split.
  all: try solve [simpl_pp; exact Hmem].
  all: try solve [etransitivity;
    [first [solve [eapply VMMemoryGrowth.read_mem_preserves_mem; eassumption]
      | solve [eapply VMMemoryGrowth.read_pte_preserves_mem; eassumption]
      | solve [eapply VMMemoryGrowth.reg_write_preserves_mem; eassumption]
      | solve [eapply VMMemoryGrowth.cse_preserves_mem; eassumption]
      | solve [eapply VMMemoryGrowth.barrier_preserves_mem; eassumption]
      | solve [eapply VMMemoryGrowth.trans_start_preserves_mem; eassumption]
      | solve [eapply VMMemoryGrowth.take_exception_preserves_mem; eassumption]]|exact Hmem]].
  all: try solve [eapply read_mem_core; eassumption].
  all: try solve [eapply read_pte_core; eassumption].
  all: try solve [eapply run_trans_start_core; eassumption].
  all: try solve [eapply run_reg_write_core; [exact Hrc|exact Hmem|exact Hbound|exact Hok|eassumption]].
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_cse ?ti _ ?v ?before) |- _ =>
    exact (run_cse_core ti l v before after result Hrc Hmem Hbound Hok (Nat.le_refl _) H) end].
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_barrier ?ti _ ?bar ?v ?before) |- _ =>
    exact (run_barrier_core ti l bar v before after result Hrc Hmem Hbound Hok (Nat.le_refl _) H) end].
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_take_exception ?ti _ ?fault ?v ?before) |- _ =>
    exact (run_take_exception_core ti l fault v before after result Hrc Hmem Hbound Hok (Nat.le_refl _) H) end].
  all: simpl_pp.
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_reg_read ?reg ?racc ?before) |- _ =>
    exact (run_reg_read_core l reg racc before after result Hok H) end].
  all: try solve [match goal with H : Exec.elem_of_results (?after, ?result) (run_trans_end ?trans ?before) |- _ =>
    exact (run_trans_end_core l trans before after result Hok H) end].
  all: core_frame.
Qed.
Theorem instruction_core n (tid : fin n) {A} (mon : iMon A) : fin_to_nat tid ≠ rc →
  ∀ l pp pp' value, PPState.mem pp = l ++ e :: r → VMViews.ok pp → core l (PPState.state pp) →
  Exec.elem_of_results (pp', value) (cinterp (run_outcome' n tid imem) mon pp) →
  ∃ l', PPState.mem pp' = l' ++ e :: r ∧ core l' (PPState.state pp').
Proof.
  intros Hrc. induction mon as [a|call k IH]; intros l pp pp' value Hmem Hbound Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exists l; auto.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[ret pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (run_outcome_core n tid l out pp mid _ Hrc Hmem Hbound Hok Hout) as [l' [Hm' Hc']].
      eapply IH; [exact Hm'|eapply VMViews.run_outcome_ok; eassumption|exact Hc'|exact Htail].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.
End Removed.
End VMSwapRemoveCore.
