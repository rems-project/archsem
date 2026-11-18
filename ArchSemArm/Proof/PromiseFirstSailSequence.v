(******************************************************************************)
(* UM execution invariants and replay across fulfilled promises               *)
(******************************************************************************)

(** These lemmas use the concrete UM outcome handler. A run with unchanged
    history may include arbitrarily many fulfilled writes. A run that adds
    exactly one message can replay from a state that already promises it. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstExecutionCurrent
  PromiseFirstSailExecution PromiseFirstSailRead PromiseFirstSailControl
  PromiseFirstSailReplay PromiseFirstSailInstruction PromiseFirstSailFulfilled.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module UMContinuation.
Import UMPromising UMReadReplay UMControlReplay UMFulfilledReplay.
#[local] Typeclasses Transparent Memory.t othrow.

Lemma set_fwdbs_only_fwdb addrs n (data : bv n) time vdata xcl ts :
  TState.set_fwdbs addrs data time vdata xcl ts =
  setv TState.fwdb (TState.fwdb (TState.set_fwdbs addrs data time vdata xcl ts)) ts.
Proof.
  unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)).
  intro pairs. revert ts. induction pairs as [|[addr byte] pairs IH]; intro ts; cbn.
  - destruct ts. reflexivity.
  - rewrite IH. destruct ts. reflexivity.
Qed.

Lemma write_mem_order_view_monotone tid addr size macc data ppst ppst' pre :
  Exec.elem_of_results (ppst', pre) (write_mem tid addr size macc data ppst) →
  order_view ppst ≤ order_view ppst'.
Proof.
  destruct ppst as [ts mem iis]. intro Hrun. unfold write_mem in Hrun.
  UMMemoryGrowth.invert_execution; subst.
  all: unfold order_view, TState.min_new_prom_view; cbn.
  all: rewrite set_fwdbs_only_fwdb; cbn.
  all: rewrite update_cohs_only_coh; cbn.
  all: destruct ts, iis; cbn; unfold join, join_nat.
  all: repeat first [apply Nat.le_refl | apply Nat.max_le_compat | apply Nat.le_max_r | apply Nat.le_max_l].
Qed.

Lemma write_mem_pending_subset tid addr size macc data ppst ppst' pre :
  Exec.elem_of_results (ppst', pre) (write_mem tid addr size macc data ppst) →
  ∀ p ∈ TState.prom (PPState.state ppst'), p ∈ TState.prom (PPState.state ppst).
Proof.
  destruct ppst as [ts mem iis]. intro Hrun. unfold write_mem in Hrun.
  UMMemoryGrowth.invert_execution; subst.
  all: cbn; rewrite set_fwdbs_only_fwdb; cbn.
  all: rewrite update_cohs_only_coh; cbn.
  all: destruct ts, iis; cbn; intros p Hin;
    apply list_elem_of_filter in Hin as [_ Hin]; exact Hin.
Qed.

Lemma read_mem_pending_same addr size macc imem ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (read_mem addr size macc imem ppst) →
  TState.prom (PPState.state ppst') = TState.prom (PPState.state ppst).
Proof.
  destruct ppst as [ts mem iis]. intro Hrun. unfold read_mem in Hrun.
  UMMemoryGrowth.invert_execution; subst.
  all: cbn; rewrite update_cohs_only_coh; destruct ts; reflexivity.
Qed.

Lemma set_reg_pending_same reg rv ts ts' :
  TState.set_reg reg rv ts = Some ts' → TState.prom ts' = TState.prom ts.
Proof.
  unfold TState.set_reg.
  match goal with |- context[if ?b then _ else _] => destruct b end;
    [|discriminate].
  intro H. injection H as <-. destruct ts. reflexivity.
Qed.

Lemma outcome_order_view_monotone_all tid imem out ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  order_view ppst ≤ order_view ppst'.
Proof.
  intro Hrun. funelim (run_outcome tid imem out ppst).
  all: rewrite <- Heqcall in Hrun.
  all: UMMemoryGrowth.invert_execution; subst.
  all: try solve [eapply read_mem_order_view_monotone; eassumption].
  all: try solve [eapply write_mem_order_view_monotone; eassumption].
  all: unfold order_view; cbn.
  all: try match goal with
  | H : TState.set_reg _ _ _ = Some _ |- _ =>
    rewrite (set_reg_min_view _ _ _ _ H)
  end.
  all: unfold TState.min_new_prom_view; cbn.
  all: try match goal with pp : PPState.t _ _ _ |- _ => destruct pp as [ts mem iis] end.
  all: cbn; unfold join, join_nat.
  all: repeat first [apply Nat.le_refl | apply Nat.max_le_compat | apply Nat.le_max_r | apply Nat.le_max_l].
Qed.

Lemma outcome_pending_subset tid imem out ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  ∀ p ∈ TState.prom (PPState.state ppst'), p ∈ TState.prom (PPState.state ppst).
Proof.
  intro Hrun. funelim (run_outcome tid imem out ppst).
  all: rewrite <- Heqcall in Hrun.
  all: UMMemoryGrowth.invert_execution; subst.
  all: try solve [eapply write_mem_pending_subset; eassumption].
  all: try match goal with
  | H : Exec.elem_of_results _ (read_mem _ _ _ _ _) |- _ =>
    rewrite (read_mem_pending_same _ _ _ _ _ _ _ H); auto
  end.
  all: cbn.
  all: try match goal with
  | H : TState.set_reg _ _ _ = Some _ |- _ =>
    rewrite (set_reg_pending_same _ _ _ _ H)
  end.
  all: try match goal with pp : PPState.t _ _ _ |- _ => destruct pp as [ts mem iis] end.
  all: cbn; auto.
Qed.
Lemma read_mem_min_view_monotone addr size macc imem ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (read_mem addr size macc imem ppst) →
  TState.min_new_prom_view (PPState.state ppst) ≤ TState.min_new_prom_view (PPState.state ppst').
Proof.
  destruct ppst as [ts mem iis]. intro Hrun. unfold read_mem in Hrun.
  UMMemoryGrowth.invert_execution.
  all: unfold TState.min_new_prom_view; cbn.
  all: rewrite update_cohs_only_coh.
  all: destruct ts, iis; cbn.
  all: unfold join, join_nat.
  all: repeat first [apply Nat.max_le_compat | apply Nat.le_refl | apply Nat.le_max_r | apply Nat.le_max_l].
Qed.
Lemma write_mem_min_view_monotone tid addr size macc data ppst ppst' pre :
  Exec.elem_of_results (ppst', pre) (write_mem tid addr size macc data ppst) →
  TState.min_new_prom_view (PPState.state ppst) ≤ TState.min_new_prom_view (PPState.state ppst').
Proof.
  destruct ppst as [ts mem iis]. intro Hrun. unfold write_mem in Hrun.
  UMMemoryGrowth.invert_execution; subst.
  all: unfold TState.min_new_prom_view; cbn.
  all: rewrite set_fwdbs_only_fwdb; cbn.
  all: rewrite update_cohs_only_coh; cbn.
  all: destruct ts, iis; cbn; unfold join, join_nat.
  all: repeat first [apply Nat.le_refl | apply Nat.max_le_compat | apply Nat.le_max_r | apply Nat.le_max_l].
Qed.
Lemma outcome_min_view_monotone tid imem out ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  TState.min_new_prom_view (PPState.state ppst) ≤ TState.min_new_prom_view (PPState.state ppst').
Proof.
  intro Hrun. funelim (run_outcome tid imem out ppst).
  all: rewrite <- Heqcall in Hrun.
  all: UMMemoryGrowth.invert_execution; subst.
  all: try solve [eapply read_mem_min_view_monotone; eassumption].
  all: try solve [eapply write_mem_min_view_monotone; eassumption].
  all: cbn.
  all: try match goal with
  | H : TState.set_reg _ _ _ = Some _ |- _ =>
    rewrite (set_reg_min_view _ _ _ _ H)
  end.
  all: unfold TState.min_new_prom_view; cbn.
  all: try match goal with pp : PPState.t _ _ _ |- _ => destruct pp as [ts mem iis] end.
  all: cbn; unfold join, join_nat.
  all: repeat first [apply Nat.le_refl | apply Nat.max_le_compat | apply Nat.le_max_r | apply Nat.le_max_l].
Qed.

Definition pending_bounded (ppst : PPState.t TState.t Msg.t IIS.t) : Prop :=
  ∀ p ∈ TState.prom (PPState.state ppst), p ≤ length (PPState.mem ppst).

Lemma outcome_pending_bounded {n} (tid : fin n) imem out ppst ppst' ret pre :
  pending_bounded ppst →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  pending_bounded ppst'.
Proof.
  intros Hbound Hrun p Hin.
  pose proof (outcome_pending_subset _ _ _ _ _ _ _ Hrun p Hin) as Hbefore.
  specialize (Hbound p Hbefore).
  destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst ppst' ret pre Hrun)
    as [Hsame|[extra [vpre [_ [Hmem _]]]]].
  - rewrite Hsame. exact Hbound.
  - rewrite Hmem, length_app. eapply Nat.le_trans; [exact Hbound|apply Nat.le_add_l].
Qed.

Lemma unchanged_outcome_after_promise tid imem out msg ppst ppst' ret pre :
  pending_bounded ppst →
  fetch_preserved imem msg ppst out →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  PPState.mem ppst' = PPState.mem ppst →
  TState.min_new_prom_view (PPState.state ppst') < S (length (PPState.mem ppst)) →
  let p := S (length (PPState.mem ppst)) in
  Exec.elem_of_results (add_pending_message msg p ppst', (ret, pre))
    (run_outcome tid imem out (add_pending_message msg p ppst)).
Proof.
  intros Hbound Hfetch Hrun Hmem Hview.
  assert (Hpre : pre = None).
  { destruct pre as [vpre|]; [|reflexivity].
    destruct (UMSailReplay.run_outcome_promise_replay_one tid imem out ppst ppst'
      ret vpre Hrun) as [ev [Hnew _]].
    rewrite Hmem in Hnew. apply (f_equal length) in Hnew. cbn in Hnew. lia. }
  subst pre.
  destruct out as [reg racc|reg racc val|req|req|req val tags|barrier|cop|tlbi|exn| |trans|trans|err];
    try solve [eapply no_update_outcome_after_promise_min; [exact I|exact Hfetch|exact Hrun|exact Hview]].
  - destruct req as [macc addr pas size taglen]. destruct taglen as [|taglen].
    + simp run_outcome in Hrun |- *.
      apply Exec.elem_of_bind_elim in Hrun as [mid [Hpas [Hguard Hrun]]].
      apply Exec.elem_of_guard_or_inv in Hguard as ->.
      apply Exec.elem_of_bind_elim in Hrun as [mid [Hexpl [Hguard Hrun]]].
      apply Exec.elem_of_guard_or_inv in Hguard as ->.
      apply Exec.elem_of_bind_elim in Hrun as [mid [pre [Hwrite Hrun]]].
      apply Exec.elem_of_mret_inv in Hrun as [-> Heq]. inversion Heq; subst.
      eapply exec_guard_or_bind_intro; [reflexivity|].
      eapply exec_guard_or_bind_intro; [exact Hexpl|].
      eapply Exec.elem_of_bind_intro.
      * eapply write_mem_fulfilled_after_promise; [exact Hbound|exact Hwrite].
      * apply Exec.elem_of_mret.
    + simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
  - simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
Qed.

Lemma instruction_facts {n A} (tid : fin n) imem (mon : iMon A) ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  order_view ppst ≤ order_view ppst' ∧
  (∀ p ∈ TState.prom (PPState.state ppst'), p ∈ TState.prom (PPState.state ppst)) ∧
  (∃ extra, PPState.mem ppst' = (extra ++ PPState.mem ppst)%list).
Proof.
  revert ppst ppst' ret. induction mon as [r|call k IH]; intros ppst ppst' ret Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _].
    repeat split; try lia; try auto. exists []. reflexivity.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]].
      cbn in Heq. subst res.
      destruct (IH r mid ppst' ret Htail) as [Hview [Hprom [extra Hmem]]].
      split.
      * pose proof (outcome_order_view_monotone_all _ _ _ _ _ _ _ Hout). lia.
      * split.
        -- intros p Hin. eapply outcome_pending_subset; [exact Hout|apply Hprom, Hin].
        -- destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst mid r pre Hout)
             as [Hsame|[added [vpre [_ [Hadded _]]]]].
           ++ exists extra. rewrite Hmem, Hsame. reflexivity.
           ++ exists (extra ++ added)%list. rewrite Hmem, Hadded, app_assoc. reflexivity.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->. eapply IH, Htail.
Qed.

Lemma instruction_pending_bounded {n A} (tid : fin n) imem (mon : iMon A) ppst ppst' ret :
  pending_bounded ppst →
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  pending_bounded ppst'.
Proof.
  intros Hbound Hrun p Hin.
  destruct (instruction_facts tid imem mon ppst ppst' ret Hrun) as [_ [Hprom [extra Hmem]]].
  specialize (Hbound p (Hprom p Hin)). rewrite Hmem, length_app. lia.
Qed.

Lemma instruction_min_view_monotone {n A} (tid : fin n) imem (mon : iMon A) ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  TState.min_new_prom_view (PPState.state ppst) ≤ TState.min_new_prom_view (PPState.state ppst').
Proof.
  revert ppst ppst' ret. induction mon as [a|call k IH]; intros ppst ppst' ret Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. lia.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      pose proof (outcome_min_view_monotone _ _ _ _ _ _ _ Hout).
      specialize (IH r mid ppst' ret Htail). lia.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->. eapply IH, Htail.
Qed.

Lemma unchanged_instruction_replay {n A} (tid : fin n) imem msg (mon : iMon A)
    ppst ppst' ret :
  pending_bounded ppst →
  UMInstructionReplay.preserved_fetches tid imem msg mon ppst →
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  PPState.mem ppst' = PPState.mem ppst →
  TState.min_new_prom_view (PPState.state ppst') < S (length (PPState.mem ppst)) →
  Exec.elem_of_results (add_pending_message msg (S (length (PPState.mem ppst))) ppst', ret)
    (cinterp (run_outcome' tid imem) mon
      (add_pending_message msg (S (length (PPState.mem ppst))) ppst)).
Proof.
  revert ppst ppst' ret.
  induction mon as [a|call k IH]; intros ppst ppst' ret Hpending Hfetch Hrun Hmem Hbound.
  - cbn in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    apply Exec.elem_of_mret.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]].
      cbn in Heq. subst res.
      destruct Hfetch as [Hfetch Hfetch_tail].
      destruct (instruction_facts tid imem (k r) mid ppst' ret Htail)
        as [Horder [_ [extra Hsuffix]]].
      pose proof (instruction_min_view_monotone tid imem (k r) mid ppst' ret Htail) as Hview.
      assert (Hmidmem : PPState.mem mid = PPState.mem ppst).
      { destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst mid r pre Hout)
          as [Hsame|[added [vpre [Hnonempty [Hadded _]]]]]; [exact Hsame|].
        rewrite Hadded, Hmem in Hsuffix.
        apply (f_equal length) in Hsuffix. rewrite !length_app in Hsuffix.
        destruct added; [contradiction|cbn in Hsuffix; lia]. }
      eapply Exec.elem_of_bind_intro with
        (st' := add_pending_message msg (S (length (PPState.mem ppst))) mid) (a := r).
      * unfold run_outcome'. eapply Exec.elem_of_fmap_intro with (a := (r, pre)) (f := fst).
        eapply unchanged_outcome_after_promise; try eassumption. lia.
      * rewrite <- Hmidmem. eapply IH.
        -- eapply outcome_pending_bounded; eassumption.
        -- eapply Hfetch_tail; exact Hout.
        -- exact Htail.
        -- congruence.
        -- rewrite Hmidmem. exact Hbound.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|].
      eapply IH; eauto.
Qed.

(** The run may fulfill any number of older promises. Its history records
    exactly one new message; the theorem moves that message to its start. *)
Lemma single_new_message_replay {n A} (tid : fin n) imem msg (mon : iMon A)
    ppst ppst' ret :
  pending_bounded ppst →
  UMInstructionReplay.preserved_fetches tid imem msg mon ppst →
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  PPState.mem ppst' = msg :: PPState.mem ppst →
  order_view ppst < S (length (PPState.mem ppst)) ∧
  Exec.elem_of_results (ppst', ret)
    (cinterp (run_outcome' tid imem) mon
      (add_pending_message msg (S (length (PPState.mem ppst))) ppst)).
Proof.
  revert ppst ppst' ret.
  induction mon as [a|call k IH]; intros ppst ppst' ret Hpending Hfetch Hrun Hmem.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _].
    apply (f_equal length) in Hmem. cbn in Hmem. lia.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]].
      cbn in Heq. subst res. destruct Hfetch as [Hfetch Hfetch_tail].
      destruct (decide (PPState.mem mid = PPState.mem ppst)) as [Hmidmem|Hchanged].
      * assert (Htailmem : PPState.mem ppst' = msg :: PPState.mem mid) by congruence.
        assert (Hpending_mid : pending_bounded mid) by (eapply outcome_pending_bounded; eassumption).
        destruct (IH r mid ppst' ret Hpending_mid (Hfetch_tail _ _ _ Hout) Htail Htailmem)
          as [Hbound Hreplay].
        rewrite Hmidmem in Hbound, Hreplay. split.
        -- pose proof (outcome_order_view_monotone_all _ _ _ _ _ _ _ Hout). lia.
        -- eapply Exec.elem_of_bind_intro with
             (st' := add_pending_message msg (S (length (PPState.mem ppst))) mid) (a := r).
           ++ unfold run_outcome'. eapply Exec.elem_of_fmap_intro with (a := (r, pre)) (f := fst).
              eapply unchanged_outcome_after_promise; try eassumption.
              eapply Nat.le_lt_trans; [apply Nat.le_max_r|exact Hbound].
           ++ exact Hreplay.
      * destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst mid r pre Hout)
          as [Hsame|[added [vpre [_ [_ [Hpre Hprebound]]]]]]; [contradiction|].
        subst pre.
        destruct (UMSailReplay.run_outcome_promise_replay_one tid imem out ppst mid r vpre Hout)
          as [ev [Hmid [Howner [Hprebound' Hreplay]]]].
        destruct (instruction_facts tid imem (k r) mid ppst' ret Htail)
          as [_ [_ [extra Hsuffix]]].
        assert (Hextra : extra = []).
        { rewrite Hmid, Hmem in Hsuffix. apply (f_equal length) in Hsuffix.
          rewrite length_app in Hsuffix. cbn in Hsuffix.
          destruct extra; [reflexivity|cbn in Hsuffix; lia]. }
        subst extra. cbn in Hsuffix.
        rewrite Hsuffix, Hmid in Hmem. injection Hmem as Hev. subst ev.
        split.
        -- pose proof (UMSailReplay.run_outcome_new_order_view_bound
             tid imem out ppst mid r vpre Hout). unfold order_view. lia.
        -- eapply Exec.elem_of_bind_intro with (st' := mid) (a := r).
           ++ unfold run_outcome'. eapply Exec.elem_of_fmap_intro with (a := (r, None)) (f := fst).
              exact Hreplay.
           ++ exact Htail.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->.
      destruct (IH r ppst ppst' ret Hpending (Hfetch r) Htail Hmem) as [Hbound Hreplay].
      split; [exact Hbound|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|exact Hreplay].
Qed.

End UMContinuation.
