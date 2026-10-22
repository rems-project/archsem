(******************************************************************************)
(* Certifying the first new message of a finite UM instruction sequence       *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstConcreteCurrent PromiseFirstExecutionCurrent PromiseFirstSailCurrent
  PromiseFirstSailExecution PromiseFirstSailReplay PromiseFirstSailSequence
  PromiseFirstSailThread PromiseFirstSailCertification.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module UMThreadCertification.
Import UMPromising UMContinuation UMThreadReplay.
#[local] Typeclasses Transparent Memory.t UMPromising
  Promising.mEvent Promising.tState Promising.iis.

Lemma collect_unchanged_outcome {n} (tid : fin n) imem out proms ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  PPState.mem ppst' = PPState.mem ppst →
  Exec.elem_of_results ((proms, ppst'), ret)
    (CPState.run_outcome_with_promise UMPromising tid imem
      (length (PPState.mem ppst)) out (proms, ppst)).
Proof.
  intros Hout Hmem.
  pose proof (collect_outcome_intro UMPromising tid imem
    (length (PPState.mem ppst)) out proms ppst ppst' ret pre Hout) as Hcollect.
  rewrite Hmem, Nat.sub_diag in Hcollect. cbn [take app] in Hcollect.
  destruct pre as [pre|]; [destruct (decide (pre ≤ length (PPState.mem ppst)))|];
    exact Hcollect.
Qed.

Lemma collect_unchanged_instruction {n A} (tid : fin n) imem (mon : iMon A)
    proms ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  PPState.mem ppst' = PPState.mem ppst →
  Exec.elem_of_results ((proms, ppst'), ret)
    (cinterp (CPState.run_outcome_with_promise UMPromising tid imem
      (length (PPState.mem ppst))) mon (proms, ppst)).
Proof.
  revert proms ppst ppst' ret.
  induction mon as [a|call k IH]; intros proms ppst ppst' ret Hrun Hmem.
  - cbn in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    apply Exec.elem_of_mret.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (instruction_facts tid imem (k r) mid ppst' ret Htail)
        as [_ [_ [extra Hsuffix]]].
      assert (Hmid : PPState.mem mid = PPState.mem ppst).
      { destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst mid r pre Hout)
          as [Hsame|[added [vpre [Hnonempty [Hadded _]]]]]; [exact Hsame|].
        rewrite Hadded, Hmem in Hsuffix. apply (f_equal length) in Hsuffix.
        rewrite !length_app in Hsuffix. destruct added; [contradiction|cbn in Hsuffix; lia]. }
      eapply Exec.elem_of_bind_intro.
      * eapply collect_unchanged_outcome; eassumption.
      * rewrite <- Hmid. eapply IH; [exact Htail|congruence].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|].
      eapply IH; eassumption.
Qed.

Lemma collect_first_new_instruction {n A} (tid : fin n) imem (mon : iMon A)
    proms ppst ppst' ret msg :
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  PPState.mem ppst' = msg :: PPState.mem ppst →
  ∃ proms', msg ∈ proms' ∧ Exec.elem_of_results ((proms', ppst'), ret)
    (cinterp (CPState.run_outcome_with_promise UMPromising tid imem
      (length (PPState.mem ppst))) mon (proms, ppst)).
Proof.
  revert proms ppst ppst' ret.
  induction mon as [a|call k IH]; intros proms ppst ppst' ret Hrun Hmem.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _].
    apply (f_equal length) in Hmem. cbn in Hmem. lia.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (decide (PPState.mem mid = PPState.mem ppst)) as [Hsame|Hchanged].
      * destruct (IH r proms mid ppst' ret Htail ltac:(congruence))
          as [proms' [Hin Hcollect]].
        exists proms'. split; [exact Hin|].
        eapply Exec.elem_of_bind_intro.
        -- eapply collect_unchanged_outcome; eassumption.
        -- rewrite <- Hsame. exact Hcollect.
      * destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst mid r pre Hout)
          as [Hsame|[added [vpre [_ [_ [Hpre Hbound]]]]]]; [contradiction|].
        subst pre.
        destruct (UMSailReplay.run_outcome_promise_replay_one tid imem out ppst mid r vpre Hout)
          as [ev [Hmid _]].
        destruct (instruction_facts tid imem (k r) mid ppst' ret Htail)
          as [_ [_ [extra Hsuffix]]].
        assert (Hextra : extra = []).
        { rewrite Hmid, Hmem in Hsuffix. apply (f_equal length) in Hsuffix.
          rewrite length_app in Hsuffix. cbn in Hsuffix.
          destruct extra; [reflexivity|cbn in Hsuffix; lia]. }
        subst extra. cbn in Hsuffix.
        rewrite Hsuffix, Hmid in Hmem. injection Hmem as Hev. subst ev.
        pose proof (collect_outcome_intro UMPromising tid imem
          (length (PPState.mem ppst)) out proms ppst mid r (Some vpre) Hout) as Hcollect.
        rewrite decide_True in Hcollect by exact Hbound.
        rewrite Hmid in Hcollect. cbn [length] in Hcollect.
        replace (S (length (PPState.mem ppst)) - length (PPState.mem ppst)) with 1 in Hcollect by lia.
        cbn [take app] in Hcollect.
        destruct (collect_instruction_complete UMPromising tid imem
          (length (PPState.mem ppst)) (k r) (msg :: proms) mid ppst' ret Htail)
          as [proms' Hcollect_tail].
        exists proms'. split.
        -- destruct (collect_instruction_suffix UMPromising tid imem
             (length (PPState.mem ppst)) (k r) _ _ _ _ _ Hcollect_tail) as [rest Hrest].
           rewrite Hrest. apply elem_of_app. right. left; reflexivity.
        -- eapply Exec.elem_of_bind_intro; eassumption.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      destruct (IH r proms ppst ppst' ret Htail Hmem) as [proms' [Hin Hcollect]].
      exists proms'. split; [exact Hin|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|exact Hcollect].
Qed.

Lemma instruction_new_message_min_bound {n A} (tid : fin n) imem (mon : iMon A)
    ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  PPState.mem ppst' ≠ PPState.mem ppst →
  TState.min_new_prom_view (PPState.state ppst) ≤ length (PPState.mem ppst).
Proof.
  revert ppst ppst' ret.
  induction mon as [a|call k IH]; intros ppst ppst' ret Hrun Hchanged.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. contradiction.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (decide (PPState.mem mid = PPState.mem ppst)) as [Hsame|Hnew].
      * pose proof (IH r mid ppst' ret Htail ltac:(congruence)) as Hbound.
        pose proof (outcome_min_view_monotone tid imem out ppst mid r pre Hout) as Hmono.
        rewrite Hsame in Hbound. lia.
      * destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst mid r pre Hout)
          as [Hsame|[added [vpre [_ [_ [Hpre Hprebound]]]]]]; [contradiction|].
        subst pre.
        pose proof (UMSailReplay.run_outcome_new_order_view_bound tid imem out ppst mid r vpre Hout)
          as Hbound.
        unfold join, join_nat in Hbound.
        eapply Nat.le_trans; [|exact Hprebound].
        eapply Nat.le_trans; [apply Nat.le_max_r|exact Hbound].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

Lemma thread_new_message_min_bound {n} (tid : fin n) imem bps isem
    count ts mem fin finmem :
  thread_steps tid imem bps isem count ts mem fin finmem →
  finmem ≠ mem → TState.min_new_prom_view ts ≤ length mem.
Proof.
  intro Hsteps.
  induction Hsteps as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intro Hchanged; [contradiction|].
  destruct (decide (midmem = mem)) as [Hsame|Hnew].
  - subst midmem. specialize (IH Hchanged).
    pose proof (instruction_min_view_monotone tid imem isem _ _ _ Hinst) as Hmono.
    cbn in Hmono. lia.
  - exact (instruction_new_message_min_bound tid imem isem _ _ _ Hinst Hnew).
Qed.

Lemma thread_steps_middle_memory {n} (tid : fin n) imem bps isem
    count ts mem mid midmem fin finmem iis :
  Exec.elem_of_results (PPState.Make mid midmem iis, ())
    (cinterp (run_outcome' tid imem) isem (PPState.Make ts mem IIS.init)) →
  thread_steps tid imem bps isem count mid midmem fin finmem →
  (finmem = mem → midmem = mem) ∧
  (∀ msg, finmem = msg :: mem → midmem = mem ∨ midmem = msg :: mem).
Proof.
  intros Hinst Htail.
  destruct (instruction_facts tid imem isem _ _ _ Hinst) as [_ [_ [first Hfirst]]].
  destruct (thread_steps_suffix tid imem bps isem _ _ _ _ _ Htail) as [rest Hrest].
  cbn in Hfirst. split.
  - intro Hsame.
    assert (Hnil : first = []).
    { rewrite Hfirst, Hsame in Hrest. apply (f_equal length) in Hrest.
      rewrite !length_app in Hrest. destruct first; [reflexivity|cbn in Hrest; lia]. }
    subst first. exact Hfirst.
  - intros msg Hmem. destruct first as [|ev first]; [left; exact Hfirst|].
    assert (Hnil : rest = [] ∧ first = []).
    { rewrite Hfirst, Hmem in Hrest. apply (f_equal length) in Hrest.
      rewrite length_app in Hrest. cbn in Hrest. rewrite length_app in Hrest.
      split; [destruct rest|destruct first]; try reflexivity; cbn in Hrest; lia. }
    destruct Hnil as [-> ->]. cbn in Hrest. right. congruence.
Qed.

(** The chosen instruction prefix either reaches its end or stops after the
    first message because the prerequisite view has passed the original
    history. In both cases enumeration retains that message. *)
Lemma first_new_message_certification_aux {n} (tid : fin n) imem
    (term : terminationCondition n) isem count ts mem fin finmem :
  thread_steps tid imem (term !!! tid) isem count ts mem fin finmem →
  ∀ base_mem msg proms iis,
  finmem = msg :: base_mem →
  (mem = base_mem ∨ (mem = msg :: base_mem ∧ msg ∈ proms)) →
  ∃ proms' ppst' ending,
    msg ∈ proms' ∧
    (CPState.terminated_ts UMPromising (term !!! tid) fin = true →
      ending ≠ CPState.OutOfFuel) ∧
    Exec.elem_of_results ((proms', ppst'), ending)
      (CPState.run_to_termination isem UMPromising term tid imem count
        (length base_mem) (proms, PPState.Make ts mem iis)).
Proof.
  intro Hsteps.
  induction Hsteps as [ts mem|count ts mem mid midmem fin finmem iis0 Hterm Hinst Htail IH];
    intros base_mem msg proms iis Hfinal Hmode.
  - assert (Hin : msg ∈ proms).
    { destruct Hmode as [Hsame|[_ Hin]]; [|exact Hin].
      rewrite Hsame in Hfinal. apply (f_equal length) in Hfinal. cbn in Hfinal. lia. }
    cbn [CPState.run_to_termination].
    destruct (decide (length base_mem < TState.min_new_prom_view ts)) as [Hstop|Hcontinue].
    + eexists proms, _, CPState.StoppedEarly. split; [exact Hin|].
      split; [discriminate|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn. rewrite decide_True by exact Hstop. apply Exec.elem_of_mret.
    + destruct (CPState.terminated_ts UMPromising (term !!! tid) ts) eqn:Hterm.
      * eexists proms, _, CPState.Terminated. split; [exact Hin|].
        split; [discriminate|].
        eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
        cbn -[CPState.terminated_ts]. rewrite decide_False by exact Hcontinue.
        rewrite Hterm. apply Exec.elem_of_mret.
      * eexists proms, _, CPState.OutOfFuel. split; [exact Hin|].
        split; [discriminate|].
        eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
        cbn -[CPState.terminated_ts]. rewrite decide_False by exact Hcontinue.
        rewrite Hterm. apply Exec.elem_of_mret.
  - destruct (decide (length base_mem < TState.min_new_prom_view ts)) as [Hstop|Hcontinue].
    + assert (Hin : msg ∈ proms).
      { destruct Hmode as [Hsame|[_ Hin]]; [|exact Hin].
        assert (Hnew : finmem ≠ mem).
        { rewrite Hfinal, Hsame. intro Heq. apply (f_equal length) in Heq. cbn in Heq. lia. }
        assert (Hbound : TState.min_new_prom_view ts ≤ length mem).
        { eapply thread_new_message_min_bound; [econstructor; eassumption|exact Hnew]. }
        rewrite Hsame in Hbound. lia. }
      exists proms, (PPState.Make ts mem iis), CPState.StoppedEarly. split; [exact Hin|].
      split; [discriminate|].
      cbn [CPState.run_to_termination].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn. rewrite decide_True by exact Hstop. apply Exec.elem_of_mret.
    + assert (Hcollect : ∃ proms_mid,
        Exec.elem_of_results ((proms_mid, PPState.Make mid midmem iis0), ())
          (cinterp (CPState.run_outcome_with_promise UMPromising tid imem
            (length base_mem)) isem (proms, PPState.Make ts mem IIS.init)) ∧
        (midmem = base_mem ∨ (midmem = msg :: base_mem ∧ msg ∈ proms_mid))).
      { destruct Hmode as [Hsame|[Hsame Hin]].
        - subst mem.
          destruct (proj2 (thread_steps_middle_memory tid imem (term !!! tid)
            isem _ _ _ _ _ _ _ _ Hinst Htail) msg Hfinal) as [Hmid|Hmid].
          + exists proms. split; [|left; exact Hmid].
            exact (collect_unchanged_instruction tid imem isem proms
              (PPState.Make ts base_mem IIS.init)
              (PPState.Make mid midmem iis0) () Hinst Hmid).
          + destruct (collect_first_new_instruction tid imem isem proms _ _ _ msg Hinst Hmid)
              as [proms_mid [Hin Hcollect]].
            exists proms_mid. split; [exact Hcollect|right; split; assumption].
        - assert (Hmid : midmem = mem).
          { eapply (proj1 (thread_steps_middle_memory tid imem (term !!! tid)
              isem _ _ _ _ _ _ _ _ Hinst Htail)). congruence. }
          destruct (collect_instruction_complete UMPromising tid imem
            (length base_mem) isem proms _ _ _ Hinst) as [proms_mid Hcollect].
          exists proms_mid. split; [exact Hcollect|]. right. split; [congruence|].
          destruct (collect_instruction_suffix UMPromising tid imem
            (length base_mem) isem _ _ _ _ _ Hcollect) as [extra Hextra].
          rewrite Hextra. apply elem_of_app. right. exact Hin. }
      destruct Hcollect as [proms_mid [Hcollect Hmode_mid]].
      destruct (IH base_mem msg proms_mid iis0 Hfinal Hmode_mid)
        as [proms' [ppst' [ending [Hin [Hend Hcert]]]]].
      exists proms', ppst', ending. split; [exact Hin|]. split; [exact Hend|].
      cbn [CPState.run_to_termination].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn -[CPState.terminated_ts]. rewrite decide_False by exact Hcontinue.
      rewrite Hterm.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
      eapply Exec.elem_of_bind_intro; [exact Hcollect|exact Hcert].
Qed.

Theorem first_new_message_enumerated {n} (tid : fin n) imem
    (term : terminationCondition n) isem count ts mem fin msg :
  thread_steps tid imem (term !!! tid) isem count ts mem fin (msg :: mem) →
  msg ∈ (CPState.enumerate_results isem UMPromising term tid imem count ts mem)
    .(CPState.promises UMPromising).
Proof.
  intro Hsteps.
  destruct (first_new_message_certification_aux tid imem term isem
    _ _ _ _ _ Hsteps mem msg [] IIS.init eq_refl (or_introl eq_refl))
    as [proms [ppst [ending [Hin [_ Hcert]]]]].
  unfold CPState.enumerate_results. cbn [CPState.promises Promising.filter_promises].
  apply elem_of_remove_dups, list_elem_of_In, List.in_concat.
  exists proms. split; [|apply list_elem_of_In; exact Hin].
  apply list_elem_of_In, elem_of_app. left.
  apply list_elem_of_fmap. exists (proms, ppst). split; [reflexivity|].
  unfold Exec.success_state_list.
  apply list_elem_of_fmap. exists ((proms, ppst), ending). split; [reflexivity|exact Hcert].
Qed.

(** A terminating prefix can be replayed in certification at every larger
    fuel: the zero-step case reaches Terminated or StoppedEarly. This is
    stronger than the exact-fuel statement for a nonterminating prefix. *)
Lemma terminated_first_new_message_certification {n} (tid : fin n) imem
    (term : terminationCondition n) isem count ts mem fin finmem :
  thread_steps tid imem (term !!! tid) isem count ts mem fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  ∀ base_mem msg proms iis,
  finmem = msg :: base_mem →
  (mem = base_mem ∨ (mem = msg :: base_mem ∧ msg ∈ proms)) →
  ∃ proms' ppst' ending,
    msg ∈ proms' ∧ ending ≠ CPState.OutOfFuel ∧
    Exec.elem_of_results ((proms', ppst'), ending)
      (CPState.run_to_termination isem UMPromising term tid imem count
        (length base_mem) (proms, PPState.Make ts mem iis)).
Proof.
  intros Hsteps Hterminated base_mem msg proms iis Hfinal Hmode.
  destruct (first_new_message_certification_aux tid imem term isem
    _ _ _ _ _ Hsteps base_mem msg proms iis Hfinal Hmode)
    as [proms' [ppst' [ending [Hin [Hend Hcert]]]]].
  exists proms', ppst', ending. split; [exact Hin|].
  split; [apply Hend, Hterminated|exact Hcert].
Qed.

Lemma terminating_thread_certification {n} (tid : fin n) imem
    (term : terminationCondition n) isem count ts mem fin finmem :
  thread_steps tid imem (term !!! tid) isem count ts mem fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  ∀ base proms iis,
  ∃ proms' ppst' ending,
    (∀ msg, msg ∈ proms → msg ∈ proms') ∧ ending ≠ CPState.OutOfFuel ∧
    Exec.elem_of_results ((proms', ppst'), ending)
      (CPState.run_to_termination isem UMPromising term tid imem count base
        (proms, PPState.Make ts mem iis)).
Proof.
  intro Hsteps.
  induction Hsteps as [ts mem|count ts mem mid midmem fin finmem iis0 Hterm Hinst Htail IH];
    intros Hfinal base proms iis.
  - destruct (decide (base < TState.min_new_prom_view ts)) as [Hstop|Hcontinue].
    + exists proms, (PPState.Make ts mem iis), CPState.StoppedEarly.
      split; [auto|]. split; [discriminate|].
      cbn [CPState.run_to_termination].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn. rewrite decide_True by exact Hstop. apply Exec.elem_of_mret.
    + exists proms, (PPState.Make ts mem iis), CPState.Terminated.
      split; [auto|]. split; [discriminate|].
      cbn [CPState.run_to_termination].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn -[CPState.terminated_ts]. rewrite decide_False by exact Hcontinue.
      rewrite Hfinal. apply Exec.elem_of_mret.
  - destruct (decide (base < TState.min_new_prom_view ts)) as [Hstop|Hcontinue].
    + exists proms, (PPState.Make ts mem iis), CPState.StoppedEarly.
      split; [auto|]. split; [discriminate|].
      cbn [CPState.run_to_termination].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn. rewrite decide_True by exact Hstop. apply Exec.elem_of_mret.
    + destruct (collect_instruction_complete UMPromising tid imem base isem proms
        (PPState.Make ts mem IIS.init) (PPState.Make mid midmem iis0) () Hinst)
        as [proms_mid Hcollect].
      destruct (IH Hfinal base proms_mid iis0)
        as [proms' [ppst' [ending [Hkeep [Hend Hcert]]]]].
      exists proms', ppst', ending. split.
      * intros msg Hin. apply Hkeep.
        destruct (collect_instruction_suffix UMPromising tid imem base isem
          _ _ _ _ _ Hcollect) as [extra Hextra].
        rewrite Hextra. apply elem_of_app. right. exact Hin.
      * split; [exact Hend|].
        cbn [CPState.run_to_termination].
        eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
        cbn -[CPState.terminated_ts]. rewrite decide_False by exact Hcontinue.
        rewrite Hterm.
        eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
        eapply Exec.elem_of_bind_intro; [exact Hcollect|exact Hcert].
Qed.

Lemma first_new_message_with_terminating_suffix {n} (tid : fin n) imem
    (term : terminationCondition n) isem count ts mem mid midmem :
  thread_steps tid imem (term !!! tid) isem count ts mem mid midmem →
  ∀ suffix_count fin finmem,
  thread_steps tid imem (term !!! tid) isem suffix_count mid midmem fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  ∀ base_mem msg proms iis,
  midmem = msg :: base_mem →
  (mem = base_mem ∨ (mem = msg :: base_mem ∧ msg ∈ proms)) →
  ∃ proms' ppst' ending,
    msg ∈ proms' ∧ ending ≠ CPState.OutOfFuel ∧
    Exec.elem_of_results ((proms', ppst'), ending)
      (CPState.run_to_termination isem UMPromising term tid imem
        (count + suffix_count) (length base_mem) (proms, PPState.Make ts mem iis)).
Proof.
  intro Hsteps.
  induction Hsteps as [ts mem|count ts mem next nextmem mid midmem iis0 Hterm Hinst Htail IH];
    intros suffix_count fin finmem Hsuffix Hfinal base_mem msg proms iis Hmid Hmode.
  - assert (Hin : msg ∈ proms).
    { destruct Hmode as [Hsame|[_ Hin]]; [|exact Hin].
      rewrite Hsame in Hmid. apply (f_equal length) in Hmid. cbn in Hmid. lia. }
    destruct (terminating_thread_certification tid imem term isem
      suffix_count ts mem fin finmem Hsuffix Hfinal (length base_mem) proms iis)
      as [proms' [ppst' [ending [Hkeep [Hend Hcert]]]]].
    exists proms', ppst', ending. split; [apply Hkeep, Hin|].
    split; assumption.
  - destruct (decide (length base_mem < TState.min_new_prom_view ts)) as [Hstop|Hcontinue].
    + assert (Hin : msg ∈ proms).
      { destruct Hmode as [Hsame|[_ Hin]]; [|exact Hin].
        assert (Hnew : midmem ≠ mem).
        { rewrite Hmid, Hsame. intro Heq. apply (f_equal length) in Heq. cbn in Heq. lia. }
        assert (Hbound : TState.min_new_prom_view ts ≤ length mem).
        { eapply thread_new_message_min_bound; [econstructor; eassumption|exact Hnew]. }
        rewrite Hsame in Hbound. lia. }
      exists proms, (PPState.Make ts mem iis), CPState.StoppedEarly.
      split; [exact Hin|]. split; [discriminate|].
      cbn [CPState.run_to_termination].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn. rewrite decide_True by exact Hstop. apply Exec.elem_of_mret.
    + assert (Hcollect : ∃ proms_next,
        Exec.elem_of_results ((proms_next, PPState.Make next nextmem iis0), ())
          (cinterp (CPState.run_outcome_with_promise UMPromising tid imem
            (length base_mem)) isem (proms, PPState.Make ts mem IIS.init)) ∧
        (nextmem = base_mem ∨ (nextmem = msg :: base_mem ∧ msg ∈ proms_next))).
      { destruct Hmode as [Hsame|[Hsame Hin]].
        - subst mem.
          destruct (proj2 (thread_steps_middle_memory tid imem (term !!! tid)
            isem _ _ _ _ _ _ _ _ Hinst Htail) msg Hmid) as [Hnext|Hnext].
          + exists proms. split; [|left; exact Hnext].
            exact (collect_unchanged_instruction tid imem isem proms
              (PPState.Make ts base_mem IIS.init)
              (PPState.Make next nextmem iis0) () Hinst Hnext).
          + destruct (collect_first_new_instruction tid imem isem proms
              _ _ _ msg Hinst Hnext) as [proms_next [Hin Hcollect]].
            exists proms_next. split; [exact Hcollect|right; split; assumption].
        - assert (Hnext : nextmem = mem).
          { eapply (proj1 (thread_steps_middle_memory tid imem (term !!! tid)
              isem _ _ _ _ _ _ _ _ Hinst Htail)). congruence. }
          destruct (collect_instruction_complete UMPromising tid imem
            (length base_mem) isem proms _ _ _ Hinst) as [proms_next Hcollect].
          exists proms_next. split; [exact Hcollect|]. right. split; [congruence|].
          destruct (collect_instruction_suffix UMPromising tid imem
            (length base_mem) isem _ _ _ _ _ Hcollect) as [extra Hextra].
          rewrite Hextra. apply elem_of_app. right. exact Hin. }
      destruct Hcollect as [proms_next [Hcollect Hmode_next]].
      destruct (IH suffix_count fin finmem Hsuffix Hfinal base_mem msg proms_next iis0
        Hmid Hmode_next) as [proms' [ppst' [ending [Hin [Hend Hcert]]]]].
      exists proms', ppst', ending. split; [exact Hin|]. split; [exact Hend|].
      cbn [CPState.run_to_termination].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn -[CPState.terminated_ts]. rewrite decide_False by exact Hcontinue.
      rewrite Hterm.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
      eapply Exec.elem_of_bind_intro; [exact Hcollect|exact Hcert].
Qed.

End UMThreadCertification.

#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.

(** A terminating one-message execution supplies a certificate at every
    larger fuel, including when earlier promises are fulfilled along the way. *)
Lemma UMSail_terminated_first_new_message_stable nondet {n} (tid : fin n) imem
    (term : terminationCondition n) count ts mem fin msg :
  UMThreadReplay.thread_steps tid imem (term !!! tid) (sail_tiny_arm_sem nondet)
    count ts mem fin (msg :: mem) →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  StablePromiseCandidate UMPromising nondet term tid imem ts mem msg.
Proof.
  intros Hsteps Hterm.
  destruct (UMThreadCertification.terminated_first_new_message_certification
    tid imem term (sail_tiny_arm_sem nondet) count ts mem fin (msg :: mem)
    Hsteps Hterm mem msg [] UMPromising.IIS.init eq_refl (or_introl eq_refl))
    as [proms [ppst [ending [Hin [Hend Hcert]]]]].
  eapply completed_candidate_is_stable.
  - exact UM_filter_retains_membership.
  - eapply UMThreadCertification.first_new_message_enumerated. exact Hsteps.
  - exact Hin.
  - exact Hend.
  - exact Hcert.
Qed.

Lemma UMSail_first_new_message_stable_with_terminating_suffix
    nondet {n} (tid : fin n) imem (term : terminationCondition n)
    count ts mem mid msg suffix_count fin finmem :
  UMThreadReplay.thread_steps tid imem (term !!! tid) (sail_tiny_arm_sem nondet)
    count ts mem mid (msg :: mem) →
  UMThreadReplay.thread_steps tid imem (term !!! tid) (sail_tiny_arm_sem nondet)
    suffix_count mid (msg :: mem) fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  StablePromiseCandidate UMPromising nondet term tid imem ts mem msg.
Proof.
  intros Hprefix Hsuffix Hterm.
  destruct (UMThreadCertification.first_new_message_with_terminating_suffix
    tid imem term (sail_tiny_arm_sem nondet) count ts mem mid (msg :: mem)
    Hprefix suffix_count fin finmem Hsuffix Hterm mem msg []
    UMPromising.IIS.init eq_refl (or_introl eq_refl))
    as [proms [ppst [ending [Hin [Hend Hcert]]]]].
  assert (Hcandidate : msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet)
    UMPromising term tid imem (count + suffix_count) ts mem).(CPState.promises UMPromising)).
  { unfold CPState.enumerate_results.
    cbn [CPState.promises Promising.filter_promises].
    eapply collected_promise_in_raw_candidates; [exact Hin|exact Hcert]. }
  eapply completed_candidate_is_stable.
  - exact UM_filter_retains_membership.
  - exact Hcandidate.
  - exact Hin.
  - exact Hend.
  - exact Hcert.
Qed.

(** A truncated certificate becomes stable when its concrete endpoint has a
    terminating continuation. The continuation may append further messages. *)
Lemma UMSail_out_of_fuel_candidate_with_terminating_extension
    nondet {n} (tid : fin n) imem (term : terminationCondition n)
    fuel ts mem msg proms mid midmem iis count fin finmem :
  msg ∈ proms →
  Exec.elem_of_results
    ((proms, PPState.Make mid midmem iis), CPState.OutOfFuel)
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) UMPromising term tid imem
      fuel (length mem) ([], PPState.Make ts mem UMPromising.IIS.init)) →
  UMThreadReplay.thread_steps tid imem (term !!! tid) (sail_tiny_arm_sem nondet)
    count mid midmem fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  StablePromiseCandidate UMPromising nondet term tid imem ts mem msg.
Proof.
  intros Hin Hprefix Hsteps Hterm.
  destruct (UMThreadCertification.terminating_thread_certification tid imem term
    (sail_tiny_arm_sem nondet) count mid midmem fin finmem Hsteps Hterm
    (length mem) proms iis) as [proms' [ppst' [ending [Hkeep [Hend Hsuffix]]]]].
  pose proof (out_of_fuel_certification_continue UMPromising nondet term tid imem
    fuel count (length mem) [] (PPState.Make ts mem UMPromising.IIS.init)
    proms (PPState.Make mid midmem iis) proms' ppst' ending Hprefix Hsuffix) as Hcert.
  assert (Hcandidate : msg ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet)
    UMPromising term tid imem (fuel + count) ts mem).(CPState.promises UMPromising)).
  { unfold CPState.enumerate_results.
    cbn [CPState.promises Promising.filter_promises].
    eapply collected_promise_in_raw_candidates; [apply Hkeep, Hin|exact Hcert]. }
  eapply completed_candidate_is_stable.
  - exact UM_filter_retains_membership.
  - exact Hcandidate.
  - apply Hkeep, Hin.
  - exact Hend.
  - exact Hcert.
Qed.

(** Moving the first new message preserves the entire terminating execution
    and supplies a certificate for every sufficiently large fuel. *)
Theorem UMSail_first_new_message_certified_replay nondet {n}
    (term : terminationCondition n) initMs code (tid : fin n) st
    count mid msg suffix_count fin finmem :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid)
    (sail_tiny_arm_sem nondet) count (PState.tstate tid st) (PState.events st)
    mid (msg :: PState.events st) →
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid)
    (sail_tiny_arm_sem nondet) suffix_count mid (msg :: PState.events st) fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  StablePromiseCandidate UMPromising nondet term tid (PState.initmem st)
    (PState.tstate tid st) (PState.events st) msg ∧
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid)
    (sail_tiny_arm_sem nondet) (count + suffix_count)
    (UMPromising.TState.promise (S (length (PState.events st))) (PState.tstate tid st))
    (msg :: PState.events st) fin finmem.
Proof.
  intros Hsafe Hreach Hprefix Hsuffix Hterm. split.
  - eapply UMSail_first_new_message_stable_with_terminating_suffix; eassumption.
  - eapply UMThreadReplay.thread_steps_trans; [|exact Hsuffix].
    eapply UMThreadReplay.UMSail_first_new_message_thread_replay; eassumption.
Qed.

Theorem UMSail_first_new_message_promise_transition nondet {n}
    (term : terminationCondition n) initMs code (tid : fin n) st
    count mid msg suffix_count fin finmem :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid)
    (sail_tiny_arm_sem nondet) count (PState.tstate tid st) (PState.events st)
    mid (msg :: PState.events st) →
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid)
    (sail_tiny_arm_sem nondet) suffix_count mid (msg :: PState.events st) fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  ∃ st' threshold,
    PState.promise UMPromising msg st = Ok st' ∧
    (∀ fuel, threshold ≤ fuel →
      Exec.elem_of_results (st', None)
        (CPState.run_transition_promise_first (sail_tiny_arm_sem nondet)
          UMPromising term fuel st)) ∧
    PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st' ∧
    UMThreadReplay.thread_steps tid (PState.initmem st') (term !!! tid)
      (sail_tiny_arm_sem nondet) (count + suffix_count)
      (PState.tstate tid st') (PState.events st') fin finmem.
Proof.
  intros Hsafe Hreach Hprefix Hsuffix Hterm.
  destruct (UMSail_first_new_message_certified_replay nondet term initMs code tid
    st count mid msg suffix_count fin finmem Hsafe Hreach Hprefix Hsuffix Hterm)
    as [[threshold Hcandidate] Hreplay].
  pose proof (UMThreadReplay.first_new_message_owner nondet tid (PState.initmem st)
    (term !!! tid) count (PState.tstate tid st) (PState.events st)
    mid (msg :: PState.events st) Hprefix msg eq_refl) as Howner.
  destruct (UMPromising_promise_exists msg st) as [st' Hpromise].
  assert (Hstep : ∀ fuel, threshold ≤ fuel →
    Exec.elem_of_results (st', None)
      (CPState.run_transition_promise_first (sail_tiny_arm_sem nondet)
        UMPromising term fuel st)).
  { intros fuel Hfuel.
    eapply run_transition_promise_first_none_intro with (tid := tid) (ev := msg) (nst := st').
    - rewrite promise_first_execution_results_lookup. apply Hcandidate, Hfuel.
    - exact Hpromise.
    - reflexivity. }
  exists st', threshold. split; [exact Hpromise|]. split; [exact Hstep|]. split.
  - eapply PromiseFirstReachable_step; [exact Hreach|apply Hstep, Nat.le_refl].
  - destruct (UMPromising_promise_success msg st st' Hpromise) as [Himem [Hmem Hstates]].
    specialize (Hstates tid).
    rewrite UMPromising_emit_promise_ok, bool_decide_true in Hstates by exact Howner.
    injection Hstates as Hstate.
    rewrite Himem, Hmem, <- Hstate. exact Hreplay.
Qed.
