(******************************************************************************)
(* Replaying UM reads when another thread prepends a message                  *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstConcreteCurrent PromiseFirstExecutionCurrent PromiseFirstSailCurrent
  PromiseFirstSailState PromiseFirstSailThread
  PromiseFirstSailRead PromiseFirstSailControl PromiseFirstSailExecution
  PromiseFirstSailInstruction PromiseFirstSailFulfilled PromiseFirstSailSequence PromiseFirstSailReplay.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module UMForeignReplay.
Import UMPromising.
#[local] Typeclasses Transparent Memory.t othrow.

(** A message owned by another thread changes this thread's shared history
    while leaving its pending-promise list unchanged. *)
Definition add_message (msg : Msg.t) (ppst : PPState.t TState.t Msg.t IIS.t) :=
  PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst) (PPState.iis ppst).

Lemma read_mem_after_message addr size macc imem msg ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (read_mem addr size macc imem ppst) →
  Exec.elem_of_results (add_message msg ppst', ret)
    (read_mem addr size macc imem (add_message msg ppst)).
Proof.
  destruct ppst as [ts mem iis]. intro Hrun.
  unfold read_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [vaddr [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [Hnp [Hguard Hrun]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  apply Exec.elem_of_bind_elim in Hrun as [mid [mem0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [candidates [Hread Hrun]]].
  apply exec_lift_result_inv in Hread as [-> Hread].
  apply Exec.elem_of_bind_elim in Hrun as [mid [candidate [Hchoice Htail]]].
  apply Exec.elem_of_mchoosel_inv in Hchoice as [-> Hin].
  cbn in Hread.
  pose proof (read_all_aux_success_bound Some _ _ _ _ _ _ _ Hread) as Hmin.
  destruct (read_all_cons_preserves_candidates Some addr size imem mem msg _ candidates
    Hmin Hread) as [new_candidates [Hread' Hsubset]].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply exec_guard_discard_bind_intro; [exact Hnp|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [add_message].
  eapply Exec.elem_of_bind_intro with (a := new_candidates).
  - apply exec_lift_result. exact Hread'.
  - eapply Exec.elem_of_bind_intro with (a := candidate).
    + apply Exec.elem_of_mchoosel, Hsubset, Hin.
    + cbn [add_message PPState.state PPState.mem PPState.iis] in *.
      UMMemoryGrowth.invert_execution.
      all: subst ret.
      all: cbn [add_message].
      all: repeat first
        [ eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
        | eapply exec_guard_discard_bind_intro; [assumption|] ].
      all: apply Exec.elem_of_mret.
Qed.

Lemma mem_read_after_message tid imem req msg ppst ppst' ret pre :
  (is_ifetch (MemReq.access_kind req) = true →
    MemReq.size req = 4%N →
    read_ifetch (MemReq.address req) imem (msg :: PPState.mem ppst) =
    read_ifetch (MemReq.address req) imem (PPState.mem ppst)) →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem (MemRead req) ppst) →
  Exec.elem_of_results (add_message msg ppst', (ret, pre))
    (run_outcome tid imem (MemRead req) (add_message msg ppst)).
Proof.
  destruct req as [macc addr pas size tags].
  destruct tags as [|tags]; intros Hfetch Hrun.
  2: { simp run_outcome in Hrun. UMMemoryGrowth.invert_execution. }
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [Hpas [Hguard Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  eapply exec_guard_or_bind_intro; [exact Hpas|].
  destruct (is_ifetch macc) eqn:Hif.
  - apply Exec.elem_of_bind_elim in Hrun as [mid [Hsize [Hguard Hrun]]].
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hrun as [mid [mem [Hget Hrun]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as [mid [opcode [Hread Hrun]]].
    apply Exec.elem_of_lift_res_inv in Hread as [-> Hread].
    apply Exec.elem_of_mret_inv in Hrun as [-> Heq].
    injection Heq as -> ->.
    destruct (Exec.elem_of_guard_or (E:=string) (add_message msg ppst)
      "Ifetch read of size other than 4" Hsize) as [Hsize' Hguard].
    replace Hsize' with Hsize in Hguard by apply proof_irrel.
    eapply Exec.elem_of_bind_intro; [exact Hguard|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro with (a := opcode).
    + apply Exec.elem_of_lift_res. cbn.
      rewrite (Hfetch Hif Hsize). exact Hread.
    + apply Exec.elem_of_mret.
  - destruct (is_explicit macc) eqn:Hexpl.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [val [Hread Hrun]]].
      apply Exec.elem_of_mret_inv in Hrun as [-> Heq].
      injection Heq as -> ->.
      eapply Exec.elem_of_bind_intro; [eapply read_mem_after_message; exact Hread|].
      apply Exec.elem_of_mret.
    + UMMemoryGrowth.invert_execution.
Qed.
Lemma reg_read_after_message tid imem reg racc msg ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem (RegRead reg racc) ppst) →
  Exec.elem_of_results (add_message msg ppst', (ret, pre))
    (run_outcome tid imem (RegRead reg racc) (add_message msg ppst)).
Proof.
  destruct ppst as [ts mem iis]. intro Hrun.
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [Hacc [Hguard Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  unfold othrow in Hrun.
  match type of Hrun with context[match ?opt with _ => _ end] =>
    destruct opt as [[val v]|] eqn:Hlookup end.
  2: { UMMemoryGrowth.invert_execution. }
  UMMemoryGrowth.invert_execution.
  eapply exec_guard_or_bind_intro; [reflexivity|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  unfold othrow. cbn. rewrite Hlookup. cbn.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  apply Exec.elem_of_mret.
Qed.

Lemma reg_write_after_message tid imem reg racc val msg ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem (RegWrite reg racc val) ppst) →
  Exec.elem_of_results (add_message msg ppst', (ret, pre))
    (run_outcome tid imem (RegWrite reg racc val) (add_message msg ppst)).
Proof.
  destruct ppst as [ts mem iis]. intro Hrun.
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [Hacc [Hguard Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  apply Exec.elem_of_bind_elim in Hrun as [mid [strict [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  eapply exec_guard_or_bind_intro; [exact Hacc|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  match type of Hrun with context[if ?b then _ else _] => destruct b eqn:Hpc end.
  - apply bool_decide_eq_true_1 in Hpc.
    apply Exec.elem_of_bind_elim in Hrun as [mid [vreg [Hpcstep Hrun]]].
    UMMemoryGrowth.invert_execution. subst.
    eapply Exec.elem_of_bind_intro with (a := 0).
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      eapply exec_guard_discard_bind_intro; [assumption|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
      apply Exec.elem_of_mret.
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn in Heqo |- *. rewrite Heqo.
      unfold othrow. cbn.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
      apply Exec.elem_of_mret.
  - UMMemoryGrowth.invert_execution. subst.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn in Heqo |- *. rewrite Heqo.
    unfold othrow. cbn.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_mret.
Qed.

Lemma no_update_outcome_after_message tid imem out msg ppst ppst' ret pre :
  IEffectNoUpdate (inl out) →
  UMControlReplay.fetch_preserved imem msg ppst out →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  Exec.elem_of_results (add_message msg ppst', (ret, pre))
    (run_outcome tid imem out (add_message msg ppst)).
Proof.
  intros Hno Hfetch Hrun.
  destruct out as [reg racc|reg racc val|req|req|req val tags|barrier|cop|tlbi|exn| |trans|trans|err];
    cbn [IEffectNoUpdate] in Hno; try contradiction.
  - apply reg_read_after_message, Hrun.
  - apply reg_write_after_message, Hrun.
  - apply mem_read_after_message; assumption.
  - destruct ppst as [ts mem iis]. simp run_outcome in Hrun |- *.
    UMMemoryGrowth.invert_execution. subst.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply exec_guard_discard_bind_intro; [assumption|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_mret.
  - destruct barrier as [dsb|dmb|[]|[]|[]|[]];
      try destruct (DxB_types dsb); try destruct (DxB_types dmb);
      simp run_outcome in Hrun |- *;
      cbn beta iota zeta in Hrun |- *;
      UMMemoryGrowth.invert_execution; subst.
    all: destruct ppst as [ts mem iis]; destruct ts; cbn in *.
    all: repeat (cbn beta iota zeta; first
      [ apply Exec.elem_of_mret
      | apply Exec.elem_of_mset
      | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
      | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
      | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
      | eapply exec_guard_discard_bind_intro; [assumption|]
      | match goal with
        | |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) =>
          eapply Exec.elem_of_bind_intro
        end ]).
  - simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
  - simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
  - simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
  - simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
  - simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
Qed.

Lemma no_update_instruction_after_message {A} tid imem msg (mon : iMon A) ppst ppst' ret :
  IMonNoUpdate mon →
  UMInstructionReplay.preserved_fetches tid imem msg mon ppst →
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  Exec.elem_of_results (add_message msg ppst', ret)
    (cinterp (run_outcome' tid imem) mon (add_message msg ppst)).
Proof.
  revert ppst ppst' ret.
  induction mon as [a|call k IH]; intros ppst ppst' ret Hshape Hfetch Hrun.
  - cbn in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    apply Exec.elem_of_mret.
  - destruct Hshape as [Hno Hshape]. destruct call as [out|[choices]]; cbn in Hrun |- *.
    + destruct Hfetch as [Hfetch Htailfetch].
      apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[v pre] [Heq Hout]].
      cbn in Heq. subst r.
      eapply Exec.elem_of_bind_intro with (st' := add_message msg mid) (a := v).
      * unfold run_outcome'. eapply Exec.elem_of_fmap_intro with (a := (v, pre)) (f := fst).
        eapply no_update_outcome_after_message; eassumption.
      * eapply IH; [apply Hshape|eapply Htailfetch; exact Hout|exact Htail].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|].
      eapply IH; [apply Hshape|apply Hfetch|exact Htail].
Qed.
#[local] Existing Instance PromMemory.lookup_inst.
#[local] Existing Instance PromMemory.exclusive_dec.

Lemma fulfill_after_message msg future prom mem :
  (∀ t ∈ prom, t ≤ length mem) →
  Memory.fulfill msg prom (future :: mem) = Memory.fulfill msg prom mem.
Proof.
  intro Hbound. unfold Memory.fulfill, PromMemory.fulfill.
  f_equal. f_equal.
  induction prom as [|t prom IH]; [reflexivity|].
  rewrite !filter_cons.
  rewrite PromMemory.lookup_cons_old by (apply Hbound; set_solver).
  rewrite IH by (intros; apply Hbound; set_solver). reflexivity.
Qed.

Lemma write_mem_fulfilled_after_message tid addr size macc data msg ppst ppst' :
  (∀ t ∈ TState.prom (PPState.state ppst), t ≤ length (PPState.mem ppst)) →
  Exec.elem_of_results (ppst', None) (write_mem tid addr size macc data ppst) →
  Exec.elem_of_results (add_message msg ppst', None)
    (write_mem tid addr size macc data (add_message msg ppst)).
Proof.
  destruct ppst as [ts mem iis]. cbn. intros Hbound Hrun.
  unfold write_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [mem0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[time fresh] [Hfulfill Hrun]]].
  destruct (Memory.fulfill (Msg.make tid addr size data) (TState.prom ts) mem)
    as [t|] eqn:Hlookup.
  all: cbn [PPState.state PPState.mem] in Hfulfill; rewrite Hlookup in Hfulfill.
  2: { exfalso. UMMemoryGrowth.invert_execution; cbn in *; discriminate. }
  apply Exec.elem_of_mret_inv in Hfulfill as [-> Heq]. inversion Heq; subst time fresh.
  pose proof (UMFulfilledReplay.fulfill_bound _ _ _ _ Hlookup) as Htime.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [add_message PPState.state PPState.mem].
  rewrite fulfill_after_message by exact Hbound. rewrite Hlookup.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  UMFulfilledReplay.invert_execution_with_guards; subst; try discriminate.
  all: cbn [PPState.state PPState.mem PPState.iis compose] in *.
  all: repeat first
    [ apply Exec.elem_of_guard_discard_unit;
      rewrite UMFulfilledReplay.exclusive_before_future by assumption; assumption
    | apply Exec.elem_of_mret
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_guard_discard_unit;
        rewrite UMFulfilledReplay.exclusive_before_future by assumption; assumption|]
    | eapply exec_guard_discard_bind_intro; [assumption|]
    | match goal with H : ?x = _ |- context[?x] => progress rewrite H end
    | progress cbn [add_message PPState.state PPState.iis PPState.mem compose othrow]
    | match goal with
      | |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) => eapply Exec.elem_of_bind_intro
      end ].
Qed.
Lemma unchanged_outcome_after_message tid imem out msg ppst ppst' ret pre :
  UMContinuation.pending_bounded ppst →
  UMControlReplay.fetch_preserved imem msg ppst out →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  PPState.mem ppst' = PPState.mem ppst →
  Exec.elem_of_results (add_message msg ppst', (ret, pre))
    (run_outcome tid imem out (add_message msg ppst)).
Proof.
  intros Hbound Hfetch Hrun Hmem.
  assert (Hpre : pre = None).
  { destruct pre as [vpre|]; [|reflexivity].
    destruct (UMSailReplay.run_outcome_promise_replay_one tid imem out ppst ppst'
      ret vpre Hrun) as [ev [Hnew _]].
    rewrite Hmem in Hnew. apply (f_equal length) in Hnew. cbn in Hnew. lia. }
  subst pre.
  destruct out as [reg racc|reg racc val|req|req|req val tags|barrier|cop|tlbi|exn| |trans|trans|err];
    try solve [eapply no_update_outcome_after_message; [exact I|exact Hfetch|exact Hrun]].
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
      * eapply write_mem_fulfilled_after_message; [exact Hbound|exact Hwrite].
      * apply Exec.elem_of_mret.
    + simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
  - simp run_outcome in Hrun. UMMemoryGrowth.invert_execution.
Qed.

Lemma unchanged_instruction_after_message {n A} (tid : fin n) imem msg (mon : iMon A)
    ppst ppst' ret :
  UMContinuation.pending_bounded ppst →
  UMInstructionReplay.preserved_fetches tid imem msg mon ppst →
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  PPState.mem ppst' = PPState.mem ppst →
  Exec.elem_of_results (add_message msg ppst', ret)
    (cinterp (run_outcome' tid imem) mon (add_message msg ppst)).
Proof.
  revert ppst ppst' ret.
  induction mon as [a|call k IH]; intros ppst ppst' ret Hpending Hfetch Hrun Hmem.
  - cbn in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    apply Exec.elem_of_mret.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]].
      cbn in Heq. subst res.
      destruct Hfetch as [Hfetch Hfetch_tail].
      destruct (UMContinuation.instruction_facts tid imem (k r) mid ppst' ret Htail)
        as [_ [_ [extra Hsuffix]]].
      assert (Hmidmem : PPState.mem mid = PPState.mem ppst).
      { destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst mid r pre Hout)
          as [Hsame|[added [vpre [Hnonempty [Hadded _]]]]]; [exact Hsame|].
        rewrite Hadded, Hmem in Hsuffix.
        apply (f_equal length) in Hsuffix. rewrite !length_app in Hsuffix.
        destruct added; [contradiction|cbn in Hsuffix; lia]. }
      eapply Exec.elem_of_bind_intro with (st' := add_message msg mid) (a := r).
      * unfold run_outcome'. eapply Exec.elem_of_fmap_intro with (a := (r, pre)) (f := fst).
        eapply unchanged_outcome_after_message; eassumption.
      * eapply IH.
        -- eapply UMContinuation.outcome_pending_bounded; eassumption.
        -- eapply Hfetch_tail; exact Hout.
        -- exact Htail.
        -- congruence.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|].
      eapply IH; eauto.
Qed.
End UMForeignReplay.

Lemma UM_fixed_thread_after_message {n} (tid : fin n) imem bps isem msg
    count ts mem fin finmem :
  UMThreadReplay.thread_steps tid imem bps isem count ts mem fin finmem →
  finmem = mem →
  UMContinuation.pending_bounded (PPState.Make ts mem UMPromising.IIS.init) →
  UMThreadReplay.thread_fetches tid imem bps isem msg ts mem →
  UMThreadReplay.thread_steps tid imem bps isem count ts (msg :: mem) fin (msg :: finmem).
Proof.
  intro Htrace.
  induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intros Hmem Hpending Hfetch; [constructor|].
  destruct (UMContinuation.instruction_facts tid imem isem _ _ _ Hinst)
    as [_ [_ [first Hfirst]]].
  destruct (UMThreadReplay.thread_steps_suffix tid imem bps isem _ _ _ _ _ Htail)
    as [rest Hrest].
  cbn in Hfirst.
  assert (Hnil : first = []).
  { rewrite Hfirst, Hmem in Hrest. apply (f_equal length) in Hrest.
    rewrite !length_app in Hrest. destruct first; [reflexivity|cbn in Hrest; lia]. }
  subst first. cbn in Hfirst. subst midmem.
  econstructor; [exact Hterm| |].
  - apply (UMForeignReplay.unchanged_instruction_after_message tid imem msg isem
      (PPState.Make ts mem UMPromising.IIS.init) (PPState.Make mid mem iis) ()).
    + exact Hpending.
    + apply (Hfetch 0 ts mem); [constructor|exact Hterm].
    + exact Hinst.
    + reflexivity.
  - apply IH; [exact Hmem| |].
    + exact (UMContinuation.instruction_pending_bounded tid imem isem
        (PPState.Make ts mem UMPromising.IIS.init) (PPState.Make mid mem iis) ()
        Hpending Hinst).
    + intros steps next nextmem Hsteps Hnextterm.
      eapply Hfetch; [econstructor; eassumption|exact Hnextterm].
Qed.

#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.
#[local] Typeclasses Transparent UMPromising.Memory.t.

(** The unchanged pending list here is derived from the message's owner and
    the actual global promise operation. Older fulfilled writes are allowed. *)
Theorem UMSail_foreign_message_thread_replay nondet {n}
    (term : terminationCondition n) initMs code (tid : fin n) st next
    msg count fin :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  event_misses_code Msg.read_byte code msg →
  Msg.tid msg ≠ (tid : nat) →
  PState.promise UMPromising msg st = Ok next →
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid) (sail_tiny_arm_sem nondet)
    count (PState.tstate tid st) (PState.events st) fin (PState.events st) →
  UMThreadReplay.thread_steps tid (PState.initmem next) (term !!! tid) (sail_tiny_arm_sem nondet)
    count (PState.tstate tid next) (PState.events next) fin (PState.events next).
Proof.
  intros Hsafe Hreach Hmiss Hforeign Hpromise Hsteps.
  destruct (UMPromising_promise_success msg st next Hpromise) as [Himem [Hmem Hstates]].
  specialize (Hstates tid).
  rewrite UMPromising_emit_promise_ok, bool_decide_false in Hstates by exact Hforeign.
  injection Hstates as Hstate.
  rewrite Himem, Hmem, <- Hstate.
  eapply UM_fixed_thread_after_message; [exact Hsteps|reflexivity| |].
  - intros p Hin. exact (proj2 (UMSail_promise_first_pending_bounds
      nondet term initMs st tid p Hreach Hin)).
  - intros steps ts mem Hprefix Hterm.
    assert (Hsource : CPState.terminated_ts UMPromising (term !!! tid)
      (PState.tstate tid st) = false).
    { eapply UMThreadReplay.thread_steps_source_nonterminated; eassumption. }
    eapply (UMThreadReplay.actual_thread_fetches nondet term initMs code tid
      (PState.initmem st) msg (PState.tstate tid st) (PState.events st)
      Hsafe Hmiss).
    + eapply SailThreadPrefix_start; eassumption.
    + exact Hprefix.
    + exact Hterm.
Qed.
