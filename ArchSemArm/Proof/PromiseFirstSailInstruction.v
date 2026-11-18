(******************************************************************************)
(* Complete UM instruction replay after prepromising its unique new message  *)
(******************************************************************************)

(** This induction replays every outcome before the new write, fulfills the
    prepromised write into exactly its original post-state, and reuses the
    original suffix. Fetch preservation is discharged for actual Sail
    prefixes in PromiseFirstSailCurrent. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstExecutionCurrent
  PromiseFirstSailExecution PromiseFirstSailReplay PromiseFirstSailRead
  PromiseFirstSailControl.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module UMInstructionReplay.
Import UMPromising UMReadReplay UMControlReplay.
#[local] Typeclasses Transparent Memory.t.

Fixpoint preserved_fetches {A} tid imem msg
    (mon : iMon A) (ppst : PPState.t TState.t Msg.t IIS.t) : Prop :=
  match mon with
  | Ret _ => True
  | Next (inl out) k =>
      fetch_preserved imem msg ppst out ∧
      ∀ after ret pre, Exec.elem_of_results (after, (ret, pre))
        (run_outcome tid imem out ppst) →
        preserved_fetches tid imem msg (k ret) after
  | Next (inr _) k => ∀ ret, preserved_fetches tid imem msg (k ret) ppst
  end.

Lemma one_update_replay {n A} (tid : fin n) imem msg (mon : iMon A)
    ppst ppst' ret :
  IMonAtMostOneUpdate mon →
  preserved_fetches tid imem msg mon ppst →
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' tid imem) mon ppst) →
  PPState.mem ppst' = msg :: PPState.mem ppst →
  order_view ppst < S (length (PPState.mem ppst)) ∧
  Exec.elem_of_results (ppst', ret)
    (cinterp (run_outcome' tid imem) mon
      (add_pending_message msg (S (length (PPState.mem ppst))) ppst)).
Proof.
  revert ppst ppst' ret.
  induction mon as [a|call k IH]; intros ppst ppst' ret Hshape Hfetch Hrun Hmem.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _].
    apply (f_equal length) in Hmem. cbn in Hmem. lia.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]].
      cbn in Heq. subst res.
      destruct Hfetch as [Hfetch Hfetch_tail].
      destruct Hshape as [[Hno Hshape]|Hshape].
      * pose proof (UMSailMemory.outcome_no_update_mem tid imem out ppst mid r pre Hno Hout)
          as Hmidmem.
        assert (Htailmem : PPState.mem ppst' = msg :: PPState.mem mid) by congruence.
        destruct (IH r mid ppst' ret (Hshape r) (Hfetch_tail _ _ _ Hout)
          Htail Htailmem) as [Hbound Hreplay].
        rewrite Hmidmem in Hbound, Hreplay.
        split.
        -- pose proof (outcome_order_view_monotone tid imem out ppst mid r pre Hno Hout).
           lia.
        -- eapply Exec.elem_of_bind_intro with
             (st' := add_pending_message msg (S (length (PPState.mem ppst))) mid)
             (a := r).
           ++ unfold run_outcome'. eapply Exec.elem_of_fmap_intro with (a := (r, pre)) (f := fst).
              eapply no_update_outcome_after_promise; eassumption.
           ++ exact Hreplay.
      * assert (Htailmem : PPState.mem ppst' = PPState.mem mid).
        { eapply (no_update_instruction_memory UMPromising tid imem).
          - intros. eapply UMSailMemory.outcome_no_update_mem; eassumption.
          - apply Hshape.
          - exact Htail. }
        destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst mid r pre Hout)
          as [Hsame|[extra [vpre [_ [_ [Hpre Hprebound]]]]]].
        { rewrite Htailmem, Hsame in Hmem.
          apply (f_equal length) in Hmem. cbn in Hmem. lia. }
        subst pre.
        destruct (UMSailReplay.run_outcome_promise_replay_one tid imem out ppst mid r vpre Hout)
          as [msg' [Hmid [Htid [Hbound Hreplay]]]].
        rewrite Htailmem, Hmid in Hmem. injection Hmem as Heqmsg. subst msg'.
        split.
        -- pose proof (UMSailReplay.run_outcome_new_order_view_bound
             tid imem out ppst mid r vpre Hout).
           unfold order_view. lia.
        -- eapply Exec.elem_of_bind_intro with (st' := mid) (a := r).
           ++ unfold run_outcome'. eapply Exec.elem_of_fmap_intro with (a := (r, None)) (f := fst). exact Hreplay.
           ++ exact Htail.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->.
      assert (Hshape_tail : IMonAtMostOneUpdate (k r)).
      { destruct Hshape as [[_ Hshape]|Hshape]; [apply Hshape|].
        apply imon_one_update_of_no_update, Hshape. }
      destruct (IH r ppst ppst' ret Hshape_tail (Hfetch r) Htail Hmem)
        as [Hbound Hreplay].
      split; [exact Hbound|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|exact Hreplay].
Qed.
End UMInstructionReplay.
