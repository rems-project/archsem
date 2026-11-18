(******************************************************************************)
(* VM certification collects events emitted by its own thread                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstExecutionCurrent
  PromiseFirstSailCertification PromiseFirstSailVMEventValidity
  PromiseFirstVMExecutionCurrent PromiseFirstSailExecution.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module VMCollectedOwnership.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis Memory.t.
Section Ownership.
Context (bbm : bool).
Local Notation prom := (VMPromising bbm).

Definition owned (tid : nat) (evs : list Ev.t) := Forall (λ ev, Ev.tid ev = tid) evs.
Definition owned_suffix (tid : nat) (base mem : Memory.t) :=
  ∃ extra, mem = (extra ++ base)%list ∧ owned tid extra.
Lemma owned_refl tid mem : owned_suffix tid mem mem.
Proof. exists []. split; [reflexivity|constructor]. Qed.
Lemma owned_trans tid a b c : owned_suffix tid a b → owned_suffix tid b c → owned_suffix tid a c.
Proof.
  intros [xs [-> Hxs]] [ys [-> Hys]]. exists (ys ++ xs)%list.
  split; [apply app_assoc|apply Forall_app; auto].
Qed.
Lemma owned_suffix_take tid base mem :
  owned_suffix tid base mem → owned tid (take (length mem - length base) mem).
Proof.
  intros [extra [-> Howned]]. rewrite length_app, Nat.add_sub, take_app_length. exact Howned.
Qed.
Lemma materialize_owned tid imem pre tlbi recipient p p' time created : TLBI.tid tlbi = tid →
  Exec.elem_of_results (p', (time, created))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient p) →
  owned_suffix tid (PPState.mem p) (PPState.mem p').
Proof.
  intros Howner Hrun. apply VMMemoryGrowth.materialize_tlbi_growth in Hrun.
  destruct created; cbn in Hrun.
  - destruct Hrun as [epoch [-> _]]. exists [Ev.Tlbi tlbi recipient epoch].
    split; [reflexivity|constructor; [exact Howner|constructor]].
  - rewrite Hrun. apply owned_refl.
Qed.
Lemma recipients_owned tid imem pre tlbi recipients acc p p' ret : TLBI.tid tlbi = tid →
  Exec.elem_of_results (p', ret)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients p) →
  owned_suffix tid (PPState.mem p) (PPState.mem p').
Proof.
  intro Howner. revert acc p p' ret.
  induction recipients as [|recipient recipients IH]; intros acc p p' ret Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. apply owned_refl.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [a [Hstep Htail]]].
    destruct acc as [[vs vo] cr]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time created] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply owned_trans; [eapply materialize_owned; eassumption|eapply IH; exact Htail].
Qed.
Lemma tlbi_owned n tid imem viio tlbi p p' ret :
  Exec.elem_of_results (p', ret) (run_tlbi n tid imem viio tlbi p) →
  owned_suffix tid (PPState.mem p) (PPState.mem p').
Proof.
  intro Hrun. unfold run_tlbi in Hrun. VMMemoryGrowth.invert_execution.
  all: subst.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply recipients_owned in H; [|reflexivity] end.
  all: repeat match goal with q : PPState.t _ _ _ |- _ => destruct q end; cbn in *; assumption.
Qed.
Lemma outcome_owned_suffix {n} (tid : fin n) imem out base p p' ret pre :
  owned_suffix tid base (PPState.mem p) →
  Exec.elem_of_results (p', (ret, pre)) (run_outcome n tid imem out p) →
  owned_suffix tid base (PPState.mem p').
Proof.
  intros Hbase Hrun. eapply owned_trans; [exact Hbase|].
  assert (Hdec : Decision (IEffectNoUpdate (inl out))) by (destruct out; cbn; typeclasses eauto).
  destruct (decide (IEffectNoUpdate (inl out))) as [Hno|Hno].
  { rewrite (VMSailMemory.outcome_no_update_mem n tid imem out p p' ret pre Hno Hrun).
    apply owned_refl. }
  destruct out; cbn in Hno; try contradiction.
  - match type of Hrun with Exec.elem_of_results _ (run_outcome _ _ _ (MemWrite ?mr _ _) _) =>
      destruct mr as [macc addr pas size [|ntags]] end;
      simp run_outcome in Hrun; VMMemoryGrowth.invert_execution.
    match goal with H : Exec.elem_of_results _ (write_mem _ _ _ _ _ _ _) |- _ =>
      apply VMMemoryGrowth.write_mem_growth in H as [->|[pre [-> _]]] end.
    + apply owned_refl.
    + eexists [_]. split; [reflexivity|constructor; [reflexivity|constructor]].
  - simp run_outcome in Hrun. VMMemoryGrowth.invert_execution. eapply tlbi_owned; eassumption.
Qed.
Lemma collect_outcome_owned {n} (tid : fin n) imem base out proms ppst proms' ppst' ret :
  owned tid proms → owned_suffix tid base (PPState.mem ppst) →
  Exec.elem_of_results ((proms', ppst'), ret)
    (CPState.run_outcome_with_promise prom tid imem (length base) out (proms, ppst)) →
  owned tid proms' ∧ owned_suffix tid base (PPState.mem ppst').
Proof.
  intros Hproms Hmem Hrun.
  destruct (collect_outcome_inv prom tid imem (length base) out
    proms ppst proms' ppst' ret Hrun) as [pre [Hout Hcollect]].
  pose proof (outcome_owned_suffix tid imem out base ppst ppst' ret pre Hmem Hout) as Hmem'.
  split; [|exact Hmem']. rewrite Hcollect. destruct pre as [pre|]; [|exact Hproms].
  destruct (decide (pre ≤ length base)); [|exact Hproms].
  apply Forall_app. split; [apply owned_suffix_take|exact Hproms].
  eapply outcome_owned_suffix; [exists []; split; [reflexivity|constructor]|exact Hout].
Qed.

Local Lemma lift_snd_error {A B E R} (a a' : A) (b b' : B)
    (e : Exec.t B E R) err :
  ((a', b'), err) ∈ Exec.errors (Exec.liftSt snd e (a,b)) → a' = a.
Proof.
  unfold Exec.liftSt, Exec.liftSt_full, Exec.map_state. cbn.
  intro Hin. apply list_elem_of_fmap in Hin as [[s er] [Heq _]].
  inversion Heq. reflexivity.
Qed.

Lemma collect_outcome_error_owned {n} (tid : fin n) imem base out proms ppst proms' ppst' err :
  owned tid proms →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_outcome_with_promise prom tid imem base out (proms, ppst)) →
  owned tid proms'.
Proof.
  intros Howned Herr. unfold CPState.run_outcome_with_promise in Herr.
  apply exec_error_bind in Herr as [Herr|[start [len [Hlen Herr]]]]; [inversion Herr|].
  apply Exec.elem_of_mget_inv in Hlen as [-> ->].
  apply exec_error_bind in Herr as [Herr|[mid [[ret pre] [Hout Herr]]]].
  - apply lift_snd_error in Herr. subst proms'. exact Howned.
  - destruct pre as [pre|].
    + destruct (decide (pre ≤ base)); [|inversion Herr].
      apply exec_error_bind in Herr as [Herr|[mid' [mem [Hget Herr]]]];
        [inversion Herr|].
      apply exec_error_bind in Herr as [Herr|[last [[] [Hset Herr]]]];
        inversion Herr.
    + inversion Herr.
Qed.

Lemma collect_instruction_owned {n A} (tid : fin n) imem base (mon : iMon A)
    proms ppst proms' ppst' ret :
  owned tid proms → owned_suffix tid base (PPState.mem ppst) →
  Exec.elem_of_results ((proms', ppst'), ret)
    (cinterp (CPState.run_outcome_with_promise prom tid imem (length base))
      mon (proms, ppst)) →
  owned tid proms' ∧ owned_suffix tid base (PPState.mem ppst').
Proof.
  revert proms ppst proms' ppst' ret.
  induction mon as [value|call k IH]; intros proms ppst proms' ppst' ret Howned Hmem Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [Heq _].
    injection Heq as <- <-. auto.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [[next_pro next_st] [r [Hout Htail]]].
      destruct (collect_outcome_owned tid imem base out proms ppst next_pro next_st r
        Howned Hmem Hout) as [Howned' Hmem'].
      eapply IH; eassumption.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->. eapply IH; eassumption.
Qed.

Lemma collect_instruction_error_owned {n A} (tid : fin n) imem base (mon : iMon A)
    proms ppst proms' ppst' err :
  owned tid proms → owned_suffix tid base (PPState.mem ppst) →
  ((proms', ppst'), err) ∈ Exec.errors
    (cinterp (CPState.run_outcome_with_promise prom tid imem (length base))
      mon (proms, ppst)) →
  owned tid proms'.
Proof.
  revert proms ppst.
  induction mon as [value|call k IH]; intros proms ppst Howned Hmem Herr.
  - inversion Herr.
  - destruct call as [out|[choices]]; cbn in Herr.
    + apply exec_error_bind in Herr as [Herr|[[next_pro next_st] [r [Hout Herr]]]].
      * eapply collect_outcome_error_owned; eassumption.
      * destruct (collect_outcome_owned tid imem base out proms ppst next_pro next_st r
          Howned Hmem Hout) as [Howned' Hmem'].
        eapply IH; eassumption.
    + apply exec_error_bind in Herr as [Herr|[mid [r [Hchoice Herr]]]].
      * inversion Herr.
      * apply Exec.elem_of_mchoose_inv in Hchoice as ->. eapply IH; eassumption.
Qed.

Lemma run_owned {n} (tid : fin n) imem base isem (term : terminationCondition n)
    fuel proms ppst proms' ppst' ending :
  owned tid proms → owned_suffix tid base (PPState.mem ppst) →
  Exec.elem_of_results ((proms', ppst'), ending)
    (CPState.run_to_termination isem prom term tid imem fuel
      (length base) (proms, ppst)) →
  owned tid proms'.
Proof.
  revert proms ppst.
  induction fuel as [|fuel IH]; intros proms [ts mem iis] Howned Hmem Hrun.
  all: cbn [CPState.run_to_termination] in Hrun.
  all: apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  all: apply Exec.elem_of_mget_inv in Hget as [-> ->];
    cbn -[CPState.terminated_ts] in Hrun.
  all: destruct (decide (length base < TState.min_new_prom_view ts));
    [apply Exec.elem_of_mret_inv in Hrun as [Heq _];
      inversion Heq; subst; exact Howned|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
    rewrite Hterm in Hrun;
    [apply Exec.elem_of_mret_inv in Hrun as [Heq _];
      inversion Heq; subst; exact Howned|].
  - apply Exec.elem_of_mret_inv in Hrun as [Heq _].
    inversion Heq; subst; exact Howned.
  - apply Exec.elem_of_bind_elim in Hrun as [reset [[] [Hreset Hrun]]].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply Exec.elem_of_bind_elim in Hrun as [[next_pro next_st] [[] [Hinst Htail]]].
    destruct (collect_instruction_owned tid imem base isem proms
      (PPState.Make ts mem IIS.init) next_pro next_st () Howned Hmem Hinst)
      as [Howned' Hmem'].
    apply (retained_candidate_result prom) in Htail as [[_ [Heq _]]|Htail].
    { injection Heq as <- <-. assumption. }
    eapply IH; eassumption.
Qed.

Lemma run_error_owned {n} (tid : fin n) imem base isem (term : terminationCondition n)
    fuel proms ppst proms' ppst' err :
  owned tid proms → owned_suffix tid base (PPState.mem ppst) →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_to_termination isem prom term tid imem fuel
      (length base) (proms, ppst)) →
  owned tid proms'.
Proof.
  revert proms ppst.
  induction fuel as [|fuel IH]; intros proms [ts mem iis] Howned Hmem Herr.
  all: cbn [CPState.run_to_termination] in Herr.
  all: apply exec_error_bind in Herr as [Herr|[mid [ts0 [Hget Herr]]]];
    [inversion Herr|].
  all: apply Exec.elem_of_mget_inv in Hget as [-> ->];
    cbn -[CPState.terminated_ts] in Herr.
  all: destruct (decide (length base < TState.min_new_prom_view ts)); [inversion Herr|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
    rewrite Hterm in Herr; [inversion Herr|].
  - inversion Herr.
  - apply exec_error_bind in Herr as [Herr|[reset [[] [Hreset Herr]]]];
      [inversion Herr|].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply exec_error_bind in Herr as [Herr|[[next_pro next_st] [[] [Hinst Herr]]]].
    + exact (collect_instruction_error_owned tid imem base isem proms
        (PPState.Make ts mem IIS.init) proms' ppst' err Howned Hmem Herr).
    + destruct (collect_instruction_owned tid imem base isem proms
        (PPState.Make ts mem IIS.init) next_pro next_st () Howned Hmem Hinst)
        as [Howned' Hmem'].
      rewrite (retained_candidate_errors prom) in Herr. eapply IH; eassumption.
Qed.

Section Candidates.
Context {n : nat} (tid : fin n) (imem : memoryMap).
Theorem raw_promise_owner isem (term : terminationCondition n) fuel ts mem ev :
  ev ∈ (CPState.enumerate_results isem prom term tid imem fuel ts mem)
    .(CPState.promises prom) → Ev.tid ev = (tid : nat).
Proof.
  unfold CPState.enumerate_results. cbn. intro Hin.
  rewrite elem_of_remove_dups in Hin. apply list_elem_of_In, List.in_concat in Hin
    as [proms [Hsource Hev]].
  apply list_elem_of_In in Hsource. apply list_elem_of_In in Hev.
  assert (Howned : owned tid proms).
  { apply elem_of_app in Hsource as [Hsource|Hsource].
    - apply list_elem_of_fmap in Hsource as [[proms' p] [Heq Hsource]]. cbn in Heq. subst proms'.
      unfold Exec.success_state_list in Hsource.
      apply list_elem_of_fmap in Hsource as [[pair ending] [Heq Hrun]]. cbn in Heq. subst pair.
      exact (run_owned tid imem mem isem term fuel [] (PPState.Make ts mem IIS.init)
        proms p ending ltac:(constructor) (owned_refl tid mem) Hrun).
    - apply list_elem_of_fmap in Hsource as [[proms' p] [Heq Hsource]]. cbn in Heq. subst proms'.
      apply list_elem_of_fmap in Hsource as [[pair err] [Heq Hrun]]. cbn in Heq. subst pair.
      exact (run_error_owned tid imem mem isem term fuel [] (PPState.Make ts mem IIS.init)
        proms p err ltac:(constructor) (owned_refl tid mem) Hrun). }
  unfold owned in Howned. rewrite Forall_forall in Howned. exact (Howned ev Hev).
Qed.

End Candidates.
End Ownership.
End VMCollectedOwnership.
