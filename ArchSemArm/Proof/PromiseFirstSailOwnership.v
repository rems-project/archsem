(******************************************************************************)
(* Ownership of promises collected by actual UM certification                *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent
  PromiseFirstExecutionCurrent PromiseFirstSailReplay PromiseFirstSailCertification.

Local Open Scope stdpp.
Local Open Scope nat_scope.

Module UMCollectedOwnership.
Import UMPromising.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis Memory.t.

Definition owned (tid : nat) (msgs : list Msg.t) :=
  Forall (λ msg, Msg.tid msg = tid) msgs.
Definition owned_suffix (tid : nat) (base mem : Memory.t) :=
  ∃ extra, mem = (extra ++ base)%list ∧ owned tid extra.

Lemma owned_suffix_take tid base mem :
  owned_suffix tid base mem → owned tid (take (length mem - length base) mem).
Proof.
  intros [extra [-> Howned]]. rewrite length_app.
  replace (length extra + length base - length base) with (length extra) by lia.
  rewrite take_app_length. exact Howned.
Qed.

Lemma outcome_owned_suffix {n} (tid : fin n) imem out base ppst ppst' ret pre :
  owned_suffix tid base (PPState.mem ppst) →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  owned_suffix tid base (PPState.mem ppst').
Proof.
  intros [extra [Hmem Howned]] Hout. destruct pre as [pre|].
  - destruct (UMSailReplay.run_outcome_promise_replay_one tid imem out ppst ppst'
      ret pre Hout) as [msg [Hnew [Howner _]]].
    exists (msg :: extra). split; [rewrite Hnew, Hmem; reflexivity|].
    constructor; assumption.
  - destruct (UMMemoryGrowth.outcome_memory_growth n tid imem out ppst ppst' ret None Hout)
      as [Hsame|[added [pre [_ [_ [Hbad _]]]]]]; [|discriminate].
    exists extra. split; [rewrite Hsame; exact Hmem|exact Howned].
Qed.

Lemma collect_outcome_owned {n} (tid : fin n) imem base out proms ppst proms' ppst' ret :
  owned tid proms → owned_suffix tid base (PPState.mem ppst) →
  Exec.elem_of_results ((proms', ppst'), ret)
    (CPState.run_outcome_with_promise UMPromising tid imem (length base) out (proms, ppst)) →
  owned tid proms' ∧ owned_suffix tid base (PPState.mem ppst').
Proof.
  intros Hproms Hmem Hrun.
  destruct (collect_outcome_inv UMPromising tid imem (length base) out
    proms ppst proms' ppst' ret Hrun) as [pre [Hout Hcollect]].
  pose proof (outcome_owned_suffix tid imem out base ppst ppst' ret pre Hmem Hout) as Hmem'.
  split; [|exact Hmem']. rewrite Hcollect. destruct pre as [pre|]; [|exact Hproms].
  destruct (decide (pre ≤ length base)); [|exact Hproms].
  apply Forall_app. split; [apply owned_suffix_take, Hmem'|exact Hproms].
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
    (CPState.run_outcome_with_promise UMPromising tid imem base out (proms, ppst)) →
  owned tid proms'.
Proof.
  intros Howned Herr. unfold CPState.run_outcome_with_promise in Herr.
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
    (cinterp (CPState.run_outcome_with_promise UMPromising tid imem (length base))
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
    (cinterp (CPState.run_outcome_with_promise UMPromising tid imem (length base))
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
    (CPState.run_to_termination isem UMPromising term tid imem fuel
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
  all: destruct (CPState.terminated_ts UMPromising (term !!! tid) ts) eqn:Hterm;
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
    eapply IH; eassumption.
Qed.

Lemma run_error_owned {n} (tid : fin n) imem base isem (term : terminationCondition n)
    fuel proms ppst proms' ppst' err :
  owned tid proms → owned_suffix tid base (PPState.mem ppst) →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_to_termination isem UMPromising term tid imem fuel
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
  all: destruct (CPState.terminated_ts UMPromising (term !!! tid) ts) eqn:Hterm;
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
      eapply IH; eassumption.
Qed.

Theorem enumerated_promise_owner {n} (tid : fin n) imem isem
    (term : terminationCondition n) fuel ts mem msg :
  msg ∈ (CPState.enumerate_results isem UMPromising term tid imem fuel ts mem)
    .(CPState.promises UMPromising) →
  Msg.tid msg = (tid : nat).
Proof.
  intro Hcandidate.
  destruct (enumerate_results_promise_witness (prom := UMPromising) isem
    term tid imem fuel ts mem msg ltac:(intros; assumption) Hcandidate)
    as [proms [ppst [Hin Hcert]]].
  assert (Hempty : owned tid []). { constructor. }
  assert (Hmem : owned_suffix tid mem mem).
  { exists []. split; [reflexivity|constructor]. }
  assert (Howned : owned tid proms).
  { destruct Hcert as [[ending Hcert]|[err Hcert]].
    - exact (run_owned tid imem mem isem term fuel [] (PPState.Make ts mem IIS.init)
        proms ppst ending Hempty Hmem Hcert).
    - exact (run_error_owned tid imem mem isem term fuel [] (PPState.Make ts mem IIS.init)
        proms ppst err Hempty Hmem Hcert). }
  unfold owned in Howned. rewrite Forall_forall in Howned. exact (Howned msg Hin).
Qed.

End UMCollectedOwnership.
