(******************************************************************************)
(* Positive-sized writes in VM certification candidates                        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstExecutionCurrent
  PromiseFirstSailCertification PromiseFirstSailVMEventValidity.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMEventCertification.
Import VMPromising VMEventValidity.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis Memory.t.

Lemma growth_take base mem : growth base mem →
  Forall event_positive (take (length mem - length base) mem).
Proof.
  intros [extra [-> Hpositive]]. rewrite length_app.
  replace (length extra + length base - length base) with (length extra) by lia.
  rewrite take_app_length. exact Hpositive.
Qed.

Section Certification.
Context (bbm : bool) {n : nat} (tid : fin n) (imem : memoryMap).
Local Notation prom := (VMPromising bbm).

Lemma collect_outcome base out proms p proms' p' ret :
  outcome_positive out → Forall event_positive proms → growth base (PPState.mem p) →
  Exec.elem_of_results ((proms', p'), ret)
    (CPState.run_outcome_with_promise prom tid imem (length base) out (proms, p)) →
  Forall event_positive proms' ∧ growth base (PPState.mem p').
Proof.
  intros Hout Hproms Hmem Hrun.
  destruct (collect_outcome_inv prom tid imem (length base) out proms p proms' p' ret Hrun)
    as [pre [Hhandle Hcollect]].
  assert (Hmem' : growth base (PPState.mem p')).
  { eapply growth_trans; [exact Hmem|eapply outcome_growth; eassumption]. }
  split; [|exact Hmem']. rewrite Hcollect. destruct pre as [pre|]; [|exact Hproms].
  destruct (decide (pre ≤ length base)); [|exact Hproms].
  apply Forall_app. split; [apply growth_take, Hmem'|exact Hproms].
Qed.

Local Lemma lift_snd_error {A B E R} (a a' : A) (b b' : B)
    (e : Exec.t B E R) err :
  ((a', b'), err) ∈ Exec.errors (Exec.liftSt snd e (a, b)) → a' = a.
Proof.
  unfold Exec.liftSt, Exec.liftSt_full, Exec.map_state. cbn.
  intro Hin. apply list_elem_of_fmap in Hin as [[s er] [Heq _]].
  inversion Heq. reflexivity.
Qed.

(** An error in a handler occurs before it adds candidates. *)
Lemma collect_outcome_error base out proms p proms' p' err :
  Forall event_positive proms →
  ((proms', p'), err) ∈ Exec.errors
    (CPState.run_outcome_with_promise prom tid imem base out (proms, p)) →
  Forall event_positive proms'.
Proof.
  intros Hpositive Herr. unfold CPState.run_outcome_with_promise in Herr.
  apply exec_error_bind in Herr as [Herr|[mid [[ret pre] [Hout Herr]]]].
  - apply lift_snd_error in Herr. subst proms'. exact Hpositive.
  - destruct pre as [pre|].
    + destruct (decide (pre ≤ base)); [|inversion Herr].
      apply exec_error_bind in Herr as [Herr|[mid' [mem [Hget Herr]]]]; [inversion Herr|].
      apply exec_error_bind in Herr as [Herr|[last [[] [Hset Herr]]]]; inversion Herr.
    + inversion Herr.
Qed.

Lemma collect_instruction {A} base (mon : iMon A) proms p proms' p' ret :
  positive mon → Forall event_positive proms → growth base (PPState.mem p) →
  Exec.elem_of_results ((proms', p'), ret)
    (cinterp (CPState.run_outcome_with_promise prom tid imem (length base)) mon (proms, p)) →
  Forall event_positive proms' ∧ growth base (PPState.mem p').
Proof.
  revert proms p proms' p' ret.
  induction mon as [value|[out|[choices]] k IH]; intros proms p proms' p' ret Hp Hproms Hmem Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [Heq _].
    injection Heq as <- <-. auto.
  - destruct Hp as [Ho Hk]. cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [[next_pro next_st] [r [Hout Htail]]].
    destruct (collect_outcome base out proms p next_pro next_st r Ho Hproms Hmem Hout)
      as [Hproms' Hmem'].
    eapply IH; [apply Hk|eassumption..].
  - cbn in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
    apply Exec.elem_of_mchoose_inv in Hchoice as ->. eapply IH; [apply Hp|eassumption..].
Qed.

Lemma collect_instruction_error {A} base (mon : iMon A) proms p proms' p' err :
  positive mon → Forall event_positive proms → growth base (PPState.mem p) →
  ((proms', p'), err) ∈ Exec.errors
    (cinterp (CPState.run_outcome_with_promise prom tid imem (length base)) mon (proms, p)) →
  Forall event_positive proms'.
Proof.
  revert proms p.
  induction mon as [value|[out|[choices]] k IH]; intros proms p Hp Hproms Hmem Herr.
  - inversion Herr.
  - destruct Hp as [Ho Hk]. cbn in Herr.
    apply exec_error_bind in Herr as [Herr|[[next_pro next_st] [r [Hout Herr]]]].
    + eapply collect_outcome_error; eassumption.
    + destruct (collect_outcome base out proms p next_pro next_st r Ho Hproms Hmem Hout)
        as [Hproms' Hmem'].
      eapply IH; [apply Hk|eassumption..].
  - cbn in Herr. apply exec_error_bind in Herr as [Herr|[mid [r [Hchoice Herr]]]].
    + inversion Herr.
    + apply Exec.elem_of_mchoose_inv in Hchoice as ->. eapply IH; [apply Hp|eassumption..].
Qed.

Lemma run_positive base isem (term : terminationCondition n) fuel proms p proms' p' ending :
  positive isem → Forall event_positive proms → growth base (PPState.mem p) →
  Exec.elem_of_results ((proms', p'), ending)
    (CPState.run_to_termination isem prom term tid imem fuel (length base) (proms, p)) →
  Forall event_positive proms'.
Proof.
  intro Hpositive. revert proms p.
  induction fuel as [|fuel IH]; intros proms [ts mem iis] Hproms Hmem Hrun.
  all: cbn [CPState.run_to_termination] in Hrun.
  all: apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  all: apply Exec.elem_of_mget_inv in Hget as [-> ->]; cbn -[CPState.terminated_ts] in Hrun.
  all: destruct (decide (length base < TState.min_new_prom_view ts));
    [apply Exec.elem_of_mret_inv in Hrun as [Heq _]; inversion Heq; subst; exact Hproms|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm; rewrite Hterm in Hrun;
    [apply Exec.elem_of_mret_inv in Hrun as [Heq _]; inversion Heq; subst; exact Hproms|].
  - apply Exec.elem_of_mret_inv in Hrun as [Heq _]. inversion Heq; subst; exact Hproms.
  - apply Exec.elem_of_bind_elim in Hrun as [reset [[] [Hreset Hrun]]].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply Exec.elem_of_bind_elim in Hrun as [[next_pro next_st] [[] [Hinst Htail]]].
    destruct (collect_instruction base isem proms (PPState.Make ts mem IIS.init)
      next_pro next_st () Hpositive Hproms Hmem Hinst) as [Hproms' Hmem'].
    eapply IH; eassumption.
Qed.

Lemma run_error_positive base isem (term : terminationCondition n) fuel proms p proms' p' err :
  positive isem → Forall event_positive proms → growth base (PPState.mem p) →
  ((proms', p'), err) ∈ Exec.errors
    (CPState.run_to_termination isem prom term tid imem fuel (length base) (proms, p)) →
  Forall event_positive proms'.
Proof.
  intro Hpositive. revert proms p.
  induction fuel as [|fuel IH]; intros proms [ts mem iis] Hproms Hmem Herr.
  all: cbn [CPState.run_to_termination] in Herr.
  all: apply exec_error_bind in Herr as [Herr|[mid [ts0 [Hget Herr]]]]; [inversion Herr|].
  all: apply Exec.elem_of_mget_inv in Hget as [-> ->]; cbn -[CPState.terminated_ts] in Herr.
  all: destruct (decide (length base < TState.min_new_prom_view ts)); [inversion Herr|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
    rewrite Hterm in Herr; [inversion Herr|].
  - inversion Herr.
  - apply exec_error_bind in Herr as [Herr|[reset [[] [Hreset Herr]]]]; [inversion Herr|].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply exec_error_bind in Herr as [Herr|[[next_pro next_st] [[] [Hinst Herr]]]].
    + exact (collect_instruction_error base isem proms (PPState.Make ts mem IIS.init)
        proms' p' err Hpositive Hproms Hmem Herr).
    + destruct (collect_instruction base isem proms (PPState.Make ts mem IIS.init)
        next_pro next_st () Hpositive Hproms Hmem Hinst) as [Hproms' Hmem'].
      eapply IH; eassumption.
Qed.

(** The unreduced runner also retains candidates from paths ending in an error. *)
Theorem raw_promise_positive nondet (term : terminationCondition n) fuel ts mem ev :
  ev ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) prom term tid imem fuel ts mem)
    .(CPState.promises prom) → event_positive ev.
Proof.
  unfold CPState.enumerate_results. cbn. intro Hin.
  rewrite elem_of_remove_dups in Hin. apply list_elem_of_In, List.in_concat in Hin
    as [proms [Hsource Hev]].
  apply list_elem_of_In in Hsource. apply list_elem_of_In in Hev.
  assert (Hpositive : Forall event_positive proms).
  { apply elem_of_app in Hsource as [Hsource|Hsource].
    - apply list_elem_of_fmap in Hsource as [[proms' p] [Heq Hsource]]. cbn in Heq. subst proms'.
      unfold Exec.success_state_list in Hsource.
      apply list_elem_of_fmap in Hsource as [[pair ending] [Heq Hrun]]. cbn in Heq. subst pair.
      exact (run_positive mem (sail_tiny_arm_sem nondet) term fuel [] (PPState.Make ts mem IIS.init)
        proms p ending (sail_tiny_arm_positive nondet) ltac:(constructor) (growth_refl mem) Hrun).
    - apply list_elem_of_fmap in Hsource as [[proms' p] [Heq Hsource]]. cbn in Heq. subst proms'.
      apply list_elem_of_fmap in Hsource as [[pair err] [Heq Hrun]]. cbn in Heq. subst pair.
      exact (run_error_positive mem (sail_tiny_arm_sem nondet) term fuel [] (PPState.Make ts mem IIS.init)
        proms p err (sail_tiny_arm_positive nondet) ltac:(constructor) (growth_refl mem) Hrun). }
  rewrite Forall_forall in Hpositive. exact (Hpositive ev Hev).
Qed.

(** Promise filtering preserves the size restriction. *)
Theorem enumerated_promise_positive nondet (term : terminationCondition n) fuel ts mem ev :
  ev ∈ (CPState.enumerate_results_filtered (sail_tiny_arm_sem nondet) prom term tid imem fuel ts mem)
    .(CPState.promises prom) → event_positive ev.
Proof.
  intro Hcandidate.
  assert (Hfilter : ∀ candidates event,
    event ∈ Promising.filter_promises prom n tid mem candidates → event ∈ candidates).
  { intros candidates event H. cbn [Promising.filter_promises VMPromising] in H.
    unfold filter_commuting_promises in H. destruct mem; [exact H|].
    apply list_elem_of_filter in H as [_ H]. exact H. }
  destruct (enumerate_results_promise_witness (prom := prom) (sail_tiny_arm_sem nondet)
    term tid imem fuel ts mem ev Hfilter Hcandidate) as [proms [p [Hin Hcert]]].
  assert (Hpositive : Forall event_positive proms).
  { destruct Hcert as [[ending Hcert]|[err Hcert]].
    - exact (run_positive mem (sail_tiny_arm_sem nondet) term fuel [] (PPState.Make ts mem IIS.init)
        proms p ending (sail_tiny_arm_positive nondet) ltac:(constructor) (growth_refl mem) Hcert).
    - exact (run_error_positive mem (sail_tiny_arm_sem nondet) term fuel [] (PPState.Make ts mem IIS.init)
        proms p err (sail_tiny_arm_positive nondet) ltac:(constructor) (growth_refl mem) Hcert). }
  rewrite Forall_forall in Hpositive. exact (Hpositive ev Hin).
Qed.
End Certification.
End VMEventCertification.
