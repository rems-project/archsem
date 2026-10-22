(******************************************************************************)
(* Normalizing all new messages of a terminating UM Sail thread               *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstConcreteCurrent PromiseFirstExecutionCurrent PromiseFirstSailCurrent
  PromiseFirstSailCertification PromiseFirstSailScheduling PromiseFirstSailThread
  PromiseFirstSailThreadCertification.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.
#[local] Typeclasses Transparent UMPromising.Memory.t.

Section NormalizeThread.
Context (nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region) (tid : fin n)
  (fin : UMPromising.TState.t) (finmem : UMPromising.Memory.t).

Local Lemma normalize_thread_bounded budget :
  ∀ st count,
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid)
    (sail_tiny_arm_sem nondet) count (PState.tstate tid st) (PState.events st) fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  length finmem ≤ budget + length (PState.events st) →
  ∃ before,
    rtc (StableCertifiedPromiseStep UMPromising nondet term) st before ∧
    PState.initmem before = PState.initmem st ∧
    PState.events before = finmem ∧
    ThreadInstructionExecution UMPromising tid (PState.initmem before)
      (sail_tiny_arm_sem nondet) term (PState.events before)
      (PState.tstate tid before) fin.
Proof.
  induction budget as [|budget IH]; intros st count Hsafe Hreach Hsteps Hterm Hbound.
  - destruct (UMThreadReplay.thread_steps_suffix tid (PState.initmem st)
      (term !!! tid) (sail_tiny_arm_sem nondet) _ _ _ _ _ Hsteps)
      as [extra Hextra].
    assert (Hnil : extra = []).
    { rewrite Hextra, length_app in Hbound. destruct extra; [reflexivity|cbn in Hbound; lia]. }
    subst extra. cbn in Hextra.
    exists st. split; [apply rtc_refl|]. split; [reflexivity|].
    split; [symmetry; exact Hextra|].
    eapply UMThreadReplay.fixed_thread_steps_execution; eassumption.
  - destruct (decide (finmem = PState.events st)) as [Hsame|Hnew].
    + exists st. split; [apply rtc_refl|]. split; [reflexivity|].
      split; [symmetry; exact Hsame|].
      eapply UMThreadReplay.fixed_thread_steps_execution; eassumption.
    + destruct (UMThreadReplay.first_new_message_split nondet tid (PState.initmem st)
        (term !!! tid) count (PState.tstate tid st) (PState.events st) fin finmem
        Hsteps Hnew) as [prefix_count [mid [msg [suffix_count [Hprefix Hsuffix]]]]].
      destruct (UMSail_first_new_message_promise_transition nondet term initMs code tid
        st prefix_count mid msg suffix_count fin finmem Hsafe Hreach Hprefix Hsuffix Hterm)
        as [next [threshold [Hpromise [Hstep [Hreach_next Hreplay]]]]].
      destruct (UMPromising_promise_success msg st next Hpromise)
        as [Himem [Hmem _]].
      assert (Hbound_next : length finmem ≤ budget + length (PState.events next)).
      { rewrite Hmem.
        change (length finmem ≤ budget + S (length (PState.events st))).
        lia. }
      destruct (IH next (prefix_count + suffix_count) Hsafe Hreach_next
        Hreplay Hterm Hbound_next)
        as [before [Hpromises [Himem_before [Hmem_before Hfinal]]]].
      exists before. split.
      * eapply rtc_l; [|exact Hpromises].
        exists tid, msg. split; [|exact Hpromise].
        eapply UMSail_first_new_message_stable_with_terminating_suffix; eassumption.
      * split; [rewrite Himem_before; exact Himem|].
        split; assumption.
Qed.

(** Every write added by this thread is moved into a finite prefix of actual,
    fuel-stable promise steps. The final thread execution preserves the
    complete final memory and thread state. Other threads' instruction
    executions are outside this statement. *)
Theorem UMSail_terminating_thread_normalization st count :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  UMThreadReplay.thread_steps tid (PState.initmem st) (term !!! tid)
    (sail_tiny_arm_sem nondet) count (PState.tstate tid st) (PState.events st) fin finmem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  ∃ before,
    rtc (StableCertifiedPromiseStep UMPromising nondet term) st before ∧
    PState.initmem before = PState.initmem st ∧
    PState.events before = finmem ∧
    ThreadInstructionExecution UMPromising tid (PState.initmem before)
      (sail_tiny_arm_sem nondet) term (PState.events before)
      (PState.tstate tid before) fin.
Proof.
  intros Hsafe Hreach Hsteps Hterm.
  eapply (normalize_thread_bounded (length finmem)); try eassumption. lia.
Qed.
End NormalizeThread.
