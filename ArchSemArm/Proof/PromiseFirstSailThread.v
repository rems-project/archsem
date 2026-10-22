(******************************************************************************)
(* Moving the first new UM message before a finite Sail thread prefix         *)
(******************************************************************************)

(** The instruction count, termination checks, and final thread state are
    preserved. The concrete Sail theorem derives fetch preservation and
    pending bounds from code immutability and promise-first reachability.
    Inter-thread scheduling, certification fuel, and VM replay remain separate
    obligations for the full final-state equivalence. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstExecutionCurrent PromiseFirstSailRead PromiseFirstSailControl
  PromiseFirstSailInstruction PromiseFirstSailReplay PromiseFirstSailSequence PromiseFirstSailCurrent PromiseFirstSailState.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module UMThreadReplay.
Import UMPromising UMReadReplay UMControlReplay UMContinuation UMInstructionReplay.
#[local] Typeclasses Transparent Memory.t.

(** A finite thread execution prefix using the actual instruction interpreter.
    Each instruction starts with fresh IIS and checks its termination condition. *)
Inductive thread_steps {n} (tid : fin n) imem bps (isem : iMon ()) :
    nat → TState.t → Memory.t → TState.t → Memory.t → Prop :=
| thread_steps_zero ts mem : thread_steps tid imem bps isem 0 ts mem ts mem
| thread_steps_succ count ts mem mid midmem fin finmem iis :
    CPState.terminated_ts UMPromising bps ts = false →
    Exec.elem_of_results (PPState.Make mid midmem iis, ())
      (cinterp (run_outcome' tid imem) isem (PPState.Make ts mem IIS.init)) →
    thread_steps tid imem bps isem count mid midmem fin finmem →
    thread_steps tid imem bps isem (S count) ts mem fin finmem.

Lemma thread_steps_trans {n} (tid : fin n) imem bps isem
    count ts mem mid midmem :
  thread_steps tid imem bps isem count ts mem mid midmem →
  ∀ suffix_count fin finmem,
  thread_steps tid imem bps isem suffix_count mid midmem fin finmem →
  thread_steps tid imem bps isem (count + suffix_count) ts mem fin finmem.
Proof.
  intro Hprefix.
  induction Hprefix as [ts mem|count ts mem next nextmem mid midmem iis Hterm Hinst Htail IH];
    intros suffix_count fin finmem Hsuffix; cbn.
  - exact Hsuffix.
  - econstructor; [exact Hterm|exact Hinst|apply IH, Hsuffix].
Qed.

Lemma thread_steps_suffix {n} (tid : fin n) imem bps isem count ts mem fin finmem :
  thread_steps tid imem bps isem count ts mem fin finmem →
  ∃ extra, finmem = (extra ++ mem)%list.
Proof.
  intro Htrace. induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH].
  - exists []. reflexivity.
  - destruct (instruction_facts tid imem isem _ _ _ Hinst) as [_ [_ [first Hfirst]]].
    destruct IH as [rest Hrest]. exists (rest ++ first)%list.
    cbn in Hfirst. rewrite Hrest, Hfirst, app_assoc. reflexivity.
Qed.

Lemma first_new_message_owner nondet {n} (tid : fin n) imem bps
    count ts mem fin finmem :
  thread_steps tid imem bps (sail_tiny_arm_sem nondet) count ts mem fin finmem →
  ∀ msg, finmem = msg :: mem → Msg.tid msg = (tid : nat).
Proof.
  intro Htrace.
  induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intros msg Hmem.
  - apply (f_equal length) in Hmem. cbn in Hmem. lia.
  - destruct (decide (midmem = mem)) as [Hsame|Hchanged].
    + apply IH. congruence.
    + destruct (UMSail_instruction_updating_outcome_replay nondet tid imem
        (PPState.Make ts mem IIS.init) (PPState.Make mid midmem iis) Hinst Hchanged)
        as [ev [out [before [after [ret [pre [Howner [Hmid _]]]]]]]].
      cbn in Hmid.
      destruct (thread_steps_suffix tid imem bps (sail_tiny_arm_sem nondet)
        _ _ _ _ _ Htail) as [rest Hrest].
      assert (Hnil : rest = []).
      { rewrite Hmid, Hmem in Hrest. apply (f_equal length) in Hrest.
        rewrite length_app in Hrest. destruct rest; [reflexivity|cbn in Hrest; lia]. }
      subst rest. cbn in Hrest. rewrite Hmid, Hmem in Hrest.
      injection Hrest as Heq. subst ev. exact Howner.
Qed.

Lemma first_new_message_split nondet {n} (tid : fin n) imem bps
    count ts mem fin finmem :
  thread_steps tid imem bps (sail_tiny_arm_sem nondet) count ts mem fin finmem →
  finmem ≠ mem →
  ∃ prefix_count mid msg suffix_count,
    thread_steps tid imem bps (sail_tiny_arm_sem nondet)
      prefix_count ts mem mid (msg :: mem) ∧
    thread_steps tid imem bps (sail_tiny_arm_sem nondet)
      suffix_count mid (msg :: mem) fin finmem.
Proof.
  intro Htrace.
  induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intro Hchanged; [contradiction|].
  destruct (decide (midmem = mem)) as [Hsame|Hnew].
  - subst midmem.
    destruct (IH Hchanged) as [prefix_count [next [msg [suffix_count [Hprefix Hsuffix]]]]].
    exists (S prefix_count), next, msg, suffix_count. split; [|exact Hsuffix].
    econstructor; eassumption.
  - destruct (UMSail_instruction_updating_outcome_replay nondet tid imem
      (PPState.Make ts mem IIS.init) (PPState.Make mid midmem iis) Hinst Hnew)
      as [msg [out [before [after [ret [pre [_ [Hmem _]]]]]]]].
    cbn in Hmem. subst midmem.
    exists 1, mid, msg, count. split; [|exact Htail].
    econstructor; [exact Hterm|exact Hinst|constructor].
Qed.

Definition thread_fetches {n} (tid : fin n) imem bps isem msg ts mem : Prop :=
  ∀ count ts' mem', thread_steps tid imem bps isem count ts mem ts' mem' →
    CPState.terminated_ts UMPromising bps ts' = false →
    preserved_fetches tid imem msg isem (PPState.Make ts' mem' IIS.init).

Lemma promise_terminated bps p ts :
  CPState.terminated_ts UMPromising bps (TState.promise p ts) =
  CPState.terminated_ts UMPromising bps ts.
Proof. destruct ts. reflexivity. Qed.

Lemma first_new_message_thread_replay {n} (tid : fin n) imem bps isem msg
    count ts mem fin finmem :
  thread_steps tid imem bps isem count ts mem fin finmem →
  finmem = msg :: mem →
  pending_bounded (PPState.Make ts mem IIS.init) →
  thread_fetches tid imem bps isem msg ts mem →
  TState.min_new_prom_view ts ≤ length mem ∧
  thread_steps tid imem bps isem count
    (TState.promise (S (length mem)) ts) (msg :: mem) fin finmem.
Proof.
  intro Htrace.
  induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intros Hmem Hpending Hfetch.
  - apply (f_equal length) in Hmem. cbn in Hmem. lia.
  - pose proof (Hfetch 0 ts mem (thread_steps_zero tid imem bps isem ts mem) Hterm) as Hfetch0.
    destruct (instruction_facts tid imem isem _ _ _ Hinst) as [Horder [Hprom [first Hfirst]]].
    cbn in Hfirst.
    destruct (decide (midmem = mem)) as [Hsame|Hchanged].
    + clear Hfirst. subst midmem.
      assert (Hpending_mid : pending_bounded (PPState.Make mid mem IIS.init)).
      { pose proof (instruction_pending_bounded tid imem isem _ _ _ Hpending Hinst) as Hmid.
        exact Hmid. }
      assert (Hfetch_mid : thread_fetches tid imem bps isem msg mid mem).
      { intros k next nextmem Hnext Hnextterm. eapply Hfetch; [|exact Hnextterm].
        econstructor; eassumption. }
      destruct (IH Hmem Hpending_mid Hfetch_mid) as [Hbound Hreplay].
      split.
      * pose proof (instruction_min_view_monotone tid imem isem _ _ _ Hinst) as Hmono.
        cbn in Hmono. lia.
      * econstructor.
        -- rewrite promise_terminated. exact Hterm.
        -- pose proof (unchanged_instruction_replay tid imem msg isem _ _ _
             Hpending Hfetch0 Hinst eq_refl) as Hreplayinst.
           apply Hreplayinst. cbn. lia.
        -- exact Hreplay.
    + destruct (thread_steps_suffix tid imem bps isem _ _ _ _ _ Htail) as [rest Hrest].
      destruct first as [|ev first]; [cbn in Hfirst; contradiction|].
      assert (Hempty : rest = [] ∧ first = []).
      { rewrite Hfirst, Hmem in Hrest. apply (f_equal length) in Hrest.
        rewrite length_app in Hrest. cbn in Hrest. rewrite length_app in Hrest.
        split; [destruct rest|destruct first]; try reflexivity; cbn in Hrest; lia. }
      destruct Hempty as [-> ->]. cbn in Hfirst, Hrest.
      rewrite Hrest, Hfirst in Hmem. injection Hmem as Hev. subst ev.
      destruct (single_new_message_replay tid imem msg isem _ _ _
        Hpending Hfetch0 Hinst Hfirst) as [Hbound Hreplayinst].
      split.
      * unfold order_view in Hbound. cbn in Hbound. unfold join, join_nat in Hbound. lia.
      * econstructor.
        -- rewrite promise_terminated. exact Hterm.
        -- exact Hreplayinst.
        -- exact Htail.
Qed.

Lemma thread_steps_source_nonterminated {n} (tid : fin n) imem bps isem
    count ts mem fin finmem :
  thread_steps tid imem bps isem count ts mem fin finmem →
  CPState.terminated_ts UMPromising bps fin = false →
  CPState.terminated_ts UMPromising bps ts = false.
Proof. intros Htrace Hfinal. inversion Htrace; subst; assumption. Qed.
#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.

Lemma thread_steps_sail_prefix nondet {n} (term : terminationCondition n)
    initMs (tid : fin n) imem count ts mem fin finmem :
  thread_steps tid imem (term !!! tid) (sail_tiny_arm_sem nondet) count ts mem fin finmem →
  SailThreadPrefix UMPromising nondet term initMs tid imem
    (PPState.Make ts mem IIS.init) (sail_tiny_arm_sem nondet) →
  (CPState.terminated_ts UMPromising (term !!! tid) fin = false →
    SailThreadPrefix UMPromising nondet term initMs tid imem
      (PPState.Make fin finmem IIS.init) (sail_tiny_arm_sem nondet)) ∧
  (count ≠ 0 → ∃ iis, SailThreadPrefix UMPromising nondet term initMs tid imem
    (PPState.Make fin finmem iis) (Ret ())).
Proof.
  intro Htrace.
  induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH]; intro Hstart.
  - split; [intros _; exact Hstart|contradiction].
  - assert (Hret : SailThreadPrefix UMPromising nondet term initMs tid imem
      (PPState.Make mid midmem iis) (Ret ())).
    { eapply sail_instruction_result_prefix; eassumption. }
    destruct count as [|count].
    + inversion Htail; subst. split.
      * intro Hfinal. eapply SailThreadPrefix_next with (ppst := PPState.Make fin finmem iis); eassumption.
      * intros _. exists iis. exact Hret.
    + assert (Hmidterm : CPState.terminated_ts UMPromising (term !!! tid) mid = false).
      { inversion Htail; assumption. }
      assert (Hmidprefix : SailThreadPrefix UMPromising nondet term initMs tid imem
        (PPState.Make mid midmem IIS.init) (sail_tiny_arm_sem nondet)).
      { eapply SailThreadPrefix_next with (ppst := PPState.Make mid midmem iis); eassumption. }
      destruct (IH Hmidprefix) as [Hbefore Hafter].
      split; [exact Hbefore|intros _; apply Hafter; lia].
Qed.

Lemma actual_thread_fetches nondet {n} (term : terminationCondition n)
    initMs code (tid : fin n) imem msg ts mem :
  UMSailNoSelfModifying nondet term initMs code →
  event_misses_code Msg.read_byte code msg →
  SailThreadPrefix UMPromising nondet term initMs tid imem
    (PPState.Make ts mem IIS.init) (sail_tiny_arm_sem nondet) →
  thread_fetches tid imem (term !!! tid) (sail_tiny_arm_sem nondet) msg ts mem.
Proof.
  intros Hsafe Hmiss Hstart count ts' mem' Hsteps Hterm.
  destruct (thread_steps_sail_prefix nondet term initMs tid imem _ _ _ _ _ Hsteps Hstart)
    as [Hprefix _].
  eapply UMSail_prefix_preserved_fetches; [exact Hsafe|exact Hmiss|apply Hprefix, Hterm].
Qed.

(** The replay conditions are obtained from the actual reachable Sail state
    and its code-immutability hypothesis, including the newly written message. *)
Theorem UMSail_first_new_message_thread_replay nondet {n}
    (term : terminationCondition n) initMs code (tid : fin n) st count fin msg :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  thread_steps tid (PState.initmem st) (term !!! tid) (sail_tiny_arm_sem nondet)
    count (PState.tstate tid st) (PState.events st) fin (msg :: PState.events st) →
  thread_steps tid (PState.initmem st) (term !!! tid) (sail_tiny_arm_sem nondet)
    count (TState.promise (S (length (PState.events st))) (PState.tstate tid st))
      (msg :: PState.events st) fin (msg :: PState.events st).
Proof.
  intros Hsafe Hreach Hsteps.
  assert (Hcount : count ≠ 0).
  { intro Heq. subst count. inversion Hsteps; subst.
    match goal with H : ?l = _ :: ?l |- _ =>
      apply (f_equal length) in H; cbn in H; lia
    | H : _ :: ?l = ?l |- _ => apply (f_equal length) in H; cbn in H; lia end. }
  assert (Hterm : CPState.terminated_ts UMPromising (term !!! tid) (PState.tstate tid st) = false).
  { inversion Hsteps; subst; [contradiction|assumption]. }
  assert (Hstart : SailThreadPrefix UMPromising nondet term initMs tid (PState.initmem st)
    (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init) (sail_tiny_arm_sem nondet)).
  { eapply SailThreadPrefix_start; eassumption. }
  destruct (thread_steps_sail_prefix nondet term initMs tid (PState.initmem st)
    _ _ _ _ _ Hsteps Hstart) as [_ Hfinal].
  destruct (Hfinal Hcount) as [iis Hlast].
  pose proof (sail_prefix_code_immutable _ _ _ _ _ _ Hsafe
    tid (PState.initmem st) _ (Ret ()) Hlast) as Hcode.
  assert (Hmiss : event_misses_code Msg.read_byte code msg).
  { apply Hcode. left; reflexivity. }
  assert (Hpending : pending_bounded
    (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init)).
  { intros p Hin. exact (proj2 (UMSail_promise_first_pending_bounds
      nondet term initMs st tid p Hreach Hin)). }
  pose proof (actual_thread_fetches nondet term initMs code tid (PState.initmem st)
    msg _ _ Hsafe Hmiss Hstart) as Hfetch.
  exact (proj2 (first_new_message_thread_replay tid (PState.initmem st) (term !!! tid)
    (sail_tiny_arm_sem nondet) msg _ _ _ _ _ Hsteps eq_refl Hpending Hfetch)).
Qed.

Lemma fixed_thread_steps_execution {n} (tid : fin n) imem
    (term : terminationCondition n) isem count ts mem fin finmem :
  thread_steps tid imem (term !!! tid) isem count ts mem fin finmem →
  finmem = mem →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  ThreadInstructionExecution UMPromising tid imem isem term mem ts fin.
Proof.
  intro Htrace.
  induction Htrace as [ts mem|count ts mem mid midmem fin finmem iis Hterm Hinst Htail IH];
    intros Hsame Hfinal.
  - constructor. exact Hfinal.
  - destruct (instruction_facts tid imem isem _ _ _ Hinst) as [_ [_ [first Hfirst]]].
    destruct (thread_steps_suffix tid imem (term !!! tid) isem _ _ _ _ _ Htail) as [rest Hrest].
    cbn in Hfirst.
    assert (Hempty : first = []).
    { rewrite Hfirst, Hsame in Hrest. apply (f_equal length) in Hrest.
      rewrite !length_app in Hrest. destruct first; [reflexivity|cbn in Hrest; lia]. }
    subst first. cbn in Hfirst. subst midmem.
    econstructor; [exact Hterm|exact Hinst|apply IH; assumption].
Qed.

Corollary UMSail_first_new_message_thread_execution nondet {n}
    (term : terminationCondition n) initMs code (tid : fin n) st count fin msg :
  UMSailNoSelfModifying nondet term initMs code →
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  thread_steps tid (PState.initmem st) (term !!! tid) (sail_tiny_arm_sem nondet)
    count (PState.tstate tid st) (PState.events st) fin (msg :: PState.events st) →
  CPState.terminated_ts UMPromising (term !!! tid) fin = true →
  ThreadInstructionExecution UMPromising tid (PState.initmem st)
    (sail_tiny_arm_sem nondet) term (msg :: PState.events st)
    (TState.promise (S (length (PState.events st))) (PState.tstate tid st)) fin.
Proof.
  intros Hsafe Hreach Hsteps Hterm. eapply fixed_thread_steps_execution.
  - eapply UMSail_first_new_message_thread_replay; eassumption.
  - reflexivity.
  - exact Hterm.
Qed.

End UMThreadReplay.
