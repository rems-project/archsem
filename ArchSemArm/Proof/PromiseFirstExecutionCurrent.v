(******************************************************************************)
(* Successful thread exploration with no collected promises                  *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSem Require Import GenPromising.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** A successful outcome either leaves memory unchanged, or prepends at least
    one event and reports a prerequisite view no later than the old memory.
    This bound makes the first new event visible to the promise collector. *)
Definition OutcomeMemoryGrowth (prom : Promising.Model) : Prop :=
  ∀ n (tid : fin n) initmem out ppst ppst' ret vpre,
    Exec.elem_of_results (ppst', (ret, vpre))
      (prom.(Promising.handle_outcome) n tid initmem out ppst) →
    PPState.mem ppst' = PPState.mem ppst ∨
    ∃ extra pre,
      extra ≠ [] ∧
      PPState.mem ppst' = (extra ++ PPState.mem ppst)%list ∧
      vpre = Some pre ∧ pre ≤ length (PPState.mem ppst).

Section Exploration.
Context (prom : Promising.Model) {n : nat} (tid : fin n) (initmem : memoryMap).
Local Notation mEvent := prom.(Promising.mEvent).
Local Notation ppState :=
  (PPState.t prom.(Promising.tState) mEvent prom.(Promising.iis)).

Lemma collect_outcome_intro base out proms (ppst : ppState) ppst' ret vpre :
  Exec.elem_of_results (ppst', (ret, vpre))
    (prom.(Promising.handle_outcome) n tid initmem out ppst) →
  Exec.elem_of_results
    ((match vpre with
      | Some pre => if decide (pre ≤ base) then
          (take (length (PPState.mem ppst') - base) (PPState.mem ppst') ++ proms)%list
        else proms
      | None => proms
      end, ppst'), ret)
    (CPState.run_outcome_with_promise prom tid initmem base out (proms, ppst)).
Proof.
  intro Hout. unfold CPState.run_outcome_with_promise.
  eapply Exec.elem_of_bind_intro.
  - exact (Exec.elem_of_liftSt (proms, ppst) ppst' (ret, vpre) snd
      (prom.(Promising.handle_outcome) n tid initmem out) Hout).
  - destruct vpre as [pre|]; [|apply Exec.elem_of_mret].
    destruct (decide (pre ≤ base)); [|apply Exec.elem_of_mret].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_mret.
Qed.

(** Collecting promises preserves every successful instruction path. The
    collector's final list is existential because an instruction can append
    several events, or report a prerequisite view beyond the chosen base. *)
Lemma collect_instruction_complete {A} base (mon : iMon A)
    proms (ppst : ppState) ppst' ret :
  Exec.elem_of_results (ppst', ret)
    (cinterp (λ out, prom.(Promising.handle_outcome) n tid initmem out |$> fst)
      mon ppst) →
  ∃ proms', Exec.elem_of_results ((proms', ppst'), ret)
    (cinterp (CPState.run_outcome_with_promise prom tid initmem base)
      mon (proms, ppst)).
Proof.
  revert proms ppst ppst' ret.
  induction mon as [a|call k IH]; intros proms ppst ppst' ret Hrun.
  - cbn in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    exists proms. apply Exec.elem_of_mret.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]].
      cbn in Heq. subst res.
      pose proof (collect_outcome_intro base out proms ppst mid r pre Hout) as Hcollect.
      match type of Hcollect with
      | Exec.elem_of_results ((?collected, _), _) _ =>
          destruct (IH r collected mid ppst' ret Htail) as [proms' Htail']
      end.
      exists proms'. eapply Exec.elem_of_bind_intro; eassumption.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoice Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoice as ->.
      destruct (IH r proms ppst ppst' ret Htail) as [proms' Htail'].
      exists proms'. eapply Exec.elem_of_bind_intro;
        [apply Exec.elem_of_mchoose|exact Htail'].
Qed.

Lemma collect_outcome_inv base out proms (ppst : ppState)
    proms' ppst' (ret : eff_ret out) :
  Exec.elem_of_results ((proms', ppst'), ret)
    (CPState.run_outcome_with_promise prom tid initmem base out (proms, ppst)) →
  ∃ vpre,
    Exec.elem_of_results (ppst', (ret, vpre))
      (prom.(Promising.handle_outcome) n tid initmem out ppst) ∧
    proms' =
      match vpre with
      | Some pre => if decide (pre ≤ base) then
          (take (length (PPState.mem ppst') - base) (PPState.mem ppst') ++ proms)%list
        else proms
      | None => proms
      end.
Proof.
  unfold CPState.run_outcome_with_promise.
  intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun
    as [pair_mid [[res vpre] [Hhandle Htail]]].
  apply Exec.elem_of_liftSt_inv in Hhandle as [pp_mid [-> Hhandle]].
  cbn in Hhandle.
  destruct vpre as [pre|].
  - destruct (decide (pre ≤ base)) as [Hle|Hgt].
    + apply Exec.elem_of_bind_elim in Htail as [pair_get [mem [Hget Htail]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      apply Exec.elem_of_bind_elim in Htail as [pair_set [[] [Hset Hret]]].
      apply Exec.elem_of_mset_inv in Hset as ->.
      apply Exec.elem_of_mret_inv in Hret as [Heq ->].
      inversion Heq; subst proms' ppst'.
      exists (Some pre). split; [exact Hhandle|].
      rewrite decide_True by exact Hle. reflexivity.
    + apply Exec.elem_of_mret_inv in Htail as [Heq ->].
      inversion Heq; subst proms' ppst'.
      exists (Some pre). split; [exact Hhandle|].
      rewrite decide_False by exact Hgt. reflexivity.
  - apply Exec.elem_of_mret_inv in Htail as [Heq ->].
    inversion Heq; subst proms' ppst'.
    exists None. split; [exact Hhandle|reflexivity].
Qed.

Lemma collect_outcome_suffix base out proms (ppst : ppState)
    proms' ppst' ret :
  Exec.elem_of_results ((proms', ppst'), ret)
    (CPState.run_outcome_with_promise prom tid initmem base out (proms, ppst)) →
  ∃ extra, proms' = (extra ++ proms)%list.
Proof.
  intro Hrun.
  destruct (collect_outcome_inv _ _ _ _ _ _ _ Hrun) as [vpre [_ Hproms]].
  rewrite Hproms. destruct vpre as [pre|].
  - destruct (decide (pre ≤ base)); [eexists; reflexivity|exists []; reflexivity].
  - exists []. reflexivity.
Qed.

Lemma collect_outcome_empty base out proms (ppst : ppState) ppst' ret :
  OutcomeMemoryGrowth prom →
  length (PPState.mem ppst) = base →
  Exec.elem_of_results (([], ppst'), ret)
    (CPState.run_outcome_with_promise prom tid initmem base out (proms, ppst)) →
  proms = [] ∧ PPState.mem ppst' = PPState.mem ppst ∧
  Exec.elem_of_results (ppst', ret)
    ((prom.(Promising.handle_outcome) n tid initmem out |$> fst) ppst).
Proof.
  intros Hgrowth Hbase Hrun.
  destruct (collect_outcome_suffix _ _ _ _ _ _ _ Hrun) as [extra Hsuffix].
  symmetry in Hsuffix. apply app_eq_nil in Hsuffix as [_ Hproms].
  split; [exact Hproms|].
  destruct (collect_outcome_inv _ _ _ _ _ _ _ Hrun) as [vpre [Hout Hcol]].
  split.
  - destruct (Hgrowth n tid initmem out ppst ppst' ret vpre Hout)
      as [Hmem|[added [pre [Hnonempty [Hmem [Hv Hpre]]]]]]; [exact Hmem|].
    subst vpre. rewrite decide_True in Hcol by lia.
    symmetry in Hcol. apply app_eq_nil in Hcol as [Htake _].
    apply (f_equal (@length mEvent)) in Htake.
    rewrite length_take, Hmem, length_app in Htake.
    assert (0 < length added) by (destruct added; [contradiction|cbn; lia]).
    cbn in Htake. exfalso. lia.
  - exact (Exec.elem_of_fmap_intro ppst ppst' (ret, vpre)
      (prom.(Promising.handle_outcome) n tid initmem out) fst Hout).
Qed.

Lemma collect_instruction_suffix {A} base (mon : iMon A)
    proms (ppst : ppState) proms' ppst' ret :
  Exec.elem_of_results ((proms', ppst'), ret)
    (cinterp (CPState.run_outcome_with_promise prom tid initmem base)
      mon (proms, ppst)) →
  ∃ extra, proms' = (extra ++ proms)%list.
Proof.
  revert proms ppst proms' ppst' ret.
  induction mon as [r|call k IH]; intros proms ppst proms' ppst' ret Hrun;
    cbn in Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [Heq _].
    inversion Heq. exists []. reflexivity.
  - destruct call as [out|[choices]].
    + apply Exec.elem_of_bind_elim in Hrun
        as [[proms_mid pp_mid] [res [Hout Htail]]].
      destruct (collect_outcome_suffix _ _ _ _ _ _ _ Hout) as [a Ha].
      destruct (IH _ _ _ _ _ _ Htail) as [b Hb].
      exists (b ++ a)%list. rewrite Hb, Ha, app_assoc. reflexivity.
    + apply Exec.elem_of_bind_elim in Hrun as [pair_mid [res [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      eapply IH. exact Htail.
Qed.

Lemma collect_instruction_empty {A} base (mon : iMon A)
    proms (ppst : ppState) ppst' ret :
  OutcomeMemoryGrowth prom →
  length (PPState.mem ppst) = base →
  Exec.elem_of_results (([], ppst'), ret)
    (cinterp (CPState.run_outcome_with_promise prom tid initmem base)
      mon (proms, ppst)) →
  proms = [] ∧ PPState.mem ppst' = PPState.mem ppst ∧
  Exec.elem_of_results (ppst', ret)
    (cinterp (λ out, prom.(Promising.handle_outcome) n tid initmem out |$> fst)
      mon ppst).
Proof.
  intro Hgrowth. revert proms ppst ppst' ret.
  induction mon as [r|call k IH]; intros proms ppst ppst' ret Hbase Hrun;
    cbn in Hrun |- *.
  - apply Exec.elem_of_mret_inv in Hrun as [Heq ->].
    inversion Heq; subst. repeat split; try reflexivity.
    apply Exec.elem_of_mret.
  - destruct call as [out|[choices]].
    + apply Exec.elem_of_bind_elim in Hrun
        as [[proms_mid pp_mid] [res [Hout Htail]]].
      destruct (collect_instruction_suffix _ (k res) _ _ _ _ _ Htail)
        as [extra Hsuffix].
      symmetry in Hsuffix. apply app_eq_nil in Hsuffix as [_ ->].
      destruct (collect_outcome_empty _ _ _ _ _ _ Hgrowth Hbase Hout)
        as [Hproms [Hmem Hout']].
      destruct (IH _ _ _ _ _ ltac:(rewrite Hmem; exact Hbase) Htail)
        as [_ [Hmem' Htail']].
      split; [exact Hproms|]. split; [congruence|].
      eapply Exec.elem_of_bind_intro; eassumption.
    + apply Exec.elem_of_bind_elim in Hrun as [pair_mid [res [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      destruct (IH _ _ _ _ _ Hbase Htail) as [Hproms [Hmem Htail']].
      split; [exact Hproms|]. split; [exact Hmem|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|exact Htail'].
Qed.

(** A terminating instruction sequence at a fixed shared history.  Each
    instruction starts with fresh intra-instruction state, as [run_tid] does. *)
Inductive ThreadInstructionExecution (isem : iMon ())
    (term : terminationCondition n) (mem : list mEvent) :
    prom.(Promising.tState) → prom.(Promising.tState) → Prop :=
| ThreadInstructionExecution_done ts :
    CPState.terminated_ts prom (term !!! tid) ts = true →
    ThreadInstructionExecution isem term mem ts ts
| ThreadInstructionExecution_step ts ts_mid ts_final iis :
    CPState.terminated_ts prom (term !!! tid) ts = false →
    Exec.elem_of_results (PPState.Make ts_mid mem iis, ())
      (cinterp (λ out, prom.(Promising.handle_outcome) n tid initmem out |$> fst)
        isem (PPState.Make ts mem prom.(Promising.iis_init))) →
    ThreadInstructionExecution isem term mem ts_mid ts_final →
    ThreadInstructionExecution isem term mem ts ts_final.

Lemma collect_thread_suffix isem (term : terminationCondition n) fuel base
    proms (ppst : ppState) proms' ppst' ending :
  Exec.elem_of_results ((proms', ppst'), ending)
    (CPState.run_to_termination isem prom term tid initmem fuel base (proms, ppst)) →
  ∃ extra, proms' = (extra ++ proms)%list.
Proof.
  revert proms ppst proms' ppst' ending.
  induction fuel as [|fuel IH];
    intros proms [ts mem iis] proms' ppst' ending Hrun.
  all: cbn [CPState.run_to_termination] in Hrun.
  all: apply Exec.elem_of_bind_elim in Hrun as [pair_get [ts0 [Hget Hrun]]].
  all: apply Exec.elem_of_mget_inv in Hget as [-> ->];
    cbn -[CPState.terminated_ts] in Hrun.
  all: destruct (decide (base < prom.(Promising.tState_min_new_prom_view) ts));
    [apply Exec.elem_of_mret_inv in Hrun as [Heq _];
      inversion Heq; exists []; reflexivity|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
    rewrite Hterm in Hrun;
    [apply Exec.elem_of_mret_inv in Hrun as [Heq _];
      inversion Heq; exists []; reflexivity|].
  - apply Exec.elem_of_mret_inv in Hrun as [Heq _].
    inversion Heq. exists []. reflexivity.
  - apply Exec.elem_of_bind_elim in Hrun as [pair_reset [[] [Hreset Hrun]]].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply Exec.elem_of_bind_elim in Hrun
      as [[proms_mid pp_mid] [[] [Hinst Htail]]].
    destruct (collect_instruction_suffix base isem _ _ _ _ _ Hinst) as [a Ha].
    destruct (IH _ _ _ _ _ Htail) as [b Hb].
    exists (b ++ a)%list. rewrite Hb, Ha, app_assoc. reflexivity.
Qed.

Lemma collect_thread_empty isem (term : terminationCondition n) fuel base
    proms (ppst : ppState) ppst' :
  OutcomeMemoryGrowth prom →
  length (PPState.mem ppst) = base →
  Exec.elem_of_results (([], ppst'), CPState.Terminated)
    (CPState.run_to_termination isem prom term tid initmem fuel base (proms, ppst)) →
  proms = [] ∧ PPState.mem ppst' = PPState.mem ppst ∧
  ThreadInstructionExecution isem term (PPState.mem ppst)
    (PPState.state ppst) (PPState.state ppst').
Proof.
  intro Hgrowth. revert proms ppst ppst'.
  induction fuel as [|fuel IH]; intros proms [ts mem iis] ppst' Hbase Hrun.
  all: cbn [CPState.run_to_termination] in Hrun.
  all: apply Exec.elem_of_bind_elim in Hrun as [pair_get [ts0 [Hget Hrun]]].
  all: apply Exec.elem_of_mget_inv in Hget as [-> ->];
    cbn -[CPState.terminated_ts] in Hrun.
  all: destruct (decide (base < prom.(Promising.tState_min_new_prom_view) ts));
    [apply Exec.elem_of_mret_inv in Hrun as [_ Hending]; discriminate|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
    rewrite Hterm in Hrun.
  1,3: apply Exec.elem_of_mret_inv in Hrun as [Heq _];
    inversion Heq; subst; repeat split; try reflexivity;
    apply ThreadInstructionExecution_done; exact Hterm.
  - apply Exec.elem_of_mret_inv in Hrun as [_ Hending]. discriminate.
  - apply Exec.elem_of_bind_elim in Hrun as [pair_reset [[] [Hreset Hrun]]].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply Exec.elem_of_bind_elim in Hrun
      as [[proms_mid pp_mid] [[] [Hinst Htail]]].
    destruct (collect_thread_suffix isem term fuel base _ _ _ _ _ Htail)
      as [extra Hsuffix].
    symmetry in Hsuffix. apply app_eq_nil in Hsuffix as [_ ->].
    destruct (collect_instruction_empty base isem proms
      (PPState.Make ts mem prom.(Promising.iis_init)) pp_mid ()
      Hgrowth Hbase Hinst)
      as [Hproms [Hmem Hinst']].
    cbn in Hmem.
    destruct (IH _ _ _ ltac:(rewrite Hmem; exact Hbase) Htail)
      as [_ [Hmem' Htrace]].
    cbn. split; [exact Hproms|]. split; [congruence|].
    destruct pp_mid as [ts_mid mem_mid iis_mid]. cbn in Hmem. subst mem_mid.
    eapply ThreadInstructionExecution_step; eassumption.
Qed.

End Exploration.

(** Enumeration can omit the explored memory from its final-state candidate:
    the empty collected list guarantees that memory is exactly the starting
    history, provided the model satisfies the outcome-level growth law. *)
Lemma enumerated_final_thread_execution
    (prom : Promising.Model) isem {n} (term : terminationCondition n)
    (tid : fin n) initmem fuel ts mem ts' :
  OutcomeMemoryGrowth prom →
  ts' ∈ (CPState.enumerate_results isem prom term tid initmem fuel ts mem)
    .(CPState.final_states prom) →
  ThreadInstructionExecution prom tid initmem isem term mem ts ts'.
Proof.
  intros Hgrowth Hin.
  apply (proj1 (enumerate_results_final_state_witness isem term tid
    initmem fuel ts mem ts')) in Hin.
  destruct Hin as [ppst [Hstate Hrun]].
  destruct (collect_thread_empty prom tid initmem isem term fuel (length mem)
    [] (PPState.Make ts mem prom.(Promising.iis_init)) ppst
    Hgrowth eq_refl Hrun) as [_ [_ Htrace]].
  cbn in Htrace. rewrite Hstate in Htrace. exact Htrace.
Qed.


Module UMMemoryGrowth.
Import UMPromising.

#[local] Typeclasses Transparent Memory.t.
#[local] Typeclasses Transparent othrow.
#[local] Instance exec_unfold : Exec.Unfold := {}.

Lemma promise_memory msg mem mem' time :
  Exec.elem_of_results (mem', time) (Memory.promise msg mem) →
  mem' = msg :: mem ∧ time = length (msg :: mem).
Proof.
  intro H.
  change ((mem', time) ∈ [(msg :: mem, length (msg :: mem))]) in H.
  apply list_elem_of_singleton in H. inversion H. auto.
Qed.

Ltac invert_execution :=
  repeat match goal with
  | x : unit |- _ => destruct x
  | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  | H : None = Some _ |- _ => inversion H
  | H : Some _ = None |- _ => inversion H
  | H : (_, _) = ?p |- _ => destruct p; inversion H; subst; clear H
  | H : ?p = (_, _) |- _ => destruct p; inversion H; subst; clear H
  | H : Exec.elem_of_results _ (Memory.promise _ _) |- _ =>
      apply promise_memory in H as [-> ->]
  | H : Exec.elem_of_results _ ((guard_discard _) _) |- _ =>
      apply Exec.elem_of_guard_discard_inv in H as ->
  | H : Exec.elem_of_results _ ((guard_discard' _) _) |- _ =>
      apply Exec.elem_of_guard_discard_unit_inv in H as ->
  | H : Exec.elem_of_results _ ((guard_or _ _) _) |- _ =>
      apply Exec.elem_of_guard_or_inv in H as ->
  | H : Exec.elem_of_results _ ((_ ≫= _) _) |- _ =>
      apply Exec.elem_of_bind_elim in H as [? [? [? H]]]
  | H : Exec.elem_of_results _ ((mget _) _) |- _ =>
      apply Exec.elem_of_mget_inv in H as [-> ->]
  | H : Exec.elem_of_results _ ((mGet) _) |- _ =>
      apply Exec.elem_of_mGet_inv in H as [-> ->]
  | H : Exec.elem_of_results _ ((mret _) _) |- _ =>
      apply Exec.elem_of_mret_inv in H as [-> ?]
  | H : Exec.elem_of_results _ ((msetv _ _) _) |- _ => unfold msetv in H
  | H : Exec.elem_of_results _ ((mset _ _) _) |- _ =>
      apply Exec.elem_of_mset_inv in H as ->
  | H : Exec.elem_of_results _ ((mSet _) _) |- _ =>
      apply Exec.elem_of_mSet_inv in H as ->
  | H : Exec.elem_of_results _ ((Exec.liftSt _ _) _) |- _ =>
      apply Exec.elem_of_liftSt_inv in H as [? [-> H]]
  | H : Exec.elem_of_results _ ((mlift _) _) |- _ =>
      apply Exec.elem_of_lift_res_inv in H as [-> H]
  | H : Exec.elem_of_results _ ((mchoosel _) _) |- _ =>
      apply Exec.elem_of_mchoosel_inv in H as [-> _]
  | H : Exec.elem_of_results _ ((mthrow _) _) |- _ =>
      unfold elem_of, Exec.elem_of_results in H; cbn in H; inversion H
  | H : Exec.elem_of_results _ ((mdiscard) _) |- _ =>
      rewrite Exec.mdiscard_eq in H;
      unfold elem_of, Exec.elem_of_results in H; cbn in H; inversion H
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[othrow _ ?opt] => unfold othrow in H end
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[if ?b then _ else _] => destruct b eqn:? end
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[match ?x with _ => _ end] => destruct x eqn:? end
  end.

Lemma read_mem_preserves_mem addr size macc init ppst ppst' res :
  Exec.elem_of_results (ppst', res) (read_mem addr size macc init ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H. unfold read_mem in H.
  invert_execution; reflexivity.
Qed.

Lemma write_mem_growth tid addr size macc data ppst ppst' vpre :
  Exec.elem_of_results (ppst', vpre)
    (write_mem tid addr size macc data ppst) →
  PPState.mem ppst' = PPState.mem ppst ∨
  ∃ pre,
    PPState.mem ppst' = Msg.make tid addr size data :: PPState.mem ppst ∧
    vpre = Some pre ∧ pre ≤ length (PPState.mem ppst).
Proof.
  destruct ppst as [ts mem iis].
  intro H. unfold write_mem in H.
  invert_execution; cbn in *; subst; try discriminate;
    first [left; reflexivity | right; eexists; split; [reflexivity|];
      split; [reflexivity|lia]].
Qed.

Lemma outcome_memory_growth : OutcomeMemoryGrowth UMPromising.
Proof.
  intros n tid initmem out ppst ppst' ret vpre H.
  change (Exec.elem_of_results (ppst', (ret, vpre))
    (run_outcome tid initmem out ppst)) in H.
  funelim (run_outcome tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: invert_execution; try solve [left;
    match goal with p : PPState.t _ _ _ |- _ => destruct p end; reflexivity].
  all: try solve [left; eapply read_mem_preserves_mem; eauto].
  all: try match goal with
  | H : Exec.elem_of_results _ (write_mem _ _ _ _ _ _) |- _ =>
      apply write_mem_growth in H as [H|[pre [Hmem [Hv Hpre]]]];
      [left; exact H|right; eexists [_], pre; repeat split; eauto; discriminate]
  end.
Qed.

End UMMemoryGrowth.
