(******************************************************************************)
(* Memory growth in the current virtual-memory promising model               *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSem Require Import GenPromising.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstExecutionCurrent.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMMemoryGrowth.
Import VMPromising.

#[local] Typeclasses Transparent Memory.t othrow.
#[local] Instance exec_unfold : Exec.Unfold := {}.

Lemma promise_memory ev mem mem' time :
  Exec.elem_of_results (mem', time) (Memory.promise ev mem) →
  mem' = ev :: mem ∧ time = length (ev :: mem).
Proof.
  intro H.
  change ((mem', time) ∈ [(ev :: mem, length (ev :: mem))]) in H.
  apply list_elem_of_singleton in H. inversion H. auto.
Qed.

Ltac invert_execution :=
  repeat first [progress UMMemoryGrowth.invert_execution |
    match goal with
    | H : Exec.elem_of_results _ (Memory.promise _ _) |- _ =>
        apply promise_memory in H as [-> ->]
    end].

Ltac finish_memory_equality :=
  repeat match goal with p : PPState.t _ _ _ |- _ => destruct p end;
  repeat match goal with p : (TState.t * IIS.t)%type |- _ => destruct p end;
  reflexivity.

Lemma read_mem_preserves_mem addr size macc init ppst ppst' res :
  Exec.elem_of_results (ppst', res)
    (read_mem_explicit init addr size macc ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H. unfold read_mem_explicit in H.
  invert_execution; finish_memory_equality.
Qed.

Lemma read_pte_preserves_mem ppst ppst' res :
  Exec.elem_of_results (ppst', res) (read_pte ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H. unfold read_pte in H.
  invert_execution; finish_memory_equality.
Qed.

Lemma reg_write_preserves_mem tid init reg racc val ppst ppst' res :
  Exec.elem_of_results (ppst', res) (run_reg_write tid init reg racc val ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H. unfold run_reg_write in H.
  invert_execution; finish_memory_equality.
Qed.

Lemma cse_preserves_mem tid init vmax ppst ppst' res :
  Exec.elem_of_results (ppst', res) (run_cse tid init vmax ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H. unfold run_cse in H.
  invert_execution; finish_memory_equality.
Qed.

Lemma trans_start_preserves_mem tid init start ppst ppst' res :
  Exec.elem_of_results (ppst', res) (run_trans_start tid init start ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H. unfold run_trans_start in H.
  invert_execution; finish_memory_equality.
Qed.

Lemma write_mem_growth tid init addr size macc data ppst ppst' vpre :
  Exec.elem_of_results (ppst', vpre)
    (write_mem tid init addr size macc data ppst) →
  PPState.mem ppst' = PPState.mem ppst ∨
  ∃ pre,
    PPState.mem ppst' = Ev.Msg (Msg.make tid addr size data) :: PPState.mem ppst ∧
    vpre = Some pre ∧ pre ≤ length (PPState.mem ppst).
Proof.
  destruct ppst as [ts mem iis].
  intro H. unfold write_mem in H.
  invert_execution; cbn in *; subst; try discriminate;
    first [left; reflexivity | right; eexists; split; [reflexivity|];
      split; [reflexivity|lia]].
Qed.

Lemma materialize_tlbi_growth tid init pre tlbi recipient ppst ppst' time created :
  Exec.elem_of_results (ppst', (time, created))
    (materialize_tlbi_for_recipient tid init pre tlbi recipient ppst) →
  if created then
    PPState.mem ppst' = Ev.Tlbi tlbi recipient :: PPState.mem ppst ∧
    pre ≤ length (PPState.mem ppst)
  else PPState.mem ppst' = PPState.mem ppst.
Proof.
  destruct ppst as [ts mem iis].
  intro H. unfold materialize_tlbi_for_recipient in H.
  invert_execution; cbn in *; subst;
    first [reflexivity | split; [reflexivity|lia]].
Qed.

Definition tlbi_recipient_step tid init pre tlbi :
    (view * view) * bool → nat →
    Exec.t (PPState.t TState.t Ev.t IIS.t) string ((view * view) * bool) :=
  λ '((vself, vother), created) recipient,
    '(time, is_new) ← materialize_tlbi_for_recipient tid init pre tlbi recipient;
    let vself := if decide (recipient = tid) then max vself time else vself in
    let vother := if decide (recipient = tid) then vother else max vother time in
    mret ((vself, vother), created || is_new).

Lemma tlbi_recipients_growth tid init pre tlbi recipients
    vself0 vother0 created0 ppst ppst' vself vother created :
  Exec.elem_of_results (ppst', ((vself, vother), created))
    (foldlM (tlbi_recipient_step tid init pre tlbi)
      ((vself0, vother0), created0) recipients ppst) →
  (PPState.mem ppst' = PPState.mem ppst ∧ created = created0) ∨
  ∃ extra, extra ≠ [] ∧
    PPState.mem ppst' = (extra ++ PPState.mem ppst)%list ∧
    created = true ∧ pre ≤ length (PPState.mem ppst).
Proof.
  revert vself0 vother0 created0 ppst ppst' vself vother created.
  induction recipients as [|recipient recipients IH];
    intros vself0 vother0 created0 ppst ppst' vself vother created Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> Heq].
    inversion Heq. left. auto.
  - cbn [foldlM] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [pp_mid [[[vself_mid vother_mid] created_mid] [Hstep Htail]]].
    unfold tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [pp_mat [[time is_new] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> Heq].
    inversion Heq; subst vself_mid vother_mid created_mid.
    apply materialize_tlbi_growth in Hmat.
    destruct is_new.
    + cbn in Hmat. destruct Hmat as [Hmem Hpre].
      rewrite Bool.orb_true_r in Htail.
      destruct (IH _ _ _ _ _ _ _ _ Htail)
        as [[Hmem' Hcreated]|[extra [Hnonempty [Hmem' [Hcreated _]]]]].
      * right. exists [Ev.Tlbi tlbi recipient].
        repeat split; try discriminate; try assumption.
        cbn. congruence.
      * right. exists (extra ++ [Ev.Tlbi tlbi recipient])%list.
        split; [intro Hnil; apply app_eq_nil in Hnil as [_ Hnil]; discriminate|].
        split; [rewrite Hmem', Hmem, <- app_assoc; reflexivity|]. auto.
    + cbn in Hmat. rewrite Bool.orb_false_r in Htail.
      destruct (IH _ _ _ _ _ _ _ _ Htail)
        as [[Hmem' Hcreated]|[extra [Hnonempty [Hmem' [Hcreated Hpre]]]]].
      * left. split; congruence.
      * right. exists extra. rewrite Hmat in Hmem', Hpre. auto.
Qed.

Lemma tlbi_growth n tid init viio tlbi ppst ppst' vpre :
  Exec.elem_of_results (ppst', vpre) (run_tlbi n tid init viio tlbi ppst) →
  PPState.mem ppst' = PPState.mem ppst ∨
  ∃ extra pre, extra ≠ [] ∧
    PPState.mem ppst' = (extra ++ PPState.mem ppst)%list ∧
    vpre = Some pre ∧ pre ≤ length (PPState.mem ppst).
Proof.
  destruct ppst as [ts mem iis].
  intro H. unfold run_tlbi in H.
  invert_execution.
  all: match goal with
  | Hrec : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
      apply tlbi_recipients_growth in Hrec;
      destruct Hrec as [[Hmem Hflag]|[extra [Hnonempty [Hmem [Hflag Hpre]]]]]
  end.
  all: repeat match goal with p : PPState.t _ _ _ |- _ => destruct p end.
  all: cbn in *; subst; try discriminate.
  all: first [left; reflexivity | right; eexists extra, _;
    repeat split; eauto].
Qed.

Lemma barrier_preserves_mem tid init barrier vmax ppst ppst' res :
  Exec.elem_of_results (ppst', res) (run_barrier tid init barrier vmax ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H. unfold run_barrier in H.
  invert_execution; try finish_memory_equality.
  all: eapply cse_preserves_mem; eassumption.
Qed.

Lemma take_exception_preserves_mem tid init fault vmax ppst ppst' res :
  Exec.elem_of_results (ppst', res) (run_take_exception tid init fault vmax ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H. unfold run_take_exception in H.
  invert_execution; eapply cse_preserves_mem; eassumption.
Qed.

Lemma outcome_memory_growth bbm : OutcomeMemoryGrowth (VMPromising bbm).
Proof.
  intros n tid initmem out ppst ppst' ret vpre H.
  change (Exec.elem_of_results (ppst', (ret, vpre))
    (run_outcome n tid initmem out ppst)) in H.
  funelim (run_outcome n tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: invert_execution; try solve [left; finish_memory_equality].
  all: try solve [left; eapply read_mem_preserves_mem; eauto].
  all: try solve [left; eapply read_pte_preserves_mem; eauto].
  all: try solve [left; eapply reg_write_preserves_mem; eauto].
  all: try solve [left; eapply cse_preserves_mem; eauto].
  all: try solve [left; eapply barrier_preserves_mem; eauto].
  all: try solve [left; eapply trans_start_preserves_mem; eauto].
  all: try solve [left; eapply take_exception_preserves_mem; eauto].
  all: try match goal with
  | H : Exec.elem_of_results _ (write_mem _ _ _ _ _ _ _) |- _ =>
      apply write_mem_growth in H as [H|[pre [Hmem [Hv Hpre]]]];
      [left; exact H|right; eexists [_], pre; repeat split; eauto; discriminate]
  end.
  all: match goal with
  | H : Exec.elem_of_results _ (run_tlbi _ _ _ _ _ _) |- _ =>
      exact (tlbi_growth _ _ _ _ _ _ _ _ H)
  end.
Qed.

End VMMemoryGrowth.
