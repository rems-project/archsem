(******************************************************************************)
(* Concrete execution consequences of the sail-tiny-arm instruction shape     *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailSyntax PromiseFirstExecutionCurrent
  PromiseFirstVMExecutionCurrent.

Definition IEffectNoUpdate (call : outcome + MChoice) : Prop :=
  match call with
  | inl (MemWrite _ _ _) | inl (TlbOp _) => False
  | _ => True
  end.
Fixpoint IMonNoUpdate {A} (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next call k => IEffectNoUpdate call ∧ ∀ r, IMonNoUpdate (k r)
  end.
Fixpoint IMonAtMostOneUpdate {A} (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next call k =>
      (IEffectNoUpdate call ∧ ∀ r, IMonAtMostOneUpdate (k r)) ∨
      (∀ r, IMonNoUpdate (k r))
  end.
Lemma imon_no_update_bind {A B} (mon : iMon A) (k : A → iMon B) :
  IMonNoUpdate mon → (∀ a, IMonNoUpdate (k a)) → IMonNoUpdate (mon ≫= k).
Proof.
  revert B k. induction mon as [a|out km IH]; intros B k Hm Hk.
  - apply Hk.
  - cbn in Hm |- *. destruct Hm as [Ho Ht]. split; [exact Ho|].
    intro r. apply IH; [apply Ht|exact Hk].
Qed.
Lemma imon_one_update_of_no_update {A} (mon : iMon A) :
  IMonNoUpdate mon → IMonAtMostOneUpdate mon.
Proof.
  induction mon as [a|out k IH]; intro Hm; [exact I|].
  cbn in Hm |- *. destruct Hm as [Ho Ht]. left. split; [exact Ho|].
  intro r. apply IH, Ht.
Qed.
Lemma imon_one_update_bind_left {A B} (mon : iMon A) (k : A → iMon B) :
  IMonNoUpdate mon → (∀ a, IMonAtMostOneUpdate (k a)) →
  IMonAtMostOneUpdate (mon ≫= k).
Proof.
  revert B k. induction mon as [a|out km IH]; intros B k Hm Hk.
  - apply Hk.
  - cbn in Hm |- *. destruct Hm as [Ho Ht]. left. split; [exact Ho|].
    intro r. apply IH; [apply Ht|exact Hk].
Qed.
Lemma imon_one_update_bind_right {A B} (mon : iMon A) (k : A → iMon B) :
  IMonAtMostOneUpdate mon → (∀ a, IMonNoUpdate (k a)) →
  IMonAtMostOneUpdate (mon ≫= k).
Proof.
  revert B k. induction mon as [a|out km IH]; intros B k Hm Hk.
  - apply imon_one_update_of_no_update, Hk.
  - cbn in Hm |- *. destruct Hm as [[Ho Ht]|Ht].
    + left. split; [exact Ho|]. intro r. apply IH; [apply Ht|exact Hk].
    + right. intro r. apply imon_no_update_bind; [apply Ht|exact Hk].
Qed.
Ltac solve_sail_outcome_shape :=
  repeat progress (
    cbn [Sail_outcome_interp Sail_choose Sail_nochoose
      mcall_noret mdiscard mchoosef mchoosel mchoose] in *;
    unfold mret, mbind, fmap, mthrow, mcall, mcallM,
      mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
      iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
    cbn in *);
  repeat match goal with
  | H : Empty_set |- _ => destruct H
  | H : False |- _ => contradiction
  | |- context[if ?b then _ else _] => destruct b; cbn in *
  | |- context[match ?r with _ => _ end] => destruct r; cbn in *
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- _ ∨ _ => right
  end.
Lemma sail_outcome_no_update_interp nondet {eo A} (out : SI.outcome eo A) :
  SailOutcomeNoUpdate out → IMonNoUpdate (Sail_outcome_interp nondet out).
Proof.
  destruct out; intro Hout; try contradiction; solve_sail_outcome_shape.
  all: destruct ty; solve_sail_outcome_shape.
Qed.
Lemma sail_outcome_one_update_interp nondet {eo A} (out : SI.outcome eo A) :
  IMonAtMostOneUpdate (Sail_outcome_interp nondet out).
Proof.
  destruct out; solve_sail_outcome_shape.
  all: destruct ty; solve_sail_outcome_shape.
Qed.
Lemma sail_no_update_interp nondet {eo A} (mon : SI.iMon eo A) :
  SailNoUpdate mon → IMonNoUpdate (iMon_from_Sail nondet mon).
Proof.
  induction mon as [a|T out k IH]; intro Hm; [exact I|].
  cbn in Hm |- *. destruct Hm as [Ho Ht].
  apply imon_no_update_bind; [apply sail_outcome_no_update_interp, Ho|].
  intro r. apply IH, Ht.
Qed.
Lemma sail_one_update_interp nondet {eo A} (mon : SI.iMon eo A) :
  SailAtMostOneUpdate mon → IMonAtMostOneUpdate (iMon_from_Sail nondet mon).
Proof.
  induction mon as [a|T out k IH]; intro Hm; [exact I|].
  cbn in Hm |- *. destruct Hm as [[Ho Ht]|Ht].
  - apply imon_one_update_bind_left; [apply sail_outcome_no_update_interp, Ho|].
    intro r. apply IH, Ht.
  - apply imon_one_update_bind_right; [apply sail_outcome_one_update_interp|].
    intro r. apply sail_no_update_interp, Ht.
Qed.
Lemma sail_tiny_arm_at_most_one_update nondet :
  IMonAtMostOneUpdate (sail_tiny_arm_sem nondet).
Proof. apply sail_one_update_interp, sail_one_update_fetch_and_execute. Qed.

(** The syntax bound identifies the only outcome that can change memory.
    The premise below is discharged by each concrete handler. *)
#[local] Instance no_update_decision call : Decision (IEffectNoUpdate call).
Proof. destruct call as [out|ch]; [destruct out|]; cbn; typeclasses eauto. Defined.

Section UpdateWitness.
Context (prom : Promising.Model) {n : nat} (tid : fin n) (initmem : memoryMap).
Local Notation ppState :=
  (PPState.t prom.(Promising.tState) prom.(Promising.mEvent) prom.(Promising.iis)).
Context (Hno_update : ∀ out (ppst ppst' : ppState) ret vpre,
  IEffectNoUpdate (inl out) →
  Exec.elem_of_results (ppst', (ret, vpre))
    (prom.(Promising.handle_outcome) n tid initmem out ppst) →
  PPState.mem ppst' = PPState.mem ppst).
Local Notation handler :=
  (λ out, prom.(Promising.handle_outcome) n tid initmem out |$> fst).

Lemma no_update_instruction_memory {A} (mon : iMon A) ppst ppst' ret :
  IMonNoUpdate mon →
  Exec.elem_of_results (ppst', ret) (cinterp handler mon ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof using Hno_update.
  revert ppst ppst' ret.
  induction mon as [a|call k IH]; intros ppst ppst' ret Hshape Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. reflexivity.
  - destruct Hshape as [Ho Ht]. destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]].
      cbn in Heq. subst res.
      rewrite (IH _ _ _ _ (Ht r) Htail).
      eapply Hno_update; eassumption.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      eapply IH; [apply Ht|exact Htail].
Qed.

Definition UpdatingOutcomeWitness (mem mem' : list prom.(Promising.mEvent)) : Prop :=
  ∃ out before after ret vpre,
    ¬ IEffectNoUpdate (inl out) ∧
    PPState.mem before = mem ∧ PPState.mem after = mem' ∧
    Exec.elem_of_results (after, (ret, vpre))
      (prom.(Promising.handle_outcome) n tid initmem out before).

Lemma one_update_instruction_memory {A} (mon : iMon A) ppst ppst' ret :
  IMonAtMostOneUpdate mon →
  Exec.elem_of_results (ppst', ret) (cinterp handler mon ppst) →
  PPState.mem ppst' = PPState.mem ppst ∨
  UpdatingOutcomeWitness (PPState.mem ppst) (PPState.mem ppst').
Proof using Hno_update.
  revert ppst ppst' ret.
  induction mon as [a|call k IH]; intros ppst ppst' ret Hshape Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. left; reflexivity.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]].
      cbn in Heq. subst res.
      destruct Hshape as [[Ho Ht]|Ht].
      * pose proof (Hno_update _ _ _ _ _ Ho Hout) as Hmem.
        destruct (IH _ _ _ _ (Ht r) Htail) as [Hmem'|Hwitness];
          rewrite Hmem in *; [left; exact Hmem'|right; exact Hwitness].
      * pose proof (no_update_instruction_memory _ _ _ _ (Ht r) Htail) as Hmem.
        destruct (decide (IEffectNoUpdate (inl out))) as [Ho|Ho].
        -- left. rewrite Hmem. eapply Hno_update; eassumption.
        -- right. exists out, ppst, mid, r, pre.
           repeat split; try assumption; try reflexivity. symmetry; exact Hmem.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      destruct Hshape as [[_ Ht]|Ht].
      * eapply IH; [apply Ht|exact Htail].
      * left. eapply no_update_instruction_memory; [apply Ht|exact Htail].
Qed.
End UpdateWitness.

Module UMSailMemory.
Import UMPromising.
#[local] Typeclasses Transparent Memory.t.
#[local] Typeclasses Transparent othrow.
#[local] Instance exec_unfold : Exec.Unfold := {}.

Lemma outcome_no_update_mem tid initmem out ppst ppst' ret vpre :
  IEffectNoUpdate (inl out) →
  Exec.elem_of_results (ppst', (ret, vpre))
    (run_outcome tid initmem out ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intros Hshape H.
  funelim (run_outcome tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: cbn in Hshape; try contradiction.
  all: UMMemoryGrowth.invert_execution; try solve [
    match goal with p : PPState.t _ _ _ |- _ => destruct p end; reflexivity].
  all: eapply UMMemoryGrowth.read_mem_preserves_mem; eauto.
Qed.
Lemma outcome_single_update_mem tid initmem out ppst ppst' ret vpre :
  Exec.elem_of_results (ppst', (ret, vpre))
    (run_outcome tid initmem out ppst) →
  PPState.mem ppst' = PPState.mem ppst ∨
  ∃ msg, PPState.mem ppst' = msg :: PPState.mem ppst.
Proof.
  intro H. funelim (run_outcome tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: UMMemoryGrowth.invert_execution; try solve [left;
    match goal with p : PPState.t _ _ _ |- _ => destruct p end; reflexivity].
  all: try solve [left; eapply UMMemoryGrowth.read_mem_preserves_mem; eauto].
  all: match goal with
  | H : Exec.elem_of_results _ (write_mem _ _ _ _ _ _) |- _ =>
      apply UMMemoryGrowth.write_mem_growth in H as [H|[pre [Hmem _]]];
      [left; exact H|right; eexists; exact Hmem]
  end.
Qed.
End UMSailMemory.

Module VMSailMemory.
Import VMPromising.
#[local] Typeclasses Transparent Memory.t othrow.
#[local] Instance exec_unfold : Exec.Unfold := {}.
Lemma outcome_no_update_mem n tid initmem out ppst ppst' ret vpre :
  IEffectNoUpdate (inl out) →
  Exec.elem_of_results (ppst', (ret, vpre))
    (run_outcome n tid initmem out ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intros Hshape H. funelim (run_outcome n tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: cbn in Hshape; try contradiction.
  all: VMMemoryGrowth.invert_execution; try solve [VMMemoryGrowth.finish_memory_equality].
  all: eauto using VMMemoryGrowth.read_mem_preserves_mem,
    VMMemoryGrowth.read_pte_preserves_mem,
    VMMemoryGrowth.reg_write_preserves_mem,
    VMMemoryGrowth.cse_preserves_mem,
    VMMemoryGrowth.barrier_preserves_mem,
    VMMemoryGrowth.trans_start_preserves_mem,
    VMMemoryGrowth.take_exception_preserves_mem.
Qed.
End VMSailMemory.

Lemma VMSail_instruction_one_updating_outcome bbm nondet {n} (tid : fin n)
    initmem ppst ppst' :
  Exec.elem_of_results (ppst', ())
    (cinterp (VMPromising.run_outcome' n tid initmem)
      (sail_tiny_arm_sem nondet) ppst) →
  PPState.mem ppst' = PPState.mem ppst ∨
  UpdatingOutcomeWitness (VMPromising.VMPromising bbm) tid initmem
    (PPState.mem ppst) (PPState.mem ppst').
Proof.
  apply (one_update_instruction_memory (VMPromising.VMPromising bbm) tid initmem).
  - intros. eapply VMSailMemory.outcome_no_update_mem; eassumption.
  - apply sail_tiny_arm_at_most_one_update.
Qed.

(** A successful UM Sail instruction appends at most one concrete message.
    This follows from the installed Sail source and the current handler. *)
Lemma UMSail_instruction_single_new_event nondet {n} (tid : fin n) initmem ppst ppst' :
  Exec.elem_of_results (ppst', ())
    (cinterp (UMPromising.run_outcome' tid initmem) (sail_tiny_arm_sem nondet) ppst) →
  PPState.mem ppst' = PPState.mem ppst ∨
  ∃ msg, PPState.mem ppst' = msg :: PPState.mem ppst.
Proof.
  intro Hrun.
  assert (Hone : PPState.mem ppst' = PPState.mem ppst ∨
    UpdatingOutcomeWitness UMPromising tid
      initmem (PPState.mem ppst) (PPState.mem ppst')).
  { eapply (one_update_instruction_memory UMPromising tid initmem).
    - intros. eapply UMSailMemory.outcome_no_update_mem; eassumption.
    - apply sail_tiny_arm_at_most_one_update.
    - exact Hrun. }
  destruct Hone as [Heq|[out [before [after [ret [pre [_ [Hbefore [Hafter Hout]]]]]]]]].
  - left; exact Heq.
  - pose proof (UMSailMemory.outcome_single_update_mem
      tid initmem out before after ret pre Hout) as Hmem.
    rewrite Hbefore, Hafter in Hmem. exact Hmem.
Qed.
