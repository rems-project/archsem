(******************************************************************************)
(* Replaying UM register, control, and barrier outcomes before a new write    *)
(******************************************************************************)

(** The combined intra-instruction and ordering view grows monotonically
    through outcomes that do not update memory. Its bound at a later new
    write supplies the guard bounds needed to move that promise earlier. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstExecutionCurrent PromiseFirstSailRead PromiseFirstSailExecution.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module UMControlReplay.
Import UMPromising UMReadReplay.
#[local] Typeclasses Transparent Memory.t othrow.

Lemma reg_read_after_promise tid imem reg racc msg p ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, pre))
    (run_outcome tid imem (RegRead reg racc) ppst) →
  Exec.elem_of_results (add_pending_message msg p ppst', (ret, pre))
    (run_outcome tid imem (RegRead reg racc) (add_pending_message msg p ppst)).
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

Lemma promise_set_reg p reg rv ts :
  TState.set_reg reg rv (TState.promise p ts) =
  TState.promise p <$> TState.set_reg reg rv ts.
Proof.
  destruct ts. unfold TState.set_reg. cbn.
  match goal with |- context[if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma no_promises_until_promise v p ts :
  TState.no_promises_until v ts → v < p →
  TState.no_promises_until v (TState.promise p ts).
Proof.
  intros Hnp Hlt t Ht. apply elem_of_cons in Ht as [->|Ht]; auto.
Qed.

Lemma promise_update_vcap p v ts :
  TState.update TState.vcap v (TState.promise p ts) =
  TState.promise p (TState.update TState.vcap v ts).
Proof. destruct ts. reflexivity. Qed.

Lemma reg_write_after_promise tid imem reg racc val msg p ppst ppst' ret pre :
  (reg = pc_reg → IIS.strict (PPState.iis ppst) < p) →
  Exec.elem_of_results (ppst', (ret, pre))
    (run_outcome tid imem (RegWrite reg racc val) ppst) →
  Exec.elem_of_results (add_pending_message msg p ppst', (ret, pre))
    (run_outcome tid imem (RegWrite reg racc val) (add_pending_message msg p ppst)).
Proof.
  destruct ppst as [ts mem iis]. cbn. intros Hbound Hrun.
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [Hacc [Hguard Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  apply Exec.elem_of_bind_elim in Hrun as [mid [strict [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  eapply exec_guard_or_bind_intro; [exact Hacc|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  match type of Hrun with context[if ?b then _ else _] =>
    destruct b eqn:Hpc end.
  - apply bool_decide_eq_true_1 in Hpc.
    apply Exec.elem_of_bind_elim in Hrun as [mid [vreg [Hpcstep Hrun]]].
    UMMemoryGrowth.invert_execution. subst.
    eapply Exec.elem_of_bind_intro with (a := 0).
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      eapply exec_guard_discard_bind_intro.
      * apply no_promises_until_promise; [assumption|apply Hbound; reflexivity].
      * eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
        apply Exec.elem_of_mret.
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn in Heqo |- *.
      rewrite promise_update_vcap, promise_set_reg, Heqo.
      unfold othrow. cbn.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
      apply Exec.elem_of_mret.
  - UMMemoryGrowth.invert_execution. subst.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn in Heqo |- *.
    rewrite promise_set_reg, Heqo.
    unfold othrow. cbn.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_mret.
Qed.

Definition order_view (ppst : PPState.t TState.t Msg.t IIS.t) : nat :=
  IIS.strict (PPState.iis ppst) ⊔ TState.min_new_prom_view (PPState.state ppst).

Lemma update_cohs_only_coh avs ts :
  TState.update_cohs avs ts =
  setv TState.coh (TState.coh (TState.update_cohs avs ts)) ts.
Proof.
  unfold TState.update_cohs. induction avs as [|[a v] avs IH]; cbn.
  - destruct ts. reflexivity.
  - rewrite IH. destruct ts. reflexivity.
Qed.

Lemma read_mem_order_view_monotone addr size macc imem ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (read_mem addr size macc imem ppst) →
  order_view ppst ≤ order_view ppst'.
Proof.
  destruct ppst as [ts mem iis]. intro Hrun. unfold read_mem in Hrun.
  UMMemoryGrowth.invert_execution.
  all: unfold order_view, TState.min_new_prom_view; cbn.
  all: rewrite update_cohs_only_coh.
  all: destruct ts, iis; cbn.
  all: unfold join, join_nat.
  all: repeat first [apply Nat.max_le_compat | apply Nat.le_refl | apply Nat.le_max_r | apply Nat.le_max_l].
Qed.

Lemma set_reg_min_view reg rv ts ts' :
  TState.set_reg reg rv ts = Some ts' →
  TState.min_new_prom_view ts' = TState.min_new_prom_view ts.
Proof.
  unfold TState.set_reg.
  match goal with |- context[if ?b then _ else _] => destruct b end;
    [|discriminate].
  intro H. injection H as <-. destruct ts. reflexivity.
Qed.

Lemma outcome_order_view_monotone tid imem out ppst ppst' ret pre :
  IEffectNoUpdate (inl out) →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  order_view ppst ≤ order_view ppst'.
Proof.
  intros Hno Hrun. funelim (run_outcome tid imem out ppst).
  all: cbn [IEffectNoUpdate] in Hno; try contradiction.
  all: rewrite <- Heqcall in Hrun.
  all: UMMemoryGrowth.invert_execution; subst.
  all: try solve [eapply read_mem_order_view_monotone; eassumption].
  all: unfold order_view; cbn.
  all: try match goal with
  | H : TState.set_reg _ _ _ = Some _ |- _ =>
    rewrite (set_reg_min_view _ _ _ _ H)
  end.
  all: unfold TState.min_new_prom_view; cbn.
  all: try match goal with pp : PPState.t _ _ _ |- _ => destruct pp as [ts mem iis] end.
  all: cbn.
  all: unfold join, join_nat.
  all: repeat first [apply Nat.le_refl | apply Nat.max_le_compat | apply Nat.le_max_r | apply Nat.le_max_l].
Qed.

Definition fetch_preserved imem msg (ppst : PPState.t TState.t Msg.t IIS.t) (out : outcome) : Prop :=
  match out with
  | MemRead req => is_ifetch req.(MemReq.access_kind) = true →
      req.(MemReq.size) = 4%N →
      read_ifetch req.(MemReq.address) imem (msg :: PPState.mem ppst) =
      read_ifetch req.(MemReq.address) imem (PPState.mem ppst)
  | _ => True
  end.

Ltac solve_max_le :=
  first [apply Nat.le_refl |
    match goal with
    | |- Nat.max _ _ ≤ _ => apply Nat.max_lub; solve_max_le
    | |- ?x ≤ Nat.max ?a ?b =>
      first [eapply (Nat.le_trans x a); [solve_max_le|apply Nat.le_max_l] |
        eapply (Nat.le_trans x b); [solve_max_le|apply Nat.le_max_r]]
    end].

Lemma no_update_outcome_after_promise tid imem out msg ppst ppst' ret pre :
  IEffectNoUpdate (inl out) →
  fetch_preserved imem msg ppst out →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  order_view ppst' < S (length (PPState.mem ppst)) →
  let p := S (length (PPState.mem ppst)) in
  Exec.elem_of_results (add_pending_message msg p ppst', (ret, pre))
    (run_outcome tid imem out (add_pending_message msg p ppst)).
Proof.
  intros Hno Hfetch Hrun Hbound.
  pose proof (outcome_order_view_monotone tid imem out ppst ppst' ret pre Hno Hrun) as Hmono.
  assert (Hstrict : IIS.strict (PPState.iis ppst) < S (length (PPState.mem ppst))).
  { unfold order_view, join, join_nat in Hmono, Hbound. lia. }
  destruct out as [reg racc|reg racc val|req|req|req val tags|barrier|cop|tlbi|exn| |trans|trans|err];
    cbn [IEffectNoUpdate] in Hno; try contradiction.
  - apply reg_read_after_promise, Hrun.
  - eapply reg_write_after_promise; [intros _; exact Hstrict|exact Hrun].
  - apply UMOutcomeReplay.mem_read_after_promise; assumption.
  - destruct ppst as [ts mem iis]. simp run_outcome in Hrun |- *.
    UMMemoryGrowth.invert_execution. subst.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply exec_guard_discard_bind_intro.
    + apply no_promises_until_promise; assumption.
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
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
      | eapply exec_guard_discard_bind_intro;
        [apply no_promises_until_promise; [assumption|];
         eapply Nat.le_lt_trans; [|exact Hbound];
         unfold order_view, TState.min_new_prom_view, join, join_nat; cbn;
         solve_max_le|]
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
Lemma pc_write_control_bound tid imem racc val ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem (RegWrite pc_reg racc val) ppst) →
  IIS.strict (PPState.iis ppst) ≤ TState.min_new_prom_view (PPState.state ppst').
Proof.
  intro Hrun. simp run_outcome in Hrun.
  UMMemoryGrowth.invert_execution; subst; try discriminate.
  all: cbn.
  all: match goal with H : TState.set_reg _ _ _ = Some _ |- _ =>
    rewrite (set_reg_min_view _ _ _ _ H) end.
  all: unfold TState.min_new_prom_view, join, join_nat; cbn.
  all: destruct ppst as [ts mem iis]; destruct ts; cbn; solve_max_le.
Qed.

Lemma no_update_outcome_after_promise_min tid imem out msg ppst ppst' ret pre :
  IEffectNoUpdate (inl out) →
  fetch_preserved imem msg ppst out →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem out ppst) →
  TState.min_new_prom_view (PPState.state ppst') < S (length (PPState.mem ppst)) →
  let p := S (length (PPState.mem ppst)) in
  Exec.elem_of_results (add_pending_message msg p ppst', (ret, pre))
    (run_outcome tid imem out (add_pending_message msg p ppst)).
Proof.
  intros Hno Hfetch Hrun Hbound.
  destruct out as [reg racc|reg racc val|req|req|req val tags|barrier|cop|tlbi|exn| |trans|trans|err];
    cbn [IEffectNoUpdate] in Hno; try contradiction.
  - apply reg_read_after_promise, Hrun.
  - eapply reg_write_after_promise; [|exact Hrun].
    intro Heq. subst reg. eapply Nat.le_lt_trans; [eapply pc_write_control_bound; exact Hrun|exact Hbound].
  - apply UMOutcomeReplay.mem_read_after_promise; assumption.
  - destruct ppst as [ts mem iis]. simp run_outcome in Hrun |- *.
    UMMemoryGrowth.invert_execution. subst.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply exec_guard_discard_bind_intro.
    + apply no_promises_until_promise; [assumption|].
      eapply Nat.le_lt_trans; [|exact Hbound].
      unfold TState.min_new_prom_view, join, join_nat, add_pending_message; cbn.
      destruct ts, iis; cbn. solve_max_le.
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
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
      | eapply exec_guard_discard_bind_intro;
        [apply no_promises_until_promise; [assumption|];
         eapply Nat.le_lt_trans; [|exact Hbound];
         unfold TState.min_new_prom_view, join, join_nat; cbn;
         solve_max_le|]
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
End UMControlReplay.
