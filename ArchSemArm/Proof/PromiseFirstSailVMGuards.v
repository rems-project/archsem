(******************************************************************************)
(* VM promise guards and lookup bounds after a future global event           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMReplay.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMGuardReplay.
Import VMPromising.

Lemma fold_min_bound base ps : foldr (λ p acc, min acc p) base ps ≤ base.
Proof. induction ps; cbn; lia. Qed.
Lemma fold_min_gt v base ps :
  v < foldr (λ p acc, min acc p) base ps ↔ v < base ∧ ∀ p ∈ ps, v < p.
Proof.
  induction ps as [|p ps IH]; cbn.
  - split; [intro H; split; [exact H|set_solver]|tauto].
  - split.
    + intro H. assert (Htail : v < foldr (λ p acc, min acc p) base ps) by lia.
      apply IH in Htail as [Hbase Hps]. split; [exact Hbase|].
      intros q Hq. apply elem_of_cons in Hq as [->|Hq]; [lia|apply Hps, Hq].
    + intros [Hbase Hps]. assert (Hp : v < p) by (apply Hps; left; reflexivity).
      assert (Htail : v < foldr (λ p acc, min acc p) base ps).
      { apply IH. split; [exact Hbase|]. intros q Hq. apply Hps. right. exact Hq. }
      lia.
Qed.
Lemma min_promise_bound vmax ts : TState.min_promise vmax ts ≤ S vmax.
Proof. unfold TState.min_promise. pose proof (fold_min_bound (vmax + 1) (TState.prom_wr ts ++ TState.prom_tlbi ts)). lia. Qed.
Lemma min_promise_gt v vmax ts :
  v < TState.min_promise vmax ts ↔ v ≤ vmax ∧ TState.no_promises_until v ts.
Proof.
  unfold TState.min_promise, TState.no_promises_until. split.
  - intro H. apply fold_min_gt in H as [H Hps]. split; [lia|exact Hps].
  - intros [H Hps]. apply fold_min_gt. split; [lia|exact Hps].
Qed.

Lemma emit_promise_pending tid imem mem ev ts issued :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  TState.prom_wr issued =
    (if bool_decide (Ev.tid ev = tid) then
       match ev with
       | Ev.Msg _ => S (length mem) :: TState.prom_wr ts
       | _ => TState.prom_wr ts
       end else TState.prom_wr ts) ∧
  TState.prom_tlbi issued =
    (if bool_decide (Ev.tid ev = tid) then
       match ev with
       | Ev.Msg _ => TState.prom_tlbi ts
       | _ => S (length mem) :: TState.prom_tlbi ts
       end else TState.prom_tlbi ts).
Proof.
  unfold TState.emit_promise, TState.process_event. intro Hpromise.
  apply VMReadReplay.run_tlb_frame in Hpromise.
  destruct (bool_decide (Ev.tid ev = tid)); [destruct ev|];
    rewrite Hpromise; split; reflexivity.
Qed.

Lemma emit_promise_no_promises_until tid imem mem ev ts issued v :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  TState.no_promises_until v ts → v ≤ length mem →
  TState.no_promises_until v issued.
Proof.
  intros Hpromise Hguard Hbound.
  pose proof (emit_promise_pending tid imem mem ev ts issued Hpromise)
    as [Hwr Htlbi].
  unfold TState.no_promises_until in *. rewrite Hwr, Htlbi.
  assert (Hfuture : v < S (length mem)) by lia.
  destruct ev; cbn [Ev.tid]; destruct (bool_decide _);
    intros p Hp; apply elem_of_app in Hp as [Hp|Hp];
    try (apply elem_of_cons in Hp as [->|Hp]);
    first [exact Hfuture|apply Hguard; apply elem_of_app; auto].
Qed.

Lemma emit_promise_no_write_promises_until tid imem mem ev ts issued v :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  TState.no_write_promises_until v ts → v ≤ length mem →
  TState.no_write_promises_until v issued.
Proof.
  intros Hpromise Hguard Hbound.
  pose proof (emit_promise_pending tid imem mem ev ts issued Hpromise) as [Hwr _].
  unfold TState.no_write_promises_until in *. rewrite Hwr.
  assert (Hfuture : v < S (length mem)) by lia.
  destruct ev; cbn [Ev.tid]; try destruct (bool_decide _);
    intros p Hp; try (apply elem_of_cons in Hp as [->|Hp]);
    first [exact Hfuture|apply Hguard, Hp].
Qed.

Theorem emit_promise_min_bound tid imem mem ev ts issued vmax vmax' :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  vmax ≤ length mem → vmax ≤ vmax' →
  TState.min_promise vmax ts ≤ TState.min_promise vmax' issued.
Proof.
  intros Hpromise Hmem Hmax.
  destruct (TState.min_promise vmax ts) as [|v] eqn:Hmin; [lia|].
  assert (Hlt : v < TState.min_promise vmax ts) by lia.
  apply min_promise_gt in Hlt as [Hv Hguard].
  assert (Hnew : v < TState.min_promise vmax' issued).
  { apply min_promise_gt. split; [lia|].
    eapply emit_promise_no_promises_until; [exact Hpromise|exact Hguard|lia]. }
  lia.
Qed.

Corollary emit_promise_translation_bound tid imem mem ev ts issued :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  pred (TState.min_promise (length mem) ts) ≤
    pred (TState.min_promise (length (ev :: mem)) issued).
Proof.
  intro Hpromise. apply Nat.pred_le_mono.
  eapply emit_promise_min_bound; [exact Hpromise|lia|cbn; lia].
Qed.

Theorem emit_promise_cse_candidate tid imem mem ev ts issued vpre vmax vmax' v :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  vmax ≤ length mem → vmax ≤ vmax' →
  v ∈ TState.cse_candidates vpre vmax ts →
  v ∈ TState.cse_candidates vpre vmax' issued.
Proof.
  intros Hpromise Hmem Hmax Hin.
  pose proof (emit_promise_min_bound tid imem mem ev ts issued vmax vmax' Hpromise Hmem Hmax).
  unfold TState.cse_candidates in *. rewrite elem_of_seq in *. lia.
Qed.
End VMGuardReplay.
