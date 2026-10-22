(******************************************************************************)
(* Replaying fulfilled UM writes past an additional future promise            *)
(******************************************************************************)

(** A pending timestamp already present in the history remains the selected
    fulfillment after a later message is promised. RMW and exclusive checks
    use the history before that old write, and all state updates commute with
    the extra pending timestamp. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstExecutionCurrent
  PromiseFirstSailRead.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module UMFulfilledReplay.
Import UMPromising UMReadReplay.
#[local] Typeclasses Transparent Memory.t Memory.exclusive othrow.
#[local] Existing Instance PromMemory.lookup_inst.
#[local] Existing Instance PromMemory.exclusive_dec.

Lemma fulfill_bound msg prom mem time :
  Memory.fulfill msg prom mem = Some time → time ≤ length mem.
Proof.
  unfold Memory.fulfill, PromMemory.fulfill. rewrite head_reverse.
  intro H. apply last_Some_elem_of in H. apply list_elem_of_filter in H as [Hlookup _].
  unfold lookup, PromMemory.lookup_inst in Hlookup.
  destruct (time =? 0)%stdpp; [discriminate|].
  destruct (time <=? length mem)%nat eqn:Hle; [apply Nat.leb_le, Hle|discriminate].
Qed.

Lemma fulfill_after_future_promise msg future prom mem time :
  (∀ t ∈ prom, t ≤ length mem) →
  Memory.fulfill msg prom mem = Some time →
  Memory.fulfill msg (S (length mem) :: prom) (future :: mem) = Some time.
Proof.
  intros Hbound Hfulfill. unfold Memory.fulfill, PromMemory.fulfill in *.
  rewrite head_reverse in *.
  assert (Hfilter : filter (λ t, (future :: mem : PromMemory.t Msg.t) !! t = Some msg) prom =
    filter (λ t, mem !! t = Some msg) prom).
  { clear Hfulfill. induction prom as [|t prom IH]; [reflexivity|].
    rewrite !filter_cons. rewrite PromMemory.lookup_cons_old by (apply Hbound; set_solver).
    rewrite IH by (intros; apply Hbound; set_solver). reflexivity. }
  rewrite filter_cons. rewrite Hfilter.
  destruct (decide ((future :: mem : PromMemory.t Msg.t) !! S (length mem) = Some msg));
    [|exact Hfulfill].
  destruct (filter (λ t, mem !! t = Some msg) prom) as [|t rest] eqn:Hfiltered.
  - rewrite Hfiltered in Hfulfill. discriminate.
  - rewrite last_cons_cons. rewrite <- Hfiltered. exact Hfulfill.
Qed.

Lemma filter_promise_old p time ts :
  p ≠ time →
  set TState.prom (filter (λ t, t ≠ time)) (TState.promise p ts) =
  TState.promise p (set TState.prom (filter (λ t, t ≠ time)) ts).
Proof. intros Hneq. destruct ts. cbn. rewrite decide_True by assumption. reflexivity. Qed.

Lemma promise_set_fwdbs addrs n (data : bv n) time vdata xcl p ts :
  TState.set_fwdbs addrs data time vdata xcl (TState.promise p ts) =
  TState.promise p (TState.set_fwdbs addrs data time vdata xcl ts).
Proof.
  unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)).
  intro pairs. revert ts. induction pairs as [|[addr byte] pairs IH]; intro ts; cbn.
  - reflexivity.
  - rewrite <- IH. f_equal; destruct ts; reflexivity.
Qed.

Lemma promise_update_vwr p v ts :
  TState.update TState.vwr v (TState.promise p ts) =
  TState.promise p (TState.update TState.vwr v ts).
Proof. destruct ts; reflexivity. Qed.
Lemma promise_update_vrel p v ts :
  TState.update TState.vrel v (TState.promise p ts) =
  TState.promise p (TState.update TState.vrel v ts).
Proof. destruct ts; reflexivity. Qed.
Lemma promise_update_vacq p v ts :
  TState.update TState.vacq v (TState.promise p ts) =
  TState.promise p (TState.update TState.vacq v ts).
Proof. destruct ts; reflexivity. Qed.
Lemma promise_clear_xclb p ts :
  TState.clear_xclb (TState.promise p ts) = TState.promise p (TState.clear_xclb ts).
Proof. destruct ts; reflexivity. Qed.

Lemma exclusive_before_future tid addr size tread time msg mem :
  time ≤ length mem →
  Memory.exclusive tid addr size tread time (msg :: mem) =
  Memory.exclusive tid addr size tread time mem.
Proof.
  intro Htime. unfold Memory.exclusive, PromMemory.exclusive.
  rewrite PromMemory.cut_before_cons_old by lia. reflexivity.
Qed.

Ltac invert_execution_with_guards :=
  repeat match goal with
  | x : unit |- _ => destruct x
  | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  | H : None = Some _ |- _ => inversion H
  | H : Some _ = None |- _ => inversion H
  | H : (_, _) = ?p |- _ => destruct p; inversion H; subst; clear H
  | H : ?p = (_, _) |- _ => destruct p; inversion H; subst; clear H
  | H : Exec.elem_of_results _ (Memory.promise _ _) |- _ =>
      apply UMMemoryGrowth.promise_memory in H as [-> ->]
  | H : Exec.elem_of_results _ ((guard_discard _) _) |- _ =>
      apply Exec.elem_of_guard_discard_inv in H as ->
  | H : Exec.elem_of_results _ ((guard_discard' _) _) |- _ =>
      let Hp := fresh "Hexclusive" in
      pose proof (Exec.elem_of_guard_discard_unit_prop _ _ H) as Hp;
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

Lemma write_mem_fulfilled_after_promise tid addr size macc data msg ppst ppst' :
  (∀ t ∈ TState.prom (PPState.state ppst), t ≤ length (PPState.mem ppst)) →
  Exec.elem_of_results (ppst', None) (write_mem tid addr size macc data ppst) →
  let p := S (length (PPState.mem ppst)) in
  Exec.elem_of_results (add_pending_message msg p ppst', None)
    (write_mem tid addr size macc data (add_pending_message msg p ppst)).
Proof.
  destruct ppst as [ts mem iis]. cbn. intros Hbound Hrun.
  unfold write_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [mem0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[time fresh] [Hfulfill Hrun]]].
  destruct (Memory.fulfill (Msg.make tid addr size data) (TState.prom ts) mem)
    as [t|] eqn:Hlookup.
  all: cbn [PPState.state PPState.mem] in Hfulfill; rewrite Hlookup in Hfulfill.
  2: { exfalso. UMMemoryGrowth.invert_execution; cbn in *; discriminate. }
  apply Exec.elem_of_mret_inv in Hfulfill as [-> Heq]. inversion Heq; subst time fresh.
  pose proof (fulfill_bound _ _ _ _ Hlookup) as Htime.
  pose proof (fulfill_after_future_promise _ msg _ _ _ Hbound Hlookup) as Hlookup'.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [add_pending_message PPState.state PPState.mem TState.promise]. rewrite Hlookup'.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  invert_execution_with_guards; subst; try discriminate.
  all: cbn [PPState.state PPState.mem PPState.iis compose] in *.
  all: repeat first
    [ apply Exec.elem_of_guard_discard_unit;
      rewrite exclusive_before_future by assumption; assumption
    | apply Exec.elem_of_mret
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_guard_discard_unit;
        rewrite exclusive_before_future by assumption; assumption|]
    | eapply exec_guard_discard_bind_intro; [assumption|]
    | match goal with H : ?x = _ |- context[?x] => progress rewrite H end
    | progress change (TState.xclb (TState.promise (S (length mem)) ts)) with (TState.xclb ts)
    | progress cbn [add_pending_message PPState.state PPState.iis PPState.mem
        compose TState.promise othrow]
    | match goal with
      | |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) => eapply Exec.elem_of_bind_intro
      end ].
  all: unfold add_pending_message; cbn.

  all: rewrite <- promise_set_fwdbs.
  all: try rewrite <- promise_clear_xclb.
  all: try rewrite <- promise_update_vacq.
  all: rewrite <- promise_update_vrel, <- promise_update_vwr, <- promise_update_cohs.
  all: destruct ts; cbn; rewrite decide_True by lia; apply Exec.elem_of_mret.
Qed.
End UMFulfilledReplay.
