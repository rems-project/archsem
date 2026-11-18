(******************************************************************************)
(* Preissuing a fresh VM write preserves the complete outcome state           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMReplay
  PromiseFirstVMExecutionCurrent PromiseFirstSailRead PromiseFirstSailFulfilled
  PromiseFirstSailVMTLBINormalization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMWriteNormalization.
Import VMPromising.
#[local] Typeclasses Transparent Memory.t view UMPromising.view othrow.
#[local] Existing Instance PromMemory.lookup_inst.
#[local] Existing Instance PromMemory.exclusive_dec.

Lemma process_event_pending tid imem mem ev time ts :
  TState.process_event tid imem mem ev (TState.promise_write time ts) =
    TState.promise_write time <$> TState.process_event tid imem mem ev ts.
Proof.
  unfold TState.process_event, TState.run_tlb.
  change (TState.tlb (TState.promise_write time ts)) with (TState.tlb ts).
  destruct (TState.tlb ts) as [cache|].
  - destruct (TLB.fill_promise tid imem mem ev cache) as [[next []]|err]; reflexivity.
  - reflexivity.
Qed.

Lemma emit_fresh tid imem mem addr size data ts next :
  TState.process_event tid imem (Ev.Msg (Msg.make tid addr size data) :: mem)
    (Ev.Msg (Msg.make tid addr size data)) ts = Ok next →
  TState.emit_promise tid imem (Ev.Msg (Msg.make tid addr size data) :: mem)
    (Ev.Msg (Msg.make tid addr size data)) ts =
      Ok (TState.promise_write (S (length mem)) next).
Proof.
  intro Hprocess. unfold TState.emit_promise.
  cbn [Ev.tid Msg.tid]. rewrite bool_decide_true by reflexivity.
  rewrite process_event_pending, Hprocess. reflexivity.
Qed.

Lemma exclusive_latest tid addr size tread ev mem :
  Memory.exclusive tid addr size tread (S (length mem)) (ev :: mem) =
  Memory.exclusive tid addr size tread (S (length mem)) mem.
Proof.
  unfold Memory.exclusive, PromMemory.exclusive.
  replace (S (length mem) - 1) with (length mem) by lia.
  rewrite PromMemory.cut_before_cons_old by lia. reflexivity.
Qed.

Lemma clear_pending time ts :
  set TState.prom_wr (filter (λ t, t ≠ time)) (TState.promise_write time ts) =
  set TState.prom_wr (filter (λ t, t ≠ time)) ts.
Proof.
  destruct ts. unfold TState.promise_write. cbn.
  rewrite decide_False by congruence. reflexivity.
Qed.

Theorem write_fresh_normalization tid imem addr size macc data ts mem iis ppst' vpre :
  Exec.elem_of_results (ppst', Some vpre)
    (write_mem tid imem addr size macc data (PPState.Make ts mem iis)) →
  ∃ issued,
    TState.emit_promise tid imem (Ev.Msg (Msg.make tid addr size data) :: mem)
      (Ev.Msg (Msg.make tid addr size data)) ts = Ok issued ∧
    Exec.elem_of_results (ppst', None)
      (write_mem tid imem addr size macc data
        (PPState.Make issued (Ev.Msg (Msg.make tid addr size data) :: mem) iis)).
Proof.
  intro Hrun. unfold write_mem in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [mem0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[time fresh] [Halloc Hrun]]].
  destruct (Memory.fulfill (Ev.Msg (Msg.make tid addr size data)) (TState.prom_wr ts) mem)
    as [oldtime|] eqn:Hfulfill.
  all: cbn [PPState.state PPState.mem] in Halloc; rewrite Hfulfill in Halloc.
  - apply Exec.elem_of_mret_inv in Halloc as [-> Heq]. inversion Heq; subst time fresh.
    exfalso. VMMemoryGrowth.invert_execution; cbn in *; discriminate.
  - apply Exec.elem_of_bind_elim in Halloc as [pp_prom [time_prom [Hpromise Halloc]]].
    apply Exec.elem_of_liftSt_inv in Hpromise as [newmem [-> Hpromise]].
    apply VMMemoryGrowth.promise_memory in Hpromise as [-> ->].
    apply Exec.elem_of_bind_elim in Halloc as [mid0 [mem0 [Hget Halloc]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Halloc as [mid0 [next [Hprocess Halloc]]].
    apply exec_lift_result_inv in Hprocess as [-> Hprocess].
    apply Exec.elem_of_bind_elim in Halloc as [mid0 [[] [Hset Halloc]]].
    apply Exec.elem_of_mset_inv in Hset as ->.
    apply Exec.elem_of_mret_inv in Halloc as [-> Heq]. inversion Heq; subst time fresh.
    cbn [PPState.state PPState.mem PPState.iis] in Hprocess.
    pose proof (VMReadReplay.run_tlb_frame _ ts next Hprocess) as Hframe.
    assert (Hfulfill' : Memory.fulfill (Ev.Msg (Msg.make tid addr size data))
      (TState.prom_wr (TState.promise_write (S (length mem)) next))
      (Ev.Msg (Msg.make tid addr size data) :: mem) = Some (S (length mem))).
    { rewrite Hframe.
      change (Memory.fulfill (Ev.Msg (Msg.make tid addr size data))
        (S (length mem) :: TState.prom_wr ts)
        (Ev.Msg (Msg.make tid addr size data) :: mem) = Some (S (length mem))).
      apply VMTLBINormalization.fulfill_fresh, Hfulfill. }
    exists (TState.promise_write (S (length mem)) next). split.
    + apply emit_fresh, Hprocess.
    + unfold write_mem.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      cbn [PPState.state PPState.mem]. rewrite Hfulfill'.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
      UMFulfilledReplay.invert_execution_with_guards; subst; try discriminate.
      all: cbn [PPState.state PPState.mem PPState.iis compose] in *.
      all: rewrite Hframe; clear Hframe.
      all: change (TState.xclb (TState.promise_write (S (length mem))
        (setv TState.tlb (TState.tlb next) ts))) with (TState.xclb ts).
      all: repeat first
        [ apply Exec.elem_of_guard_discard_unit;
            first [rewrite exclusive_latest; assumption|assumption]
        | apply Exec.elem_of_mret
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_guard_discard_unit;
            first [rewrite exclusive_latest; assumption|assumption]|]
        | eapply exec_guard_discard_bind_intro; [assumption|]
        | match goal with H : ?x = _ |- context[?x] => progress rewrite H end
        | progress cbn [PPState.state PPState.mem PPState.iis compose othrow]
        | match goal with |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) =>
            eapply Exec.elem_of_bind_intro end ].
      all: unfold Exec.elem_of_results; cbn [Exec.results mret Exec.mret_inst Exec.res_mret_inst];
        apply list_elem_of_singleton; f_equal.
      all: cbn.
      all: try rewrite clear_pending.
      all: try reflexivity.
      all: destruct ts, iis; cbn; try rewrite decide_False by congruence; reflexivity.
Qed.
End VMWriteNormalization.
