(******************************************************************************)
(* Preissuing a fresh recipient TLBI preserves its complete execution state   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstSailVMReplay
  PromiseFirstVMExecutionCurrent PromiseFirstSailRead PromiseFirstSailReplay.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMTLBINormalization.
Import VMPromising.
#[local] Existing Instance PromMemory.lookup_inst.
#[local] Typeclasses Transparent Memory.t view UMPromising.view.

Lemma process_event_pending tid imem mem ev time ts :
  TState.process_event tid imem mem ev (TState.promise_tlbi time ts) =
    TState.promise_tlbi time <$> TState.process_event tid imem mem ev ts.
Proof.
  unfold TState.process_event, TState.run_tlb.
  change (TState.tlb (TState.promise_tlbi time ts)) with (TState.tlb ts).
  destruct (TState.tlb ts) as [cache|].
  - destruct (TLB.fill_promise tid imem mem ev cache) as [[next []]|err]; reflexivity.
  - reflexivity.
Qed.

Lemma fulfill_fresh ev mem pending :
  Memory.fulfill ev pending mem = None →
  Memory.fulfill ev (S (length mem) :: pending) (ev :: mem) = Some (S (length mem)).
Proof.
  intro Hnone.
  assert (Hno_match : ∀ t ∈ pending, mem !! t ≠ Some ev).
  { unfold Memory.fulfill, PromMemory.fulfill in Hnone.
    rewrite head_reverse in Hnone. apply last_None in Hnone.
    intros t Hin Hlookup.
    exact (filter_nil_not_elem_of (λ t, mem !! t = Some ev) pending t Hnone Hlookup Hin). }
  unfold Memory.fulfill, PromMemory.fulfill. rewrite head_reverse.
  rewrite filter_cons_True by apply PromMemory.lookup_latest.
  apply UMSailReplay.last_cons_all_eq.
  intros t Hmatch. apply list_elem_of_filter in Hmatch as [Hlookup Hin].
  apply PromMemory.lookup_cons_inv_same in Hlookup as [Hold|Htime].
  - exfalso. exact (Hno_match t Hin Hold).
  - exact Htime.
Qed.

Lemma emit_fresh tid imem mem tlbi recipient ts next :
  TLBI.tid tlbi = tid →
  TState.process_event tid imem (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem)
    (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) ts = Ok next →
  TState.emit_promise tid imem (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem)
    (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) ts =
      Ok (TState.promise_tlbi (S (length mem)) next).
Proof.
  intros Howner Hprocess. unfold TState.emit_promise.
  cbn [Ev.tid]. rewrite bool_decide_true by exact Howner.
  rewrite process_event_pending, Hprocess. reflexivity.
Qed.

Lemma materialize_fresh tid imem pre tlbi recipient ts mem iis next :
  Memory.fulfill (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) (TState.prom_tlbi ts) mem = None →
  TState.process_event tid imem (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem)
    (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) ts = Ok next →
  pre < S (length mem) →
  Exec.elem_of_results
    (PPState.Make (set TState.prom_tlbi (filter (λ t, t ≠ S (length mem))) next)
      (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem) iis, (S (length mem), true))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient (PPState.Make ts mem iis)).
Proof.
  intros Hnone Hprocess Hpre.
  unfold materialize_tlbi_for_recipient.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [PPState.state PPState.mem]. rewrite Hnone.
  eapply Exec.elem_of_bind_intro.
  - eapply Exec.elem_of_bind_intro.
    + apply Exec.elem_of_liftSt with
        (st' := Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem)
        (a := S (length mem)).
      change ((Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem, S (length mem)) ∈
        [(Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem, S (length mem))]).
      left; reflexivity.
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      eapply Exec.elem_of_bind_intro; [apply exec_lift_result; exact Hprocess|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
      apply Exec.elem_of_mret.
  - eapply exec_guard_discard_bind_intro; [exact Hpre|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_mret.
Qed.
Lemma materialize_fulfilled tid imem pre tlbi recipient ts mem iis time :
  Memory.fulfill (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) (TState.prom_tlbi ts) mem = Some time →
  pre < time →
  Exec.elem_of_results
    (PPState.Make (set TState.prom_tlbi (filter (λ t, t ≠ time)) ts) mem iis, (time, false))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient (PPState.Make ts mem iis)).
Proof.
  intros Hfulfill Hpre. unfold materialize_tlbi_for_recipient.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [PPState.state PPState.mem]. rewrite Hfulfill.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  eapply exec_guard_discard_bind_intro; [exact Hpre|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  apply Exec.elem_of_mret.
Qed.

Lemma materialize_fresh_inv tid imem pre tlbi recipient ts mem iis ppst' time :
  Exec.elem_of_results (ppst', (time, true))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient (PPState.Make ts mem iis)) →
  Memory.fulfill (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) (TState.prom_tlbi ts) mem = None ∧
  time = S (length mem) ∧ pre < S (length mem) ∧
  ∃ next,
    TState.process_event tid imem (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem)
      (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) ts = Ok next ∧
    ppst' = PPState.Make (set TState.prom_tlbi (filter (λ t, t ≠ S (length mem))) next)
      (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem) iis.
Proof.
  intro Hrun. unfold materialize_tlbi_for_recipient in Hrun.
  VMMemoryGrowth.invert_execution; cbn in *; subst; try discriminate.
  repeat split; try assumption. eexists. split.
  - apply PromiseFirstCurrent.lift_result_res_success. eassumption.
  - reflexivity.
Qed.

Lemma clear_pending time ts :
  set TState.prom_tlbi (filter (λ t, t ≠ time)) (TState.promise_tlbi time ts) =
  set TState.prom_tlbi (filter (λ t, t ≠ time)) ts.
Proof.
  destruct ts. unfold TState.promise_tlbi. cbn.
  rewrite decide_False by congruence. reflexivity.
Qed.

(** A fresh TLBI recipient event can be moved immediately before its
    materialization. Cache histories, views, pending events and IIS all agree
    afterwards. The only premise beyond the actual successful run says the
    TLBI is issued by this thread, as run_tlbi constructs it. *)
Theorem materialize_fresh_normalization tid imem pre tlbi recipient ts mem iis ppst' time :
  TLBI.tid tlbi = tid →
  Exec.elem_of_results (ppst', (time, true))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient (PPState.Make ts mem iis)) →
  ∃ issued,
    TState.emit_promise tid imem (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem)
      (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) ts = Ok issued ∧
    Exec.elem_of_results (ppst', (time, false))
      (materialize_tlbi_for_recipient tid imem pre tlbi recipient
        (PPState.Make issued (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem) iis)).
Proof.
  intros Howner Hrun.
  destruct (materialize_fresh_inv tid imem pre tlbi recipient ts mem iis ppst' time Hrun)
    as [Hnone [-> [Hpre [next [Hprocess ->]]]]].
  exists (TState.promise_tlbi (S (length mem)) next). split.
  - apply emit_fresh; assumption.
  - rewrite <- (clear_pending (S (length mem)) next).
    apply materialize_fulfilled; [|exact Hpre].
    pose proof (VMReadReplay.run_tlb_frame _ ts next Hprocess) as Hframe.
    change (TState.dsb_epoch (TState.promise_tlbi (S (length mem)) next))
      with (TState.dsb_epoch next).
    change (TState.prom_tlbi (TState.promise_tlbi (S (length mem)) next))
      with (S (length mem) :: TState.prom_tlbi next).
    rewrite Hframe.
    change (Memory.fulfill (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts))
      (S (length mem) :: TState.prom_tlbi ts)
      (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts) :: mem) = Some (S (length mem))).
    apply fulfill_fresh, Hnone.
Qed.
End VMTLBINormalization.
