(******************************************************************************)
(* Pending promises in reachable sail-tiny-arm promise-first states *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstConcreteCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** Histories are newest first. An event's timestamp is the length of the
    suffix starting at that event. *)
Fixpoint pending_event_times {E} (owned : E → bool) (mem : list E) : list nat :=
  match mem with
  | [] => []
  | ev :: rest =>
      if owned ev then S (length rest) :: pending_event_times owned rest
      else pending_event_times owned rest
  end.

Lemma pending_event_times_bounds {E} (owned : E → bool) mem t :
  t ∈ pending_event_times owned mem → 0 < t ∧ t ≤ length mem.
Proof.
  induction mem as [|ev mem IH]; cbn; [inversion 1|].
  destruct (owned ev).
  - intros Hin. apply elem_of_cons in Hin as [->|Hin]; [lia|].
    specialize (IH Hin). lia.
  - intro Hin. specialize (IH Hin). lia.
Qed.

Definition UM_pending_times tid : list Msg.t → list nat :=
  pending_event_times (λ msg, bool_decide (Msg.tid msg = tid)).

(** UM promise steps retain the initial instruction state and add exactly
    the timestamps of the issuing thread's events to its pending list. *)
Lemma UMSail_promise_first_state_shape nondet {n} (term : terminationCondition n)
    initMs st :
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  PState.initmem st = archState.memory initMs ∧
  ∀ tid : fin n,
    PState.tstate tid st = setv UMPromising.TState.prom
      (UM_pending_times (tid : nat) (PState.events st))
      (UMPromising.TState.init (archState.memory initMs) (archState.regs initMs !!! tid)).
Proof.
  intro Hreach. induction Hreach as [st Hinit|fuel st st' Hreach [Himem Hstates] Hstep].
  - destruct (UMPromising_initialization_success initMs st Hinit)
      as [Himem [Hmem Hstates]]. split; [exact Himem|].
    intro tid. specialize (Hstates tid). rewrite UMPromising_tState_init_ok in Hstates.
    injection Hstates as Hstates. rewrite <- Hstates, Hmem. reflexivity.
  - destruct (run_transition_promise_first_none_inv (sail_tiny_arm_sem nondet)
      term fuel st st' Hstep) as [owner [ev [nst [_ [Hpromise Hnext]]]]].
    subst nst. destruct (UMPromising_promise_success ev st st' Hpromise)
      as [Himem' [Hmem Hhooks]]. split; [rewrite Himem'; exact Himem|].
    intro tid. specialize (Hhooks tid). rewrite UMPromising_emit_promise_ok in Hhooks.
    rewrite Hstates in Hhooks. rewrite Hmem.
    unfold UM_pending_times. cbn [pending_event_times] in *.
    destruct (bool_decide (Msg.tid ev = (tid : nat))); injection Hhooks as Hhooks; rewrite <- Hhooks; reflexivity.
Qed.

Lemma UMSail_promise_first_pending_bounds nondet {n} (term : terminationCondition n)
    initMs st tid t :
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  t ∈ UMPromising.TState.prom (PState.tstate tid st) →
  0 < t ∧ t ≤ length (PState.events st).
Proof.
  intros Hreach Hin. destruct (UMSail_promise_first_state_shape nondet term initMs st Hreach)
    as [_ Hshape]. rewrite Hshape in Hin. cbn in Hin.
  eapply pending_event_times_bounds. exact Hin.
Qed.

Lemma UMSail_promise_first_zero_control nondet {n} (term : terminationCondition n)
    initMs st tid :
  PromiseFirstReachable UMPromising (sail_tiny_arm_sem nondet) term initMs true st →
  UMPromising.TState.min_new_prom_view (PState.tstate tid st) = 0 ∧
  UMPromising.TState.no_promises_until 0 (PState.tstate tid st).
Proof.
  intro Hreach. split.
  - destruct (UMSail_promise_first_state_shape nondet term initMs st Hreach)
      as [_ Hshape]. rewrite Hshape. reflexivity.
  - intros t Hin. eapply UMSail_promise_first_pending_bounds in Hin; [lia|exact Hreach].
Qed.

Definition VM_write_times tid : list Ev.t → list nat :=
  pending_event_times (λ ev, if ev is Ev.Msg msg then bool_decide (Msg.tid msg = tid)
    else false).
Definition VM_tlbi_times tid : list Ev.t → list nat :=
  pending_event_times (λ ev, if ev is Ev.Tlbi tlbi recipient then bool_decide (Ev.tid ev = tid)
    else false).

Local Lemma result_bind_ok_inv {E A B} (e : result E A) (k : A → result E B) b :
  (e ≫= k) = Ok b → ∃ a, e = Ok a ∧ k a = Ok b.
Proof.
  destruct e as [a|err]; cbn; [intros H; exists a; split; [reflexivity|exact H]|discriminate].
Qed.

Lemma VM_initial_promise_fields tid imem regs ts :
  VMPromising.TState.init tid imem regs = Ok ts →
  VMPromising.TState.prom_wr ts = [] ∧
  VMPromising.TState.prom_tlbi ts = [] ∧
  VMPromising.TState.min_new_prom_view ts = 0.
Proof.
  unfold VMPromising.TState.init. intro Hinit.
  apply result_bind_ok_inv in Hinit as [el [_ Hinit]].
  apply result_bind_ok_inv in Hinit as [guard [_ Hinit]].
  apply result_bind_ok_inv in Hinit as [sctlr [_ Hinit]].
  apply result_bind_ok_inv in Hinit as [tlb [_ Hinit]].
  injection Hinit as Hinit. subst ts. repeat split; reflexivity.
Qed.

Lemma VM_run_tlb_promise_fields upd ts ts' :
  VMPromising.TState.run_tlb upd ts = Ok ts' →
  VMPromising.TState.prom_wr ts' = VMPromising.TState.prom_wr ts ∧
  VMPromising.TState.prom_tlbi ts' = VMPromising.TState.prom_tlbi ts ∧
  VMPromising.TState.min_new_prom_view ts' = VMPromising.TState.min_new_prom_view ts.
Proof.
  unfold VMPromising.TState.run_tlb.
  destruct (VMPromising.TState.tlb ts) as [tlb|].
  - destruct (upd tlb) as [[tlb' []]|err]; cbn; [|discriminate].
    intro H. inversion H; subst. repeat split; reflexivity.
  - intro H. inversion H; subst. repeat split; reflexivity.
Qed.

Lemma VM_emit_promise_fields bbm tid imem mem ev ts ts' :
  Promising.emit_promise (VMPromising.VMPromising bbm) tid imem (ev :: mem) ev ts = Ok ts' →
  VMPromising.TState.prom_wr ts' =
    (if ev is Ev.Msg msg then
      if bool_decide (Msg.tid msg = tid) then S (length mem) :: VMPromising.TState.prom_wr ts
      else VMPromising.TState.prom_wr ts
    else VMPromising.TState.prom_wr ts) ∧
  VMPromising.TState.prom_tlbi ts' =
    (if ev is Ev.Tlbi tlbi recipient then
      if bool_decide (Ev.tid ev = tid) then S (length mem) :: VMPromising.TState.prom_tlbi ts
      else VMPromising.TState.prom_tlbi ts
    else VMPromising.TState.prom_tlbi ts) ∧
  VMPromising.TState.min_new_prom_view ts' = VMPromising.TState.min_new_prom_view ts.
Proof.
  rewrite VMPromising_emit_promise_result.
  unfold VMPromising.TState.emit_promise, VMPromising.TState.process_event.
  destruct ev; cbn [Ev.tid]; destruct (bool_decide _);
    intro H; apply VM_run_tlb_promise_fields in H; exact H.
Qed.

(** VM promise steps also process the TLB. Write and TLBI promise lists still
    contain exactly the issuing thread's corresponding event timestamps. *)
Lemma VMSail_promise_first_promise_inventory bbm nondet {n} (term : terminationCondition n)
    initMs st :
  PromiseFirstReachable (VMPromising.VMPromising bbm) (sail_tiny_arm_sem nondet)
    term initMs true st →
  PState.initmem st = archState.memory initMs ∧
  ∀ tid : fin n,
    VMPromising.TState.prom_wr (PState.tstate tid st) =
      VM_write_times (tid : nat) (PState.events st) ∧
    VMPromising.TState.prom_tlbi (PState.tstate tid st) =
      VM_tlbi_times (tid : nat) (PState.events st) ∧
    VMPromising.TState.min_new_prom_view (PState.tstate tid st) = 0.
Proof.
  intro Hreach. induction Hreach as [st Hinit|fuel st st' Hreach [Himem Hstates] Hstep].
  - destruct (VMPromising_initialization_success initMs st Hinit)
      as [Himem [Hmem Hstates]]. split; [exact Himem|].
    intro tid. specialize (Hstates tid). rewrite VMPromising_tState_init_result in Hstates.
    apply VM_initial_promise_fields in Hstates. rewrite Hmem. exact Hstates.
  - destruct (run_transition_promise_first_none_inv (sail_tiny_arm_sem nondet)
      term fuel st st' Hstep) as [owner [ev [nst [_ [Hpromise Hnext]]]]].
    subst nst. destruct (VMPromising_promise_success ev st st' Hpromise)
      as [Himem' [Hmem Hhooks]]. split; [rewrite Himem'; exact Himem|].
    intro tid. specialize (Hhooks tid). apply VM_emit_promise_fields in Hhooks.
    destruct (Hstates tid) as [Hwr [Htlbi Hmin]].
    destruct Hhooks as [Hwr' [Htlbi' Hmin']].
    rewrite Hwr', Htlbi', Hmin', Hwr, Htlbi, Hmin, Hmem.
    unfold VM_write_times, VM_tlbi_times. destruct ev; cbn [pending_event_times];
      repeat split; reflexivity.
Qed.

Lemma VMSail_promise_first_pending_bounds bbm nondet {n} (term : terminationCondition n)
    initMs st tid t :
  PromiseFirstReachable (VMPromising.VMPromising bbm) (sail_tiny_arm_sem nondet)
    term initMs true st →
  t ∈ (VMPromising.TState.prom_wr (PState.tstate tid st) ++
    VMPromising.TState.prom_tlbi (PState.tstate tid st))%list →
  0 < t ∧ t ≤ length (PState.events st).
Proof.
  intros Hreach Hin. destruct (VMSail_promise_first_promise_inventory bbm nondet term
    initMs st Hreach) as [_ Hshape]. destruct (Hshape tid) as [Hwr [Htlbi _]].
  rewrite Hwr, Htlbi in Hin. apply elem_of_app in Hin as [Hin|Hin];
    eapply pending_event_times_bounds; exact Hin.
Qed.

Lemma VMSail_promise_first_zero_control bbm nondet {n} (term : terminationCondition n)
    initMs st tid :
  PromiseFirstReachable (VMPromising.VMPromising bbm) (sail_tiny_arm_sem nondet)
    term initMs true st →
  VMPromising.TState.min_new_prom_view (PState.tstate tid st) = 0 ∧
  VMPromising.TState.no_promises_until 0 (PState.tstate tid st).
Proof.
  intro Hreach. split.
  - destruct (VMSail_promise_first_promise_inventory bbm nondet term initMs st Hreach)
      as [_ Hshape]. exact (proj2 (proj2 (Hshape tid))).
  - intros t Hin. eapply VMSail_promise_first_pending_bounds in Hin; [lia|exact Hreach].
Qed.
