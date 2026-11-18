(******************************************************************************)
(* A zero-length write refutes unrestricted backward lookup replay             *)
(******************************************************************************)
From ASCommon Require Import Options Common CResult CList Exec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMWalkStart.
#[local] Open Scope stdpp.
#[local] Open Scope bv.

(** [LookupBi] quantifies over every memory event. A zero-length write can
    duplicate a descriptor candidate without giving it a fresh timestamp.
    The table traversal then adds the interval [1,0], which has no backward
    match. The thread state comes from initialization and promise delivery,
    and satisfies the stated view invariant. [VMEventValidity] and
    [VMEventCertification] prove positivity for fresh Sail events and
    certification candidates; [LookupReplay] now requires that property. *)
Module VMLookupZeroWrite.
Definition imem : memoryMap :=
  ∅ |> mem_insert 0 8 0x1003 |> mem_insert 0x1000 8 0x401.
Definition regs : registerMap :=
  ∅ |> reg_insert CurrentEL 1 |> reg_insert SCTLR_EL1 1
    |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
    |> reg_insert ID_AA64MMFR1_EL1 0.
Definition write := Ev.Msg (Msg.make 1 0x1000 8 0).
Definition empty_write := Ev.Msg (Msg.make 1 0x1000 0 0).
Definition old_state :=
  ts ← TState.init 0 imem regs;
  TState.emit_promise 0 imem [write] write ts.
Definition new_state :=
  ts ← old_state;
  TState.emit_promise 0 imem [empty_write; write] empty_write ts.
Definition lookup (mem : list Ev.t) (r : result string TState.t) :=
  match r with
  | Ok ts => Exec.results (TState.tlb_lookup 0 imem mem ts false false 0 0 0
      0 0 (pred (TState.min_promise (length mem) ts)))
  | Error _ => []
  end.
Definition old_results := lookup [write] old_state.
Definition new_results := lookup [empty_write; write] new_state.
Definition extra := TLB.Result.make 0 [0x1003; 0] 1 0 None.
Lemma old_list : old_results =
  [TLB.Result.make 0 [0x1003; 0x401] 0 1 None;
   TLB.Result.make 0 [0x1003; 0] 1 1 None].
Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.
Lemma new_list : new_results =
  [TLB.Result.make 0 [0x1003; 0x401] 0 2 None;
   TLB.Result.make 0 [0x1003; 0] 1 2 None; extra].
Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.
Lemma extra_member : extra ∈ new_results.
Proof. rewrite new_list. right. right. left. Qed.
Lemma old_end r : r ∈ old_results → TLB.Result.path r = [0x1003; 0] →
  TLB.Result.tend r = 1%nat.
Proof.
  rewrite old_list. intros Hr Hp.
  apply elem_of_cons in Hr as [->|Hr].
  - discriminate Hp.
  - apply list_elem_of_singleton in Hr as ->. reflexivity.
Qed.

#[local] Open Scope nat_scope.

Lemma old_ok ts : old_state = Ok ts → VMViews.ts_ok 1 ts.
Proof.
  unfold old_state. destruct (TState.init 0 imem regs) as [init|err] eqn:Hi;
    cbn [mbind result_bind]; [|discriminate].
  intro He. eapply (VMViews.emit_promise 0 imem [write] write 0 init ts);
    [cbn; lia| |exact He].
  eapply VMViews.init, Hi.
Qed.

Lemma old_bound : (λ ts, pred (TState.min_promise 1 ts)) <$> old_state = Ok 1.
Proof. vm_compute. reflexivity. Qed.
Lemma new_bound : (λ ts, pred (TState.min_promise 2 ts)) <$> new_state = Ok 2.
Proof. vm_compute. reflexivity. Qed.

Theorem lookup_bi_zero_write_false :
  ¬ VMWalkStart.LookupBi 0 imem [write] empty_write false.
Proof.
  intro HB.
  pose proof old_list as Hl. pose proof new_list as Hl'.
  unfold old_results, lookup in Hl. unfold new_results, lookup in Hl'.
  destruct old_state as [ts|err] eqn:Hold; [|discriminate Hl].
  destruct new_state as [issued|err'] eqn:Hnew; [|discriminate Hl'].
  assert (He : TState.emit_promise 0 imem [empty_write; write] empty_write ts = Ok issued).
  { unfold new_state in Hnew. rewrite Hold in Hnew. exact Hnew. }
  pose proof old_bound as Ho. rewrite Hold in Ho. injection Ho as Ho.
  pose proof new_bound as Hn. rewrite Hnew in Hn. injection Hn as Hn.
  destruct (HB ts issued false false 0%bv 0%bv 0%bv 0 0
    (old_ok ts Hold) ltac:(discriminate) He ltac:(lia) ltac:(lia))
    as (Hle & Hfacts & Hfw & Hbw).
  assert (Hx : extra ∈ Exec.results (TState.tlb_lookup 0 imem [empty_write; write]
    issued false false 0%bv 0%bv 0%bv 0 0 (pred (TState.min_promise 2 issued)))).
  { rewrite Hl'. right. right. left. }
  destruct (Hbw extra Hx ltac:(cbn; lia)) as (r & Hr & Hrel).
  assert (Hr' : r ∈ old_results).
  { unfold old_results, lookup. rewrite Hold. exact Hr. }
  destruct Hrel as (_ & Hp & _ & Heq & _).
  pose proof (old_end r Hr' (eq_sym Hp)) as Hend.
  change (0 = TLB.Result.tend r ∨
    (TLB.Result.tend r = pred (TState.min_promise 1 ts) ∧
      0 = pred (TState.min_promise 2 issued))) in Heq.
  rewrite Ho, Hn, Hend in Heq. destruct Heq as [Heq|[Heq Heq']]; lia.
Qed.

Corollary unrestricted_lookup_replay_false :
  ¬ (∀ (tid : fin 2) imem mem ev own, VMWalkStart.LookupBi tid imem mem ev own).
Proof.
  intro H. apply lookup_bi_zero_write_false.
  exact (H 0%fin imem [write] empty_write false).
Qed.
End VMLookupZeroWrite.
