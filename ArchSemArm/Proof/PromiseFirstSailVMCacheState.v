(******************************************************************************)
(* Thread-state cache invariant at the current memory length                   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheIndexed
  PromiseFirstSailVMCacheLastTLBI PromiseFirstSailVMCacheOrder.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** A thread cache is ordered and bounded by [bound], has unique entries in
    each context and a coherent physical-page index. Every cache operation of
    a thread keeps this at the memory length, provided the time it is given
    does not exceed the memory length. *)
Module VMCacheState.
Import VMPromising VMCacheLastTLBI.
Local Notation action A := (stateT TLB.t (result string) A).

Definition cache_inv bound (cache : TLB.t) :=
  VMCacheOrder.good bound cache ∧ unique cache ∧ VMCacheIndexed.valid cache.

Definition cache_ok bound (ts : TState.t) :=
  ∀ cache, TState.tlb ts = Some cache → cache_inv bound cache.

Lemma cache_inv_mono bound bound' cache : bound ≤ bound' → cache_inv bound cache → cache_inv bound' cache.
Proof. intros Hle [Hgood Hrest]. split; [eapply VMCacheOrder.good_mono; eassumption|exact Hrest]. Qed.

Lemma cache_ok_mono bound bound' ts : bound ≤ bound' → cache_ok bound ts → cache_ok bound' ts.
Proof. intros Hle Hok cache Hcache. eapply cache_inv_mono; [exact Hle|]. apply Hok, Hcache. Qed.

(** A cache step from bound [bound] to bound [bound']. *)
Definition step_inv {A} bound bound' (run : action A) :=
  ∀ old new value, cache_inv bound old → run old = Ok (new, value) → cache_inv bound' new.

Lemma run_tlb_ok bound bound' run ts ts' :
  step_inv bound bound' run → cache_ok bound ts → TState.run_tlb run ts = Ok ts' → cache_ok bound' ts'.
Proof.
  intros Hrun Hok Hts. unfold TState.run_tlb in Hts.
  destruct (TState.tlb ts) as [cache|] eqn:Hcache.
  - unfold fmap, result_fmap, mbind, result_bind in Hts.
    destruct (run cache) as [[next value]|err] eqn:Hnext; [|discriminate].
    cbn in Hts. injection Hts as <-. intros final Hfinal. cbn in Hfinal. injection Hfinal as <-.
    eapply Hrun; [apply Hok, Hcache|exact Hnext].
  - injection Hts as <-. intros cache Hsome. rewrite Hcache in Hsome. discriminate.
Qed.

Lemma step_ret {A} bound (value : A) : step_inv bound bound (mret value).
Proof.
  intros old new result Hold Hrun. change (@Ok string _ (old, value) = Ok (new, result)) in Hrun.
  injection Hrun as <- <-. exact Hold.
Qed.

Lemma step_bind {A B} bound mid bound' (run : action A) (next : A → action B) :
  step_inv bound mid run → (∀ value, step_inv mid bound' (next value)) → step_inv bound bound' (run ≫= next).
Proof.
  intros Hfirst Hnext old new result Hold Hrun. unfold mbind, st_bind, result_bind in Hrun.
  destruct (run old) as [[state value]|err] eqn:Hmid; [|discriminate].
  eapply Hnext; [eapply Hfirst; eassumption|exact Hrun].
Qed.

Lemma step_othrow {A} bound (err : string) (opt : option A) : step_inv bound bound (othrow err opt).
Proof. destruct opt; [apply step_ret|]. intros old new value Hold Hrun. discriminate. Qed.

Lemma step_fill_promise tid imem mem ev bound :
  bound ≤ length mem → step_inv bound (length mem) (TLB.fill_promise tid imem mem ev).
Proof.
  intros Hbound old new [] [Hgood [Hunique Hvalid]] Hrun. split; [|split].
  - eapply VMCacheOrder.good_fill_promise; eassumption.
  - eapply unique_fill_promise; eassumption.
  - eapply VMCacheIndexed.fill_promise; eassumption.
Qed.

Lemma step_fill_cse tid imem mem time ttbr0 ttbr1 bound :
  time ≤ length mem → step_inv bound (length mem) (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  intros Htime old new [] [Hgood [Hunique Hvalid]] Hrun. split; [|split].
  - replace (length mem) with (time `max` length mem) by lia.
    eapply VMCacheOrder.good_fill_cse; eassumption.
  - eapply unique_fill_cse; eassumption.
  - eapply VMCacheIndexed.fill_cse; eassumption.
Qed.

Lemma step_fill_asid_root tid imem mem root time bound :
  time ≤ length mem → step_inv bound (length mem) (TLB.fill_asid_root tid imem mem root time).
Proof.
  intros Htime old new [] [Hgood [Hunique Hvalid]] Hrun. split; [|split].
  - replace (length mem) with (time `max` length mem) by lia.
    eapply VMCacheOrder.good_fill_asid_root; eassumption.
  - eapply unique_fill_asid_root; eassumption.
  - eapply VMCacheIndexed.fill_asid_root; eassumption.
Qed.

Theorem init tid imem iregs ts : TState.init tid imem iregs = Ok ts → cache_ok 0 ts.
Proof.
  unfold TState.init, othrow, guard_or, mbind, result_bind, fmap, result_fmap.
  destruct (reg_lookup CurrentEL iregs); [|discriminate]. cbn.
  match goal with |- context[match ?d with left _ => _ | right _ => _ end] => destruct d end;
    cbn; [|discriminate].
  destruct (reg_lookup SCTLR_EL1 iregs); [|discriminate]. cbn.
  match goal with |- context[if ?b then _ else _] => destruct b end.
  - destruct (TLB.init tid imem iregs) as [cache|] eqn:Hinit; [|discriminate]. cbn.
    intro Hts. injection Hts as <-. intros final Hfinal. cbn in Hfinal. injection Hfinal as <-.
    split; [eapply VMCacheOrder.good_init; exact Hinit|].
    split; [eapply unique_init; exact Hinit|eapply VMCacheIndexed.init; exact Hinit].
  - intro Hts. injection Hts as <-. intros cache Hcache. discriminate.
Qed.

Theorem process_event tid imem mem ev bound ts ts' :
  bound ≤ length mem → cache_ok bound ts →
  TState.process_event tid imem mem ev ts = Ok ts' → cache_ok (length mem) ts'.
Proof.
  intros Hbound Hok Hrun. eapply run_tlb_ok; [|exact Hok|exact Hrun].
  apply step_fill_promise, Hbound.
Qed.

Theorem emit_promise tid imem mem ev bound ts ts' :
  bound ≤ length mem → cache_ok bound ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → cache_ok (length mem) ts'.
Proof.
  intros Hbound Hok Hrun. unfold TState.emit_promise in Hrun.
  eapply process_event; [exact Hbound| |exact Hrun].
  case_bool_decide; [destruct ev|]; exact Hok.
Qed.

Theorem cse imem mem tid time bound ts ts' :
  time ≤ length mem → cache_ok bound ts →
  TState.cse imem mem tid time ts = Ok ts' → cache_ok (length mem) ts'.
Proof.
  intros Htime Hok Hrun. unfold TState.cse in Hrun.
  unfold mbind, result_bind in Hrun.
  match type of Hrun with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hrun as <-. eapply run_tlb_ok; [| |exact Hmid]; [|exact Hok].
  intros old new [] Hold Hstep.
  unfold mbind, st_bind, result_bind, mret, st_ret, result_ret, othrow in Hstep.
  cbn -[TLB.fill_cse TState.read_sreg_direct] in Hstep.
  destruct (TState.read_sreg_direct _ TTBR0_EL1) as [ttbr0|]; [|discriminate].
  eapply step_fill_cse; [exact Htime|exact Hold|exact Hstep].
Qed.

(** Every root fill in a system-register write uses a time no later than the
    memory length; the resulting cache is then bounded by the memory length. *)
Lemma step_roots {T} bound (roots : list T) (fill : T → action ()) :
  (∀ root, root ∈ roots → step_inv bound bound (fill root)) →
  step_inv bound bound (mapM fill roots).
Proof.
  induction roots as [|root roots IH]; intro Hfill; cbn [mapM]; [apply step_ret|].
  apply step_bind with (mid := bound); [apply Hfill; left|intro].
  apply step_bind with (mid := bound); [apply IH; intros other Hin; apply Hfill; right; exact Hin|intro].
  apply step_ret.
Qed.

Lemma step_some {A B} bound bound' (err : string) (value : A) (next : A → action B) :
  step_inv bound bound' (next value) → step_inv bound bound' (othrow err (Some value) ≫= next).
Proof. intros Hnext old new result Hold Hrun. exact (Hnext old new result Hold Hrun). Qed.

Definition roots_bounded bound (roots : option (list (bv 64 * nat))) :=
  ∀ root, root ∈ default [] roots → root.2 ≤ bound.

Theorem add_wsreg tid imem mem sreg val time bound ts ts' :
  bound ≤ length mem → time ≤ length mem → cache_ok bound ts →
  roots_bounded (length mem) (TState.read_sreg_indirect ts TTBR0_EL1) →
  roots_bounded (length mem) (TState.read_sreg_indirect ts TTBR1_EL1) →
  TState.add_wsreg tid imem mem sreg val time ts = Ok ts' → cache_ok (length mem) ts'.
Proof.
  intros Hbound Htime Hok Hroots0 Hroots1 Hrun. unfold TState.add_wsreg in Hrun.
  unfold mbind, result_bind in Hrun.
  match type of Hrun with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hrun as <-. change (cache_ok (length mem) mid).
  eapply run_tlb_ok; [| |exact Hmid]; [|exact (cache_ok_mono bound _ ts Hbound Hok)].
  destruct sreg as [r|r|r|r]; try apply step_ret.
  destruct r; try apply step_ret; cbv beta iota zeta.
  - (* TTBR0_EL1 *)
    apply step_bind with (mid := length mem); [apply step_fill_asid_root, Htime|intros []].
    apply step_bind with (mid := length mem); [|intro; apply step_ret].
    apply step_roots. intros [ttbr1 view] Hin. apply step_fill_asid_root.
    specialize (Hroots1 _ Hin). cbn in Hroots1. unfold join, join_nat in *. lia.
  - (* TTBR1_EL1 *)
    destruct (TState.read_sreg_indirect ts TTBR0_EL1) as [ttbr0s|] eqn:Hread;
      [|intros old new value _ Hstep; discriminate].
    apply step_some.
    apply step_bind with (mid := length mem); [|intro; apply step_ret].
    apply step_roots. intros [ttbr0 view] Hin. apply step_fill_asid_root.
    assert (Hview : view ≤ length mem).
    { apply (Hroots0 (ttbr0, view)). exact Hin. }
    unfold join, join_nat in *. lia.
Qed.

End VMCacheState.
