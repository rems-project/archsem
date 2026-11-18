(******************************************************************************)
(* Exclusion initialization, promises, broadcast and machine instructions     *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstFreshBroadcast PromiseFirstSailVMViews
  PromiseFirstSailVMCacheState PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveHistory
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveThread
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMSwapRemoveStampRun PromiseFirstSailVMSwapRemoveTLBI
  PromiseFirstSailVMSwapRemoveInvariant.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveMachine.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Definition thread_ok p ts := VMSwapRemoveThread.thread_ok p ts ∧ VMSwapRemoveStamps.ts_ok p ts.

Lemma initial p bound ts : bound < p → VMViews.ts_ok bound ts →
  (∀ c, TState.tlb ts = Some c → Forall (λ root, root.2 ≤ bound) (TLB.asid_roots c)) → thread_ok p ts.
Proof.
  intros Hp Hts Hroots. split; [split|].
  - eapply VMSwapRemoveViews.ts_before; eassumption.
  - intros c Hc. eapply VMSwapRemoveHistory.cache_bounded;
      [exact Hp|apply (VMViews.ok_cache _ _ Hts c Hc)|apply Hroots, Hc].
  - eapply VMSwapRemoveStamps.ts_before; eassumption.
Qed.

Lemma pp_init p ts mem : 0 < p → VMViews.ts_ok (length mem) ts → thread_ok p ts →
  VMSwapRemoveInvariant.ok p (PPState.Make ts mem IIS.init).
Proof.
  intros Hp Hbound [Hviews Hstamps]. split; [split|split].
  - exact Hbound.
  - eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. lia.
  - split; [exact Hviews|]. apply VMSwapRemoveViews.iis_init, VMSwapRemoveState.allowed_zero, Hp.
  - split; [exact Hstamps|apply VMSwapRemoveStamps.iis_init].
Qed.

Lemma emit_vcse tid imem mem ev ts ts' : TState.emit_promise tid imem mem ev ts = Ok ts' →
  TState.vcse ts' = TState.vcse ts.
Proof.
  unfold TState.emit_promise. intro Hrun.
  destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hrun) as [o ->].
  destruct (bool_decide _); [destruct ev|]; reflexivity.
Qed.

Lemma emit_ok p tid imem mem ev ts ts' : length mem ≠ p → thread_ok p ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → thread_ok p ts'.
Proof.
  intros Hlen [[Hviews Hcache] Hstamps] Hrun.
  pose proof (emit_vcse _ _ _ _ _ _ Hrun) as Hvc.
  split; [split|].
  - rewrite Hvc. eapply VMSwapRemoveViews.emit_promise; [left; exact Hlen|exact Hviews|exact Hrun].
  - eapply VMSwapRemoveState.emit_cache; eassumption.
  - eapply VMSwapRemoveStamps.emit_promise; eassumption.
Qed.

Lemma emit_foreign tid imem mem tlbi rc epoch ts : tid ≠ rc → tid ≠ TLBI.tid tlbi →
  TState.emit_promise tid imem mem (Ev.Tlbi tlbi rc epoch) ts = Ok ts.
Proof.
  intros Hrc Hissuer. unfold TState.emit_promise. cbn [Ev.tid].
  case_bool_decide; [congruence|].
  unfold TState.process_event, TState.run_tlb. destruct ts as [wr pt regs levs coh tcoh rd w dmbst dmb dsb spec cse
    self other msr acq rel fwd xcl ep cache]. cbn [TState.tlb]. destruct cache as [cache|]; [|reflexivity].
  unfold TLB.fill_promise. csimp. unfold TLB.fill_event.
  rewrite decide_False by exact Hrc. reflexivity.
Qed.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Definition state_ok p (target : fin n) (st : state) :=
  VMViews.state_ok st ∧ thread_ok p (PState.tstate target st).

Lemma promise_foreign_initial target tlbi rc epoch st st' :
  fin_to_nat target ≠ rc → fin_to_nat target ≠ TLBI.tid tlbi → VMViews.state_ok st →
  (∀ c, TState.tlb (PState.tstate target st) = Some c →
    Forall (λ root, root.2 ≤ length (PState.events st)) (TLB.asid_roots c)) →
  PState.promise prom (Ev.Tlbi tlbi rc epoch) st = Ok st' →
  state_ok (S (length (PState.events st))) target st'.
Proof.
  intros Hrc Hissuer Hbounds Hroots Hrun. split; [eapply VMViews.promise_ok; eassumption|].
  unfold PState.promise in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap target) as Hlook. cbn in Hlook.
  rewrite emit_foreign in Hlook by assumption. unfold PState.tstate. cbn. injection Hlook as <-.
  apply (initial _ (length (PState.events st))); [lia|apply Hbounds|exact Hroots].
Qed.

Lemma promise_ok p target ev st st' : p ≤ length (PState.events st) → state_ok p target st →
  PState.promise prom ev st = Ok st' → state_ok p target st'.
Proof.
  intros Hb [Hbounds Htarget] Hrun. split; [eapply VMViews.promise_ok; eassumption|].
  unfold PState.promise in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  unfold PState.tstate. cbn. eapply emit_ok;
    [|exact Htarget|exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap target)].
  destruct st. cbn in Hb |- *. lia.
Qed.

Lemma broadcast_ok p (target owner : fin n) imem base extra (states states' : vec TState.t n) :
  p ≤ length base → thread_ok p (states !!! target) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states' → thread_ok p (states' !!! target).
Proof.
  intros Hb Hpre. revert states'. induction extra as [|ev extra IH]; intros states' Hrun.
  - injection Hrun as <-. exact Hpre.
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid;
      [|discriminate]. cbn [mbind result_bind] in Hrun.
    pose proof (IH mid eq_refl) as Hrest.
    pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun target) as Hlook. cbn in Hlook.
    destruct (decide (target = owner)).
    + injection Hlook as <-. exact Hrest.
    + eapply emit_ok; [|exact Hrest|exact Hlook]. cbn. rewrite length_app. cbn in Hb |- *. lia.
Qed.

Theorem run_tid_ok target owner isem l r tlbi rc epoch st st' : fin_to_nat target ≠ rc →
  PState.events st = l ++ Ev.Tlbi tlbi rc epoch :: r → state_ok (S (length r)) target st →
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom owner st) →
  state_ok (S (length r)) target st'.
Proof.
  intros Hrc Hmem [Hbounds Htarget] Hrun. split; [eapply VMViews.run_tid_ok; eassumption|].
  destruct (run_tid_broadcast_decompose prom isem owner st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  assert (Hinitbound : VMViews.ok (PPState.Make (PState.tstate owner st) (PState.events st) IIS.init)).
  { split; [apply Hbounds|]. eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. lia. }
  destruct (VMViews.instruction_ok n owner (PState.initmem st) isem _ _ () Hinitbound Hinst)
    as [_ [extra Hextra]]. cbn in Hextra. subst mem.
  rewrite length_app, Nat.add_sub, take_app_length in Hstates.
  unfold PState.tstate. cbn. eapply broadcast_ok; [| |exact Hstates]; [rewrite Hmem, length_app; cbn; lia|].
  destruct (decide (target = owner)) as [->|Hne].
  - rewrite vlookup_insert.
    assert (Hinit : VMSwapRemoveInvariant.ok (S (length r))
        (PPState.Make (PState.tstate owner st) (PState.events st) IIS.init)) by
      (apply pp_init; [lia|apply Hbounds|exact Htarget]).
    destruct (VMSwapRemoveInvariant.instruction_ok n owner (PState.initmem st) r tlbi rc epoch Hrc l
      isem (PPState.Make (PState.tstate owner st) (PState.events st) IIS.init)
      (PPState.Make ts (extra ++ PState.events st) iis) () Hmem Hinit Hinst)
      as [[_ [[Hts _] [Hstamps _]]] _].
    split; assumption.
  - rewrite vlookup_insert_ne; [exact Htarget|congruence].
Qed.
End Machine.
End VMSwapRemoveMachine.
