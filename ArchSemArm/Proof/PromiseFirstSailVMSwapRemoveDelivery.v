(******************************************************************************)
(* Promise delivery and thread execution after removing a foreign TLBI        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstFreshBroadcast
  PromiseFirstSailVMViews PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveLocal
  PromiseFirstSailVMSwapRemoveCore PromiseFirstSailVMSwapRemoveMachine
  PromiseFirstSailVMSwapRemoveOutcome PromiseFirstSailVMPageWrites PromiseFirstSailVMSwapPos.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveDelivery.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Section Removed.
Context (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).

Lemma update_rel f1 f2 a b :
  (∀ ts, f2 (ts_map g ts) = ts_map g (f1 ts)) →
  (∀ ts cache, f2 (setv TState.tlb cache ts) = setv TState.tlb cache (f2 ts)) →
  (∀ ts, TState.tlb (f2 ts) = TState.tlb ts) → ts_rel r a b → ts_rel r (f1 a) (f2 b).
Proof.
  intros Hmap Hcomm Htlb [Hshape Hsim]. unfold ts_rel. rewrite <- Hmap. split.
  - rewrite Htlb. transitivity (f2 (setv TState.tlb (TState.tlb b) (ts_map g a))).
    + apply f_equal, Hshape.
    + apply Hcomm.
  - rewrite !Htlb. exact Hsim.
Qed.

Lemma promise_write_rel v a b : ts_rel r a b →
  ts_rel r (TState.promise_write v a) (TState.promise_write (g v) b).
Proof.
  apply update_rel; [intro; symmetry; apply (VMSwapRemoveMap.map_promise_write p ltac:(lia))
    |intros; reflexivity|intro; reflexivity].
Qed.
Lemma promise_tlbi_rel v a b : ts_rel r a b →
  ts_rel r (TState.promise_tlbi v a) (TState.promise_tlbi (g v) b).
Proof.
  apply update_rel; [intro; symmetry; apply (VMSwapRemoveMap.map_promise_tlbi p ltac:(lia))
    |intros; reflexivity|intro; reflexivity].
Qed.

Theorem emit_remove tid l ev a b a' : ts_rel r a b → ts_inv imem r tlbi rc epoch l a →
  TState.emit_promise tid imem (ev :: l ++ e :: r) ev a = Ok a' →
  ∃ b', TState.emit_promise tid imem (ev :: l ++ r) ev b = Ok b' ∧ ts_rel r a' b' ∧
    ts_inv imem r tlbi rc epoch (ev :: l) a'.
Proof.
  intros Hrel Hinv Hrun. unfold TState.emit_promise in Hrun |- *.
  assert (Htime : length (ev :: l ++ r) = g (length (ev :: l ++ e :: r))).
  { rewrite unshift_ge by (cbn; rewrite length_app; cbn; lia). cbn. rewrite !length_app. cbn. lia. }
  destruct (bool_decide _); [destruct ev|].
  all: try rewrite Htime.
  all: eapply process_event_remove; [| |exact Hrun].
  all: try solve [exact Hrel|apply promise_write_rel, Hrel|apply promise_tlbi_rel, Hrel].
  all: intros c Hc; apply Hinv, Hc.
Qed.

Lemma emit_core tid l ev a a' : VMSwapRemoveCore.core imem r tlbi rc epoch l a →
  TState.emit_promise tid imem (ev :: l ++ e :: r) ev a = Ok a' →
  VMSwapRemoveCore.core imem r tlbi rc epoch (ev :: l) a'.
Proof.
  intros Hcore Hrun. unfold TState.emit_promise in Hrun.
  eapply VMSwapRemoveCore.process_event; [|exact Hrun].
  destruct (bool_decide _); [destruct ev|].
  all: apply (VMSwapRemoveCore.frame imem r tlbi rc epoch l a).
  all: try reflexivity.
  all: try exact Hcore.
  all: apply Nat.le_refl.
Qed.

Theorem bcast_thread_remove {n} (owner : fin n) l extra i a b a' : i ≠ owner →
  ts_rel r a b → ts_inv imem r tlbi rc epoch l a →
  VMSwapInsert.bcast_thread owner imem (l ++ e :: r) extra i a = Ok a' →
  ∃ b', VMSwapInsert.bcast_thread owner imem (l ++ r) extra i b = Ok b' ∧
    ts_rel r a' b' ∧ ts_inv imem r tlbi rc epoch (extra ++ l) a'.
Proof.
  intros Hne Hrel Hinv. revert a' b Hrel. induction extra as [|ev older IH]; intros a' b Hrel Hrun.
  - injection Hrun as <-. exists b. split; [reflexivity|split; assumption].
  - cbn [VMSwapInsert.bcast_thread] in Hrun |- *.
    destruct (VMSwapInsert.bcast_thread owner imem (l ++ e :: r) older i a) as [mid|err] eqn:Hmid;
      [|discriminate].
    destruct (IH mid b Hrel eq_refl) as [mid' [Hmid' [Hrel' Hinv']]].
    rewrite Hmid'. cbn [mbind result_bind] in Hrun |- *.
    rewrite decide_False in Hrun |- * by exact Hne.
    rewrite !app_assoc in Hrun |- *.
    eapply emit_remove; eassumption.
Qed.

Lemma iis_init : iis_map g IIS.init = IIS.init.
Proof. unfold iis_map, IIS.init. cbn. rewrite unshift_zero. reflexivity. Qed.

Lemma pp_init l ts : VMViews.ts_ok (length (l ++ e :: r)) ts →
  VMSwapRemoveMachine.thread_ok p ts → ts_pos ts → VMPageWrites.ts_ok (l ++ e :: r) ts →
  VMSwapRemoveCore.core imem r tlbi rc epoch l ts →
  VMSwapRemoveOutcome.ok imem r tlbi rc epoch (PPState.Make ts (l ++ e :: r) IIS.init).
Proof.
  intros Hbounds Hthread Hpos Hpage Hcore. split.
  - apply VMSwapRemoveMachine.pp_init; [lia|exact Hbounds|exact Hthread].
  - split; [exact Hpos|]. split; [exact Hpage|]. exists l. split; [reflexivity|exact Hcore].
Qed.
End Removed.

Section RunTid.
Context (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat) (bbm : bool) {n : nat} (isem : iMon ()).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

(** Replay the executing thread and expose the fresh-event deliveries. Each
    thread's exchange relation can then supply its own broadcast proof. *)
Theorem run_tid_remove (tid : fin n) (s s' s1 : state) l :
  fin_to_nat tid ≠ rc → PState.initmem s' = PState.initmem s →
  PState.events s = l ++ e :: r → PState.events s' = l ++ r →
  ts_rel r (PState.tstate tid s) (PState.tstate tid s') →
  VMSwapRemoveOutcome.ok (PState.initmem s) r tlbi rc epoch
    (PPState.Make (PState.tstate tid s) (PState.events s) IIS.init) →
  Exec.elem_of_results (s1, ()) (PState.run_tid isem prom tid s) →
  ∃ extra ts ts' iis,
    PState.initmem s1 = PState.initmem s ∧ PState.events s1 = extra ++ l ++ e :: r ∧
    ts_rel r ts ts' ∧
    VMSwapRemoveOutcome.ok (PState.initmem s) r tlbi rc epoch
      (PPState.Make ts (extra ++ l ++ e :: r) iis) ∧
    (∀ i, VMSwapInsert.bcast_thread tid (PState.initmem s) (l ++ e :: r) extra i
      (vinsert tid ts (PState.tstates s) !!! i) = Ok (PState.tstates s1 !!! i)) ∧
    (∀ states', (∀ i, VMSwapInsert.bcast_thread tid (PState.initmem s) (l ++ r) extra i
      (vinsert tid ts' (PState.tstates s') !!! i) = Ok (states' !!! i)) →
      Exec.elem_of_results (PState.Make states' (PState.initmem s) (extra ++ l ++ r), ())
        (PState.run_tid isem prom tid s')).
Proof.
  intros Hrc Himem Hmem Hmem' Hts Hok Hrun.
  destruct (run_tid_broadcast_decompose prom isem tid s s1 Hrun)
    as [ts [mem [iis [states [Hinst [Hb ->]]]]]].
  assert (Hbound : VMViews.ok (PPState.Make (PState.tstate tid s) (PState.events s) IIS.init)) by apply Hok.
  destruct (VMViews.instruction_ok n tid (PState.initmem s) isem _ _ () Hbound Hinst)
    as [_ [extra Hextra]]. cbn in Hextra. subst mem.
  assert (Hrel : related r tlbi rc epoch
    (PPState.Make (PState.tstate tid s) (PState.events s) IIS.init)
    (PPState.Make (PState.tstate tid s') (PState.events s') IIS.init)).
  { split; [exists l; auto|]. split; [exact Hts|symmetry; apply iis_init]. }
  destruct (proj1 (VMSwapRemoveOutcome.instruction_remove_sim (PState.initmem s) r tlbi rc epoch
    n tid isem _ _ Hrc Hrel Hok) _ () Hinst)
    as [[ts' mem' iis'] [Hinst' [[[prefix [Hlong Hshort]] [Hts' Hiis']] Hok']]].
  cbn in Hlong, Hshort, Hts', Hiis'. subst mem'.
  assert (Hprefix : prefix = extra ++ l).
  { rewrite Hmem, app_assoc in Hlong. symmetry. eapply app_inv_tail. exact Hlong. }
  subst prefix. rewrite length_app, Nat.add_sub, take_app_length in Hb.
  exists extra, ts, ts', iis. split; [reflexivity|]. split; [cbn; rewrite Hmem; reflexivity|].
  split; [exact Hts'|]. split; [rewrite <- Hmem; exact Hok'|]. split.
  - rewrite <- Hmem. exact (VMSwapInsert.broadcast_fresh_lookup bbm tid _ _ _ _ _ Hb).
  - intros states' Hall. rewrite app_assoc.
    replace (PState.initmem s) with (PState.initmem s') by exact Himem.
    apply run_tid_broadcast_intro with (ts := ts') (iis := iis').
    + rewrite Himem. exact Hinst'.
    + rewrite Hmem', <- app_assoc, length_app, Nat.add_sub, take_app_length.
      apply VMSwapInsert.broadcast_fresh_intro. rewrite Himem. exact Hall.
Qed.
End RunTid.
End VMSwapRemoveDelivery.
