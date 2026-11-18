(******************************************************************************)
(* Removal entry invariants along promises and mixed machine execution       *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstFreshBroadcast
  PromiseFirstSailVMViews PromiseFirstSailVMPageWrites PromiseFirstSailVMSwapPos
  PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveCore
  PromiseFirstSailVMSwapRemoveDelivery PromiseFirstSailVMSwapRemoveMachine
  PromiseFirstSailVMSwapRemoveInit PromiseFirstSailVMSwapRemoveOutcome PromiseFirstSailVMNormalization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveTrace.
Import VMPromising VMSwapRemoveRun.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma bcast_owner {n} (owner : fin n) imem base extra ts :
  VMSwapInsert.bcast_thread owner imem base extra owner ts = Ok ts.
Proof.
  induction extra as [|ev older IH]; [reflexivity|]. cbn [VMSwapInsert.bcast_thread]. rewrite IH.
  cbn. rewrite decide_True by reflexivity. reflexivity.
Qed.
Lemma bcast_core {n} (owner target : fin n) imem l r tlbi rc epoch extra ts ts' : target ≠ owner →
  VMSwapRemoveCore.core imem r tlbi rc epoch l ts →
  VMSwapInsert.bcast_thread owner imem (l ++ Ev.Tlbi tlbi rc epoch :: r) extra target ts = Ok ts' →
  VMSwapRemoveCore.core imem r tlbi rc epoch (extra ++ l) ts'.
Proof.
  intros Hne Hcore. revert ts'. induction extra as [|ev older IH]; intros ts' Hrun.
  - injection Hrun as <-. exact Hcore.
  - cbn [VMSwapInsert.bcast_thread] in Hrun.
    destruct (VMSwapInsert.bcast_thread owner imem (l ++ Ev.Tlbi tlbi rc epoch :: r) older target ts)
      as [mid|err] eqn:Hmid; [|discriminate].
    pose proof (IH mid eq_refl) as Hmidcore. cbn [mbind result_bind] in Hrun.
    rewrite decide_False in Hrun by exact Hne. rewrite app_assoc in Hrun.
    eapply VMSwapRemoveDelivery.emit_core; eassumption.
Qed.

Section Machine.
Context (bbm : bool) {n : nat} (target : fin n) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Hypothesis Hrc : fin_to_nat target ≠ rc.
Local Notation p := (S (length r)).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Definition ok (st : state) := VMSwapRemoveInit.state_ok st ∧
  VMSwapRemoveMachine.thread_ok p (PState.tstate target st) ∧
  ∃ l, PState.events st = l ++ e :: r ∧
    VMSwapRemoveCore.core (PState.initmem st) r tlbi rc epoch l (PState.tstate target st).

Lemma pp_ok st : ok st → VMSwapRemoveOutcome.ok (PState.initmem st) r tlbi rc epoch
  (PPState.Make (PState.tstate target st) (PState.events st) IIS.init).
Proof.
  intros [[Hroots [Hpos [[Hbounds Hpage] Hmsr]]] [Hthread [l [Hmem Hcore]]]].
  rewrite Hmem. apply VMSwapRemoveDelivery.pp_init.
  - rewrite <- Hmem. apply Hbounds.
  - exact Hthread.
  - apply Hpos.
  - rewrite <- Hmem. apply Hpage.
  - exact Hcore.
Qed.

Lemma promise_ok ev st st' : ok st → PState.promise prom ev st = Ok st' → ok st'.
Proof.
  clear Hrc.
  intros [Hglobal [Hthread [l [Hmem Hcore]]]] Hrun. split; [eapply VMSwapRemoveInit.promise_ok; eassumption|].
  assert (Hbounds : VMViews.state_ok st) by apply Hglobal.
  pose proof (VMSwapRemoveMachine.promise_ok bbm p target ev st st'
    ltac:(rewrite Hmem, length_app; cbn; lia) (conj Hbounds Hthread) Hrun) as [_ Hthread'].
  split; [exact Hthread'|]. unfold PState.promise in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  destruct st as [states imem mem]. cbn in *.
  exists (ev :: l). split; [cbn; rewrite Hmem; reflexivity|].
  unfold PState.tstate. cbn. pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap target) as Hlook.
  cbn in Hlook. rewrite Hmem in Hlook. eapply VMSwapRemoveDelivery.emit_core; eassumption.
Qed.

Theorem run_tid_ok isem (owner : fin n) st st' : ok st →
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom owner st) → ok st'.
Proof using Hrc.
  intros [Hglobal [Hthread [l [Hmem Hcore]]]] Hrun. split; [eapply VMSwapRemoveInit.run_tid_ok; eassumption|].
  assert (Hbounds : VMViews.state_ok st) by apply Hglobal.
  pose proof (VMSwapRemoveMachine.run_tid_ok bbm target owner isem l r tlbi rc epoch st st'
    Hrc Hmem (conj Hbounds Hthread) Hrun) as [_ Hthread'].
  split; [exact Hthread'|].
  destruct (run_tid_broadcast_decompose prom isem owner st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  assert (Hbound : VMViews.ok (PPState.Make (PState.tstate owner st) (PState.events st) IIS.init)).
  { split; [apply Hbounds|]. eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. lia. }
  destruct (VMViews.instruction_ok n owner (PState.initmem st) isem _ _ () Hbound Hinst)
    as [_ [extra Hextra]]. cbn in Hextra. subst mem.
  rewrite length_app, Nat.add_sub, take_app_length in Hstates.
  pose proof (VMSwapInsert.broadcast_fresh_lookup bbm owner _ _ _ _ _ Hstates target) as Hlook.
  exists (extra ++ l). split; [cbn; rewrite Hmem, app_assoc; reflexivity|]. unfold PState.tstate. cbn.
  destruct (decide (target = owner)) as [Heq|Hne].
  - subst owner. rewrite bcast_owner in Hlook. injection Hlook as <-. rewrite vlookup_insert.
    destruct (VMSwapRemoveCore.instruction_core (PState.initmem st) r tlbi rc epoch n target isem Hrc
      l (PPState.Make (PState.tstate target st) (PState.events st) IIS.init)
      (PPState.Make ts (extra ++ PState.events st) iis) () Hmem Hbound Hcore Hinst)
      as [l' [Hmem' Hcore']]. cbn in Hmem'.
    assert (Hl : l' = extra ++ l).
    { rewrite Hmem, app_assoc in Hmem'. symmetry. eapply app_inv_tail. exact Hmem'. }
    subst l'. exact Hcore'.
  - rewrite vlookup_insert_ne in Hlook by congruence. rewrite Hmem in Hlook.
    eapply bcast_core; [exact Hne|exact Hcore|exact Hlook].
Qed.

Theorem raw_trace_ok nondet term st evs st' : ok st →
  VMNormalization.RawTrace bbm nondet term st evs st' → ok st'.
Proof.
  intros Hok Htrace. induction Htrace as [|evs mid fin ev Htrace IH [_ Hpromise]]; [exact Hok|].
  eapply promise_ok; eassumption.
Qed.
Theorem mixed_rtc_ok nondet term st st' : ok st →
  rtc (VMNormalization.Mixed bbm nondet term) st st' → ok st'.
Proof using Hrc.
  intros Hok Hsteps. induction Hsteps as [st|st mid fin Hstep _ IH]; [exact Hok|].
  apply IH. destruct Hstep as [(tid & _ & Hrun)|(ev & _ & Hpromise)].
  - eapply run_tid_ok; eassumption.
  - eapply promise_ok; eassumption.
Qed.
Theorem initial st st' : PState.events st = r → fin_to_nat target ≠ TLBI.tid tlbi →
  VMSwapRemoveInit.state_ok st → PState.promise prom e st = Ok st' → ok st'.
Proof using Hrc.
  intros Hmem Hissuer Hglobal Hrun.
  pose proof (VMSwapRemoveInit.promise_foreign_initial bbm target tlbi rc epoch st st' Hrc Hissuer Hglobal Hrun)
    as [Hrel Hentry].
  rewrite Hmem in Hentry.
  destruct Hentry as [[Hbounds [[Hviews Hii] [Hstamps Hstampii]]] [Hpos [Hpage [l [Hmem' Hcore]]]]].
  split; [eapply VMSwapRemoveInit.promise_ok; eassumption|].
  split; [split; assumption|]. exists l. split; [exact Hmem'|].
  destruct (PromiseFirstCurrent.promise_success prom e st st' Hrun) as [Himem _].
  rewrite Himem. exact Hcore.
Qed.
End Machine.
End VMSwapRemoveTrace.
