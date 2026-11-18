(******************************************************************************)
(* Replay machine steps across a per-thread foreign TLBI bridge               *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstFreshBroadcast
  PromiseFirstSailVMViews PromiseFirstSailVMSwapBridge PromiseFirstSailVMSwapRemoveTrace
  PromiseFirstSailVMSwapRemoveCore PromiseFirstSailVMSwapRemoveOutcome
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapInsert PromiseFirstSailVMNormalization
  PromiseFirstSailVMSwap PromiseFirstSailVMSwapRemoveDelivery.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapMachineBridge.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.
Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

(** Each thread may remove a different foreign event to relate the two
    histories. The event and its two positions remain fixed as execution
    appends a common prefix. *)
Definition thread_link (tid : fin n) (a : state) mem b :=
  ∃ before after tlbi rc epoch l1 l2,
    fin_to_nat tid ≠ rc ∧ l1 ++ before = l2 ++ after ∧
    PState.events a = l1 ++ Ev.Tlbi tlbi rc epoch :: before ∧
    mem = l2 ++ Ev.Tlbi tlbi rc epoch :: after ∧
    VMSwapBridge.thread_related before after (l1 ++ before) (PState.tstate tid a) b ∧
    VMSwapRemoveTrace.ok tid before tlbi rc epoch a.
Definition related (a b : state) :=
  PState.initmem a = PState.initmem b ∧
  length (PState.events a) = length (PState.events b) ∧
  map Ev.get_msg (PState.events a) = map Ev.get_msg (PState.events b) ∧
  ∀ tid, thread_link tid a (PState.events b) (PState.tstate tid b).

Lemma link_pc tid a mem b : thread_link tid a mem b → TState.pc b = TState.pc (PState.tstate tid a).
Proof.
  intros (before & after & tlbi & rc & epoch & l1 & l2 & Hrc & Heq & Ha & Hb & Hr & Hok).
  eapply VMSwapBridge.thread_pc; exact Hr.
Qed.
Lemma link_regs tid a mem b : thread_link tid a mem b →
  TState.reg_map b = TState.reg_map (PState.tstate tid a).
Proof.
  intros (before & after & tlbi & rc & epoch & l1 & l2 & Hrc & Heq & Ha & Hb & Hr & Hok).
  eapply VMSwapBridge.thread_regs; exact Hr.
Qed.
Lemma architectural_state a b : related a b → PState.to_archState prom a = PState.to_archState prom b.
Proof.
  intros [Himem [Hlen [Hmsgs Hlinks]]]. unfold PState.to_archState. cbn.
  f_equal.
  - rewrite Himem. apply VMSwap.to_memMap_msgs, Hmsgs.
  - apply vec_eq. intro tid. rewrite !vlookup_map.
    symmetry. apply (link_regs tid a (PState.events b) (PState.tstate tid b)), Hlinks.
Qed.
Lemma removal_inv (tid : fin n) before tlbi rc epoch l (a : state) :
  PState.events a = l ++ Ev.Tlbi tlbi rc epoch :: before →
  VMSwapRemoveTrace.ok tid before tlbi rc epoch a →
  VMSwapRemoveRun.ts_inv (PState.initmem a) before tlbi rc epoch l (PState.tstate tid a).
Proof.
  intros Hmem [_ [_ [l' [Hmem' Hcore]]]].
  assert (E : l' = l) by (apply (app_inv_tail (Ev.Tlbi tlbi rc epoch :: before)); congruence).
  subst l'. apply Hcore.
Qed.

Lemma link_emit tid a a' mem b ev : thread_link tid a mem b →
  PState.promise prom ev a = Ok a' →
  ∃ b', TState.emit_promise tid (PState.initmem a) (ev :: mem) ev b = Ok b' ∧
    thread_link tid a' (ev :: mem) b'.
Proof.
  intros (before & after & tlbi & rc & epoch & l1 & l2 & Hrc & Heq & Ha & Hb & Hr & Hok) Hrun.
  destruct (PromiseFirstCurrent.promise_success prom ev a a' Hrun) as [Himem [Hmem Hemit]].
  specialize (Hemit tid). change (TState.emit_promise tid (PState.initmem a)
    (ev :: PState.events a) ev (PState.tstate tid a) = Ok (PState.tstate tid a')) in Hemit.
  rewrite Ha in Hemit. destruct (VMSwapBridge.emit_sim before after tlbi rc epoch tid
    (PState.initmem a) l1 l2 ev _ _ _ Heq Hr (removal_inv tid before tlbi rc epoch l1 a Ha Hok) Hemit)
    as [b' [Hemit' [Hr' Hinv']]].
  exists b'. split; [rewrite Hb; exact Hemit'|].
  exists before, after, tlbi, rc, epoch, (ev :: l1), (ev :: l2).
  split; [exact Hrc|]. split; [cbn; rewrite Heq; reflexivity|].
  split; [cbn; rewrite Hmem, Ha; reflexivity|]. split; [cbn; rewrite Hb; reflexivity|].
  split; [exact Hr'|]. eapply VMSwapRemoveTrace.promise_ok; eassumption.
Qed.

Theorem promise_sim ev a b a' : related a b → PState.promise prom ev a = Ok a' →
  ∃ b', PState.promise prom ev b = Ok b' ∧ related a' b'.
Proof.
  intros [Himem [Hlen [Hmsgs Hlinks]]] Hrun.
  pose proof (λ tid, link_emit tid a a' (PState.events b) (PState.tstate tid b) ev (Hlinks tid) Hrun) as Hall.
  set (states := fun_to_vec (λ tid,
    match TState.emit_promise tid (PState.initmem a) (ev :: PState.events b) ev (PState.tstate tid b) with
    | Ok ts => ts | Error _ => PState.tstate tid b end)).
  assert (Hstates : ∀ tid : fin n, TState.emit_promise tid (PState.initmem a)
      (ev :: PState.events b) ev (PState.tstate tid b) = Ok (states !!! tid) ∧
      thread_link tid a' (ev :: PState.events b) (states !!! tid)).
  { intro tid. unfold states. rewrite lookup_fun_to_vec.
    destruct (Hall tid) as [ts [-> Hlink]]. auto. }
  exists (PState.Make states (PState.initmem b) (ev :: PState.events b)). split.
  - change ((nts ←@{result string} vimapM
      (λ tid ts, TState.emit_promise tid (PState.initmem b) (ev :: PState.events b) ev ts)
      (PState.tstates b);
      Ok (PState.Make nts (PState.initmem b) (ev :: PState.events b))) =
      Ok (PState.Make states (PState.initmem b) (ev :: PState.events b))).
    rewrite <- Himem.
    assert (E : vimapM (λ tid ts, TState.emit_promise tid (PState.initmem a)
      (ev :: PState.events b) ev ts) (PState.tstates b) = Ok states).
    { apply VMSwapInsert.vimapM_intro'. intro tid. apply Hstates. }
    rewrite E. reflexivity.
  - destruct (PromiseFirstCurrent.promise_success prom ev a a' Hrun) as [Hi [Hm _]].
    split; [change (PState.initmem a' = PState.initmem b); rewrite Hi; exact Himem|].
    split; [cbn; rewrite Hm; cbn; lia|].
    split; [cbn; rewrite Hm; cbn; rewrite Hmsgs; reflexivity|]. intro tid. apply Hstates.
Qed.

Theorem raw_candidate_sim nondet term tid fuel ev a b : related a b →
  VMNormalization.RawCandidate bbm nondet term a tid fuel ev →
  VMNormalization.RawCandidate bbm nondet term b tid fuel ev.
Proof.
  intros [Himem [_ [_ Hlinks]]] Hcandidate.
  destruct (Hlinks tid) as (before & after & tlbi & rc & epoch & l1 & l2 & Hrc & Heq & Ha & Hb & Hr & Hok).
  pose proof (VMSwapBridge.thread_init before after tlbi rc epoch l1 l2 _ _ Heq Hr)
    as [mid [Hremove [Hinsert Hbound]]].
  pose proof (VMSwapRemoveTrace.pp_ok tid before tlbi rc epoch a Hok) as Hentry.
  unfold VMNormalization.RawCandidate in *. rewrite <- Himem, Hb. rewrite Ha in Hcandidate, Hentry.
  destruct mid as [tsm memm iis].
  assert (Ei : iis = IIS.init).
  { destruct Hremove as [_ [_ Hii]]. cbn in Hii.
    rewrite VMSwapRemoveDelivery.iis_init in Hii. exact Hii. }
  subst iis. eapply VMSwapBridge.enum_raw_promises_sim; eassumption.
Qed.

Theorem raw_step_sim nondet term ev a b a' : related a b →
  VMNormalization.RawStep bbm nondet term ev a a' →
  ∃ b', VMNormalization.RawStep bbm nondet term ev b b' ∧ related a' b'.
Proof.
  intros Hr [[tid [fuel Hcandidate]] Hrun].
  destruct (promise_sim ev a b a' Hr Hrun) as [b' [Hrun' Hr']].
  exists b'. split; [split|exact Hr'].
  - exists tid, fuel. eapply raw_candidate_sim; eassumption.
  - exact Hrun'.
Qed.

Lemma link_broadcast isem owner tid a a' extra mem b : tid ≠ owner →
  thread_link tid a mem b → PState.events a' = extra ++ PState.events a →
  Exec.elem_of_results (a', ()) (PState.run_tid isem prom owner a) →
  VMSwapInsert.bcast_thread owner (PState.initmem a) (PState.events a) extra tid
    (PState.tstate tid a) = Ok (PState.tstate tid a') →
  ∃ b', VMSwapInsert.bcast_thread owner (PState.initmem a) mem extra tid b = Ok b' ∧
    thread_link tid a' (extra ++ mem) b'.
Proof.
  intros Hne (before & after & tlbi & rc & epoch & l1 & l2 & Hrc & Heq & Ha & Hb & Hr & Hok)
    Hmem Hrun Hbroadcast.
  rewrite Ha in Hbroadcast.
  destruct (VMSwapBridge.broadcast_sim before after tlbi rc epoch owner tid
    (PState.initmem a) l1 l2 extra _ _ _ Hne Heq Hr
    (removal_inv tid before tlbi rc epoch l1 a Ha Hok) Hbroadcast)
    as [b' [Hbroadcast' [Hr' Hinv']]].
  exists b'. split; [rewrite Hb; exact Hbroadcast'|].
  exists before, after, tlbi, rc, epoch, (extra ++ l1), (extra ++ l2).
  split; [exact Hrc|]. split; [rewrite <- !app_assoc, Heq; reflexivity|].
  split; [rewrite Hmem, Ha, app_assoc; reflexivity|].
  split; [rewrite Hb, app_assoc; reflexivity|].
  split; [rewrite <- app_assoc; exact Hr'|]. eapply VMSwapRemoveTrace.run_tid_ok; eassumption.
Qed.

Theorem instruction_sim isem owner a b a' : related a b →
  Exec.elem_of_results (a', ()) (PState.run_tid isem prom owner a) →
  ∃ b', Exec.elem_of_results (b', ()) (PState.run_tid isem prom owner b) ∧ related a' b'.
Proof.
  intros [Himem [Hlen [Hmsgs Hlinks]]] Hrun.
  destruct (run_tid_broadcast_decompose prom isem owner a a' Hrun)
    as (ts & mem & iis & states & Hinst & Hbroadcast & Hfinal).
  destruct (Hlinks owner)
    as (before & after & tlbi & rc & epoch & l1 & l2 & Hrc & Heq & Ha & Hb & Hr & Hok).
  pose proof (VMSwapRemoveTrace.pp_ok owner before tlbi rc epoch a Hok) as Hentry.
  rewrite Ha in Hinst, Hentry.
  destruct (VMSwapBridge.instruction_thread_sim before after tlbi rc epoch n owner
    (PState.initmem a) isem l1 l2 _ _ ts mem iis () Hrc Heq Hr Hentry Hinst)
    as (extra & ts' & iis' & Hmem & Hinst' & Hr' & Hentry').
  assert (HmemA : mem = extra ++ PState.events a) by (rewrite Ha; exact Hmem).
  assert (HmemA' : PState.events a' = extra ++ PState.events a) by (rewrite Hfinal; exact HmemA).
  assert (HinstB : Exec.elem_of_results (PPState.Make ts' (extra ++ PState.events b) iis', ())
      (cinterp (run_outcome' n owner (PState.initmem b)) isem
        (PPState.Make (PState.tstate owner b) (PState.events b) IIS.init))).
  { rewrite <- Himem, Hb. exact Hinst'. }
  rewrite HmemA, length_app, Nat.add_sub, take_app_length in Hbroadcast.
  assert (Hall : ∀ tid, ∃ value,
    VMSwapInsert.bcast_thread owner (PState.initmem b) (PState.events b) extra tid
      (vinsert owner ts' (PState.tstates b) !!! tid) = Ok value ∧
    thread_link tid a' (extra ++ PState.events b) value).
  { intro tid.
    pose proof (VMSwapInsert.broadcast_fresh_lookup bbm owner _ _ _ _ _ Hbroadcast tid) as Hlook.
    destruct (decide (tid = owner)) as [->|Hne].
    - rewrite VMSwapRemoveTrace.bcast_owner in Hlook. rewrite vlookup_insert in Hlook.
      injection Hlook as Hts.
      exists ts'. split; [rewrite vlookup_insert; apply VMSwapRemoveTrace.bcast_owner|].
      exists before, after, tlbi, rc, epoch, (extra ++ l1), (extra ++ l2).
      split; [exact Hrc|]. split; [rewrite <- !app_assoc, Heq; reflexivity|].
      split; [rewrite HmemA', Ha, app_assoc; reflexivity|].
      split; [rewrite Hb, app_assoc; reflexivity|]. split.
      + rewrite Hfinal. change (VMSwapBridge.thread_related before after ((extra ++ l1) ++ before)
          (states !!! owner) ts'). rewrite <- Hts, <- app_assoc. exact Hr'.
      + eapply VMSwapRemoveTrace.run_tid_ok; eassumption.
    - rewrite vlookup_insert_ne in Hlook |- * by congruence.
      assert (Hlook' : VMSwapInsert.bcast_thread owner (PState.initmem a) (PState.events a)
        extra tid (PState.tstate tid a) = Ok (PState.tstate tid a')).
      { rewrite Hfinal. exact Hlook. }
      rewrite <- Himem. eapply link_broadcast;
        [exact Hne|apply Hlinks|exact HmemA'|exact Hrun|exact Hlook']. }
  set (states' := fun_to_vec (λ tid,
    match VMSwapInsert.bcast_thread owner (PState.initmem b) (PState.events b) extra tid
      (vinsert owner ts' (PState.tstates b) !!! tid) with
    | Ok value => value | Error _ => PState.tstate tid b end)).
  assert (Hstates : ∀ tid,
    VMSwapInsert.bcast_thread owner (PState.initmem b) (PState.events b) extra tid
      (vinsert owner ts' (PState.tstates b) !!! tid) = Ok (states' !!! tid) ∧
    thread_link tid a' (extra ++ PState.events b) (states' !!! tid)).
  { intro tid. unfold states'. rewrite lookup_fun_to_vec. destruct (Hall tid) as [value [-> Hlink]]. auto. }
  exists (PState.Make states' (PState.initmem b) (extra ++ PState.events b)). split.
  - eapply run_tid_broadcast_intro; [exact HinstB|].
    rewrite length_app, Nat.add_sub, take_app_length.
    apply VMSwapInsert.broadcast_fresh_intro. intro tid. apply Hstates.
  - split; [rewrite Hfinal; exact Himem|]. split.
    + cbn. rewrite HmemA', !length_app, Hlen. reflexivity.
    + split; [cbn; rewrite HmemA', !map_app, Hmsgs; reflexivity|]. intro tid. apply Hstates.
Qed.

Theorem mixed_sim nondet term a b a' : related a b →
  VMNormalization.Mixed bbm nondet term a a' →
  ∃ b', VMNormalization.Mixed bbm nondet term b b' ∧ related a' b'.
Proof.
  intros Hr [(tid & Hactive & Hrun)|(ev & Hraw)].
  - destruct (instruction_sim _ tid a b a' Hr Hrun) as [b' [Hrun' Hr']].
    exists b'. split; [left; exists tid; split; [|exact Hrun']|exact Hr'].
    unfold PState.terminated_tid, PState.terminated_ts in *.
    change (pc_terminated (term !!! tid) (TState.pc (PState.tstate tid b)) = false).
    rewrite (link_pc tid a (PState.events b) (PState.tstate tid b) (proj2 (proj2 (proj2 Hr)) tid)).
    exact Hactive.
  - destruct (raw_step_sim nondet term ev a b a' Hr Hraw) as [b' [Hraw' Hr']].
    exists b'. split; [right; exists ev; exact Hraw'|exact Hr'].
Qed.
Theorem mixed_rtc_sim nondet term a b final : related a b →
  rtc (VMNormalization.Mixed bbm nondet term) a final →
  ∃ final', rtc (VMNormalization.Mixed bbm nondet term) b final' ∧ related final final'.
Proof.
  intros Hr Hsteps. revert b Hr.
  induction Hsteps as [a|a mid final Hstep Htail IH]; intros b Hr.
  - exists b. split; [constructor|exact Hr].
  - destruct (mixed_sim nondet term a b mid Hr Hstep) as [mid' [Hstep' Hr']].
    destruct (IH mid' Hr') as [final' [Htail' Hfinal]].
    exists final'. split; [econstructor; eassumption|exact Hfinal].
Qed.
End Machine.
End VMSwapMachineBridge.
