(******************************************************************************)
(* Thread replay by removing and reinserting one foreign TLBI                  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemoveLocal
  PromiseFirstSailVMSwapRemoveOutcome PromiseFirstSailVMSwapRemoveCertification
  PromiseFirstSailVMSwapInsertCertification PromiseFirstSailVMSwapRemoveDelivery
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapSim.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapBridge.
Import VMPromising VMSwapLookup VMSwapSim.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Section Bridge.
Context (before after : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation Remove := (VMSwapRemoveLocal.related before tlbi rc epoch).
Local Notation Insert := (VMSwapInsert.pp_rel after tlbi rc epoch).

Definition related a b := ∃ mid, Remove a mid ∧ Insert mid b ∧ VMViews.ok mid.
Definition terminal_related a b := ∃ mid, Remove a mid ∧ Insert mid b.

Definition thread_related (mem : Memory.t) a b := ∃ mid,
  VMSwapRemoveRun.ts_rel before a mid ∧ b = ts_map (shift (S (length after))) mid ∧
  ts_pos mid ∧ VMViews.ts_ok (length mem) mid.

Lemma thread_pc mem a b : thread_related mem a b → TState.pc b = TState.pc a.
Proof.
  intros [mid [[Hshape Hcache] [-> Hrest]]]. rewrite ts_map_pc, Hshape.
  change (TState.pc (ts_map (unshift (S (length before))) a) = TState.pc a). apply ts_map_pc.
Qed.

Lemma thread_regs mem a b : thread_related mem a b → TState.reg_map b = TState.reg_map a.
Proof.
  intros [mid [[Hshape Hcache] [-> Hrest]]]. rewrite ts_map_reg_map, Hshape.
  change (TState.reg_map (ts_map (unshift (S (length before))) a) = TState.reg_map a).
  apply ts_map_reg_map.
Qed.

Lemma thread_init l1 l2 a b : l1 ++ before = l2 ++ after →
  thread_related (l1 ++ before) a b →
  related (PPState.Make a (l1 ++ Ev.Tlbi tlbi rc epoch :: before) IIS.init)
    (PPState.Make b (l2 ++ Ev.Tlbi tlbi rc epoch :: after) IIS.init).
Proof.
  intros Hmem [mid [Hr [Hi [Hp Hb]]]].
  exists (PPState.Make mid (l1 ++ before) IIS.init). split.
  - split; [exists l1; split; reflexivity|]. split; [exact Hr|].
    symmetry. apply VMSwapRemoveDelivery.iis_init.
  - split.
    + split; [exists l2; split; [exact Hmem|reflexivity]|]. split; [exact Hi|].
      split; [apply iis_rel_init; lia|exact Hp].
    + split; [exact Hb|]. eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. cbn; lia.
Qed.

Lemma related_thread l a b : related a b →
  PPState.mem a = l ++ Ev.Tlbi tlbi rc epoch :: before →
  thread_related (l ++ before) (PPState.state a) (PPState.state b).
Proof.
  intros [mid [Hr [Hi Hb]]] Hmem.
  pose proof (VMSwapRemoveOutcome.short_mem before tlbi rc epoch l a mid Hr Hmem) as Hshort.
  exists (PPState.state mid). split; [apply Hr|]. split; [apply Hi|].
  split; [apply Hi|]. rewrite <- Hshort. apply Hb.
Qed.

Lemma related_memory l1 l2 a b : l1 ++ before = l2 ++ after → related a b →
  PPState.mem a = l1 ++ Ev.Tlbi tlbi rc epoch :: before →
  PPState.mem b = l2 ++ Ev.Tlbi tlbi rc epoch :: after.
Proof.
  intros Hmem [mid [Hr [Hi Hbounds]]] Ha.
  destruct Hi as [[prefix [Hm Hb]] Hrest].
  pose proof (VMSwapRemoveOutcome.short_mem before tlbi rc epoch l1 a mid Hr Ha) as Hshort.
  assert (Hprefix : prefix = l2).
  { apply (app_inv_tail after prefix l2). rewrite <- Hm, Hshort. exact Hmem. }
  subst prefix. exact Hb.
Qed.

Theorem emit_sim tid imem l1 l2 ev a b a' : l1 ++ before = l2 ++ after →
  thread_related (l1 ++ before) a b →
  VMSwapRemoveRun.ts_inv imem before tlbi rc epoch l1 a →
  TState.emit_promise tid imem (ev :: l1 ++ Ev.Tlbi tlbi rc epoch :: before) ev a = Ok a' →
  ∃ b', TState.emit_promise tid imem (ev :: l2 ++ Ev.Tlbi tlbi rc epoch :: after) ev b = Ok b' ∧
    thread_related (ev :: l1 ++ before) a' b' ∧
    VMSwapRemoveRun.ts_inv imem before tlbi rc epoch (ev :: l1) a'.
Proof.
  intros Hmem [mid [Hr [-> [Hp Hb]]]] Hinv Hrun.
  destruct (VMSwapRemoveDelivery.emit_remove imem before tlbi rc epoch tid l1 ev a mid a'
    Hr Hinv Hrun) as [mid' [Hmid [Hr' Hinv']]].
  exists (ts_map (shift (S (length after))) mid'). split.
  - rewrite emit_promise_shifted, <- Hmem, Hmid. reflexivity.
  - split; [|exact Hinv']. exists mid'. split; [exact Hr'|]. split; [reflexivity|].
    split.
    + eapply emit_promise_pos; [|exact Hp|exact Hmid]. cbn; lia.
    + eapply VMViews.emit_promise; [|exact Hb|exact Hmid]. cbn; lia.
Qed.

Theorem broadcast_sim {n} (owner : fin n) tid imem l1 l2 extra a b a' : tid ≠ owner →
  l1 ++ before = l2 ++ after → thread_related (l1 ++ before) a b →
  VMSwapRemoveRun.ts_inv imem before tlbi rc epoch l1 a →
  VMSwapInsert.bcast_thread owner imem (l1 ++ Ev.Tlbi tlbi rc epoch :: before) extra tid a = Ok a' →
  ∃ b', VMSwapInsert.bcast_thread owner imem (l2 ++ Ev.Tlbi tlbi rc epoch :: after) extra tid b = Ok b' ∧
    thread_related (extra ++ l1 ++ before) a' b' ∧
    VMSwapRemoveRun.ts_inv imem before tlbi rc epoch (extra ++ l1) a'.
Proof.
  intros Hne Hmem Hrel Hinv. revert a' b Hrel.
  induction extra as [|ev older IH]; intros a' b Hrel Hrun.
  - injection Hrun as <-. exists b. split; [reflexivity|split; assumption].
  - cbn [VMSwapInsert.bcast_thread] in Hrun |- *.
    destruct (VMSwapInsert.bcast_thread owner imem (l1 ++ Ev.Tlbi tlbi rc epoch :: before) older tid a)
      as [mid|err] eqn:Hmid; [|discriminate].
    destruct (IH mid b Hrel eq_refl) as [mid' [Hmid' [Hrel' Hinv']]].
    rewrite Hmid'. cbn [mbind result_bind] in Hrun |- *.
    rewrite decide_False in Hrun |- * by exact Hne.
    cbn [app]. rewrite !app_assoc in Hrun, Hrel' |- *.
    assert (Hmem' : (older ++ l1) ++ before = (older ++ l2) ++ after)
      by (rewrite <- !app_assoc, Hmem; reflexivity).
    pose proof (emit_sim tid imem (older ++ l1) (older ++ l2) ev mid mid' a'
      Hmem' Hrel' Hinv' Hrun) as Hresult.
    destruct Hresult as [b' [Hb [Hr' Hi']]]. exists b'. split; [exact Hb|]. split; [|exact Hi'].
    assert (E : (older ++ l1) ++ before = older ++ (l1 ++ before)) by (symmetry; apply app_assoc).
    rewrite E in Hr'. exact Hr'.
Qed.

Theorem instruction_sim n (tid : fin n) imem {A} (mon : iMon A) a b :
  fin_to_nat tid ≠ rc → related a b → VMSwapRemoveOutcome.ok imem before tlbi rc epoch a →
  (∀ a' value, Exec.elem_of_results (a', value) (cinterp (run_outcome' n tid imem) mon a) →
    ∃ b', Exec.elem_of_results (b', value) (cinterp (run_outcome' n tid imem) mon b) ∧
      related a' b' ∧ VMSwapRemoveOutcome.ok imem before tlbi rc epoch a') ∧
  (∀ a' err, (a', err) ∈ Exec.errors (cinterp (run_outcome' n tid imem) mon a) →
    ∃ b' err', (b', err') ∈ Exec.errors (cinterp (run_outcome' n tid imem) mon b) ∧
      terminal_related a' b').
Proof.
  intros Hrc [mid [Hremove [Hinsert Hbounds]]] Hok.
  destruct (VMSwapRemoveOutcome.instruction_remove_sim imem before tlbi rc epoch n tid mon
    a mid Hrc Hremove Hok) as [Hr He].
  destruct (VMSwapInsert.instruction_insert_sim after tlbi rc epoch n tid imem Hrc mon
    mid b Hinsert Hbounds) as [Hr' He']. split.
  - intros a' value Hrun. destruct (Hr a' value Hrun) as [mid' [Hmid [Hremove' Hok']]].
    destruct (Hr' mid' value Hmid) as [b' [Hb Hinsert']].
    exists b'. split; [exact Hb|]. split; [|exact Hok'].
    exists mid'. split; [exact Hremove'|]. split; [exact Hinsert'|].
    eapply VMViews.instruction_ok; eassumption.
  - intros a' err Hrun. destruct (He a' err Hrun) as [mid' [err' [Hmid Hremove']]].
    destruct (He' mid' err' Hmid) as [b' [err'' [Hb Hinsert']]].
    exists b', err''. split; [exact Hb|]. exists mid'. auto.
Qed.

Theorem enum_raw_promises_sim bbm {n} (isem : iMon ()) (term : terminationCondition n)
    (tid : fin n) imem fuel ts1 tsm ts2 mem1 memm mem2 ev :
  fin_to_nat tid ≠ rc →
  Remove (PPState.Make ts1 mem1 IIS.init) (PPState.Make tsm memm IIS.init) →
  Insert (PPState.Make tsm memm IIS.init) (PPState.Make ts2 mem2 IIS.init) →
  VMViews.ok (PPState.Make tsm memm IIS.init) →
  VMSwapRemoveOutcome.ok imem before tlbi rc epoch (PPState.Make ts1 mem1 IIS.init) →
  ev ∈ CPState.promises (VMPromising bbm)
    (CPState.enumerate_results isem (VMPromising bbm) term tid imem fuel ts1 mem1) →
  ev ∈ CPState.promises (VMPromising bbm)
    (CPState.enumerate_results isem (VMPromising bbm) term tid imem fuel ts2 mem2).
Proof.
  intros Hrc Hr Hi Hb Hok Hcandidate.
  eapply VMSwapInsertCertification.enum_raw_promises_sim;
    [exact Hrc|exact Hi|exact Hb|].
  eapply VMSwapRemoveCertification.enum_raw_promises_sim; eassumption.
Qed.

Theorem instruction_thread_sim n (tid : fin n) imem {A} (mon : iMon A) l1 l2 a b a' mem' iis value :
  fin_to_nat tid ≠ rc → l1 ++ before = l2 ++ after → thread_related (l1 ++ before) a b →
  VMSwapRemoveOutcome.ok imem before tlbi rc epoch
    (PPState.Make a (l1 ++ Ev.Tlbi tlbi rc epoch :: before) IIS.init) →
  Exec.elem_of_results (PPState.Make a' mem' iis, value)
    (cinterp (run_outcome' n tid imem) mon
      (PPState.Make a (l1 ++ Ev.Tlbi tlbi rc epoch :: before) IIS.init)) →
  ∃ extra b' iis', mem' = extra ++ l1 ++ Ev.Tlbi tlbi rc epoch :: before ∧
    Exec.elem_of_results (PPState.Make b' (extra ++ l2 ++ Ev.Tlbi tlbi rc epoch :: after) iis', value)
      (cinterp (run_outcome' n tid imem) mon
        (PPState.Make b (l2 ++ Ev.Tlbi tlbi rc epoch :: after) IIS.init)) ∧
    thread_related (extra ++ l1 ++ before) a' b' ∧
    VMSwapRemoveOutcome.ok imem before tlbi rc epoch (PPState.Make a' mem' iis).
Proof.
  intros Hrc Hmem Hrel Hok Hrun.
  destruct (proj1 (instruction_sim n tid imem mon _ _ Hrc (thread_init l1 l2 a b Hmem Hrel) Hok)
    _ value Hrun) as [[b' mb iis'] [Hrun' [Hrel' Hok']]].
  assert (Hbounds : VMViews.ok (PPState.Make a (l1 ++ Ev.Tlbi tlbi rc epoch :: before) IIS.init))
    by apply Hok.
  destruct (VMViews.instruction_ok n tid imem mon _ _ value Hbounds Hrun) as [_ [extra Hextra]].
  cbn in Hextra. exists extra, b', iis'. split; [exact Hextra|].
  assert (Hmem' : (extra ++ l1) ++ before = (extra ++ l2) ++ after)
    by (rewrite <- !app_assoc, Hmem; reflexivity).
  assert (Ha : PPState.mem (PPState.Make a' mem' iis) = (extra ++ l1) ++ Ev.Tlbi tlbi rc epoch :: before)
    by (cbn; rewrite Hextra, app_assoc; reflexivity).
  pose proof (related_memory (extra ++ l1) (extra ++ l2) _ _ Hmem' Hrel' Ha) as Hb.
  cbn in Hb. rewrite <- app_assoc in Hb. subst mb. split; [exact Hrun'|].
  split; [|exact Hok']. rewrite app_assoc. exact (related_thread (extra ++ l1) _ _ Hrel' Ha).
Qed.
End Bridge.
End VMSwapBridge.
