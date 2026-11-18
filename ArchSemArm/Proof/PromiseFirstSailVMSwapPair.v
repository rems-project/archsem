(******************************************************************************)
(* Initialize machine replay from two certified disjoint TLBI promises        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstSailVMViews
  PromiseFirstSailVMOwnership PromiseFirstSailVMNormalization PromiseFirstSailVMSwap
  PromiseFirstSailVMSwapMachineBridge PromiseFirstSailVMSwapInitial
  PromiseFirstSailVMSwapRemoveInit PromiseFirstSailVMSwapRemoveTrace
  PromiseFirstSailVMSwapRemoveMachine PromiseFirstSailVMSwapRemoveCertification
  PromiseFirstSailVMSwapInsertCertification PromiseFirstSailVMSwapMaterialize
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMInstructionReplay PromiseFirstSailVMSwapPos.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapPair.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma emit_tlbi_total tid imem mem tlbi rc epoch ts : VMSwapMaterialize.valid ts →
  ∃ ts', TState.emit_promise tid imem mem (Ev.Tlbi tlbi rc epoch) ts = Ok ts'.
Proof.
  intro Hv. unfold TState.emit_promise.
  destruct (bool_decide (Ev.tid (Ev.Tlbi tlbi rc epoch) = tid)).
  - apply VMSwapMaterialize.process_tlbi_total. intros c Hc. apply Hv. exact Hc.
  - apply VMSwapMaterialize.process_tlbi_total, Hv.
Qed.

Section Machine.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation RawCandidate := (VMNormalization.RawCandidate bbm nondet term).
Local Notation RawStep := (VMNormalization.RawStep bbm nondet term).
Local Notation ok := (VMSwapRemoveInit.state_ok).

Lemma promise_tlbi_total tlbi rc epoch (st : state) : VMViews.state_ok st →
  ∃ st', PState.promise prom (Ev.Tlbi tlbi rc epoch) st = Ok st'.
Proof.
  intro Hok.
  assert (Hall : ∀ tid : fin n, ∃ ts', TState.emit_promise tid (PState.initmem st)
      (Ev.Tlbi tlbi rc epoch :: PState.events st) (Ev.Tlbi tlbi rc epoch)
      (PState.tstate tid st) = Ok ts').
  { intro tid. apply emit_tlbi_total. intros c Hc. exact (proj2 (proj2 (VMViews.ok_cache _ _ (Hok tid) c Hc))). }
  set (states := fun_to_vec (λ tid,
    match TState.emit_promise tid (PState.initmem st) (Ev.Tlbi tlbi rc epoch :: PState.events st)
        (Ev.Tlbi tlbi rc epoch) (PState.tstate tid st) with
    | Ok ts' => ts' | Error _ => PState.tstate tid st end)).
  exists (PState.Make states (PState.initmem st) (Ev.Tlbi tlbi rc epoch :: PState.events st)).
  change ((nts ←@{result string} vimapM
    (λ tid ts, TState.emit_promise tid (PState.initmem st) (Ev.Tlbi tlbi rc epoch :: PState.events st)
      (Ev.Tlbi tlbi rc epoch) ts) (PState.tstates st);
    Ok (PState.Make nts (PState.initmem st) (Ev.Tlbi tlbi rc epoch :: PState.events st))) =
    Ok (PState.Make states (PState.initmem st) (Ev.Tlbi tlbi rc epoch :: PState.events st))).
  rewrite (VMNormalization.vimapM_intro _ _ states); [reflexivity|].
  intro tid. change (TState.emit_promise tid (PState.initmem st)
    (Ev.Tlbi tlbi rc epoch :: PState.events st) (Ev.Tlbi tlbi rc epoch)
    (PState.tstate tid st) = Ok (states !!! tid)).
  unfold states. rewrite lookup_fun_to_vec. destruct (Hall tid) as [ts' ->]. reflexivity.
Qed.

Lemma candidate_owner st tid fuel ev : RawCandidate st tid fuel ev → Ev.tid ev = fin_to_nat tid.
Proof. apply VMCollectedOwnership.raw_promise_owner. Qed.

Lemma candidate_remove_foreign st st' tid fuel ev tlbi rc epoch :
  fin_to_nat tid ≠ rc → fin_to_nat tid ≠ TLBI.tid tlbi → ok st →
  PState.promise prom (Ev.Tlbi tlbi rc epoch) st = Ok st' →
  RawCandidate st' tid fuel ev → RawCandidate st tid fuel ev.
Proof.
  intros Hrc Hissuer Hok Hrun Hcand.
  destruct (VMSwapRemoveInit.promise_foreign_initial bbm tid tlbi rc epoch st st'
    Hrc Hissuer Hok Hrun) as [Hr Hentry].
  destruct (PromiseFirstCurrent.promise_success prom _ _ _ Hrun) as [Himem _].
  unfold VMNormalization.RawCandidate in *. rewrite Himem in Hcand.
  eapply (VMSwapRemoveCertification.enum_raw_promises_sim (PState.events st) tlbi rc epoch
    bbm (sail_tiny_arm_sem nondet) term tid (PState.initmem st) fuel
    (PState.tstate tid st') (PState.tstate tid st) (PState.events st') (PState.events st) ev);
    [exact Hrc|exact Hr|exact Hentry|exact Hcand].
Qed.

Lemma candidate_insert_foreign st st' tid fuel ev tlbi rc epoch :
  fin_to_nat tid ≠ rc → fin_to_nat tid ≠ TLBI.tid tlbi → ok st →
  PState.promise prom (Ev.Tlbi tlbi rc epoch) st = Ok st' →
  RawCandidate st tid fuel ev → RawCandidate st' tid fuel ev.
Proof.
  intros Hrc Hissuer Hok Hrun Hcand.
  destruct (PromiseFirstCurrent.promise_success prom _ _ _ Hrun) as [Himem [Hmem Hemit]].
  assert (Hbounds : VMViews.state_ok st) by apply Hok.
  assert (Hroots : VMRoots.state_roots st) by apply Hok.
  assert (Hpos : VMSwapPos.state_pos st) by apply Hok.
  eapply (VMSwapInsertCertification.raw_candidate_sim (PState.events st) tlbi rc epoch
    bbm nondet term tid st st' [] fuel ev); [exact Hrc|symmetry; exact Himem|reflexivity|exact Hmem| |apply Hpos|apply Hbounds|exact Hcand].
  specialize (Hemit tid). change (TState.emit_promise tid (PState.initmem st)
    (Ev.Tlbi tlbi rc epoch :: PState.events st) (Ev.Tlbi tlbi rc epoch)
    (PState.tstate tid st) = Ok (PState.tstate tid st')) in Hemit.
  rewrite VMSwapRemoveMachine.emit_foreign in Hemit by assumption. injection Hemit as <-.
  symmetry. apply VMSwapInitial.shift_initial; [apply Hbounds|apply Hroots].
Qed.

Theorem raw_pair_swap e1 e2 st one long : ok st → Ev.out_of_order e1 e2 = true →
  RawStep e1 st one → RawStep e2 one long →
  ∃ short swapped, RawStep e2 st short ∧ RawStep e1 short swapped.
Proof.
  intros Hok Horder [(tid1 & fuel1 & Hc1) Hp1] [(tid2 & fuel2 & Hc2) Hp2].
  pose proof (candidate_owner _ _ _ _ Hc1) as Hown1.
  pose proof (candidate_owner _ _ _ _ Hc2) as Hown2.
  destruct (VMSwap.out_of_order_inv e1 e2 Horder)
    as (t1 & r1 & k1 & t2 & r2 & k2 & -> & -> & Hlt & Hne & Hnr2 & Hnr1).
  cbn in Hown1, Hown2.
  assert (Hb : VMViews.state_ok st) by apply Hok.
  destruct (promise_tlbi_total t2 r2 k2 st Hb) as [short Hshort].
  assert (Hshortok : ok short) by (eapply VMSwapRemoveInit.promise_ok; eassumption).
  assert (Hbs : VMViews.state_ok short) by apply Hshortok.
  destruct (promise_tlbi_total t1 r1 k1 short Hbs) as [swapped Hswapped].
  exists short, swapped. split; split; try assumption.
  - exists tid2, fuel2. eapply (candidate_remove_foreign st one tid2 fuel2 (Ev.Tlbi t2 r2 k2) t1 r1 k1);
      [congruence|congruence|exact Hok|exact Hp1|exact Hc2].
  - exists tid1, fuel1. eapply (candidate_insert_foreign st short tid1 fuel1 (Ev.Tlbi t1 r1 k1) t2 r2 k2);
      [congruence|congruence|exact Hok|exact Hshort|exact Hc1].
Qed.

Theorem pair_related e1 e2 (st one long short swapped : state) : ok st → Ev.out_of_order e1 e2 = true →
  PState.promise prom e1 st = Ok one → PState.promise prom e2 one = Ok long →
  PState.promise prom e2 st = Ok short → PState.promise prom e1 short = Ok swapped →
  VMSwapMachineBridge.related long swapped.
Proof.
  intros Hok Horder Hp1 Hp2 Hp3 Hp4.
  pose proof (VMSwap.out_of_order_disjoint e1 e2) as Hdisjoint.
  destruct (VMSwap.out_of_order_inv e1 e2 Horder)
    as (t1 & r1 & k1 & t2 & r2 & k2 & -> & -> & Hlt & Hne & Hnr2 & Hnr1).
  destruct (PromiseFirstCurrent.promise_success prom _ _ _ Hp1) as [Hi1 [Hm1 He1]].
  destruct (PromiseFirstCurrent.promise_success prom _ _ _ Hp2) as [Hi2 [Hm2 He2]].
  destruct (PromiseFirstCurrent.promise_success prom _ _ _ Hp3) as [Hi3 [Hm3 He3]].
  destruct (PromiseFirstCurrent.promise_success prom _ _ _ Hp4) as [Hi4 [Hm4 He4]].
  rewrite Hi1, Hm1 in He2. rewrite Hi3, Hm3 in He4.
  assert (Hb : VMViews.state_ok st) by apply Hok.
  assert (Hr : VMRoots.state_roots st) by apply Hok.
  assert (Ht : VMSwapPos.state_pos st) by apply Hok.
  assert (Hone : ok one) by (eapply VMSwapRemoveInit.promise_ok; eassumption).
  split; [rewrite Hi2, Hi1, Hi4, Hi3; reflexivity|].
  split; [rewrite Hm2, Hm1, Hm4, Hm3; reflexivity|].
  split; [rewrite Hm2, Hm1, Hm4, Hm3; reflexivity|].
  intro tid. destruct (Hdisjoint tid Horder) as [Hforeign|Hforeign].
  - apply bool_decide_eq_false in Hforeign.
    assert (Hrc : fin_to_nat tid ≠ r1) by tauto.
    assert (Hissuer : fin_to_nat tid ≠ TLBI.tid t1) by tauto.
    exists (PState.events st), (Ev.Tlbi t2 r2 k2 :: PState.events st), t1, r1, k1,
      [Ev.Tlbi t2 r2 k2], [].
    split; [exact Hrc|]. split; [reflexivity|].
    split; [rewrite Hm2, Hm1; reflexivity|]. split; [rewrite Hm4, Hm3; reflexivity|]. split.
    + eapply VMSwapInitial.older_initial;
        [exact Hrc|exact Hissuer|apply Hb|apply Hr|apply Ht|apply He1|apply He2|apply He3|apply He4].
    + eapply VMSwapRemoveTrace.promise_ok; [|exact Hp2].
      eapply VMSwapRemoveTrace.initial; [exact Hrc|reflexivity|exact Hissuer|exact Hok|exact Hp1].
  - apply bool_decide_eq_false in Hforeign.
    assert (Hrc : fin_to_nat tid ≠ r2) by tauto.
    assert (Hissuer : fin_to_nat tid ≠ TLBI.tid t2) by tauto.
    exists (Ev.Tlbi t1 r1 k1 :: PState.events st), (PState.events st), t2, r2, k2,
      [], [Ev.Tlbi t1 r1 k1].
    split; [exact Hrc|]. split; [reflexivity|].
    split; [rewrite Hm2, Hm1; reflexivity|]. split; [rewrite Hm4, Hm3; reflexivity|]. split.
    + eapply VMSwapInitial.newer_initial;
        [exact Hrc|exact Hissuer|apply Hb|apply Hr|apply Ht|apply He1|apply He2|apply He3|apply He4].
    + eapply VMSwapRemoveTrace.initial; [exact Hrc|exact Hm1|exact Hissuer|exact Hone|exact Hp2].
Qed.

Theorem raw_pair_related e1 e2 st one long : ok st → Ev.out_of_order e1 e2 = true →
  RawStep e1 st one → RawStep e2 one long →
  ∃ short swapped, RawStep e2 st short ∧ RawStep e1 short swapped ∧
    VMSwapMachineBridge.related long swapped.
Proof.
  intros Hok Horder Hfirst Hsecond.
  destruct (raw_pair_swap e1 e2 st one long Hok Horder Hfirst Hsecond)
    as (short & swapped & Hthird & Hfourth).
  exists short, swapped. split; [exact Hthird|]. split; [exact Hfourth|].
  eapply pair_related; [exact Hok|exact Horder|apply Hfirst|apply Hsecond|apply Hthird|apply Hfourth].
Qed.
Corollary raw_pair_continuation e1 e2 st one long final : ok st → Ev.out_of_order e1 e2 = true →
  RawStep e1 st one → RawStep e2 one long → rtc (VMNormalization.Mixed bbm nondet term) long final →
  ∃ short swapped final', RawStep e2 st short ∧ RawStep e1 short swapped ∧
    rtc (VMNormalization.Mixed bbm nondet term) swapped final' ∧
    VMSwapMachineBridge.related final final' ∧
    PState.to_archState prom final = PState.to_archState prom final' ∧
    length (PState.events final) = length (PState.events final').
Proof.
  intros Hok Horder Hfirst Hsecond Hcont.
  destruct (raw_pair_related e1 e2 st one long Hok Horder Hfirst Hsecond)
    as (short & swapped & Hthird & Hfourth & Hrel).
  destruct (VMSwapMachineBridge.mixed_rtc_sim bbm nondet term long swapped final Hrel Hcont)
    as [final' [Hcont' Hrel']].
  exists short, swapped, final'. split; [exact Hthird|]. split; [exact Hfourth|].
  split; [exact Hcont'|]. split; [exact Hrel'|]. split.
  - apply VMSwapMachineBridge.architectural_state, Hrel'.
  - apply Hrel'.
Qed.
End Machine.
End VMSwapPair.
