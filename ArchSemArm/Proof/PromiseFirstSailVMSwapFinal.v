(******************************************************************************)
(* Preserve final validation and architectural results across TLBI exchange  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMCacheSim
  PromiseFirstSailVMCacheState PromiseFirstSailVMCacheOrder PromiseFirstSailVMCacheRefill
  PromiseFirstSailVMCacheContext PromiseFirstSailVMBBMTransport PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapRemove PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveEvents PromiseFirstSailVMSwapRemoveHistory
  PromiseFirstSailVMSwapRemoveTrace PromiseFirstSailVMSwapBridge PromiseFirstSailVMSwapMachineBridge
  PromiseFirstSailVMSwapBBMCompress PromiseFirstSailVMSwapBBMRemove PromiseFirstSailVMSwapBBMCache
  PromiseFirstSailVMNormalization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.
Module VMSwapFinal.
Import VMPromising VMSwapSim VMSwapLookup VMSwapMachineBridge.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma cache_rows p limit bound cache : VMCacheState.cache_inv bound cache →
  VMSwapRemoveHistory.cache_ok p limit cache →
  VMSwapBBMRemove.rows
    (λ events, VMCacheOrder.ordered events ∧ Forall (VMSwapBBMCompress.no_invalid p) events) (TLB.vatlb cache).
Proof.
  intros [Hgood [Hunique Hvalid]] [Hhist Hroots] ctxt entry events Hrow.
  pose proof (VMBBMTransport.row_history cache ctxt entry events Hunique Hrow) as Hsame.
  rewrite <- Hsame. split; [apply Hgood|].
  eapply list.Forall_impl; [apply Hhist|]. intros [event time] Hallow.
  destruct event; [exact I|]. destruct Hallow as [Hne|[Hbad _]]; [exact Hne|discriminate].
Qed.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Theorem link_bbm tid (a : state) mem b : thread_link tid a mem b →
  BBM.check (PState.initmem a) (PState.events a) (PState.tstate tid a) = Ok false →
  BBM.check (PState.initmem a) mem b = Ok false.
Proof.
  intros (before & after & tlbi & rc & epoch & l1 & l2 & Hrc & Heq & Ha & Hb & Hr & Hok) Hcheck.
  destruct Hr as (mid & Hremove & -> & Hpos & Hmid).
  destruct Hok as [Hglobal [[[Hviews Hcache] Hstamps] Htail]].
  assert (Hbounds : VMViews.state_ok a) by apply Hglobal.
  unfold BBM.check in *. rewrite ts_map_tlb.
  destruct (TState.tlb (PState.tstate tid a)) as [c|] eqn:Hc.
  - destruct (VMSwapRemoveRun.ts_rel_tlb before _ _ c Hremove Hc) as [d [Hd Hsim]].
    rewrite Hd. cbn [fmap option_fmap].
    pose proof (VMViews.ok_cache _ _ (Hbounds tid) c Hc) as Hgood.
    pose proof (VMViews.ok_cache _ _ Hmid d Hd) as Hgoodmid.
    rewrite Ha in Hcheck.
    pose proof (VMSwapBBMRemove.check_tlb_remove (PState.initmem a) l1 before
      (Ev.Tlbi tlbi rc epoch) _ c eq_refl (cache_rows _ _ _ _ Hgood (Hcache c Hc)) Hcheck) as Hremoved.
    assert (Hmidcheck : BBM.check_tlb (PState.initmem a) (l1 ++ before)
      (elements (dom (PState.initmem a))) d = Ok false).
    { eapply (VMBBMTransport.check_tlb_equiv (PState.initmem a) (l1 ++ before)
        (elements (dom (PState.initmem a))) (tlb_map (unshift (S (length before))) c) d);
        [apply Hsim|apply Hsim| | |apply Hsim|exact Hremoved].
      - intro fe. rewrite VMSwapRemove.history_tlb_map.
        apply VMSwapRemoveEvents.ordered_map_unshift. apply Hgood.
      - intro fe. apply Hgoodmid. }
    rewrite Hb. apply VMSwapBBMCache.check_tlb_insert; [reflexivity|].
    rewrite <- Heq. exact Hmidcheck.
  - rewrite (VMSwapRemoveRun.ts_rel_tlb_none before _ _ Hremove Hc). reflexivity.
Qed.

Lemma link_nopromises tid (a : state) mem b : thread_link tid a mem b →
  is_emptyb (TState.prom_wr (PState.tstate tid a) ++ TState.prom_tlbi (PState.tstate tid a)) =
  is_emptyb (TState.prom_wr b ++ TState.prom_tlbi b).
Proof.
  intros (before & after & tlbi & rc & epoch & l1 & l2 & Hrc & Heq & Ha & Hb & Hr & Hok).
  destruct Hr as (mid & Hremove & -> & Hpos & Hmid).
  pose proof (VMSwapRemoveRun.ts_rel_frame before _ _ Hremove) as Hframe.
  pose proof (f_equal TState.prom_wr Hframe) as Hwr.
  pose proof (f_equal TState.prom_tlbi Hframe) as Htlbi.
  change (TState.prom_wr mid = map (unshift (S (length before))) (TState.prom_wr (PState.tstate tid a))) in Hwr.
  change (TState.prom_tlbi mid = map (unshift (S (length before))) (TState.prom_tlbi (PState.tstate tid a))) in Htlbi.
  cbn [ts_map TState.prom_wr TState.prom_tlbi]. rewrite Hwr, Htlbi.
  destruct (TState.prom_wr (PState.tstate tid a)), (TState.prom_tlbi (PState.tstate tid a)); reflexivity.
Qed.

Lemma terminated term (a b : state) : related a b → PState.terminated prom term a = PState.terminated prom term b.
Proof.
  intros [_ [_ [_ Hlinks]]]. unfold PState.terminated, fforallb.
  apply VMCacheSimOutcome.forallb_ext'. intro tid.
  unfold PState.terminated_tid, PState.terminated_ts.
  change (pc_terminated (term !!! tid) (TState.pc (PState.tstate tid a)) =
    pc_terminated (term !!! tid) (TState.pc (PState.tstate tid b))).
  rewrite (link_pc tid a (PState.events b) (PState.tstate tid b) (Hlinks tid)). reflexivity.
Qed.
Lemma nopromises (a b : state) : related a b → PState.nopromises prom a = PState.nopromises prom b.
Proof.
  intros [_ [_ [_ Hlinks]]]. unfold PState.nopromises, fforallb.
  apply VMCacheSimOutcome.forallb_ext'. intro tid. apply (link_nopromises tid a (PState.events b)), Hlinks.
Qed.

Lemma check_valid_end_tid (a b : state) tid : related a b →
  PState.check_valid_end_tid prom a tid = [] → PState.check_valid_end_tid prom b tid = [].
Proof.
  intros [Himem [_ [_ Hlinks]]] Hcheck. unfold PState.check_valid_end_tid in *.
  change ((if bbm then match BBM.check (PState.initmem a) (PState.events a) (PState.tstate tid a) with
    | Ok true => ["BBM violation detected"] | Ok false => [] | Error err => [err] end else []) = []) in Hcheck.
  change ((if bbm then match BBM.check (PState.initmem b) (PState.events b) (PState.tstate tid b) with
    | Ok true => ["BBM violation detected"] | Ok false => [] | Error err => [err] end else []) = []).
  destruct bbm; [|reflexivity].
  destruct (BBM.check (PState.initmem a) (PState.events a) (PState.tstate tid a)) as [[]|err] eqn:Hbbm;
    try discriminate.
  rewrite <- Himem, (link_bbm tid a (PState.events b) (PState.tstate tid b) (Hlinks tid) Hbbm). reflexivity.
Qed.
Lemma check_valid_end (a b : state) : related a b →
  PState.check_valid_end prom a = [] → PState.check_valid_end prom b = [].
Proof.
  intros Hr Hcheck. unfold PState.check_valid_end in *.
  induction (enum (fin n)) as [|tid tids IH]; [reflexivity|].
  cbn [map List.concat] in Hcheck |- *. apply app_eq_nil in Hcheck as [Htid Htids].
  rewrite (check_valid_end_tid a b tid Hr Htid), (IH Htids). reflexivity.
Qed.

Theorem final_result term (a b : state) fs : related a b →
  VMNormalization.FinalResult bbm term a fs → VMNormalization.FinalResult bbm term b fs.
Proof.
  intros Hr [pt [Hvalid <-]].
  assert (pt' : CPState.terminated prom term b).
  { pose proof (terminated term a b Hr) as Ht. pose proof pt as pt0.
    unfold CPState.terminated, PState.terminated in Ht, pt0 |- *.
    rewrite <- Ht. exact pt0. }
  exists pt'. split.
  - destruct (VMCacheSimOutcome.validate_final_state_inv bbm a a a Hvalid) as [_ [Hpn Herrs]].
    apply VMCacheSimOutcome.validate_final_state_intro.
    + rewrite <- (nopromises a b Hr). exact Hpn.
    + apply (check_valid_end a b Hr), Herrs.
  - cbn. symmetry. apply (architectural_state bbm), Hr.
Qed.
End Machine.
End VMSwapFinal.
