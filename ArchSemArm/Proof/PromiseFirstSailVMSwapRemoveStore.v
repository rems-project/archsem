(******************************************************************************)
(* View, cache and timestamp exclusion through explicit writes                *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveThread
  PromiseFirstSailVMSwapRemoveTimes PromiseFirstSailVMSwapRemoveMemory
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMSwapRemoveStampRun PromiseFirstSailVMSwapRemoveTLBI.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveStore.
Import VMPromising VMSwapRemoveState VMSwapRemoveViews VMSwapRemoveThread.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma fwdbs_frame addrs n (data : bv n) time vdata xcl ts :
  TState.vcse (TState.set_fwdbs addrs data time vdata xcl ts) = TState.vcse ts ∧
  TState.tlb (TState.set_fwdbs addrs data time vdata xcl ts) = TState.tlb ts.
Proof.
  unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)) as items.
  intro items. revert ts. induction items as [|[a byte] items IH]; intro ts; [split; reflexivity|].
  cbn [foldl]. exact (IH (TState.set_fwdb a (FwdItem.make time vdata byte xcl) ts)).
Qed.

#[local] Hint Rewrite VMViews.strict_set_rmw_read VMViews.strict_set_trs
  VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_iis_field VMViews.mem_set_iis_field VMViews.iis_set_iis_field
  VMViews.state_set_mem VMViews.mem_set_mem VMViews.iis_set_mem : pp_store.
Ltac simpl_pp := unfold VMSwapRemoveThread.ok, setv in *; autorewrite with pp_store in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Ltac context_frame := first [reflexivity
  | match goal with |- context[TState.set_fwdbs ?addrs ?data ?time ?v ?xcl ?before] =>
      first [rewrite (proj1 (@fwdbs_frame addrs _ data time v xcl before)); context_frame
        |rewrite (proj2 (@fwdbs_frame addrs _ data time v xcl before)); context_frame] end
  | match goal with |- ?lhs = ?rhs => lazymatch lhs with context[TState.update_cohs ?avs ?before] =>
      first [change (TState.vcse (TState.update_cohs avs before) = rhs);
        rewrite (proj1 (VMSwapRemoveMemory.update_cohs_frame avs before)); context_frame
      |change (TState.tlb (TState.update_cohs avs before) = rhs);
        rewrite (proj2 (VMSwapRemoveMemory.update_cohs_frame avs before)); context_frame] end end].

Ltac solve_view := cbn [compose PPState.state PPState.iis fst snd];
  first [assumption | apply allowed_max; solve_view
    | apply view_if_ok; [apply allowed_zero; lia|solve_view]
    | left; cbn [length]; rewrite ?length_app; cbn; lia].
Ltac solve_views := first [assumption
  | apply list.Forall_fmap; apply list.Forall_forall; intros ? ?; cbn; solve_view].
Ltac solve_opt := first [assumption
  | unfold opt_ok; let H := fresh in intros ? H; first [discriminate H|injection H as <-; solve_view]].
Ltac solve_fields := first [assumption
  | apply update_vwr; [apply allowed_max|solve_view|solve_fields]
  | apply update_vrel; [apply allowed_max|solve_view|solve_fields]
  | apply update_vacq; [apply allowed_max|solve_view|solve_fields]
  | apply update_cohs; [apply allowed_zero; lia|apply allowed_max|solve_views|solve_fields]
  | apply filter_prom_wr; solve_fields
  | apply set_fwdbs; [solve_view|solve_view|solve_opt|solve_fields]
  | apply clear_xclb; solve_fields
  | apply iis_rmw_read; [intros; discriminate|solve_fields]
  | match goal with
    | |- ts_ok ?Q (TState.make _ _ (TState.regs ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
      let HX := fresh in assert (HX : ts_ok Q X) by solve_fields;
      destruct HX; constructor; cbn; try assumption; apply Forall_filter; assumption
    end].

Lemma write_mem_views tid imem l r tlbi rc epoch addr size macc data pp pp' value :
  PPState.mem pp = l ++ Ev.Tlbi tlbi rc epoch :: r → VMSwapRemoveThread.ok (S (length r)) pp →
  VMSwapRemoveStampMemory.ok (S (length r)) pp →
  Exec.elem_of_results (pp', value) (write_mem tid imem addr size macc data pp) →
  VMSwapRemoveThread.ok (S (length r)) pp'.
Proof.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hstamps Hrun. unfold write_mem in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: pose proof Hok as [[Hts Hcache] Hiis]; VMViews.facts Hts; VMViews.facts Hiis.
  all: try match goal with H : Memory.fulfill _ _ _ = Some ?time |- _ =>
    assert (Htime : time ≠ S (length r)) by
      (eapply VMSwapRemoveTimes.fulfill_avoids;
        [exact (VMSwapRemoveStamps.ok_prom_wr _ _ (proj1 Hstamps))|exact H]) end.
  all: try match goal with H : TState.xclb ?X = Some ?xcl, Hts : ts_ok _ ?X |- _ =>
    destruct (ok_xclb _ _ Hts xcl H) as [Hxcltime Hxclview] end.
  all: try match goal with H : TState.process_event ?tid ?imem ?mem ?ev ?before = Ok ?after |- _ =>
    assert (Hbase : local_ok (S (length r)) after iis) by
      (eapply (VMSwapRemoveThread.process_event (S (length r)) tid imem mem ev before after iis);
       [cbn; rewrite length_app; cbn; lia|exact Hok|exact H]);
    destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ H) as [o He];
    assert (Hvc : TState.vcse after = TState.vcse before) by (rewrite He; reflexivity) end.
  all: try pose proof Hok as Hbase.
  all: pose proof Hbase as [[Hbasets Hbasecache] Hbaseiis].
  all: try rewrite Hvc in Hbasets, Hbaseiis.
  all: match type of Hbase with local_ok _ ?base _ =>
    eapply (frame (S (length r)) base _ iis); [context_frame|context_frame| | |exact Hbase] end.
  all: try rewrite Hvc; solve_fields.
Qed.

Lemma write_mem_inv tid imem l r tlbi rc epoch addr size macc data pp pp' value :
  PPState.mem pp = l ++ Ev.Tlbi tlbi rc epoch :: r → VMSwapRemoveTLBI.inv (S (length r)) pp →
  Exec.elem_of_results (pp', value) (write_mem tid imem addr size macc data pp) →
  VMSwapRemoveTLBI.inv (S (length r)) pp'.
Proof.
  intros Hmem [Hviews Hstamps] Hrun. split.
  - eapply write_mem_views; eassumption.
  - eapply VMSwapRemoveStampEvents.write_mem_ok; eassumption.
Qed.
End VMSwapRemoveStore.
