(******************************************************************************)
(* Memory writes after removing a foreign TLBI                               *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemove
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveLocal
  PromiseFirstSailVMSwapRemoveRead PromiseFirstSailVMSwapRemoveEffects PromiseFirstSailVMSwapRemoveTimes
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMSwapRemoveStore PromiseFirstSailVMViews PromiseFirstSailVMSwapPos.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveStoreSim.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome VMSwapRemoveEffects.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Section Removed.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation R := (effect_rel r tlbi rc epoch).

Ltac bind V := eapply (esim_bind _ V); [|
  let x := fresh "x" in let y := fresh "y" in let Hxy := fresh "Hxy" in intros x y Hxy;
  lazymatch type of x with unit => clear Hxy; destruct x, y | _ => idtac end].
Ltac fold_unshift := unfold join, join_nat in *;
  repeat first [rewrite (VMSwapRemoveMap.unshift_view_if p ltac:(lia))|rewrite <- unshift_max].
Ltac scalar maplemma stamplemma := apply VMSwapRemoveEffects.update_state;
  [intros; symmetry; apply (maplemma p ltac:(lia))|intros; reflexivity|intro; reflexivity|intros; apply stamplemma; assumption].

Theorem write_mem_sim l addr size macc data a b : R a b → PPState.mem a = l ++ e :: r →
  ts_inv imem r tlbi rc epoch l (PPState.state a) →
  VMSwapInsert.esim_at R (λ x y : option nat, y = g <$> x)
    (write_mem tid imem addr size macc data) (write_mem tid imem addr size macc data) a b.
Proof.
  intros Hrel Hmem Hcache. unfold write_mem.
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  pose proof Hrel as [[[prefix [Hm Hm']] [Ht Hi]] [Hstamps Hii]].
  assert (Hprefix : prefix = l) by (rewrite Hmem in Hm; apply (app_inv_tail _ _ _) in Hm; symmetry; exact Hm).
  subst prefix. rewrite Hmem, Hm'.
  eapply (VMSwapInsert.esim_at_bind _ (λ x y : nat * bool, y.1 = g x.1 ∧ y.2 = x.2 ∧ x.1 ≠ p)).
  - pose proof (proj1 Ht) as Hshape. rewrite Hshape.
    cbn [ts_map TState.prom_wr].
    rewrite (fulfill_remove r tlbi rc epoch l _ _ (VMSwapRemoveStamps.ok_prom_wr _ _ Hstamps)).
    destruct (Memory.fulfill _ _ (l ++ e :: r)) as [time|] eqn:Hfulfill; cbn [fmap option_fmap option_map].
    + apply VMSwapInsert.esim_at_of; [|exact Hrel]. apply esim_ret.
      split; [reflexivity|]. split; [reflexivity|].
      eapply VMSwapRemoveTimes.fulfill_avoids; [apply Hstamps|exact Hfulfill].
    + rewrite <- Hshape. eapply fresh_event_map;
        [intros t Htime; cbn; split; [reflexivity|split; [reflexivity|exact Htime]]|exact Hrel|exact Hmem|exact Hcache].
  - intros a' b' [time fresh] [time' fresh'] Ha Hb Hr [Htime [Hfresh Hne]].
    cbn in Htime, Hfresh, Hne. subst time' fresh'.
    apply VMSwapInsert.esim_at_of; [|exact Hr].
    bind (@eq bool).
    { destruct (is_atomic_rmw macc); [|apply esim_ret; reflexivity].
      bind (λ x y : option (nat * bool), y = (λ tb, (g tb.1, tb.2)) <$> x); [apply get_rmw|]. subst y.
      eapply (esim_bind _ (λ x y : nat * bool, y = (g x.1, x.2)));
        [apply VMSwapInsert.esim_othrow_map, VMSwapInsert.option_rel_fmap|intros [tread acquire] pair' ->]. cbn [fst snd].
      bind (@eq unit); [apply esim_guard_discard'; apply (VMSwapInsert.exclusive_remove r tlbi rc epoch); exact Hne|].
      bind (@eq unit).
      { apply esim_msetv. intros [ta ma ia] [tb mb ib] [[Hms [Hts His]] [Hs Hsi]].
        unfold effect_rel, related; cbn in *; subst ib.
        split; [split; [exact Hms|split; [exact Hts|reflexivity]]|].
        split; [exact Hs|apply VMSwapRemoveStamps.iis_rmw; [discriminate|exact Hsi]]. }
      apply esim_ret. reflexivity. }
    subst y.
    bind (λ x y : nat, y = g x); [apply get_strict|]. subst y.
    pose proof (proj1 Ht) as Hshape. rewrite Hshape.
    cbn [ts_map TState.vrd TState.vwr TState.vdmb TState.vdmbst TState.vdsb TState.vcse
      TState.vacq TState.vrel TState.vspec TState.coh TState.xclb]. fold_unshift.
    eapply esim_bind.
    { apply esim_guard_discard. intros [Hv Hcoh]. split.
      - apply (proj2 (unshift_lt_iff_ne p _ time Hne ltac:(lia))), Hv.
      - intros address Hin. rewrite (VMSwapRemoveMap.lookup_total_map p ltac:(lia)).
        apply (proj2 (unshift_lt_iff_ne p _ time Hne ltac:(lia))), Hcoh, Hin. }
    intros ? ? _.
    bind (λ x y : option nat, y = g <$> x ∧ (∀ t, x = Some t → t ≠ p)); [apply get_inv|].
    destruct Hxy as [-> Hinv].
    bind (@eq unit).
    { apply esim_guard_discard'. match goal with |- context [if ?o is Some _ then _ else _] => destruct o as [inv|] end; cbn;
        [apply (proj2 (unshift_lt_iff_ne p time inv (Hinv inv eq_refl) ltac:(lia)))|auto]. }
    bind (@eq unit).
    { change (esim R eq (mset PPState.state (set TState.prom_wr (filter (λ t, t ≠ time))))
        (mset PPState.state (set TState.prom_wr (filter (λ t, t ≠ g time))))).
      apply VMSwapRemoveEffects.update_state.
      - intros ts Hts. symmetry. apply (VMSwapRemoveMap.map_filter_prom_wr p ltac:(lia)); [exact Hne|apply Hts].
      - intros; reflexivity.
      - intro; reflexivity.
      - intros; apply VMSwapRemoveStamps.filter_prom_wr; assumption. }
    replace (map (λ x : bv addr_size, (x, g time)) (addr_range addr size)) with
      (map (λ av, (av.1, g av.2)) (map (λ x : bv addr_size, (x, time)) (addr_range addr size)))
      by (rewrite map_map; reflexivity).
    bind (@eq unit).
    { apply VMSwapRemoveEffects.update_state.
      - intros; symmetry; apply (VMSwapRemoveMap.map_update_cohs p ltac:(lia)).
      - intros; apply VMCacheSimOutcome.update_cohs_setv.
      - intro; apply VMSwapPos.update_cohs_tlb.
      - intros ts Hts. apply VMSwapRemoveStamps.update_cohs; [lia| |exact Hts].
        apply list.Forall_fmap, list.Forall_forall. intros; exact Hne. }
    bind (@eq unit); [scalar VMSwapRemoveMap.map_vwr VMSwapRemoveStamps.update_vwr|].
    bind (@eq unit); [scalar VMSwapRemoveMap.map_vrel VMSwapRemoveStamps.update_vrel|].
    bind (@eq unit).
    { destruct (_ && _ && _); [scalar VMSwapRemoveMap.map_vacq VMSwapRemoveStamps.update_vacq|apply esim_ret; reflexivity]. }
    bind (λ x y : option nat, y = g <$> x).
    { destruct (is_exclusive macc); [|apply esim_ret; reflexivity].
      change (TState.xclb (setv TState.tlb (TState.tlb (PPState.state b)) (ts_map g (PPState.state a))))
        with (xcl_map g <$> TState.xclb (PPState.state a)).
      destruct (TState.xclb (PPState.state a)) as [xcl|]; cbn [fmap option_fmap option_map]; [|apply esim_discard].
      bind (@eq unit); [scalar VMSwapRemoveMap.map_clear_xclb VMSwapRemoveStamps.clear_xclb|].
      destruct xcl as [xt xa xs xv]. cbn [xcl_map XclItem.addr XclItem.size XclItem.time XclItem.view].
      destruct (decide _); [|apply esim_discard].
      bind (@eq unit); [apply esim_guard_discard'; apply (VMSwapInsert.exclusive_remove r tlbi rc epoch); exact Hne|].
      apply esim_ret. reflexivity. }
    match goal with H : ?y = g <$> ?x |- _ => subst y end.
    bind (@eq unit).
    { apply VMSwapRemoveEffects.update_state.
      - intros; symmetry; apply (VMSwapRemoveMap.map_set_fwdbs p ltac:(lia)).
      - intros; apply VMCacheSimOutcome.set_fwdbs_setv.
      - intro; apply VMSwapPos.set_fwdbs_tlb.
      - intros; apply VMSwapRemoveStamps.set_fwdbs; assumption. }
    apply esim_ret. destruct fresh; reflexivity.
Qed.
End Removed.
End VMSwapRemoveStoreSim.
