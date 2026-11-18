(******************************************************************************)
(* Register-write simulation after removing a foreign TLBI                     *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemove
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveLocal
  PromiseFirstSailVMSwapRemoveCSE PromiseFirstSailVMViews PromiseFirstSailVMPageWrites.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveRegWrite.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma set_reg_square r reg vv ta tb : ts_rel r ta tb →
  option_rel (ts_rel r) (TState.set_reg reg vv ta)
    (TState.set_reg reg (vv_map (unshift (S (length r))) vv) tb).
Proof.
  intro Hrel. pose proof (VMSwapRemoveMap.map_set_reg (S (length r)) ltac:(lia) reg vv ta) as Hmap.
  destruct (TState.set_reg reg vv ta) as [ta'|] eqn:Hset.
  - cbn in Hmap. destruct (VMCacheSimOutcome.set_reg_sim reg _ _ tb _ Hrel Hmap) as [tb' [Hset' Hsim]].
    rewrite Hset'. exact Hsim.
  - cbn in Hmap. rewrite (VMCacheSimOutcome.set_reg_none_sim reg _ _ tb Hrel Hmap). exact I.
Qed.

Section Removed.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation R := (related r tlbi rc epoch).

Lemma get_state : esim R (ts_rel r) (mget PPState.state) (mget PPState.state).
Proof. apply esim_mget. intros a b [_ [Ht _]]. exact Ht. Qed.
Ltac bind V := eapply (esim_bind _ V); [|
  let x := fresh "x" in let y := fresh "y" in let Hxy := fresh "Hxy" in intros x y Hxy;
  lazymatch type of x with unit => clear Hxy; destruct x, y | _ => idtac end].
Ltac fold_unshift := unfold join, join_nat in *;
  repeat first [rewrite (VMSwapRemoveMap.unshift_view_if p ltac:(lia))|rewrite <- unshift_max].
Ltac update := apply VMSwapRemoveCSE.update_state;
  [intro; symmetry; first [apply (VMSwapRemoveMap.map_vmsr p ltac:(lia))|apply (VMSwapRemoveMap.map_vspec p ltac:(lia))]
  |intros; reflexivity|intro; reflexivity].
Ltac set_reg_fold :=
  match goal with |- context [TState.set_reg ?reg (?val, g ?time) ?ts] =>
    change (TState.set_reg reg (val, g time) ts) with (TState.set_reg reg (vv_map g (val, time)) ts) end.

Theorem run_reg_write_sim l reg racc val a b : R a b → PPState.mem a = l ++ e :: r → VMViews.ok a →
  ts_inv imem r tlbi rc epoch l (PPState.state a) → msr_inv (PPState.state a) →
  VMSwapRemoveMap.promises_avoid p (PPState.state a) → VMPageWrites.ok a →
  VMSwapInsert.esim_at R eq (run_reg_write tid imem reg racc val) (run_reg_write tid imem reg racc val) a b.
Proof using Hrc.
  intros Hrel Hmem Hbound Hcache Hmsr Hprom Hevents. unfold run_reg_write.
  apply (VMSwapInsert.esim_at_bind _ eq); [apply VMSwapInsert.esim_at_of; [apply esim_guard_or_refl|exact Hrel]|].
  intros a' b' u u' Ha Hb Hrel' <-. apply Exec.elem_of_guard_or_inv in Ha as ->.
  apply Exec.elem_of_guard_or_inv in Hb as ->.
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_of; [|exact Hrel].
  destruct a as [ta ma ia], b as [tb mb ib]. cbn in *.
  destruct Hrel as [[prefix [Hm Hm']] [Ht Hi]]. cbn in *.
  assert (Hprefix : prefix = l) by (rewrite Hmem in Hm; apply (app_inv_tail _ _ _) in Hm; symmetry; exact Hm).
  subst prefix ma mb ib.
  destruct Hbound as [Hbt Hbi]. cbn in Hbt, Hbi.
  pose proof (VMViews.ok_strict _ _ Hbi) as Hstrict.
  pose proof (VMViews.ok_vcse _ _ Hbt) as Hvcse.
  pose proof (VMViews.ok_vspec _ _ Hbt) as Hvspec.
  pose proof (VMViews.ok_vdsb _ _ Hbt) as Hvdsb.
  pose proof (VMViews.ok_vmsr _ _ Hbt) as Hvmsr.
  pose proof (proj1 Ht) as Hshape. rewrite Hshape.
  cbn [ts_map TState.vcse TState.vspec TState.vdsb iis_map IIS.strict]. fold_unshift.
  destruct racc as [acc|].
  - bind (λ x y : nat, y = g x).
    { destruct (decide _); [|destruct (decide _)]; [| |apply esim_throw].
      - bind (λ x y : reg_type reg * view, y = vv_map g x ∧ TState.read_sreg_direct ta reg = Some x).
        { apply VMSwapInsert.esim_othrow_map.
          change (TState.read_sreg_direct (setv TState.tlb (TState.tlb tb) (ts_map g ta)) reg)
            with (TState.read_sreg_direct (ts_map g ta) reg).
          rewrite ts_map_read_sreg_direct.
          destruct (TState.read_sreg_direct ta reg); cbn; [split; reflexivity|exact I]. }
        destruct x as [old view], y as [old' view'], Hxy as [Hval Hread]. unfold vv_map in Hval; cbn in Hval.
        injection Hval as <- ->.
        pose proof (VMViews.read_sreg_direct_ok _ _ _ _ Hbt Hread) as Hview. cbn in Hview.
        fold_unshift. bind (ts_rel r).
        { apply esim_lift_result.
          - intros ta' Hrun.
            match type of Hrun with TState.add_wsreg _ _ _ _ _ ?v _ = _ =>
              destruct (add_wsreg_remove tid imem r tlbi rc epoch Hrc l reg val v ta tb ta' Ht Hcache
                ltac:(lia) ltac:(lia) (ttbr_ok_of_inv _ v ta Hmsr Hvmsr) Hrun) as (tb' & Hrun' & Hrel'' & Hcache') end.
            exists tb'. split; [rewrite <- Hshape; exact Hrun'|exact Hrel''].
          - intros err Hrun.
            destruct (VMPageWrites.add_wsreg_remove_error tid imem l r tlbi rc epoch reg val _ ta tb err Ht Hevents Hrun)
              as [err' Hrun']. exists err'. rewrite <- Hshape. exact Hrun'. }
        bind (@eq unit); [apply VMSwapRemoveCSE.set_state, Hxy|apply esim_ret; reflexivity].
      - bind (ts_rel r).
        { apply VMSwapInsert.esim_othrow_map. set_reg_fold.
          rewrite <- Hshape. apply set_reg_square, Ht. }
        bind (@eq unit); [apply VMSwapRemoveCSE.set_state, Hxy|apply esim_ret; reflexivity]. }
    subst y. bind (@eq unit); [update|apply VMSwapRemoveCSE.add].
  - match goal with |- esim _ _ (if ?choice then _ else _) _ => destruct choice end.
    + eapply esim_bind; [apply esim_guard_discard; apply (VMSwapRemoveMap.map_no_promises_until p ltac:(lia)), Hprom|intros ? ? _].
      bind (@eq unit); [update|].
      bind (ts_rel r); [apply get_state|].
      bind (ts_rel r).
      { apply VMSwapInsert.esim_othrow_map.
        replace (val, 0) with (vv_map g (val, 0)) at 2 by (unfold vv_map; cbn; rewrite unshift_zero; reflexivity).
        apply set_reg_square, Hxy. }
      apply VMSwapRemoveCSE.set_state, Hxy0.
    + destruct (decide _); [|apply esim_throw].
      bind (ts_rel r).
      { apply VMSwapInsert.esim_othrow_map. set_reg_fold. rewrite <- Hshape. apply set_reg_square, Ht. }
      apply VMSwapRemoveCSE.set_state, Hxy.
Qed.
End Removed.
End VMSwapRemoveRegWrite.
