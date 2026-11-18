(******************************************************************************)
(* Exact merging of lookup results after removing a foreign TLBI              *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveLookup
  PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveTimes PromiseFirstSailVMWalkLookup
  PromiseFirstSailVMViews PromiseFirstSailVMCacheState PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMLookup PromiseFirstSailVMSwapRemoveHistory PromiseFirstSailVMSwapRemoveLookupViews
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveThread PromiseFirstSailVMSwapRemoveEvents.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveMerge.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveViews.
#[local] Typeclasses Transparent view UMPromising.view.

Definition stamped p cap result := good p cap result ∧ opt_ok (λ t, t ≠ p) (TLB.Result.inv_time result).

Lemma option_inj p a b : opt_ok (λ t, t ≠ p) a → opt_ok (λ t, t ≠ p) b →
  unshift p <$> a = unshift p <$> b → a = b.
Proof.
  destruct a as [a|], b as [b|]; cbn; intros Ha Hb Heq; try discriminate; [|reflexivity].
  injection Heq as Heq. f_equal. apply (unshift_eq_ne p a b); [apply Ha|apply Hb|exact Heq]; reflexivity.
Qed.

Lemma key_map p cap a b : 0 < p → stamped p cap a → stamped p cap b →
  VMCacheSim.key (res_map (unshift p) a) = VMCacheSim.key (res_map (unshift p) b) ↔
  VMCacheSim.key a = VMCacheSim.key b.
Proof.
  intros Hp [Ga Ia] [Gb Ib]. unfold VMCacheSim.key. cbn [res_map TLB.Result.path TLB.Result.tend TLB.Result.inv_time].
  split; intro H; injection H as H1 H2 H3 H4; f_equal; [f_equal; [f_equal; assumption|]| |f_equal; [f_equal; assumption|]|].
  - eapply good_inj; eassumption.
  - eapply option_inj; eassumption.
  - rewrite H3. reflexivity.
  - rewrite H4. reflexivity.
Qed.

Lemma comb_map p a b : VMCacheSim.comb (res_map (unshift p) a) (res_map (unshift p) b) =
  res_map (unshift p) (VMCacheSim.comb a b).
Proof.
  destruct a, b. unfold VMCacheSim.comb, res_map, TLB.Result.walk, setv. cbn.
  match goal with |- context[if ?choice then _ else _] => destruct choice end;
    cbn; rewrite unshift_min; reflexivity.
Qed.

Lemma stamped_comb p cap a b : stamped p cap a → VMCacheSim.key a = VMCacheSim.key b →
  stamped p cap (VMCacheSim.comb a b).
Proof.
  intros [Ha Hi] Hkey. split; [apply good_comb; assumption|]. rewrite VMCacheSim.comb_inv by exact Hkey. exact Hi.
Qed.

Lemma merge_into p cap result acc : 0 < p → stamped p cap result → Forall (stamped p cap) acc →
  TLB.Result.merge_into (res_map (unshift p) result) (map (res_map (unshift p)) acc) =
    map (res_map (unshift p)) (TLB.Result.merge_into result acc) ∧
  Forall (stamped p cap) (TLB.Result.merge_into result acc).
Proof.
  intros Hp Hresult Hacc. induction Hacc as [|a acc Ha Hacc IH].
  - split; [reflexivity|constructor; [exact Hresult|constructor]].
  - cbn [map]. rewrite !VMCacheSim.merge_into_cons.
    pose proof (key_map p cap a result Hp Ha Hresult) as Hkey.
    pose proof (VMCacheSim.mergeable_key a result) as Hm.
    pose proof (VMCacheSim.mergeable_key (res_map (unshift p) a) (res_map (unshift p) result)) as Hm'.
    destruct (decide (TLB.Result.mergeable a result)) as [H1|H1];
      destruct (decide (TLB.Result.mergeable (res_map (unshift p) a) (res_map (unshift p) result))) as [H2|H2];
      try tauto.
    + split; [cbn [map]; rewrite comb_map; reflexivity|]. constructor; [apply stamped_comb; tauto|exact Hacc].
    + destruct IH as [Heq Hi]. split; [cbn [map]; rewrite Heq; reflexivity|constructor; assumption].
Qed.

Theorem merge_exact p cap results : 0 < p → Forall (stamped p cap) results →
  TLB.Result.merge (map (res_map (unshift p)) results) = map (res_map (unshift p)) (TLB.Result.merge results).
Proof.
  intros Hp Hresults. unfold TLB.Result.merge.
  cut (∀ acc, Forall (stamped p cap) acc →
    foldl (λ acc r, TLB.Result.merge_into r acc) (map (res_map (unshift p)) acc)
      (map (res_map (unshift p)) results) =
    map (res_map (unshift p)) (foldl (λ acc r, TLB.Result.merge_into r acc) acc results));
    [intro H; apply (H []); constructor|].
  induction Hresults as [|result results Hr Hresults IH]; intros acc Hacc; [reflexivity|].
  cbn [map foldl]. destruct (merge_into p cap result acc Hp Hr Hacc) as [Heq Hi].
  rewrite Heq. apply IH, Hi.
Qed.

Lemma Forall2_map_eq {A B} (f : A → B) xs ys : Forall2 (λ x y, y = f x) xs ys → ys = map f xs.
Proof. induction 1; cbn; congruence. Qed.
Lemma events_good p tid ifetch ttbr path events tmin tmax inv : 0 < p → Forall tpos events →
  Forall (λ et, ∀ issuer, et.1 = TLB.Entry.Tlbi issuer → et.2 ≠ p) events →
  Forall (good p tmax) (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof.
  intros Hp Hpos Htimes. apply list.Forall_forall. intros result Hin. split.
  - exact (VMViews.Forall_elem _ _ _ (VMWalkLookup.parent_end_bound tid ifetch ttbr path events tmin tmax inv) Hin).
  - intro Hend. destruct (decide (tmax = pred p)) as [Hcap|Hcap]; [exact Hcap|].
    pose proof (VMSwapRemoveLookup.events_caps p tid ifetch ttbr path events Hp Hpos Htimes
      tmin tmax inv Hcap) as Hends.
    pose proof (VMViews.Forall_elem _ _ _ Hends Hin). contradiction.
Qed.

Lemma ptes_factor p ptes : 0 < p → Forall (λ vt : bv 64 * nat, vt.2 ≠ p) ptes →
  map_ptes p (VMSwapRemoveLookup.unshift_ptes p ptes) = ptes.
Proof.
  intros Hp Htimes. induction Htimes as [|[pte time] ptes Htime Htimes IH]; [reflexivity|].
  cbn [map_ptes VMSwapRemoveLookup.unshift_ptes map fst snd]. cbn in Htime.
  rewrite shift_unshift by assumption. f_equal. exact IH.
Qed.

Section Removed.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat)
  (ifetch upper : bool) (vpn : pn).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation mem := (l ++ Ev.Tlbi tlbi rc epoch :: r).
Local Notation short := (l ++ r).

Lemma fe_good fe events tmin_ok tmin_unc tmax results : tmax ≤ length mem → Forall tpos events →
  Forall (λ et, ∀ issuer, et.1 = TLB.Entry.Tlbi issuer → et.2 ≠ p) events →
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax = Ok results →
  Forall (good p tmax) results.
Proof.
  intros Hb Hpos Htimes. unfold TLB.get_result_from_FE. case_decide.
  - unfold TLB.get_result_from_table_FE.
    destruct (decide (tmax < tmin_unc)); [injection 1 as <-; constructor|].
    destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection 1 as <-; constructor].
    pose proof (events_good p tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe) events tmin_unc tmax None
      ltac:(lia) Hpos Htimes) as Hparents.
    destruct (TLB.get_results_from_events _ _ _ _ _ _ _ _) as [|result parents]; [injection 1 as <-; constructor|].
    destruct (Memory.read_all_pte _ imem mem tmin_unc tmax) as [ptes|err] eqn:Hread; [|discriminate].
    injection 1 as <-.
    assert (Hptes : Forall (λ vt : bv 64 * nat, vt.2 ≠ p) ptes) by
      (apply list.Forall_forall; intros pte Hin; eapply VMSwapRemoveTimes.read_all_pte_avoids; eassumption).
    pose proof (uncacheable_aux_good p ltac:(lia) tmax lvl tmin_unc (result :: parents)
      (VMSwapRemoveLookup.unshift_ptes p ptes) Hparents tmax ltac:(unfold good_cap; tauto)) as Hgood.
    rewrite ptes_factor in Hgood by (try lia; exact Hptes). exact Hgood.
  - unfold TLB.get_result_from_leaf_FE. injection 1 as <-.
    destruct (decide (tmax < tmin_ok)); [constructor|]. apply events_good; [lia|exact Hpos|exact Htimes].
Qed.

Lemma lookup_good cache limit asid tmin_ok tmin_unc tmax :
  VMCacheState.cache_inv (length mem) cache → pos_cache cache →
  VMSwapRemoveHistory.histories (VMSwapRemoveEvents.event_allowed p limit) cache → tmax ≤ length mem →
  Forall (good p tmax) (Exec.results (TLB.lookup tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid)).
Proof.
  intros [Hgood [Hunique Hvalid]] Hpos Hhist Hb. apply VMViews.Forall_results. intros result Hin.
  apply VMLookupReplay.lookup_witness in Hin as (fe & events & candidates & Hentry & Hget & Hin).
  pose proof (pos_get_fes cache _ fe events Hpos Hentry) as Htimes.
  assert (Havoid : Forall (λ et, ∀ issuer, et.1 = TLB.Entry.Tlbi issuer → et.2 ≠ p) events).
  { apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [_ Hentry]].
    unfold TLB.VATLB.get_fe in Hentry.
    apply list_elem_of_In, List.in_map_iff in Hentry as [[entry events'] [Heq Hentry]].
    apply list_elem_of_In in Hentry. injection Heq as <- <-.
    rewrite <- (VMBBMTransport.row_history cache ctxt entry events' Hunique Hentry).
    eapply list.Forall_impl; [apply Hhist|]. intros [event time] [Hne|[Hload _]] issuer He;
      [exact Hne|cbn in Hload, He; congruence]. }
  exact (VMViews.Forall_elem _ _ _ (fe_good fe events tmin_ok tmin_unc tmax candidates Hb Htimes Havoid Hget) Hin).
Qed.

Lemma tlb_good ts asid ttbr0 tmin_ok tmin_unc tmax :
  VMViews.ts_ok (length mem) ts → VMSwapRemoveThread.thread_ok p ts → ts_pos ts → tmax ≤ length mem →
  Forall (good p tmax) (Exec.results (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax)).
Proof.
  intros Hbound [Hviews Hcache] Hpos Hb. rewrite tlb_lookup_shape.
  destruct (TState.tlb ts) as [cache|] eqn:Hc; [|constructor].
  unfold Exec.merge. cbn [Exec.results]. apply Forall_app. split.
  - apply (lookup_good cache (TState.vcse ts));
      [apply (VMViews.ok_cache _ _ Hbound), Hc|apply Hpos, Hc|apply (proj1 (Hcache cache Hc))|exact Hb].
  - apply VMSwapLookup.root_lookup_good.
Qed.

Lemma tlb_stamped ts asid ttbr0 tmin_ok tmin_unc tmax :
  VMViews.ts_ok (length mem) ts → VMSwapRemoveThread.thread_ok p ts → ts_pos ts →
  VMSwapRemoveState.allowed p (TState.vcse ts) tmin_ok →
  VMSwapRemoveState.allowed p (TState.vcse ts) tmin_unc → tmax ≤ length mem →
  Forall (stamped p tmax) (Exec.results (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax)).
Proof.
  intros Hbound Hthread Hpos Hmin Hunc Hb.
  pose proof (tlb_good ts asid ttbr0 tmin_ok tmin_unc tmax Hbound Hthread Hpos Hb) as Hgood.
  apply VMViews.Forall_results. intros result Hin. split.
  - exact (VMViews.Forall_elem _ _ _ Hgood Hin).
  - exact (proj2 (VMSwapRemoveLookupViews.tlb_lookup_ok imem l r tlbi rc epoch tid ts
      ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax result Hbound Hthread Hmin Hunc Hb Hin)).
Qed.

Theorem tlb_merged_exact ts asid ttbr0 tmin_ok tmin_unc tmax :
  VMViews.ts_ok (length mem) ts → VMSwapRemoveThread.thread_ok p ts → ts_pos ts →
  VMSwapRemoveState.allowed p (TState.vcse ts) tmin_ok →
  VMSwapRemoveState.allowed p (TState.vcse ts) tmin_unc →
  TState.vcse ts ≤ tmin_ok → TState.vcse ts ≤ tmin_unc → TState.vcse ts ≤ tmax → tmax ≤ length mem →
  let before := TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax in
  let after := TState.tlb_lookup tid imem short (ts_map g ts) ifetch upper vpn asid ttbr0 (g tmin_ok) (g tmin_unc) (g tmax) in
  res_lift (λ x y, y = res_map g x)
    (Exec.make (TLB.Result.merge (Exec.results before)) (Exec.errors before))
    (Exec.make (TLB.Result.merge (Exec.results after)) (Exec.errors after)).
Proof.
  intros Hbound Hthread Hpos Hmin Hunc Hlo Hlo' Hcap Hb. cbn zeta.
  destruct (VMSwapRemoveLookup.tlb_exact tid imem l r tlbi rc epoch ifetch vpn ts upper asid ttbr0
    tmin_ok tmin_unc tmax Hbound Hthread Hpos Hmin Hunc Hlo Hlo' Hcap Hb) as [Hresults Herr].
  apply Forall2_map_eq in Hresults.
  pose proof (tlb_stamped ts asid ttbr0 tmin_ok tmin_unc tmax Hbound Hthread Hpos Hmin Hunc Hb) as Hstamps.
  split; cbn [Exec.results Exec.errors]; [|exact Herr].
  rewrite Hresults, (merge_exact p tmax _ ltac:(lia) Hstamps). apply VMSwapLookup.Forall2_map_r.
Qed.
End Removed.
End VMSwapRemoveMerge.
