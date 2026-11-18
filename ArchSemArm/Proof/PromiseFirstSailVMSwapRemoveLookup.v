(******************************************************************************)
(* Exact cached and root lookup after removing a foreign TLBI                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheOrder PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMSwapRemove PromiseFirstSailVMSwapRemoveEvents PromiseFirstSailVMSwapRemoveLookupViews
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveTimes
  PromiseFirstSailVMCacheState PromiseFirstSailVMCacheSim PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMLookup PromiseFirstSailVMSwapRemoveHistory PromiseFirstSailVMRootLookup
  PromiseFirstSailVMViews PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveThread.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveLookup.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveEvents.
#[local] Typeclasses Transparent view UMPromising.view.

Lemma unshift_lt_cap p a b : 0 < p → a ≠ pred p → unshift p a < unshift p b ↔ a < b.
Proof. intros. shift_cases. Qed.
Lemma unshift_pred_ne p t : 0 < p → t ≠ p → unshift p (pred t) = pred (unshift p t).
Proof. intros. shift_cases. Qed.
Lemma min_avoids a b t : a ≠ t → b ≠ t → Nat.min a b ≠ t.
Proof. lia. Qed.

Definition cap_ok p result := TLB.Result.tend result ≠ pred p.

(** The only empty interval that unshift could make nonempty is [p,p-1].
    The CSE-relative view invariant rules it out for actual query bounds. *)
Definition window p tmin tmax := tmin ≠ p ∨ tmax ≠ pred p.
Lemma window_compare p tmin tmax : 0 < p → window p tmin tmax →
  unshift p tmax < unshift p tmin ↔ tmax < tmin.
Proof.
  intros Hp [Hmin|Hmax]; [apply unshift_lt_iff_ne|apply unshift_lt_cap]; assumption.
Qed.
Lemma window_min p tmin a b : window p tmin a → window p tmin b → window p tmin (Nat.min a b).
Proof. intros [Hmin|Ha] [Hmin'|Hb]; [left|left|left|right]; try assumption. apply min_avoids; assumption. Qed.
Lemma window_allowed p limit tmin tmax : 0 < p → VMSwapRemoveState.allowed p limit tmin →
  limit ≤ tmax → window p tmin tmax.
Proof. intros Hp [Hmin|Hlimit] Hmax; [left; exact Hmin|right; lia]. Qed.

Lemma events_exact p tid ifetch ttbr path events tmin tmax inv :
  0 < p → window p tmin tmax → VMCacheOrder.ordered events → Forall tpos events →
  Forall (event_allowed p tmin) events →
  TLB.get_results_from_events tid ifetch ttbr path (map_evs (unshift p) events)
    (unshift p tmin) (unshift p tmax) (unshift p <$> inv) =
  map (res_map (unshift p)) (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof.
  intros Hp Hcap Hord Hpos Hevents. destruct (decide (tmin ≤ tmax)) as [Hrange|Hempty].
  - apply get_results_from_events_remove_exact; assumption.
  - rewrite !events_empty; [reflexivity|lia|]. apply window_compare; [exact Hp|exact Hcap|lia].
Qed.

Lemma events_caps p tid ifetch ttbr path events : 0 < p → Forall tpos events →
  Forall (λ et, ∀ issuer, et.1 = TLB.Entry.Tlbi issuer → et.2 ≠ p) events →
  ∀ tmin tmax inv, tmax ≠ pred p →
  Forall (cap_ok p) (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof.
  intro Hp. induction events as [events IH] using (induction_ltof1 _ (@length _)).
  unfold ltof in IH. intros Hpos Htimes.
  destruct events as [|[event time] events]; intros tmin tmax inv Hcap;
    cbn [TLB.get_results_from_events]; destruct (decide (tmax < tmin)); try constructor.
  apply list.Forall_cons in Hpos as [Hpos Htailpos].
  apply list.Forall_cons in Htimes as [Htime Htail]. destruct event as [|issuer].
  - destruct (decide (tmax < time)); [apply IH; [cbn; lia|exact Htailpos|exact Htail|exact Hcap]|].
    destruct (decide (time < tmin)); [constructor; [exact Hcap|constructor]|].
    destruct events as [|[[|issuer'] time'] rest].
    + constructor; [exact Hcap|apply IH; [cbn; lia|exact Htailpos|exact Htail|exact Hcap]].
    + constructor; [exact Hcap|apply IH; [cbn; lia|exact Htailpos|exact Htail|exact Hcap]].
    + pose proof Htailpos as Hallpos. pose proof Htail as Hall.
      apply list.Forall_cons in Htailpos as [_ Hrestpos]. apply list.Forall_cons in Htail as [_ Hrest].
      destruct (decide (time = time' ∧ (ifetch ∨ issuer' = tid))).
      * destruct rest as [|[[|issuer''] time''] rest].
        2: apply IH; [cbn; lia|exact Hrestpos|exact Hrest|exact Hcap].
        all: constructor; [exact Hcap|apply IH; [cbn; lia|exact Hallpos|exact Hall|exact Hcap]].
      * constructor; [exact Hcap|apply IH; [cbn; lia|exact Hallpos|exact Hall|exact Hcap]].
  - apply IH; [cbn; lia|exact Htailpos|exact Htail|].
    apply min_avoids; [exact Hcap|]. specialize (Htime issuer eq_refl). cbn in Hpos, Htime. lia.
Qed.

Definition unshift_ptes p (ptes : list (bv 64 * nat)) := map (λ vt, (vt.1, unshift p vt.2)) ptes.

Lemma get_fes_time_map f cache ctxts :
  TLB.get_fes (tlb_map f cache) ctxts =
  map (λ row, (row.1, map_evs f row.2)) (TLB.get_fes cache ctxts).
Proof.
  unfold TLB.get_fes. induction ctxts as [|ctxt ctxts IH]; [reflexivity|].
  cbn [map List.concat]. rewrite map_app, IH. f_equal.
  unfold TLB.VATLB.get_fe. rewrite tlb_map_vatlb, vatlb_get_map, !map_map.
  apply map_ext. intros [entry events]. reflexivity.
Qed.

Lemma uncacheable_exact p lvl tmin results : 0 < p →
  Forall (λ result, window p tmin (TLB.Result.tend result)) results →
  ∀ ptes tmax, Forall (λ vt, vt.2 ≠ p) ptes → window p tmin tmax →
  TLB.get_results_from_events_uncacheable_aux (map (res_map (unshift p)) results)
    (unshift_ptes p ptes) (unshift p tmin) (unshift p tmax) lvl =
  map (res_map (unshift p)) (TLB.get_results_from_events_uncacheable_aux results ptes tmin tmax lvl).
Proof.
  intros Hp Hresults. induction Hresults as [|result results Hcap Hresults IH];
    intros ptes tmax Hptes Hmax; [reflexivity|].
  cbn [map]. rewrite !unc_cons.
  revert tmax Hmax. induction Hptes as [|[pte time] ptes Htime Hptes IHp]; intros tmax Hmax;
    cbn [unc_inner unshift_ptes map fst snd]; [reflexivity|].
  cbn [res_map TLB.Result.tend TLB.Result.tstart]. cbn in Htime.
  assert (Hcapmin : window p tmin (Nat.min (TLB.Result.tend result) tmax)) by (apply window_min; assumption).
  assert (Hrange : Nat.min (unshift p (TLB.Result.tend result)) (unshift p tmax) < unshift p tmin ↔
    Nat.min (TLB.Result.tend result) tmax < tmin) by
    (rewrite <- unshift_min; apply window_compare; assumption).
  destruct (decide (Nat.min (TLB.Result.tend result) tmax < tmin)) as [H1|H1];
    destruct (decide (Nat.min (unshift p (TLB.Result.tend result)) (unshift p tmax) < unshift p tmin)) as [H2|H2];
    try tauto; try reflexivity.
  assert (Hrest :
    (if decide (unshift p time ≤ unshift p (TLB.Result.tstart result))
     then TLB.get_results_from_events_uncacheable_aux (map (res_map (unshift p)) results)
       ((pte, unshift p time) :: unshift_ptes p ptes) (unshift p tmin) (unshift p tmax) lvl
     else unc_inner (res_map (unshift p) result) (map (res_map (unshift p)) results)
       (unshift p tmin) lvl (unshift_ptes p ptes) (pred (unshift p time))) =
    map (res_map (unshift p))
      (if decide (time ≤ TLB.Result.tstart result)
       then TLB.get_results_from_events_uncacheable_aux results ((pte, time) :: ptes) tmin tmax lvl
       else unc_inner result results tmin lvl ptes (pred time))).
  { pose proof (unshift_le_iff_ne p time (TLB.Result.tstart result) Htime Hp) as Hle.
    destruct (decide (time ≤ TLB.Result.tstart result)) as [H3|H3];
      destruct (decide (unshift p time ≤ unshift p (TLB.Result.tstart result))) as [H4|H4];
      try tauto.
    - apply (IH ((pte, time) :: ptes) tmax); [constructor; assumption|exact Hmax].
    - rewrite <- unshift_pred_ne by assumption. apply (IHp (pred time)). right. lia. }
  destruct (decide (is_tlb_fillable lvl pte)); [exact Hrest|].
  cbn [map]. f_equal; [|exact Hrest]. destruct result; cbn.
  unfold res_map, setv. cbn. rewrite !unshift_max, unshift_min. reflexivity.
Qed.
Lemma events_windows p tid ifetch ttbr path events tmin tmax inv :
  0 < p → window p tmin tmax → Forall tpos events → Forall (event_allowed p tmin) events →
  Forall (λ result, window p tmin (TLB.Result.tend result))
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof.
  intros Hp [Hmin|Hmax] Hpos Htimes.
  - apply list.Forall_forall. intros. left. exact Hmin.
  - eapply list.Forall_impl; [eapply events_caps; [exact Hp|exact Hpos| |exact Hmax]|].
    + eapply list.Forall_impl; [exact Htimes|]. intros [event time] [Hne|[Hload _]] issuer He;
        [exact Hne|cbn in Hload, He; congruence].
    + intros result Hcap. right. exact Hcap.
Qed.

Section Removed.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat)
  (ifetch : bool) (vpn : pn).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation mem := (l ++ Ev.Tlbi tlbi rc epoch :: r).
Local Notation short := (l ++ r).

Lemma ptes_exact addr tmin tmax : tmin ≤ tmax → tmax ≤ length mem →
  Memory.read_all_pte addr imem short (g tmin) (g tmax) =
  unshift_ptes p <$> Memory.read_all_pte addr imem mem tmin tmax.
Proof.
  intros Hrange Hbound.
  rewrite (read_all_pte_remove addr imem l r tlbi rc epoch tmin tmax Hrange)
    by (rewrite !length_app in *; cbn in *; lia).
  destruct (Memory.read_all_pte _ _ _ _ _) as [ptes|err]; [|reflexivity]. cbn. f_equal.
  unfold unshift_ptes. rewrite map_map. induction ptes as [|[pte time] ptes IH]; cbn; [reflexivity|].
  rewrite unshift_shift, <- IH. reflexivity.
Qed.

Lemma ptes_exact_window addr tmin tmax : window p tmin tmax → tmax ≤ length mem →
  Memory.read_all_pte addr imem short (g tmin) (g tmax) =
  unshift_ptes p <$> Memory.read_all_pte addr imem mem tmin tmax.
Proof.
  intros Hw Hb. destruct (decide (tmin ≤ tmax)) as [Hrange|Hempty]; [apply ptes_exact; assumption|].
  assert (Hempty' : g tmax < g tmin) by (apply window_compare; [lia|exact Hw|lia]).
  unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw.
  rewrite !decide_False by lia. reflexivity.
Qed.

Lemma filter_ptes P `{∀ x, Decision (P x)} ptes :
  filter (λ '(pte, _), P pte) (unshift_ptes p ptes) =
  unshift_ptes p (filter (λ '(pte, _), P pte) ptes).
Proof.
  induction ptes as [|[pte t] ptes IH]; [reflexivity|]. unfold unshift_ptes in *.
  cbn [map fst snd]. rewrite !filter_cons. case_decide; cbn [map fst snd]; rewrite IH; reflexivity.
Qed.

Lemma leaf_exact fe events tmin tmax : window p tmin tmax → VMCacheOrder.ordered events →
  Forall tpos events → Forall (event_allowed p tmin) events →
  TLB.get_result_from_leaf_FE tid ifetch fe (map_evs g events) (g tmin) (g tmax) =
  map (res_map g) (TLB.get_result_from_leaf_FE tid ifetch fe events tmin tmax).
Proof.
  intros Hwindow Horder Hpos Htimes. unfold TLB.get_result_from_leaf_FE.
  pose proof (window_compare p tmin tmax ltac:(lia) Hwindow) as Hrange.
  destruct (decide (tmax < tmin)); destruct (decide (g tmax < g tmin)); try tauto; try reflexivity.
  exact (events_exact p tid ifetch _ _ events tmin tmax None ltac:(lia) Hwindow Horder Hpos Htimes).
Qed.

Lemma table_exact fe events tmin tmax : tmax ≤ length mem → window p tmin tmax →
  VMCacheOrder.ordered events → Forall tpos events → Forall (event_allowed p tmin) events →
  TLB.get_result_from_table_FE tid imem short ifetch vpn fe (map_evs g events) (g tmin) (g tmax) =
  map (res_map g) <$> TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin tmax.
Proof.
  intros Hbound Hwindow Horder Hpos Htimes. unfold TLB.get_result_from_table_FE.
  pose proof (window_compare p tmin tmax ltac:(lia) Hwindow) as Hrange.
  destruct (decide (tmax < tmin)) as [Hempty|Hnonempty];
    destruct (decide (g tmax < g tmin)); try tauto; try reflexivity.
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|reflexivity].
  rewrite (events_exact p tid ifetch _ _ events tmin tmax None ltac:(lia) Hwindow Horder Hpos Htimes).
  pose proof (events_windows p tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    events tmin tmax None ltac:(lia) Hwindow Hpos Htimes) as Hwindows.
  destruct (TLB.get_results_from_events tid ifetch _ _ events tmin tmax None) as [|result results]; [reflexivity|].
  cbn [map]. rewrite ptes_exact by (try lia; exact Hbound).
  destruct (Memory.read_all_pte _ imem mem tmin tmax) as [ptes|err] eqn:Hread; [|reflexivity].
  cbn [fmap result_fmap mbind result_bind mret result_ret]. f_equal.
  apply (uncacheable_exact p lvl tmin (result :: results) ltac:(lia) Hwindows ptes tmax); [|exact Hwindow].
  apply list.Forall_forall. intros pte Hin. eapply VMSwapRemoveTimes.read_all_pte_avoids; eassumption.
Qed.

Lemma fe_exact fe events tmin_ok tmin_unc tmax : tmax ≤ length mem →
  window p tmin_ok tmax → window p tmin_unc tmax → VMCacheOrder.ordered events → Forall tpos events →
  Forall (event_allowed p tmin_ok) events → Forall (event_allowed p tmin_unc) events →
  TLB.get_result_from_FE tid imem short ifetch vpn fe (map_evs g events) (g tmin_ok) (g tmin_unc) (g tmax) =
  map (res_map g) <$> TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax.
Proof.
  intros Hb Hok Hunc Horder Hpos Heok Heunc. unfold TLB.get_result_from_FE. case_decide.
  - apply table_exact; assumption.
  - cbn. f_equal. apply leaf_exact; assumption.
Qed.

Theorem lookup_exact cache limit upper asid tmin_ok tmin_unc tmax :
  VMCacheState.cache_inv (length mem) cache → pos_cache cache →
  VMSwapRemoveHistory.histories (event_allowed p limit) cache →
  limit ≤ tmin_ok → limit ≤ tmin_unc → tmax ≤ length mem →
  window p tmin_ok tmax → window p tmin_unc tmax →
  res_lift (λ x y, y = res_map g x)
    (TLB.lookup tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid)
    (TLB.lookup tid imem short (tlb_map g cache) ifetch upper vpn (g tmin_ok) (g tmin_unc) (g tmax) asid).
Proof.
  intros [Hgood [Hunique Hvalid]] Hpos Hhist Hlow Hok Hb Hwok Hwunc.
  assert (Hrows : ∀ fe events, (fe, events) ∈
    TLB.get_fes cache (TLB.get_global_Ctxts upper vpn ++ TLB.get_asid_Ctxts upper vpn asid) →
    VMCacheOrder.ordered events ∧ Forall tpos events ∧
      Forall (event_allowed p tmin_ok) events ∧ Forall (event_allowed p tmin_unc) events).
  { intros fe events Hentry. apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [_ Hentry]].
    unfold TLB.VATLB.get_fe in Hentry.
    apply list_elem_of_In, List.in_map_iff in Hentry as [[entry events'] [Heq Hentry]].
    apply list_elem_of_In in Hentry. injection Heq as <- <-.
    pose proof (Hpos ctxt entry events' Hentry) as Hrowpos.
    rewrite <- (VMBBMTransport.row_history cache ctxt entry events' Hunique Hentry) in Hrowpos |- *.
    split; [apply Hgood|]. split; [exact Hrowpos|]. split.
    - apply (VMSwapRemoveHistory.histories_mono p limit tmin_ok cache Hlow Hhist).
    - apply (VMSwapRemoveHistory.histories_mono p limit tmin_unc cache Hok Hhist). }
  rewrite !VMCacheSim.lookup_shape.
  eapply (res_lift_bind (λ row row', row ∈ TLB.get_fes cache
    (TLB.get_global_Ctxts upper vpn ++ TLB.get_asid_Ctxts upper vpn asid) ∧
    row' = (row.1, map_evs g row.2))).
  - apply res_lift_mchoosel. rewrite get_fes_time_map.
    apply CList.Forall2_map_r, Forall2_diag. intros row Hrow. split; [exact Hrow|reflexivity].
  - intros [fe events] row' [Hrow ->]. cbn [fst snd VMCacheSim.fe_res].
    destruct (Hrows fe events Hrow) as (Hord & Htimes & Hallowed & Hallowed').
    eapply (res_lift_bind (λ la lb, lb = map (res_map g) la)).
    + apply res_lift_lift. rewrite fe_exact by assumption.
      destruct (TLB.get_result_from_FE _ _ _ _ _ _ _ _ _ _); reflexivity.
    + intros la lb ->. apply res_lift_mchoosel, VMSwapLookup.Forall2_map_r.
Qed.

Lemma root_exact limit ts upper ttbr0 tmin tmax :
  VMSwapRemoveViews.ts_ok (VMSwapRemoveState.allowed p limit) ts →
  VMSwapRemoveState.allowed p limit tmin → limit ≤ tmax → tmax ≤ length mem →
  res_lift (λ x y, y = res_map g x)
    (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin tmax)
    (VMRootLookupReplay.root_lookup imem short (ts_map g ts) upper vpn ttbr0 (g tmin) (g tmax)).
Proof.
  intros Hts Hmin Hlimit Hb. unfold VMRootLookupReplay.root_lookup.
  assert (Hw : window p tmin tmax) by (eapply window_allowed; [lia|exact Hmin|exact Hlimit]).
  pose proof (window_compare p tmin tmax ltac:(lia) Hw) as Hrange.
  destruct (decide (tmin ≤ tmax)); destruct (decide (g tmin ≤ g tmax));
    try (exfalso; lia); [|split; [constructor|reflexivity]].
  eapply (res_lift_bind (λ vws vws', vws' = map (vv_map g) vws ∧
    Forall (λ vv, VMSwapRemoveState.allowed p limit vv.2) vws)).
  { apply res_lift_lift. destruct upper.
    - rewrite ts_map_read_sreg_indirect.
      destruct (TState.read_sreg_indirect ts TTBR1_EL1) as [vws|] eqn:Hread; cbn; [|reflexivity].
      split; [reflexivity|]. apply list.Forall_forall. intros vv Hin.
      exact (VMSwapRemoveViews.read_sreg_indirect _ ts _ _ Hts Hread vv Hin).
    - cbn. split; [unfold vv_map; cbn; rewrite ?unshift_zero; reflexivity|]. constructor; [|constructor].
      apply VMSwapRemoveState.allowed_zero. lia. }
  intros vws vws' [-> Hviews].
  eapply (res_lift_bind (λ vv vv', vv' = vv_map g vv ∧ VMSwapRemoveState.allowed p limit vv.2)).
  { apply res_lift_mchoosel, CList.Forall2_map_r, Forall2_diag. intros vv Hin. split; [reflexivity|].
    exact (VMViews.Forall_elem _ _ _ Hviews Hin). }
  intros [ttbr vttbr] vv' [-> Hvttbr]. cbn [vv_map fst snd].
  replace (g tmin ⊔ g vttbr) with (g (tmin ⊔ vttbr))
    by (unfold join, join_nat; apply unshift_max).
  eapply (res_lift_bind (λ ptes ptes', ptes' = unshift_ptes p ptes)).
  { apply res_lift_lift. rewrite ptes_exact_window.
    - destruct (Memory.read_all_pte _ imem mem _ tmax); reflexivity.
    - eapply window_allowed; [lia|apply VMSwapRemoveState.allowed_max; eassumption|exact Hlimit].
    - exact Hb. }
  intros ptes ptes' ->. apply res_lift_mchoosel. rewrite filter_ptes.
  induction (filter _ ptes) as [|[pte vpte] ptes'' IH]; cbn [map unshift_ptes fst snd];
    constructor; [|exact IH].
  unfold res_map. cbn. rewrite !unshift_max. reflexivity.
Qed.

Theorem tlb_exact ts upper asid ttbr0 tmin_ok tmin_unc tmax :
  VMViews.ts_ok (length mem) ts → VMSwapRemoveThread.thread_ok p ts → ts_pos ts →
  VMSwapRemoveState.allowed p (TState.vcse ts) tmin_ok →
  VMSwapRemoveState.allowed p (TState.vcse ts) tmin_unc →
  TState.vcse ts ≤ tmin_ok → TState.vcse ts ≤ tmin_unc → TState.vcse ts ≤ tmax → tmax ≤ length mem →
  res_lift (λ x y, y = res_map g x)
    (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax)
    (TState.tlb_lookup tid imem short (ts_map g ts) ifetch upper vpn asid ttbr0 (g tmin_ok) (g tmin_unc) (g tmax)).
Proof.
  intros Hbound [Hviews Hcache] Hpos Hok Hunc Hlow Hlow' Hcap Hb.
  pose proof (root_exact (TState.vcse ts) ts upper ttbr0 tmin_unc tmax Hviews Hunc Hcap Hb) as Hroot.
  rewrite !tlb_lookup_shape, ts_map_tlb.
  destruct (TState.tlb ts) as [cache|] eqn:Hc; cbn [fmap option_fmap option_map];
    [|split; [constructor|reflexivity]].
  assert (Hlookup : res_lift (λ x y, y = res_map g x)
    (TLB.lookup tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid)
    (TLB.lookup tid imem short (tlb_map g cache) ifetch upper vpn (g tmin_ok) (g tmin_unc) (g tmax) asid)).
  { apply (lookup_exact cache (TState.vcse ts));
      [apply (VMViews.ok_cache _ _ Hbound), Hc|apply Hpos, Hc|apply (proj1 (Hcache cache Hc))|
       exact Hlow|exact Hlow'|exact Hb| |]; eapply window_allowed; [lia|exact Hok|exact Hcap|lia|exact Hunc|exact Hcap]. }
  destruct Hlookup as [Hl He], Hroot as [Hr Her]. unfold Exec.merge.
  split; cbn [Exec.results Exec.errors]; [apply Forall2_app; assumption|rewrite He, Her; reflexivity].
Qed.
End Removed.
End VMSwapRemoveLookup.
