(******************************************************************************)
(* Translation-start simulation after removing a foreign TLBI                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveMerge PromiseFirstSailVMSwapRemoveLookup
  PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveThread
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMSwapRemoveLookupViews PromiseFirstSailVMViews.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveLocal.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMCacheSim VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Definition trs_map (f : nat → nat) (trs : IIS.TransRes.t) :=
  IIS.TransRes.make (f (IIS.TransRes.trans_start trs)) (f (IIS.TransRes.trans_end trs))
    (IIS.TransRes.root trs) (IIS.TransRes.remaining trs).
Definition iis_map (f : nat → nat) (iis : IIS.t) :=
  IIS.make (f (IIS.strict iis)) (trs_map f <$> IIS.trs iis) (f <$> IIS.inv_time iis)
    ((λ tb : nat * bool, (f tb.1, tb.2)) <$> IIS.rmw_read iis) (regs_map f (IIS.sreg_reads iis)).

Lemma iis_sreg f reg vv iis :
  iis_map f (IIS.add_sreg_read reg vv iis) = IIS.add_sreg_read reg (vv_map f vv) (iis_map f iis).
Proof.
  unfold iis_map, IIS.add_sreg_read, set. cbn. f_equal.
  unfold regs_map. apply dmap_eq. intro key. rewrite dmap_lookup_map.
  destruct (decide (key = reg)) as [->|Hne].
  - rewrite !dmap_lookup_insert. reflexivity.
  - rewrite !dmap_lookup_insert_ne by congruence. rewrite dmap_lookup_map. reflexivity.
Qed.

Section Map.
Context (p : nat) (Hp : 0 < p).
Local Notation g := (unshift p).
Definition pr_rel (a b : TState.t * IIS.t) := b.1 = ts_map g a.1 ∧ b.2 = iis_map g a.2.

Ltac bind V := eapply (esim_bind _ V); [|let x := fresh "x" in let y := fresh "y" in
  let Hxy := fresh "Hxy" in intros x y Hxy].

Lemma read_sreg_indirect_sim reg racc :
  esim pr_rel (λ x y, y = vv_map g x) (read_sreg_indirect reg racc) (read_sreg_indirect reg racc).
Proof.
  unfold read_sreg_indirect.
  bind (λ x y, y = iis_map g x); [apply esim_mget; intros a b [_ Hi]; exact Hi|]. subst y.
  cbn [iis_map IIS.sreg_reads]. unfold regs_map. rewrite dmap_lookup_map.
  destruct (dmap_lookup reg (IIS.sreg_reads x)) as [vv|] eqn:E; rewrite ?E; cbn;
    [apply esim_ret; reflexivity|].
  bind (λ x y, y = ts_map g x); [apply esim_mget; intros a b [Ht _]; exact Ht|]. subst y.
  bind (λ x y : list (reg_type reg * view), y = map (vv_map g) x).
  { apply VMSwapInsert.esim_othrow_map. rewrite ts_map_read_sreg_indirect. apply VMSwapInsert.option_rel_fmap. }
  subst y. bind (λ x y : reg_type reg * view, y = vv_map g x); [apply VMSwapInsert.esim_mchoosel_map|]. subst y.
  bind (@eq unit); [|apply esim_ret; reflexivity].
  apply esim_mset. intros [ta ia] [tb ib] [Ht Hi]. unfold pr_rel; cbn in *; subst tb ib.
  split; [reflexivity|symmetry; apply iis_sreg].
Qed.

Lemma map_tcohs_before asid offsets inv ts :
  VMSwapRemoveViews.opt_ok (λ t, t ≠ p) inv →
  TState.tcohs_before_inv_time asid offsets inv ts →
  TState.tcohs_before_inv_time asid offsets (g <$> inv) (ts_map g ts).
Proof using Hp.
  destruct inv as [time|]; cbn; [|auto]. intros Htime Hbefore offset Hin.
  unfold TState.get_tcoh in *. cbn [ts_map TState.tcoh].
  rewrite (VMSwapRemoveMap.lookup_total_map p Hp).
  apply (proj2 (unshift_lt_iff_ne p _ time (Htime time eq_refl) Hp)), Hbefore, Hin.
Qed.
End Map.

Section Removed.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Definition pp_rel (a b : PPState.t TState.t Ev.t IIS.t) :=
  (∃ l, PPState.mem a = l ++ e :: r ∧ PPState.mem b = l ++ r) ∧
  PPState.state b = ts_map g (PPState.state a) ∧ PPState.iis b = iis_map g (PPState.iis a).

Lemma set_state (f1 f2 : TState.t → TState.t) :
  (∀ ts, f2 (ts_map g ts) = ts_map g (f1 ts)) →
  esim pp_rel eq (mset PPState.state f1) (mset PPState.state f2).
Proof.
  intro Hf. apply esim_mset. intros [ta ma ia] [tb mb ib] [Hm [Ht Hi]].
  unfold pp_rel; cbn in *; subst tb ib. split; [exact Hm|]. split; [apply Hf|reflexivity].
Qed.
Lemma set_iis (f1 f2 : IIS.t → IIS.t) :
  (∀ iis, f2 (iis_map g iis) = iis_map g (f1 iis)) →
  esim pp_rel eq (mset PPState.iis f1) (mset PPState.iis f2).
Proof.
  intro Hf. apply esim_mset. intros [ta ma ia] [tb mb ib] [Hm [Ht Hi]].
  unfold pp_rel; cbn in *; subst tb ib. split; [exact Hm|]. split; [reflexivity|apply Hf].
Qed.
Lemma lift_pair {A B} (V : A → B → Prop) m1 m2 : esim (pr_rel p) V m1 m2 →
  esim pp_rel V (Exec.liftSt (PPState.state ×× PPState.iis) m1)
    (Exec.liftSt (PPState.state ×× PPState.iis) m2).
Proof.
  apply esim_liftSt.
  - intros a b [_ [Ht Hi]]. split; assumption.
  - intros [ta ma ia] [tb mb ib] [ta' ia'] [tb' ib'] [Hm [Ht Hi]] [Ht' Hi'].
    unfold pp_rel; cbn in *. split; [exact Hm|]. split; assumption.
Qed.

Lemma map_nil {A B} (f : A → B) xs : map f xs = [] ↔ xs = [].
Proof. destruct xs; cbn; split; congruence. Qed.

(** The exclusion invariant and view bounds are needed at entry. Intermediate
    states carry the exact time map, including states where the handler errors. *)
Lemma run_trans_start_exact start a b : pp_rel a b → VMViews.ok a →
  VMSwapRemoveThread.ok p a → VMSwapRemoveStamps.ts_ok p (PPState.state a) → ts_pos (PPState.state a) →
  VMSwapInsert.esim_at pp_rel eq (run_trans_start tid imem start) (run_trans_start tid imem start) a b.
Proof.
  intros Hrel Hbound Hthread Hstamps Hpos. unfold run_trans_start.
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  destruct a as [ts mem iis], b as [ts' mem' iis'].
  destruct Hrel as [[l [Hmem Hmem']] [Hts Hiis]]. cbn in *; subst mem mem' ts' iis'.
  rewrite (VMSwapRemoveMap.map_ets2 p ltac:(lia)).
  cbn [ts_map TState.vcse TState.vdsb TState.vwr TState.vrd iis_map IIS.strict].
  unfold join, join_nat in *.
  repeat first [rewrite (VMSwapRemoveMap.unshift_view_if p ltac:(lia))|rewrite <- unshift_max].
  assert (Hprom : VMSwapRemoveMap.promises_avoid p ts).
  { apply Forall_app. split; [apply Hstamps|apply Hstamps]. }
  assert (Hmin : TState.min_promise (length (l ++ r)) (ts_map g ts) =
    g (TState.min_promise (length (l ++ e :: r)) ts)).
  { apply (VMSwapRemoveMap.map_min_promise p ltac:(lia)).
    rewrite unshift_ge by (rewrite !length_app; cbn; lia).
    rewrite !length_app; cbn; lia. }
  assert (Hminne : TState.min_promise (length (l ++ e :: r)) ts ≠ p).
  { apply (VMSwapRemoveMap.min_promise_avoids p ltac:(lia) (length (l ++ e :: r)) ts);
      [rewrite length_app; cbn; lia|exact Hprom]. }
  rewrite Hmin, <- (unshift_pred p _ Hminne).
  apply VMSwapInsert.esim_at_of.
  2: { split; [exists l; split; reflexivity|split; reflexivity]. }
  eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
  match goal with |- esim _ _ (guard_discard (?vp ≤ ?cp) ≫= _) _ =>
    set (vpre := vp); set (cap := cp) in * end.
  eapply esim_bind; [apply esim_guard_discard; apply unshift_mono|intros Hguard _ _].
  assert (Hvc : TState.vcse ts ≤ vpre) by (unfold vpre; lia).
  assert (Hcap : cap ≤ length (l ++ e :: r)).
  { unfold cap. pose proof (VMSwapInsert.min_promise_le (length (l ++ e :: r)) ts). lia. }
  pose proof Hthread as [[Hviews Hcache] Hivs].
  assert (Hpre : VMSwapRemoveState.allowed p (TState.vcse ts) vpre).
  { unfold vpre. VMViews.facts Hviews; VMViews.facts Hivs. VMSwapRemoveThread.solve_view. }
  match goal with |- context [TState.tlb_lookup _ _ _ _ _ _ _ _ _ _ ?iv _] => set (vinv := iv) in * end.
  assert (Hinv : VMSwapRemoveState.allowed p (TState.vcse ts) vinv).
  { unfold vinv. VMViews.facts Hviews; VMViews.facts Hivs. VMSwapRemoveThread.solve_view. }
  assert (Hvcinv : TState.vcse ts ≤ vinv) by (unfold vinv; lia).
  assert (Hrange : g cap < g vinv ↔ cap < vinv).
  { pose proof (VMSwapRemoveLookup.window_allowed p (TState.vcse ts) vinv cap ltac:(lia) Hinv ltac:(lia)) as Hw.
    pose proof (VMSwapRemoveLookup.window_compare p vinv cap ltac:(lia) Hw). lia. }
  eapply (esim_bind _ (λ a b : IIS.TransRes.t * option nat,
    b.1 = trs_map g a.1 ∧ b.2 = g <$> a.2 ∧ VMSwapRemoveViews.opt_ok (λ t, t ≠ p) a.2)).
  { destruct (is_upper_va _) as [upper|].
    - eapply (esim_bind _ (@eq reg)); [apply (esim_lift_result _ eq); intros; eauto|intros reg reg' <-].
      eapply (esim_bind _ (λ x y : bv 64 * view, y = vv_map g x)).
      { apply lift_pair. exact (read_sreg_indirect_sim p TTBR0_EL1 None). }
      intros [ttbr0 v0] ttbr0' Httbr. subst ttbr0'. cbn [vv_map fst snd].
      eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
      match goal with |- context [TState.tlb_lookup tid imem (l ++ e :: r) ts ?ifc ?up ?vpn ?asid ?t0 _ _ _] =>
        destruct (VMSwapRemoveMerge.tlb_merged_exact tid imem l r tlbi rc epoch ifc up vpn ts asid t0
          vpre vinv cap (proj1 Hbound) (proj1 Hthread) Hpos Hpre Hinv Hvc Hvcinv ltac:(lia) Hcap)
          as [Hresults Herrors];
        assert (Hresultok : Forall (VMSwapRemoveLookupViews.result_ok p (TState.vcse ts))
          (TLB.Result.merge (Exec.results (TState.tlb_lookup tid imem (l ++ e :: r) ts ifc up vpn asid t0 vpre vinv cap))))
          by (apply VMSwapRemoveLookupViews.merge_ok, VMViews.Forall_results; intros result Hin;
              exact (VMSwapRemoveLookupViews.tlb_lookup_ok imem l r tlbi rc epoch tid ts ifc up vpn asid t0
                vpre vinv cap result (proj1 Hbound) (proj1 Hthread) Hpre Hinv Hcap Hin)) end.
      cbn [Exec.results Exec.errors] in Hresults, Herrors.
      apply VMSwapRemoveMerge.Forall2_map_eq in Hresults.
      eapply esim_bind.
      { apply esim_guard_or; cbn [Exec.results Exec.errors]; rewrite Hresults, <- Herrors.
        all: intro Hempty; intros Hr He; apply Hrange; apply Hempty; try exact He.
        all: first [apply map_nil in Hr; exact Hr|rewrite Hr; reflexivity]. }
      intros ? ? _.
      eapply (esim_bind _ (λ x y : TLB.Result.t,
        y = res_map g x ∧ VMSwapRemoveViews.opt_ok (λ t, t ≠ p) (TLB.Result.inv_time x))).
      { apply esim_lift_res.
        - intros result Hin. exists (res_map g result). split.
          + cbn [Exec.results]. rewrite Hresults. apply list_elem_of_fmap. eauto.
          + split; [reflexivity|exact (proj2 (VMViews.Forall_elem _ _ _ Hresultok Hin))].
        - intros err Herr. exists err. cbn [Exec.errors] in Herr |- *. rewrite <- Herrors. exact Herr. }
      intros result result' [-> Hstamp]. cbn [res_map TLB.Result.ttbr TLB.Result.path TLB.Result.tstart TLB.Result.tend TLB.Result.inv_time].
      eapply (esim_bind _ eq); [apply esim_othrow; [intros ? ->; eauto|auto]|intros ? ? <-].
      apply esim_ret. cbn. split; [reflexivity|]. split; [reflexivity|exact Hstamp].
    - apply esim_ret. cbn. split; [reflexivity|]. split; [reflexivity|intros ? Hnone; discriminate]. }
  intros [tres inv] [tres' inv'] [Htres [Hinv' Hstamp]]. cbn in Htres, Hinv', Hstamp; subst tres' inv'.
  cbv beta iota.
  eapply esim_bind; [apply esim_guard_discard; apply (map_tcohs_before p ltac:(lia)); exact Hstamp|intros ? ? _].
  cbn [trs_map IIS.TransRes.trans_start].
  eapply (esim_bind _ eq); [apply set_state; intro; symmetry; apply (VMSwapRemoveMap.map_update_tcohs p ltac:(lia))|intros ? ? _].
  eapply (esim_bind _ eq); [apply set_iis; intro; reflexivity|intros ? ? _].
  apply set_iis; intro; reflexivity.
Qed.
Definition related (a b : PPState.t TState.t Ev.t IIS.t) :=
  (∃ l, PPState.mem a = l ++ e :: r ∧ PPState.mem b = l ++ r) ∧
  VMSwapRemoveRun.ts_rel r (PPState.state a) (PPState.state b) ∧
  PPState.iis b = iis_map g (PPState.iis a).

Lemma related_factor a b : related a b → ∃ mid, pp_rel a mid ∧ VMCacheSim.pp_sim mid b.
Proof.
  destruct a as [ta ma ia], b as [tb mb ib]. intros [Hm [Ht Hi]]. cbn in *.
  exists {| PPState.state := ts_map g ta; PPState.mem := mb; PPState.iis := iis_map g ia |}.
  split; [split; [exact Hm|split; reflexivity]|]. split; [reflexivity|]. split; [symmetry; exact Hi|exact Ht].
Qed.
Lemma related_compose a mid b : pp_rel a mid → VMCacheSim.pp_sim mid b → related a b.
Proof.
  intros [[l [Ha Hmid]] [Ht Hi]] [Hmem [Hiis Hsim]]. split.
  - exists l. split; [exact Ha|rewrite <- Hmem; exact Hmid].
  - split; [unfold VMSwapRemoveRun.ts_rel; rewrite <- Ht; exact Hsim|rewrite <- Hiis; exact Hi].
Qed.

(** Compose exact removal with cache simulation to allow different internal
    cache allocations in the shorter execution. *)
Theorem run_trans_start_sim start a b : related a b → VMViews.ok a →
  VMSwapRemoveThread.ok p a → VMSwapRemoveStamps.ts_ok p (PPState.state a) → ts_pos (PPState.state a) →
  VMSwapInsert.esim_at related eq (run_trans_start tid imem start) (run_trans_start tid imem start) a b.
Proof.
  intros Hrel Hb Hthread Hstamps Hpos. destruct (related_factor a b Hrel) as [mid [Hmap Hcache]].
  destruct (run_trans_start_exact start a mid Hmap Hb Hthread Hstamps Hpos) as [Hr He].
  pose proof (VMCacheSimOutcome.run_trans_start_sim tid imem start) as [Cr Ce].
  split.
  - intros a' x Hrun. destruct (Hr a' x Hrun) as (mid' & y & Hrun' & Hmap' & <-).
    destruct (Cr mid b mid' x Hcache Hrun') as (b' & y & Hrun'' & Hcache' & <-).
    exists b', x. split; [exact Hrun''|]. split; [eapply related_compose; eassumption|reflexivity].
  - intros a' err Hrun. destruct (He a' err Hrun) as (mid' & err' & Hrun' & Hmap').
    destruct (Ce mid b mid' err' Hcache Hrun') as (b' & err'' & Hrun'' & Hcache').
    exists b', err''. split; [exact Hrun''|eapply related_compose; eassumption].
Qed.
End Removed.
End VMSwapRemoveLocal.
