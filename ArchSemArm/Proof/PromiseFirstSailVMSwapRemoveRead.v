(******************************************************************************)
(* Register reads and translation consumption after removing a TLBI           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveLocal.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveRead.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma iis_add p v iis : iis_map (unshift p) (IIS.add v iis) = IIS.add (unshift p v) (iis_map (unshift p) iis).
Proof. destruct iis. unfold iis_map, IIS.add, set. cbn. rewrite unshift_max. reflexivity. Qed.
Lemma pop_map f tres : IIS.TransRes.pop (trs_map f tres) =
  (λ tv : IIS.TransRes.t * bv 64, (trs_map f tv.1, tv.2)) <$> IIS.TransRes.pop tres.
Proof. unfold IIS.TransRes.pop. destruct tres as [start stop root remaining], remaining; reflexivity. Qed.

Section Map.
Context (p : nat) (Hp : 0 < p).
Local Notation g := (unshift p).
Local Notation R := (pr_rel p).
Definition tsr (a b : TState.t) := b = ts_map g a.

Ltac bind V := eapply (esim_bind _ V); [|let x := fresh "x" in let y := fresh "y" in
  let Hxy := fresh "Hxy" in intros x y Hxy].
Lemma get_ts : esim R tsr (mget fst) (mget fst).
Proof. apply esim_mget. intros a b [Ht _]. exact Ht. Qed.
Lemma get_iis : esim R (λ x y, y = iis_map g x) (mget snd) (mget snd).
Proof. apply esim_mget. intros a b [_ Hi]. exact Hi. Qed.
Lemma set_ts f1 f2 : (∀ ts, f2 (ts_map g ts) = ts_map g (f1 ts)) →
  esim R eq (mset fst f1) (mset fst f2).
Proof.
  intro Hf. apply esim_mset. intros [ta ia] [tb ib] [Ht Hi].
  unfold pr_rel; cbn in *; subst tb ib. split; [apply Hf|reflexivity].
Qed.
Lemma set_iis f1 f2 : (∀ iis, f2 (iis_map g iis) = iis_map g (f1 iis)) →
  esim R eq (mset snd f1) (mset snd f2).
Proof.
  intro Hf. apply esim_mset. intros [ta ia] [tb ib] [Ht Hi].
  unfold pr_rel; cbn in *; subst tb ib. split; [reflexivity|apply Hf].
Qed.
Lemma add v : esim R eq (mset snd (IIS.add v)) (mset snd (IIS.add (g v))).
Proof. apply set_iis. intro. symmetry. apply iis_add. Qed.
Lemma lift_thread {A B} (V : A → B → Prop) m1 m2 : esim tsr V m1 m2 →
  esim R V (Exec.liftSt fst m1) (Exec.liftSt fst m2).
Proof.
  apply esim_liftSt.
  - intros a b [Ht _]. exact Ht.
  - intros [ta ia] [tb ib] ta' tb' [Ht Hi] Ht'. split; assumption.
Qed.

Lemma run_reg_trans_read_sim reg racc trs :
  esim tsr (λ x y, y = vv_map g x) (run_reg_trans_read reg racc trs)
    (run_reg_trans_read reg racc (trs_map g trs)).
Proof using Hp.
  unfold run_reg_trans_read. cbn [trs_map IIS.TransRes.root].
  eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
  eapply (esim_bind _ eq); [apply VMSwapInsert.esim_othrow_map;
    destruct (IIS.TransRes.root trs); cbn; reflexivity || exact I|intros ? ? <-].
  destruct (decide _) as [Heq|];
    [apply esim_ret; unfold vv_map; cbn; rewrite unshift_zero; reflexivity|].
  bind tsr.
  { split; [|apply eerr_nil; reflexivity].
    intros a b a' value Hrel Hrun. apply Exec.elem_of_mGet_inv in Hrun as [-> ->].
    exists b, b. split; [apply Exec.elem_of_mGet|auto]. }
  match goal with Hmap : tsr _ ?mapped |- _ => unfold tsr in Hmap; subst mapped end.
  eapply esim_bind; [apply esim_guard_or_refl|intros ? ? _].
  apply VMSwapInsert.esim_othrow_map. rewrite (VMSwapRemoveMap.map_read_reg p Hp).
  apply VMSwapInsert.option_rel_fmap.
Qed.

Lemma run_reg_general_read_sim reg racc :
  esim R (λ x y, y = vv_map g x) (run_reg_general_read reg racc) (run_reg_general_read reg racc).
Proof using Hp.
  unfold run_reg_general_read. bind tsr; [apply get_ts|]. unfold tsr in Hxy. subst y.
  destruct (decide _); [destruct (decide _)|].
  - apply VMSwapInsert.esim_othrow_map. rewrite ts_map_read_sreg_direct. apply VMSwapInsert.option_rel_fmap.
  - apply VMSwapRemoveLocal.read_sreg_indirect_sim.
  - apply VMSwapInsert.esim_othrow_map. rewrite (VMSwapRemoveMap.map_read_reg p Hp). apply VMSwapInsert.option_rel_fmap.
Qed.

Lemma run_reg_read_sim reg racc : esim R eq (run_reg_read reg racc) (run_reg_read reg racc).
Proof using Hp.
  unfold run_reg_read. bind (λ x y : reg_type reg * view, y = vv_map g x).
  { bind (λ x y, y = iis_map g x); [apply get_iis|]. subst y.
    cbn [iis_map IIS.trs]. destruct (IIS.trs x) as [trs|]; cbn.
    - apply lift_thread, run_reg_trans_read_sim.
    - apply run_reg_general_read_sim. }
  destruct x as [value v]. subst y. cbn [vv_map fst snd].
  bind (@eq unit); [apply add|apply esim_ret; reflexivity].
Qed.

Lemma run_trans_end_sim te : esim R eq (run_trans_end te) (run_trans_end te).
Proof using Hp.
  unfold run_trans_end. bind tsr; [apply get_ts|]. unfold tsr in Hxy. subst y.
  bind (λ x y, y = iis_map g x); [apply get_iis|]. subst y.
  cbn [iis_map IIS.trs]. destruct (IIS.trs x0) as [trs|]; cbn; [|apply esim_throw].
  bind (@eq unit).
  { apply esim_msetv. intros [ta ia] [tb ib] [Ht Hi]. unfold pr_rel; cbn in *; subst tb ib. split; reflexivity. }
  bind (@eq unit); [apply add|].
  bind (@eq unit); [apply set_ts; intro; symmetry; apply (VMSwapRemoveMap.map_vspec p Hp)|].
  destruct (decide _); [apply esim_ret; reflexivity|].
  cbn [ts_map TState.vrd TState.vwr TState.vdmbst TState.vdmb TState.vdsb TState.vcse TState.vacq].
  rewrite (VMSwapRemoveMap.map_ets3 p Hp). unfold join, join_nat.
  repeat first [rewrite (VMSwapRemoveMap.unshift_view_if p Hp)|rewrite <- unshift_max].
  match goal with |- esim _ _ (if ?a <=? ?b then _ else _) _ =>
    destruct (a <=? b) eqn:Hle; [apply Nat.leb_le in Hle|apply esim_discard] end.
  match type of Hle with ?a ≤ ?b =>
    assert (Hle' : (g a <=? g b) = true) by (apply Nat.leb_le, unshift_mono, Hle) end.
  rewrite Hle'. bind (@eq unit); [apply add|apply add].
Qed.
End Map.
Section Removed.
Context (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation PR := (VMSwapRemoveLocal.pp_rel r tlbi rc epoch).
Local Notation RR := (VMSwapRemoveLocal.related r tlbi rc epoch).

Lemma read_pte_exact : esim PR eq read_pte read_pte.
Proof.
  unfold read_pte.
  eapply (esim_bind _ (λ x y : option IIS.TransRes.t, y = trs_map g <$> x)).
  { apply esim_mget. intros a b [_ [_ Hi]]. cbn. rewrite Hi. reflexivity. }
  intros opt opt' ->.
  eapply (esim_bind _ (λ x y, y = trs_map g x)).
  { apply VMSwapInsert.esim_othrow_map, VMSwapInsert.option_rel_fmap. }
  intros trs trs' ->.
  eapply (esim_bind _ (λ x y : IIS.TransRes.t * bv 64, y = (trs_map g x.1, x.2))).
  { apply esim_lift_result.
    - intros [next value] Hrun. rewrite pop_map, Hrun. eexists. split; reflexivity.
    - intros err Hrun. rewrite pop_map, Hrun. eexists. reflexivity. }
  intros [next value] output ->. cbn [fst snd].
  eapply (esim_bind _ eq); [|intros ? ? _; apply esim_ret; reflexivity].
  apply esim_msetv. intros [ta ma ia] [tb mb ib] [Hm [Ht Hi]].
  unfold VMSwapRemoveLocal.pp_rel; cbn in *; subst tb ib. split; [exact Hm|split; reflexivity].
Qed.

Lemma compose {A B} (V : A → B → Prop) m1 m2 m3 : esim PR V m1 m2 →
  esim VMCacheSim.pp_sim eq m2 m3 → esim RR V m1 m3.
Proof.
  intros [Mr Me] [Cr Ce]. split.
  - intros a b a' x Hrel Hrun.
    destruct (related_factor r tlbi rc epoch a b Hrel) as [mid [Hmap Hcache]].
    destruct (Mr a mid a' x Hmap Hrun) as (mid' & y & Hrun' & Hmap' & Hval).
    destruct (Cr mid b mid' y Hcache Hrun') as (b' & z & Hrun'' & Hcache' & <-).
    exists b', y. split; [exact Hrun''|]. split; [eapply related_compose; eassumption|exact Hval].
  - intros a b a' err Hrel Hrun.
    destruct (related_factor r tlbi rc epoch a b Hrel) as [mid [Hmap Hcache]].
    destruct (Me a mid a' err Hmap Hrun) as (mid' & err' & Hrun' & Hmap').
    destruct (Ce mid b mid' err' Hcache Hrun') as (b' & err'' & Hrun'' & Hcache').
    exists b', err''. split; [exact Hrun''|eapply related_compose; eassumption].
Qed.

Theorem read_pte_sim : esim RR eq read_pte read_pte.
Proof. eapply compose; [apply read_pte_exact|apply VMCacheSimOutcome.read_pte_sim]. Qed.

Theorem reg_read_sim reg racc :
  esim RR eq (Exec.liftSt (PPState.state ×× PPState.iis) (run_reg_read reg racc))
    (Exec.liftSt (PPState.state ×× PPState.iis) (run_reg_read reg racc)).
Proof.
  eapply compose.
  - apply VMSwapRemoveLocal.lift_pair, (run_reg_read_sim p ltac:(lia)).
  - apply VMCacheSimOutcome.esim_liftSt_pp, VMCacheSimOutcome.run_reg_read_sim.
Qed.

Theorem trans_end_sim te :
  esim RR eq (Exec.liftSt (PPState.state ×× PPState.iis) (run_trans_end te))
    (Exec.liftSt (PPState.state ×× PPState.iis) (run_trans_end te)).
Proof.
  eapply compose.
  - apply VMSwapRemoveLocal.lift_pair, (run_trans_end_sim p ltac:(lia)).
  - apply VMCacheSimOutcome.esim_liftSt_pp, VMCacheSimOutcome.run_trans_end_sim.
Qed.
End Removed.
End VMSwapRemoveRead.
