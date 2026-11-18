(******************************************************************************)
(* Preserve the complete BBM checker when removing a foreign TLBI            *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMBBMTransport PromiseFirstSailVMCacheOrder
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapBBMTime PromiseFirstSailVMSwapBBMCheck
  PromiseFirstSailVMSwapBBMCache.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapBBMCompress PromiseFirstSailVMSwapBBMMemoryAny.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.
Module VMSwapBBMRemove.
Import VMPromising VMSwapSim VMSwapBBMTime VMSwapBBMCompress VMSwapBBMCheck VMSwapBBMCache VMBBMTransport.
#[local] Typeclasses Transparent Memory.t.

Lemma overlaps_remove p bound mapped a b : 0 < p →
  VMCacheOrder.ordered a → VMCacheOrder.ordered b → Forall (no_invalid p) a → Forall (no_invalid p) b →
  cut (λ _, True) (unshift p) bound mapped →
  BBM.time_overlaps bound a b =
    BBM.time_overlaps mapped (events_map (unshift p) a) (events_map (unshift p) b).
Proof.
  intros Hp Ha Hb Hna Hnb Hcut.
  pose proof (intervals_remove p bound mapped a b Hp Ha Hb Hna Hnb Hcut) as Hrel.
  unfold BBM.time_overlaps. destruct Hrel; reflexivity.
Qed.

Theorem violation_remove imem l r ev addrs ctxt e1 e2 a b : Ev.get_msg ev = None →
  VMCacheOrder.ordered a → VMCacheOrder.ordered b →
  Forall (no_invalid (S (length r))) a → Forall (no_invalid (S (length r))) b →
  BBM.is_bbm_violation imem (l ++ ev :: r) addrs (length (l ++ ev :: r)) ctxt e1 e2 a b =
  BBM.is_bbm_violation imem (l ++ r) addrs (length (l ++ r)) ctxt e1 e2
    (events_map (unshift (S (length r))) a) (events_map (unshift (S (length r))) b).
Proof.
  intros He Ha Hb Hna Hnb.
  assert (Hcut : cut (λ _, True) (unshift (S (length r))) (length (l ++ ev :: r)) (length (l ++ r))).
  { replace (length (l ++ ev :: r)) with (S (length (l ++ r))) by (rewrite !length_app; cbn; lia).
    apply (unshift_all_bound (S (length r)) (S (length (l ++ r)))); [lia|rewrite length_app; lia]. }
  pose proof (intervals_remove (S (length r)) _ _ a b ltac:(lia) Ha Hb Hna Hnb Hcut) as Hintervals.
  pose proof (overlaps_remove (S (length r)) _ _ a b ltac:(lia) Ha Hb Hna Hnb Hcut) as Hoverlap.
  pose proof (intervals_bound (length (l ++ ev :: r)) a b) as Hbounds.
  assert (Hmaps : ∀ lvl oa1 oa2,
    mapM (λ '(lo, hi), BBM.mem_contents_eq_btw imem (l ++ ev :: r) addrs lo hi lvl oa1 oa2)
      (BBM.time_intervals (length (l ++ ev :: r)) a b) =
    mapM (λ '(lo, hi), BBM.mem_contents_eq_btw imem (l ++ r) addrs lo hi lvl oa1 oa2)
      (BBM.time_intervals (length (l ++ r))
        (events_map (unshift (S (length r))) a) (events_map (unshift (S (length r))) b))).
  { intros lvl oa1 oa2. clear Hoverlap.
    induction Hintervals as [|[lo hi] [lo' hi'] xs ys Hrel Htail IH]; [reflexivity|].
    apply Forall_cons_1 in Hbounds as [[Hlo Hhi] Hbounds].
    destruct Hrel as [Heq Hcuts]. cbn in Heq. subst lo'. cbn [mapM].
    rewrite (VMSwapBBMMemoryAny.contents_between_remove imem addrs l r ev lo hi hi' lvl oa1 oa2 He
      ltac:(cbn in Hlo,Hhi; rewrite length_app in Hhi; cbn in Hhi; rewrite length_app; lia) Hcuts),
      (IH Hbounds). reflexivity. }
  unfold BBM.is_bbm_violation. rewrite Hoverlap.
  destruct (decide (is_final (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e1))); [|reflexivity].
  destruct (decide (is_final (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e2))); [|reflexivity].
  match goal with |- context [if negb ?test then _ else _] => destruct (negb test) end; [reflexivity|].
  match goal with |- context [if negb ?test then _ else _] => destruct (negb test) end; [reflexivity|].
  match goal with |- context [if negb ?test then _ else _] => destruct (negb test) end; [reflexivity|].
  destruct (decide (output_prefix (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e1) ≠
    output_prefix (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e2))); [|reflexivity].
  destruct Hintervals; [reflexivity|]. cbn beta iota zeta.
  destruct (decide (allow_write (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e1))); [reflexivity|].
  destruct (decide (allow_write (TLB.Ctxt.lvl ctxt) (TLB.Entry.pte e2))); [reflexivity|].
  rewrite Hmaps. reflexivity.
Qed.

Definition rows (Q : TLB.Entry.events → Prop) (v : TLB.VATLB.t) :=
  ∀ ctxt entry events, (entry, events) ∈ TLB.VATLB.get ctxt v → Q events.

Lemma gdesc_rows Q v query fe events : rows Q v →
  (fe, events) ∈ BBM.gdesc_get query (BBM.global_descendants (TLB.VATLB.entries_by_ctxt v)) → Q events.
Proof.
  intros Hhist Hin. apply gdesc_member in Hin as (ctxt & entries & entry & Hctxt & Hrow & Hrest).
  rewrite <- (ebc_get _ _ _ Hctxt) in Hrow. eapply Hhist; exact Hrow.
Qed.

Lemma conflicts_transport Q f v bound mapped ctxt : rows Q v →
  (∀ a b, Q a → Q b → BBM.time_overlaps bound a b =
    BBM.time_overlaps mapped (events_map f a) (events_map f b)) →
  conflicts (vatlb_map f v) mapped ctxt (TLB.VATLB.get ctxt (vatlb_map f v)) →
  conflicts v bound ctxt (TLB.VATLB.get ctxt v).
Proof.
  intros Hhist Hoverlaps [[entry events] [Hrow [Hfinal Hconflict]]].
  apply row_map_member in Hrow as [old [Hrow ->]].
  pose proof (Hhist ctxt entry old Hrow) as Hold.
  exists (entry, old). split; [exact Hrow|]. split; [exact Hfinal|].
  destruct Hconflict as [[plvl [Hlt [[pe pevs] [Hin [Hpe Hoverlap]]]]]|[[Hasid [glvl [Hle [[ge gevs] [Hin Hoverlap]]]]]|[Hasid [[ge gevs] [Hin Hoverlap]]]]].
  - apply row_map_member in Hin as [other [Hin ->]]. left. exists plvl. split; [exact Hlt|].
    exists (pe, other). split; [exact Hin|]. split; [exact Hpe|].
    rewrite (Hoverlaps old other Hold (Hhist _ _ _ Hin)). exact Hoverlap.
  - apply row_map_member in Hin as [other [Hin ->]]. right; left. split; [exact Hasid|].
    exists glvl. split; [exact Hle|]. exists (ge, other). split; [exact Hin|].
    rewrite (Hoverlaps old other Hold (Hhist _ _ _ Hin)). exact Hoverlap.
  - apply gdesc_map_member in Hin as [other [Hin ->]]. right; right. split; [exact Hasid|].
    exists (ge, other). split; [exact Hin|].
    rewrite (Hoverlaps old other Hold (gdesc_rows Q v _ ge other Hhist Hin)). exact Hoverlap.
Qed.

Theorem check_tlb_transport Q f imem mem mem' addrs cache : rows Q (TLB.vatlb cache) →
  (∀ a b, Q a → Q b → BBM.time_overlaps (length mem) a b =
    BBM.time_overlaps (length mem') (events_map f a) (events_map f b)) →
  (∀ ctxt e1 e2 a b, Q a → Q b →
    BBM.is_bbm_violation imem mem addrs (length mem) ctxt e1 e2 a b =
    BBM.is_bbm_violation imem mem' addrs (length mem') ctxt e1 e2 (events_map f a) (events_map f b)) →
  BBM.check_tlb imem mem addrs cache = Ok false →
  BBM.check_tlb imem mem' addrs (tlb_map f cache) = Ok false.
Proof.
  intros Hhist Hoverlaps Hviolations Hrun. apply check_tlb_false. intro ctxt.
  destruct (proj1 (check_tlb_false _ _ _ _) Hrun ctxt) as [Hpairs Hconflicts].
  rewrite tlb_map_vatlb. split.
  - rewrite vatlb_get_map. unfold pair_check in *.
    rewrite <- (pairs_map (λ '(e1, h1) '(e2, h2),
      negb <$> BBM.is_bbm_violation imem mem addrs (length mem) ctxt e1 e2 h1 h2)
      _ (λ ee, (ee.1, map_evs f ee.2)) (TLB.VATLB.get ctxt (TLB.vatlb cache)));
      [exact Hpairs|].
    intros [e1 h1] [e2 h2] Hrow1 Hrow2. cbn beta iota zeta. rewrite !map_evs_events.
    apply f_equal, Hviolations; [apply (Hhist _ _ _ Hrow1)|apply (Hhist _ _ _ Hrow2)].
  - intro Hbad. apply Hconflicts. eapply conflicts_transport; eassumption.
Qed.

Theorem check_tlb_remove imem l r ev addrs cache : Ev.get_msg ev = None →
  rows (λ events, VMCacheOrder.ordered events ∧ Forall (no_invalid (S (length r))) events)
    (TLB.vatlb cache) →
  BBM.check_tlb imem (l ++ ev :: r) addrs cache = Ok false →
  BBM.check_tlb imem (l ++ r) addrs (tlb_map (unshift (S (length r))) cache) = Ok false.
Proof.
  intros He Hhist. apply (check_tlb_transport
    (λ events, VMCacheOrder.ordered events ∧ Forall (no_invalid (S (length r))) events));
    [exact Hhist| |].
  - intros a b [Ha Hna] [Hb Hnb]. apply overlaps_remove; [lia|exact Ha|exact Hb|exact Hna|exact Hnb|].
    replace (length (l ++ ev :: r)) with (S (length (l ++ r))) by (rewrite !length_app; cbn; lia).
    apply (unshift_all_bound (S (length r)) (S (length (l ++ r)))); [lia|rewrite length_app; lia].
  - intros ctxt e1 e2 a b [Ha Hna] [Hb Hnb]. apply violation_remove; assumption.
Qed.
End VMSwapBBMRemove.
