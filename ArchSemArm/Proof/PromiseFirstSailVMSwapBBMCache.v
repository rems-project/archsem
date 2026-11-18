(******************************************************************************)
(* Transport the complete BBM checker through timestamp maps                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapBBMTime PromiseFirstSailVMSwapBBMMemory.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapBBMCheck.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.
Module VMSwapBBMCache.
Import VMPromising VMSwapSim VMSwapBBMTime VMSwapBBMCheck VMBBMTransport.
#[local] Typeclasses Transparent Memory.t.

Definition histories (P : nat → Prop) (v : TLB.VATLB.t) :=
  ∀ ctxt entry events, (entry, events) ∈ TLB.VATLB.get ctxt v → Forall (λ ev, P ev.2) events.

Lemma map_evs_events f events : map_evs f events = events_map f events.
Proof. unfold map_evs, events_map. apply map_ext. intros []; reflexivity. Qed.

Lemma row_map_member f v ctxt entry events :
  (entry, events) ∈ TLB.VATLB.get ctxt (vatlb_map f v) ↔
  ∃ old, (entry, old) ∈ TLB.VATLB.get ctxt v ∧ events = events_map f old.
Proof.
  rewrite vatlb_get_map. split.
  - intro H. apply list_elem_of_fmap in H as [[e h] [Heq Hin]]. cbn in Heq.
    injection Heq as -> ->. exists h. split; [exact Hin|apply map_evs_events].
  - intros [old [Hin ->]]. apply list_elem_of_fmap. exists (entry, old).
    split; [change ((entry, events_map f old) = (entry, map_evs f old)); rewrite map_evs_events; reflexivity|exact Hin].
Qed.

Lemma gdesc_map_member f v query fe events :
  (fe, events) ∈ BBM.gdesc_get query (BBM.global_descendants (TLB.VATLB.entries_by_ctxt (vatlb_map f v))) ↔
  ∃ old, (fe, old) ∈ BBM.gdesc_get query (BBM.global_descendants (TLB.VATLB.entries_by_ctxt v)) ∧
    events = events_map f old.
Proof.
  split.
  - intro Hin. apply gdesc_member in Hin as (ctxt & entries & entry & Hctxt & Hrow & Hfe & Hdesc).
    rewrite <- (ebc_get _ _ _ Hctxt) in Hrow.
    apply row_map_member in Hrow as [old [Hrow ->]]. exists old. split; [|reflexivity].
    apply gdesc_member. exists ctxt, (TLB.VATLB.get ctxt v), entry.
    split; [apply ebc_get_nonempty; intro Hnil; rewrite Hnil in Hrow; inversion Hrow|auto].
  - intros [old [Hin ->]]. apply gdesc_member in Hin as (ctxt & entries & entry & Hctxt & Hrow & Hfe & Hdesc).
    rewrite <- (ebc_get _ _ _ Hctxt) in Hrow.
    assert (Hrow' : (entry, events_map f old) ∈ TLB.VATLB.get ctxt (vatlb_map f v)).
    { apply row_map_member. exists old. auto. }
    apply gdesc_member. exists ctxt, (TLB.VATLB.get ctxt (vatlb_map f v)), entry.
    split; [apply ebc_get_nonempty; intro Hnil; rewrite Hnil in Hrow'; inversion Hrow'|auto].
Qed.

Lemma gdesc_histories P v query fe events : histories P v →
  (fe, events) ∈ BBM.gdesc_get query (BBM.global_descendants (TLB.VATLB.entries_by_ctxt v)) →
  Forall (λ ev, P ev.2) events.
Proof.
  intros Hhist Hin. apply gdesc_member in Hin as (ctxt & entries & entry & Hctxt & Hrow & Hrest).
  rewrite <- (ebc_get _ _ _ Hctxt) in Hrow. eapply Hhist; exact Hrow.
Qed.

Lemma conflicts_map P f v bound mapped ctxt : histories P v → order_on P f → cut P f bound mapped →
  conflicts (vatlb_map f v) mapped ctxt (TLB.VATLB.get ctxt (vatlb_map f v)) →
  conflicts v bound ctxt (TLB.VATLB.get ctxt v).
Proof.
  intros Hhist Horder Hcut [[entry events] [Hrow [Hfinal Hconflict]]].
  apply row_map_member in Hrow as [old [Hrow ->]].
  pose proof (Hhist ctxt entry old Hrow) as Hold.
  exists (entry, old). split; [exact Hrow|]. split; [exact Hfinal|].
  destruct Hconflict as [[plvl [Hlt [[pe pevs] [Hin [Hpe Hoverlap]]]]]|[[Hasid [glvl [Hle [[ge gevs] [Hin Hoverlap]]]]]|[Hasid [[ge gevs] [Hin Hoverlap]]]]].
  - apply row_map_member in Hin as [other [Hin ->]]. left. exists plvl. split; [exact Hlt|].
    exists (pe, other). split; [exact Hin|]. split; [exact Hpe|].
    rewrite (overlaps P f bound mapped old other Horder Hold (Hhist _ _ _ Hin) Hcut). exact Hoverlap.
  - apply row_map_member in Hin as [other [Hin ->]]. right; left. split; [exact Hasid|].
    exists glvl. split; [exact Hle|]. exists (ge, other). split; [exact Hin|].
    rewrite (overlaps P f bound mapped old other Horder Hold (Hhist _ _ _ Hin) Hcut). exact Hoverlap.
  - apply gdesc_map_member in Hin as [other [Hin ->]]. right; right. split; [exact Hasid|].
    exists (ge, other). split; [exact Hin|].
    rewrite (overlaps P f bound mapped old other Horder Hold (gdesc_histories P v _ ge other Hhist Hin) Hcut).
    exact Hoverlap.
Qed.

Lemma mapM_map_ext {A B C E} (f : A → result E C) (g : B → result E C) h xs :
  (∀ x, x ∈ xs → f x = g (h x)) → mapM f xs = mapM g (map h xs).
Proof.
  induction xs as [|x xs IH]; intro H; [reflexivity|]. cbn [mapM map].
  rewrite (H x ltac:(left)), IH; [reflexivity|]. intros y Hin. apply H. right; exact Hin.
Qed.
Lemma pairs_map {A B} (f : A → A → result string bool) (g : B → B → result string bool) h xs :
  (∀ x y, x ∈ xs → y ∈ xs → f x y = g (h x) (h y)) →
  BBM.for_all_pairs f xs = BBM.for_all_pairs g (map h xs).
Proof.
  induction xs as [|x xs IH]; intro H; [reflexivity|]. cbn [BBM.for_all_pairs map].
  rewrite (mapM_map_ext (f x) (g (h x)) h xs);
    [|intros y Hy; apply H; [left|right; exact Hy]].
  rewrite IH; [reflexivity|]. intros a b Ha Hb. apply H; right; assumption.
Qed.

Theorem check_tlb_map P f imem mem mem' addrs cache :
  histories P (TLB.vatlb cache) → order_on P f → cut P f (length mem) (length mem') →
  (∀ lo hi hi' lvl oa1 oa2, P lo → lo ≤ hi → hi ≤ length mem → cut P f hi hi' →
    BBM.mem_contents_eq_btw imem mem addrs lo hi lvl oa1 oa2 =
    BBM.mem_contents_eq_btw imem mem' addrs (f lo) hi' lvl oa1 oa2) →
  BBM.check_tlb imem mem addrs cache = Ok false →
  BBM.check_tlb imem mem' addrs (tlb_map f cache) = Ok false.
Proof.
  intros Hhist Horder Hcut Hcontents Hrun. apply check_tlb_false. intro ctxt.
  destruct (proj1 (check_tlb_false _ _ _ _) Hrun ctxt) as [Hpairs Hconflicts].
  rewrite tlb_map_vatlb. split.
  - rewrite vatlb_get_map. unfold pair_check in *.
    rewrite <- (pairs_map (λ '(e1, h1) '(e2, h2),
      negb <$> BBM.is_bbm_violation imem mem addrs (length mem) ctxt e1 e2 h1 h2)
      _ (λ ee, (ee.1, map_evs f ee.2)) (TLB.VATLB.get ctxt (TLB.vatlb cache)));
      [exact Hpairs|].
    intros [e1 h1] [e2 h2] Hrow1 Hrow2. cbn beta iota zeta. rewrite !map_evs_events.
    apply f_equal. apply (violation_transport P f);
      [exact Horder|apply (Hhist _ _ _ Hrow1)|apply (Hhist _ _ _ Hrow2)|exact Hcut|exact Hcontents].
  - intro Hbad. apply Hconflicts. eapply conflicts_map; eassumption.
Qed.
Corollary check_tlb_insert imem l r ev addrs cache : Ev.get_msg ev = None →
  BBM.check_tlb imem (l ++ r) addrs cache = Ok false →
  BBM.check_tlb imem (l ++ ev :: r) addrs (tlb_map (shift (S (length r))) cache) = Ok false.
Proof.
  intro He. apply (check_tlb_map (λ _, True)).
  - intros ctxt entry events Hin. apply Forall_forall. intros; exact I.
  - apply shift_order; lia.
  - replace (length (l ++ ev :: r)) with (S (length (l ++ r))) by (rewrite !length_app; cbn; lia).
    apply shift_bound. rewrite length_app; lia.
  - intros lo hi hi' lvl oa1 oa2 _ Hlo Hhi Hcut. symmetry.
    apply VMSwapBBMMemory.contents_between_insert; [exact He| |exact Hcut].
    apply (shift_bound (S (length r)) (length (l ++ r)) ltac:(rewrite length_app; lia) lo I). lia.
Qed.

(** Removal here requires that all cache timestamps avoid the removed slot.
    Reachable CSE-created loads may occupy it; transporting those histories
    requires a separate extension of the interval argument. *)
Corollary check_tlb_remove_unused imem l r ev addrs cache : Ev.get_msg ev = None →
  histories (λ t, t ≠ S (length r)) (TLB.vatlb cache) →
  BBM.check_tlb imem (l ++ ev :: r) addrs cache = Ok false →
  BBM.check_tlb imem (l ++ r) addrs (tlb_map (unshift (S (length r))) cache) = Ok false.
Proof.
  intros He Hhist. apply (check_tlb_map (λ t, t ≠ S (length r))).
  - exact Hhist.
  - apply unshift_order; lia.
  - replace (length (l ++ ev :: r)) with (S (length (l ++ r))) by (rewrite !length_app; cbn; lia).
    apply (unshift_bound (S (length r)) (S (length (l ++ r)))); [lia|rewrite length_app; lia].
  - intros lo hi hi' lvl oa1 oa2 Hne Hlo Hhi Hcut.
    apply VMSwapBBMMemory.contents_between_remove; [exact He|exact Hne| |exact Hcut].
    rewrite !length_app in Hhi |- *. cbn in Hhi. lia.
Qed.
End VMSwapBBMCache.
