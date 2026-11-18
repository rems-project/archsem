(******************************************************************************)
(* Fresh events and fulfillment after removing a foreign TLBI                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMSwapSim
  PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapRemove
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveMap PromiseFirstSailVMSwapRemoveLocal
  PromiseFirstSailVMSwapRemoveRead PromiseFirstSailVMSwapRemoveCSE PromiseFirstSailVMSwapRemoveTimes
  PromiseFirstSailVMSwapRemoveStamps PromiseFirstSailVMViews.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveEffects.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma stamps_promises p ts : VMSwapRemoveStamps.ts_ok p ts → VMSwapRemoveMap.promises_avoid p ts.
Proof. intro Hts. apply Forall_app. split; [apply Hts|apply Hts]. Qed.

Section Removed.
Context (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation RR := (related r tlbi rc epoch).

Definition effect_rel (a b : PPState.t TState.t Ev.t IIS.t) := RR a b ∧
  VMSwapRemoveStamps.ts_ok p (PPState.state a) ∧ VMSwapRemoveStamps.iis_ok p (PPState.iis a).
Local Notation R := effect_rel.

Lemma get_state : esim R (λ x y, ts_rel r x y ∧ VMSwapRemoveStamps.ts_ok p x)
  (mget PPState.state) (mget PPState.state).
Proof. apply esim_mget. intros a b [[_ [Ht _]] [Hts _]]. split; assumption. Qed.
Lemma get_strict : esim R (λ x y : nat, y = g x)
  (mget (IIS.strict ∘ PPState.iis)) (mget (IIS.strict ∘ PPState.iis)).
Proof. apply esim_mget. intros a b [[_ [_ Hi]] _]. cbn [compose]. rewrite Hi. reflexivity. Qed.
Lemma get_iis : esim R (λ x y, y = iis_map g x ∧ VMSwapRemoveStamps.iis_ok p x)
  (mget PPState.iis) (mget PPState.iis).
Proof. apply esim_mget. intros a b [[_ [_ Hi]] [_ Hii]]. split; assumption. Qed.
Lemma get_mem : esim R (λ x y, ∃ l, x = l ++ e :: r ∧ y = l ++ r) (mget PPState.mem) (mget PPState.mem).
Proof. apply esim_mget. intros a b [[Hm _] _]. exact Hm. Qed.
Lemma get_inv : esim R (λ x y : option nat, y = g <$> x ∧ (∀ t, x = Some t → t ≠ p))
  (mget (IIS.inv_time ∘ PPState.iis)) (mget (IIS.inv_time ∘ PPState.iis)).
Proof.
  apply esim_mget. intros a b [[_ [_ Hi]] [_ Hii]]. cbn [compose].
  split; [rewrite Hi; reflexivity|apply Hii].
Qed.
Lemma get_rmw : esim R (λ x y : option (nat * bool), y = (λ tb, (g tb.1, tb.2)) <$> x)
  (mget (IIS.rmw_read ∘ PPState.iis)) (mget (IIS.rmw_read ∘ PPState.iis)).
Proof. apply esim_mget. intros a b [[_ [_ Hi]] _]. cbn [compose]. rewrite Hi. reflexivity. Qed.

Lemma fulfill_remove l ev proms : Forall (λ t, t ≠ p) proms →
  Memory.fulfill ev (map g proms) (l ++ r) = g <$> Memory.fulfill ev proms (l ++ e :: r).
Proof.
  intro Hproms.
  assert (Hfactor : map (shift p) (map g proms) = proms).
  { induction Hproms as [|time proms Htime Hproms IH]; cbn; [reflexivity|].
    rewrite shift_unshift by (try lia; exact Htime). f_equal. exact IH. }
  pose proof (fulfill_insert_tlbi l r tlbi rc epoch ev (map g proms)) as Hfulfill.
  rewrite Hfactor in Hfulfill. rewrite Hfulfill.
  destruct (Memory.fulfill ev (map g proms) (l ++ r)); cbn; [rewrite unshift_shift|]; reflexivity.
Qed.

Lemma set_state ta tb : ts_rel r ta tb → VMSwapRemoveStamps.ts_ok p ta →
  esim R eq (msetv PPState.state ta) (msetv PPState.state tb).
Proof.
  intros Hmap Hstamp. apply esim_msetv. intros [a ma ia] [b mb ib] [[Hm [_ Hi]] [_ Hinv]].
  unfold effect_rel, related; cbn in *. split; [split; [exact Hm|split; assumption]|split; assumption].
Qed.
Lemma update_state f1 f2 : (∀ ts, VMSwapRemoveStamps.ts_ok p ts → f2 (ts_map g ts) = ts_map g (f1 ts)) →
  (∀ ts cache, f2 (setv TState.tlb cache ts) = setv TState.tlb cache (f2 ts)) →
  (∀ ts, TState.tlb (f2 ts) = TState.tlb ts) →
  (∀ ts, VMSwapRemoveStamps.ts_ok p ts → VMSwapRemoveStamps.ts_ok p (f1 ts)) →
  esim R eq (mset PPState.state f1) (mset PPState.state f2).
Proof.
  intros Hmap Hcomm Htlb Hstamp. apply esim_mset.
  intros [ta ma ia] [tb mb ib] [[Hm [Ht Hi]] [Hts Hii]].
  unfold effect_rel, related; cbn in *. split; [split; [exact Hm|split; [|exact Hi]]|split; [apply Hstamp, Hts|exact Hii]].
  unfold ts_rel. rewrite <- (Hmap ta Hts). destruct Ht as [Hshape Hsim]. split.
  - rewrite Htlb. transitivity (f2 (setv TState.tlb (TState.tlb tb) (ts_map g ta))).
    + apply f_equal, Hshape.
    + apply Hcomm.
  - rewrite !Htlb. exact Hsim.
Qed.
Lemma set_iis f1 f2 : (∀ iis, f2 (iis_map g iis) = iis_map g (f1 iis)) →
  (∀ iis, VMSwapRemoveStamps.iis_ok p iis → VMSwapRemoveStamps.iis_ok p (f1 iis)) →
  esim R eq (mset PPState.iis f1) (mset PPState.iis f2).
Proof.
  intros Hmap Hstamp. apply esim_mset.
  intros [ta ma ia] [tb mb ib] [[Hm [Ht Hi]] [Hts Hii]].
  unfold effect_rel, related; cbn in *. split; [split; [exact Hm|split; [exact Ht|rewrite Hi; apply Hmap]]|].
  split; [exact Hts|apply Hstamp, Hii].
Qed.

Lemma promise_rel ev a b : R a b →
  R (setv PPState.mem (ev :: PPState.mem a) a) (setv PPState.mem (ev :: PPState.mem b) b).
Proof.
  destruct a as [ta ma ia], b as [tb mb ib]. intros [[[l [Hm Hm']] [Ht Hi]] Hstamps]. cbn in *.
  unfold effect_rel, related; cbn. split; [split; [exists (ev :: l); cbn; split; congruence|split; assumption]|exact Hstamps].
Qed.

Lemma promise_at {A B} (V : A → B → Prop) ev l a b
    (k1 : nat → Memory.t → Exec.t (PPState.t TState.t Ev.t IIS.t) string A)
    (k2 : nat → Memory.t → Exec.t (PPState.t TState.t Ev.t IIS.t) string B) :
  R a b → PPState.mem a = l ++ e :: r →
  VMSwapInsert.esim_at R V (k1 (S (length (l ++ e :: r))) (ev :: l ++ e :: r))
    (k2 (g (S (length (l ++ e :: r)))) (ev :: l ++ r))
    (setv PPState.mem (ev :: PPState.mem a) a) (setv PPState.mem (ev :: PPState.mem b) b) →
  VMSwapInsert.esim_at R V
    (time ← Exec.liftSt PPState.mem (Memory.promise ev); mem ← mget PPState.mem; k1 time mem)
    (time ← Exec.liftSt PPState.mem (Memory.promise ev); mem ← mget PPState.mem; k2 time mem) a b.
Proof.
  intros Hrel Hmem Hk.
  assert (Hshort : PPState.mem b = l ++ r).
  { destruct Hrel as [[[prefix [Ha Hb]] _] _]. rewrite Hmem in Ha. apply (app_inv_tail _ _ _) in Ha. subst prefix. exact Hb. }
  assert (Htime : S (length (l ++ r)) = g (S (length (l ++ e :: r)))).
  { rewrite unshift_ge by (rewrite !length_app; cbn; lia). rewrite !length_app; cbn; lia. }
  eapply (VMSwapInsert.esim_at_bind _ (λ x y : nat, x = S (length (l ++ e :: r)) ∧ y = g x)).
  - split.
    + intros a' time Hrun. apply VMSwapInsert.promise_lift_inv in Hrun as [-> ->].
      exists (setv PPState.mem (ev :: PPState.mem b) b), (S (length (PPState.mem b))).
      split; [apply VMSwapInsert.promise_lift_intro|]. split; [apply promise_rel, Hrel|].
      rewrite Hmem, Hshort. split; [reflexivity|exact Htime].
    + intros a' err Hrun. rewrite VMSwapInsert.promise_lift_errors in Hrun. inversion Hrun.
  - intros a' b' time time' Ha Hb Hr [Ht Ht'].
    apply VMSwapInsert.promise_lift_inv in Ha as [-> ->].
    apply VMSwapInsert.promise_lift_inv in Hb as [-> ->].
    apply VMSwapInsert.esim_at_mget; [exact Hr|].
    unfold setv in Hk |- *. rewrite !VMViews.mem_set_mem.
    rewrite Hmem, Hshort, Htime. rewrite Hmem, Hshort in Hk. exact Hk.
Qed.
Theorem fresh_event_map {A B} (V : A → B → Prop) (f1 : nat → A) (f2 : nat → B)
    tid imem l ev a b : (∀ t, t ≠ p → V (f1 t) (f2 (g t))) →
  R a b → PPState.mem a = l ++ e :: r →
  ts_inv imem r tlbi rc epoch l (PPState.state a) →
  VMSwapInsert.esim_at R V
    (time ← Exec.liftSt PPState.mem (Memory.promise ev); mem ← mget PPState.mem;
     nts ← mlift (TState.process_event tid imem mem ev (PPState.state a));
     msetv PPState.state nts;; mret (f1 time))
    (time ← Exec.liftSt PPState.mem (Memory.promise ev); mem ← mget PPState.mem;
     nts ← mlift (TState.process_event tid imem mem ev (PPState.state b));
     msetv PPState.state nts;; mret (f2 time)) a b.
Proof.
  intros Hvalue Hrel Hmem Hcache. pose proof (proj1 (proj2 (proj1 Hrel))) as Hts.
  apply (promise_at _ ev l a b); [exact Hrel|exact Hmem|].
  apply VMSwapInsert.esim_at_of; [|apply promise_rel, Hrel].
  eapply (esim_bind _ (λ x y, ts_rel r x y ∧ VMSwapRemoveStamps.ts_ok p x)).
  - apply esim_lift_result.
    + intros ts' Hrun.
      destruct (process_event_remove tid imem r tlbi rc epoch l ev _ _ ts' Hts Hcache Hrun)
        as (short' & Hshort & Hrel' & Hcache').
      exists short'. split; [exact Hshort|]. split; [exact Hrel'|].
      eapply VMSwapRemoveStamps.process_event; [apply Hrel|exact Hrun].
    + intros err Hrun. exact (process_event_remove_err tid imem r tlbi rc epoch l ev _ _ err Hts Hrun).
  - intros ts' short' [Hmap Hstamps]. eapply (esim_bind _ eq); [apply set_state; assumption|intros ? ? _].
    apply esim_ret, Hvalue. rewrite length_app; cbn; lia.
Qed.
End Removed.
End VMSwapRemoveEffects.
