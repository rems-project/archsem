(******************************************************************************)
(* Transport entry-pair BBM checks through timestamp maps                    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMBBM PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapBBMTime PromiseFirstSailVMSwapBBMMemory.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.
Module VMSwapBBMCheck.
Import VMPromising VMSwapSim VMSwapBBMTime VMBBMTransport.
#[local] Typeclasses Transparent Memory.t.

Lemma intervals_bound bound a b :
  Forall (λ pair, pair.1 ≤ pair.2 ∧ pair.2 ≤ bound) (BBM.time_intervals bound a b).
Proof.
  revert bound b. induction a as [|[event1 stamp1] rest1 IH1]; intros bound b; [constructor|].
  revert bound. induction b as [|[event2 stamp2] rest2 IH2]; intro bound.
  - rewrite VMBBMReplay.time_intervals_nil_r. constructor.
  - assert (Hpop1 : Forall (λ pair : nat * nat, pair.1 ≤ pair.2 ∧ pair.2 ≤ bound)
      (BBM.time_intervals (min bound (pred stamp1)) rest1 ((event2, stamp2) :: rest2))).
    { eapply list.Forall_impl; [apply IH1|]. intros [lo hi] [Hlo Hhi]. cbn in *; lia. }
    assert (Hpop2 : Forall (λ pair : nat * nat, pair.1 ≤ pair.2 ∧ pair.2 ≤ bound)
      (BBM.time_intervals (min bound (pred stamp2)) ((event1, stamp1) :: rest1) rest2)).
    { eapply list.Forall_impl; [apply IH2|]. intros [lo hi] [Hlo Hhi]. cbn in *; lia. }
    rewrite intervals_cons. cbn beta iota zeta.
    destruct event1, event2; repeat case_decide; try assumption.
    all: constructor; [cbn; lia|assumption].
Qed.

Lemma mapM_Forall2 {A B C E} (R : A → B → Prop) (f : A → result E C) (g : B → result E C) xs ys :
  Forall2 R xs ys → (∀ x y, R x y → f x = g y) → mapM f xs = mapM g ys.
Proof. intros Hrel Hfg. induction Hrel; [reflexivity|]. cbn. rewrite (Hfg _ _ H), IHHrel. reflexivity. Qed.

Theorem violation_transport P f imem mem mem' addrs bound mapped ctxt e1 e2 a b :
  order_on P f → Forall (λ event, P event.2) a → Forall (λ event, P event.2) b →
  cut P f bound mapped →
  (∀ lo hi hi' lvl oa1 oa2, P lo → lo ≤ hi → hi ≤ bound → cut P f hi hi' →
    BBM.mem_contents_eq_btw imem mem addrs lo hi lvl oa1 oa2 =
    BBM.mem_contents_eq_btw imem mem' addrs (f lo) hi' lvl oa1 oa2) →
  BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 a b =
  BBM.is_bbm_violation imem mem' addrs mapped ctxt e1 e2 (events_map f a) (events_map f b).
Proof.
  intros Horder Ha Hb Hcut Hcontents.
  pose proof (intervals_transport P f bound mapped a b Horder Ha Hb Hcut) as Hintervals.
  pose proof (overlaps P f bound mapped a b Horder Ha Hb Hcut) as Hoverlap.
  pose proof (intervals_bound bound a b) as Hbounds.
  assert (Hmaps : ∀ lvl oa1 oa2,
    mapM (λ '(lo, hi), BBM.mem_contents_eq_btw imem mem addrs lo hi lvl oa1 oa2)
      (BBM.time_intervals bound a b) =
    mapM (λ '(lo, hi), BBM.mem_contents_eq_btw imem mem' addrs lo hi lvl oa1 oa2)
      (BBM.time_intervals mapped (events_map f a) (events_map f b))).
  { intros lvl oa1 oa2. clear Hoverlap.
    induction Hintervals as [|[lo hi] [lo' hi'] xs ys Hrel Htail IH]; [reflexivity|].
    apply Forall_cons_1 in Hbounds as [[Hlo Hhi] Hbounds].
    destruct Hrel as [HP [Heq Hcuts]]. cbn in *. subst lo'. cbn [mapM].
    rewrite (Hcontents lo hi hi' lvl oa1 oa2 HP Hlo Hhi Hcuts), (IH Hbounds). reflexivity. }
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

Corollary violation_insert imem l r ev addrs ctxt e1 e2 a b : Ev.get_msg ev = None →
  BBM.is_bbm_violation imem (l ++ r) addrs (length (l ++ r)) ctxt e1 e2 a b =
  BBM.is_bbm_violation imem (l ++ ev :: r) addrs (length (l ++ ev :: r)) ctxt e1 e2
    (events_map (shift (S (length r))) a) (events_map (shift (S (length r))) b).
Proof.
  intro He. replace (length (l ++ ev :: r)) with (S (length (l ++ r))) by (rewrite !length_app; cbn; lia).
  apply (violation_transport (λ _, True));
    [apply shift_order; lia|apply Forall_forall; intros; exact I|
     apply Forall_forall; intros; exact I|apply shift_bound; rewrite length_app; lia|].
  intros lo hi hi' lvl oa1 oa2 _ Hlo Hhi Hcut. symmetry.
  apply VMSwapBBMMemory.contents_between_insert; [exact He| |exact Hcut].
  apply (shift_bound (S (length r)) (length (l ++ r)) ltac:(rewrite length_app; lia) lo I). lia.
Qed.

Corollary violation_remove imem l r ev addrs ctxt e1 e2 a b : Ev.get_msg ev = None →
  Forall (λ event, event.2 ≠ S (length r)) a → Forall (λ event, event.2 ≠ S (length r)) b →
  BBM.is_bbm_violation imem (l ++ ev :: r) addrs (length (l ++ ev :: r)) ctxt e1 e2 a b =
  BBM.is_bbm_violation imem (l ++ r) addrs (length (l ++ r)) ctxt e1 e2
    (events_map (unshift (S (length r))) a) (events_map (unshift (S (length r))) b).
Proof.
  intros He Ha Hb.
  replace (length (l ++ ev :: r)) with (S (length (l ++ r))) by (rewrite !length_app; cbn; lia).
  apply (violation_transport (λ t, t ≠ S (length r)));
    [apply unshift_order; lia|exact Ha|exact Hb| |].
  - apply (unshift_bound (S (length r)) (S (length (l ++ r)))); [lia|rewrite length_app; lia].
  - intros lo hi hi' lvl oa1 oa2 Hne Hlo Hhi Hcut.
    apply VMSwapBBMMemory.contents_between_remove; [exact He|exact Hne|lia|exact Hcut].
Qed.
End VMSwapBBMCheck.
