(******************************************************************************)
(* BBM intervals under insertion or removal of an unused timestamp             *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMBBM PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMSwapSim.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMSwapBBMTime.
Definition events_map (f : nat → nat) (events : TLB.Entry.events) :=
  map (λ '(event, stamp), (event, f stamp)) events.
(** A bound can lie in a gap introduced by timestamp insertion. Comparing
    all used timestamps with that bound is enough for the interval traversal,
    including its predecessor clamps at invalidation events. *)
Definition cut (P : nat → Prop) f bound mapped := ∀ t, P t → (t ≤ bound ↔ f t ≤ mapped).
Definition order_on (P : nat → Prop) f :=
  (∀ t, P t → (f t = 0 ↔ t = 0)) ∧
  (∀ t u, P t → P u → (f t ≤ f u ↔ t ≤ u)).

Lemma cut_pred P f bound mapped stamp : order_on P f → cut P f bound mapped → P stamp →
  cut P f (min bound (pred stamp)) (min mapped (pred (f stamp))).
Proof.
  intros [Hzero Hle] Hcut Hstamp t Ht. specialize (Hcut t Ht).
  specialize (Hle stamp t Hstamp Ht).
  pose proof (Hzero stamp Hstamp). pose proof (Hzero t Ht). lia.
Qed.
Lemma cut_max P f bound mapped x y : cut P f bound mapped → P x → P y →
  (max x y ≤ bound ↔ max (f x) (f y) ≤ mapped).
Proof. intros Hcut Hx Hy. pose proof (Hcut x Hx). pose proof (Hcut y Hy). lia. Qed.

Lemma allowed_max (P : nat → Prop) x y : P x → P y → P (max x y).
Proof. intros Hx Hy. destruct (le_dec x y); [rewrite Nat.max_r|rewrite Nat.max_l]; auto; lia. Qed.
Lemma map_max P f x y : order_on P f → P x → P y → f (max x y) = max (f x) (f y).
Proof.
  intros [_ Ho] Hx Hy. pose proof (Ho x y Hx Hy).
  destruct (le_dec x y); [rewrite !Nat.max_r|rewrite !Nat.max_l]; lia.
Qed.
Definition interval_related P f (a b : nat * nat) := P a.1 ∧ b.1 = f a.1 ∧ cut P f a.2 b.2.

Theorem intervals_transport P f bound mapped a b : order_on P f →
  Forall (λ e, P e.2) a → Forall (λ e, P e.2) b → cut P f bound mapped →
  Forall2 (interval_related P f) (BBM.time_intervals bound a b)
    (BBM.time_intervals mapped (events_map f a) (events_map f b)).
Proof.
  intros Horder. revert bound mapped b.
  induction a as [|[event1 stamp1] rest1 IH1]; intros bound mapped b Ha Hb Hcut.
  - constructor.
  - apply Forall_cons_1 in Ha as [Hstamp1 Hrest1]. cbn in Hstamp1.
    revert bound mapped Hb Hcut. induction b as [|[event2 stamp2] rest2 IH2]; intros bound mapped Hb Hcut.
    + rewrite !VMBBMReplay.time_intervals_nil_r. constructor.
    + apply Forall_cons_1 in Hb as [Hstamp2 Hrest2]. cbn in Hstamp2.
      assert (Hb : Forall (λ e : TLB.Entry.event * nat, P e.2) ((event2, stamp2) :: rest2))
        by (constructor; assumption).
      pose proof (IH1 (min bound (pred stamp1)) (min mapped (pred (f stamp1)))
        ((event2, stamp2) :: rest2) Hrest1 Hb (cut_pred P f bound mapped stamp1 Horder Hcut Hstamp1)) as Hpop1.
      pose proof (IH2 (min bound (pred stamp2)) (min mapped (pred (f stamp2)))
        Hrest2 (cut_pred P f bound mapped stamp2 Horder Hcut Hstamp2)) as Hpop2.
      pose proof (proj2 Horder stamp2 stamp1 Hstamp2 Hstamp1) as Hle21.
      pose proof (proj2 Horder stamp1 stamp2 Hstamp1 Hstamp2) as Hle12.
      pose proof (cut_max P f bound mapped stamp1 stamp2 Hcut Hstamp1 Hstamp2) as Hmax.
      change (Forall2 (interval_related P f)
        (BBM.time_intervals bound ((event1, stamp1) :: rest1) ((event2, stamp2) :: rest2))
        (BBM.time_intervals mapped ((event1, f stamp1) :: events_map f rest1)
          ((event2, f stamp2) :: events_map f rest2))).
      rewrite !VMBBMTransport.intervals_cons. cbn beta iota zeta.
      destruct event1, event2; repeat case_decide; try (exfalso; lia); try assumption.
      all: constructor; [|assumption].
      all: split; [apply allowed_max; assumption|].
      all: split; [symmetry; apply (map_max P f); assumption|exact Hcut].
Qed.

Theorem intervals_empty P f bound mapped a b : order_on P f →
  Forall (λ e, P e.2) a → Forall (λ e, P e.2) b → cut P f bound mapped →
  (BBM.time_intervals bound a b = [] ↔
    BBM.time_intervals mapped (events_map f a) (events_map f b) = []).
Proof.
  intros Ho Ha Hb Hcut.
  pose proof (intervals_transport P f bound mapped a b Ho Ha Hb Hcut) as Hrel.
  induction Hrel; split; intro Hnil; try reflexivity; discriminate.
Qed.

Theorem overlaps P f bound mapped a b : order_on P f →
  Forall (λ e, P e.2) a → Forall (λ e, P e.2) b → cut P f bound mapped →
  BBM.time_overlaps bound a b = BBM.time_overlaps mapped (events_map f a) (events_map f b).
Proof.
  intros Horder Ha Hb Hcut.
  pose proof (intervals_empty P f bound mapped a b Horder Ha Hb Hcut) as Hempty.
  unfold BBM.time_overlaps.
  destruct (BBM.time_intervals bound a b), (BBM.time_intervals mapped (events_map f a) (events_map f b));
    try reflexivity; exfalso; intuition discriminate.
Qed.
Lemma shift_order p : 0 < p → order_on (λ _, True) (VMSwapSim.shift p).
Proof.
  intro Hp. split.
  - intros t _. pose proof (VMSwapSim.shift_le_iff p t 0).
    rewrite VMSwapSim.shift_zero in H by exact Hp. lia.
  - intros t u _ _. apply VMSwapSim.shift_le_iff.
Qed.
Lemma unshift_order p : 0 < p → order_on (λ t, t ≠ p) (VMSwapSim.unshift p).
Proof.
  intro Hp. split.
  - intros t Ht. pose proof (VMSwapSim.unshift_le_iff_ne p t 0 Ht Hp).
    rewrite VMSwapSim.unshift_zero in H. lia.
  - intros t u Ht Hu. apply VMSwapSim.unshift_le_iff_ne; assumption.
Qed.
Lemma shift_bound p bound : p ≤ S bound → cut (λ _, True) (VMSwapSim.shift p) bound (S bound).
Proof. intros Hp t _. unfold VMSwapSim.shift. case_decide; lia. Qed.
Lemma unshift_bound p bound : 0 < p → p ≤ bound →
  cut (λ t, t ≠ p) (VMSwapSim.unshift p) bound (pred bound).
Proof.
  intros Hp Hbound t Ht. pose proof (VMSwapSim.unshift_le_iff_ne p t bound Ht Hp).
  rewrite (VMSwapSim.unshift_ge p bound Hbound) in H. tauto.
Qed.
Corollary overlaps_insert p bound a b : 0 < p → p ≤ S bound →
  BBM.time_overlaps bound a b =
    BBM.time_overlaps (S bound) (events_map (VMSwapSim.shift p) a) (events_map (VMSwapSim.shift p) b).
Proof.
  intros Hp Hb. apply (overlaps (λ _, True));
    [apply shift_order, Hp|apply Forall_forall; intros; exact I|
      apply Forall_forall; intros; exact I|apply shift_bound, Hb].
Qed.
Corollary overlaps_remove p bound a b : 0 < p → p ≤ bound →
  Forall (λ e, e.2 ≠ p) a → Forall (λ e, e.2 ≠ p) b →
  BBM.time_overlaps bound a b =
    BBM.time_overlaps (pred bound) (events_map (VMSwapSim.unshift p) a) (events_map (VMSwapSim.unshift p) b).
Proof.
  intros Hp Hb Ha Hbs. apply (overlaps (λ t, t ≠ p));
    [apply unshift_order, Hp|exact Ha|exact Hbs|apply unshift_bound; assumption].
Qed.
End VMSwapBBMTime.
