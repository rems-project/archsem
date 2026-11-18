(******************************************************************************)
(* Compress BBM intervals across a foreign TLBI, including CSE loads         *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMBBM PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMCacheOrder PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapRemoveEvents
  PromiseFirstSailVMSwapBBMTime.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.
Module VMSwapBBMCompress.
Import VMPromising VMSwapSim VMSwapBBMTime VMBBMTransport.

Lemma intervals_late_r top bound event rest events :
  bound < top → VMCacheOrder.ordered ((TLB.Entry.Load, top) :: rest) →
  VMCacheOrder.ordered events →
  VMCacheOrder.bounded top events →
  BBM.time_intervals bound events ((event, top) :: rest) = BBM.time_intervals bound events rest.
Proof.
  intros Hlt Hrest Hord Hb.
  assert (Hr : VMCacheOrder.ordered ((event, top) :: rest)).
  { destruct rest as [|[e t] rest]; [split; exact I|]. destruct Hrest as [[Hle Hno] Htail].
    split; [split; [exact Hle|destruct event; tauto]|exact Htail]. }
  rewrite time_intervals_sym by assumption.
  rewrite intervals_late_l; [apply time_intervals_sym; [apply Hrest|exact Hord]|exact Hlt| |exact Hb].
  exact (VMCacheOrder.ordered_head_bound _ _ _ Hrest).
Qed.

Lemma intervals_invalid_l bound tid time rest other : 0 < time →
  VMCacheOrder.ordered ((TLB.Entry.Tlbi tid, time) :: rest) → VMCacheOrder.ordered other →
  BBM.time_intervals bound ((TLB.Entry.Tlbi tid, time) :: rest) other =
  BBM.time_intervals (min bound (pred time)) rest other.
Proof.
  intros Htime Hfirst. revert bound. induction other as [|[event stamp] other IH]; intros bound Hother.
  - rewrite !VMBBMReplay.time_intervals_nil_r. reflexivity.
  - rewrite intervals_cons. cbn beta iota zeta.
    destruct (decide (stamp < time)) as [Hlt|Hge]; [reflexivity|].
    rewrite IH by apply Hother.
    assert (Hrest : VMCacheOrder.ordered rest) by apply Hfirst.
    assert (Hbound : VMCacheOrder.bounded stamp rest).
    { eapply VMCacheOrder.bounded_mono; [|exact (VMCacheOrder.ordered_head_bound _ _ _ Hfirst)]. lia. }
    rewrite (time_intervals_sym (min bound (pred time)) rest ((event, stamp) :: other))
      by assumption.
    rewrite intervals_late_l by first [assumption|lia|exact (VMCacheOrder.ordered_head_bound _ _ _ Hother)].
    rewrite time_intervals_sym by (assumption || apply Hother).
    replace (min (min bound (pred stamp)) (pred time)) with (min bound (pred time)) by lia.
    reflexivity.
Qed.

(** Popping a load need not clamp the bound: the next entry is an
    invalidation at an earlier or equal timestamp. *)
Lemma pop_load bound stamp rest other :
  VMCacheOrder.ordered ((TLB.Entry.Load, stamp) :: rest) → VMCacheOrder.ordered other →
  BBM.time_intervals (min bound (pred stamp)) rest other = BBM.time_intervals bound rest other.
Proof.
  intros Hrest Hother. destruct rest as [|[event time] rest]; [reflexivity|].
  destruct Hrest as [[Hle Hno] Htail]. destruct event as [|tid]; [exfalso; apply Hno; auto|].
  destruct time as [|time]; [rewrite !intervals_tlbi_zero_l; reflexivity|].
  rewrite !intervals_invalid_l by (assumption || lia).
  replace (min (min bound (pred stamp)) (pred (S time))) with (min bound (pred (S time))) by lia.
  reflexivity.
Qed.
Lemma pop_load_r bound stamp rest other :
  VMCacheOrder.ordered ((TLB.Entry.Load, stamp) :: rest) → VMCacheOrder.ordered other →
  BBM.time_intervals (min bound (pred stamp)) other rest = BBM.time_intervals bound other rest.
Proof.
  intros Hrest Hother.
  rewrite (time_intervals_sym (min bound (pred stamp)) other rest) by (assumption || apply Hrest).
  rewrite (pop_load bound stamp rest other Hrest Hother).
  apply time_intervals_sym; [apply Hrest|exact Hother].
Qed.

Lemma load_tie bound stamp rest1 rest2 :
  VMCacheOrder.ordered ((TLB.Entry.Load, stamp) :: rest1) →
  VMCacheOrder.ordered ((TLB.Entry.Load, stamp) :: rest2) →
  BBM.time_intervals bound rest1 ((TLB.Entry.Load, stamp) :: rest2) =
  BBM.time_intervals bound ((TLB.Entry.Load, stamp) :: rest1) rest2.
Proof.
  intros Hfirst Hsecond.
  rewrite <- (pop_load bound stamp rest1 ((TLB.Entry.Load, stamp) :: rest2) Hfirst Hsecond).
  rewrite (intervals_load_tie bound stamp rest1 rest2 Hfirst).
  rewrite (time_intervals_sym bound ((TLB.Entry.Load, stamp) :: rest1) rest2)
    by (assumption || apply Hsecond).
  rewrite <- (pop_load bound stamp rest2 ((TLB.Entry.Load, stamp) :: rest1) Hsecond Hfirst).
  rewrite (intervals_load_tie bound stamp rest2 rest1 Hsecond).
  apply time_intervals_sym; [apply Hfirst|apply Hsecond].
Qed.

Definition pop_bound (event : TLB.Entry.event) bound stamp :=
  match event with TLB.Entry.Load => bound | TLB.Entry.Tlbi _ => min bound (pred stamp) end.

Lemma intervals_cons_free bound event1 stamp1 rest1 event2 stamp2 rest2 :
  VMCacheOrder.ordered ((event1, stamp1) :: rest1) →
  VMCacheOrder.ordered ((event2, stamp2) :: rest2) →
  BBM.time_intervals bound ((event1, stamp1) :: rest1) ((event2, stamp2) :: rest2) =
  let pop1 := BBM.time_intervals (pop_bound event1 bound stamp1) rest1 ((event2, stamp2) :: rest2) in
  let pop2 := BBM.time_intervals (pop_bound event2 bound stamp2) ((event1, stamp1) :: rest1) rest2 in
  match event1, event2 with
  | TLB.Entry.Load, TLB.Entry.Load =>
      let rest := if decide (stamp2 ≤ stamp1) then pop1 else pop2 in
      if decide (max stamp1 stamp2 ≤ bound) then (max stamp1 stamp2, bound) :: rest else rest
  | TLB.Entry.Load, _ => if decide (stamp2 ≤ stamp1) then pop1 else pop2
  | _, _ => if decide (stamp2 < stamp1) then pop1 else pop2
  end.
Proof.
  intros Hfirst Hsecond. rewrite intervals_cons. destruct event1, event2; cbn beta iota zeta.
  all: unfold pop_bound.
  all: try rewrite (pop_load bound stamp1 rest1 _ Hfirst Hsecond).
  all: try rewrite (pop_load_r bound stamp2 rest2 _ Hsecond Hfirst).
  all: reflexivity.
Qed.

Lemma unshift_all_bound p bound : 0 < p → p ≤ bound → cut (λ _, True) (unshift p) bound (pred bound).
Proof. intros Hp Hb t _. unfold unshift. case_decide; lia. Qed.
Lemma unshift_strict_right p t stamp : 0 < p → stamp ≠ p → 0 < stamp →
  (unshift p t < unshift p stamp ↔ t < stamp).
Proof. intros Hp Hne Hpos. unfold unshift. repeat case_decide; lia. Qed.
Lemma unshift_le_left p stamp t : 0 < p → stamp ≠ p →
  (unshift p stamp ≤ unshift p t ↔ stamp ≤ t).
Proof. intros Hp Hne. unfold unshift. repeat case_decide; lia. Qed.
Lemma cut_pred_invalid p bound mapped stamp : 0 < p → stamp ≠ p → 0 < stamp →
  cut (λ _, True) (unshift p) bound mapped →
  cut (λ _, True) (unshift p) (min bound (pred stamp)) (min mapped (pred (unshift p stamp))).
Proof.
  intros Hp Hne Hpos Hcut t _. specialize (Hcut t I).
  pose proof (unshift_strict_right p t stamp Hp Hne Hpos).
  assert (Hu : 0 < unshift p stamp) by (unfold unshift; case_decide; lia).
  lia.
Qed.
Lemma mapped_ordered p events : VMCacheOrder.ordered events →
  VMCacheOrder.ordered (events_map (unshift p) events).
Proof.
  intro H. pose proof (VMSwapRemoveEvents.ordered_map_unshift p events H) as Hr.
  assert (Heq : map_evs (unshift p) events = events_map (unshift p) events).
  { unfold map_evs, events_map. apply map_ext. intros []; reflexivity. }
  rewrite <- Heq. exact Hr.
Qed.
Lemma intervals_tlbi_zero_r bound tid rest events :
  VMCacheOrder.ordered events → VMCacheOrder.ordered ((TLB.Entry.Tlbi tid, 0) :: rest) →
  BBM.time_intervals bound events ((TLB.Entry.Tlbi tid, 0) :: rest) = [].
Proof. intros. rewrite time_intervals_sym by assumption. apply intervals_tlbi_zero_l. Qed.

Definition no_invalid p (ev : TLB.Entry.event * nat) :=
  match ev.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi _ => ev.2 ≠ p end.
Definition interval_map f (a b : nat * nat) := b.1 = f a.1 ∧ cut (λ _, True) f a.2 b.2.

Theorem intervals_remove p bound mapped a b : 0 < p →
  VMCacheOrder.ordered a → VMCacheOrder.ordered b →
  Forall (no_invalid p) a → Forall (no_invalid p) b →
  cut (λ _, True) (unshift p) bound mapped →
  Forall2 (interval_map (unshift p)) (BBM.time_intervals bound a b)
    (BBM.time_intervals mapped (events_map (unshift p) a) (events_map (unshift p) b)).
Proof.
  intro Hp. revert bound mapped b.
  induction a as [|[event1 stamp1] rest1 IH1]; intros bound mapped b Ha Hb Hna Hnb Hcut; [constructor|].
  apply Forall_cons_1 in Hna as [Hn1 Hnr1].
  revert bound mapped Hb Hnb Hcut.
  induction b as [|[event2 stamp2] rest2 IH2]; intros bound mapped Hb Hnb Hcut.
  - rewrite !VMBBMReplay.time_intervals_nil_r. constructor.
  - apply Forall_cons_1 in Hnb as [Hn2 Hnr2].
    assert (Hnb : Forall (no_invalid p) ((event2, stamp2) :: rest2)) by (constructor; assumption).
    pose proof (mapped_ordered p _ Ha) as Hma. pose proof (mapped_ordered p _ Hb) as Hmb.
    change (VMCacheOrder.ordered ((event1, unshift p stamp1) :: events_map (unshift p) rest1)) in Hma.
    change (VMCacheOrder.ordered ((event2, unshift p stamp2) :: events_map (unshift p) rest2)) in Hmb.
    change (Forall2 (interval_map (unshift p))
      (BBM.time_intervals bound ((event1, stamp1) :: rest1) ((event2, stamp2) :: rest2))
      (BBM.time_intervals mapped ((event1, unshift p stamp1) :: events_map (unshift p) rest1)
        ((event2, unshift p stamp2) :: events_map (unshift p) rest2))).
    destruct (decide (event1 = TLB.Entry.Load ∨ 0 < stamp1)) as [Hz1|Hz1].
    2: { destruct event1; [tauto|]. assert (stamp1 = 0) by lia. subst stamp1.
         rewrite unshift_zero, !intervals_tlbi_zero_l. constructor. }
    destruct (decide (event2 = TLB.Entry.Load ∨ 0 < stamp2)) as [Hz2|Hz2].
    2: { destruct event2; [tauto|]. assert (stamp2 = 0) by lia. subst stamp2.
         rewrite unshift_zero in Hmb |- *. rewrite !intervals_tlbi_zero_r by assumption. constructor. }
    assert (Hcut1 : cut (λ _, True) (unshift p) (pop_bound event1 bound stamp1)
      (pop_bound event1 mapped (unshift p stamp1))).
    { destruct event1; [exact Hcut|]. apply cut_pred_invalid;
        [exact Hp|exact Hn1|destruct Hz1; [discriminate|assumption]|exact Hcut]. }
    assert (Hcut2 : cut (λ _, True) (unshift p) (pop_bound event2 bound stamp2)
      (pop_bound event2 mapped (unshift p stamp2))).
    { destruct event2; [exact Hcut|]. apply cut_pred_invalid;
        [exact Hp|exact Hn2|destruct Hz2; [discriminate|assumption]|exact Hcut]. }
    pose proof (IH1 (pop_bound event1 bound stamp1) (pop_bound event1 mapped (unshift p stamp1))
      ((event2, stamp2) :: rest2) (proj2 Ha) Hb Hnr1 Hnb Hcut1) as Hpop1.
    pose proof (IH2 (pop_bound event2 bound stamp2) (pop_bound event2 mapped (unshift p stamp2))
      (proj2 Hb) Hnr2 Hcut2) as Hpop2.
    pose proof (cut_max (λ _, True) (unshift p) bound mapped stamp1 stamp2 Hcut I I) as Hmax.
    rewrite (intervals_cons_free _ _ _ _ _ _ _ Ha Hb), (intervals_cons_free _ _ _ _ _ _ _ Hma Hmb).
    cbn beta iota zeta. destruct event1 as [|issuer1], event2 as [|issuer2].
    + cbn [pop_bound] in Hpop1, Hpop2.
      destruct (decide (stamp2 ≤ stamp1)) as [Hle|Hgt];
        destruct (decide (unshift p stamp2 ≤ unshift p stamp1)) as [Hle'|Hgt'].
      * destruct (decide (max stamp1 stamp2 ≤ bound)),
          (decide (max (unshift p stamp1) (unshift p stamp2) ≤ mapped)); try (exfalso; tauto).
        -- constructor; [split; [symmetry; apply unshift_max|exact Hcut]|exact Hpop1].
        -- exact Hpop1.
      * exfalso. apply Hgt', unshift_mono, Hle.
      * assert (Heq : unshift p stamp1 = unshift p stamp2).
        { pose proof (unshift_mono p stamp1 stamp2 ltac:(lia)); lia. }
        assert (Htails : BBM.time_intervals mapped (events_map (unshift p) rest1)
            ((TLB.Entry.Load, unshift p stamp2) :: events_map (unshift p) rest2) =
          BBM.time_intervals mapped ((TLB.Entry.Load, unshift p stamp1) :: events_map (unshift p) rest1)
            (events_map (unshift p) rest2)).
        { rewrite <- Heq in Hmb |- *. apply load_tie; assumption. }
        rewrite Htails.
        destruct (decide (max stamp1 stamp2 ≤ bound)),
          (decide (max (unshift p stamp1) (unshift p stamp2) ≤ mapped)); try (exfalso; tauto).
        -- constructor; [split; [symmetry; apply unshift_max|exact Hcut]|exact Hpop2].
        -- exact Hpop2.
      * destruct (decide (max stamp1 stamp2 ≤ bound)),
          (decide (max (unshift p stamp1) (unshift p stamp2) ≤ mapped)); try (exfalso; tauto).
        -- constructor; [split; [symmetry; apply unshift_max|exact Hcut]|exact Hpop2].
        -- exact Hpop2.
    + pose proof (unshift_le_left p stamp2 stamp1 Hp Hn2) as Hle.
      repeat case_decide; try (exfalso; tauto); assumption.
    + pose proof (unshift_strict_right p stamp2 stamp1 Hp Hn1 ltac:(destruct Hz1; [discriminate|assumption])) as Hlt.
      repeat case_decide; try (exfalso; tauto); assumption.
    + pose proof (unshift_strict_right p stamp2 stamp1 Hp Hn1 ltac:(destruct Hz1; [discriminate|assumption])) as Hlt.
      repeat case_decide; try (exfalso; tauto); assumption.
Qed.
End VMSwapBBMCompress.
