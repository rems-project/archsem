(******************************************************************************)
(* Fulfillment of promises after exchanging adjacent events                 *)
(******************************************************************************)
From ASCommon Require Import Options Common.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwap PromiseFirstSailVMSwapSim.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapPromises.
Import VMPromising.
#[local] Typeclasses Transparent view UMPromising.view Memory.t.

Lemma time_involutive k t : VMSwap.swap_time k (VMSwap.swap_time k t) = t.
Proof. unfold VMSwap.swap_time. repeat case_decide; subst; lia. Qed.
Lemma time_injective k a b : VMSwap.swap_time k a = VMSwap.swap_time k b → a = b.
Proof. intro H. rewrite <- (time_involutive k a), <- (time_involutive k b), H. reflexivity. Qed.
Lemma time_fixed k t : t ≠ k → t ≠ S k → VMSwap.swap_time k t = t.
Proof. intros Hk Hsk. unfold VMSwap.swap_time. repeat case_decide; congruence. Qed.

Lemma lookup_swap (l r : Memory.t) e1 e2 t :
  VMSwapSim.mlookup (l ++ e1 :: e2 :: r) (VMSwap.swap_time (S (length r)) t) =
  VMSwapSim.mlookup (l ++ e2 :: e1 :: r) t.
Proof.
  destruct (decide (t = S (length r))) as [->|Hp].
  - unfold VMSwap.swap_time. rewrite decide_True by reflexivity.
    rewrite VMSwapSim.insert_lookup_new.
    replace (l ++ e2 :: e1 :: r) with ((l ++ [e2]) ++ e1 :: r)
      by (rewrite <- app_assoc; reflexivity).
    rewrite VMSwapSim.insert_lookup_new. reflexivity.
  - destruct (decide (t = S (S (length r)))) as [->|Hq].
    + unfold VMSwap.swap_time. rewrite decide_False by lia. rewrite decide_True by reflexivity.
      replace (l ++ e1 :: e2 :: r) with ((l ++ [e1]) ++ e2 :: r)
        by (rewrite <- app_assoc; reflexivity).
      rewrite !VMSwapSim.insert_lookup_new. reflexivity.
    + rewrite time_fixed by assumption.
      rewrite !VMSwapSim.lookup_spec, !length_app. cbn [length].
      case_decide; [|reflexivity].
      destruct (lt_dec (length l + S (S (length r)) - t) (length l)) as [Hleft|Hright].
      * rewrite !nth_error_app1 by lia. reflexivity.
      * rewrite !nth_error_app2 by lia.
        assert (Hindex : 2 ≤ length l + S (S (length r)) - t - length l) by lia.
        replace (length l + S (S (length r)) - t - length l)
          with (S (S (length l + S (S (length r)) - t - length l - 2))) by lia.
        reflexivity.
Qed.

Definition matching (mem : Memory.t) (ev : Ev.t) (proms : list nat) :=
  filter (λ t, VMSwapSim.mlookup mem t = Some ev) proms.

(** The two endpoints may trade places in the promise list. Since they
    represent distinct events, each event's matching sublist still follows
    the timestamp renaming in order. This is what [Memory.fulfill] observes. *)
Definition related k (ma mb : Memory.t) (pa pb : list nat) :=
  ∀ ev, matching mb ev pb = map (VMSwap.swap_time k) (matching ma ev pa).

Lemma fulfill_related k ma mb pa pb ev : related k ma mb pa pb →
  Memory.fulfill ev pb mb = VMSwap.swap_time k <$> Memory.fulfill ev pa ma.
Proof.
  intro Hrel. unfold Memory.fulfill, PromMemory.fulfill.
  change (head (reverse (matching mb ev pb)) = VMSwap.swap_time k <$> head (reverse (matching ma ev pa))).
  rewrite Hrel. generalize (matching ma ev pa) as xs. intro xs.
  unfold reverse. rewrite <- (rev_alt (map _ xs)), <- (rev_alt xs), <- map_rev.
  destruct (rev xs); reflexivity.
Qed.

Lemma matching_filter mem ev proms gone :
  matching mem ev (filter (λ t, t ≠ gone) proms) =
  filter (λ t, t ≠ gone) (matching mem ev proms).
Proof.
  unfold matching. induction proms as [|t proms IH]; [reflexivity|].
  rewrite !filter_cons. repeat case_decide; cbn [filter]; rewrite ?filter_cons;
    repeat case_decide; rewrite ?IH; try reflexivity; congruence.
Qed.
Lemma filter_map_time k gone proms :
  filter (λ t, t ≠ VMSwap.swap_time k gone) (map (VMSwap.swap_time k) proms) =
  map (VMSwap.swap_time k) (filter (λ t, t ≠ gone) proms).
Proof.
  induction proms as [|t proms IH]; [reflexivity|]. cbn [map]. rewrite !filter_cons.
  repeat case_decide; cbn [map]; rewrite ?IH; try reflexivity; try congruence.
  all: match goal with H : VMSwap.swap_time ?key _ = VMSwap.swap_time ?key _ |- _ =>
    apply time_injective in H; congruence end.
Qed.
Lemma fulfill_filter k ma mb pa pb gone : related k ma mb pa pb →
  related k ma mb (filter (λ t, t ≠ gone) pa) (filter (λ t, t ≠ VMSwap.swap_time k gone) pb).
Proof.
  intros Hrel ev. rewrite !matching_filter, Hrel, filter_map_time. reflexivity.
Qed.
Lemma matching_map (l r : Memory.t) e1 e2 ev proms :
  matching (l ++ e1 :: e2 :: r) ev (map (VMSwap.swap_time (S (length r))) proms) =
  map (VMSwap.swap_time (S (length r))) (matching (l ++ e2 :: e1 :: r) ev proms).
Proof.
  unfold matching. induction proms as [|t proms IH]; [reflexivity|]. cbn [map].
  rewrite !filter_cons, lookup_swap. case_decide; cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma matching_swap_distinct mem a b tail ev : VMSwapSim.mlookup mem a ≠ VMSwapSim.mlookup mem b →
  matching mem ev (a :: b :: tail) = matching mem ev (b :: a :: tail).
Proof.
  intro Hne. unfold matching. rewrite !filter_cons.
  repeat case_decide; try reflexivity; congruence.
Qed.

Lemma initial_pair (r : Memory.t) e1 e2 proms : e1 ≠ e2 →
  (∀ t, t ∈ proms → t ≤ length r) →
  related (S (length r)) (e2 :: e1 :: r) (e1 :: e2 :: r)
    (S (S (length r)) :: S (length r) :: proms)
    (S (S (length r)) :: S (length r) :: proms).
Proof.
  intros Hne Hbound ev.
  pose proof (matching_map [] r e1 e2 ev (S (S (length r)) :: S (length r) :: proms)) as Hmap.
  cbn [app] in Hmap. rewrite <- Hmap. cbn [map].
  assert (Hfixed : map (VMSwap.swap_time (S (length r))) proms = proms).
  { etransitivity; [|apply map_id]. apply map_ext_in. intros t Hin. apply list_elem_of_In in Hin.
    apply time_fixed; specialize (Hbound t Hin); lia. }
  rewrite Hfixed. unfold VMSwap.swap_time at 1 2.
  rewrite decide_False by lia. rewrite !decide_True by reflexivity.
  apply matching_swap_distinct.
  change (VMSwapSim.mlookup ([] ++ e1 :: e2 :: r) (S (length (e2 :: r))) ≠
    VMSwapSim.mlookup ([e1] ++ e2 :: r) (S (length r))).
  rewrite !VMSwapSim.insert_lookup_new. congruence.
Qed.

Lemma matching_cons_old (mem : Memory.t) fresh ev proms :
  (∀ t, t ∈ proms → t ≤ length mem) → matching (fresh :: mem) ev proms = matching mem ev proms.
Proof.
  unfold matching. induction proms as [|t proms IH]; intro Hbound; [reflexivity|].
  rewrite !filter_cons.
  assert (Hlook : VMSwapSim.mlookup (fresh :: mem) t = VMSwapSim.mlookup mem t).
  { unfold VMSwapSim.mlookup. apply PromMemory.lookup_cons_old. apply Hbound. left. }
  rewrite Hlook, IH; [reflexivity|]. intros t' Hin. apply Hbound. right. exact Hin.
Qed.

Lemma extend_history k ma mb pa pb fresh : related k ma mb pa pb →
  (∀ t, t ∈ pa → t ≤ length ma) → (∀ t, t ∈ pb → t ≤ length mb) →
  related k (fresh :: ma) (fresh :: mb) pa pb.
Proof. intros Hrel Ha Hb ev. rewrite !matching_cons_old by assumption. apply Hrel. Qed.

Lemma cons_related k ma mb pa pb ta tb : related k ma mb pa pb →
  tb = VMSwap.swap_time k ta → VMSwapSim.mlookup mb tb = VMSwapSim.mlookup ma ta →
  related k ma mb (ta :: pa) (tb :: pb).
Proof.
  intros Hrel -> Hlook ev. specialize (Hrel ev). unfold matching in Hrel |- *.
  rewrite !filter_cons, Hlook.
  case_decide; cbn [map]; rewrite Hrel; reflexivity.
Qed.

Theorem emit_related k ma mb pa pb fresh : related k ma mb pa pb →
  length ma = length mb → S k ≤ length ma →
  (∀ t, t ∈ pa → t ≤ length ma) → (∀ t, t ∈ pb → t ≤ length mb) →
  related k (fresh :: ma) (fresh :: mb) (S (length ma) :: pa) (S (length mb) :: pb).
Proof.
  intros Hrel Hlen Hk Ha Hb. apply cons_related.
  - apply extend_history; assumption.
  - rewrite time_fixed; lia.
  - change (VMSwapSim.mlookup ([] ++ fresh :: mb) (S (length mb)) =
      VMSwapSim.mlookup ([] ++ fresh :: ma) (S (length ma))).
    rewrite !VMSwapSim.insert_lookup_new. reflexivity.
Qed.
Theorem initial_out_of_order (r : Memory.t) e1 e2 proms : Ev.out_of_order e1 e2 = true →
  (∀ t, t ∈ proms → t ≤ length r) →
  related (S (length r)) (e2 :: e1 :: r) (e1 :: e2 :: r)
    (S (S (length r)) :: S (length r) :: proms)
    (S (S (length r)) :: S (length r) :: proms).
Proof.
  intros Horder Hbound. apply initial_pair; [|exact Hbound].
  destruct (VMSwap.out_of_order_inv _ _ Horder)
    as (t1 & r1 & k1 & t2 & r2 & k2 & -> & -> & Hlt & _).
  intro Heq. injection Heq. lia.
Qed.

Lemma member_forward k ma mb pa pb t ev : related k ma mb pa pb →
  t ∈ pa → VMSwapSim.mlookup ma t = Some ev → VMSwap.swap_time k t ∈ pb.
Proof.
  intros Hrel Hin Hlook.
  assert (Hmatch : t ∈ matching ma ev pa) by (apply list_elem_of_filter; auto).
  assert (Hmapped : VMSwap.swap_time k t ∈ map (VMSwap.swap_time k) (matching ma ev pa)).
  { apply list_elem_of_fmap. exists t. auto. }
  rewrite <- (Hrel ev) in Hmapped. apply list_elem_of_filter in Hmapped as [_ Hmapped]. exact Hmapped.
Qed.
Lemma member_backward k ma mb pa pb t ev : related k ma mb pa pb →
  t ∈ pb → VMSwapSim.mlookup mb t = Some ev → VMSwap.swap_time k t ∈ pa.
Proof.
  intros Hrel Hin Hlook.
  assert (Hmatch : t ∈ matching mb ev pb) by (apply list_elem_of_filter; auto).
  rewrite (Hrel ev) in Hmatch. apply list_elem_of_fmap in Hmatch as [old [-> Hmatch]].
  rewrite time_involutive. apply list_elem_of_filter in Hmatch as [_ Hmatch]. exact Hmatch.
Qed.

Definition valid (mem : Memory.t) (proms : list nat) :=
  ∀ t, t ∈ proms → ∃ ev, VMSwapSim.mlookup mem t = Some ev.

Lemma member_iff k ma mb pa pb t : related k ma mb pa pb → valid ma pa → valid mb pb →
  (VMSwap.swap_time k t ∈ pb ↔ t ∈ pa).
Proof.
  intros Hrel Ha Hb. split; intro Hin.
  - destruct (Hb _ Hin) as [ev Hlook].
    pose proof (member_backward _ _ _ _ _ _ _ Hrel Hin Hlook) as Hback.
    rewrite time_involutive in Hback. exact Hback.
  - destruct (Ha _ Hin) as [ev Hlook]. eapply member_forward; eassumption.
Qed.

Theorem fulfill_success k ma mb pa pb ev time : related k ma mb pa pb →
  Memory.fulfill ev pa ma = Some time →
  Memory.fulfill ev pb mb = Some (VMSwap.swap_time k time) ∧
  related k ma mb (filter (λ t, t ≠ time) pa)
    (filter (λ t, t ≠ VMSwap.swap_time k time) pb).
Proof.
  intros Hrel Hful. split; [rewrite (fulfill_related _ _ _ _ _ _ Hrel), Hful; reflexivity|].
  apply fulfill_filter, Hrel.
Qed.
End VMSwapPromises.
