(******************************************************************************)
(* Commuting TLBI events in VM histories                                      *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** The promise-first VM runner explores one order of each class of
    commuting TLBI events: a candidate is rejected when it is
    [Ev.out_of_order] after the newest event. This file proves the
    combinatorial part of that reduction and the thread-level facts that hold
    without renaming timestamps:

    - an out-of-order pair is a pair of TLBIs with a smaller recipient last,
      with disjoint affected threads;
    - an adjacent transposition of such a pair keeps the memory snapshot and
      every write at its position, and strictly decreases the number of
      recipient inversions;
    - hence every history reaches, by such transpositions, a history with no
      adjacent out-of-order pair;
    - delivering a TLBI event to a thread it does not affect leaves that
      thread state unchanged, at every history.

    Histories are newest first, as in [PState.events]. *)

Module VMSwap.
Import VMPromising.

(** * Out-of-order pairs *)

Lemma out_of_order_inv e1 e2 : Ev.out_of_order e1 e2 = true →
  ∃ t1 r1 k1 t2 r2 k2,
    e1 = Ev.Tlbi t1 r1 k1 ∧ e2 = Ev.Tlbi t2 r2 k2 ∧ r2 < r1 ∧
    TLBI.tid t1 ≠ TLBI.tid t2 ∧ TLBI.tid t1 ≠ r2 ∧ r1 ≠ TLBI.tid t2.
Proof.
  destruct e1 as [m1|t1 r1 k1], e2 as [m2|t2 r2 k2]; cbn; try discriminate.
  intro H. apply bool_decide_eq_true in H as [Hlt Hcase].
  exists t1, r1, k1, t2, r2, k2. auto.
Qed.

(** Every thread is unaffected by at least one event of an out-of-order pair. *)
Lemma out_of_order_disjoint e1 e2 i : Ev.out_of_order e1 e2 = true →
  Ev.affects e1 i = false ∨ Ev.affects e2 i = false.
Proof.
  intro H. destruct (out_of_order_inv e1 e2 H)
    as (t1 & r1 & k1 & t2 & r2 & k2 & -> & -> & Hlt & Hne & Hne1 & Hne2).
  cbn. destruct (decide (i = TLBI.tid t1 ∨ i = r1)) as [Ha|Ha].
  - right. apply bool_decide_eq_false.
    intros [Hb|Hb]; destruct Ha as [Ha|Ha]; subst; try congruence; lia.
  - left. apply bool_decide_eq_false. exact Ha.
Qed.

Lemma out_of_order_not_msg e1 e2 : Ev.out_of_order e1 e2 = true →
  Ev.get_msg e1 = None ∧ Ev.get_msg e2 = None.
Proof.
  intro H. destruct (out_of_order_inv e1 e2 H)
    as (t1 & r1 & k1 & t2 & r2 & k2 & -> & -> & _). split; reflexivity.
Qed.

(** * Adjacent transpositions *)

Definition sorted (mem : list Ev.t) : Prop :=
  ∀ l1 l2 e1 e2, mem = (l1 ++ e2 :: e1 :: l2)%list → Ev.out_of_order e1 e2 = false.

Inductive swap_step : list Ev.t → list Ev.t → Prop :=
| swap_step_intro l1 l2 e1 e2 :
    Ev.out_of_order e1 e2 = true →
    swap_step (l1 ++ e2 :: e1 :: l2)%list (l1 ++ e1 :: e2 :: l2)%list.

Lemma swap_step_length mem mem' : swap_step mem mem' → length mem' = length mem.
Proof. intros [l1 l2 e1 e2 _]. rewrite !length_app. reflexivity. Qed.

Lemma swap_step_permutation mem mem' : swap_step mem mem' → mem' ≡ₚ mem.
Proof. intros [l1 l2 e1 e2 _]. apply Permutation_app_head. constructor. Qed.

Lemma swap_step_msgs mem mem' : swap_step mem mem' → map Ev.get_msg mem' = map Ev.get_msg mem.
Proof.
  intros [l1 l2 e1 e2 H]. destruct (out_of_order_not_msg e1 e2 H) as [H1 H2].
  rewrite !map_app. cbn. rewrite H1, H2. reflexivity.
Qed.

Lemma to_memMap_msgs imem (mem mem' : list Ev.t) :
  map Ev.get_msg mem = map Ev.get_msg mem' →
  Memory.to_memMap imem mem = Memory.to_memMap imem mem'.
Proof.
  revert mem'. induction mem as [|e mem IH]; intros [|e' mem'] H; try discriminate; [reflexivity|].
  injection H as He Hrest. unfold Memory.to_memMap, PromMemory.to_memMap in *. cbn.
  rewrite He, (IH mem' Hrest). reflexivity.
Qed.

Lemma swap_step_memMap imem mem mem' : swap_step mem mem' →
  Memory.to_memMap imem mem' = Memory.to_memMap imem mem.
Proof. intro H. apply to_memMap_msgs, swap_step_msgs, H. Qed.

Lemma swap_rtc_memMap imem mem mem' : rtc swap_step mem mem' →
  Memory.to_memMap imem mem' = Memory.to_memMap imem mem.
Proof.
  intro H. induction H; [reflexivity|]. rewrite IHrtc. apply swap_step_memMap. exact H.
Qed.

Lemma swap_rtc_permutation mem mem' : rtc swap_step mem mem' → mem' ≡ₚ mem.
Proof.
  intro H. induction H; [apply Permutation_refl|].
  eapply Permutation_trans; [exact IHrtc|]. apply swap_step_permutation, H.
Qed.

(** * Recipient inversions *)

Definition inverted (older newer : Ev.t) : bool :=
  match older, newer with
  | Ev.Tlbi _ r1 _, Ev.Tlbi _ r2 _ => bool_decide (r2 < r1)
  | _, _ => false
  end.

(** For a newest-first history, count the older events forming an
    inversion with each event. *)
Fixpoint inversions (mem : list Ev.t) : nat :=
  match mem with
  | [] => 0
  | e :: older => length (filter (λ x, inverted x e = true) older) + inversions older
  end.

Lemma out_of_order_inverted e1 e2 : Ev.out_of_order e1 e2 = true →
  inverted e1 e2 = true ∧ inverted e2 e1 = false.
Proof.
  intro H. destruct (out_of_order_inv e1 e2 H)
    as (t1 & r1 & k1 & t2 & r2 & k2 & -> & -> & Hlt & _).
  cbn. split; [apply bool_decide_eq_true; lia|apply bool_decide_eq_false; lia].
Qed.

Lemma filter_length_perm (P : Ev.t → Prop) `{∀ x, Decision (P x)} (l l' : list Ev.t) :
  l ≡ₚ l' → length (filter P l) = length (filter P l').
Proof. intro Hp. apply Permutation_length. apply filter_Permutation. exact Hp. Qed.

Lemma swap_step_inversions mem mem' : swap_step mem mem' → inversions mem' < inversions mem.
Proof.
  intros [l1 l2 e1 e2 H]. destruct (out_of_order_inverted e1 e2 H) as [H12 H21].
  induction l1 as [|a l1 IH]; cbn [app inversions].
  - rewrite !filter_cons. rewrite H12, H21.
    repeat case_decide; try congruence. cbn [length]. lia.
  - assert (Hperm : (l1 ++ e1 :: e2 :: l2)%list ≡ₚ (l1 ++ e2 :: e1 :: l2)%list).
    { apply Permutation_app_head. constructor. }
    rewrite (filter_length_perm _ _ _ Hperm). lia.
Qed.

(** * Sorting by adjacent transpositions *)

Fixpoint sortedb (mem : list Ev.t) : bool :=
  match mem with
  | e2 :: ((e1 :: _) as older) => negb (Ev.out_of_order e1 e2) && sortedb older
  | _ => true
  end.

Lemma sortedb_sorted mem : sortedb mem = true → sorted mem.
Proof.
  intros Hs l1 l2 e1 e2 ->. revert Hs. induction l1 as [|a l1 IH]; intro Hs.
  - cbn in Hs. apply andb_prop in Hs as [Hn _]. destruct (Ev.out_of_order e1 e2); [discriminate|reflexivity].
  - apply IH. destruct l1 as [|b l1]; cbn in Hs |- *.
    + apply andb_prop in Hs as [_ Hs]. exact Hs.
    + apply andb_prop in Hs as [_ Hs]. exact Hs.
Qed.

Lemma not_sortedb mem : sortedb mem = false →
  ∃ l1 l2 e1 e2, mem = (l1 ++ e2 :: e1 :: l2)%list ∧ Ev.out_of_order e1 e2 = true.
Proof.
  induction mem as [|e2 mem IH]; intro Hs; [discriminate|].
  destruct mem as [|e1 mem]; [discriminate|].
  cbn [sortedb] in Hs. destruct (Ev.out_of_order e1 e2) eqn:Hord.
  - exists [], mem, e1, e2. split; [reflexivity|exact Hord].
  - cbn in Hs. destruct (IH Hs) as (l1 & l2 & a & b & Heq & Hab).
    exists (e2 :: l1), l2, a, b. split; [|exact Hab]. rewrite Heq. reflexivity.
Qed.

Theorem bubble_sort mem : ∃ mem', rtc swap_step mem mem' ∧ sorted mem'.
Proof.
  induction mem as [mem IH] using (induction_ltof1 _ inversions). unfold ltof in IH.
  destruct (sortedb mem) eqn:Hs.
  - exists mem. split; [apply rtc_refl|apply sortedb_sorted, Hs].
  - destruct (not_sortedb mem Hs) as (l1 & l2 & e1 & e2 & -> & Hord).
    pose proof (swap_step_intro l1 l2 e1 e2 Hord) as Hstep.
    destruct (IH _ (swap_step_inversions _ _ Hstep)) as [mem' [Hrtc Hsorted]].
    exists mem'. split; [eapply rtc_l; eassumption|exact Hsorted].
Qed.

(** * Thread states not affected by an event *)

Lemma emit_promise_unaffected (i : nat) imem mem ev ts :
  Ev.affects ev i = false → TState.emit_promise i imem mem ev ts = Ok ts.
Proof.
  destruct ev as [msg|tlbi r k]; cbn; [discriminate|].
  intro H. apply bool_decide_eq_false in H.
  unfold TState.emit_promise. cbn.
  rewrite bool_decide_false by (intro Heq; apply H; left; symmetry; exact Heq).
  unfold TState.process_event, TState.run_tlb.
  destruct (TState.tlb ts) as [c|] eqn:Hc; [|reflexivity].
  unfold TLB.fill_promise, TLB.fill_event. cbn.
  destruct (decide (i = r)) as [Heq|_]; [exfalso; apply H; right; exact Heq|].
  cbn. f_equal. destruct ts. cbn in Hc |- *. subst. reflexivity.
Qed.

(** Delivering both events of a pair to a thread affected by neither gives
    the same state in both orders and at every history. *)
Corollary emit_promise_unaffected_both (i : nat) imem mem mem' e1 e2 ts :
  Ev.affects e1 i = false → Ev.affects e2 i = false →
  (TState.emit_promise i imem mem e1 ts ≫= TState.emit_promise i imem mem' e2) =
  (TState.emit_promise i imem mem e2 ts ≫= TState.emit_promise i imem mem' e1).
Proof.
  intros H1 H2. rewrite !emit_promise_unaffected by assumption. cbn.
  rewrite !emit_promise_unaffected by assumption. reflexivity.
Qed.

(** * Guards of the emitter over its outstanding promises

    In the same-emitter case both events are promises of the emitter, and
    the swap exchanges their timestamps [k] and [S k]. The guards that read
    the outstanding promise set depend only on that set as a multiset, so
    they cannot distinguish the two orders while both promises are
    outstanding. Once only the older instruction's promise is fulfilled, the
    remaining promise has timestamp [S k] in the original order and [k] in
    the swapped order; [no_promises_until] then differs only at the view
    [k], and the CSE candidates differ only by the candidate [k]. *)

Definition swap_time (k t : nat) : nat :=
  if decide (t = k) then S k else if decide (t = S k) then k else t.

Definition outstanding (ts : TState.t) : list nat := (TState.prom_wr ts ++ TState.prom_tlbi ts)%list.

Lemma no_promises_until_perm v ts ts' :
  outstanding ts ≡ₚ outstanding ts' →
  TState.no_promises_until v ts ↔ TState.no_promises_until v ts'.
Proof.
  unfold outstanding, TState.no_promises_until. intro Hp.
  split; intros H p Hin; apply H.
  - apply list_elem_of_In. apply (Permutation_in _ (Permutation_sym Hp)).
    apply list_elem_of_In. exact Hin.
  - apply list_elem_of_In. apply (Permutation_in _ Hp). apply list_elem_of_In. exact Hin.
Qed.

Lemma foldr_min_perm (base : nat) (l l' : list nat) :
  l ≡ₚ l' → foldr (λ p v, min v p) base l = foldr (λ p v, min v p) base l'.
Proof.
  induction 1 as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn; lia.
Qed.

Lemma min_promise_perm vmax ts ts' :
  outstanding ts ≡ₚ outstanding ts' → TState.min_promise vmax ts = TState.min_promise vmax ts'.
Proof. intro Hp. unfold TState.min_promise. apply foldr_min_perm, Hp. Qed.

Lemma cse_candidates_perm vpre vmax ts ts' :
  outstanding ts ≡ₚ outstanding ts' →
  TState.cse_candidates vpre vmax ts = TState.cse_candidates vpre vmax ts'.
Proof.
  intro Hp. unfold TState.cse_candidates. rewrite (min_promise_perm vmax ts ts' Hp). reflexivity.
Qed.

(** Exchanging two timestamps that both occur, once each, in a list of
    distinct promise timestamps permutes that list. *)
Lemma swap_time_perm k (l : list nat) :
  NoDup l → k ∈ l → S k ∈ l → map (swap_time k) l ≡ₚ l.
Proof.
  intros Hnd Hk HSk.
  apply elem_of_Permutation in Hk as [l1 Hl1].
  assert (HSk1 : S k ∈ l1).
  { apply list_elem_of_In in HSk. apply (Permutation_in _ Hl1) in HSk.
    apply list_elem_of_In in HSk. apply elem_of_cons in HSk as [H|H]; [lia|exact H]. }
  apply elem_of_Permutation in HSk1 as [l2 Hl2].
  assert (Hall : l ≡ₚ k :: S k :: l2) by (eapply Permutation_trans; [exact Hl1|constructor; exact Hl2]).
  assert (Hnd' : NoDup (k :: S k :: l2)).
  { apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact Hall|]. apply NoDup_ListNoDup, Hnd. }
  apply list.NoDup_cons in Hnd' as [Hk2 Hnd']. apply list.NoDup_cons in Hnd' as [HSk2 _].
  assert (Hl2id : map (swap_time k) l2 = l2).
  { etransitivity; [|apply map_id]. apply map_ext_in. intros x Hx.
    apply list_elem_of_In in Hx. unfold swap_time.
    destruct (decide (x = k)) as [->|Hxk].
    { exfalso. apply Hk2. right. exact Hx. }
    destruct (decide (x = S k)) as [->|_]; [contradiction|reflexivity]. }
  eapply Permutation_trans; [apply Permutation_map, Hall|].
  cbn [map]. unfold swap_time at 1 2.
  rewrite decide_True by reflexivity. rewrite decide_False by lia. rewrite decide_True by reflexivity.
  rewrite Hl2id. eapply Permutation_trans; [constructor|apply Permutation_sym, Hall].
Qed.

(** With one of the two promises remaining, the guards agree at every view
    other than [k]. *)
Lemma no_promises_until_one_swapped v k (l : list nat) :
  v ≠ k →
  (∀ p, p ∈ S k :: l → v < p) ↔ (∀ p, p ∈ k :: l → v < p).
Proof.
  intro Hv. split; intros H p Hin; apply elem_of_cons in Hin as [->|Hin].
  - specialize (H (S k) ltac:(left)). lia.
  - apply H. right. exact Hin.
  - specialize (H k ltac:(left)). lia.
  - apply H. right. exact Hin.
Qed.

End VMSwap.
