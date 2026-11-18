(******************************************************************************)
(* BBM byte comparisons across insertion or removal of a TLBI                  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapInsert.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapBBMTime.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.
Module VMSwapBBMMemory.
Import VMPromising VMSwapSim VMSwapBBMTime.
#[local] Typeclasses Transparent Memory.t.

Definition writes_between (P : Msg.t → Prop) mem lo hi :=
  ∀ ev, ev ∈ PromMemory.cut_after lo (PromMemory.cut_before hi mem) →
    match Ev.get_msg ev with Some msg => P msg | None => True end.
#[local] Typeclasses Transparent writes_between.

Lemma writes_insert P l r e lo hi hi' : Ev.get_msg e = None →
  cut (λ _, True) (shift (S (length r))) hi hi' →
  writes_between P (l ++ e :: r) (shift (S (length r)) lo) hi' ↔
  writes_between P (l ++ r) lo hi.
Proof.
  intros He Hcut. split; intros H ev Hin.
  - apply VMSwapInsert.slice_elem in Hin as (t & Hlo & Hhi & Hlook).
    apply H, VMSwapInsert.slice_elem. exists (shift (S (length r)) t).
    split; [apply shift_lt_iff, Hlo|]. split; [apply (Hcut t I), Hhi|].
    rewrite insert_lookup. exact Hlook.
  - apply VMSwapInsert.slice_elem in Hin as (t & Hlo & Hhi & Hlook).
    destruct (decide (t = S (length r))) as [->|Hne].
    { rewrite insert_lookup_new in Hlook. injection Hlook as <-. rewrite He. exact I. }
    remember (unshift (S (length r)) t) as u eqn:Hu.
    assert (Et : t = shift (S (length r)) u) by (subst u; symmetry; apply shift_unshift; lia).
    subst t. rewrite insert_lookup in Hlook. apply H, VMSwapInsert.slice_elem.
    exists u. split; [apply shift_lt_iff in Hlo; exact Hlo|].
    split; [apply (Hcut u I); exact Hhi|exact Hlook].
Qed.

Lemma mapM_ext_result {A B E} (f g : A → result E B) xs :
  (∀ x, x ∈ xs → f x = g x) → mapM f xs = mapM g xs.
Proof.
  induction xs as [|x xs IH]; intro H; [reflexivity|]. cbn.
  rewrite (H x ltac:(left)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma contents_insert imem addrs l r e time lvl oa1 oa2 : Ev.get_msg e = None →
  shift (S (length r)) time ≤ S (length (l ++ r)) →
  BBM.mem_contents_eq imem (l ++ e :: r) addrs (shift (S (length r)) time) lvl oa1 oa2 =
  BBM.mem_contents_eq imem (l ++ r) addrs time lvl oa1 oa2.
Proof.
  intros He Htime. unfold BBM.mem_contents_eq. f_equal. apply mapM_ext_result.
  intros offs Hin. unfold Memory.read_byte.
  rewrite !read_byte_insert by assumption. rewrite unshift_shift. reflexivity.
Qed.

Theorem contents_between_insert imem addrs l r e lo hi hi' lvl oa1 oa2 : Ev.get_msg e = None →
  shift (S (length r)) lo ≤ S (length (l ++ r)) →
  cut (λ _, True) (shift (S (length r))) hi hi' →
  BBM.mem_contents_eq_btw imem (l ++ e :: r) addrs (shift (S (length r)) lo) hi' lvl oa1 oa2 =
  BBM.mem_contents_eq_btw imem (l ++ r) addrs lo hi lvl oa1 oa2.
Proof.
  intros He Hlo Hcut. unfold BBM.mem_contents_eq_btw.
  rewrite (contents_insert imem addrs l r e lo lvl oa1 oa2 He Hlo).
  assert (Hsame :
    bool_decide (writes_between (λ msg, ¬ Msg.overlap (prefix_to_pa lvl oa1)
      (Z.to_N (bv_modulus (offset_bits lvl))) msg ∧ ¬ Msg.overlap (prefix_to_pa lvl oa2)
      (Z.to_N (bv_modulus (offset_bits lvl))) msg)
      (l ++ e :: r) (shift (S (length r)) lo) hi') =
    bool_decide (writes_between (λ msg, ¬ Msg.overlap (prefix_to_pa lvl oa1)
      (Z.to_N (bv_modulus (offset_bits lvl))) msg ∧ ¬ Msg.overlap (prefix_to_pa lvl oa2)
      (Z.to_N (bv_modulus (offset_bits lvl))) msg) (l ++ r) lo hi)).
  { apply bool_decide_ext. apply writes_insert; assumption. }
  unfold writes_between in Hsame. rewrite Hsame. reflexivity.
Qed.

Lemma inverse_cut p hi hi' : 0 < p → cut (λ t, t ≠ p) (unshift p) hi hi' →
  cut (λ _, True) (shift p) hi' hi.
Proof.
  intros Hp Hcut t _. specialize (Hcut (shift p t) (shift_ne p t)).
  rewrite unshift_shift in Hcut. tauto.
Qed.

Corollary contents_between_remove imem addrs l r e lo hi hi' lvl oa1 oa2 : Ev.get_msg e = None →
  lo ≠ S (length r) → lo ≤ S (length (l ++ r)) →
  cut (λ t, t ≠ S (length r)) (unshift (S (length r))) hi hi' →
  BBM.mem_contents_eq_btw imem (l ++ e :: r) addrs lo hi lvl oa1 oa2 =
  BBM.mem_contents_eq_btw imem (l ++ r) addrs (unshift (S (length r)) lo) hi' lvl oa1 oa2.
Proof.
  intros He Hne Hlo Hcut.
  assert (Hbound : shift (S (length r)) (unshift (S (length r)) lo) ≤ S (length (l ++ r))).
  { rewrite shift_unshift by (assumption || lia). exact Hlo. }
  pose proof (contents_between_insert imem addrs l r e (unshift (S (length r)) lo)
    hi' hi lvl oa1 oa2 He Hbound (inverse_cut (S (length r)) hi hi' ltac:(lia) Hcut)) as H.
  rewrite shift_unshift in H by (assumption || lia). exact H.
Qed.
End VMSwapBBMMemory.
