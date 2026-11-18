(******************************************************************************)
(* Preserve BBM memory comparisons at the removed timestamp                  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapInsert
  PromiseFirstSailVMSwapBBMTime PromiseFirstSailVMSwapBBMMemory.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.
Module VMSwapBBMMemoryAny.
Import VMPromising VMSwapSim VMSwapBBMTime VMSwapBBMMemory.
#[local] Typeclasses Transparent Memory.t writes_between.

Lemma writes_remove P l r e lo hi hi' : Ev.get_msg e = None →
  cut (λ _, True) (unshift (S (length r))) hi hi' →
  writes_between P (l ++ e :: r) lo hi ↔
  writes_between P (l ++ r) (unshift (S (length r)) lo) hi'.
Proof.
  intros He Hcut. split; intros H ev Hin.
  - apply VMSwapInsert.slice_elem in Hin as (t & Hlo & Hhi & Hlook).
    apply H, VMSwapInsert.slice_elem. exists (shift (S (length r)) t).
    split.
    + apply (unshift_lt_iff_ne (S (length r)) lo (shift (S (length r)) t));
        [apply shift_ne|lia|rewrite unshift_shift; exact Hlo].
    + split.
      * apply (Hcut (shift (S (length r)) t) I). rewrite unshift_shift. exact Hhi.
      * rewrite insert_lookup. exact Hlook.
  - apply VMSwapInsert.slice_elem in Hin as (t & Hlo & Hhi & Hlook).
    destruct (decide (t = S (length r))) as [->|Hne].
    { rewrite insert_lookup_new in Hlook. injection Hlook as <-. rewrite He. exact I. }
    apply H, VMSwapInsert.slice_elem. exists (unshift (S (length r)) t). split.
    + apply unshift_lt_iff_ne; [exact Hne|lia|exact Hlo].
    + split; [apply (Hcut t I), Hhi|].
      rewrite <- (insert_lookup l r e (unshift (S (length r)) t)).
      rewrite shift_unshift by (assumption || lia). exact Hlook.
Qed.

Lemma contents_remove imem addrs l r e time lvl oa1 oa2 : Ev.get_msg e = None →
  time ≤ S (length (l ++ r)) →
  BBM.mem_contents_eq imem (l ++ e :: r) addrs time lvl oa1 oa2 =
  BBM.mem_contents_eq imem (l ++ r) addrs (unshift (S (length r)) time) lvl oa1 oa2.
Proof.
  intros He Htime. unfold BBM.mem_contents_eq. f_equal. apply mapM_ext_result.
  intros offs Hin. unfold Memory.read_byte. rewrite !read_byte_insert by assumption. reflexivity.
Qed.

Theorem contents_between_remove imem addrs l r e lo hi hi' lvl oa1 oa2 : Ev.get_msg e = None →
  lo ≤ S (length (l ++ r)) → cut (λ _, True) (unshift (S (length r))) hi hi' →
  BBM.mem_contents_eq_btw imem (l ++ e :: r) addrs lo hi lvl oa1 oa2 =
  BBM.mem_contents_eq_btw imem (l ++ r) addrs (unshift (S (length r)) lo) hi' lvl oa1 oa2.
Proof.
  intros He Hlo Hcut. unfold BBM.mem_contents_eq_btw.
  rewrite (contents_remove imem addrs l r e lo lvl oa1 oa2 He Hlo).
  assert (Hsame :
    bool_decide (writes_between (λ msg, ¬ Msg.overlap (prefix_to_pa lvl oa1)
      (Z.to_N (bv_modulus (offset_bits lvl))) msg ∧ ¬ Msg.overlap (prefix_to_pa lvl oa2)
      (Z.to_N (bv_modulus (offset_bits lvl))) msg) (l ++ e :: r) lo hi) =
    bool_decide (writes_between (λ msg, ¬ Msg.overlap (prefix_to_pa lvl oa1)
      (Z.to_N (bv_modulus (offset_bits lvl))) msg ∧ ¬ Msg.overlap (prefix_to_pa lvl oa2)
      (Z.to_N (bv_modulus (offset_bits lvl))) msg)
      (l ++ r) (unshift (S (length r)) lo) hi')).
  { apply bool_decide_ext. apply writes_remove; assumption. }
  unfold writes_between in Hsame. rewrite Hsame. reflexivity.
Qed.
End VMSwapBBMMemoryAny.
