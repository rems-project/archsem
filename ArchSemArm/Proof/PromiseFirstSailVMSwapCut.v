(******************************************************************************)
(* View cuts around two adjacent TLBI timestamps                             *)
(******************************************************************************)
From ASCommon Require Import Options Common.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwap PromiseFirstSailVMSwapSim.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapCut.
Import VMPromising.
#[local] Typeclasses Transparent view UMPromising.view.

(** Removing both adjacent TLBI events identifies the three cuts immediately
    before, between and after them. Such cuts see the same message history. *)
Definition same k a b := a = b ∨ (pred k ≤ a ≤ S k ∧ pred k ≤ b ≤ S k).

Lemma same_refl k a : same k a a.
Proof. left; reflexivity. Qed.
Lemma same_sym k a b : same k a b → same k b a.
Proof. unfold same; intuition lia. Qed.
Lemma same_trans k a b c : same k a b → same k b c → same k a c.
Proof. unfold same; intuition lia. Qed.
Lemma same_max k a a' b b' : same k a a' → same k b b' → same k (max a b) (max a' b').
Proof. unfold same. intros Ha Hb. destruct (le_dec a b), (le_dec a' b');
  rewrite ?Nat.max_r, ?Nat.max_l by lia; intuition lia. Qed.
Lemma same_lt k a b t : 0 < k → same k a b → t ≠ k → t ≠ S k → (a < t ↔ b < t).
Proof. unfold same; intuition lia. Qed.
Lemma same_le k a b t : 0 < k → same k a b → t ≠ pred k → t ≠ k → (a ≤ t ↔ b ≤ t).
Proof. unfold same; intuition lia. Qed.
Lemma swap_same k t : same k t (VMSwap.swap_time k t).
Proof. unfold same, VMSwap.swap_time. repeat case_decide; subst; intuition lia. Qed.

Lemma unshift_pair_same k a b : 0 < k →
  VMSwapSim.unshift k (VMSwapSim.unshift k a) =
  VMSwapSim.unshift k (VMSwapSim.unshift k b) ↔ same k a b.
Proof.
  intro Hk. unfold VMSwapSim.unshift, same. repeat case_decide; intuition lia.
Qed.

Lemma swap_list_fixed k (proms : list nat) : k ∉ proms → S k ∉ proms →
  map (VMSwap.swap_time k) proms = proms.
Proof.
  intros Hk Hsk. etransitivity; [|apply map_id]. apply map_ext_in.
  intros t Hin. apply list_elem_of_In in Hin. unfold VMSwap.swap_time.
  repeat case_decide; subst; try contradiction; reflexivity.
Qed.

(** Once the two promises have been fulfilled, a guard cannot distinguish
    these three cuts. Full DSB completion supplies the TLBI-list exclusion;
    the write list also excludes TLBI timestamps. *)
Lemma no_promises_until k v v' ts ts' : 0 < k → same k v v' →
  k ∉ VMSwap.outstanding ts → S k ∉ VMSwap.outstanding ts →
  VMSwap.outstanding ts' ≡ₚ map (VMSwap.swap_time k) (VMSwap.outstanding ts) →
  (TState.no_promises_until v ts ↔ TState.no_promises_until v' ts').
Proof.
  intros Hk Hv Hp Hsp Hprom.
  rewrite swap_list_fixed in Hprom by assumption.
  pose proof (VMSwap.no_promises_until_perm v' ts' ts Hprom) as Hperm.
  assert (Hview : TState.no_promises_until v ts ↔ TState.no_promises_until v' ts).
  { unfold TState.no_promises_until. split; intros H t Hin.
    - apply (proj1 (same_lt k v v' t Hk Hv ltac:(intro E; subst; contradiction)
        ltac:(intro E; subst; contradiction))), H, Hin.
    - apply (proj2 (same_lt k v v' t Hk Hv ltac:(intro E; subst; contradiction)
        ltac:(intro E; subst; contradiction))), H, Hin. }
  tauto.
Qed.

Lemma cut_before_suffix (prefix suffix : Memory.t) :
  PromMemory.cut_before (length suffix) (prefix ++ suffix) = suffix.
Proof.
  unfold PromMemory.cut_before. rewrite length_app, Nat.add_sub, drop_app_length. reflexivity.
Qed.

Lemma tlbi_pair_cut imem (l r : Memory.t) tlbi1 rc1 ep1 tlbi2 rc2 ep2 t :
  length r ≤ t ≤ S (S (length r)) →
  Memory.to_memMap imem (PromMemory.cut_before t
    (l ++ Ev.Tlbi tlbi2 rc2 ep2 :: Ev.Tlbi tlbi1 rc1 ep1 :: r)) = Memory.to_memMap imem r.
Proof.
  intros Ht. assert (t = length r ∨ t = S (length r) ∨ t = S (S (length r))) by lia.
  destruct H as [-> | [-> | ->]].
  - replace (l ++ Ev.Tlbi tlbi2 rc2 ep2 :: Ev.Tlbi tlbi1 rc1 ep1 :: r)
      with ((l ++ [Ev.Tlbi tlbi2 rc2 ep2; Ev.Tlbi tlbi1 rc1 ep1]) ++ r)
      by (rewrite <- app_assoc; reflexivity).
    rewrite cut_before_suffix. reflexivity.
  - change (Memory.to_memMap imem (PromMemory.cut_before (length (Ev.Tlbi tlbi1 rc1 ep1 :: r))
      (l ++ Ev.Tlbi tlbi2 rc2 ep2 :: Ev.Tlbi tlbi1 rc1 ep1 :: r)) = Memory.to_memMap imem r).
    replace (l ++ Ev.Tlbi tlbi2 rc2 ep2 :: Ev.Tlbi tlbi1 rc1 ep1 :: r)
      with ((l ++ [Ev.Tlbi tlbi2 rc2 ep2]) ++ Ev.Tlbi tlbi1 rc1 ep1 :: r)
      by (rewrite <- app_assoc; reflexivity).
    rewrite cut_before_suffix. reflexivity.
  - change (Memory.to_memMap imem (PromMemory.cut_before
      (length (Ev.Tlbi tlbi2 rc2 ep2 :: Ev.Tlbi tlbi1 rc1 ep1 :: r))
      (l ++ Ev.Tlbi tlbi2 rc2 ep2 :: Ev.Tlbi tlbi1 rc1 ep1 :: r)) = Memory.to_memMap imem r).
    rewrite cut_before_suffix. reflexivity.
Qed.
End VMSwapCut.
