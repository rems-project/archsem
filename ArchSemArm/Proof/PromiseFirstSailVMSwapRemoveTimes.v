(******************************************************************************)
(* Read and fulfilled-promise times avoid a removed non-write event           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailRead PromiseFirstSailVMSwapSim.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveTimes.
Import VMPromising VMSwapSim.

Lemma max_avoids p a b : a ≠ p → b ≠ p → a `max` b ≠ p.
Proof. lia. Qed.
Lemma max_list_avoids p {A} (f : A → nat) xs : 0 < p → Forall (λ x, f x ≠ p) xs →
  max_list_with f xs ≠ p.
Proof.
  intros Hp Hxs. induction Hxs as [|x xs Hx Hxs IH]; [cbn; lia|].
  cbn. apply max_avoids; assumption.
Qed.

Lemma read_all_btw_avoids addr size imem l r tlbi rc epoch tmin tmax reads :
  tmax ≤ length (l ++ Ev.Tlbi tlbi rc epoch :: r) →
  Memory.read_all_btw addr size imem (l ++ Ev.Tlbi tlbi rc epoch :: r) tmin tmax = Ok reads →
  ∀ bytes, bytes ∈ reads → Forall (λ bt, bt.2 ≠ S (length r)) bytes.
Proof.
  intros Hmax Hread bytes Hin. destruct (decide (tmin ≤ tmax)) as [Hle|Hgt].
  - unfold Memory.read_all_btw in Hread.
    rewrite read_all_btw_remove in Hread by (try reflexivity; try exact Hle; rewrite !length_app in *; cbn in *; lia).
    destruct (PromMemory.read_all_btw _ _ _ _ _ _ _) as [short|err] eqn:Hs; cbn in Hread; [|discriminate].
    injection Hread as <-. apply list_elem_of_fmap in Hin as [old [-> Hin]].
    unfold shift_bytes. apply list.Forall_fmap. apply list.Forall_forall.
    intros [byte time] Hbt. cbn. apply shift_ne.
  - unfold Memory.read_all_btw, PromMemory.read_all_btw in Hread.
    rewrite decide_False in Hread by exact Hgt. injection Hread as <-. inversion Hin.
Qed.

Lemma read_all_avoids addr size imem l r tlbi rc epoch tmin reads :
  Memory.read_all addr size imem (l ++ Ev.Tlbi tlbi rc epoch :: r) tmin = Ok reads →
  ∀ bytes, bytes ∈ reads → Forall (λ bt, bt.2 ≠ S (length r)) bytes.
Proof.
  intro Hread. eapply (read_all_btw_avoids addr size imem l r tlbi rc epoch tmin
    (length (l ++ Ev.Tlbi tlbi rc epoch :: r)) reads); [lia|].
  pose proof (read_all_aux_success_bound Ev.get_msg _ _ _ _ _ _ _ Hread) as Hle.
  unfold Memory.read_all_btw, PromMemory.read_all_btw.
  rewrite decide_True by exact Hle. unfold PromMemory.cut_before. rewrite Nat.sub_diag, drop_0. exact Hread.
Qed.

Lemma read_all_pte_avoids addr imem l r tlbi rc epoch tmin tmax reads :
  tmax ≤ length (l ++ Ev.Tlbi tlbi rc epoch :: r) →
  Memory.read_all_pte addr imem (l ++ Ev.Tlbi tlbi rc epoch :: r) tmin tmax = Ok reads →
  ∀ pte, pte ∈ reads → pte.2 ≠ S (length r).
Proof.
  intros Hmax Hread pte Hin. unfold Memory.read_all_pte in Hread.
  destruct (Memory.read_all_btw _ _ _ _ _ _) as [bytes|err] eqn:Hbytes; cbn in Hread; [|discriminate].
  injection Hread as <-. apply list_elem_of_fmap in Hin as [row [-> Hin]]. cbn.
  apply max_list_avoids; [lia|]. eapply read_all_btw_avoids; eassumption.
Qed.

Lemma fulfill_member (ev : Ev.t) promises mem time : PromMemory.fulfill ev promises mem = Some time → time ∈ promises.
Proof.
  unfold PromMemory.fulfill. rewrite head_reverse. intro H.
  apply last_Some_elem_of in H. apply list_elem_of_filter in H as [_ H]. exact H.
Qed.

Lemma fulfill_avoids p (ev : Ev.t) promises mem time : Forall (λ t, t ≠ p) promises →
  PromMemory.fulfill ev promises mem = Some time → time ≠ p.
Proof.
  intros Hp Hrun. rewrite list.Forall_forall in Hp. apply Hp. eapply fulfill_member; exact Hrun.
Qed.
End VMSwapRemoveTimes.
