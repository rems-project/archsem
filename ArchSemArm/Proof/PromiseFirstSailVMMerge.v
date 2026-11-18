(******************************************************************************)
(* Translation-result merging preserves candidates up to walk addresses      *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMInterval PromiseFirstSailVMTranslation.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMMergeReplay.
Import VMPromising.

(** Merging retains the leaf descriptor and each table descriptor's
    non-address bits, and may lower the start of the selected interval.
    It does not preserve the root or the table addresses. *)
Definition represents (candidate representative : TLB.Result.t) : Prop :=
  TLB.Result.mergeable representative candidate ∧
  TLB.Result.tstart representative ≤ TLB.Result.tstart candidate.

Lemma mergeable_refl r : TLB.Result.mergeable r r.
Proof. repeat split; reflexivity. Qed.
Lemma mergeable_sym r s : TLB.Result.mergeable r s → TLB.Result.mergeable s r.
Proof. unfold TLB.Result.mergeable. intros [? [? [? ?]]]. auto. Qed.
Lemma mergeable_trans r s t :
  TLB.Result.mergeable r s → TLB.Result.mergeable s t → TLB.Result.mergeable r t.
Proof. unfold TLB.Result.mergeable. intros [? [? [? ?]]] [? [? [? ?]]]. repeat split; congruence. Qed.
Lemma mergeable_start r s time :
  TLB.Result.mergeable (setv TLB.Result.tstart time r) s ↔ TLB.Result.mergeable r s.
Proof. reflexivity. Qed.
Lemma represents_refl r : represents r r.
Proof. split; [apply mergeable_refl|lia]. Qed.
Lemma represents_trans r s t : represents r s → represents s t → represents r t.
Proof.
  intros [Hrs Hstart] [Hst Hstart']. split; [|lia].
  eapply mergeable_trans; eassumption.
Qed.

(** The merged result takes the root and path of either merged result. *)
Lemma mergeable_pick (smaller : bool) first r s :
  TLB.Result.mergeable first r → TLB.Result.mergeable first s →
  TLB.Result.mergeable (if smaller then r else first) s.
Proof.
  intros Hr Hs. destruct smaller; [|exact Hs].
  eapply mergeable_trans; [apply mergeable_sym, Hr|exact Hs].
Qed.

Lemma merge_into_covers r rs candidate :
  candidate ∈ r :: rs →
  ∃ representative, representative ∈ TLB.Result.merge_into r rs ∧
    represents candidate representative.
Proof.
  induction rs as [|first rest IH]; intro Hin.
  - apply list_elem_of_singleton in Hin as ->.
    exists r. split; [left; reflexivity|apply represents_refl].
  - cbn [TLB.Result.merge_into].
    destruct (decide (TLB.Result.mergeable first r)) as [Hmerge|Hmerge].
    + apply elem_of_cons in Hin as [->|Hin].
      * eexists. split; [left; reflexivity|].
        split; [apply mergeable_start, mergeable_pick; exact Hmerge|change (min (TLB.Result.tstart first) (TLB.Result.tstart r) ≤ TLB.Result.tstart r); lia].
      * apply elem_of_cons in Hin as [->|Hin].
        -- eexists. split; [left; reflexivity|].
           split; [apply mergeable_start, mergeable_pick; [exact Hmerge|apply mergeable_refl]|change (min (TLB.Result.tstart first) (TLB.Result.tstart r) ≤ TLB.Result.tstart first); lia].
        -- exists candidate. split; [right; exact Hin|apply represents_refl].
    + apply elem_of_cons in Hin as [Hin|Hin].
      * destruct (IH ltac:(apply elem_of_cons; left; exact Hin)) as [representative [Hrep Hrel]].
        exists representative. split; [right; exact Hrep|exact Hrel].
      * apply elem_of_cons in Hin as [->|Hin].
        -- exists first. split; [left; reflexivity|apply represents_refl].
        -- destruct (IH ltac:(right; exact Hin)) as [representative [Hrep Hrel]].
           exists representative. split; [right; exact Hrep|exact Hrel].
Qed.

(** Every merged start is the start of a real input in the same merge class.
    The representative's table addresses need not be that input's addresses. *)
Lemma merge_into_witness r rs representative :
  representative ∈ TLB.Result.merge_into r rs →
  ∃ source, source ∈ r :: rs ∧ TLB.Result.mergeable representative source ∧
    TLB.Result.tstart representative = TLB.Result.tstart source.
Proof.
  induction rs as [|first rest IH]; cbn [TLB.Result.merge_into]; intro Hin.
  - apply list_elem_of_singleton in Hin as ->.
    exists r. split; [left; reflexivity|]. split; [apply mergeable_refl|reflexivity].
  - destruct (decide (TLB.Result.mergeable first r)) as [Hmerge|Hmerge].
    + apply elem_of_cons in Hin as [->|Hin].
      * destruct (decide (TLB.Result.tstart first ≤ TLB.Result.tstart r)).
        -- exists first. split; [set_solver|]. split;
             [apply mergeable_start, mergeable_pick; [exact Hmerge|apply mergeable_refl]|change (min (TLB.Result.tstart first) (TLB.Result.tstart r) = TLB.Result.tstart first); lia].
        -- exists r. split; [left; reflexivity|]. split;
             [apply mergeable_start, mergeable_pick; exact Hmerge|change (min (TLB.Result.tstart first) (TLB.Result.tstart r) = TLB.Result.tstart r); lia].
      * exists representative. split; [set_solver|].
        split; [apply mergeable_refl|reflexivity].
    + apply elem_of_cons in Hin as [->|Hin].
      * exists first. split; [set_solver|]. split; [apply mergeable_refl|reflexivity].
      * destruct (IH Hin) as [source [Hsource Hrel]]. exists source. split; [set_solver|exact Hrel].
Qed.

Lemma fold_merge_covers (rs acc : list TLB.Result.t) candidate :
  candidate ∈ (acc ++ rs)%list →
  ∃ representative,
    representative ∈ foldl (λ acc r, TLB.Result.merge_into r acc) acc rs ∧
    represents candidate representative.
Proof.
  revert acc candidate. induction rs as [|r rs IH]; intros acc candidate Hin; cbn.
  - exists candidate. rewrite app_nil_r in Hin. split; [exact Hin|apply represents_refl].
  - apply elem_of_app in Hin as [Hin|Hin].
    + destruct (merge_into_covers r acc candidate ltac:(right; exact Hin))
        as [mid [Hmid Hrel]].
      destruct (IH (TLB.Result.merge_into r acc) mid ltac:(apply elem_of_app; left; exact Hmid))
        as [representative [Hrep Hrel']].
      exists representative. split; [exact Hrep|eapply represents_trans; eassumption].
    + apply elem_of_cons in Hin as [->|Hin].
      * destruct (merge_into_covers r acc r ltac:(left; reflexivity)) as [mid [Hmid Hrel]].
        destruct (IH (TLB.Result.merge_into r acc) mid ltac:(apply elem_of_app; left; exact Hmid))
          as [representative [Hrep Hrel']].
        exists representative. split; [exact Hrep|eapply represents_trans; eassumption].
      * apply IH. apply elem_of_app. right. exact Hin.
Qed.

Lemma fold_merge_witness (rs acc : list TLB.Result.t) representative :
  representative ∈ foldl (λ acc r, TLB.Result.merge_into r acc) acc rs →
  ∃ source, source ∈ (acc ++ rs)%list ∧ TLB.Result.mergeable representative source ∧
    TLB.Result.tstart representative = TLB.Result.tstart source.
Proof.
  revert acc representative. induction rs as [|r rs IH]; intros acc representative Hin; cbn in Hin.
  - exists representative. rewrite app_nil_r. split; [exact Hin|].
    split; [apply mergeable_refl|reflexivity].
  - destruct (IH _ _ Hin) as [mid [Hmid [Hrel Hstart]]].
    apply elem_of_app in Hmid as [Hmid|Hmid].
    + destruct (merge_into_witness r acc mid Hmid) as [source [Hsource [Hrel' Hstart']]].
      exists source. split; [set_solver|]. split;
        [eapply mergeable_trans; eassumption|congruence].
    + exists mid. split; [set_solver|auto].
Qed.

Theorem merge_covers rs candidate :
  candidate ∈ rs →
  ∃ representative, representative ∈ TLB.Result.merge rs ∧ represents candidate representative.
Proof. apply (fold_merge_covers rs []). Qed.

Theorem merge_witness rs representative :
  representative ∈ TLB.Result.merge rs →
  ∃ source, source ∈ rs ∧ TLB.Result.mergeable representative source ∧
    TLB.Result.tstart representative = TLB.Result.tstart source.
Proof. apply (fold_merge_witness rs []). Qed.

(** This is a relation on lookup results, not yet a theorem that Sail
    instructions are insensitive to the changed table addresses. *)
Definition replays (bound : nat) (old new : TLB.Result.t) : Prop :=
  last (TLB.Result.path new) = last (TLB.Result.path old) ∧
  map TLB.Result.table_attrs (removelast (TLB.Result.path new)) =
    map TLB.Result.table_attrs (removelast (TLB.Result.path old)) ∧
  TLB.Result.tstart new ≤ TLB.Result.tstart old ∧
  TLB.Result.tend old ≤ TLB.Result.tend new ∧
  VMTranslationReplay.inv_after bound (TLB.Result.inv_time old) (TLB.Result.inv_time new).

Lemma extends_replays bound old new :
  VMIntervalReplay.extends_translation bound old new → replays bound old new.
Proof.
  intros [_ [Hpath [Hstart [Hend Hinv]]]]. unfold replays.
  rewrite Hpath. repeat split; try reflexivity; try lia; exact Hinv.
Qed.

Theorem merge_replays bound olds news :
  (∀ old ∈ olds, ∃ new, new ∈ news ∧ replays bound old new) →
  ∀ old ∈ TLB.Result.merge olds,
    ∃ new, new ∈ TLB.Result.merge news ∧ replays bound old new.
Proof.
  intros Hreplay old Hold.
  destruct (merge_witness olds old Hold) as [source [Hsource [Hshape Htime]]].
  destruct (Hreplay source Hsource) as [target [Htarget Hrel]].
  destruct (merge_covers news target Htarget) as [new [Hnew [Hshape' Htime']]].
  exists new. split; [exact Hnew|].
  destruct Hshape as [Hleaf [Htables [Hend Hinv]]].
  destruct Hshape' as [Hleaf' [Htables' [Hend' Hinv']]].
  destruct Hrel as [Hleaf'' [Htables'' [Hstart [Hend'' Hinv'']]]].
  unfold replays. repeat split; try congruence; try lia.
Qed.
End VMMergeReplay.
