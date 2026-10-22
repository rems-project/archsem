(******************************************************************************)
(* Replaying bounded translation searches after future TLB events             *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMTranslationReplay.
Import VMPromising.

(** A newly imposed invalidation deadline lies beyond the replayed access. *)
Definition inv_after (bound : nat) (old new : option nat) : Prop :=
  new = old ∨ ∃ time, bound < time ∧ new = Some time.

Definition same_translation (bound : nat) (old new : TLB.Result.t) : Prop :=
  TLB.Result.ttbr new = TLB.Result.ttbr old ∧
  TLB.Result.path new = TLB.Result.path old ∧
  TLB.Result.tstart new = TLB.Result.tstart old ∧
  TLB.Result.tend new = TLB.Result.tend old ∧
  inv_after bound (TLB.Result.inv_time old) (TLB.Result.inv_time new).

Lemma inv_after_access bound old new time :
  inv_after bound old new → time ≤ bound →
  (if old is Some deadline then time < deadline else True) →
  (if new is Some deadline then time < deadline else True).
Proof.
  intros [->|[deadline [Hbound ->]]] Htime Hold; [exact Hold|lia].
Qed.

Lemma same_translation_make bound ttbr path tmin tmax inv inv' :
  inv_after bound inv inv' →
  same_translation bound (TLB.Result.make ttbr path tmin tmax inv)
    (TLB.Result.make ttbr path tmin tmax inv').
Proof. intro H. repeat split; try reflexivity. exact H. Qed.

Lemma lookup_change_initial_inv tid ifetch ttbr path bound events tmin tmax inv inv' :
  inv_after bound inv inv' →
  Forall2 (same_translation bound)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv').
Proof.
  revert tmin tmax inv inv'.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmin tmax inv inv' Hinv.
  destruct events as [|[event time] events].
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); constructor.
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); [constructor|].
    destruct event.
    + destruct (decide (tmax < time)); [apply IH; [unfold ltof; cbn; lia|exact Hinv]|].
      destruct (decide (time < tmin)).
      { constructor; [apply same_translation_make, Hinv|constructor]. }
      destruct events as [|[event' time'] rest].
      * constructor; [apply same_translation_make, Hinv|apply IH; [unfold ltof; cbn; lia|exact Hinv]].
      * destruct event'.
        -- constructor; [apply same_translation_make, Hinv|apply IH; [unfold ltof; cbn; lia|exact Hinv]].
        -- destruct (decide (time = time' ∧ (ifetch ∨ tid0 = tid))).
           ++ apply IH; [unfold ltof; cbn; lia|exact Hinv].
           ++ constructor; [apply same_translation_make, Hinv|apply IH; [unfold ltof; cbn; lia|exact Hinv]].
    + destruct (decide (ifetch ∨ tid0 = tid)).
      * apply IH; [unfold ltof; cbn; lia|exact Hinv].
      * apply IH; [unfold ltof; cbn; lia|]. left. reflexivity.
Qed.

Lemma future_load_lookup tid ifetch ttbr path events tmin tmax inv time :
  tmax < time →
  TLB.get_results_from_events tid ifetch ttbr path
    ((TLB.Entry.Load, time) :: events) tmin tmax inv =
  TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv.
Proof.
  intro Htime. cbn [TLB.get_results_from_events].
  destruct (decide (tmax < tmin)) as [Hempty|Hrange].
  - destruct events; cbn [TLB.get_results_from_events]; rewrite decide_True by exact Hempty; reflexivity.
  - rewrite decide_True by exact Htime. reflexivity.
Qed.

Lemma future_tlbi_lookup tid ifetch ttbr path events tmin tmax inv time issuer :
  tmax < time →
  TLB.get_results_from_events tid ifetch ttbr path
    ((TLB.Entry.Tlbi issuer, time) :: events) tmin tmax inv =
  TLB.get_results_from_events tid ifetch ttbr path events tmin tmax
    (if decide (ifetch ∨ issuer = tid) then inv else Some time).
Proof.
  intro Htime. cbn [TLB.get_results_from_events].
  destruct (decide (tmax < tmin)) as [Hempty|Hrange].
  - destruct events; cbn [TLB.get_results_from_events]; rewrite decide_True by exact Hempty; reflexivity.
  - rewrite Nat.min_l by lia. reflexivity.
Qed.
Lemma inv_after_trans bound old mid new :
  inv_after bound old mid → inv_after bound mid new → inv_after bound old new.
Proof.
  intros Hold [->|Hfuture]; [exact Hold|right; exact Hfuture].
Qed.

Lemma future_prefix_lookup tid ifetch ttbr path bound prefix events tmin tmax inv :
  Forall (λ event, bound < event.2) prefix → tmax ≤ bound →
  ∃ inv', inv_after bound inv inv' ∧
    TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin tmax inv =
    TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv'.
Proof.
  revert inv. induction prefix as [|[event time] prefix IH]; intros inv Hprefix Hmax.
  - exists inv. split; [left; reflexivity|reflexivity].
  - apply Forall_cons in Hprefix as [Htime Hprefix]. cbn in Htime.
    destruct event as [|issuer].
    + cbn [app]. rewrite future_load_lookup by lia. apply IH; assumption.
    + cbn [app]. rewrite future_tlbi_lookup by lia.
      destruct (IH (if decide (ifetch ∨ issuer = tid) then inv else Some time)
        Hprefix Hmax) as [inv' [Hinv Hlookup]].
      exists inv'. split; [|exact Hlookup].
      eapply inv_after_trans; [|exact Hinv].
      destruct (decide (ifetch ∨ issuer = tid)); [left; reflexivity|].
      right. exists time. auto.
Qed.

(** All old translation candidates survive a prefix of later entry events.
    A foreign TLBI may introduce a new deadline, bounded beyond old accesses. *)
Theorem future_prefix_translation_replay tid ifetch ttbr path bound prefix events tmin tmax inv :
  Forall (λ event, bound < event.2) prefix → tmax ≤ bound →
  Forall2 (same_translation bound)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv)
    (TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin tmax inv).
Proof.
  intros Hprefix Hmax.
  destruct (future_prefix_lookup tid ifetch ttbr path bound prefix events tmin tmax inv
    Hprefix Hmax) as [inv' [Hinv Hlookup]].
  rewrite Hlookup. apply lookup_change_initial_inv, Hinv.
Qed.

Lemma same_translation_access bound old new access :
  same_translation bound old new → access ≤ bound →
  (if TLB.Result.inv_time old is Some deadline then access < deadline else True) →
  (if TLB.Result.inv_time new is Some deadline then access < deadline else True).
Proof.
  intros [_ [_ [_ [_ Hinv]]]] Haccess Hvalid.
  eapply inv_after_access; eassumption.
Qed.

Theorem future_prefix_candidate tid ifetch ttbr path bound prefix events tmin tmax inv result :
  Forall (λ event, bound < event.2) prefix → tmax ≤ bound →
  result ∈ TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv →
  ∃ result', result' ∈ TLB.get_results_from_events tid ifetch ttbr path
      (prefix ++ events)%list tmin tmax inv ∧
    same_translation bound result result' ∧
    ∀ access, access ≤ bound →
      (if TLB.Result.inv_time result is Some deadline then access < deadline else True) →
      (if TLB.Result.inv_time result' is Some deadline then access < deadline else True).
Proof.
  intros Hprefix Hmax Hin.
  pose proof (future_prefix_translation_replay tid ifetch ttbr path bound prefix events
    tmin tmax inv Hprefix Hmax) as Hreplay.
  assert (Hcandidate : ∃ result', result' ∈ TLB.get_results_from_events tid ifetch ttbr path
      (prefix ++ events)%list tmin tmax inv ∧ same_translation bound result result').
  { induction Hreplay as [|old new olds news Hsame Htail IH].
    - inversion Hin.
    - apply elem_of_cons in Hin as [->|Hin].
      + exists new. split; [left; reflexivity|exact Hsame].
      + destruct (IH Hin) as [result' [Hmember Hsame']].
        exists result'. split; [right; exact Hmember|exact Hsame']. }
  destruct Hcandidate as [result' [Hmember Hsame]].
  exists result'. split; [exact Hmember|]. split; [exact Hsame|].
  intros. eapply same_translation_access; eassumption.
Qed.
End VMTranslationReplay.
