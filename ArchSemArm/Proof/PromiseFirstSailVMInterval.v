(******************************************************************************)
(* VM translation intervals under increasing lookup bounds                   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMTranslation.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMIntervalReplay.
Import VMPromising VMTranslationReplay.

(** A larger query may extend the end of a translation interval. Its root,
    descriptor path and earliest translation time are preserved. *)
Definition extends_translation (bound : nat) (old new : TLB.Result.t) : Prop :=
  TLB.Result.ttbr new = TLB.Result.ttbr old ∧
  TLB.Result.path new = TLB.Result.path old ∧
  TLB.Result.tstart new = TLB.Result.tstart old ∧
  TLB.Result.tend old ≤ TLB.Result.tend new ∧
  inv_after bound (TLB.Result.inv_time old) (TLB.Result.inv_time new).

Lemma extends_translation_refl bound result :
  extends_translation bound result result.
Proof. unfold extends_translation. repeat split; try reflexivity; try lia. left. reflexivity. Qed.

Lemma extends_translation_trans bound old mid new :
  extends_translation bound old mid → extends_translation bound mid new →
  extends_translation bound old new.
Proof.
  intros [Hr [Hp [Hs [He Hi]]]] [Hr' [Hp' [Hs' [He' Hi']]]].
  repeat split; try congruence; try lia.
  eapply inv_after_trans; eassumption.
Qed.

Lemma same_translation_extends bound old new :
  same_translation bound old new → extends_translation bound old new.
Proof.
  intros [Hr [Hp [Hs [He Hi]]]]. repeat split; try assumption; lia.
Qed.

Lemma extends_translation_access bound old new time :
  extends_translation bound old new → time ≤ bound →
  TLB.Result.tstart old ≤ time ≤ TLB.Result.tend old →
  (if TLB.Result.inv_time old is Some deadline then time < deadline else True) →
  TLB.Result.tstart new ≤ time ≤ TLB.Result.tend new ∧
  (if TLB.Result.inv_time new is Some deadline then time < deadline else True).
Proof.
  intros [_ [_ [Hs [He Hi]]]] Hbound Hrange Hvalid.
  split; [lia|]. eapply inv_after_access; eassumption.
Qed.

Lemma extends_translation_make bound ttbr path start stop stop' inv :
  stop ≤ stop' →
  extends_translation bound (TLB.Result.make ttbr path start stop inv)
    (TLB.Result.make ttbr path start stop' inv).
Proof. intro H. unfold extends_translation. cbn. repeat split; try reflexivity; try lia. left. reflexivity. Qed.

(** This holds for arbitrary entry histories, including adjacent load/TLBI
    markers that the lookup coalesces. *)
Theorem lookup_larger_bound tid ifetch ttbr path bound events tmin tmax tmax' inv result :
  tmax ≤ tmax' →
  result ∈ TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv →
  ∃ result', result' ∈ TLB.get_results_from_events tid ifetch ttbr path
      events tmin tmax' inv ∧ extends_translation bound result result'.
Proof.
  revert tmin tmax tmax' inv result.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmin tmax tmax' inv result Hmax Hin.
  destruct (decide (tmax < tmin)) as [Hempty|Hrange].
  { destruct events; cbn [TLB.get_results_from_events] in Hin;
      rewrite decide_True in Hin by exact Hempty; inversion Hin. }
  destruct events as [|[event time] events].
  { cbn [TLB.get_results_from_events] in Hin.
    rewrite decide_False in Hin by exact Hrange. inversion Hin. }
  cbn [TLB.get_results_from_events] in Hin |- *.
  rewrite decide_False in Hin by exact Hrange.
  rewrite decide_False by lia.
  destruct event as [|issuer].
  - destruct (decide (tmax < time)) as [Hold|Hold].
    + destruct (decide (tmax' < time)) as [Hnew|Hnew].
      * eapply IH; [unfold ltof; cbn; lia|exact Hmax|exact Hin].
      * rewrite decide_False by lia.
        destruct events as [|[event' time'] rest].
        -- cbn [TLB.get_results_from_events] in Hin.
           rewrite decide_False in Hin by exact Hrange. inversion Hin.
        -- destruct event' as [|issuer].
           ++ destruct (IH ((TLB.Entry.Load, time') :: rest)
                ltac:(unfold ltof; cbn; lia) tmin tmax tmax' inv result Hmax Hin)
                as [result' [Hmember Hsame]].
              exists result'. split; [right; exact Hmember|exact Hsame].
           ++ destruct (decide (time = time' ∧ (ifetch ∨ issuer = tid))) as [Hmerge|Hmerge].
              ** destruct Hmerge as [<- Hmerge].
                 destruct rest as [|[[|issuer'] stamp] rest].
                 1,3: match type of Hin with
                   | _ ∈ TLB.get_results_from_events _ _ _ _ ?es _ _ _ =>
                     destruct (IH es ltac:(unfold ltof; cbn; lia)
                       tmin tmax tmax' inv result Hmax Hin) as [result' [Hmember Hsame]];
                     exists result'; split; [right; exact Hmember|exact Hsame]
                   end.
                 change (result ∈ (if decide (tmax < tmin) then [] else
                   TLB.get_results_from_events tid ifetch ttbr path
                     ((TLB.Entry.Load, stamp) :: rest) tmin (min tmax (pred time))
                     (if decide (ifetch ∨ issuer = tid) then inv else Some time))) in Hin.
                 rewrite (decide_False (P := tmax < tmin)) in Hin by exact Hrange.
                 rewrite (decide_True (P := ifetch ∨ issuer = tid)) in Hin by exact Hmerge.
                 rewrite Nat.min_l in Hin by lia.
                 eapply IH; [unfold ltof; cbn; lia|exact Hmax|exact Hin].
              ** destruct (IH ((TLB.Entry.Tlbi issuer, time') :: rest)
                   ltac:(unfold ltof; cbn; lia) tmin tmax tmax' inv result Hmax Hin)
                   as [result' [Hmember Hsame]].
                 exists result'. split; [right; exact Hmember|exact Hsame].
    + rewrite decide_False by lia.
      destruct (decide (time < tmin)) as [Hmin|Hmin].
      * apply list_elem_of_singleton in Hin as ->.
        eexists. split; [apply list_elem_of_singleton; reflexivity|].
        apply extends_translation_make, Hmax.
      * destruct events as [|[event' time'] rest].
        -- cbn [TLB.get_results_from_events] in Hin.
           rewrite decide_False in Hin by exact Hrange.
           apply list_elem_of_singleton in Hin as ->.
           eexists. split; [left; reflexivity|apply extends_translation_make, Hmax].
        -- destruct event' as [|issuer].
           ++ apply elem_of_cons in Hin as [->|Hin].
              ** eexists. split; [left; reflexivity|apply extends_translation_make, Hmax].
              ** destruct (IH ((TLB.Entry.Load, time') :: rest)
                   ltac:(unfold ltof; cbn; lia) tmin tmax tmax' inv result Hmax Hin)
                   as [result' [Hmember Hsame]].
                 exists result'. split; [right; exact Hmember|exact Hsame].
           ++ destruct (decide (time = time' ∧ (ifetch ∨ issuer = tid))).
              ** destruct rest as [|[[|issuer'] stamp] rest].
                 2: eapply IH; [unfold ltof; cbn; lia|exact Hmax|exact Hin].
                 all: apply elem_of_cons in Hin as [->|Hin].
                 all: try (eexists; split; [left; reflexivity|apply extends_translation_make, Hmax]).
                 all: match type of Hin with
                   | _ ∈ TLB.get_results_from_events _ _ _ _ ?es _ _ _ =>
                     destruct (IH es ltac:(unfold ltof; cbn; lia)
                       tmin tmax tmax' inv result Hmax Hin) as [result' [Hmember Hsame]];
                     exists result'; split; [right; exact Hmember|exact Hsame]
                   end.
              ** apply elem_of_cons in Hin as [->|Hin].
                 --- eexists. split; [left; reflexivity|apply extends_translation_make, Hmax].
                 --- destruct (IH ((TLB.Entry.Tlbi issuer, time') :: rest)
                       ltac:(unfold ltof; cbn; lia) tmin tmax tmax' inv result Hmax Hin)
                       as [result' [Hmember Hsame]].
                     exists result'. split; [right; exact Hmember|exact Hsame].
  - eapply IH; [unfold ltof; cbn; lia| |exact Hin].
    apply Nat.min_le_compat_r, Hmax.
Qed.

Theorem future_prefix_larger_bound tid ifetch ttbr path bound prefix events
    tmin tmax tmax' inv result :
  Forall (λ event, bound < event.2) prefix → tmax ≤ bound → tmax ≤ tmax' →
  result ∈ TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv →
  ∃ result', result' ∈ TLB.get_results_from_events tid ifetch ttbr path
      (prefix ++ events)%list tmin tmax' inv ∧ extends_translation bound result result'.
Proof.
  intros Hprefix Hbound Hmax Hin.
  destruct (future_prefix_candidate tid ifetch ttbr path bound prefix events
    tmin tmax inv result Hprefix Hbound Hin) as [mid [Hmid [Hsame _]]].
  destruct (lookup_larger_bound tid ifetch ttbr path bound (prefix ++ events)%list
    tmin tmax tmax' inv mid Hmax Hmid) as [result' [Hmember Hextends]].
  exists result'. split; [exact Hmember|].
  eapply extends_translation_trans; [apply same_translation_extends; exact Hsame|exact Hextends].
Qed.
End VMIntervalReplay.
