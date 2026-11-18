(******************************************************************************)
(* BBM checks ignore entries with no recorded lifetime                        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMBBMReplay.
Import VMPromising.

Lemma time_intervals_nil_l bound events : BBM.time_intervals bound [] events = [].
Proof. reflexivity. Qed.
Lemma time_intervals_nil_r bound events : BBM.time_intervals bound events [] = [].
Proof. destruct events as [|[event time] events]; reflexivity. Qed.
Lemma time_overlaps_nil_l bound events : BBM.time_overlaps bound [] events = false.
Proof. reflexivity. Qed.
Lemma time_overlaps_nil_r bound events : BBM.time_overlaps bound events [] = false.
Proof. unfold BBM.time_overlaps. rewrite time_intervals_nil_r. reflexivity. Qed.

Lemma violation_nil_l imem mem addrs bound ctxt e1 e2 events :
  BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 [] events = Ok false.
Proof.
  unfold BBM.is_bbm_violation. rewrite ?time_overlaps_nil_l, ?time_intervals_nil_l.
  repeat match goal with |- context[if ?b then _ else _] => destruct b end; rewrite ?andb_false_r; reflexivity.
Qed.
Lemma violation_nil_r imem mem addrs bound ctxt e1 e2 events :
  BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 events [] = Ok false.
Proof.
  unfold BBM.is_bbm_violation. rewrite ?time_overlaps_nil_r, ?time_intervals_nil_r.
  repeat match goal with |- context[if ?b then _ else _] => destruct b end; rewrite ?andb_false_r; reflexivity.
Qed.

Local Lemma check_list_cons {E A} (f : A → result E bool) x xs :
  List.forallb id <$> mapM f (x :: xs) =
    (b ← f x; rest ← List.forallb id <$> mapM f xs; mret (b && rest)).
Proof.
  cbn [mapM]. unfold mbind, result_bind, fmap, result_fmap, mret, result_ret.
  destruct (f x); [destruct (mapM f xs); reflexivity|reflexivity].
Qed.

Local Lemma check_list_filter {E A} (keep : A → Prop) `{∀ x, Decision (keep x)}
    (f : A → result E bool) xs :
  (∀ x, ¬ keep x → f x = Ok true) →
  List.forallb id <$> mapM f (filter keep xs) = List.forallb id <$> mapM f xs.
Proof.
  intro Hskip. induction xs as [|x xs IH]; [reflexivity|].
  rewrite filter_cons. destruct (decide (keep x)) as [Hkeep|Hkeep].
  - rewrite !check_list_cons, IH. reflexivity.
  - rewrite check_list_cons, Hskip by exact Hkeep. rewrite <- IH.
    unfold mbind, result_bind, fmap, result_fmap, mret, result_ret.
    destruct (mapM f (filter keep xs)); reflexivity.
Qed.

Local Lemma check_list_true {E A} (f : A → result E bool) xs :
  (∀ x, f x = Ok true) → List.forallb id <$> mapM f xs = Ok true.
Proof.
  intro Hf. induction xs; [reflexivity|]. rewrite check_list_cons, Hf, IHxs. reflexivity.
Qed.

Lemma for_all_pairs_filter {A} (keep : A → Prop) `{∀ x, Decision (keep x)}
    (f : A → A → result string bool) xs :
  (∀ x y, ¬ keep x → f x y = Ok true) →
  (∀ x y, ¬ keep y → f x y = Ok true) →
  BBM.for_all_pairs f (filter keep xs) = BBM.for_all_pairs f xs.
Proof.
  intros Hleft Hright. induction xs as [|x xs IH]; [reflexivity|].
  rewrite filter_cons. destruct (decide (keep x)) as [Hkeep|Hkeep].
  - cbn [BBM.for_all_pairs]. rewrite check_list_filter by (intros; apply Hright; assumption).
    rewrite IH. reflexivity.
  - cbn [BBM.for_all_pairs]. rewrite check_list_true by (intro; apply Hleft, Hkeep).
    cbn [mbind result_bind]. exact IH.
Qed.

(** Rollback can retain allocated entries with empty histories. Removing
    them preserves the BBM pair check, including its error result. *)
Theorem pair_check_nonempty imem mem addrs bound ctxt entries :
  BBM.for_all_pairs
    (λ '(e1, events1) '(e2, events2),
      negb <$> BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 events1 events2)
    (filter (λ entry, entry.2 ≠ []) entries) =
  BBM.for_all_pairs
    (λ '(e1, events1) '(e2, events2),
      negb <$> BBM.is_bbm_violation imem mem addrs bound ctxt e1 e2 events1 events2) entries.
Proof.
  apply for_all_pairs_filter.
  - intros [e1 events1] [e2 events2] Hempty. cbn in Hempty.
    destruct events1; [rewrite violation_nil_l; reflexivity|].
    exfalso. apply Hempty. discriminate.
  - intros [e1 events1] [e2 events2] Hempty. cbn in Hempty.
    destruct events2; [rewrite violation_nil_r; reflexivity|].
    exfalso. apply Hempty. discriminate.
Qed.

(** Parent and global conflicts use lifetime overlap. Empty histories can
    be removed from either side of those searches as well. *)
Lemma overlapping_entries_nonempty {A} bound events (entries : list (A * TLB.Entry.events))
    (P : A → Prop) :
  (∃ entry history, (entry, history) ∈ filter (λ entry, entry.2 ≠ []) entries ∧
    P entry ∧ BBM.time_overlaps bound events history = true) ↔
  (∃ entry history, (entry, history) ∈ entries ∧
    P entry ∧ BBM.time_overlaps bound events history = true).
Proof.
  split.
  - intros [entry [history [Hin Hrest]]]. apply list_elem_of_filter in Hin.
    exists entry, history. tauto.
  - intros [entry [history [Hin [HP Hoverlap]]]].
    exists entry, history. split; [|auto]. apply list_elem_of_filter. split; [|exact Hin].
    cbn. intro Hempty. subst history. rewrite time_overlaps_nil_r in Hoverlap. discriminate.
Qed.

Lemma empty_has_no_overlap {A} bound (entries : list (A * TLB.Entry.events)) :
  ¬ ∃ entry history, (entry, history) ∈ entries ∧ BBM.time_overlaps bound [] history = true.
Proof. intros [entry [history [_ Hoverlap]]]. discriminate. Qed.

Lemma check_tlb_vatlb imem mem addrs old new :
  TLB.vatlb old = TLB.vatlb new →
  BBM.check_tlb imem mem addrs old = BBM.check_tlb imem mem addrs new.
Proof. intro Hsame. unfold BBM.check_tlb. rewrite Hsame. reflexivity. Qed.

End VMBBMReplay.
