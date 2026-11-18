(******************************************************************************)
(* Histories with an inserted non-write event                                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwap.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

(** The exchange of an out-of-order pair [e1], [e2] is the composition of two
    moves of one event: removing [e2] from the original history and inserting
    it below [e1]. With [G = X ++ e1 :: H],

    - the original history is [X ++ e2 :: (e1 :: H)], [G] with [e2] inserted
      at timestamp [length H + 2];
    - the exchanged history is [(X ++ [e1]) ++ e2 :: H], [G] with [e2]
      inserted at timestamp [length H + 1].

    A thread not affected by the moved event relates its views on the two
    histories by [shift p] (inserting the event at timestamp [p]) and
    [unshift p] (removing it). This file proves the history layer of that
    relation: inserting a non-write event at timestamp [p] maps every lookup
    and every read of the shared memory by [shift p], and reading at a
    timestamp [t] of the longer history reads at [unshift p t] of the shorter
    one.

    For the TLB of a thread that is not the recipient of the inserted TLBI,
    [tlb_map (shift p)] shifts every entry event time and root time. Every
    cache maintenance operation commutes with it ([natural]): entry filling,
    root and table refills, write and TLBI refills, [fill_from] (which
    processes the inserted event as a no-op), [roll_back], [fill_cse],
    [fill_asid_root] and [fill_promise].

    Lookups do not commute exactly: an entry invalidated at timestamp [p] of
    the shorter history is valid until [p - 1] there and until [p] in the
    longer one. PromiseFirstSailVMSwapLookup relates lookup results up to
    [unshift p] on [Result.tend] and shows that merging still commutes. *)

Module VMSwapSim.
Import VMPromising.

(** * Timestamp maps *)

Definition shift (p t : nat) : nat := if decide (t < p) then t else S t.
Definition unshift (p t : nat) : nat := if decide (t < p) then t else pred t.

Lemma shift_lt p t : t < p → shift p t = t.
Proof. intro H. unfold shift. rewrite decide_True by exact H. reflexivity. Qed.

Lemma shift_ge p t : p ≤ t → shift p t = S t.
Proof. intro H. unfold shift. rewrite decide_False by lia. reflexivity. Qed.

Lemma unshift_lt p t : t < p → unshift p t = t.
Proof. intro H. unfold unshift. rewrite decide_True by exact H. reflexivity. Qed.

Lemma unshift_ge p t : p ≤ t → unshift p t = pred t.
Proof. intro H. unfold unshift. rewrite decide_False by lia. reflexivity. Qed.

Ltac shift_cases :=
  unfold shift, unshift in *; repeat case_decide; lia.

Lemma unshift_shift p t : unshift p (shift p t) = t.
Proof. shift_cases. Qed.

Lemma shift_unshift p t : t ≠ p → 0 < p → shift p (unshift p t) = t.
Proof. intros. shift_cases. Qed.

Lemma shift_ne p t : shift p t ≠ p.
Proof. shift_cases. Qed.

Lemma shift_le_iff p a b : shift p a ≤ shift p b ↔ a ≤ b.
Proof. shift_cases. Qed.

Lemma shift_lt_iff p a b : shift p a < shift p b ↔ a < b.
Proof. shift_cases. Qed.

Lemma shift_inj p a b : shift p a = shift p b → a = b.
Proof. shift_cases. Qed.

Lemma shift_max p a b : shift p (a `max` b) = shift p a `max` shift p b.
Proof. shift_cases. Qed.

Lemma unshift_max p a b : unshift p (a `max` b) = unshift p a `max` unshift p b.
Proof. shift_cases. Qed.

Lemma unshift_mono p a b : a ≤ b → unshift p a ≤ unshift p b.
Proof. shift_cases. Qed.

Lemma shift_zero p : 0 < p → shift p 0 = 0.
Proof. shift_cases. Qed.

Lemma unshift_zero p : unshift p 0 = 0.
Proof. shift_cases. Qed.

(** Comparisons with a timestamp other than [p] survive removal. *)
Lemma unshift_le_iff_ne p a b : a ≠ p → 0 < p → unshift p a ≤ unshift p b ↔ a ≤ b.
Proof. intros. shift_cases. Qed.

Lemma unshift_lt_iff_ne p a b : b ≠ p → 0 < p → unshift p a < unshift p b ↔ a < b.
Proof. intros. shift_cases. Qed.

(** * The two moves of an exchange *)

Lemma swap_as_insertions {A} (X H : list A) e1 e2 :
  (X ++ e2 :: e1 :: H = X ++ e2 :: (e1 :: H))%list ∧
  (X ++ e1 :: e2 :: H = (X ++ [e1]) ++ e2 :: H)%list ∧
  (X ++ e1 :: H = X ++ (e1 :: H))%list ∧
  (X ++ e1 :: H = (X ++ [e1]) ++ H)%list.
Proof. rewrite <- !app_assoc. auto. Qed.

(** * Generic histories *)

Section History.
Context {ev : Type}.
Local Notation mem := (PromMemory.t ev).

Lemma insert_length (l r : list ev) e :
  length (l ++ e :: r) = S (length (l ++ r)).
Proof. rewrite !length_app. cbn. lia. Qed.

(** Timestamp lookup in a history (timestamp [1] is the oldest event). *)
Definition mlookup (m : mem) (t : nat) : option ev :=
  @lookup nat ev (PromMemory.t ev) PromMemory.lookup_inst t m.

Lemma lookup_spec (m : list ev) t : mlookup m t =
  if decide (1 ≤ t ≤ length m) then nth_error m (length m - t) else None.
Proof.
  unfold mlookup, lookup, PromMemory.lookup_inst. cbv zeta.
  case_bool_decide as H0; case_decide as H.
  - lia.
  - reflexivity.
  - destruct (Nat.leb t (length m)) eqn:Hle; [reflexivity|].
    apply Nat.leb_gt in Hle. lia.
  - destruct (Nat.leb t (length m)) eqn:Hle; [|reflexivity].
    apply Nat.leb_le in Hle. lia.
Qed.

Lemma insert_lookup (l r : mem) e t :
  mlookup (l ++ e :: r) (shift (S (length r)) t) = mlookup (l ++ r) t.
Proof.
  destruct (decide (t < S (length r))) as [Hlt|Hlt].
  - rewrite shift_lt by exact Hlt.
    rewrite !lookup_spec, insert_length, length_app.
    case_decide as H1; case_decide as H2; try lia; [|reflexivity].
    + replace (S (length l + length r) - t) with (length l + S (length r - t)) by lia.
      replace (length l + length r - t) with (length l + (length r - t)) by lia.
      rewrite !nth_error_app2 by lia.
      replace (length l + S (length r - t) - length l) with (S (length r - t)) by lia.
      replace (length l + (length r - t) - length l) with (length r - t) by lia.
      reflexivity.
  - rewrite shift_ge by lia.
    rewrite !lookup_spec, insert_length, length_app.
    case_decide as H1; case_decide as H2; try lia; [|reflexivity].
    + replace (S (length l + length r) - S t) with (length l + length r - t) by lia.
      rewrite !nth_error_app1 by lia. reflexivity.
Qed.

Lemma insert_lookup_new (l r : mem) e :
  mlookup (l ++ e :: r) (S (length r)) = Some e.
Proof.
  rewrite lookup_spec, insert_length, length_app.
  case_decide; [|lia].
  replace (S (length l + length r) - S (length r)) with (length l) by lia.
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma cut_before_insert_low (l r : mem) e t : t ≤ length r →
  PromMemory.cut_before t (l ++ e :: r) = PromMemory.cut_before t (l ++ r).
Proof.
  intro Ht. unfold PromMemory.cut_before. rewrite insert_length, length_app.
  replace (S (length l + length r) - t) with (length l + S (length r - t)) by lia.
  replace (length l + length r - t) with (length l + (length r - t)) by lia.
  rewrite !drop_app_ge by lia.
  replace (length l + S (length r - t) - length l) with (S (length r - t)) by lia.
  replace (length l + (length r - t) - length l) with (length r - t) by lia.
  reflexivity.
Qed.

Lemma cut_before_insert_high (l r : mem) e t : length r < t → t ≤ S (length (l ++ r)) →
  ∃ l', PromMemory.cut_before t (l ++ e :: r) = (l' ++ e :: r)%list ∧
    PromMemory.cut_before (pred t) (l ++ r) = (l' ++ r)%list ∧
    t = length l' + S (length r).
Proof.
  intros Hlo Hhi. rewrite length_app in Hhi. unfold PromMemory.cut_before.
  rewrite insert_length, length_app.
  exists (drop (S (length l + length r) - t) l).
  rewrite !drop_app_le by lia.
  replace (S (length l + length r) - t) with (length l + length r - pred t) by lia.
  split; [reflexivity|]. split; [reflexivity|]. rewrite length_drop. lia.
Qed.

Context (get_msg : ev → option Msg.t).

Lemma insert_to_memMap imem (l r : mem) e : get_msg e = None →
  PromMemory.to_memMap get_msg imem (l ++ e :: r) = PromMemory.to_memMap get_msg imem (l ++ r).
Proof.
  intro He. unfold PromMemory.to_memMap. rewrite !foldr_app. cbn. rewrite He. reflexivity.
Qed.

Definition shift_bytes (p : nat) (bytes : list (bv 8 * nat)) : list (bv 8 * nat) :=
  map (λ bt, (bt.1, shift p bt.2)) bytes.

Lemma shift_bytes_fst p bytes : (shift_bytes p bytes).*1 = bytes.*1.
Proof.
  unfold shift_bytes. induction bytes as [|[b t] bytes IH]; cbn; [reflexivity|].
  f_equal. exact IH.
Qed.

Lemma shift_bytes_id p bytes : (∀ bt, bt ∈ bytes → bt.2 < p) → shift_bytes p bytes = bytes.
Proof.
  intro H. unfold shift_bytes. etransitivity; [|apply map_id].
  apply map_ext_in. intros [b t] Hin. cbn. rewrite shift_lt; [reflexivity|].
  apply (H (b, t)). apply list_elem_of_In. exact Hin.
Qed.

Section Read.
Context (addr : address) (size : N) (imem : memoryMap).

Lemma read_from_aux_times (m : mem) tread bytes :
  PromMemory.read_from_aux get_msg addr size imem m tread = Ok bytes →
  ∀ bt, bt ∈ bytes → bt.2 ≤ tread.
Proof.
  revert m bytes. induction tread as [|tread IH]; intros m bytes Hr bt Hin.
  - assert (Hr' : (othrow ("Memory read of unmapped bytes at " ++ pretty addr)%string
      (mem_lookup_bytes addr size imem) |$> map (.,0)) = Ok bytes)
      by (destruct m; exact Hr).
    clear Hr. rename Hr' into Hr.
    destruct (mem_lookup_bytes addr size imem) as [bs|]; cbn in Hr; [|discriminate].
    injection Hr as <-. apply list_elem_of_fmap in Hin as [b [-> _]]. cbn. lia.
  - destruct m as [|e m]; cbn [PromMemory.read_from_aux] in Hr; [discriminate|].
    destruct (get_msg e) as [msg|].
    + case_decide.
      * injection Hr as <-. apply list_elem_of_fmap in Hin as [b [-> _]]. cbn. lia.
      * destruct (PromMemory.read_from_aux get_msg addr size imem m tread) as [prev|]
          eqn:Hprev; cbn in Hr; [|discriminate].
        pose proof (IH m prev Hprev) as Hp.
        case_decide.
        -- injection Hr as <-. apply list_elem_of_lookup in Hin as [i Hi].
           change (imap ?f prev) with (stdpp_imap f prev) in Hi.
           rewrite list_lookup_imap in Hi.
           destruct (prev !! i) as [[b t]|] eqn:Hpi; [|discriminate]. cbn in Hi.
           injection Hi as <-.
           destruct (Msg.read_byte _ msg); [cbn; lia|].
           cbn. specialize (Hp (b, t) (list_elem_of_lookup_2 _ _ _ Hpi)). cbn in Hp. lia.
        -- injection Hr as <-. specialize (Hp bt Hin). lia.
    + specialize (IH m bytes Hr bt Hin). lia.
Qed.

Lemma result_fmap_shift_id p (x : result string (list (bv 8 * nat))) n :
  (∀ bytes, x = Ok bytes → ∀ bt, bt ∈ bytes → bt.2 ≤ n) → n < p →
  shift_bytes p <$> x = x.
Proof.
  intros H Hn. destruct x as [bytes|err]; [|reflexivity]. cbn. f_equal.
  apply shift_bytes_id. intros bt Hin. specialize (H bytes eq_refl bt Hin). lia.
Qed.

Lemma imap_map_comm {A B C D} (f : nat → C → D) (h : A → C) (g : nat → A → B)
    (k : B → D) (l : list A) :
  (∀ i x, f i (h x) = k (g i x)) → stdpp_imap f (map h l) = map k (stdpp_imap g l).
Proof.
  revert f g. induction l as [|x l IH]; intros f g H; cbn; [reflexivity|].
  f_equal; [apply H|]. apply IH. intros. apply H.
Qed.

(** Reading the longer history at a timestamp above the inserted event
    reads the shorter one at the previous timestamp and shifts the write
    timestamps at and above [S t]. *)
Lemma read_from_aux_insert (l r : mem) e t : get_msg e = None →
  PromMemory.read_from_aux get_msg addr size imem (l ++ e :: r) (length l + S t) =
  shift_bytes (S t) <$>
    PromMemory.read_from_aux get_msg addr size imem (l ++ r) (length l + t).
Proof.
  intro He. induction l as [|x l IH].
  - cbn [app length Nat.add]. cbn [PromMemory.read_from_aux]. rewrite He.
    symmetry. apply (result_fmap_shift_id (S t) _ t); [|lia].
    intros bytes Hr. exact (read_from_aux_times _ _ _ Hr).
  - cbn [app length]. replace (S (length l) + S t) with (S (length l + S t)) by lia.
    replace (S (length l) + t) with (S (length l + t)) by lia.
    cbn [PromMemory.read_from_aux]. destruct (get_msg x) as [msg|]; [|exact IH].
    case_decide.
    + cbn. f_equal. unfold shift_bytes. rewrite map_map. apply map_ext. intros b. cbn.
      rewrite shift_ge by lia. f_equal. lia.
    + rewrite IH.
      destruct (PromMemory.read_from_aux get_msg addr size imem (l ++ r) (length l + t))
        as [prev|err]; cbn; [|reflexivity].
      case_decide; cbn; f_equal.
      unfold shift_bytes. change (imap ?f ?l) with (stdpp_imap f l).
      apply imap_map_comm. intros i [b' t']. cbv beta. cbn [fst snd].
      destruct (Msg.read_byte _ msg); cbn [fst snd]; [|reflexivity].
      rewrite shift_ge by lia. f_equal. lia.
Qed.

(** Reading at any timestamp [t] of the history with the inserted non-write
    event reads at [unshift p t] of the history without it. *)
Lemma read_from_insert (l r : mem) e t : get_msg e = None → t ≤ S (length (l ++ r)) →
  PromMemory.read_from get_msg addr size imem (l ++ e :: r) t =
  shift_bytes (S (length r)) <$>
    PromMemory.read_from get_msg addr size imem (l ++ r) (unshift (S (length r)) t).
Proof.
  intros He Ht. unfold PromMemory.read_from.
  destruct (decide (t ≤ length r)) as [Hlow|Hhigh].
  - rewrite unshift_lt by lia. rewrite cut_before_insert_low by exact Hlow.
    symmetry. apply (result_fmap_shift_id _ _ t); [|lia].
    intros bytes Hr. exact (read_from_aux_times _ _ _ Hr).
  - destruct (cut_before_insert_high l r e t ltac:(lia) Ht) as [l' [H1 [H2 Ht']]].
    rewrite unshift_ge by lia. rewrite H1, H2, Ht'.
    replace (pred (length l' + S (length r))) with (length l' + length r) by lia.
    apply read_from_aux_insert. exact He.
Qed.

Corollary read_from_insert_shift (l r : mem) e t : get_msg e = None →
  t ≤ length (l ++ r) →
  PromMemory.read_from get_msg addr size imem (l ++ e :: r) (shift (S (length r)) t) =
  shift_bytes (S (length r)) <$>
    PromMemory.read_from get_msg addr size imem (l ++ r) t.
Proof.
  intros He Ht. rewrite read_from_insert by (try exact He; shift_cases).
  rewrite unshift_shift. reflexivity.
Qed.
End Read.

Lemma read_byte_insert addr imem (l r : mem) e t : get_msg e = None →
  t ≤ S (length (l ++ r)) →
  PromMemory.read_byte get_msg addr imem (l ++ e :: r) t =
  PromMemory.read_byte get_msg addr imem (l ++ r) (unshift (S (length r)) t).
Proof.
  intros He Ht. unfold PromMemory.read_byte. rewrite read_from_insert by assumption.
  destruct (PromMemory.read_from _ _ _ _ _ _) as [bytes|]; cbn; [|reflexivity].
  rewrite shift_bytes_fst. reflexivity.
Qed.

Lemma read_word_insert addr imem (l r : mem) e t : get_msg e = None →
  t ≤ S (length (l ++ r)) →
  PromMemory.read_word get_msg addr imem (l ++ e :: r) t =
  PromMemory.read_word get_msg addr imem (l ++ r) (unshift (S (length r)) t).
Proof.
  intros He Ht. unfold PromMemory.read_word. rewrite read_from_insert by assumption.
  destruct (PromMemory.read_from _ _ _ _ _ _) as [bytes|]; cbn; [|reflexivity].
  rewrite shift_bytes_fst. reflexivity.
Qed.

(** ** Ranges of reads *)

Section ReadAll.
Context (addr : address) (size : N) (imem : memoryMap).

Lemma read_all_aux_times (m : mem) tmin tmax reads :
  PromMemory.read_all_aux get_msg addr size imem m tmin tmax = Ok reads →
  ∀ bytes bt, bytes ∈ reads → bt ∈ bytes → bt.2 ≤ tmax.
Proof.
  revert tmax reads. induction m as [|x m IH]; intros tmax reads Hr bytes bt Hin Hbt.
  all: cbn [PromMemory.read_all_aux] in Hr.
  all: case_bool_decide as Heq.
  1, 3: subst tmax; destruct (PromMemory.read_from_aux _ _ _ _ _ _) as [b|] eqn:Hb;
    cbn in Hr; [|discriminate]; injection Hr as <-;
    apply list_elem_of_singleton in Hin as ->; exact (read_from_aux_times _ _ _ _ _ _ Hb _ Hbt).
  - destruct tmax; discriminate.
  - destruct tmax as [|tmax]; [discriminate|].
    destruct (PromMemory.read_all_aux get_msg addr size imem m tmin tmax) as [prev|]
      eqn:Hprev; cbn in Hr; [|discriminate].
    pose proof (IH tmax prev Hprev) as Hp.
    destruct (get_msg x) as [msg|].
    + case_decide.
      * injection Hr as <-. apply elem_of_cons in Hin as [->|Hin].
        -- apply list_elem_of_fmap in Hbt as [b [-> _]]. cbn. lia.
        -- specialize (Hp bytes bt Hin Hbt). lia.
      * case_decide.
        -- destruct prev as [|prevm prev']; [discriminate|]. injection Hr as <-.
           apply elem_of_cons in Hin as [->|Hin].
           ++ apply list_elem_of_lookup in Hbt as [i Hi].
              change (imap ?f ?l) with (stdpp_imap f l) in Hi.
              rewrite list_lookup_imap in Hi.
              destruct (prevm !! i) as [[b t]|] eqn:Hpi; [|discriminate]. cbn in Hi.
              injection Hi as <-.
              destruct (Msg.read_byte _ msg); [cbn; lia|].
              cbn. specialize (Hp prevm (b, t) ltac:(left) (list_elem_of_lookup_2 _ _ _ Hpi)).
              cbn in Hp. lia.
           ++ specialize (Hp bytes bt Hin Hbt). lia.
        -- injection Hr as <-. specialize (Hp bytes bt Hin Hbt). lia.
    + injection Hr as <-. specialize (Hp bytes bt Hin Hbt). lia.
Qed.

Lemma read_all_aux_insert (l r : mem) e tmin t : get_msg e = None → tmin ≤ length l + t →
  PromMemory.read_all_aux get_msg addr size imem (l ++ e :: r) (shift (S t) tmin)
    (length l + S t) =
  map (shift_bytes (S t)) <$>
    PromMemory.read_all_aux get_msg addr size imem (l ++ r) tmin (length l + t).
Proof.
  intros He Hle. induction l as [|x l IH].
  - cbn [app length Nat.add] in Hle |- *. rewrite shift_lt by lia.
    cbn [PromMemory.read_all_aux].
    rewrite bool_decide_false by lia. rewrite He.
    destruct (PromMemory.read_all_aux get_msg addr size imem r tmin t) as [prev|err] eqn:Hprev;
      cbn; [|reflexivity].
    f_equal. symmetry. etransitivity; [|apply map_id]. apply map_ext_in. intros bytes Hin.
    apply shift_bytes_id. intros bt Hbt.
    pose proof (read_all_aux_times _ _ _ _ Hprev bytes bt (proj2 (list_elem_of_In _ _) Hin) Hbt). lia.
  - cbn [length] in Hle.
    destruct (decide (tmin = S (length l + t))) as [->|Htop].
    { rewrite shift_ge by lia.
      pose proof (read_from_aux_insert addr size imem (x :: l) r e t He) as Hfrom.
      cbn [app length] in Hfrom |- *.
      replace (S (length l) + S t) with (S (length l + S t)) in Hfrom |- * by lia.
      replace (S (length l) + t) with (S (length l + t)) in Hfrom |- * by lia.
      cbn [PromMemory.read_all_aux]. rewrite !bool_decide_true by lia.
      replace (S (S (length l + t))) with (S (length l + S t)) by lia.
      rewrite Hfrom.
      destruct (PromMemory.read_from_aux get_msg addr size imem (x :: l ++ r)
        (S (length l + t))); reflexivity. }
    cbn [app length]. replace (S (length l) + S t) with (S (length l + S t)) by lia.
    replace (S (length l) + t) with (S (length l + t)) by lia.
    cbn [PromMemory.read_all_aux].
    rewrite !bool_decide_false by shift_cases. rewrite IH by lia.
    destruct (PromMemory.read_all_aux get_msg addr size imem (l ++ r) tmin (length l + t))
      as [prev|err]; cbn; [|reflexivity].
    destruct (get_msg x) as [msg|]; [|reflexivity].
    case_decide.
    + cbn. f_equal. f_equal. unfold shift_bytes. rewrite map_map. apply map_ext. intros b.
      cbn. rewrite shift_ge by lia. f_equal. lia.
    + case_decide; [|reflexivity].
      destruct prev as [|prevm prev']; cbn; [reflexivity|]. f_equal. f_equal.
      unfold shift_bytes. change (imap ?f ?l) with (stdpp_imap f l).
      apply imap_map_comm. intros i [b' t']. cbv beta. cbn [fst snd].
      destruct (Msg.read_byte _ msg); cbn [fst snd]; [|reflexivity].
      rewrite shift_ge by lia. f_equal. lia.
Qed.

(** Reading a range of the longer history whose bounds are images of
    [shift p] reads the corresponding range of the shorter one. *)
Lemma read_all_btw_insert (l r : mem) e tmin tmax : get_msg e = None →
  tmax ≤ length (l ++ r) →
  PromMemory.read_all_btw get_msg addr size imem (l ++ e :: r)
    (shift (S (length r)) tmin) (shift (S (length r)) tmax) =
  map (shift_bytes (S (length r))) <$>
    PromMemory.read_all_btw get_msg addr size imem (l ++ r) tmin tmax.
Proof.
  intros He Hmax. unfold PromMemory.read_all_btw.
  case_decide as H1; case_decide as H2;
    try (exfalso; apply shift_le_iff in H1; contradiction);
    try (exfalso; apply H1, shift_le_iff, H2); [|reflexivity].
  destruct (decide (tmax ≤ length r)) as [Hlow|Hhigh].
  - rewrite !shift_lt by lia. rewrite cut_before_insert_low by exact Hlow.
    destruct (PromMemory.read_all_aux _ _ _ _ _ _ _) as [reads|] eqn:Hr; cbn; [|reflexivity].
    f_equal. symmetry. etransitivity; [|apply map_id]. apply map_ext_in. intros bytes Hin.
    apply shift_bytes_id. intros bt Hbt.
    pose proof (read_all_aux_times _ _ _ _ Hr bytes bt (proj2 (list_elem_of_In _ _) Hin) Hbt).
    lia.
  - rewrite (shift_ge _ tmax) by lia.
    destruct (cut_before_insert_high l r e (S tmax) ltac:(lia) ltac:(lia))
      as [l' [Hc1 [Hc2 Hlen]]].
    rewrite Hc1. cbn [pred] in Hc2. rewrite Hc2, Hlen.
    replace tmax with (length l' + length r) by lia.
    apply read_all_aux_insert; [exact He|lia].
Qed.

(** A range starting at the inserted event reads the range starting just
    below it. *)
Lemma read_all_aux_insert_at (l r : mem) e t : get_msg e = None →
  PromMemory.read_all_aux get_msg addr size imem (l ++ e :: r) (S t) (length l + S t) =
  map (shift_bytes (S t)) <$>
    PromMemory.read_all_aux get_msg addr size imem (l ++ r) t (length l + t).
Proof.
  intro He. induction l as [|x l IH].
  - cbn [app length Nat.add]. cbn [PromMemory.read_all_aux].
    rewrite !bool_decide_true by lia.
    assert (Hr : PromMemory.read_all_aux get_msg addr size imem r t t =
      (PromMemory.read_from_aux get_msg addr size imem r t |$> (.:: []))).
    { destruct r; cbn [PromMemory.read_all_aux]; rewrite bool_decide_true by lia;
        reflexivity. }
    rewrite Hr. cbn [PromMemory.read_from_aux]. rewrite He.
    destruct (PromMemory.read_from_aux get_msg addr size imem r t) as [bytes|] eqn:Hb;
      cbn; [|reflexivity].
    f_equal. cbn. f_equal. symmetry. apply shift_bytes_id. intros bt Hbt.
    pose proof (read_from_aux_times addr size imem _ _ _ Hb bt Hbt). lia.
  - cbn [app length]. replace (S (length l) + S t) with (S (length l + S t)) by lia.
    replace (S (length l) + t) with (S (length l + t)) by lia.
    cbn [PromMemory.read_all_aux].
    rewrite !bool_decide_false by lia.
    replace (length l + S t) with (length l + S t) in IH by reflexivity. rewrite IH.
    destruct (PromMemory.read_all_aux get_msg addr size imem (l ++ r) t (length l + t))
      as [prev|err]; cbn; [|reflexivity].
    destruct (get_msg x) as [msg|]; [|reflexivity].
    case_decide.
    + cbn. f_equal. f_equal. unfold shift_bytes. rewrite map_map. apply map_ext. intros b.
      cbn. rewrite shift_ge by lia. f_equal. lia.
    + case_decide; [|reflexivity].
      destruct prev as [|prevm prev']; cbn; [reflexivity|]. f_equal. f_equal.
      unfold shift_bytes. change (imap ?f ?l) with (stdpp_imap f l).
      apply imap_map_comm. intros i [b' t']. cbv beta. cbn [fst snd].
      destruct (Msg.read_byte _ msg); cbn [fst snd]; [|reflexivity].
      rewrite shift_ge by lia. f_equal. lia.
Qed.

(** Reading any nonempty range of the history with the inserted non-write
    event reads the range of the history without it whose bounds are
    [unshift]ed: the remove direction. *)
Lemma read_all_btw_remove (l r : mem) e tmin tmax : get_msg e = None →
  tmin ≤ tmax → tmax ≤ S (length (l ++ r)) →
  PromMemory.read_all_btw get_msg addr size imem (l ++ e :: r) tmin tmax =
  map (shift_bytes (S (length r))) <$>
    PromMemory.read_all_btw get_msg addr size imem (l ++ r)
      (unshift (S (length r)) tmin) (unshift (S (length r)) tmax).
Proof.
  intros He Hle Hmax.
  destruct (decide (tmin = S (length r))) as [->|Hmin];
    [|destruct (decide (tmax = S (length r))) as [->|Hmaxp]].
  - rewrite unshift_ge by lia. cbn [pred].
    unfold PromMemory.read_all_btw. rewrite !decide_True by (shift_cases).
    destruct (cut_before_insert_high l r e tmax ltac:(lia) Hmax) as [l' [Hc1 [Hc2 Hlen]]].
    rewrite Hc1, (unshift_ge _ tmax) by lia. rewrite Hc2, Hlen.
    replace (pred (length l' + S (length r))) with (length l' + length r) by lia.
    apply read_all_aux_insert_at, He.
  - rewrite (unshift_ge _ (S (length r))) by lia. cbn [pred].
    rewrite unshift_lt by lia.
    unfold PromMemory.read_all_btw. rewrite !decide_True by lia.
    destruct (cut_before_insert_high l r e (S (length r)) ltac:(lia) Hmax)
      as [l' [Hc1 [Hc2 Hlen]]].
    cbn [pred] in Hc2. rewrite Hc1, Hc2.
    assert (Hl' : l' = []) by (destruct l'; [reflexivity|cbn in Hlen; lia]). subst l'.
    cbn [app]. cbn [PromMemory.read_all_aux]. rewrite bool_decide_false by lia. rewrite He.
    destruct (PromMemory.read_all_aux get_msg addr size imem r tmin (length r))
      as [reads|] eqn:Hr; cbn; [|reflexivity].
    f_equal. symmetry. etransitivity; [|apply map_id]. apply map_ext_in. intros bytes Hin.
    apply shift_bytes_id. intros bt Hbt.
    pose proof (read_all_aux_times _ _ _ _ Hr bytes bt (proj2 (list_elem_of_In _ _) Hin) Hbt).
    lia.
  - assert (Hu : unshift (S (length r)) tmax ≤ length (l ++ r)).
    { rewrite length_app in Hmax |- *. shift_cases. }
    pose proof (read_all_btw_insert l r e (unshift (S (length r)) tmin)
      (unshift (S (length r)) tmax) He Hu) as H.
    rewrite !shift_unshift in H by lia. exact H.
Qed.

End ReadAll.

(** ** Fulfilment of promises *)

Lemma insert_fulfill `{EqDecision ev} (l r : mem) e ev' (proms : list nat) :
  PromMemory.fulfill ev' (map (shift (S (length r))) proms) (l ++ e :: r) =
  shift (S (length r)) <$> PromMemory.fulfill ev' proms (l ++ r).
Proof.
  unfold PromMemory.fulfill.
  assert (Hf : filter (λ t, mlookup (l ++ e :: r) t = Some ev')
      (map (shift (S (length r))) proms) =
    map (shift (S (length r))) (filter (λ t, mlookup (l ++ r) t = Some ev') proms)).
  { induction proms as [|t proms IH]; [reflexivity|]. cbn [map].
    rewrite !filter_cons. rewrite insert_lookup.
    case_decide; cbn [map]; rewrite IH; reflexivity. }
  change (hd_error (reverse (filter (λ t, mlookup (l ++ e :: r) t = Some ev')
      (map (shift (S (length r))) proms))) =
    shift (S (length r)) <$> hd_error (reverse (filter (λ t, mlookup (l ++ r) t = Some ev')
      proms))).
  rewrite Hf. generalize (filter (λ t, mlookup (l ++ r) t = Some ev') proms) as xs.
  intro xs. unfold reverse. rewrite <- (rev_alt (map _ xs)), <- (rev_alt xs).
  rewrite <- map_rev. destruct (rev xs); reflexivity.
Qed.
End History.

(** * VM histories *)

Lemma tlbi_not_msg tlbi r k : Ev.get_msg (Ev.Tlbi tlbi r k) = None.
Proof. reflexivity. Qed.

Lemma insert_memMap_tlbi imem (l r : Memory.t) tlbi rc k :
  Memory.to_memMap imem (l ++ Ev.Tlbi tlbi rc k :: r) = Memory.to_memMap imem (l ++ r).
Proof. apply insert_to_memMap. reflexivity. Qed.

Lemma max_list_with_shift p (bytes : list (bv 8 * nat)) : 0 < p →
  max_list_with snd (shift_bytes p bytes) = shift p (max_list_with snd bytes).
Proof.
  intro Hp. induction bytes as [|[b t] bytes IH]; cbn; [symmetry; apply shift_zero, Hp|].
  change (max_list_with snd (shift_bytes p bytes)) with
    (max_list_with snd (shift_bytes p bytes)).
  rewrite IH. symmetry. apply shift_max.
Qed.

(** The PTE values of a range, with their write timestamps, after inserting a
    TLBI event at timestamp [S (length r)]. *)
Lemma read_all_pte_insert addr imem (l r : Memory.t) tlbi rc k tmin tmax :
  tmax ≤ length (l ++ r) →
  Memory.read_all_pte addr imem (l ++ Ev.Tlbi tlbi rc k :: r)
    (shift (S (length r)) tmin) (shift (S (length r)) tmax) =
  map (λ vt, (vt.1, shift (S (length r)) vt.2)) <$>
    Memory.read_all_pte addr imem (l ++ r) tmin tmax.
Proof.
  intro Hmax. unfold Memory.read_all_pte, Memory.read_all_btw.
  rewrite (read_all_btw_insert Ev.get_msg addr 8 imem l r _ tmin tmax (tlbi_not_msg _ _ _) Hmax).
  destruct (PromMemory.read_all_btw _ _ _ _ _ _ _) as [reads|]; cbn; [|reflexivity].
  f_equal. rewrite !map_map. apply map_ext. intro bytes. cbn.
  rewrite shift_bytes_fst, max_list_with_shift by lia. reflexivity.
Qed.

Lemma read_byte_insert_tlbi addr imem (l r : Memory.t) tlbi rc k t :
  t ≤ S (length (l ++ r)) →
  Memory.read_byte addr imem (l ++ Ev.Tlbi tlbi rc k :: r) t =
  Memory.read_byte addr imem (l ++ r) (unshift (S (length r)) t).
Proof. intro Ht. apply read_byte_insert; [reflexivity|exact Ht]. Qed.

Lemma read_word_insert_tlbi addr imem (l r : Memory.t) tlbi rc k t :
  t ≤ S (length (l ++ r)) →
  Memory.read_word addr imem (l ++ Ev.Tlbi tlbi rc k :: r) t =
  Memory.read_word addr imem (l ++ r) (unshift (S (length r)) t).
Proof. intro Ht. apply read_word_insert; [reflexivity|exact Ht]. Qed.

Lemma fulfill_insert_tlbi (l r : Memory.t) tlbi rc k ev (proms : list nat) :
  Memory.fulfill ev (map (shift (S (length r))) proms) (l ++ Ev.Tlbi tlbi rc k :: r) =
  shift (S (length r)) <$> Memory.fulfill ev proms (l ++ r).
Proof. apply insert_fulfill. Qed.

Lemma read_all_pte_remove addr imem (l r : Memory.t) tlbi rc k tmin tmax :
  tmin ≤ tmax → tmax ≤ S (length (l ++ r)) →
  Memory.read_all_pte addr imem (l ++ Ev.Tlbi tlbi rc k :: r) tmin tmax =
  map (λ vt, (vt.1, shift (S (length r)) vt.2)) <$>
    Memory.read_all_pte addr imem (l ++ r)
      (unshift (S (length r)) tmin) (unshift (S (length r)) tmax).
Proof.
  intros Hle Hmax. unfold Memory.read_all_pte, Memory.read_all_btw.
  rewrite (read_all_btw_remove Ev.get_msg addr 8 imem l r _ tmin tmax (tlbi_not_msg _ _ _)
    Hle Hmax).
  destruct (PromMemory.read_all_btw _ _ _ _ _ _ _) as [reads|]; cbn; [|reflexivity].
  f_equal. rewrite !map_map. apply map_ext. intro bytes. cbn.
  rewrite shift_bytes_fst, max_list_with_shift by lia. reflexivity.
Qed.

(** * Time maps on TLB caches

    A cache of a thread unaffected by the inserted event is mapped by
    [tlb_map (shift p)]: every entry event time and root time is shifted. *)

Definition map_evs (f : nat → nat) (evs : TLB.Entry.events) : TLB.Entry.events :=
  map (λ et, (et.1, f et.2)) evs.

Definition vatlb_map (f : nat → nat) (v : TLB.VATLB.t) : TLB.VATLB.t :=
  hmap (T1 := TLB.VATLB.T) (T2 := TLB.VATLB.T)
    (λ lvl m, map (λ ee, (ee.1, map_evs f ee.2)) <$> m) v.

Definition tlb_map (f : nat → nat) (c : TLB.t) : TLB.t :=
  TLB.make (vatlb_map f (TLB.vatlb c)) (TLB.pte_present c) (TLB.next_table_cache c)
    (map (λ rt, (rt.1, f rt.2)) (TLB.asid_roots c)) (TLB.ets c).

Lemma map_evs_id evs : map_evs id evs = evs.
Proof. unfold map_evs. etransitivity; [|apply map_id]. apply map_ext. intros []. reflexivity. Qed.

Lemma vatlb_ext (v w : TLB.VATLB.t) : (∀ lvl, hget lvl v = hget lvl w) → v = w.
Proof.
  intro H. destruct v as [v0 [v1 [v2 [v3 []]]]], w as [w0 [w1 [w2 [w3 []]]]].
  pose proof (H 0%fin) as H0. pose proof (H 1%fin) as H1.
  pose proof (H 2%fin) as H2. pose proof (H 3%fin) as H3.
  cbn in H0, H1, H2, H3. subst. reflexivity.
Qed.

Lemma vatlb_map_id v : vatlb_map id v = v.
Proof.
  apply vatlb_ext. intro lvl. unfold vatlb_map. rewrite hget_hmap.
  generalize (hget lvl v). unfold TLB.VATLB.T. intro m.
  apply map_eq. intro key. rewrite lookup_fmap.
  destruct (m !! key) as [entries|]; cbn; [|reflexivity]. f_equal.
  etransitivity; [|apply map_id]. apply map_ext. intros [entry evs]. cbn [fst snd].
  rewrite map_evs_id. reflexivity.
Qed.

Lemma tlb_map_id c : tlb_map id c = c.
Proof.
  destruct c as [v pp ntc roots ets]. unfold tlb_map.
  cbn [TLB.vatlb TLB.pte_present TLB.next_table_cache TLB.asid_roots TLB.ets].
  rewrite vatlb_map_id. f_equal. etransitivity; [|apply map_id].
  apply map_ext. intros []. reflexivity.
Qed.

Lemma vatlb_get_map f ctxt v :
  TLB.VATLB.get ctxt (vatlb_map f v) =
  map (λ ee, (ee.1, map_evs f ee.2)) (TLB.VATLB.get ctxt v).
Proof.
  unfold TLB.VATLB.get, vatlb_map. rewrite hget_hmap.
  generalize (hget (TLB.Ctxt.lvl ctxt) v). unfold TLB.VATLB.T. intro m.
  rewrite lookup_fmap. destruct (m !! _); reflexivity.
Qed.

Lemma lookup_assoc_map_snd {K V W} `{EqDecision K} (g : V → W) (l : list (K * V)) k :
  lookup_assoc k (map (λ kv, (kv.1, g kv.2)) l) = g <$> lookup_assoc k l.
Proof.
  induction l as [|[k' v] l IH]; [reflexivity|]. cbn [map lookup_assoc fst snd].
  case_decide; [reflexivity|exact IH].
Qed.

Lemma vatlb_lookup_map f v fe : vatlb_map f v !! fe = map_evs f <$> v !! fe.
Proof.
  unfold lookup, TLB.VATLB.lookup_fe. rewrite vatlb_get_map. apply lookup_assoc_map_snd.
Qed.

Lemma partial_alter_assoc_map {K V W} `{EqDecision K} (h : V → W)
    (g : option W → option W) (g' : option V → option V) (k : K) (l : list (K * V)) :
  (∀ x, g (h <$> x) = h <$> g' x) →
  partial_alter_assoc g k (map (λ kv, (kv.1, h kv.2)) l) =
  map (λ kv, (kv.1, h kv.2)) (partial_alter_assoc g' k l).
Proof.
  intro Hg. induction l as [|[k' v] l IH]; cbn [map partial_alter_assoc fst snd].
  - specialize (Hg None). cbn in Hg. rewrite Hg. destruct (g' None); reflexivity.
  - case_decide.
    + specialize (Hg (Some v)). cbn in Hg. rewrite Hg. destruct (g' (Some v)); reflexivity.
    + cbn [map fst snd]. rewrite IH. reflexivity.
Qed.

Lemma vatlb_partial_alter_map f (g g' : option TLB.Entry.events → option TLB.Entry.events)
    fe v :
  (∀ x, g (map_evs f <$> x) = map_evs f <$> g' x) →
  partial_alter g fe (vatlb_map f v) = vatlb_map f (partial_alter g' fe v).
Proof.
  intro Hg. destruct fe as [[lvl nd] entry].
  unfold partial_alter, TLB.VATLB.partial_alter_fe, TLB.VATLB.alter_entries.
  cbn [TLB.FE.ctxt TLB.FE.entry projT1 projT2 TLB.Ctxt.lvl TLB.Ctxt.nd].
  apply vatlb_ext. intro lvl'. destruct (decide (lvl' = lvl)) as [->|Hne].
  - rewrite hvec_get_set_same. unfold vatlb_map. rewrite !hget_hmap, hvec_get_set_same.
    generalize (hget lvl v). unfold TLB.VATLB.T. intro m.
    apply map_eq. intro key. rewrite lookup_fmap.
    destruct (decide (key = nd)) as [->|Hk].
    + rewrite !lookup_partial_alter_eq. rewrite lookup_fmap.
      destruct (m !! nd) as [entries|]; cbn [fmap option_fmap option_map]; f_equal.
      * apply partial_alter_assoc_map. exact Hg.
      * exact (partial_alter_assoc_map _ g g' entry [] Hg).
    + rewrite !lookup_partial_alter_ne by congruence. rewrite lookup_fmap. reflexivity.
  - rewrite hvec_get_set_diff by exact Hne. unfold vatlb_map.
    rewrite !hget_hmap, hvec_get_set_diff by exact Hne. reflexivity.
Qed.

Lemma tlb_map_vatlb f c : TLB.vatlb (tlb_map f c) = vatlb_map f (TLB.vatlb c).
Proof. reflexivity. Qed.

Lemma tlb_map_set_entry f c fe (l : TLB.Entry.events) :
  tlb_map f (set TLB.vatlb (partial_alter (λ _, Some l) fe) c) =
  set TLB.vatlb (partial_alter (λ _, Some (map_evs f l)) fe) (tlb_map f c).
Proof.
  destruct c. unfold tlb_map, set. cbn [TLB.vatlb TLB.pte_present TLB.next_table_cache
    TLB.asid_roots TLB.ets]. f_equal.
  symmetry. apply vatlb_partial_alter_map. intro x. reflexivity.
Qed.

(** ** Cache actions commuting with a time map *)

Local Notation action A := (stateT TLB.t (result string) A).

Definition natural {A} (f : nat → nat) (ra rb : action A) : Prop :=
  ∀ c, rb (tlb_map f c) = (λ r, (tlb_map f r.1, r.2)) <$> ra c.

Lemma fill_entry_map f time fe :
  natural f (TLB.fill_entry time fe) (TLB.fill_entry (f time) fe).
Proof.
  intro c. unfold TLB.fill_entry. cbn -[tlb_map vatlb_map]. unfold mget.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose. cbn -[tlb_map vatlb_map].
  change (TLB.VATLB.lookup_fe fe (TLB.vatlb (tlb_map f c))) with
    (TLB.vatlb (tlb_map f c) !! fe).
  change (TLB.VATLB.lookup_fe fe (TLB.vatlb c)) with (TLB.vatlb c !! fe).
  rewrite tlb_map_vatlb, vatlb_lookup_map.
  destruct (TLB.vatlb c !! fe) as [evs|] eqn:Hl; rewrite ?Hl;
    [destruct evs as [|[[|tid'] t] rest]|].
  - cbn -[tlb_map vatlb_map]. f_equal. f_equal.
    symmetry. exact (tlb_map_set_entry f c fe [(TLB.Entry.Load, time)]).
  - reflexivity.
  - cbn -[tlb_map vatlb_map]. f_equal. f_equal.
    symmetry. exact (tlb_map_set_entry f c fe ((TLB.Entry.Load, time) :: (TLB.Entry.Tlbi tid', t) :: rest)).
  - pose proof (tlb_map_set_entry f c fe [(TLB.Entry.Load, time)]) as E.
    destruct (decide (TLB.FE.is_table fe)); cbn -[tlb_map vatlb_map]; f_equal; f_equal.
    + match goal with |- set TLB.next_table_cache ?h ?S1 =
          tlb_map f (set TLB.next_table_cache ?h ?S2) =>
        transitivity (set TLB.next_table_cache h (tlb_map f S2));
        [f_equal; symmetry; exact E|reflexivity] end.
    + symmetry. exact E.
Qed.

Lemma natural_ret {A} f (x : A) : natural f (mret x) (mret x).
Proof. intro c. reflexivity. Qed.

Lemma natural_bind {A B} f (ra rb : action A) (ka kb : A → action B) :
  natural f ra rb → (∀ x, natural f (ka x) (kb x)) → natural f (ra ≫= ka) (rb ≫= kb).
Proof.
  intros Ha Hk c. unfold mbind at 1 2, st_bind. rewrite Ha.
  destruct (ra c) as [[c' x]|err]; cbn; [apply Hk|reflexivity].
Qed.

Lemma natural_fmap {A B} f (g : A → B) (ra rb : action A) :
  natural f ra rb → natural f (g <$> ra) (g <$> rb).
Proof.
  intros Ha c. unfold fmap at 1 3, st_fmap. rewrite Ha.
  destruct (ra c) as [[c' x]|err]; reflexivity.
Qed.

Lemma natural_mapM {A B} f (ga gb : A → action B) (l : list A) :
  (∀ x, natural f (ga x) (gb x)) → natural f (mapM ga l) (mapM gb l).
Proof.
  intro Hg. induction l as [|x l IH]; cbn [mapM]; [apply natural_ret|].
  apply natural_bind; [apply Hg|intro y]. apply natural_bind; [exact IH|intro k].
  apply natural_ret.
Qed.

Lemma natural_get {A} f (proj : TLB.t → A) :
  (∀ c, proj (tlb_map f c) = proj c) → natural f (mget proj) (mget proj).
Proof.
  intros Hp c.
  change ((mget proj : action A) (tlb_map f c)) with
    (Ok (tlb_map f c, proj (tlb_map f c)) : result string _).
  change ((mget proj : action A) c) with (Ok (c, proj c) : result string _).
  rewrite Hp. reflexivity.
Qed.

Lemma natural_throw {A} f (err : string) : natural f (mthrow err : action A) (mthrow err).
Proof. intro c. reflexivity. Qed.

Lemma natural_guard_or f (err : string) (P : Prop) `{Decision P} :
  natural f (guard_or err P : action P) (guard_or err P).
Proof. intro c. unfold guard_or. destruct (decide P); reflexivity. Qed.

Lemma natural_mlift {A} f (r : result string A) : natural f (mlift r) (mlift r).
Proof. intro c. destruct r; reflexivity. Qed.

Lemma natural_ntc f h :
  natural f (mset TLB.next_table_cache h) (mset TLB.next_table_cache h).
Proof. intro c. reflexivity. Qed.

Lemma natural_mset_vatlb f (g g' : TLB.VATLB.t → TLB.VATLB.t) :
  (∀ v, vatlb_map f (g v) = g' (vatlb_map f v)) →
  natural f (mset TLB.vatlb g) (mset TLB.vatlb g').
Proof.
  intros Hg c.
  change ((mset TLB.vatlb g' : action ()) (tlb_map f c)) with
    (Ok (set TLB.vatlb g' (tlb_map f c), ()) : result string _).
  change ((mset TLB.vatlb g : action ()) c) with (Ok (set TLB.vatlb g c, ()) : result string _).
  cbn [fmap result_fmap fst snd]. f_equal. f_equal.
  destruct c. unfold tlb_map, set. cbn [TLB.vatlb TLB.pte_present TLB.next_table_cache
    TLB.asid_roots TLB.ets]. rewrite Hg. reflexivity.
Qed.

Lemma lookup_imap_gmap {K A B} `{Countable K} (h : K → A → B) (m : gmap K A) key :
  (imap h m) !! key = h key <$> (m !! key).
Proof.
  change ((map_imap (λ k v, Some (h k v)) m) !! key = h key <$> (m !! key)).
  rewrite map_lookup_imap. destruct (m !! key); reflexivity.
Qed.

Lemma gmap_map_fe_comm f (g g' : TLB.FE.t → TLB.Entry.events → TLB.Entry.events) (lvl : Level)
    (m : gmap (TLB.NDCtxt.t lvl) (list (TLB.Entry.t lvl * TLB.Entry.events))) :
  (∀ fe evs, g' fe (map_evs f evs) = map_evs f (g fe evs)) →
  map (λ ee, (ee.1, map_evs f ee.2)) <$>
    imap (λ nd, map (λ '(entry, events), (entry, g (TLB.FE.make_nd lvl nd entry) events))) m =
  imap (λ nd, map (λ '(entry, events), (entry, g' (TLB.FE.make_nd lvl nd entry) events)))
    (map (λ ee, (ee.1, map_evs f ee.2)) <$> m).
Proof.
  intro Hg. apply map_eq. intro key. rewrite lookup_fmap, !lookup_imap_gmap, lookup_fmap.
  destruct (m !! key) as [entries|]; [|reflexivity]. cbn [fmap option_fmap option_map].
  f_equal. rewrite !map_map. apply map_ext. intros [entry evs]. cbn [fst snd].
  rewrite Hg. reflexivity.
Qed.

Lemma vatlb_map_fe_comm f (g g' : TLB.FE.t → TLB.Entry.events → TLB.Entry.events) v :
  (∀ fe evs, g' fe (map_evs f evs) = map_evs f (g fe evs)) →
  vatlb_map f (TLB.VATLB.map_fe g v) = TLB.VATLB.map_fe g' (vatlb_map f v).
Proof.
  intro Hg. apply vatlb_ext. intro lvl. unfold vatlb_map, TLB.VATLB.map_fe.
  rewrite !hget_hmap. apply gmap_map_fe_comm. exact Hg.
Qed.

Lemma collect_fe_map f (P : TLB.FE.t → Prop) `{∀ fe, Decision (P fe)} v :
  TLB.VATLB.collect_fe P (vatlb_map f v) = TLB.VATLB.collect_fe P v.
Proof.
  unfold TLB.VATLB.collect_fe. f_equal. extensionality acc. extensionality lvl.
  unfold vatlb_map. rewrite hget_hmap. generalize (hget lvl v). unfold TLB.VATLB.T.
  intro m. rewrite map_fold_fmap. f_equal. extensionality nd. extensionality entries.
  extensionality acc'. cbn. change (map ?g entries) with (g <$> entries).
  rewrite foldl_fmap. f_equal. extensionality a. extensionality ee.
  destruct ee. reflexivity.
Qed.

Lemma is_active_map f v fe : TLB.VATLB.is_active (vatlb_map f v) fe = TLB.VATLB.is_active v fe.
Proof.
  unfold TLB.VATLB.is_active. rewrite vatlb_lookup_map.
  destruct (v !! fe) as [[|[[] t] evs]|]; reflexivity.
Qed.

Lemma get_relevant_entries_map f asids page :
  natural f (TLB.get_relevant_entries asids page) (TLB.get_relevant_entries asids page).
Proof.
  unfold TLB.get_relevant_entries.
  apply natural_bind; [apply natural_get; reflexivity|intro entries].
  intro c.
  change ((mget TLB.vatlb ≫= ?k : action _) (tlb_map f c)) with
    (k (TLB.vatlb (tlb_map f c)) (tlb_map f c)).
  change ((mget TLB.vatlb ≫= ?k : action _) c) with (k (TLB.vatlb c) c). cbv beta.
  rewrite tlb_map_vatlb.
  rewrite (list_filter_iff (λ fe, TLB.VATLB.is_active (vatlb_map f (TLB.vatlb c)) fe ∧
      TLB.FE.is_active_asid asids fe)
    (λ fe, TLB.VATLB.is_active (TLB.vatlb c) fe ∧ TLB.FE.is_active_asid asids fe));
    [reflexivity|].
  intro fe. rewrite is_active_map. reflexivity.
Qed.

(** *** Filling against a shifted history *)

Section Fill.
Context (f : nat → nat) (imem : memoryMap) (mem mem' : Memory.t) (time : nat).
Hypothesis Hread : ∀ addr,
  Memory.read_word addr imem mem' (f time) = Memory.read_word addr imem mem time.

Lemma fill_root_map roots :
  natural f (TLB.fill_root imem mem time roots) (TLB.fill_root imem mem' (f time) roots).
Proof using Hread.
  unfold TLB.fill_root. apply natural_fmap, natural_mapM. intros [[asid val_ttbr] upper].
  apply natural_bind; [apply natural_get; reflexivity|intro indexes].
  apply natural_fmap, natural_mapM. intro idx. rewrite Hread.
  destruct (Memory.read_word _ imem mem time) as [memval|]; [|apply natural_ret].
  destruct (decide (is_table 0%fin memval)); [|apply natural_ret].
  apply natural_bind; [apply fill_entry_map|intros []; apply natural_ret].
Qed.

Lemma fill_from_entry_map fe :
  natural f (TLB.fill_from_entry imem mem time fe) (TLB.fill_from_entry imem mem' (f time) fe).
Proof using Hread.
  unfold TLB.fill_from_entry.
  apply natural_bind; [apply natural_guard_or|intros _].
  apply natural_bind; [apply natural_get; reflexivity|intro indexes].
  apply natural_bind; [intro c; destruct (child_lvl _); reflexivity|intro clvl].
  apply natural_fmap, natural_mapM. intro idx. rewrite Hread.
  destruct (Memory.read_word _ imem mem time) as [memval|]; [|apply natural_ret].
  destruct (decide (is_tlb_fillable clvl memval)); [|apply natural_ret].
  apply natural_bind; [apply natural_mlift|intro next].
  apply natural_bind; [apply fill_entry_map|intros []; [|apply natural_ret]].
  destruct (decide (is_table clvl memval)); apply natural_ret.
Qed.

Lemma fill_from_entries_step_map entries :
  natural f (TLB.fill_from_entries_step imem mem time entries)
    (TLB.fill_from_entries_step imem mem' (f time) entries).
Proof using Hread.
  unfold TLB.fill_from_entries_step. apply natural_fmap, natural_mapM.
  intro fe. apply fill_from_entry_map.
Qed.

Lemma fill_from_entries_map entries :
  natural f (TLB.fill_from_entries imem mem time entries)
    (TLB.fill_from_entries imem mem' (f time) entries).
Proof using Hread.
  unfold TLB.fill_from_entries.
  apply natural_bind; [apply fill_from_entries_step_map|intro e1].
  apply natural_bind; [apply fill_from_entries_step_map|intro e2].
  apply natural_bind; [apply fill_from_entries_step_map|intro e3].
  unfold guard_or'. apply natural_bind; [apply natural_guard_or|intros _; apply natural_ret].
Qed.

Lemma fill_from_roots_map roots :
  natural f (TLB.fill_from_roots imem mem time roots)
    (TLB.fill_from_roots imem mem' (f time) roots).
Proof using Hread.
  unfold TLB.fill_from_roots.
  apply natural_bind; [apply fill_root_map|intro entries]. apply fill_from_entries_map.
Qed.

Lemma fill_write_map roots msg :
  natural f (TLB.fill_write imem mem time roots msg)
    (TLB.fill_write imem mem' (f time) roots msg).
Proof using Hread.
  unfold TLB.fill_write.
  apply natural_bind; [apply natural_guard_or|intros _].
  apply natural_bind; [apply fill_root_map|intro lvl0].
  apply natural_bind; [apply get_relevant_entries_map|intro relevant].
  apply fill_from_entries_map.
Qed.

Lemma invalidate_map tid evs :
  map_evs f (if evs is [] then [] else (TLB.Entry.Tlbi tid, time) :: evs) =
  (if map_evs f evs is [] then [] else (TLB.Entry.Tlbi tid, f time) :: map_evs f evs).
Proof. destruct evs; reflexivity. Qed.

Lemma fill_tlbi_map roots tlbi :
  natural f (TLB.fill_tlbi imem mem time roots tlbi)
    (TLB.fill_tlbi imem mem' (f time) roots tlbi).
Proof using Hread.
  unfold TLB.fill_tlbi. destruct (TLBI.last tlbi).
  - intro c.
    change ((mget TLB.vatlb ≫= ?k : action _) (tlb_map f c)) with
      (k (TLB.vatlb (tlb_map f c)) (tlb_map f c)).
    change ((mget TLB.vatlb ≫= ?k : action _) c) with (k (TLB.vatlb c) c). cbv beta.
    rewrite tlb_map_vatlb.
    match goal with |- ?L (tlb_map f c) = _ <$> ?R c =>
      enough (Hn : natural f R L) by apply Hn end.
    apply natural_bind; [apply natural_get; intro c'; apply collect_fe_map|intro entries].
    rewrite (list_filter_iff
      (λ entry, default [] (vatlb_map f (TLB.vatlb c) !! entry) ≠ [])
      (λ entry, default [] (TLB.vatlb c !! entry) ≠ [])).
    2: { intro entry. rewrite vatlb_lookup_map.
         destruct (TLB.vatlb c !! entry) as [[|ev evs]|]; cbn; split; congruence. }
    apply natural_bind; [|intro parents; apply fill_from_entries_map].
    apply natural_fmap, natural_mapM. intro entry.
    apply natural_bind; [|intros _; apply get_relevant_entries_map].
    apply natural_mset_vatlb. intro v. symmetry. apply vatlb_partial_alter_map.
    intros [evs|]; [|reflexivity]. cbn [fmap option_fmap option_map].
    f_equal. symmetry. apply invalidate_map.
  - apply natural_bind; [|intros _; apply fill_from_roots_map].
    apply natural_mset_vatlb. intro v. apply vatlb_map_fe_comm.
    intros fe evs. case_decide; [|reflexivity]. symmetry. apply invalidate_map.
Qed.

Lemma fill_event_map tid roots ev :
  natural f (TLB.fill_event tid imem mem time roots ev)
    (TLB.fill_event tid imem mem' (f time) roots ev).
Proof using Hread.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch].
  - apply fill_write_map.
  - case_decide; [apply fill_tlbi_map|apply natural_ret].
Qed.

End Fill.

Lemma fill_from_roots_nil imem mem t c : TLB.fill_from_roots imem mem t [] c = Ok (c, ()).
Proof. reflexivity. Qed.

(** ** Refilling over a history with an inserted TLBI for another recipient

    The cache of thread [tid] on [l ++ r] and on [l ++ Ev.Tlbi tlbi rc k :: r]
    with [tid ≠ rc] are related by [tlb_map (shift p)], [p = S (length r)]:
    refilling a range of the longer history processes the inserted event as a
    no-op and every other event at its shifted timestamp. *)

Section Shifted.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

Definition map_roots (g : nat → nat) (roots : list (bv 16 * bv 64 * bool * nat)) :=
  map (λ rt, (rt.1, g rt.2)) roots.

Lemma map_roots_fst g roots : (map_roots g roots).*1 = roots.*1.
Proof.
  induction roots as [|[x t] roots IH]; [reflexivity|]. unfold map_roots in *. cbn.
  f_equal. exact IH.
Qed.

Lemma filter_map_roots_lt g tb ta roots : (∀ t, g t < tb ↔ t < ta) →
  filter (λ '(_, time), time < tb) (map_roots g roots) =
  map_roots g (filter (λ '(_, time), time < ta) roots).
Proof.
  intro H. induction roots as [|[x t] roots IH]; [reflexivity|].
  unfold map_roots in *. cbn [map fst snd]. rewrite !filter_cons.
  pose proof (H t). repeat case_decide; try tauto; cbn [map fst snd]; rewrite ?IH; reflexivity.
Qed.

Lemma filter_map_roots_eq g tb ta roots : (∀ t, g t = tb ↔ t = ta) →
  filter (λ '(_, time), time = tb) (map_roots g roots) =
  map_roots g (filter (λ '(_, time), time = ta) roots).
Proof.
  intro H. induction roots as [|[x t] roots IH]; [reflexivity|].
  unfold map_roots in *. cbn [map fst snd]. rewrite !filter_cons.
  pose proof (H t). repeat case_decide; try tauto; cbn [map fst snd]; rewrite ?IH; reflexivity.
Qed.

Lemma filter_map_roots_eq_none g tb roots : (∀ t, g t ≠ tb) →
  filter (λ '(_, time), time = tb) (map_roots g roots) = [].
Proof.
  intro H. induction roots as [|[x t] roots IH]; [reflexivity|].
  unfold map_roots in *. cbn [map fst snd]. rewrite filter_cons.
  case_decide; [exfalso; eapply H; eassumption|exact IH].
Qed.

Lemma read_shifted t : t ≤ length mem →
  ∀ addr, Memory.read_word addr imem mem' (f t) = Memory.read_word addr imem mem t.
Proof.
  intros Ht addr. rewrite read_word_insert_tlbi by shift_cases. rewrite unshift_shift.
  reflexivity.
Qed.

Lemma fill_event_shifted t roots ev : t ≤ length mem →
  natural f (TLB.fill_event tid imem mem t roots ev)
    (TLB.fill_event tid imem mem' (f t) roots ev).
Proof. intro Ht. apply fill_event_map, read_shifted, Ht. Qed.

Lemma fill_from_roots_shifted t roots : t ≤ length mem →
  natural f (TLB.fill_from_roots imem mem t roots)
    (TLB.fill_from_roots imem mem' (f t) roots).
Proof. intro Ht. apply fill_from_roots_map, read_shifted, Ht. Qed.

(** Bounds of the refilled range: the shorter range starts at [tmin], the
    longer one at its image, or at the inserted event when [tmin = p]. *)
Definition start_rel (tmin tmin' : nat) : Prop :=
  tmin' = f tmin ∨ (tmin = p ∧ tmin' = p).

(** Below the inserted event the two refills coincide. *)
Lemma fill_from_btw_below tmax : ∀ roots iter tmin tmin', tmax < p →
  start_rel tmin tmin' → length iter ≤ length mem →
  natural f (TLB.fill_from_btw tid imem mem roots tmin tmax iter)
    (TLB.fill_from_btw tid imem mem' (map_roots f roots) tmin' tmax iter).
Proof.
  induction tmax as [|tmax IH]; intros roots iter tmin tmin' Hp Hmin Hiter;
    cbn [TLB.fill_from_btw].
  all: unfold start_rel in Hmin.
  all: case_decide as H1; case_decide as H2;
    try (exfalso; unfold shift in *; repeat case_decide; lia).
  1, 3: apply natural_ret.
  - apply natural_throw.
  - destruct iter as [|ev nmem]; [apply natural_throw|].
    rewrite (filter_map_roots_lt f (S tmax) (S tmax)) by (intro t; shift_cases).
    rewrite (filter_map_roots_eq f (S tmax) (S tmax)) by (intro t; shift_cases).
    rewrite !map_roots_fst.
    apply natural_bind; [apply IH; [lia|exact Hmin|cbn in Hiter; lia]|intros _].
    pose proof (fill_event_shifted (S tmax)
      (filter (λ '(_, time), time < S tmax) roots).*1 ev) as Hev.
    pose proof (fill_from_roots_shifted (S tmax)
      (filter (λ '(_, time), time = S tmax) roots).*1) as Hroots.
    rewrite shift_lt in Hev, Hroots by lia.
    apply natural_bind; [apply Hev; rewrite length_app in *; lia|intros _].
    apply Hroots. rewrite length_app. lia.
Qed.

Lemma fill_from_btw_stop m roots tmin tmax iter : tmax < tmin →
  TLB.fill_from_btw tid imem m roots tmin tmax iter = mret ().
Proof. intro H. destruct tmax; cbn [TLB.fill_from_btw]; case_decide; [reflexivity|lia|reflexivity|lia]. Qed.

(** Roots visible only from timestamp [q] on do not matter below [q]. *)
Lemma fill_from_btw_prefilter m roots tmin tmax iter q : tmax < q →
  TLB.fill_from_btw tid imem m (filter (λ '(_, time), time < q) roots) tmin tmax iter =
  TLB.fill_from_btw tid imem m roots tmin tmax iter.
Proof.
  intro Hq. destruct tmax as [|tmax]; cbn [TLB.fill_from_btw]; [reflexivity|].
  rewrite !list_filter_filter.
  rewrite (list_filter_iff
    (λ x, (λ '(_, time), time < S tmax) x ∧ (λ '(_, time), time < q) x)
    (λ '(_, time), time < S tmax)) by (intros [x t]; cbn; lia).
  rewrite (list_filter_iff
    (λ x, (λ '(_, time), time = S tmax) x ∧ (λ '(_, time), time < q) x)
    (λ '(_, time), time = S tmax)) by (intros [x t]; cbn; lia).
  reflexivity.
Qed.

Lemma natural_bind_id {A} f (ra : action A) (rb : action A) (kb : A → action A) :
  natural f ra rb → (∀ x c, kb x c = Ok (c, x)) → natural f ra (rb ≫= kb).
Proof.
  intros Ha Hk c. unfold mbind at 1, st_bind. rewrite Ha.
  destruct (ra c) as [[c' x]|err]; cbn; [apply Hk|reflexivity].
Qed.

Hypothesis Hrc : tid ≠ rc.

Lemma inserted_event_noop roots c :
  (TLB.fill_event tid imem mem' p roots (Ev.Tlbi tlbi rc k) ≫= λ _,
    TLB.fill_from_roots imem mem' p []) c = Ok (c, ()).
Proof using Hrc.
  unfold TLB.fill_event. case_decide; [contradiction|]. reflexivity.
Qed.

(** At and above the inserted event, the longer refill processes the inserted
    event as a no-op. *)
Lemma fill_from_btw_above l' : ∀ roots tmin tmin', start_rel tmin tmin' →
  length l' ≤ length l →
  natural f (TLB.fill_from_btw tid imem mem roots tmin (length (l' ++ r)) (l' ++ r))
    (TLB.fill_from_btw tid imem mem' (map_roots f roots) tmin' (S (length (l' ++ r)))
      (l' ++ Ev.Tlbi tlbi rc k :: r)).
Proof using Hrc.
  induction l' as [|x l' IH]; intros roots tmin tmin' Hmin Hl; unfold start_rel in Hmin.
  - cbn [app length]. cbn [TLB.fill_from_btw]. case_decide as Hb.
    + rewrite fill_from_btw_stop by (unfold shift in *; repeat case_decide; lia).
      apply natural_ret.
    + rewrite (filter_map_roots_lt f p p) by (intro t; shift_cases).
      rewrite (filter_map_roots_eq_none f p) by (intro t; apply shift_ne).
      rewrite <- (fill_from_btw_prefilter mem roots tmin (length r) r p) by lia.
      intro c. unfold mbind at 1, st_bind.
      rewrite (fill_from_btw_below (length r) (filter (λ '(_, time), time < p) roots) r
        tmin tmin' ltac:(lia) Hmin ltac:(rewrite length_app; lia) c).
      destruct (TLB.fill_from_btw tid imem mem _ tmin (length r) r c) as [[c' []]|err];
        cbn [fmap result_fmap]; [|reflexivity].
      exact (inserted_event_noop _ (tlb_map f c')).
  - cbn [app length]. cbn [TLB.fill_from_btw].
    assert (Hge : p ≤ S (length (l' ++ r))) by (rewrite length_app; lia).
    case_decide as H1; case_decide as H2;
      try (exfalso; unfold shift in *; repeat case_decide; lia).
    + apply natural_ret.
    + rewrite (filter_map_roots_lt f (S (S (length (l' ++ r)))) (S (length (l' ++ r))))
        by (intro t; shift_cases).
      rewrite (filter_map_roots_eq f (S (S (length (l' ++ r)))) (S (length (l' ++ r))))
        by (intro t; shift_cases).
      rewrite !map_roots_fst.
      apply natural_bind; [apply IH; [exact Hmin|cbn in Hl; lia]|intros _].
      pose proof (fill_event_shifted (S (length (l' ++ r)))
        (filter (λ '(_, time), time < S (length (l' ++ r))) roots).*1 x) as Hev.
      pose proof (fill_from_roots_shifted (S (length (l' ++ r)))
        (filter (λ '(_, time), time = S (length (l' ++ r))) roots).*1) as Hroots.
      rewrite shift_ge in Hev, Hroots by lia.
      apply natural_bind; [apply Hev; rewrite !length_app in *; cbn in Hl; lia|intros _].
      apply Hroots. rewrite !length_app in *. cbn in Hl. lia.
Qed.

(** Refilling to the end of the history. *)
Theorem fill_from_shifted roots tmin tmin' : start_rel tmin tmin' →
  natural f (TLB.fill_from tid imem mem roots tmin)
    (TLB.fill_from tid imem mem' (map_roots f roots) tmin').
Proof using Hrc.
  intro Hmin. unfold TLB.fill_from. rewrite insert_length.
  exact (fill_from_btw_above l roots tmin tmin' Hmin (le_n _)).
Qed.

End Shifted.

(** ** Cache maintenance operations *)

Lemma natural_mset_roots f g g' :
  (∀ rs, map_roots f (g rs) = g' (map_roots f rs)) →
  natural f (mset TLB.asid_roots g) (mset TLB.asid_roots g').
Proof.
  intros Hg c.
  change ((mset TLB.asid_roots g' : action ()) (tlb_map f c)) with
    (Ok (set TLB.asid_roots g' (tlb_map f c), ()) : result string _).
  change ((mset TLB.asid_roots g : action ()) c) with
    (Ok (set TLB.asid_roots g c, ()) : result string _).
  cbn [fmap result_fmap fst snd]. f_equal. f_equal.
  destruct c. unfold tlb_map, set. cbn [TLB.vatlb TLB.pte_present TLB.next_table_cache
    TLB.asid_roots TLB.ets]. f_equal. symmetry. exact (Hg _).
Qed.

Lemma natural_get_roots {A} f (ka kb : list (bv 16 * bv 64 * bool * nat) → action A) :
  (∀ rs, natural f (ka rs) (kb (map_roots f rs))) →
  natural f (mget TLB.asid_roots ≫= ka) (mget TLB.asid_roots ≫= kb).
Proof.
  intros Hk c.
  change ((mget TLB.asid_roots ≫= kb : action A) (tlb_map f c)) with
    (kb (TLB.asid_roots (tlb_map f c)) (tlb_map f c)).
  change ((mget TLB.asid_roots ≫= ka : action A) c) with (ka (TLB.asid_roots c) c).
  apply Hk.
Qed.

Lemma roll_back_map f time time' : (∀ t, f t ≤ time' ↔ t ≤ time) →
  natural f (TLB.roll_back time) (TLB.roll_back time').
Proof.
  intro Hf. unfold TLB.roll_back. apply natural_mset_vatlb. intro v.
  apply vatlb_map_fe_comm. intros fe evs. unfold map_evs.
  induction evs as [|[ev t] evs IH]; [reflexivity|]. cbn [map fst snd].
  rewrite !filter_cons. pose proof (Hf t).
  repeat case_decide; try tauto; cbn [map fst snd]; rewrite ?IH; reflexivity.
Qed.

Section Maintenance.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

Lemma start_rel_succ time : start_rel r (S time) (S (f time)).
Proof.
  clear Hrc. unfold start_rel.
  destruct (decide (time = length r)) as [->|Hne]; shift_cases.
Qed.

Theorem fill_cse_shifted time ttbr0 ttbr1 :
  natural f (TLB.fill_cse tid imem mem time ttbr0 ttbr1)
    (TLB.fill_cse tid imem mem' (f time) ttbr0 ttbr1).
Proof using Hrc.
  unfold TLB.fill_cse.
  apply natural_bind; [apply roll_back_map; intro t; apply shift_le_iff|intros _].
  destruct ttbr1 as [ttbr1|].
  - set (roots := [(bv_extract 48 16 ttbr0, ttbr0, false, time);
      (bv_extract 48 16 ttbr0, ttbr1, true, time)]).
    change [(bv_extract 48 16 ttbr0, ttbr0, false, f time);
      (bv_extract 48 16 ttbr0, ttbr1, true, f time)] with (map_roots f roots).
    apply natural_bind; [apply natural_mset_roots; reflexivity|intros _].
    apply fill_from_shifted; [exact Hrc|apply start_rel_succ].
  - set (roots := [(bv_extract 48 16 ttbr0, ttbr0, false, time)]).
    change [(bv_extract 48 16 ttbr0, ttbr0, false, f time)] with (map_roots f roots).
    apply natural_bind; [apply natural_mset_roots; reflexivity|intros _].
    apply fill_from_shifted; [exact Hrc|apply start_rel_succ].
Qed.

Theorem fill_asid_root_shifted root time : time ≤ length mem →
  natural f (TLB.fill_asid_root tid imem mem root time)
    (TLB.fill_asid_root tid imem mem' root (f time)).
Proof using Hrc.
  intro Ht. unfold TLB.fill_asid_root.
  apply natural_bind; [apply roll_back_map; intro t; apply shift_le_iff|intros _].
  apply natural_bind; [apply natural_mset_roots; reflexivity|intros _].
  apply natural_bind; [apply fill_from_roots_shifted, Ht|intros _].
  apply natural_get_roots. intro rs.
  apply fill_from_shifted; [exact Hrc|apply start_rel_succ].
Qed.

(** A new event appended to both histories. *)
Theorem fill_promise_shifted ev :
  natural f (TLB.fill_promise tid imem (ev :: mem) ev)
    (TLB.fill_promise tid imem (ev :: mem') ev).
Proof.
  clear Hrc. unfold TLB.fill_promise. apply natural_get_roots. intro rs. rewrite map_roots_fst.
  pose proof (fill_event_shifted tid imem (ev :: l) r tlbi rc k (length (ev :: l ++ r))
    rs.*1 ev (le_n _)) as H.
  cbn [app] in H. rewrite shift_ge in H by (cbn [length]; rewrite length_app; lia).
  cbn [length] in H |- *. rewrite insert_length. exact H.
Qed.

End Maintenance.

End VMSwapSim.
