From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent.

#[local] Open Scope stdpp.

Definition code_covers_range (code : code_region) (addr : address) (size : N) :=
  ∀ a, addr_in_range addr size a → code a.

Lemma code_miss_disjoint code addr size msg :
  (0 < size)%N → (0 < Msg.size msg)%N →
  code_covers_range code addr size →
  event_misses_code Msg.read_byte code msg →
  ¬ Msg.overlap addr size msg.
Proof.
  intros Hsize Hmsgsize Hcode Hmiss Hoverlap.
  destruct (proj1 (addr_overlap_spec addr size (Msg.addr msg) (Msg.size msg))
    (conj Hoverlap (conj Hsize Hmsgsize)))
    as [i [j [Hi [Hj Hij]]]].
  assert (Hinside : addr_in_range (Msg.addr msg) (Msg.size msg)
      (addr_addN addr i)).
  { apply addr_in_range_spec. exists j. split; [symmetry; exact Hij|exact Hj]. }
  specialize (Hmiss (addr_addN addr i)).
  assert (Hcovered : code (addr_addN addr i)).
  { apply Hcode. apply addr_in_range_spec. exists i. auto. }
  specialize (Hmiss Hcovered).
  unfold Msg.read_byte in Hmiss.
  rewrite (decide_True _ _ Hinside) in Hmiss.
  discriminate.
Qed.

(** Appending an event outside the read range leaves both bytes and their
    source timestamps unchanged, including unmapped-memory errors. *)
Lemma read_from_aux_cons_disjoint {ev : Type} (get_msg : ev → option Msg.t)
    addr size imem (mem : PromMemory.t ev) event :
  (0 < size)%N →
  (∀ msg, get_msg event = Some msg → ¬ Msg.overlap addr size msg) →
  PromMemory.read_from_aux get_msg addr size imem
    (event :: mem) (length (event :: mem)) =
  PromMemory.read_from_aux get_msg addr size imem mem (length mem).
Proof.
  intros Hsize Hdisjoint.
  cbn [length PromMemory.read_from_aux].
  destruct (get_msg event) as [msg|] eqn:Hmsg; [|reflexivity].
  specialize (Hdisjoint msg eq_refl).
  destruct (decide (Msg.addr msg = addr ∧ Msg.size msg = size)) as [Heq|Hneq].
  - destruct Heq as [Ha Hs].
    exfalso. apply Hdisjoint.
    unfold Msg.overlap. rewrite Ha, Hs.
    apply addr_overlap_refl. exact Hsize.
  - destruct (PromMemory.read_from_aux get_msg addr size imem mem (length mem));
      cbn; [|reflexivity].
    rewrite (decide_False _ _ Hdisjoint). reflexivity.
Qed.

Lemma read_initial_cons_disjoint {ev : Type} (get_msg : ev → option Msg.t)
    addr size imem (mem : PromMemory.t ev) event :
  (0 < size)%N →
  (∀ msg, get_msg event = Some msg → ¬ Msg.overlap addr size msg) →
  PromMemory.read_initial get_msg addr size imem (event :: mem) =
  PromMemory.read_initial get_msg addr size imem mem.
Proof.
  intros Hsize Hdisjoint.
  unfold PromMemory.read_initial.
  rewrite read_from_aux_cons_disjoint by assumption.
  reflexivity.
Qed.

Lemma read_from_aux_cons_empty {ev : Type} (get_msg : ev → option Msg.t)
    addr size imem (mem : PromMemory.t ev) event msg :
  (0 < size)%N → get_msg event = Some msg → Msg.size msg = 0%N →
  PromMemory.read_from_aux get_msg addr size imem
    (event :: mem) (length (event :: mem)) =
  PromMemory.read_from_aux get_msg addr size imem mem (length mem).
Proof.
  intros Hsize Hmsg Hempty.
  assert (Hread : ∀ a, Msg.read_byte a msg = None).
  {
    intro a. unfold Msg.read_byte.
    rewrite decide_False.
    - reflexivity.
    - unfold addr_in_range. rewrite Hempty. lia.
  }
  cbn [length PromMemory.read_from_aux]. rewrite Hmsg.
  destruct (decide (Msg.addr msg = addr ∧ Msg.size msg = size)) as [Heq|Hneq].
  - destruct Heq as [_ Hs]. exfalso. lia.
  - destruct (PromMemory.read_from_aux get_msg addr size imem mem (length mem))
      as [bytes|err]; cbn; [|reflexivity].
    destruct (decide (Msg.overlap addr size msg)); [|reflexivity].
    f_equal.
    transitivity (imap (const id) bytes).
    + apply imap_ext. intros i byte Hi. rewrite Hread. reflexivity.
    + unfold imap, list_imap. rewrite imap_const. apply list_fmap_id.
Qed.

Lemma read_from_aux_cons_code_miss {ev : Type} (get_msg : ev → option Msg.t)
    code addr size imem (mem : PromMemory.t ev) event :
  (0 < size)%N → code_covers_range code addr size →
  (∀ msg, get_msg event = Some msg → event_misses_code Msg.read_byte code msg) →
  PromMemory.read_from_aux get_msg addr size imem
    (event :: mem) (length (event :: mem)) =
  PromMemory.read_from_aux get_msg addr size imem mem (length mem).
Proof.
  intros Hsize Hcode Hmiss.
  destruct (get_msg event) as [msg|] eqn:Hget.
  - destruct (decide (Msg.size msg = 0%N)) as [Hempty|Hnonempty].
    + eapply read_from_aux_cons_empty; eauto.
    + apply read_from_aux_cons_disjoint; [exact Hsize|].
      intros msg' Hmsg'. rewrite Hget in Hmsg'. inversion Hmsg'; subst msg'.
      eapply code_miss_disjoint; [exact Hsize|lia|exact Hcode|].
      apply Hmiss. reflexivity.
  - cbn [length PromMemory.read_from_aux]. rewrite Hget. reflexivity.
Qed.

Lemma read_initial_cons_code_miss {ev : Type} (get_msg : ev → option Msg.t)
    code addr size imem (mem : PromMemory.t ev) event :
  (0 < size)%N → code_covers_range code addr size →
  (∀ msg, get_msg event = Some msg → event_misses_code Msg.read_byte code msg) →
  PromMemory.read_initial get_msg addr size imem (event :: mem) =
  PromMemory.read_initial get_msg addr size imem mem.
Proof.
  intros Hsize Hcode Hmiss.
  unfold PromMemory.read_initial.
  rewrite (read_from_aux_cons_code_miss get_msg code addr size imem mem event)
    by assumption.
  reflexivity.
Qed.

Lemma UMPromising_ifetch_cons_disjoint addr imem mem msg :
  ¬ Msg.overlap addr 4 msg →
  UMPromising.read_ifetch addr imem (msg :: mem) =
  UMPromising.read_ifetch addr imem mem.
Proof.
  intro Hdisjoint.
  unfold UMPromising.read_ifetch, UMPromising.Memory.read_initial.
  rewrite read_initial_cons_disjoint.
  - reflexivity.
  - lia.
  - intros msg' Heq. inversion Heq; subst. exact Hdisjoint.
Qed.

Lemma VMPromising_ifetch_cons_disjoint addr imem mem event :
  (∀ msg, Ev.get_msg event = Some msg → ¬ Msg.overlap addr 4 msg) →
  VMPromising.read_imem imem addr (event :: mem) =
  VMPromising.read_imem imem addr mem.
Proof.
  intro Hdisjoint.
  unfold VMPromising.read_imem, VMPromising.Memory.read_initial.
  rewrite read_initial_cons_disjoint.
  - reflexivity.
  - lia.
  - exact Hdisjoint.
Qed.
