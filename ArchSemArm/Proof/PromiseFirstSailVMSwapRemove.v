(******************************************************************************)
(* Cache maintenance over a history with a removed TLBI                       *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapSim PromiseFirstSailVMCacheHistory
  PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheTraversal PromiseFirstSailVMCacheIndexed
  PromiseFirstSailVMCacheLastTLBI PromiseFirstSailVMCacheConfig PromiseFirstSailVMCacheContext
  PromiseFirstSailVMCacheSim PromiseFirstSailVMCacheExchange PromiseFirstSailVMCacheEvents
  PromiseFirstSailVMCacheIndex PromiseFirstSailVMCacheOrder PromiseFirstSailVMCacheRollback.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

(** The removal direction of the exchange simulation, at the level of the
    cache of a thread [tid] that is not the recipient of the TLBI
    [Ev.Tlbi tlbi rc k] at timestamp [p = S (length r)] of the longer history
    [l ++ Ev.Tlbi tlbi rc k :: r]. A timestamp [t] of the longer history is
    read at [unshift p t] of the shorter history [l ++ r], so [p] collapses
    onto [p - 1].

    [unshift p] factors as [unshift p ∘ collapse p], where [collapse p] maps
    [p] to [p - 1] inside the longer history, and [shift p ∘ unshift p =
    collapse p]. A cache operation of the longer history therefore commutes
    with [tlb_map (unshift p)] when it commutes with [tlb_map (collapse p)]
    ([natural_remove_collapse]): the insertion lemmas of VMSwapSim give the
    rest. Collapsing commutes with every fill at a timestamp of the longer
    history (both read the same memory, the event at [p] is a no-op for
    [tid]) and with [roll_back] at any time other than [p - 1]. *)

Module VMSwapRemove.
Import VMPromising VMSwapSim.
Local Notation action A := (stateT TLB.t (result string) A).

(** * Collapsing [p] onto [p - 1] *)

Definition collapse (p t : nat) : nat := if decide (t = p) then pred p else t.

Ltac collapse_cases := unfold collapse, shift, unshift in *; repeat case_decide; lia.

Lemma collapse_ne p t : t ≠ p → collapse p t = t.
Proof. intro H. unfold collapse. rewrite decide_False by exact H. reflexivity. Qed.

Lemma collapse_at p : collapse p p = pred p.
Proof. unfold collapse. rewrite decide_True by reflexivity. reflexivity. Qed.

Lemma collapse_le p t : collapse p t ≤ t.
Proof. collapse_cases. Qed.

Lemma shift_unshift_collapse p t : 0 < p → shift p (unshift p t) = collapse p t.
Proof. intro. collapse_cases. Qed.

Lemma unshift_collapse p t : unshift p (collapse p t) = unshift p t.
Proof. collapse_cases. Qed.

Lemma collapse_le_iff p a b : b ≠ pred p → 0 < p → collapse p a ≤ collapse p b ↔ a ≤ b.
Proof. intros. collapse_cases. Qed.

Lemma unshift_le_iff_npred p a b : b ≠ pred p → 0 < p → unshift p a ≤ unshift p b ↔ a ≤ b.
Proof. intros. collapse_cases. Qed.

Lemma unshift_le_length p t n : t ≤ S n → p ≤ S n → unshift p t ≤ n.
Proof. intros. collapse_cases. Qed.

(** * Composing cache maps *)

Lemma map_evs_compose a b evs : map_evs a (map_evs b evs) = map_evs (a ∘ b) evs.
Proof. unfold map_evs. rewrite map_map. reflexivity. Qed.

Lemma map_evs_ext a b evs : (∀ t, a t = b t) → map_evs a evs = map_evs b evs.
Proof. intro H. unfold map_evs. apply map_ext. intros [x t]. cbn. rewrite H. reflexivity. Qed.

Lemma vatlb_map_compose a b v : vatlb_map a (vatlb_map b v) = vatlb_map (a ∘ b) v.
Proof.
  apply vatlb_ext. intro lvl. unfold vatlb_map. rewrite !hget_hmap.
  generalize (hget lvl v). unfold TLB.VATLB.T. intro m.
  apply map_eq. intro key. rewrite !lookup_fmap.
  destruct (m !! key) as [entries|]; cbn; [|reflexivity]. f_equal.
  rewrite map_map. apply map_ext. intros [entry evs]. cbn [fst snd].
  rewrite map_evs_compose. reflexivity.
Qed.

Lemma vatlb_map_ext a b v : (∀ t, a t = b t) → vatlb_map a v = vatlb_map b v.
Proof.
  intro H. apply vatlb_ext. intro lvl. unfold vatlb_map. rewrite !hget_hmap.
  generalize (hget lvl v). unfold TLB.VATLB.T. intro m.
  apply map_eq. intro key. rewrite !lookup_fmap.
  destruct (m !! key) as [entries|]; cbn; [|reflexivity]. f_equal.
  apply map_ext. intros [entry evs]. cbn [fst snd].
  rewrite (map_evs_ext a b evs H). reflexivity.
Qed.

Lemma tlb_map_compose a b c : tlb_map a (tlb_map b c) = tlb_map (a ∘ b) c.
Proof.
  destruct c as [v pp ntc roots ets]. unfold tlb_map.
  cbn [TLB.vatlb TLB.pte_present TLB.next_table_cache TLB.asid_roots TLB.ets].
  rewrite vatlb_map_compose, map_map. reflexivity.
Qed.

Lemma tlb_map_ext a b c : (∀ t, a t = b t) → tlb_map a c = tlb_map b c.
Proof.
  intro H. destruct c as [v pp ntc roots ets]. unfold tlb_map.
  cbn [TLB.vatlb TLB.pte_present TLB.next_table_cache TLB.asid_roots TLB.ets].
  rewrite (vatlb_map_ext a b v H). f_equal.
  apply map_ext. intros [x t]. cbn. rewrite H. reflexivity.
Qed.

Lemma natural_compose {A} a b (ra rb rc : action A) :
  natural a ra rb → natural b rb rc → natural (b ∘ a) ra rc.
Proof.
  intros Hab Hbc c. rewrite <- tlb_map_compose, Hbc, Hab.
  destruct (ra c) as [[c' x]|err]; cbn [fmap result_fmap fst snd]; [|reflexivity].
  rewrite tlb_map_compose. reflexivity.
Qed.

Lemma natural_ext {A} a b (ra rb : action A) : (∀ t, a t = b t) → natural a ra rb → natural b ra rb.
Proof.
  intros H Ha c. rewrite <- (tlb_map_ext a b c H), Ha.
  destruct (ra c) as [[c' x]|err]; cbn [fmap result_fmap fst snd]; [|reflexivity].
  rewrite (tlb_map_ext a b c' H). reflexivity.
Qed.

Section Factor.
Context (p : nat) (Hp : 0 < p).

Lemma tlb_map_unshift_collapse c : tlb_map (unshift p) (tlb_map (collapse p) c) = tlb_map (unshift p) c.
Proof. rewrite tlb_map_compose. apply tlb_map_ext. intro t. apply unshift_collapse. Qed.

Lemma tlb_map_shift_unshift c : tlb_map (shift p) (tlb_map (unshift p) c) = tlb_map (collapse p) c.
Proof using Hp. rewrite tlb_map_compose. apply tlb_map_ext. intro t. apply shift_unshift_collapse, Hp. Qed.

Lemma tlb_map_unshift_shift c : tlb_map (unshift p) (tlb_map (shift p) c) = c.
Proof.
  rewrite tlb_map_compose.
  etransitivity; [apply tlb_map_ext with (b := id); intro t; apply unshift_shift|apply tlb_map_id].
Qed.

(** An insertion square read backwards on a collapsed cache. *)
Lemma natural_remove {A} (ra rb : action A) : natural (shift p) ra rb →
  ∀ c', ra (tlb_map (unshift p) c') =
    (λ r, (tlb_map (unshift p) r.1, r.2)) <$> rb (tlb_map (collapse p) c').
Proof using Hp.
  intros Hn c'. rewrite <- tlb_map_shift_unshift, Hn.
  destruct (ra (tlb_map (unshift p) c')) as [[c x]|err];
    cbn [fmap result_fmap fst snd]; [|reflexivity].
  rewrite tlb_map_unshift_shift. reflexivity.
Qed.

(** Removal = collapse inside the longer history, then the insertion square
    read backwards. *)
Theorem natural_remove_collapse {A} (long long' short : action A) :
  natural (shift p) short long' → natural (collapse p) long long' →
  natural (unshift p) long short.
Proof using Hp.
  intros Hins Hcol c'. rewrite (natural_remove short long' Hins c'), Hcol.
  destruct (long c') as [[c x]|err]; cbn [fmap result_fmap fst snd]; [|reflexivity].
  rewrite tlb_map_unshift_collapse. reflexivity.
Qed.
End Factor.

(** * Squares on restricted caches

    [natural_on P f ra rb] is [natural f ra rb] for the caches satisfying
    [P]. Collapsing [p] commutes with [roll_back (p - 1)] only on caches
    without events at [p], and with refills that start at or below [p] only
    when no root has time [p]. *)

Definition natural_on {A} (P : TLB.t → Prop) (f : nat → nat) (ra rb : action A) : Prop :=
  ∀ c, P c → rb (tlb_map f c) = (λ r, (tlb_map f r.1, r.2)) <$> ra c.

Lemma natural_on_of {A} P f (ra rb : action A) : natural f ra rb → natural_on P f ra rb.
Proof. intros H c _. apply H. Qed.

Lemma natural_on_weaken {A} (P Q : TLB.t → Prop) f (ra rb : action A) :
  (∀ c, Q c → P c) → natural_on P f ra rb → natural_on Q f ra rb.
Proof. intros HQ H c Hc. apply H, HQ, Hc. Qed.

Lemma natural_on_bind {A B} (P : TLB.t → Prop) (Q : A → TLB.t → Prop) f
    (ra rb : action A) (ka kb : A → action B) :
  natural_on P f ra rb →
  (∀ c c' x, P c → ra c = Ok (c', x) → Q x c') →
  (∀ x, natural_on (Q x) f (ka x) (kb x)) →
  natural_on P f (ra ≫= ka) (rb ≫= kb).
Proof.
  intros Ha Hpost Hk c Hc. unfold mbind at 1 2, st_bind. rewrite (Ha c Hc).
  destruct (ra c) as [[c' x]|err] eqn:Hrun; cbn; [|reflexivity].
  apply Hk. exact (Hpost c c' x Hc Hrun).
Qed.

Lemma natural_on_get_roots {A} P f (ka kb : list (bv 16 * bv 64 * bool * nat) → action A) :
  (∀ rs, natural_on (λ c, P c ∧ TLB.asid_roots c = rs) f (ka rs) (kb (map_roots f rs))) →
  natural_on P f (mget TLB.asid_roots ≫= ka) (mget TLB.asid_roots ≫= kb).
Proof.
  intros Hk c Hc.
  change ((mget TLB.asid_roots ≫= kb : action A) (tlb_map f c)) with
    (kb (TLB.asid_roots (tlb_map f c)) (tlb_map f c)).
  change ((mget TLB.asid_roots ≫= ka : action A) c) with (ka (TLB.asid_roots c) c).
  apply (Hk (TLB.asid_roots c) c). split; [exact Hc|reflexivity].
Qed.

Lemma natural_on_mset_vatlb P f (g g' : TLB.VATLB.t → TLB.VATLB.t) :
  (∀ c, P c → vatlb_map f (g (TLB.vatlb c)) = g' (vatlb_map f (TLB.vatlb c))) →
  natural_on P f (mset TLB.vatlb g) (mset TLB.vatlb g').
Proof.
  intros Hg c Hc.
  change ((mset TLB.vatlb g' : action ()) (tlb_map f c)) with
    (Ok (set TLB.vatlb g' (tlb_map f c), ()) : result string _).
  change ((mset TLB.vatlb g : action ()) c) with (Ok (set TLB.vatlb g c, ()) : result string _).
  cbn [fmap result_fmap fst snd]. f_equal. f_equal.
  specialize (Hg c Hc). destruct c. unfold tlb_map, set in *.
  cbn [TLB.vatlb TLB.pte_present TLB.next_table_cache TLB.asid_roots TLB.ets] in *.
  rewrite Hg. reflexivity.
Qed.

Section RestrictedFactor.
Context (p : nat) (Hp : 0 < p).

Theorem natural_on_remove_collapse {A} P (long long' short : action A) :
  natural (shift p) short long' → natural_on P (collapse p) long long' →
  natural_on P (unshift p) long short.
Proof using Hp.
  intros Hins Hcol c' Hc. rewrite (natural_remove p Hp short long' Hins c'), (Hcol c' Hc).
  destruct (long c') as [[c x]|err]; cbn [fmap result_fmap fst snd]; [|reflexivity].
  rewrite tlb_map_unshift_collapse. reflexivity.
Qed.
End RestrictedFactor.

(** Caches and roots without timestamp [t]. *)
Definition evs_avoid (t : nat) (evs : TLB.Entry.events) : Prop := ∀ x, x ∈ evs → x.2 ≠ t.

Definition tlb_avoid (t : nat) (c : TLB.t) : Prop :=
  ∀ lvl nd entries ee, hget lvl (TLB.vatlb c) !! nd = Some entries → ee ∈ entries →
    evs_avoid t ee.2.

Definition roots_avoid (t : nat) (c : TLB.t) : Prop := ∀ x, x ∈ TLB.asid_roots c → x.2 ≠ t.

Lemma map_evs_avoid p evs : evs_avoid p evs → map_evs (collapse p) evs = evs.
Proof.
  intro H. induction evs as [|[ev t] evs IH]; [reflexivity|]. cbn [map_evs map fst snd].
  unfold map_evs in IH. rewrite IH by (intros x Hx; apply H, list_elem_of_further, Hx).
  rewrite collapse_ne by exact (H _ (list_elem_of_here _ _)). reflexivity.
Qed.

Lemma evs_avoid_filter t (P : TLB.Entry.event * nat → Prop) `{∀ x, Decision (P x)} evs :
  evs_avoid t evs → evs_avoid t (filter P evs).
Proof. intros Hev x Hx. apply list_elem_of_filter in Hx as [_ Hx]. exact (Hev x Hx). Qed.

Lemma gmap_map_fe_comm_on f (g g' : TLB.FE.t → TLB.Entry.events → TLB.Entry.events)
    (Q : TLB.Entry.events → Prop) (lvl : Level)
    (m : gmap (TLB.NDCtxt.t lvl) (list (TLB.Entry.t lvl * TLB.Entry.events))) :
  (∀ nd entries ee, m !! nd = Some entries → ee ∈ entries → Q ee.2) →
  (∀ fe evs, Q evs → g' fe (map_evs f evs) = map_evs f (g fe evs)) →
  map (λ ee, (ee.1, map_evs f ee.2)) <$>
    imap (λ nd, map (λ '(entry, events), (entry, g (TLB.FE.make_nd lvl nd entry) events))) m =
  imap (λ nd, map (λ '(entry, events), (entry, g' (TLB.FE.make_nd lvl nd entry) events)))
    (map (λ ee, (ee.1, map_evs f ee.2)) <$> m).
Proof.
  intros HQ Hg. apply map_eq. intro key. rewrite lookup_fmap, !lookup_imap_gmap, lookup_fmap.
  destruct (m !! key) as [entries|] eqn:Hm; [|reflexivity]. cbn [fmap option_fmap option_map].
  f_equal. rewrite !map_map. apply map_ext_in. intros [entry evs] Hin. cbn [fst snd].
  rewrite Hg; [reflexivity|]. apply (HQ key entries (entry, evs) Hm), list_elem_of_In, Hin.
Qed.

Lemma vatlb_map_fe_comm_on f (g g' : TLB.FE.t → TLB.Entry.events → TLB.Entry.events)
    (Q : TLB.Entry.events → Prop) v :
  (∀ lvl nd entries ee, hget lvl v !! nd = Some entries → ee ∈ entries → Q ee.2) →
  (∀ fe evs, Q evs → g' fe (map_evs f evs) = map_evs f (g fe evs)) →
  vatlb_map f (TLB.VATLB.map_fe g v) = TLB.VATLB.map_fe g' (vatlb_map f v).
Proof.
  intros HQ Hg. apply vatlb_ext. intro lvl. unfold vatlb_map, TLB.VATLB.map_fe.
  rewrite !hget_hmap. apply (gmap_map_fe_comm_on f g g' Q); [|exact Hg].
  intros nd entries ee. apply HQ.
Qed.

Lemma roll_back_collapse_avoid p :
  natural_on (tlb_avoid p) (collapse p) (TLB.roll_back (pred p)) (TLB.roll_back (pred p)).
Proof.
  unfold TLB.roll_back. apply natural_on_mset_vatlb. intros c Hc.
  apply (vatlb_map_fe_comm_on _ _ _ (evs_avoid p)); [exact Hc|].
  intros fe evs Havoid. rewrite map_evs_avoid by exact Havoid.
  rewrite map_evs_avoid; [reflexivity|]. apply evs_avoid_filter, Havoid.
Qed.

(** * Collapsing inside the longer history *)

Section Collapse.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Local Notation p := (S (length r)).
Local Notation h := (collapse (S (length r))).
Local Notation g := (unshift (S (length r))).
Local Notation f := (shift (S (length r))).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

Lemma Hp : 0 < p.
Proof. lia. Qed.

Lemma read_collapse t : t ≤ S (length mem) →
  ∀ addr, Memory.read_word addr imem mem' (h t) = Memory.read_word addr imem mem' t.
Proof.
  intros Ht addr. pose proof (collapse_le p t).
  rewrite !read_word_insert_tlbi by lia. rewrite unshift_collapse. reflexivity.
Qed.

Lemma fill_event_collapse t roots ev : t ≤ S (length mem) →
  natural h (TLB.fill_event tid imem mem' t roots ev)
    (TLB.fill_event tid imem mem' (h t) roots ev).
Proof. intro Ht. apply fill_event_map, read_collapse, Ht. Qed.

Lemma fill_from_roots_collapse t roots : t ≤ S (length mem) →
  natural h (TLB.fill_from_roots imem mem' t roots)
    (TLB.fill_from_roots imem mem' (h t) roots).
Proof. intro Ht. apply fill_from_roots_map, read_collapse, Ht. Qed.

Lemma roll_back_collapse time : time ≠ pred p →
  natural h (TLB.roll_back time) (TLB.roll_back (h time)).
Proof. intro Ht. apply roll_back_map. intro t. apply collapse_le_iff; [exact Ht|lia]. Qed.

(** * Removal squares for single operations *)

Theorem fill_event_remove t roots ev : t ≠ p → t ≤ S (length mem) →
  natural g (TLB.fill_event tid imem mem' t roots ev)
    (TLB.fill_event tid imem mem (g t) roots ev).
Proof.
  intros Hne Ht. apply (natural_remove_collapse p Hp _ (TLB.fill_event tid imem mem' t roots ev)).
  - pose proof (fill_event_shifted tid imem l r tlbi rc k (g t) roots ev) as H.
    rewrite (shift_unshift p t Hne Hp) in H.
    apply H, unshift_le_length; [exact Ht|rewrite length_app; lia].
  - pose proof (fill_event_collapse t roots ev Ht) as H.
    rewrite (collapse_ne p t Hne) in H. exact H.
Qed.

Theorem fill_from_roots_remove t roots : t ≤ S (length mem) →
  natural g (TLB.fill_from_roots imem mem' t roots)
    (TLB.fill_from_roots imem mem (g t) roots).
Proof.
  intro Ht. apply (natural_remove_collapse p Hp _ (TLB.fill_from_roots imem mem' (h t) roots)).
  - rewrite <- (shift_unshift_collapse p t Hp).
    apply fill_from_roots_shifted. apply unshift_le_length; [exact Ht|rewrite length_app; lia].
  - apply fill_from_roots_collapse, Ht.
Qed.

Theorem roll_back_remove time : time ≠ pred p →
  natural g (TLB.roll_back time) (TLB.roll_back (g time)).
Proof. intro Ht. apply roll_back_map. intro t. apply unshift_le_iff_npred; [exact Ht|lia]. Qed.

End Collapse.

(** A new event appended in front of both histories. *)
Theorem fill_promise_remove tid imem (l r : Memory.t) tlbi rc k ev :
  natural (unshift (S (length r))) (TLB.fill_promise tid imem (ev :: l ++ Ev.Tlbi tlbi rc k :: r) ev)
    (TLB.fill_promise tid imem (ev :: l ++ r) ev).
Proof.
  apply (natural_remove_collapse _ (Hp r) _ (TLB.fill_promise tid imem (ev :: l ++ Ev.Tlbi tlbi rc k :: r) ev)).
  - exact (fill_promise_shifted tid imem l r tlbi rc k ev).
  - unfold TLB.fill_promise. apply natural_get_roots. intro rs. rewrite map_roots_fst.
    pose proof (fill_event_collapse tid imem (ev :: l) r tlbi rc k
      (length (ev :: l ++ Ev.Tlbi tlbi rc k :: r)) rs.*1 ev) as H.
    cbn [app] in H. rewrite collapse_ne in H by (cbn [length]; rewrite length_app; cbn; lia).
    apply H. cbn [length]. rewrite !length_app. cbn. lia.
Qed.

(** * Refills under collapse *)

Lemma filter_map_roots_lt_in g tb ta (roots : list (bv 16 * bv 64 * bool * nat)) :
  (∀ x, x ∈ roots → g x.2 < tb ↔ x.2 < ta) →
  filter (λ '(_, time), time < tb) (map_roots g roots) =
  map_roots g (filter (λ '(_, time), time < ta) roots).
Proof.
  intro H. induction roots as [|[x t] roots IH]; [reflexivity|].
  pose proof (H (x, t) (list_elem_of_here _ _)) as Ht. cbn [snd] in Ht.
  specialize (IH (λ y Hy, H y (list_elem_of_further _ _ _ Hy))).
  unfold map_roots in *. cbn [map fst snd]. rewrite !filter_cons.
  repeat case_decide; try tauto; cbn [map fst snd]; rewrite ?IH; reflexivity.
Qed.

Lemma filter_map_roots_eq_in g tb ta (roots : list (bv 16 * bv 64 * bool * nat)) :
  (∀ x, x ∈ roots → g x.2 = tb ↔ x.2 = ta) →
  filter (λ '(_, time), time = tb) (map_roots g roots) =
  map_roots g (filter (λ '(_, time), time = ta) roots).
Proof.
  intro H. induction roots as [|[x t] roots IH]; [reflexivity|].
  pose proof (H (x, t) (list_elem_of_here _ _)) as Ht. cbn [snd] in Ht.
  specialize (IH (λ y Hy, H y (list_elem_of_further _ _ _ Hy))).
  unfold map_roots in *. cbn [map fst snd]. rewrite !filter_cons.
  repeat case_decide; try tauto; cbn [map fst snd]; rewrite ?IH; reflexivity.
Qed.

Lemma filter_roots_eq_nil t (roots : list (bv 16 * bv 64 * bool * nat)) :
  (∀ x, x ∈ roots → x.2 ≠ t) → filter (λ '(_, time), time = t) roots = [].
Proof.
  intro H. induction roots as [|[x t'] roots IH]; [reflexivity|].
  pose proof (H (x, t') (list_elem_of_here _ _)) as Ht. cbn [snd] in Ht.
  rewrite filter_cons, decide_False by exact Ht.
  apply IH. intros y Hy. apply H, list_elem_of_further, Hy.
Qed.

Section RefillCollapse.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation h := (collapse (S (length r))).
Local Notation g := (unshift (S (length r))).
Local Notation f := (shift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

(** Roots at [p] are allowed only when the refill starts above [p]: they are
    then active but never added, on both sides. *)
Definition roots_ok (roots : list (bv 16 * bv 64 * bool * nat)) (tmin : nat) : Prop :=
  ∀ x, x ∈ roots → x.2 = p → p < tmin.

Definition cstart (tmin tmin' : nat) : Prop := tmin' = tmin ∨ (tmin = S p ∧ tmin' = p).

Lemma roots_ok_filter (P : bv 16 * bv 64 * bool * nat → Prop) `{∀ x, Decision (P x)} roots tmin :
  roots_ok roots tmin → roots_ok (filter P roots) tmin.
Proof. intros Hok x Hx. apply list_elem_of_filter in Hx as [_ Hx]. exact (Hok x Hx). Qed.

Lemma cstart_succ time : cstart (S time) (S (h time)).
Proof.
  clear Hrc. unfold cstart. destruct (decide (time = p)) as [->|Hne].
  - right. rewrite collapse_at. split; [reflexivity|lia].
  - left. rewrite collapse_ne by exact Hne. reflexivity.
Qed.

Lemma fill_from_btw_collapse_below tmax : ∀ roots iter tmin tmin', tmax < p →
  cstart tmin tmin' → roots_ok roots tmin →
  natural h (TLB.fill_from_btw tid imem mem' roots tmin tmax iter)
    (TLB.fill_from_btw tid imem mem' (map_roots h roots) tmin' tmax iter).
Proof.
  clear Hrc. induction tmax as [|tmax IH]; intros roots iter tmin tmin' Hlt Hmin Hok;
    cbn [TLB.fill_from_btw]; unfold cstart in Hmin.
  all: case_decide as H1; case_decide as H2; try (exfalso; lia).
  1, 3: apply natural_ret.
  - apply natural_throw.
  - destruct iter as [|ev nmem]; [apply natural_throw|].
    assert (Hid : ∀ x, x ∈ roots → h x.2 = x.2).
    { intros [y t] Hy. cbn [snd]. destruct (decide (t = p)) as [->|Hne].
      - specialize (Hok _ Hy eq_refl). lia.
      - apply collapse_ne, Hne. }
    rewrite (filter_map_roots_lt_in h (S tmax) (S tmax))
      by (intros x Hx; rewrite (Hid x Hx); reflexivity).
    rewrite (filter_map_roots_eq_in h (S tmax) (S tmax))
      by (intros x Hx; rewrite (Hid x Hx); reflexivity).
    rewrite !map_roots_fst.
    apply natural_bind; [apply IH; [lia|exact Hmin|apply roots_ok_filter, Hok]|intros _].
    apply natural_bind; [|intros _].
    + pose proof (fill_event_collapse tid imem l r tlbi rc k (S tmax)
        (filter (λ '(_, time), time < S tmax) roots).*1 ev) as H.
      rewrite collapse_ne in H by lia. apply H. rewrite length_app. lia.
    + pose proof (fill_from_roots_collapse imem l r tlbi rc k (S tmax)
        (filter (λ '(_, time), time = S tmax) roots).*1) as H.
      rewrite collapse_ne in H by lia. apply H. rewrite length_app. lia.
Qed.

Lemma fill_from_btw_collapse_above l' : ∀ roots tmin tmin', cstart tmin tmin' →
  roots_ok roots tmin → length l' ≤ length l →
  natural h (TLB.fill_from_btw tid imem mem' roots tmin (length (l' ++ e :: r)) (l' ++ e :: r))
    (TLB.fill_from_btw tid imem mem' (map_roots h roots) tmin' (length (l' ++ e :: r))
      (l' ++ e :: r)).
Proof using Hrc.
  induction l' as [|x l' IH]; intros roots tmin tmin' Hmin Hok Hl; unfold cstart in Hmin.
  - cbn [app length]. cbn [TLB.fill_from_btw].
    destruct (decide (p < tmin)) as [Hgt|Hle].
    + destruct Hmin as [->|[-> ->]].
      * rewrite decide_True by exact Hgt. apply natural_ret.
      * rewrite decide_False by lia.
        rewrite (filter_map_roots_eq_none (collapse (S (length r))) (S (length r)))
          by (intro t; collapse_cases).
        rewrite fill_from_btw_stop by lia.
        apply natural_bind_id; [apply natural_ret|]. intros [] c.
        exact (inserted_event_noop tid imem l r tlbi rc k Hrc _ c).
    + destruct Hmin as [->|[-> ->]]; [|lia].
      rewrite !decide_False by exact Hle.
      assert (Hid : ∀ x, x ∈ roots → h x.2 = x.2 ∧ x.2 ≠ p).
      { intros [y t] Hy. cbn [snd]. destruct (decide (t = p)) as [->|Hne].
        - specialize (Hok _ Hy eq_refl). lia.
        - split; [apply collapse_ne, Hne|exact Hne]. }
      rewrite (filter_map_roots_lt_in h p p)
        by (intros y Hy; rewrite (proj1 (Hid y Hy)); reflexivity).
      rewrite (filter_map_roots_eq_in h p p)
        by (intros y Hy; rewrite (proj1 (Hid y Hy)); reflexivity).
      rewrite (filter_roots_eq_nil p roots) by (intros y Hy; exact (proj2 (Hid y Hy))).
      rewrite !map_roots_fst.
      apply natural_bind;
        [apply fill_from_btw_collapse_below; [lia|left; reflexivity|apply roots_ok_filter, Hok]
        |intros _].
      apply natural_bind; [|intros _].
      * unfold TLB.fill_event. rewrite decide_False by exact Hrc. apply natural_ret.
      * intro c. cbn [map_roots map]. rewrite !fill_from_roots_nil. reflexivity.
  - cbn [app length]. cbn [TLB.fill_from_btw].
    assert (Hge : p ≤ length (l' ++ e :: r)) by (rewrite length_app; cbn; lia).
    case_decide as H1; case_decide as H2; try (exfalso; lia).
    + apply natural_ret.
    + rewrite (filter_map_roots_lt h (S (length (l' ++ e :: r))) (S (length (l' ++ e :: r))))
        by (intro t; collapse_cases).
      rewrite (filter_map_roots_eq h (S (length (l' ++ e :: r))) (S (length (l' ++ e :: r))))
        by (intro t; collapse_cases).
      rewrite !map_roots_fst.
      apply natural_bind;
        [apply IH; [exact Hmin|apply roots_ok_filter, Hok|cbn in Hl; lia]|intros _].
      assert (Hb : S (length (l' ++ e :: r)) ≤ S (length mem)).
      { cbn [length] in Hl. rewrite !length_app in *. cbn in *. lia. }
      apply natural_bind; [|intros _].
      * pose proof (fill_event_collapse tid imem l r tlbi rc k (S (length (l' ++ e :: r)))
          (filter (λ '(_, time), time < S (length (l' ++ e :: r))) roots).*1 x) as H.
        rewrite collapse_ne in H by lia. apply H, Hb.
      * pose proof (fill_from_roots_collapse imem l r tlbi rc k (S (length (l' ++ e :: r)))
          (filter (λ '(_, time), time = S (length (l' ++ e :: r))) roots).*1) as H.
        rewrite collapse_ne in H by lia. apply H, Hb.
Qed.

Theorem fill_from_collapse roots tmin tmin' : cstart tmin tmin' → roots_ok roots tmin →
  natural h (TLB.fill_from tid imem mem' roots tmin)
    (TLB.fill_from tid imem mem' (map_roots h roots) tmin').
Proof using Hrc.
  intros Hmin Hok. unfold TLB.fill_from.
  exact (fill_from_btw_collapse_above l roots tmin tmin' Hmin Hok (le_n _)).
Qed.

Theorem fill_cse_collapse time ttbr0 ttbr1 : time ≠ pred p →
  natural h (TLB.fill_cse tid imem mem' time ttbr0 ttbr1)
    (TLB.fill_cse tid imem mem' (h time) ttbr0 ttbr1).
Proof using Hrc.
  intro Ht. unfold TLB.fill_cse.
  apply natural_bind; [apply roll_back_collapse, Ht|intros _].
  destruct ttbr1 as [ttbr1|].
  - set (roots := [(bv_extract 48 16 ttbr0, ttbr0, false, time);
      (bv_extract 48 16 ttbr0, ttbr1, true, time)]).
    change [(bv_extract 48 16 ttbr0, ttbr0, false, h time);
      (bv_extract 48 16 ttbr0, ttbr1, true, h time)] with (map_roots h roots).
    apply natural_bind; [apply natural_mset_roots; reflexivity|intros _].
    apply fill_from_collapse; [apply cstart_succ|].
    intros y Hy Hyp. unfold roots in Hy. set_unfold in Hy.
    decompose [or] Hy; subst; cbn in *; lia.
  - set (roots := [(bv_extract 48 16 ttbr0, ttbr0, false, time)]).
    change [(bv_extract 48 16 ttbr0, ttbr0, false, h time)] with (map_roots h roots).
    apply natural_bind; [apply natural_mset_roots; reflexivity|intros _].
    apply fill_from_collapse; [apply cstart_succ|].
    intros y Hy Hyp. unfold roots in Hy. set_unfold in Hy.
    decompose [or] Hy; subst; cbn in *; lia.
Qed.

Theorem fill_cse_remove time ttbr0 ttbr1 : time ≠ pred p →
  natural g (TLB.fill_cse tid imem mem' time ttbr0 ttbr1)
    (TLB.fill_cse tid imem mem (g time) ttbr0 ttbr1).
Proof using Hrc.
  intro Ht.
  apply (natural_remove_collapse p (Hp r) _ (TLB.fill_cse tid imem mem' (h time) ttbr0 ttbr1)).
  - pose proof (fill_cse_shifted tid imem l r tlbi rc k Hrc (g time) ttbr0 ttbr1) as H.
    rewrite (shift_unshift_collapse p time (Hp r)) in H. exact H.
  - apply fill_cse_collapse, Ht.
Qed.

(** Root fills at or above [p]: every root of the cache at [p] is active. *)
Theorem fill_asid_root_collapse root time : p ≤ time → time ≤ S (length mem) →
  natural h (TLB.fill_asid_root tid imem mem' root time)
    (TLB.fill_asid_root tid imem mem' root (h time)).
Proof using Hrc.
  intros Hge Ht. unfold TLB.fill_asid_root.
  apply natural_bind; [apply roll_back_collapse; lia|intros _].
  apply natural_bind; [apply natural_mset_roots; reflexivity|intros _].
  apply natural_bind; [apply fill_from_roots_collapse, Ht|intros _].
  apply natural_get_roots. intro rs.
  apply fill_from_collapse; [apply cstart_succ|]. intros y _ Hy. lia.
Qed.

Theorem fill_asid_root_remove root time : p ≤ time → time ≤ S (length mem) →
  natural g (TLB.fill_asid_root tid imem mem' root time)
    (TLB.fill_asid_root tid imem mem root (g time)).
Proof using Hrc.
  intros Hge Ht.
  apply (natural_remove_collapse p (Hp r) _ (TLB.fill_asid_root tid imem mem' root (h time))).
  - pose proof (fill_asid_root_shifted tid imem l r tlbi rc k Hrc root (g time)) as H.
    rewrite (shift_unshift_collapse p time (Hp r)) in H.
    apply H, unshift_le_length; [exact Ht|rewrite length_app; lia].
  - apply fill_asid_root_collapse; assumption.
Qed.

(** ** Squares below [p] on restricted caches

    A CSE at [p - 1] is a square on caches without events at [p]. A root
    fill below [p] is a square on caches without roots at [p] (and without
    events at [p] when it rolls back to [p - 1]). *)

Theorem fill_cse_collapse_on time ttbr0 ttbr1 :
  natural_on (λ c, time = pred p → tlb_avoid p c) h
    (TLB.fill_cse tid imem mem' time ttbr0 ttbr1)
    (TLB.fill_cse tid imem mem' (h time) ttbr0 ttbr1).
Proof using Hrc.
  destruct (decide (time = pred p)) as [Ht|Ht];
    [|apply natural_on_of, fill_cse_collapse, Ht].
  unfold TLB.fill_cse.
  apply (natural_on_bind _ (λ _ _, True)).
  { rewrite (collapse_ne p time) by lia. subst time.
    eapply natural_on_weaken; [|apply roll_back_collapse_avoid]. intros c Hc. exact (Hc eq_refl). }
  { intros; exact I. }
  intros _. apply natural_on_of.
  destruct ttbr1 as [ttbr1|].
  - set (roots := [(bv_extract 48 16 ttbr0, ttbr0, false, time);
      (bv_extract 48 16 ttbr0, ttbr1, true, time)]).
    change [(bv_extract 48 16 ttbr0, ttbr0, false, h time);
      (bv_extract 48 16 ttbr0, ttbr1, true, h time)] with (map_roots h roots).
    apply natural_bind; [apply natural_mset_roots; reflexivity|intros _].
    apply fill_from_collapse; [apply cstart_succ|].
    intros y Hy Hyp. unfold roots in Hy. set_unfold in Hy.
    decompose [or] Hy; subst; cbn in *; lia.
  - set (roots := [(bv_extract 48 16 ttbr0, ttbr0, false, time)]).
    change [(bv_extract 48 16 ttbr0, ttbr0, false, h time)] with (map_roots h roots).
    apply natural_bind; [apply natural_mset_roots; reflexivity|intros _].
    apply fill_from_collapse; [apply cstart_succ|].
    intros y Hy Hyp. unfold roots in Hy. set_unfold in Hy.
    decompose [or] Hy; subst; cbn in *; lia.
Qed.

Theorem fill_cse_remove_on time ttbr0 ttbr1 :
  natural_on (λ c, time = pred p → tlb_avoid p c) g
    (TLB.fill_cse tid imem mem' time ttbr0 ttbr1)
    (TLB.fill_cse tid imem mem (g time) ttbr0 ttbr1).
Proof using Hrc.
  apply (natural_on_remove_collapse p (Hp r) _ _ (TLB.fill_cse tid imem mem' (h time) ttbr0 ttbr1)).
  - pose proof (fill_cse_shifted tid imem l r tlbi rc k Hrc (g time) ttbr0 ttbr1) as H.
    rewrite (shift_unshift_collapse p time (Hp r)) in H. exact H.
  - apply fill_cse_collapse_on.
Qed.

Lemma roots_avoid_roll_back t time c c' :
  roots_avoid t c → TLB.roll_back time c = Ok (c', ()) → roots_avoid t c'.
Proof. intros Hc Hrun. injection Hrun as <-. exact Hc. Qed.

Lemma roots_avoid_fill_from_roots t m time roots c c' :
  roots_avoid t c → TLB.fill_from_roots imem m time roots c = Ok (c', ()) → roots_avoid t c'.
Proof.
  intros Hc Hrun x Hx. apply Hc.
  pose proof (VMCacheRoots.fill_from_roots imem m time roots c c' () Hrun) as E.
  unfold VMCacheRoots.config in E. rewrite <- E. exact Hx.
Qed.

Theorem fill_asid_root_collapse_below root time : time < p →
  natural_on (λ c, roots_avoid p c ∧ (time = pred p → tlb_avoid p c)) h
    (TLB.fill_asid_root tid imem mem' root time)
    (TLB.fill_asid_root tid imem mem' root (h time)).
Proof using Hrc.
  intro Hlt. rewrite (collapse_ne p time) by lia. unfold TLB.fill_asid_root.
  apply (natural_on_bind _ (λ _ c, roots_avoid p c)).
  { destruct (decide (time = pred p)) as [Ht|Ht].
    - subst time. eapply natural_on_weaken; [|apply roll_back_collapse_avoid].
      intros c [_ Hc]. exact (Hc eq_refl).
    - apply natural_on_of. pose proof (roll_back_collapse r time Ht) as H.
      rewrite (collapse_ne p time) in H by lia. exact H. }
  { intros c c' [] [Hc _] Hrun. exact (roots_avoid_roll_back _ _ c c' Hc Hrun). }
  intros _.
  apply (natural_on_bind _ (λ _ c, roots_avoid p c)).
  { apply natural_on_of, natural_mset_roots. intro rs. cbn [map_roots map fst snd].
    rewrite (collapse_ne p time) by lia. reflexivity. }
  { intros c c' [] Hc Hrun. injection Hrun as <-. intros x Hx.
    apply elem_of_cons in Hx as [->|Hx]; [cbn; lia|exact (Hc x Hx)]. }
  intros _.
  apply (natural_on_bind _ (λ _ c, roots_avoid p c)).
  { apply natural_on_of. pose proof (fill_from_roots_collapse imem l r tlbi rc k time [root]) as H.
    rewrite (collapse_ne p time) in H by lia. apply H. rewrite length_app. lia. }
  { intros c c' [] Hc Hrun. exact (roots_avoid_fill_from_roots _ mem' time [root] c c' Hc Hrun). }
  intros _.
  apply natural_on_get_roots. intros rs c [Hc <-].
  apply (fill_from_collapse (TLB.asid_roots c) (S time) (S time)); [left; reflexivity|].
  intros x Hx Hxp. exfalso. exact (Hc x Hx Hxp).
Qed.

Theorem fill_asid_root_remove_below root time : time < p →
  natural_on (λ c, roots_avoid p c ∧ (time = pred p → tlb_avoid p c)) g
    (TLB.fill_asid_root tid imem mem' root time)
    (TLB.fill_asid_root tid imem mem root (g time)).
Proof using Hrc.
  intro Hlt.
  apply (natural_on_remove_collapse p (Hp r) _ _ (TLB.fill_asid_root tid imem mem' root (h time))).
  - pose proof (fill_asid_root_shifted tid imem l r tlbi rc k Hrc root (g time)) as H.
    rewrite (shift_unshift_collapse p time (Hp r)) in H.
    apply H. rewrite unshift_lt by lia. rewrite length_app. lia.
  - apply fill_asid_root_collapse_below, Hlt.
Qed.

End RefillCollapse.

(** * Footprints of cache actions

    Collapsing [p] onto [p - 1] merges root fills at [p - 1] and [p] into one
    root fill at [p - 1]. Root fills at the same timestamp commute up to
    [VMCacheRefill.equiv] because each table traversal level writes only
    entries of that level and reads only their histories. [local S run]
    states that [run] writes only histories of entries in [S] and reads only
    those histories and the present-PTE map. *)

Section Footprint.
Import VMCacheRefill.

Definition agree (S : TLB.FE.t → Prop) (a b : TLB.t) : Prop :=
  TLB.pte_present a = TLB.pte_present b ∧ ∀ fe, S fe → history a fe = history b fe.

Definition local {A} (S : TLB.FE.t → Prop) (run : action A) : Prop :=
  ∀ c c' x, run c = Ok (c', x) →
    TLB.pte_present c' = TLB.pte_present c ∧ (∀ fe, ¬ S fe → history c' fe = history c fe) ∧
    ∀ d, agree S c d → ∃ d', run d = Ok (d', x) ∧ agree S c' d'.

Lemma local_ret {A} S (x : A) : local S (mret x).
Proof.
  intros c c' y Hrun. change (@Ok string _ (c, x) = Ok (c', y)) in Hrun. injection Hrun as <- <-.
  split; [reflexivity|]. split; [reflexivity|]. intros d Hd. exists d. split; [reflexivity|exact Hd].
Qed.

Lemma local_none {A} S (run : action A) :
  (∀ c c' x, run c = Ok (c', x) → c' = c ∧ ∀ d, run d = Ok (d, x)) → local S run.
Proof.
  intros H c c' x Hrun. destruct (H c c' x Hrun) as [-> Hd].
  split; [reflexivity|]. split; [reflexivity|]. intros d Had. exists d. split; [apply Hd|exact Had].
Qed.

Lemma local_bind {A B} S (ra : action A) (k : A → action B) :
  local S ra → (∀ c c' x, ra c = Ok (c', x) → local S (k x)) → local S (ra ≫= k).
Proof.
  intros Ha Hk c c'' y Hrun. unfold mbind, st_bind, result_bind in Hrun |- *.
  destruct (ra c) as [[c' x]|err] eqn:H1; [|discriminate].
  destruct (Ha c c' x H1) as [Hp1 [Hout1 Hrep1]].
  destruct (Hk c c' x H1 c' c'' y Hrun) as [Hp2 [Hout2 Hrep2]].
  split; [congruence|]. split; [intros fe Hfe; rewrite Hout2, Hout1 by exact Hfe; reflexivity|].
  intros d Hd. destruct (Hrep1 d Hd) as [d' [Hd1 Had']]. rewrite Hd1.
  destruct (Hrep2 d' Had') as [d'' [Hd2 Had'']]. exists d''. split; [exact Hd2|exact Had''].
Qed.

Lemma local_fmap {A B} S (f : A → B) (ra : action A) : local S ra → local S (f <$> ra).
Proof.
  intros Ha c c' y Hrun. unfold fmap, st_fmap, result_fmap in Hrun |- *.
  destruct (ra c) as [[c1 x]|err] eqn:H1; [|discriminate]. injection Hrun as <- <-.
  destruct (Ha c c1 x H1) as [Hp [Hout Hrep]]. split; [exact Hp|]. split; [exact Hout|].
  intros d Hd. destruct (Hrep d Hd) as [d' [Hd1 Had]]. rewrite Hd1. exists d'. split; [reflexivity|exact Had].
Qed.

Lemma local_weaken {A} (S T : TLB.FE.t → Prop) `{∀ fe, Decision (S fe)} (run : action A) :
  (∀ fe, S fe → T fe) → local S run → local T run.
Proof.
  intros HST Hrun c c' x Hc. destruct (Hrun c c' x Hc) as [Hp [Hout Hrep]].
  split; [exact Hp|]. split; [intros fe Hfe; apply Hout; intro Hs; apply Hfe, HST, Hs|].
  intros d [Hdp Hdh]. destruct (Hrep d) as [d' [Hd Had]].
  { split; [exact Hdp|]. intros fe Hfe. apply Hdh, HST, Hfe. }
  destruct (Hrun d d' x Hd) as [Hp' [Hout' _]].
  exists d'. split; [exact Hd|]. split; [destruct Had as [Hq _]; exact Hq|].
  intros fe Hfe. destruct (decide (S fe)) as [Hs|Hs]; [apply Had, Hs|].
  rewrite Hout, Hout' by exact Hs. apply Hdh, Hfe.
Qed.

Lemma local_get_present S : local S (mget TLB.pte_present).
Proof.
  intros c c' x Hrun. change (@Ok string _ (c, TLB.pte_present c) = Ok (c', x)) in Hrun.
  injection Hrun as <- <-. split; [reflexivity|]. split; [reflexivity|].
  intros d [Hdp Hdh]. exists d. split; [|split; assumption].
  change (@Ok string _ (d, TLB.pte_present d) = Ok (d, TLB.pte_present c)). rewrite Hdp. reflexivity.
Qed.

Lemma local_lift_bind {A B} S (r : result string A) (k : A → action B) :
  (∀ x, r = Ok x → local S (k x)) → local S (mlift r ≫= k).
Proof.
  intro Hk. destruct r as [x|err].
  - intros c c' y Hrun. exact (Hk x eq_refl c c' y Hrun).
  - intros c c' y Hrun. discriminate.
Qed.

Lemma local_othrow_bind {A B} S (err : string) (o : option A) (k : A → action B) :
  (∀ x, o = Some x → local S (k x)) → local S (othrow err o ≫= k).
Proof.
  intro Hk. destruct o as [x|].
  - intros c c' y Hrun. exact (Hk x eq_refl c c' y Hrun).
  - intros c c' y Hrun. discriminate.
Qed.

Lemma local_guard_bind {B} S (err : string) (P : Prop) `{Decision P} (k : action B) :
  (P → local S k) → local S (guard_or err P ≫= λ _, k).
Proof.
  intro Hk. unfold guard_or. destruct (decide P) as [HP|HP].
  - intros c c' y Hrun. exact (Hk HP c c' y Hrun).
  - intros c c' y Hrun. discriminate.
Qed.

Lemma local_guard' S (err : string) (P : Prop) `{Decision P} : local S (guard_or' err P : action ()).
Proof.
  apply local_none. intros c c' x Hrun. unfold guard_or', guard_or in Hrun |- *.
  destruct (decide P); [|discriminate]. injection Hrun as <- <-. split; [reflexivity|]. intro d. reflexivity.
Qed.

Lemma local_mapM {A B} S (f : A → action B) xs :
  (∀ x, x ∈ xs → local S (f x)) → local S (mapM f xs).
Proof.
  induction xs as [|x xs IH]; intro Hf; cbn [mapM]; [apply local_ret|].
  apply local_bind; [apply Hf, list_elem_of_here|intros _ _ y _].
  apply local_bind; [apply IH; intros z Hz; apply Hf, list_elem_of_further, Hz|intros _ _ ys _].
  apply local_ret.
Qed.

Lemma local_fill_entry time fe : local (λ q, q = fe) (TLB.fill_entry time fe).
Proof.
  intros c c' x Hrun. destruct (fill_entry_effect time fe c c' x Hrun) as [Hp [Hl Hh]].
  split; [exact Hp|]. split; [intros q Hq; rewrite Hh, decide_False by exact Hq; reflexivity|].
  intros d [Hdp Hdh]. destruct (fill_entry_total time fe d) as [d' [y Hd]].
  destruct (fill_entry_effect time fe d d' y Hd) as [Hp' [Hl' Hh']].
  assert (y = x) as -> by (rewrite Hl', Hl, (Hdh fe eq_refl); reflexivity).
  exists d'. split; [exact Hd|]. split; [congruence|].
  intros q ->. rewrite Hh, Hh', !decide_True by reflexivity. rewrite (Hdh fe eq_refl). reflexivity.
Qed.

(** Actions with disjoint footprints commute up to [equiv]. *)
Theorem local_comm {A B} (S T : TLB.FE.t → Prop) `{∀ fe, Decision (S fe)}
    `{∀ fe, Decision (T fe)} (ra : action A) (rb : action B) c c1 c2 x y :
  local S ra → local T rb → (∀ fe, S fe → T fe → False) →
  ra c = Ok (c1, x) → rb c1 = Ok (c2, y) →
  ∃ d1 d2, rb c = Ok (d1, y) ∧ ra d1 = Ok (d2, x) ∧ equiv c2 d2.
Proof.
  intros Ha Hb Hdis H1 H2.
  destruct (Ha c c1 x H1) as [Hp1 [Hout1 Hrep1]].
  destruct (Hb c1 c2 y H2) as [Hp2 [Hout2 Hrep2]].
  destruct (Hrep2 c) as [d1 [Hd1 Hag1]].
  { split; [exact Hp1|]. intros fe Hfe. apply Hout1. intro Hs. exact (Hdis fe Hs Hfe). }
  destruct (Hb c d1 y Hd1) as [Hpd1 [Houtd1 _]].
  destruct (Hrep1 d1) as [d2 [Hd2 Hag2]].
  { split; [congruence|]. intros fe Hfe. symmetry. apply Houtd1. intro Ht. exact (Hdis fe Hfe Ht). }
  destruct (Ha d1 d2 x Hd2) as [Hpd2 [Houtd2 _]].
  exists d1, d2. split; [exact Hd1|]. split; [exact Hd2|].
  split; [destruct Hag2 as [Hq _]; congruence|]. intro fe.
  destruct (decide (S fe)) as [Hs|Hs].
  - rewrite Hout2 by (intro Ht; exact (Hdis fe Hs Ht)). apply Hag2, Hs.
  - rewrite Houtd2 by exact Hs. destruct (decide (T fe)) as [Ht|Ht]; [apply Hag1, Ht|].
    rewrite Hout2, Hout1, Houtd1 by assumption. reflexivity.
Qed.

Lemma local_get_proj {X} S (g : gmap pn (list (bv 9)) → X) : local S (mget (g ∘ TLB.pte_present)).
Proof.
  intros c c' x Hrun. change (@Ok string _ (c, g (TLB.pte_present c)) = Ok (c', x)) in Hrun.
  injection Hrun as <- <-. split; [reflexivity|]. split; [reflexivity|].
  intros d [Hdp Hdh]. exists d. split; [|split; assumption].
  change (@Ok string _ (d, g (TLB.pte_present d)) = Ok (d, g (TLB.pte_present c))).
  rewrite Hdp. reflexivity.
Qed.

(** ** Outputs *)

Definition yields {A} (Q : A → Prop) (run : action A) : Prop :=
  ∀ c c' x, run c = Ok (c', x) → Q x.

Lemma bind_inv {A B} (ra : action A) (k : A → action B) c c'' y :
  (ra ≫= k) c = Ok (c'', y) → ∃ c' x, ra c = Ok (c', x) ∧ k x c' = Ok (c'', y).
Proof.
  unfold mbind, st_bind, result_bind. destruct (ra c) as [[c' x]|err]; [|discriminate].
  intro H. exists c', x. split; [reflexivity|exact H].
Qed.

Lemma bind_intro {A B} (ra : action A) (k : A → action B) c c' c'' x y :
  ra c = Ok (c', x) → k x c' = Ok (c'', y) → (ra ≫= k) c = Ok (c'', y).
Proof. unfold mbind, st_bind, result_bind. intros H1 H2. rewrite H1. exact H2. Qed.

Lemma yields_ret {A} (Q : A → Prop) x : Q x → yields Q (mret x).
Proof.
  intros HQ c c' y Hrun. change (@Ok string _ (c, x) = Ok (c', y)) in Hrun.
  injection Hrun as _ <-. exact HQ.
Qed.

Lemma yields_bind {A B} (Q : B → Prop) (ra : action A) (k : A → action B) :
  (∀ c c' x, ra c = Ok (c', x) → yields Q (k x)) → yields Q (ra ≫= k).
Proof.
  intros Hk c c'' y Hrun. apply bind_inv in Hrun as [c' [x [H1 H2]]]. exact (Hk c c' x H1 _ _ _ H2).
Qed.

Lemma yields_lift_bind {A B} (Q : B → Prop) (r : result string A) (k : A → action B) :
  (∀ x, r = Ok x → yields Q (k x)) → yields Q (mlift r ≫= k).
Proof.
  intro Hk. destruct r as [x|err].
  - intros c c' y Hrun. exact (Hk x eq_refl c c' y Hrun).
  - intros c c' y Hrun. discriminate.
Qed.

Lemma yields_fmap {A B} (P : A → Prop) (Q : B → Prop) (f : A → B) (ra : action A) :
  yields P ra → (∀ x, P x → Q (f x)) → yields Q (f <$> ra).
Proof.
  intros Ha Hf c c' y Hrun. unfold fmap, st_fmap, result_fmap in Hrun.
  destruct (ra c) as [[c1 x]|err] eqn:H1; [|discriminate]. injection Hrun as _ <-.
  exact (Hf x (Ha c c1 x H1)).
Qed.

Lemma yields_mapM {A B} (P : B → Prop) (f : A → action B) xs :
  (∀ x, yields P (f x)) → yields (λ ys, ∀ y, y ∈ ys → P y) (mapM f xs).
Proof.
  intro Hf. induction xs as [|x xs IH]; cbn [mapM].
  - apply yields_ret. intros y Hy. apply elem_of_nil in Hy as [].
  - apply yields_bind. intros c c' y Hy.
    apply yields_bind. intros c1 c2 ys Hys. apply yields_ret.
    intros z Hz. apply elem_of_cons in Hz as [->|Hz]; [exact (Hf x c c' y Hy)|exact (IH c1 c2 ys Hys z Hz)].
Qed.

Lemma yields_concat {A} (R : A → Prop) (run : action (list (list A))) :
  yields (λ outs, ∀ o, o ∈ outs → ∀ y, y ∈ o → R y) run →
  yields (λ out, ∀ y, y ∈ out → R y) (List.concat <$> run).
Proof.
  intro H. apply (yields_fmap _ _ _ _ H). intros outs Houts y Hy.
  apply list_elem_of_In, in_concat in Hy as [o [Ho Hy]].
  exact (Houts o (proj2 (list_elem_of_In _ _) Ho) y (proj2 (list_elem_of_In _ _) Hy)).
Qed.

(** ** Levels of the table traversal *)

Definition at_lvl (j : nat) (fe : TLB.FE.t) : Prop := fin_to_nat (TLB.FE.lvl fe) = j.
#[local] Instance at_lvl_dec j fe : Decision (at_lvl j fe).
Proof. unfold at_lvl. apply _. Defined.

Definition above_lvl (j : nat) (fe : TLB.FE.t) : Prop := j < fin_to_nat (TLB.FE.lvl fe).
#[local] Instance above_lvl_dec j fe : Decision (above_lvl j fe).
Proof. unfold above_lvl. apply _. Defined.

Lemma append_at_lvl entry idx pte child clvl :
  child_lvl (TLB.FE.lvl entry) = Some clvl → TLB.FE.append entry idx pte = Ok child →
  at_lvl (S (TLB.FE.lvl entry)) child.
Proof.
  intros Hclvl Happ. unfold at_lvl.
  rewrite (VMCacheTraversal.append_level entry idx pte child clvl Hclvl Happ).
  pose proof (child_lvl_add_one _ _ Hclvl). lia.
Qed.

Lemma local_fill_from_entry imem mem time entry :
  local (at_lvl (S (TLB.FE.lvl entry))) (TLB.fill_from_entry imem mem time entry).
Proof.
  unfold TLB.fill_from_entry. apply local_guard_bind. intros _.
  apply local_bind; [apply local_get_proj|intros _ _ indexes _].
  apply local_othrow_bind. intros clvl Hclvl.
  apply local_fmap, local_mapM. intros idx _.
  destruct (Memory.read_word _ imem mem time) as [pte|err]; [|apply local_ret].
  destruct (decide (is_tlb_fillable clvl pte)); [|apply local_ret].
  apply local_lift_bind. intros child Happ.
  apply local_bind.
  - apply (@local_weaken _ (λ q, q = child) _ (λ q, decide (q = child)));
      [|apply local_fill_entry]. intros q ->.
    exact (append_at_lvl entry idx pte child clvl Hclvl Happ).
  - intros _ _ loaded _. destruct loaded; [destruct (decide (is_table clvl pte))|]; apply local_ret.
Qed.

Lemma yields_fill_from_entry imem mem time entry :
  yields (λ out, ∀ y, y ∈ out → at_lvl (S (TLB.FE.lvl entry)) y)
    (TLB.fill_from_entry imem mem time entry).
Proof.
  unfold TLB.fill_from_entry. intros c c' x Hrun. unfold guard_or in Hrun.
  destruct (decide (TLB.FE.is_table entry)); [|discriminate].
  apply bind_inv in Hrun as [c1 [u [_ Hrun]]].
  apply bind_inv in Hrun as [c2 [indexes [_ Hrun]]].
  destruct (child_lvl (TLB.FE.lvl entry)) as [clvl|] eqn:Hclvl; [|discriminate].
  revert c2 c' x Hrun.
  apply yields_concat, yields_mapM. intro idx.
  destruct (Memory.read_word _ imem mem time) as [pte|err];
    [|apply yields_ret; intros ? Hy; apply elem_of_nil in Hy as []].
  destruct (decide (is_tlb_fillable clvl pte));
    [|apply yields_ret; intros ? Hy; apply elem_of_nil in Hy as []].
  apply yields_lift_bind. intros child Happ. apply yields_bind. intros _ _ loaded _.
  destruct loaded; [destruct (decide (is_table clvl pte))|]; apply yields_ret; intros y Hy;
    (apply list_elem_of_singleton in Hy as -> || apply elem_of_nil in Hy as []).
  exact (append_at_lvl entry idx pte child clvl Hclvl Happ).
Qed.

Definition all_at (j : nat) (entries : list TLB.FE.t) : Prop := ∀ e, e ∈ entries → at_lvl j e.

Lemma local_step imem mem time j entries : all_at j entries →
  local (at_lvl (S j)) (TLB.fill_from_entries_step imem mem time entries).
Proof.
  intro Hj. unfold TLB.fill_from_entries_step. apply local_fmap, local_mapM. intros e He.
  pose proof (Hj e He) as He'. unfold at_lvl in He'. rewrite <- He'. apply local_fill_from_entry.
Qed.

Lemma yields_step imem mem time j entries : all_at j entries →
  yields (all_at (S j)) (TLB.fill_from_entries_step imem mem time entries).
Proof.
  intro Hj. unfold TLB.fill_from_entries_step. intros c c' out Hrun.
  assert (Hy : yields (λ outs, ∀ o, o ∈ outs → ∀ y, y ∈ o → at_lvl (S j) y)
    (mapM (TLB.fill_from_entry imem mem time) entries)).
  { clear c c' out Hrun. intros c0 c1 outs Hrun0 o Ho. revert c0 c1 outs Hrun0 o Ho.
    induction entries as [|e entries IH]; cbn [mapM]; intros c0 c1 outs Hrun0 o Ho.
    - change (@Ok string _ (c0, []) = Ok (c1, outs)) in Hrun0. injection Hrun0 as _ <-.
      apply elem_of_nil in Ho as [].
    - apply bind_inv in Hrun0 as [c2 [o1 [H1 H2]]]. apply bind_inv in H2 as [c3 [os [H3 H4]]].
      change (@Ok string _ (c3, o1 :: os) = Ok (c1, outs)) in H4. injection H4 as _ <-.
      apply elem_of_cons in Ho as [->|Ho].
      + pose proof (Hj e (list_elem_of_here _ _)) as He. unfold at_lvl in He.
        intros y Hy. rewrite <- He. exact (yields_fill_from_entry imem mem time e c0 c2 o1 H1 y Hy).
      + exact (IH (λ e' He', Hj e' (list_elem_of_further _ _ _ He')) c2 c3 os H3 o Ho). }
  exact (yields_concat _ _ Hy c c' out Hrun).
Qed.

(** [n] traversal steps followed by the termination check, as in
    [TLB.fill_from_entries]. *)
Fixpoint steps imem mem time (n : nat) (entries : list TLB.FE.t) : action () :=
  match n with
  | 0 => guard_or' "fill_from_entries messed up" (entries = [])
  | S n => next ← TLB.fill_from_entries_step imem mem time entries; steps imem mem time n next
  end.

Lemma fill_from_entries_steps imem mem time entries :
  TLB.fill_from_entries imem mem time entries = steps imem mem time 3 entries.
Proof. reflexivity. Qed.

Lemma local_steps imem mem time n : ∀ j entries, all_at j entries →
  local (above_lvl j) (steps imem mem time n entries).
Proof.
  induction n as [|n IH]; intros j entries Hj; cbn [steps]; [apply local_guard'|].
  apply local_bind.
  - refine (local_weaken (at_lvl (S j)) (above_lvl j) _ _ (local_step _ _ _ j _ Hj)).
    intros fe Hfe. unfold above_lvl, at_lvl in *. lia.
  - intros c c' next Hrun.
    refine (local_weaken (above_lvl (S j)) (above_lvl j) _ _
      (IH (S j) next (yields_step _ _ _ j _ Hj _ _ _ Hrun))).
    intros fe Hfe. unfold above_lvl in *. lia.
Qed.

Lemma respects_steps imem mem time n entries : respects (steps imem mem time n entries).
Proof.
  revert entries. induction n as [|n IH]; intro entries; cbn [steps]; [apply respects_guard_unit|].
  apply respects_bind; [apply fill_from_entries_step_equiv|intro; apply IH].
Qed.

Lemma mapM_app_run {A B} (f : A → action B) xs ys c :
  mapM f (xs ++ ys) c = (us ← mapM f xs; vs ← mapM f ys; mret (us ++ vs)) c.
Proof.
  revert c. induction xs as [|x xs IH]; intro c; cbn [app mapM].
  - unfold mbind, st_bind, result_bind. cbn. destruct (mapM f ys c) as [[c' vs]|err]; reflexivity.
  - unfold mbind, st_bind, result_bind, mret, st_ret, result_ret in *.
    destruct (f x c) as [[c1 u]|err]; cbn; [|reflexivity]. rewrite IH.
    destruct (mapM f xs c1) as [[c2 us]|err]; cbn; [|reflexivity].
    destruct (mapM f ys c2) as [[c3 vs]|err]; reflexivity.
Qed.

Lemma step_app imem mem time xs ys c :
  TLB.fill_from_entries_step imem mem time (xs ++ ys) c =
  (us ← TLB.fill_from_entries_step imem mem time xs;
   vs ← TLB.fill_from_entries_step imem mem time ys; mret (us ++ vs)) c.
Proof.
  unfold TLB.fill_from_entries_step, fmap at 1, st_fmap. rewrite mapM_app_run.
  unfold mbind, st_bind, result_bind, fmap, st_fmap, result_fmap.
  destruct (mapM (TLB.fill_from_entry imem mem time) xs c) as [[c1 us]|err]; [|reflexivity]. cbn.
  destruct (mapM (TLB.fill_from_entry imem mem time) ys c1) as [[c2 vs]|err]; [|reflexivity]. cbn.
  rewrite concat_app. reflexivity.
Qed.

(** ** Splitting a traversal *)

Definition sim_to {A} (ra rb : action A) : Prop :=
  ∀ c c' x, ra c = Ok (c', x) → ∃ c'', rb c = Ok (c'', x) ∧ equiv c' c''.

Lemma guard_nil_run (es : list TLB.FE.t) c c' (x : ()) :
  (guard_or' "fill_from_entries messed up" (es = []) : action ()) c = Ok (c', x) ↔ es = [] ∧ c' = c.
Proof.
  unfold guard_or. destruct x. destruct (decide (es = [])) as [He|He].
  - change (@Ok string _ (c, ()) = Ok (c', ()) ↔ es = [] ∧ c' = c).
    split; [intro H; injection H as <-; split; [exact He|reflexivity]|intros [_ ->]; reflexivity].
  - change (@Error string (TLB.t * ()) "fill_from_entries messed up" = Ok (c', ()) ↔ es = [] ∧ c' = c).
    split; [discriminate|intros [? _]; contradiction].
Qed.

Lemma lvl_disjoint j fe : at_lvl (S j) fe → above_lvl (S j) fe → False.
Proof. unfold at_lvl, above_lvl. lia. Qed.

Theorem steps_app imem mem time n : ∀ j xs ys, all_at j xs → all_at j ys →
  sim_to (steps imem mem time n (xs ++ ys))
    (steps imem mem time n xs;; steps imem mem time n ys) ∧
  sim_to (steps imem mem time n xs;; steps imem mem time n ys)
    (steps imem mem time n (xs ++ ys)).
Proof.
  induction n as [|n IH]; intros j xs ys Hx Hy.
  - cbn [steps]. split; intros c c' [] Hrun.
    + apply guard_nil_run in Hrun as [Hnil ->]. apply app_eq_nil in Hnil as [-> ->].
      exists c. split; [|apply equiv_refl].
      apply (bind_intro _ _ c c c () ()); apply guard_nil_run; split; reflexivity.
    + apply bind_inv in Hrun as [c1 [[] [H1 H2]]].
      apply guard_nil_run in H1 as [-> ->]. apply guard_nil_run in H2 as [-> ->].
      exists c. split; [apply guard_nil_run; split; reflexivity|apply equiv_refl].
  - cbn [steps]. split; intros c c' [] Hrun.
    + apply bind_inv in Hrun as [c1 [zs [Hst Hrest]]]. rewrite step_app in Hst.
      apply bind_inv in Hst as [ca [xs' [Hxa Hst]]]. apply bind_inv in Hst as [cb [ys' [Hyb Hret]]].
      change (@Ok string _ (cb, xs' ++ ys') = Ok (c1, zs)) in Hret. injection Hret as <- <-.
      pose proof (yields_step imem mem time j xs Hx _ _ _ Hxa) as Hx'.
      pose proof (yields_step imem mem time j ys Hy _ _ _ Hyb) as Hy'.
      destruct (IH (S j) xs' ys' Hx' Hy') as [Hjs _].
      destruct (Hjs cb c' () Hrest) as [e [Hseq He]].
      apply bind_inv in Hseq as [e1 [[] [He1 He2]]].
      destruct (local_comm (at_lvl (S j)) (above_lvl (S j)) _ _ ca cb e1 ys' ()
        (local_step imem mem time j ys Hy) (local_steps imem mem time n (S j) xs' Hx')
        (lvl_disjoint j) Hyb He1) as [d1 [d2 [Hd1 [Hd2 Hed]]]].
      destruct (respects_steps imem mem time n ys' e1 d2 e () Hed He2) as [d3 [Hd3 Hed3]].
      exists d3. split; [|eapply equiv_trans; eassumption].
      apply (bind_intro _ _ c d1 d3 () ()).
      * apply (bind_intro _ _ c ca d1 xs' ()); assumption.
      * apply (bind_intro _ _ d1 d2 d3 ys' ()); assumption.
    + apply bind_inv in Hrun as [d1 [[] [H1 H2]]].
      apply bind_inv in H1 as [ca [xs' [Hxa Hxs]]].
      apply bind_inv in H2 as [d2 [ys' [Hyb Hys]]].
      pose proof (yields_step imem mem time j xs Hx _ _ _ Hxa) as Hx'.
      pose proof (yields_step imem mem time j ys Hy _ _ _ Hyb) as Hy'.
      destruct (local_comm (above_lvl (S j)) (at_lvl (S j)) _ _ ca d1 d2 () ys'
        (local_steps imem mem time n (S j) xs' Hx') (local_step imem mem time j ys Hy)
        (λ fe Ha Hb, lvl_disjoint j fe Hb Ha) Hxs Hyb) as [e1 [e2 [He1 [He2 Hed]]]].
      destruct (respects_steps imem mem time n ys' d2 e2 c' () Hed Hys) as [e3 [He3 Hed3]].
      destruct (IH (S j) xs' ys' Hx' Hy') as [_ Hsj].
      destruct (Hsj e1 e3 ()) as [e4 [He4 Hed4]].
      { apply (bind_intro _ _ e1 e2 e3 () ()); assumption. }
      exists e4. split; [|eapply equiv_trans; eassumption].
      apply (bind_intro _ _ c e1 e4 (xs' ++ ys') ()); [|exact He4].
      rewrite step_app. apply (bind_intro _ _ c ca e1 xs' (xs' ++ ys')); [exact Hxa|].
      apply (bind_intro _ _ ca e1 e1 ys' (xs' ++ ys')); [exact He1|reflexivity].
Qed.

(** ** Root fills *)

Lemma local_fill_root imem mem time roots :
  local (at_lvl 0) (TLB.fill_root imem mem time roots).
Proof.
  unfold TLB.fill_root. apply local_fmap, local_mapM. intros [[asid ttbr] upper] _.
  apply local_bind; [apply local_get_proj|intros _ _ indexes _].
  apply local_fmap, local_mapM. intros idx _.
  destruct (Memory.read_word _ imem mem time) as [pte|err]; [|apply local_ret].
  destruct (decide (is_table 0%fin pte)); [|apply local_ret].
  apply local_bind.
  - refine (@local_weaken _ (λ q, q = TLB.FE.make0 upper idx asid ttbr pte) (at_lvl 0)
      (λ q, decide (q = _)) _ _ (local_fill_entry _ _)).
    intros q ->. reflexivity.
  - intros _ _ loaded _. destruct loaded; apply local_ret.
Qed.

Lemma yields_fill_root imem mem time roots :
  yields (all_at 0) (TLB.fill_root imem mem time roots).
Proof.
  unfold TLB.fill_root. apply yields_concat, yields_mapM. intros [[asid ttbr] upper].
  apply yields_bind. intros _ _ indexes _.
  apply yields_concat, yields_mapM. intro idx.
  destruct (Memory.read_word _ imem mem time) as [pte|err];
    [|apply yields_ret; intros ? Hy; apply elem_of_nil in Hy as []].
  destruct (decide (is_table 0%fin pte));
    [|apply yields_ret; intros ? Hy; apply elem_of_nil in Hy as []].
  apply yields_bind. intros _ _ loaded _.
  destruct loaded; apply yields_ret; intros y Hy;
    (apply list_elem_of_singleton in Hy as -> || apply elem_of_nil in Hy as []).
  reflexivity.
Qed.

Lemma fill_root_app imem mem time xs ys c :
  TLB.fill_root imem mem time (xs ++ ys) c =
  (us ← TLB.fill_root imem mem time xs; vs ← TLB.fill_root imem mem time ys; mret (us ++ vs)) c.
Proof.
  unfold TLB.fill_root, fmap at 1, st_fmap. rewrite mapM_app_run.
  unfold mbind, st_bind, result_bind, fmap, st_fmap, result_fmap.
  match goal with |- context [mapM ?F xs c] =>
    destruct (mapM F xs c) as [[c1 us]|err]; [|reflexivity]; cbn;
    destruct (mapM F ys c1) as [[c2 vs]|err]; [|reflexivity]; cbn end.
  rewrite concat_app. reflexivity.
Qed.

Lemma lvl_disjoint0 fe : at_lvl 0 fe → above_lvl 0 fe → False.
Proof. unfold at_lvl, above_lvl. lia. Qed.

Lemma fill_from_roots_steps imem mem time roots c :
  TLB.fill_from_roots imem mem time roots c =
  (es ← TLB.fill_root imem mem time roots; steps imem mem time 3 es) c.
Proof. reflexivity. Qed.

(** Root fills at one timestamp: filling [xs ++ ys] equals filling [xs] then
    [ys], up to [equiv]. *)
Theorem fill_from_roots_app imem mem time xs ys :
  sim_to (TLB.fill_from_roots imem mem time (xs ++ ys))
    (TLB.fill_from_roots imem mem time xs;; TLB.fill_from_roots imem mem time ys) ∧
  sim_to (TLB.fill_from_roots imem mem time xs;; TLB.fill_from_roots imem mem time ys)
    (TLB.fill_from_roots imem mem time (xs ++ ys)).
Proof.
  split; intros c c' [] Hrun.
  - rewrite fill_from_roots_steps in Hrun.
    apply bind_inv in Hrun as [c1 [zs [Hst Hrest]]]. rewrite fill_root_app in Hst.
    apply bind_inv in Hst as [ca [xs' [Hxa Hst]]]. apply bind_inv in Hst as [cb [ys' [Hyb Hret]]].
    change (@Ok string _ (cb, xs' ++ ys') = Ok (c1, zs)) in Hret. injection Hret as <- <-.
    pose proof (yields_fill_root imem mem time xs _ _ _ Hxa) as Hx'.
    pose proof (yields_fill_root imem mem time ys _ _ _ Hyb) as Hy'.
    destruct (steps_app imem mem time 3 0 xs' ys' Hx' Hy') as [Hjs _].
    destruct (Hjs cb c' () Hrest) as [e [Hseq He]].
    apply bind_inv in Hseq as [e1 [[] [He1 He2]]].
    destruct (local_comm (at_lvl 0) (above_lvl 0) _ _ ca cb e1 ys' ()
      (local_fill_root imem mem time ys) (local_steps imem mem time 3 0 xs' Hx')
      lvl_disjoint0 Hyb He1) as [d1 [d2 [Hd1 [Hd2 Hed]]]].
    destruct (respects_steps imem mem time 3 ys' e1 d2 e () Hed He2) as [d3 [Hd3 Hed3]].
    exists d3. split; [|eapply equiv_trans; eassumption].
    apply (bind_intro _ _ c d1 d3 () ()).
    + rewrite fill_from_roots_steps. apply (bind_intro _ _ c ca d1 xs' ()); assumption.
    + rewrite fill_from_roots_steps. apply (bind_intro _ _ d1 d2 d3 ys' ()); assumption.
  - apply bind_inv in Hrun as [d1 [[] [H1 H2]]].
    rewrite fill_from_roots_steps in H1, H2.
    apply bind_inv in H1 as [ca [xs' [Hxa Hxs]]].
    apply bind_inv in H2 as [d2 [ys' [Hyb Hys]]].
    pose proof (yields_fill_root imem mem time xs _ _ _ Hxa) as Hx'.
    pose proof (yields_fill_root imem mem time ys _ _ _ Hyb) as Hy'.
    destruct (local_comm (above_lvl 0) (at_lvl 0) _ _ ca d1 d2 () ys'
      (local_steps imem mem time 3 0 xs' Hx') (local_fill_root imem mem time ys)
      (λ fe Ha Hb, lvl_disjoint0 fe Hb Ha) Hxs Hyb) as [e1 [e2 [He1 [He2 Hed]]]].
    destruct (respects_steps imem mem time 3 ys' d2 e2 c' () Hed Hys) as [e3 [He3 Hed3]].
    destruct (steps_app imem mem time 3 0 xs' ys' Hx' Hy') as [_ Hsj].
    destruct (Hsj e1 e3 ()) as [e4 [He4 Hed4]].
    { apply (bind_intro _ _ e1 e2 e3 () ()); assumption. }
    exists e4. split; [|eapply equiv_trans; eassumption].
    rewrite fill_from_roots_steps.
    apply (bind_intro _ _ c e1 e4 (xs' ++ ys') ()); [|exact He4].
    rewrite fill_root_app. apply (bind_intro _ _ c ca e1 xs' (xs' ++ ys')); [exact Hxa|].
    apply (bind_intro _ _ ca e1 e1 ys' (xs' ++ ys')); [exact He1|reflexivity].
Qed.

(** ** Permuting the roots of a fill

    The level-0 entries of a root carry its ASID, table address and half of
    the address space, so distinct roots fill disjoint entries. *)

Definition root_fe (rt : bv 16 * bv 64 * bool) (fe : TLB.FE.t) : Prop :=
  at_lvl 0 fe ∧ TLB.FE.asid fe = Some rt.1.1 ∧ TLB.FE.ttbr fe = rt.1.2 ∧ TLB.FE.upper fe = rt.2.
#[local] Instance root_fe_dec rt fe : Decision (root_fe rt fe).
Proof. unfold root_fe. apply _. Defined.

Lemma root_fe_inj a b fe : root_fe a fe → root_fe b fe → a = b.
Proof.
  destruct a as [[a1 a2] a3], b as [[b1 b2] b3]. unfold root_fe. cbn.
  intros [_ [H1 [H2 H3]]] [_ [H1' [H2' H3']]]. congruence.
Qed.

Lemma local_fill_root_one imem mem time rt :
  local (root_fe rt) (TLB.fill_root imem mem time [rt]).
Proof.
  unfold TLB.fill_root. apply local_fmap, local_mapM. intros [[asid ttbr] upper] Hin.
  apply list_elem_of_singleton in Hin. subst rt.
  apply local_bind; [apply local_get_proj|intros _ _ indexes _].
  apply local_fmap, local_mapM. intros idx _.
  destruct (Memory.read_word _ imem mem time) as [pte|err]; [|apply local_ret].
  destruct (decide (is_table 0%fin pte)); [|apply local_ret].
  apply local_bind.
  - refine (@local_weaken _ (λ q, q = TLB.FE.make0 upper idx asid ttbr pte) _
      (λ q, decide (q = _)) _ _ (local_fill_entry _ _)).
    intros q ->. repeat split.
  - intros _ _ loaded _. destruct loaded; apply local_ret.
Qed.

Lemma fill_root_cons imem mem time x xs c :
  TLB.fill_root imem mem time (x :: xs) c =
  (us ← TLB.fill_root imem mem time [x]; vs ← TLB.fill_root imem mem time xs; mret (us ++ vs)) c.
Proof. exact (fill_root_app imem mem time [x] xs c). Qed.

Theorem fill_root_permutation imem mem time roots roots' : roots ≡ₚ roots' →
  ∀ c c' out, TLB.fill_root imem mem time roots c = Ok (c', out) →
  ∃ c'' out', TLB.fill_root imem mem time roots' c = Ok (c'', out') ∧ equiv c' c'' ∧ out ≡ₚ out'.
Proof.
  induction 1 as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; intros c c' out Hrun.
  - exists c', out. split; [exact Hrun|]. split; [apply equiv_refl|apply Permutation_refl].
  - rewrite fill_root_cons in Hrun.
    apply bind_inv in Hrun as [c1 [ex [Hx Hrun]]]. apply bind_inv in Hrun as [c2 [el [Hl Hret]]].
    change (@Ok string _ (c2, ex ++ el) = Ok (c', out)) in Hret. injection Hret as <- <-.
    destruct (IH c1 c2 el Hl) as [c3 [el' [Hl' [He Hp]]]].
    exists c3, (ex ++ el'). split; [|split; [exact He|apply Permutation_app_head, Hp]].
    rewrite fill_root_cons. apply (bind_intro _ _ c c1 c3 ex); [exact Hx|].
    apply (bind_intro _ _ c1 c3 c3 el'); [exact Hl'|reflexivity].
  - destruct (decide (x = y)) as [->|Hne].
    { exists c', out. split; [exact Hrun|]. split; [apply equiv_refl|apply Permutation_refl]. }
    rewrite fill_root_cons in Hrun.
    apply bind_inv in Hrun as [c1 [ey [Hy Hrun]]]. apply bind_inv in Hrun as [c2 [rest [Hrest Hret]]].
    change (@Ok string _ (c2, ey ++ rest) = Ok (c', out)) in Hret. injection Hret as <- <-.
    rewrite fill_root_cons in Hrest.
    apply bind_inv in Hrest as [c3 [ex [Hx Hrest]]]. apply bind_inv in Hrest as [c4 [el [Hl Hret]]].
    change (@Ok string _ (c4, ex ++ el) = Ok (c2, rest)) in Hret. injection Hret as <- <-.
    destruct (local_comm (root_fe y) (root_fe x) _ _ c c1 c3 ey ex
      (local_fill_root_one imem mem time y) (local_fill_root_one imem mem time x)
      (λ fe Ha Hb, Hne (eq_sym (root_fe_inj y x fe Ha Hb))) Hy Hx) as [d1 [d2 [Hd1 [Hd2 Hed]]]].
    destruct (fill_root_equiv imem mem time l c3 d2 c4 el Hed Hl) as [d3 [Hd3 Hed3]].
    exists d3, (ex ++ ey ++ el). split; [|split; [exact Hed3|]].
    + rewrite fill_root_cons. apply (bind_intro _ _ c d1 d3 ex); [exact Hd1|].
      apply (bind_intro _ _ d1 d3 d3 (ey ++ el)); [|reflexivity].
      rewrite fill_root_cons. apply (bind_intro _ _ d1 d2 d3 ey); [exact Hd2|].
      apply (bind_intro _ _ d2 d3 d3 el); [exact Hd3|reflexivity].
    + rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - destruct (IH1 c c' out Hrun) as [c1 [o1 [H1 [He1 Hp1]]]].
    destruct (IH2 c c1 o1 H1) as [c2 [o2 [H2 [He2 Hp2]]]].
    exists c2, o2. split; [exact H2|]. split; [eapply equiv_trans; eassumption|].
    eapply Permutation_trans; eassumption.
Qed.

(** Root fills at one timestamp do not depend on the order of the roots, up
    to [equiv]. *)
Theorem fill_from_roots_permutation imem mem time roots roots' : roots ≡ₚ roots' →
  sim_to (TLB.fill_from_roots imem mem time roots) (TLB.fill_from_roots imem mem time roots').
Proof.
  intros Hperm c c' [] Hrun. rewrite fill_from_roots_steps in Hrun.
  apply bind_inv in Hrun as [c1 [es [Hroot Hsteps]]].
  destruct (fill_root_permutation imem mem time roots roots' Hperm c c1 es Hroot)
    as [c2 [es' [Hroot' [He Hp]]]].
  destruct (VMCacheTraversal.fill_from_entries_permutation imem mem time es es' c1 c2 c' He Hp Hsteps)
    as [c3 [Hsteps' He3]].
  exists c3. split; [|exact He3].
  rewrite fill_from_roots_steps. apply (bind_intro _ _ c c2 c3 es'); assumption.
Qed.

Lemma sim_to_trans {A} (ra rb rc : action A) : sim_to ra rb → sim_to rb rc → sim_to ra rc.
Proof.
  intros Hab Hbc c c' x Hrun. destruct (Hab c c' x Hrun) as [c1 [H1 He1]].
  destruct (Hbc c c1 x H1) as [c2 [H2 He2]]. exists c2. split; [exact H2|eapply equiv_trans; eassumption].
Qed.

End Footprint.

(** * Squares up to simulated caches

    Root fills at [p - 1] and [p] of the longer history merge into one root
    fill at [p - 1] under the collapse; the result equals the separate fills
    only up to [VMCacheRefill.equiv]. [wsq f ra rb] relates [ra] on a cache [c]
    to [rb] on every cache simulated ([VMCacheSim.cache_sim]) by [tlb_map f c]. *)

Section SimSquares.
Import VMCacheRefill.

Lemma history_tlb_map f c fe : history (tlb_map f c) fe = map_evs f (history c fe).
Proof.
  unfold history. rewrite tlb_map_vatlb, vatlb_lookup_map.
  destruct (TLB.vatlb c !! fe); reflexivity.
Qed.

Lemma obs_tlb_map f a b :
  VMCacheContext.observational a b →
  VMCacheContext.observational (tlb_map f a) (tlb_map f b).
Proof.
  intros [[Hp Hh] [Hr He]]. split; [split|split].
  - exact Hp.
  - intro fe. rewrite !history_tlb_map, Hh. reflexivity.
  - cbn [tlb_map TLB.asid_roots]. rewrite Hr. reflexivity.
  - exact He.
Qed.

Lemma wf_tlb_map f c : VMCacheSim.wf (tlb_map f c) ↔ VMCacheSim.wf c.
Proof.
  unfold VMCacheSim.wf, VMCacheIndexed.valid, VMCacheLastTLBI.unique,
    VMCacheExchange.unique_entries.
  cbn [tlb_map TLB.vatlb TLB.next_table_cache].
  assert (Hsome : ∀ fe, is_Some (vatlb_map f (TLB.vatlb c) !! fe) ↔ is_Some (TLB.vatlb c !! fe)).
  { intro fe. rewrite vatlb_lookup_map. apply fmap_is_Some. }
  assert (Hkeys : ∀ ctxt, map fst (TLB.VATLB.get ctxt (vatlb_map f (TLB.vatlb c))) =
    map fst (TLB.VATLB.get ctxt (TLB.vatlb c))).
  { intro ctxt. rewrite vatlb_get_map, map_map. reflexivity. }
  split; intros [Hv Hu]; split.
  - intro page. destruct (Hv page) as [Hn He]. split; [exact Hn|].
    intro fe. specialize (He fe). specialize (Hsome fe). tauto.
  - intro ctxt. rewrite <- Hkeys. apply Hu.
  - intro page. destruct (Hv page) as [Hn He]. split; [exact Hn|].
    intro fe. specialize (He fe). specialize (Hsome fe). tauto.
  - intro ctxt. rewrite Hkeys. apply Hu.
Qed.

Lemma cache_sim_tlb_map f a b :
  VMCacheSim.cache_sim a b → VMCacheSim.cache_sim (tlb_map f a) (tlb_map f b).
Proof.
  intros [Ho [Ha Hb]]. split; [apply obs_tlb_map, Ho|].
  split; apply wf_tlb_map; assumption.
Qed.

(** Replay on simulated caches. *)
Lemma sim_of_equiv {A} (run : action A) :
  (∀ a b a' x, VMCacheSim.wf a → VMCacheSim.wf b → equiv a b → run a = Ok (a', x) →
    ∃ b', run b = Ok (b', x) ∧ equiv a' b') →
  VMCacheRoots.preserves run → VMCacheConfig.preserves run →
  VMCacheIndexed.preserves run → VMCacheLastTLBI.keeps VMCacheLastTLBI.unique run →
  VMCacheSim.sim_action run.
Proof.
  intros Heq Hroots Hconf Hval Huniq a b a' x [[He [Hr Hets]] [[Hva Hua] [Hvb Hub]]] Hrun.
  destruct (Heq a b a' x (conj Hva Hua) (conj Hvb Hub) He Hrun) as [b' [Hb He']].
  exists b'. split; [exact Hb|].
  pose proof (Hroots _ _ _ Hrun) as R1. pose proof (Hroots _ _ _ Hb) as R2.
  pose proof (Hconf _ _ _ Hrun) as C1. pose proof (Hconf _ _ _ Hb) as C2.
  unfold VMCacheRoots.config in R1, R2. unfold VMCacheConfig.config in C1, C2.
  split; [split; [exact He'|split]|split; split].
  - congruence.
  - injection C1 as _ C1. injection C2 as _ C2. congruence.
  - exact (Hval _ _ _ Hva Hrun).
  - exact (Huniq _ _ _ Hua Hrun).
  - exact (Hval _ _ _ Hvb Hb).
  - exact (Huniq _ _ _ Hub Hb).
Qed.

Lemma fill_event_sim tid imem mem time roots ev :
  VMCacheSim.sim_action (TLB.fill_event tid imem mem time roots ev).
Proof.
  apply sim_of_equiv.
  - intros a b a' [] [Hva Hua] [Hvb Hub] He Hrun.
    exact (VMCacheLastTLBI.fill_event_equiv tid imem mem time roots ev a b a' Hva Hvb Hua Hub He Hrun).
  - apply VMCacheRoots.fill_event.
  - apply VMCacheConfig.fill_event.
  - apply VMCacheIndexed.fill_event.
  - apply VMCacheLastTLBI.unique_fill_event.
Qed.

Lemma fill_from_roots_sim imem mem time roots :
  VMCacheSim.sim_action (TLB.fill_from_roots imem mem time roots).
Proof.
  apply sim_of_equiv.
  - intros a b a' x _ _ He Hrun. exact (fill_from_roots_equiv imem mem time roots a b a' x He Hrun).
  - apply VMCacheRoots.fill_from_roots.
  - apply VMCacheConfig.fill_from_roots.
  - apply VMCacheIndexed.fill_from_roots.
  - apply VMCacheLastTLBI.unique_fill_from_roots.
Qed.

Lemma fill_from_btw_sim tid imem fullmem roots tmin tmax mem :
  VMCacheSim.sim_action (TLB.fill_from_btw tid imem fullmem roots tmin tmax mem).
Proof.
  apply sim_of_equiv.
  - intros a b a' [] [Hva Hua] [Hvb Hub] He Hrun.
    exact (VMCacheLastTLBI.fill_from_btw_equiv tid imem fullmem roots tmin tmax mem a b a'
      Hva Hvb Hua Hub He Hrun).
  - apply VMCacheRoots.fill_from_btw.
  - apply VMCacheConfig.fill_from_btw.
  - apply VMCacheIndexed.fill_from_btw.
  - apply VMCacheLastTLBI.unique_fill_from_btw.
Qed.

(** [wsq f ra rb]: [ra] on a cache [c] is replayed by [rb] on every cache
    simulated by [tlb_map f c]. *)
Definition wsq {A} (f : nat → nat) (ra rb : action A) : Prop :=
  ∀ c d c' x, VMCacheSim.cache_sim (tlb_map f c) d → ra c = Ok (c', x) →
    ∃ d', rb d = Ok (d', x) ∧ VMCacheSim.cache_sim (tlb_map f c') d'.

Lemma wsq_of_natural {A} f (ra rb : action A) :
  natural f ra rb → VMCacheSim.sim_action rb → wsq f ra rb.
Proof.
  intros Hn Hs c d c' x Hsim Hrun.
  assert (H : rb (tlb_map f c) = Ok (tlb_map f c', x)) by (rewrite Hn, Hrun; reflexivity).
  exact (Hs _ _ _ _ Hsim H).
Qed.

Lemma wsq_bind {A B} f (ra rb : action A) (ka kb : A → action B) :
  wsq f ra rb → (∀ x, wsq f (ka x) (kb x)) → wsq f (ra ≫= ka) (rb ≫= kb).
Proof.
  intros Ha Hk c d c'' y Hsim Hrun. apply bind_inv in Hrun as [c' [x [H1 H2]]].
  destruct (Ha c d c' x Hsim H1) as [d' [Hd1 Hsim']].
  destruct (Hk x c' d' c'' y Hsim' H2) as [d'' [Hd2 Hsim'']].
  exists d''. split; [|exact Hsim'']. exact (bind_intro _ _ d d' d'' x y Hd1 Hd2).
Qed.

Lemma wsq_ret {A} f (x : A) : wsq f (mret x) (mret x).
Proof. apply wsq_of_natural; [apply natural_ret|apply VMCacheSim.sim_ret]. Qed.

(** Removal through a collapse up to simulation. *)
Theorem wsq_remove_collapse {A} p (Hp : 0 < p) (long long' short : action A) :
  natural (shift p) short long' → wsq (collapse p) long long' → wsq (unshift p) long short.
Proof.
  intros Hins Hcol c d c' x Hsim Hrun.
  pose proof (cache_sim_tlb_map (shift p) _ _ Hsim) as Hsim'.
  rewrite (tlb_map_shift_unshift p Hp) in Hsim'.
  destruct (Hcol c _ c' x Hsim' Hrun) as [d' [Hd' Hsimd]].
  rewrite Hins in Hd'.
  destruct (short d) as [[d1 y]|err] eqn:Hs; cbn in Hd'; [|discriminate].
  injection Hd' as <- <-. exists d1. split; [reflexivity|].
  pose proof (cache_sim_tlb_map (unshift p) _ _ Hsimd) as H.
  rewrite (tlb_map_unshift_collapse p) , (tlb_map_unshift_shift p) in H. exact H.
Qed.
Lemma wsq_get_roots {A} f (ka kb : list (bv 16 * bv 64 * bool * nat) → action A) :
  (∀ rs, wsq f (ka rs) (kb (map_roots f rs))) →
  wsq f (mget TLB.asid_roots ≫= ka) (mget TLB.asid_roots ≫= kb).
Proof.
  intros Hk c d c' x Hsim Hrun.
  change ((mget TLB.asid_roots ≫= ka : action A) c) with (ka (TLB.asid_roots c) c) in Hrun.
  change ((mget TLB.asid_roots ≫= kb : action A) d) with (kb (TLB.asid_roots d) d).
  assert (Hr : TLB.asid_roots d = map_roots f (TLB.asid_roots c)).
  { destruct Hsim as [[_ [Hr _]] _]. rewrite <- Hr. reflexivity. }
  rewrite Hr. exact (Hk _ c d c' x Hsim Hrun).
Qed.

(** A cache with the same histories, roots and ETS as a well formed cache is
    simulated by everything that cache is simulated by. *)
Lemma cache_sim_equiv_l a b d : equiv a b → TLB.asid_roots a = TLB.asid_roots b →
  TLB.ets a = TLB.ets b → VMCacheSim.wf a → VMCacheSim.cache_sim b d → VMCacheSim.cache_sim a d.
Proof.
  intros He Hr Hets Hwf [[He' [Hr' Hets']] [_ Hwd]]. split; [|split; assumption].
  split; [eapply equiv_trans; eassumption|split; congruence].
Qed.
Lemma bind_unit_run {A} (ra : action ()) (k : action A) c c'' y :
  (ra ≫= λ _, k) c = Ok (c'', y) → ∃ c', ra c = Ok (c', ()) ∧ k c' = Ok (c'', y).
Proof. intro H. apply bind_inv in H as [c' [[] H]]. exists c'. exact H. Qed.

Lemma fill_from_btw_nil tid imem m roots tmin tmax c c' : tmin ≤ tmax →
  TLB.fill_from_btw tid imem m roots tmin tmax [] c ≠ Ok (c', ()).
Proof. intro H. destruct tmax; cbn [TLB.fill_from_btw]; rewrite decide_False by lia; discriminate. Qed.

Lemma fill_from_btw_zero tid imem m roots tmin iter c c' : tmin ≤ 0 →
  TLB.fill_from_btw tid imem m roots tmin 0 iter c ≠ Ok (c', ()).
Proof. intro H. cbn [TLB.fill_from_btw]. rewrite decide_False by lia. discriminate. Qed.

Lemma fill_from_btw_unfold tid imem m roots tmin tmax n ev it c : tmax = S n → tmin ≤ tmax →
  TLB.fill_from_btw tid imem m roots tmin tmax (ev :: it) c =
  (TLB.fill_from_btw tid imem m (filter (λ '(_, time), time < tmax) roots) tmin n it;;
   TLB.fill_event tid imem m tmax (filter (λ '(_, time), time < tmax) roots).*1 ev;;
   TLB.fill_from_roots imem m tmax (filter (λ '(_, time), time = tmax) roots).*1) c.
Proof. intros -> H. cbn [TLB.fill_from_btw]. rewrite decide_False by lia. reflexivity. Qed.

Lemma roll_back_sim time : VMCacheSim.sim_action (TLB.roll_back time).
Proof.
  apply sim_of_equiv.
  - intros a b a' [] _ _ He Hrun. injection Hrun as <-.
    eexists. split; [reflexivity|]. apply VMCacheEvents.map_equiv; [reflexivity|exact He].
  - unfold TLB.roll_back. apply VMCacheRoots.preserves_set. reflexivity.
  - unfold TLB.roll_back. apply VMCacheConfig.preserves_set. reflexivity.
  - apply VMCacheIndexed.roll_back.
  - apply VMCacheLastTLBI.unique_roll_back.
Qed.

Lemma mset_roots_sim g : VMCacheSim.sim_action (mset TLB.asid_roots g).
Proof.
  intros a b a' [] [[[Hp Hh] [Hr Hets]] [[Hva Hua] [Hvb Hub]]] Hrun.
  change (@Ok string _ (set TLB.asid_roots g a, ()) = Ok (a', ())) in Hrun. injection Hrun as <-.
  exists (set TLB.asid_roots g b). split; [reflexivity|].
  split; [split; [split; [exact Hp|exact Hh]|split]|split; split].
  - cbn [set TLB.asid_roots]. destruct a, b; cbn in *. congruence.
  - destruct a, b; cbn in *. exact Hets.
  - exact (VMCacheIndexed.roots g a _ () Hva eq_refl).
  - exact (VMCacheLastTLBI.unique_roots g a _ () Hua eq_refl).
  - exact (VMCacheIndexed.roots g b _ () Hvb eq_refl).
  - exact (VMCacheLastTLBI.unique_roots g b _ () Hub eq_refl).
Qed.

Section CollapseSim.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Local Notation p := (S (length r)).
Local Notation h := (collapse (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

Lemma collapse_added_perm (roots : list (bv 16 * bv 64 * bool * nat)) :
  filter (λ '(_, time), time = length r) (map_roots h roots) ≡ₚ
  map_roots h (filter (λ '(_, time), time = length r) roots ++
    filter (λ '(_, time), time = p) roots).
Proof.
  induction roots as [|[x t] roots IH]; [apply Permutation_refl|].
  unfold map_roots in *. cbn [map fst snd]. rewrite !filter_cons.
  destruct (decide (t = p)) as [->|Hne].
  - rewrite collapse_at. cbn [pred].
    repeat case_decide; try lia. rewrite map_app. cbn [map fst snd]. rewrite collapse_at.
    apply Permutation_cons_app. rewrite <- map_app. exact IH.
  - rewrite (collapse_ne p t Hne).
    repeat case_decide; try lia; [|exact IH].
    cbn [app map fst snd]. rewrite collapse_ne by lia. apply perm_skip, IH.
Qed.

Lemma filter_lt_lt (roots : list (bv 16 * bv 64 * bool * nat)) a b : a ≤ b →
  filter (λ '(_, time), time < a) (filter (λ '(_, time), time < b) roots) =
  filter (λ '(_, time), time < a) roots.
Proof.
  intro Hab. rewrite list_filter_filter.
  apply list_filter_iff. intros [x t]. cbn. lia.
Qed.

Lemma filter_eq_lt (roots : list (bv 16 * bv 64 * bool * nat)) a b : a < b →
  filter (λ '(_, time), time = a) (filter (λ '(_, time), time < b) roots) =
  filter (λ '(_, time), time = a) roots.
Proof.
  intro Hab. rewrite list_filter_filter.
  apply list_filter_iff. intros [x t]. cbn. lia.
Qed.

Lemma fill_from_roots_wf imem' m t rs c c' :
  VMCacheSim.wf c → TLB.fill_from_roots imem' m t rs c = Ok (c', ()) → VMCacheSim.wf c'.
Proof.
  intros [Hv Hu] Hrun. split.
  - exact (VMCacheIndexed.fill_from_roots imem' m t rs c c' () Hv Hrun).
  - exact (VMCacheLastTLBI.unique_fill_from_roots imem' m t rs c c' () Hu Hrun).
Qed.

Lemma fill_from_roots_config imem' m t rs c c' :
  TLB.fill_from_roots imem' m t rs c = Ok (c', ()) →
  TLB.asid_roots c' = TLB.asid_roots c ∧ TLB.ets c' = TLB.ets c.
Proof.
  intro Hrun. split.
  - exact (VMCacheRoots.fill_from_roots imem' m t rs c c' () Hrun).
  - pose proof (VMCacheConfig.fill_from_roots imem' m t rs c c' () Hrun) as H.
    unfold VMCacheConfig.config in H. congruence.
Qed.

(** The two root fills at [p - 1] and [p] of the longer history collapse to one
    root fill at [p - 1] with the interleaved roots. *)
Lemma collapse_pair_sim (A B C : list (bv 16 * bv 64 * bool)) c c1 c' d :
  C ≡ₚ A ++ B → VMCacheSim.wf c →
  TLB.fill_from_roots imem mem' (length r) A c = Ok (c1, ()) →
  TLB.fill_from_roots imem mem' p B c1 = Ok (c', ()) →
  VMCacheSim.cache_sim (tlb_map h c) d →
  ∃ d', TLB.fill_from_roots imem mem' (length r) C d = Ok (d', ()) ∧
    VMCacheSim.cache_sim (tlb_map h c') d'.
Proof.
  intros Hperm Hwf H1 H2 Hsim.
  assert (Hb : p ≤ S (length mem)) by (rewrite length_app; lia).
  assert (Hm1 : TLB.fill_from_roots imem mem' (length r) A (tlb_map h c) = Ok (tlb_map h c1, ())).
  { pose proof (fill_from_roots_collapse imem l r tlbi rc k (length r) A) as N.
    rewrite collapse_ne in N by lia. rewrite N by lia. rewrite H1. reflexivity. }
  assert (Hm2 : TLB.fill_from_roots imem mem' (length r) B (tlb_map h c1) = Ok (tlb_map h c', ())).
  { pose proof (fill_from_roots_collapse imem l r tlbi rc k p B Hb) as N.
    rewrite collapse_at in N. cbn [pred] in N. rewrite N, H2. reflexivity. }
  destruct (proj2 (fill_from_roots_app imem mem' (length r) A B) (tlb_map h c) (tlb_map h c') ()
    (bind_intro _ _ _ _ _ () () Hm1 Hm2)) as [e1 [He1 Heq1]].
  destruct (fill_from_roots_permutation imem mem' (length r) (A ++ B) C (Permutation_sym Hperm)
    _ _ () He1) as [e2 [He2 Heq2]].
  destruct (fill_from_roots_sim imem mem' (length r) C _ d e2 () Hsim He2) as [d' [Hd' Hsim']].
  exists d'. split; [exact Hd'|].
  pose proof (fill_from_roots_config _ _ _ _ _ _ Hm1) as [R1 E1].
  pose proof (fill_from_roots_config _ _ _ _ _ _ Hm2) as [R2 E2].
  pose proof (fill_from_roots_config _ _ _ _ _ _ He2) as [R3 E3].
  apply (cache_sim_equiv_l _ e2); [eapply equiv_trans; eassumption|congruence|congruence| |exact Hsim'].
  apply wf_tlb_map.
  pose proof (fill_from_roots_wf imem mem' (length r) A _ _ Hwf H1) as Hwf1.
  exact (fill_from_roots_wf imem mem' p B _ _ Hwf1 H2).
Qed.

Hypothesis Hrc : tid ≠ rc.

(** The refill step at [p] of a refill starting at or below [p - 1]: the root
    fills at [p - 1] and [p] merge. *)
Lemma collapse_at_sim roots tmin iter : tmin ≤ length r →
  wsq h (TLB.fill_from_btw tid imem mem' roots tmin p (e :: iter))
    (TLB.fill_from_btw tid imem mem' (map_roots h roots) tmin p (e :: iter)).
Proof using Hrc.
  intros Hmin c d c' [] Hsim Hrun.
  rewrite (fill_from_btw_unfold _ _ _ _ _ _ (length r)) in Hrun by lia.
  rewrite (fill_from_btw_unfold _ _ _ _ _ _ (length r)) by lia.
  apply bind_unit_run in Hrun as [c1 [Hx Hrest]].
  apply bind_unit_run in Hrest as [c2 [Hev Hfill]].
  unfold TLB.fill_event in Hev. rewrite decide_False in Hev by exact Hrc.
  change (@Ok string _ (c1, ()) = Ok (c2, ())) in Hev. injection Hev as <-.
  destruct (decide (length r = 0)) as [E0|E0].
  { exfalso. rewrite E0 in Hx. assert (H0 : tmin ≤ 0) by lia.
    exact (fill_from_btw_zero _ _ _ _ _ _ _ _ H0 Hx). }
  destruct iter as [|ev it].
  { exfalso. assert (H0 : tmin ≤ length r) by lia.
    exact (fill_from_btw_nil _ _ _ _ _ _ _ _ H0 Hx). }
  rewrite (fill_from_btw_unfold _ _ _ _ _ _ (pred (length r))) in Hx by lia.
  rewrite filter_lt_lt, filter_eq_lt in Hx by lia.
  apply bind_unit_run in Hx as [c3 [Hy Hx]]. apply bind_unit_run in Hx as [c4 [Hevq HA]].
  assert (Hlen : length r ≤ S (length mem)) by (rewrite length_app; lia).
  (* the prefix below [p - 1] *)
  destruct (wsq_of_natural h _ _
    (fill_from_btw_collapse_below tid imem l r tlbi rc k (pred (length r))
      (filter (λ '(_, time), time < length r) roots) it tmin tmin ltac:(lia) (or_introl eq_refl)
      ltac:(intros x Hx Hxp; apply list_elem_of_filter in Hx as [Hx _];
            destruct x as [? t]; cbn in Hx, Hxp; lia))
    (fill_from_btw_sim _ _ _ _ _ _ _) c d c3 () Hsim Hy) as [d3 [Hd3 Hsim3]].
  (* the event at [p - 1] *)
  pose proof (fill_event_collapse tid imem l r tlbi rc k (length r)
    (filter (λ '(_, time), time < length r) roots).*1 ev Hlen) as Nev.
  rewrite collapse_ne in Nev by lia.
  destruct (wsq_of_natural h _ _ Nev (fill_event_sim _ _ _ _ _ _) c3 d3 c4 () Hsim3 Hevq)
    as [d4 [Hd4 Hsim4]].
  (* the merged root fills *)
  assert (Hperm : (filter (λ '(_, time), time = length r) (map_roots h roots)).*1 ≡ₚ
    (filter (λ '(_, time), time = length r) roots).*1 ++ (filter (λ '(_, time), time = p) roots).*1).
  { pose proof (Permutation_map fst (collapse_added_perm roots)) as P.
    change (fst <$> filter (λ '(_, time), time = length r) (map_roots h roots) ≡ₚ
      (map_roots h (filter (λ '(_, time), time = length r) roots ++
        filter (λ '(_, time), time = p) roots)).*1) in P.
    rewrite map_roots_fst, fmap_app in P. exact P. }
  pose proof (proj1 (wf_tlb_map h c4) (proj1 (proj2 Hsim4))) as Hwf4.
  destruct (collapse_pair_sim _ _ _ c4 c1 c' d4 Hperm Hwf4 HA Hfill Hsim4) as [d5 [Hd5 Hsim5]].
  exists d5. split; [|exact Hsim5].
  apply (bind_intro _ _ d d5 d5 () ()).
  - rewrite (fill_from_btw_unfold _ _ _ _ _ _ (pred (length r))) by lia.
    rewrite filter_lt_lt, filter_eq_lt by lia.
    rewrite (filter_map_roots_lt h (length r) (length r)) by (intro t; collapse_cases).
    rewrite map_roots_fst.
    apply (bind_intro _ _ d d3 d5 () ()); [exact Hd3|].
    apply (bind_intro _ _ d3 d4 d5 () ()); [exact Hd4|exact Hd5].
  - cbv beta. rewrite (filter_map_roots_eq_none h p) by (intro t; collapse_cases).
    exact (inserted_event_noop tid imem l r tlbi rc k Hrc _ d5).
Qed.

Lemma collapse_above_sim l' : ∀ roots tmin, tmin ≤ length r → length l' ≤ length l →
  wsq h (TLB.fill_from_btw tid imem mem' roots tmin (length (l' ++ e :: r)) (l' ++ e :: r))
    (TLB.fill_from_btw tid imem mem' (map_roots h roots) tmin (length (l' ++ e :: r))
      (l' ++ e :: r)).
Proof using Hrc.
  induction l' as [|x l' IH]; intros roots tmin Hmin Hl.
  - cbn [app length]. apply collapse_at_sim, Hmin.
  - cbn [app length]. cbn [TLB.fill_from_btw].
    assert (Hge : p ≤ length (l' ++ e :: r)) by (rewrite length_app; cbn; lia).
    rewrite !decide_False by lia.
    rewrite (filter_map_roots_lt h (S (length (l' ++ e :: r))) (S (length (l' ++ e :: r))))
      by (intro t; collapse_cases).
    rewrite (filter_map_roots_eq h (S (length (l' ++ e :: r))) (S (length (l' ++ e :: r))))
      by (intro t; collapse_cases).
    rewrite !map_roots_fst.
    apply wsq_bind; [apply IH; [exact Hmin|cbn in Hl; lia]|intros _].
    assert (Hb : S (length (l' ++ e :: r)) ≤ S (length mem)).
    { cbn [length] in Hl. rewrite !length_app in *. cbn in *. lia. }
    apply wsq_bind; [|intros _].
    + apply wsq_of_natural; [|apply fill_event_sim].
      pose proof (fill_event_collapse tid imem l r tlbi rc k (S (length (l' ++ e :: r)))
        (filter (λ '(_, time), time < S (length (l' ++ e :: r))) roots).*1 x) as H.
      rewrite collapse_ne in H by lia. apply H, Hb.
    + apply wsq_of_natural; [|apply fill_from_roots_sim].
      pose proof (fill_from_roots_collapse imem l r tlbi rc k (S (length (l' ++ e :: r)))
        (filter (λ '(_, time), time = S (length (l' ++ e :: r))) roots).*1) as H.
      rewrite collapse_ne in H by lia. apply H, Hb.
Qed.

(** A refill starting at or below [p - 1] collapses up to simulation, with
    roots at [p] allowed. *)
Theorem fill_from_collapse_sim roots tmin : tmin ≤ length r →
  wsq h (TLB.fill_from tid imem mem' roots tmin)
    (TLB.fill_from tid imem mem' (map_roots h roots) tmin).
Proof using Hrc.
  intro Hmin. unfold TLB.fill_from. exact (collapse_above_sim l roots tmin Hmin (le_n _)).
Qed.

(** Root fills strictly below [p - 1] collapse up to simulation on every cache. *)
Theorem fill_asid_root_collapse_sim root time : S time ≤ length r →
  wsq h (TLB.fill_asid_root tid imem mem' root time)
    (TLB.fill_asid_root tid imem mem' root (h time)).
Proof using Hrc.
  intro Hlt. rewrite (collapse_ne p time) by lia. unfold TLB.fill_asid_root.
  apply wsq_bind; [|intros _].
  { apply wsq_of_natural; [|apply roll_back_sim].
    pose proof (roll_back_collapse r time ltac:(lia)) as H.
    rewrite (collapse_ne p time) in H by lia. exact H. }
  apply wsq_bind; [|intros _].
  { apply wsq_of_natural; [|apply mset_roots_sim].
    apply natural_mset_roots. intro rs. cbn [map_roots map fst snd].
    rewrite (collapse_ne p time) by lia. reflexivity. }
  apply wsq_bind; [|intros _].
  { apply wsq_of_natural; [|apply fill_from_roots_sim].
    pose proof (fill_from_roots_collapse imem l r tlbi rc k time [root]) as H.
    rewrite (collapse_ne p time) in H by lia. apply H. rewrite length_app. lia. }
  apply wsq_get_roots. intro rs. apply fill_from_collapse_sim. exact Hlt.
Qed.

Theorem fill_asid_root_remove_sim root time : S time ≤ length r →
  wsq (unshift p) (TLB.fill_asid_root tid imem mem' root time)
    (TLB.fill_asid_root tid imem mem root (unshift p time)).
Proof using Hrc.
  intro Hlt.
  apply (wsq_remove_collapse p (Hp r) _ (TLB.fill_asid_root tid imem mem' root (h time))).
  - pose proof (fill_asid_root_shifted tid imem l r tlbi rc k Hrc root (unshift p time)) as H.
    rewrite (shift_unshift_collapse p time (Hp r)) in H.
    apply H. rewrite unshift_lt by lia. rewrite length_app. lia.
  - apply fill_asid_root_collapse_sim, Hlt.
Qed.

End CollapseSim.
End SimSquares.

(** * Rollbacks to [p - 1] (case (a))

    A rollback to [p - 1] of the longer history drops the entries loaded at
    [p], while the collapsed rollback keeps them (at [p - 1]). Invariant [J]
    states that those entries are exactly the refill of the roots of time [p]
    on the cache rolled back to [p - 1]; with it, a root fill at [p - 1] and a
    context synchronization at [p - 1] (without roots at [p]) are squares up
    to simulation. *)

Section RollbackCollapse.
Import VMCacheRefill.
Local Notation rolled := VMCacheExchange.rolled.

Lemma roll_back_run t c : TLB.roll_back t c = Ok (rolled t c, ()).
Proof. reflexivity. Qed.

Lemma equiv_tlb_map f a b : equiv a b → equiv (tlb_map f a) (tlb_map f b).
Proof. intros [Hp Hh]. split; [exact Hp|]. intro fe. rewrite !history_tlb_map, Hh. reflexivity. Qed.

Lemma wf_rolled t c : VMCacheSim.wf c → VMCacheSim.wf (rolled t c).
Proof.
  intros [Hv Hu]. split.
  - exact (VMCacheIndexed.roll_back t c _ () Hv (roll_back_run t c)).
  - exact (VMCacheLastTLBI.unique_roll_back t c _ () Hu (roll_back_run t c)).
Qed.

Lemma fill_from_btw_stop' tid imem m roots tmin tmax iter c : tmax < tmin →
  TLB.fill_from_btw tid imem m roots tmin tmax iter c = Ok (c, ()).
Proof. intro H. destruct tmax; cbn [TLB.fill_from_btw]; rewrite decide_True by lia; reflexivity. Qed.

Lemma fill_from_roots_det imem m t rs c a b :
  TLB.fill_from_roots imem m t rs c = Ok (a, ()) → TLB.fill_from_roots imem m t rs c = Ok (b, ()) → a = b.
Proof. intros H1 H2. rewrite H1 in H2. congruence. Qed.

Section Rolled.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Local Notation p := (S (length r)).
Local Notation q := (length r).
Local Notation h := (collapse (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

Lemma roll_back_collapse_p : natural h (TLB.roll_back p) (TLB.roll_back q).
Proof. apply roll_back_map. intro t. collapse_cases. Qed.

(** The roots of the cache visible from [p]. *)
Definition proots (c : TLB.t) : list (bv 16 * bv 64 * bool) :=
  (filter (λ '(_, time), time = p) (TLB.asid_roots c)).*1.

(** Invariant J: the cache at [p] is the cache at [p - 1] with the roots of
    time [p] filled, up to [equiv]. *)
Definition J (c : TLB.t) : Prop :=
  ∃ c', TLB.fill_from_roots imem mem' p (proots c) (rolled q c) = Ok (c', ()) ∧
    equiv (rolled p c) c'.

Lemma okr_filter (B : list (bv 16 * bv 64 * bool)) :
  ∀ (R : list (bv 16 * bv 64 * bool * nat)) t, p < t →
    (filter (λ '(_, time), time = p) R).*1 = B →
    (filter (λ '(_, time), time = p) (filter (λ '(_, time), time < t) R)).*1 = B.
Proof.
  intros R t Ht HR. rewrite <- HR. f_equal. rewrite list_filter_filter.
  apply list_filter_iff. intros [x u]. cbn. lia.
Qed.

(** A successful refill passes through step [p]. *)
Lemma fill_from_btw_base_ok l' : ∀ R tmin c c', tmin ≤ p →
  TLB.fill_from_btw tid imem mem' R tmin (length (l' ++ e :: r)) (l' ++ e :: r) c = Ok (c', ()) →
  ∃ R' c'', (filter (λ '(_, time), time = p) R').*1 = (filter (λ '(_, time), time = p) R).*1 ∧
    TLB.fill_from_btw tid imem mem' R' tmin p (e :: r) c = Ok (c'', ()).
Proof.
  induction l' as [|x l' IH]; intros R tmin c c' Hmin Hrun.
  - exists R, c'. split; [reflexivity|exact Hrun].
  - cbn [app length] in Hrun.
    assert (Hge : p ≤ length (l' ++ e :: r)) by (rewrite length_app; cbn; lia).
    rewrite (fill_from_btw_unfold _ _ _ _ _ _ (length (l' ++ e :: r))) in Hrun by lia.
    apply bind_unit_run in Hrun as [c1 [H1 _]].
    destruct (IH _ tmin c c1 Hmin H1) as [R' [c'' [HR Hb]]].
    exists R', c''. split; [|exact Hb]. rewrite HR. apply okr_filter; [lia|reflexivity].
Qed.


(** Refill steps above [p] lift a relation at step [p]. *)
Lemma collapse_above_rel (OkR : list (bv 16 * bv 64 * bool * nat) → Prop)
    (Rel : TLB.t → TLB.t → Prop) tmin :
  tmin ≤ p →
  (∀ R t, p < t → OkR R → OkR (filter (λ '(_, time), time < t) R)) →
  (∀ R c d c', OkR R → Rel c d → TLB.fill_from_btw tid imem mem' R tmin p (e :: r) c = Ok (c', ()) →
    ∃ d', TLB.fill_from_btw tid imem mem' (map_roots h R) tmin p (e :: r) d = Ok (d', ()) ∧
      VMCacheSim.cache_sim (tlb_map h c') d') →
  ∀ l' R c d c', OkR R → length l' ≤ length l → Rel c d →
    TLB.fill_from_btw tid imem mem' R tmin (length (l' ++ e :: r)) (l' ++ e :: r) c = Ok (c', ()) →
    ∃ d', TLB.fill_from_btw tid imem mem' (map_roots h R) tmin (length (l' ++ e :: r))
        (l' ++ e :: r) d = Ok (d', ()) ∧ VMCacheSim.cache_sim (tlb_map h c') d'.
Proof.
  intros Hmin Hfilter Hbase l'. induction l' as [|x l' IH]; intros R c d c' HR Hl Hrel Hrun.
  - exact (Hbase R c d c' HR Hrel Hrun).
  - cbn [app length] in Hrun |- *.
    assert (Hge : p ≤ length (l' ++ e :: r)) by (rewrite length_app; cbn; lia).
    set (N := S (length (l' ++ e :: r))) in *.
    rewrite (fill_from_btw_unfold _ _ _ _ _ N (length (l' ++ e :: r))) in Hrun by lia.
    apply bind_unit_run in Hrun as [c1 [H1 Hrun]]. apply bind_unit_run in Hrun as [c2 [H2 H3]].
    destruct (IH (filter (λ '(_, time), time < N) R) c d c1 (Hfilter R N ltac:(lia) HR)
      ltac:(cbn in Hl; lia) Hrel H1) as [d1 [Hd1 Hsim1]].
    assert (Hb : N ≤ S (length mem)).
    { unfold N. cbn [length] in Hl. rewrite !length_app in *. cbn in *. lia. }
    pose proof (fill_event_collapse tid imem l r tlbi rc k N
      (filter (λ '(_, time), time < N) R).*1 x Hb) as N1.
    rewrite collapse_ne in N1 by lia.
    destruct (wsq_of_natural h _ _ N1 (fill_event_sim _ _ _ _ _ _) c1 d1 c2 () Hsim1 H2)
      as [d2 [Hd2 Hsim2]].
    pose proof (fill_from_roots_collapse imem l r tlbi rc k N
      (filter (λ '(_, time), time = N) R).*1 Hb) as N2.
    rewrite collapse_ne in N2 by lia.
    destruct (wsq_of_natural h _ _ N2 (fill_from_roots_sim _ _ _ _) c2 d2 c' () Hsim2 H3)
      as [d3 [Hd3 Hsim3]].
    exists d3. split; [|exact Hsim3].
    rewrite (fill_from_btw_unfold _ _ _ _ _ N (length (l' ++ e :: r))) by lia.
    rewrite (filter_map_roots_lt h N N) by (intro t; unfold N; collapse_cases).
    rewrite (filter_map_roots_eq h N N) by (intro t; unfold N; collapse_cases).
    rewrite !map_roots_fst.
    apply (bind_intro _ _ d d1 d3 () ()); [exact Hd1|].
    apply (bind_intro _ _ d1 d2 d3 () ()); [exact Hd2|exact Hd3].
Qed.

Hypothesis Hrc : tid ≠ rc.

(** Step [p] of a refill starting at [p]: the longer history fills the roots
    of time [p], which the collapsed cache already holds. *)
Lemma collapse_base_ahead (B : list (bv 16 * bv 64 * bool)) R c d c' cB :
  (filter (λ '(_, time), time = p) R).*1 = B →
  TLB.fill_from_roots imem mem' p B c = Ok (cB, ()) →
  VMCacheSim.cache_sim (tlb_map h cB) d →
  TLB.fill_from_btw tid imem mem' R p p (e :: r) c = Ok (c', ()) →
  ∃ d', TLB.fill_from_btw tid imem mem' (map_roots h R) p p (e :: r) d = Ok (d', ()) ∧
    VMCacheSim.cache_sim (tlb_map h c') d'.
Proof using Hrc.
  intros HB HcB Hsim Hrun.
  rewrite (fill_from_btw_unfold _ _ _ _ _ _ q) in Hrun by lia.
  apply bind_unit_run in Hrun as [c1 [H1 Hrun]]. apply bind_unit_run in Hrun as [c2 [H2 H3]].
  rewrite fill_from_btw_stop' in H1 by lia. injection H1 as <-.
  unfold TLB.fill_event in H2. rewrite decide_False in H2 by exact Hrc.
  change (@Ok string _ (c, ()) = Ok (c2, ())) in H2. injection H2 as <-.
  rewrite HB in H3. rewrite (fill_from_roots_det _ _ _ _ _ _ _ H3 HcB).
  exists d. split; [|exact Hsim].
  rewrite (fill_from_btw_unfold _ _ _ _ _ _ q) by lia.
  apply (bind_intro _ _ d d d () ()); [apply fill_from_btw_stop'; lia|].
  cbv beta. rewrite (filter_map_roots_eq_none h p) by (intro t; collapse_cases).
  exact (inserted_event_noop tid imem l r tlbi rc k Hrc _ d).
Qed.

(** Case (a) for a root fill at [p - 1]: the collapsed rollback to [p - 1]
    keeps the entries loaded at [p]; invariant J says they are the entries
    the longer history refills at [p]. *)
Theorem fill_asid_root_collapse_q root c d c' :
  J c → VMCacheSim.cache_sim (tlb_map h c) d →
  TLB.fill_asid_root tid imem mem' root q c = Ok (c', ()) →
  ∃ d', TLB.fill_asid_root tid imem mem' root q d = Ok (d', ()) ∧
    VMCacheSim.cache_sim (tlb_map h c') d'.
Proof using Hrc.
  intros [cJ [HJ HJeq]] Hsim Hrun.
  set (B := proots c) in *.
  set (g := λ rs : list (bv 16 * bv 64 * bool * nat), (root, q) :: rs).
  pose proof (proj1 (wf_tlb_map h c) (proj1 (proj2 Hsim))) as Hwf.
  unfold TLB.fill_asid_root in Hrun.
  apply bind_unit_run in Hrun as [c1 [H1 Hrun]]. rewrite roll_back_run in H1. injection H1 as <-.
  apply bind_unit_run in Hrun as [c2 [H2 Hrun]].
  change (@Ok string _ (set TLB.asid_roots g (rolled q c), ()) = Ok (c2, ())) in H2.
  injection H2 as <-.
  set (c2 := set TLB.asid_roots g (rolled q c)) in *.
  apply bind_unit_run in Hrun as [c3 [H3 H4]].
  change (TLB.fill_from tid imem mem' (TLB.asid_roots c3) (S q) c3 = Ok (c', ())) in H4.
  pose proof (fill_from_roots_config _ _ _ _ _ _ H3) as [R3 E3].
  assert (Hwf2 : VMCacheSim.wf c2).
  { destruct (wf_rolled q c Hwf) as [Hv Hu]. split.
    - exact (VMCacheIndexed.roots g _ _ () Hv eq_refl).
    - exact (VMCacheLastTLBI.unique_roots g _ _ () Hu eq_refl). }
  pose proof (fill_from_roots_wf _ _ _ _ _ _ Hwf2 H3) as Hwf3.
  (* the collapsed rollback holds the [p]-roots' entries *)
  destruct (wsq_of_natural h _ _ roll_back_collapse_p (roll_back_sim q) c d (rolled p c) ()
    Hsim (roll_back_run p c)) as [d1 [Hd1 Hsim1]].
  rewrite roll_back_run in Hd1. injection Hd1 as <-.
  pose proof (fill_from_roots_config _ _ _ _ _ _ HJ) as [RJ EJ].
  assert (HwfJ : VMCacheSim.wf cJ) by exact (fill_from_roots_wf _ _ _ _ _ _ (wf_rolled q c Hwf) HJ).
  assert (Hsim1' : VMCacheSim.cache_sim (tlb_map h cJ) (rolled q d)).
  { apply (cache_sim_equiv_l _ (tlb_map h (rolled p c))); [| | |apply wf_tlb_map, HwfJ|exact Hsim1].
    - apply equiv_tlb_map, equiv_sym, HJeq.
    - cbn [tlb_map TLB.asid_roots]. rewrite RJ. reflexivity.
    - cbn [tlb_map TLB.ets]. rewrite EJ. reflexivity. }
  (* setting the roots *)
  assert (Nset : natural h (mset TLB.asid_roots g) (mset TLB.asid_roots g)).
  { apply natural_mset_roots. intro rs. cbn [map_roots map fst snd g].
    rewrite (collapse_ne p q) by lia. reflexivity. }
  destruct (wsq_of_natural h _ _ Nset (mset_roots_sim g) cJ (rolled q d) (set TLB.asid_roots g cJ) ()
    Hsim1' eq_refl) as [d2 [Hd2 Hsim2]].
  change (@Ok string _ (set TLB.asid_roots g (rolled q d), ()) = Ok (d2, ())) in Hd2.
  injection Hd2 as <-.
  (* [B] filled on the long cache after setting the roots *)
  destruct (fill_from_roots_equiv imem mem' p B (rolled q c) c2 cJ () (equiv_refl _) HJ)
    as [c2B [Hc2B Heq2B]].
  pose proof (fill_from_roots_config _ _ _ _ _ _ Hc2B) as [R2B E2B].
  assert (Hsim2' : VMCacheSim.cache_sim (tlb_map h c2B) (set TLB.asid_roots g (rolled q d))).
  { apply (cache_sim_equiv_l _ (tlb_map h (set TLB.asid_roots g cJ))); [| | | |exact Hsim2].
    - apply equiv_tlb_map, equiv_sym, Heq2B.
    - cbn [tlb_map TLB.asid_roots]. rewrite R2B. unfold c2. destruct c, cJ; cbn in *.
      rewrite RJ. reflexivity.
    - cbn [tlb_map TLB.ets]. rewrite E2B. unfold c2. destruct c, cJ; cbn in *.
      rewrite EJ. reflexivity.
    - apply wf_tlb_map. exact (fill_from_roots_wf _ _ _ _ _ _ Hwf2 Hc2B). }
  (* the long run fills [B] at step [p] on [c3] *)
  set (R := TLB.asid_roots c3) in *.
  assert (HRB : (filter (λ '(_, time), time = p) R).*1 = B).
  { assert (Hc2r : TLB.asid_roots c2 = (root, q) :: TLB.asid_roots c) by (unfold c2; destruct c; reflexivity).
    rewrite R3, Hc2r. unfold B, proots.
    rewrite filter_cons, decide_False by (cbn; lia). reflexivity. }
  unfold TLB.fill_from in H4.
  destruct (fill_from_btw_base_ok l R (S q) c3 c' ltac:(lia) H4) as [Rb [cb [HRb Hb]]].
  rewrite (fill_from_btw_unfold _ _ _ _ _ _ q) in Hb by lia.
  apply bind_unit_run in Hb as [cb1 [Hb1 Hb]]. apply bind_unit_run in Hb as [cb2 [Hb2 Hb3]].
  rewrite fill_from_btw_stop' in Hb1 by lia. injection Hb1 as <-.
  unfold TLB.fill_event in Hb2. rewrite decide_False in Hb2 by exact Hrc.
  change (@Ok string _ (c3, ()) = Ok (cb2, ())) in Hb2. injection Hb2 as <-.
  rewrite HRb, HRB in Hb3. rename Hb3 into Hc3B. rename cb into c3B.
  (* collapsed: [B] (already present) then [root]; long under [h]: [root] then [B] *)
  assert (Hq : q ≤ S (length mem)) by (rewrite length_app; lia).
  assert (Hpb : p ≤ S (length mem)) by (rewrite length_app; lia).
  pose proof (fill_from_roots_collapse imem l r tlbi rc k q [root] Hq) as Nq.
  rewrite collapse_ne in Nq by lia.
  pose proof (fill_from_roots_collapse imem l r tlbi rc k p B Hpb) as Np.
  rewrite collapse_at in Np. cbn [pred] in Np.
  assert (M3 : TLB.fill_from_roots imem mem' q [root] (tlb_map h c2) = Ok (tlb_map h c3, ()))
    by (rewrite Nq, H3; reflexivity).
  assert (M3B : TLB.fill_from_roots imem mem' q B (tlb_map h c3) = Ok (tlb_map h c3B, ()))
    by (rewrite Np, Hc3B; reflexivity).
  assert (M2B : TLB.fill_from_roots imem mem' q B (tlb_map h c2) = Ok (tlb_map h c2B, ()))
    by (rewrite Np, Hc2B; reflexivity).
  destruct (proj2 (fill_from_roots_app imem mem' q [root] B) _ _ ()
    (bind_intro _ _ _ _ _ () () M3 M3B)) as [z1 [Hz1 Heq1]].
  destruct (fill_from_roots_permutation imem mem' q ([root] ++ B) (B ++ [root])
    (Permutation_app_comm _ _) _ _ () Hz1) as [z2 [Hz2 Heq2]].
  destruct (proj1 (fill_from_roots_app imem mem' q B [root]) _ _ () Hz2) as [z3 [Hz3 Heq3]].
  apply bind_unit_run in Hz3 as [y [Hy Hz3]].
  rewrite M2B in Hy. injection Hy as <-.
  destruct (fill_from_roots_sim imem mem' q [root] _ _ z3 () Hsim2' Hz3) as [d3 [Hd3 Hsim3]].
  assert (Hsim3' : VMCacheSim.cache_sim (tlb_map h c3B) d3).
  { pose proof (fill_from_roots_config _ _ _ _ _ _ Hz3) as [Rz Ez].
    pose proof (fill_from_roots_config _ _ _ _ _ _ Hc3B) as [R3B E3B].
    apply (cache_sim_equiv_l _ z3); [| | | |exact Hsim3].
    - eapply equiv_trans; [exact Heq1|]. eapply equiv_trans; [exact Heq2|exact Heq3].
    - rewrite Rz. cbn [tlb_map TLB.asid_roots]. rewrite R3B. change (TLB.asid_roots c3) with R. rewrite R3, R2B. reflexivity.
    - rewrite Ez. cbn [tlb_map TLB.ets]. rewrite E3B, E3, E2B. reflexivity.
    - apply wf_tlb_map. exact (fill_from_roots_wf _ _ _ _ _ _ Hwf3 Hc3B). }
  (* the refill from [p] *)
  destruct (collapse_above_rel (λ R', (filter (λ '(_, time), time = p) R').*1 = B)
    (λ a b, a = c3 ∧ b = d3) p ltac:(lia) (λ R' t Ht HR', okr_filter B R' t Ht HR')
    ltac:(intros R' a b a' HR' [-> ->] Hrun';
          exact (collapse_base_ahead B R' c3 d3 a' c3B HR' Hc3B Hsim3' Hrun'))
    l R c3 d3 c' HRB (le_n _) (conj eq_refl eq_refl) H4) as [d' [Hd' Hsim']].
  exists d'. split; [|exact Hsim'].
  unfold TLB.fill_asid_root.
  apply (bind_intro _ _ d (rolled q d) d' () ()); [apply roll_back_run|].
  apply (bind_intro _ _ _ (set TLB.asid_roots g (rolled q d)) d' () ()); [reflexivity|].
  apply (bind_intro _ _ _ d3 d' () ()); [exact Hd3|].
  change (TLB.fill_from tid imem mem' (TLB.asid_roots d3) (S q) d3 = Ok (d', ())).
  assert (Hrd : TLB.asid_roots d3 = map_roots h R).
  { pose proof (fill_from_roots_config _ _ _ _ _ _ Hd3) as [Rd _]. rewrite Rd, R3.
    assert (Hc2r : TLB.asid_roots c2 = (root, q) :: TLB.asid_roots c) by (unfold c2; destruct c; reflexivity).
    assert (Hd2r : TLB.asid_roots (set TLB.asid_roots g (rolled q d)) = (root, q) :: TLB.asid_roots d)
      by (destruct d; reflexivity).
    rewrite Hc2r, Hd2r. cbn [map_roots map fst snd]. rewrite (collapse_ne p q) by lia.
    destruct Hsim as [[_ [Hr _]] _]. rewrite <- Hr. reflexivity. }
  rewrite Hrd. exact Hd'.
Qed.

(** Case (a) for a context synchronization at [p - 1], when no root has time
    [p]: J makes the rollbacks to [p - 1] and [p] agree. *)
Lemma set_fill_collapse_q (rs : list (bv 16 * bv 64 * bool * nat)) :
  Forall (λ x, x.2 = q) rs →
  natural h (msetv TLB.asid_roots rs;; TLB.fill_from tid imem mem' rs p)
    (msetv TLB.asid_roots rs;; TLB.fill_from tid imem mem' rs p).
Proof using Hrc.
  intro Hq. assert (Hmap : map_roots h rs = rs).
  { induction Hq as [|[x t] rs Ht _ IH]; [reflexivity|]. cbn in Ht |- *. subst t.
    unfold map_roots in IH. rewrite IH, collapse_ne by lia. reflexivity. }
  apply natural_bind; [unfold msetv; apply natural_mset_roots; intro; exact Hmap|intros _].
  pose proof (fill_from_collapse tid imem l r tlbi rc k Hrc rs p p (or_introl eq_refl)) as H.
  rewrite Hmap in H. apply H. intros x Hx Hxp.
  apply list.Forall_forall with (x := x) in Hq; [|exact Hx]. lia.
Qed.

Lemma set_fill_sim rs : VMCacheSim.sim_action (msetv TLB.asid_roots rs;; TLB.fill_from tid imem mem' rs p).
Proof.
  apply VMCacheSim.sim_bind; [unfold msetv; apply mset_roots_sim|intros _].
  unfold TLB.fill_from. apply fill_from_btw_sim.
Qed.

Theorem fill_cse_collapse_q ttbr0 ttbr1 c d c' :
  J c → proots c = [] → VMCacheSim.cache_sim (tlb_map h c) d →
  TLB.fill_cse tid imem mem' q ttbr0 ttbr1 c = Ok (c', ()) →
  ∃ d', TLB.fill_cse tid imem mem' q ttbr0 ttbr1 d = Ok (d', ()) ∧
    VMCacheSim.cache_sim (tlb_map h c') d'.
Proof using Hrc.
  intros [cJ [HJ HJeq]] Hnil Hsim Hrun. rewrite Hnil in HJ.
  rewrite fill_from_roots_nil in HJ. injection HJ as <-.
  pose proof (proj1 (wf_tlb_map h c) (proj1 (proj2 Hsim))) as Hwf.
  destruct (wsq_of_natural h _ _ roll_back_collapse_p (roll_back_sim q) c d (rolled p c) ()
    Hsim (roll_back_run p c)) as [d1 [Hd1 Hsim1]].
  rewrite roll_back_run in Hd1. injection Hd1 as <-.
  assert (Hsim1' : VMCacheSim.cache_sim (tlb_map h (rolled q c)) (rolled q d)).
  { apply (cache_sim_equiv_l _ (tlb_map h (rolled p c))); [| | | |exact Hsim1].
    - apply equiv_tlb_map, equiv_sym, HJeq.
    - reflexivity.
    - reflexivity.
    - apply wf_tlb_map, wf_rolled, Hwf. }
  unfold TLB.fill_cse in Hrun |- *.
  apply bind_unit_run in Hrun as [c1 [H1 Hrun]]. rewrite roll_back_run in H1. injection H1 as <-.
  cbv zeta in Hrun |- *.
  destruct ttbr1 as [ttbr1|].
  - destruct (wsq_of_natural h _ _ (set_fill_collapse_q [(bv_extract 48 16 ttbr0, ttbr0, false, q);
      (bv_extract 48 16 ttbr0, ttbr1, true, q)] ltac:(repeat constructor)) (set_fill_sim _)
      _ _ c' () Hsim1' Hrun) as [d' [Hd' Hsim']].
    exists d'. split; [|exact Hsim'].
    apply (bind_intro _ _ d (rolled q d) d' () ()); [apply roll_back_run|exact Hd'].
  - destruct (wsq_of_natural h _ _ (set_fill_collapse_q [(bv_extract 48 16 ttbr0, ttbr0, false, q)]
      ltac:(repeat constructor)) (set_fill_sim _)
      _ _ c' () Hsim1' Hrun) as [d' [Hd' Hsim']].
    exists d'. split; [|exact Hsim'].
    apply (bind_intro _ _ d (rolled q d) d' () ()); [apply roll_back_run|exact Hd'].
Qed.

End Rolled.
End RollbackCollapse.

(** ** Preservation of J *)

Section JPreservation.
Import VMCacheRefill.
Local Notation rolled := VMCacheExchange.rolled.

Lemma frame_rolled_equiv t a b : VMCacheIndex.frame t a b →
  TLB.pte_present a = TLB.pte_present b → equiv (rolled t a) (rolled t b).
Proof.
  intros [Hl _] Hp. split; [exact Hp|]. intro fe. unfold rolled.
  rewrite !VMCacheEvents.history_map by reflexivity. exact (Hl fe).
Qed.

Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Local Notation p := (S (length r)).
Local Notation q := (length r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

(** J survives a promise appended at the end of the longer history. *)
Theorem J_fill_promise ev c c' :
  J imem l r tlbi rc k c → TLB.fill_promise tid imem (ev :: mem') ev c = Ok (c', ()) →
  J imem (ev :: l) r tlbi rc k c'.
Proof.
  intros [cJ [HJ HJeq]] Hrun.
  assert (Hlen : p ≤ length mem') by (rewrite length_app; cbn; lia).
  pose proof (VMCacheIndex.fill_promise_frame_at tid imem mem' ev q c c' ltac:(lia) Hrun) as Fq.
  pose proof (VMCacheIndex.fill_promise_frame_at tid imem mem' ev p c c' Hlen Hrun) as Fp.
  pose proof (VMCacheConfig.fill_promise tid imem (ev :: mem') ev c c' () Hrun) as Hconf.
  unfold VMCacheConfig.config in Hconf.
  assert (Hpte : TLB.pte_present c = TLB.pte_present c') by congruence.
  pose proof (VMCacheRoots.fill_promise tid imem (ev :: mem') ev c c' () Hrun) as Hroots.
  unfold VMCacheRoots.config in Hroots.
  assert (HB : proots r c' = proots r c) by (unfold proots; rewrite Hroots; reflexivity).
  destruct (fill_from_roots_equiv imem mem' p (proots r c) (rolled q c) (rolled q c') cJ ()
    (frame_rolled_equiv _ _ _ Fq Hpte) HJ) as [cJ' [HJ' Heq']].
  exists cJ'. split.
  - rewrite HB. change ((ev :: l) ++ Ev.Tlbi tlbi rc k :: r) with (ev :: mem').
    rewrite VMCacheHistory.fill_from_roots_future by exact Hlen. exact HJ'.
  - eapply equiv_trans; [apply equiv_sym, (frame_rolled_equiv _ _ _ Fp Hpte)|].
    eapply equiv_trans; [exact HJeq|exact Heq'].
Qed.
End JPreservation.


(** ** Remove form of case (a) *)

(** [wsq] restricted to caches satisfying [P]. *)
Definition wsq_on {A} (P : TLB.t → Prop) (f : nat → nat) (ra rb : action A) : Prop :=
  ∀ c d c' x, P c → VMCacheSim.cache_sim (tlb_map f c) d → ra c = Ok (c', x) →
    ∃ d', rb d = Ok (d', x) ∧ VMCacheSim.cache_sim (tlb_map f c') d'.

Lemma wsq_on_of {A} P f (ra rb : action A) : wsq f ra rb → wsq_on P f ra rb.
Proof. intros H c d c' x _. apply H. Qed.

Theorem wsq_on_remove_collapse {A} p (Hp : 0 < p) P (long long' short : action A) :
  natural (shift p) short long' → wsq_on P (collapse p) long long' →
  wsq_on P (unshift p) long short.
Proof.
  intros Hins Hcol c d c' x HP Hsim Hrun.
  pose proof (cache_sim_tlb_map (shift p) _ _ Hsim) as Hsim'.
  rewrite (tlb_map_shift_unshift p Hp) in Hsim'.
  destruct (Hcol c _ c' x HP Hsim' Hrun) as [d' [Hd' Hsimd]].
  rewrite Hins in Hd'.
  destruct (short d) as [[d1 y]|err] eqn:Hs; cbn in Hd'; [|discriminate].
  injection Hd' as <- <-. exists d1. split; [reflexivity|].
  pose proof (cache_sim_tlb_map (unshift p) _ _ Hsimd) as H.
  rewrite (tlb_map_unshift_collapse p) , (tlb_map_unshift_shift p) in H. exact H.
Qed.

Section RemoveQ.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation q := (length r).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

Theorem fill_asid_root_remove_q root :
  wsq_on (J imem l r tlbi rc k) (unshift p) (TLB.fill_asid_root tid imem mem' root q)
    (TLB.fill_asid_root tid imem mem root q).
Proof using Hrc.
  apply (wsq_on_remove_collapse p (Hp r) _ _ (TLB.fill_asid_root tid imem mem' root q)).
  - pose proof (fill_asid_root_shifted tid imem l r tlbi rc k Hrc root q) as H.
    rewrite shift_lt in H by lia. apply H. rewrite length_app. lia.
  - intros c d c' [] HJ Hsim Hrun.
    exact (fill_asid_root_collapse_q tid imem l r tlbi rc k Hrc root c d c' HJ Hsim Hrun).
Qed.

Theorem fill_cse_remove_q ttbr0 ttbr1 :
  wsq_on (λ c, J imem l r tlbi rc k c ∧ proots r c = []) (unshift p)
    (TLB.fill_cse tid imem mem' q ttbr0 ttbr1) (TLB.fill_cse tid imem mem q ttbr0 ttbr1).
Proof using Hrc.
  apply (wsq_on_remove_collapse p (Hp r) _ _ (TLB.fill_cse tid imem mem' q ttbr0 ttbr1)).
  - pose proof (fill_cse_shifted tid imem l r tlbi rc k Hrc q ttbr0 ttbr1) as H.
    rewrite shift_lt in H by lia. exact H.
  - intros c d c' [] [HJ Hnil] Hsim Hrun.
    exact (fill_cse_collapse_q tid imem l r tlbi rc k Hrc ttbr0 ttbr1 c d c' HJ Hnil Hsim Hrun).
Qed.
End RemoveQ.

(** ** Preservation of J through context changes *)

Section JTools.
Import VMCacheRefill.
Local Notation rolled := VMCacheExchange.rolled.

(** Equal histories up to [t]. *)
Definition hsame (t : nat) (a b : TLB.t) : Prop :=
  ∀ fe, VMCacheRollback.past t (history a fe) = VMCacheRollback.past t (history b fe).

Lemma hsame_refl t a : hsame t a a.
Proof. intro fe. reflexivity. Qed.
Lemma hsame_sym t a b : hsame t a b → hsame t b a.
Proof. intros H fe. symmetry. apply H. Qed.
Lemma hsame_trans t a b c : hsame t a b → hsame t b c → hsame t a c.
Proof. intros H1 H2 fe. rewrite H1. apply H2. Qed.
Lemma hsame_mono t t' a b : t' ≤ t → hsame t a b → hsame t' a b.
Proof.
  intros Hle H fe. rewrite <- (VMCacheExchange.past_past t' t (history a fe) Hle),
    <- (VMCacheExchange.past_past t' t (history b fe) Hle), H. reflexivity.
Qed.
Lemma frame_hsame t a b : VMCacheIndex.frame t a b → hsame t a b.
Proof. intros [Hl _] fe. exact (Hl fe). Qed.
Lemma hsame_rolled_equiv t a b : hsame t a b → TLB.pte_present a = TLB.pte_present b →
  equiv (rolled t a) (rolled t b).
Proof.
  intros Hl Hp. split; [exact Hp|]. intro fe. unfold rolled.
  rewrite !VMCacheEvents.history_map by reflexivity. exact (Hl fe).
Qed.
Lemma hsame_rolled t t' c : t ≤ t' → hsame t c (rolled t' c).
Proof.
  intros Hle fe. unfold rolled. rewrite VMCacheEvents.history_map by reflexivity.
  symmetry. apply VMCacheExchange.past_past, Hle.
Qed.
Lemma good_rolled_equiv t c : VMCacheOrder.good t c → equiv (rolled t c) c.
Proof.
  intro Hg. split; [reflexivity|]. intro fe. unfold rolled.
  rewrite VMCacheEvents.history_map by reflexivity.
  apply VMCacheOrder.filter_bounded, (proj2 (Hg fe)).
Qed.

Lemma preserves_fill_from_btw bound tid imem fullmem : ∀ tmax roots tmin mem, bound < tmin →
  VMCacheIndex.preserves bound (TLB.fill_from_btw tid imem fullmem roots tmin tmax mem).
Proof.
  induction tmax as [|tmax IH]; intros roots tmin mem Hb; cbn [TLB.fill_from_btw];
    destruct (decide (_ < _)); try apply VMCacheIndex.preserves_ret.
  - apply VMCacheIndex.preserves_throw.
  - destruct mem as [|ev mem]; [apply VMCacheIndex.preserves_throw|].
    apply VMCacheIndex.preserves_bind; [apply IH, Hb|intros []].
    apply VMCacheIndex.preserves_bind;
      [|intros []; apply VMCacheIndex.preserves_fill_from_roots; lia].
    intros old new [] H. eapply VMCacheIndex.fill_event_frame; [|exact H]. lia.
Qed.

Lemma fill_asid_root_inv tid imem m root t c c' :
  TLB.fill_asid_root tid imem m root t c = Ok (c', ()) →
  ∃ c3, TLB.fill_from_roots imem m t [root]
      (set TLB.asid_roots ((root, t) ::.) (rolled t c)) = Ok (c3, ()) ∧
    TLB.fill_from tid imem m (TLB.asid_roots c3) (S t) c3 = Ok (c', ()).
Proof.
  intro Hrun. unfold TLB.fill_asid_root in Hrun.
  apply bind_unit_run in Hrun as [c1 [H1 Hrun]]. rewrite roll_back_run in H1. injection H1 as <-.
  apply bind_unit_run in Hrun as [c2 [H2 Hrun]].
  change (@Ok string _ (set TLB.asid_roots ((root, t) ::.) (rolled t c), ()) = Ok (c2, ())) in H2.
  injection H2 as <-.
  apply bind_unit_run in Hrun as [c3 [H3 H4]]. exists c3. split; [exact H3|exact H4].
Qed.

Lemma fill_cse_inv tid imem m t ttbr0 ttbr1 c c' :
  TLB.fill_cse tid imem m t ttbr0 ttbr1 c = Ok (c', ()) →
  ∃ rs, Forall (λ x, x.2 = t) rs ∧
    TLB.fill_from tid imem m rs (S t) (setv TLB.asid_roots rs (rolled t c)) = Ok (c', ()).
Proof.
  intro Hrun. unfold TLB.fill_cse in Hrun.
  apply bind_unit_run in Hrun as [c1 [H1 Hrun]]. rewrite roll_back_run in H1. injection H1 as <-.
  cbv zeta in Hrun. destruct ttbr1 as [ttbr1|].
  - eexists. split; [|exact Hrun]. repeat constructor.
  - eexists. split; [|exact Hrun]. repeat constructor.
Qed.
End JTools.

Section JPreservation2.
Import VMCacheRefill.
Local Notation rolled := VMCacheExchange.rolled.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation q := (length r).
Local Notation e := (Ev.Tlbi tlbi rc k).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

(** J only depends on the histories up to [p] and the roots of time [p]. *)
Lemma J_transport c c' : J imem l r tlbi rc k c → hsame p c c' →
  TLB.pte_present c = TLB.pte_present c' → proots r c' = proots r c → J imem l r tlbi rc k c'.
Proof.
  clear Hrc. intros [cJ [HJ HJeq]] Hs Hpte HB.
  destruct (fill_from_roots_equiv imem mem' p (proots r c) (rolled q c) (rolled q c') cJ ()
    (hsame_rolled_equiv _ _ _ (hsame_mono p q c c' ltac:(lia) Hs) Hpte) HJ) as [cJ' [HJ' Heq']].
  exists cJ'. split; [rewrite HB; exact HJ'|].
  eapply equiv_trans; [apply equiv_sym, (hsame_rolled_equiv _ _ _ Hs Hpte)|].
  eapply equiv_trans; [exact HJeq|exact Heq'].
Qed.

(** Refill steps above [p] keep the histories up to [p]. *)
Lemma fill_from_btw_split l' : ∀ R tmin c c', tmin ≤ p →
  TLB.fill_from_btw tid imem mem' R tmin (length (l' ++ e :: r)) (l' ++ e :: r) c = Ok (c', ()) →
  ∃ R' c'', (filter (λ '(_, time), time = p) R').*1 = (filter (λ '(_, time), time = p) R).*1 ∧
    TLB.fill_from_btw tid imem mem' R' tmin p (e :: r) c = Ok (c'', ()) ∧
    hsame p c'' c' ∧ TLB.pte_present c'' = TLB.pte_present c'.
Proof.
  clear Hrc. induction l' as [|x l' IH]; intros R tmin c c' Hmin Hrun.
  - exists R, c'. split; [reflexivity|]. split; [exact Hrun|]. split; [apply hsame_refl|reflexivity].
  - cbn [app length] in Hrun.
    assert (Hge : p ≤ length (l' ++ e :: r)) by (rewrite length_app; cbn; lia).
    rewrite (fill_from_btw_unfold _ _ _ _ _ _ (length (l' ++ e :: r))) in Hrun by lia.
    apply bind_unit_run in Hrun as [c1 [H1 Hrun]]. apply bind_unit_run in Hrun as [c2 [H2 H3]].
    destruct (IH _ tmin c c1 Hmin H1) as [R' [c'' [HR [Hb [Hs Hpte]]]]].
    exists R', c''. split; [rewrite HR; apply okr_filter; [lia|reflexivity]|]. split; [exact Hb|].
    assert (F2 : VMCacheIndex.frame p c1 c2)
      by (eapply VMCacheIndex.fill_event_frame; [|exact H2]; lia).
    assert (F3 : VMCacheIndex.frame p c2 c')
      by (eapply VMCacheIndex.preserves_fill_from_roots; [|exact H3]; lia).
    pose proof (VMCacheConfig.fill_event tid imem mem' _ _ _ c1 c2 () H2) as C2.
    pose proof (VMCacheConfig.fill_from_roots imem mem' _ _ c2 c' () H3) as C3.
    unfold VMCacheConfig.config in C2, C3.
    split.
    + eapply hsame_trans; [exact Hs|]. eapply hsame_trans; apply frame_hsame; eassumption.
    + rewrite Hpte. congruence.
Qed.

(** A refill from at most [p] of a cache bounded below its start
    establishes J. *)
Lemma J_refill R tmin b c c' : tmin ≤ p → b < tmin → b ≤ q → VMCacheOrder.good b c →
  TLB.asid_roots c = R →
  TLB.fill_from tid imem mem' R tmin c = Ok (c', ()) → J imem l r tlbi rc k c'.
Proof using Hrc.
  intros Hmin Hb Hbq Hg HR Hrun. unfold TLB.fill_from in Hrun.
  destruct (fill_from_btw_split l R tmin c c' Hmin Hrun) as [R' [c'' [HR' [Hb' [Hs Hpte]]]]].
  rewrite (fill_from_btw_unfold _ _ _ _ _ _ q) in Hb' by lia.
  apply bind_unit_run in Hb' as [xq [Hq Hb']]. apply bind_unit_run in Hb' as [xq' [Hev Hp]].
  unfold TLB.fill_event in Hev. rewrite decide_False in Hev by exact Hrc.
  change (@Ok string _ (xq, ()) = Ok (xq', ())) in Hev. injection Hev as <-.
  pose proof (VMCacheOrder.good_fill_from_btw _ _ _ _ _ _ _ _ _ _ Hb Hg Hq) as Gq.
  replace (b `max` q) with q in Gq by lia.
  assert (Gp : VMCacheOrder.good p c'').
  { eapply VMCacheOrder.good_fill_from_roots; [|exact Hp].
    eapply VMCacheOrder.good_mono; [|exact Gq]. lia. }
  assert (Hroots : TLB.asid_roots c' = R).
  { pose proof (VMCacheRoots.fill_from_btw tid imem mem' R tmin (length mem') mem' c c' () Hrun) as H.
    unfold VMCacheRoots.config in H. congruence. }
  assert (HB : (filter (λ '(_, time), time = p) R').*1 = proots r c').
  { unfold proots. rewrite Hroots. exact HR'. }
  rewrite HB in Hp.
  pose proof (VMCacheIndex.preserves_fill_from_roots q imem mem' p _ ltac:(lia) xq c'' () Hp) as Fq.
  pose proof (VMCacheConfig.fill_from_roots imem mem' p _ xq c'' () Hp) as Cq.
  unfold VMCacheConfig.config in Cq.
  assert (E1 : equiv xq (rolled q c')).
  { eapply equiv_trans; [apply equiv_sym, good_rolled_equiv, Gq|].
    apply hsame_rolled_equiv; [|congruence].
    eapply hsame_trans; [apply frame_hsame, Fq|]. apply (hsame_mono p); [lia|exact Hs]. }
  destruct (fill_from_roots_equiv imem mem' p (proots r c') xq (rolled q c') c'' () E1 Hp)
    as [w [Hw Ew]].
  exists w. split; [exact Hw|].
  eapply equiv_trans; [|exact Ew].
  eapply equiv_trans; [apply hsame_rolled_equiv; [apply hsame_sym, Hs|symmetry; exact Hpte]|].
  apply good_rolled_equiv, Gp.
Qed.

(** Root fills and context synchronizations at or below [p - 1] establish J. *)
Theorem J_fill_asid_root_below root t b c c' : t ≤ q → VMCacheOrder.good b c →
  TLB.fill_asid_root tid imem mem' root t c = Ok (c', ()) → J imem l r tlbi rc k c'.
Proof using Hrc.
  intros Ht Hg Hrun. destruct (fill_asid_root_inv _ _ _ _ _ _ _ Hrun) as [c3 [H3 H4]].
  assert (G3 : VMCacheOrder.good t c3).
  { eapply VMCacheOrder.good_fill_from_roots; [|exact H3]. exact (VMCacheOrder.good_rolled b t c Hg). }
  exact (J_refill _ (S t) t c3 c' ltac:(lia) ltac:(lia) Ht G3 eq_refl H4).
Qed.

Theorem J_fill_cse_below ttbr0 ttbr1 t b c c' : t ≤ q → VMCacheOrder.good b c →
  TLB.fill_cse tid imem mem' t ttbr0 ttbr1 c = Ok (c', ()) → J imem l r tlbi rc k c'.
Proof using Hrc.
  intros Ht Hg Hrun. destruct (fill_cse_inv _ _ _ _ _ _ _ _ Hrun) as [rs [_ H]].
  exact (J_refill rs (S t) t (setv TLB.asid_roots rs (rolled t c)) c' ltac:(lia) ltac:(lia) Ht
    (VMCacheOrder.good_rolled b t c Hg) eq_refl H).
Qed.

(** Root fills above [p] keep J. *)
Theorem J_fill_asid_root_above root t c c' : p < t → J imem l r tlbi rc k c →
  TLB.fill_asid_root tid imem mem' root t c = Ok (c', ()) → J imem l r tlbi rc k c'.
Proof.
  clear Hrc. intros Ht HJ Hrun.
  pose proof (VMCacheExchange.fill_asid_root_roots _ _ _ _ _ _ _ Hrun) as Hroots.
  pose proof (VMCacheConfig.fill_asid_root _ _ _ _ _ _ _ () Hrun) as Hconf.
  unfold VMCacheConfig.config in Hconf.
  destruct (fill_asid_root_inv _ _ _ _ _ _ _ Hrun) as [c3 [H3 H4]].
  apply (J_transport c); [exact HJ| |congruence|].
  - eapply hsame_trans; [apply (hsame_rolled p t c); lia|].
    change (hsame p (set TLB.asid_roots (cons (root, t)) (rolled t c)) c').
    eapply hsame_trans.
    + apply frame_hsame. eapply VMCacheIndex.preserves_fill_from_roots; [|exact H3]. lia.
    + apply frame_hsame. eapply preserves_fill_from_btw; [|exact H4]. lia.
  - unfold proots. rewrite Hroots, filter_cons, decide_False by (cbn; lia). reflexivity.
Qed.

(** A root fill at [p] adds its root to the roots of time [p]. *)
Theorem J_fill_asid_root_p root b c c' : J imem l r tlbi rc k c → VMCacheOrder.good b c →
  TLB.fill_asid_root tid imem mem' root p c = Ok (c', ()) → J imem l r tlbi rc k c'.
Proof.
  clear Hrc. intros [cJ [HJ HJeq]] Hg Hrun.
  pose proof (VMCacheExchange.fill_asid_root_roots _ _ _ _ _ _ _ Hrun) as Hroots.
  pose proof (VMCacheConfig.fill_asid_root _ _ _ _ _ _ _ () Hrun) as Hconf.
  unfold VMCacheConfig.config in Hconf.
  destruct (fill_asid_root_inv _ _ _ _ _ _ _ Hrun) as [c3 [H3 H4]].
  set (c2 := set TLB.asid_roots ((root, p) ::.) (rolled p c)) in *.
  set (B := proots r c) in *.
  assert (HB : proots r c' = root :: B).
  { unfold B, proots. rewrite Hroots, filter_cons, decide_True by reflexivity. reflexivity. }
  pose proof (VMCacheConfig.fill_from_roots _ _ _ _ _ _ () H3) as C3.
  unfold VMCacheConfig.config in C3.
  assert (F3 : VMCacheIndex.frame q c2 c3)
    by (eapply VMCacheIndex.preserves_fill_from_roots; [|exact H3]; lia).
  assert (F4 : VMCacheIndex.frame p c3 c')
    by (eapply preserves_fill_from_btw; [|exact H4]; lia).
  assert (Hpte2 : TLB.pte_present c2 = TLB.pte_present c) by reflexivity.
  assert (Hpte3 : TLB.pte_present c3 = TLB.pte_present c') by congruence.
  assert (Hq : hsame q c c').
  { eapply hsame_trans; [apply (hsame_rolled q p c); lia|].
    eapply hsame_trans; [apply frame_hsame, F3|]. apply (hsame_mono p); [lia|apply frame_hsame, F4]. }
  assert (G3 : VMCacheOrder.good p c3).
  { eapply VMCacheOrder.good_fill_from_roots; [|exact H3]. exact (VMCacheOrder.good_rolled b p c Hg). }
  destruct (fill_from_roots_equiv imem mem' p [root] c2 cJ c3 () HJeq H3) as [y [Hy Ey]].
  destruct (proj2 (fill_from_roots_app imem mem' p B [root]) _ _ ()
    (bind_intro _ _ _ _ _ () () HJ Hy)) as [z [Hz Ez]].
  destruct (fill_from_roots_permutation imem mem' p (B ++ [root]) (root :: B)
    (Permutation_app_comm B [root]) _ _ () Hz) as [w [Hw Ew]].
  destruct (fill_from_roots_equiv imem mem' p (root :: B) (rolled q c) (rolled q c') w ()
    (hsame_rolled_equiv _ _ _ Hq ltac:(congruence)) Hw) as [w' [Hw' Ew']].
  exists w'. rewrite HB. split; [exact Hw'|].
  eapply equiv_trans;
    [apply hsame_rolled_equiv; [apply hsame_sym, frame_hsame, F4|symmetry; exact Hpte3]|].
  eapply equiv_trans; [apply good_rolled_equiv, G3|].
  eapply equiv_trans; [exact Ey|]. eapply equiv_trans; [exact Ez|].
  eapply equiv_trans; [exact Ew|exact Ew'].
Qed.
End JPreservation2.


(** * Totality of cache maintenance (copied from VMFillTotal of
    PromiseFirstSailVMInstructionReplay)

    On a valid cache over a history whose writes stay within a page, every
    context change succeeds. *)
Module SwapFillTotal.
Import VMPromising.
#[local] Existing Instance TLB.Decision_affects.
Local Notation action A := (stateT TLB.t (result string) A).
Local Notation valid := VMCacheIndexed.valid.

Definition total {A} (Q : A → Prop) (run : action A) :=
  ∀ c, valid c → ∃ c' a, run c = Ok (c', a) ∧ Q a.

Lemma total_ret {A} (Q : A → Prop) a : Q a → total Q (mret a).
Proof. intros Hq c Hc. exists c, a. split; [reflexivity|exact Hq]. Qed.
Lemma total_bind {A B} (Q : A → Prop) (R : B → Prop) (m : action A) (k : A → action B) :
  total Q m → VMCacheIndexed.preserves m → (∀ a, Q a → total R (k a)) → total R (m ≫= k).
Proof.
  intros Hm Hp Hk c Hc. destruct (Hm c Hc) as [c1 [a [Hrun Hq]]].
  destruct (Hk a Hq c1 (Hp c c1 a Hc Hrun)) as [c2 [b [Hrun2 Hr]]].
  exists c2, b. split; [|exact Hr].
  unfold mbind, st_bind, result_bind. rewrite Hrun. exact Hrun2.
Qed.
Lemma total_fmap {A B} (Q : A → Prop) (R : B → Prop) (f : A → B) (m : action A) :
  total Q m → (∀ a, Q a → R (f a)) → total R (f <$> m).
Proof.
  intros Hm Hf c Hc. destruct (Hm c Hc) as [c1 [a [Hrun Hq]]].
  exists c1, (f a). split; [|apply Hf, Hq].
  unfold fmap, st_fmap, result_fmap. rewrite Hrun. reflexivity.
Qed.
Lemma total_get {A} (proj : TLB.t → A) : total (λ _, True) (mget proj).
Proof. intros c Hc. exists c, (proj c). split; [reflexivity|exact I]. Qed.
Lemma total_weaken {A} (Q R : A → Prop) (m : action A) :
  total Q m → (∀ a, Q a → R a) → total R m.
Proof. intros Hm Hw c Hc. destruct (Hm c Hc) as [c1 [a [H Hq]]]. eauto. Qed.
Lemma total_mapM {A B} (Q : B → Prop) (f : A → action B) xs :
  (∀ x, x ∈ xs → total Q (f x)) → (∀ x, VMCacheIndexed.preserves (f x)) →
  total (Forall Q) (mapM f xs).
Proof.
  intros Hf Hp. induction xs as [|x xs IH]; cbn [mapM].
  - apply total_ret. constructor.
  - eapply total_bind; [apply Hf; set_solver|apply Hp|]. intros b Hb.
    eapply total_bind; [apply IH; intros; apply Hf; set_solver|apply VMCacheIndexed.preserves_mapM, Hp|].
    intros bs Hbs. apply total_ret. constructor; assumption.
Qed.
Lemma total_set {A} (proj : TLB.t → A) `{Setter _ _ proj} (f : A → A) :
  total (λ _, True) (mset proj f).
Proof. intros c Hc. exists (set proj f c), (). split; [reflexivity|exact I]. Qed.

Lemma total_fill_entry time fe : total (λ _, True) (TLB.fill_entry time fe).
Proof.
  intros c Hc. destruct (VMCacheRefill.fill_entry_total time fe c) as [c' [l H]].
  exists c', l. split; [exact H|exact I].
Qed.

(** A table entry and its level lower bound. *)
Definition deep (k : nat) (fe : TLB.FE.t) :=
  TLB.FE.is_table fe ∧ k ≤ fin_to_nat (TLB.FE.lvl fe).

Lemma table_lvl fe : TLB.FE.is_table fe → fin_to_nat (TLB.FE.lvl fe) ≤ 2.
Proof.
  intro Ht. change (is_table (TLB.FE.lvl fe) (TLB.FE.pte fe)) in Ht. destruct Ht as [Hne _].
  revert Hne. generalize (TLB.FE.lvl fe). intro l. unfold leaf_lvl.
  repeat (inv_fin l; [intros; cbn; lia|intro l]). inv_fin l; [|intro l; inv_fin l].
  intros Hne. exfalso. apply Hne. reflexivity.
Qed.
Lemma child_lvl_table fe : TLB.FE.is_table fe →
  ∃ clvl, child_lvl (TLB.FE.lvl fe) = Some clvl ∧ fin_to_nat clvl = S (fin_to_nat (TLB.FE.lvl fe)).
Proof.
  intro Ht. pose proof (table_lvl fe Ht) as Hle. revert Hle.
  generalize (TLB.FE.lvl fe). intro l.
  inv_fin l; [|intro l; inv_fin l; [|intro l; inv_fin l; [|intro l; inv_fin l; [|intro l; inv_fin l]]]].
  all: intros; first [eexists; split; reflexivity | cbn in *; lia].
Qed.

Lemma total_guard (err : string) (P : Prop) `{Decision P} : P → total (λ _, True) (guard_or err P).
Proof.
  intro Hp. unfold guard_or. destruct (decide P) as [p|]; [|contradiction].
  apply (total_ret (λ _, True)). exact I.
Qed.

Lemma append_ok fe idx pte : TLB.FE.is_table fe → ∃ child, TLB.FE.append fe idx pte = Ok child.
Proof.
  intro Ht. destruct (child_lvl_table fe Ht) as [clvl [Hc _]].
  unfold TLB.FE.append. destruct (inspect (child_lvl (TLB.FE.lvl fe))) as [[l|] Hl];
    [eexists; reflexivity|congruence].
Qed.

Lemma total_fill_from_entry imem mem time fe k :
  deep k fe → total (Forall (deep (S k))) (TLB.fill_from_entry imem mem time fe).
Proof.
  intros [Htab Hk]. unfold TLB.fill_from_entry.
  destruct (child_lvl_table fe Htab) as [clvl [Hc Hlvl]].
  eapply total_bind; [|apply VMCacheIndexed.preserves_guard|].
  { apply total_guard, Htab. }
  intros _ _. eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|].
  intros indexes _.
  eapply total_bind; [|apply VMCacheIndexed.preserves_othrow|].
  { rewrite Hc. apply (total_ret (λ c, c = clvl)). reflexivity. }
  intros ? ->.
  eapply total_fmap; [apply (total_mapM (Forall (deep (S k))))|].
  3: { intros lists Hlists. apply Forall_concat. exact Hlists. }
  2: { intro idx. VMCacheIndexed.solve_index. }
  intros idx _. cbv beta.
  destruct (Memory.read_word _ imem mem time) as [memval|err];
    [|apply total_ret; constructor].
  destruct (decide (is_tlb_fillable clvl memval)); [|apply total_ret; constructor].
  destruct (append_ok fe idx memval Htab) as [child Happ].
  eapply total_bind; [|apply VMCacheIndexed.preserves_lift|].
  { rewrite Happ. apply (total_ret (λ x, x = child)). reflexivity. }
  intros ? ->.
  eapply total_bind; [apply total_fill_entry|apply VMCacheIndexed.preserves_fill_entry|].
  intros [] _; [|apply total_ret; constructor].
  destruct (decide (is_table clvl memval)) as [Ht|]; [|apply total_ret; constructor].
  apply total_ret. constructor; [|constructor]. split.
  - apply (proj2 (VMCacheTraversal.append_table fe idx memval child clvl Hc Happ)), Ht.
  - rewrite (VMCacheTraversal.append_level fe idx memval child clvl Hc Happ). lia.
Qed.

Lemma total_fill_from_entries_step imem mem time entries k :
  Forall (deep k) entries →
  total (Forall (deep (S k))) (TLB.fill_from_entries_step imem mem time entries).
Proof.
  intro Hall. unfold TLB.fill_from_entries_step.
  eapply total_fmap; [apply (total_mapM (Forall (deep (S k))))|].
  - intros fe Hin. apply total_fill_from_entry. rewrite Forall_forall in Hall. apply Hall. apply list_elem_of_In, Hin.
  - intro fe. apply VMCacheIndexed.fill_from_entry.
  - intros lists Hlists. apply Forall_concat. exact Hlists.
Qed.

Lemma deep_three_nil entries : Forall (deep 3) entries → entries = [].
Proof.
  destruct entries as [|fe entries]; [reflexivity|].
  intro H. inversion H as [|? ? [Ht Hk] _]; subst. pose proof (table_lvl fe Ht). lia.
Qed.

Lemma total_fill_from_entries imem mem time entries :
  Forall (deep 0) entries → total (λ _, True) (TLB.fill_from_entries imem mem time entries).
Proof.
  intro Hall. unfold TLB.fill_from_entries.
  eapply total_bind; [apply (total_fill_from_entries_step _ _ _ _ 0 Hall)|
    apply VMCacheIndexed.fill_from_entries_step|]. intros e1 H1.
  eapply total_bind; [apply (total_fill_from_entries_step _ _ _ _ 1 H1)|
    apply VMCacheIndexed.fill_from_entries_step|]. intros e2 H2.
  eapply total_bind; [apply (total_fill_from_entries_step _ _ _ _ 2 H2)|
    apply VMCacheIndexed.fill_from_entries_step|]. intros e3 H3.
  rewrite (deep_three_nil e3 H3). unfold guard_or'.
  eapply total_bind; [|apply VMCacheIndexed.preserves_guard|].
  { apply total_guard. reflexivity. }
  intros _ _. apply total_ret. exact I.
Qed.

Lemma total_fill_root imem mem time roots :
  total (Forall (deep 0)) (TLB.fill_root imem mem time roots).
Proof.
  unfold TLB.fill_root.
  eapply total_fmap; [apply (total_mapM (Forall (deep 0)))|].
  3: { intros lists Hlists. apply Forall_concat. exact Hlists. }
  2: { intros [[asid ttbr] upper]. VMCacheIndexed.solve_index. }
  intros [[asid ttbr] upper] _. cbv beta.
  eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros indexes _.
  eapply total_fmap; [apply (total_mapM (Forall (deep 0)))|].
  3: { intros lists Hlists. apply Forall_concat. exact Hlists. }
  2: { intro idx. VMCacheIndexed.solve_index. }
  intros idx _. cbv beta.
  destruct (Memory.read_word _ imem mem time) as [memval|err]; [|apply total_ret; constructor].
  destruct (decide (is_table 0%fin memval)) as [Ht|]; [|apply total_ret; constructor].
  eapply total_bind; [apply total_fill_entry|apply VMCacheIndexed.preserves_fill_entry|].
  intros [] _; apply total_ret; [|constructor].
  constructor; [|constructor]. split; [exact Ht|cbn; lia].
Qed.

Lemma total_relevant asids page :
  total (Forall (deep 0)) (TLB.get_relevant_entries asids page).
Proof.
  intros c Hc. eexists c, _. split; [reflexivity|].
  apply Forall_forall. intros fe Hin. apply list_elem_of_In in Hin.
  apply list_elem_of_filter in Hin as [_ Hin].
  destruct (Hc page) as [_ Hmem]. apply Hmem in Hin as [Ht _]. split; [exact Ht|lia].
Qed.

Definition ev_ok (ev : Ev.t) : Prop :=
  match ev with
  | Ev.Msg msg => pa_to_pn (Msg.addr msg) =
      pa_to_pn (addr_addN (Msg.addr msg) (N.pred (Msg.size msg)))
  | _ => True
  end.

Lemma total_fill_from_roots imem mem time roots :
  total (λ _, True) (TLB.fill_from_roots imem mem time roots).
Proof.
  unfold TLB.fill_from_roots.
  eapply total_bind; [apply total_fill_root|apply VMCacheIndexed.fill_root|].
  intros entries Hall. apply total_fill_from_entries, Hall.
Qed.

Lemma total_fill_tlbi imem mem time roots tlbi :
  total (λ _, True) (TLB.fill_tlbi imem mem time roots tlbi).
Proof.
  unfold TLB.fill_tlbi. destruct (TLBI.last tlbi).
  - eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros ? _.
    eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros entries _.
    eapply total_bind.
    + eapply total_fmap; [apply (total_mapM (Forall (deep 0)))|].
      3: { intros lists Hlists. apply Forall_concat. exact Hlists. }
      2: { intro fe. apply VMCacheIndexed.preserves_bind; [apply VMCacheIndexed.preserves_alter|].
           intro. apply VMCacheIndexed.relevant_entries. }
      intros fe _. cbv beta.
      eapply total_bind; [apply total_set|apply VMCacheIndexed.preserves_alter|].
      intros _ _. apply total_relevant.
    + apply VMCacheIndexed.preserves_fmap, VMCacheIndexed.preserves_mapM. intro fe.
      apply VMCacheIndexed.preserves_bind; [apply VMCacheIndexed.preserves_alter|].
      intro. apply VMCacheIndexed.relevant_entries.
    + intros parents Hall. apply total_fill_from_entries, Hall.
  - eapply total_bind; [apply total_set|apply VMCacheIndexed.preserves_map_fe|].
    intros _ _. apply total_fill_from_roots.
Qed.

Lemma total_fill_write imem mem time roots msg :
  ev_ok (Ev.Msg msg) → total (λ _, True) (TLB.fill_write imem mem time roots msg).
Proof.
  intro Hok. unfold TLB.fill_write.
  eapply total_bind; [apply total_guard, Hok|apply VMCacheIndexed.preserves_guard|].
  intros _ _.
  eapply total_bind; [apply total_fill_root|apply VMCacheIndexed.fill_root|]. intros l0 H0.
  eapply total_bind; [apply total_relevant|apply VMCacheIndexed.relevant_entries|]. intros l1 H1.
  apply total_fill_from_entries. apply Forall_app. split; assumption.
Qed.

Theorem total_fill_promise tid imem mem ev :
  ev_ok ev → total (λ _, True) (TLB.fill_promise tid imem mem ev).
Proof.
  intro Hok. unfold TLB.fill_promise.
  eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros roots _.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch].
  - apply total_fill_write, Hok.
  - destruct (decide (tid = recipient)); [apply total_fill_tlbi|apply total_ret; exact I].
Qed.

Lemma fill_promise_ev_ok tid imem mem ev c c' :
  TLB.fill_promise tid imem mem ev c = Ok (c', ()) → ev_ok ev.
Proof.
  destruct ev as [msg|]; [|intros; exact I]. cbn [ev_ok].
  unfold TLB.fill_promise, TLB.fill_event, TLB.fill_write.
  unfold mbind, st_bind, result_bind. cbn -[guard_or].
  unfold guard_or. destruct (decide _) as [Hp|]; [intros; exact Hp|discriminate].
Qed.
(*END*)

Lemma total_fill_event tid imem mem time roots ev :
  ev_ok ev → total (λ _, True) (TLB.fill_event tid imem mem time roots ev).
Proof.
  intro Hok. unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch].
  - apply total_fill_write, Hok.
  - destruct (decide (tid = recipient)); [apply total_fill_tlbi|apply total_ret; exact I].
Qed.

Lemma total_fill_from_btw tid imem fullmem : ∀ mem roots tmin, 0 < tmin → Forall ev_ok mem →
  total (λ _, True) (TLB.fill_from_btw tid imem fullmem roots tmin (length mem) mem).
Proof.
  induction mem as [|ev mem IH]; intros roots tmin Hmin Hok; cbn [length TLB.fill_from_btw];
    destruct (decide (_ < _)); try (apply total_ret; exact I).
  - lia.
  - apply Forall_cons_1 in Hok as [Hev Hok].
    eapply total_bind; [apply IH; assumption|apply VMCacheIndexed.fill_from_btw|]. intros [] _.
    eapply total_bind; [apply total_fill_event, Hev|apply VMCacheIndexed.fill_event|]. intros [] _.
    apply total_fill_from_roots.
Qed.

Theorem total_fill_cse tid imem mem time ttbr0 ttbr1 : Forall ev_ok mem →
  total (λ _, True) (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  intro Hok. unfold TLB.fill_cse, TLB.roll_back.
  eapply total_bind; [apply total_set|apply VMCacheIndexed.preserves_map_fe|]. intros [] _.
  cbv zeta. unfold msetv.
  eapply total_bind; [apply total_set|apply VMCacheIndexed.roots|]. intros [] _.
  unfold TLB.fill_from. apply total_fill_from_btw; [lia|exact Hok].
Qed.

Theorem total_fill_asid_root tid imem mem root time : Forall ev_ok mem →
  total (λ _, True) (TLB.fill_asid_root tid imem mem root time).
Proof.
  intro Hok. unfold TLB.fill_asid_root, TLB.roll_back.
  eapply total_bind; [apply total_set|apply VMCacheIndexed.preserves_map_fe|]. intros [] _.
  eapply total_bind; [apply total_set|apply VMCacheIndexed.roots|]. intros [] _.
  eapply total_bind; [apply total_fill_from_roots|apply VMCacheIndexed.fill_from_roots|].
  intros [] _.
  eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros roots _.
  unfold TLB.fill_from. apply total_fill_from_btw; [lia|exact Hok].
Qed.
End SwapFillTotal.

End VMSwapRemove.
