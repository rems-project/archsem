(******************************************************************************)
(* Cache-history exclusion around a removed foreign TLBI                     *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheOrder
  PromiseFirstSailVMCacheEvents PromiseFirstSailVMCacheLastTLBI PromiseFirstSailVMCacheHistory
  PromiseFirstSailVMCacheExchange PromiseFirstSailVMSwapRemove
  PromiseFirstSailVMSwapRemoveEvents.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

(** Cache histories and root timestamps satisfy [event_allowed p limit].
    The removed TLBI targets another thread, so replaying memory cannot add
    a marker at [p]. CSE may introduce a load at [p] once [limit] reaches it.
    Root writes require their view to avoid [p] until then. The thread-level
    invariant must supply that view condition and connect [limit] to vcse. *)
Module VMSwapRemoveHistory.
Import VMPromising VMCacheRefill VMCacheOrder VMCacheLastTLBI.
#[local] Existing Instance TLB.Decision_affects.

Section Predicate.
Context (P : TLB.Entry.event * nat → Prop).
Definition histories (cache : TLB.t) := ∀ fe, Forall P (history cache fe).
Definition roots_ok (roots : list ((bv 16 * bv 64 * bool) * nat)) :=
  Forall (λ root, P (TLB.Entry.Load, root.2)) roots.

Lemma fill_entry time fe : P (TLB.Entry.Load, time) → keeps histories (TLB.fill_entry time fe).
Proof.
  intros Htime old new loaded Hold Hrun.
  destruct (fill_entry_effect time fe old new loaded Hrun) as [_ [_ Hhist]].
  intro query. rewrite Hhist. destruct (decide (query = fe)); [|apply Hold].
  unfold loaded_history. destruct (active (history old fe)); [apply Hold|].
  constructor; [exact Htime|apply Hold].
Qed.

Lemma set_index f : keeps histories (mset TLB.next_table_cache f).
Proof. apply keeps_set. intros old Hold. exact Hold. Qed.
Lemma set_roots f : keeps histories (mset TLB.asid_roots f).
Proof. apply keeps_set. intros old Hold. exact Hold. Qed.

Lemma map_histories f :
  (∀ fe, f fe [] = []) → (∀ fe events, Forall P events → Forall P (f fe events)) →
  keeps histories (mset TLB.vatlb (TLB.VATLB.map_fe f)).
Proof.
  intros Hnil Hf. apply keeps_set. intros old Hold fe.
  rewrite VMCacheEvents.history_map by apply Hnil. apply Hf, Hold.
Qed.

Lemma alter_histories f fe : f [] = [] → (∀ events, Forall P events → Forall P (f events)) →
  keeps histories (mset TLB.vatlb (alter f fe)).
Proof.
  intros Hnil Hf. apply keeps_set. intros old Hold query.
  rewrite history_alter_any by exact Hnil. destruct (decide (query = fe)); [apply Hf|]; apply Hold.
Qed.

Lemma invalidate_histories time tlbi fe : P (TLB.Entry.Tlbi (TLBI.tid tlbi), time) →
  keeps histories (mset TLB.vatlb (alter (invalidate time tlbi) fe)).
Proof.
  intro Htime. apply alter_histories; [reflexivity|]. intros [|event events] Hhist; [constructor|].
  constructor; assumption.
Qed.

Local Opaque TLB.fill_entry.
Ltac solve_histories :=
  first [apply keeps_ret | apply keeps_get | apply keeps_lift
    | apply keeps_throw | apply keeps_othrow | apply keeps_guard | apply keeps_guard_unit
    | apply fill_entry; assumption | apply set_index
    | apply keeps_bind; [solve_histories|intro; solve_histories]
    | apply keeps_fmap; solve_histories | apply keeps_mapM; intro; solve_histories
    | match goal with |- keeps _ (match ?x with _ => _ end) => destruct x; solve_histories end].

Lemma fill_root imem mem time roots : P (TLB.Entry.Load, time) →
  keeps histories (TLB.fill_root imem mem time roots).
Proof. intro Htime. unfold TLB.fill_root. solve_histories. Qed.
Lemma fill_from_entry imem mem time entry : P (TLB.Entry.Load, time) →
  keeps histories (TLB.fill_from_entry imem mem time entry).
Proof. intro Htime. unfold TLB.fill_from_entry. solve_histories. Qed.
Lemma fill_from_entries imem mem time entries : P (TLB.Entry.Load, time) →
  keeps histories (TLB.fill_from_entries imem mem time entries).
Proof.
  intro Htime. unfold TLB.fill_from_entries, TLB.fill_from_entries_step.
  do 3 (apply keeps_bind; [apply keeps_fmap, keeps_mapM; intro; apply fill_from_entry, Htime|intro]).
  apply keeps_guard_unit.
Qed.
Lemma fill_from_roots imem mem time roots : P (TLB.Entry.Load, time) →
  keeps histories (TLB.fill_from_roots imem mem time roots).
Proof.
  intro Htime. unfold TLB.fill_from_roots.
  apply keeps_bind; [apply fill_root, Htime|intro; apply fill_from_entries, Htime].
Qed.
Lemma relevant_entries asids page : keeps histories (TLB.get_relevant_entries asids page).
Proof. unfold TLB.get_relevant_entries. solve_histories. Qed.

Local Opaque TLB.fill_root TLB.fill_from_entry TLB.fill_from_entries TLB.fill_from_roots TLB.get_relevant_entries.

Lemma fill_write imem mem time roots msg : P (TLB.Entry.Load, time) →
  keeps histories (TLB.fill_write imem mem time roots msg).
Proof.
  intro Htime. unfold TLB.fill_write, guard_or. destruct (decide _); [|apply keeps_throw].
  apply keeps_bind; [apply keeps_ret|intro].
  apply keeps_bind; [apply fill_root, Htime|intro].
  apply keeps_bind; [apply relevant_entries|intro; apply fill_from_entries, Htime].
Qed.

Lemma fill_tlbi imem mem time roots tlbi : P (TLB.Entry.Load, time) →
  P (TLB.Entry.Tlbi (TLBI.tid tlbi), time) → keeps histories (TLB.fill_tlbi imem mem time roots tlbi).
Proof.
  intros Hload Htlbi. destruct (TLBI.last tlbi) eqn:Hlast.
  - intros old new value Hhist Hrun. rewrite last_shape in Hrun by exact Hlast. revert Hhist Hrun.
    apply keeps_bind; [|intro; apply fill_from_entries, Hload].
    apply keeps_fmap, keeps_mapM. intro entry. unfold step.
    apply keeps_bind; [apply invalidate_histories, Htlbi|intro; apply relevant_entries].
  - unfold TLB.fill_tlbi. rewrite Hlast.
    apply keeps_bind; [|intro; apply fill_from_roots, Hload].
    apply map_histories.
    + intro fe. destruct (decide (TLB.affects tlbi fe)); reflexivity.
    + intros fe events Hhist. destruct (decide (TLB.affects tlbi fe)); [|exact Hhist].
      destruct events; [constructor|constructor; assumption].
Qed.

Definition event_ok tid time ev :=
  match ev with
  | Ev.Msg _ => P (TLB.Entry.Load, time)
  | Ev.Tlbi tlbi recipient _ => tid = recipient →
      P (TLB.Entry.Load, time) ∧ P (TLB.Entry.Tlbi (TLBI.tid tlbi), time)
  end.

Lemma fill_event tid imem mem time roots ev : event_ok tid time ev →
  keeps histories (TLB.fill_event tid imem mem time roots ev).
Proof.
  unfold event_ok, TLB.fill_event. destruct ev as [msg|tlbi recipient epoch].
  - apply fill_write.
  - intro H. destruct (decide (tid = recipient)) as [Heq|Hne]; [destruct (H Heq); apply fill_tlbi; assumption|apply keeps_ret].
Qed.

Fixpoint memory_ok tid (mem : Memory.t) : Prop :=
  match mem with [] => True | ev :: rest => event_ok tid (S (length rest)) ev ∧ memory_ok tid rest end.

Lemma roots_filter (Q : ((bv 16 * bv 64 * bool) * nat) → Prop) `{∀ x, Decision (Q x)} roots :
  roots_ok roots → roots_ok (filter Q roots).
Proof.
  intro Hr. unfold roots_ok in *. rewrite list.Forall_forall in Hr |- *. intros x Hx. apply Hr.
  apply list_elem_of_filter in Hx as [_ Hx]. exact Hx.
Qed.

Lemma fill_added imem mem time roots : roots_ok roots →
  keeps histories (TLB.fill_from_roots imem mem time
    (map fst (filter (λ '(_, stamp), stamp = time) roots))).
Proof.
  intros Hroots. remember (filter (λ '(_, stamp), stamp = time) roots) as added eqn:Hadded.
  destruct added as [|[root stamp] added].
  - rewrite VMCacheHistory.fill_from_roots_nil. apply keeps_ret.
  - apply fill_from_roots. assert (Hin : (root, stamp) ∈ filter (λ '(_, stamp), stamp = time) roots)
      by (rewrite <- Hadded; left).
    apply list_elem_of_filter in Hin as [Heq Hin]. cbn in Heq. subst stamp.
    unfold roots_ok in Hroots. rewrite list.Forall_forall in Hroots. exact (Hroots _ Hin).
Qed.

Lemma fill_from_btw tid imem mem past : memory_ok tid past → ∀ roots tmin,
  roots_ok roots → keeps histories (TLB.fill_from_btw tid imem mem roots tmin (length past) past).
Proof.
  induction past as [|ev past IH]; cbn [memory_ok]; intros Hmem roots tmin Hroots.
  - cbn [length TLB.fill_from_btw]. destruct (decide _); [apply keeps_ret|apply keeps_throw].
  - destruct Hmem as [Hev Hmem]. cbn [length TLB.fill_from_btw].
    destruct (decide _); [apply keeps_ret|].
    apply keeps_bind; [apply IH; [exact Hmem|apply roots_filter, Hroots]|intro].
    apply keeps_bind; [apply fill_event, Hev|intro]. apply fill_added, Hroots.
Qed.

Lemma roll_back time : keeps histories (TLB.roll_back time).
Proof.
  unfold TLB.roll_back. apply map_histories; [intro; reflexivity|].
  intros fe events H. rewrite list.Forall_forall in H |- *. intros x Hx. apply H.
  apply list_elem_of_filter in Hx as [_ Hx]. exact Hx.
Qed.

Lemma fill_cse tid imem mem time ttbr0 ttbr1 : memory_ok tid mem → P (TLB.Entry.Load, time) →
  keeps histories (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  intros Hmem Htime. unfold TLB.fill_cse, TLB.fill_from.
  apply keeps_bind; [apply roll_back|intro]. apply keeps_bind; [apply set_roots|intro].
  apply fill_from_btw; [exact Hmem|]. destruct ttbr1; repeat constructor; exact Htime.
Qed.
Lemma fill_asid_root tid imem mem root time old new : memory_ok tid mem →
  P (TLB.Entry.Load, time) → histories old → roots_ok (TLB.asid_roots old) →
  TLB.fill_asid_root tid imem mem root time old = Ok (new, ()) → histories new.
Proof.
  intros Hmem Htime Hold Hroots Hrun.
  destruct (VMSwapRemove.fill_asid_root_inv _ _ _ _ _ _ _ Hrun) as [mid [Hfill Hfrom]].
  assert (Hrolled : histories (VMCacheExchange.rolled time old)).
  { eapply roll_back; [exact Hold|apply VMSwapRemove.roll_back_run]. }
  assert (Hmid : histories mid).
  { assert (Hstart : histories (set TLB.asid_roots ((root, time) ::.) (VMCacheExchange.rolled time old)))
      by exact Hrolled.
    eapply fill_from_roots; [exact Htime|exact Hstart|exact Hfill]. }
  pose proof (VMCacheRoots.fill_from_roots _ _ _ _ _ _ () Hfill) as Hrootsmid.
  unfold VMCacheRoots.config in Hrootsmid.
  assert (Hrmid : roots_ok (TLB.asid_roots mid)).
  { rewrite Hrootsmid. constructor; [exact Htime|exact Hroots]. }
  eapply fill_from_btw; [exact Hmem|exact Hrmid|exact Hmid|exact Hfrom].
Qed.

Lemma fill_promise tid imem mem ev : event_ok tid (length mem) ev →
  keeps histories (TLB.fill_promise tid imem mem ev).
Proof.
  intro Hev. unfold TLB.fill_promise. apply keeps_bind; [apply keeps_get|intro; apply fill_event, Hev].
Qed.
End Predicate.

Lemma event_allowed_ne p limit tid time ev : time ≠ p →
  event_ok (VMSwapRemoveEvents.event_allowed p limit) tid time ev.
Proof.
  intro Hne. destruct ev as [msg|tlbi recipient epoch]; cbn [event_ok].
  - left. exact Hne.
  - intros _. split; left; exact Hne.
Qed.

Lemma memory_below p limit tid mem : length mem < p →
  memory_ok (VMSwapRemoveEvents.event_allowed p limit) tid mem.
Proof.
  induction mem as [|ev mem IH]; cbn [length memory_ok]; intro Hlen; [exact I|].
  split; [apply event_allowed_ne; lia|apply IH; lia].
Qed.

(** Processing a foreign TLBI adds no cache marker at its timestamp. *)
Theorem memory_removed limit tid l r tlbi rc epoch : tid ≠ rc →
  memory_ok (VMSwapRemoveEvents.event_allowed (S (length r)) limit) tid
    (l ++ Ev.Tlbi tlbi rc epoch :: r).
Proof.
  intro Hne. induction l as [|ev l IH]; cbn [app memory_ok].
  - split.
    + cbn [event_ok]. intro H. contradiction.
    + apply memory_below. lia.
  - split; [apply event_allowed_ne; rewrite length_app; cbn; lia|exact IH].
Qed.

Lemma histories_bounded p limit bound cache : bound < p → VMCacheOrder.good bound cache →
  histories (VMSwapRemoveEvents.event_allowed p limit) cache.
Proof.
  intros Hlt Hgood fe. destruct (Hgood fe) as [_ Hbound].
  eapply list.Forall_impl; [exact Hbound|]. intros et Htime. left. cbn in Htime |- *. lia.
Qed.

Lemma histories_mono p lower upper cache : lower ≤ upper →
  histories (VMSwapRemoveEvents.event_allowed p lower) cache →
  histories (VMSwapRemoveEvents.event_allowed p upper) cache.
Proof.
  intros Hle Hhist fe. eapply list.Forall_impl; [apply Hhist|].
  intros et [Hne|[Hload Htime]]; [left; exact Hne|right; split; [exact Hload|lia]].
Qed.
Definition cache_ok p limit cache :=
  histories (VMSwapRemoveEvents.event_allowed p limit) cache ∧
  roots_ok (VMSwapRemoveEvents.event_allowed p limit) (TLB.asid_roots cache).

Lemma roots_mono p lower upper roots : lower ≤ upper →
  roots_ok (VMSwapRemoveEvents.event_allowed p lower) roots →
  roots_ok (VMSwapRemoveEvents.event_allowed p upper) roots.
Proof.
  intros Hle Hr. eapply list.Forall_impl; [exact Hr|].
  intros root [Hne|[Hload Htime]]; [left; exact Hne|right; split; [exact Hload|lia]].
Qed.

Lemma cache_mono p lower upper cache : lower ≤ upper → cache_ok p lower cache → cache_ok p upper cache.
Proof. intros Hle [Hhist Hroots]. split; [eapply histories_mono|eapply roots_mono]; eassumption. Qed.

Lemma cache_bounded p limit bound cache : bound < p → VMCacheOrder.good bound cache →
  Forall (λ root, root.2 ≤ bound) (TLB.asid_roots cache) → cache_ok p limit cache.
Proof.
  intros Hlt Hgood Hroots. split; [eapply histories_bounded; eassumption|].
  eapply list.Forall_impl; [exact Hroots|]. intros root Htime. left. cbn in Htime |- *. lia.
Qed.

Lemma allowed_load p limit time : time ≠ p ∨ p ≤ limit →
  VMSwapRemoveEvents.event_allowed p limit (TLB.Entry.Load, time).
Proof. intros [Hne|Hle]; [left; exact Hne|right; split; [reflexivity|exact Hle]]. Qed.

Lemma cache_fill_promise p limit tid imem mem ev old new : length mem ≠ p → cache_ok p limit old →
  TLB.fill_promise tid imem mem ev old = Ok (new, ()) → cache_ok p limit new.
Proof.
  intros Hlen [Hhist Hroots] Hrun. split.
  - eapply fill_promise; [apply event_allowed_ne, Hlen|exact Hhist|exact Hrun].
  - pose proof (VMCacheRoots.fill_promise _ _ _ _ _ _ () Hrun) as Hr.
    unfold VMCacheRoots.config in Hr. rewrite Hr. exact Hroots.
Qed.

Lemma cache_fill_asid_root limit tid imem l r tlbi rc epoch root time old new :
  tid ≠ rc → (time ≠ S (length r) ∨ S (length r) ≤ limit) → cache_ok (S (length r)) limit old →
  TLB.fill_asid_root tid imem (l ++ Ev.Tlbi tlbi rc epoch :: r) root time old = Ok (new, ()) →
  cache_ok (S (length r)) limit new.
Proof.
  intros Hrc Htime [Hhist Hroots] Hrun. split.
  - eapply fill_asid_root; [apply memory_removed, Hrc|apply allowed_load, Htime|
      exact Hhist|exact Hroots|exact Hrun].
  - rewrite (VMCacheExchange.fill_asid_root_roots _ _ _ _ _ _ _ Hrun).
    constructor; [apply allowed_load, Htime|exact Hroots].
Qed.

Lemma cache_fill_cse limit tid imem l r tlbi rc epoch time ttbr0 ttbr1 old new :
  tid ≠ rc → cache_ok (S (length r)) limit old →
  TLB.fill_cse tid imem (l ++ Ev.Tlbi tlbi rc epoch :: r) time ttbr0 ttbr1 old = Ok (new, ()) →
  cache_ok (S (length r)) (time `max` limit) new.
Proof.
  intros Hrc [Hhist Hroots] Hrun.
  assert (Htime : VMSwapRemoveEvents.event_allowed (S (length r)) (time `max` limit)
      (TLB.Entry.Load, time)).
  { apply allowed_load. destruct (decide (time = S (length r))); [right; lia|left; assumption]. }
  split.
  - eapply fill_cse; [apply memory_removed, Hrc|exact Htime| |exact Hrun].
    eapply histories_mono; [|exact Hhist]. lia.
  - rewrite (VMCacheHistory.fill_cse_roots _ _ _ _ _ _ _ _ Hrun).
    destruct ttbr1.
    + constructor; [exact Htime|constructor; [exact Htime|constructor]].
    + constructor; [exact Htime|constructor].
Qed.
End VMSwapRemoveHistory.
