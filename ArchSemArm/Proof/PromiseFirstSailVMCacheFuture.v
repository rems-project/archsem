(******************************************************************************)
(* The timestamps and issuers added by one future cache event                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheRefill
  PromiseFirstSailVMCacheOrder PromiseFirstSailVMCacheEvents PromiseFirstSailVMCacheLastTLBI
  PromiseFirstSailVMCacheRollback PromiseFirstSailVMBBMTransport PromiseFirstSailVMCacheFill
  PromiseFirstSailVMCacheState.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheFuture.
Import VMPromising VMCacheRefill VMCacheOrder VMCacheLastTLBI.
#[local] Existing Instance TLB.Decision_affects.

Definition allowed bound owner (et : TLB.Entry.event * nat) : Prop :=
  et.2 ≤ bound ∨ et.2 = S bound ∧
    match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => issuer = owner end.
Definition histories bound owner (cache : TLB.t) : Prop :=
  ∀ fe, Forall (allowed bound owner) (history cache fe).

Lemma histories_bounded bound owner cache : good bound cache → histories bound owner cache.
Proof.
  intros Hgood fe. destruct (Hgood fe) as [_ Hbound].
  eapply list.Forall_impl; [exact Hbound|]. intros et Htime. left. exact Htime.
Qed.

Lemma allowed_load bound owner : allowed bound owner (TLB.Entry.Load, S bound).
Proof. right. split; [reflexivity|exact I]. Qed.
Lemma allowed_tlbi bound owner : allowed bound owner (TLB.Entry.Tlbi owner, S bound).
Proof. right. split; reflexivity. Qed.

Lemma fill_entry bound owner fe : keeps (histories bound owner) (TLB.fill_entry (S bound) fe).
Proof.
  intros old new loaded Hold Hrun.
  destruct (fill_entry_effect (S bound) fe old new loaded Hrun) as [_ [_ Hhist]].
  intro query. rewrite Hhist. destruct (decide (query = fe)); [|apply Hold].
  unfold loaded_history. destruct (active (history old fe)); [apply Hold|].
  constructor; [apply allowed_load|apply Hold].
Qed.

Lemma set_index bound owner f : keeps (histories bound owner) (mset TLB.next_table_cache f).
Proof. apply keeps_set. intros old Hold. exact Hold. Qed.

Lemma map_histories bound owner f :
  (∀ fe, f fe [] = []) →
  (∀ fe events, Forall (allowed bound owner) events → Forall (allowed bound owner) (f fe events)) →
  keeps (histories bound owner) (mset TLB.vatlb (TLB.VATLB.map_fe f)).
Proof.
  intros Hnil Hf. apply keeps_set. intros old Hold fe.
  rewrite VMCacheEvents.history_map by apply Hnil. apply Hf, Hold.
Qed.

Lemma alter_histories bound owner f fe : f [] = [] →
  (∀ events, Forall (allowed bound owner) events → Forall (allowed bound owner) (f events)) →
  keeps (histories bound owner) (mset TLB.vatlb (alter f fe)).
Proof.
  intros Hnil Hf. apply keeps_set. intros old Hold query.
  rewrite history_alter_any by exact Hnil.
  destruct (decide (query = fe)); [apply Hf|]; apply Hold.
Qed.

Lemma invalidate_histories bound tlbi fe :
  keeps (histories bound (TLBI.tid tlbi))
    (mset TLB.vatlb (alter (invalidate (S bound) tlbi) fe)).
Proof.
  apply alter_histories; [reflexivity|]. intros [|event events] Hhist; [constructor|].
  constructor; [apply allowed_tlbi|exact Hhist].
Qed.

Local Opaque TLB.fill_entry.
Ltac solve_histories :=
  first [apply keeps_ret | apply keeps_get | apply keeps_lift
    | apply keeps_throw | apply keeps_othrow | apply keeps_guard | apply keeps_guard_unit
    | apply fill_entry | apply set_index
    | apply keeps_bind; [solve_histories|intro; solve_histories]
    | apply keeps_fmap; solve_histories | apply keeps_mapM; intro; solve_histories
    | match goal with |- keeps _ (match ?x with _ => _ end) => destruct x; solve_histories end].

Lemma fill_root bound owner imem mem roots :
  keeps (histories bound owner) (TLB.fill_root imem mem (S bound) roots).
Proof. unfold TLB.fill_root. solve_histories. Qed.
Lemma fill_from_entry bound owner imem mem entry :
  keeps (histories bound owner) (TLB.fill_from_entry imem mem (S bound) entry).
Proof. unfold TLB.fill_from_entry. solve_histories. Qed.
Lemma fill_from_entries bound owner imem mem entries :
  keeps (histories bound owner) (TLB.fill_from_entries imem mem (S bound) entries).
Proof.
  unfold TLB.fill_from_entries, TLB.fill_from_entries_step.
  do 3 (apply keeps_bind; [apply keeps_fmap, keeps_mapM; intro; apply fill_from_entry|intro]).
  apply keeps_guard_unit.
Qed.
Lemma fill_from_roots bound owner imem mem roots :
  keeps (histories bound owner) (TLB.fill_from_roots imem mem (S bound) roots).
Proof.
  unfold TLB.fill_from_roots. apply keeps_bind; [apply fill_root|intro; apply fill_from_entries].
Qed.
Lemma relevant_entries bound owner asids page :
  keeps (histories bound owner) (TLB.get_relevant_entries asids page).
Proof. unfold TLB.get_relevant_entries. solve_histories. Qed.

Local Opaque TLB.fill_root TLB.fill_from_entry TLB.fill_from_entries TLB.fill_from_roots TLB.get_relevant_entries.

Lemma fill_write bound owner imem mem roots msg :
  keeps (histories bound owner) (TLB.fill_write imem mem (S bound) roots msg).
Proof.
  unfold TLB.fill_write, guard_or. destruct (decide _); [|apply keeps_throw].
  apply keeps_bind; [apply keeps_ret|intro].
  apply keeps_bind; [apply fill_root|intro].
  apply keeps_bind; [apply relevant_entries|intro; apply fill_from_entries].
Qed.

Lemma fill_tlbi bound imem mem roots tlbi :
  keeps (histories bound (TLBI.tid tlbi)) (TLB.fill_tlbi imem mem (S bound) roots tlbi).
Proof.
  destruct (TLBI.last tlbi) eqn:Hlast.
  - intros old new value Hhist Hrun. rewrite last_shape in Hrun by exact Hlast. revert Hhist Hrun.
    apply keeps_bind; [|intro; apply fill_from_entries].
    apply keeps_fmap, keeps_mapM. intro entry. unfold step.
    apply keeps_bind; [apply invalidate_histories|intro; apply relevant_entries].
  - unfold TLB.fill_tlbi. rewrite Hlast.
    apply keeps_bind; [|intro; apply fill_from_roots].
    apply map_histories.
    + intro fe. destruct (decide (TLB.affects tlbi fe)); reflexivity.
    + intros fe events Hhist. destruct (decide (TLB.affects tlbi fe)); [|exact Hhist].
      destruct events; [constructor|constructor; [apply allowed_tlbi|exact Hhist]].
Qed.

Lemma fill_event bound tid imem mem roots ev :
  keeps (histories bound (Ev.tid ev)) (TLB.fill_event tid imem mem (S bound) roots ev).
Proof.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch]; [apply fill_write|].
  destruct (decide (tid = recipient)); [apply fill_tlbi|apply keeps_ret].
Qed.

Theorem fill_promise tid imem mem ev old new :
  good (length mem) old → TLB.fill_promise tid imem (ev :: mem) ev old = Ok (new, ()) →
  histories (length mem) (Ev.tid ev) new.
Proof.
  intros Hgood Hrun.
  assert (Hkeeps : keeps (histories (length mem) (Ev.tid ev)) (TLB.fill_promise tid imem (ev :: mem) ev)).
  { unfold TLB.fill_promise. apply keeps_bind; [apply keeps_get|]. intro. apply fill_event. }
  eapply Hkeeps; [apply histories_bounded, Hgood|exact Hrun].
Qed.

Lemma row_history cache ctxt fe events : unique cache →
  (fe, events) ∈ TLB.VATLB.get_fe (TLB.vatlb cache) ctxt → history cache fe = events.
Proof.
  intros Hunique Hin. unfold TLB.VATLB.get_fe in Hin.
  apply list_elem_of_fmap in Hin as [[entry found] [Heq Hin]]. injection Heq as Hfe Hevents. subst fe events.
  eapply VMBBMTransport.row_history; eassumption.
Qed.

Lemma row_good bound cache ctxt fe events : good bound cache → unique cache →
  (fe, events) ∈ TLB.VATLB.get_fe (TLB.vatlb cache) ctxt → ordered events ∧ bounded bound events.
Proof. intros Hgood Hunique Hin. rewrite <- (row_history cache ctxt fe events Hunique Hin). apply Hgood. Qed.

Lemma row_allowed bound owner cache ctxt fe events : histories bound owner cache → unique cache →
  (fe, events) ∈ TLB.VATLB.get_fe (TLB.vatlb cache) ctxt → Forall (allowed bound owner) events.
Proof. intros Hhist Hunique Hin. rewrite <- (row_history cache ctxt fe events Hunique Hin). apply Hhist. Qed.

Lemma ordered_split bound events : ordered events →
  ∃ prefix, events = (prefix ++ VMCacheRollback.past bound events)%list ∧
    Forall (λ et, bound < et.2) prefix.
Proof.
  induction events as [|[event time] events IH]; intro Hordered.
  - exists []. split; [reflexivity|constructor].
  - destruct (decide (time ≤ bound)) as [Hle|Hgt].
    + exists []. split; [|constructor]. unfold VMCacheRollback.past.
      symmetry. apply filter_bounded. constructor; [exact Hle|].
      eapply bounded_mono; [exact Hle|]. apply (ordered_head_bound event time events Hordered).
    + destruct (IH (proj2 Hordered)) as [prefix [Heq Hprefix]].
      exists ((event, time) :: prefix). split.
      * rewrite VMCacheRollback.past_future by lia. cbn [app]. f_equal. exact Heq.
      * constructor; [cbn; lia|exact Hprefix].
Qed.

Lemma prefix_allowed bound owner prefix events :
  Forall (allowed bound owner) (prefix ++ events)%list →
  Forall (λ et, bound < et.2) prefix →
  Forall (λ et, et.2 = S bound ∧
    match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => issuer = owner end) prefix.
Proof.
  intros Hallowed Hfuture. apply Forall_app in Hallowed as [Hprefix _].
  induction Hprefix as [|[event time] prefix Hhead Hprefix IH]; [constructor|].
  apply Forall_cons_1 in Hfuture as [Htime Hfuture]. constructor; [|apply IH, Hfuture].
  destruct Hhead as [Hpast|Hnew]; [cbn in Hpast, Htime; lia|exact Hnew].
Qed.

Lemma same_past_member bound old new ctxt fe events :
  VMCacheRollback.same_past bound old new →
  (fe, events) ∈ TLB.VATLB.get_fe new ctxt → VMCacheRollback.past bound events ≠ [] →
  ∃ before, (fe, before) ∈ TLB.VATLB.get_fe old ctxt ∧
    VMCacheRollback.past bound before = VMCacheRollback.past bound events.
Proof.
  intros Hsame Hin Hnonempty. unfold TLB.VATLB.get_fe in Hin |- *.
  apply list_elem_of_fmap in Hin as [[entry found] [Heq Hin]]. injection Heq as Hfe Hevents. subst fe events.
  assert (Hrow : (entry, VMCacheRollback.past bound found) ∈
    VMCacheRollback.rows bound (TLB.VATLB.get ctxt new)).
  { unfold VMCacheRollback.rows. apply list_elem_of_filter. split; [exact Hnonempty|].
    apply list_elem_of_fmap. exists (entry, found). auto. }
  rewrite <- Hsame in Hrow. unfold VMCacheRollback.rows in Hrow.
  apply list_elem_of_filter in Hrow as [_ Hrow].
  apply list_elem_of_fmap in Hrow as [[oldentry before] [Heq Hrow]].
  injection Heq as Hentry Hevents. subst oldentry. exists before. split; [|symmetry; exact Hevents].
  apply list_elem_of_fmap. exists (entry, before). auto.
Qed.

Theorem promise_entry_forward tid imem mem ev old new ctxt fe events :
  VMCacheState.cache_inv (length mem) old →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (new, ()) →
  (fe, events) ∈ TLB.VATLB.get_fe (TLB.vatlb old) ctxt →
  ∃ prefix,
    (fe, (prefix ++ events)%list) ∈ TLB.VATLB.get_fe (TLB.vatlb new) ctxt ∧
    Forall (λ et, et.2 = S (length mem) ∧
      match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => issuer = Ev.tid ev end) prefix.
Proof.
  intros [Hgood [Hunique Hvalid]] Hrun Hin.
  destruct (VMCacheFillReplay.fill_promise_extends tid imem mem ev old new Hrun ctxt fe events Hin)
    as [prefix [Hfuture Hnew]].
  pose proof (fill_promise tid imem mem ev old new Hgood Hrun) as Hhist.
  pose proof (unique_fill_promise tid imem (ev :: mem) ev old new () Hunique Hrun) as Hunique'.
  exists prefix. split; [exact Hnew|]. apply (prefix_allowed (length mem) (Ev.tid ev) prefix events);
    [eapply row_allowed; eassumption|exact Hfuture].
Qed.

Theorem promise_entry_backward tid imem mem ev old new ctxt fe events :
  VMCacheState.cache_inv (length mem) old →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (new, ()) →
  (fe, events) ∈ TLB.VATLB.get_fe (TLB.vatlb new) ctxt →
  ∃ prefix before, events = (prefix ++ before)%list ∧
    Forall (λ et, et.2 = S (length mem) ∧
      match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => issuer = Ev.tid ev end) prefix ∧
    (before = [] ∨ (fe, before) ∈ TLB.VATLB.get_fe (TLB.vatlb old) ctxt) ∧
    bounded (length mem) before.
Proof.
  intros [Hgood [Hunique Hvalid]] Hrun Hin.
  pose proof (good_fill_promise tid imem (ev :: mem) ev (length mem) old new ltac:(cbn; lia) Hgood Hrun) as Hgood'.
  pose proof (unique_fill_promise tid imem (ev :: mem) ev old new () Hunique Hrun) as Hunique'.
  destruct (row_good _ new ctxt fe events Hgood' Hunique' Hin) as [Horder Hbound].
  destruct (ordered_split (length mem) events Horder) as [prefix [Heq Hfuture]].
  pose proof (fill_promise tid imem mem ev old new Hgood Hrun) as Hhist.
  pose proof (row_allowed _ _ new ctxt fe events Hhist Hunique' Hin) as Hallowed.
  exists prefix, (VMCacheRollback.past (length mem) events). split; [exact Heq|]. split.
  - apply (prefix_allowed (length mem) (Ev.tid ev) prefix (VMCacheRollback.past (length mem) events));
      [rewrite <- Heq; exact Hallowed|exact Hfuture].
  - split.
    + destruct (decide (VMCacheRollback.past (length mem) events = [])) as [Hempty|Hnonempty]; [auto|].
      destruct (same_past_member (length mem) (TLB.vatlb old) (TLB.vatlb new) ctxt fe events
        (VMCacheRollback.fill_promise_same_past tid imem mem ev old new Hrun) Hin Hnonempty)
        as [before [Hbefore Hpast]].
      destruct (row_good _ old ctxt fe before Hgood Hunique Hbefore) as [_ Hbeforebound].
      unfold VMCacheRollback.past in Hpast. rewrite filter_bounded in Hpast by exact Hbeforebound.
      right. unfold VMCacheRollback.past. rewrite <- Hpast. exact Hbefore.
    + exact (proj2 (past_good _ (length mem) events Horder Hbound)).
Qed.

End VMCacheFuture.
