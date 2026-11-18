(******************************************************************************)
(* Rollback preserves point lookups and the active physical-page index        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache
  PromiseFirstSailVMCacheRollback.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheIndex.
Import VMPromising VMCacheReplay VMCacheRollback.
#[local] Existing Instance TLB.Decision_affects.
Local Notation action A := (stateT TLB.t (result string) A).

Definition project time (events : option TLB.Entry.events) := past time (default [] events).
Definition same_lookups time (old new : TLB.VATLB.t) :=
  ∀ fe, project time (old !! fe) = project time (new !! fe).
Definition active_at time (cache : TLB.t) fe : bool :=
  if project time (TLB.vatlb cache !! fe) is (TLB.Entry.Load, _) :: _ then true else false.
Definition active_index time (cache : TLB.t) page :=
  filter (λ fe, active_at time cache fe) (TLB.next_table_cache cache !!! page).
Definition frame time (old new : TLB.t) :=
  same_lookups time (TLB.vatlb old) (TLB.vatlb new) ∧
  ∀ page, active_index time old page = active_index time new page.

Lemma frame_refl time cache : frame time cache cache.
Proof. split; intro; reflexivity. Qed.
Lemma frame_trans time old mid new : frame time old mid → frame time mid new → frame time old new.
Proof.
  intros [Hlookup1 Hindex1] [Hlookup2 Hindex2]. split; intro.
  - rewrite Hlookup1. apply Hlookup2.
  - rewrite Hindex1. apply Hindex2.
Qed.

Lemma lookup_project_update {K} `{EqDecision K} time key f
    (entries : list (K * TLB.Entry.events)) :
  (∀ events, lookup_assoc key entries = Some events →
    ∃ events', f (Some events) = Some events' ∧ past time events' = past time events) →
  (lookup_assoc key entries = None → project time (f None) = []) →
  ∀ query, project time (lookup_assoc query (partial_alter_assoc f key entries)) =
    project time (lookup_assoc query entries).
Proof.
  induction entries as [|[first events] rest IH]; intros Hsome Hnone query.
  - cbn [partial_alter_assoc]. specialize (Hnone eq_refl).
    destruct (f None) as [events'|]; [|reflexivity].
    cbn [lookup_assoc]. destruct (decide (query = key)); [exact Hnone|reflexivity].
  - cbn [partial_alter_assoc]. destruct (decide (key = first)) as [->|Hkey].
    + destruct (Hsome events ltac:(cbn [lookup_assoc]; rewrite decide_True by reflexivity; reflexivity))
        as [events' [Hnew Hpast]]. rewrite Hnew.
      cbn [lookup_assoc]. destruct (decide (query = first)); [exact Hpast|reflexivity].
    + cbn [lookup_assoc]. destruct (decide (query = first)); [reflexivity|].
      apply IH.
      * intros old Hlookup. apply Hsome. cbn [lookup_assoc]. rewrite decide_False by exact Hkey. exact Hlookup.
      * intro Hlookup. apply Hnone. cbn [lookup_assoc]. rewrite decide_False by exact Hkey. exact Hlookup.
Qed.

Lemma update_same_lookups time cache fe f :
  (∀ events, cache !! fe = Some events →
    ∃ events', f (Some events) = Some events' ∧ past time events' = past time events) →
  (cache !! fe = None → project time (f None) = []) →
  same_lookups time cache (partial_alter f fe cache).
Proof.
  destruct fe as [ctxt entry]. intros Hsome Hnone [other query].
  unfold partial_alter, TLB.VATLB.partial_alter_fe, lookup, TLB.VATLB.lookup_fe.
  cbn [TLB.FE.ctxt TLB.FE.entry projT1 projT2].
  destruct (decide (ctxt = other)) as [<-|Hne].
  - rewrite get_alter_entries_same. symmetry. apply lookup_project_update; assumption.
  - rewrite get_alter_entries_other by exact Hne. reflexivity.
Qed.

Lemma lookup_assoc_map {K} `{EqDecision K} (f : K → TLB.Entry.events → TLB.Entry.events) entries key :
  lookup_assoc key (map (λ '(k, events), (k, f k events)) entries) =
    f key <$> lookup_assoc key entries.
Proof.
  induction entries as [|[first events] entries IH]; [reflexivity|].
  cbn [map lookup_assoc]. destruct (decide (key = first)) as [->|Hne]; [reflexivity|exact IH].
Qed.

Lemma lookup_map_fe f cache fe :
  TLB.VATLB.map_fe f cache !! fe = f fe <$> (cache !! fe).
Proof.
  destruct fe as [ctxt entry]. unfold lookup, TLB.VATLB.lookup_fe.
  cbn [TLB.FE.ctxt TLB.FE.entry projT1 projT2].
  rewrite get_map_fe, lookup_assoc_map. reflexivity.
Qed.

Lemma map_same_lookups time f cache :
  (∀ fe events, past time (f fe events) = past time events) →
  same_lookups time cache (TLB.VATLB.map_fe f cache).
Proof.
  intros Hf fe. rewrite lookup_map_fe.
  destruct (cache !! fe) as [events|]; [symmetry; apply Hf|reflexivity].
Qed.

Lemma frame_vatlb time cache vatlb :
  same_lookups time (TLB.vatlb cache) vatlb →
  frame time cache (setv TLB.vatlb vatlb cache).
Proof.
  intro Hlookup. split; [exact Hlookup|]. intro page.
  unfold active_index. cbn. apply list_filter_iff. intro fe.
  unfold active_at. cbn. rewrite Hlookup. reflexivity.
Qed.

Lemma frame_index time cache fe : active_at time cache fe = false →
  frame time cache (set TLB.next_table_cache (alter_default (fe ::.) (TLB.FE.next_table fe)) cache).
Proof.
  intro Hinactive. split; [intro; reflexivity|]. intro page.
  unfold active_index. cbn. rewrite !lookup_total_lookup.
  unfold alter_default. rewrite lookup_partial_alter.
  destruct (decide (page = TLB.FE.next_table fe)) as [->|Hne].
  - rewrite decide_True by reflexivity. cbn [default].
    change (filter (λ fe0, active_at time cache fe0)
        (default [] (TLB.next_table_cache cache !! TLB.FE.next_table fe)) =
      filter (λ fe0, active_at time cache fe0)
        (fe :: default [] (TLB.next_table_cache cache !! TLB.FE.next_table fe))).
    rewrite filter_cons, Hinactive, decide_False by (cbn; tauto). reflexivity.
  - rewrite decide_False by congruence. reflexivity.
Qed.


Lemma fill_entry_frame bound time fe old new loaded :
  bound < time → TLB.fill_entry time fe old = Ok (new, loaded) → frame bound old new.
Proof.
  intros Htime Hfill. unfold TLB.fill_entry in Hfill. cbn in Hfill.
  unfold mget in Hfill.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose in Hfill. cbn in Hfill.
  destruct (TLB.vatlb old !! fe) as [events|] eqn:Hlookup; rewrite Hlookup in Hfill.
  - destruct events as [|[event stamp] rest].
    + unfold mret, result_ret in Hfill. injection Hfill as <- <-.
      apply frame_vatlb, update_same_lookups.
      * intros events Hget. rewrite Hlookup in Hget. injection Hget as <-.
        eexists. split; [reflexivity|apply past_future, Htime].
      * intro Hnone. rewrite Hlookup in Hnone. discriminate.
    + destruct event.
      * unfold mret, result_ret in Hfill. injection Hfill as <- <-. apply frame_refl.
      * unfold mret, result_ret in Hfill. injection Hfill as <- <-.
        apply frame_vatlb, update_same_lookups.
        -- intros events Hget. rewrite Hlookup in Hget. injection Hget as <-.
           eexists. split; [reflexivity|apply past_future, Htime].
        -- intro Hnone. rewrite Hlookup in Hnone. discriminate.
  - set (inserted := setv TLB.vatlb
      (partial_alter (λ _, Some [(TLB.Entry.Load, time)]) fe (TLB.vatlb old)) old).
    assert (Hinsert : frame bound old inserted).
    { apply frame_vatlb, update_same_lookups.
      - intros events Hget. rewrite Hlookup in Hget. discriminate.
      - intro. apply past_future, Htime. }
    assert (Hinactive : active_at bound inserted fe = false).
    { destruct Hinsert as [Hget _]. unfold active_at. rewrite <- Hget, Hlookup. reflexivity. }
    destruct (decide (TLB.FE.is_table fe));
      unfold mret, result_ret, mbind, result_bind in Hfill; cbn in Hfill;
      injection Hfill as <- <-.
    + change (frame bound old
        (set TLB.next_table_cache (alter_default (fe ::.) (TLB.FE.next_table fe)) inserted)).
      eapply frame_trans; [exact Hinsert|apply frame_index, Hinactive].
    + exact Hinsert.
Qed.

Definition preserves {A} (bound : nat) (run : action A) : Prop :=
  ∀ old new ret, run old = Ok (new, ret) → frame bound old new.

Lemma preserves_ret {A} bound (a : A) : preserves bound (mret a).
Proof.
  intros old new ret Hrun. change (@Ok string _ (old, a) = Ok (new, ret)) in Hrun.
  injection Hrun as <- <-. apply frame_refl.
Qed.

Lemma preserves_bind {A B} bound (run : action A) (k : A → action B) :
  preserves bound run → (∀ a, preserves bound (k a)) → preserves bound (run ≫= k).
Proof.
  intros Hrun Htail old new ret Hresult.
  unfold mbind, st_bind, result_bind in Hresult.
  destruct (run old) as [[mid a]|err] eqn:Hfirst; [|discriminate].
  eapply frame_trans; [eapply Hrun; exact Hfirst|eapply Htail; exact Hresult].
Qed.

Lemma preserves_fmap {A B} bound (run : action A) (f : A → B) :
  preserves bound run → preserves bound (f <$> run).
Proof.
  intros Hrun old new ret Hresult.
  unfold fmap, st_fmap, result_fmap in Hresult.
  destruct (run old) as [[mid a]|err] eqn:Hfirst; [|discriminate].
  injection Hresult as <- <-. eapply Hrun. exact Hfirst.
Qed.

Lemma preserves_get {A} bound (proj : TLB.t → A) : preserves bound (mget proj).
Proof.
  intros old new ret Hresult.
  change (@Ok string _ (old, proj old) = Ok (new, ret)) in Hresult.
  injection Hresult as <- <-. apply frame_refl.
Qed.

Lemma preserves_lift {A} bound (r : result string A) : preserves bound (mlift r).
Proof.
  destruct r as [a|err]; intros old new ret Hresult.
  - change (@Ok string _ (old, a) = Ok (new, ret)) in Hresult.
    injection Hresult as <- <-. apply frame_refl.
  - discriminate.
Qed.

Lemma preserves_throw {A} bound (err : string) : preserves bound (mthrow err : action A).
Proof. intros old new ret Hresult. discriminate. Qed.

Lemma preserves_othrow {A} bound (err : string) (opt : option A) : preserves bound (othrow err opt).
Proof. destruct opt; [apply preserves_ret|apply preserves_throw]. Qed.

Lemma preserves_guard bound (err : string) (P : Prop) `{Decision P} : preserves bound (guard_or err P).
Proof. unfold guard_or. destruct (decide P); [apply preserves_ret|apply preserves_throw]. Qed.

Lemma preserves_guard_unit bound (err : string) (P : Prop) `{Decision P} : preserves bound (guard_or' err P).
Proof. unfold guard_or'. apply preserves_bind; [apply preserves_guard|intro; apply preserves_ret]. Qed.

Lemma preserves_mapM {A B} bound (f : A → action B) xs :
  (∀ a, preserves bound (f a)) → preserves bound (mapM f xs).
Proof.
  intro Hf. induction xs as [|a xs IH]; cbn [mapM]; [apply preserves_ret|].
  apply preserves_bind; [apply Hf|]. intro b.
  apply preserves_bind; [exact IH|]. intro bs. apply preserves_ret.
Qed.

Lemma preserves_fill_entry bound time fe :
  bound < time → preserves bound (TLB.fill_entry time fe).
Proof. intros Htime old new ret Hrun. eapply fill_entry_frame; eassumption. Qed.

Ltac solve_preserves :=
  first
    [ apply preserves_ret
    | apply preserves_get
    | apply preserves_lift
    | apply preserves_throw
    | apply preserves_othrow
    | apply preserves_guard
    | apply preserves_guard_unit
    | apply preserves_fill_entry; assumption
    | apply preserves_fmap; solve_preserves
    | apply preserves_bind; [solve_preserves|intro; solve_preserves]
    | apply preserves_mapM; intro; solve_preserves
    | match goal with |- preserves _ (match ?x with _ => _ end) =>
        destruct x; solve_preserves end ].

Lemma preserves_fill_root bound imem mem time roots :
  bound < time → preserves bound (TLB.fill_root imem mem time roots).
Proof.
  intro Htime. unfold TLB.fill_root. solve_preserves.
Qed.

Lemma preserves_fill_from_entry bound imem mem time entry :
  bound < time → preserves bound (TLB.fill_from_entry imem mem time entry).
Proof.
  intro Htime. unfold TLB.fill_from_entry. solve_preserves.
Qed.

Lemma preserves_fill_from_entries_step bound imem mem time entries :
  bound < time → preserves bound (TLB.fill_from_entries_step imem mem time entries).
Proof.
  intro Htime. unfold TLB.fill_from_entries_step.
  apply preserves_fmap, preserves_mapM. intro entry.
  apply preserves_fill_from_entry, Htime.
Qed.

Lemma preserves_fill_from_entries bound imem mem time entries :
  bound < time → preserves bound (TLB.fill_from_entries imem mem time entries).
Proof.
  intro Htime. unfold TLB.fill_from_entries.
  do 3 (apply preserves_bind; [apply preserves_fill_from_entries_step, Htime|intro]).
  apply preserves_guard_unit.
Qed.

Lemma preserves_fill_from_roots bound imem mem time roots :
  bound < time → preserves bound (TLB.fill_from_roots imem mem time roots).
Proof.
  intro Htime. unfold TLB.fill_from_roots.
  apply preserves_bind; [apply preserves_fill_root, Htime|].
  intro entries. apply preserves_fill_from_entries, Htime.
Qed.
Lemma preserves_vatlb bound (f : TLB.VATLB.t → TLB.VATLB.t) :
  (∀ cache, same_lookups bound cache (f cache)) → preserves bound (mset TLB.vatlb f).
Proof.
  intros Hf old new ret Hrun. destruct ret.
  change (@Ok string _ (set TLB.vatlb f old, ()) = Ok (new, ())) in Hrun.
  injection Hrun as <-. apply frame_vatlb, Hf.
Qed.

Lemma preserves_relevant_entries bound asids page :
  preserves bound (TLB.get_relevant_entries asids page).
Proof. unfold TLB.get_relevant_entries. solve_preserves. Qed.

Lemma preserves_tlbi_marker bound time issuer fe :
  bound < time → preserves bound (mset TLB.vatlb (alter (λ events, if events is [] then [] else (TLB.Entry.Tlbi issuer, time)::events) fe)).
Proof.
  intro Htime. apply preserves_vatlb. intro cache.
  unfold alter, alter_default. apply update_same_lookups.
  - intros events Hlookup. destruct events as [|event events]; eexists; split;
      try reflexivity. apply past_future, Htime.
  - intro Hnone. reflexivity.
Qed.

Lemma preserves_invalidate_all bound time tlbi :
  bound < time → preserves bound (mset TLB.vatlb (TLB.VATLB.map_fe
    (λ fe events, if decide (TLB.affects tlbi fe)
      then (if events is [] then [] else (TLB.Entry.Tlbi (TLBI.tid tlbi), time) :: events) else events))).
Proof.
  intro Htime. apply preserves_vatlb. intro cache. apply map_same_lookups.
  intros fe events. destruct (decide (TLB.affects tlbi fe)); [destruct events|];
    try reflexivity. apply past_future, Htime.
Qed.

Ltac solve_fill_preserves :=
  first
    [ apply preserves_fill_root; assumption
    | apply preserves_fill_from_entry; assumption
    | apply preserves_fill_from_entries; assumption
    | apply preserves_fill_from_roots; assumption
    | apply preserves_tlbi_marker; assumption
    | apply preserves_invalidate_all; assumption
    | apply preserves_relevant_entries
    | solve_preserves
    | apply preserves_fmap; solve_fill_preserves
    | apply preserves_bind; [solve_fill_preserves|intro; solve_fill_preserves]
    | apply preserves_mapM; intro; solve_fill_preserves
    | match goal with |- preserves _ (match ?x with _ => _ end) =>
        destruct x; solve_fill_preserves end ].

Lemma preserves_fill_write bound imem mem time roots msg :
  bound < time → preserves bound (TLB.fill_write imem mem time roots msg).
Proof. intro Htime. unfold TLB.fill_write. solve_fill_preserves. Qed.

Lemma preserves_fill_tlbi bound imem mem time roots tlbi :
  bound < time → preserves bound (TLB.fill_tlbi imem mem time roots tlbi).
Proof. intro Htime. unfold TLB.fill_tlbi. solve_fill_preserves. Qed.

Theorem fill_event_frame bound tid imem mem time roots ev old new :
  bound < time → TLB.fill_event tid imem mem time roots ev old = Ok (new, ()) →
  frame bound old new.
Proof.
  intro Htime. assert (Hpres : preserves bound (TLB.fill_event tid imem mem time roots ev)); [|intro Hrun; exact (Hpres old new () Hrun)].
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch].
  - apply preserves_fill_write, Htime.
  - destruct (decide (tid = recipient)); [apply preserves_fill_tlbi, Htime|apply preserves_ret].
Qed.

Theorem fill_promise_frame tid imem mem ev old new :
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (new, ()) →
  frame (length mem) old new.
Proof.
  assert (Hpres : preserves (length mem) (TLB.fill_promise tid imem (ev :: mem) ev)); [|intro Hrun; exact (Hpres old new () Hrun)].
  unfold TLB.fill_promise. apply preserves_bind; [apply preserves_get|].
  intro roots. intros before after ret Hfill. destruct ret.
  eapply fill_event_frame; [|exact Hfill]. cbn. lia.
Qed.
Theorem emit_promise_cache_frame tid imem mem ev ts ts' old :
  TState.tlb ts = Some old →
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok ts' →
  ∃ new, TState.tlb ts' = Some new ∧
    frame (length mem) old new.
Proof.
  intros Hcache Hpromise.
  set (pending := if bool_decide (Ev.tid ev = tid) then
    match ev with
    | Ev.Msg _ => TState.promise_write (length (ev :: mem)) ts
    | _ => TState.promise_tlbi (length (ev :: mem)) ts
    end else ts).
  assert (Hpending : TState.tlb pending = Some old).
  { unfold pending. destruct (bool_decide (Ev.tid ev = tid)); [destruct ev|]; exact Hcache. }
  change (TState.run_tlb (TLB.fill_promise tid imem (ev :: mem) ev) pending = Ok ts') in Hpromise.
  unfold TState.run_tlb in Hpromise. rewrite Hpending in Hpromise.
  destruct (TLB.fill_promise tid imem (ev :: mem) ev old) as [[new []]|err] eqn:Hfill;
    cbn in Hpromise; [|discriminate].
  injection Hpromise as <-. exists new. split; [reflexivity|].
  eapply fill_promise_frame. exact Hfill.
Qed.


Theorem fill_promise_frame_at tid imem mem ev time old issued :
  time ≤ length mem →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) → frame time old issued.
Proof.
  intro Htime. assert (Hpres : preserves time (TLB.fill_promise tid imem (ev :: mem) ev));
    [|intro Hrun; exact (Hpres old issued () Hrun)].
  unfold TLB.fill_promise. apply preserves_bind; [apply preserves_get|].
  intro roots. intros before after ret Hfill. destruct ret.
  eapply fill_event_frame; [|exact Hfill]. cbn. lia.
Qed.

Lemma rollback_active time cache fe :
  TLB.VATLB.is_active (TLB.VATLB.map_fe (λ _, past time) (TLB.vatlb cache)) fe =
    active_at time cache fe.
Proof.
  unfold TLB.VATLB.is_active, active_at. rewrite lookup_map_fe.
  unfold project. destruct (TLB.vatlb cache !! fe) as [events|]; reflexivity.
Qed.

Lemma relevant_rollback time cache asids page :
  snd <$> TLB.get_relevant_entries asids page
    (set TLB.vatlb (TLB.VATLB.map_fe (λ _, past time)) cache) =
  Ok (filter (TLB.FE.is_active_asid asids) (active_index time cache page)).
Proof.
  unfold TLB.get_relevant_entries.
  change (@Ok string _ (filter (λ fe,
      TLB.VATLB.is_active (TLB.VATLB.map_fe (λ _, past time) (TLB.vatlb cache)) fe ∧
      TLB.FE.is_active_asid asids fe) (TLB.next_table_cache cache !!! page)) =
    Ok (filter (TLB.FE.is_active_asid asids) (active_index time cache page))).
  unfold active_index. rewrite list_filter_filter. f_equal.
  apply list_filter_iff. intro fe. rewrite rollback_active. tauto.
Qed.

(** A future allocation may leave a dormant index entry after rollback.
    The complete active index, including list order, is unchanged. *)
Theorem fill_promise_rollback_relevant tid imem mem ev time old issued
    rolled_old rolled_issued asids page :
  time ≤ length mem →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.roll_back time old = Ok (rolled_old, ()) →
  TLB.roll_back time issued = Ok (rolled_issued, ()) →
  snd <$> TLB.get_relevant_entries asids page rolled_old =
    snd <$> TLB.get_relevant_entries asids page rolled_issued.
Proof.
  intros Htime Hpromise Hold Hissued.
  change (@Ok string _ (set TLB.vatlb (TLB.VATLB.map_fe (λ _, past time)) old, ()) = Ok (rolled_old, ())) in Hold.
  change (@Ok string _ (set TLB.vatlb (TLB.VATLB.map_fe (λ _, past time)) issued, ()) = Ok (rolled_issued, ())) in Hissued.
  injection Hold as <-. injection Hissued as <-.
  rewrite !relevant_rollback.
  destruct (fill_promise_frame_at tid imem mem ev time old issued Htime Hpromise) as [_ Hindex].
  rewrite Hindex. reflexivity.
Qed.

End VMCacheIndex.
