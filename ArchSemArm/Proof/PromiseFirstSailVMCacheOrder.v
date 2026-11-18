(******************************************************************************)
(* Ordered entry histories under cache maintenance                            *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache PromiseFirstSailVMCacheRefill
  PromiseFirstSailVMCacheEvents PromiseFirstSailVMCacheIndex PromiseFirstSailVMCacheIndexed
  PromiseFirstSailVMCacheExchange
  PromiseFirstSailVMCacheLastTLBI.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** The comment on [TLB.Entry.events] requires histories to be sorted with
    the most recent event first and to have no two consecutive loads. Cache
    maintenance keeps both properties when it runs no earlier than every
    recorded event. *)
Module VMCacheOrder.
Import VMPromising VMCacheReplay VMCacheRefill VMCacheLastTLBI.
#[local] Existing Instance TLB.Decision_affects.
Local Notation action A := (stateT TLB.t (result string) A).

Fixpoint ordered (events : TLB.Entry.events) : Prop :=
  match events with
  | [] => True
  | (event, stamp) :: rest =>
      match rest with
      | [] => True
      | (event', stamp') :: _ =>
          stamp' ≤ stamp ∧ ¬ (event = TLB.Entry.Load ∧ event' = TLB.Entry.Load)
      end ∧ ordered rest
  end.

Definition bounded bound (events : TLB.Entry.events) := Forall (λ event, event.2 ≤ bound) events.

Definition good bound (cache : TLB.t) :=
  ∀ fe, ordered (history cache fe) ∧ bounded bound (history cache fe).

Lemma bounded_mono bound bound' events : bound ≤ bound' → bounded bound events → bounded bound' events.
Proof. intros Hle Hbound. induction Hbound; constructor; [cbn in *; lia|assumption]. Qed.

Lemma good_mono bound bound' cache : bound ≤ bound' → good bound cache → good bound' cache.
Proof.
  intros Hle Hgood fe. destruct (Hgood fe) as [Hordered Hbound].
  split; [exact Hordered|]. eapply bounded_mono; eassumption.
Qed.

Lemma push_good event time events :
  bounded time events → ordered events → (event = TLB.Entry.Load → active events = false) →
  ordered ((event, time) :: events) ∧ bounded time ((event, time) :: events).
Proof.
  intros Hbound Hordered Hload. split; [|constructor; [cbn; lia|exact Hbound]].
  destruct events as [|[event' stamp] rest]; cbn [ordered]; [split; constructor|].
  split; [|exact Hordered]. split.
  - apply Forall_cons_1 in Hbound as [Hstamp _]. exact Hstamp.
  - intros [-> ->]. specialize (Hload eq_refl). discriminate.
Qed.

Definition invalidate_good (f : TLB.Entry.events → TLB.Entry.events) time :=
  f [] = [] ∧ ∀ events, ordered events → bounded time events →
    ordered (f events) ∧ bounded time (f events).

Lemma invalidate_is_good time tlbi : invalidate_good (invalidate time tlbi) time.
Proof.
  split; [reflexivity|]. intros [|event events] Hordered Hbound; [split; constructor|].
  apply push_good; [exact Hbound|exact Hordered|discriminate].
Qed.

Lemma history_map_good time f cache :
  (∀ fe, invalidate_good (f fe) time) → good time cache →
  good time (set TLB.vatlb (TLB.VATLB.map_fe f) cache).
Proof.
  intros Hf Hgood fe. rewrite VMCacheEvents.history_map by apply (Hf fe).
  destruct (Hgood fe) as [Hordered Hbound]. apply (Hf fe); assumption.
Qed.

Lemma history_alter_any f fe cache query : f [] = [] →
  history (set TLB.vatlb (alter f fe) cache) query =
    if decide (query = fe) then f (history cache query) else history cache query.
Proof.
  intro Hempty. unfold history. cbn [TLB.vatlb]. rewrite lookup_alter_fe.
  destruct (decide (query = fe)); [|reflexivity].
  destruct (TLB.vatlb cache !! query); [reflexivity|exact (eq_sym Hempty)].
Qed.

Lemma history_alter_good time f fe cache :
  invalidate_good f time → good time cache → good time (set TLB.vatlb (alter f fe) cache).
Proof.
  intros [Hempty Hf] Hgood query. rewrite history_alter_any by exact Hempty.
  destruct (Hgood query) as [Hordered Hbound].
  destruct (decide (query = fe)); [apply Hf; assumption|split; assumption].
Qed.

Lemma good_fill_entry time fe : keeps (good time) (TLB.fill_entry time fe).
Proof.
  intros old new loaded Hgood Hfill.
  destruct (fill_entry_effect time fe old new loaded Hfill) as [_ [_ Hhistory]].
  intro query. rewrite Hhistory. destruct (Hgood query) as [Hordered Hbound].
  destruct (decide (query = fe)) as [->|Hne]; [|split; assumption].
  unfold loaded_history. destruct (active (history old fe)) eqn:Hactive; [split; assumption|].
  apply push_good; [exact Hbound|exact Hordered|intros _; exact Hactive].
Qed.

Lemma good_map time f : (∀ fe, invalidate_good (f fe) time) →
  keeps (good time) (mset TLB.vatlb (TLB.VATLB.map_fe f)).
Proof. intro Hf. apply keeps_set. intros old Hold. apply history_map_good; assumption. Qed.

Lemma good_alter time tlbi fe : keeps (good time) (mset TLB.vatlb (alter (invalidate time tlbi) fe)).
Proof. apply keeps_set. intros old Hold. apply history_alter_good; [apply invalidate_is_good|exact Hold]. Qed.

Local Opaque TLB.fill_entry.
Ltac solve_good :=
  first [apply keeps_ret | apply keeps_get | apply keeps_lift
    | apply keeps_throw | apply keeps_othrow | apply keeps_guard | apply keeps_guard_unit
    | apply good_fill_entry | apply good_alter
    | apply keeps_bind; [solve_good|intro; solve_good]
    | apply keeps_fmap; solve_good | apply keeps_mapM; intro; solve_good
    | match goal with |- keeps _ (match ?x with _ => _ end) => destruct x; solve_good end].

Lemma good_set_index time f : keeps (good time) (mset TLB.next_table_cache f).
Proof. apply keeps_set. intros old Hold. exact Hold. Qed.

Lemma good_fill_root imem mem time roots : keeps (good time) (TLB.fill_root imem mem time roots).
Proof. unfold TLB.fill_root. solve_good. Qed.
Lemma good_fill_from_entry imem mem time entry : keeps (good time) (TLB.fill_from_entry imem mem time entry).
Proof. unfold TLB.fill_from_entry. solve_good. Qed.
Lemma good_fill_from_entries imem mem time entries : keeps (good time) (TLB.fill_from_entries imem mem time entries).
Proof.
  unfold TLB.fill_from_entries, TLB.fill_from_entries_step.
  do 3 (apply keeps_bind; [apply keeps_fmap, keeps_mapM; intro; apply good_fill_from_entry|intro]).
  apply keeps_guard_unit.
Qed.
Lemma good_fill_from_roots imem mem time roots : keeps (good time) (TLB.fill_from_roots imem mem time roots).
Proof.
  unfold TLB.fill_from_roots. apply keeps_bind; [apply good_fill_root|intro; apply good_fill_from_entries].
Qed.
Lemma good_relevant time asids page : keeps (good time) (TLB.get_relevant_entries asids page).
Proof. unfold TLB.get_relevant_entries. solve_good. Qed.

Local Opaque TLB.fill_root TLB.fill_from_entry TLB.fill_from_entries TLB.fill_from_roots TLB.get_relevant_entries.

Lemma good_fill_write imem mem time roots msg : keeps (good time) (TLB.fill_write imem mem time roots msg).
Proof.
  unfold TLB.fill_write. unfold guard_or.
  destruct (decide _); [|apply keeps_throw].
  apply keeps_bind; [apply keeps_ret|intro].
  apply keeps_bind; [apply good_fill_root|intro].
  apply keeps_bind; [apply good_relevant|intro]. apply good_fill_from_entries.
Qed.

Lemma good_fill_tlbi imem mem time roots tlbi : keeps (good time) (TLB.fill_tlbi imem mem time roots tlbi).
Proof.
  destruct (TLBI.last tlbi) eqn:Hlast.
  - intros old new value Hgood Hrun. rewrite last_shape in Hrun by exact Hlast. revert Hgood Hrun.
    apply keeps_bind; [|intro; apply good_fill_from_entries].
    apply keeps_fmap, keeps_mapM. intro entry. unfold step.
    apply keeps_bind; [apply good_alter|intro; apply good_relevant].
  - unfold TLB.fill_tlbi. rewrite Hlast.
    apply keeps_bind; [|intro; apply good_fill_from_roots].
    apply good_map. intro fe. split.
    + destruct (decide (TLB.affects tlbi fe)); reflexivity.
    + intros events Hordered Hbound. destruct (decide (TLB.affects tlbi fe)); [|split; assumption].
      apply (invalidate_is_good time tlbi); assumption.
Qed.

Lemma good_fill_event tid imem mem time roots ev : keeps (good time) (TLB.fill_event tid imem mem time roots ev).
Proof.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch]; [apply good_fill_write|].
  destruct (decide (tid = recipient)); [apply good_fill_tlbi|apply keeps_ret].
Qed.

Local Opaque TLB.fill_write TLB.fill_tlbi TLB.fill_event.

Lemma ordered_head_bound event stamp rest : ordered ((event, stamp) :: rest) → bounded stamp rest.
Proof.
  revert event stamp. induction rest as [|[event' stamp'] rest IH]; intros event stamp Hordered;
    [constructor|].
  destruct Hordered as [[Hstamp _] Hrest]. constructor; [exact Hstamp|].
  eapply bounded_mono; [exact Hstamp|]. eapply IH. exact Hrest.
Qed.

Lemma filter_bounded time (events : TLB.Entry.events) :
  bounded time events → filter (λ '(_, stamp), stamp ≤ time) events = events.
Proof.
  induction events as [|[event stamp] events IH]; intro Hbound; [reflexivity|].
  apply Forall_cons_1 in Hbound as [Hstamp Hbound]. rewrite filter_cons.
  rewrite decide_True by exact Hstamp. rewrite IH by exact Hbound. reflexivity.
Qed.

Lemma past_good bound time events : ordered events → bounded bound events →
  ordered (filter (λ '(_, stamp), stamp ≤ time) events) ∧
  bounded time (filter (λ '(_, stamp), stamp ≤ time) events).
Proof.
  induction events as [|[event stamp] events IH]; intros Hordered Hbound; [split; constructor|].
  split.
  - rewrite filter_cons. destruct (decide (stamp ≤ time)) as [Hle|Hgt].
    + rewrite filter_bounded; [exact Hordered|].
      eapply bounded_mono; [exact Hle|]. eapply ordered_head_bound. exact Hordered.
    + apply IH; [destruct events as [|[] events]; [exact I|apply Hordered]|].
      apply Forall_cons_1 in Hbound as [_ Hbound]. exact Hbound.
  - unfold bounded. apply Forall_forall. intros [event' stamp'] Hin.
    apply list_elem_of_In, list_elem_of_filter in Hin as [Hle _]. exact Hle.
Qed.

Lemma good_roll_back bound time cache cache' :
  good bound cache → TLB.roll_back time cache = Ok (cache', ()) → good time cache'.
Proof.
  intros Hgood Hrun. change (@Ok string _ (set TLB.vatlb
    (TLB.VATLB.map_fe (λ _, filter (λ '(_, stamp), stamp ≤ time))) cache, ()) = Ok (cache', ())) in Hrun.
  injection Hrun as <-. intro fe. rewrite VMCacheEvents.history_map by reflexivity.
  destruct (Hgood fe) as [Hordered Hbound]. eapply past_good; eassumption.
Qed.

Lemma good_rolled bound time cache : good bound cache → good time (VMCacheExchange.rolled time cache).
Proof. intro Hgood. eapply good_roll_back; [exact Hgood|reflexivity]. Qed.

Theorem good_fill_from_btw tid imem fullmem roots tmin tmax mem bound cache cache' :
  bound < tmin → good bound cache →
  TLB.fill_from_btw tid imem fullmem roots tmin tmax mem cache = Ok (cache', ()) →
  good (bound `max` tmax) cache'.
Proof.
  revert roots mem cache cache'. induction tmax as [|tmax IH];
    intros roots mem cache cache' Hmin Hgood Hrun; cbn [TLB.fill_from_btw] in Hrun;
    destruct (decide (_ < _)) as [Hlt|Hge].
  - change (@Ok string _ (cache, ()) = Ok (cache', ())) in Hrun. injection Hrun as <-.
    eapply good_mono; [|exact Hgood]. lia.
  - discriminate.
  - change (@Ok string _ (cache, ()) = Ok (cache', ())) in Hrun. injection Hrun as <-.
    eapply good_mono; [|exact Hgood]. lia.
  - destruct mem as [|ev mem]; [discriminate|].
    unfold mbind, st_bind, result_bind in Hrun.
    set (active_roots := filter (λ '(_, time), time < S tmax) roots) in *.
    set (added_roots := filter (λ '(_, time), time = S tmax) roots) in *.
    destruct (TLB.fill_from_btw tid imem fullmem active_roots tmin tmax mem cache)
      as [[mid []]|err] eqn:Hprefix; [|discriminate]. cbn in Hrun.
    destruct (TLB.fill_event tid imem fullmem (S tmax) active_roots.*1 ev mid)
      as [[next []]|err] eqn:Hstep; [|discriminate]. cbn in Hrun.
    pose proof (IH active_roots mem cache mid Hmin Hgood Hprefix) as Hmid.
    assert (Hnext : good (S tmax) next).
    { eapply good_fill_event; [|exact Hstep]. eapply good_mono; [|exact Hmid]. lia. }
    replace (bound `max` S tmax) with (S tmax) by lia.
    eapply good_fill_from_roots; [exact Hnext|exact Hrun].
Qed.

Theorem good_fill_cse tid imem mem time ttbr0 ttbr1 bound cache cache' :
  good bound cache → TLB.fill_cse tid imem mem time ttbr0 ttbr1 cache = Ok (cache', ()) →
  good (time `max` length mem) cache'.
Proof.
  intros Hgood Hrun.
  set (roots := if ttbr1 is Some upper then
    [(bv_extract 48 16 ttbr0, ttbr0, false, time); (bv_extract 48 16 ttbr0, upper, true, time)]
    else [(bv_extract 48 16 ttbr0, ttbr0, false, time)]).
  change (TLB.fill_from_btw tid imem mem roots (S time) (length mem) mem
    (setv TLB.asid_roots roots (VMCacheExchange.rolled time cache)) = Ok (cache', ())) in Hrun.
  assert (Hstart : good time (setv TLB.asid_roots roots (VMCacheExchange.rolled time cache)))
    by exact (good_rolled bound time cache Hgood).
  eapply good_fill_from_btw; [|exact Hstart|exact Hrun]. lia.
Qed.

Theorem good_fill_asid_root tid imem mem root time bound cache cache' :
  good bound cache → TLB.fill_asid_root tid imem mem root time cache = Ok (cache', ()) →
  good (time `max` length mem) cache'.
Proof.
  intros Hgood Hrun.
  set (before := set TLB.asid_roots (cons (root, time)) (VMCacheExchange.rolled time cache)).
  change ((TLB.fill_from_roots imem mem time [root] before ≫=
    λ '(mid, _), TLB.fill_from_btw tid imem mem (TLB.asid_roots mid)
      (S time) (length mem) mem mid) = Ok (cache', ())) in Hrun.
  unfold mbind, st_bind, result_bind in Hrun.
  destruct (TLB.fill_from_roots imem mem time [root] before) as [[filled []]|err] eqn:Hfill;
    [|discriminate].
  assert (Hfilled : good time filled).
  { eapply good_fill_from_roots; [|exact Hfill]. exact (good_rolled bound time cache Hgood). }
  eapply good_fill_from_btw; [|exact Hfilled|exact Hrun]. lia.
Qed.

Theorem good_fill_promise tid imem mem ev bound cache cache' :
  bound ≤ length mem → good bound cache →
  TLB.fill_promise tid imem mem ev cache = Ok (cache', ()) → good (length mem) cache'.
Proof.
  intros Hbound Hgood Hrun. unfold TLB.fill_promise in Hrun.
  unfold mbind, st_bind, result_bind in Hrun. cbn in Hrun.
  eapply good_fill_event; [|exact Hrun]. eapply good_mono; eassumption.
Qed.

Theorem good_init tid imem iregs cache : TLB.init tid imem iregs = Ok cache → good 0 cache.
Proof.
  unfold TLB.init, guard_or, othrow, mbind, result_bind, fmap, result_fmap.
  destruct (reg_lookup TCR_EL1 iregs) as [tcr|]; [|discriminate]. cbn.
  match goal with |- context[match ?d with left _ => _ | right _ => _ end] => destruct d end;
    cbn; [|discriminate].
  destruct (reg_lookup TTBR0_EL1 iregs) as [ttbr0|]; [|discriminate]. cbn.
  destruct (TLB.get_ets iregs) as [ets|]; [|discriminate]. cbn.
  match goal with |- context[TLB.fill_from_roots ?i ?m ?t ?rs ?st] =>
    destruct (TLB.fill_from_roots i m t rs st) as [[ending []]|err] eqn:Hrun end;
    [|discriminate]. cbn. intro Hcache. injection Hcache as <-.
  eapply good_fill_from_roots; [|exact Hrun].
  intro fe. unfold history. cbn [TLB.vatlb]. rewrite VMCacheIndexed.lookup_init. split; constructor.
Qed.

End VMCacheOrder.
