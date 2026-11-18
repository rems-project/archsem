(******************************************************************************)
(* Rebuilding tables with different sets of dormant cache allocations         *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache
  PromiseFirstSailVMCacheConfig PromiseFirstSailVMCacheIndex.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheRefill.
Import VMPromising VMCacheReplay.
Local Notation action A := (stateT TLB.t (result string) A).

Definition history (cache : TLB.t) fe := default [] (TLB.vatlb cache !! fe).
Definition active (events : TLB.Entry.events) : bool :=
  if events is (TLB.Entry.Load, _) :: _ then true else false.
Definition equiv (old new : TLB.t) :=
  TLB.pte_present old = TLB.pte_present new ∧ ∀ fe, history old fe = history new fe.

Lemma equiv_refl cache : equiv cache cache.
Proof. split; intros; reflexivity. Qed.
Lemma equiv_sym old new : equiv old new → equiv new old.
Proof. intros [Hconfig Hhist]. split; [symmetry; exact Hconfig|intro; symmetry; apply Hhist]. Qed.
Lemma equiv_trans old mid new : equiv old mid → equiv mid new → equiv old new.
Proof. intros [Hc1 Hh1] [Hc2 Hh2]. split; [congruence|intro; rewrite Hh1; apply Hh2]. Qed.

Lemma lookup_assoc_set {K V} `{EqDecision K} (entries : list (K * V)) key value query :
  lookup_assoc query (partial_alter_assoc (λ _, Some value) key entries) =
    if decide (query = key) then Some value else lookup_assoc query entries.
Proof.
  induction entries as [|[first old] entries IH]; cbn [partial_alter_assoc lookup_assoc].
  - destruct (decide (query = key)); reflexivity.
  - destruct (decide (key = first)) as [->|Hkey]; cbn [lookup_assoc].
    + destruct (decide (query = first)); reflexivity.
    + destruct (decide (query = first)) as [->|Hquery].
      * rewrite decide_False by congruence. reflexivity.
      * exact IH.
Qed.

Lemma lookup_set (cache : TLB.VATLB.t) (fe : TLB.FE.t) (value : TLB.Entry.events) query :
  (partial_alter (λ _, Some value) fe cache) !! query =
    if decide (query = fe) then Some value else cache !! query.
Proof.
  destruct fe as [ctxt entry], query as [other queried].
  unfold partial_alter, TLB.VATLB.partial_alter_fe, lookup, TLB.VATLB.lookup_fe.
  cbn [TLB.FE.ctxt TLB.FE.entry projT1 projT2].
  destruct (decide (ctxt = other)) as [<-|Hctxt].
  - rewrite get_alter_entries_same, lookup_assoc_set.
    destruct (decide (queried = entry)) as [->|Hentry].
    + rewrite !decide_True by reflexivity. reflexivity.
    + rewrite (decide_False (P := queried = entry)) by exact Hentry.
      rewrite decide_False; [reflexivity|]. intro Heq.
      apply (inj (existT ctxt)) in Heq. contradiction.
  - rewrite get_alter_entries_other by exact Hctxt.
    rewrite decide_False; [reflexivity|]. intro Heq.
    apply (f_equal TLB.FE.ctxt) in Heq. cbn in Heq. congruence.
Qed.

Definition loaded_history time events :=
  if active events then events else (TLB.Entry.Load, time) :: events.
Definition load_effect time fe (before after : TLB.t) loaded :=
  TLB.pte_present after = TLB.pte_present before ∧
  loaded = negb (active (history before fe)) ∧
  ∀ query, history after query =
    if decide (query = fe) then loaded_history time (history before fe) else history before query.

Lemma fill_entry_total time fe cache : ∃ next loaded, TLB.fill_entry time fe cache = Ok (next, loaded).
Proof.
  unfold TLB.fill_entry. cbn. unfold mget.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose. cbn.
  destruct (TLB.vatlb cache !! fe) as [events|] eqn:Hlookup; rewrite Hlookup.
  - destruct events as [|[event stamp] rest]; [eexists _, _; reflexivity|].
    destruct event; eexists _, _; reflexivity.
  - destruct (decide (TLB.FE.is_table fe)); eexists _, _; reflexivity.
Qed.

Lemma fill_entry_effect time fe before after loaded :
  TLB.fill_entry time fe before = Ok (after, loaded) → load_effect time fe before after loaded.
Proof.
  intro Hfill. unfold TLB.fill_entry in Hfill. cbn in Hfill. unfold mget in Hfill.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose in Hfill. cbn in Hfill.
  unfold load_effect, history.
  destruct (TLB.vatlb before !! fe) as [events|] eqn:Hlookup; rewrite Hlookup in Hfill.
  - destruct events as [|[event stamp] rest].
    + unfold mret, result_ret in Hfill. injection Hfill as <- <-.
      split; [reflexivity|]. split; [reflexivity|]. intro query. cbn [TLB.vatlb].
      rewrite lookup_set. destruct (decide (query = fe)); reflexivity.
    + destruct event.
      * unfold mret, result_ret in Hfill. injection Hfill as <- <-.
        split; [reflexivity|]. split; [reflexivity|]. intro query.
        destruct (decide (query = fe)) as [->|Hne]; [rewrite Hlookup|]; reflexivity.
      * unfold mret, result_ret in Hfill. injection Hfill as <- <-.
        split; [reflexivity|]. split; [reflexivity|]. intro query. cbn [TLB.vatlb].
        rewrite lookup_set. destruct (decide (query = fe)); reflexivity.
  - destruct (decide (TLB.FE.is_table fe));
      unfold mret, result_ret, mbind, result_bind in Hfill; cbn in Hfill;
      injection Hfill as <- <-.
    all: split; [reflexivity|]; split; [reflexivity|]; intro query; cbn [TLB.vatlb];
      rewrite lookup_set; destruct (decide (query = fe)); reflexivity.
Qed.

(** The output boolean agrees even when one cache has an empty allocation
    for the entry and the other has no allocation yet. *)
Theorem fill_entry_equiv time fe old new old' loaded :
  equiv old new → TLB.fill_entry time fe old = Ok (old', loaded) →
  ∃ new', TLB.fill_entry time fe new = Ok (new', loaded) ∧ equiv old' new'.
Proof.
  intros [Hconfig Hhist] Hold.
  destruct (fill_entry_total time fe new) as [new' [loaded' Hnew]].
  destruct (fill_entry_effect time fe old old' loaded Hold) as [Hc1 [Hl1 Hh1]].
  destruct (fill_entry_effect time fe new new' loaded' Hnew) as [Hc2 [Hl2 Hh2]].
  assert (Hloaded : loaded' = loaded) by (rewrite Hl1, Hl2, Hhist; reflexivity).
  rewrite Hloaded in Hnew.
  exists new'. split; [exact Hnew|]. split; [congruence|]. intro query.
  rewrite Hh1, Hh2, !Hhist. reflexivity.
Qed.

Definition respects {A} (run : action A) :=
  ∀ old new old' value, equiv old new → run old = Ok (old', value) →
    ∃ new', run new = Ok (new', value) ∧ equiv old' new'.

Lemma respects_ret {A} (value : A) : respects (mret value).
Proof.
  intros old new old' result Heq Hrun.
  change (@Ok string _ (old, value) = Ok (old', result)) in Hrun. injection Hrun as <- <-.
  exists new. split; [reflexivity|exact Heq].
Qed.
Lemma respects_bind {A B} (run : action A) (next : A → action B) :
  respects run → (∀ value, respects (next value)) → respects (run ≫= next).
Proof.
  intros Hrun Hnext old new old' result Heq Hresult.
  unfold mbind, st_bind, result_bind in Hresult |- *.
  destruct (run old) as [[mid value]|err] eqn:Hfirst; [|discriminate].
  destruct (Hrun old new mid value Heq Hfirst) as [mid' [Hfirst' Heq']]. rewrite Hfirst'.
  exact (Hnext value mid mid' old' result Heq' Hresult).
Qed.
Lemma respects_fmap {A B} (f : A → B) (run : action A) : respects run → respects (f <$> run).
Proof.
  intros Hrun old new old' result Heq Hresult.
  unfold fmap, st_fmap, result_fmap in Hresult |- *.
  destruct (run old) as [[mid value]|err] eqn:Hfirst; [|discriminate]. injection Hresult as <- <-.
  destruct (Hrun old new mid value Heq Hfirst) as [mid' [Hfirst' Heq']]. rewrite Hfirst'.
  exists mid'. auto.
Qed.
Lemma respects_lift {A} (run : result string A) : respects (mlift run).
Proof.
  destruct run as [value|err]; intros old new old' result Heq Hrun; [|discriminate].
  change (@Ok string _ (old, value) = Ok (old', result)) in Hrun. injection Hrun as <- <-.
  exists new. auto.
Qed.
Lemma respects_throw {A} (err : string) : respects (mthrow err : action A).
Proof. intros old new old' result Heq Hrun. discriminate. Qed.
Lemma respects_othrow {A} (err : string) (opt : option A) : respects (othrow err opt).
Proof. destruct opt; [apply respects_ret|apply respects_throw]. Qed.
Lemma respects_guard (err : string) (P : Prop) `{Decision P} : respects (guard_or err P).
Proof. unfold guard_or. destruct (decide P); [apply respects_ret|apply respects_throw]. Qed.
Lemma respects_guard_unit (err : string) (P : Prop) `{Decision P} : respects (guard_or' err P).
Proof. unfold guard_or'. apply respects_bind; [apply respects_guard|intro; apply respects_ret]. Qed.
Lemma respects_get {A} (proj : TLB.t → A) :
  (∀ old new, equiv old new → proj old = proj new) → respects (mget proj).
Proof.
  intros Hproj old new old' value Heq Hrun.
  change (@Ok string _ (old, proj old) = Ok (old', value)) in Hrun. injection Hrun as <- <-.
  exists new. split; [change (@Ok string _ (new, proj new) = Ok (new, proj old)); rewrite (Hproj old new Heq); reflexivity|exact Heq].
Qed.
Lemma respects_indexes page : respects (mget ((.!!!page) ∘ TLB.pte_present)).
Proof. apply respects_get. intros old new [Hsame _]. unfold compose. rewrite Hsame. reflexivity. Qed.
Lemma respects_mapM {A B} (f : A → action B) xs :
  (∀ x, respects (f x)) → respects (mapM f xs).
Proof.
  intro Hf. induction xs as [|x xs IH]; cbn [mapM]; [apply respects_ret|].
  apply respects_bind; [apply Hf|]. intro value.
  apply respects_bind; [exact IH|]. intro values. apply respects_ret.
Qed.

Lemma respects_fill_entry time fe : respects (TLB.fill_entry time fe).
Proof. exact (fill_entry_equiv time fe). Qed.

Local Opaque TLB.fill_entry.
Ltac solve_refill :=
  first [apply respects_ret | apply respects_lift | apply respects_throw
    | apply respects_othrow | apply respects_guard | apply respects_guard_unit
    | apply respects_indexes | apply respects_fill_entry
    | apply respects_bind; [solve_refill|intro; solve_refill]
    | apply respects_fmap; solve_refill
    | apply respects_mapM; intro; solve_refill
    | match goal with |- respects (match ?x with _ => _ end) => destruct x; solve_refill end].

Theorem fill_root_equiv imem mem time roots : respects (TLB.fill_root imem mem time roots).
Proof. unfold TLB.fill_root. solve_refill. Qed.
Theorem fill_from_entry_equiv imem mem time entry : respects (TLB.fill_from_entry imem mem time entry).
Proof. unfold TLB.fill_from_entry. solve_refill. Qed.
Theorem fill_from_entries_step_equiv imem mem time entries : respects (TLB.fill_from_entries_step imem mem time entries).
Proof.
  unfold TLB.fill_from_entries_step. apply respects_fmap, respects_mapM.
  intro entry. apply fill_from_entry_equiv.
Qed.
Theorem fill_from_entries_equiv imem mem time entries : respects (TLB.fill_from_entries imem mem time entries).
Proof.
  unfold TLB.fill_from_entries.
  do 3 (apply respects_bind; [apply fill_from_entries_step_equiv|intro]).
  apply respects_guard_unit.
Qed.
Theorem fill_from_roots_equiv imem mem time roots : respects (TLB.fill_from_roots imem mem time roots).
Proof.
  unfold TLB.fill_from_roots. apply respects_bind; [apply fill_root_equiv|].
  intro entries. apply fill_from_entries_equiv.
Qed.


Definition load_history time fe (hist : TLB.FE.t → TLB.Entry.events) query :=
  if decide (query = fe) then loaded_history time (hist fe) else hist query.

Lemma load_history_commute time first second hist query :
  load_history time second (load_history time first hist) query =
    load_history time first (load_history time second hist) query.
Proof.
  unfold load_history. repeat case_decide; simplify_eq; try congruence.
Qed.

Theorem fill_two_swap time first second old mid last loaded1 loaded2 :
  first ≠ second →
  TLB.fill_entry time first old = Ok (mid, loaded1) →
  TLB.fill_entry time second mid = Ok (last, loaded2) →
  ∃ mid' last',
    TLB.fill_entry time second old = Ok (mid', loaded2) ∧
    TLB.fill_entry time first mid' = Ok (last', loaded1) ∧ equiv last last'.
Proof.
  intros Hne Hfirst Hsecond.
  destruct (fill_entry_total time second old) as [mid' [loaded2' Hsecond']].
  destruct (fill_entry_total time first mid') as [last' [loaded1' Hfirst']].
  destruct (fill_entry_effect time first old mid loaded1 Hfirst) as [Hc1 [Hl1 Hh1]].
  destruct (fill_entry_effect time second mid last loaded2 Hsecond) as [Hc2 [Hl2 Hh2]].
  destruct (fill_entry_effect time second old mid' loaded2' Hsecond') as [Hc2' [Hl2' Hh2']].
  destruct (fill_entry_effect time first mid' last' loaded1' Hfirst') as [Hc1' [Hl1' Hh1']].
  assert (Hloaded1 : loaded1' = loaded1).
  { rewrite Hl1', Hl1, Hh2', decide_False by exact Hne. reflexivity. }
  assert (Hloaded2 : loaded2' = loaded2).
  { rewrite Hl2', Hl2, Hh1, decide_False by congruence. reflexivity. }
  rewrite Hloaded1 in Hfirst'. rewrite Hloaded2 in Hsecond'.
  exists mid', last'. split; [exact Hsecond'|]. split; [exact Hfirst'|].
  split; [congruence|]. intro query. rewrite Hh2, Hh1'.
  pose proof (load_history_commute time first second (history old) query) as Hcommute.
  unfold load_history in Hcommute.
  rewrite !Hh1, !Hh2'. exact Hcommute.
Qed.

Definition emitted (keep : TLB.FE.t → bool) fe loaded :=
  if loaded && keep fe then [fe] else [].
Fixpoint fill_batch time keep (entries : list TLB.FE.t) : action (list TLB.FE.t) :=
  match entries with
  | [] => mret []
  | entry :: rest =>
      loaded ← TLB.fill_entry time entry;
      emitted_rest ← fill_batch time keep rest;
      mret (emitted keep entry loaded ++ emitted_rest)%list
  end.

Lemma fill_batch_equiv time keep entries : respects (fill_batch time keep entries).
Proof.
  induction entries; cbn [fill_batch]; [apply respects_ret|].
  apply respects_bind; [apply respects_fill_entry|]. intro loaded.
  apply respects_bind; [exact IHentries|]. intro rest. apply respects_ret.
Qed.

Lemma fill_batch_total time keep entries old :
  ∃ new emitted_entries, fill_batch time keep entries old = Ok (new, emitted_entries).
Proof.
  revert old. induction entries as [|entry rest IH]; intro old; [exists old, []; reflexivity|].
  destruct (fill_entry_total time entry old) as [mid [loaded Hfill]].
  destruct (IH mid) as [new [emitted_entries Hrest]].
  exists new, (emitted keep entry loaded ++ emitted_entries)%list.
  cbn [fill_batch]. unfold mbind, st_bind, result_bind. rewrite Hfill. cbn. rewrite Hrest. reflexivity.
Qed.

Theorem fill_batch_permutation time keep entries entries' :
  entries ≡ₚ entries' →
  ∀ old last emitted_entries,
    fill_batch time keep entries old = Ok (last, emitted_entries) →
    ∃ last' emitted_entries',
      fill_batch time keep entries' old = Ok (last', emitted_entries') ∧
      equiv last last' ∧ emitted_entries ≡ₚ emitted_entries'.
Proof.
  intro Hperm. induction Hperm as [|entry entries entries' Hperm IH|
    first second entries|entries middle entries' Hleft IHleft Hright IHright];
    intros old last emitted_entries Hrun.
  - exists last, emitted_entries. split; [exact Hrun|]. split; [apply equiv_refl|apply Permutation_refl].
  - cbn [fill_batch] in Hrun |- *. unfold mbind, st_bind, result_bind in Hrun |- *.
    destruct (TLB.fill_entry time entry old) as [[mid loaded]|err] eqn:Hfirst; [|discriminate]. cbn in Hrun |- *.
    destruct (fill_batch time keep entries mid) as [[ending outputs]|err] eqn:Hrest; [|discriminate]. cbn in Hrun |- *.
    injection Hrun as <- <-.
    destruct (IH mid ending outputs Hrest) as [ending' [outputs' [Hrest' [Heq Houtputs]]]].
    rewrite Hrest'. eexists _, _. split; [reflexivity|]. split; [exact Heq|].
    apply Permutation_app_head, Houtputs.
  - destruct (decide (first = second)) as [->|Hne].
    { exists last, emitted_entries. split; [exact Hrun|]. split; [apply equiv_refl|apply Permutation_refl]. }
    cbn [fill_batch] in Hrun |- *. unfold mbind, st_bind, result_bind in Hrun |- *.
    destruct (TLB.fill_entry time second old) as [[mid loaded2]|err] eqn:Hsecond; [|discriminate]. cbn in Hrun |- *.
    destruct (TLB.fill_entry time first mid) as [[both loaded1]|err] eqn:Hfirst; [|discriminate]. cbn in Hrun |- *.
    destruct (fill_batch time keep entries both) as [[ending outputs]|err] eqn:Hrest; [|discriminate]. cbn in Hrun |- *.
    injection Hrun as <- <-.
    destruct (fill_two_swap time second first old mid both loaded2 loaded1 ltac:(congruence) Hsecond Hfirst)
      as [mid' [both' [Hfirst' [Hsecond' Heq]]]].
    destruct (fill_batch_equiv time keep entries both both' ending outputs Heq Hrest)
      as [ending' [Hrest' Hend]].
    rewrite Hfirst'. cbn. rewrite Hsecond'. cbn. rewrite Hrest'. eexists _, _. split; [reflexivity|]. split; [exact Hend|].
    rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - destruct (IHleft old last emitted_entries Hrun) as [mid [outputs [Hmid [Heq Houtputs]]]].
    destruct (IHright old mid outputs Hmid) as [ending [outputs' [Hend [Heq' Houtputs']]]].
    exists ending, outputs'. split; [exact Hend|]. split.
    + eapply equiv_trans; eassumption.
    + eapply Permutation_trans; eassumption.
Qed.

End VMCacheRefill.
