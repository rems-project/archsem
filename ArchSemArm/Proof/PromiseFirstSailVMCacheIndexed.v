(******************************************************************************)
(* Coherence of the physical-page index with allocated table entries          *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache
  PromiseFirstSailVMCacheIndex PromiseFirstSailVMCacheRefill.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheIndexed.
Import VMPromising VMCacheReplay VMCacheRefill.
#[local] Existing Instance TLB.Decision_affects.
Local Notation action A := (stateT TLB.t (result string) A).

Definition valid (cache : TLB.t) := ∀ page,
  NoDup (TLB.next_table_cache cache !!! page) ∧
  ∀ fe, fe ∈ TLB.next_table_cache cache !!! page ↔
    TLB.FE.is_table fe ∧ TLB.FE.next_table fe = page ∧ is_Some (TLB.vatlb cache !! fe).

Lemma same_domain old new :
  TLB.next_table_cache old = TLB.next_table_cache new →
  (∀ fe, is_Some (TLB.vatlb old !! fe) ↔ is_Some (TLB.vatlb new !! fe)) →
  valid old → valid new.
Proof.
  intros Hindex Hdomain Hvalid page. destruct (Hvalid page) as [Hunique Hentries].
  split; [rewrite <- Hindex; exact Hunique|]. intro fe. rewrite <- Hindex. specialize (Hentries fe). specialize (Hdomain fe). tauto.
Qed.

Lemma set_existing cache fe events old_events :
  valid cache → TLB.vatlb cache !! fe = Some old_events →
  valid (setv TLB.vatlb (partial_alter (λ _, Some events) fe (TLB.vatlb cache)) cache).
Proof.
  intros Hvalid Hlookup. eapply same_domain with (old := cache); [reflexivity| |exact Hvalid].
  intro query. cbn [TLB.vatlb]. rewrite lookup_set.
  destruct (decide (query = fe)) as [->|Hne]; [rewrite Hlookup; split; eexists; reflexivity|reflexivity].
Qed.

Lemma set_fresh_leaf cache fe events :
  valid cache → ¬ TLB.FE.is_table fe →
  valid (setv TLB.vatlb (partial_alter (λ _, Some events) fe (TLB.vatlb cache)) cache).
Proof.
  intros Hvalid Hleaf page. destruct (Hvalid page) as [Hunique Hentries].
  split; [exact Hunique|]. intro query. cbn [TLB.vatlb TLB.next_table_cache].
  rewrite lookup_set. specialize (Hentries query).
  destruct (decide (query = fe)) as [->|Hne]; tauto.
Qed.

Lemma set_fresh_table cache fe events :
  valid cache → TLB.vatlb cache !! fe = None → TLB.FE.is_table fe →
  valid (set TLB.next_table_cache (alter_default (fe ::.) (TLB.FE.next_table fe))
    (setv TLB.vatlb (partial_alter (λ _, Some events) fe (TLB.vatlb cache)) cache)).
Proof.
  intros Hvalid Hnone Htable page. destruct (Hvalid page) as [Hunique Hentries].
  cbn [TLB.next_table_cache TLB.vatlb].
  rewrite lookup_total_lookup. unfold alter_default. rewrite lookup_partial_alter.
  destruct (decide (TLB.FE.next_table fe = page)) as [Hpage|Hpage].
  - try rewrite decide_True by exact Hpage. cbn [default].
    rewrite Hpage. rewrite <- lookup_total_lookup.
    change (NoDup (fe :: TLB.next_table_cache cache !!! page) ∧
      ∀ query, query ∈ fe :: TLB.next_table_cache cache !!! page ↔
        TLB.FE.is_table query ∧ TLB.FE.next_table query = page ∧
        is_Some ((partial_alter (λ _, Some events) fe (TLB.vatlb cache)) !! query)).
    split.
    + apply list.NoDup_cons. split; [|exact Hunique]. intro Hin.
      apply Hentries in Hin as [_ [_ Hallocated]]. rewrite Hnone in Hallocated. destruct Hallocated as [? Hbad]. discriminate.
    + intro query. rewrite lookup_set. specialize (Hentries query).
      pose proof (elem_of_cons (TLB.next_table_cache cache !!! page) query fe) as Hcons.
      destruct (decide (query = fe)) as [->|Hne].
      * assert (is_Some (Some events)) by (eexists; reflexivity).
        assert (fe = fe) by reflexivity. tauto.
      * tauto.
  - try rewrite decide_False by exact Hpage. rewrite <- lookup_total_lookup. split; [exact Hunique|].
    intro query. rewrite lookup_set. specialize (Hentries query).
    destruct (decide (query = fe)) as [->|Hne]; tauto.
Qed.

Lemma fill_entry time fe old new loaded :
  valid old → TLB.fill_entry time fe old = Ok (new, loaded) → valid new.
Proof.
  intros Hvalid Hfill. unfold TLB.fill_entry in Hfill. cbn in Hfill. unfold mget in Hfill.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose in Hfill. cbn in Hfill.
  destruct (TLB.vatlb old !! fe) as [events|] eqn:Hlookup; rewrite Hlookup in Hfill.
  - destruct events as [|[event stamp] rest].
    + unfold mret, result_ret in Hfill. injection Hfill as <- <-. eapply set_existing; eassumption.
    + destruct event; unfold mret, result_ret in Hfill; injection Hfill as <- <-;
        [exact Hvalid|eapply set_existing; eassumption].
  - destruct (decide (TLB.FE.is_table fe)) as [Htable|Htable];
      unfold mret, result_ret, mbind, result_bind in Hfill; cbn in Hfill;
      injection Hfill as <- <-.
    + apply set_fresh_table; assumption.
    + apply set_fresh_leaf; assumption.
Qed.

Lemma map_vatlb f cache : valid cache → valid (set TLB.vatlb (TLB.VATLB.map_fe f) cache).
Proof.
  intro Hvalid. eapply same_domain with (old := cache); [reflexivity| |exact Hvalid]. intro fe. cbn [TLB.vatlb].
  rewrite VMCacheIndex.lookup_map_fe. destruct (TLB.vatlb cache !! fe) as [events|];
    [split; eexists; reflexivity|reflexivity].
Qed.

Lemma lookup_assoc_alter {K V} `{EqDecision K} (f : V → V) key (entries : list (K * V)) query :
  lookup_assoc query (partial_alter_assoc (fmap f) key entries) =
    if decide (query = key) then f <$> lookup_assoc query entries else lookup_assoc query entries.
Proof.
  induction entries as [|[first value] entries IH]; cbn [partial_alter_assoc lookup_assoc].
  - destruct (decide (query = key)); reflexivity.
  - destruct (decide (key = first)) as [->|Hkey]; cbn [fmap option_fmap option_map lookup_assoc].
    + destruct (decide (query = first)); reflexivity.
    + destruct (decide (query = first)) as [->|Hquery].
      * rewrite decide_False by congruence. reflexivity.
      * exact IH.
Qed.

Lemma alter_domain (cache : TLB.VATLB.t) (fe : TLB.FE.t) (f : TLB.Entry.events → TLB.Entry.events) (query : TLB.FE.t) :
  is_Some ((alter f fe cache) !! query) ↔ is_Some (cache !! query).
Proof.
  destruct fe as [ctxt entry], query as [other queried].
  unfold alter, alter_default, partial_alter, TLB.VATLB.partial_alter_fe, lookup, TLB.VATLB.lookup_fe.
  cbn [TLB.FE.ctxt TLB.FE.entry projT1 projT2].
  destruct (decide (ctxt = other)) as [<-|Hctxt].
  - rewrite get_alter_entries_same, lookup_assoc_alter. cbn [TLB.FE.entry TLB.FE.ctxt TLB.FE.lvl projT1 projT2].
    destruct (decide (queried = entry)) as [Heq|Hne];
      [rewrite decide_True by exact Heq|rewrite decide_False by exact Hne; reflexivity].
    change (is_Some (f <$> lookup_assoc queried (TLB.VATLB.get ctxt cache)) ↔
      is_Some (lookup_assoc queried (TLB.VATLB.get ctxt cache))).
    destruct (lookup_assoc queried (TLB.VATLB.get ctxt cache)); [split; eexists; reflexivity|reflexivity].
  - rewrite get_alter_entries_other by exact Hctxt. reflexivity.
Qed.

Lemma alter_vatlb f fe cache : valid cache → valid (set TLB.vatlb (alter f fe) cache).
Proof.
  intro Hvalid. eapply same_domain with (old := cache); [reflexivity| |exact Hvalid]. intro query.
  symmetry. apply alter_domain.
Qed.


Definition preserves {A} (run : action A) :=
  ∀ old new value, valid old → run old = Ok (new, value) → valid new.
Lemma preserves_ret {A} (value : A) : preserves (mret value).
Proof.
  intros old new result Hvalid Hrun. change (@Ok string _ (old, value) = Ok (new, result)) in Hrun.
  injection Hrun as <- <-. exact Hvalid.
Qed.
Lemma preserves_bind {A B} (run : action A) (next : A → action B) :
  preserves run → (∀ value, preserves (next value)) → preserves (run ≫= next).
Proof.
  intros Hfirst Hnext old new result Hvalid Hrun.
  unfold mbind, st_bind, result_bind in Hrun.
  destruct (run old) as [[mid value]|err] eqn:Hmid; [|discriminate].
  eapply Hnext; [eapply Hfirst; eassumption|exact Hrun].
Qed.
Lemma preserves_fmap {A B} (f : A → B) (run : action A) : preserves run → preserves (f <$> run).
Proof.
  intros Hfirst old new result Hvalid Hrun. unfold fmap, st_fmap, result_fmap in Hrun.
  destruct (run old) as [[mid value]|err] eqn:Hmid; [|discriminate].
  injection Hrun as <- <-. eapply Hfirst; eassumption.
Qed.
Lemma preserves_get {A} (proj : TLB.t → A) : preserves (mget proj).
Proof.
  intros old new result Hvalid Hrun. change (@Ok string _ (old, proj old) = Ok (new, result)) in Hrun.
  injection Hrun as <- <-. exact Hvalid.
Qed.
Lemma preserves_set {A} (proj : TLB.t → A) `{Setter _ _ proj} (f : A → A) :
  (∀ old, valid old → valid (set proj f old)) → preserves (mset proj f).
Proof.
  intros Hf old new result Hvalid Hrun. destruct result.
  change (@Ok string _ (set proj f old, ()) = Ok (new, ())) in Hrun.
  injection Hrun as <-. apply Hf, Hvalid.
Qed.
Lemma preserves_lift {A} (run : result string A) : preserves (mlift run).
Proof.
  destruct run as [value|err]; intros old new result Hvalid Hrun; [|discriminate].
  change (@Ok string _ (old, value) = Ok (new, result)) in Hrun. injection Hrun as <- <-. exact Hvalid.
Qed.
Lemma preserves_throw {A} (err : string) : preserves (mthrow err : action A).
Proof. intros old new value Hvalid Hrun. discriminate. Qed.
Lemma preserves_othrow {A} (err : string) (opt : option A) : preserves (othrow err opt).
Proof. destruct opt; [apply preserves_ret|apply preserves_throw]. Qed.
Lemma preserves_guard (err : string) (P : Prop) `{Decision P} : preserves (guard_or err P).
Proof. unfold guard_or. destruct (decide P); [apply preserves_ret|apply preserves_throw]. Qed.
Lemma preserves_guard_unit (err : string) (P : Prop) `{Decision P} : preserves (guard_or' err P).
Proof. unfold guard_or'. apply preserves_bind; [apply preserves_guard|intro; apply preserves_ret]. Qed.
Lemma preserves_mapM {A B} (f : A → action B) xs :
  (∀ x, preserves (f x)) → preserves (mapM f xs).
Proof.
  intro Hf. induction xs; cbn [mapM]; [apply preserves_ret|].
  apply preserves_bind; [apply Hf|]. intro value.
  apply preserves_bind; [exact IHxs|]. intro values. apply preserves_ret.
Qed.
Lemma preserves_fill_entry time fe : preserves (TLB.fill_entry time fe).
Proof. exact (fill_entry time fe). Qed.
Lemma preserves_map_fe f : preserves (mset TLB.vatlb (TLB.VATLB.map_fe f)).
Proof. apply preserves_set, map_vatlb. Qed.
Lemma preserves_alter f fe : preserves (mset TLB.vatlb (alter f fe)).
Proof. apply preserves_set, alter_vatlb. Qed.

Local Opaque TLB.fill_entry.
Ltac solve_index :=
  first [apply preserves_ret | apply preserves_get | apply preserves_lift
    | apply preserves_throw | apply preserves_othrow | apply preserves_guard | apply preserves_guard_unit
    | apply preserves_fill_entry | apply preserves_map_fe | apply preserves_alter
    | apply preserves_bind; [solve_index|intro; solve_index]
    | apply preserves_fmap; solve_index | apply preserves_mapM; intro; solve_index
    | match goal with |- preserves (match ?x with _ => _ end) => destruct x; solve_index end].
Lemma fill_root imem mem time roots : preserves (TLB.fill_root imem mem time roots).
Proof. unfold TLB.fill_root. solve_index. Qed.
Lemma fill_from_entry imem mem time entry : preserves (TLB.fill_from_entry imem mem time entry).
Proof. unfold TLB.fill_from_entry. solve_index. Qed.
Lemma fill_from_entries_step imem mem time entries : preserves (TLB.fill_from_entries_step imem mem time entries).
Proof. unfold TLB.fill_from_entries_step. apply preserves_fmap, preserves_mapM. intro; apply fill_from_entry. Qed.
Lemma fill_from_entries imem mem time entries : preserves (TLB.fill_from_entries imem mem time entries).
Proof.
  unfold TLB.fill_from_entries.
  do 3 (apply preserves_bind; [apply fill_from_entries_step|intro]). apply preserves_guard_unit.
Qed.
Lemma fill_from_roots imem mem time roots : preserves (TLB.fill_from_roots imem mem time roots).
Proof. unfold TLB.fill_from_roots. apply preserves_bind; [apply fill_root|intro; apply fill_from_entries]. Qed.
Lemma relevant_entries asids page : preserves (TLB.get_relevant_entries asids page).
Proof. unfold TLB.get_relevant_entries. solve_index. Qed.
Local Opaque TLB.fill_root TLB.fill_from_entry TLB.fill_from_entries TLB.fill_from_roots TLB.get_relevant_entries.
Ltac solve_fill_index :=
  first [apply fill_root | apply fill_from_entry | apply fill_from_entries
    | apply fill_from_roots | apply relevant_entries | solve_index
    | apply preserves_bind; [solve_fill_index|intro; solve_fill_index]
    | apply preserves_fmap; solve_fill_index | apply preserves_mapM; intro; solve_fill_index
    | match goal with |- preserves (match ?x with _ => _ end) => destruct x; solve_fill_index end].
Lemma fill_write imem mem time roots msg : preserves (TLB.fill_write imem mem time roots msg).
Proof. unfold TLB.fill_write. solve_fill_index. Qed.
Lemma fill_tlbi imem mem time roots tlbi : preserves (TLB.fill_tlbi imem mem time roots tlbi).
Proof. unfold TLB.fill_tlbi. solve_fill_index. Qed.
Lemma fill_event tid imem mem time roots ev : preserves (TLB.fill_event tid imem mem time roots ev).
Proof.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch]; [apply fill_write|].
  destruct (decide (tid = recipient)); [apply fill_tlbi|apply preserves_ret].
Qed.
Lemma fill_promise tid imem mem ev : preserves (TLB.fill_promise tid imem mem ev).
Proof. unfold TLB.fill_promise. apply preserves_bind; [apply preserves_get|intro; apply fill_event]. Qed.
Lemma roll_back time : preserves (TLB.roll_back time).
Proof. unfold TLB.roll_back. apply preserves_map_fe. Qed.
Lemma roots f : preserves (mset TLB.asid_roots f).
Proof.
  apply preserves_set. intros cache Hvalid. eapply same_domain with (old := cache); [reflexivity|intro; reflexivity|exact Hvalid].
Qed.
Lemma fill_from_btw tid imem fullmem roots tmin tmax mem : preserves (TLB.fill_from_btw tid imem fullmem roots tmin tmax mem).
Proof.
  revert roots mem. induction tmax as [|tmax IH]; intros roots mem;
    cbn [TLB.fill_from_btw]; destruct (decide (_ < _)); try apply preserves_ret.
  - apply preserves_throw.
  - destruct mem; [apply preserves_throw|].
    apply preserves_bind; [apply IH|]. intro.
    apply preserves_bind; [apply fill_event|intro; apply fill_from_roots].
Qed.
Lemma fill_cse tid imem mem time ttbr0 ttbr1 : preserves (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  unfold TLB.fill_cse, TLB.fill_from. apply preserves_bind; [apply roll_back|]. intro.
  apply preserves_bind; [unfold msetv; apply roots|intro; apply fill_from_btw].
Qed.
Lemma fill_asid_root tid imem mem root time : preserves (TLB.fill_asid_root tid imem mem root time).
Proof.
  unfold TLB.fill_asid_root, TLB.fill_from. apply preserves_bind; [apply roll_back|]. intro.
  apply preserves_bind; [apply roots|]. intro.
  apply preserves_bind; [apply fill_from_roots|]. intro.
  apply preserves_bind; [apply preserves_get|intro; apply fill_from_btw].
Qed.


Lemma lookup_init fe : (TLB.VATLB.init !! fe) = None.
Proof.
  unfold lookup, TLB.VATLB.lookup_fe, TLB.VATLB.get, TLB.VATLB.init.
  rewrite hvec_get_func. reflexivity.
Qed.

Lemma empty_valid present roots ets : valid (TLB.make TLB.VATLB.init present ∅ roots ets).
Proof.
  intro page. cbn [TLB.next_table_cache TLB.vatlb]. rewrite lookup_total_empty.
  split; [constructor|]. intro fe. rewrite lookup_init. split.
  - intro Hmember. apply not_elem_of_nil in Hmember. contradiction.
  - intros [_ [_ [events Hnone]]]. discriminate.
Qed.

Theorem init tid imem iregs cache : TLB.init tid imem iregs = Ok cache → valid cache.
Proof.
  unfold TLB.init, guard_or, othrow, mbind, result_bind, fmap, result_fmap.
  destruct (reg_lookup TCR_EL1 iregs) as [tcr|]; [|discriminate]. cbn.
  match goal with |- context[match ?d with left _ => _ | right _ => _ end] => destruct d end;
    cbn; [|discriminate].
  destruct (reg_lookup TTBR0_EL1 iregs) as [ttbr0|]; [|discriminate]. cbn.
  destruct (TLB.get_ets iregs) as [ets|]; [|discriminate]. cbn.
  set (roots := if reg_lookup TTBR1_EL1 iregs is Some ttbr1 then
    [(bv_extract 48 16 ttbr0, ttbr0, false, 0); (bv_extract 48 16 ttbr0, ttbr1, true, 0)]
    else [(bv_extract 48 16 ttbr0, ttbr0, false, 0)]).
  change ((fst <$> TLB.fill_from_roots imem [] 0 roots.*1
    (TLB.make TLB.VATLB.init (TLB.get_pte_present imem) ∅ roots ets)) = Ok cache → valid cache).
  unfold fmap, result_fmap.
  match goal with |- context[TLB.fill_from_roots ?i ?m ?t ?rs ?st] =>
    destruct (TLB.fill_from_roots i m t rs st) as [[ending []]|err] eqn:Hrun end;
    [|discriminate]. cbn. intro Hcache. injection Hcache as <-.
  eapply fill_from_roots; [apply empty_valid|exact Hrun].
Qed.


Definition relevant cache asids page :=
  filter (λ fe, TLB.VATLB.is_active (TLB.vatlb cache) fe ∧ TLB.FE.is_active_asid asids fe)
    (TLB.next_table_cache cache !!! page).

Lemma relevant_run cache asids page :
  TLB.get_relevant_entries asids page cache = Ok (cache, relevant cache asids page).
Proof. reflexivity. Qed.

Lemma is_active_history cache fe :
  TLB.VATLB.is_active (TLB.vatlb cache) fe = active (history cache fe).
Proof. unfold TLB.VATLB.is_active, active, history. destruct (TLB.vatlb cache !! fe); reflexivity. Qed.

Lemma active_allocated cache fe : active (history cache fe) → is_Some (TLB.vatlb cache !! fe).
Proof.
  unfold history. destruct (TLB.vatlb cache !! fe) as [events|] eqn:Hlookup.
  - intro. eexists. reflexivity.
  - intro Hactive. change False in Hactive. contradiction.
Qed.

Lemma relevant_member cache asids page fe : valid cache →
  (fe ∈ relevant cache asids page ↔
    TLB.FE.is_table fe ∧ TLB.FE.next_table fe = page ∧
    active (history cache fe) ∧ TLB.FE.is_active_asid asids fe).
Proof.
  intro Hvalid. destruct (Hvalid page) as [_ Hentries]. unfold relevant. split.
  - intro Hin. apply list_elem_of_filter in Hin as [[Hactive Hasid] Hin].
    apply Hentries in Hin as [Htable [Hpage _]]. rewrite is_active_history in Hactive. tauto.
  - intros [Htable [Hpage [Hactive Hasid]]]. apply list_elem_of_filter. split.
    + rewrite is_active_history. auto.
    + apply Hentries. split; [exact Htable|]. split; [exact Hpage|apply active_allocated, Hactive].
Qed.

Theorem relevant_permutation old new asids page :
  valid old → valid new → equiv old new → relevant old asids page ≡ₚ relevant new asids page.
Proof.
  intros Hold Hnew [_ Hhist]. apply list.NoDup_Permutation.
  - unfold relevant. apply list.NoDup_filter. exact (proj1 (Hold page)).
  - unfold relevant. apply list.NoDup_filter. exact (proj1 (Hnew page)).
  - intro fe. pose proof (relevant_member old asids page fe Hold) as Hleft.
    pose proof (relevant_member new asids page fe Hnew) as Hright.
    rewrite Hhist in Hleft. tauto.
Qed.

End VMCacheIndexed.
