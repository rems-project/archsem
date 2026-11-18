(******************************************************************************)
(* Replay of local last-level invalidations across dormant allocations        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache PromiseFirstSailVMCacheRefill
  PromiseFirstSailVMCacheTraversal PromiseFirstSailVMCacheIndexed
  PromiseFirstSailVMCacheIndex PromiseFirstSailVMCacheEvents PromiseFirstSailVMCacheExchange.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheLastTLBI.
Import VMPromising VMCacheReplay VMCacheRefill VMCacheTraversal VMCacheEvents.
#[local] Existing Instance TLB.Decision_affects.
Local Notation action A := (stateT TLB.t (result string) A).

(** * Allocated entries are unique within each context *)

Definition unique := VMCacheExchange.unique_entries.

Lemma keys_partial_alter {K V} `{EqDecision K} (f : option V → option V) key
    (entries : list (K * V)) x :
  x ∈ map fst (partial_alter_assoc f key entries) → x ∈ map fst entries ∨ x = key.
Proof.
  induction entries as [|[first value] entries IH]; cbn [partial_alter_assoc].
  - destruct (f None); cbn [map fst]; [set_solver|set_solver].
  - destruct (decide (key = first)) as [->|Hne].
    + destruct (f (Some value)); cbn [map fst]; set_solver.
    + cbn [map fst]. intro Hin. apply elem_of_cons in Hin as [->|Hin]; [left; left|].
      destruct (IH Hin) as [Hold| ->]; [left; right; exact Hold|right; reflexivity].
Qed.

Lemma nodup_partial_alter {K V} `{EqDecision K} (f : option V → option V) key
    (entries : list (K * V)) :
  NoDup (map fst entries) → NoDup (map fst (partial_alter_assoc f key entries)).
Proof.
  induction entries as [|[first value] entries IH]; cbn [partial_alter_assoc map fst]; intro Hunique.
  - destruct (f None); cbn [map fst]; [constructor; [set_solver|constructor]|constructor].
  - apply list.NoDup_cons in Hunique as [Hfresh Hunique].
    destruct (decide (key = first)) as [->|Hne].
    + destruct (f (Some value)); cbn [map fst]; [apply list.NoDup_cons; split|]; assumption.
    + cbn [map fst]. apply list.NoDup_cons. split; [|apply IH, Hunique].
      intro Hin. apply keys_partial_alter in Hin as [Hin|Heq]; [contradiction|congruence].
Qed.

Lemma unique_partial_alter f fe cache :
  unique cache → unique (set TLB.vatlb (partial_alter f fe) cache).
Proof.
  intros Hunique ctxt. cbn [TLB.vatlb]. unfold partial_alter, TLB.VATLB.partial_alter_fe.
  destruct (decide (TLB.FE.ctxt fe = ctxt)) as [<-|Hne].
  - rewrite get_alter_entries_same. apply nodup_partial_alter, Hunique.
  - rewrite get_alter_entries_other by exact Hne. apply Hunique.
Qed.

Lemma unique_map_fe f cache : unique cache → unique (set TLB.vatlb (TLB.VATLB.map_fe f) cache).
Proof.
  intros Hunique ctxt. cbn [TLB.vatlb]. rewrite get_map_fe, VMCacheExchange.map_keys. apply Hunique.
Qed.

Section Keeps.
  Context (I : TLB.t → Prop).
  Definition keeps {A} (run : action A) :=
    ∀ old new value, I old → run old = Ok (new, value) → I new.
  Lemma keeps_ret {A} (value : A) : keeps (mret value).
  Proof.
    intros old new result Hold Hrun. change (@Ok string _ (old, value) = Ok (new, result)) in Hrun.
    injection Hrun as <- <-. exact Hold.
  Qed.
  Lemma keeps_bind {A B} (run : action A) (next : A → action B) :
    keeps run → (∀ value, keeps (next value)) → keeps (run ≫= next).
  Proof.
    intros Hfirst Hnext old new result Hold Hrun.
    unfold mbind, st_bind, result_bind in Hrun.
    destruct (run old) as [[mid value]|err] eqn:Hmid; [|discriminate].
    eapply Hnext; [eapply Hfirst; eassumption|exact Hrun].
  Qed.
  Lemma keeps_fmap {A B} (f : A → B) (run : action A) : keeps run → keeps (f <$> run).
  Proof.
    intros Hfirst old new result Hold Hrun. unfold fmap, st_fmap, result_fmap in Hrun.
    destruct (run old) as [[mid value]|err] eqn:Hmid; [|discriminate].
    injection Hrun as <- <-. eapply Hfirst; eassumption.
  Qed.
  Lemma keeps_get {A} (proj : TLB.t → A) : keeps (mget proj).
  Proof.
    intros old new result Hold Hrun. change (@Ok string _ (old, proj old) = Ok (new, result)) in Hrun.
    injection Hrun as <- <-. exact Hold.
  Qed.
  Lemma keeps_set {A} (proj : TLB.t → A) `{Setter _ _ proj} (f : A → A) :
    (∀ old, I old → I (set proj f old)) → keeps (mset proj f).
  Proof.
    intros Hf old new result Hold Hrun. destruct result.
    change (@Ok string _ (set proj f old, ()) = Ok (new, ())) in Hrun.
    injection Hrun as <-. apply Hf, Hold.
  Qed.
  Lemma keeps_lift {A} (run : result string A) : keeps (mlift run).
  Proof.
    destruct run as [value|err]; intros old new result Hold Hrun; [|discriminate].
    change (@Ok string _ (old, value) = Ok (new, result)) in Hrun. injection Hrun as <- <-. exact Hold.
  Qed.
  Lemma keeps_throw {A} (err : string) : keeps (mthrow err : action A).
  Proof. intros old new value Hold Hrun. discriminate. Qed.
  Lemma keeps_othrow {A} (err : string) (opt : option A) : keeps (othrow err opt).
  Proof. destruct opt; [apply keeps_ret|apply keeps_throw]. Qed.
  Lemma keeps_guard (err : string) (P : Prop) `{Decision P} : keeps (guard_or err P).
  Proof. unfold guard_or. destruct (decide P); [apply keeps_ret|apply keeps_throw]. Qed.
  Lemma keeps_guard_unit (err : string) (P : Prop) `{Decision P} : keeps (guard_or' err P).
  Proof. unfold guard_or'. apply keeps_bind; [apply keeps_guard|intro; apply keeps_ret]. Qed.
  Lemma keeps_mapM {A B} (f : A → action B) xs : (∀ x, keeps (f x)) → keeps (mapM f xs).
  Proof.
    intro Hf. induction xs; cbn [mapM]; [apply keeps_ret|].
    apply keeps_bind; [apply Hf|]. intro value.
    apply keeps_bind; [exact IHxs|]. intro values. apply keeps_ret.
  Qed.
End Keeps.

Lemma unique_fill_entry time fe : keeps unique (TLB.fill_entry time fe).
Proof.
  intros old new loaded Hunique Hfill. unfold TLB.fill_entry in Hfill. cbn in Hfill. unfold mget in Hfill.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose in Hfill. cbn in Hfill.
  destruct (TLB.vatlb old !! fe) as [events|] eqn:Hlookup; rewrite Hlookup in Hfill.
  - destruct events as [|[event stamp] rest].
    + unfold mret, result_ret in Hfill. injection Hfill as <- <-. apply unique_partial_alter, Hunique.
    + destruct event; unfold mret, result_ret in Hfill; injection Hfill as <- <-;
        [exact Hunique|apply unique_partial_alter, Hunique].
  - destruct (decide (TLB.FE.is_table fe));
      unfold mret, result_ret, mbind, result_bind in Hfill; cbn in Hfill;
      injection Hfill as <- <-; apply (unique_partial_alter _ fe old Hunique).
Qed.

Lemma unique_alter f fe : keeps unique (mset TLB.vatlb (alter f fe)).
Proof. apply keeps_set. intros old Hold. apply unique_partial_alter, Hold. Qed.
Lemma unique_map f : keeps unique (mset TLB.vatlb (TLB.VATLB.map_fe f)).
Proof. apply keeps_set. intros old Hold. apply unique_map_fe, Hold. Qed.

Local Opaque TLB.fill_entry.
Ltac solve_unique :=
  first [apply keeps_ret | apply keeps_get | apply keeps_lift
    | apply keeps_throw | apply keeps_othrow | apply keeps_guard | apply keeps_guard_unit
    | apply unique_fill_entry | apply unique_map | apply unique_alter
    | apply keeps_bind; [solve_unique|intro; solve_unique]
    | apply keeps_fmap; solve_unique | apply keeps_mapM; intro; solve_unique
    | match goal with |- keeps _ (match ?x with _ => _ end) => destruct x; solve_unique end].
Lemma unique_fill_root imem mem time roots : keeps unique (TLB.fill_root imem mem time roots).
Proof. unfold TLB.fill_root. solve_unique. Qed.
Lemma unique_fill_from_entry imem mem time entry : keeps unique (TLB.fill_from_entry imem mem time entry).
Proof. unfold TLB.fill_from_entry. solve_unique. Qed.
Lemma unique_fill_from_entries imem mem time entries : keeps unique (TLB.fill_from_entries imem mem time entries).
Proof.
  unfold TLB.fill_from_entries, TLB.fill_from_entries_step.
  do 3 (apply keeps_bind; [apply keeps_fmap, keeps_mapM; intro; apply unique_fill_from_entry|intro]).
  apply keeps_guard_unit.
Qed.
Lemma unique_fill_from_roots imem mem time roots : keeps unique (TLB.fill_from_roots imem mem time roots).
Proof.
  unfold TLB.fill_from_roots. apply keeps_bind; [apply unique_fill_root|intro; apply unique_fill_from_entries].
Qed.
Lemma unique_relevant asids page : keeps unique (TLB.get_relevant_entries asids page).
Proof. unfold TLB.get_relevant_entries. solve_unique. Qed.
Local Opaque TLB.fill_root TLB.fill_from_entry TLB.fill_from_entries TLB.fill_from_roots TLB.get_relevant_entries.
Ltac solve_fill_unique :=
  first [apply unique_fill_root | apply unique_fill_from_entry | apply unique_fill_from_entries
    | apply unique_fill_from_roots | apply unique_relevant | solve_unique
    | apply keeps_bind; [solve_fill_unique|intro; solve_fill_unique]
    | apply keeps_fmap; solve_fill_unique | apply keeps_mapM; intro; solve_fill_unique
    | match goal with |- keeps _ (match ?x with _ => _ end) => destruct x; solve_fill_unique end].
Lemma unique_fill_write imem mem time roots msg : keeps unique (TLB.fill_write imem mem time roots msg).
Proof. unfold TLB.fill_write. solve_fill_unique. Qed.
Lemma unique_fill_tlbi imem mem time roots tlbi : keeps unique (TLB.fill_tlbi imem mem time roots tlbi).
Proof. unfold TLB.fill_tlbi. solve_fill_unique. Qed.
Lemma unique_fill_event tid imem mem time roots ev : keeps unique (TLB.fill_event tid imem mem time roots ev).
Proof.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch]; [apply unique_fill_write|].
  destruct (decide (tid = recipient)); [apply unique_fill_tlbi|apply keeps_ret].
Qed.
Lemma unique_fill_promise tid imem mem ev : keeps unique (TLB.fill_promise tid imem mem ev).
Proof. unfold TLB.fill_promise. apply keeps_bind; [apply keeps_get|intro; apply unique_fill_event]. Qed.
Lemma unique_roll_back time : keeps unique (TLB.roll_back time).
Proof. unfold TLB.roll_back. apply unique_map. Qed.
Lemma unique_roots f : keeps unique (mset TLB.asid_roots f).
Proof. apply keeps_set. intros old Hold. exact Hold. Qed.
Lemma unique_fill_from_btw tid imem fullmem roots tmin tmax mem :
  keeps unique (TLB.fill_from_btw tid imem fullmem roots tmin tmax mem).
Proof.
  revert roots mem. induction tmax as [|tmax IH]; intros roots mem;
    cbn [TLB.fill_from_btw]; destruct (decide (_ < _)); try apply keeps_ret.
  - apply keeps_throw.
  - destruct mem; [apply keeps_throw|].
    apply keeps_bind; [apply IH|]. intro.
    apply keeps_bind; [apply unique_fill_event|intro; apply unique_fill_from_roots].
Qed.
Lemma unique_fill_cse tid imem mem time ttbr0 ttbr1 : keeps unique (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  unfold TLB.fill_cse, TLB.fill_from. apply keeps_bind; [apply unique_roll_back|]. intro.
  apply keeps_bind; [unfold msetv; apply unique_roots|intro; apply unique_fill_from_btw].
Qed.
Lemma unique_fill_asid_root tid imem mem root time : keeps unique (TLB.fill_asid_root tid imem mem root time).
Proof.
  unfold TLB.fill_asid_root, TLB.fill_from. apply keeps_bind; [apply unique_roll_back|]. intro.
  apply keeps_bind; [apply unique_roots|]. intro.
  apply keeps_bind; [apply unique_fill_from_roots|]. intro.
  apply keeps_bind; [apply keeps_get|intro; apply unique_fill_from_btw].
Qed.

Lemma get_init ctxt : TLB.VATLB.get ctxt TLB.VATLB.init = [].
Proof. unfold TLB.VATLB.get, TLB.VATLB.init. rewrite hvec_get_func. reflexivity. Qed.

Lemma unique_init tid imem iregs cache : TLB.init tid imem iregs = Ok cache → unique cache.
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
  eapply unique_fill_from_roots; [|exact Hrun].
  intro ctxt. change (NoDup (map fst (TLB.VATLB.get ctxt TLB.VATLB.init))).
  rewrite get_init. constructor.
Qed.

(** * The entries collected by an invalidation *)

Definition inner (P : TLB.FE.t → Prop) `{∀ fe, Decision (P fe)} lvl
    (nd : TLB.NDCtxt.t lvl) (entries : list (TLB.Entry.t lvl * TLB.Entry.events)) acc :=
  foldl (λ acc '(entry, _),
      let fe := TLB.FE.make_nd lvl nd entry in
      if bool_decide (P fe) then fe :: acc else acc) acc entries.

Lemma collect_unfold P `{∀ fe, Decision (P fe)} cache :
  TLB.VATLB.collect_fe P cache =
    foldl (λ acc lvl, map_fold (inner P lvl) acc (hget lvl cache)) [] (enum Level).
Proof. reflexivity. Qed.

Lemma make_nd_inj lvl nd nd' entry entry' :
  TLB.FE.make_nd lvl nd entry = TLB.FE.make_nd lvl nd' entry' → nd = nd' ∧ entry = entry'.
Proof.
  unfold TLB.FE.make_nd. intro Heq.
  pose proof (f_equal projT1 Heq) as Hctxt. cbn in Hctxt.
  apply (inj (existT lvl)) in Hctxt. subst nd'.
  apply (inj (existT (existT lvl nd))) in Heq. split; [reflexivity|exact Heq].
Qed.

Lemma inner_elem P `{∀ fe, Decision (P fe)} lvl nd entries acc x :
  x ∈ inner P lvl nd entries acc ↔
    x ∈ acc ∨ ∃ entry events, (entry, events) ∈ entries ∧ x = TLB.FE.make_nd lvl nd entry ∧ P x.
Proof.
  revert acc. induction entries as [|[entry events] entries IH]; intro acc; cbn [inner foldl].
  - split; [intro Hin; left; exact Hin|]. intros [Hin|[? [? [Hin _]]]]; [exact Hin|inversion Hin].
  - change (x ∈ inner P lvl nd entries
      (if bool_decide (P (TLB.FE.make_nd lvl nd entry)) then TLB.FE.make_nd lvl nd entry :: acc else acc) ↔
      x ∈ acc ∨ ∃ entry' events', (entry', events') ∈ (entry, events) :: entries ∧
        x = TLB.FE.make_nd lvl nd entry' ∧ P x).
    etrans; [apply IH|]. split.
    + intros [Hin|[entry' [events' [Hin [-> HP]]]]].
      * case_bool_decide as HP.
        -- apply elem_of_cons in Hin as [->|Hin]; [right; exists entry, events; split; [left|auto]|left; exact Hin].
        -- left. exact Hin.
      * right. exists entry', events'. split; [right; exact Hin|auto].
    + intros [Hin|[entry' [events' [Hin [-> HP]]]]].
      * left. case_bool_decide; [right; exact Hin|exact Hin].
      * apply elem_of_cons in Hin as [Heq|Hin].
        -- injection Heq as -> ->. left. rewrite bool_decide_true by exact HP. left.
        -- right. exists entry', events'. auto.
Qed.

Lemma inner_nodup P `{∀ fe, Decision (P fe)} lvl nd entries acc :
  NoDup acc → NoDup (map fst entries) →
  (∀ entry events, (entry, events) ∈ entries → TLB.FE.make_nd lvl nd entry ∉ acc) →
  NoDup (inner P lvl nd entries acc).
Proof.
  revert acc. induction entries as [|[entry events] entries IH]; intros acc Hacc Hkeys Hfresh;
    cbn [inner foldl]; [exact Hacc|].
  cbn [map fst] in Hkeys. apply list.NoDup_cons in Hkeys as [Hnew Hkeys].
  change (NoDup (inner P lvl nd entries
    (if bool_decide (P (TLB.FE.make_nd lvl nd entry)) then TLB.FE.make_nd lvl nd entry :: acc else acc))).
  apply IH; [|exact Hkeys|].
  - case_bool_decide; [|exact Hacc]. apply list.NoDup_cons. split; [|exact Hacc].
    apply (Hfresh entry events). left.
  - intros entry' events' Hin Hacc'. case_bool_decide; [apply elem_of_cons in Hacc' as [Heq|Hacc']|].
    + apply make_nd_inj in Heq as [_ ->]. apply Hnew. apply list_elem_of_fmap. exists (entry, events'). auto.
    + eapply Hfresh; [right; exact Hin|exact Hacc'].
    + eapply Hfresh; [right; exact Hin|exact Hacc'].
Qed.

Definition level_member (cache : TLB.VATLB.t) lvl (P : TLB.FE.t → Prop) x :=
  ∃ nd entry events, (entry, events) ∈ default [] (hget lvl cache !! nd) ∧
    x = TLB.FE.make_nd lvl nd entry ∧ P x.

Lemma rows_elem P `{∀ fe, Decision (P fe)} lvl acc rows x :
  x ∈ foldr (uncurry (inner P lvl)) acc rows ↔ x ∈ acc ∨
    ∃ nd entries entry events, (nd, entries) ∈ rows ∧ (entry, events) ∈ entries ∧
      x = TLB.FE.make_nd lvl nd entry ∧ P x.
Proof.
  induction rows as [|[nd entries] rows IH]; cbn [foldr uncurry].
  - split; [intro Hin; left; exact Hin|]. intros [Hin|[? [? [? [? [Hin _]]]]]]; [exact Hin|inversion Hin].
  - etrans; [apply inner_elem|]. split.
    + intros [Hin|[entry [events [Hin [-> HP]]]]].
      * apply IH in Hin as [Hin|[nd' [entries' [entry [events [Hrow Hrest]]]]]]; [left; exact Hin|].
        right. exists nd', entries', entry, events. split; [right; exact Hrow|exact Hrest].
      * right. exists nd, entries, entry, events. split; [left|auto].
    + intros [Hin|[nd' [entries' [entry [events [Hrow [Hentry [-> HP]]]]]]]]; [left; apply IH; left; exact Hin|].
      apply elem_of_cons in Hrow as [Heq|Hrow].
      * injection Heq as -> ->. right. exists entry, events. auto.
      * left. apply IH. right. exists nd', entries', entry, events. auto.
Qed.

Lemma level_elem P `{∀ fe, Decision (P fe)} cache lvl acc x :
  x ∈ map_fold (inner P lvl) acc (hget lvl cache) ↔ x ∈ acc ∨ level_member cache lvl P x.
Proof.
  rewrite (map_fold_foldr (M := gmap (TLB.NDCtxt.t lvl))). etrans; [apply rows_elem|].
  unfold level_member. split; (intros [Hin|Hrest]; [left; exact Hin|right]).
  - destruct Hrest as [nd [entries [entry [events [Hrow [Hentry Hrest]]]]]].
    apply (elem_of_map_to_list (M := gmap (TLB.NDCtxt.t lvl))) in Hrow.
    exists nd, entry, events. split; [|exact Hrest].
    change (default [] (hget lvl cache !! nd)) with
      (default [] ((hget lvl cache : gmap (TLB.NDCtxt.t lvl) _) !! nd)).
    rewrite Hrow. exact Hentry.
  - destruct Hrest as [nd [entry [events [Hentry Hrest]]]].
    destruct (hget lvl cache !! nd) as [entries|] eqn:Hlookup; [|inversion Hentry].
    exists nd, entries, entry, events. split; [|auto].
    apply (elem_of_map_to_list (M := gmap (TLB.NDCtxt.t lvl))). exact Hlookup.
Qed.

Lemma rows_member P `{∀ fe, Decision (P fe)} lvl acc rows y :
  y ∈ foldr (uncurry (inner P lvl)) acc rows → y ∈ acc ∨
    ∃ nd entries entry, (nd, entries) ∈ rows ∧ y = TLB.FE.make_nd lvl nd entry.
Proof.
  intro Hin. apply rows_elem in Hin as [Hin|[nd [entries [entry [_ [Hrow [_ [Heq _]]]]]]]];
    [left; exact Hin|right; exists nd, entries, entry; auto].
Qed.

Lemma rows_nodup P `{∀ fe, Decision (P fe)} lvl acc rows :
  NoDup (map fst rows) → (∀ nd entries, (nd, entries) ∈ rows → NoDup (map fst entries)) →
  NoDup acc → (∀ x, x ∈ acc → TLB.FE.lvl x ≠ lvl) →
  NoDup (foldr (uncurry (inner P lvl)) acc rows).
Proof.
  intros Hkeys Hrow Hacc Hlevel.
  induction rows as [|[nd entries] rows IH]; cbn [foldr uncurry]; [exact Hacc|].
  cbn [map fst] in Hkeys. apply list.NoDup_cons in Hkeys as [Hnew Hkeys].
  apply inner_nodup.
  - apply IH; [exact Hkeys|]. intros nd' entries' Hin. apply (Hrow nd'). right. exact Hin.
  - apply (Hrow nd). left.
  - intros entry events Hin Hmember.
    destruct (rows_member P lvl acc rows _ Hmember) as [Hacc'|[nd' [entries' [entry' [Hrow' Heq]]]]].
    + apply (Hlevel _ Hacc'). reflexivity.
    + apply make_nd_inj in Heq as [<- _]. apply Hnew. apply list_elem_of_fmap. exists (nd, entries'). auto.
Qed.

Lemma level_nodup P `{∀ fe, Decision (P fe)} cache lvl acc :
  (∀ nd, NoDup (map fst (default [] (hget lvl cache !! nd)))) →
  NoDup acc → (∀ x, x ∈ acc → TLB.FE.lvl x ≠ lvl) →
  NoDup (map_fold (inner P lvl) acc (hget lvl cache)).
Proof.
  intros Hunique Hacc Hlevel. rewrite (map_fold_foldr (M := gmap (TLB.NDCtxt.t lvl))).
  apply rows_nodup; [apply (NoDup_fst_map_to_list (M := gmap (TLB.NDCtxt.t lvl)))| |exact Hacc|exact Hlevel].
  intros nd entries Hin. apply (elem_of_map_to_list (M := gmap (TLB.NDCtxt.t lvl))) in Hin.
  specialize (Hunique nd).
  change (default [] (hget lvl cache !! nd)) with
    (default [] ((hget lvl cache : gmap (TLB.NDCtxt.t lvl) _) !! nd)) in Hunique.
  rewrite Hin in Hunique. exact Hunique.
Qed.

Lemma lookup_assoc_elem {K V} `{EqDecision K} (key : K) (entries : list (K * V)) :
  is_Some (lookup_assoc key entries) ↔ ∃ value, (key, value) ∈ entries.
Proof.
  induction entries as [|[first value] entries IH]; cbn [lookup_assoc].
  - split; [intros [? Hbad]; discriminate|intros [? Hin]; inversion Hin].
  - destruct (decide (key = first)) as [->|Hne].
    + split; [intros _; exists value; left|intros _; eexists; reflexivity].
    + etrans; [exact IH|]. split; intros [found Hin]; exists found; [right; exact Hin|].
      apply elem_of_cons in Hin as [Heq|Hin]; [injection Heq as ->; contradiction|exact Hin].
Qed.

Lemma lookup_fe_elem (cache : TLB.VATLB.t) lvl nd entry :
  is_Some (cache !! TLB.FE.make_nd lvl nd entry) ↔
    ∃ events, (entry, events) ∈ default [] (hget lvl cache !! nd).
Proof. apply lookup_assoc_elem. Qed.

Theorem collect_elem P `{∀ fe, Decision (P fe)} cache x :
  x ∈ TLB.VATLB.collect_fe P cache ↔ P x ∧ is_Some (cache !! x).
Proof.
  rewrite collect_unfold.
  assert (Hlevels : ∀ levels acc, x ∈ foldl (λ acc lvl, map_fold (inner P lvl) acc (hget lvl cache)) acc levels ↔
    x ∈ acc ∨ ∃ lvl, lvl ∈ levels ∧ level_member cache lvl P x).
  { induction levels as [|lvl levels IH]; intro acc; cbn [foldl].
    - split; [intro Hin; left; exact Hin|]. intros [Hin|[? [Hin _]]]; [exact Hin|inversion Hin].
    - etrans; [apply IH|]. pose proof (level_elem P cache lvl acc x) as Hlevel. split.
      + intros [Hin|[lvl' [Hin Hmember]]].
        * apply Hlevel in Hin as [Hin|Hmember]; [left; exact Hin|].
          right. exists lvl. split; [left|exact Hmember].
        * right. exists lvl'. split; [right; exact Hin|exact Hmember].
      + intros [Hin|[lvl' [Hin Hmember]]]; [left; apply Hlevel; left; exact Hin|].
        apply elem_of_cons in Hin as [->|Hin]; [left; apply Hlevel; right; exact Hmember|].
        right. exists lvl'. auto. }
  etrans; [apply Hlevels|]. split.
  - intros [Hin|[lvl [_ [nd [entry [events [Hentry [-> HP]]]]]]]]; [inversion Hin|].
    split; [exact HP|]. apply lookup_fe_elem. exists events. exact Hentry.
  - intros [HP Hsome]. right. destruct x as [[lvl nd] entry].
    exists lvl. split; [apply elem_of_enum|].
    change (is_Some (cache !! TLB.FE.make_nd lvl nd entry)) in Hsome.
    apply lookup_fe_elem in Hsome as [events Hentry].
    exists nd, entry, events. split; [exact Hentry|]. split; [reflexivity|exact HP].
Qed.

Theorem collect_nodup P `{∀ fe, Decision (P fe)} (cache : TLB.t) :
  unique cache → NoDup (TLB.VATLB.collect_fe P (TLB.vatlb cache)).
Proof.
  intro Hunique. rewrite collect_unfold.
  assert (Hlevels : ∀ levels acc, NoDup levels → NoDup acc →
    (∀ x, x ∈ acc → TLB.FE.lvl x ∉ levels) →
    NoDup (foldl (λ acc lvl, map_fold (inner P lvl) acc (hget lvl (TLB.vatlb cache))) acc levels)).
  { induction levels as [|lvl levels IH]; intros acc Hlevels Hacc Hfresh; cbn [foldl]; [exact Hacc|].
    apply list.NoDup_cons in Hlevels as [Hnew Hlevels].
    apply IH; [exact Hlevels| |].
    - apply level_nodup; [intro nd; exact (Hunique (existT lvl nd))|exact Hacc|].
      intros x Hin Heq. apply (Hfresh x Hin). rewrite Heq. left.
    - intros x Hin. apply level_elem in Hin as [Hin|[nd [entry [events [_ [-> _]]]]]].
      + intro Hlevel. apply (Hfresh x Hin). right. exact Hlevel.
      + exact Hnew. }
  apply Hlevels; [apply NoDup_enum|constructor|intros x Hin; inversion Hin].
Qed.

(** * The invalidation loop *)

Definition invalidate time tlbi (events : TLB.Entry.events) :=
  if events is [] then [] else (TLB.Entry.Tlbi (TLBI.tid tlbi), time) :: events.
Definition step asids time tlbi (entry : TLB.FE.t) : action (list TLB.FE.t) :=
  mset TLB.vatlb (alter (invalidate time tlbi) entry);;
  TLB.get_relevant_entries asids (TLB.FE.cur_table entry).
Definition live tlbi (cache : TLB.VATLB.t) :=
  filter (λ entry, default [] (cache !! entry) ≠ []) (TLB.VATLB.collect_fe (TLB.affects tlbi) cache).

Lemma last_shape imem mem time roots tlbi cache : TLBI.last tlbi = true →
  TLB.fill_tlbi imem mem time roots tlbi cache =
    (parents ← List.concat <$> mapM (step (remove_dups roots.*1.*1) time tlbi) (live tlbi (TLB.vatlb cache));
     TLB.fill_from_entries imem mem time parents) cache.
Proof. intro Hlast. unfold TLB.fill_tlbi. rewrite Hlast. reflexivity. Qed.

Lemma final_not_table lvl pte : is_final lvl pte → ¬ is_table lvl pte.
Proof.
  unfold is_final, is_table, is_block, leaf_lvl.
  assert (Hbits : ∀ bits : bv 2, bits = 1%bv → bits = 3%bv → False).
  { intros bits -> Hbad. apply (f_equal bv_unsigned) in Hbad. discriminate Hbad. }
  inv_fin lvl; [intros [_ Hblock] [_ Htable]; exact (Hbits _ Hblock Htable)|intro lvl].
  inv_fin lvl; [intros [_ Hblock] [_ Htable]; exact (Hbits _ Hblock Htable)|intro lvl].
  inv_fin lvl; [intros [_ Hblock] [_ Htable]; exact (Hbits _ Hblock Htable)|intro lvl].
  inv_fin lvl; [intros _ [Hlvl _]; apply Hlvl; reflexivity|intro lvl].
  inv_fin lvl.
Qed.

Lemma last_leaf tlbi fe : TLBI.last tlbi = true → TLB.affects tlbi fe → ¬ TLB.FE.is_table fe.
Proof.
  intros Hlast Haffects.
  destruct tlbi as [tid|tid asid|tid asid upper vpn last|tid upper vpn last];
    unfold TLBI.last in Hlast; cbn in Hlast; try discriminate; subst last.
  - destruct Haffects as [_ [_ [Hfinal _]]]. exact (final_not_table _ _ Hfinal).
  - destruct Haffects as [_ [Hfinal _]]. exact (final_not_table _ _ Hfinal).
Qed.

Lemma lookup_alter_fe f fe (cache : TLB.VATLB.t) query :
  (alter f fe cache) !! query = if decide (query = fe) then f <$> cache !! query else cache !! query.
Proof.
  destruct fe as [ctxt entry], query as [other queried].
  unfold alter, alter_default, partial_alter, TLB.VATLB.partial_alter_fe, lookup, TLB.VATLB.lookup_fe.
  cbn [TLB.FE.ctxt TLB.FE.entry projT1 projT2].
  destruct (decide (ctxt = other)) as [<-|Hctxt].
  - rewrite get_alter_entries_same, VMCacheIndexed.lookup_assoc_alter.
    destruct (decide (queried = entry)) as [->|Hne].
    + rewrite !decide_True by reflexivity. reflexivity.
    + rewrite (decide_False (P := queried = entry)) by exact Hne.
      rewrite decide_False; [reflexivity|]. intro Heq. apply (inj (existT ctxt)) in Heq. contradiction.
  - rewrite get_alter_entries_other by exact Hctxt.
    rewrite decide_False; [reflexivity|]. intro Heq.
    apply (f_equal TLB.FE.ctxt) in Heq. cbn in Heq. congruence.
Qed.

Lemma history_alter time tlbi fe cache query :
  history (set TLB.vatlb (alter (invalidate time tlbi) fe) cache) query =
    if decide (query = fe) then invalidate time tlbi (history cache query) else history cache query.
Proof.
  unfold history. cbn [TLB.vatlb]. rewrite lookup_alter_fe.
  destruct (decide (query = fe)); [|reflexivity].
  destruct (TLB.vatlb cache !! query); reflexivity.
Qed.

Lemma filter_elem_ext {A} (P Q : A → Prop) `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} (xs : list A) :
  (∀ x, x ∈ xs → P x ↔ Q x) → filter P xs = filter Q xs.
Proof.
  induction xs as [|x xs IH]; intro Hsame; [reflexivity|]. rewrite !filter_cons.
  rewrite IH by (intros y Hin; apply Hsame; right; exact Hin).
  assert (Hx : P x ↔ Q x) by (apply Hsame; left).
  destruct (decide (P x)) as [HP|HP], (decide (Q x)) as [HQ|HQ]; try reflexivity; exfalso.
  - apply HQ, Hx, HP.
  - apply HP, Hx, HQ.
Qed.

Lemma relevant_alter_leaf time tlbi fe cache asids page :
  VMCacheIndexed.valid cache → ¬ TLB.FE.is_table fe →
  VMCacheIndexed.relevant (set TLB.vatlb (alter (invalidate time tlbi) fe) cache) asids page =
    VMCacheIndexed.relevant cache asids page.
Proof.
  intros Hvalid Hleaf. unfold VMCacheIndexed.relevant. cbn [TLB.next_table_cache TLB.vatlb].
  apply filter_elem_ext. intros query Hin.
  destruct (Hvalid page) as [_ Hentries]. apply Hentries in Hin as [Htable _].
  unfold TLB.VATLB.is_active. rewrite lookup_alter_fe.
  rewrite decide_False; [reflexivity|]. intros ->. contradiction.
Qed.

Lemma valid_alter time tlbi fe cache :
  VMCacheIndexed.valid cache → VMCacheIndexed.valid (set TLB.vatlb (alter (invalidate time tlbi) fe) cache).
Proof. apply VMCacheIndexed.alter_vatlb. Qed.

Theorem loop_closed asids time tlbi entries cache :
  NoDup entries → (∀ entry, entry ∈ entries → ¬ TLB.FE.is_table entry) → VMCacheIndexed.valid cache →
  ∃ ending, mapM (step asids time tlbi) entries cache =
      Ok (ending, map (λ entry, VMCacheIndexed.relevant cache asids (TLB.FE.cur_table entry)) entries) ∧
    TLB.pte_present ending = TLB.pte_present cache ∧ VMCacheIndexed.valid ending ∧
    ∀ query, history ending query =
      if decide (query ∈ entries) then invalidate time tlbi (history cache query) else history cache query.
Proof.
  revert cache. induction entries as [|entry entries IH]; intros cache Hunique Hleaf Hvalid.
  - exists cache. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hvalid|].
    intro query. rewrite decide_False by apply not_elem_of_nil. reflexivity.
  - apply list.NoDup_cons in Hunique as [Hnew Hunique].
    set (mid := set TLB.vatlb (alter (invalidate time tlbi) entry) cache).
    assert (Hentry : ¬ TLB.FE.is_table entry) by (apply Hleaf; left).
    assert (Hmid : VMCacheIndexed.valid mid) by apply valid_alter, Hvalid.
    destruct (IH mid Hunique (λ e Hin, Hleaf e (proj2 (elem_of_cons _ _ _) (or_intror Hin))) Hmid)
      as [ending [Hrun [Hpresent [Hvalid' Hhistory]]]].
    exists ending. split; [|split; [exact Hpresent|split; [exact Hvalid'|]]].
    + cbn [mapM]. unfold step at 1.
      change ((TLB.get_relevant_entries asids (TLB.FE.cur_table entry) mid ≫= λ '(next, found),
        (mapM (step asids time tlbi) entries next ≫= λ '(last, rest), Ok (last, found :: rest)))
        = Ok (ending, VMCacheIndexed.relevant cache asids (TLB.FE.cur_table entry) ::
          map (λ entry, VMCacheIndexed.relevant cache asids (TLB.FE.cur_table entry)) entries)).
      rewrite VMCacheIndexed.relevant_run. cbn [mbind result_bind]. rewrite Hrun. cbn [mbind result_bind].
      unfold mid. rewrite relevant_alter_leaf by assumption.
      f_equal. f_equal. f_equal. apply map_ext_in. intros other Hin.
      apply relevant_alter_leaf; [exact Hvalid|exact Hentry].
    + intro query. rewrite Hhistory. unfold mid. rewrite !history_alter.
      destruct (decide (query = entry)) as [->|Hne].
      * rewrite decide_False by exact Hnew. rewrite decide_True by left. reflexivity.
      * destruct (decide (query ∈ entries)) as [Hin|Hout].
        -- rewrite decide_True by (right; exact Hin). reflexivity.
        -- rewrite decide_False; [reflexivity|]. intro Hin. apply elem_of_cons in Hin as [->|Hin]; contradiction.
Qed.

Lemma live_elem tlbi (cache : TLB.t) entry :
  entry ∈ live tlbi (TLB.vatlb cache) ↔ TLB.affects tlbi entry ∧ history cache entry ≠ [].
Proof.
  unfold live. etrans; [apply list_elem_of_filter|]. unfold history. split.
  - intros [Hlive Hin]. apply collect_elem in Hin as [Haffects _]. auto.
  - intros [Haffects Hlive]. split; [exact Hlive|]. apply collect_elem. split; [exact Haffects|].
    destruct (TLB.vatlb cache !! entry); [eexists; reflexivity|contradiction].
Qed.

Lemma concat_map_permutation {A B} (f g : A → list B) xs :
  (∀ x, f x ≡ₚ g x) → List.concat (map f xs) ≡ₚ List.concat (map g xs).
Proof.
  intro Hfg. induction xs as [|x xs IH]; cbn [map List.concat]; [apply Permutation_refl|].
  apply Permutation_app; [apply Hfg|exact IH].
Qed.

(** Equivalent caches may disagree on empty allocations. The invalidation
    only follows entries with events, so both caches refill the same parents. *)
Theorem fill_tlbi_last_equiv imem mem time roots tlbi old new old' :
  TLBI.last tlbi = true →
  VMCacheIndexed.valid old → VMCacheIndexed.valid new → unique old → unique new → equiv old new →
  TLB.fill_tlbi imem mem time roots tlbi old = Ok (old', ()) →
  ∃ new', TLB.fill_tlbi imem mem time roots tlbi new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  intros Hlast Hvalid Hvalid' Hunique Hunique' Heq Hrun.
  rewrite last_shape in Hrun |- * by exact Hlast.
  set (asids := remove_dups roots.*1.*1) in *.
  assert (Hnodup : ∀ cache : TLB.t, unique cache → NoDup (live tlbi (TLB.vatlb cache))).
  { intros cache Hcache. apply list.NoDup_filter, collect_nodup, Hcache. }
  assert (Hleaf : ∀ (cache : TLB.t) entry, entry ∈ live tlbi (TLB.vatlb cache) → ¬ TLB.FE.is_table entry).
  { intros cache entry Hin. apply live_elem in Hin as [Haffects _]. eapply last_leaf; eassumption. }
  destruct (loop_closed asids time tlbi (live tlbi (TLB.vatlb old)) old
    (Hnodup old Hunique) (Hleaf old) Hvalid) as [mid [Hloop [Hpresent [Hmid Hhistory]]]].
  destruct (loop_closed asids time tlbi (live tlbi (TLB.vatlb new)) new
    (Hnodup new Hunique') (Hleaf new) Hvalid') as [mid' [Hloop' [Hpresent' [Hmid' Hhistory']]]].
  unfold mbind, st_bind, result_bind, fmap, st_fmap, result_fmap in Hrun |- *.
  rewrite Hloop in Hrun. rewrite Hloop'. cbn in Hrun |- *.
  assert (Hsame : ∀ entry, entry ∈ live tlbi (TLB.vatlb old) ↔ entry ∈ live tlbi (TLB.vatlb new)).
  { destruct Heq as [_ Hhist]. intro entry. split; intro Hin;
      apply live_elem in Hin as [Haffects Hlive]; apply live_elem;
      (split; [exact Haffects|]); [rewrite <- Hhist|rewrite Hhist]; exact Hlive. }
  assert (Hmid_eq : equiv mid mid').
  { destruct Heq as [Hconfig Hhist]. split; [congruence|]. intro query.
    rewrite Hhistory, Hhistory', Hhist.
    destruct (decide (query ∈ live tlbi (TLB.vatlb old))) as [Hin|Hout];
      [rewrite decide_True by (apply Hsame, Hin)|rewrite decide_False by (intro Hin; apply Hout, Hsame, Hin)];
      reflexivity. }
  assert (Hperm : live tlbi (TLB.vatlb old) ≡ₚ live tlbi (TLB.vatlb new)).
  { apply list.NoDup_Permutation; [apply Hnodup, Hunique|apply Hnodup, Hunique'|exact Hsame]. }
  eapply fill_from_entries_permutation; [exact Hmid_eq| |exact Hrun].
  eapply Permutation_trans; [apply concat_permutation, Permutation_map, Hperm|].
  apply concat_map_permutation. intro entry.
  apply VMCacheIndexed.relevant_permutation; assumption.
Qed.

(** * Replay without the restriction to non-last invalidations *)

Local Opaque TLB.fill_write TLB.fill_tlbi.

Theorem fill_event_equiv tid imem mem time roots ev old new old' :
  VMCacheIndexed.valid old → VMCacheIndexed.valid new → unique old → unique new → equiv old new →
  TLB.fill_event tid imem mem time roots ev old = Ok (old', ()) →
  ∃ new', TLB.fill_event tid imem mem time roots ev new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  intros Hvalid Hvalid' Hunique Hunique' Heq Hrun.
  destruct ev as [msg|tlbi recipient epoch]; cbn [TLB.fill_event] in Hrun |- *.
  - exact (fill_write_equiv imem mem time roots msg old new old' Hvalid Hvalid' Heq Hrun).
  - destruct (decide (tid = recipient)) as [Hrecipient|Hrecipient].
    + destruct (TLBI.last tlbi) eqn:Hlast.
      * exact (fill_tlbi_last_equiv imem mem time roots tlbi old new old'
          Hlast Hvalid Hvalid' Hunique Hunique' Heq Hrun).
      * exact (fill_tlbi_nonlast_equiv imem mem time roots tlbi old new old' Hlast Heq Hrun).
    + change (@Ok string _ (old, ()) = Ok (old', ())) in Hrun. injection Hrun as <-.
      exists new. split; [reflexivity|exact Heq].
Qed.

Theorem fill_from_btw_equiv tid imem fullmem roots tmin tmax mem old new old' :
  VMCacheIndexed.valid old → VMCacheIndexed.valid new → unique old → unique new → equiv old new →
  TLB.fill_from_btw tid imem fullmem roots tmin tmax mem old = Ok (old', ()) →
  ∃ new', TLB.fill_from_btw tid imem fullmem roots tmin tmax mem new = Ok (new', ()) ∧ equiv old' new'.
Proof.
  revert roots mem old new old'. induction tmax as [|tmax IH];
    intros roots mem old new old' Hvalid Hvalid' Hunique Hunique' Heq Hrun;
    cbn [TLB.fill_from_btw] in Hrun |- *; destruct (decide (_ < _)).
  - change (@Ok string _ (old, ()) = Ok (old', ())) in Hrun. injection Hrun as <-.
    exists new. auto.
  - discriminate.
  - change (@Ok string _ (old, ()) = Ok (old', ())) in Hrun. injection Hrun as <-.
    exists new. auto.
  - destruct mem as [|ev mem]; [discriminate|].
    unfold mbind, st_bind, result_bind in Hrun |- *.
    set (active_roots := filter (λ '(_, time), time < S tmax) roots) in *.
    set (added_roots := filter (λ '(_, time), time = S tmax) roots) in *.
    destruct (TLB.fill_from_btw tid imem fullmem active_roots tmin tmax mem old)
      as [[mid []]|err] eqn:Hprefix; [|discriminate]. cbn in Hrun.
    destruct (TLB.fill_event tid imem fullmem (S tmax) active_roots.*1 ev mid)
      as [[next []]|err] eqn:Hstep; [|discriminate]. cbn in Hrun.
    destruct (IH active_roots mem old new mid Hvalid Hvalid' Hunique Hunique' Heq Hprefix)
      as [mid' [Hprefix' Heq_mid]].
    pose proof (VMCacheIndexed.fill_from_btw tid imem fullmem active_roots tmin tmax mem
      old mid () Hvalid Hprefix) as Hmid.
    pose proof (VMCacheIndexed.fill_from_btw tid imem fullmem active_roots tmin tmax mem
      new mid' () Hvalid' Hprefix') as Hmid'.
    pose proof (unique_fill_from_btw tid imem fullmem active_roots tmin tmax mem
      old mid () Hunique Hprefix) as Humid.
    pose proof (unique_fill_from_btw tid imem fullmem active_roots tmin tmax mem
      new mid' () Hunique' Hprefix') as Humid'.
    destruct (fill_event_equiv tid imem fullmem (S tmax) active_roots.*1 ev mid mid' next
      Hmid Hmid' Humid Humid' Heq_mid Hstep) as [next' [Hstep' Heq_next]].
    rewrite Hprefix'. cbn. rewrite Hstep'. cbn.
    eapply fill_from_roots_equiv; [exact Heq_next|exact Hrun].
Qed.

End VMCacheLastTLBI.
