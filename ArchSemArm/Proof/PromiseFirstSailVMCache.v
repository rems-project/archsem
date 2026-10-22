(******************************************************************************)
(* Preserving old translation entries while extending their event histories   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMTranslation.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheReplay.
Import VMPromising VMTranslationReplay.
#[local] Existing Instance TLB.Decision_affects.

Definition extends (bound : nat) (old new : TLB.VATLB.t) : Prop :=
  ∀ ctxt fe events, (fe, events) ∈ TLB.VATLB.get_fe old ctxt →
  ∃ prefix, Forall (λ event, bound < event.2) prefix ∧
    (fe, (prefix ++ events)%list) ∈ TLB.VATLB.get_fe new ctxt.

Lemma extends_refl bound cache : extends bound cache cache.
Proof. intros ctxt fe events Hin. exists []. split; [constructor|exact Hin]. Qed.

Lemma extends_trans bound old mid new :
  extends bound old mid → extends bound mid new → extends bound old new.
Proof.
  intros Hfirst Hsecond ctxt fe events Hin.
  destruct (Hfirst ctxt fe events Hin) as [prefix [Hprefix Hmid]].
  destruct (Hsecond ctxt fe (prefix ++ events)%list Hmid) as [suffix [Hsuffix Hnew]].
  exists (suffix ++ prefix)%list. split.
  - apply Forall_app. auto.
  - rewrite <- app_assoc. exact Hnew.
Qed.

Lemma lookup_total_imap {K A B} `{Countable K} (f : K → A → B) (m : gmap K A) key :
  (imap f m) !! key = f key <$> (m !! key).
Proof.
  change ((map_imap (λ k v, Some (f k v)) m) !! key = f key <$> (m !! key)).
  rewrite map_lookup_imap. destruct (m !! key); reflexivity.
Qed.

Lemma get_map_fe f cache ctxt :
  TLB.VATLB.get ctxt (TLB.VATLB.map_fe f cache) =
  map (λ '(entry, events), (entry, f (existT ctxt entry) events)) (TLB.VATLB.get ctxt cache).
Proof.
  destruct ctxt as [lvl nd].
  unfold TLB.VATLB.get, TLB.VATLB.map_fe.
  rewrite hget_hmap, lookup_total_imap.
  unfold TLB.Ctxt.nd, TLB.Ctxt.lvl; cbn.
  destruct (hget lvl cache !! nd) eqn:Hlookup; rewrite Hlookup; reflexivity.
Qed.

Lemma get_fe_map_fe f cache ctxt :
  TLB.VATLB.get_fe (TLB.VATLB.map_fe f cache) ctxt =
  map (λ '(fe, events), (fe, f fe events)) (TLB.VATLB.get_fe cache ctxt).
Proof.
  unfold TLB.VATLB.get_fe. rewrite get_map_fe, !map_map. apply map_ext.
  intros [entry events]. reflexivity.
Qed.

Lemma map_fe_extends bound f cache :
  (∀ fe events, ∃ prefix, Forall (λ event, bound < event.2) prefix ∧
    f fe events = (prefix ++ events)%list) →
  extends bound cache (TLB.VATLB.map_fe f cache).
Proof.
  intros Hf ctxt fe events Hin.
  destruct (Hf fe events) as [prefix [Hprefix Heq]].
  exists prefix. split; [exact Hprefix|]. rewrite get_fe_map_fe.
  apply list_elem_of_fmap. exists (fe, events). split; [cbn; rewrite Heq; reflexivity|exact Hin].
Qed.

Lemma get_alter_entries_same ctxt f cache :
  TLB.VATLB.get ctxt (TLB.VATLB.alter_entries ctxt f cache) = f (TLB.VATLB.get ctxt cache).
Proof.
  unfold TLB.VATLB.get, TLB.VATLB.alter_entries.
  rewrite hvec_get_set_same.
  rewrite (lookup_partial_alter_eq (M := gmap (TLB.NDCtxt.t (TLB.Ctxt.lvl ctxt)))).
  destruct (hget (TLB.Ctxt.lvl ctxt) cache !! TLB.Ctxt.nd ctxt) eqn:Hlookup;
    rewrite Hlookup; reflexivity.
Qed.

Lemma get_alter_entries_other ctxt other f cache :
  ctxt ≠ other →
  TLB.VATLB.get other (TLB.VATLB.alter_entries ctxt f cache) = TLB.VATLB.get other cache.
Proof.
  destruct ctxt as [lvl nd], other as [lvl' nd']. intro Hne.
  unfold TLB.VATLB.get, TLB.VATLB.alter_entries. unfold TLB.Ctxt.nd, TLB.Ctxt.lvl; cbn.
  destruct (decide (lvl = lvl')) as [Heq|Hlevel].
  - subst lvl'. rewrite hvec_get_set_same, (lookup_partial_alter_ne (M := gmap (TLB.NDCtxt.t lvl))); [reflexivity|].
    intro Heq. subst nd'. contradiction.
  - rewrite hvec_get_set_diff by congruence. reflexivity.
Qed.

Lemma alter_entries_extends bound ctxt f cache :
  (∀ entry events, (entry, events) ∈ TLB.VATLB.get ctxt cache →
    ∃ prefix, Forall (λ event, bound < event.2) prefix ∧
      (entry, (prefix ++ events)%list) ∈ f (TLB.VATLB.get ctxt cache)) →
  extends bound cache (TLB.VATLB.alter_entries ctxt f cache).
Proof.
  intros Hf other fe events Hin. destruct (decide (ctxt = other)) as [<-|Hne].
  - unfold TLB.VATLB.get_fe in Hin |- *.
    apply list_elem_of_fmap in Hin as [[entry oldevents] [Heq Hin]].
    injection Heq as Hfe Hevents. subst fe events.
    destruct (Hf entry oldevents Hin) as [prefix [Hprefix Hmember]].
    exists prefix. split; [exact Hprefix|]. rewrite get_alter_entries_same.
    apply list_elem_of_fmap. exists (entry, (prefix ++ oldevents)%list). auto.
  - exists []. split; [constructor|].
    unfold TLB.VATLB.get_fe in Hin |- *.
    rewrite get_alter_entries_other by exact Hne. exact Hin.
Qed.

Lemma partial_alter_assoc_extends {K} `{EqDecision K} bound key f
    (entries : list (K * TLB.Entry.events)) :
  (∀ events, lookup_assoc key entries = Some events →
    ∃ prefix, Forall (λ event, bound < event.2) prefix ∧
      f (Some events) = Some (prefix ++ events)%list) →
  ∀ entry events, (entry, events) ∈ entries →
    ∃ prefix, Forall (λ event, bound < event.2) prefix ∧
      (entry, (prefix ++ events)%list) ∈ partial_alter_assoc f key entries.
Proof.
  induction entries as [|[first firstevents] rest IH]; intros Hf entry events Hin.
  - inversion Hin.
  - cbn [partial_alter_assoc]. destruct (decide (key = first)) as [->|Hne].
    + destruct (Hf firstevents ltac:(cbn [lookup_assoc]; rewrite decide_True by reflexivity; reflexivity))
        as [prefix [Hprefix Hupdate]]. rewrite Hupdate.
      apply elem_of_cons in Hin as [Heq|Hin].
      * injection Heq as -> ->. exists prefix. split; [exact Hprefix|left; reflexivity].
      * exists []. split; [constructor|right; exact Hin].
    + apply elem_of_cons in Hin as [Heq|Hin].
      * injection Heq as -> ->. exists []. split; [constructor|left; reflexivity].
      * assert (Hrest : ∀ old, lookup_assoc key rest = Some old →
          ∃ prefix, Forall (λ event, bound < event.2) prefix ∧
            f (Some old) = Some (prefix ++ old)%list).
        { intros old Hlookup. apply Hf. cbn [lookup_assoc].
          rewrite decide_False by exact Hne. exact Hlookup. }
        destruct (IH Hrest entry events Hin) as [prefix [Hprefix Hmember]].
        exists prefix. split; [exact Hprefix|right; exact Hmember].
Qed.

Lemma update_entry_extends bound cache fe f :
  (∀ events, cache !! fe = Some events →
    ∃ prefix, Forall (λ event, bound < event.2) prefix ∧
      f (Some events) = Some (prefix ++ events)%list) →
  extends bound cache (partial_alter f fe cache).
Proof.
  intro Hf. unfold partial_alter, TLB.VATLB.partial_alter_fe.
  apply alter_entries_extends. intros entry events Hin.
  eapply partial_alter_assoc_extends; [|exact Hin].
  intros old Hlookup. apply Hf. exact Hlookup.
Qed.

Lemma invalidate_all_extends bound time tlbi cache :
  bound < time →
  extends bound cache (TLB.VATLB.map_fe
    (λ fe events, if decide (TLB.affects tlbi fe)
      then (TLB.Entry.Tlbi (TLBI.tid tlbi), time) :: events else events) cache).
Proof.
  intro Htime. apply map_fe_extends. intros fe events.
  destruct (decide (TLB.affects tlbi fe)).
  - exists [(TLB.Entry.Tlbi (TLBI.tid tlbi), time)]. split; [|reflexivity].
    constructor; [exact Htime|constructor].
  - exists []. split; [constructor|reflexivity].
Qed.

Lemma fill_entry_extends bound time fe old new loaded :
  bound < time → TLB.fill_entry time fe old = Ok (new, loaded) →
  extends bound (TLB.vatlb old) (TLB.vatlb new).
Proof.
  intros Htime Hfill. unfold TLB.fill_entry in Hfill. cbn in Hfill.
  unfold mget in Hfill.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose in Hfill. cbn in Hfill.
  destruct (TLB.vatlb old !! fe) as [events|] eqn:Hlookup; rewrite Hlookup in Hfill.
  - destruct events as [|[event stamp] rest].
    + unfold mret, result_ret in Hfill. injection Hfill as <- <-.
      apply update_entry_extends. intros events Hget.
      rewrite Hlookup in Hget. injection Hget as <-.
      exists [(TLB.Entry.Load, time)]. split; [constructor; [exact Htime|constructor]|reflexivity].
    + destruct event.
      * unfold mret, result_ret in Hfill. injection Hfill as <- <-. apply extends_refl.
      * unfold mret, result_ret in Hfill. injection Hfill as <- <-.
        apply update_entry_extends. intros events Hget.
        rewrite Hlookup in Hget. injection Hget as <-.
        exists [(TLB.Entry.Load, time)]. split; [constructor; [exact Htime|constructor]|reflexivity].
  - destruct (decide (TLB.FE.is_table fe));
      unfold mret, result_ret, mbind, result_bind in Hfill; cbn in Hfill;
      injection Hfill as <- <-.
    all: apply update_entry_extends; intros events Hget; rewrite Hlookup in Hget; discriminate.
Qed.

(** An existing full entry keeps every bounded translation choice after a
    cache extension, with the possibly tightened deadline proved safe. *)
Theorem extended_cache_candidate bound old new ctxt fe events tid ifetch tmin tmax inv result :
  extends bound old new → tmax ≤ bound →
  (fe, events) ∈ TLB.VATLB.get_fe old ctxt →
  result ∈ TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    events tmin tmax inv →
  ∃ events' result',
    (fe, events') ∈ TLB.VATLB.get_fe new ctxt ∧
    result' ∈ TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      events' tmin tmax inv ∧
    same_translation bound result result' ∧
    ∀ access, access ≤ bound →
      (if TLB.Result.inv_time result is Some deadline then access < deadline else True) →
      (if TLB.Result.inv_time result' is Some deadline then access < deadline else True).
Proof.
  intros Hextends Hmax Hentry Hresult.
  destruct (Hextends ctxt fe events Hentry) as [prefix [Hprefix Hentry']].
  destruct (future_prefix_candidate tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    bound prefix events tmin tmax inv result Hprefix Hmax Hresult)
    as [result' [Hin [Hsame Haccess]]].
  exists (prefix ++ events)%list, result'. split; [exact Hentry'|].
  split; [exact Hin|]. split; assumption.
Qed.
End VMCacheReplay.
