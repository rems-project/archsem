(******************************************************************************)
(* Replay of uncacheable descendants of cached table entries                  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMInterval PromiseFirstSailVMTranslation
  PromiseFirstSailVMLookup PromiseFirstSailVMRootLookup PromiseFirstSailRead
  PromiseFirstSailVMCache PromiseFirstSailVMCacheFill PromiseFirstSailVMBounds
  PromiseFirstSailVMGuards.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMTableReplay.
Import VMPromising VMIntervalReplay VMTranslationReplay.

(** The two-list traversal makes the same decisions when parent interval
    starts are unchanged. Larger interval ends only add available choices. *)
Lemma uncacheable_extends bound old new ptes tmin tmax tmax' lvl result :
  Forall2 (extends_translation bound) old new → tmax ≤ tmax' →
  result ∈ TLB.get_results_from_events_uncacheable_aux old ptes tmin tmax lvl →
  ∃ result', result' ∈ TLB.get_results_from_events_uncacheable_aux new ptes tmin tmax' lvl ∧
    extends_translation bound result result'.
Proof.
  intro Hsame. revert ptes tmax tmax' result.
  induction Hsame as [|old new olds news Hhead Htail IH]; intros ptes tmax tmax' result Hmax Hin.
  - inversion Hin.
  - destruct old as [ttbr path start stop inv], new as [ttbr' path' start' stop' inv'].
    destruct Hhead as [Hr [Hp [Hs [He Hi]]]]. cbn in Hr, Hp, Hs, He, Hi.
    subst ttbr' path' start'.
    revert tmax tmax' result Hmax Hin.
    induction ptes as [|[pte time] ptes IHptes]; intros tmax tmax' result Hmax Hin;
      [inversion Hin|].
    cbn [TLB.get_results_from_events_uncacheable_aux TLB.Result.tend TLB.Result.tstart] in Hin |- *.
    destruct (decide (min stop tmax < tmin)) as [Hempty|Hrange]; [inversion Hin|].
    rewrite decide_False by lia.
    destruct (decide (time ≤ start)); destruct (decide (is_tlb_fillable lvl pte)).
    + eapply IH; eassumption.
    + apply elem_of_cons in Hin as [->|Hin].
      * eexists. split; [left; reflexivity|].
        unfold extends_translation. cbn. repeat split; try reflexivity; try lia. exact Hi.
      * destruct (IH _ _ _ _ Hmax Hin) as [result' [Hmember Hext]].
        exists result'. split; [right; exact Hmember|exact Hext].
    + eapply IHptes; [apply Nat.le_refl|exact Hin].
    + apply elem_of_cons in Hin as [->|Hin].
      * eexists. split; [left; reflexivity|].
        unfold extends_translation. cbn. repeat split; try reflexivity; try lia. exact Hi.
      * destruct (IHptes _ _ _ (Nat.le_refl _) Hin) as [result' [Hmember Hext]].
        exists result'. split; [right; exact Hmember|exact Hext].
Qed.

Lemma extends_Forall2_refl bound results :
  Forall2 (extends_translation bound) results results.
Proof. induction results; constructor; [apply extends_translation_refl|assumption]. Qed.

(** Widening past the end of a cache's recorded history preserves the list
    of parent intervals in order, including adjacent load/invalidation pairs. *)
Lemma bounded_parents_widen tid ifetch ttbr path bound events tmin tmax tmax' inv :
  Forall (λ event, event.2 ≤ bound) events →
  tmin ≤ tmax → bound ≤ tmax → tmax ≤ tmax' →
  Forall2 (extends_translation bound)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax' inv).
Proof.
  revert tmin tmax tmax' inv.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmin tmax tmax' inv Hbound Hrange Htime Hmax.
  destruct events as [|[event time] events].
  - cbn [TLB.get_results_from_events]. rewrite (decide_False (P := tmax < tmin)), (decide_False (P := tmax' < tmin)) by lia. constructor.
  - apply Forall_cons in Hbound as [Hstamp Htail]. cbn in Hstamp.
    cbn [TLB.get_results_from_events]. rewrite (decide_False (P := tmax < tmin)), (decide_False (P := tmax' < tmin)) by lia.
    destruct event.
    + destruct (decide (tmax < time)); [lia|].
      destruct (decide (tmax' < time)); [lia|]. destruct (decide (time < tmin)).
      * constructor; [apply extends_translation_make, Hmax|constructor].
      * destruct events as [|[event' time'] rest].
        -- cbn [TLB.get_results_from_events]. rewrite (decide_False (P := tmax < tmin)), (decide_False (P := tmax' < tmin)) by lia.
           constructor; [apply extends_translation_make, Hmax|constructor].
        -- destruct event'.
           ++ constructor; [apply extends_translation_make, Hmax|].
              apply IH; [unfold ltof; cbn; lia|exact Htail|exact Hrange|exact Htime|exact Hmax].
           ++ destruct (decide (time = time' ∧ (ifetch ∨ tid0 = tid))).
              ** destruct rest as [|[[|issuer] stamp] rest].
                 2: apply IH; [unfold ltof; cbn; lia| |exact Hrange|exact Htime|exact Hmax].
                 2: apply Forall_cons in Htail; tauto.
                 all: constructor; [apply extends_translation_make, Hmax|].
                 all: apply IH; [unfold ltof; cbn; lia|exact Htail|exact Hrange|exact Htime|exact Hmax].
              ** constructor; [apply extends_translation_make, Hmax|].
                 apply IH; [unfold ltof; cbn; lia|exact Htail|exact Hrange|exact Htime|exact Hmax].
    + rewrite !Nat.min_r by lia. apply extends_Forall2_refl.
Qed.

Lemma same_extends_Forall2 bound old mid new :
  Forall2 (same_translation bound) old mid →
  Forall2 (extends_translation bound) mid new →
  Forall2 (extends_translation bound) old new.
Proof.
  intro Hsame. revert new. induction Hsame; intros new Hext; inversion Hext; subst; constructor.
  - eapply extends_translation_trans; [apply same_translation_extends; eassumption|eassumption].
  - eauto.
Qed.

(** New cache markers can add parent intervals above the old bound. Every
    old parent interval remains behind that prefix, in the same order. *)
Lemma parents_future_prefix tid ifetch ttbr path bound prefix events tmin tmax inv inv' :
  Forall (λ event, bound < event.2) prefix →
  Forall (λ event, event.2 ≤ bound) events →
  tmin ≤ bound → bound ≤ tmax → inv_after bound inv inv' →
  ∃ extra results,
    TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin tmax inv' =
      (extra ++ results)%list ∧
    Forall (λ result, bound < TLB.Result.tstart result ∧ bound ≤ TLB.Result.tend result) extra ∧
    Forall2 (extends_translation bound)
      (TLB.get_results_from_events tid ifetch ttbr path events tmin bound inv) results.
Proof.
  revert tmax inv'.
  induction prefix as [prefix IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmax inv' Hprefix Hevents Hmin Hmax Hinv.
  destruct prefix as [|[event time] prefix].
  - exists [], (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv').
    split; [reflexivity|]. split; [constructor|].
    eapply same_extends_Forall2.
    + apply lookup_change_initial_inv, Hinv.
    + apply bounded_parents_widen; try assumption; lia.
  - apply Forall_cons in Hprefix as [Htime Hprefix]. cbn in Htime.
    cbn [app TLB.get_results_from_events]. rewrite decide_False by lia.
    destruct event as [|issuer].
    + destruct (decide (tmax < time)).
      * apply IH; [unfold ltof; cbn; lia|exact Hprefix|exact Hevents|exact Hmin|exact Hmax|exact Hinv].
      * rewrite decide_False by lia.
        destruct prefix as [|[event' time'] prefix].
        -- cbn [app]. destruct events as [|[event' time'] events].
           ++ cbn [TLB.get_results_from_events]. rewrite decide_False by lia.
              eexists [_], []. split; [reflexivity|]. split.
              ** constructor; [split; assumption|constructor].
              ** cbn [TLB.get_results_from_events]. rewrite decide_False by lia. constructor.
           ++ assert (Hstamp : time' ≤ bound) by (apply Forall_cons in Hevents as [H _]; exact H).
              destruct event'; [|rewrite decide_False by lia].
              all: eexists [_], (TLB.get_results_from_events tid ifetch ttbr path _ tmin tmax inv').
              all: split; [reflexivity|]; split; [constructor; [split; assumption|constructor]|].
              all: eapply same_extends_Forall2; [apply lookup_change_initial_inv, Hinv|].
              all: apply bounded_parents_widen; try assumption; lia.
        -- cbn [app]. destruct event'.
           ++ destruct (IH ((TLB.Entry.Load, time') :: prefix) ltac:(unfold ltof; cbn; lia)
                tmax inv' Hprefix Hevents Hmin Hmax Hinv) as [extra [results [Heq [Hextra Hresults]]]].
              rewrite Heq. exists (TLB.Result.make ttbr path time tmax inv' :: extra), results.
              split; [reflexivity|]. split; [constructor; [split; assumption|exact Hextra]|exact Hresults].
           ++ destruct (decide (time = time' ∧ (ifetch ∨ tid0 = tid))).
              ** destruct (IH prefix ltac:(unfold ltof; cbn; lia) tmax inv'
                   ltac:(apply Forall_cons in Hprefix; tauto) Hevents Hmin Hmax Hinv)
                   as [extra [results [Heq [Hextra Hresults]]]].
                 destruct (prefix ++ events)%list as [|[[|issuer'] stamp] rest] eqn:Hnext.
                 2: exists extra, results; auto.
                 all: destruct (IH ((TLB.Entry.Tlbi tid0, time') :: prefix)
                   ltac:(unfold ltof; cbn; lia) tmax inv' Hprefix Hevents Hmin Hmax Hinv)
                   as [extra' [results' [Heq' [Hextra' Hresults']]]].
                 all: cbn [app] in Heq'; rewrite Hnext in Heq'; rewrite Heq'.
                 all: exists (TLB.Result.make ttbr path time tmax inv' :: extra'), results';
                   split; [reflexivity|]; split;
                   [constructor; [split; assumption|exact Hextra']|exact Hresults'].
              ** destruct (IH ((TLB.Entry.Tlbi tid0, time') :: prefix) ltac:(unfold ltof; cbn; lia)
                   tmax inv' Hprefix Hevents Hmin Hmax Hinv) as [extra [results [Heq [Hextra Hresults]]]].
                 rewrite Heq. exists (TLB.Result.make ttbr path time tmax inv' :: extra), results.
                 split; [reflexivity|]. split; [constructor; [split; assumption|exact Hextra]|exact Hresults].
    + apply IH; [unfold ltof; cbn; lia|exact Hprefix|exact Hevents|exact Hmin|lia|].
      destruct (decide (ifetch ∨ issuer = tid)); [exact Hinv|]. right. exists time. auto.
Qed.

Lemma uncacheable_future_parents bound extra parents ptes tmin tmax lvl result :
  Forall (λ parent, bound < TLB.Result.tstart parent ∧ bound ≤ TLB.Result.tend parent) extra →
  Forall (λ pte, pte.2 ≤ bound) ptes → tmin ≤ bound → bound ≤ tmax →
  result ∈ TLB.get_results_from_events_uncacheable_aux parents ptes tmin tmax lvl →
  result ∈ TLB.get_results_from_events_uncacheable_aux (extra ++ parents)%list ptes tmin tmax lvl.
Proof.
  intros Hextra Hptes Hmin Hmax Hin. induction Hextra as [|parent extra [Hstart Hend] Hextra IH];
    [exact Hin|].
  destruct ptes as [|[pte time] ptes]; [destruct parents; inversion Hin|].
  apply Forall_cons in Hptes as [Htime Hptes]. cbn in Htime.
  cbn [app TLB.get_results_from_events_uncacheable_aux].
  rewrite decide_False by lia. rewrite (decide_True (P := time ≤ TLB.Result.tstart parent)) by lia.
  destruct (decide (is_tlb_fillable lvl pte)); [exact IH|right; exact IH].
Qed.

(** Prefixing future parent intervals preserves every old table lookup when
    its descriptor-read list stays unchanged. *)
Theorem uncacheable_future_history tid ifetch ttbr path bound prefix events ptes
    tmin tmax lvl result :
  Forall (λ event, bound < event.2) prefix →
  Forall (λ event, event.2 ≤ bound) events →
  Forall (λ pte, pte.2 ≤ bound) ptes → tmin ≤ bound → bound ≤ tmax →
  result ∈ TLB.get_results_from_events_uncacheable_aux
    (TLB.get_results_from_events tid ifetch ttbr path events tmin bound None)
    ptes tmin bound lvl →
  ∃ result', result' ∈ TLB.get_results_from_events_uncacheable_aux
    (TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin tmax None)
    ptes tmin tmax lvl ∧ extends_translation bound result result'.
Proof.
  intros Hprefix Hevents Hptes Hmin Hmax Hin.
  destruct (parents_future_prefix tid ifetch ttbr path bound prefix events tmin tmax None None
    Hprefix Hevents Hmin Hmax (or_introl eq_refl)) as [extra [parents [Heq [Hextra Hparents]]]].
  destruct (uncacheable_extends bound _ parents ptes tmin bound tmax lvl result
    Hparents Hmax Hin) as [result' [Hmember Hext]].
  exists result'. split; [|exact Hext]. rewrite Heq.
  eapply uncacheable_future_parents; eassumption.
Qed.

Lemma bytes_imap_bounded addr msg time bytes :
  Forall (λ byte, byte.2 ≤ time) bytes →
  Forall (λ byte, byte.2 ≤ time)
    (imap (λ idx byte_time,
      if Msg.read_byte (addr `+Z` Z.of_nat idx)%bv msg is Some byte
      then (byte, time) else byte_time) bytes).
Proof.
  intros Hbytes. apply Forall_forall. intros byte Hin.
  apply elem_of_lookup_imap in Hin as [idx [old [-> Hlookup]]].
  destruct (Msg.read_byte _ msg); [cbn; lia|].
  apply (proj1 (Forall_forall _ _) Hbytes), list_elem_of_lookup. eauto.
Qed.

Lemma read_from_aux_bounded {E} (get_msg : E → option Msg.t) addr size imem mem time bytes :
  PromMemory.read_from_aux get_msg addr size imem mem time = Ok bytes →
  Forall (λ byte, byte.2 ≤ time) bytes.
Proof.
  revert mem bytes. induction time as [|time IH]; intros mem bytes Hread.
  - destruct mem; cbn [PromMemory.read_from_aux] in Hread;
      destruct (mem_lookup_bytes addr size imem) as [bs|];
      unfold othrow in Hread; cbn in Hread; try discriminate;
      injection Hread as <-; apply Forall_fmap, Forall_forall; intros; cbn; lia.
  - destruct mem as [|ev mem]; [discriminate|].
    cbn [PromMemory.read_from_aux] in Hread.
    destruct (get_msg ev) as [msg|].
    + destruct (decide (Msg.addr msg = addr ∧ Msg.size msg = size)).
      * injection Hread as <-. apply Forall_fmap, Forall_forall. intros; cbn; lia.
      * destruct (PromMemory.read_from_aux get_msg addr size imem mem time)
          as [old|err] eqn:Hold; [|discriminate].
        assert (Hbound : Forall (λ byte, byte.2 ≤ S time) old).
        { eapply Forall_impl; [eapply IH; exact Hold|]. intros byte Hbyte. cbn in Hbyte |- *. lia. }
        cbn in Hread. destruct (decide (Msg.overlap addr size msg)); injection Hread as <-.
        -- apply bytes_imap_bounded, Hbound.
        -- exact Hbound.
    + eapply Forall_impl; [eapply IH; exact Hread|]. intros byte Hbyte. cbn in Hbyte |- *. lia.
Qed.


Lemma read_all_aux_bounded {E} (get_msg : E → option Msg.t) addr size imem mem tmin time candidates :
  PromMemory.read_all_aux get_msg addr size imem mem tmin time = Ok candidates →
  Forall (Forall (λ byte, byte.2 ≤ time)) candidates.
Proof.
  revert time candidates. induction mem as [|ev mem IH]; intros time candidates Hread;
    cbn [PromMemory.read_all_aux] in Hread;
    destruct (time =? tmin)%stdpp eqn:Heq.
  all: try (apply bool_decide_eq_true_1 in Heq; subst tmin;
    match type of Hread with context[PromMemory.read_from_aux ?f ?a ?s ?i ?m ?t] =>
      destruct (PromMemory.read_from_aux f a s i m t) as [bytes|err] eqn:Hbytes end;
    cbn in Hread; [injection Hread as <-; constructor;
      [eapply read_from_aux_bounded; exact Hbytes|constructor]|discriminate]).
  - destruct time; discriminate.
  - destruct time as [|time]; [discriminate|].
    destruct (PromMemory.read_all_aux get_msg addr size imem mem tmin time)
      as [old|err] eqn:Hold; [|discriminate].
    assert (Hbound : Forall (Forall (λ byte, byte.2 ≤ S time)) old).
    { eapply Forall_impl; [eapply IH; exact Hold|].
      intros bytes Hbytes. eapply Forall_impl; [exact Hbytes|].
      intros byte Hbyte. cbn in Hbyte |- *. lia. }
    cbn in Hread. destruct (get_msg ev) as [msg|]; [|injection Hread as <-; exact Hbound].
    match type of Hread with context[if ?b then _ else _] => destruct b end.
    + injection Hread as <-. constructor; [|exact Hbound].
      apply Forall_fmap, Forall_forall. intros; cbn; lia.
    + match type of Hread with context[if ?b then _ else _] => destruct b end; [|injection Hread as <-; exact Hbound].
      destruct old as [|bytes old]; [discriminate|]. injection Hread as <-.
      constructor; [apply bytes_imap_bounded; apply Forall_cons in Hbound; tauto|exact Hbound].

Qed.

Lemma max_bytes_bound time bytes :
  Forall (λ byte : bv 8 * nat, byte.2 ≤ time) bytes → max_list_with snd bytes ≤ time.
Proof.
  intro Hbytes. rewrite max_list_with_foldr. induction Hbytes; cbn; lia.
Qed.

Lemma read_all_pte_bounded addr imem mem tmin tmax ptes :
  Memory.read_all_pte addr imem mem tmin tmax = Ok ptes →
  Forall (λ pte, pte.2 ≤ tmax) ptes.
Proof.
  unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw.
  destruct (decide (tmin ≤ tmax)); [|injection 1 as <-; constructor].
  destruct (PromMemory.read_all_aux Ev.get_msg addr 8 imem
    (PromMemory.cut_before tmax mem) tmin tmax) as [bytes|err] eqn:Hbytes;
    [|discriminate].
  injection 1 as <-. apply Forall_fmap.
  eapply Forall_impl; [eapply read_all_aux_bounded; exact Hbytes|].
  intros bs Hbs. cbn. apply max_bytes_bound, Hbs.
Qed.

Lemma read_all_pte_nonwrite addr imem mem ev tmin :
  Ev.get_msg ev = None → tmin ≤ length mem →
  Memory.read_all_pte addr imem (ev :: mem) tmin (S (length mem)) =
    Memory.read_all_pte addr imem mem tmin (length mem).
Proof.
  intros Hnone Hmin. unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw.
  rewrite !decide_True by lia.
  unfold PromMemory.cut_before. cbn [length]. rewrite !Nat.sub_diag, !drop_0.
  cbn [PromMemory.read_all_aux].
  rewrite bool_decide_false by lia.
  destruct (PromMemory.read_all_aux Ev.get_msg addr 8 imem mem tmin (length mem));
    cbn; [rewrite Hnone; reflexivity|reflexivity].
Qed.

Theorem table_nonwrite_future tid imem mem ev ifetch vpn fe events prefix tmin candidates result :
  Ev.get_msg ev = None →
  Forall (λ event, length mem < event.2) prefix →
  Forall (λ event, event.2 ≤ length mem) events →
  TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin (length mem) = Ok candidates →
  result ∈ candidates →
  ∃ candidates' result',
    TLB.get_result_from_table_FE tid imem (ev :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin (S (length mem)) = Ok candidates' ∧
    result' ∈ candidates' ∧ extends_translation (length mem) result result'.
Proof.
  intros Hnone Hprefix Hevents Hread Hin.
  unfold TLB.get_result_from_table_FE in Hread |- *.
  destruct (decide (length mem < tmin)); [injection Hread as <-; inversion Hin|].
  rewrite decide_False by lia.
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection Hread as <-; inversion Hin].
  destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    events tmin (length mem) None) as [|parent parents] eqn:Hparents;
    [injection Hread as <-; inversion Hin|].
  destruct (Memory.read_all_pte _ imem mem tmin (length mem)) as [ptes|err] eqn:Hptes;
    [|discriminate]. injection Hread as <-.
  pose proof (read_all_pte_bounded _ imem mem tmin (length mem) ptes Hptes) as Hptes_bound.
  change (result ∈ TLB.get_results_from_events_uncacheable_aux
    (parent :: parents) ptes tmin (length mem) lvl) in Hin.
  rewrite <- Hparents in Hin.
  destruct (uncacheable_future_history tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (length mem) prefix events ptes tmin (S (length mem)) lvl result
    Hprefix Hevents Hptes_bound ltac:(lia) ltac:(lia) Hin) as [result' [Hmember Hext]].
  destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (prefix ++ events)%list tmin (S (length mem)) None) as [|parent' parents'];
    [inversion Hmember|].
  rewrite read_all_pte_nonwrite by assumption || lia. rewrite Hptes.
  eexists _, result'. split; [reflexivity|]. auto.
Qed.

Definition cache_bounded bound (cache : TLB.t) : Prop :=
  ∀ ctxt fe events, (fe, events) ∈ TLB.VATLB.get_fe (TLB.vatlb cache) ctxt →
    Forall (λ event, event.2 ≤ bound) events.

Theorem lookup_nonwrite_future tid imem mem ev old new ifetch upper vpn
    tmin_ok tmin_unc asid result :
  Ev.get_msg ev = None → cache_bounded (length mem) old →
  VMCacheReplay.extends (length mem) (TLB.vatlb old) (TLB.vatlb new) →
  Exec.elem_of_results result
    (TLB.lookup tid imem mem old ifetch upper vpn tmin_ok tmin_unc (length mem) asid) →
  ∃ result', Exec.elem_of_results result'
    (TLB.lookup tid imem (ev :: mem) new ifetch upper vpn tmin_ok tmin_unc (S (length mem)) asid) ∧
    extends_translation (length mem) result result'.
Proof.
  intros Hnone Hbounded Hextends Hin.
  apply VMLookupReplay.lookup_witness in Hin as [fe [events [candidates [Hentry [Hread Hin]]]]].
  apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [Hctxt Hentry]].
  destruct (Hextends ctxt fe events Hentry) as [prefix [Hprefix Hentry']].
  assert (Hreplay : ∃ candidates' result',
    TLB.get_result_from_FE tid imem (ev :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin_ok tmin_unc (S (length mem)) = Ok candidates' ∧
    result' ∈ candidates' ∧ extends_translation (length mem) result result').
  { unfold TLB.get_result_from_FE in Hread |- *.
    destruct (decide (TLB.FE.is_table fe)).
    - eapply table_nonwrite_future; [exact Hnone|exact Hprefix|eapply Hbounded; exact Hentry|exact Hread|exact Hin].
    - unfold TLB.get_result_from_leaf_FE in Hread |- *.
      destruct (decide (length mem < tmin_ok)); [injection Hread as <-; inversion Hin|].
      rewrite decide_False by lia. injection Hread as <-.
      destruct (future_prefix_larger_bound tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
        (length mem) prefix events tmin_ok (length mem) (S (length mem)) None result
        Hprefix ltac:(lia) ltac:(lia) Hin) as [result' [Hmember Hext]].
      eexists _, result'. split; [reflexivity|]. auto. }
  destruct Hreplay as [candidates' [result' [Hread' [Hmember Hext]]]].
  exists result'. split; [|exact Hext]. apply VMLookupReplay.lookup_witness.
  exists fe, (prefix ++ events)%list, candidates'. split; [|auto].
  apply VMLookupReplay.get_fes_witness. exists ctxt. auto.
Qed.

Local Lemma merge_success {E A} (result : A) (left right : Exec.res E A) :
  Exec.elem_of_results result (Exec.merge left right) ↔
    Exec.elem_of_results result left ∨ Exec.elem_of_results result right.
Proof. unfold Exec.elem_of_results, Exec.merge. cbn. apply elem_of_app. Qed.

(** Actual promise emission chooses either the former bound or its successor.
    A TLBI changes cache histories but leaves all descriptor bytes unchanged. *)
Theorem emit_tlbi_lookup tid imem mem tlbi recipient epoch ts issued old ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc result :
  TState.tlb ts = Some old → cache_bounded (length mem) old →
  TState.emit_promise tid imem (Ev.Tlbi tlbi recipient epoch :: mem)
    (Ev.Tlbi tlbi recipient epoch) ts = Ok issued →
  Exec.elem_of_results result (TState.tlb_lookup tid imem mem ts ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc (pred (TState.min_promise (length mem) ts))) →
  ∃ result', Exec.elem_of_results result'
    (TState.tlb_lookup tid imem (Ev.Tlbi tlbi recipient epoch :: mem) issued ifetch upper vpn
      asid ttbr0 tmin_ok tmin_unc
      (pred (TState.min_promise (S (length mem)) issued))) ∧
    extends_translation (length mem) result result'.
Proof.
  intros Hcache Hbounded Hpromise Hin.
  destruct (VMBoundsReplay.emit_promise_translation_bound_cases tid imem mem
    (Ev.Tlbi tlbi recipient epoch) ts issued Hpromise) as [Hsame|[Hold Hnew]].
  - cbn [length] in Hsame. rewrite Hsame.
    destruct (VMLookupReplay.emit_promise_lookup_replay tid imem mem
      (Ev.Tlbi tlbi recipient epoch) ts issued ifetch upper vpn asid ttbr0 tmin_ok tmin_unc
      (pred (TState.min_promise (length mem) ts)) result Hpromise ltac:(pose proof (VMGuardReplay.min_promise_bound (length mem) ts); lia) Hin)
      as [result' [Hmember Hext]].
    exists result'. split; [exact Hmember|apply same_translation_extends, Hext].
  - cbn [length] in Hnew. rewrite Hnew. rewrite Hold in Hin.
    destruct (VMCacheFillReplay.emit_promise_cache_extends tid imem mem
      (Ev.Tlbi tlbi recipient epoch) ts issued old Hcache Hpromise)
      as [new [Hcache' Hextends]].
    unfold TState.tlb_lookup in Hin |- *. rewrite Hcache in Hin. rewrite Hcache'.
    apply merge_success in Hin as [Hcached|Hroot].
    + destruct (lookup_nonwrite_future tid imem mem (Ev.Tlbi tlbi recipient epoch)
        old new ifetch upper vpn tmin_ok tmin_unc asid result eq_refl Hbounded Hextends Hcached)
        as [result' [Hmember Hext]].
      exists result'. split; [apply merge_success; left; exact Hmember|exact Hext].
    + destruct (VMRootLookupReplay.root_lookup_larger_bound imem mem
        (Ev.Tlbi tlbi recipient epoch) ts issued upper vpn ttbr0 tmin_unc
        (length mem) (S (length mem)) result
        (VMLookupReplay.emit_promise_preserves_sreg tid imem
          (Ev.Tlbi tlbi recipient epoch :: mem) (Ev.Tlbi tlbi recipient epoch)
          ts issued TTBR1_EL1 Hpromise) ltac:(lia) ltac:(lia) ltac:(lia) Hroot)
        as [result' [Hmember Hext]].
      exists result'. split; [apply merge_success; right; exact Hmember|exact Hext].
Qed.

End VMTableReplay.
