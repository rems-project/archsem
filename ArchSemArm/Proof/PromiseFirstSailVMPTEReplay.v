(******************************************************************************)
(* Descriptor-read deltas and table replay after a new memory event           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMTableReplay
  PromiseFirstSailVMInterval PromiseFirstSailVMTranslation PromiseFirstSailRead
  PromiseFirstSailVMLookup PromiseFirstSailVMCache PromiseFirstSailVMCacheFill
  PromiseFirstSailVMBounds PromiseFirstSailVMGuards PromiseFirstSailVMRootLookup
  PromiseFirstConcreteCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMPTEReplay.
Import VMPromising VMTableReplay VMIntervalReplay VMTranslationReplay.

Lemma imap_update_max time (f : nat → bv 8 * nat → bv 8 * nat) bytes :
  Forall (λ byte, byte.2 ≤ time) bytes →
  (∀ idx byte, f idx byte = byte ∨ (f idx byte).2 = time) →
  imap f bytes = bytes ∨ max_list_with snd (imap f bytes) = time.
Proof.
  unfold imap, list_imap. intro Hbytes. revert f. induction Hbytes as [|byte bytes Hbyte Hbytes IH]; intros f Hf.
  - left. reflexivity.
  - rewrite imap_cons. destruct (IH (f ∘ S) ltac:(intros; apply Hf)) as [Hsame|Hmax];
      destruct (Hf 0 byte) as [Hhead|Hhead].
    + left. rewrite Hsame, Hhead. reflexivity.
    + right. rewrite Hsame, max_list_with_foldr. cbn. rewrite Hhead.
      pose proof (max_bytes_bound time bytes Hbytes) as Hbound.
      rewrite max_list_with_foldr in Hbound. lia.
    + right. rewrite max_list_with_foldr in Hmax |- *. cbn. rewrite Hhead. lia.
    + right. rewrite max_list_with_foldr in Hmax |- *. cbn. rewrite Hhead. lia.
Qed.

Lemma updated_bytes_delta addr msg time bytes :
  Forall (λ byte, byte.2 ≤ time) bytes →
  let updated := imap (λ idx byte_time,
    if Msg.read_byte (addr `+Z` Z.of_nat idx)%bv msg is Some byte
    then (byte, time) else byte_time) bytes in
  updated = bytes ∨ max_list_with snd updated = time.
Proof.
  intro Hbytes. cbn zeta. apply imap_update_max; [exact Hbytes|].
  intros idx byte. destruct (Msg.read_byte _ msg); [right|left]; reflexivity.
Qed.

Lemma full_write_timestamp (msg : Msg.t) time :
  Msg.size msg = 8%N →
  max_list_with snd (map (λ byte, (byte, time)) (bv_to_bytes 8 (Msg.val msg))) = time.
Proof.
  intro Hsize. assert (Hlen : length (bv_to_bytes 8 (Msg.val msg)) = 8).
  { rewrite length_bv_to_bytes, Hsize. reflexivity. }
  destruct (bv_to_bytes 8 (Msg.val msg)) as [|b bs]; [discriminate|].
  assert (Hbound : max_list_with snd (map (λ byte, (byte, time)) bs) ≤ time).
  { apply max_bytes_bound, Forall_fmap, Forall_forall. intros; cbn; lia. }
  rewrite max_list_with_foldr in Hbound |- *. cbn. lia.
Qed.

(** A write adds one timestamped descriptor value. A partial write that
    changes none of the returned bytes only duplicates the first candidate. *)
Definition descriptor_delta (time : nat) (old new : list (bv 64 * nat)) : Prop :=
  new = old ∨
  (∃ pte, new = (pte, time) :: old) ∨
  (∃ first rest, old = first :: rest ∧ new = first :: old).

Lemma read_all_pte_delta addr imem mem ev tmin ptes :
  tmin ≤ length mem →
  Memory.read_all_pte addr imem mem tmin (length mem) = Ok ptes →
  ∃ ptes', Memory.read_all_pte addr imem (ev :: mem) tmin (S (length mem)) = Ok ptes' ∧
    descriptor_delta (S (length mem)) ptes ptes'.
Proof.
  intros Hmin Hread.
  unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw in Hread |- *.
  rewrite decide_True in Hread by exact Hmin. rewrite decide_True by lia.
  unfold PromMemory.cut_before in Hread |- *. cbn [length].
  rewrite Nat.sub_diag, drop_0 in Hread. rewrite Nat.sub_diag, drop_0.
  destruct (PromMemory.read_all_aux Ev.get_msg addr 8 imem mem tmin (length mem))
    as [bytes|err] eqn:Hbytes; [|discriminate]. injection Hread as <-.
  pose proof (read_all_aux_success_nonempty Ev.get_msg addr 8 imem mem tmin
    (length mem) bytes Hbytes) as Hnonempty.
  pose proof (read_all_aux_bounded Ev.get_msg addr 8 imem mem tmin (length mem)
    bytes Hbytes) as Hbound.
  cbn [PromMemory.read_all_aux]. rewrite bool_decide_false by lia. rewrite Hbytes. cbn.
  destruct (Ev.get_msg ev) as [msg|].
  - match goal with |- context[if ?b then _ else _] => destruct b as [Hfull|Hfull] end.
    + destruct Hfull as [_ Hsize]. eexists. split; [reflexivity|].
      right. left. eexists. cbn. rewrite full_write_timestamp by exact Hsize. reflexivity.
    + match goal with |- context[if ?b then _ else _] => destruct b end.
      * destruct bytes as [|first rest]; [contradiction|].
        apply Forall_cons in Hbound as [Hfirst Hrest].
        assert (Hfirst' : Forall (λ byte, byte.2 ≤ S (length mem)) first).
        { eapply Forall_impl; [exact Hfirst|]. intros byte Hbyte. cbn in Hbyte |- *. lia. }
        destruct (updated_bytes_delta addr msg (S (length mem)) first Hfirst') as [Hsame|Hstamp].
        -- eexists. split; [reflexivity|]. right. right. cbn.
           rewrite Hsame. eexists _, _. auto.
        -- eexists. split; [reflexivity|]. right. left. cbn.
           rewrite Hstamp. eexists. reflexivity.
      * eexists. split; [reflexivity|]. left. reflexivity.
  - eexists. split; [reflexivity|]. left. reflexivity.
Qed.

Lemma uncacheable_member_range parent parents ptes tmin tmax lvl result :
  result ∈ TLB.get_results_from_events_uncacheable_aux (parent :: parents) ptes tmin tmax lvl →
  tmin ≤ min (TLB.Result.tend parent) tmax.
Proof.
  destruct ptes as [|[pte time] ptes]; [inversion 1|].
  cbn [TLB.get_results_from_events_uncacheable_aux].
  destruct (decide (min (TLB.Result.tend parent) tmax < tmin)); [inversion 1|lia].
Qed.

Lemma uncacheable_prepend_late parent parents ptes tmin tmax pte time lvl result :
  TLB.Result.tstart parent < time → pred time ≤ tmax →
  result ∈ TLB.get_results_from_events_uncacheable_aux (parent :: parents) ptes tmin (pred time) lvl →
  result ∈ TLB.get_results_from_events_uncacheable_aux (parent :: parents)
    ((pte, time) :: ptes) tmin tmax lvl.
Proof.
  intros Hstart Hmax Hin.
  pose proof (uncacheable_member_range parent parents ptes tmin (pred time) lvl result Hin) as Hrange.
  cbn [TLB.get_results_from_events_uncacheable_aux].
  rewrite decide_False by lia.
  rewrite (decide_False (P := time ≤ TLB.Result.tstart parent)) by lia.
  destruct (decide (is_tlb_fillable lvl pte)); [exact Hin|right; exact Hin].
Qed.

Lemma uncacheable_duplicate parents pte time ptes tmin tmax lvl result :
  result ∈ TLB.get_results_from_events_uncacheable_aux parents ((pte, time) :: ptes) tmin tmax lvl →
  result ∈ TLB.get_results_from_events_uncacheable_aux parents
    ((pte, time) :: (pte, time) :: ptes) tmin tmax lvl.
Proof.
  revert tmax result. induction parents as [|parent parents IH]; intros tmax result Hin;
    [inversion Hin|].
  cbn [TLB.get_results_from_events_uncacheable_aux] in Hin |- *.
  destruct (decide (min (TLB.Result.tend parent) tmax < tmin)); [inversion Hin|].
  destruct (decide (time ≤ TLB.Result.tstart parent)) as [Hstart|Hstart];
    destruct (decide (is_tlb_fillable lvl pte)) as [Hfill|Hfill].
  - apply IH, Hin.
  - apply elem_of_cons in Hin as [->|Hin]; [left; reflexivity|right; apply IH, Hin].
  - pose proof (uncacheable_prepend_late parent parents ptes tmin (pred time)
      pte time lvl result ltac:(lia) ltac:(lia) Hin) as Hlate.
    cbn [TLB.get_results_from_events_uncacheable_aux] in Hlate.
    rewrite (decide_False (P := time ≤ TLB.Result.tstart parent)) in Hlate by lia.
    rewrite (decide_True (P := is_tlb_fillable lvl pte)) in Hlate by exact Hfill.
    exact Hlate.
  - apply elem_of_cons in Hin as [->|Hin]; [left; reflexivity|right].
    pose proof (uncacheable_prepend_late parent parents ptes tmin (pred time)
      pte time lvl result ltac:(lia) ltac:(lia) Hin) as Hlate.
    cbn [TLB.get_results_from_events_uncacheable_aux] in Hlate.
    rewrite (decide_False (P := time ≤ TLB.Result.tstart parent)) in Hlate by lia.
    rewrite (decide_False (P := is_tlb_fillable lvl pte)) in Hlate by exact Hfill.
    exact Hlate.
Qed.

Lemma uncacheable_future_parents_one bound extra parents ptes tmin tmax lvl result :
  Forall (λ parent, bound < TLB.Result.tstart parent ∧ bound ≤ TLB.Result.tend parent) extra →
  Forall (λ pte, pte.2 ≤ S bound) ptes → tmin ≤ bound → bound ≤ tmax →
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

Lemma parent_start_bound tid ifetch ttbr path events tmin tmax inv :
  Forall (λ parent, TLB.Result.tstart parent ≤ tmax)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof.
  revert tmin tmax inv.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmin tmax inv. destruct events as [|[event time] events];
    cbn [TLB.get_results_from_events]; destruct (decide (tmax < tmin)); try constructor.
  destruct event as [|issuer].
  - destruct (decide (tmax < time)); [apply IH; unfold ltof; cbn; lia|].
    destruct (decide (time < tmin)); [constructor; [cbn; lia|constructor]|].
    destruct events as [|[event' time'] rest].
    + constructor; [cbn; lia|]. cbn [TLB.get_results_from_events].
      rewrite decide_False by assumption. constructor.
    + destruct event' as [|issuer].
      * constructor; [cbn; lia|apply IH; unfold ltof; cbn; lia].
      * destruct (decide (time = time' ∧ (ifetch ∨ issuer = tid))).
        -- destruct rest as [|[[|issuer'] stamp] rest];
             first [apply IH; unfold ltof; cbn; lia
               |constructor; [cbn; lia|apply IH; unfold ltof; cbn; lia]].
        -- constructor; [cbn; lia|apply IH; unfold ltof; cbn; lia].
  - eapply Forall_impl; [apply IH; unfold ltof; cbn; lia|].
    intros parent Hparent. cbn in Hparent |- *. lia.
Qed.

Lemma extends_parent_starts bound old new :
  Forall2 (extends_translation bound) old new →
  Forall (λ parent, TLB.Result.tstart parent ≤ bound) old →
  Forall (λ parent, TLB.Result.tstart parent ≤ bound) new.
Proof.
  intro Hparents. induction Hparents as [|old new olds news Hhead Htail IH];
    intro Hstarts; [constructor|].
  apply Forall_cons in Hstarts as [Hstart Hstarts]. constructor; [|auto].
  destruct Hhead as [_ [_ [Hstart' _]]]. rewrite Hstart'. exact Hstart.
Qed.

Lemma uncacheable_descriptor_delta bound old new ptes ptes' tmin lvl result :
  Forall2 (extends_translation bound) old new →
  Forall (λ parent, TLB.Result.tstart parent ≤ bound) old →
  descriptor_delta (S bound) ptes ptes' →
  result ∈ TLB.get_results_from_events_uncacheable_aux old ptes tmin bound lvl →
  ∃ result', result' ∈ TLB.get_results_from_events_uncacheable_aux new ptes' tmin (S bound) lvl ∧
    extends_translation bound result result'.
Proof.
  intros Hparents Hstarts Hdelta Hin.
  destruct Hdelta as [->|[[pte ->]|[first [rest [Hptes ->]]]]].
  - eapply uncacheable_extends with (tmax := bound); [exact Hparents|lia|exact Hin].
  - destruct (uncacheable_extends bound old new ptes tmin bound bound lvl result
      Hparents ltac:(lia) Hin) as [result' [Hmember Hext]].
    pose proof (extends_parent_starts bound old new Hparents Hstarts) as Hnewstarts.
    destruct new as [|parent parents]; [inversion Hmember|].
    apply Forall_cons in Hnewstarts as [Hstart _].
    exists result'. split; [|exact Hext].
    apply uncacheable_prepend_late; [lia|cbn; lia|exact Hmember].
  - destruct first as [pte time]. subst ptes.
    destruct (uncacheable_extends bound old new ((pte, time) :: rest) tmin bound (S bound)
      lvl result Hparents ltac:(lia) Hin) as [result' [Hmember Hext]].
    exists result'. split; [apply uncacheable_duplicate, Hmember|exact Hext].
Qed.

Theorem uncacheable_write_history tid ifetch ttbr path bound prefix events ptes ptes'
    tmin lvl result :
  Forall (λ event, bound < event.2) prefix →
  Forall (λ event, event.2 ≤ bound) events →
  Forall (λ pte, pte.2 ≤ S bound) ptes' → tmin ≤ bound →
  descriptor_delta (S bound) ptes ptes' →
  result ∈ TLB.get_results_from_events_uncacheable_aux
    (TLB.get_results_from_events tid ifetch ttbr path events tmin bound None)
    ptes tmin bound lvl →
  ∃ result', result' ∈ TLB.get_results_from_events_uncacheable_aux
    (TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin (S bound) None)
    ptes' tmin (S bound) lvl ∧ extends_translation bound result result'.
Proof.
  intros Hprefix Hevents Hptes Hmin Hdelta Hin.
  destruct (parents_future_prefix tid ifetch ttbr path bound prefix events tmin (S bound) None None
    Hprefix Hevents Hmin ltac:(lia) (or_introl eq_refl)) as [extra [parents [Heq [Hextra Hparents]]]].
  destruct (uncacheable_descriptor_delta bound _ parents ptes ptes' tmin lvl result
    Hparents (parent_start_bound tid ifetch ttbr path events tmin bound None) Hdelta Hin)
    as [result' [Hmember Hext]].
  exists result'. split; [|exact Hext]. rewrite Heq.
  eapply uncacheable_future_parents_one; try eassumption; lia.
Qed.

(** All shared events, including full and partial descriptor writes, preserve
    old table candidates when the query grows by one timestamp. *)
Theorem table_future tid imem mem ev ifetch vpn fe events prefix tmin candidates result :
  Forall (λ event, length mem < event.2) prefix →
  Forall (λ event, event.2 ≤ length mem) events →
  TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin (length mem) = Ok candidates →
  result ∈ candidates →
  ∃ candidates' result',
    TLB.get_result_from_table_FE tid imem (ev :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin (S (length mem)) = Ok candidates' ∧
    result' ∈ candidates' ∧ extends_translation (length mem) result result'.
Proof.
  intros Hprefix Hevents Hread Hin.
  unfold TLB.get_result_from_table_FE in Hread |- *.
  destruct (decide (length mem < tmin)); [injection Hread as <-; inversion Hin|].
  rewrite decide_False by lia.
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection Hread as <-; inversion Hin].
  destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    events tmin (length mem) None) as [|parent parents] eqn:Hparents;
    [injection Hread as <-; inversion Hin|].
  destruct (Memory.read_all_pte _ imem mem tmin (length mem)) as [ptes|err] eqn:Hptes;
    [|discriminate]. injection Hread as <-.
  change (result ∈ TLB.get_results_from_events_uncacheable_aux
    (parent :: parents) ptes tmin (length mem) lvl) in Hin.
  rewrite <- Hparents in Hin.
  destruct (read_all_pte_delta _ imem mem ev tmin ptes ltac:(lia) Hptes)
    as [ptes' [Hptes' Hdelta]].
  pose proof (read_all_pte_bounded _ imem (ev :: mem) tmin (S (length mem)) ptes' Hptes') as Hptes_bound.
  destruct (uncacheable_write_history tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (length mem) prefix events ptes ptes' tmin lvl result
    Hprefix Hevents Hptes_bound ltac:(lia) Hdelta Hin) as [result' [Hmember Hext]].
  destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (prefix ++ events)%list tmin (S (length mem)) None) as [|parent' parents'];
    [inversion Hmember|].
  rewrite Hptes'. eexists _, result'. split; [reflexivity|]. auto.
Qed.

Theorem lookup_future tid imem mem ev old new ifetch upper vpn
    tmin_ok tmin_unc asid result :
  cache_bounded (length mem) old →
  VMCacheReplay.extends (length mem) (TLB.vatlb old) (TLB.vatlb new) →
  Exec.elem_of_results result
    (TLB.lookup tid imem mem old ifetch upper vpn tmin_ok tmin_unc (length mem) asid) →
  ∃ result', Exec.elem_of_results result'
    (TLB.lookup tid imem (ev :: mem) new ifetch upper vpn tmin_ok tmin_unc (S (length mem)) asid) ∧
    extends_translation (length mem) result result'.
Proof.
  intros Hbounded Hextends Hin.
  apply VMLookupReplay.lookup_witness in Hin as [fe [events [candidates [Hentry [Hread Hin]]]]].
  apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [Hctxt Hentry]].
  destruct (Hextends ctxt fe events Hentry) as [prefix [Hprefix Hentry']].
  assert (Hreplay : ∃ candidates' result',
    TLB.get_result_from_FE tid imem (ev :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin_ok tmin_unc (S (length mem)) = Ok candidates' ∧
    result' ∈ candidates' ∧ extends_translation (length mem) result result').
  { unfold TLB.get_result_from_FE in Hread |- *.
    destruct (decide (TLB.FE.is_table fe)).
    - eapply table_future; [exact Hprefix|eapply Hbounded; exact Hentry|exact Hread|exact Hin].
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
    Descriptor replay handles arbitrary full and partial PTE writes. *)
Theorem emit_promise_lookup tid imem mem ev ts issued old ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc result :
  TState.tlb ts = Some old → cache_bounded (length mem) old →
  TState.emit_promise tid imem (ev :: mem)
    ev ts = Ok issued →
  Exec.elem_of_results result (TState.tlb_lookup tid imem mem ts ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc (pred (TState.min_promise (length mem) ts))) →
  ∃ result', Exec.elem_of_results result'
    (TState.tlb_lookup tid imem (ev :: mem) issued ifetch upper vpn
      asid ttbr0 tmin_ok tmin_unc
      (pred (TState.min_promise (S (length mem)) issued))) ∧
    extends_translation (length mem) result result'.
Proof.
  intros Hcache Hbounded Hpromise Hin.
  destruct (VMBoundsReplay.emit_promise_translation_bound_cases tid imem mem
    ev ts issued Hpromise) as [Hsame|[Hold Hnew]].
  - cbn [length] in Hsame. rewrite Hsame.
    destruct (VMLookupReplay.emit_promise_lookup_replay tid imem mem
      ev ts issued ifetch upper vpn asid ttbr0 tmin_ok tmin_unc
      (pred (TState.min_promise (length mem) ts)) result Hpromise ltac:(pose proof (VMGuardReplay.min_promise_bound (length mem) ts); lia) Hin)
      as [result' [Hmember Hext]].
    exists result'. split; [exact Hmember|apply same_translation_extends, Hext].
  - cbn [length] in Hnew. rewrite Hnew. rewrite Hold in Hin.
    destruct (VMCacheFillReplay.emit_promise_cache_extends tid imem mem
      ev ts issued old Hcache Hpromise)
      as [new [Hcache' Hextends]].
    unfold TState.tlb_lookup in Hin |- *. rewrite Hcache in Hin. rewrite Hcache'.
    apply merge_success in Hin as [Hcached|Hroot].
    + destruct (lookup_future tid imem mem ev
        old new ifetch upper vpn tmin_ok tmin_unc asid result Hbounded Hextends Hcached)
        as [result' [Hmember Hext]].
      exists result'. split; [apply merge_success; left; exact Hmember|exact Hext].
    + destruct (VMRootLookupReplay.root_lookup_larger_bound imem mem
        ev ts issued upper vpn ttbr0 tmin_unc
        (length mem) (S (length mem)) result
        (VMLookupReplay.emit_promise_preserves_sreg tid imem
          (ev :: mem) ev
          ts issued TTBR1_EL1 Hpromise) ltac:(lia) ltac:(lia) ltac:(lia) Hroot)
        as [result' [Hmember Hext]].
      exists result'. split; [apply merge_success; right; exact Hmember|exact Hext].
Qed.

#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState.
#[local] Typeclasses Transparent Memory.t.

(** Global delivery uses this for every thread, independently of which thread
    owns the write or receives an invalidation. *)
Theorem global_promise_lookup bbm {n} (tid : fin n)
    (st next : PState.t TState.t Ev.t n) ev old ifetch upper vpn
    asid ttbr0 tmin_ok tmin_unc result :
  PState.promise (VMPromising bbm) ev st = Ok next →
  TState.tlb (PState.tstate tid st) = Some old →
  cache_bounded (length (PState.events st)) old →
  Exec.elem_of_results result
    (TState.tlb_lookup tid (PState.initmem st) (PState.events st) (PState.tstate tid st)
      ifetch upper vpn asid ttbr0 tmin_ok tmin_unc
      (pred (TState.min_promise (length (PState.events st)) (PState.tstate tid st)))) →
  ∃ result', Exec.elem_of_results result'
    (TState.tlb_lookup tid (PState.initmem next) (PState.events next) (PState.tstate tid next)
      ifetch upper vpn asid ttbr0 tmin_ok tmin_unc
      (pred (TState.min_promise (length (PState.events next)) (PState.tstate tid next)))) ∧
    extends_translation (length (PState.events st)) result result'.
Proof.
  intros Hpromise Hcache Hbounded Hin.
  destruct (VMPromising_promise_success ev st next Hpromise) as [Himem [Hevents Hstates]].
  rewrite Himem, Hevents. eapply emit_promise_lookup;
    [exact Hcache|exact Hbounded|exact (Hstates tid)|exact Hin].
Qed.

End VMPTEReplay.
