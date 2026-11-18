(******************************************************************************)
(* Context/promise exchange and the allocation condition for exact rollback   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache
  PromiseFirstSailVMCacheHistory PromiseFirstSailVMCacheRollback PromiseFirstSailVMCacheConfig PromiseFirstSailVMBBM.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheExchange.
Import VMPromising VMCacheReplay VMCacheRollback VMCacheHistory.

Lemma past_past before after events : before ≤ after →
  past before (past after events) = past before events.
Proof.
  intro Htime. unfold past. rewrite list_filter_filter.
  apply list_filter_iff. intros [event time]. cbn. lia.
Qed.

Lemma rows_rows {A} before after (entries : list (A * TLB.Entry.events)) : before ≤ after →
  rows before (rows after entries) = rows before entries.
Proof.
  intro Htime. induction entries as [|[key events] entries IH]; [reflexivity|].
  rewrite rows_cons. destruct (decide (past after events ≠ [])) as [Hlive|Hempty].
  - rewrite rows_cons, past_past by exact Htime. rewrite IH, rows_cons. reflexivity.
  - assert (Hpast : past before events = []).
    { rewrite <- (past_past before after events Htime).
      destruct (past after events); [reflexivity|exfalso; apply Hempty; discriminate]. }
    rewrite IH, rows_cons, Hpast, decide_False by tauto. reflexivity.
Qed.

Lemma same_past_mono before after old new : before ≤ after →
  same_past after old new → same_past before old new.
Proof.
  intros Htime Hsame ctxt.
  rewrite <- (rows_rows before after (TLB.VATLB.get ctxt old) Htime),
    <- (rows_rows before after (TLB.VATLB.get ctxt new) Htime).
  rewrite Hsame. reflexivity.
Qed.

(** The observable histories after the actual rollback are equal, including
    histories of entries allocated only by the future event. *)
Theorem fill_promise_rollback_rows tid imem mem ev time old issued rolled_old rolled_issued :
  time ≤ length mem →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.roll_back time old = Ok (rolled_old, ()) →
  TLB.roll_back time issued = Ok (rolled_issued, ()) →
  ∀ ctxt,
    filter (λ entry, entry.2 ≠ []) (TLB.VATLB.get ctxt (TLB.vatlb rolled_old)) =
    filter (λ entry, entry.2 ≠ []) (TLB.VATLB.get ctxt (TLB.vatlb rolled_issued)).
Proof.
  intros Htime Hpromise Hold Hissued ctxt.
  change (@Ok string _ (set TLB.vatlb (TLB.VATLB.map_fe (λ _, past time)) old, ()) = Ok (rolled_old, ())) in Hold.
  change (@Ok string _ (set TLB.vatlb (TLB.VATLB.map_fe (λ _, past time)) issued, ()) = Ok (rolled_issued, ())) in Hissued.
  injection Hold as <-. injection Hissued as <-. cbn [TLB.vatlb].
  rewrite !get_map_fe.
  apply (same_past_mono time (length mem) _ _ Htime).
  apply (fill_promise_same_past tid imem mem ev old issued Hpromise).
Qed.

Definition unique_entries (cache : TLB.t) :=
  ∀ ctxt, NoDup (map fst (TLB.VATLB.get ctxt (TLB.vatlb cache))).

(** Allocation layout includes dormant entries and the physical-page index.
    Keeping it fixed is stronger than equality of visible histories. *)
Definition same_layout (old new : TLB.t) :=
  TLB.VATLB.map_fe (λ _ _, []) (TLB.vatlb old) =
    TLB.VATLB.map_fe (λ _ _, []) (TLB.vatlb new) ∧
  TLB.pte_present old = TLB.pte_present new ∧
  TLB.next_table_cache old = TLB.next_table_cache new ∧
  TLB.asid_roots old = TLB.asid_roots new ∧ TLB.ets old = TLB.ets new.

Definition same_allocations (old new : TLB.t) :=
  TLB.VATLB.map_fe (λ _ _, []) (TLB.vatlb old) =
    TLB.VATLB.map_fe (λ _ _, []) (TLB.vatlb new) ∧
  TLB.next_table_cache old = TLB.next_table_cache new.

Lemma fill_promise_layout tid imem mem ev old issued :
  same_allocations old issued →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  same_layout old issued.
Proof.
  intros [Hvatlb Hindex] Hpromise.
  pose proof (VMCacheConfig.fill_promise tid imem (ev :: mem) ev old issued () Hpromise) as Hconfig.
  pose proof (VMCacheRoots.fill_promise tid imem (ev :: mem) ev old issued () Hpromise) as Hroots.
  unfold VMCacheConfig.config in Hconfig. unfold VMCacheRoots.config in Hroots.
  unfold same_layout. split; [exact Hvatlb|]. split; [congruence|].
  split; [exact Hindex|]. split; congruence.
Qed.

Lemma hvec_ext {n} {T : fin n → Type} (old new : hvec T) :
  (∀ index, hget index old = hget index new) → old = new.
Proof.
  revert T old new. induction n as [|n IH]; intros T old new Hsame.
  - destruct old, new. reflexivity.
  - destruct old as [head tail], new as [head' tail'].
    pose proof (Hsame 0%fin) as Hhead. cbn in Hhead. subst head'.
    f_equal. apply IH. intro index. exact (Hsame (FS index)).
Qed.

Lemma map_keys {K V W} (f : K → V → W) (entries : list (K * V)) :
  map fst (map (λ '(key, value), (key, f key value)) entries) = map fst entries.
Proof. rewrite map_map. apply map_ext. intros [key value]. reflexivity. Qed.

Lemma restore_empty_rows {K} (old new : list (K * TLB.Entry.events)) :
  NoDup (map fst old) → map fst old = map fst new →
  filter (λ entry, entry.2 ≠ []) old = filter (λ entry, entry.2 ≠ []) new → old = new.
Proof.
  revert new. induction old as [|[key events] old IH]; intros new Hunique Hkeys Hlive;
    destruct new as [|[key' events'] new]; try discriminate; [reflexivity|].
  cbn [map fst] in Hkeys. injection Hkeys as <- Hkeys.
  apply list.NoDup_cons in Hunique as [Hfresh Hunique].
  change (key ∉ map fst old) in Hfresh.
  rewrite !filter_cons in Hlive. cbn in Hlive.
  match type of Hlive with (if ?b then _ else _) = _ => destruct b as [Hliveold|Hemptyold] end;
    match type of Hlive with _ = (if ?b then _ else _) => destruct b as [Hlivenew|Hemptynew] end.
  - injection Hlive as Hevents Hlive. subst events'. f_equal. eapply IH; eassumption.
  - exfalso. apply Hfresh. rewrite Hkeys.
    assert (Hin : (key, events) ∈ filter (λ entry : K * TLB.Entry.events, entry.2 ≠ []) new).
    { rewrite <- Hlive. left. }
    apply list_elem_of_filter in Hin as [_ Hin]. apply list_elem_of_fmap. exists (key, events). auto.
  - exfalso. apply Hfresh.
    assert (Hin : (key, events') ∈ filter (λ entry : K * TLB.Entry.events, entry.2 ≠ []) old).
    { rewrite Hlive. left. }
    apply list_elem_of_filter in Hin as [_ Hin]. apply list_elem_of_fmap. exists (key, events'). auto.
  - assert (events = []) by (destruct events; [reflexivity|exfalso; apply Hemptyold; discriminate]).
    assert (events' = []) by (destruct events'; [reflexivity|exfalso; apply Hemptynew; discriminate]).
    subst events events'. f_equal. eapply IH; eassumption.
Qed.

Lemma past_layout_vatlb time old new :
  unique_entries old → same_layout old new → same_past time (TLB.vatlb old) (TLB.vatlb new) →
  TLB.VATLB.map_fe (λ _, past time) (TLB.vatlb old) =
    TLB.VATLB.map_fe (λ _, past time) (TLB.vatlb new).
Proof.
  intros Hunique [Hlayout _] Hpast. apply hvec_ext. intro lvl. apply (map_eq (M := gmap (TLB.NDCtxt.t lvl))). intro nd.
  pose proof (f_equal (λ cache, hget lvl cache !! nd) Hlayout) as Hshape.
  unfold TLB.VATLB.map_fe in Hshape |- *.
  rewrite !hget_hmap, !lookup_total_imap in Hshape |- *.
  specialize (Hpast (existT lvl nd)). specialize (Hunique (existT lvl nd)).
  change (rows time (default [] (hget lvl (TLB.vatlb old) !! nd)) =
    rows time (default [] (hget lvl (TLB.vatlb new) !! nd))) in Hpast.
  change (NoDup (map fst (default [] (hget lvl (TLB.vatlb old) !! nd)))) in Hunique.
  destruct (hget lvl (TLB.vatlb old) !! nd) as [entries|] eqn:Hold;
    destruct (hget lvl (TLB.vatlb new) !! nd) as [entries'|] eqn:Hnew;
    rewrite Hold, Hnew in Hshape |- *; cbn in Hshape; try discriminate; [|reflexivity].
  rewrite ?Hold, ?Hnew in Hpast. rewrite ?Hold in Hunique.
  injection Hshape as Hshape.
  pose proof (f_equal (map fst) Hshape) as Hkeys. rewrite !map_keys in Hkeys.
  cbn in Hpast, Hunique.
  change (Some (map (λ '(entry, events), (entry, past time events)) entries) =
    Some (map (λ '(entry, events), (entry, past time events)) entries')).
  f_equal. apply restore_empty_rows.
  - rewrite map_keys. exact Hunique.
  - rewrite !map_keys. exact Hkeys.
  - exact Hpast.
Qed.

Definition rolled time (cache : TLB.t) :=
  set TLB.vatlb (TLB.VATLB.map_fe (λ _, past time)) cache.

Lemma past_layout_rolled time old new :
  unique_entries old → same_layout old new → same_past time (TLB.vatlb old) (TLB.vatlb new) →
  rolled time old = rolled time new.
Proof.
  intros Hunique Hlayout Hpast.
  pose proof (past_layout_vatlb time old new Hunique Hlayout Hpast) as Hvatlb.
  destruct Hlayout as [_ [Hpte [Hindex [Hroots Hets]]]].
  destruct old, new. unfold rolled. cbn in *. congruence.
Qed.

Theorem fill_promise_rolled tid imem mem ev time old issued :
  time ≤ length mem → unique_entries old → same_allocations old issued →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  rolled time old = rolled time issued.
Proof.
  intros Htime Hunique Hlayout Hpromise. apply past_layout_rolled; [exact Hunique| |].
  - eapply fill_promise_layout; eassumption.
  - eapply same_past_mono; [exact Htime|]. eapply fill_promise_same_past. exact Hpromise.
Qed.

Lemma fill_cse_rolled tid imem mem time ttbr0 ttbr1 old new :
  rolled time old = rolled time new →
  TLB.fill_cse tid imem mem time ttbr0 ttbr1 old =
    TLB.fill_cse tid imem mem time ttbr0 ttbr1 new.
Proof.
  intro Hrolled.
  assert (Hback : TLB.roll_back time old = TLB.roll_back time new).
  { change (@Ok string _ (rolled time old, ()) = Ok (rolled time new, ())).
    rewrite Hrolled. reflexivity. }
  unfold TLB.fill_cse, mbind, st_bind. rewrite Hback. reflexivity.
Qed.

Lemma fill_asid_root_rolled tid imem mem root time old new :
  rolled time old = rolled time new →
  TLB.fill_asid_root tid imem mem root time old =
    TLB.fill_asid_root tid imem mem root time new.
Proof.
  intro Hrolled.
  assert (Hback : TLB.roll_back time old = TLB.roll_back time new).
  { change (@Ok string _ (rolled time old, ()) = Ok (rolled time new, ())).
    rewrite Hrolled. reflexivity. }
  unfold TLB.fill_asid_root, mbind, st_bind. rewrite Hback. reflexivity.
Qed.

Theorem fill_cse_exchange tid imem mem ev time ttbr0 ttbr1 old issued after_cse :
  time ≤ length mem → unique_entries old → same_allocations old issued →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_cse tid imem mem time ttbr0 ttbr1 old = Ok (after_cse, ()) →
  TLB.fill_cse tid imem (ev :: mem) time ttbr0 ttbr1 issued =
    TLB.fill_promise tid imem (ev :: mem) ev after_cse.
Proof.
  intros Htime Hunique Hlayout Hpromise Hcse.
  rewrite <- (fill_cse_rolled tid imem (ev :: mem) time ttbr0 ttbr1 old issued
    (fill_promise_rolled tid imem mem ev time old issued Htime Hunique Hlayout Hpromise)).
  apply fill_cse_future_promise; assumption.
Qed.

Lemma fill_asid_root_roots tid imem mem root time old new :
  TLB.fill_asid_root tid imem mem root time old = Ok (new, ()) →
  TLB.asid_roots new = (root, time) :: TLB.asid_roots old.
Proof.
  intro Hrun. unfold TLB.fill_asid_root in Hrun.
  set (start := set TLB.asid_roots (cons (root, time)) (rolled time old)).
  change ((TLB.fill_from_roots imem mem time [root] start ≫=
    λ '(mid, _), TLB.fill_from tid imem mem (TLB.asid_roots mid) (S time) mid) = Ok (new, ())) in Hrun.
  destruct (TLB.fill_from_roots imem mem time [root] start) as [[mid []]|err] eqn:Hfirst;
    [|discriminate].
  pose proof (VMCacheRoots.fill_from_roots imem mem time [root] start mid () Hfirst) as Hmid.
  cbn [mbind result_bind] in Hrun.
  pose proof (VMCacheRoots.fill_from_btw tid imem mem (TLB.asid_roots mid)
    (S time) (length mem) mem mid new () Hrun) as Hnew.
  unfold VMCacheRoots.config in Hmid, Hnew. rewrite Hnew, Hmid. reflexivity.
Qed.

Lemma fill_asid_root_future_promise tid imem mem ev root time old after_root :
  time ≤ length mem →
  Forall (λ entry, entry.2 ≤ length mem) (TLB.asid_roots old) →
  TLB.fill_asid_root tid imem mem root time old = Ok (after_root, ()) →
  TLB.fill_asid_root tid imem (ev :: mem) root time old =
    TLB.fill_promise tid imem (ev :: mem) ev after_root.
Proof.
  intros Htime Hroots Hroot. rewrite fill_asid_root_future by assumption.
  unfold mbind, st_bind, result_bind. rewrite Hroot.
  pose proof (fill_asid_root_roots tid imem mem root time old after_root Hroot) as Hafter.
  unfold TLB.fill_promise.
  change (TLB.fill_event tid imem (ev :: mem) (S (length mem))
    (root :: (TLB.asid_roots old).*1) ev after_root =
    TLB.fill_event tid imem (ev :: mem) (S (length mem))
      (TLB.asid_roots after_root).*1 ev after_root).
  rewrite Hafter. reflexivity.
Qed.

Theorem fill_asid_root_exchange tid imem mem ev root time old issued after_root :
  time ≤ length mem → unique_entries old → same_allocations old issued →
  Forall (λ entry, entry.2 ≤ length mem) (TLB.asid_roots old) →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.fill_asid_root tid imem mem root time old = Ok (after_root, ()) →
  TLB.fill_asid_root tid imem (ev :: mem) root time issued =
    TLB.fill_promise tid imem (ev :: mem) ev after_root.
Proof.
  intros Htime Hunique Hlayout Hroots Hpromise Hroot.
  rewrite <- (fill_asid_root_rolled tid imem (ev :: mem) root time old issued
    (fill_promise_rolled tid imem mem ev time old issued Htime Hunique Hlayout Hpromise)).
  apply fill_asid_root_future_promise; assumption.
Qed.

(** Pairwise BBM validation at rollback also ignores entries allocated only
    by the future promise; no allocation-layout assumption is needed here. *)
Theorem fill_promise_rollback_pairs tid imem mem ev time old issued rolled_old rolled_issued
    check_mem addrs bound ctxt :
  time ≤ length mem →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (issued, ()) →
  TLB.roll_back time old = Ok (rolled_old, ()) →
  TLB.roll_back time issued = Ok (rolled_issued, ()) →
  BBM.for_all_pairs
    (λ '(e1, events1) '(e2, events2),
      negb <$> BBM.is_bbm_violation imem check_mem addrs bound ctxt e1 e2 events1 events2)
    (TLB.VATLB.get ctxt (TLB.vatlb rolled_old)) =
  BBM.for_all_pairs
    (λ '(e1, events1) '(e2, events2),
      negb <$> BBM.is_bbm_violation imem check_mem addrs bound ctxt e1 e2 events1 events2)
    (TLB.VATLB.get ctxt (TLB.vatlb rolled_issued)).
Proof.
  intros Htime Hpromise Hold Hissued.
  rewrite <- (VMBBMReplay.pair_check_nonempty imem check_mem addrs bound ctxt
    (TLB.VATLB.get ctxt (TLB.vatlb rolled_old))),
    <- (VMBBMReplay.pair_check_nonempty imem check_mem addrs bound ctxt
      (TLB.VATLB.get ctxt (TLB.vatlb rolled_issued))).
  rewrite (fill_promise_rollback_rows tid imem mem ev time old issued rolled_old rolled_issued
    Htime Hpromise Hold Hissued ctxt). reflexivity.
Qed.

End VMCacheExchange.
