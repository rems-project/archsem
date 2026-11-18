(******************************************************************************)
(* Bidirectional lookup replay with exact interval endpoints                   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMTranslation
  PromiseFirstSailVMInterval PromiseFirstSailVMLookup PromiseFirstSailVMPTEReplay
  PromiseFirstSailVMWalkStart PromiseFirstSailVMTableReplay PromiseFirstSailRead
  PromiseFirstSailVMRootLookup PromiseFirstCurrent PromiseFirstSailVMCacheFuture
  PromiseFirstSailVMCacheState PromiseFirstSailVMViews PromiseFirstSailVMBounds PromiseFirstSailVMGuards
  PromiseFirstSailVMWalkReplay PromiseFirstSailVMNormalization PromiseFirstSailVMDirect
  PromiseFirstSailNoFuel PromiseFirstSailCurrent PromiseFirstVMExecutionCurrent PromiseFirstEquivCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMWalkLookup.
Import VMPromising VMWalkStart.
#[local] Typeclasses Transparent view UMPromising.view.

(** An existing invalidation deadline is preserved. Only an absent deadline
    can become a deadline beyond the original memory history. *)
Definition inv_replay bound (old new : option nat) : Prop :=
  new = old ∨ (old = None ∧ ∃ time, bound < time ∧ new = Some time).

Lemma inv_replay_refl bound inv : inv_replay bound inv inv.
Proof. left. reflexivity. Qed.

Lemma inv_replay_none bound inv :
  VMTranslationReplay.inv_after bound None inv → inv_replay bound None inv.
Proof. intros [H|H]; [left; exact H|right; auto]. Qed.

Lemma res_rel_make bound tmax tmax' ttbr path start stop inv inv' :
  inv_replay bound inv inv' →
  res_rel (TIf bound tmax tmax')
    (TLB.Result.make ttbr path start stop inv)
    (TLB.Result.make ttbr path start stop inv').
Proof.
  intro Hi. unfold res_rel, TIf, ti. cbn. repeat split; try reflexivity.
  - left. reflexivity.
  - exact Hi.
Qed.

(** Changing the initial deadline preserves every result in both directions.
    A TLBI encountered inside the history overwrites both initial deadlines
    with the same value. This also covers histories with consecutive TLBIs. *)
Lemma lookup_change_initial_inv tid ifetch ttbr path bound events tmin tmax
    lo hi inv inv' :
  inv_replay bound inv inv' →
  Forall2 (res_rel (TIf bound lo hi))
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv').
Proof.
  revert tmin tmax inv inv'.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmin tmax inv inv' Hinv.
  destruct events as [|[event time] events].
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); constructor.
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); [constructor|].
    destruct event.
    + destruct (decide (tmax < time)); [apply IH; [unfold ltof; cbn; lia|exact Hinv]|].
      destruct (decide (time < tmin)).
      { constructor; [apply res_rel_make, Hinv|constructor]. }
      destruct events as [|[event' time'] rest].
      * constructor; [apply res_rel_make, Hinv|apply IH; [unfold ltof; cbn; lia|exact Hinv]].
      * destruct event'.
        -- constructor; [apply res_rel_make, Hinv|apply IH; [unfold ltof; cbn; lia|exact Hinv]].
        -- destruct (decide (time = time' ∧ (ifetch ∨ tid0 = tid))).
           ++ destruct rest as [|[[|issuer] stamp] rest];
                first [apply IH; [unfold ltof; cbn; lia|exact Hinv]
                  |constructor; [apply res_rel_make, Hinv
                    |apply IH; [unfold ltof; cbn; lia|exact Hinv]]].
           ++ constructor; [apply res_rel_make, Hinv|apply IH; [unfold ltof; cbn; lia|exact Hinv]].
    + destruct (decide (ifetch ∨ tid0 = tid)).
      * apply IH; [unfold ltof; cbn; lia|exact Hinv].
      * apply IH; [unfold ltof; cbn; lia|apply inv_replay_refl].
Qed.

Theorem future_prefix_exact tid ifetch ttbr path bound prefix events tmin tmax lo hi :
  Forall (λ event, bound < event.2) prefix → tmax ≤ bound →
  Forall2 (res_rel (TIf bound lo hi))
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax None)
    (TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin tmax None).
Proof.
  intros Hprefix Hmax.
  destruct (VMTranslationReplay.future_prefix_lookup tid ifetch ttbr path bound prefix events
    tmin tmax None Hprefix Hmax) as (inv & Hi & He).
  rewrite He. apply lookup_change_initial_inv, inv_replay_none, Hi.
Qed.

Lemma forall2_forward {A B} (R : A → B → Prop) xs ys x :
  Forall2 R xs ys → x ∈ xs → ∃ y, y ∈ ys ∧ R x y.
Proof.
  intro H. induction H as [|a b xs ys Hab Hrest IH]; intro Hx; [inversion Hx|].
  apply elem_of_cons in Hx as [->|Hx].
  - exists b. split; [left; reflexivity|exact Hab].
  - destruct (IH Hx) as (y & Hy & Hr). exists y. split; [right; exact Hy|exact Hr].
Qed.

Lemma forall2_backward {A B} (R : A → B → Prop) xs ys y :
  Forall2 R xs ys → y ∈ ys → ∃ x, x ∈ xs ∧ R x y.
Proof.
  intro H. induction H as [|a b xs ys Hab Hrest IH]; intro Hy; [inversion Hy|].
  apply elem_of_cons in Hy as [->|Hy].
  - exists a. split; [left; reflexivity|exact Hab].
  - destruct (IH Hy) as (x & Hx & Hr). exists x. split; [right; exact Hx|exact Hr].
Qed.

(** A bounded lookup has no additional old-starting alternatives after a
    future prefix. The backward direction is needed when merging results,
    since an extra alternative could otherwise lower a merge class's start. *)
Corollary future_prefix_bi tid ifetch ttbr path bound prefix events tmin tmax :
  Forall (λ event, bound < event.2) prefix → tmax ≤ bound →
  let olds := TLB.get_results_from_events tid ifetch ttbr path events tmin tmax None in
  let news := TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin tmax None in
  (∀ r, r ∈ olds → ∃ r', r' ∈ news ∧ res_rel (TIf bound tmax tmax) r r') ∧
  (∀ r', r' ∈ news → ∃ r, r ∈ olds ∧ res_rel (TIf bound tmax tmax) r r').
Proof.
  intros Hprefix Hmax olds news.
  pose proof (future_prefix_exact tid ifetch ttbr path bound prefix events tmin tmax
    tmax tmax Hprefix Hmax) as H.
  split; intros r Hr.
  - eapply forall2_forward; eassumption.
  - eapply forall2_backward; eassumption.
Qed.

Lemma res_rel_refl bound lo hi r : res_rel (TIf bound lo hi) r r.
Proof.
  unfold res_rel, TIf, ti. repeat split; try reflexivity; left; reflexivity.
Qed.

Lemma results_refl bound lo hi rs : Forall2 (res_rel (TIf bound lo hi)) rs rs.
Proof. induction rs; constructor; [apply res_rel_refl|assumption]. Qed.

(** When the window grows past the whole old history, an interval ending
    below the old bound keeps that endpoint. Intervals ending at the bound
    may grow to the new bound. The correspondence includes the backward
    direction and preserves every existing invalidation deadline. *)
Theorem lookup_larger_bound_exact tid ifetch ttbr path bound events tmin tmax tmax' inv :
  Forall (λ event, event.2 ≤ tmax) events → tmin ≤ tmax → tmax ≤ tmax' →
  Forall2 (res_rel (TIf bound tmax tmax'))
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax' inv).
Proof.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros Hbound Hmin Hmax.
  destruct events as [|[event time] events].
  - cbn [TLB.get_results_from_events]. repeat case_decide; constructor.
  - apply Forall_cons in Hbound as [Ht Hb]. cbn in Ht.
    cbn [TLB.get_results_from_events].
    rewrite (decide_False (P := tmax < tmin)),
      (decide_False (P := tmax' < tmin)) by lia.
    destruct event as [|issuer].
    + rewrite (decide_False (P := tmax < time)),
        (decide_False (P := tmax' < time)) by lia.
      destruct (decide (time < tmin)).
      { constructor; [|constructor]. unfold res_rel, TIf, ti. cbn.
        repeat split; try reflexivity; [right; auto|left; reflexivity]. }
      assert (Hmake : res_rel (TIf bound tmax tmax')
        (TLB.Result.make ttbr path time tmax inv)
        (TLB.Result.make ttbr path time tmax' inv)).
      { unfold res_rel, TIf, ti. cbn. repeat split; try reflexivity;
          [right; auto|left; reflexivity]. }
      destruct events as [|[event' time'] rest].
      * constructor; [exact Hmake|apply IH; [unfold ltof; cbn; lia|exact Hb|exact Hmin|exact Hmax]].
      * destruct event' as [|issuer'].
        -- constructor; [exact Hmake|apply IH; [unfold ltof; cbn; lia|exact Hb|exact Hmin|exact Hmax]].
        -- destruct (decide (time = time' ∧ (ifetch ∨ issuer' = tid))).
           ++ destruct rest as [|[[|issuer''] stamp] rest].
              2: apply IH; [unfold ltof; cbn; lia|apply Forall_cons in Hb as [_ Hb]; exact Hb|exact Hmin|exact Hmax].
              all: constructor; [exact Hmake|apply IH; [unfold ltof; cbn; lia|exact Hb|exact Hmin|exact Hmax]].
           ++ constructor; [exact Hmake|apply IH; [unfold ltof; cbn; lia|exact Hb|exact Hmin|exact Hmax]].
    + rewrite !Nat.min_r by lia. apply results_refl.
Qed.

Lemma filter_replayed bound lo hi olds news :
  Forall2 (res_rel (TIf bound lo hi)) olds news →
  Forall (λ r, TLB.Result.tstart r ≤ bound) olds →
  Forall2 (res_rel (TIf bound lo hi)) olds
    (filter (λ r, TLB.Result.tstart r ≤ bound) news).
Proof.
  intro H. induction H as [|a b olds news Hab Hrest IH]; intro Hb.
  - constructor.
  - apply Forall_cons in Hb as [Ha Hb].
    rewrite filter_cons_True by (destruct Hab as [_ [_ [Hs _]]]; lia).
    constructor; [exact Hab|apply IH, Hb].
Qed.

Lemma filter_events_bound tid ifetch ttbr path events tmin tmax inv bound :
  tmax ≤ bound →
  filter (λ r, TLB.Result.tstart r ≤ bound)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv) =
    TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv.
Proof.
  intro Hle.
  pose proof (VMPTEReplay.parent_start_bound tid ifetch ttbr path events tmin tmax inv) as H.
  induction H as [|r rs Hr Hrs IH]; [reflexivity|].
  rewrite filter_cons_True by lia. f_equal. exact IH.
Qed.

Lemma fresh_load_normal tid ifetch ttbr path bound events tmin :
  Forall (λ event, event.2 ≤ bound) events → tmin ≤ bound →
  TLB.get_results_from_events tid ifetch ttbr path
    ((TLB.Entry.Load, S bound) :: events) tmin (S bound) None =
  TLB.Result.make ttbr path (S bound) (S bound) None ::
    TLB.get_results_from_events tid ifetch ttbr path events tmin (S bound) None.
Proof.
  intros Hb Hmin. cbn [TLB.get_results_from_events].
  rewrite (decide_False (P := S bound < tmin)),
    (decide_False (P := S bound < S bound)),
    (decide_False (P := S bound < tmin)) by lia.
  destruct events as [|[[|issuer] time] rest]; try reflexivity.
  apply Forall_cons in Hb as [Ht _]. cbn in Ht.
  rewrite decide_False by (intros [He _]; lia). reflexivity.
Qed.

Theorem future_prefix_larger_exact tid ifetch ttbr path bound prefix events tmin :
  Forall (λ event, event.2 = S bound) prefix →
  Forall (λ event, event.2 ≤ bound) events → tmin ≤ bound →
  Forall2 (res_rel (TIf bound bound (S bound)))
    (TLB.get_results_from_events tid ifetch ttbr path events tmin bound None)
    (filter (λ r, TLB.Result.tstart r ≤ bound)
      (TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list
        tmin (S bound) None)).
Proof.
  induction prefix as [prefix IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros Hp Hb Hmin.
  destruct prefix as [|[event time] prefix].
  - cbn [app]. apply filter_replayed.
    + apply lookup_larger_bound_exact; try assumption; lia.
    + apply VMPTEReplay.parent_start_bound.
  - apply Forall_cons in Hp as [Ht Hp]. cbn in Ht. subst time.
    destruct event as [|issuer].
    + destruct prefix as [|[event time] rest].
      * cbn [app]. rewrite fresh_load_normal by assumption.
        rewrite filter_cons_False by (cbn; lia).
        apply (IH []); [unfold ltof; cbn; lia|constructor|exact Hb|exact Hmin].
      * apply Forall_cons in Hp as [Ht Hp]. cbn in Ht. subst time.
        cbn [app TLB.get_results_from_events].
        rewrite !(decide_False (P := S bound < tmin)),
          !(decide_False (P := S bound < S bound)) by lia.
        destruct event as [|issuer].
        -- rewrite filter_cons_False by (cbn; lia).
           specialize (IH ((TLB.Entry.Load, S bound) :: rest)
             ltac:(unfold ltof; cbn; lia) ltac:(constructor; [reflexivity|exact Hp]) Hb Hmin).
           cbn [app TLB.get_results_from_events] in IH.
           rewrite !(decide_False (P := S bound < tmin)),
             !(decide_False (P := S bound < S bound)) in IH by lia. exact IH.
        -- destruct (decide (S bound = S bound ∧ (ifetch ∨ issuer = tid))).
           ++ pose proof (IH rest ltac:(unfold ltof; cbn; lia) Hp Hb Hmin) as Hrest.
              specialize (IH ((TLB.Entry.Tlbi issuer, S bound) :: rest)
                ltac:(unfold ltof; cbn; lia) ltac:(constructor; [reflexivity|exact Hp]) Hb Hmin).
              cbn [app TLB.get_results_from_events] in IH.
              rewrite (decide_False (P := S bound < tmin)) in IH by lia.
              destruct (rest ++ events)%list as [|[[|issuer'] stamp] tail] eqn:Hnext.
              2: exact Hrest.
              all: rewrite filter_cons_False by (cbn; lia); exact IH.
           ++ rewrite filter_cons_False by (cbn; lia).
              specialize (IH ((TLB.Entry.Tlbi issuer, S bound) :: rest)
                ltac:(unfold ltof; cbn; lia) ltac:(constructor; [reflexivity|exact Hp]) Hb Hmin).
              cbn [app TLB.get_results_from_events] in IH.
              rewrite (decide_False (P := S bound < tmin)) in IH by lia. exact IH.
    + assert (He : TLB.get_results_from_events tid ifetch ttbr path
        (((TLB.Entry.Tlbi issuer, S bound) :: prefix) ++ events)%list tmin (S bound) None =
        TLB.get_results_from_events tid ifetch ttbr path
        (((TLB.Entry.Tlbi issuer, S bound) :: prefix) ++ events)%list tmin bound None).
      { cbn [app TLB.get_results_from_events].
        rewrite (decide_False (P := S bound < tmin)),
          (decide_False (P := bound < tmin)) by lia.
        rewrite !Nat.min_r by lia. reflexivity. }
      rewrite He, filter_events_bound by lia. apply future_prefix_exact; [|lia].
      constructor; [cbn; lia|]. eapply Forall_impl; [exact Hp|]. intros [e t] Ht. cbn in *. lia.
Qed.

(** An own TLBI, or any TLBI during instruction fetch, does not introduce an
    invalidation deadline. With a fixed window the result lists are equal. *)
Theorem future_prefix_own tid (ifetch : bool) ttbr path bound prefix events tmin tmax inv :
  Forall (λ et, bound < et.2 ∧
    match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => ifetch ∨ issuer = tid end) prefix →
  tmax ≤ bound →
  TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin tmax inv =
  TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv.
Proof.
  intros Hp Hmax. induction Hp as [|[event time] prefix [Ht Ho] Hp IH]; [reflexivity|].
  cbn in Ht, Ho. cbn [app]. destruct event as [|issuer].
  - rewrite VMTranslationReplay.future_load_lookup by lia. exact IH.
  - rewrite VMTranslationReplay.future_tlbi_lookup by lia.
    rewrite decide_True by exact Ho. exact IH.
Qed.

(** The two query-bound cases produced by promise emission: the upper bound
    is unchanged, or it grows from the old history length to its successor. *)
Theorem events_replay_exact tid ifetch ttbr path bound prefix events tmin tmax tmax' :
  Forall (λ event, event.2 = S bound) prefix →
  Forall (λ event, event.2 ≤ bound) events →
  tmin ≤ tmax → tmax ≤ bound →
  (tmax' = tmax ∨ (tmax = bound ∧ tmax' = S bound)) →
  Forall2 (res_rel (TIf bound tmax tmax'))
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax None)
    (filter (λ r, TLB.Result.tstart r ≤ bound)
      (TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list
        tmin tmax' None)).
Proof.
  intros Hp Hb Hmin Hmax [->|[-> ->]].
  - apply filter_replayed.
    + apply future_prefix_exact; [|exact Hmax].
      eapply Forall_impl; [exact Hp|]. intros [e t] Ht. cbn in *. lia.
    + eapply Forall_impl; [apply VMPTEReplay.parent_start_bound|]. cbn. lia.
  - apply future_prefix_larger_exact; assumption.
Qed.

Corollary events_replay_bi tid ifetch ttbr path bound prefix events tmin tmax tmax' :
  Forall (λ event, event.2 = S bound) prefix →
  Forall (λ event, event.2 ≤ bound) events →
  tmin ≤ tmax → tmax ≤ bound →
  (tmax' = tmax ∨ (tmax = bound ∧ tmax' = S bound)) →
  let olds := TLB.get_results_from_events tid ifetch ttbr path events tmin tmax None in
  let news := TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin tmax' None in
  (∀ r, r ∈ olds → ∃ r', r' ∈ news ∧ res_rel (TIf bound tmax tmax') r r') ∧
  (∀ r', r' ∈ news → TLB.Result.tstart r' ≤ bound →
    ∃ r, r ∈ olds ∧ res_rel (TIf bound tmax tmax') r r').
Proof.
  intros Hp Hb Hmin Hmax Hcases olds news.
  pose proof (events_replay_exact tid ifetch ttbr path bound prefix events tmin tmax tmax'
    Hp Hb Hmin Hmax Hcases) as H.
  split.
  - intros r Hr. destruct (forall2_forward _ _ _ _ H Hr) as (r' & Hr' & Hrel).
    apply list_elem_of_filter in Hr' as [_ Hr']. exists r'. auto.
  - intros r' Hr' Hstart. eapply forall2_backward; [exact H|].
    apply list_elem_of_filter. auto.
Qed.

Lemma descriptor_delta_forward time old new pte :
  VMPTEReplay.descriptor_delta time old new → pte ∈ old → pte ∈ new.
Proof.
  intros [->|[(fresh & ->)|(first & rest & -> & ->)]] Hin; [exact Hin|right; exact Hin|right; exact Hin].
Qed.

Lemma descriptor_delta_backward bound old new pte time :
  VMPTEReplay.descriptor_delta (S bound) old new →
  (pte, time) ∈ new → time ≤ bound → (pte, time) ∈ old.
Proof.
  intros [->|[(fresh & ->)|(first & rest & -> & ->)]] Hin Htime; [exact Hin| |].
  - apply elem_of_cons in Hin as [He|Hin]; [injection He; lia|exact Hin].
  - apply elem_of_cons in Hin as [->|Hin]; [left; reflexivity|exact Hin].
Qed.

(** With a fixed query window, descriptor reads are unchanged. The stronger
    deadline relation therefore lifts through the table traversal exactly. *)
Lemma uncacheable_fixed bound query old new ptes tmin tmax lvl :
  Forall2 (res_rel (TIf bound query query)) old new →
  Forall2 (res_rel (TIf bound query query))
    (TLB.get_results_from_events_uncacheable_aux old ptes tmin tmax lvl)
    (TLB.get_results_from_events_uncacheable_aux new ptes tmin tmax lvl).
Proof.
  intro Hsame. revert ptes tmax.
  induction Hsame as [|old new olds news Hhead Htail IH]; intros ptes tmax.
  - constructor.
  - destruct old as [ttbr path start stop inv], new as [ttbr' path' start' stop' inv'].
    destruct Hhead as (Httbr & Hpath & Hstart & Hstop & Hinv).
    cbn in Httbr, Hpath, Hstart, Hstop, Hinv.
    assert (stop' = stop) by (destruct Hstop as [Hstop|[Hstop Hstop']]; congruence).
    subst ttbr' path' start' stop'.
    cbn [TLB.get_results_from_events_uncacheable_aux].
    revert tmax. induction ptes as [|[pte time] ptes IHptes]; intro tmax; [constructor|].
    cbn [TLB.Result.tstart TLB.Result.tend].
    destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
    destruct (decide (time ≤ start));
      destruct (decide (is_tlb_fillable lvl pte));
      try (constructor; [apply res_rel_make, Hinv|]);
      first [apply IH|apply IHptes].
Qed.

Lemma table_future_prefix_exact tid imem mem event ifetch vpn fe events prefix tmin tmax old :
  Forall (λ event, length mem < event.2) prefix → tmax ≤ length mem →
  TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin tmax = Ok old →
  ∃ new,
    TLB.get_result_from_table_FE tid imem (event :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin tmax = Ok new ∧
    Forall2 (res_rel (TIf (length mem) tmax tmax)) old new.
Proof.
  intros Hprefix Hmax. unfold TLB.get_result_from_table_FE.
  destruct (decide (tmax < tmin));
    [injection 1 as <-; exists []; split; [reflexivity|constructor]|].
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|];
    [|injection 1 as <-; exists []; split; [reflexivity|constructor]].
  pose proof (future_prefix_exact tid ifetch (TLB.FE.ttbr fe)
    (TLB.FE.ptes fe) (length mem) prefix events tmin tmax tmax tmax Hprefix Hmax) as Hpre.
  destruct Hpre as [|first first' rest rest' Hfirst Hrest].
  - injection 1 as <-. exists []. split; [reflexivity|constructor].
  - rewrite VMLookupReplay.read_all_pte_future by exact Hmax.
    destruct (Memory.read_all_pte _ imem mem tmin tmax) as [ptes|err];
      cbn; [|discriminate].
    injection 1 as <-. eexists. split; [reflexivity|].
    apply (uncacheable_fixed (length mem) tmax
      (first :: rest) (first' :: rest') ptes tmin tmax lvl).
    constructor; assumption.
Qed.

Lemma entry_future_prefix_exact tid imem mem event ifetch vpn fe events prefix tmin_ok tmin_unc tmax old :
  Forall (λ event, length mem < event.2) prefix → tmax ≤ length mem →
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax = Ok old →
  ∃ new,
    TLB.get_result_from_FE tid imem (event :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin_ok tmin_unc tmax = Ok new ∧
    Forall2 (res_rel (TIf (length mem) tmax tmax)) old new.
Proof.
  intros Hprefix Hmax. unfold TLB.get_result_from_FE.
  destruct (decide (TLB.FE.is_table fe)).
  - apply table_future_prefix_exact; assumption.
  - unfold TLB.get_result_from_leaf_FE.
    destruct (decide (tmax < tmin_ok)).
    + injection 1 as <-. exists []. split; [reflexivity|constructor].
    + injection 1 as <-. eexists. split; [reflexivity|].
      apply future_prefix_exact; assumption.
Qed.

(** Descriptor reads return eight-byte arrays. A positive write that
    overlaps one of these arrays gives it a fresh timestamp, excluding
    unchanged duplicates from the descriptor delta. *)
Lemma initial_bytes_length addr size imem bytes :
  mem_lookup_bytes addr size imem = Some bytes → length bytes = N.to_nat size.
Proof.
  unfold mem_lookup_bytes, list_of_options. intro H.
  apply length_mapM in H. rewrite length_map, addr_range_length in H. lia.
Qed.

Lemma read_from_bytes_length {E} (get_msg : E → option Msg.t) addr imem mem time bytes :
  PromMemory.read_from_aux get_msg addr 8 imem mem time = Ok bytes →
  length bytes = 8.
Proof.
  revert mem bytes. induction time as [|time IH]; intros mem bytes Hread.
  - destruct mem; cbn [PromMemory.read_from_aux] in Hread;
      destruct (mem_lookup_bytes addr 8 imem) as [bs|] eqn:Hbs;
      unfold othrow in Hread; cbn in Hread; try discriminate;
      injection Hread as <-; rewrite length_map; exact (initial_bytes_length addr 8 imem bs Hbs).
  - destruct mem as [|ev mem]; [discriminate|].
    cbn [PromMemory.read_from_aux] in Hread.
    destruct (get_msg ev) as [msg|].
    + destruct (decide (Msg.addr msg = addr ∧ Msg.size msg = 8%N)) as [Hfull|Hfull].
      * injection Hread as <-. rewrite length_map, length_bv_to_bytes.
        destruct Hfull as [_ ->]. reflexivity.
      * destruct (PromMemory.read_from_aux get_msg addr 8 imem mem time)
          as [old|err] eqn:Hold; [|discriminate].
        cbn in Hread. destruct (decide (Msg.overlap addr 8 msg)); injection Hread as <-.
        -- unfold imap, list_imap. rewrite length_imap. eapply IH, Hold.
        -- eapply IH, Hold.
    + eapply IH, Hread.
Qed.

Lemma read_all_bytes_length {E} (get_msg : E → option Msg.t) addr imem mem tmin time candidates :
  PromMemory.read_all_aux get_msg addr 8 imem mem tmin time = Ok candidates →
  Forall (λ bytes, length bytes = 8) candidates.
Proof.
  revert time candidates. induction mem as [|ev mem IH]; intros time candidates Hread;
    cbn [PromMemory.read_all_aux] in Hread;
    destruct (time =? tmin)%stdpp eqn:Heq.
  all: try (apply bool_decide_eq_true_1 in Heq; subst tmin;
    match type of Hread with context[PromMemory.read_from_aux ?f ?a ?s ?i ?m ?t] =>
      destruct (PromMemory.read_from_aux f a s i m t) as [bytes|err] eqn:Hbytes end;
    cbn in Hread; [injection Hread as <-; constructor;
      [eapply read_from_bytes_length; exact Hbytes|constructor]|discriminate]).
  - destruct time; discriminate.
  - destruct time as [|time]; [discriminate|].
    destruct (PromMemory.read_all_aux get_msg addr 8 imem mem tmin time)
      as [old|err] eqn:Hold; [|discriminate].
    pose proof (IH time old Hold) as Hlen.
    cbn in Hread. destruct (get_msg ev) as [msg|]; [|injection Hread as <-; exact Hlen].
    match type of Hread with context[if ?b then _ else _] => destruct b as [Hfull|Hfull] end.
    + injection Hread as <-. constructor; [|exact Hlen].
      rewrite length_map, length_bv_to_bytes. destruct Hfull as [_ ->]. reflexivity.
    + match type of Hread with context[if ?b then _ else _] => destruct b end;
        [|injection Hread as <-; exact Hlen].
      destruct old as [|bytes old]; [discriminate|]. injection Hread as <-.
      constructor; [|exact Hlen]. unfold imap, list_imap. rewrite length_imap.
      apply Forall_cons in Hlen. tauto.
Qed.

Lemma overlapping_byte addr msg :
  (0 < Msg.size msg)%N → Msg.overlap addr 8 msg →
  ∃ i byte, i < 8 ∧ Msg.read_byte (addr `+Z` Z.of_nat i)%bv msg = Some byte.
Proof.
  intros Hsize Hov.
  destruct (proj1 (addr_overlap_spec addr 8 (Msg.addr msg) (Msg.size msg))
    ltac:(split; [exact Hov|split; lia])) as (i & j & Hi & Hj & Hij).
  exists (N.to_nat i).
  assert (Hrange : addr_in_range (Msg.addr msg) (Msg.size msg)
      (addr `+Z` Z.of_nat (N.to_nat i))%bv).
  { rewrite N_nat_Z. change (addr_in_range (Msg.addr msg) (Msg.size msg) (addr_addN addr i)).
    apply addr_in_range_spec. exists j. split; [symmetry; exact Hij|exact Hj]. }
  unfold Msg.read_byte. rewrite decide_True by exact Hrange.
  eexists. split; [lia|reflexivity].
Qed.

Lemma updated_descriptor_fresh addr msg time bytes :
  length bytes = 8 → Forall (λ byte : bv 8 * nat, byte.2 < time) bytes →
  (0 < Msg.size msg)%N → Msg.overlap addr 8 msg →
  let updated := imap (λ idx byte_time,
    if Msg.read_byte (addr `+Z` Z.of_nat idx)%bv msg is Some byte
    then (byte, time) else byte_time) bytes in
  max_list_with snd updated = time.
Proof.
  intros Hlen Hbytes Hsize Hov. cbn zeta.
  assert (Hle : Forall (λ byte : bv 8 * nat, byte.2 ≤ time) bytes).
  { eapply Forall_impl; [exact Hbytes|]. cbn. lia. }
  destruct (VMPTEReplay.updated_bytes_delta addr msg time bytes Hle) as [Hsame|Hmax];
    [|exact Hmax].
  destruct (overlapping_byte addr msg Hsize Hov) as (i & byte & Hi & Hread).
  destruct (lookup_lt_is_Some_2 bytes i ltac:(lia)) as [[old stamp] Hlookup].
  pose proof (f_equal (λ bs, bs !! i) Hsame) as Heq.
  unfold imap, list_imap in Heq.
  rewrite list_lookup_imap, Hlookup in Heq.
  change (Some (if Msg.read_byte (addr `+Z` Z.of_nat i)%bv msg is Some b
    then (b, time) else (old, stamp)) = Some (old, stamp)) in Heq.
  rewrite Hread in Heq. injection Heq as _ Heq.
  rewrite Forall_forall in Hbytes.
  specialize (Hbytes (old, stamp) (list_elem_of_lookup_2 _ _ _ Hlookup)).
  cbn in Hbytes. lia.
Qed.

Lemma read_all_pte_positive_delta addr imem mem ev tmin ptes :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) →
  tmin ≤ length mem →
  Memory.read_all_pte addr imem mem tmin (length mem) = Ok ptes →
  ∃ ptes', Memory.read_all_pte addr imem (ev :: mem) tmin (S (length mem)) = Ok ptes' ∧
    (ptes' = ptes ∨ ∃ pte, ptes' = (pte, S (length mem)) :: ptes).
Proof.
  intros Hpositive Hmin Hread.
  unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw in Hread |- *.
  rewrite decide_True in Hread by exact Hmin. rewrite decide_True by lia.
  unfold PromMemory.cut_before in Hread |- *. cbn [length].
  rewrite Nat.sub_diag, drop_0 in Hread. rewrite Nat.sub_diag, drop_0.
  destruct (PromMemory.read_all_aux Ev.get_msg addr 8 imem mem tmin (length mem))
    as [bytes|err] eqn:Hbytes; [|discriminate]. injection Hread as <-.
  pose proof (read_all_aux_success_nonempty Ev.get_msg addr 8 imem mem tmin
    (length mem) bytes Hbytes) as Hnonempty.
  pose proof (VMTableReplay.read_all_aux_bounded Ev.get_msg addr 8 imem mem tmin
    (length mem) bytes Hbytes) as Hbound.
  pose proof (read_all_bytes_length Ev.get_msg addr imem mem tmin
    (length mem) bytes Hbytes) as Hlen.
  cbn [PromMemory.read_all_aux]. rewrite bool_decide_false by lia. rewrite Hbytes. cbn.
  destruct (Ev.get_msg ev) as [msg|] eqn:Hmsg.
  - match goal with |- context[if ?b then _ else _] => destruct b as [Hfull|Hfull] end.
    + destruct Hfull as [_ Hsize]. eexists. split; [reflexivity|].
      right. eexists. cbn. rewrite VMPTEReplay.full_write_timestamp by exact Hsize. reflexivity.
    + match goal with |- context[if ?b then _ else _] => destruct b as [Hov|Hov] end.
      * destruct bytes as [|first rest]; [contradiction|].
        apply Forall_cons in Hbound as [Hfirst Hrest].
        apply Forall_cons in Hlen as [Hfirstlen Hrestlen].
        assert (Hfirst' : Forall (λ byte : bv 8 * nat, byte.2 < S (length mem)) first).
        { eapply Forall_impl; [exact Hfirst|]. intros byte Hbyte. cbn in Hbyte |- *. lia. }
        pose proof (updated_descriptor_fresh addr msg (S (length mem)) first
          Hfirstlen Hfirst' (Hpositive msg eq_refl) Hov) as Hfresh.
        eexists. split; [reflexivity|]. right. eexists. cbn. rewrite Hfresh. reflexivity.
      * eexists. split; [reflexivity|]. left. reflexivity.
  - eexists. split; [reflexivity|]. left. reflexivity.
Qed.

(** Growing windows: separate future parent intervals and fresh descriptors,
    and preserve the endpoints of the remaining uncacheable results. *)
Lemma uncacheable_future_parent bound parent parents ptes tmin lvl :
  bound < TLB.Result.tstart parent → bound ≤ TLB.Result.tend parent →
  Forall (λ pte : bv 64 * nat, pte.2 ≤ S bound) ptes → tmin ≤ bound →
  filter (λ r, TLB.Result.tstart r ≤ bound)
    (TLB.get_results_from_events_uncacheable_aux (parent :: parents) ptes tmin (S bound) lvl) =
  filter (λ r, TLB.Result.tstart r ≤ bound)
    (TLB.get_results_from_events_uncacheable_aux parents ptes tmin (S bound) lvl).
Proof.
  intros Hstart Hend Hptes Hmin. destruct parent as [ttbr path start stop inv].
  cbn in Hstart, Hend.
  destruct ptes as [|[pte time] ptes]; [destruct parents; reflexivity|].
  apply Forall_cons in Hptes as [Htime Hptes]. cbn in Htime.
  cbn [TLB.get_results_from_events_uncacheable_aux TLB.Result.tend TLB.Result.tstart].
  rewrite (decide_False (P := Nat.min stop (S bound) < tmin)) by lia.
  rewrite (decide_True (P := time ≤ start)) by lia.
  destruct (decide (is_tlb_fillable lvl pte)); [reflexivity|].
  rewrite filter_cons. rewrite decide_False; [reflexivity|]. cbn. lia.
Qed.

Lemma uncacheable_future_prefix bound prefix parents ptes tmin lvl :
  Forall (λ r, bound < TLB.Result.tstart r ∧ bound ≤ TLB.Result.tend r) prefix →
  Forall (λ pte : bv 64 * nat, pte.2 ≤ S bound) ptes → tmin ≤ bound →
  filter (λ r, TLB.Result.tstart r ≤ bound)
    (TLB.get_results_from_events_uncacheable_aux (prefix ++ parents)%list ptes tmin (S bound) lvl) =
  filter (λ r, TLB.Result.tstart r ≤ bound)
    (TLB.get_results_from_events_uncacheable_aux parents ptes tmin (S bound) lvl).
Proof.
  intros Hprefix Hptes Hmin. induction Hprefix as [|parent prefix [Hs He] Hprefix IH]; [reflexivity|].
  cbn [app]. rewrite uncacheable_future_parent; auto.
Qed.

Lemma uncacheable_capped bound old new ptes tmin tmax lvl :
  Forall2 (res_rel (TIf bound bound (S bound))) old new →
  Forall (λ pte : bv 64 * nat, pte.2 ≤ S bound) ptes → tmax ≤ bound →
  Forall2 (res_rel (TIf bound bound (S bound)))
    (TLB.get_results_from_events_uncacheable_aux old ptes tmin tmax lvl)
    (TLB.get_results_from_events_uncacheable_aux new ptes tmin tmax lvl).
Proof.
  intro Hrel. revert ptes tmax.
  induction Hrel as [|old new olds news Hhead Htail IH]; intros ptes tmax Hp Hmax.
  - constructor.
  - destruct old as [ttbr path start stop inv], new as [ttbr' path' start' stop' inv'].
    destruct Hhead as (Httbr & Hpath & Hstart & Hstop & Hinv).
    cbn in Httbr, Hpath, Hstart, Hstop, Hinv. subst ttbr' path' start'.
    assert (Hcap : ∀ cap, cap ≤ bound → Nat.min stop' cap = Nat.min stop cap).
    { intros cap Hc. destruct Hstop as [H|[H H']]; subst; lia. }
    cbn [TLB.get_results_from_events_uncacheable_aux].
    revert tmax Hmax. induction Hp as [|[pte time] ptes Htime Hptes IHptes]; intros tmax Hmax;
      [constructor|]. cbn in Htime.
    cbn [TLB.Result.tstart TLB.Result.tend]. rewrite Hcap by exact Hmax.
    destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
    destruct (decide (time ≤ start)); destruct (decide (is_tlb_fillable lvl pte)).
    + apply IH; [constructor; assumption|exact Hmax].
    + constructor.
      * unfold res_rel, TIf, ti. cbn. repeat split; try reflexivity; [left; reflexivity|exact Hinv].
      * apply IH; [constructor; assumption|exact Hmax].
    + apply IHptes. lia.
    + constructor.
      * unfold res_rel, TIf, ti. cbn. repeat split; try reflexivity; [left; reflexivity|exact Hinv].
      * apply IHptes. lia.
Qed.

Lemma uncacheable_fresh_descriptor bound parent parents pte ptes tmin lvl :
  TLB.Result.tstart parent ≤ bound → tmin ≤ bound →
  filter (λ r, TLB.Result.tstart r ≤ bound)
    (TLB.get_results_from_events_uncacheable_aux (parent :: parents)
      ((pte, S bound) :: ptes) tmin (S bound) lvl) =
  filter (λ r, TLB.Result.tstart r ≤ bound)
    (TLB.get_results_from_events_uncacheable_aux (parent :: parents) ptes tmin bound lvl).
Proof.
  intros Hstart Hmin. destruct parent as [ttbr path start stop inv]. cbn in Hstart.
  cbn [TLB.get_results_from_events_uncacheable_aux TLB.Result.tend TLB.Result.tstart].
  destruct (decide (Nat.min stop (S bound) < tmin)) as [Hrange|Hrange].
  - destruct ptes as [|[old time] ptes]; [reflexivity|].
    rewrite decide_True by lia. reflexivity.
  - rewrite (decide_False (P := S bound ≤ start)) by lia.
    rewrite Nat.pred_succ. destruct (decide (is_tlb_fillable lvl pte)); [reflexivity|].
    rewrite filter_cons. rewrite decide_False; [reflexivity|]. cbn. lia.
Qed.

Lemma uncacheable_larger bound old new ptes tmin lvl :
  Forall2 (res_rel (TIf bound bound (S bound))) old new →
  Forall (λ r, TLB.Result.tend r ≤ bound) old →
  Forall (λ pte : bv 64 * nat, pte.2 ≤ bound) ptes → tmin ≤ bound →
  Forall2 (res_rel (TIf bound bound (S bound)))
    (TLB.get_results_from_events_uncacheable_aux old ptes tmin bound lvl)
    (TLB.get_results_from_events_uncacheable_aux new ptes tmin (S bound) lvl).
Proof.
  intro Hrel. revert ptes.
  induction Hrel as [|old new olds news Hhead Htail IH]; intros ptes Hends Hp Hmin.
  - constructor.
  - assert (Hall : Forall2 (res_rel (TIf bound bound (S bound))) (old :: olds) (new :: news))
      by (constructor; assumption).
    destruct old as [ttbr path start stop inv], new as [ttbr' path' start' stop' inv'].
    destruct Hhead as (Httbr & Hpath & Hstart & Hstop & Hinv).
    cbn in Httbr, Hpath, Hstart, Hstop, Hinv. subst ttbr' path' start'.
    apply Forall_cons in Hends as [Hend Hends]. cbn in Hend.
    assert (Hguard : Nat.min stop' (S bound) < tmin ↔ Nat.min stop bound < tmin).
    { destruct Hstop as [H|[H H']]; subst; lia. }
    assert (Hendrel : Nat.min stop' (S bound) = Nat.min stop bound ∨
      (Nat.min stop bound = bound ∧ Nat.min stop' (S bound) = S bound)).
    { destruct Hstop as [H|[H H']]; subst; [left|right]; lia. }
    cbn [TLB.get_results_from_events_uncacheable_aux].
    destruct ptes as [|[pte time] ptes]; [constructor|].
    apply Forall_cons in Hp as [Htime Hptes]. cbn in Htime.
    cbn [TLB.Result.tstart TLB.Result.tend].
    destruct (decide (Nat.min stop bound < tmin));
      destruct (decide (Nat.min stop' (S bound) < tmin)); try (exfalso; tauto); [constructor|].
    destruct (decide (time ≤ start)); destruct (decide (is_tlb_fillable lvl pte)).
    + apply IH; [exact Hends|constructor; assumption|exact Hmin].
    + constructor.
      * unfold res_rel, TIf, ti. cbn. repeat split; try reflexivity; assumption.
      * apply IH; [exact Hends|constructor; assumption|exact Hmin].
    + apply (uncacheable_capped bound _ _ ptes tmin (Nat.pred time) lvl Hall); [|lia].
      eapply Forall_impl; [exact Hptes|]. cbn. lia.
    + constructor.
      * unfold res_rel, TIf, ti. cbn. repeat split; try reflexivity; assumption.
      * apply (uncacheable_capped bound _ _ ptes tmin (Nat.pred time) lvl Hall); [|lia].
        eapply Forall_impl; [exact Hptes|]. cbn. lia.
Qed.

Lemma read_all_pte_past addr imem mem ev tmin ptes' :
  tmin ≤ length mem →
  Memory.read_all_pte addr imem (ev :: mem) tmin (S (length mem)) = Ok ptes' →
  ∃ ptes, Memory.read_all_pte addr imem mem tmin (length mem) = Ok ptes.
Proof.
  intros Hmin Hread.
  unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw in Hread |- *.
  rewrite decide_True in Hread by lia. rewrite decide_True by exact Hmin.
  unfold PromMemory.cut_before in Hread |- *. cbn [length] in Hread.
  rewrite Nat.sub_diag, drop_0 in Hread. rewrite Nat.sub_diag, drop_0.
  cbn [PromMemory.read_all_aux] in Hread. rewrite bool_decide_false in Hread by lia.
  destruct (PromMemory.read_all_aux Ev.get_msg addr 8 imem mem tmin (length mem))
    as [bytes|err] eqn:Hbytes; [eexists; reflexivity|discriminate].
Qed.

Lemma parent_end_bound tid ifetch ttbr path events tmin tmax inv :
  Forall (λ parent, TLB.Result.tend parent ≤ tmax)
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

Lemma uncacheable_start_bound bound parents ptes tmin tmax lvl :
  Forall (λ r, TLB.Result.tstart r ≤ bound) parents →
  Forall (λ pte : bv 64 * nat, pte.2 ≤ bound) ptes → tmin ≤ bound →
  Forall (λ r, TLB.Result.tstart r ≤ bound)
    (TLB.get_results_from_events_uncacheable_aux parents ptes tmin tmax lvl).
Proof.
  intro Hparents. revert ptes tmax.
  induction Hparents as [|parent parents Hparent Hparents IH]; intros ptes tmax Hp Hmin; [constructor|].
  destruct parent as [ttbr path start stop inv]. cbn in Hparent.
  cbn [TLB.get_results_from_events_uncacheable_aux].
  revert tmax. induction Hp as [|[pte time] ptes Htime Hptes IHptes]; intro tmax; [constructor|].
  cbn [TLB.Result.tstart TLB.Result.tend]. cbn in Htime.
  destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
  destruct (decide (time ≤ start)); destruct (decide (is_tlb_fillable lvl pte));
    try (constructor; [cbn; lia|]); first [apply IH; [constructor; assumption|exact Hmin]|apply IHptes].
Qed.

Lemma related_start_bound bound lo hi old new :
  Forall2 (res_rel (TIf bound lo hi)) old new →
  Forall (λ r, TLB.Result.tstart r ≤ bound) old →
  Forall (λ r, TLB.Result.tstart r ≤ bound) new.
Proof.
  intro Hrel. induction Hrel as [|a b xs ys Hr Hrs IH]; intro Hstart; [constructor|].
  apply Forall_cons in Hstart as [Ha Hxs]. constructor; [|apply IH, Hxs].
  destruct Hr as (_ & _ & Hs & _). lia.
Qed.

Lemma uncacheable_positive_delta bound old extra new ptes ptes' tmin lvl :
  Forall2 (res_rel (TIf bound bound (S bound))) old new →
  Forall (λ r, TLB.Result.tstart r ≤ bound) old →
  Forall (λ r, TLB.Result.tend r ≤ bound) old →
  Forall (λ r, bound < TLB.Result.tstart r ∧ bound ≤ TLB.Result.tend r) extra →
  Forall (λ pte : bv 64 * nat, pte.2 ≤ bound) ptes → tmin ≤ bound →
  (ptes' = ptes ∨ ∃ pte, ptes' = (pte, S bound) :: ptes) →
  Forall2 (res_rel (TIf bound bound (S bound)))
    (TLB.get_results_from_events_uncacheable_aux old ptes tmin bound lvl)
    (filter (λ r, TLB.Result.tstart r ≤ bound)
      (TLB.get_results_from_events_uncacheable_aux (extra ++ new)%list ptes' tmin (S bound) lvl)).
Proof.
  intros Hrel Hstart Hend Hextra Hptes Hmin Hdelta.
  assert (Hptes1 : Forall (λ pte : bv 64 * nat, pte.2 ≤ S bound) ptes).
  { eapply Forall_impl; [exact Hptes|]. cbn. lia. }
  assert (Hptes' : Forall (λ pte : bv 64 * nat, pte.2 ≤ S bound) ptes').
  { destruct Hdelta as [->|[pte ->]]; [exact Hptes1|constructor; [cbn; lia|exact Hptes1]]. }
  rewrite uncacheable_future_prefix by assumption.
  pose proof (related_start_bound bound bound (S bound) old new Hrel Hstart) as Hnew.
  destruct Hdelta as [->|[pte ->]].
  - apply filter_replayed.
    + apply uncacheable_larger; assumption.
    + apply uncacheable_start_bound; assumption.
  - destruct new as [|parent parents].
    { destruct old; [constructor|inversion Hrel]. }
    apply Forall_cons in Hnew as [Hparent Hparents].
    rewrite uncacheable_fresh_descriptor by assumption.
    apply filter_replayed.
    + apply uncacheable_capped; [exact Hrel|exact Hptes1|lia].
    + apply uncacheable_start_bound; assumption.
Qed.

Lemma parents_replay_split tid ifetch ttbr path bound prefix events tmin :
  Forall (λ event, event.2 = S bound) prefix →
  Forall (λ event, event.2 ≤ bound) events → tmin ≤ bound →
  ∃ extra past,
    TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin (S bound) None =
      (extra ++ past)%list ∧
    Forall (λ r, bound < TLB.Result.tstart r ∧ bound ≤ TLB.Result.tend r) extra ∧
    Forall2 (res_rel (TIf bound bound (S bound)))
      (TLB.get_results_from_events tid ifetch ttbr path events tmin bound None) past.
Proof.
  intros Hp Hb Hmin.
  assert (Hp' : Forall (λ event, bound < event.2) prefix).
  { eapply Forall_impl; [exact Hp|]. intros [e t] Ht. cbn in *. lia. }
  destruct (VMTableReplay.parents_future_prefix tid ifetch ttbr path bound prefix events
    tmin (S bound) None None Hp' Hb Hmin ltac:(lia) ltac:(left; reflexivity))
    as [extra [past [Hnew [Hextra Hweak]]]].
  pose proof (VMPTEReplay.extends_parent_starts bound _ _ Hweak
    (VMPTEReplay.parent_start_bound tid ifetch ttbr path events tmin bound None)) as Hpast.
  assert (Hfe : filter (λ r, TLB.Result.tstart r ≤ bound) extra = []).
  { clear Hnew. induction Hextra as [|r rs [Hs He] Hrs IH]; [reflexivity|].
    rewrite filter_cons_False by lia. exact IH. }
  assert (Hfp : filter (λ r, TLB.Result.tstart r ≤ bound) past = past).
  { clear Hnew Hweak. induction Hpast as [|r rs Hs Hrs IH]; [reflexivity|].
    rewrite filter_cons_True by exact Hs. f_equal. exact IH. }
  pose proof (future_prefix_larger_exact tid ifetch ttbr path bound prefix events tmin Hp Hb Hmin)
    as Hstrong.
  rewrite Hnew, filter_app, Hfe, Hfp in Hstrong. cbn [app] in Hstrong.
  exists extra, past. auto.
Qed.

Theorem uncacheable_history_exact tid ifetch ttbr path bound prefix events ptes ptes' tmin lvl :
  Forall (λ event, event.2 = S bound) prefix →
  Forall (λ event, event.2 ≤ bound) events → tmin ≤ bound →
  Forall (λ pte : bv 64 * nat, pte.2 ≤ bound) ptes →
  (ptes' = ptes ∨ ∃ pte, ptes' = (pte, S bound) :: ptes) →
  Forall2 (res_rel (TIf bound bound (S bound)))
    (TLB.get_results_from_events_uncacheable_aux
      (TLB.get_results_from_events tid ifetch ttbr path events tmin bound None) ptes tmin bound lvl)
    (filter (λ r, TLB.Result.tstart r ≤ bound)
      (TLB.get_results_from_events_uncacheable_aux
        (TLB.get_results_from_events tid ifetch ttbr path (prefix ++ events)%list tmin (S bound) None)
        ptes' tmin (S bound) lvl)).
Proof.
  intros Hp Hb Hmin Hptes Hdelta.
  destruct (parents_replay_split tid ifetch ttbr path bound prefix events tmin Hp Hb Hmin)
    as [extra [past [Hnew [Hextra Hrel]]]].
  rewrite Hnew. apply uncacheable_positive_delta; try assumption.
  - apply VMPTEReplay.parent_start_bound.
  - apply parent_end_bound.
Qed.

(** A successful table lookup after a positive write or a TLBI has an old
    counterpart for every result whose start is within the old history. *)
Theorem table_growing_backward tid imem mem ev ifetch vpn fe events prefix tmin new :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) →
  Forall (λ event, event.2 = S (length mem)) prefix →
  Forall (λ event, event.2 ≤ length mem) events → tmin ≤ length mem →
  TLB.get_result_from_table_FE tid imem (ev :: mem) ifetch vpn fe
    (prefix ++ events)%list tmin (S (length mem)) = Ok new →
  ∃ old, TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin (length mem) = Ok old ∧
    Forall2 (res_rel (TIf (length mem) (length mem) (S (length mem)))) old
      (filter (λ r, TLB.Result.tstart r ≤ length mem) new).
Proof.
  intros Hpositive Hp Hb Hmin Hread.
  unfold TLB.get_result_from_table_FE in Hread |- *.
  rewrite decide_False in Hread by lia. rewrite decide_False by lia.
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|];
    [|injection Hread as <-; exists []; split; [reflexivity|constructor]].
  pose proof (future_prefix_larger_exact tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (length mem) prefix events tmin Hp Hb Hmin) as Hparents.
  destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (prefix ++ events)%list tmin (S (length mem)) None) as [|parent parents] eqn:Hnew.
  - injection Hread as <-. cbn [filter] in Hparents.
    assert (Hold : TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      events tmin (length mem) None = []) by (inversion Hparents; reflexivity).
    rewrite Hold. exists []. split; [reflexivity|constructor].
  - destruct (Memory.read_all_pte _ imem (ev :: mem) tmin (S (length mem)))
      as [ptes'|err] eqn:Hptes'; [|discriminate]. injection Hread as <-.
    destruct (read_all_pte_past _ imem mem ev tmin ptes' Hmin Hptes') as [ptes Hptes].
    destruct (read_all_pte_positive_delta _ imem mem ev tmin ptes Hpositive Hmin Hptes)
      as [found [Hfound Hdelta]]. rewrite Hptes' in Hfound. injection Hfound as <-.
    pose proof (VMTableReplay.read_all_pte_bounded _ imem mem tmin (length mem) ptes Hptes) as Hbound.
    pose proof (uncacheable_history_exact tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      (length mem) prefix events ptes ptes' tmin lvl Hp Hb Hmin Hbound Hdelta) as Hrel.
    rewrite Hnew in Hrel.
    destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      events tmin (length mem) None) as [|p ps].
    + exists []. split; [reflexivity|exact Hrel].
    + rewrite Hptes. eexists. split; [reflexivity|exact Hrel].
Qed.

Theorem table_growing_forward tid imem mem ev ifetch vpn fe events prefix tmin old :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) →
  Forall (λ event, event.2 = S (length mem)) prefix →
  Forall (λ event, event.2 ≤ length mem) events →
  TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin (length mem) = Ok old →
  old ≠ [] →
  ∃ new, TLB.get_result_from_table_FE tid imem (ev :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin (S (length mem)) = Ok new ∧
    Forall2 (res_rel (TIf (length mem) (length mem) (S (length mem)))) old
      (filter (λ r, TLB.Result.tstart r ≤ length mem) new).
Proof.
  intros Hpositive Hp Hb Hread Hnonempty.
  unfold TLB.get_result_from_table_FE in Hread |- *.
  destruct (decide (length mem < tmin)); [injection Hread as <-; contradiction|].
  rewrite decide_False by lia.
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection Hread as <-; contradiction].
  pose proof (future_prefix_larger_exact tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (length mem) prefix events tmin Hp Hb ltac:(lia)) as Hparents.
  destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    events tmin (length mem) None) as [|parent parents] eqn:Hold;
    [injection Hread as <-; contradiction|].
  destruct (Memory.read_all_pte _ imem mem tmin (length mem)) as [ptes|err] eqn:Hptes;
    [|discriminate]. injection Hread as <-.
  destruct (read_all_pte_positive_delta _ imem mem ev tmin ptes Hpositive ltac:(lia) Hptes)
    as [ptes' [Hptes' Hdelta]].
  pose proof (VMTableReplay.read_all_pte_bounded _ imem mem tmin (length mem) ptes Hptes) as Hbound.
  pose proof (uncacheable_history_exact tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (length mem) prefix events ptes ptes' tmin lvl Hp Hb ltac:(lia) Hbound Hdelta) as Hrel.
  rewrite Hold in Hrel.
  destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (prefix ++ events)%list tmin (S (length mem)) None) as [|p ps];
    [inversion Hparents|].
  rewrite Hptes'. eexists. split; [reflexivity|exact Hrel].
Qed.

Lemma uncacheable_start_lower parents ptes tmin tmax lvl :
  Forall (λ r, tmin ≤ TLB.Result.tstart r)
    (TLB.get_results_from_events_uncacheable_aux parents ptes tmin tmax lvl).
Proof.
  revert ptes tmax. induction parents as [|parent parents IH]; intros ptes tmax; [constructor|].
  destruct parent as [ttbr path start stop inv].
  revert tmax. induction ptes as [|[pte time] ptes IHptes]; intro tmax; [constructor|].
  cbn [TLB.get_results_from_events_uncacheable_aux TLB.Result.tstart TLB.Result.tend].
  destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
  destruct (decide (time ≤ start));
    destruct (decide (is_tlb_fillable lvl pte));
    try (constructor; [cbn; lia|]); first [apply IH|apply IHptes].
Qed.

Lemma table_start_lower tid imem mem ifetch vpn fe events tmin tmax results result :
  TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin tmax = Ok results →
  result ∈ results → tmin ≤ TLB.Result.tstart result.
Proof.
  unfold TLB.get_result_from_table_FE.
  destruct (decide (tmax < tmin)); [injection 1 as <-; inversion 1|].
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection 1 as <-; inversion 1].
  destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    events tmin tmax None) as [|parent parents]; [injection 1 as <-; inversion 1|].
  destruct (Memory.read_all_pte _ imem mem tmin tmax) as [ptes|err]; [|discriminate].
  injection 1 as <-. intro Hin.
  pose proof (uncacheable_start_lower (parent :: parents) ptes tmin tmax lvl) as Hlower.
  rewrite Forall_forall in Hlower. exact (Hlower result Hin).
Qed.

Lemma table_fixed_backward tid imem mem ev ifetch vpn fe events prefix tmin tmax new :
  Forall (λ event, length mem < event.2) prefix → tmax ≤ length mem →
  TLB.get_result_from_table_FE tid imem (ev :: mem) ifetch vpn fe
    (prefix ++ events)%list tmin tmax = Ok new →
  ∃ old, TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin tmax = Ok old ∧
    Forall2 (res_rel (TIf (length mem) tmax tmax)) old new.
Proof.
  intros Hp Hmax. unfold TLB.get_result_from_table_FE.
  destruct (decide (tmax < tmin));
    [injection 1 as <-; exists []; split; [reflexivity|constructor]|].
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|];
    [|injection 1 as <-; exists []; split; [reflexivity|constructor]].
  pose proof (future_prefix_exact tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
    (length mem) prefix events tmin tmax tmax tmax Hp Hmax) as Hparents.
  destruct Hparents as [|first first' rest rest' Hfirst Hrest].
  - injection 1 as <-. exists []. split; [reflexivity|constructor].
  - rewrite VMLookupReplay.read_all_pte_future by exact Hmax.
    destruct (Memory.read_all_pte _ imem mem tmin tmax) as [ptes|err]; [|discriminate].
    injection 1 as <-. eexists. split; [reflexivity|].
    apply (uncacheable_fixed (length mem) tmax
      (first :: rest) (first' :: rest') ptes tmin tmax lvl). constructor; assumption.
Qed.

Theorem entry_replay_forward tid imem mem ev ifetch vpn fe events prefix tmin_ok tmin_unc
    tmax tmax' old result :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) →
  Forall (λ event, event.2 = S (length mem)) prefix →
  Forall (λ event, event.2 ≤ length mem) events → tmax ≤ length mem →
  (tmax' = tmax ∨ (tmax = length mem ∧ tmax' = S (length mem))) →
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax = Ok old →
  result ∈ old →
  ∃ new result', TLB.get_result_from_FE tid imem (ev :: mem) ifetch vpn fe
      (prefix ++ events)%list tmin_ok tmin_unc tmax' = Ok new ∧
    result' ∈ new ∧ res_rel (TIf (length mem) tmax tmax') result result'.
Proof.
  intros Hpositive Hp Hb Hmax Hcases Hread Hin.
  assert (Hp' : Forall (λ event, length mem < event.2) prefix).
  { eapply Forall_impl; [exact Hp|]. intros [e t] Ht. cbn in *. lia. }
  destruct Hcases as [->|[-> ->]].
  - destruct (entry_future_prefix_exact tid imem mem ev ifetch vpn fe events prefix
      tmin_ok tmin_unc tmax old Hp' Hmax Hread) as [new [Hnew Hrel]].
    destruct (forall2_forward _ _ _ _ Hrel Hin) as [result' [Hin' Hr]]. eauto.
  - unfold TLB.get_result_from_FE in Hread |- *.
    destruct (decide (TLB.FE.is_table fe)).
    + destruct (table_growing_forward tid imem mem ev ifetch vpn fe events prefix tmin_unc old
        Hpositive Hp Hb Hread ltac:(intro H; subst old; inversion Hin)) as [new [Hnew Hrel]].
      destruct (forall2_forward _ _ _ _ Hrel Hin) as [result' [Hin' Hr]].
      apply list_elem_of_filter in Hin' as [_ Hin']. eauto.
    + unfold TLB.get_result_from_leaf_FE in Hread |- *.
      destruct (decide (length mem < tmin_ok)); [injection Hread as <-; inversion Hin|].
      rewrite decide_False by lia. injection Hread as <-.
      pose proof (future_prefix_larger_exact tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
        (length mem) prefix events tmin_ok Hp Hb ltac:(lia)) as Hrel.
      destruct (forall2_forward _ _ _ _ Hrel Hin) as [result' [Hin' Hr]].
      apply list_elem_of_filter in Hin' as [_ Hin']. eauto.
Qed.

Theorem entry_replay_backward tid imem mem ev ifetch vpn fe events prefix tmin_ok tmin_unc
    tmax tmax' new result' :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) →
  Forall (λ event, event.2 = S (length mem)) prefix →
  Forall (λ event, event.2 ≤ length mem) events → tmin_ok ≤ tmax → tmax ≤ length mem →
  (tmax' = tmax ∨ (tmax = length mem ∧ tmax' = S (length mem))) →
  TLB.get_result_from_FE tid imem (ev :: mem) ifetch vpn fe
    (prefix ++ events)%list tmin_ok tmin_unc tmax' = Ok new →
  result' ∈ new → TLB.Result.tstart result' ≤ length mem →
  ∃ old result, TLB.get_result_from_FE tid imem mem ifetch vpn fe
      events tmin_ok tmin_unc tmax = Ok old ∧
    result ∈ old ∧ res_rel (TIf (length mem) tmax tmax') result result'.
Proof.
  intros Hpositive Hp Hb Hmin Hmax Hcases Hread Hin Hstart.
  assert (Hp' : Forall (λ event, length mem < event.2) prefix).
  { eapply Forall_impl; [exact Hp|]. intros [e t] Ht. cbn in *. lia. }
  unfold TLB.get_result_from_FE in Hread |- *.
  destruct (decide (TLB.FE.is_table fe)).
  - destruct Hcases as [->|[-> ->]].
    + destruct (table_fixed_backward tid imem mem ev ifetch vpn fe events prefix
        tmin_unc tmax new Hp' Hmax Hread) as [old [Hold Hrel]].
      destruct (forall2_backward _ _ _ _ Hrel Hin) as [result [Hr Hrelr]]. eauto.
    + pose proof (table_start_lower tid imem (ev :: mem) ifetch vpn fe (prefix ++ events)%list
        tmin_unc (S (length mem)) new result' Hread Hin) as Hunc.
      destruct (table_growing_backward tid imem mem ev ifetch vpn fe events prefix
        tmin_unc new Hpositive Hp Hb ltac:(lia) Hread) as [old [Hold Hrel]].
      assert (Hin' : result' ∈ filter (λ r, TLB.Result.tstart r ≤ length mem) new)
        by (apply list_elem_of_filter; auto).
      destruct (forall2_backward _ _ _ _ Hrel Hin') as [result [Hr Hrelr]]. eauto.
  - unfold TLB.get_result_from_leaf_FE in Hread |- *.
    rewrite decide_False by lia. rewrite decide_False in Hread by (destruct Hcases as [->|[-> ->]]; lia).
    injection Hread as <-.
    pose proof (events_replay_exact tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      (length mem) prefix events tmin_ok tmax tmax' Hp Hb Hmin Hmax Hcases) as Hrel.
    destruct (forall2_backward _ _ _ result' Hrel ltac:(apply list_elem_of_filter; auto))
      as [result [Hr Hrelr]]. eauto.
Qed.

Lemma pte_replay_forward addr imem mem ev tmin tmax tmax' old pte :
  tmin ≤ tmax → tmax ≤ length mem →
  (tmax' = tmax ∨ (tmax = length mem ∧ tmax' = S (length mem))) →
  Memory.read_all_pte addr imem mem tmin tmax = Ok old → pte ∈ old →
  ∃ new, Memory.read_all_pte addr imem (ev :: mem) tmin tmax' = Ok new ∧ pte ∈ new.
Proof.
  intros Hmin Hmax Hcases Hread Hin.
  destruct (VMRootLookupReplay.read_all_pte_larger_bound addr imem mem ev tmin tmax tmax' old
    Hmin Hmax ltac:(destruct Hcases as [->|[-> ->]]; lia)
    ltac:(destruct Hcases as [->|[-> ->]]; lia) Hread) as [new [Hnew Hsub]]. eauto.
Qed.

Lemma pte_replay_backward addr imem mem ev tmin tmax tmax' new pte time :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) →
  tmin ≤ tmax → tmax ≤ length mem →
  (tmax' = tmax ∨ (tmax = length mem ∧ tmax' = S (length mem))) →
  Memory.read_all_pte addr imem (ev :: mem) tmin tmax' = Ok new →
  (pte, time) ∈ new → time ≤ length mem →
  ∃ old, Memory.read_all_pte addr imem mem tmin tmax = Ok old ∧ (pte, time) ∈ old.
Proof.
  intros Hpositive Hmin Hmax [->|[-> ->]] Hread Hin Htime.
  - rewrite VMLookupReplay.read_all_pte_future in Hread by exact Hmax. eauto.
  - destruct (read_all_pte_past addr imem mem ev tmin new Hmin Hread) as [old Hold].
    destruct (read_all_pte_positive_delta addr imem mem ev tmin old Hpositive Hmin Hold)
      as [found [Hfound Hdelta]]. rewrite Hread in Hfound. injection Hfound as <-.
    exists old. split; [exact Hold|].
    destruct Hdelta as [->|[fresh ->]]; [exact Hin|].
    apply elem_of_cons in Hin as [Heq|Hin]; [injection Heq; lia|exact Hin].
Qed.

Lemma root_lookup_witness imem mem ts upper vpn ttbr0 tmin tmax r :
  Exec.elem_of_results r (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin tmax) ↔
  tmin ≤ tmax ∧ ∃ (ttbrs : list (bv 64 * nat)) ttbr vttbr ptes pte vpte,
    (if upper then othrow "Can't read TTBR1_EL1, but using negative addresses"
        (TState.read_sreg_indirect ts TTBR1_EL1) else Ok [(ttbr0, 0)]) = Ok ttbrs ∧
    (ttbr, vttbr) ∈ ttbrs ∧
    Memory.read_all_pte (index_table (ttbr_root_table ttbr) (vpn_level_index 0%fin vpn))
      imem mem (tmin ⊔ vttbr) tmax = Ok ptes ∧
    (pte, vpte) ∈ ptes ∧ ¬ is_tlb_fillable 0%fin pte ∧
    r = TLB.Result.make ttbr [pte] (tmin ⊔ vttbr ⊔ vpte) tmax None.
Proof.
  unfold VMRootLookupReplay.root_lookup.
  destruct (decide (tmin ≤ tmax)) as [Hmin|Hmin].
  - split.
    + intro Hin. apply Exec.elem_of_res_bind_elim in Hin as [ttbrs [Hregs Hin]].
      apply Exec.elem_of_res_bind_elim in Hin as [[ttbr vttbr] [Hchoice Hin]].
      apply Exec.elem_of_res_bind_elim in Hin as [ptes [Hread Hin]].
      apply PromiseFirstCurrent.lift_result_res_success in Hregs, Hread.
      apply Exec.elem_of_res_mchoosel_inv in Hchoice, Hin.
      apply list_elem_of_fmap in Hin as [[pte vpte] [-> Hin]].
      apply list_elem_of_filter in Hin as [Hinvalid Hin]. split; [exact Hmin|]. eauto 12.
    + intros [_ (ttbrs & ttbr & vttbr & ptes & pte & vpte & Hregs & Hchoice & Hread & Hin & Hinvalid & ->)].
      eapply Exec.elem_of_res_bind_intro; [apply PromiseFirstCurrent.lift_result_res_success; exact Hregs|].
      eapply Exec.elem_of_res_bind_intro with (a := (ttbr, vttbr));
        [apply Exec.elem_of_res_mchoosel; exact Hchoice|].
      eapply Exec.elem_of_res_bind_intro; [apply PromiseFirstCurrent.lift_result_res_success; exact Hread|].
      apply Exec.elem_of_res_mchoosel, list_elem_of_fmap. exists (pte, vpte).
      split; [reflexivity|apply list_elem_of_filter; auto].
  - split; [inversion 1|tauto].
Qed.

Theorem root_replay_forward imem mem ev ts issued upper vpn ttbr0 tmin tmax tmax' r :
  TState.read_sreg_indirect issued TTBR1_EL1 = TState.read_sreg_indirect ts TTBR1_EL1 →
  tmax ≤ length mem →
  (tmax' = tmax ∨ (tmax = length mem ∧ tmax' = S (length mem))) →
  Exec.elem_of_results r (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin tmax) →
  ∃ r', Exec.elem_of_results r'
      (VMRootLookupReplay.root_lookup imem (ev :: mem) issued upper vpn ttbr0 tmin tmax') ∧
    res_rel (TIf (length mem) tmax tmax') r r'.
Proof.
  intros Hregs Hmax Hcases Hin. apply root_lookup_witness in Hin
    as [Hmin (ttbrs & ttbr & vttbr & ptes & pte & vpte & Httbrs & Hchoice & Hread & Hin & Hinvalid & ->)].
  assert (Hreadmin : tmin ⊔ vttbr ≤ tmax).
  { destruct (decide (tmin ⊔ vttbr ≤ tmax)); [assumption|].
    unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw in Hread.
    rewrite decide_False in Hread by assumption. injection Hread as <-. inversion Hin. }
  destruct (pte_replay_forward _ imem mem ev _ tmax tmax' ptes (pte, vpte)
    Hreadmin Hmax Hcases Hread Hin) as [ptes' [Hread' Hin']].
  exists (TLB.Result.make ttbr [pte] (tmin ⊔ vttbr ⊔ vpte) tmax' None). split.
  - apply root_lookup_witness. split; [destruct Hcases as [->|[-> ->]]; lia|].
    exists ttbrs, ttbr, vttbr, ptes', pte, vpte. rewrite Hregs. repeat split; assumption || reflexivity.
  - unfold res_rel, TIf, ti. cbn. repeat split; try reflexivity.
    + right. auto.
    + left. reflexivity.
Qed.

Theorem root_replay_backward imem mem ev ts issued upper vpn ttbr0 tmin tmax tmax' r' :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) →
  TState.read_sreg_indirect issued TTBR1_EL1 = TState.read_sreg_indirect ts TTBR1_EL1 →
  tmax ≤ length mem →
  (tmax' = tmax ∨ (tmax = length mem ∧ tmax' = S (length mem))) →
  Exec.elem_of_results r'
    (VMRootLookupReplay.root_lookup imem (ev :: mem) issued upper vpn ttbr0 tmin tmax') →
  TLB.Result.tstart r' ≤ length mem →
  ∃ r, Exec.elem_of_results r
      (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin tmax) ∧
    res_rel (TIf (length mem) tmax tmax') r r'.
Proof.
  intros Hpositive Hregs Hmax Hcases Hin Hstart. apply root_lookup_witness in Hin
    as [Hmin (ttbrs & ttbr & vttbr & ptes' & pte & vpte & Httbrs & Hchoice & Hread & Hin & Hinvalid & ->)].
  cbn in Hstart. unfold join, join_nat in Hstart. rewrite Hregs in Httbrs.
  assert (Hreadmin : tmin ⊔ vttbr ≤ tmax).
  { destruct Hcases as [->|[-> ->]]; [|unfold join, join_nat; lia].
    destruct (decide (tmin ⊔ vttbr ≤ tmax)); [assumption|].
    unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw in Hread.
    rewrite decide_False in Hread by assumption. injection Hread as <-. inversion Hin. }
  destruct (pte_replay_backward _ imem mem ev _ tmax tmax' ptes' pte vpte
    Hpositive Hreadmin Hmax Hcases Hread Hin ltac:(lia)) as [ptes [Hread' Hin']].
  exists (TLB.Result.make ttbr [pte] (tmin ⊔ vttbr ⊔ vpte) tmax None). split.
  - apply root_lookup_witness. split; [unfold join, join_nat in Hreadmin; lia|].
    exists ttbrs, ttbr, vttbr, ptes, pte, vpte. repeat split; assumption || reflexivity.
  - unfold res_rel, TIf, ti. cbn. repeat split; try reflexivity.
    + right. auto.
    + left. reflexivity.
Qed.

Theorem entry_fixed_own tid imem mem ev (ifetch : bool) vpn fe events prefix tmin_ok tmin_unc tmax :
  Forall (λ et, length mem < et.2 ∧
    match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => ifetch ∨ issuer = tid end) prefix →
  tmax ≤ length mem →
  TLB.get_result_from_FE tid imem (ev :: mem) ifetch vpn fe
    (prefix ++ events)%list tmin_ok tmin_unc tmax =
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax.
Proof.
  intros Hp Hmax. unfold TLB.get_result_from_FE.
  destruct (decide (TLB.FE.is_table fe)).
  - unfold TLB.get_result_from_table_FE. destruct (decide (tmax < tmin_unc)); [reflexivity|].
    destruct (child_lvl (TLB.FE.lvl fe)); [|reflexivity].
    rewrite (future_prefix_own tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      (length mem) prefix events tmin_unc tmax None Hp Hmax).
    destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      events tmin_unc tmax None); [reflexivity|].
    rewrite VMLookupReplay.read_all_pte_future by exact Hmax. reflexivity.
  - unfold TLB.get_result_from_leaf_FE. destruct (decide (tmax < tmin_ok)); [reflexivity|].
    rewrite (future_prefix_own tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      (length mem) prefix events tmin_ok tmax None Hp Hmax). reflexivity.
Qed.

Lemma root_fixed_own imem mem ev ts issued upper vpn ttbr0 tmin tmax :
  TState.read_sreg_indirect issued TTBR1_EL1 = TState.read_sreg_indirect ts TTBR1_EL1 →
  tmax ≤ length mem →
  VMRootLookupReplay.root_lookup imem (ev :: mem) issued upper vpn ttbr0 tmin tmax =
    VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin tmax.
Proof.
  intros Hregs Hmax. unfold VMRootLookupReplay.root_lookup. rewrite Hregs.
  destruct (decide (tmin ≤ tmax)); [|reflexivity].
  f_equal. extensionality ttbrs. f_equal. extensionality ttbrv. destruct ttbrv as [ttbr vttbr].
  rewrite VMLookupReplay.read_all_pte_future by exact Hmax. reflexivity.
Qed.

Lemma entry_empty tid imem mem ifetch vpn fe tmin_ok tmin_unc tmax :
  TLB.get_result_from_FE tid imem mem ifetch vpn fe [] tmin_ok tmin_unc tmax = Ok [].
Proof.
  unfold TLB.get_result_from_FE, TLB.get_result_from_table_FE, TLB.get_result_from_leaf_FE.
  destruct (decide (TLB.FE.is_table fe));
    repeat match goal with |- context [decide ?P] => destruct (decide P) end;
    try destruct (child_lvl (TLB.FE.lvl fe)); cbn [TLB.get_results_from_events];
    repeat match goal with |- context [decide ?P] => destruct (decide P) end; reflexivity.
Qed.

Lemma res_rel_eq_refl r : res_rel eq r r.
Proof. unfold res_rel. repeat split; reflexivity. Qed.

Lemma prefix_stamps bound owner prefix :
  Forall (λ et : TLB.Entry.event * nat, et.2 = S bound ∧
    match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => issuer = owner end) prefix →
  Forall (λ et, et.2 = S bound) prefix.
Proof. intro Hp. eapply list.Forall_impl; [exact Hp|]. intros [e t] [Ht _]. exact Ht. Qed.

Lemma prefix_own bound owner tid (ifetch : bool) prefix : owner = tid →
  Forall (λ et : TLB.Entry.event * nat, et.2 = S bound ∧
    match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => issuer = owner end) prefix →
  Forall (λ et, bound < et.2 ∧
    match et.1 with TLB.Entry.Load => True | TLB.Entry.Tlbi issuer => ifetch ∨ issuer = tid end) prefix.
Proof.
  intros -> Hp. eapply list.Forall_impl; [exact Hp|]. intros [[|issuer] t] [Ht Ho]; cbn in *; auto with lia.
Qed.

Theorem fill_lookup_bi tid imem mem ev old new (own : bool) ifetch upper vpn asid
    tmin_ok tmin_unc tmax tmax' :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) →
  VMCacheState.cache_inv (length mem) old →
  TLB.fill_promise tid imem (ev :: mem) ev old = Ok (new, ()) →
  (own = true → Ev.tid ev = tid ∧ tmax' = tmax) →
  tmin_ok ≤ tmax → tmax ≤ length mem →
  (tmax' = tmax ∨ (tmax = length mem ∧ tmax' = S (length mem))) →
  let TI := if own then eq else TIf (length mem) tmax tmax' in
  (∀ r, Exec.elem_of_results r (TLB.lookup tid imem mem old ifetch upper vpn tmin_ok tmin_unc tmax asid) →
    ∃ r', Exec.elem_of_results r'
      (TLB.lookup tid imem (ev :: mem) new ifetch upper vpn tmin_ok tmin_unc tmax' asid) ∧ res_rel TI r r') ∧
  (∀ r', Exec.elem_of_results r'
      (TLB.lookup tid imem (ev :: mem) new ifetch upper vpn tmin_ok tmin_unc tmax' asid) →
    TLB.Result.tstart r' ≤ length mem →
    ∃ r, Exec.elem_of_results r (TLB.lookup tid imem mem old ifetch upper vpn tmin_ok tmin_unc tmax asid) ∧
      res_rel TI r r').
Proof.
  intros Hpositive Hok Hfill Hown Hmin Hmax Hcases TI.
  destruct Hok as [Hgood [Hunique Hvalid]].
  assert (Hok : VMCacheState.cache_inv (length mem) old) by (split; [exact Hgood|split; assumption]).
  split.
  - intros r Hin. apply VMLookupReplay.lookup_witness in Hin as (fe & events & candidates & Hentry & Hread & Hin).
    apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [Hctxt Hentry]].
    destruct (VMCacheFuture.promise_entry_forward tid imem mem ev old new ctxt fe events Hok Hfill Hentry)
      as [prefix [Hnew Hp]].
    destruct (VMCacheFuture.row_good _ old ctxt fe events Hgood Hunique Hentry) as [_ Hb].
    assert (Hreplay : ∃ candidates' r', TLB.get_result_from_FE tid imem (ev :: mem) ifetch vpn fe
        (prefix ++ events)%list tmin_ok tmin_unc tmax' = Ok candidates' ∧
      r' ∈ candidates' ∧ res_rel TI r r').
    { unfold TI. destruct own.
      - destruct (Hown eq_refl) as [Howner ->].
        rewrite entry_fixed_own; [exists candidates, r; auto using res_rel_eq_refl| |exact Hmax].
        eapply prefix_own; eassumption.
      - eapply entry_replay_forward; [exact Hpositive|eapply prefix_stamps; exact Hp|exact Hb|exact Hmax|exact Hcases|exact Hread|exact Hin]. }
    destruct Hreplay as [candidates' [r' [Hread' [Hin' Hr]]]]. exists r'. split; [|exact Hr].
    apply VMLookupReplay.lookup_witness. exists fe, (prefix ++ events)%list, candidates'.
    split; [apply VMLookupReplay.get_fes_witness; exists ctxt; auto|auto].
  - intros r' Hin Hstart. apply VMLookupReplay.lookup_witness in Hin as (fe & events & candidates' & Hentry & Hread & Hin).
    apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [Hctxt Hentry]].
    destruct (VMCacheFuture.promise_entry_backward tid imem mem ev old new ctxt fe events Hok Hfill Hentry)
      as [prefix [before [-> [Hp [Hbefore Hb]]]]].
    assert (Hreplay : ∃ candidates r, TLB.get_result_from_FE tid imem mem ifetch vpn fe
        before tmin_ok tmin_unc tmax = Ok candidates ∧ r ∈ candidates ∧ res_rel TI r r').
    { unfold TI. destruct own.
      - destruct (Hown eq_refl) as [Howner ->]. rewrite entry_fixed_own in Hread;
          [exists candidates', r'; auto using res_rel_eq_refl| |exact Hmax].
        eapply prefix_own; eassumption.
      - eapply entry_replay_backward; [exact Hpositive|eapply prefix_stamps; exact Hp|exact Hb|exact Hmin|exact Hmax|exact Hcases|exact Hread|exact Hin|exact Hstart]. }
    destruct Hreplay as [candidates [r [Hold [Hr Hrel]]]].
    destruct Hbefore as [->|Hbefore].
    { rewrite entry_empty in Hold. injection Hold as <-. inversion Hr. }
    exists r. split; [|exact Hrel]. apply VMLookupReplay.lookup_witness.
    exists fe, before, candidates. split; [apply VMLookupReplay.get_fes_witness; exists ctxt; auto|auto].
Qed.

Lemma uncacheable_end_bound bound parents ptes tmin tmax lvl :
  tmax ≤ bound → Forall (λ pte : bv 64 * nat, pte.2 ≤ S bound) ptes →
  Forall (λ r, TLB.Result.tend r ≤ bound)
    (TLB.get_results_from_events_uncacheable_aux parents ptes tmin tmax lvl).
Proof.
  revert ptes tmax. induction parents as [|parent parents IH]; intros ptes tmax Hmax Hp; [constructor|].
  destruct parent as [ttbr path start stop inv].
  revert tmax Hmax. induction Hp as [|[pte time] ptes Htime Hp IHptes]; intros tmax Hmax; [constructor|].
  cbn [TLB.get_results_from_events_uncacheable_aux TLB.Result.tstart TLB.Result.tend]. cbn in Htime.
  destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
  destruct (decide (time ≤ start)); destruct (decide (is_tlb_fillable lvl pte));
    try (constructor; [cbn; lia|]);
    first [apply IH; [exact Hmax|constructor; assumption]|apply IHptes; lia].
Qed.

Lemma entry_end_bound tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax results :
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax = Ok results →
  Forall (λ r, TLB.Result.tend r ≤ tmax) results.
Proof.
  unfold TLB.get_result_from_FE. destruct (decide (TLB.FE.is_table fe)).
  - unfold TLB.get_result_from_table_FE.
    destruct (decide (tmax < tmin_unc)); [injection 1 as <-; constructor|].
    destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection 1 as <-; constructor].
    destruct (TLB.get_results_from_events tid ifetch (TLB.FE.ttbr fe) (TLB.FE.ptes fe)
      events tmin_unc tmax None) as [|parent parents]; [injection 1 as <-; constructor|].
    destruct (Memory.read_all_pte _ imem mem tmin_unc tmax) as [ptes|err] eqn:Hp; [|discriminate].
    injection 1 as <-. apply (uncacheable_end_bound tmax (parent :: parents) ptes tmin_unc tmax lvl); [lia|].
    apply VMTableReplay.read_all_pte_bounded in Hp.
    eapply list.Forall_impl; [exact Hp|]. cbn. lia.
  - unfold TLB.get_result_from_leaf_FE. injection 1 as <-.
    destruct (decide (tmax < tmin_ok)); [constructor|apply parent_end_bound].
Qed.

Lemma entry_results_ok tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax bound results :
  tmax ≤ bound → Forall (λ event, event.2 ≤ bound) events →
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax = Ok results →
  Forall (VMViews.result_ok bound) results.
Proof.
  intros Hmax Hb Hread. destruct (decide (tmin_unc ≤ bound)) as [Hunc|Hunc].
  - exact (VMViews.fe_results_ok tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax bound
      results Hunc Hmax Hb Hread).
  - unfold TLB.get_result_from_FE in Hread. destruct (decide (TLB.FE.is_table fe)).
    + unfold TLB.get_result_from_table_FE in Hread. rewrite decide_True in Hread by lia.
      injection Hread as <-. constructor.
    + unfold TLB.get_result_from_leaf_FE in Hread. injection Hread as <-.
      destruct (decide (tmax < tmin_ok)); [constructor|].
      apply VMViews.events_ok; [exact Hmax|discriminate|exact Hb].
Qed.

Lemma cached_result_bounds tid imem mem cache ifetch upper vpn asid tmin_ok tmin_unc tmax r :
  VMCacheState.cache_inv (length mem) cache → tmax ≤ length mem →
  Exec.elem_of_results r (TLB.lookup tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid) →
  TLB.Result.tstart r ≤ length mem ∧ TLB.Result.tend r ≤ tmax ∧ VMViews.le_opt (length mem) (TLB.Result.inv_time r).
Proof.
  intros [Hgood [Hunique Hvalid]] Hmax Hin.
  apply VMLookupReplay.lookup_witness in Hin as (fe & events & results & Hentry & Hread & Hin).
  apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [_ Hentry]].
  destruct (VMCacheFuture.row_good _ cache ctxt fe events Hgood Hunique Hentry) as [_ Hb].
  pose proof (entry_results_ok tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax (length mem)
    results Hmax Hb Hread) as Hok.
  pose proof (entry_end_bound tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax results Hread) as Hend.
  rewrite Forall_forall in Hok, Hend. specialize (Hok r Hin). specialize (Hend r Hin).
  unfold VMViews.result_ok in Hok. tauto.
Qed.

Lemma root_result_bounds imem mem ts upper vpn ttbr0 tmin tmax r :
  tmax ≤ length mem →
  Exec.elem_of_results r (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin tmax) →
  TLB.Result.tstart r ≤ length mem ∧ TLB.Result.tend r ≤ tmax ∧ VMViews.le_opt (length mem) (TLB.Result.inv_time r).
Proof.
  intros Hmax Hin. apply root_lookup_witness in Hin
    as [Hmin (ttbrs & ttbr & vttbr & ptes & pte & vpte & Httbrs & Hchoice & Hread & Hin & Hinvalid & ->)].
  assert (Hreadmin : tmin ⊔ vttbr ≤ tmax).
  { destruct (decide (tmin ⊔ vttbr ≤ tmax)); [assumption|].
    unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw in Hread.
    rewrite decide_False in Hread by assumption. injection Hread as <-. inversion Hin. }
  apply VMTableReplay.read_all_pte_bounded in Hread.
  rewrite Forall_forall in Hread. specialize (Hread (pte, vpte) Hin).
  cbn in Hread. unfold join, join_nat in Hreadmin. split; [cbn; unfold join, join_nat; lia|].
  split; [cbn; lia|discriminate].
Qed.

Lemma emit_cache tid imem mem ev ts issued :
  TState.emit_promise tid imem mem ev ts = Ok issued →
  match TState.tlb ts, TState.tlb issued with
  | Some old, Some new => TLB.fill_promise tid imem mem ev old = Ok (new, ())
  | None, None => True
  | _, _ => False
  end.
Proof.
  unfold TState.emit_promise, TState.process_event.
  set (pending := if bool_decide (Ev.tid ev = tid) then
    match ev with Ev.Msg _ => TState.promise_write (length mem) ts
    | _ => TState.promise_tlbi (length mem) ts end else ts).
  assert (Hp : TState.tlb pending = TState.tlb ts).
  { unfold pending. destruct (bool_decide (Ev.tid ev = tid)); [destruct ev|]; reflexivity. }
  unfold TState.run_tlb. rewrite Hp. destruct (TState.tlb ts) as [old|].
  - destruct (TLB.fill_promise tid imem mem ev old) as [[new []]|err] eqn:Hfill;
      cbn; [|discriminate]. injection 1 as <-. destruct pending. reflexivity.
  - injection 1 as <-. rewrite Hp. exact I.
Qed.

Theorem lookup_bi_positive tid imem mem ev own :
  (∀ msg, Ev.get_msg ev = Some msg → (0 < Msg.size msg)%N) → LookupBi tid imem mem ev own.
Proof.
  intros Hpositive ts issued ifetch upper vpn asid ttbr0 tmin_ok tmin_unc Hts Howner Hpromise Hmin Hunc.
  cbn zeta.
  set (tmax := pred (TState.min_promise (length mem) ts)) in *.
  set (tmax' := pred (TState.min_promise (length (ev :: mem)) issued)).
  assert (Hmax : tmax ≤ length mem).
  { unfold tmax. pose proof (VMGuardReplay.min_promise_bound (length mem) ts). lia. }
  assert (Hcases : tmax' = tmax ∨ (tmax = length mem ∧ tmax' = S (length mem))).
  { exact (VMBoundsReplay.emit_promise_translation_bound_cases tid imem mem ev ts issued Hpromise). }
  assert (Hown : own = true → Ev.tid ev = tid ∧ tmax' = tmax).
  { intro H. split; [apply Howner, H|]. unfold tmax', tmax. cbn [length].
    rewrite (VMBoundsReplay.emit_own_promise_min tid imem mem ev ts issued (Howner H) Hpromise). reflexivity. }
  split; [destruct Hcases as [->|[-> ->]]; lia|].
  pose proof (emit_cache tid imem (ev :: mem) ev ts issued Hpromise) as Hcache.
  pose proof (VMLookupReplay.emit_promise_preserves_sreg tid imem (ev :: mem) ev ts issued TTBR1_EL1 Hpromise)
    as Hregs.
  destruct (TState.tlb ts) as [old|] eqn:Hold; destruct (TState.tlb issued) as [new|] eqn:Hnew;
    try contradiction.
  2: { unfold TState.tlb_lookup. rewrite Hold, Hnew.
    split; [intros r H; inversion H|]. split; intros r H; inversion H. }
  assert (Hok : VMCacheState.cache_inv (length mem) old) by (eapply VMViews.ok_cache; eassumption).
  destruct (fill_lookup_bi tid imem mem ev old new own ifetch upper vpn asid tmin_ok tmin_unc tmax tmax'
    Hpositive Hok Hcache Hown Hmin Hmax Hcases) as [Hforward Hbackward].
  assert (Hrootforward : ∀ r, Exec.elem_of_results r
      (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin_unc tmax) →
    ∃ r', Exec.elem_of_results r'
      (VMRootLookupReplay.root_lookup imem (ev :: mem) issued upper vpn ttbr0 tmin_unc tmax') ∧
      res_rel (if own then eq else TIf (length mem) tmax tmax') r r').
  { intros r Hr. destruct own.
    - destruct (Hown eq_refl) as [_ ->].
      rewrite (root_fixed_own imem mem ev ts issued upper vpn ttbr0 tmin_unc tmax Hregs Hmax).
      exists r. auto using res_rel_eq_refl.
    - eapply root_replay_forward; eassumption. }
  assert (Hrootbackward : ∀ r', Exec.elem_of_results r'
      (VMRootLookupReplay.root_lookup imem (ev :: mem) issued upper vpn ttbr0 tmin_unc tmax') →
    TLB.Result.tstart r' ≤ length mem →
    ∃ r, Exec.elem_of_results r
      (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin_unc tmax) ∧
      res_rel (if own then eq else TIf (length mem) tmax tmax') r r').
  { intros r' Hr Hstart. destruct own.
    - destruct (Hown eq_refl) as [_ ->].
      rewrite (root_fixed_own imem mem ev ts issued upper vpn ttbr0 tmin_unc tmax Hregs Hmax) in Hr.
      exists r'. auto using res_rel_eq_refl.
    - eapply root_replay_backward; eassumption. }
  unfold TState.tlb_lookup. rewrite Hold, Hnew.
  cbn [Exec.merge Exec.results].
  split.
  - intros r Hr. apply elem_of_app in Hr as [Hr|Hr].
    + eapply cached_result_bounds; eassumption.
    + eapply root_result_bounds; eassumption.
  - split.
    + intros r Hr. apply elem_of_app in Hr as [Hr|Hr].
      * destruct (Hforward r Hr) as [r' [Hr' Hrel]]. exists r'. split; [apply elem_of_app; left; exact Hr'|exact Hrel].
      * destruct (Hrootforward r Hr) as [r' [Hr' Hrel]]. exists r'. split; [apply elem_of_app; right; exact Hr'|exact Hrel].
    + intros r' Hr Hstart. apply elem_of_app in Hr as [Hr|Hr].
      * destruct (Hbackward r' Hr Hstart) as [r [Hr' Hrel]]. exists r. split; [apply elem_of_app; left; exact Hr'|exact Hrel].
      * destruct (Hrootbackward r' Hr Hstart) as [r [Hr' Hrel]]. exists r. split; [apply elem_of_app; right; exact Hr'|exact Hrel].
Qed.

Theorem lookup_replay {n} : @LookupReplay n.
Proof.
  intros tid imem mem ev own Hpositive. apply lookup_bi_positive.
  destruct ev as [msg|tlbi recipient epoch]; cbn; [|discriminate].
  intros found Heq. injection Heq as <-. exact Hpositive.
Qed.

(** Lookup replay is discharged. The remaining semantic obligations are the
    reachable walk-shape invariant and the TLBI exchange simulation. *)
Theorem final_state_equiv_lookup (bbm nondet : bool) {n : nat} (term : terminationCondition n)
    (initMs : archState n) (code : code_region) :
  VMWalkReplay.ShInvariant bbm nondet term initMs (@Shape n) →
  VMNormalization.VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  (∀ initPs fuel returned fsig,
    PState.from_archState (VMPromising bbm) initMs = Ok initPs →
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) (VMPromising bbm) n)
        fuel term initMs initPs) →
    VMNormalization.VMNormalizationSearchesComplete bbm nondet term initMs (projT1 fsig)) →
  (∀ fuel fs (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf_uncached (VMPromising bbm) (sail_tiny_arm_sem nondet)
        fuel n term initMs →
    PromiseFirstSearchesCompleteFromInitial (VMPromising bbm) nondet term initMs fuel) →
  VMPromisingFinalStateEquiv bbm (sail_tiny_arm_sem nondet) term initMs.
Proof. apply final_state_equiv_start, lookup_replay. Qed.

End VMWalkLookup.
