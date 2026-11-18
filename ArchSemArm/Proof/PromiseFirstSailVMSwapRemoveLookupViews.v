(******************************************************************************)
(* Lookup start views and invalidation deadlines under timestamp exclusion   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstSailVMViews
  PromiseFirstSailVMCacheState PromiseFirstSailVMBBMTransport PromiseFirstSailVMLookup
  PromiseFirstSailVMRootLookup PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveViews
  PromiseFirstSailVMSwapRemoveHistory PromiseFirstSailVMSwapRemoveEvents
  PromiseFirstSailVMSwapRemoveTimes PromiseFirstSailVMSwapRemoveThread.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveLookupViews.
Import VMPromising VMSwapRemoveState VMSwapRemoveViews VMSwapRemoveEvents.
#[local] Typeclasses Transparent view UMPromising.view.

Definition result_ok p limit (result : TLB.Result.t) :=
  allowed p limit (TLB.Result.tstart result) ∧ opt_ok (λ t, t ≠ p) (TLB.Result.inv_time result).
Lemma load_allowed p limit t : event_allowed p limit (TLB.Entry.Load, t) → allowed p limit t.
Proof. intros [H|[_ H]]; [left|right]; exact H. Qed.
Lemma tlbi_avoids p limit tid t : event_allowed p limit (TLB.Entry.Tlbi tid, t) → t ≠ p.
Proof. intros [H|[H _]]; [exact H|discriminate]. Qed.

Lemma events_ok p limit tid ifetch ttbr path events tmin tmax inv :
  allowed p limit tmin → opt_ok (λ t, t ≠ p) inv → Forall (event_allowed p limit) events →
  Forall (result_ok p limit) (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof.
  revert tmin tmax inv.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmin tmax inv Hmin Hinv Hevents. destruct events as [|[event time] events].
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); constructor.
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); [constructor|].
    apply list.Forall_cons in Hevents as [Htime Hevents]. destruct event.
    + apply load_allowed in Htime. destruct (decide (tmax < time)).
      { apply IH; [unfold ltof; cbn; lia|exact Hmin|exact Hinv|exact Hevents]. }
      destruct (decide (time < tmin)).
      { constructor; [split; [exact Hmin|exact Hinv]|constructor]. }
      destruct events as [|[event' time'] rest].
      * constructor; [split; [exact Htime|exact Hinv]|].
        apply IH; [unfold ltof; cbn; lia|exact Hmin|exact Hinv|exact Hevents].
      * destruct event'.
        -- constructor; [split; [exact Htime|exact Hinv]|].
           apply IH; [unfold ltof; cbn; lia|exact Hmin|exact Hinv|exact Hevents].
        -- pose proof Hevents as Hall. apply list.Forall_cons in Hevents as [_ Hrest].
           destruct (decide (time = time' ∧ (ifetch ∨ tid0 = tid))).
           ++ destruct rest as [|[[|issuer] stamp] rest].
              2: apply IH; [unfold ltof; cbn; lia|exact Hmin|exact Hinv|exact Hrest].
              all: constructor; [split; [exact Htime|exact Hinv]|].
              all: apply IH; [unfold ltof; cbn; lia|exact Hmin|exact Hinv|exact Hall].
           ++ constructor; [split; [exact Htime|exact Hinv]|].
              apply IH; [unfold ltof; cbn; lia|exact Hmin|exact Hinv|exact Hall].
    + apply tlbi_avoids in Htime. destruct (decide (ifetch ∨ tid0 = tid)).
      * apply IH; [unfold ltof; cbn; lia|exact Hmin|exact Hinv|exact Hevents].
      * apply IH; [unfold ltof; cbn; lia|exact Hmin| |exact Hevents].
        intros t Ht. injection Ht as <-. exact Htime.
Qed.

Lemma uncacheable_ok p limit results ptes tmin tmax lvl :
  allowed p limit tmin → Forall (result_ok p limit) results →
  Forall (λ pte, allowed p limit pte.2) ptes →
  Forall (result_ok p limit) (TLB.get_results_from_events_uncacheable_aux results ptes tmin tmax lvl).
Proof.
  intros Hmin Hresults. revert ptes tmax.
  induction Hresults as [|result results Hhead Htail IH]; intros ptes tmax Hptes; [constructor|].
  destruct result as [ttbr path start stop inv], Hhead as [Hstart Hinv]. cbn in Hstart, Hinv.
  cbn [TLB.get_results_from_events_uncacheable_aux].
  revert tmax. induction Hptes as [|[pte time] ptes Htime Hptes IHptes]; intro tmax; [constructor|].
  cbn [TLB.Result.tstart TLB.Result.tend]. cbn in Htime.
  destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
  destruct (decide (time ≤ start)); destruct (decide (is_tlb_fillable lvl pte));
    try (constructor; [split; cbn; [repeat apply allowed_max; assumption|exact Hinv]|]);
    first [apply IH; constructor; assumption|apply IHptes].
Qed.

Section Removed.
Context (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation mem := (l ++ Ev.Tlbi tlbi rc epoch :: r).

Lemma ptes_ok limit addr tmin tmax ptes : tmax ≤ length mem →
  Memory.read_all_pte addr imem mem tmin tmax = Ok ptes → Forall (λ pte, allowed p limit pte.2) ptes.
Proof.
  intros Hmax Hread. apply list.Forall_forall. intros pte Hin. left.
  eapply VMSwapRemoveTimes.read_all_pte_avoids; eassumption.
Qed.

Lemma fe_results_ok limit tid ifetch vpn fe events tmin_ok tmin_unc tmax results :
  allowed p limit tmin_ok → allowed p limit tmin_unc → tmax ≤ length mem →
  Forall (event_allowed p limit) events →
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax = Ok results →
  Forall (result_ok p limit) results.
Proof.
  intros Hok Hunc Hmax Hevents. unfold TLB.get_result_from_FE. case_decide.
  - unfold TLB.get_result_from_table_FE.
    destruct (decide (tmax < tmin_unc)); [injection 1 as <-; constructor|].
    destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection 1 as <-; constructor].
    match goal with |- context[TLB.get_results_from_events ?a ?b ?c ?d ?e ?f ?g ?h] =>
      assert (Hpres : Forall (result_ok p limit) (TLB.get_results_from_events a b c d e f g h))
        by (apply events_ok; [exact Hunc|discriminate|exact Hevents]);
      destruct (TLB.get_results_from_events a b c d e f g h) as [|candidate candidates]
    end; [injection 1 as <-; constructor|].
    match goal with |- context[Memory.read_all_pte ?a ?b ?c ?d ?e] =>
      destruct (Memory.read_all_pte a b c d e) as [ptes|err] eqn:Hread end; cbn; [|discriminate].
    injection 1 as <-.
    exact (uncacheable_ok p limit (candidate :: candidates) ptes tmin_unc tmax lvl Hunc Hpres
      (ptes_ok limit _ _ _ _ Hmax Hread)).
  - unfold TLB.get_result_from_leaf_FE. injection 1 as <-.
    destruct (decide (tmax < tmin_ok)); [constructor|]. apply events_ok; [exact Hok|discriminate|exact Hevents].
Qed.

Lemma lookup_ok limit tid cache ifetch upper vpn tmin_ok tmin_unc tmax asid result :
  VMCacheState.cache_inv (length mem) cache →
  VMSwapRemoveHistory.histories (event_allowed p limit) cache →
  allowed p limit tmin_ok → allowed p limit tmin_unc → tmax ≤ length mem →
  Exec.elem_of_results result (TLB.lookup tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid) →
  result_ok p limit result.
Proof.
  intros [Hgood [Hunique _]] Hhist Hok Hunc Hmax Hin.
  apply VMLookupReplay.lookup_witness in Hin as (fe & events & candidates & Hentry & Hget & Hin).
  assert (Hevents : Forall (event_allowed p limit) events).
  { apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [_ Hentry]].
    unfold TLB.VATLB.get_fe in Hentry.
    apply list_elem_of_In, List.in_map_iff in Hentry as [[entry events'] [Heq Hentry]].
    apply list_elem_of_In in Hentry. injection Heq as <- <-.
    rewrite <- (VMBBMTransport.row_history cache ctxt entry events' Hunique Hentry). apply Hhist. }
  eapply VMViews.Forall_elem; [|exact Hin]. eapply fe_results_ok; [| | | |exact Hget]; assumption.
Qed.

Lemma root_lookup_ok limit ts upper vpn ttbr0 tmin_unc tmax result :
  ts_ok (allowed p limit) ts → allowed p limit tmin_unc → tmax ≤ length mem →
  Exec.elem_of_results result (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin_unc tmax) →
  result_ok p limit result.
Proof.
  intros Hts Hunc Hmax. unfold VMRootLookupReplay.root_lookup.
  destruct (decide (tmin_unc ≤ tmax)); [|intro H; inversion H].
  intro Hin. apply Exec.elem_of_res_bind_elim in Hin as [ttbrs [Hregs Hin]].
  apply Exec.elem_of_res_bind_elim in Hin as [[ttbr vttbr] [Hchoice Hin]].
  apply Exec.elem_of_res_bind_elim in Hin as [ptes [Hread Hin]].
  apply PromiseFirstCurrent.lift_result_res_success in Hread, Hregs.
  apply Exec.elem_of_res_mchoosel_inv in Hin, Hchoice.
  apply list_elem_of_fmap in Hin as [[pte vpte] [-> Hin]].
  apply list_elem_of_filter in Hin as [_ Hin].
  assert (Hvttbr : allowed p limit vttbr).
  { destruct upper.
    - unfold othrow in Hregs.
      destruct (TState.read_sreg_indirect ts TTBR1_EL1) as [vvs|] eqn:Hvvs; [|discriminate].
      injection Hregs as <-. exact (read_sreg_indirect _ ts _ _ Hts Hvvs _ Hchoice).
    - injection Hregs as <-. apply list_elem_of_singleton in Hchoice. injection Hchoice as _ ->.
      apply allowed_zero. lia. }
  pose proof (ptes_ok limit _ _ _ _ Hmax Hread) as Hptes.
  pose proof (VMViews.Forall_elem _ _ _ Hptes Hin) as Hvpte. cbn in Hvpte.
  split; cbn; [repeat apply allowed_max; assumption|discriminate].
Qed.

Lemma tlb_lookup_ok tid ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax result :
  VMViews.ts_ok (length mem) ts → VMSwapRemoveThread.thread_ok p ts →
  allowed p (TState.vcse ts) tmin_ok → allowed p (TState.vcse ts) tmin_unc → tmax ≤ length mem →
  Exec.elem_of_results result (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) →
  result_ok p (TState.vcse ts) result.
Proof.
  intros Hbound [Hts Hcache] Hok Hunc Hmax Hin. unfold TState.tlb_lookup in Hin.
  destruct (TState.tlb ts) as [cache|] eqn:Hc;
    [|unfold Exec.elem_of_results in Hin; cbn in Hin; inversion Hin].
  unfold Exec.elem_of_results, Exec.merge in Hin. cbn [Exec.results] in Hin.
  apply elem_of_app in Hin as [Hin|Hin].
  - eapply lookup_ok; [apply (VMViews.ok_cache _ _ Hbound), Hc|apply (proj1 (Hcache cache Hc))|
      exact Hok|exact Hunc|exact Hmax|exact Hin].
  - eapply root_lookup_ok; eassumption.
Qed.
End Removed.

Lemma merge_into_ok p limit result results : result_ok p limit result → Forall (result_ok p limit) results →
  Forall (result_ok p limit) (TLB.Result.merge_into result results).
Proof.
  intros Hresult Hresults. induction Hresults as [|other results Hother Hresults IH]; cbn;
    [constructor; [exact Hresult|constructor]|].
  case_decide; constructor; try assumption.
  destruct Hother as [Hstart Hinv], Hresult as [Hstart' Hinv']. split.
  - apply allowed_min; assumption.
  - change (opt_ok (λ t, t ≠ p) (TLB.Result.inv_time
      (if TLB.Result.walk_lt (TLB.Result.walk result) (TLB.Result.walk other) then result else other))).
    destruct (TLB.Result.walk_lt _ _); assumption.
Qed.
Lemma merge_ok p limit results : Forall (result_ok p limit) results → Forall (result_ok p limit) (TLB.Result.merge results).
Proof.
  unfold TLB.Result.merge. intro Hresults.
  cut (∀ acc, Forall (result_ok p limit) acc →
    Forall (result_ok p limit) (foldl (λ acc r, TLB.Result.merge_into r acc) acc results));
    [intro H; apply H; constructor|].
  induction Hresults as [|result results Hresult Hresults IH]; intros acc Hacc; cbn; [exact Hacc|].
  apply IH, merge_into_ok; assumption.
Qed.
End VMSwapRemoveLookupViews.
