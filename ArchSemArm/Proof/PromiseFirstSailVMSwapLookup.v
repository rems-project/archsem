(******************************************************************************)
(* TLB lookups over a history with an inserted TLBI                           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCache PromiseFirstSailVMCacheLastTLBI
  PromiseFirstSailVMCacheSim
  PromiseFirstSailVMRootLookup PromiseFirstSailVMSwapSim.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

(** Lookups of a cache mapped by [tlb_map (shift p)] give results related by
    [res_rel p]: equal walk, [tstart] shifted, [tend] equal after [unshift p],
    and [inv_time] shifted. [tend] cannot be shifted exactly: an entry
    invalidated at timestamp [p] of the shorter history is valid until [p - 1]
    there and until [p] in the longer one. For arbitrary related lists,
    merging only refines ([merge_match]). Within one lookup bounded by [T],
    however, a result [tend] is [p - 1] only when [T] is, so [unshift p] is
    injective on its [tend] values and the merged alternatives are related one
    to one ([tlb_lookup_merge_map]). *)

Module VMSwapLookup.
Import VMPromising VMSwapSim.

(** * Timestamp facts *)

Lemma lt_shift_iff p a x : 0 < p → a < shift p x ↔ unshift p a < x.
Proof. intro. shift_cases. Qed.

Lemma unshift_min_pred p a t : 0 < p →
  unshift p (a `min` pred (shift p t)) = unshift p a `min` pred t.
Proof. intro. shift_cases. Qed.

Lemma unshift_min p a b : unshift p (a `min` b) = unshift p a `min` unshift p b.
Proof. shift_cases. Qed.

Lemma unshift_shift_max p a b :
  unshift p (shift p a `max` b) = a `max` unshift p b.
Proof. shift_cases. Qed.

(** * Related results *)

Definition res_rel (p : nat) (x y : TLB.Result.t) : Prop :=
  TLB.Result.ttbr y = TLB.Result.ttbr x ∧ TLB.Result.path y = TLB.Result.path x ∧
  TLB.Result.tstart y = shift p (TLB.Result.tstart x) ∧
  unshift p (TLB.Result.tend y) = TLB.Result.tend x ∧
  TLB.Result.inv_time y = shift p <$> TLB.Result.inv_time x.

Lemma res_rel_make p ttbr path ts te te' inv :
  unshift p te' = te →
  res_rel p (TLB.Result.make ttbr path ts te inv)
    (TLB.Result.make ttbr path (shift p ts) te' (shift p <$> inv)).
Proof. intro H. repeat split; cbn; auto. Qed.

Section Events.
Context (p : nat) (Hp : 0 < p) (tid : nat) (ifetch : bool) (ttbr : bv 64) (path : list (bv 64)).

Lemma get_results_from_events_map events : ∀ tmin tmax tmax' inv,
  unshift p tmax' = tmax →
  Forall2 (res_rel p)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv)
    (TLB.get_results_from_events tid ifetch ttbr path (map_evs (shift p) events)
      (shift p tmin) tmax' (shift p <$> inv)).
Proof using Hp.
  induction events as [events IH] using (induction_ltof1 _ (@length _)).
  unfold ltof in IH. destruct events as [|[ev t] events]; intros tmin tmax tmax' inv Hmax.
  all: assert (Hlt : tmax' < shift p tmin ↔ tmax < tmin)
    by (pose proof (lt_shift_iff p tmax' tmin Hp) as H; rewrite Hmax in H; exact H).
  all: cbn [TLB.get_results_from_events map_evs map fst snd].
  all: destruct (decide (tmax < tmin)) as [Hs|Hs];
    destruct (decide (tmax' < shift p tmin)) as [Hs'|Hs']; try tauto; [constructor|].
  - constructor.
  - destruct ev as [|tidt].
    + assert (Hl1 : tmax' < shift p t ↔ tmax < t)
        by (pose proof (lt_shift_iff p tmax' t Hp) as H; rewrite Hmax in H; exact H).
      destruct (decide (tmax < t)) as [Ht|Ht];
        destruct (decide (tmax' < shift p t)) as [Ht'|Ht']; try tauto;
        [apply (IH events ltac:(cbn; lia) _ _ _ _ Hmax)|].
      destruct (decide (t < tmin)) as [Hm|Hm];
        destruct (decide (shift p t < shift p tmin)) as [Hm'|Hm'];
        try (rewrite shift_lt_iff in Hm'; tauto);
        try (exfalso; apply Hm', shift_lt_iff, Hm).
      * constructor; [apply res_rel_make, Hmax|constructor].
      * destruct events as [|[[|tidt'] t'] events'];
          cbn [map_evs map fst snd].
        -- constructor; [apply res_rel_make, Hmax|apply (IH [] ltac:(cbn; lia) _ _ _ _ Hmax)].
        -- constructor; [apply res_rel_make, Hmax|].
           apply (IH ((TLB.Entry.Load, t') :: events') ltac:(cbn; lia) _ _ _ _ Hmax).
        -- destruct (decide (t = t' ∧ (ifetch ∨ tidt' = tid))) as [Hc|Hc];
             destruct (decide (shift p t = shift p t' ∧ (ifetch ∨ tidt' = tid))) as [Hc'|Hc'].
           ++ destruct events' as [|[[|tidt''] t''] events'']; cbn [map_evs map fst snd];
                first [apply IH; [cbn; lia|exact Hmax]
                  |constructor; [apply res_rel_make, Hmax|apply IH; [cbn; lia|exact Hmax]]].
           ++ exfalso. apply Hc'. destruct Hc as [-> Hc]. auto.
           ++ exfalso. apply Hc. destruct Hc' as [Hc' Hi]. apply shift_inj in Hc'. auto.
           ++ constructor; [apply res_rel_make, Hmax|].
              apply (IH ((TLB.Entry.Tlbi tidt', t') :: events') ltac:(cbn; lia) _ _ _ _ Hmax).
    + assert (Hm : unshift p (tmax' `min` pred (shift p t)) = tmax `min` pred t)
        by (rewrite unshift_min_pred, Hmax by exact Hp; reflexivity).
      destruct (decide (ifetch ∨ tidt = tid)).
      * apply (IH events ltac:(cbn; lia) _ _ _ _ Hm).
      * apply (IH events ltac:(cbn; lia) _ _ _ (Some t) Hm).
Qed.

End Events.

Lemma unshift_pred_shift p t : 0 < p → unshift p (pred (shift p t)) = pred t.
Proof. intro. shift_cases. Qed.

Definition map_ptes (p : nat) (ptes : list (bv 64 * nat)) : list (bv 64 * nat) :=
  map (λ vt, (vt.1, shift p vt.2)) ptes.

(** The inner loop of [TLB.get_results_from_events_uncacheable_aux], named. *)
Fixpoint unc_inner (r : TLB.Result.t) (rs : list TLB.Result.t) (tmin : nat) (lvl : Level)
    (ptes : list (bv 64 * nat)) (tmax : nat) : list TLB.Result.t :=
  match ptes with
  | [] => []
  | (pte, tpte) :: nptes =>
      if decide (TLB.Result.tend r `min` tmax < tmin) then []
      else
        let rest :=
          if decide (tpte ≤ TLB.Result.tstart r)
          then TLB.get_results_from_events_uncacheable_aux rs ptes tmin tmax lvl
          else unc_inner r rs tmin lvl nptes (pred tpte) in
        if decide (is_tlb_fillable lvl pte) then rest
        else
          (r |> set TLB.Result.path (.++ [pte])
             |> setv TLB.Result.tstart (TLB.Result.tstart r `max` tpte `max` tmin)
             |> setv TLB.Result.tend (TLB.Result.tend r `min` tmax)) :: rest
  end.

Lemma unc_cons r rs ptes tmin tmax lvl :
  TLB.get_results_from_events_uncacheable_aux (r :: rs) ptes tmin tmax lvl =
  unc_inner r rs tmin lvl ptes tmax.
Proof.
  revert tmax. induction ptes as [|[pte tpte] ptes IH]; intro tmax; [reflexivity|].
  cbn [unc_inner]. rewrite <- IH. reflexivity.
Qed.

Lemma uncacheable_aux_map p (Hp : 0 < p) lvl tmin results results' :
  Forall2 (res_rel p) results results' →
  ∀ ptes tmax tmax', unshift p tmax' = tmax →
  Forall2 (res_rel p)
    (TLB.get_results_from_events_uncacheable_aux results ptes tmin tmax lvl)
    (TLB.get_results_from_events_uncacheable_aux results' (map_ptes p ptes)
      (shift p tmin) tmax' lvl).
Proof.
  induction 1 as [|r r' rs rs' Hr Hrs IH]; intros ptes tmax tmax' Hmax; [constructor|].
  rewrite !unc_cons.
  revert tmax tmax' Hmax. induction ptes as [|[pte tpte] ptes IHp]; intros tmax tmax' Hmax;
    cbn [unc_inner map_ptes map fst snd]; [constructor|].
  pose proof Hr as (Httbr & Hpath & Hstart & Hend & Hinv).
  assert (Hrng : unshift p (TLB.Result.tend r' `min` tmax') = TLB.Result.tend r `min` tmax)
    by (rewrite unshift_min, Hend, Hmax; reflexivity).
  assert (Hlt : TLB.Result.tend r' `min` tmax' < shift p tmin ↔
      TLB.Result.tend r `min` tmax < tmin)
    by (pose proof (lt_shift_iff p (TLB.Result.tend r' `min` tmax') tmin Hp) as H;
        rewrite Hrng in H; exact H).
  destruct (decide (TLB.Result.tend r `min` tmax < tmin)) as [H1|H1];
    destruct (decide (TLB.Result.tend r' `min` tmax' < shift p tmin)) as [H2|H2];
    try tauto; [constructor|].
  assert (Hrest : Forall2 (res_rel p)
    (if decide (tpte ≤ TLB.Result.tstart r)
     then TLB.get_results_from_events_uncacheable_aux rs ((pte, tpte) :: ptes) tmin tmax lvl
     else unc_inner r rs tmin lvl ptes (pred tpte))
    (if decide (shift p tpte ≤ TLB.Result.tstart r')
     then TLB.get_results_from_events_uncacheable_aux rs'
       ((pte, shift p tpte) :: map_ptes p ptes) (shift p tmin) tmax' lvl
     else unc_inner r' rs' (shift p tmin) lvl (map_ptes p ptes) (pred (shift p tpte)))).
  { rewrite Hstart. destruct (decide (tpte ≤ TLB.Result.tstart r)) as [H3|H3];
      destruct (decide (shift p tpte ≤ shift p (TLB.Result.tstart r))) as [H4|H4];
      try (rewrite shift_le_iff in H4; tauto);
      try (exfalso; apply H4, shift_le_iff, H3).
    - apply (IH ((pte, tpte) :: ptes) tmax tmax' Hmax).
    - apply IHp. apply unshift_pred_shift, Hp. }
  destruct (decide (is_tlb_fillable lvl pte)); [exact Hrest|].
  constructor; [|exact Hrest].
  clear -Httbr Hpath Hstart Hrng Hinv.
  destruct r as [t1 p1 s1 e1 i1], r' as [t2 p2 s2 e2 i2].
  cbn in Httbr, Hpath, Hstart, Hrng, Hinv. subst t2 p2 s2 i2.
  repeat split; cbn; [rewrite !shift_max; reflexivity|exact Hrng].
Qed.

(** * Related computations *)

Definition result_rel {A B} (R : A → B → Prop) (x : result string A) (y : result string B) :=
  match x, y with
  | Ok a, Ok b => R a b
  | Error e, Error e' => e = e'
  | _, _ => False
  end.

Definition res_lift {A B} (R : A → B → Prop) (x : Exec.res string A) (y : Exec.res string B) :=
  Forall2 R (Exec.results x) (Exec.results y) ∧ Exec.errors x = Exec.errors y.

Lemma res_lift_mchoosel {A B} (R : A → B → Prop) la lb :
  Forall2 R la lb → res_lift R (mchoosel la) (mchoosel lb).
Proof.
  intro H. split; [rewrite !VMCacheSim.mchoosel_results; exact H|reflexivity].
Qed.

Lemma res_lift_bind {A B C D} (R : A → B → Prop) (S : C → D → Prop)
    (x : Exec.res string A) (y : Exec.res string B) ka kb :
  res_lift R x y → (∀ a b, R a b → res_lift S (ka a) (kb b)) →
  res_lift S (x ≫= ka) (y ≫= kb).
Proof.
  intros [Hr He] Hk. split.
  - rewrite !VMCacheSim.res_bind_results.
    induction Hr as [|a b la lb Hab _ IH]; cbn; [constructor|].
    apply Forall2_app; [apply (Hk a b Hab)|exact IH].
  - rewrite !VMCacheSim.res_bind_errors, He. f_equal.
    clear He. induction Hr as [|a b la lb Hab _ IH]; cbn; [reflexivity|].
    rewrite (proj2 (Hk a b Hab)), IH. reflexivity.
Qed.

Lemma res_lift_lift {A B} (R : A → B → Prop) (x : result string A) (y : result string B) :
  result_rel R x y → res_lift R (mlift x) (mlift y).
Proof.
  destruct x as [a|e], y as [b|e']; cbn; try tauto.
  - intro H. split; [constructor; [exact H|constructor]|reflexivity].
  - intros ->. split; [constructor|reflexivity].
Qed.

Section Lookup.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat)
  (ifetch upper : bool) (vpn : pn).
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

Lemma leaf_FE_map fe events tmin tmax tmax' : unshift p tmax' = tmax →
  Forall2 (res_rel p)
    (TLB.get_result_from_leaf_FE tid ifetch fe events tmin tmax)
    (TLB.get_result_from_leaf_FE tid ifetch fe (map_evs f events) (f tmin) tmax').
Proof.
  intro Hmax. unfold TLB.get_result_from_leaf_FE.
  assert (Hlt : tmax' < f tmin ↔ tmax < tmin)
    by (pose proof (lt_shift_iff p tmax' tmin ltac:(lia)) as H; rewrite Hmax in H; exact H).
  destruct (decide (tmax < tmin)); destruct (decide (tmax' < f tmin)); try tauto; [constructor|].
  exact (get_results_from_events_map p ltac:(lia) tid ifetch _ _ events tmin tmax tmax' None Hmax).
Qed.

Lemma table_FE_map fe events tmin tmax tmax' : unshift p tmax' = tmax →
  tmax' ≤ S (length mem) →
  result_rel (Forall2 (res_rel p))
    (TLB.get_result_from_table_FE tid imem mem ifetch vpn fe events tmin tmax)
    (TLB.get_result_from_table_FE tid imem mem' ifetch vpn fe (map_evs f events) (f tmin) tmax').
Proof.
  intros Hmax Hb. unfold TLB.get_result_from_table_FE.
  assert (Hlt : tmax' < f tmin ↔ tmax < tmin)
    by (pose proof (lt_shift_iff p tmax' tmin ltac:(lia)) as H; rewrite Hmax in H; exact H).
  destruct (decide (tmax < tmin)); destruct (decide (tmax' < f tmin)); try tauto;
    [cbn; constructor|].
  destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|cbn; constructor].
  pose proof (get_results_from_events_map p ltac:(lia) tid ifetch (TLB.FE.ttbr fe)
    (TLB.FE.ptes fe) events tmin tmax tmax' None Hmax) as Hres.
  change (shift p <$> None) with (@None nat) in Hres.
  destruct (TLB.get_results_from_events tid ifetch _ _ events tmin tmax None) as [|x xs];
    destruct (TLB.get_results_from_events tid ifetch _ _ (map_evs f events) (f tmin) tmax' None)
      as [|y ys];
    try (inversion Hres; fail); [cbn; constructor|].
  rewrite (read_all_pte_remove _ imem l r tlbi rc k (f tmin) tmax') by lia.
  rewrite unshift_shift, Hmax.
  destruct (Memory.read_all_pte _ imem mem tmin tmax) as [ptes|err]; cbn; [|reflexivity].
  exact (uncacheable_aux_map p ltac:(lia) lvl tmin (x :: xs) (y :: ys) Hres ptes tmax tmax' Hmax).
Qed.

Lemma FE_map fe events tmin_ok tmin_unc tmax tmax' : unshift p tmax' = tmax →
  tmax' ≤ S (length mem) →
  result_rel (Forall2 (res_rel p))
    (TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax)
    (TLB.get_result_from_FE tid imem mem' ifetch vpn fe (map_evs f events)
      (f tmin_ok) (f tmin_unc) tmax').
Proof.
  intros Hmax Hb. unfold TLB.get_result_from_FE. case_decide.
  - apply table_FE_map; assumption.
  - cbn. apply leaf_FE_map, Hmax.
Qed.

Lemma get_fes_map c ctxts :
  TLB.get_fes (tlb_map f c) ctxts =
  map (λ row, (row.1, map_evs f row.2)) (TLB.get_fes c ctxts).
Proof.
  unfold TLB.get_fes. induction ctxts as [|ctxt ctxts IH]; [reflexivity|].
  cbn [map List.concat]. rewrite map_app, IH. f_equal.
  unfold TLB.VATLB.get_fe. rewrite tlb_map_vatlb, vatlb_get_map, !map_map.
  apply map_ext. intros [entry evs]. reflexivity.
Qed.

Lemma Forall2_map_r {A B} (g : A → B) (la : list A) :
  Forall2 (λ x y, y = g x) la (map g la).
Proof. induction la; constructor; auto. Qed.

(** Lookups of the shifted cache give related alternatives and equal errors. *)
Theorem lookup_map c tmin_ok tmin_unc tmax tmax' asid : unshift p tmax' = tmax →
  tmax' ≤ S (length mem) →
  res_lift (res_rel p)
    (TLB.lookup tid imem mem c ifetch upper vpn tmin_ok tmin_unc tmax asid)
    (TLB.lookup tid imem mem' (tlb_map f c) ifetch upper vpn (f tmin_ok) (f tmin_unc)
      tmax' asid).
Proof.
  intros Hmax Hb. rewrite !VMCacheSim.lookup_shape.
  apply (res_lift_bind (λ row row', row' = (row.1, map_evs f row.2))).
  - apply res_lift_mchoosel. rewrite get_fes_map. apply Forall2_map_r.
  - intros [fe events] row' ->. cbn [fst snd VMCacheSim.fe_res].
    apply (res_lift_bind (Forall2 (res_rel p))).
    + apply res_lift_lift, FE_map; assumption.
    + intros la lb Hl. apply res_lift_mchoosel, Hl.
Qed.

Lemma read_all_pte_map addr tmin tmax tmax' : unshift p tmax' = tmax →
  tmax' ≤ S (length mem) →
  Memory.read_all_pte addr imem mem' (f tmin) tmax' =
  map_ptes p <$> Memory.read_all_pte addr imem mem tmin tmax.
Proof.
  intros Hmax Hb. destruct (decide (tmin ≤ tmax)) as [Hle|Hlt].
  - rewrite (read_all_pte_remove addr imem l r tlbi rc k (f tmin) tmax').
    + rewrite unshift_shift, Hmax. reflexivity.
    + pose proof (lt_shift_iff p tmax' tmin ltac:(lia)) as H. rewrite Hmax in H. lia.
    + exact Hb.
  - assert (Hlt' : tmax' < f tmin)
      by (pose proof (lt_shift_iff p tmax' tmin ltac:(lia)) as H; rewrite Hmax in H; lia).
    unfold Memory.read_all_pte, Memory.read_all_btw, PromMemory.read_all_btw.
    rewrite !decide_False by lia. reflexivity.
Qed.

Lemma filter_map_ptes P `{∀ x, Decision (P x)} ptes :
  filter (λ '(pte, _), P pte) (map_ptes p ptes) =
  map_ptes p (filter (λ '(pte, _), P pte) ptes).
Proof.
  induction ptes as [|[pte t] ptes IH]; [reflexivity|]. unfold map_ptes in *.
  cbn [map fst snd]. rewrite !filter_cons. case_decide; cbn [map fst snd]; rewrite IH; reflexivity.
Qed.

(** Uncached invalid root entries. *)
Lemma root_lookup_map ts ts' ttbr0 tmin_unc tmax tmax' :
  TState.read_sreg_indirect ts' TTBR1_EL1 =
    map (λ vw, (vw.1, f vw.2)) <$> TState.read_sreg_indirect ts TTBR1_EL1 →
  unshift p tmax' = tmax → tmax' ≤ S (length mem) →
  res_lift (res_rel p)
    (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin_unc tmax)
    (VMRootLookupReplay.root_lookup imem mem' ts' upper vpn ttbr0 (f tmin_unc) tmax').
Proof.
  intros Hreg Hmax Hb. unfold VMRootLookupReplay.root_lookup.
  assert (Hle : f tmin_unc ≤ tmax' ↔ tmin_unc ≤ tmax)
    by (pose proof (lt_shift_iff p tmax' tmin_unc ltac:(lia)) as H; rewrite Hmax in H; lia).
  destruct (decide (tmin_unc ≤ tmax)); destruct (decide (f tmin_unc ≤ tmax')); try tauto;
    [|split; [constructor|reflexivity]].
  apply (res_lift_bind (Forall2 (λ vw vw', vw' = (vw.1, f vw.2)))).
  { apply res_lift_lift. destruct upper.
    - rewrite Hreg. destruct (TState.read_sreg_indirect ts TTBR1_EL1) as [vws|]; cbn;
        [apply Forall2_map_r|reflexivity].
    - cbn. constructor; [|constructor]. cbn. rewrite shift_zero by lia. reflexivity. }
  intros vws vws' Hvws.
  apply (res_lift_bind (λ vw vw', vw' = (vw.1, f vw.2))); [apply res_lift_mchoosel, Hvws|].
  intros [ttbr vttbr] vw' ->. cbn [fst snd].
  replace (f tmin_unc ⊔ f vttbr) with (f (tmin_unc ⊔ vttbr))
    by (unfold join, join_nat; apply shift_max).
  apply (res_lift_bind (λ ptes ptes', ptes' = map_ptes p ptes)).
  { apply res_lift_lift. rewrite (read_all_pte_map _ _ tmax tmax' Hmax Hb).
    destruct (Memory.read_all_pte _ imem mem _ tmax); reflexivity. }
  intros ptes ptes' ->. apply res_lift_mchoosel.
  rewrite filter_map_ptes.
  induction (filter _ ptes) as [|[pte vpte] ptes'' IH]; cbn [map map_ptes fst snd];
    constructor; [|exact IH].
  replace (f (tmin_unc ⊔ vttbr) ⊔ f vpte) with (f (tmin_unc ⊔ vttbr ⊔ vpte))
    by (unfold join, join_nat; apply shift_max).
  apply res_rel_make, Hmax.
Qed.

Lemma tlb_lookup_shape ts asid ttbr0 tmin_ok tmin_unc tmax mem0 :
  TState.tlb_lookup tid imem mem0 ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax =
  match TState.tlb ts with
  | Some c => Exec.merge (TLB.lookup tid imem mem0 c ifetch upper vpn tmin_ok tmin_unc tmax asid)
      (VMRootLookupReplay.root_lookup imem mem0 ts upper vpn ttbr0 tmin_unc tmax)
  | None => mthrow "TLB lookup, but translation disabled by SCTLR_EL1"
  end.
Proof. unfold TState.tlb_lookup. destruct (TState.tlb ts); reflexivity. Qed.

(** The thread-level lookup. *)
Theorem tlb_lookup_map ts ts' asid ttbr0 tmin_ok tmin_unc tmax tmax' :
  TState.tlb ts' = tlb_map f <$> TState.tlb ts →
  TState.read_sreg_indirect ts' TTBR1_EL1 =
    map (λ vw, (vw.1, f vw.2)) <$> TState.read_sreg_indirect ts TTBR1_EL1 →
  unshift p tmax' = tmax → tmax' ≤ S (length mem) →
  res_lift (res_rel p)
    (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax)
    (TState.tlb_lookup tid imem mem' ts' ifetch upper vpn asid ttbr0 (f tmin_ok) (f tmin_unc)
      tmax').
Proof.
  intros Htlb Hreg Hmax Hb. rewrite !tlb_lookup_shape, Htlb.
  destruct (TState.tlb ts) as [c|]; cbn [fmap option_fmap option_map];
    [|split; [constructor|reflexivity]].
  destruct (lookup_map c tmin_ok tmin_unc tmax tmax' asid Hmax Hb) as [H1 H2].
  destruct (root_lookup_map ts ts' ttbr0 tmin_unc tmax tmax' Hreg Hmax Hb) as [H3 H4].
  unfold Exec.merge. split; cbn [Exec.results Exec.errors].
  - apply Forall2_app; assumption.
  - rewrite H2, H4. reflexivity.
Qed.

End Lookup.

(** * Merging refines

    Results related by [res_rel p] merge at least as finely in the longer
    history: two results with [tend] [p - 1] and [p] there may correspond to
    two results with [tend] [p - 1] in the shorter one. Every merged result of
    the shorter history is matched by a merged result of the longer one of the
    same leaf class whose [tstart] is not later; the walk may differ. *)

Definition res_wrel (p : nat) (x y : TLB.Result.t) : Prop :=
  list.last (TLB.Result.path y) = list.last (TLB.Result.path x) ∧
  map TLB.Result.table_attrs (removelast (TLB.Result.path y)) =
    map TLB.Result.table_attrs (removelast (TLB.Result.path x)) ∧
  unshift p (TLB.Result.tend y) = TLB.Result.tend x ∧
  TLB.Result.inv_time y = shift p <$> TLB.Result.inv_time x ∧
  TLB.Result.tstart y ≤ shift p (TLB.Result.tstart x).

Local Notation gk := VMCacheSim.gk.
Local Notation key := VMCacheSim.key.

Lemma fold_gk_attained k l : ∀ o x, foldl (gk k) o l = Some x →
  (∃ a, o = Some a ∧ TLB.Result.tstart x = TLB.Result.tstart a) ∨
  (∃ z, z ∈ l ∧ key z = k ∧ TLB.Result.tstart x = TLB.Result.tstart z).
Proof.
  induction l as [|r l IH]; intros o x H; cbn [foldl] in H.
  - left. exists x. auto.
  - destruct (IH _ _ H) as [[a' [Ha' Hx]]|[z [Hz [Hk Hx]]]];
      [|right; exists z; split; [right; exact Hz|auto]].
    unfold gk in Ha'. destruct (decide (key r = k)) as [Hr|Hr].
    + injection Ha' as <-. destruct o as [a|].
      * rewrite VMCacheSim.comb_tstart in Hx.
        destruct (decide (TLB.Result.tstart a ≤ TLB.Result.tstart r)).
        -- left. exists a. split; [reflexivity|lia].
        -- right. exists r. split; [left|split; [exact Hr|lia]].
      * right. exists r. split; [left|auto].
    + left. exists a'. auto.
Qed.

Lemma fold_gk_le k l : ∀ o y, foldl (gk k) o l = Some y →
  (∀ a, o = Some a → TLB.Result.tstart y ≤ TLB.Result.tstart a) ∧
  (∀ z, z ∈ l → key z = k → TLB.Result.tstart y ≤ TLB.Result.tstart z).
Proof.
  induction l as [|r l IH]; intros o y H; cbn [foldl] in H.
  - split; [intros a ->; injection H as ->; lia|intros z Hz; inversion Hz].
  - destruct (IH _ _ H) as [Ho Hl]. unfold gk in Ho. split.
    + intros a ->. destruct (decide (key r = k)).
      * specialize (Ho _ eq_refl). rewrite VMCacheSim.comb_tstart in Ho. lia.
      * apply Ho. reflexivity.
    + intros z Hz Hk. apply elem_of_cons in Hz as [->|Hz]; [|apply Hl; assumption].
      rewrite decide_True in Ho by exact Hk. specialize (Ho _ eq_refl).
      destruct o as [a|]; [rewrite VMCacheSim.comb_tstart in Ho|]; lia.
Qed.

Lemma fold_gk_some_stays k l a : ∃ y, foldl (gk k) (Some a) l = Some y.
Proof.
  revert a. induction l as [|r l IH]; intro a; [eauto|]. cbn [foldl]. unfold gk at 2.
  destruct (decide (key r = k)); apply IH.
Qed.

Lemma fold_gk_some k l o z : z ∈ l → key z = k → ∃ y, foldl (gk k) o l = Some y.
Proof.
  revert o. induction l as [|r l IH]; intros o Hz Hk; [inversion Hz|]. cbn [foldl].
  apply elem_of_cons in Hz as [->|Hz]; [|apply IH; assumption].
  unfold gk at 2. rewrite decide_True by exact Hk. apply fold_gk_some_stays.
Qed.

Lemma fold_gk_key k l y : foldl (gk k) None l = Some y → key y = k.
Proof.
  intro H. cut (VMCacheSim.keyed k (foldl (gk k) None l)); [intro Hk; apply Hk, H|].
  assert (H0 : VMCacheSim.keyed k None) by (intros a Ha; discriminate).
  revert H0. generalize (@None TLB.Result.t) as o. clear H.
  induction l as [|r l IH]; intros o Ho; [exact Ho|].
  cbn [foldl]. apply IH, VMCacheSim.gk_keyed, Ho.
Qed.

Lemma key_parts r r' : key r = key r' →
  list.last (TLB.Result.path r) = list.last (TLB.Result.path r') ∧
  map TLB.Result.table_attrs (removelast (TLB.Result.path r)) =
    map TLB.Result.table_attrs (removelast (TLB.Result.path r')) ∧
  TLB.Result.tend r = TLB.Result.tend r' ∧ TLB.Result.inv_time r = TLB.Result.inv_time r'.
Proof. unfold key. intro H. injection H. auto. Qed.

Theorem merge_match p la lb x : Forall2 (res_rel p) la lb →
  x ∈ TLB.Result.merge la → ∃ y, y ∈ TLB.Result.merge lb ∧ res_wrel p x y.
Proof.
  intros Hrel Hin. unfold TLB.Result.merge in *.
  apply (VMCacheSim.elem_find_key _ _ (VMCacheSim.merge_nodup la [] (NoDup_nil_2))) in Hin.
  rewrite VMCacheSim.find_merge in Hin. cbn [VMCacheSim.find_key] in Hin.
  destruct (fold_gk_attained _ _ _ _ Hin) as [[a [Ha _]]|[z [Hz [Hkz Hxz]]]]; [discriminate|].
  apply list_elem_of_lookup in Hz as [i Hi].
  destruct (Forall2_lookup_l _ _ _ _ _ Hrel Hi) as [bz [Hbi Hzb]].
  destruct (fold_gk_some (key bz) lb None bz (list_elem_of_lookup_2 _ _ _ Hbi) eq_refl)
    as [y Hy].
  exists y. split.
  - apply (VMCacheSim.find_key_elem (key bz)). rewrite VMCacheSim.find_merge. exact Hy.
  - pose proof (fold_gk_key _ _ _ Hy) as Hky.
    destruct (key_parts _ _ Hky) as (Hl1 & Ha1 & He1 & Hi1).
    destruct (key_parts _ _ Hkz) as (Hl2 & Ha2 & He2 & Hi2).
    destruct Hzb as (Ht & Hp & Hs & He & Hinv).
    destruct (fold_gk_le _ _ _ _ Hy) as [_ Hle].
    specialize (Hle bz (list_elem_of_lookup_2 _ _ _ Hbi) eq_refl).
    repeat split.
    + rewrite Hl1, Hp, Hl2. reflexivity.
    + rewrite Ha1, Hp, Ha2. reflexivity.
    + rewrite He1, He, He2. reflexivity.
    + rewrite Hi1, Hinv, Hi2. reflexivity.
    + rewrite Hxz, <- Hs. exact Hle.
Qed.

(** * Exact merging within one lookup

    Within one lookup bounded by [T] in the longer history, a result [tend]
    is either the bound or below the predecessor of a shifted timestamp, so
    [tend] is [p - 1] only when [T] is: [unshift p] is injective on the
    [tend] values of one lookup, and merging commutes with [res_rel]. *)

Definition good_cap (p T c : nat) : Prop := c = pred p → T = pred p.

Definition good (p T : nat) (y : TLB.Result.t) : Prop :=
  TLB.Result.tend y ≤ T ∧ good_cap p T (TLB.Result.tend y).

Lemma good_cap_pred p T t : 0 < p → 0 < t → good_cap p T (pred (shift p t)).
Proof. intros Hp Ht H. exfalso. shift_cases. Qed.

Lemma good_cap_min p T c d : good_cap p T c → good_cap p T d → good_cap p T (c `min` d).
Proof. unfold good_cap. lia. Qed.

(** TLBI events of an entry have positive timestamps. *)
Definition tpos (et : TLB.Entry.event * nat) : Prop :=
  match et.1 with TLB.Entry.Tlbi _ => 0 < et.2 | TLB.Entry.Load => True end.

Lemma get_results_from_events_good p (Hp : 0 < p) T tid ifetch ttbr path events :
  Forall tpos events →
  ∀ tmin c inv, c ≤ T → good_cap p T c →
  Forall (good p T)
    (TLB.get_results_from_events tid ifetch ttbr path (map_evs (shift p) events) tmin c inv).
Proof.
  induction events as [events IH] using (induction_ltof1 _ (@length _)).
  unfold ltof in IH. intro Hpos.
  destruct events as [|[ev t] events]; intros tmin c inv Hc Hg;
    cbn [TLB.get_results_from_events map_evs map fst snd];
    (destruct (decide (c < tmin)); [constructor|]); [constructor|].
  inversion Hpos as [|? ? Ht Hpos1]. clear Hpos. rename Hpos1 into Hpos.
  destruct ev as [|tidt].
  - destruct (decide (c < shift p t)); [apply (IH events ltac:(cbn; lia)); assumption|].
    destruct (decide (shift p t < tmin)); [constructor; [split; assumption|constructor]|].
    destruct events as [|[[|tidt'] t'] events']; cbn [map_evs map fst snd].
    + constructor; [split; assumption|apply (IH [] ltac:(cbn; lia)); assumption].
    + constructor; [split; assumption|].
      apply (IH ((TLB.Entry.Load, t') :: events') ltac:(cbn; lia)); assumption.
    + pose proof Hpos as Hpos0. inversion Hpos as [|? ? Ht' Hpos'].
      case_decide.
      * pose proof (IH events' ltac:(cbn; lia) Hpos' tmin c inv Hc Hg) as Hmerge.
        pose proof (IH ((TLB.Entry.Tlbi tidt', t') :: events')
          ltac:(cbn; lia) Hpos0 tmin c inv Hc Hg) as Hnormal.
        destruct events' as [|[[|tidt''] t''] events'']; cbn [map_evs map fst snd].
        2: exact Hmerge.
        all: constructor; [split; assumption|exact Hnormal].
      * constructor; [split; assumption|].
        apply (IH ((TLB.Entry.Tlbi tidt', t') :: events') ltac:(cbn; lia));
          [constructor; assumption|assumption|assumption].
  - unfold tpos in Ht. cbn in Ht.
    apply (IH events ltac:(cbn; lia)); [exact Hpos|lia|].
    apply good_cap_min; [exact Hg|apply good_cap_pred; assumption].
Qed.

Lemma uncacheable_aux_good p (Hp : 0 < p) T lvl tmin results ptes :
  Forall (good p T) results →
  ∀ c, good_cap p T c →
  Forall (good p T)
    (TLB.get_results_from_events_uncacheable_aux results (map_ptes p ptes) tmin c lvl).
Proof.
  intro Hres. revert ptes. induction Hres as [|r rs Hr Hrs IH]; intros ptes c Hc; [constructor|].
  rewrite unc_cons.
  revert c Hc. induction ptes as [|[pte tpte] ptes IHp]; intros c Hc;
    cbn [unc_inner map_ptes map fst snd]; [constructor|].
  destruct (decide (TLB.Result.tend r `min` c < tmin)); [constructor|].
  assert (Hrest : Forall (good p T)
    (if decide (shift p tpte ≤ TLB.Result.tstart r)
     then TLB.get_results_from_events_uncacheable_aux rs
       ((pte, shift p tpte) :: map_ptes p ptes) tmin c lvl
     else unc_inner r rs tmin lvl (map_ptes p ptes) (pred (shift p tpte)))).
  { case_decide.
    - apply (IH ((pte, tpte) :: ptes) c Hc).
    - apply IHp. intro Hq. exfalso. shift_cases. }
  destruct (decide (is_tlb_fillable lvl pte)); [exact Hrest|].
  constructor; [|exact Hrest].
  destruct Hr as [Hr1 Hr2]. destruct r. cbn -[Nat.min] in *.
  unfold good. change (TLB.Result.tend (setv TLB.Result.tend ?x ?r)) with x.
  split; [lia|]. apply good_cap_min; assumption.
Qed.

Lemma good_inj p T y1 y2 : 0 < p → good p T y1 → good p T y2 →
  unshift p (TLB.Result.tend y1) = unshift p (TLB.Result.tend y2) →
  TLB.Result.tend y1 = TLB.Result.tend y2.
Proof.
  intros Hp [H1 G1] [H2 G2]. unfold good_cap in *.
  destruct (decide (TLB.Result.tend y1 = pred p)) as [E1|E1];
    [specialize (G1 E1)|];
  (destruct (decide (TLB.Result.tend y2 = pred p)) as [E2|E2]; [specialize (G2 E2)|]);
  intro H; unfold unshift in H; repeat case_decide; lia.
Qed.

Lemma shift_min p a b : shift p (a `min` b) = shift p a `min` shift p b.
Proof. shift_cases. Qed.

Lemma res_rel_key p T a b r r' : 0 < p → res_rel p a b → res_rel p r r' →
  good p T b → good p T r' → key b = key r' ↔ key a = key r.
Proof.
  intros Hp (_ & Hpa & _ & Hea & Hia) (_ & Hpr & _ & Her & Hir) Gb Gr.
  unfold key. rewrite Hpa, Hpr, Hia, Hir. split; intro H; injection H as H1 H2 H3 H4.
  - f_equal; [f_equal; [f_equal; [exact H1|exact H2]|]|].
    + rewrite <- Hea, <- Her, H3. reflexivity.
    + destruct (TLB.Result.inv_time a), (TLB.Result.inv_time r); cbn in H4;
        try discriminate; [injection H4 as H4; apply shift_inj in H4; subst|]; reflexivity.
  - f_equal; [f_equal; [f_equal; [exact H1|exact H2]|]|].
    + apply (good_inj p T); [exact Hp|exact Gb|exact Gr|]. rewrite Hea, Her. exact H3.
    + rewrite H4. reflexivity.
Qed.

Lemma comb_rel p a b r r' : res_rel p a b → res_rel p r r' →
  res_rel p (VMCacheSim.comb a r) (VMCacheSim.comb b r').
Proof.
  intros Ha Hr. pose proof Ha as (Hta & Hpa & Hsa & Hea & Hia).
  pose proof Hr as (Htr & Hpr & Hsr & Her & Hir).
  unfold VMCacheSim.comb. unfold TLB.Result.walk. rewrite Hta, Hpa, Htr, Hpr.
  destruct (TLB.Result.walk_lt _ _); unfold res_rel;
    repeat change (TLB.Result.ttbr (setv TLB.Result.tstart ?x ?y)) with (TLB.Result.ttbr y);
    repeat change (TLB.Result.path (setv TLB.Result.tstart ?x ?y)) with (TLB.Result.path y);
    repeat change (TLB.Result.tstart (setv TLB.Result.tstart ?x ?y)) with x;
    repeat change (TLB.Result.tend (setv TLB.Result.tstart ?x ?y)) with (TLB.Result.tend y);
    repeat change (TLB.Result.inv_time (setv TLB.Result.tstart ?x ?y)) with
      (TLB.Result.inv_time y);
    (split; [assumption|]); (split; [assumption|]);
    (split; [rewrite Hsa, Hsr; symmetry; apply shift_min|]); split; assumption.
Qed.

Lemma good_comb p T a r : good p T a → VMCacheSim.key a = VMCacheSim.key r →
  good p T (VMCacheSim.comb a r).
Proof. intros Ga Hk. unfold good. rewrite VMCacheSim.comb_tend by exact Hk. exact Ga. Qed.

Lemma merge_into_rel p T (Hp : 0 < p) r r' acc acc' :
  Forall2 (res_rel p) acc acc' → Forall (good p T) acc' → res_rel p r r' → good p T r' →
  Forall2 (res_rel p) (TLB.Result.merge_into r acc) (TLB.Result.merge_into r' acc') ∧
  Forall (good p T) (TLB.Result.merge_into r' acc').
Proof.
  intros Hacc Gacc Hr Gr. induction Hacc as [|a b acc acc' Hab Hacc IH].
  - split; cbn; constructor; auto.
  - inversion Gacc as [|? ? Gb Gacc']. subst.
    rewrite !VMCacheSim.merge_into_cons.
    pose proof (res_rel_key p T a b r r' Hp Hab Hr Gb Gr) as Hk.
    pose proof (VMCacheSim.mergeable_key b r') as Mk1.
    pose proof (VMCacheSim.mergeable_key a r) as Mk2.
    destruct (decide (TLB.Result.mergeable b r')) as [Hm'|Hm'];
      destruct (decide (TLB.Result.mergeable a r)) as [Hm|Hm]; try tauto.
    + split; constructor; [apply comb_rel; assumption|assumption| |assumption].
      apply good_comb; [exact Gb|apply Mk1, Hm'].
    + destruct (IH Gacc') as [H1 H2].
      split; constructor; [exact Hab|exact H1|exact Gb|exact H2].
Qed.

Theorem merge_rel p T (Hp : 0 < p) la lb :
  Forall2 (res_rel p) la lb → Forall (good p T) lb →
  Forall2 (res_rel p) (TLB.Result.merge la) (TLB.Result.merge lb).
Proof.
  intros Hl Gl. unfold TLB.Result.merge.
  cut (∀ acc acc', Forall2 (res_rel p) acc acc' → Forall (good p T) acc' →
    Forall2 (res_rel p) (foldl (λ acc r, TLB.Result.merge_into r acc) acc la)
      (foldl (λ acc r, TLB.Result.merge_into r acc) acc' lb));
    [intro H; apply H; constructor|].
  induction Hl as [|x y la lb Hxy Hl IH]; intros acc acc' Hacc Gacc; [exact Hacc|].
  inversion Gl as [|? ? Gy Gl']. subst. cbn [foldl].
  destruct (merge_into_rel p T Hp x y acc acc' Hacc Gacc Hxy Gy) as [H1 H2].
  apply IH; assumption.
Qed.

(** ** The longer lookup is [good] *)

(** Entry TLBI events have positive times: they are timestamps of history
    events. Loads may happen at time 0. *)
Definition pos_cache (c : TLB.t) : Prop :=
  ∀ ctxt entry evs, (entry, evs) ∈ TLB.VATLB.get ctxt (TLB.vatlb c) →
    Forall tpos evs.

Lemma pos_get_fes c ctxts fe evs : pos_cache c → (fe, evs) ∈ TLB.get_fes c ctxts →
  Forall tpos evs.
Proof.
  intros Hc Hin. unfold TLB.get_fes in Hin.
  apply list_elem_of_In, in_concat in Hin as [rows [Hrows Hin]].
  apply in_map_iff in Hrows as [ctxt [<- _]]. apply list_elem_of_In in Hin.
  unfold TLB.VATLB.get_fe in Hin. apply list_elem_of_fmap in Hin as [[entry evs'] [Heq Hin]].
  injection Heq as _ <-. eapply Hc. exact Hin.
Qed.

Lemma Forall_results_bind {A B} (P : B → Prop) (x : Exec.res string A) (k : A → Exec.res string B) :
  (∀ a, a ∈ Exec.results x → Forall P (Exec.results (k a))) →
  Forall P (Exec.results (x ≫= k)).
Proof.
  intro H. rewrite VMCacheSim.res_bind_results.
  induction (Exec.results x) as [|a l IH]; cbn; [constructor|].
  apply Forall_app. split; [apply H; left|apply IH; intros; apply H; right; assumption].
Qed.

Section Good.
Context (tid : nat) (imem : memoryMap) (l r : Memory.t) (tlbi : TLBI.t) (rc k : nat)
  (ifetch upper : bool) (vpn : pn).
Local Notation p := (S (length r)).
Local Notation f := (shift (S (length r))).
Local Notation mem := (l ++ r).
Local Notation mem' := (l ++ Ev.Tlbi tlbi rc k :: r).

Lemma good_cap_top T : good_cap p T T.
Proof. intro H. exact H. Qed.

Lemma FE_good fe events tmin_ok tmin_unc tmax tmax' : Forall tpos events →
  unshift p tmax' = tmax → tmax' ≤ S (length mem) →
  match TLB.get_result_from_FE tid imem mem' ifetch vpn fe (map_evs f events)
      (f tmin_ok) (f tmin_unc) tmax' with
  | Ok res => Forall (good p tmax') res
  | Error _ => True
  end.
Proof.
  intros Hpos Hmax Hb. unfold TLB.get_result_from_FE. case_decide.
  - unfold TLB.get_result_from_table_FE.
    destruct (decide (tmax' < f tmin_unc)); [cbn; constructor|].
    destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|cbn; constructor].
    pose proof (get_results_from_events_good p ltac:(lia) tmax' tid ifetch (TLB.FE.ttbr fe)
      (TLB.FE.ptes fe) events Hpos (f tmin_unc) tmax' None (le_n _) (good_cap_top _)) as Hg.
    destruct (TLB.get_results_from_events _ _ _ _ _ _ _ _) as [|x xs]; [cbn; constructor|].
    rewrite (read_all_pte_map imem l r tlbi rc k _ tmin_unc tmax tmax' Hmax Hb).
    destruct (Memory.read_all_pte _ imem mem tmin_unc tmax) as [ptes|]; cbn; [|exact I].
    exact (uncacheable_aux_good p ltac:(lia) tmax' lvl (f tmin_unc) (x :: xs) ptes Hg
      tmax' (good_cap_top _)).
  - unfold TLB.get_result_from_leaf_FE. cbn.
    destruct (decide (tmax' < f tmin_ok)); [constructor|].
    exact (get_results_from_events_good p ltac:(lia) tmax' tid ifetch _ _ events Hpos
      (f tmin_ok) tmax' None (le_n _) (good_cap_top _)).
Qed.

Lemma lookup_good c tmin_ok tmin_unc tmax tmax' asid : pos_cache c →
  unshift p tmax' = tmax → tmax' ≤ S (length mem) →
  Forall (good p tmax') (Exec.results
    (TLB.lookup tid imem mem' (tlb_map f c) ifetch upper vpn (f tmin_ok) (f tmin_unc)
      tmax' asid)).
Proof.
  intros Hc Hmax Hb. rewrite VMCacheSim.lookup_shape. apply Forall_results_bind.
  intros [fe evs'] Hin. rewrite VMCacheSim.mchoosel_results, get_fes_map in Hin.
  apply list_elem_of_fmap in Hin as [[fe0 evs] [Heq Hin]]. injection Heq as -> ->.
  cbn [fst snd VMCacheSim.fe_res]. apply Forall_results_bind. intros res Hres.
  rewrite VMCacheSim.mchoosel_results.
  pose proof (FE_good fe0 evs tmin_ok tmin_unc tmax tmax' (pos_get_fes _ _ _ _ Hc Hin)
    Hmax Hb) as Hg.
  destruct (TLB.get_result_from_FE _ _ _ _ _ _ _ _ _ _) as [l0|e]; cbn in Hres.
  - apply list_elem_of_singleton in Hres as ->. exact Hg.
  - inversion Hres.
Qed.

Lemma root_lookup_good ts ttbr0 tmin tmax' :
  Forall (good p tmax') (Exec.results
    (VMRootLookupReplay.root_lookup imem mem' ts upper vpn ttbr0 tmin tmax')).
Proof.
  unfold VMRootLookupReplay.root_lookup. destruct (decide (tmin ≤ tmax')); [|constructor].
  apply Forall_results_bind. intros ttbrs _.
  apply Forall_results_bind. intros [ttbr vttbr] _.
  apply Forall_results_bind. intros ptes _.
  rewrite VMCacheSim.mchoosel_results. apply Forall_forall. intros y Hy.
  apply list_elem_of_In, list_elem_of_fmap in Hy as [[pte vpte] [-> _]].
  split; [cbn; lia|apply good_cap_top].
Qed.

(** Merged lookup alternatives of the shorter and the longer history are
    related one to one. *)
Theorem tlb_lookup_merge_map ts ts' asid ttbr0 tmin_ok tmin_unc tmax tmax' :
  TState.tlb ts' = tlb_map f <$> TState.tlb ts →
  (∀ c, TState.tlb ts = Some c → pos_cache c) →
  TState.read_sreg_indirect ts' TTBR1_EL1 =
    map (λ vw, (vw.1, f vw.2)) <$> TState.read_sreg_indirect ts TTBR1_EL1 →
  unshift p tmax' = tmax → tmax' ≤ S (length mem) →
  Forall2 (res_rel p)
    (TLB.Result.merge (Exec.results
      (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax)))
    (TLB.Result.merge (Exec.results
      (TState.tlb_lookup tid imem mem' ts' ifetch upper vpn asid ttbr0 (f tmin_ok)
        (f tmin_unc) tmax'))) ∧
  Exec.errors (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) =
  Exec.errors (TState.tlb_lookup tid imem mem' ts' ifetch upper vpn asid ttbr0 (f tmin_ok)
    (f tmin_unc) tmax').
Proof.
  intros Htlb Hpos Hreg Hmax Hb.
  destruct (tlb_lookup_map tid imem l r tlbi rc k ifetch upper vpn ts ts' asid ttbr0 tmin_ok
    tmin_unc tmax tmax' Htlb Hreg Hmax Hb) as [Hrel Herr].
  split; [|exact Herr].
  apply (merge_rel p tmax'); [lia|exact Hrel|].
  rewrite tlb_lookup_shape, Htlb.
  destruct (TState.tlb ts) as [c|] eqn:Hc; cbn [fmap option_fmap option_map]; [|constructor].
  unfold Exec.merge. cbn [Exec.results]. apply Forall_app. split.
  - apply (lookup_good c tmin_ok tmin_unc tmax tmax' asid); [apply Hpos; reflexivity|exact Hmax|
      exact Hb].
  - apply root_lookup_good.
Qed.

End Good.

(** * Thread states and instruction states

    A thread not affected by the inserted event has all its timestamps
    shifted: [ts_map f]. Translation results stored in the instruction state
    come from lookups and are related by [iis_rel]: [trans_end] only up to
    [unshift p], as [Result.tend]. *)

Definition vv_map {A} (f : nat → nat) (vv : A * nat) : A * nat := (vv.1, f vv.2).

Definition regs_map (f : nat → nat) (m : dmap reg (λ reg, reg_type reg * view)%type) :=
  dmap_map (λ _ vv, vv_map f vv) m.

Definition wsreg_map (f : nat → nat) (w : WSReg.t) : WSReg.t :=
  WSReg.make (WSReg.sreg w) (WSReg.val w) (f (WSReg.view w)).

Definition lev_map (f : nat → nat) (lev : LEv.t) : LEv.t :=
  match lev with
  | LEv.Cse t => LEv.Cse (f t)
  | LEv.Wsreg w => LEv.Wsreg (wsreg_map f w)
  end.

Definition fwd_map (f : nat → nat) (x : FwdItem.t) : FwdItem.t :=
  FwdItem.make (f (FwdItem.time x)) (f (FwdItem.view x)) (FwdItem.byte x)
    (f <$> FwdItem.xcl_view x).

Definition xcl_map (f : nat → nat) (x : XclItem.t) : XclItem.t :=
  XclItem.make (f (XclItem.time x)) (XclItem.addr x) (XclItem.size x) (f (XclItem.view x)).

Definition ts_map (f : nat → nat) (ts : TState.t) : TState.t :=
  TState.make (map f (TState.prom_wr ts)) (map f (TState.prom_tlbi ts))
    (regs_map f (TState.regs ts)) (map (lev_map f) (TState.levs ts))
    (fmap (M := gmap address) f (TState.coh ts))
    (fmap (M := gmap (bv 16 * bv 12)) f (TState.tcoh ts))
    (f (TState.vrd ts)) (f (TState.vwr ts)) (f (TState.vdmbst ts)) (f (TState.vdmb ts))
    (f (TState.vdsb ts)) (f (TState.vspec ts)) (f (TState.vcse ts))
    (f (TState.vtlbi_self ts)) (f (TState.vtlbi_other ts)) (f (TState.vmsr ts))
    (f (TState.vacq ts)) (f (TState.vrel ts))
    (fmap (M := gmap address) (fwd_map f) (TState.fwdb ts)) (xcl_map f <$> TState.xclb ts)
    (TState.dsb_epoch ts) (tlb_map f <$> TState.tlb ts).

Definition trs_rel (p : nat) (x y : IIS.TransRes.t) : Prop :=
  IIS.TransRes.trans_start y = shift p (IIS.TransRes.trans_start x) ∧
  unshift p (IIS.TransRes.trans_end y) = IIS.TransRes.trans_end x ∧
  IIS.TransRes.root y = IIS.TransRes.root x ∧
  IIS.TransRes.remaining y = IIS.TransRes.remaining x.

Definition option_rel {A B} (R : A → B → Prop) (x : option A) (y : option B) : Prop :=
  match x, y with
  | Some a, Some b => R a b
  | None, None => True
  | _, _ => False
  end.

Definition iis_rel (p : nat) (x y : IIS.t) : Prop :=
  IIS.strict y = shift p (IIS.strict x) ∧
  option_rel (trs_rel p) (IIS.trs x) (IIS.trs y) ∧
  IIS.inv_time y = fmap (M := option) (shift p) (IIS.inv_time x) ∧
  IIS.rmw_read y = fmap (M := option) (λ tb : nat * bool, (shift p tb.1, tb.2))
    (IIS.rmw_read x) ∧
  IIS.sreg_reads y = regs_map (shift p) (IIS.sreg_reads x).

Lemma iis_rel_init p : 0 < p → iis_rel p IIS.init IIS.init.
Proof.
  intro Hp. repeat split; cbn; try reflexivity.
  all: rewrite shift_zero by exact Hp; reflexivity.
Qed.

Lemma ts_map_tlb f ts : TState.tlb (ts_map f ts) = tlb_map f <$> TState.tlb ts.
Proof. reflexivity. Qed.

Lemma to_val_view_if_map f sr w :
  WSReg.to_val_view_if sr (wsreg_map f w) = vv_map f <$> WSReg.to_val_view_if sr w.
Proof.
  destruct w as [sreg val view]. unfold WSReg.to_val_view_if, wsreg_map. cbn.
  destruct (decide (sreg = sr)) as [<-|]; reflexivity.
Qed.

Lemma read_sreg_direct_lev_map f regs sr levs :
  TState.read_sreg_direct_lev (regs_map f regs) sr (map (lev_map f) levs) =
  vv_map f <$> TState.read_sreg_direct_lev regs sr levs.
Proof.
  induction levs as [|[t|w] levs IH]; cbn [map TState.read_sreg_direct_lev lev_map].
  - unfold regs_map. rewrite dmap_lookup_map. reflexivity.
  - exact IH.
  - rewrite to_val_view_if_map. destruct (WSReg.to_val_view_if sr w); [reflexivity|exact IH].
Qed.

Lemma read_sreg_indirect_lev_map f regs sr levs :
  TState.read_sreg_indirect_lev (regs_map f regs) sr (map (lev_map f) levs) =
  map (vv_map f) <$> TState.read_sreg_indirect_lev regs sr levs.
Proof.
  induction levs as [|[t|w] levs IH]; cbn [map TState.read_sreg_indirect_lev lev_map].
  - unfold regs_map. rewrite dmap_lookup_map.
    destruct (dmap_lookup sr regs) eqn:E; rewrite ?E; reflexivity.
  - rewrite read_sreg_direct_lev_map.
    destruct (TState.read_sreg_direct_lev regs sr levs); reflexivity.
  - rewrite IH, to_val_view_if_map.
    destruct (TState.read_sreg_indirect_lev regs sr levs); [|reflexivity]. cbn.
    destruct (WSReg.to_val_view_if sr w); reflexivity.
Qed.

Lemma ts_map_read_sreg_indirect f ts sr :
  TState.read_sreg_indirect (ts_map f ts) sr = map (vv_map f) <$> TState.read_sreg_indirect ts sr.
Proof. apply read_sreg_indirect_lev_map. Qed.

Lemma ts_map_read_sreg_direct f ts sr :
  TState.read_sreg_direct (ts_map f ts) sr = vv_map f <$> TState.read_sreg_direct ts sr.
Proof. apply read_sreg_direct_lev_map. Qed.

Lemma ts_map_pc f ts : TState.pc (ts_map f ts) = TState.pc ts.
Proof.
  unfold TState.pc. cbn [ts_map TState.regs]. unfold regs_map.
  rewrite dmap_lookup_map.
  destruct (dmap_lookup pc_reg (TState.regs ts)) eqn:E; rewrite ?E; reflexivity.
Qed.

Lemma ts_map_reg_map f ts : TState.reg_map (ts_map f ts) = TState.reg_map ts.
Proof.
  apply dmap_eq. intro key. unfold TState.reg_map.
  etransitivity; [apply dmap_lookup_map|]. symmetry.
  etransitivity; [apply dmap_lookup_map|]. symmetry.
  cbn [ts_map TState.regs]. unfold regs_map.
  pose proof (dmap_lookup_map (λ (k : reg) (vv : reg_type k * nat), vv_map f vv)
    (TState.regs ts) key) as Hm.
  rewrite Hm.
  destruct (dmap_lookup key (TState.regs ts)) as [vv|] eqn:E; rewrite ?E; [|reflexivity].
  cbn [fmap option_fmap option_map vv_map fst snd].
  case_bool_decide; [|reflexivity]. rewrite ts_map_read_sreg_direct.
  destruct (TState.read_sreg_direct ts key); reflexivity.
Qed.

Lemma ts_map_min_new_prom_view p ts :
  TState.min_new_prom_view (ts_map (shift p) ts) = shift p (TState.min_new_prom_view ts).
Proof. unfold TState.min_new_prom_view. cbn. unfold join, join_nat. rewrite !shift_max. reflexivity. Qed.

(** The thread state of a thread not affected by an inserted TLBI satisfies
    the hypotheses of [tlb_lookup_merge_map]. *)
(** ** Context synchronization of an unaffected thread *)

Lemma run_tlb_map f (upd upd' : stateT TLB.t (result string) ()) ts :
  natural f upd upd' →
  TState.run_tlb upd' (ts_map f ts) = ts_map f <$> TState.run_tlb upd ts.
Proof.
  intro Hn. unfold TState.run_tlb. cbn [ts_map TState.tlb].
  destruct (TState.tlb ts) as [c|]; cbn [fmap option_fmap option_map]; [|reflexivity].
  rewrite Hn. destruct (upd c) as [[c' []]|err]; reflexivity.
Qed.

Theorem cse_shifted tid imem l r tlbi rc k v ts : tid ≠ rc →
  TState.cse imem (l ++ Ev.Tlbi tlbi rc k :: r) tid (shift (S (length r)) v)
    (ts_map (shift (S (length r))) ts) =
  ts_map (shift (S (length r))) <$> TState.cse imem (l ++ r) tid v ts.
Proof.
  intro Hrc. unfold TState.cse.
  set (f := shift (S (length r))).
  set (pre := set TState.levs (LEv.Cse v ::.) (TState.update TState.vcse v ts)).
  assert (Hpre : set TState.levs (LEv.Cse (f v) ::.) (TState.update TState.vcse (f v)
      (ts_map f ts)) = ts_map f pre).
  { unfold pre, TState.update, set, ts_map. destruct ts.
    cbn -[shift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map].
    unfold f. rewrite <- shift_max. reflexivity. }
  rewrite Hpre. clear Hpre.
  match goal with |- (TState.run_tlb ?ub _ ≫= _) = _ <$> (TState.run_tlb ?ua _ ≫= _) =>
    assert (Hn : natural f ua ub); [|rewrite (run_tlb_map f ua ub pre Hn);
      destruct (TState.run_tlb ua pre); reflexivity] end.
  { apply natural_bind; [apply natural_ret|intros []].
    rewrite !ts_map_read_sreg_direct.
    replace (fst <$> (vv_map f <$> TState.read_sreg_direct pre TTBR1_EL1)) with
      (fst <$> TState.read_sreg_direct pre TTBR1_EL1)
      by (destruct (TState.read_sreg_direct pre TTBR1_EL1); reflexivity).
    destruct (TState.read_sreg_direct pre TTBR0_EL1) as [vv|]; [|intro c; reflexivity].
    intro c. apply (fill_cse_shifted tid imem l r tlbi rc k Hrc v vv.1). }
Qed.

Corollary ts_map_lookup_hyps p ts :
  TState.tlb (ts_map (shift p) ts) = tlb_map (shift p) <$> TState.tlb ts ∧
  TState.read_sreg_indirect (ts_map (shift p) ts) TTBR1_EL1 =
    map (λ vw, (vw.1, shift p vw.2)) <$> TState.read_sreg_indirect ts TTBR1_EL1.
Proof. split; [reflexivity|apply ts_map_read_sreg_indirect]. Qed.

(** * Positive TLBI times as a cache invariant *)

Lemma partial_alter_assoc_elem {K V} `{EqDecision K} (g : option V → option V) k
    (l : list (K * V)) kv :
  kv ∈ partial_alter_assoc g k l → kv ∈ l ∨
    (∃ v0 v, (k, v0) ∈ l ∧ g (Some v0) = Some v ∧ kv = (k, v)) ∨
    (∃ v, g None = Some v ∧ kv = (k, v)).
Proof.
  induction l as [|[k' v'] l IH]; cbn [partial_alter_assoc].
  - destruct (g None) eqn:E; [|intro H; inversion H].
    intro H. apply list_elem_of_singleton in H as ->. right; right. eauto.
  - case_decide as Hk.
    + subst k'. destruct (g (Some v')) eqn:E.
      * intro Hin. apply elem_of_cons in Hin as [->|Hin]; [|left; right; exact Hin].
        right; left. exists v', v. split; [left|auto].
      * intro Hin. left. right. exact Hin.
    + intro Hin. apply elem_of_cons in Hin as [->|Hin]; [left; left|].
      destruct (IH Hin) as [H'|[[v0 [v [H1 H2]]]|H']];
        [left; right; exact H'|right; left; exists v0, v; split; [right; exact H1|exact H2]|
         right; right; exact H'].
Qed.

Lemma rows_partial_alter g fe v ctxt entry evs :
  (entry, evs) ∈ TLB.VATLB.get ctxt (partial_alter g fe v) →
  (entry, evs) ∈ TLB.VATLB.get ctxt v ∨
  (∃ evs0, (entry, evs0) ∈ TLB.VATLB.get ctxt v ∧ g (Some evs0) = Some evs) ∨
  g None = Some evs.
Proof.
  destruct fe as [ctxt0 entry0].
  unfold partial_alter, TLB.VATLB.partial_alter_fe. cbn [TLB.FE.ctxt TLB.FE.entry projT1 projT2].
  destruct (decide (ctxt0 = ctxt)) as [<-|Hne].
  - rewrite VMCacheReplay.get_alter_entries_same. intro H.
    destruct (partial_alter_assoc_elem _ _ _ _ H) as [H'|[[v0 [v' [H1 [Hg Heq]]]]|[v' [Hg Heq]]]].
    + left. exact H'.
    + injection Heq as -> ->. right; left. eauto.
    + injection Heq as -> ->. right; right. exact Hg.
  - rewrite VMCacheReplay.get_alter_entries_other by exact Hne. left. exact H.
Qed.

Lemma rows_map_fe g v ctxt entry evs :
  (entry, evs) ∈ TLB.VATLB.get ctxt (TLB.VATLB.map_fe g v) →
  ∃ evs0, (entry, evs0) ∈ TLB.VATLB.get ctxt v ∧ evs = g (existT ctxt entry) evs0.
Proof.
  rewrite VMCacheReplay.get_map_fe. intro H.
  apply list_elem_of_fmap in H as [[entry0 evs0] [Heq H]]. injection Heq as -> ->.
  eauto.
Qed.

Definition pres {A} (run : stateT TLB.t (result string) A) : Prop :=
  ∀ c c' x, pos_cache c → run c = Ok (c', x) → pos_cache c'.

Lemma pres_ret {A} (x : A) : pres (mret x).
Proof. intros c c' y Hc H. injection H as <- _. exact Hc. Qed.

Lemma pres_bind {A B} (ra : stateT TLB.t (result string) A) (k : A → stateT TLB.t (result string) B) :
  pres ra → (∀ x, pres (k x)) → pres (ra ≫= k).
Proof.
  intros Ha Hk c c' y Hc H. unfold mbind, st_bind, result_bind in H.
  destruct (ra c) as [[c1 x]|err] eqn:E; [|discriminate].
  eapply Hk; [eapply Ha; eassumption|exact H].
Qed.

Lemma pres_fmap {A B} (g : A → B) (ra : stateT TLB.t (result string) A) :
  pres ra → pres (g <$> ra).
Proof.
  intros Ha c c' y Hc H. unfold fmap, st_fmap, result_fmap in H.
  destruct (ra c) as [[c1 x]|err] eqn:E; [|discriminate]. injection H as <- _.
  eapply Ha; eassumption.
Qed.

Lemma pres_mapM {A B} (g : A → stateT TLB.t (result string) B) l :
  (∀ x, pres (g x)) → pres (mapM g l).
Proof.
  intro Hg. induction l as [|x l IH]; cbn [mapM]; [apply pres_ret|].
  apply pres_bind; [apply Hg|intro]. apply pres_bind; [exact IH|intro; apply pres_ret].
Qed.

Lemma pres_get {A} (proj : TLB.t → A) : pres (mget proj).
Proof. intros c c' y Hc H. injection H as <- _. exact Hc. Qed.

Lemma pres_throw {A} (err : string) : pres (mthrow err : stateT TLB.t (result string) A).
Proof. intros c c' y Hc H. discriminate. Qed.

Lemma pres_lift {A} (r : result string A) : pres (mlift r).
Proof. intros c c' y Hc H. destruct r; cbn in H; [injection H as <- _; exact Hc|discriminate]. Qed.

Lemma pres_set_vatlb g : (∀ v, (∀ ctxt entry evs, (entry, evs) ∈ TLB.VATLB.get ctxt v →
    Forall tpos evs) → ∀ ctxt entry evs, (entry, evs) ∈ TLB.VATLB.get ctxt (g v) →
    Forall tpos evs) →
  pres (mset TLB.vatlb g).
Proof. intros Hg c c' y Hc H. injection H as <- _. intros ctxt entry evs. apply Hg, Hc. Qed.

Lemma pres_set_other {T} (proj : TLB.t → T) `{!Setter proj} g :
  (∀ c, TLB.vatlb (set proj g c) = TLB.vatlb c) → pres (mset proj g).
Proof.
  intros Hv c c' y Hc H. injection H as <- _. intros ctxt entry evs. rewrite Hv. apply Hc.
Qed.

Lemma lookup_assoc_elem {K V} `{EqDecision K} (k : K) (l : list (K * V)) v :
  lookup_assoc k l = Some v → (k, v) ∈ l.
Proof.
  induction l as [|[k' v'] l IH]; cbn; [discriminate|].
  case_decide; [intros [= <-]; subst; left|intro Hl; right; apply IH, Hl].
Qed.

Lemma lookup_fe_row (v : TLB.VATLB.t) fe evs : v !! fe = Some evs →
  (TLB.FE.entry fe, evs) ∈ TLB.VATLB.get (TLB.FE.ctxt fe) v.
Proof. destruct fe. apply lookup_assoc_elem. Qed.

Lemma pos_set_entry c fe l : pos_cache c → Forall tpos l →
  pos_cache (set TLB.vatlb (partial_alter (λ _, Some l) fe) c).
Proof.
  intros Hc Hl ctxt entry evs H. cbn [set TLB.vatlb] in H.
  destruct (rows_partial_alter _ _ _ _ _ _ H) as [H'|[[evs0 [_ [= <-]]]|[= <-]]];
    [eapply Hc; exact H'|exact Hl|exact Hl].
Qed.

Lemma pres_fill_entry time fe : pres (TLB.fill_entry time fe).
Proof.
  intros c c' x Hc H. unfold TLB.fill_entry in H. cbn in H. unfold mget in H.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose in H. cbn -[TLB.VATLB.lookup_fe] in H.
  change (TLB.VATLB.lookup_fe fe (TLB.vatlb c)) with (TLB.vatlb c !! fe) in H.
  destruct (TLB.vatlb c !! fe) as [evs|] eqn:E; rewrite ?E in H;
    [destruct evs as [|[[|tid'] t] rest]|]; cbn in H.
  - injection H as <- _. apply pos_set_entry; [exact Hc|repeat constructor].
  - injection H as <- _. exact Hc.
  - injection H as <- _. apply pos_set_entry; [exact Hc|].
    constructor; [constructor|]. eapply Hc. apply lookup_fe_row, E.
  - assert (Hs : pos_cache (set TLB.vatlb (partial_alter (λ _, Some [(TLB.Entry.Load, time)]) fe) c))
      by (apply pos_set_entry; [exact Hc|repeat constructor]).
    destruct (decide (TLB.FE.is_table fe)); cbn in H; injection H as <- _; exact Hs.
Qed.

Lemma pres_guard_or (err : string) (P : Prop) `{Decision P} :
  pres (guard_or err P : stateT TLB.t (result string) P).
Proof. unfold guard_or. destruct (decide P); [apply pres_ret|apply pres_throw]. Qed.

Lemma pres_othrow {A} (err : string) (o : option A) :
  pres (othrow err o : stateT TLB.t (result string) A).
Proof. destruct o; [apply pres_ret|apply pres_throw]. Qed.

Lemma pres_ntc g : pres (mset TLB.next_table_cache g).
Proof. apply pres_set_other. reflexivity. Qed.

Lemma pres_roots g : pres (mset TLB.asid_roots g).
Proof. apply pres_set_other. reflexivity. Qed.

Lemma pres_rootsv rs : pres (msetv TLB.asid_roots rs).
Proof. apply pres_set_other. reflexivity. Qed.

Section PosFill.
Context (imem : memoryMap) (mem : Memory.t) (time : nat).

Lemma pres_fill_root roots : pres (TLB.fill_root imem mem time roots).
Proof.
  unfold TLB.fill_root. apply pres_fmap, pres_mapM. intros [[asid val_ttbr] upper].
  apply pres_bind; [apply pres_get|intro indexes].
  apply pres_fmap, pres_mapM. intro idx.
  destruct (Memory.read_word _ imem mem time) as [memval|]; [|apply pres_ret].
  destruct (decide (is_table 0%fin memval)); [|apply pres_ret].
  apply pres_bind; [apply pres_fill_entry|intros []; apply pres_ret].
Qed.

Lemma pres_fill_from_entry fe : pres (TLB.fill_from_entry imem mem time fe).
Proof.
  unfold TLB.fill_from_entry.
  apply pres_bind; [apply pres_guard_or|intros _].
  apply pres_bind; [apply pres_get|intro indexes].
  apply pres_bind; [apply pres_othrow|intro clvl].
  apply pres_fmap, pres_mapM. intro idx.
  destruct (Memory.read_word _ imem mem time) as [memval|]; [|apply pres_ret].
  destruct (decide (is_tlb_fillable clvl memval)); [|apply pres_ret].
  apply pres_bind; [apply pres_lift|intro next].
  apply pres_bind; [apply pres_fill_entry|intros []; [|apply pres_ret]].
  destruct (decide (is_table clvl memval)); apply pres_ret.
Qed.

Lemma pres_fill_from_entries entries : pres (TLB.fill_from_entries imem mem time entries).
Proof.
  unfold TLB.fill_from_entries, TLB.fill_from_entries_step.
  apply pres_bind; [apply pres_fmap, pres_mapM; intro; apply pres_fill_from_entry|intro e1].
  apply pres_bind; [apply pres_fmap, pres_mapM; intro; apply pres_fill_from_entry|intro e2].
  apply pres_bind; [apply pres_fmap, pres_mapM; intro; apply pres_fill_from_entry|intro e3].
  unfold guard_or'. apply pres_bind; [apply pres_guard_or|intros _; apply pres_ret].
Qed.

Lemma pres_fill_from_roots roots : pres (TLB.fill_from_roots imem mem time roots).
Proof.
  unfold TLB.fill_from_roots. apply pres_bind; [apply pres_fill_root|intro]. apply pres_fill_from_entries.
Qed.

Lemma pres_get_relevant asids page : pres (TLB.get_relevant_entries asids page).
Proof.
  unfold TLB.get_relevant_entries.
  apply pres_bind; [apply pres_get|intro]. apply pres_bind; [apply pres_get|intro]. apply pres_ret.
Qed.

Lemma pres_fill_write roots msg : pres (TLB.fill_write imem mem time roots msg).
Proof.
  unfold TLB.fill_write.
  apply pres_bind; [apply pres_guard_or|intros _].
  apply pres_bind; [apply pres_fill_root|intro].
  apply pres_bind; [apply pres_get_relevant|intro]. apply pres_fill_from_entries.
Qed.

Lemma tpos_invalidate tid evs : 0 < time → Forall tpos evs →
  Forall tpos (if evs is [] then [] else (TLB.Entry.Tlbi tid, time) :: evs).
Proof. intros Ht Hevs. destruct evs; [constructor|]. constructor; [exact Ht|exact Hevs]. Qed.

Lemma pres_fill_tlbi roots tlbi : 0 < time → pres (TLB.fill_tlbi imem mem time roots tlbi).
Proof.
  intro Ht. unfold TLB.fill_tlbi. destruct (TLBI.last tlbi).
  - apply pres_bind; [apply pres_get|intro v0].
    apply pres_bind; [apply pres_get|intro entries].
    apply pres_bind; [|intro; apply pres_fill_from_entries].
    apply pres_fmap, pres_mapM. intro entry.
    apply pres_bind; [|intros _; apply pres_get_relevant].
    apply pres_set_vatlb. intros v Hv ctxt entry' evs Hin.
    destruct (rows_partial_alter _ _ _ _ _ _ Hin) as [H'|[[evs0 [H0 Hg]]|Hg]].
    + eapply Hv. exact H'.
    + cbn in Hg. injection Hg as <-. apply tpos_invalidate; [exact Ht|eapply Hv; exact H0].
    + discriminate.
  - apply pres_bind; [|intros _; apply pres_fill_from_roots].
    apply pres_set_vatlb. intros v Hv ctxt entry evs Hin.
    apply rows_map_fe in Hin as [evs0 [H0 ->]].
    case_decide; [apply tpos_invalidate; [exact Ht|]|]; eapply Hv; exact H0.
Qed.

Lemma pres_fill_event tid roots ev : 0 < time → pres (TLB.fill_event tid imem mem time roots ev).
Proof.
  intro Ht. unfold TLB.fill_event. destruct ev; [apply pres_fill_write|].
  case_decide; [apply pres_fill_tlbi, Ht|apply pres_ret].
Qed.

End PosFill.

Lemma pres_fill_from_btw tid imem mem roots tmin tmax iter :
  pres (TLB.fill_from_btw tid imem mem roots tmin tmax iter).
Proof.
  revert roots iter. induction tmax as [|tmax IH]; intros roots iter; cbn [TLB.fill_from_btw].
  - case_decide; [apply pres_ret|apply pres_throw].
  - case_decide; [apply pres_ret|]. destruct iter as [|ev nmem]; [apply pres_throw|].
    apply pres_bind; [apply IH|intros _].
    apply pres_bind; [apply pres_fill_event; lia|intros _]. apply pres_fill_from_roots.
Qed.

Lemma pres_roll_back time : pres (TLB.roll_back time).
Proof.
  unfold TLB.roll_back. apply pres_set_vatlb. intros v Hv ctxt entry evs Hin.
  apply rows_map_fe in Hin as [evs0 [H0 ->]]. pose proof (Hv _ _ _ H0) as Hf.
  apply Forall_forall. intros x Hx.
  apply list_elem_of_In, list_elem_of_filter in Hx as [_ Hx].
  eapply Forall_forall; [exact Hf|apply list_elem_of_In; exact Hx].
Qed.

Lemma pres_fill_cse tid imem mem time ttbr0 ttbr1 :
  pres (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  unfold TLB.fill_cse. apply pres_bind; [apply pres_roll_back|intros _].
  apply pres_bind; [apply pres_rootsv|intros _]. unfold TLB.fill_from. apply pres_fill_from_btw.
Qed.

Lemma pres_fill_asid_root tid imem mem root time :
  pres (TLB.fill_asid_root tid imem mem root time).
Proof.
  unfold TLB.fill_asid_root. apply pres_bind; [apply pres_roll_back|intros _].
  apply pres_bind; [apply pres_roots|intros _].
  apply pres_bind; [apply pres_fill_from_roots|intros _].
  apply pres_bind; [apply pres_get|intro]. unfold TLB.fill_from. apply pres_fill_from_btw.
Qed.

Lemma pres_fill_promise tid imem mem ev : 0 < length mem → pres (TLB.fill_promise tid imem mem ev).
Proof.
  intro Hm. unfold TLB.fill_promise. apply pres_bind; [apply pres_get|intro].
  apply pres_fill_event, Hm.
Qed.

Lemma pos_cache_init_vatlb pp ntc roots ets : pos_cache (TLB.make TLB.VATLB.init pp ntc roots ets).
Proof.
  intros ctxt entry evs Hin. cbn [TLB.vatlb] in Hin.
  rewrite VMCacheLastTLBI.get_init in Hin. inversion Hin.
Qed.

Lemma pos_tlb_init tid imem iregs c : TLB.init tid imem iregs = Ok c → pos_cache c.
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
  eapply pres_fill_from_roots; [apply pos_cache_init_vatlb|exact Hrun].
Qed.

(** Thread states whose cache has positive TLBI times. *)
Definition ts_pos (ts : TState.t) : Prop := ∀ c, TState.tlb ts = Some c → pos_cache c.

Lemma run_tlb_pos upd ts ts' : pres upd → ts_pos ts → TState.run_tlb upd ts = Ok ts' → ts_pos ts'.
Proof.
  intros Hu Hts H. unfold TState.run_tlb in H.
  destruct (TState.tlb ts) as [c|] eqn:Hc.
  - unfold fmap, result_fmap, mbind, result_bind in H.
    destruct (upd c) as [[c' []]|err] eqn:E; [|discriminate].
    cbn in H. injection H as <-. intros c0 Hc0. cbn in Hc0. injection Hc0 as <-.
    eapply Hu; [apply Hts, Hc|exact E].
  - injection H as <-. exact Hts.
Qed.

Lemma process_event_pos tid imem mem ev ts ts' : 0 < length mem → ts_pos ts →
  TState.process_event tid imem mem ev ts = Ok ts' → ts_pos ts'.
Proof. intros Hm. apply run_tlb_pos, pres_fill_promise, Hm. Qed.

Lemma emit_promise_pos tid imem mem ev ts ts' : 0 < length mem → ts_pos ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → ts_pos ts'.
Proof.
  intros Hm Hts. unfold TState.emit_promise. apply process_event_pos; [exact Hm|].
  case_bool_decide; [destruct ev|]; exact Hts.
Qed.

Lemma cse_pos imem mem tid v ts ts' : ts_pos ts → TState.cse imem mem tid v ts = Ok ts' → ts_pos ts'.
Proof.
  intros Hts H. unfold TState.cse in H.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:E; [|discriminate]. cbn in H. injection H as <-.
  refine (run_tlb_pos _ _ _ _ _ E).
  - apply pres_bind; [apply pres_ret|intros _]. apply pres_bind; [apply pres_othrow|intro].
    apply pres_fill_cse.
  - exact Hts.
Qed.

(** ** Delivering a new event to an unaffected thread *)

Theorem emit_promise_shifted tid imem l r tlbi rc k ev ts :
  TState.emit_promise tid imem (ev :: l ++ Ev.Tlbi tlbi rc k :: r) ev
    (ts_map (shift (S (length r))) ts) =
  ts_map (shift (S (length r))) <$> TState.emit_promise tid imem (ev :: l ++ r) ev ts.
Proof.
  set (f := shift (S (length r))).
  assert (Hlen : length (ev :: l ++ Ev.Tlbi tlbi rc k :: r) = f (length (ev :: l ++ r))).
  { unfold f. rewrite shift_ge by (cbn; rewrite length_app; lia).
    cbn [length]. rewrite insert_length. reflexivity. }
  unfold TState.emit_promise. rewrite Hlen.
  set (pre := if bool_decide (Ev.tid ev = tid) then
      if ev is Ev.Msg _ then TState.promise_write (length (ev :: l ++ r)) ts
      else TState.promise_tlbi (length (ev :: l ++ r)) ts else ts).
  assert (Hpre : (if bool_decide (Ev.tid ev = tid) then
      if ev is Ev.Msg _ then TState.promise_write (f (length (ev :: l ++ r))) (ts_map f ts)
      else TState.promise_tlbi (f (length (ev :: l ++ r))) (ts_map f ts) else ts_map f ts) =
    ts_map f pre).
  { unfold pre. case_bool_decide; [destruct ev|]; reflexivity. }
  rewrite Hpre. unfold TState.process_event.
  rewrite (run_tlb_map f (TLB.fill_promise tid imem (ev :: l ++ r) ev)
    (TLB.fill_promise tid imem (ev :: l ++ Ev.Tlbi tlbi rc k :: r) ev) pre).
  - reflexivity.
  - exact (fill_promise_shifted tid imem l r tlbi rc k ev).
Qed.

End VMSwapLookup.
