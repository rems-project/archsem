(******************************************************************************)
(* Cached walks go through table descriptors                                  *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From SailStdpp Require Import ConcurrencyInterfaceBuiltinsV2.
From SailTinyArm Require Import System.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstFreshBroadcast
  PromiseFirstSailCurrent PromiseFirstVMExecutionCurrent PromiseFirstSailRead
  PromiseFirstSailVMViews PromiseFirstSailVMCacheSim
  PromiseFirstSailVMCache PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheIndex
  PromiseFirstSailVMCacheIndexed PromiseFirstSailVMCacheLastTLBI
  PromiseFirstSailVMLookup PromiseFirstSailVMRootLookup
  PromiseFirstSailVMDirect PromiseFirstSailVMNormalization PromiseFirstSailNoFuel
  PromiseFirstSailVMInstructionReplay PromiseFirstSailVMCreatingReplay
  PromiseFirstSailVMWalkSail PromiseFirstSailVMWalkReplay PromiseFirstSailVMCreatingWalk
  PromiseFirstSailVMWalkStart.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** Every entry allocated in the VA-indexed TLB walks through table
    descriptors: all its descriptors but the last are tables ([inv]). Entries
    are created only by [TLB.fill_root] (a single root descriptor) and by
    [TLB.fill_from_entry] (a table parent extended by one descriptor); every
    other cache operation only changes event histories. Hence every TLB
    lookup result is [VMWalkStart.shaped].

    [VMWalkStart.Shape] itself is not kept by every outcome from an arbitrary
    [VMViews.ok] state: an allocated table entry whose walk is not shaped
    but whose children are all fillable yields no lookup result, while a
    later write to its child table loads an unshaped child. The invariant of
    [VMWalkReplay.ShInvariant] is therefore the cache invariant [CShape],
    which implies [Shape]. *)

Module VMWalkShape.
Import VMPromising.
Local Notation action A := (stateT TLB.t (result string) A).

(** * Shaped entries *)

Definition fe_ok (fe : TLB.FE.t) : Prop :=
  ∀ i x, i < (TLB.FE.lvl fe : nat) → TLB.FE.ptes fe !! i = Some x → bv_extract 0 2 x = 3%bv.

Definition inv (c : TLB.t) : Prop := ∀ fe, is_Some (TLB.vatlb c !! fe) → fe_ok fe.

Lemma vec_to_list_ctrans {A n m} (H : n = m) (v : vec A n) :
  vec_to_list (ctrans H v) = vec_to_list v.
Proof.
  revert m H. induction v as [|x n v IH]; intros m H.
  - destruct m; [|discriminate]. rewrite ctrans_vec_vnil. reflexivity.
  - destruct m as [|m]; [discriminate|]. rewrite ctrans_vec_vcons. cbn. f_equal. apply IH.
Qed.

Lemma vec_last_lookup {A n} (v : vec A (S n)) : vec_to_list v !! n = Some (Vector.last v).
Proof.
  revert v. induction n as [|n IH]; intro v.
  - pattern v. apply vec_S_inv. intros x w. pattern w. apply vec_0_inv. reflexivity.
  - pattern v. apply vec_S_inv. intros x w. cbn. apply IH.
Qed.

Lemma ptes_length fe : length (TLB.FE.ptes fe) = S (TLB.FE.lvl fe).
Proof. unfold TLB.FE.ptes. apply length_vec_to_list. Qed.

Lemma append_ptes entry idx pte child : TLB.FE.append entry idx pte = Ok child →
  TLB.FE.ptes child = (TLB.FE.ptes entry ++ [pte])%list ∧ (TLB.FE.lvl child : nat) = S (TLB.FE.lvl entry).
Proof.
  unfold TLB.FE.append. destruct (inspect (child_lvl (TLB.FE.lvl entry))) as [[lvl|] Hlvl];
    [|discriminate]. intro Happend. injection Happend as <-. split.
  - unfold TLB.FE.ptes, TLB.FE.entry, TLB.Entry.append. cbn [projT2 TLB.Entry.ptes].
    rewrite vec_to_list_ctrans, vec_to_list_app. reflexivity.
  - pose proof (child_lvl_add_one _ _ Hlvl) as Hadd. cbn. lia.
Qed.

Lemma fe_ok_append entry idx pte child : fe_ok entry → TLB.FE.is_table entry →
  TLB.FE.append entry idx pte = Ok child → fe_ok child.
Proof.
  intros Hok Ht Ha. destruct (append_ptes _ _ _ _ Ha) as [Hp Hl].
  intros i x Hi Hx. rewrite Hp in Hx. rewrite Hl in Hi.
  pose proof (ptes_length entry) as Hlen.
  rewrite lookup_app_l in Hx by lia.
  destruct (decide (i < TLB.FE.lvl entry)) as [Hlt|Hge]; [exact (Hok i x Hlt Hx)|].
  assert (i = TLB.FE.lvl entry) by lia. subst i.
  unfold TLB.FE.ptes in Hx. rewrite vec_last_lookup in Hx. injection Hx as <-.
  destruct Ht as [_ Hb]. exact Hb.
Qed.

Lemma fe_ok_make0 upper idx asid ttbr pte : fe_ok (TLB.FE.make0 upper idx asid ttbr pte).
Proof. intros i x Hi. cbn in Hi. lia. Qed.

(** * Cache operations *)

Lemma inv_same c c' : TLB.vatlb c' = TLB.vatlb c → inv c → inv c'.
Proof. intros He H fe. rewrite He. apply H. Qed.

Lemma inv_fill_entry time fe : fe_ok fe → VMCacheLastTLBI.keeps inv (TLB.fill_entry time fe).
Proof.
  intros Hfe old new loaded Hold Hfill. unfold TLB.fill_entry in Hfill. cbn in Hfill. unfold mget in Hfill.
  unfold mbind, st_bind, fmap, st_fmap, mcall, st_call_MState, mret, st_ret,
    result_bind, result_ret, result_fmap, compose in Hfill. cbn in Hfill.
  destruct (TLB.vatlb old !! fe) as [events|] eqn:Hlookup; rewrite Hlookup in Hfill.
  - destruct events as [|[event stamp] rest].
    + unfold mret, result_ret in Hfill. injection Hfill as <- <-.
      intros q Hq. cbn [TLB.vatlb] in Hq. rewrite VMCacheRefill.lookup_set in Hq.
      destruct (decide (q = fe)) as [->|_]; [exact Hfe|exact (Hold q Hq)].
    + destruct event; unfold mret, result_ret in Hfill; injection Hfill as <- <-; [exact Hold|].
      intros q Hq. cbn [TLB.vatlb] in Hq. rewrite VMCacheRefill.lookup_set in Hq.
      destruct (decide (q = fe)) as [->|_]; [exact Hfe|exact (Hold q Hq)].
  - destruct (decide (TLB.FE.is_table fe));
      unfold mret, result_ret, mbind, result_bind in Hfill; cbn in Hfill;
      injection Hfill as <- <-.
    all: intros q Hq; cbn [TLB.vatlb TLB.next_table_cache] in Hq; rewrite VMCacheRefill.lookup_set in Hq;
      destruct (decide (q = fe)) as [->|_]; [exact Hfe|exact (Hold q Hq)].
Qed.

Lemma inv_map f : VMCacheLastTLBI.keeps inv (mset TLB.vatlb (TLB.VATLB.map_fe f)).
Proof.
  apply VMCacheLastTLBI.keeps_set. intros old Hold q Hq. cbn [TLB.vatlb] in Hq.
  rewrite VMCacheIndex.lookup_map_fe in Hq. apply fmap_is_Some in Hq. exact (Hold q Hq).
Qed.

Lemma inv_alter f fe : VMCacheLastTLBI.keeps inv (mset TLB.vatlb (alter f fe)).
Proof.
  apply VMCacheLastTLBI.keeps_set. intros old Hold q Hq. cbn [TLB.vatlb] in Hq.
  apply VMCacheIndexed.alter_domain in Hq. exact (Hold q Hq).
Qed.

Lemma inv_roots f : VMCacheLastTLBI.keeps inv (mset TLB.asid_roots f).
Proof. apply VMCacheLastTLBI.keeps_set. intros old Hold. exact Hold. Qed.

(** Cache operations keeping [inv] whose output satisfies [Q]. *)
Definition kp {A} (Q : A → Prop) (run : action A) :=
  ∀ old new v, inv old → run old = Ok (new, v) → inv new ∧ Q v.

Lemma kp_keeps {A} (run : action A) : VMCacheLastTLBI.keeps inv run → kp (λ _, True) run.
Proof. intros H old new v Hold Hrun. split; [exact (H old new v Hold Hrun)|exact I]. Qed.
Lemma keeps_kp {A} (Q : A → Prop) (run : action A) : kp Q run → VMCacheLastTLBI.keeps inv run.
Proof. intros H old new v Hold Hrun. exact (proj1 (H old new v Hold Hrun)). Qed.
Lemma kp_ret {A} (Q : A → Prop) (v : A) : Q v → kp Q (mret v).
Proof.
  intros Hv old new w Hold Hrun. change (@Ok string _ (old, v) = Ok (new, w)) in Hrun.
  injection Hrun as <- <-. split; assumption.
Qed.
Lemma kp_bind {A B} (Q : A → Prop) (R : B → Prop) (run : action A) (next : A → action B) :
  kp Q run → (∀ x, Q x → kp R (next x)) → kp R (run ≫= next).
Proof.
  intros Hfirst Hnext old new w Hold Hrun. unfold mbind, st_bind, result_bind in Hrun.
  destruct (run old) as [[mid x]|err] eqn:Hmid; [|discriminate].
  destruct (Hfirst old mid x Hold Hmid) as [Hm Hx]. exact (Hnext x Hx mid new w Hm Hrun).
Qed.
Lemma kp_fmap {A B} (Q : A → Prop) (R : B → Prop) (f : A → B) (run : action A) :
  kp Q run → (∀ x, Q x → R (f x)) → kp R (f <$> run).
Proof.
  intros Hfirst Hf old new w Hold Hrun. unfold fmap, st_fmap, result_fmap in Hrun.
  destruct (run old) as [[mid x]|err] eqn:Hmid; [|discriminate].
  injection Hrun as <- <-. destruct (Hfirst old mid x Hold Hmid) as [Hm Hx]. split; [exact Hm|apply Hf, Hx].
Qed.
Lemma kp_mapM {A B} (Q : B → Prop) (f : A → action B) xs :
  (∀ x, x ∈ xs → kp Q (f x)) → kp (Forall Q) (mapM f xs).
Proof.
  intro Hf. induction xs as [|x xs IH]; cbn [mapM]; [apply kp_ret; constructor|].
  apply (kp_bind Q); [apply Hf; left|intros y Hy].
  apply (kp_bind (Forall Q)); [apply IH; intros z Hz; apply Hf; right; exact Hz|intros ys Hys].
  apply kp_ret. constructor; assumption.
Qed.
Lemma kp_lift {A} (r : result string A) : kp (λ v, r = Ok v) (mlift r).
Proof.
  destruct r as [value|err]; intros old new w Hold Hrun; [|discriminate].
  change (@Ok string _ (old, value) = Ok (new, w)) in Hrun. injection Hrun as <- <-.
  split; [exact Hold|reflexivity].
Qed.
Lemma kp_guard (err : string) (P : Prop) `{Decision P} : kp (λ _, P) (guard_or err P).
Proof.
  unfold guard_or. destruct (decide P); [apply kp_ret; assumption|].
  intros old new v _ Hrun. discriminate.
Qed.

Lemma kp_fill_root imem mem time roots : kp (Forall fe_ok) (TLB.fill_root imem mem time roots).
Proof.
  unfold TLB.fill_root. apply (kp_fmap (Forall (Forall fe_ok))); [|intros l Hl; apply Forall_concat, Hl].
  apply kp_mapM. intros [[asid ttbr] upper] _. cbv beta iota.
  apply (kp_bind (λ _, True)); [apply kp_keeps, VMCacheLastTLBI.keeps_get|intros indexes _].
  apply (kp_fmap (Forall (Forall fe_ok))); [|intros l Hl; apply Forall_concat, Hl].
  apply kp_mapM. intros idx _.
  match goal with |- kp _ (match ?x with _ => _ end) => destruct x as [memval|err] end;
    [|apply kp_ret; constructor].
  match goal with |- kp _ (if decide ?P then _ else _) => destruct (decide P) end;
    [|apply kp_ret; constructor].
  apply (kp_bind (λ _, True)); [apply kp_keeps, inv_fill_entry, fe_ok_make0|intros loaded _].
  destruct loaded; apply kp_ret; repeat constructor; apply fe_ok_make0.
Qed.

Lemma kp_fill_from_entry imem mem time entry : fe_ok entry →
  kp (Forall fe_ok) (TLB.fill_from_entry imem mem time entry).
Proof.
  intro Hentry. unfold TLB.fill_from_entry.
  apply (kp_bind (λ _, TLB.FE.is_table entry)); [apply kp_guard|intros _ Htable].
  apply (kp_bind (λ _, True)); [apply kp_keeps, VMCacheLastTLBI.keeps_get|intros indexes _].
  apply (kp_bind (λ _, True)); [apply kp_keeps, VMCacheLastTLBI.keeps_othrow|intros clvl _].
  apply (kp_fmap (Forall (Forall fe_ok))); [|intros l Hl; apply Forall_concat, Hl].
  apply kp_mapM. intros idx _.
  match goal with |- kp _ (match ?x with _ => _ end) => destruct x as [memval|err] end;
    [|apply kp_ret; constructor].
  match goal with |- kp _ (if decide ?P then _ else _) => destruct (decide P) end;
    [|apply kp_ret; constructor].
  apply (kp_bind (λ child, TLB.FE.append entry idx memval = Ok child)); [apply kp_lift|intros child Hchild].
  pose proof (fe_ok_append _ _ _ _ Hentry Htable Hchild) as Hc.
  apply (kp_bind (λ _, True)); [apply kp_keeps, inv_fill_entry, Hc|intros loaded _].
  destruct loaded; [|apply kp_ret; constructor].
  match goal with |- kp _ (if decide ?P then _ else _) => destruct (decide P) end;
    apply kp_ret; repeat constructor; exact Hc.
Qed.

Lemma kp_fill_from_entries_step imem mem time entries : Forall fe_ok entries →
  kp (Forall fe_ok) (TLB.fill_from_entries_step imem mem time entries).
Proof.
  intro Hentries. unfold TLB.fill_from_entries_step.
  apply (kp_fmap (Forall (Forall fe_ok))); [|intros l Hl; apply Forall_concat, Hl].
  apply kp_mapM. intros entry Hin. apply kp_fill_from_entry.
  exact (VMViews.Forall_elem _ _ _ Hentries Hin).
Qed.

Lemma keeps_fill_from_entries imem mem time entries : Forall fe_ok entries →
  VMCacheLastTLBI.keeps inv (TLB.fill_from_entries imem mem time entries).
Proof.
  intro Hentries. apply (keeps_kp (λ _, True)). unfold TLB.fill_from_entries.
  apply (kp_bind (Forall fe_ok)); [apply kp_fill_from_entries_step, Hentries|intros e1 H1].
  apply (kp_bind (Forall fe_ok)); [apply kp_fill_from_entries_step, H1|intros e2 H2].
  apply (kp_bind (Forall fe_ok)); [apply kp_fill_from_entries_step, H2|intros e3 H3].
  apply kp_keeps, VMCacheLastTLBI.keeps_guard_unit.
Qed.

Lemma keeps_fill_from_roots imem mem time roots :
  VMCacheLastTLBI.keeps inv (TLB.fill_from_roots imem mem time roots).
Proof.
  apply (keeps_kp (λ _, True)). unfold TLB.fill_from_roots.
  apply (kp_bind (Forall fe_ok)); [apply kp_fill_root|intros entries Hentries].
  apply kp_keeps, keeps_fill_from_entries, Hentries.
Qed.

Lemma kp_relevant asids page : kp (Forall fe_ok) (TLB.get_relevant_entries asids page).
Proof.
  intros old new v Hold Hrun.
  change (@Ok string _ (old, filter (λ fe, TLB.VATLB.is_active (TLB.vatlb old) fe ∧
    TLB.FE.is_active_asid asids fe) (TLB.next_table_cache old !!! page)) = Ok (new, v)) in Hrun.
  injection Hrun as <- <-. split; [exact Hold|].
  apply Forall_forall. intros fe Hfe. apply list_elem_of_In in Hfe.
  apply list_elem_of_filter in Hfe as [[Ha _] _].
  apply Hold. unfold TLB.VATLB.is_active in Ha.
  destruct (TLB.vatlb old !! fe) as [events|]; [eexists; reflexivity|destruct Ha].
Qed.

Lemma keeps_fill_write imem mem time roots msg :
  VMCacheLastTLBI.keeps inv (TLB.fill_write imem mem time roots msg).
Proof.
  apply (keeps_kp (λ _, True)). unfold TLB.fill_write.
  apply (kp_bind (λ _, True)); [apply kp_keeps, VMCacheLastTLBI.keeps_guard|intros _ _].
  apply (kp_bind (Forall fe_ok)); [apply kp_fill_root|intros l0 H0].
  apply (kp_bind (Forall fe_ok)); [apply kp_relevant|intros l1 H1].
  apply kp_keeps, keeps_fill_from_entries, Forall_app. split; assumption.
Qed.

Lemma keeps_fill_tlbi imem mem time roots tlbi :
  VMCacheLastTLBI.keeps inv (TLB.fill_tlbi imem mem time roots tlbi).
Proof.
  apply (keeps_kp (λ _, True)). unfold TLB.fill_tlbi. cbv zeta.
  destruct (TLBI.last tlbi).
  - apply (kp_bind (λ _, True)); [apply kp_keeps, VMCacheLastTLBI.keeps_get|intros cache _].
    apply (kp_bind (λ _, True)); [apply kp_keeps, VMCacheLastTLBI.keeps_get|intros entries _].
    apply (kp_bind (Forall fe_ok)).
    + apply (kp_fmap (Forall (Forall fe_ok))); [|intros l Hl; apply Forall_concat, Hl].
      apply kp_mapM. intros entry _.
      apply (kp_bind (λ _, True)); [apply kp_keeps, inv_alter|intros _ _].
      apply kp_relevant.
    + intros parents Hparents. apply kp_keeps, keeps_fill_from_entries, Hparents.
  - apply (kp_bind (λ _, True)); [apply kp_keeps, inv_map|intros _ _].
    apply kp_keeps, keeps_fill_from_roots.
Qed.

Lemma keeps_fill_event tid imem mem time roots ev :
  VMCacheLastTLBI.keeps inv (TLB.fill_event tid imem mem time roots ev).
Proof.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch]; [apply keeps_fill_write|].
  destruct (decide (tid = recipient)); [apply keeps_fill_tlbi|apply VMCacheLastTLBI.keeps_ret].
Qed.

Lemma keeps_fill_promise tid imem mem ev : VMCacheLastTLBI.keeps inv (TLB.fill_promise tid imem mem ev).
Proof.
  unfold TLB.fill_promise.
  apply VMCacheLastTLBI.keeps_bind; [apply VMCacheLastTLBI.keeps_get|intro; apply keeps_fill_event].
Qed.

Lemma keeps_roll_back time : VMCacheLastTLBI.keeps inv (TLB.roll_back time).
Proof. unfold TLB.roll_back. apply inv_map. Qed.

Lemma keeps_fill_from_btw tid imem fullmem roots tmin tmax mem :
  VMCacheLastTLBI.keeps inv (TLB.fill_from_btw tid imem fullmem roots tmin tmax mem).
Proof.
  revert roots mem. induction tmax as [|tmax IH]; intros roots mem;
    cbn [TLB.fill_from_btw]; destruct (decide (_ < _)); try apply VMCacheLastTLBI.keeps_ret.
  - apply VMCacheLastTLBI.keeps_throw.
  - destruct mem; [apply VMCacheLastTLBI.keeps_throw|].
    apply VMCacheLastTLBI.keeps_bind; [apply IH|]. intro.
    apply VMCacheLastTLBI.keeps_bind; [apply keeps_fill_event|intro; apply keeps_fill_from_roots].
Qed.

Lemma keeps_fill_cse tid imem mem time ttbr0 ttbr1 :
  VMCacheLastTLBI.keeps inv (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  unfold TLB.fill_cse, TLB.fill_from. apply VMCacheLastTLBI.keeps_bind; [apply keeps_roll_back|]. intro.
  apply VMCacheLastTLBI.keeps_bind; [unfold msetv; apply inv_roots|intro; apply keeps_fill_from_btw].
Qed.

Lemma keeps_fill_asid_root tid imem mem root time :
  VMCacheLastTLBI.keeps inv (TLB.fill_asid_root tid imem mem root time).
Proof.
  unfold TLB.fill_asid_root, TLB.fill_from.
  apply VMCacheLastTLBI.keeps_bind; [apply keeps_roll_back|]. intro.
  apply VMCacheLastTLBI.keeps_bind; [apply inv_roots|]. intro.
  apply VMCacheLastTLBI.keeps_bind; [apply keeps_fill_from_roots|]. intro.
  apply VMCacheLastTLBI.keeps_bind; [apply VMCacheLastTLBI.keeps_get|intro; apply keeps_fill_from_btw].
Qed.

Lemma inv_empty present roots ets : inv (TLB.make TLB.VATLB.init present ∅ roots ets).
Proof.
  intros fe Hfe. cbn [TLB.vatlb] in Hfe. rewrite VMCacheIndexed.lookup_init in Hfe.
  destruct Hfe as [? Hbad]. discriminate.
Qed.

Theorem inv_init tid imem iregs cache : TLB.init tid imem iregs = Ok cache → inv cache.
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
    (TLB.make TLB.VATLB.init (TLB.get_pte_present imem) ∅ roots ets)) = Ok cache → inv cache).
  unfold fmap, result_fmap.
  match goal with |- context[TLB.fill_from_roots ?i ?m ?t ?rs ?st] =>
    destruct (TLB.fill_from_roots i m t rs st) as [[ending []]|err] eqn:Hrun end;
    [|discriminate]. cbn. intro Hcache. injection Hcache as <-.
  eapply keeps_fill_from_roots; [apply inv_empty|exact Hrun].
Qed.

(** * Lookup results of a shaped cache *)

Lemma events_path tid ifetch ttbr path events tmin tmax inv_time :
  Forall (λ r, TLB.Result.path r = path)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv_time).
Proof.
  revert tmin tmax inv_time.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmin tmax inv_time.
  destruct events as [|[event time] events].
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); constructor.
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); [constructor|].
    destruct event.
    + destruct (decide (tmax < time)); [apply IH; unfold ltof; cbn; lia|].
      destruct (decide (time < tmin)); [constructor; [reflexivity|constructor]|].
      destruct events as [|[event' time'] rest].
      * constructor; [reflexivity|apply IH; unfold ltof; cbn; lia].
      * destruct event'.
        -- constructor; [reflexivity|apply IH; unfold ltof; cbn; lia].
        -- case_decide.
           ++ destruct rest as [|[[|issuer] stamp] rest];
                first [apply IH; unfold ltof; cbn; lia
                  |constructor; [reflexivity|apply IH; unfold ltof; cbn; lia]].
           ++ constructor; [reflexivity|apply IH; unfold ltof; cbn; lia].
    + apply IH; unfold ltof; cbn; lia.
Qed.

Lemma uncacheable_path p results ptes tmin tmax lvl :
  Forall (λ r, TLB.Result.path r = p) results →
  Forall (λ r, ∃ pte, TLB.Result.path r = (p ++ [pte])%list)
    (TLB.get_results_from_events_uncacheable_aux results ptes tmin tmax lvl).
Proof.
  intros Hresults. revert ptes tmax.
  induction Hresults as [|result results Hhead Htail IH]; intros ptes tmax; [constructor|].
  destruct result as [ttbr path start stop inv_time]. cbn in Hhead. subst path.
  cbn [TLB.get_results_from_events_uncacheable_aux].
  revert tmax. induction ptes as [|[pte time] ptes IHptes]; intro tmax; [constructor|].
  cbn [TLB.Result.tstart TLB.Result.tend].
  destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
  destruct (decide (time ≤ start)); destruct (decide (is_tlb_fillable lvl pte));
    try (constructor; [eexists; reflexivity|]);
    first [apply IH|apply IHptes].
Qed.

Lemma lvl_lt_leaf (lvl : Level) : lvl ≠ leaf_lvl → (lvl : nat) < 3.
Proof.
  intro Hnl. pose proof (fin_to_nat_lt lvl) as Hlt.
  destruct (decide ((lvl : nat) = 3)) as [E|E]; [|lia].
  exfalso. apply Hnl. apply (inj fin_to_nat). exact E.
Qed.

Lemma shaped_leaf fe : fe_ok fe → VMWalkStart.shaped 0 (TLB.FE.ptes fe).
Proof.
  intros Hfe i x Hi Hx. rewrite ptes_length in Hi. pose proof (fin_to_nat_lt (TLB.FE.lvl fe)).
  split; [lia|]. exact (Hfe i x ltac:(lia) Hx).
Qed.

Lemma shaped_table fe pte : fe_ok fe → TLB.FE.is_table fe →
  VMWalkStart.shaped 0 (TLB.FE.ptes fe ++ [pte])%list.
Proof.
  intros Hfe Ht i x Hi Hx. rewrite length_app, ptes_length in Hi. cbn in Hi.
  pose proof (ptes_length fe) as Hlen. rewrite lookup_app_l in Hx by lia.
  destruct Ht as [Hnl Hb]. pose proof (lvl_lt_leaf _ Hnl) as Hl.
  split; [lia|].
  destruct (decide (i < TLB.FE.lvl fe)) as [Hlt|Hge]; [exact (Hfe i x Hlt Hx)|].
  assert (i = TLB.FE.lvl fe) by lia. subst i.
  unfold TLB.FE.ptes in Hx. rewrite vec_last_lookup in Hx. injection Hx as <-. exact Hb.
Qed.

Lemma lookup_shaped tid imem mem c ifetch upper vpn tmin_ok tmin_unc tmax asid r :
  inv c → Exec.elem_of_results r (TLB.lookup tid imem mem c ifetch upper vpn tmin_ok tmin_unc tmax asid) →
  VMWalkStart.shaped 0 (TLB.Result.path r).
Proof.
  intros Hc Hin.
  apply VMLookupReplay.lookup_witness in Hin as (fe & events & candidates & Hentry & Hget & Hin).
  assert (Hfe : fe_ok fe).
  { apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [_ Hentry]].
    unfold TLB.VATLB.get_fe in Hentry.
    apply list_elem_of_In, List.in_map_iff in Hentry as [[entry events'] [Heq Hentry]].
    apply list_elem_of_In in Hentry. injection Heq as <- <-.
    apply Hc. change (is_Some (lookup_assoc entry (TLB.VATLB.get ctxt (TLB.vatlb c)))).
    apply VMCacheLastTLBI.lookup_assoc_elem. exists events'. exact Hentry. }
  unfold TLB.get_result_from_FE in Hget. case_decide as Htable.
  - unfold TLB.get_result_from_table_FE in Hget.
    destruct (decide (tmax < tmin_unc)); [injection Hget as <-; inversion Hin|].
    destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection Hget as <-; inversion Hin].
    match type of Hget with context[TLB.get_results_from_events ?a ?b ?c ?d ?e ?f ?g ?h] =>
      pose proof (events_path a b c d e f g h) as Hp;
      destruct (TLB.get_results_from_events a b c d e f g h) as [|r0 rs]
    end; [injection Hget as <-; inversion Hin|].
    match type of Hget with context[Memory.read_all_pte ?a ?b ?c ?d ?e] =>
      destruct (Memory.read_all_pte a b c d e) as [ptes|err] end; cbn in Hget; [|discriminate].
    injection Hget as <-.
    destruct (VMViews.Forall_elem _ _ _ (uncacheable_path _ _ ptes tmin_unc tmax lvl Hp) Hin)
      as [pte ->].
    apply shaped_table; assumption.
  - unfold TLB.get_result_from_leaf_FE in Hget. injection Hget as <-.
    destruct (decide (tmax < tmin_ok)); [inversion Hin|].
    rewrite (VMViews.Forall_elem _ _ _ (events_path _ _ _ _ _ _ _ _) Hin). apply shaped_leaf, Hfe.
Qed.

(** The cache invariant of a thread state. *)
Definition tok (ts : TState.t) : Prop :=
  match TState.tlb ts with Some c => inv c | None => True end.

Theorem tlb_lookup_shaped tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax r :
  tok ts →
  r ∈ Exec.results (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0
    tmin_ok tmin_unc tmax) →
  VMWalkStart.shaped 0 (TLB.Result.path r).
Proof.
  intros Hts Hin. unfold TState.tlb_lookup in Hin. unfold tok in Hts.
  destruct (TState.tlb ts) as [c|]; [|cbn in Hin; inversion Hin].
  unfold Exec.merge in Hin. cbn [Exec.results] in Hin.
  apply elem_of_app in Hin as [Hin|Hin]; [eapply lookup_shaped; [exact Hts|exact Hin]|].
  change (Exec.elem_of_results r
    (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin_unc tmax)) in Hin.
  unfold VMRootLookupReplay.root_lookup in Hin.
  destruct (decide (tmin_unc ≤ tmax)); [|inversion Hin].
  apply Exec.elem_of_res_bind_elim in Hin as [ttbrs [_ Hin]].
  apply Exec.elem_of_res_bind_elim in Hin as [[ttbr vttbr] [_ Hin]].
  apply Exec.elem_of_res_bind_elim in Hin as [ptes [_ Hin]].
  apply Exec.elem_of_res_mchoosel_inv in Hin.
  apply list_elem_of_fmap in Hin as [[pte vpte] [-> _]].
  intros i x Hi. cbn in Hi. lia.
Qed.

Local Notation ppstate := (PPState.t TState.t Ev.t IIS.t).

(** The walk-shape invariant of [VMWalkReplay.ShInvariant]. *)
Definition CShape {n} (tid : fin n) (imem : memoryMap) (p : ppstate) : Prop :=
  tok (PPState.state p).

Lemma cshape_shape {n} (tid : fin n) imem p : CShape tid imem p → VMWalkStart.Shape tid imem p.
Proof. intros Hp. intros ???????? r Hr. eapply tlb_lookup_shaped; [exact Hp|exact Hr]. Qed.

Local Opaque TLB.fill_promise TLB.fill_asid_root TLB.fill_cse.

Lemma tok_tlb ts ts' : TState.tlb ts' = TState.tlb ts → tok ts → tok ts'.
Proof. unfold tok. intros ->. exact id. Qed.

Lemma run_tlb_tok run ts ts' :
  VMCacheLastTLBI.keeps inv run → tok ts → TState.run_tlb run ts = Ok ts' → tok ts'.
Proof.
  intros Hrun Hok Hts. unfold TState.run_tlb in Hts. unfold tok in *.
  destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (run c) as [[c' []]|err] eqn:Hr; cbn in Hts; [|discriminate].
    injection Hts as <-. exact (Hrun c c' () Hok Hr).
  - injection Hts as <-. rewrite Hc. exact I.
Qed.

Lemma process_event_tok tid imem mem ev ts ts' :
  tok ts → TState.process_event tid imem mem ev ts = Ok ts' → tok ts'.
Proof. apply run_tlb_tok, keeps_fill_promise. Qed.

Lemma emit_tok tid imem mem ev ts ts' :
  tok ts → TState.emit_promise tid imem mem ev ts = Ok ts' → tok ts'.
Proof.
  intros Hok He. unfold TState.emit_promise in He. eapply process_event_tok; [|exact He].
  destruct (bool_decide _); [destruct ev|]; exact Hok.
Qed.

Lemma cse_tok imem mem tid v ts ts' :
  tok ts → TState.cse imem mem tid v ts = Ok ts' → tok ts'.
Proof.
  intros Hok Hcse. unfold TState.cse, mbind, result_bind in Hcse.
  match type of Hcse with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hcse as <-. eapply run_tlb_tok; [| |exact Hmid]; [|exact Hok].
  apply (VMCacheLastTLBI.keeps_bind inv (mret ())); [apply VMCacheLastTLBI.keeps_ret|intros []].
  apply (VMCacheLastTLBI.keeps_bind inv (othrow _ _)); [apply VMCacheLastTLBI.keeps_othrow|intro].
  apply keeps_fill_cse.
Qed.

Lemma add_wsreg_tok tid imem mem sreg val v ts ts' :
  tok ts → TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → tok ts'.
Proof.
  intros Hok Hrun. unfold TState.add_wsreg, mbind, result_bind in Hrun.
  match type of Hrun with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hrun as <-. change (tok mid). eapply run_tlb_tok; [|exact Hok|exact Hmid].
  clear Hmid Hok.
  destruct sreg as [r|r|r|r]; try exact (VMCacheLastTLBI.keeps_ret inv ()).
  destruct r; try exact (VMCacheLastTLBI.keeps_ret inv ()); cbv beta iota zeta.
  - apply VMCacheLastTLBI.keeps_bind; [apply keeps_fill_asid_root|intro].
    apply VMCacheLastTLBI.keeps_bind; [|intro; apply VMCacheLastTLBI.keeps_ret].
    apply VMCacheLastTLBI.keeps_mapM. intros [ttbr view]. apply keeps_fill_asid_root.
  - apply VMCacheLastTLBI.keeps_bind; [apply VMCacheLastTLBI.keeps_othrow|intro].
    apply VMCacheLastTLBI.keeps_bind; [|intro; apply VMCacheLastTLBI.keeps_ret].
    apply VMCacheLastTLBI.keeps_mapM. intros [ttbr view]. apply keeps_fill_asid_root.
Qed.

Lemma init_tok tid imem iregs ts : TState.init tid imem iregs = Ok ts → tok ts.
Proof.
  unfold TState.init, othrow, guard_or, mbind, result_bind, fmap, result_fmap.
  destruct (reg_lookup CurrentEL iregs); [|discriminate]. cbn.
  match goal with |- context[match ?d with left _ => _ | right _ => _ end] => destruct d end;
    cbn; [|discriminate].
  destruct (reg_lookup SCTLR_EL1 iregs); [|discriminate]. cbn.
  match goal with |- context[if ?b then _ else _] => destruct b end.
  - destruct (TLB.init tid imem iregs) as [cache|] eqn:Hinit; [|discriminate]. cbn.
    injection 1 as <-. apply inv_init in Hinit. exact Hinit.
  - injection 1 as <-. exact I.
Qed.

Definition pok (p : ppstate) := tok (PPState.state p).

Ltac shape_finish :=
  cbn [PPState.state PPState.mem PPState.iis] in *;
  repeat match goal with H : ?x = ?y |- _ => is_var x; is_var y; subst x end;
  repeat match goal with
  | H : Some _ = TState.set_reg _ _ _ |- _ => symmetry in H
  | H : TState.set_reg _ _ _ = Some _ |- _ => apply VMRoots.set_reg_tlb in H
  | H : TState.process_event _ _ _ _ ?t = Ok ?t', Htok : tok ?t |- _ =>
      let Hnew := fresh "Hshape" in
      pose proof (process_event_tok _ _ _ _ t t' Htok H) as Hnew; clear H
  end;
  unfold pok in *; cbn [PPState.state PPState.mem PPState.iis fst snd] in *;
  match goal with Htok : tok ?t |- tok _ => apply (tok_tlb t); [VMRoots.tlb_eq|exact Htok] end.

Section Handlers.
Context (tid : nat) (imem : memoryMap).

Lemma run_cse_shape vmax p p' r :
  pok p → Exec.elem_of_results (p', r) (run_cse tid imem vmax p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold run_cse. intros Hr Hrun. VMViews.invert.
  unfold pok. cbn. eapply cse_tok; [exact Hr|eassumption].
Qed.

Lemma run_barrier_shape b vmax p p' r :
  pok p → Exec.elem_of_results (p', r) (run_barrier tid imem b vmax p) → pok p'.
Proof.
  intros Hr Hrun. destruct p as [ts mem iis]. unfold run_barrier in Hrun.
  VMViews.invert. all: try solve [eapply run_cse_shape; eassumption]. all: shape_finish.
Qed.

Lemma run_take_exception_shape f vmax p p' r :
  pok p → Exec.elem_of_results (p', r) (run_take_exception tid imem f vmax p) → pok p'.
Proof.
  intros Hr Hrun. destruct p as [ts mem iis]. unfold run_take_exception in Hrun.
  VMViews.invert. all: eapply run_cse_shape; eassumption.
Qed.

Lemma run_reg_write_shape reg racc val p p' r :
  pok p → Exec.elem_of_results (p', r) (run_reg_write tid imem reg racc val p) → pok p'.
Proof.
  destruct p as [ts mem iis]. intros Hr Hrun. unfold run_reg_write in Hrun. unfold pok in Hr. cbn in Hr.
  VMViews.invert.
  all: try match goal with H : TState.add_wsreg _ _ _ _ _ _ _ = Ok _ |- _ =>
    apply add_wsreg_tok in H; [|exact Hr] end.
  all: shape_finish.
Qed.

Lemma write_mem_shape addr size macc data p p' r :
  pok p → Exec.elem_of_results (p', r) (write_mem tid imem addr size macc data p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun. unfold write_mem in Hrun.
  VMViews.invert. all: shape_finish.
Qed.

Lemma materialize_shape pre tlbi recipient p p' r :
  pok p → Exec.elem_of_results (p', r)
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun.
  unfold materialize_tlbi_for_recipient in Hrun. VMViews.invert. all: shape_finish.
Qed.

Lemma recipients_shape pre tlbi recipients acc p p' r :
  pok p → Exec.elem_of_results (p', r)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients p) → pok p'.
Proof.
  revert acc p. induction recipients as [|recipient recipients IH]; intros acc p Hs Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hs.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [a [Hstep Htail]]].
    destruct acc as [[vs vo] cr]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    cbv beta iota in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[tm isn] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply IH; [|exact Htail]. eapply materialize_shape; eassumption.
Qed.

Lemma run_tlbi_shape n viio tlbi p p' r :
  pok p → Exec.elem_of_results (p', r) (run_tlbi n tid imem viio tlbi p) → pok p'.
Proof.
  destruct p as [ts mem iis]. intros Hr Hrun. unfold run_tlbi in Hrun. VMViews.invert.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply recipients_shape in H; [|exact Hr] end.
  all: match goal with H : pok ?x |- _ => destruct x; exact H end.
Qed.

Lemma read_explicit_shape addr size macc p p' r :
  pok p → Exec.elem_of_results (p', r) (read_mem_explicit imem addr size macc p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun. unfold read_mem_explicit in Hrun.
  VMViews.invert. all: shape_finish.
Qed.

Lemma read_pte_shape p p' r : pok p → Exec.elem_of_results (p', r) (read_pte p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun. unfold read_pte in Hrun.
  VMViews.invert. all: shape_finish.
Qed.

Lemma trans_start_shape s p p' r :
  pok p → Exec.elem_of_results (p', r) (run_trans_start tid imem s p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun. unfold run_trans_start in Hrun.
  VMViews.invert.
  all: try match goal with H : Exec.elem_of_results (?x, ?vv) (read_sreg_indirect ?rg ?ra ?st) |- _ =>
    pose proof (VMTLBShape.read_sreg_indirect_fst rg ra st x vv H) as Hx; clear H;
    destruct x as [ts3 iis3]; cbn in Hx; subst ts3 end.
  all: shape_finish.
Qed.
End Handlers.

Theorem run_outcome_shape n tid imem out p p' r :
  pok p → Exec.elem_of_results (p', r) (run_outcome n tid imem out p) → pok p'.
Proof.
  intros Hs H. funelim (run_outcome n tid imem out p).
  all: rewrite <- Heqcall in H.
  all: VMViews.invert; subst.
  all: try (eapply run_barrier_shape; eassumption).
  all: try (eapply run_cse_shape; eassumption).
  all: try (eapply run_take_exception_shape; eassumption).
  all: try (eapply run_reg_write_shape; eassumption).
  all: try (eapply write_mem_shape; eassumption).
  all: try (eapply run_tlbi_shape; eassumption).
  all: try (eapply read_explicit_shape; eassumption).
  all: try (eapply read_pte_shape; eassumption).
  all: try (eapply trans_start_shape; eassumption).
  all: try (match goal with H0 : Exec.elem_of_results (?x, _) (run_reg_read _ _ _) |- _ =>
    apply VMTLBShape.run_reg_read_fst in H0; destruct x; cbn in H0; subst end).
  all: try (match goal with H0 : Exec.elem_of_results (?x, _) (run_trans_end _ _) |- _ =>
    apply VMRoots.trans_end_tlb in H0; destruct x; cbn in H0 end).
  all: try shape_finish.
  all: match goal with H : pok ?x |- _ => destruct x end.
  all: unfold pok in *; cbn in *.
  all: try assumption.
  all: match goal with H0 : TState.tlb ?t = TState.tlb ?s, Hs : tok ?s |- _ =>
    exact (tok_tlb s t H0 Hs) end.
Qed.

Theorem instruction_shape n (tid : fin n) imem {A} (mon : iMon A) p p' ret :
  pok p → Exec.elem_of_results (p', ret) (cinterp (run_outcome' n tid imem) mon p) → pok p'.
Proof.
  revert p p' ret. induction mon as [a|call k IH]; intros p p' ret Hr Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hr.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      eapply IH; [eapply run_outcome_shape; eassumption|exact Htail].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

End VMWalkShape.
