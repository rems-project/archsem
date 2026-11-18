(******************************************************************************)
(* VM outcomes on thread states whose caches are observationally equivalent    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheIndexed
  PromiseFirstSailVMCacheEvents PromiseFirstSailVMCacheExchange PromiseFirstSailVMCacheConfig
  PromiseFirstSailVMCacheHistory PromiseFirstSailVMCacheLastTLBI PromiseFirstSailVMCacheContext
  PromiseFirstSailVMCacheOrder PromiseFirstSailVMCacheState PromiseFirstSailVMBBMTransport
  PromiseFirstSailVMLookup PromiseFirstSailVMRootLookup PromiseFirstSailVMCacheTraversal
  PromiseFirstSailVMViews PromiseFirstFreshBroadcast PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstSailSerialization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMCacheSim.
Import VMPromising VMCacheRefill.
#[local] Typeclasses Transparent view UMPromising.view.
Local Notation unique := VMCacheLastTLBI.unique.

(** * Simulated caches *)

(** The structural invariants needed to replay cache maintenance. They are
    preserved by every cache operation without a time bound. *)
Definition wf (cache : TLB.t) := VMCacheIndexed.valid cache ∧ unique cache.

(** Two caches are simulated when they have the same entry histories,
    present-PTE map, roots and ETS, and both are well formed. Allocation order,
    dormant rows and the physical-page index may differ. *)
Definition cache_sim (a b : TLB.t) := VMCacheContext.observational a b ∧ wf a ∧ wf b.

Lemma cache_sim_sym a b : cache_sim a b → cache_sim b a.
Proof.
  intros [Hobs [Ha Hb]]. split; [apply VMCacheContext.observational_sym, Hobs|]. auto.
Qed.

Lemma cache_sim_refl a : wf a → cache_sim a a.
Proof. intro Ha. split; [|auto]. split; [apply equiv_refl|auto]. Qed.

(** A cache action respects the simulation when every successful run on one
    cache can be replayed on a simulated cache with the same output. *)
Definition sim_action {A} (run : stateT TLB.t (result string) A) :=
  ∀ a b a' x, cache_sim a b → run a = Ok (a', x) →
    ∃ b', run b = Ok (b', x) ∧ cache_sim a' b'.

Lemma sim_ret {A} (x : A) : sim_action (mret x).
Proof.
  intros a b a' y Hsim Hrun. change (@Ok string _ (a, x) = Ok (a', y)) in Hrun.
  injection Hrun as <- <-. exists b. split; [reflexivity|exact Hsim].
Qed.

Lemma sim_bind {A B} (run : stateT TLB.t (result string) A)
    (next : A → stateT TLB.t (result string) B) :
  sim_action run → (∀ x, sim_action (next x)) → sim_action (run ≫= next).
Proof.
  intros Hrun Hnext a b a' y Hsim Hall. unfold mbind, st_bind, result_bind in Hall |- *.
  destruct (run a) as [[mid x]|err] eqn:Hfirst; [|discriminate].
  destruct (Hrun a b mid x Hsim Hfirst) as [mid' [-> Hmid]].
  exact (Hnext x mid mid' a' y Hmid Hall).
Qed.

Lemma sim_othrow {A} (err : string) (opt : option A) : sim_action (othrow err opt).
Proof.
  destruct opt; [apply sim_ret|]. intros a b a' x _ Hrun. discriminate.
Qed.

Lemma sim_mapM {A B} (f : A → stateT TLB.t (result string) B) xs :
  (∀ x, sim_action (f x)) → sim_action (mapM f xs).
Proof.
  intro Hf. induction xs as [|x xs IH]; cbn [mapM]; [apply sim_ret|].
  apply sim_bind; [apply Hf|intro]. apply sim_bind; [exact IH|intro]. apply sim_ret.
Qed.

Lemma rolled_equiv time a b :
  equiv a b → equiv (VMCacheExchange.rolled time a) (VMCacheExchange.rolled time b).
Proof.
  intros [Hpresent Hhist]. split; [exact Hpresent|]. intro fe.
  unfold VMCacheExchange.rolled. rewrite !VMCacheEvents.history_map by reflexivity.
  rewrite Hhist. reflexivity.
Qed.

Local Opaque TLB.fill_event.

Theorem fill_promise_sim tid imem mem ev : sim_action (TLB.fill_promise tid imem mem ev).
Proof.
  intros a b a' [] [[Heq [Hroots Hets]] [[Hva Hua] [Hvb Hub]]] Hrun.
  change (TLB.fill_event tid imem mem (length mem) (TLB.asid_roots a).*1 ev a = Ok (a', ()))
    in Hrun.
  destruct (VMCacheLastTLBI.fill_event_equiv tid imem mem (length mem) (TLB.asid_roots a).*1 ev
    a b a' Hva Hvb Hua Hub Heq Hrun) as [b' [Hb Heq']].
  assert (Hpa : TLB.fill_promise tid imem mem ev a = Ok (a', ())) by exact Hrun.
  rewrite Hroots in Hb.
  assert (Hpb : TLB.fill_promise tid imem mem ev b = Ok (b', ())) by exact Hb.
  exists b'. split; [exact Hpb|]. split; [split; [exact Heq'|split]|unfold wf; split; split].
  - pose proof (VMCacheRoots.fill_promise tid imem mem ev a a' () Hpa) as H1.
    pose proof (VMCacheRoots.fill_promise tid imem mem ev b b' () Hpb) as H2.
    unfold VMCacheRoots.config in H1, H2. congruence.
  - pose proof (VMCacheConfig.fill_promise tid imem mem ev a a' () Hpa) as H1.
    pose proof (VMCacheConfig.fill_promise tid imem mem ev b b' () Hpb) as H2.
    unfold VMCacheConfig.config in H1, H2. congruence.
  - eapply VMCacheIndexed.fill_promise; [exact Hva|exact Hpa].
  - eapply VMCacheLastTLBI.unique_fill_promise; [exact Hua|exact Hpa].
  - eapply VMCacheIndexed.fill_promise; [exact Hvb|exact Hpb].
  - eapply VMCacheLastTLBI.unique_fill_promise; [exact Hub|exact Hpb].
Qed.

Theorem fill_cse_sim tid imem mem time ttbr0 ttbr1 :
  sim_action (TLB.fill_cse tid imem mem time ttbr0 ttbr1).
Proof.
  intros a b a' [] [[Heq [Hroots Hets]] [[Hva Hua] [Hvb Hub]]] Hrun.
  destruct (VMCacheContext.fill_cse_rolled_equiv tid imem mem time ttbr0 ttbr1 a b a'
    Hva Hvb Hua Hub (rolled_equiv time a b Heq) Hrun) as [b' [Hb Heq']].
  exists b'. split; [exact Hb|]. split; [split; [exact Heq'|split]|unfold wf; split; split].
  - rewrite (VMCacheHistory.fill_cse_roots _ _ _ _ _ _ _ _ Hrun).
    rewrite (VMCacheHistory.fill_cse_roots _ _ _ _ _ _ _ _ Hb). reflexivity.
  - pose proof (VMCacheConfig.fill_cse tid imem mem time ttbr0 ttbr1 a a' () Hrun) as H1.
    pose proof (VMCacheConfig.fill_cse tid imem mem time ttbr0 ttbr1 b b' () Hb) as H2.
    unfold VMCacheConfig.config in H1, H2. congruence.
  - eapply VMCacheIndexed.fill_cse; [exact Hva|exact Hrun].
  - eapply VMCacheLastTLBI.unique_fill_cse; [exact Hua|exact Hrun].
  - eapply VMCacheIndexed.fill_cse; [exact Hvb|exact Hb].
  - eapply VMCacheLastTLBI.unique_fill_cse; [exact Hub|exact Hb].
Qed.

Theorem fill_asid_root_sim tid imem mem root time :
  sim_action (TLB.fill_asid_root tid imem mem root time).
Proof.
  intros a b a' [] [[Heq [Hroots Hets]] [[Hva Hua] [Hvb Hub]]] Hrun.
  destruct (VMCacheContext.fill_asid_root_rolled_equiv tid imem mem root time a b a'
    Hva Hvb Hua Hub Hroots (rolled_equiv time a b Heq) Hrun) as [b' [Hb Heq']].
  exists b'. split; [exact Hb|]. split; [split; [exact Heq'|split]|unfold wf; split; split].
  - rewrite (VMCacheExchange.fill_asid_root_roots _ _ _ _ _ _ _ Hrun).
    rewrite (VMCacheExchange.fill_asid_root_roots _ _ _ _ _ _ _ Hb). congruence.
  - pose proof (VMCacheConfig.fill_asid_root tid imem mem root time a a' () Hrun) as H1.
    pose proof (VMCacheConfig.fill_asid_root tid imem mem root time b b' () Hb) as H2.
    unfold VMCacheConfig.config in H1, H2. congruence.
  - eapply VMCacheIndexed.fill_asid_root; [exact Hva|exact Hrun].
  - eapply VMCacheLastTLBI.unique_fill_asid_root; [exact Hua|exact Hrun].
  - eapply VMCacheIndexed.fill_asid_root; [exact Hvb|exact Hb].
  - eapply VMCacheLastTLBI.unique_fill_asid_root; [exact Hub|exact Hb].
Qed.

(** * Simulated thread states *)

Definition tlb_sim (a b : option TLB.t) :=
  match a, b with
  | Some a, Some b => cache_sim a b
  | None, None => True
  | _, _ => False
  end.

(** Thread states agree on every field except the cache, and their caches are
    simulated. *)
Definition ts_sim (ts1 ts2 : TState.t) :=
  ts2 = setv TState.tlb (TState.tlb ts2) ts1 ∧ tlb_sim (TState.tlb ts1) (TState.tlb ts2).

Lemma tlb_sim_sym a b : tlb_sim a b → tlb_sim b a.
Proof. destruct a, b; cbn; try tauto. apply cache_sim_sym. Qed.

Lemma tlb_setv ts c : TState.tlb (setv TState.tlb c ts) = c.
Proof. reflexivity. Qed.

Lemma setv_tlb_same ts : setv TState.tlb (TState.tlb ts) ts = ts.
Proof. destruct ts; reflexivity. Qed.

Lemma setv_tlb_twice ts c c' : setv TState.tlb c (setv TState.tlb c' ts) = setv TState.tlb c ts.
Proof. destruct ts; reflexivity. Qed.

Lemma ts_sim_setv ts c1 c2 : tlb_sim c1 c2 →
  ts_sim (setv TState.tlb c1 ts) (setv TState.tlb c2 ts).
Proof.
  intro Hsim. split; [|exact Hsim]. cbn [TState.tlb setv]. symmetry. apply setv_tlb_twice.
Qed.

Lemma ts_sim_inv ts1 ts2 : ts_sim ts1 ts2 →
  ∃ ts c1 c2, ts1 = setv TState.tlb c1 ts ∧ ts2 = setv TState.tlb c2 ts ∧ tlb_sim c1 c2.
Proof.
  intros [Hts Hsim]. exists ts1, (TState.tlb ts1), (TState.tlb ts2).
  split; [symmetry; apply setv_tlb_same|]. split; [exact Hts|exact Hsim].
Qed.

Lemma ts_sim_sym ts1 ts2 : ts_sim ts1 ts2 → ts_sim ts2 ts1.
Proof.
  intro Hsim. apply ts_sim_inv in Hsim as (ts & c1 & c2 & -> & -> & Hsim).
  apply ts_sim_setv, tlb_sim_sym, Hsim.
Qed.

Lemma ts_sim_tlb ts1 ts2 : ts_sim ts1 ts2 → tlb_sim (TState.tlb ts1) (TState.tlb ts2).
Proof. intros [_ Hsim]. exact Hsim. Qed.

(** Every field other than the cache agrees. *)
Lemma ts_sim_frame ts1 ts2 : ts_sim ts1 ts2 →
  setv TState.tlb None ts1 = setv TState.tlb None ts2.
Proof. intros [-> _]. symmetry. apply setv_tlb_twice. Qed.

Lemma ts_sim_ets ts1 ts2 : ts_sim ts1 ts2 →
  TState.ets2 ts1 = TState.ets2 ts2 ∧ TState.ets3 ts1 = TState.ets3 ts2.
Proof.
  intros [_ Hsim]. unfold TState.ets2, TState.ets3.
  destruct (TState.tlb ts1) as [a|], (TState.tlb ts2) as [b|]; cbn in Hsim; try contradiction;
    [|auto].
  destruct Hsim as [[_ [_ Hets]] _]. rewrite Hets. auto.
Qed.

Theorem run_tlb_sim run ts c1 c2 ts1' :
  sim_action run → tlb_sim c1 c2 →
  TState.run_tlb run (setv TState.tlb c1 ts) = Ok ts1' →
  ∃ ts2', TState.run_tlb run (setv TState.tlb c2 ts) = Ok ts2' ∧ ts_sim ts1' ts2'.
Proof.
  intros Hrun Hsim Hts. unfold TState.run_tlb in Hts |- *. rewrite !tlb_setv in Hts |- *.
  destruct c1 as [a|], c2 as [b|]; cbn in Hsim; try contradiction.
  - unfold fmap, result_fmap, mbind, result_bind in Hts |- *.
    destruct (run a) as [[a' x]|err] eqn:Ha; cbn in Hts; [|discriminate].
    destruct (Hrun a b a' x Hsim Ha) as [b' [-> Hb]]. cbn.
    injection Hts as <-. eexists. split; [reflexivity|].
    rewrite !setv_tlb_twice. apply ts_sim_setv. exact Hb.
  - injection Hts as <-. eexists. split; [reflexivity|]. apply ts_sim_setv. exact I.
Qed.

Lemma run_tlb_bind_sim run (f : TState.t → TState.t) ts c1 c2 ts1' :
  sim_action run → tlb_sim c1 c2 →
  (∀ t d1 d2, tlb_sim d1 d2 → ts_sim (f (setv TState.tlb d1 t)) (f (setv TState.tlb d2 t))) →
  (TState.run_tlb run (setv TState.tlb c1 ts) ≫= (λ t, mret (f t))) = Ok ts1' →
  ∃ ts2', (TState.run_tlb run (setv TState.tlb c2 ts) ≫= (λ t, mret (f t))) = Ok ts2' ∧
    ts_sim ts1' ts2'.
Proof.
  intros Hrun Hsim Hf Hts.
  destruct (TState.run_tlb run (setv TState.tlb c1 ts)) as [mid|err] eqn:Hmid;
    cbn in Hts; [|discriminate].
  injection Hts as <-.
  destruct (run_tlb_sim run ts c1 c2 mid Hrun Hsim Hmid) as [mid' [Hmid' Hs]].
  rewrite Hmid'. cbn. eexists; split; [reflexivity|].
  apply ts_sim_inv in Hs as (t & d1 & d2 & -> & -> & Hd). apply Hf, Hd.
Qed.

Theorem process_event_sim tid imem mem ev ts1 ts2 ts1' :
  ts_sim ts1 ts2 → TState.process_event tid imem mem ev ts1 = Ok ts1' →
  ∃ ts2', TState.process_event tid imem mem ev ts2 = Ok ts2' ∧ ts_sim ts1' ts2'.
Proof.
  intros Hsim. apply ts_sim_inv in Hsim as (ts & c1 & c2 & -> & -> & Hsim).
  apply run_tlb_sim; [apply fill_promise_sim|exact Hsim].
Qed.

Definition pending tid (mem : Memory.t) ev ts :=
  if bool_decide (Ev.tid ev = tid) then
    if ev is Ev.Msg _ then TState.promise_write (length mem) ts
    else TState.promise_tlbi (length mem) ts
  else ts.

Lemma emit_shape tid imem mem ev ts c :
  TState.emit_promise tid imem mem ev (setv TState.tlb c ts) =
    TState.process_event tid imem mem ev (setv TState.tlb c (pending tid mem ev ts)).
Proof.
  unfold TState.emit_promise, pending.
  destruct (bool_decide (Ev.tid ev = tid)); [destruct ev|]; reflexivity.
Qed.

Theorem emit_promise_sim tid imem mem ev ts1 ts2 ts1' :
  ts_sim ts1 ts2 → TState.emit_promise tid imem mem ev ts1 = Ok ts1' →
  ∃ ts2', TState.emit_promise tid imem mem ev ts2 = Ok ts2' ∧ ts_sim ts1' ts2'.
Proof.
  intros Hsim. apply ts_sim_inv in Hsim as (ts & c1 & c2 & -> & -> & Hsim).
  rewrite !emit_shape. apply process_event_sim, ts_sim_setv, Hsim.
Qed.

Definition cse_pre v ts := ts |> TState.update TState.vcse v |> set TState.levs (LEv.Cse v ::.).

Lemma cse_shape imem mem tid v ts c :
  TState.cse imem mem tid v (setv TState.tlb c ts) =
    TState.run_tlb (
      mret ();;
      ttbr0 ← othrow "Can't read TTBR0_EL1" $ TState.read_sreg_direct (cse_pre v ts) TTBR0_EL1;
      let ttbr1 := TState.read_sreg_direct (cse_pre v ts) TTBR1_EL1 |$> fst in
      TLB.fill_cse tid imem mem v ttbr0.1 ttbr1) (setv TState.tlb c (cse_pre v ts)) ≫= mret.
Proof. reflexivity. Qed.

Theorem cse_sim imem mem tid v ts1 ts2 ts1' :
  ts_sim ts1 ts2 → TState.cse imem mem tid v ts1 = Ok ts1' →
  ∃ ts2', TState.cse imem mem tid v ts2 = Ok ts2' ∧ ts_sim ts1' ts2'.
Proof.
  intros Hsim. apply ts_sim_inv in Hsim as (ts & c1 & c2 & -> & -> & Hsim).
  rewrite !cse_shape. apply run_tlb_bind_sim; [|exact Hsim|intros; apply ts_sim_setv; assumption].
  apply sim_bind; [apply sim_ret|intro]. apply sim_bind; [apply sim_othrow|intro].
  apply fill_cse_sim.
Qed.

Lemma add_wsreg_shape tid imem mem (sreg : reg) (val : reg_type sreg) (v : view) ts c :
  TState.add_wsreg tid imem mem sreg val v (setv TState.tlb c ts) =
    (TState.run_tlb
      ( match sreg return reg_type sreg → stateT TLB.t (result string) () with
        | TTBR0_EL1 =>
            λ val,
            let asid := bv_extract 48 16 val in
            TLB.fill_asid_root tid imem mem (asid, val, false) v;;
            let ttbr1s := default [] (TState.read_sreg_indirect ts TTBR1_EL1) in
            for (ttbr1, v1) in ttbr1s do
              TLB.fill_asid_root tid imem mem (asid, ttbr1, true) (v ⊔ v1)
            end;;
            mret ()
        | TTBR1_EL1 =>
            λ val,
            ttbr0s ←
              othrow "Can't read TTBR0_EL1" $
                TState.read_sreg_indirect ts TTBR0_EL1;
            for (ttbr0, v0) in ttbr0s do
              let v := v ⊔ v0 in
              TLB.fill_asid_root tid imem mem (bv_extract 48 16 ttbr0, val, true) v
            end;;
            mret ()
        | _ => λ _, mret ()
       end val) (setv TState.tlb c ts)) ≫=
    (λ ts, ts |> set TState.levs ((LEv.Wsreg (WSReg.make sreg val v))::.) |> mret (M := result string)).
Proof. reflexivity. Qed.

Theorem add_wsreg_sim tid imem mem sreg val v ts1 ts2 ts1' :
  ts_sim ts1 ts2 → TState.add_wsreg tid imem mem sreg val v ts1 = Ok ts1' →
  ∃ ts2', TState.add_wsreg tid imem mem sreg val v ts2 = Ok ts2' ∧ ts_sim ts1' ts2'.
Proof.
  intros Hsim. apply ts_sim_inv in Hsim as (ts & c1 & c2 & -> & -> & Hsim).
  rewrite !add_wsreg_shape. apply run_tlb_bind_sim; [|exact Hsim|].
  2:{ intros ts' d1 d2 Hd.
    change (ts_sim (setv TState.tlb d1 (set TState.levs (LEv.Wsreg (WSReg.make sreg val v) ::.) ts'))
      (setv TState.tlb d2 (set TState.levs (LEv.Wsreg (WSReg.make sreg val v) ::.) ts'))).
    apply ts_sim_setv, Hd. }
  - destruct sreg as [r|r|r|r]; try apply sim_ret.
    destruct r; try apply sim_ret; cbv beta iota zeta.
    + apply sim_bind; [apply fill_asid_root_sim|intro].
      apply sim_bind; [apply sim_mapM; intros [? ?]; apply fill_asid_root_sim|intro; apply sim_ret].
    + apply sim_bind; [apply sim_othrow|intro].
      apply sim_bind; [apply sim_mapM; intros [? ?]; apply fill_asid_root_sim|intro; apply sim_ret].
Qed.

(** * Lookups *)

Lemma res_bind_results {E A B} (e : Exec.res E A) (k : A → Exec.res E B) :
  Exec.results (e ≫= k) = List.concat (map (λ a, Exec.results (k a)) (Exec.results e)).
Proof.
  destruct e as [l es]. unfold mbind, Exec.res_mbind_inst. cbn [Exec.results].
  induction l as [|a l IH]; cbn; [reflexivity|]. unfold Exec.merge at 1. cbn. rewrite IH. reflexivity.
Qed.

Lemma res_bind_errors {E A B} (e : Exec.res E A) (k : A → Exec.res E B) :
  Exec.errors (e ≫= k) =
    (List.concat (map (λ a, Exec.errors (k a)) (Exec.results e)) ++ Exec.errors e)%list.
Proof.
  destruct e as [l es]. unfold mbind, Exec.res_mbind_inst. cbn [Exec.results Exec.errors].
  induction l as [|a l IH]; cbn; [reflexivity|]. unfold Exec.merge at 1. cbn. rewrite IH.
  rewrite app_assoc. reflexivity.
Qed.

Lemma map_fmap {A B C} (f : B → C) (g : A → B) (L : list A) :
  map f (g <$> L) = map (λ x, f (g x)) L.
Proof. induction L; cbn; congruence. Qed.

Lemma fin_lookup_enum {A} (l : list A) :
  map (λ i, list_to_vec l !!! i) (fin_enum (length l)) = l.
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn. f_equal. rewrite map_fmap. exact IH.
Qed.

Lemma mchoosel_results {E A} (l : list A) : Exec.results (mchoosel l : Exec.res E A) = l.
Proof.
  unfold mchoosel, mchoose, mcall, Exec.res_choose_inst, fmap, Exec.res_fmap_inst. cbn.
  apply fin_lookup_enum.
Qed.

Lemma mchoosel_errors {E A} (l : list A) : Exec.errors (mchoosel l : Exec.res E A) = [].
Proof. reflexivity. Qed.

Section Lookup.
Context (tid : nat) (imem : memoryMap) (mem : Memory.t) (ifetch upper : bool) (vpn : pn)
  (tmin_ok tmin_unc tmax : nat).

(** The alternatives contributed by one cached entry. *)
Definition fe_res (row : TLB.FE.t * TLB.Entry.events) : Exec.res string TLB.Result.t :=
  let '(fe, events) := row in
  results ← mlift (TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax);
  mchoosel results.

Lemma lookup_shape cache asid :
  TLB.lookup tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid =
    mchoosel (TLB.get_fes cache (TLB.get_global_Ctxts upper vpn ++ TLB.get_asid_Ctxts upper vpn asid))
      ≫= fe_res.
Proof. reflexivity. Qed.

(** An entry without events contributes neither a result nor an error. *)
Lemma get_result_from_FE_nil fe :
  TLB.get_result_from_FE tid imem mem ifetch vpn fe [] tmin_ok tmin_unc tmax = Ok [].
Proof.
  unfold TLB.get_result_from_FE. case_decide.
  - unfold TLB.get_result_from_table_FE.
    destruct (decide (tmax < tmin_unc)); [reflexivity|].
    destruct (child_lvl (TLB.FE.lvl fe)); [|reflexivity]. cbn.
    rewrite decide_False by assumption. reflexivity.
  - unfold TLB.get_result_from_leaf_FE.
    destruct (decide (tmax < tmin_ok)); [reflexivity|]. cbn.
    rewrite decide_False by assumption. reflexivity.
Qed.

Lemma fe_res_nil fe : Exec.results (fe_res (fe, [])) = [] ∧ Exec.errors (fe_res (fe, [])) = [].
Proof.
  unfold fe_res. rewrite get_result_from_FE_nil. split; reflexivity.
Qed.

Lemma concat_filter_rows {X R} (K : R * TLB.Entry.events → list X) (rows : list (R * TLB.Entry.events)) :
  (∀ r, K (r, []) = []) →
  List.concat (map K rows) = List.concat (map K (filter (λ row, row.2 ≠ []) rows)).
Proof.
  intro Hnil. induction rows as [|[r events] rows IH]; [reflexivity|].
  rewrite filter_cons. case_decide as Hlive; cbn [map List.concat]; rewrite IH; [reflexivity|].
  cbn in Hlive. assert (events = []) as -> by (destruct events; [reflexivity|congruence]).
  rewrite Hnil. reflexivity.
Qed.

Lemma concat_get_fes_perm {X} (H : TLB.FE.t * TLB.Entry.events → list X) a b ctxts :
  (∀ fe, H (fe, []) = []) → equiv a b → unique a → unique b →
  List.concat (map H (TLB.get_fes a ctxts)) ≡ₚ List.concat (map H (TLB.get_fes b ctxts)).
Proof.
  intros Hnil Heq Ha Hb. unfold TLB.get_fes.
  induction ctxts as [|ctxt ctxts IH]; cbn [map List.concat]; [apply Permutation_refl|].
  rewrite !map_app, !List.concat_app. apply Permutation_app; [|exact IH].
  unfold TLB.VATLB.get_fe. rewrite !List.map_map.
  rewrite (concat_filter_rows (λ x, H (let '(entry, events) := x in (existT ctxt entry, events))))
    by (intro; apply Hnil).
  rewrite (concat_filter_rows (λ x, H (let '(entry, events) := x in (existT ctxt entry, events)))
    (TLB.VATLB.get ctxt (TLB.vatlb b))) by (intro; apply Hnil).
  apply VMCacheTraversal.concat_permutation, Permutation_map.
  apply VMBBMTransport.rows_permutation; assumption.
Qed.

(** Simulated caches give the same lookup alternatives and errors, up to order. *)
Theorem lookup_perm a b asid : cache_sim a b →
  Exec.results (TLB.lookup tid imem mem a ifetch upper vpn tmin_ok tmin_unc tmax asid) ≡ₚ
    Exec.results (TLB.lookup tid imem mem b ifetch upper vpn tmin_ok tmin_unc tmax asid) ∧
  Exec.errors (TLB.lookup tid imem mem a ifetch upper vpn tmin_ok tmin_unc tmax asid) ≡ₚ
    Exec.errors (TLB.lookup tid imem mem b ifetch upper vpn tmin_ok tmin_unc tmax asid).
Proof.
  intros [[Heq _] [[_ Ha] [_ Hb]]]. rewrite !lookup_shape.
  rewrite !res_bind_results, !res_bind_errors, !mchoosel_results, !mchoosel_errors, !app_nil_r.
  split; apply concat_get_fes_perm; try assumption; intro fe; apply fe_res_nil.
Qed.

Lemma tlb_lookup_shape ts c asid ttbr0 :
  TState.tlb_lookup tid imem mem (setv TState.tlb (Some c) ts) ifetch upper vpn asid ttbr0
    tmin_ok tmin_unc tmax =
  Exec.merge (TLB.lookup tid imem mem c ifetch upper vpn tmin_ok tmin_unc tmax asid)
    (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin_unc tmax).
Proof. reflexivity. Qed.

(** The thread-level lookup, including uncached invalid roots. *)
Theorem tlb_lookup_perm ts1 ts2 asid ttbr0 : ts_sim ts1 ts2 →
  Exec.results (TState.tlb_lookup tid imem mem ts1 ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) ≡ₚ
    Exec.results (TState.tlb_lookup tid imem mem ts2 ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) ∧
  Exec.errors (TState.tlb_lookup tid imem mem ts1 ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) ≡ₚ
    Exec.errors (TState.tlb_lookup tid imem mem ts2 ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax).
Proof.
  intro Hsim. apply ts_sim_inv in Hsim as (ts & c1 & c2 & -> & -> & Hsim).
  destruct c1 as [a|], c2 as [b|]; cbn in Hsim; try contradiction.
  - rewrite !tlb_lookup_shape. unfold Exec.merge. cbn [Exec.results Exec.errors].
    destruct (lookup_perm a b asid Hsim) as [Hres Herr].
    split; apply Permutation_app_tail; assumption.
  - split; apply Permutation_refl.
Qed.

End Lookup.

(** * Merging is insensitive to the order of alternatives *)

Section MergePerm.
#[local] Existing Instance TLB.Result.Decision_mergeable.
Local Notation lt := TLB.Result.walk_lt.

Lemma walk_lt_cons x w y w' :
  lt (x :: w) (y :: w') = true ↔
  (bv_unsigned x < bv_unsigned y)%Z ∨ (bv_unsigned x = bv_unsigned y ∧ lt w w' = true).
Proof.
  cbn. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y));
    destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)); cbn;
    destruct (lt w w'); split; intuition (try lia; try discriminate).
Qed.

Lemma walk_lt_irrefl w : lt w w = false.
Proof.
  induction w as [|x w IH]; cbn; [reflexivity|].
  rewrite Z.ltb_irrefl, Z.eqb_refl, IH. reflexivity.
Qed.

Lemma walk_lt_trans a b c : lt a b = true → lt b c = true → lt a c = true.
Proof.
  revert b c. induction a as [|x a IH]; intros [|y b] [|z c]; try discriminate; auto.
  intros H1 H2. apply walk_lt_cons in H1, H2. apply walk_lt_cons.
  destruct H1 as [H1|[H1 H1']], H2 as [H2|[H2 H2']]; [left; lia|left; lia|left; lia|].
  right. split; [lia|eauto].
Qed.

Lemma walk_lt_total a b : a = b ∨ lt a b = true ∨ lt b a = true.
Proof.
  revert b. induction a as [|x a IH]; intros [|y b]; auto.
  destruct (Z.lt_trichotomy (bv_unsigned x) (bv_unsigned y)) as [H|[H|H]].
  - right; left; apply walk_lt_cons; left; exact H.
  - destruct (IH b) as [->|[H'|H']].
    + left. f_equal. apply bv_eq. exact H.
    + right; left; apply walk_lt_cons; right; split; [exact H|exact H'].
    + right; right; apply walk_lt_cons; right; split; [lia|exact H'].
  - right; right; apply walk_lt_cons; left; lia.
Qed.

Definition wmin (w1 w2 : list (bv 64)) := if lt w2 w1 then w2 else w1.

Ltac walk_destruct :=
  repeat match goal with
  | |- context [lt ?x ?y] =>
      lazymatch x with context [if _ then _ else _] => fail | _ =>
      lazymatch y with context [if _ then _ else _] => fail | _ =>
        let E := fresh "E" in destruct (lt x y) eqn:E; cbv beta iota end end
  end.

Ltac walk_solve :=
  cbv beta iota;
  repeat match goal with
  | H : lt ?x ?y = false |- _ =>
      lazymatch x with
      | y => clear H
      | _ =>
        let T := fresh in let Hlt := fresh in
        pose proof (walk_lt_total x y) as T;
        destruct T as [T|[Hlt|Hlt]];
        [clear H; subst | rewrite Hlt in H; discriminate H | clear H]
      end
  end;
  repeat match goal with
  | H : lt ?x ?x = true |- _ => rewrite walk_lt_irrefl in H; discriminate H
  | H1 : lt ?x ?y = true, H2 : lt ?y ?z = true |- _ =>
      lazymatch goal with
      | _ : lt x z = true |- _ => fail
      | _ => pose proof (walk_lt_trans _ _ _ H1 H2)
      end
  end;
  first [reflexivity | congruence |
    match goal with |- ?x = ?y =>
      destruct (walk_lt_total x y) as [?|[?|?]]; [assumption|congruence|congruence] end].

Lemma wmin_comm a b : wmin a b = wmin b a.
Proof. unfold wmin. walk_destruct; walk_solve. Qed.

Lemma wmin_assoc a b c : wmin (wmin a b) c = wmin a (wmin b c).
Proof. unfold wmin. walk_destruct; walk_solve. Qed.

Definition key (r : TLB.Result.t) :=
  (list.last (TLB.Result.path r), map TLB.Result.table_attrs (removelast (TLB.Result.path r)),
   TLB.Result.tend r, TLB.Result.inv_time r).

Lemma mergeable_key r' r : TLB.Result.mergeable r' r ↔ key r' = key r.
Proof.
  unfold TLB.Result.mergeable, key. split.
  - intros (H1 & H2 & H3 & H4). f_equal; [f_equal; [f_equal|]|]; assumption.
  - intro H. injection H as H1 H2 H3 H4. auto.
Qed.

Definition comb (a r : TLB.Result.t) :=
  setv TLB.Result.tstart (TLB.Result.tstart a `min` TLB.Result.tstart r)
    (if lt (TLB.Result.walk r) (TLB.Result.walk a) then r else a).

Lemma merge_into_cons r a rs :
  TLB.Result.merge_into r (a :: rs) =
    if decide (TLB.Result.mergeable a r) then comb a r :: rs else a :: TLB.Result.merge_into r rs.
Proof. reflexivity. Qed.

Lemma result_ext r1 r2 :
  TLB.Result.walk r1 = TLB.Result.walk r2 → TLB.Result.tstart r1 = TLB.Result.tstart r2 →
  TLB.Result.tend r1 = TLB.Result.tend r2 → TLB.Result.inv_time r1 = TLB.Result.inv_time r2 →
  r1 = r2.
Proof.
  destruct r1, r2. unfold TLB.Result.walk. cbn. intro Hw. injection Hw as -> ->.
  intros -> -> ->. reflexivity.
Qed.

Lemma comb_walk a r : TLB.Result.walk (comb a r) = wmin (TLB.Result.walk a) (TLB.Result.walk r).
Proof. unfold comb, wmin. destruct (lt _ _); reflexivity. Qed.
Lemma comb_tstart a r : TLB.Result.tstart (comb a r) = TLB.Result.tstart a `min` TLB.Result.tstart r.
Proof. reflexivity. Qed.
Lemma comb_key a r : key a = key r → key (comb a r) = key a.
Proof. intro H. unfold comb. destruct (lt _ _); [exact (eq_sym H)|reflexivity]. Qed.
Lemma comb_tend a r : key a = key r → TLB.Result.tend (comb a r) = TLB.Result.tend a.
Proof. intro H. pose proof (comb_key a r H) as Hk. unfold key in Hk. congruence. Qed.
Lemma comb_inv a r : key a = key r → TLB.Result.inv_time (comb a r) = TLB.Result.inv_time a.
Proof. intro H. pose proof (comb_key a r H) as Hk. unfold key in Hk. congruence. Qed.

Lemma comb_comm a b : key a = key b → comb a b = comb b a.
Proof.
  intro H. apply result_ext.
  - rewrite !comb_walk. apply wmin_comm.
  - rewrite !comb_tstart. lia.
  - rewrite comb_tend, comb_tend by congruence. unfold key in H. congruence.
  - rewrite comb_inv, comb_inv by congruence. unfold key in H. congruence.
Qed.

Lemma comb_swap a x y : key a = key x → key a = key y →
  comb (comb a x) y = comb (comb a y) x.
Proof.
  intros Hx Hy.
  assert (Hax : key (comb a x) = key a) by (apply comb_key, Hx).
  assert (Hay : key (comb a y) = key a) by (apply comb_key, Hy).
  apply result_ext.
  - rewrite !comb_walk. rewrite !wmin_assoc. f_equal. apply wmin_comm.
  - rewrite !comb_tstart. lia.
  - rewrite comb_tend, comb_tend, comb_tend, comb_tend by congruence. reflexivity.
  - rewrite comb_inv, comb_inv, comb_inv, comb_inv by congruence. reflexivity.
Qed.

Fixpoint find_key k (l : list TLB.Result.t) : option TLB.Result.t :=
  match l with
  | [] => None
  | a :: l => if decide (key a = k) then Some a else find_key k l
  end.

Definition gk k (o : option TLB.Result.t) (r : TLB.Result.t) :=
  if decide (key r = k) then Some (match o with None => r | Some a => comb a r end) else o.

Lemma find_merge_into k r acc :
  find_key k (TLB.Result.merge_into r acc) = gk k (find_key k acc) r.
Proof.
  induction acc as [|a acc IH]; [reflexivity|].
  rewrite merge_into_cons. unfold gk.
  destruct (decide (TLB.Result.mergeable a r)) as [Hm|Hm]; apply mergeable_key in Hm || idtac.
  - cbn [find_key]. rewrite comb_key by exact Hm.
    destruct (decide (key a = k)) as [Ha|Ha].
    + rewrite decide_True by congruence. reflexivity.
    + rewrite decide_False by congruence. reflexivity.
  - cbn [find_key]. rewrite IH. unfold gk.
    destruct (decide (key a = k)) as [Ha|Ha]; [|reflexivity].
    rewrite decide_False; [reflexivity|]. intro Hr. apply Hm, mergeable_key. congruence.
Qed.

Lemma find_merge k l acc :
  find_key k (foldl (λ acc r, TLB.Result.merge_into r acc) acc l) = foldl (gk k) (find_key k acc) l.
Proof.
  revert acc. induction l as [|r l IH]; intro acc; [reflexivity|]. cbn. rewrite IH, find_merge_into.
  reflexivity.
Qed.

Definition keyed k (o : option TLB.Result.t) := ∀ a, o = Some a → key a = k.

Lemma gk_keyed k o r : keyed k o → keyed k (gk k o r).
Proof.
  intros Ho a. unfold gk. destruct (decide (key r = k)) as [Hr|Hr]; [|apply Ho].
  intro Ha. injection Ha as <-. destruct o as [b|]; [|exact Hr].
  rewrite comb_key; [apply Ho; reflexivity|]. rewrite (Ho b eq_refl). congruence.
Qed.

Lemma gk_swap k o x y : keyed k o → gk k (gk k o x) y = gk k (gk k o y) x.
Proof.
  intro Ho. unfold gk.
  destruct (decide (key x = k)) as [Hx|Hx], (decide (key y = k)) as [Hy|Hy].
  - destruct o as [a|].
    + f_equal. apply comb_swap; rewrite (Ho a eq_refl); congruence.
    + f_equal. apply comb_comm. congruence.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma gk_perm k l1 l2 o : l1 ≡ₚ l2 → keyed k o → foldl (gk k) o l1 = foldl (gk k) o l2.
Proof.
  intro Hperm. revert o. induction Hperm as [|x l1 l2 _ IH|x y l|l1 l2 l3 _ IH1 _ IH2];
    intros o Ho; cbn [foldl].
  - reflexivity.
  - apply IH, gk_keyed, Ho.
  - rewrite gk_swap by exact Ho. reflexivity.
  - rewrite IH1 by exact Ho. apply IH2, Ho.
Qed.

Lemma merge_into_keys r acc k :
  k ∈ map key (TLB.Result.merge_into r acc) → k ∈ map key acc ∨ k = key r.
Proof.
  induction acc as [|a acc IH].
  - cbn. intro H. apply list_elem_of_singleton in H. right. exact H.
  - rewrite merge_into_cons.
    destruct (decide (TLB.Result.mergeable a r)) as [Hm|Hm]; cbn [map]; intro H;
      apply elem_of_cons in H as [H|H].
    + left. rewrite H, comb_key by (apply mergeable_key, Hm). left.
    + left. right. exact H.
    + left. rewrite H. left.
    + destruct (IH H) as [H'|H']; [left; right; exact H'|right; exact H'].
Qed.

Lemma merge_into_nodup r acc : NoDup (map key acc) → NoDup (map key (TLB.Result.merge_into r acc)).
Proof.
  induction acc as [|a acc IH]; intro Hnd.
  - cbn. constructor; [apply not_elem_of_nil|constructor].
  - rewrite merge_into_cons. cbn [map] in Hnd. apply list.NoDup_cons in Hnd as [Hfresh Hnd].
    destruct (decide (TLB.Result.mergeable a r)) as [Hm|Hm]; cbn [map].
    + rewrite comb_key by (apply mergeable_key, Hm). constructor; assumption.
    + constructor; [|apply IH, Hnd]. intro H. apply merge_into_keys in H as [H|H]; [contradiction|].
      apply Hm, mergeable_key, H.
Qed.

Lemma merge_nodup l acc : NoDup (map key acc) →
  NoDup (map key (foldl (λ acc r, TLB.Result.merge_into r acc) acc l)).
Proof.
  revert acc. induction l as [|r l IH]; intros acc Hacc; [exact Hacc|]. cbn. apply IH, merge_into_nodup, Hacc.
Qed.

Lemma find_key_elem k l x : find_key k l = Some x → x ∈ l.
Proof.
  induction l as [|a l IH]; cbn; [discriminate|].
  destruct (decide (key a = k)); [intro H; injection H as <-; left|intro H; right; apply IH, H].
Qed.

Lemma elem_find_key l x : NoDup (map key l) → x ∈ l → find_key (key x) l = Some x.
Proof.
  induction l as [|a l IH]; intros Hnd Hin; [inversion Hin|].
  cbn [map] in Hnd. apply list.NoDup_cons in Hnd as [Hfresh Hnd]. cbn [find_key].
  apply elem_of_cons in Hin as [->|Hin].
  - rewrite decide_True by reflexivity. reflexivity.
  - rewrite decide_False; [apply IH; assumption|]. intro Heq. apply Hfresh.
    rewrite Heq. apply list_elem_of_fmap. exists x. split; [reflexivity|exact Hin].
Qed.

(** Merging is insensitive to the order of the alternatives, up to the order
    of the merged list. *)
Theorem merge_perm_elem l1 l2 x : l1 ≡ₚ l2 →
  x ∈ TLB.Result.merge l1 → x ∈ TLB.Result.merge l2.
Proof.
  intros Hperm Hin. unfold TLB.Result.merge in *.
  apply (elem_find_key _ _ (merge_nodup l1 [] (NoDup_nil_2))) in Hin.
  rewrite find_merge in Hin. cbn [find_key] in Hin.
  rewrite (gk_perm _ l1 l2 None Hperm) in Hin by discriminate.
  apply (find_key_elem (key x)). rewrite find_merge. exact Hin.
Qed.

Lemma merge_into_nonempty r acc : TLB.Result.merge_into r acc ≠ [].
Proof. destruct acc; cbn; [discriminate|]. case_decide; discriminate. Qed.

Lemma merge_nil l : TLB.Result.merge l = [] ↔ l = [].
Proof.
  unfold TLB.Result.merge. split; [|intros ->; reflexivity].
  destruct l as [|r l]; [reflexivity|]. cbn. intro H. exfalso.
  cut (∀ acc, acc ≠ [] → foldl (λ acc r, TLB.Result.merge_into r acc) acc l ≠ []);
    [intro Hc; exact (Hc _ (merge_into_nonempty r []) H)|].
  clear H. induction l as [|r' l IH]; intros acc Hacc; [exact Hacc|]. cbn.
  apply IH, merge_into_nonempty.
Qed.
End MergePerm.

(** * Instruction and machine states *)

Definition pp_sim (p1 p2 : PPState.t TState.t Ev.t IIS.t) :=
  PPState.mem p1 = PPState.mem p2 ∧ PPState.iis p1 = PPState.iis p2 ∧
  ts_sim (PPState.state p1) (PPState.state p2).

Definition st_sim {n} (s1 s2 : PState.t TState.t Ev.t n) :=
  PState.initmem s1 = PState.initmem s2 ∧ PState.events s1 = PState.events s2 ∧
  ∀ tid, ts_sim (PState.tstate tid s1) (PState.tstate tid s2).

Lemma vimapM_sim {A E n} (R : A → A → Prop) (f : fin n → A → result E A)
    (xs1 xs2 ys1 : vec A n) :
  (∀ i, R (xs1 !!! i) (xs2 !!! i)) →
  (∀ i x1 x2 y1, R x1 x2 → f i x1 = Ok y1 → ∃ y2, f i x2 = Ok y2 ∧ R y1 y2) →
  vimapM f xs1 = Ok ys1 → ∃ ys2, vimapM f xs2 = Ok ys2 ∧ ∀ i, R (ys1 !!! i) (ys2 !!! i).
Proof.
  revert f xs2 ys1. induction xs1 as [|x1 n xs1 IH]; intros f xs2 ys1 Hxs Hf Hmap.
  - inv_vec xs2. try intros _. injection Hmap as <-. exists [#]. split; [reflexivity|].
    intro i. inversion i.
  - inv_vec xs2. intros x2 xs2. try intros Hxs. cbn in Hmap.
    destruct (f 0%fin x1) as [y1|e] eqn:Hy; [|discriminate].
    destruct (vimapM (f ∘ FS) xs1) as [zs1|e] eqn:Hzs; [|discriminate].
    cbn in Hmap. injection Hmap as <-.
    destruct (Hf 0%fin x1 x2 y1 (Hxs 0%fin) Hy) as [y2 [Hy2 Hr]].
    destruct (IH (f ∘ FS) xs2 zs1 (λ i, Hxs (FS i)) (λ i, Hf (FS i)) Hzs) as [zs2 [Hzs2 Hrs]].
    exists (y2 ::: zs2). cbn [vimapM]. rewrite Hy2, Hzs2. split; [reflexivity|].
    intro i. dependent destruction i; [exact Hr|exact (Hrs i)].
Qed.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

(** Promises are delivered to every thread of simulated machine states. *)
Theorem promise_sim ev (s1 s2 s1' : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → PState.promise prom ev s1 = Ok s1' →
  ∃ s2', PState.promise prom ev s2 = Ok s2' ∧ st_sim s1' s2'.
Proof.
  destruct s1 as [states1 imem1 mem1], s2 as [states2 imem2 mem2].
  intros (Himem & Hmem & Hstates). cbn in Himem, Hmem. subst imem2 mem2.
  unfold PState.promise. cbn.
  destruct (vimapM _ states1) as [nts1|err] eqn:Hmap; cbn; [|discriminate].
  injection 1 as <-.
  destruct (vimapM_sim ts_sim _ states1 states2 nts1 Hstates
    (λ i x1 x2 y1 Hx Hy, emit_promise_sim _ _ _ _ x1 x2 y1 Hx Hy) Hmap) as [nts2 [Hmap2 Hnts]].
  rewrite Hmap2. cbn. eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. exact Hnts.
Qed.

(** Fresh instruction events are delivered to the other threads. *)
Theorem broadcast_sim (owner : fin n) imem base extra (states1 states2 states1' : vec TState.t n) :
  (∀ i, ts_sim (states1 !!! i) (states2 !!! i)) →
  PState.broadcast_fresh prom owner imem base extra states1 = Ok states1' →
  ∃ states2', PState.broadcast_fresh prom owner imem base extra states2 = Ok states2' ∧
    ∀ i, ts_sim (states1' !!! i) (states2' !!! i).
Proof.
  intro Hstates. revert states1'. induction extra as [|ev extra IH]; intros states1' Hrun.
  - injection Hrun as <-. exists states2. split; [reflexivity|exact Hstates].
  - cbn [PState.broadcast_fresh] in Hrun |- *.
    destruct (PState.broadcast_fresh prom owner imem base extra states1) as [mid1|err] eqn:Hmid;
      [|discriminate].
    destruct (IH mid1 eq_refl) as [mid2 [-> Hmids]]. cbn [mbind result_bind] in Hrun |- *.
    eapply vimapM_sim; [exact Hmids| |exact Hrun].
    intros i x1 x2 y1 Hx Hy. destruct (decide (i = owner)).
    + injection Hy as <-. exists x2. split; [reflexivity|exact Hx].
    + eapply emit_promise_sim; eassumption.
Qed.

Lemma valid_end_nil (r : result string bool) :
  match r with Ok true => ["BBM violation detected"] | Ok false => [] | Error err => [err] end = [] ↔
  r = Ok false.
Proof. destruct r as [[]|]; split; congruence. Qed.

(** The final break-before-make check succeeds on simulated caches alike,
    given that one of them has ordered histories. *)
Theorem bbm_check_sim imem mem bound ts1 ts2 :
  ts_sim ts1 ts2 → VMCacheState.cache_ok bound ts1 →
  BBM.check imem mem ts1 = Ok false ↔ BBM.check imem mem ts2 = Ok false.
Proof.
  intros Hsim Hok. apply ts_sim_inv in Hsim as (ts & c1 & c2 & -> & -> & Hsim).
  unfold BBM.check. rewrite !tlb_setv.
  destruct c1 as [a|], c2 as [b|]; cbn in Hsim; try contradiction; [|tauto].
  destruct Hsim as [[Heq _] [[_ Ha] [_ Hb]]].
  destruct (Hok a (tlb_setv _ _)) as [Hgood _].
  assert (Hord_a : ∀ fe, VMCacheOrder.ordered (history a fe)) by (intro fe; apply Hgood).
  assert (Hord_b : ∀ fe, VMCacheOrder.ordered (history b fe))
    by (intro fe; rewrite <- (proj2 Heq fe); apply Hgood).
  split; apply VMBBMTransport.check_tlb_equiv; try assumption. apply equiv_sym, Heq.
Qed.

Theorem check_valid_end_sim tid imem mem bound ts1 ts2 :
  ts_sim ts1 ts2 → VMCacheState.cache_ok bound ts1 →
  Promising.check_valid_end prom tid imem ts1 mem = [] ↔
  Promising.check_valid_end prom tid imem ts2 mem = [].
Proof.
  intros Hsim Hok. cbn. destruct bbm; [|tauto].
  etrans; [apply valid_end_nil|]. etrans; [|symmetry; apply valid_end_nil].
  exact (bbm_check_sim imem mem bound ts1 ts2 Hsim Hok).
Qed.

Lemma concat_map_nil_iff {A B} (f g : A → list B) l :
  (∀ x, f x = [] ↔ g x = []) →
  List.concat (map f l) = [] ↔ List.concat (map g l) = [].
Proof.
  intro H. induction l as [|x l IH]; cbn [map List.concat]; [tauto|]. split; intro E.
  - apply app_eq_nil in E as [E1 E2]. rewrite (proj1 (H x) E1), (proj1 IH E2). reflexivity.
  - apply app_eq_nil in E as [E1 E2]. rewrite (proj2 (H x) E1), (proj2 IH E2). reflexivity.
Qed.

(** Reachable machine states bound every thread cache, so the whole final
    validation transfers between simulated reachable states. *)
Theorem state_check_valid_end_sim (s1 s2 : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → VMViews.state_ok s1 →
  PState.check_valid_end prom s1 = [] ↔ PState.check_valid_end prom s2 = [].
Proof.
  intros (Himem & Hmem & Hstates) Hok. unfold PState.check_valid_end.
  apply concat_map_nil_iff. intro tid. unfold PState.check_valid_end_tid.
  rewrite <- Himem, <- Hmem.
  apply (check_valid_end_sim tid _ _ (length (PState.events s1))); [apply Hstates|].
  apply VMViews.ok_cache, Hok.
Qed.
End Machine.

End VMCacheSim.

(** * Outcomes, instructions and machine steps on simulated states *)
Module VMCacheSimOutcome.
Import VMPromising VMCacheSim.
#[local] Typeclasses Transparent view UMPromising.view.

(** * Relational reasoning on executions *)

(** Every successful result of [m1] is matched by a result of [m2]. *)
Definition rsim {St A B} (R : St → St → Prop) (V : A → B → Prop)
    (m1 : Exec.t St string A) (m2 : Exec.t St string B) :=
  ∀ s1 s2 s1' x, R s1 s2 → Exec.elem_of_results (s1', x) (m1 s1) →
    ∃ s2' y, Exec.elem_of_results (s2', y) (m2 s2) ∧ R s1' s2' ∧ V x y.

(** Every error state of [m1] is matched by an error state of [m2]. Messages may differ. *)
Definition eerr {St A B} (R : St → St → Prop)
    (m1 : Exec.t St string A) (m2 : Exec.t St string B) :=
  ∀ s1 s2 s1' e, R s1 s2 → (s1', e) ∈ Exec.errors (m1 s1) →
    ∃ s2' e', (s2', e') ∈ Exec.errors (m2 s2) ∧ R s1' s2'.

Definition esim {St A B} (R : St → St → Prop) (V : A → B → Prop)
    (m1 : Exec.t St string A) (m2 : Exec.t St string B) :=
  rsim R V m1 m2 ∧ eerr R m1 m2.

Lemma errors_bind_elim {St A B} (m : Exec.t St string A) (k : A → Exec.t St string B) s x :
  x ∈ Exec.errors ((m ≫= k) s) →
  x ∈ Exec.errors (m s) ∨ ∃ s' a, Exec.elem_of_results (s', a) (m s) ∧ x ∈ Exec.errors (k a s').
Proof.
  unfold mbind at 1, Exec.mbind_inst. unfold mbind, Exec.res_mbind_inst.
  unfold Exec.elem_of_results, elem_of at 2. destruct (m s) as [l es]. cbn.
  induction l as [|[s' a] l IH]; cbn; [left; exact H|]. intro H.
  unfold Exec.merge at 1 in H. cbn in H. apply elem_of_app in H as [H|H].
  - right. exists s', a. split; [left|exact H].
  - destruct (IH H) as [H'|(s'' & a' & Hin & He)]; [left; exact H'|].
    right. exists s'', a'. split; [right; exact Hin|exact He].
Qed.

Lemma errors_bind_intro_l {St A B} (m : Exec.t St string A) (k : A → Exec.t St string B) s x :
  x ∈ Exec.errors (m s) → x ∈ Exec.errors ((m ≫= k) s).
Proof.
  unfold mbind at 1, Exec.mbind_inst. unfold mbind, Exec.res_mbind_inst.
  destruct (m s) as [l es]. cbn. intro H.
  induction l as [|[s' a] l IH]; cbn; [exact H|].
  unfold Exec.merge at 1. cbn. apply elem_of_app. right. exact IH.
Qed.

Lemma errors_bind_intro_r {St A B} (m : Exec.t St string A) (k : A → Exec.t St string B) s s' a x :
  Exec.elem_of_results (s', a) (m s) → x ∈ Exec.errors (k a s') → x ∈ Exec.errors ((m ≫= k) s).
Proof.
  unfold mbind at 1, Exec.mbind_inst. unfold mbind, Exec.res_mbind_inst.
  unfold Exec.elem_of_results, elem_of at 1. destruct (m s) as [l es]. cbn. intros Hin H.
  induction l as [|[s'' a'] l IH]; cbn; [inversion Hin|].
  unfold Exec.merge at 1. cbn. apply elem_of_app.
  apply elem_of_cons in Hin as [Heq|Hin]; [injection Heq as -> ->; left; exact H|right; apply IH, Hin].
Qed.

Section Esim.
Context {St : Type} (R : St → St → Prop).

Lemma eerr_nil {A B} (m1 : Exec.t St string A) (m2 : Exec.t St string B) :
  (∀ s, Exec.errors (m1 s) = []) → eerr R m1 m2.
Proof. intros Hnil s1 s2 s1' e Hs Hin. rewrite Hnil in Hin. inversion Hin. Qed.

Lemma esim_ret {A B} (V : A → B → Prop) x y : V x y → esim R V (mret x) (mret y).
Proof.
  intro Hv. split; [|apply eerr_nil; reflexivity].
  intros s1 s2 s1' z Hs Hin. apply Exec.elem_of_mret_inv in Hin as [-> ->].
  exists s2, y. split; [apply Exec.elem_of_mret|]. auto.
Qed.

Lemma esim_bind {A1 A2 B1 B2} (V1 : A1 → A2 → Prop) (V : B1 → B2 → Prop) m1 m2 k1 k2 :
  esim R V1 m1 m2 → (∀ x y, V1 x y → esim R V (k1 x) (k2 y)) → esim R V (m1 ≫= k1) (m2 ≫= k2).
Proof.
  intros [Hm He] Hk. split.
  - intros s1 s2 s1' z Hs Hin.
    apply Exec.elem_of_bind_elim in Hin as [mid [x [Hx Hz]]].
    destruct (Hm _ _ _ _ Hs Hx) as [mid2 [y [Hy [Hmid Hv]]]].
    destruct (proj1 (Hk x y Hv) _ _ _ _ Hmid Hz) as [s2' [z' [Hz' [Hs' Hv']]]].
    exists s2', z'. split; [eapply Exec.elem_of_bind_intro; eassumption|auto].
  - intros s1 s2 s1' e Hs Hin. apply errors_bind_elim in Hin as [Hin|(mid & x & Hx & Hin)].
    + destruct (He _ _ _ _ Hs Hin) as [s2' [e' [He' Hs']]].
      exists s2', e'. split; [apply errors_bind_intro_l, He'|exact Hs'].
    + destruct (Hm _ _ _ _ Hs Hx) as [mid2 [y [Hy [Hmid Hv]]]].
      destruct (proj2 (Hk x y Hv) _ _ _ _ Hmid Hin) as [s2' [e' [He' Hs']]].
      exists s2', e'. split; [eapply errors_bind_intro_r; eassumption|exact Hs'].
Qed.

Lemma esim_fmap {A1 A2 B1 B2} (V1 : A1 → A2 → Prop) (V : B1 → B2 → Prop) m1 m2 (f : A1 → B1) (g : A2 → B2) :
  esim R V1 m1 m2 → (∀ x y, V1 x y → V (f x) (g y)) → esim R V (f <$> m1) (g <$> m2).
Proof.
  intros [Hm He] Hf. split.
  - intros s1 s2 s1' z Hs Hin.
    apply Exec.elem_of_fmap_inv in Hin as [x [-> Hx]].
    destruct (Hm _ _ _ _ Hs Hx) as [s2' [y [Hy [Hs' Hv]]]].
    exists s2', (g y). split; [apply Exec.elem_of_fmap_intro, Hy|auto].
  - intros s1 s2 s1' e Hs Hin. exact (He s1 s2 s1' e Hs Hin).
Qed.

Lemma esim_mget {T1 T2} (V : T1 → T2 → Prop) (f : St → T1) (g : St → T2) :
  (∀ s1 s2, R s1 s2 → V (f s1) (g s2)) → esim R V (mget f) (mget g).
Proof.
  intros Hf. split; [|apply eerr_nil; reflexivity].
  intros s1 s2 s1' x Hs Hin. apply Exec.elem_of_mget_inv in Hin as [-> ->].
  exists s2, (g s2). split; [apply Exec.elem_of_mget|auto].
Qed.

Lemma esim_mset {T} (p : St → T) `{Setter St T p} f1 f2 :
  (∀ s1 s2, R s1 s2 → R (set p f1 s1) (set p f2 s2)) → esim R eq (mset p f1) (mset p f2).
Proof.
  intros Hf. split; [|apply eerr_nil; reflexivity].
  intros s1 s2 s1' x Hs Hin. destruct x. apply Exec.elem_of_mset_inv in Hin as ->.
  exists (set p f2 s2), (). split; [apply Exec.elem_of_mset|auto].
Qed.

Lemma errors_guard_discard {P} `{Decision P} s :
  Exec.errors ((guard_discard P : Exec.t St string P) s) = [].
Proof. unfold guard_discard. destruct (decide P); reflexivity. Qed.

Lemma esim_guard_discard {P1 P2} `{Decision P1} `{Decision P2} :
  (P1 → P2) → esim R (λ _ _, True) (guard_discard P1) (guard_discard P2).
Proof.
  intros HP. split; [|apply eerr_nil, errors_guard_discard].
  intros s1 s2 s1' p Hs Hin. apply Exec.elem_of_guard_discard_inv in Hin as ->.
  destruct (Exec.elem_of_guard_discard (E := string) s2 (HP p)) as [q Hq].
  exists s2, q. auto.
Qed.

Lemma esim_guard_discard' {P1 P2} `{Decision P1} `{Decision P2} :
  (P1 → P2) → esim R eq (guard_discard' P1) (guard_discard' P2).
Proof.
  intros HP. split.
  - intros s1 s2 s1' u Hs Hin. destruct u.
    pose proof (Exec.elem_of_guard_discard_unit_prop _ _ Hin) as Hp.
    apply Exec.elem_of_guard_discard_unit_inv in Hin as ->.
    exists s2, (). split; [apply Exec.elem_of_guard_discard_unit, HP, Hp|auto].
  - apply eerr_nil. intro s. try unfold guard_discard'. unfold guard_discard.
    destruct (decide P1); reflexivity.
Qed.

Lemma esim_guard_or {P1 P2} `{Decision P1} `{Decision P2} (e1 e2 : string) :
  (P1 → P2) → (P2 → P1) → esim R (λ _ _, True) (guard_or e1 P1) (guard_or e2 P2).
Proof.
  intros HP HQ. split.
  - intros s1 s2 s1' p Hs Hin. pose proof Hin as Hp.
    apply Exec.elem_of_guard_or_inv in Hin as ->.
    destruct (Exec.elem_of_guard_or s2 e2 (HP p)) as [q Hq].
    exists s2, q. auto.
  - intros s1 s2 s1' e Hs Hin. unfold guard_or in Hin |- *.
    destruct (decide P1) as [p|Hn]; [inversion Hin|].
    destruct (decide P2) as [q|Hq]; [exfalso; apply Hn, HQ, q|].
    apply list_elem_of_singleton in Hin. injection Hin as -> ->.
    exists s2, e2. split; [left|exact Hs].
Qed.

Lemma esim_throw {A B} (V : A → B → Prop) (e1 e2 : string) :
  esim R V (mthrow e1 : Exec.t St string A) (mthrow e2 : Exec.t St string B).
Proof.
  split.
  - intros s1 s2 s1' x Hs Hin. unfold elem_of, Exec.elem_of_results in Hin. cbn in Hin. inversion Hin.
  - intros s1 s2 s1' e Hs Hin. apply list_elem_of_singleton in Hin. injection Hin as -> ->.
    exists s2, e2. split; [left|exact Hs].
Qed.

Lemma esim_discard {A B} (V : A → B → Prop) m2 : esim R V (mdiscard : Exec.t St string A) m2.
Proof.
  split.
  - intros s1 s2 s1' x Hs Hin. rewrite Exec.mdiscard_eq in Hin.
    unfold elem_of, Exec.elem_of_results in Hin. cbn in Hin. inversion Hin.
  - intros s1 s2 s1' e Hs Hin. rewrite Exec.mdiscard_eq in Hin. inversion Hin.
Qed.

Lemma esim_mchoosel {A} (l1 l2 : list A) :
  (∀ x, x ∈ l1 → x ∈ l2) → esim R eq (mchoosel l1) (mchoosel l2).
Proof.
  intros Hl. split; [|apply eerr_nil; reflexivity].
  intros s1 s2 s1' x Hs Hin. apply Exec.elem_of_mchoosel_inv in Hin as [-> Hx].
  exists s2, x. split; [apply Exec.elem_of_mchoosel, Hl, Hx|auto].
Qed.

Lemma esim_mchoose n : esim R eq (mchoose n) (mchoose n).
Proof.
  split; [|apply eerr_nil; reflexivity].
  intros s1 s2 s1' x Hs Hin. apply Exec.elem_of_mchoose_inv in Hin as ->.
  exists s2, x. split; [apply Exec.elem_of_mchoose|auto].
Qed.

Lemma esim_lift_result {A B} (V : A → B → Prop) (r1 : result string A) (r2 : result string B) :
  (∀ x, r1 = Ok x → ∃ y, r2 = Ok y ∧ V x y) → (∀ e, r1 = Error e → ∃ e', r2 = Error e') →
  esim R V (mlift r1) (mlift r2).
Proof.
  intros Hr He. destruct r1 as [x|e].
  - destruct (Hr x eq_refl) as [y [-> Hv]].
    exact (esim_ret V x y Hv).
  - destruct (He e eq_refl) as [e' ->]. apply esim_throw.
Qed.

Lemma esim_lift_res {A B} (V : A → B → Prop) (r1 : Exec.res string A) (r2 : Exec.res string B) :
  (∀ x, Exec.elem_of_results x r1 → ∃ y, Exec.elem_of_results y r2 ∧ V x y) →
  (∀ e, e ∈ Exec.errors r1 → ∃ e', e' ∈ Exec.errors r2) →
  esim R V (mlift r1) (mlift r2).
Proof.
  intros Hr He. split.
  - intros s1 s2 s1' x Hs Hin. apply Exec.elem_of_lift_res_inv in Hin as [-> Hx].
    destruct (Hr x Hx) as [y [Hy Hv]]. exists s2, y. split; [apply Exec.elem_of_lift_res, Hy|auto].
  - intros s1 s2 s1' e Hs Hin. change ((s1', e) ∈ map (s1,.) (Exec.errors r1)) in Hin.
    apply list_elem_of_fmap in Hin as [e0 [Heq Hin]]. injection Heq as -> ->.
    destruct (He e0 Hin) as [e' He']. exists s2, e'. split; [|exact Hs].
    change ((s2, e') ∈ map (s2,.) (Exec.errors r2)). apply list_elem_of_fmap. eauto.
Qed.

Lemma esim_othrow {A B} (V : A → B → Prop) (e1 e2 : string) (o1 : option A) (o2 : option B) :
  (∀ x, o1 = Some x → ∃ y, o2 = Some y ∧ V x y) → (o1 = None → o2 = None) →
  esim R V (othrow e1 o1) (othrow e2 o2).
Proof.
  intros Ho Hn. destruct o1 as [x|].
  - destruct (Ho x eq_refl) as [y [-> Hv]]. apply esim_ret, Hv.
  - rewrite (Hn eq_refl). apply esim_throw.
Qed.
End Esim.

Lemma esim_liftSt {St St' A B} (R : St → St → Prop) (R' : St' → St' → Prop) (V : A → B → Prop)
    (g : St → St') `{Setter St St' g} m1 m2 :
  (∀ s1 s2, R s1 s2 → R' (g s1) (g s2)) →
  (∀ s1 s2 t1 t2, R s1 s2 → R' t1 t2 → R (setv g t1 s1) (setv g t2 s2)) →
  esim R' V m1 m2 → esim R V (Exec.liftSt g m1) (Exec.liftSt g m2).
Proof.
  intros Hg Hset [Hm He]. split.
  - intros s1 s2 s1' x Hs Hin.
    apply Exec.elem_of_liftSt_inv in Hin as [t1 [-> Hin]].
    destruct (Hm _ _ _ _ (Hg _ _ Hs) Hin) as [t2 [y [Hy [Ht Hv]]]].
    exists (setv g t2 s2), y. split; [apply Exec.elem_of_liftSt, Hy|]. split; [apply Hset; assumption|exact Hv].
  - intros s1 s2 s1' e Hs Hin.
    change ((s1', e) ∈ map (λ '(st, a), (setv g st s1, a)) (Exec.errors (m1 (g s1)))) in Hin.
    apply list_elem_of_fmap in Hin as [[t1 e0] [Heq Hin]]. injection Heq as -> ->.
    destruct (He _ _ _ _ (Hg _ _ Hs) Hin) as [t2 [e' [He' Ht]]].
    exists (setv g t2 s2), e'. split; [|apply Hset; assumption].
    change ((setv g t2 s2, e') ∈ map (λ '(st, a), (setv g st s2, a)) (Exec.errors (m2 (g s2)))).
    apply list_elem_of_fmap. exists (t2, e'). split; [reflexivity|exact He'].
Qed.

(** * Frame lemmas for thread-state updates *)

Lemma ts_sim_by_frame x y :
  setv TState.tlb None x = setv TState.tlb None y → tlb_sim (TState.tlb x) (TState.tlb y) →
  ts_sim x y.
Proof.
  intros Hframe Hsim. split; [|exact Hsim].
  transitivity (setv TState.tlb (TState.tlb y) (setv TState.tlb None y)).
  - rewrite setv_tlb_twice. symmetry. apply setv_tlb_same.
  - rewrite <- Hframe, setv_tlb_twice. reflexivity.
Qed.

Lemma update_cohs_setv avs c t :
  TState.update_cohs avs (setv TState.tlb c t) = setv TState.tlb c (TState.update_cohs avs t).
Proof.
  unfold TState.update_cohs. induction avs as [|[a v] avs IH]; [reflexivity|].
  cbn [foldr]. rewrite IH. reflexivity.
Qed.

Lemma update_tcohs_setv asid pos v c t :
  TState.update_tcohs asid pos v (setv TState.tlb c t) =
    setv TState.tlb c (TState.update_tcohs asid pos v t).
Proof.
  unfold TState.update_tcohs. induction pos as [|po pos IH]; [reflexivity|].
  cbn [foldr]. rewrite IH. reflexivity.
Qed.

Lemma set_fwdbs_setv addrs n (data : bv n) time vdata xcl c t :
  TState.set_fwdbs addrs data time vdata xcl (setv TState.tlb c t) =
    setv TState.tlb c (TState.set_fwdbs addrs data time vdata xcl t).
Proof.
  unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)) as l. intro l.
  revert t. induction l as [|[a b] l IH]; intro t; [reflexivity|]. cbn [foldl].
  rewrite <- IH. reflexivity.
Qed.

Lemma set_reg_setv r rv c t :
  TState.set_reg r rv (setv TState.tlb c t) = setv TState.tlb c <$> TState.set_reg r rv t.
Proof.
  unfold TState.set_reg. change (TState.regs (setv TState.tlb c t)) with (TState.regs t).
  destruct (decide _); reflexivity.
Qed.

Lemma state_set_state f (p : PPState.t TState.t Ev.t IIS.t) :
  PPState.state (set PPState.state f p) = f (PPState.state p).
Proof. reflexivity. Qed.

Ltac frame_rw :=
  rewrite ?state_set_state; cbn [PPState.state];
  rewrite ?update_cohs_setv, ?update_tcohs_setv, ?set_fwdbs_setv.

Definition pr_sim (a b : TState.t * IIS.t) := ts_sim a.1 b.1 ∧ a.2 = b.2.

Ltac ts_frame Hd :=
  apply ts_sim_by_frame;
  [frame_rw; reflexivity
  |frame_rw; first [exact Hd|match goal with H : tlb_sim _ _ |- _ => exact H end]].

(** Discharge state obligations of instruction-level relational steps. *)
Ltac pp_solve :=
  let s1 := fresh "s1" in let s2 := fresh "s2" in let Hs := fresh "Hs" in
  intros s1 s2 Hs;
  lazymatch type of Hs with
  | pp_sim _ _ =>
      let a1 := fresh "a" in let m1 := fresh "m" in let i1 := fresh "i" in
      let a2 := fresh "a" in let m2 := fresh "m" in let i2 := fresh "i" in
      let Hm := fresh "Hm" in let Hi := fresh "Hi" in let Ha := fresh "Ha" in
      destruct s1 as [a1 m1 i1], s2 as [a2 m2 i2], Hs as (Hm & Hi & Ha);
      cbn [PPState.mem PPState.iis PPState.state] in Hm, Hi, Ha; subst m2 i2;
      let u := fresh "u" in let d1 := fresh "d" in let d2 := fresh "d" in let Hd := fresh "Hd" in
      apply ts_sim_inv in Ha as (u & d1 & d2 & -> & -> & Hd);
      first
        [ reflexivity
        | apply ts_sim_setv; exact Hd
        | split; [reflexivity|split; [reflexivity|]]; ts_frame Hd ]
  | pr_sim _ _ =>
      let a1 := fresh "a" in let i1 := fresh "i" in
      let a2 := fresh "a" in let i2 := fresh "i" in
      let Hi := fresh "Hi" in let Ha := fresh "Ha" in
      destruct s1 as [a1 i1], s2 as [a2 i2], Hs as [Ha Hi];
      cbn [fst snd] in Hi, Ha; subst i2;
      let u := fresh "u" in let d1 := fresh "d" in let d2 := fresh "d" in let Hd := fresh "Hd" in
      apply ts_sim_inv in Ha as (u & d1 & d2 & -> & -> & Hd);
      first
        [ reflexivity
        | apply ts_sim_setv; exact Hd
        | split; [ts_frame Hd|reflexivity] ]
  | ts_sim _ _ =>
      let u := fresh "u" in let d1 := fresh "d" in let d2 := fresh "d" in let Hd := fresh "Hd" in
      apply ts_sim_inv in Hs as (u & d1 & d2 & -> & -> & Hd);
      first
        [ reflexivity
        | apply ts_sim_setv; exact Hd
        | ts_frame Hd ]
  end.

Ltac esim_post H :=
  lazymatch type of H with
  | ts_sim ?x ?y =>
      let t := fresh "t" in let c1 := fresh "c" in let c2 := fresh "c" in let Hc := fresh "Hc" in
      apply ts_sim_inv in H as (t & c1 & c2 & -> & -> & Hc)
  | ?x = ?y => subst y
  | True => clear H
  | _ => idtac
  end.

Lemma esim_get_state :
  esim pp_sim ts_sim (mget PPState.state) (mget PPState.state).
Proof. apply esim_mget. intros s1 s2 (_ & _ & H). exact H. Qed.
Lemma esim_get_fst : esim pr_sim ts_sim (mget fst) (mget fst).
Proof. apply esim_mget. intros s1 s2 [H _]. exact H. Qed.
Lemma esim_get_ts : esim ts_sim ts_sim mGet mGet.
Proof.
  split; [|apply eerr_nil; reflexivity].
  intros s1 s2 s1' x Hs Hin. apply Exec.elem_of_mGet_inv in Hin as [-> ->].
  exists s2, s2. split; [apply Exec.elem_of_mGet|auto].
Qed.

Lemma esim_refl {St A} (m : Exec.t St string A) : esim eq eq m m.
Proof.
  split; [intros s1 s2 s1' x <- Hin; exists s1', x; auto|].
  intros s1 s2 s1' e <- Hin. exists s1', e. auto.
Qed.

Lemma esim_liftSt_mem {A} (m : Exec.t Memory.t string A) :
  esim pp_sim eq (Exec.liftSt PPState.mem m) (Exec.liftSt PPState.mem m).
Proof.
  apply (esim_liftSt _ eq); [intros s1 s2 (Hm & _ & _); exact Hm| |apply esim_refl].
  intros [a1 m1 i1] [a2 m2 i2] t1 t2 (Hm & Hi & Ha) <-. cbn in Hm, Hi, Ha. subst.
  split; [reflexivity|]. split; [reflexivity|exact Ha].
Qed.

Ltac ts_norm :=
  repeat match goal with
  | |- context [TState.prom_wr (setv TState.tlb ?c ?t)] =>
      change (TState.prom_wr (setv TState.tlb c t)) with (TState.prom_wr t)
  | |- context [TState.prom_tlbi (setv TState.tlb ?c ?t)] =>
      change (TState.prom_tlbi (setv TState.tlb c t)) with (TState.prom_tlbi t)
  | |- context [TState.xclb (setv TState.tlb ?c ?t)] =>
      change (TState.xclb (setv TState.tlb c t)) with (TState.xclb t)
  | |- context [TState.dsb_epoch (setv TState.tlb ?c ?t)] =>
      change (TState.dsb_epoch (setv TState.tlb c t)) with (TState.dsb_epoch t)
  end.

(** A failing cache operation fails on a simulated state too: success on
    the simulated state would transfer back. *)
Lemma result_error_sim {A} (r1 r2 : result string A) :
  (∀ x, r2 = Ok x → ∃ y, r1 = Ok y) → ∀ e, r1 = Error e → ∃ e', r2 = Error e'.
Proof.
  intros Hback e He. destruct r2 as [x|e']; [|eauto].
  destruct (Hback x eq_refl) as [y Hy]. congruence.
Qed.

Lemma process_event_error_sim tid imem mem ev a b e :
  ts_sim a b → TState.process_event tid imem mem ev a = Error e →
  ∃ e', TState.process_event tid imem mem ev b = Error e'.
Proof.
  intro Hs. apply result_error_sim. intros x Hx.
  destruct (process_event_sim tid imem mem ev b a x (ts_sim_sym _ _ Hs) Hx) as [y [Hy _]]. eauto.
Qed.

Lemma cse_error_sim imem mem tid v a b e :
  ts_sim a b → TState.cse imem mem tid v a = Error e →
  ∃ e', TState.cse imem mem tid v b = Error e'.
Proof.
  intro Hs. apply result_error_sim. intros x Hx.
  destruct (cse_sim imem mem tid v b a x (ts_sim_sym _ _ Hs) Hx) as [y [Hy _]]. eauto.
Qed.

Lemma add_wsreg_error_sim tid imem mem sreg val v a b e :
  ts_sim a b → TState.add_wsreg tid imem mem sreg val v a = Error e →
  ∃ e', TState.add_wsreg tid imem mem sreg val v b = Error e'.
Proof.
  intro Hs. apply result_error_sim. intros x Hx.
  destruct (add_wsreg_sim tid imem mem sreg val v b a x (ts_sim_sym _ _ Hs) Hx) as [y [Hy _]]. eauto.
Qed.

Ltac esim_tlb_op :=
  let H := fresh in
  first
  [ apply (esim_lift_result _ ts_sim);
      [intros ? H; eapply process_event_sim; [apply ts_sim_setv; eassumption|exact H]
      |intros ? H; eapply process_event_error_sim; [apply ts_sim_setv; eassumption|exact H]]
  | apply (esim_lift_result _ ts_sim);
      [intros ? H; eapply cse_sim; [apply ts_sim_setv; eassumption|exact H]
      |intros ? H; eapply cse_error_sim; [apply ts_sim_setv; eassumption|exact H]]
  | apply (esim_lift_result _ ts_sim);
      [intros ? H; eapply add_wsreg_sim; [apply ts_sim_setv; eassumption|exact H]
      |intros ? H; eapply add_wsreg_error_sim; [apply ts_sim_setv; eassumption|exact H]] ].

Lemma esim_msetv {St T} (R : St → St → Prop) (p : St → T) `{Setter St T p} v1 v2 :
  (∀ s1 s2, R s1 s2 → R (set p (λ _, v1) s1) (set p (λ _, v2) s2)) →
  esim R eq (msetv p v1) (msetv p v2).
Proof. apply esim_mset. Qed.

Lemma esim_guard_or_refl {St} (R : St → St → Prop) (e : string) P `{Decision P} :
  esim R eq (guard_or e P : Exec.t St string P) (guard_or e P).
Proof.
  unfold guard_or. destruct (decide P) as [q|].
  - apply esim_ret. reflexivity.
  - apply esim_throw.
Qed.

Lemma esim_throw_bind {St A1 A2 B C} (R : St → St → Prop) (V : B → C → Prop) (e1 e2 : string)
    (k1 : A1 → Exec.t St string B) (k2 : A2 → Exec.t St string C) :
  esim R V (mthrow e1 ≫= k1) (mthrow e2 ≫= k2).
Proof. apply (esim_bind _ (λ _ _, False)); [apply esim_throw|intros ? ? []]. Qed.

Lemma esim_discard_bind {St A B C} (R : St → St → Prop) (V : B → C → Prop)
    (k : A → Exec.t St string B) (m2 : Exec.t St string C) :
  esim R V (mdiscard ≫= k) m2.
Proof.
  split.
  - intros s1 s2 s1' x Hs Hin. apply Exec.elem_of_bind_elim in Hin as [? [? [Hin _]]].
    rewrite Exec.mdiscard_eq in Hin. unfold elem_of, Exec.elem_of_results in Hin. cbn in Hin.
    inversion Hin.
  - intros s1 s2 s1' e Hs Hin. apply errors_bind_elim in Hin as [Hin|(? & ? & Hin & _)];
      rewrite Exec.mdiscard_eq in Hin; [inversion Hin|].
    unfold elem_of, Exec.elem_of_results in Hin. cbn in Hin. inversion Hin.
Qed.

Lemma set_reg_sim r rv a b x : ts_sim a b → TState.set_reg r rv a = Some x →
  ∃ y, TState.set_reg r rv b = Some y ∧ ts_sim x y.
Proof.
  intros Hs. apply ts_sim_inv in Hs as (t & c1 & c2 & -> & -> & Hc).
  rewrite !set_reg_setv. destruct (TState.set_reg r rv t) as [u|]; cbn; [|discriminate].
  intro H. injection H as <-. eexists. split; [reflexivity|]. apply ts_sim_setv, Hc.
Qed.

Lemma set_reg_none_sim r rv a b : ts_sim a b → TState.set_reg r rv a = None →
  TState.set_reg r rv b = None.
Proof.
  intros Hs. apply ts_sim_inv in Hs as (t & c1 & c2 & -> & -> & Hc).
  rewrite !set_reg_setv. destruct (TState.set_reg r rv t); cbn; [discriminate|reflexivity].
Qed.

Lemma ets_setv_eq c1 c2 t : tlb_sim c1 c2 →
  TState.ets2 (setv TState.tlb c2 t) = TState.ets2 (setv TState.tlb c1 t) ∧
  TState.ets3 (setv TState.tlb c2 t) = TState.ets3 (setv TState.tlb c1 t).
Proof.
  intro Hc. destruct (ts_sim_ets _ _ (ts_sim_setv t c1 c2 Hc)) as [H2 H3]. auto.
Qed.

Ltac ets_norm :=
  repeat match goal with
  | H : tlb_sim ?c1 ?c2 |- context [TState.ets2 (setv TState.tlb ?c2 ?t)] =>
      rewrite (proj1 (ets_setv_eq c1 c2 t H))
  | H : tlb_sim ?c1 ?c2 |- context [TState.ets3 (setv TState.tlb ?c2 ?t)] =>
      rewrite (proj2 (ets_setv_eq c1 c2 t H))
  end.

Ltac esim_extra := fail.

Ltac esim_base :=
  lazymatch goal with
  | |- esim _ _ (othrow _ (TState.set_reg _ _ _)) _ =>
      let H := fresh in apply (esim_othrow _ ts_sim);
        [intros ? H; eapply set_reg_sim; [apply ts_sim_setv; eassumption|exact H]
        |intro H; eapply set_reg_none_sim; [apply ts_sim_setv; eassumption|exact H]]
  | |- esim _ _ (mget PPState.state) _ => apply esim_get_state
  | |- esim _ _ (mget fst) _ => apply esim_get_fst
  | |- esim _ _ mGet _ => apply esim_get_ts
  | |- esim _ _ (mget _) _ => apply (esim_mget _ eq); pp_solve
  | |- esim _ _ (Exec.liftSt PPState.mem _) _ => apply esim_liftSt_mem
  | |- esim _ _ (mlift (TState.process_event _ _ _ _ _)) _ => esim_tlb_op
  | |- esim _ _ (mlift (TState.cse _ _ _ _ _)) _ => esim_tlb_op
  | |- esim _ _ (mlift (TState.add_wsreg _ _ _ _ _ _ _)) _ => esim_tlb_op
  | |- esim _ _ (mlift _) _ =>
      let H := fresh in apply (esim_lift_result _ eq);
        [intros ? H; eexists; split; [exact H|reflexivity]|intros ? H; eexists; exact H]
  | |- esim _ _ (mret _) _ => apply (esim_ret _ eq); reflexivity
  | |- esim _ _ (guard_discard _) _ => apply esim_guard_discard; exact (λ H, H)
  | |- esim _ _ (guard_discard' _) _ => apply esim_guard_discard'; exact (λ H, H)
  | |- esim _ _ (guard_or ?e ?P) (guard_or ?e ?P) => apply esim_guard_or_refl
  | |- esim _ _ (guard_or _ _) _ => apply esim_guard_or; exact (λ H, H)
  | |- esim _ _ (mchoosel _) _ => apply esim_mchoosel; exact (λ _ H, H)
  | |- esim _ _ (mchoose _) _ => apply esim_mchoose
  | |- esim _ _ (mset _ _) _ => apply esim_mset; pp_solve
  | |- esim _ _ (msetv _ _) _ => apply esim_msetv; pp_solve
  | |- esim _ _ (mthrow _) _ => apply esim_throw
  | |- esim _ _ mdiscard _ => apply esim_discard
  | |- esim _ _ (othrow _ _) _ =>
      let H := fresh in apply (esim_othrow _ eq);
        [intros ? H; eexists; split; [exact H|reflexivity]|exact (λ H, H)]
  end.

Ltac esim_prim := first [esim_extra | esim_base].

Ltac esim_destr :=
  repeat match goal with
  | |- context [match ?p with pair _ _ => _ end] => is_var p; destruct p
  end.

Ltac esim_one :=
  (ts_norm; ets_norm;
    lazymatch goal with
    | |- esim _ _ (mthrow _ ≫= _) (mthrow _ ≫= _) => apply esim_throw_bind
    | |- esim _ _ (mdiscard ≫= _) _ => apply esim_discard_bind
    | |- esim _ _ ((_ ≫= _) ≫= _) _ =>
        eapply (esim_bind _ eq); [solve [repeat esim_one]|intros ? ? <-]
    | |- esim _ _ ((match ?b with _ => _ end) ≫= _) ((match ?b' with _ => _ end) ≫= _) =>
        first [constr_eq b b' | change b' with b];
        let E := fresh "E" in destruct b eqn:E
    | |- esim _ _ (match ?b with _ => _ end) (match ?b' with _ => _ end) =>
        first [constr_eq b b' | change b' with b];
        let E := fresh "E" in destruct b eqn:E
    | |- esim _ _ ((match ?b with _ => _ end) ≫= _) _ => let E := fresh "E" in destruct b eqn:E
    | |- esim _ _ (match ?b with _ => _ end) _ => let E := fresh "E" in destruct b eqn:E
    | |- esim _ _ (_ ≫= _) (_ ≫= _) =>
        eapply esim_bind; [esim_prim|let x := fresh "x" in let y := fresh "y" in let H := fresh "Hxy" in
                           intros x y H; esim_post H]
    | |- esim _ _ (_ <$> _) (_ <$> _) => eapply esim_fmap; [|intros ? ? <-; reflexivity]
    | |- esim _ _ _ _ => esim_prim
    end; cbv beta iota zeta; esim_destr).
Ltac esim_run := repeat esim_one.
Ltac esim_step := esim_one.

Lemma esim_liftSt_fst {A B} (V : A → B → Prop) m1 m2 :
  esim ts_sim V m1 m2 → esim pr_sim V (Exec.liftSt fst m1) (Exec.liftSt fst m2).
Proof.
  apply esim_liftSt; [intros s1 s2 [H _]; exact H|].
  intros [a1 i1] [a2 i2] t1 t2 [_ Hi] Ht. split; [exact Ht|exact Hi].
Qed.

Lemma esim_liftSt_pp {A B} (V : A → B → Prop) m1 m2 :
  esim pr_sim V m1 m2 →
  esim pp_sim V (Exec.liftSt (PPState.state ×× PPState.iis) m1)
    (Exec.liftSt (PPState.state ×× PPState.iis) m2).
Proof.
  apply esim_liftSt.
  - intros [a1 m1' i1] [a2 m2' i2] (Hm & Hi & Ha). split; [exact Ha|exact Hi].
  - intros [a1 m1' i1] [a2 m2' i2] [t1 j1] [t2 j2] (Hm & Hi & Ha) [Ht Hj].
    split; [exact Hm|]. split; [exact Hj|exact Ht].
Qed.

Lemma esim_foldlM2 {St A B} (R : St → St → Prop) (f1 f2 : A → B → Exec.t St string A) acc l :
  (∀ acc x, esim R eq (f1 acc x) (f2 acc x)) → esim R eq (foldlM f1 acc l) (foldlM f2 acc l).
Proof.
  intro Hf. revert acc. induction l as [|x l IH]; intro acc; cbn [foldlM]; [apply esim_ret; reflexivity|].
  apply (esim_bind _ eq); [apply Hf|]. intros ? ? <-. apply IH.
Qed.

Section Handlers.
Context (n_threads tid : nat) (imem : memoryMap).

Lemma run_cse_sim vmax : esim pp_sim eq (run_cse tid imem vmax) (run_cse tid imem vmax).
Proof. unfold run_cse. esim_run. Qed.

Lemma run_barrier_sim barrier vmax :
  esim pp_sim eq (run_barrier tid imem barrier vmax) (run_barrier tid imem barrier vmax).
Proof.
  unfold run_barrier. esim_step.
  destruct barrier as [dmb|dsb|[]| | | ]; try destruct (DxB_types dmb); try destruct (DxB_types dsb);
    try apply run_cse_sim; esim_run.
Qed.

Lemma run_take_exception_sim fault vmax :
  esim pp_sim eq (run_take_exception tid imem fault vmax) (run_take_exception tid imem fault vmax).
Proof. unfold run_take_exception. esim_step. destruct x; apply run_cse_sim. Qed.

Lemma read_pte_sim : esim pp_sim eq read_pte read_pte.
Proof. unfold read_pte. esim_run. Qed.

Lemma read_mem_explicit_sim addr size macc :
  esim pp_sim eq (read_mem_explicit imem addr size macc) (read_mem_explicit imem addr size macc).
Proof. unfold read_mem_explicit. esim_run. Qed.

Lemma write_mem_sim addr size macc data :
  esim pp_sim eq (write_mem tid imem addr size macc data) (write_mem tid imem addr size macc data).
Proof. unfold write_mem. esim_run. Qed.

Lemma materialize_sim vpre tlbi recipient :
  esim pp_sim eq (materialize_tlbi_for_recipient tid imem vpre tlbi recipient)
    (materialize_tlbi_for_recipient tid imem vpre tlbi recipient).
Proof. unfold materialize_tlbi_for_recipient. esim_run. Qed.

Lemma run_reg_write_sim reg racc val :
  esim pp_sim eq (run_reg_write tid imem reg racc val) (run_reg_write tid imem reg racc val).
Proof. unfold run_reg_write. esim_run. Qed.

Lemma read_sreg_indirect_sim reg racc :
  esim pr_sim eq (read_sreg_indirect reg racc) (read_sreg_indirect reg racc).
Proof. unfold read_sreg_indirect. esim_run. Qed.

Lemma run_reg_trans_read_sim reg racc trs :
  esim ts_sim eq (run_reg_trans_read reg racc trs) (run_reg_trans_read reg racc trs).
Proof. unfold run_reg_trans_read. esim_run. Qed.

Ltac esim_extra ::=
  lazymatch goal with
  | |- esim _ _ (Exec.liftSt fst (run_reg_trans_read _ _ _)) _ =>
      apply esim_liftSt_fst, run_reg_trans_read_sim
  | |- esim _ _ (read_sreg_indirect _ _) _ => apply read_sreg_indirect_sim
  | |- esim _ _ (Exec.liftSt (PPState.state ×× PPState.iis) (read_sreg_indirect _ _)) _ =>
      apply esim_liftSt_pp, read_sreg_indirect_sim
  | |- esim _ _ (materialize_tlbi_for_recipient _ _ _ _ _) _ => apply materialize_sim
  | |- esim _ _ (foldlM _ _ _) _ =>
      apply esim_foldlM2; intros [[? ?] ?] ?; cbv beta iota zeta
  end.

Lemma run_reg_general_read_sim reg racc :
  esim pr_sim eq (run_reg_general_read reg racc) (run_reg_general_read reg racc).
Proof. unfold run_reg_general_read. esim_run. Qed.

Ltac esim_extra ::=
  lazymatch goal with
  | |- esim _ _ (Exec.liftSt fst (run_reg_trans_read _ _ _)) _ =>
      apply esim_liftSt_fst, run_reg_trans_read_sim
  | |- esim _ _ (run_reg_general_read _ _) _ => apply run_reg_general_read_sim
  | |- esim _ _ (read_sreg_indirect _ _) _ => apply read_sreg_indirect_sim
  | |- esim _ _ (Exec.liftSt (PPState.state ×× PPState.iis) (read_sreg_indirect _ _)) _ =>
      apply esim_liftSt_pp, read_sreg_indirect_sim
  | |- esim _ _ (materialize_tlbi_for_recipient _ _ _ _ _) _ => apply materialize_sim
  | |- esim _ _ (foldlM _ _ _) _ =>
      apply esim_foldlM2; intros [[? ?] ?] ?; cbv beta iota zeta
  end.

Lemma run_reg_read_sim reg racc :
  esim pr_sim eq (run_reg_read reg racc) (run_reg_read reg racc).
Proof. unfold run_reg_read. esim_run. Qed.

Lemma run_trans_end_sim te :
  esim pr_sim eq (run_trans_end te) (run_trans_end te).
Proof. unfold run_trans_end. esim_run. Qed.

Lemma run_tlbi_sim viio tlbi :
  esim pp_sim eq (run_tlbi n_threads tid imem viio tlbi) (run_tlbi n_threads tid imem viio tlbi).
Proof. unfold run_tlbi. esim_run. Qed.
Lemma lookup_guard_sim mem ts1 ts2 ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax (Q : Prop) :
  ts_sim ts1 ts2 →
  (TLB.Result.merge (Exec.results (TState.tlb_lookup tid imem mem ts1 ifetch upper vpn asid ttbr0
     tmin_ok tmin_unc tmax)) = [] →
   Exec.errors (TState.tlb_lookup tid imem mem ts1 ifetch upper vpn asid ttbr0
     tmin_ok tmin_unc tmax) = [] → Q) →
  TLB.Result.merge (Exec.results (TState.tlb_lookup tid imem mem ts2 ifetch upper vpn asid ttbr0
     tmin_ok tmin_unc tmax)) = [] →
  Exec.errors (TState.tlb_lookup tid imem mem ts2 ifetch upper vpn asid ttbr0
     tmin_ok tmin_unc tmax) = [] → Q.
Proof.
  intros Hs H Hr He.
  destruct (tlb_lookup_perm tid imem mem ifetch upper vpn tmin_ok tmin_unc tmax ts1 ts2 asid ttbr0 Hs)
    as [Pr Pe].
  apply H.
  - apply (proj2 (merge_nil _)). apply (proj1 (merge_nil _)) in Hr. rewrite Hr in Pr.
    apply Permutation_nil.
    apply Permutation_sym. exact Pr.
  - rewrite He in Pe. apply Permutation_nil. apply Permutation_sym. exact Pe.
Qed.

Lemma lookup_merge_sim mem ts1 ts2 ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax x :
  ts_sim ts1 ts2 →
  x ∈ TLB.Result.merge (Exec.results (TState.tlb_lookup tid imem mem ts1 ifetch upper vpn asid ttbr0
     tmin_ok tmin_unc tmax)) →
  x ∈ TLB.Result.merge (Exec.results (TState.tlb_lookup tid imem mem ts2 ifetch upper vpn asid ttbr0
     tmin_ok tmin_unc tmax)).
Proof.
  intros Hs. apply merge_perm_elem.
  exact (proj1 (tlb_lookup_perm tid imem mem ifetch upper vpn tmin_ok tmin_unc tmax ts1 ts2 asid ttbr0 Hs)).
Qed.

Lemma lookup_errors_sim mem ts1 ts2 ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax e :
  ts_sim ts1 ts2 →
  e ∈ Exec.errors (TState.tlb_lookup tid imem mem ts1 ifetch upper vpn asid ttbr0
     tmin_ok tmin_unc tmax) →
  e ∈ Exec.errors (TState.tlb_lookup tid imem mem ts2 ifetch upper vpn asid ttbr0
     tmin_ok tmin_unc tmax).
Proof.
  intros Hs H. apply list_elem_of_In. eapply Permutation_in; [|apply list_elem_of_In, H].
  exact (proj2 (tlb_lookup_perm tid imem mem ifetch upper vpn tmin_ok tmin_unc tmax ts1 ts2 asid ttbr0 Hs)).
Qed.

Ltac esim_extra ::=
  lazymatch goal with
  | |- esim _ _ (Exec.liftSt fst (run_reg_trans_read _ _ _)) _ =>
      apply esim_liftSt_fst, run_reg_trans_read_sim
  | |- esim _ _ (run_reg_general_read _ _) _ => apply run_reg_general_read_sim
  | |- esim _ _ (read_sreg_indirect _ _) _ => apply read_sreg_indirect_sim
  | |- esim _ _ (Exec.liftSt _ ?m) _ =>
      apply esim_liftSt_pp;
      lazymatch m with
      | context [read_sreg_indirect ?r ?a] => apply (read_sreg_indirect_sim r a)
      end
  | |- esim _ _ (materialize_tlbi_for_recipient _ _ _ _ _) _ => apply materialize_sim
  | |- esim _ _ (foldlM _ _ _) _ =>
      apply esim_foldlM2; intros [[? ?] ?] ?; cbv beta iota zeta
  | |- esim _ _ (guard_or _ (Exec.results _ = [] → _)) _ =>
      apply esim_guard_or; let H := fresh in intro H; eapply lookup_guard_sim;
        [first [apply ts_sim_setv; eassumption|apply ts_sim_setv, tlb_sim_sym; eassumption]|exact H]
  | |- esim _ _ (mlift (Exec.make (TLB.Result.merge _) _)) _ =>
      let H := fresh in apply (esim_lift_res _ eq);
        [intros ? H; eexists; split;
           [eapply lookup_merge_sim; [apply ts_sim_setv; eassumption|exact H]|reflexivity]
        |intros ? H; eexists; eapply lookup_errors_sim; [apply ts_sim_setv; eassumption|exact H]]
  end.

Lemma run_trans_start_sim start :
  esim pp_sim eq (run_trans_start tid imem start) (run_trans_start tid imem start).
Proof. unfold run_trans_start. esim_run.
Qed.

Ltac esim_extra ::=
  lazymatch goal with
  | |- esim _ _ (Exec.liftSt fst (run_reg_trans_read _ _ _)) _ =>
      apply esim_liftSt_fst, run_reg_trans_read_sim
  | |- esim _ _ (run_reg_general_read _ _) _ => apply run_reg_general_read_sim
  | |- esim _ _ (read_sreg_indirect _ _) _ => apply read_sreg_indirect_sim
  | |- esim _ _ (Exec.liftSt _ ?m) _ =>
      apply esim_liftSt_pp;
      lazymatch m with
      | context [read_sreg_indirect ?r ?a] => apply (read_sreg_indirect_sim r a)
      | context [run_reg_read ?r ?a] => apply (run_reg_read_sim r a)
      | context [run_trans_end ?te] => apply (run_trans_end_sim te)
      end
  | |- esim _ _ (materialize_tlbi_for_recipient _ _ _ _ _) _ => apply materialize_sim
  | |- esim _ _ (foldlM _ _ _) _ =>
      apply esim_foldlM2; intros [[? ?] ?] ?; cbv beta iota zeta
  | |- esim _ _ (guard_or _ (Exec.results _ = [] → _)) _ =>
      apply esim_guard_or; let H := fresh in intro H; eapply lookup_guard_sim;
        [first [apply ts_sim_setv; eassumption|apply ts_sim_setv, tlb_sim_sym; eassumption]|exact H]
  | |- esim _ _ (mlift (Exec.make (TLB.Result.merge _) _)) _ =>
      let H := fresh in apply (esim_lift_res _ eq);
        [intros ? H; eexists; split;
           [eapply lookup_merge_sim; [apply ts_sim_setv; eassumption|exact H]|reflexivity]
        |intros ? H; eexists; eapply lookup_errors_sim; [apply ts_sim_setv; eassumption|exact H]]
  | |- esim _ _ (mlift (read_imem _ _ _)) _ =>
      let H := fresh in apply (esim_lift_res _ eq);
        [intros ? H; eexists; split; [exact H|reflexivity]|intros ? H; eexists; exact H]
  | |- esim _ _ (run_reg_write _ _ _ _ _) _ => apply run_reg_write_sim
  | |- esim _ _ (read_mem_explicit _ _ _ _) _ => apply read_mem_explicit_sim
  | |- esim _ _ read_pte _ => apply read_pte_sim
  | |- esim _ _ (write_mem _ _ _ _ _ _) _ => apply write_mem_sim
  | |- esim _ _ (run_barrier _ _ _ _) _ => apply run_barrier_sim
  | |- esim _ _ (run_tlbi _ _ _ _ _) _ => apply run_tlbi_sim
  | |- esim _ _ (run_cse _ _ _) _ => apply run_cse_sim
  | |- esim _ _ (run_trans_start _ _ _) _ => apply run_trans_start_sim
  | |- esim _ _ (run_take_exception _ _ _ _) _ => apply run_take_exception_sim
  end.

Lemma run_outcome_sim out :
  esim pp_sim eq (run_outcome n_threads tid imem out) (run_outcome n_threads tid imem out).
Proof.
  destruct out.
  all: lazymatch goal with
    | |- context [run_outcome _ _ _ (MemRead ?mr)] => destruct mr as [? ? ? ? [|?]]
    | |- context [run_outcome _ _ _ (MemWrite ?mr _ _)] => destruct mr as [? ? ? ? [|?]]
    | _ => idtac end.
  all: simp run_outcome; esim_run.
Qed.

Lemma cinterp_sim {A} (mon : iMon A) :
  esim pp_sim eq (cinterp (run_outcome' n_threads tid imem) mon)
    (cinterp (run_outcome' n_threads tid imem) mon).
Proof.
  induction mon as [a|call k IH].
  - cbn. apply esim_ret. reflexivity.
  - destruct call as [out|[m]]; cbn.
    + apply (esim_bind _ eq); [|intros ? ? <-; apply IH].
      apply (esim_fmap _ eq); [apply run_outcome_sim|intros ? ? <-; reflexivity].
    + apply (esim_bind _ eq); [apply esim_mchoose|intros ? ? <-; apply IH].
Qed.
End Handlers.

(** Every outcome handler, on simulated instruction states. *)
Theorem run_outcome_simulation n_threads tid imem out p1 p2 p1' r :
  pp_sim p1 p2 →
  Exec.elem_of_results (p1', r) (run_outcome n_threads tid imem out p1) →
  ∃ p2', Exec.elem_of_results (p2', r) (run_outcome n_threads tid imem out p2) ∧ pp_sim p1' p2'.
Proof.
  intros Hp Hin. destruct (proj1 (run_outcome_sim n_threads tid imem out) p1 p2 p1' r Hp Hin)
    as [p2' [r' [Hr [Hs <-]]]]. eauto.
Qed.

(** Running an instruction from simulated instruction states. *)
Theorem instruction_sim n_threads tid imem {A} (mon : iMon A) p1 p2 p1' ret :
  pp_sim p1 p2 →
  Exec.elem_of_results (p1', ret) (cinterp (run_outcome' n_threads tid imem) mon p1) →
  ∃ p2', Exec.elem_of_results (p2', ret) (cinterp (run_outcome' n_threads tid imem) mon p2) ∧
    pp_sim p1' p2'.
Proof.
  intros Hp Hin. destruct (proj1 (cinterp_sim n_threads tid imem mon) p1 p2 p1' ret Hp Hin)
    as [p2' [r [Hr [Hs <-]]]]. eauto.
Qed.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

Theorem run_tid_sim isem (tid : fin n) (s1 s2 s1' : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → Exec.elem_of_results (s1', ()) (PState.run_tid isem prom tid s1) →
  ∃ s2', Exec.elem_of_results (s2', ()) (PState.run_tid isem prom tid s2) ∧ st_sim s1' s2'.
Proof.
  intros Hs Hrun. destruct Hs as (Himem & Hmem & Hstates).
  destruct (run_tid_broadcast_decompose prom isem tid s1 s1' Hrun)
    as [ts [mem [iis [states [Hinst [Hb ->]]]]]].
  assert (Hp : pp_sim (PPState.Make (PState.tstate tid s1) (PState.events s1) IIS.init)
    (PPState.Make (PState.tstate tid s2) (PState.events s2) IIS.init)).
  { split; [exact Hmem|]. split; [reflexivity|apply Hstates]. }
  destruct (instruction_sim n tid (PState.initmem s1) isem _ _ _ () Hp Hinst)
    as [[ts2 mem2 iis2] [Hinst2 (Hm2 & Hi2 & Hts2)]].
  cbn in Hm2, Hi2, Hts2. subst mem2 iis2.
  rewrite Himem in Hinst2.
  destruct (broadcast_sim bbm tid (PState.initmem s1) (PState.events s1)
    (take (length mem - length (PState.events s1)) mem)
    (vinsert tid ts (PState.tstates s1)) (vinsert tid ts2 (PState.tstates s2)) states)
    as [states2 [Hb2 Hstates2]]; [|exact Hb|].
  { intro i. destruct (decide (i = tid)) as [->|Hne].
    - rewrite !vlookup_insert. exact Hts2.
    - rewrite !vlookup_insert_ne by congruence. apply Hstates. }
  exists (PState.Make states2 (PState.initmem s2) mem). split.
  - eapply run_tid_broadcast_intro; [exact Hinst2|].
    rewrite <- Himem, <- Hmem. exact Hb2.
  - split; [exact Himem|]. split; [reflexivity|]. intro i. apply Hstates2.
Qed.

Lemma terminated_tid_sim term (s1 s2 : PState.t TState.t Ev.t n) tid :
  st_sim s1 s2 → PState.terminated_tid prom term s1 tid = PState.terminated_tid prom term s2 tid.
Proof.
  intros (_ & _ & Hstates). unfold PState.terminated_tid, PState.terminated_ts.
  pose proof (ts_sim_frame _ _ (Hstates tid)) as Hframe.
  change (pc_terminated (term !!! tid) (TState.pc (PState.tstate tid s1)) =
    pc_terminated (term !!! tid) (TState.pc (PState.tstate tid s2))).
  change (TState.pc (PState.tstate tid s1)) with (TState.pc (setv TState.tlb None (PState.tstate tid s1))).
  change (TState.pc (PState.tstate tid s2)) with (TState.pc (setv TState.tlb None (PState.tstate tid s2))).
  rewrite Hframe. reflexivity.
Qed.

Theorem instruction_transition_sim nondet term (s1 s2 s1' : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → InstructionTransition prom nondet term s1 s1' →
  ∃ s2', InstructionTransition prom nondet term s2 s2' ∧ st_sim s1' s2'.
Proof.
  intros Hs (tid & Hterm & Hrun).
  destruct (run_tid_sim _ tid s1 s2 s1' Hs Hrun) as [s2' [Hrun2 Hs']].
  exists s2'. split; [|exact Hs']. exists tid. split; [|exact Hrun2].
  rewrite <- (terminated_tid_sim term s1 s2 tid Hs). exact Hterm.
Qed.

(** Instruction steps and promises of the Sail serialization. *)
Theorem step_sim nondet term (s1 s2 s1' : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → VMViews.Step bbm nondet term s1 s1' →
  ∃ s2', VMViews.Step bbm nondet term s2 s2' ∧ st_sim s1' s2'.
Proof.
  intros Hs [Hinst|[ev Hpromise]].
  - destruct (instruction_transition_sim nondet term s1 s2 s1' Hs Hinst) as [s2' [H2 Hs']].
    exists s2'. split; [left; exact H2|exact Hs'].
  - destruct (promise_sim bbm ev s1 s2 s1' Hs Hpromise) as [s2' [H2 Hs']].
    exists s2'. split; [right; exists ev; exact H2|exact Hs'].
Qed.

Theorem steps_sim nondet term (s1 s2 s1' : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → rtc (VMViews.Step bbm nondet term) s1 s1' →
  ∃ s2', rtc (VMViews.Step bbm nondet term) s2 s2' ∧ st_sim s1' s2'.
Proof.
  intros Hs Hsteps. revert s2 Hs. induction Hsteps as [s|s mid fin Hstep _ IH]; intros s2 Hs.
  - exists s2. split; [apply rtc_refl|exact Hs].
  - destruct (step_sim nondet term s s2 mid Hs Hstep) as [mid2 [Hstep2 Hmid]].
    destruct (IH mid2 Hmid) as [s2' [Hsteps2 Hs']].
    exists s2'. split; [eapply rtc_l; eassumption|exact Hs'].
Qed.

(** One step of the direct runner. A promise step needs the promise to be
    among the candidates enumerated from the simulated state. *)
Theorem run_step_sim isem term fuel (s1 s2 s1' : PState.t TState.t Ev.t n) :
  st_sim s1 s2 →
  (∀ tid ev, Exec.elem_of_results ev (CPState.promise_select_tid isem prom term fuel s1 tid) →
    Exec.elem_of_results ev (CPState.promise_select_tid isem prom term fuel s2 tid)) →
  Exec.elem_of_results (s1', ()) (@CPState.run_step isem prom n term fuel s1) →
  ∃ s2', Exec.elem_of_results (s2', ()) (@CPState.run_step isem prom n term fuel s2) ∧ st_sim s1' s2'.
Proof.
  intros Hs Hsel Hrun.
  apply (PromiseFirstCurrent.run_step_inv (prom := prom)) in Hrun
    as [(tid & ev & nst & Hterm & Hev & Hpromise & ->)|(tid & Hterm & Hrun)].
  - destruct (promise_sim bbm ev s1 s2 nst Hs Hpromise) as [nst2 [Hp2 Hs']].
    exists nst2. split; [|exact Hs'].
    unfold CPState.run_step.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
    eapply Exec.elem_of_bind_intro; [apply (Exec.elem_of_mchoose _ tid)|].
    rewrite <- (terminated_tid_sim term s1 s2 tid Hs), Hterm.
    eapply Exec.elem_of_bind_intro; [apply (Exec.elem_of_mchoosel _ true); apply elem_of_enum|].
    eapply cpromise_tid_intro; [apply Hsel, Hev|exact Hp2|reflexivity].
  - destruct (run_tid_sim isem tid s1 s2 s1' Hs Hrun) as [s2' [Hrun2 Hs']].
    exists s2'. split; [|exact Hs'].
    unfold CPState.run_step.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
    eapply Exec.elem_of_bind_intro; [apply (Exec.elem_of_mchoose _ tid)|].
    rewrite <- (terminated_tid_sim term s1 s2 tid Hs), Hterm.
    eapply Exec.elem_of_bind_intro; [apply (Exec.elem_of_mchoosel _ false); apply elem_of_enum|].
    exact Hrun2.
Qed.

Theorem non_cert_step_sim isem (s1 s2 s1' : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → PState.non_cert_step isem prom s1 s1' →
  ∃ s2', PState.non_cert_step isem prom s2 s2' ∧ st_sim s1' s2'.
Proof.
  intros Hs [tid s1'' Hrun|ev s1'' Hlt Hpromise].
  - destruct (run_tid_sim isem tid s1 s2 s1'' Hs Hrun) as [s2' [H2 Hs']].
    exists s2'. split; [apply PState.SRun with (tid := tid); exact H2|exact Hs'].
  - destruct (promise_sim bbm ev s1 s2 s1'' Hs Hpromise) as [s2' [H2 Hs']].
    exists s2'. split; [eapply PState.SPromise; eassumption|exact Hs'].
Qed.

Lemma forallb_ext' {A} (f g : A → bool) l : (∀ x, f x = g x) → forallb f l = forallb g l.
Proof. intro H. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite H, IH. reflexivity. Qed.

Lemma terminated_sim term (s1 s2 : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → PState.terminated prom term s1 = PState.terminated prom term s2.
Proof.
  intro Hs. unfold PState.terminated, fforallb. apply forallb_ext'. intro tid.
  apply terminated_tid_sim, Hs.
Qed.

Lemma nopromises_sim (s1 s2 : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → PState.nopromises prom s1 = PState.nopromises prom s2.
Proof.
  intros (_ & _ & Hstates). unfold PState.nopromises, fforallb. apply forallb_ext'. intro tid.
  unfold PState.nopromises_tid. pose proof (ts_sim_frame _ _ (Hstates tid)) as Hframe.
  change (is_emptyb (TState.prom_wr (setv TState.tlb None (PState.tstate tid s1)) ++
      TState.prom_tlbi (setv TState.tlb None (PState.tstate tid s1))) =
    is_emptyb (TState.prom_wr (setv TState.tlb None (PState.tstate tid s2)) ++
      TState.prom_tlbi (setv TState.tlb None (PState.tstate tid s2)))).
  rewrite Hframe. reflexivity.
Qed.

Lemma to_archState_sim (s1 s2 : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → PState.to_archState prom s1 = PState.to_archState prom s2.
Proof.
  intros (Himem & Hmem & Hstates). unfold PState.to_archState. rewrite Himem, Hmem. f_equal.
  apply vec_eq. intro i. rewrite !vlookup_map.
  pose proof (ts_sim_frame _ _ (Hstates i)) as Hframe.
  change (TState.reg_map (setv TState.tlb None (PState.tstate i s1)) =
    TState.reg_map (setv TState.tlb None (PState.tstate i s2))).
  rewrite Hframe. reflexivity.
Qed.

(** One transition of the direct runner. Final states keep the architectural
    state; non-final steps need the promise candidates of the simulated state. *)
Theorem run_transition_sim isem term fuel (s1 s2 s1' : PState.t TState.t Ev.t n) r1 :
  st_sim s1 s2 → VMViews.state_ok s1 →
  (∀ tid ev, Exec.elem_of_results ev (CPState.promise_select_tid isem prom term fuel s1 tid) →
    Exec.elem_of_results ev (CPState.promise_select_tid isem prom term fuel s2 tid)) →
  Exec.elem_of_results (s1', r1) (CPState.run_transition isem prom term fuel s1) →
  ∃ s2' r2, Exec.elem_of_results (s2', r2) (CPState.run_transition isem prom term fuel s2) ∧
    st_sim s1' s2' ∧ option_map (λ f, projT1 f) r1 = option_map (λ f, projT1 f) r2.
Proof.
  intros Hs Hok Hsel Hrun. unfold CPState.run_transition in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [st0 [st0' [Hget Hrun]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  pose proof (terminated_sim term s1 s2 Hs) as Hterm.
  destruct (decide (PState.terminated prom term s1)) as [pt|Hnot].
  - destruct (decide (PState.terminated prom term s2)) as [pt2|Hnot2];
      [|exfalso; apply Hnot2; rewrite <- Hterm; exact pt].
    apply Exec.elem_of_bind_elim in Hrun as [mid [[] [Hval Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    unfold CPState.validate_final_state in Hval.
    apply Exec.elem_of_bind_elim in Hval as [mid' [pn [Hguard Hval]]].
    pose proof Hguard as Hpn. apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    destruct (PState.check_valid_end prom s1) as [|err errs] eqn:Herrs.
    2: { apply Exec.elem_of_bind_elim in Hval as [? [? [_ Hthrow]]].
         unfold elem_of, Exec.elem_of_results in Hthrow. cbn in Hthrow. inversion Hthrow. }
    apply Exec.elem_of_mret_inv in Hval as [-> _].
    assert (Herrs2 : PState.check_valid_end prom s2 = []).
    { apply (proj1 (state_check_valid_end_sim bbm s1 s2 Hs Hok)). exact Herrs. }
    assert (Hpn2 : PState.nopromises prom s2) by (rewrite <- (nopromises_sim s1 s2 Hs); exact pn).
    exists s2, (Some (CPState.to_final_archState (CPState.make_final prom term s2 pt2))).
    split; [|split; [exact Hs|]].
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|]. cbv beta.
      match goal with |- context [decide ?P] => destruct (decide P) as [pt3|]; [|contradiction] end.
      rewrite (proof_irrel pt3 pt2).
      eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
      unfold CPState.validate_final_state.
      destruct (Exec.elem_of_guard_discard (E := string) s2 Hpn2) as [q Hq].
      eapply Exec.elem_of_bind_intro; [exact Hq|]. rewrite Herrs2. apply Exec.elem_of_mret.
    + cbn. f_equal. apply to_archState_sim, Hs.
  - destruct (decide (PState.terminated prom term s2)) as [pt2|Hnot2];
      [exfalso; apply Hnot; rewrite Hterm; exact pt2|].
    apply Exec.elem_of_bind_elim in Hrun as [mid [[] [Hstep Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    destruct (run_step_sim isem term fuel s1 s2 mid Hs Hsel Hstep) as [mid2 [Hstep2 Hmid]].
    exists mid2, None. split; [|split; [exact Hmid|reflexivity]].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|]. cbv beta.
    match goal with |- context [decide ?P] => destruct (decide P); [contradiction|] end.
    eapply Exec.elem_of_bind_intro; [exact Hstep2|apply Exec.elem_of_mret].
Qed.
End Machine.

(** * Enumeration of promise candidates *)

Lemma cinterp_gen {St A} (R : St → St → Prop) (h : ∀ out : outcome, Exec.t St string (eff_ret out))
    (mon : iMon A) :
  (∀ out, esim R eq (h out) (h out)) → esim R eq (cinterp h mon) (cinterp h mon).
Proof.
  intro Hh. induction mon as [a|call k IH].
  - cbn. apply esim_ret. reflexivity.
  - destruct call as [out|[m]]; cbn.
    + apply (esim_bind _ eq); [apply Hh|intros ? ? <-; apply IH].
    + apply (esim_bind _ eq); [apply esim_mchoose|intros ? ? <-; apply IH].
Qed.

Definition lp_sim (a b : list Ev.t * PPState.t TState.t Ev.t IIS.t) := a.1 = b.1 ∧ pp_sim a.2 b.2.

Lemma esim_liftSt_snd {A B} (V : A → B → Prop) m1 m2 :
  esim pp_sim V m1 m2 → esim lp_sim V (Exec.liftSt snd m1) (Exec.liftSt snd m2).
Proof.
  apply esim_liftSt; [intros s1 s2 [_ H]; exact H|].
  intros [l1 p1] [l2 p2] t1 t2 [Hl _] Ht. split; [exact Hl|exact Ht].
Qed.

Ltac lp_solve :=
  let l1 := fresh "l" in let p1 := fresh "p" in let l2 := fresh "l" in let p2 := fresh "p" in
  let Hl := fresh "Hl" in let Hp := fresh "Hp" in
  intros [l1 p1] [l2 p2] [Hl Hp]; cbn [fst snd] in Hl, Hp; subst l2;
  first [ destruct Hp as (Hm & _ & _); exact Hm
        | split; [reflexivity|]; destruct Hp as (Hm & Hi & Ha); split; [exact Hm|split; [reflexivity|exact Ha]]
        | split; [reflexivity|exact Hp] ].

Section Enumeration.
Context (bbm : bool) {n : nat} (isem : iMon ()) (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

Lemma run_outcome_with_promise_sim (tid : fin n) imem base out :
  esim lp_sim eq (CPState.run_outcome_with_promise prom tid imem base out)
    (CPState.run_outcome_with_promise prom tid imem base out).
Proof.
  unfold CPState.run_outcome_with_promise.
  apply (esim_bind _ eq); [apply esim_liftSt_snd, run_outcome_sim|intros [res [vpre|]] ? <-].
  - destruct (decide (vpre ≤ base)); [|apply esim_ret; reflexivity].
    apply (esim_bind _ eq); [apply esim_mget; lp_solve|intros mem ? <-].
    apply (esim_bind _ eq); [apply esim_mset; lp_solve|intros ? ? <-].
    apply esim_ret. reflexivity.
  - apply esim_ret. reflexivity.
Qed.

Lemma run_to_termination_sim (tid : fin n) imem fuel base :
  esim lp_sim eq (CPState.run_to_termination isem prom term tid imem fuel base)
    (CPState.run_to_termination isem prom term tid imem fuel base).
Proof.
  induction fuel as [|fuel IH]; cbn [CPState.run_to_termination].
  all: apply (esim_bind _ ts_sim); [apply esim_mget; intros s1 s2 [_ (_ & _ & H)]; exact H|].
  all: intros ts1 ts2 Hts; apply ts_sim_inv in Hts as (t & c1 & c2 & -> & -> & Hc).
  all: match goal with |- esim _ _ (match ?d with _ => _ end) (match ?d' with _ => _ end) =>
    change d' with d; destruct d end; [apply esim_ret; reflexivity|].
  all: match goal with |- esim _ _ (match ?d with _ => _ end) (match ?d' with _ => _ end) =>
    change d' with d; destruct d end; [apply esim_ret; reflexivity|].
  - apply esim_ret. reflexivity.
  - apply (esim_bind _ eq); [apply esim_msetv; lp_solve|intros ? ? <-].
    apply (esim_bind _ eq); [|intros ? ? <-; exact IH].
    apply cinterp_gen. intro out. apply run_outcome_with_promise_sim.
Qed.

Lemma concat_elem {A} (x : A) (L : list (list A)) : x ∈ List.concat L ↔ ∃ l, l ∈ L ∧ x ∈ l.
Proof.
  induction L as [|l L IH]; cbn.
  - split; [intro H; inversion H|intros (? & H & _); inversion H].
  - split.
    + intro H. apply elem_of_app in H as [H|H]; [exists l; split; [left|exact H]|].
      destruct (proj1 IH H) as (l' & Hl' & Hx). exists l'. split; [right; exact Hl'|exact Hx].
    + intros (l' & Hl' & Hx). apply elem_of_app.
      apply elem_of_cons in Hl' as [->|Hl']; [left; exact Hx|].
      right. apply IH. eauto.
Qed.

Lemma enum_init_sim ts1 ts2 (mem : Memory.t) : ts_sim ts1 ts2 →
  lp_sim ([], PPState.Make ts1 mem IIS.init) ([], PPState.Make ts2 mem IIS.init).
Proof. intro Hs. split; [reflexivity|]. split; [reflexivity|split; [reflexivity|exact Hs]]. Qed.

Lemma filter_promises_mono (tid : nat) mem (l1 l2 : list Ev.t) ev :
  (∀ x, x ∈ l1 → x ∈ l2) →
  ev ∈ Promising.filter_promises prom n tid mem l1 → ev ∈ Promising.filter_promises prom n tid mem l2.
Proof.
  intros Hl. cbn. unfold filter_commuting_promises. destruct mem as [|last mem]; [apply Hl|].
  intro H. apply list_elem_of_filter in H as [Hp H]. apply list_elem_of_filter. split; [exact Hp|apply Hl, H].
Qed.

Lemma enum_promises_sim tid imem fuel ts1 ts2 mem ev : ts_sim ts1 ts2 →
  ev ∈ CPState.promises prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts1 mem) →
  ev ∈ CPState.promises prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts2 mem).
Proof.
  intro Hs. destruct (run_to_termination_sim tid imem fuel (length mem)) as [Hr He].
  pose proof (enum_init_sim ts1 ts2 mem Hs) as Hinit.
  unfold CPState.enumerate_results_filtered. cbn [CPState.promises].
  apply filter_promises_mono. intro x.
  intro H. apply (proj2 (elem_of_remove_dups _ _)). apply (proj1 (elem_of_remove_dups _ _)) in H.
  apply (proj1 (concat_elem _ _)) in H as (l & Hl & Hx). apply (proj2 (concat_elem _ _)).
  exists l. split; [|exact Hx].
  apply elem_of_app in Hl as [Hl|Hl]; apply elem_of_app.
  - left. unfold Exec.success_state_list in *.
    apply list_elem_of_fmap in Hl as [[l' p] [-> Hl]]. apply list_elem_of_fmap in Hl as [[[l'' p'] r] [Heq Hl]].
    injection Heq as -> ->.
    destruct (Hr _ _ (l'', p') r Hinit Hl) as ((l2 & p2) & r2 & Hin2 & [Hl2 _] & <-).
    cbn in Hl2. subst l2.
    apply list_elem_of_fmap. exists (l'', p2). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((l'', p2), r). split; [reflexivity|exact Hin2].
  - right. apply list_elem_of_fmap in Hl as [[l' p] [-> Hl]].
    apply list_elem_of_fmap in Hl as [[[l'' p'] e] [Heq Hl]]. injection Heq as -> ->.
    destruct (He _ _ (l'', p') e Hinit Hl) as ((l2 & p2) & e2 & Hin2 & [Hl2 _]).
    cbn in Hl2. subst l2.
    apply list_elem_of_fmap. exists (l'', p2). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((l'', p2), e2). split; [reflexivity|exact Hin2].
Qed.

Lemma enum_oof_imp tid imem fuel ts1 ts2 mem : ts_sim ts1 ts2 →
  CPState.out_of_fuel prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts1 mem) →
  CPState.out_of_fuel prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts2 mem).
Proof.
  intro Hs. destruct (run_to_termination_sim tid imem fuel (length mem)) as [Hr _].
  pose proof (enum_init_sim ts1 ts2 mem Hs) as Hinit.
  unfold CPState.enumerate_results_filtered. cbn [CPState.out_of_fuel].
  intro H. apply bool_decide_unpack in H as (r & Hr1 & Hoof). apply bool_decide_pack.
  exists r. split; [|exact Hoof].
  apply list_elem_of_fmap in Hr1 as [[s r'] [-> Hin]].
  destruct (Hr _ _ s r' Hinit Hin) as (s2 & ? & Hin2 & _ & <-).
  apply list_elem_of_fmap. exists (s2, r'). split; [reflexivity|exact Hin2].
Qed.

Lemma enum_oof_sim tid imem fuel ts1 ts2 mem : ts_sim ts1 ts2 →
  CPState.out_of_fuel prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts1 mem) =
  CPState.out_of_fuel prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts2 mem).
Proof.
  intro Hs. pose proof (enum_oof_imp tid imem fuel ts1 ts2 mem Hs) as H1.
  pose proof (enum_oof_imp tid imem fuel ts2 ts1 mem (ts_sim_sym _ _ Hs)) as H2.
  destruct (CPState.out_of_fuel prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts1 mem)),
    (CPState.out_of_fuel prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts2 mem));
    [reflexivity|destruct (H1 I)|destruct (H2 I)|reflexivity].
Qed.

Lemma enum_final_sim tid imem fuel ts1 ts2 mem t1 : ts_sim ts1 ts2 →
  t1 ∈ CPState.final_states prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts1 mem) →
  ∃ t2, t2 ∈ CPState.final_states prom
    (CPState.enumerate_results_filtered isem prom term tid imem fuel ts2 mem) ∧ ts_sim t1 t2.
Proof.
  intro Hs. destruct (run_to_termination_sim tid imem fuel (length mem)) as [Hr _].
  pose proof (enum_init_sim ts1 ts2 mem Hs) as Hinit.
  unfold CPState.enumerate_results_filtered. cbn [CPState.final_states].
  intro H. apply list_elem_of_omap in H as [[[l p] r] [Hin Hf]].
  destruct r; try discriminate. destruct (is_emptyb l) eqn:Hl; [|discriminate].
  injection Hf as <-.
  destruct (Hr _ _ (l, p) CPState.Terminated Hinit Hin) as ((l2 & p2) & ? & Hin2 & [Hl2 (_ & _ & Hp)] & <-).
  cbn in Hl2, Hp. subst l2. exists (PPState.state p2). split; [|exact Hp].
  apply list_elem_of_omap. exists (l, p2, CPState.Terminated). split; [exact Hin2|]. cbn.
  rewrite Hl. reflexivity.
Qed.
End Enumeration.

Section Selection.
Context (bbm : bool) {n : nat} (isem : iMon ()) (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

(** Simulated machine states enumerate the same promise candidates. *)
Theorem promise_select_sim fuel (s1 s2 : PState.t TState.t Ev.t n) tid ev :
  st_sim s1 s2 →
  Exec.elem_of_results ev (CPState.promise_select_tid isem prom term fuel s1 tid) →
  Exec.elem_of_results ev (CPState.promise_select_tid isem prom term fuel s2 tid).
Proof.
  intros (Himem & Hmem & Hstates) Hin.
  apply PromiseFirstCurrent.promise_select_tid_inv in Hin.
  apply PromiseFirstCurrent.promise_select_tid_intro.
  change (CPState.initmem s2) with (PState.initmem s2). change (CPState.events s2) with (PState.events s2).
  rewrite <- Himem, <- Hmem. eapply enum_promises_sim; [apply Hstates|exact Hin].
Qed.

Theorem run_step_sim' fuel (s1 s2 s1' : PState.t TState.t Ev.t n) :
  st_sim s1 s2 →
  Exec.elem_of_results (s1', ()) (@CPState.run_step isem prom n term fuel s1) →
  ∃ s2', Exec.elem_of_results (s2', ()) (@CPState.run_step isem prom n term fuel s2) ∧ st_sim s1' s2'.
Proof.
  intros Hs. apply run_step_sim; [exact Hs|]. intros tid ev. apply promise_select_sim, Hs.
Qed.

Theorem run_transition_sim' fuel (s1 s2 s1' : PState.t TState.t Ev.t n) r1 :
  st_sim s1 s2 → VMViews.state_ok s1 →
  Exec.elem_of_results (s1', r1) (CPState.run_transition isem prom term fuel s1) →
  ∃ s2' r2, Exec.elem_of_results (s2', r2) (CPState.run_transition isem prom term fuel s2) ∧
    st_sim s1' s2' ∧ option_map (λ f, projT1 f) r1 = option_map (λ f, projT1 f) r2.
Proof.
  intros Hs Hok. apply run_transition_sim; [exact Hs|exact Hok|].
  intros tid ev. apply promise_select_sim, Hs.
Qed.
End Selection.

(** * Promise-first transitions *)

Lemma cinterp_inv_gen {St A} (P : St → Prop) (h : ∀ out : outcome, Exec.t St string (eff_ret out))
    (mon : iMon A) :
  (∀ out s s' r, P s → Exec.elem_of_results (s', r) (h out s) → P s') →
  ∀ s s' r, P s → Exec.elem_of_results (s', r) (cinterp h mon s) → P s'.
Proof.
  intro Hh. induction mon as [a|call k IH]; intros s s' r Hs Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hs.
  - destruct call as [out|[m]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [x [Hx Hrun]]].
      eapply IH; [eapply Hh; eassumption|exact Hrun].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [x [Hx Hrun]]].
      apply Exec.elem_of_mchoose_inv in Hx as ->. eapply IH; eassumption.
Qed.

Lemma vec_choice {A} {n} (P : fin n → A → Prop) :
  (∀ i, ∃ y, P i y) → ∃ v : vec A n, ∀ i, P i (v !!! i).
Proof.
  induction n as [|n IH]; intro H.
  - exists [#]. intro i. inversion i.
  - destruct (H 0%fin) as [y0 Hy0]. destruct (IH (λ i, P (FS i)) (λ i, H (FS i))) as [v Hv].
    exists (y0 ::: v). intro i. dependent destruction i; [exact Hy0|exact (Hv i)].
Qed.

Section PromiseFirst.
Context (bbm : bool) {n : nat} (isem : iMon ()) (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

Lemma run_outcome_with_promise_ok (tid : fin n) imem base out p p' r :
  VMViews.ok p.2 →
  Exec.elem_of_results (p', r) (CPState.run_outcome_with_promise prom tid imem base out p) →
  VMViews.ok p'.2.
Proof.
  intros Hok Hin. unfold CPState.run_outcome_with_promise in Hin.
  apply Exec.elem_of_bind_elim in Hin as [mid [[res vpre] [Hh Hin]]].
  apply Exec.elem_of_liftSt_inv in Hh as [inner [-> Hh]].
  pose proof (VMViews.run_outcome_ok n tid imem out p.2 inner (res, vpre) Hok Hh) as Hinner.
  cbv beta iota in Hin.
  destruct vpre as [vpre|]; [destruct (decide (vpre ≤ base))|].
  - apply Exec.elem_of_bind_elim in Hin as [mid' [mem [Hg Hin]]].
    apply Exec.elem_of_mget_inv in Hg as [-> ->].
    apply Exec.elem_of_bind_elim in Hin as [mid'' [[] [Hs Hin]]].
    apply Exec.elem_of_mset_inv in Hs as ->.
    apply Exec.elem_of_mret_inv in Hin as [-> _]. exact Hinner.
  - apply Exec.elem_of_mret_inv in Hin as [-> _]. exact Hinner.
  - apply Exec.elem_of_mret_inv in Hin as [-> _]. exact Hinner.
Qed.

Lemma run_to_termination_ok (tid : fin n) imem fuel base p p' r :
  VMViews.ok p.2 →
  Exec.elem_of_results (p', r) (CPState.run_to_termination isem prom term tid imem fuel base p) →
  VMViews.ok p'.2.
Proof.
  revert p. induction fuel as [|fuel IH]; intros p Hok Hin; cbn [CPState.run_to_termination] in Hin.
  all: apply Exec.elem_of_bind_elim in Hin as [mid [ts [Hg Hin]]].
  all: apply Exec.elem_of_mget_inv in Hg as [-> ->].
  all: destruct (decide _); [apply Exec.elem_of_mret_inv in Hin as [-> _]; exact Hok|].
  all: destruct (CPState.terminated_ts _ _ _); [apply Exec.elem_of_mret_inv in Hin as [-> _]; exact Hok|].
  - apply Exec.elem_of_mret_inv in Hin as [-> _]. exact Hok.
  - unfold msetv in Hin.
    apply Exec.elem_of_bind_elim in Hin as [mid [[] [Hs Hin]]].
    apply Exec.elem_of_mset_inv in Hs as ->.
    apply Exec.elem_of_bind_elim in Hin as [mid' [[] [Hc Hin]]].
    eapply IH; [|exact Hin].
    eapply (cinterp_inv_gen (λ s, VMViews.ok s.2)); [| |exact Hc].
    + intros out s s' r' Hs Hr. eapply run_outcome_with_promise_ok; eassumption.
    + destruct Hok as [Hts Hiis]. split; [exact Hts|].
      exact (VMViews.iis_ok_mono 0 _ _ (Nat.le_0_l _) VMViews.iis_init).
Qed.

Lemma enum_final_ok (tid : fin n) imem fuel ts (mem : Memory.t) t :
  VMViews.ts_ok (length mem) ts →
  t ∈ CPState.final_states prom (CPState.enumerate_results_filtered isem prom term tid imem fuel ts mem) →
  ∃ bound, VMCacheState.cache_ok bound t.
Proof.
  intros Hts H. unfold CPState.enumerate_results_filtered in H. cbn [CPState.final_states] in H.
  apply list_elem_of_omap in H as [[[l p] r] [Hin Hf]].
  destruct r; try discriminate. destruct (is_emptyb l); [|discriminate]. injection Hf as <-.
  assert (Hok : VMViews.ok p).
  { apply (run_to_termination_ok tid imem fuel (length mem) ([], PPState.Make ts mem IIS.init) (l, p)
      CPState.Terminated); [|exact Hin].
    split; [exact Hts|exact (VMViews.iis_ok_mono 0 _ _ (Nat.le_0_l _) VMViews.iis_init)]. }
  exists (length (PPState.mem p)). apply VMViews.ok_cache, (proj1 Hok).
Qed.

Lemma check_valid_end_sim_any (s1 s2 : PState.t TState.t Ev.t n) :
  st_sim s1 s2 → (∀ tid, ∃ bound, VMCacheState.cache_ok bound (PState.tstate tid s1)) →
  PState.check_valid_end prom s1 = [] ↔ PState.check_valid_end prom s2 = [].
Proof.
  intros (Himem & Hmem & Hstates) Hok. unfold PState.check_valid_end.
  apply concat_map_nil_iff. intro tid. unfold PState.check_valid_end_tid.
  rewrite <- Himem, <- Hmem. destruct (Hok tid) as [b Hb].
  apply (check_valid_end_sim bbm tid _ _ b); [apply Hstates|exact Hb].
Qed.

Lemma validate_final_state_inv (st0 s s' : PState.t TState.t Ev.t n) :
  Exec.elem_of_results (s', ()) (CPState.validate_final_state prom st0 s) →
  s' = s ∧ CPState.nopromises prom st0 ∧ PState.check_valid_end prom st0 = [].
Proof.
  unfold CPState.validate_final_state. intro Hval.
  apply Exec.elem_of_bind_elim in Hval as [mid' [pn [Hguard Hval]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  destruct (PState.check_valid_end prom st0) as [|err errs] eqn:Herrs.
  2: { apply Exec.elem_of_bind_elim in Hval as [? [? [_ Hthrow]]].
       unfold elem_of, Exec.elem_of_results in Hthrow. cbn in Hthrow. inversion Hthrow. }
  apply Exec.elem_of_mret_inv in Hval as [-> _]. auto.
Qed.

Lemma validate_final_state_intro (st0 s : PState.t TState.t Ev.t n) :
  CPState.nopromises prom st0 → PState.check_valid_end prom st0 = [] →
  Exec.elem_of_results (s, ()) (CPState.validate_final_state prom st0 s).
Proof.
  intros Hpn Herrs. unfold CPState.validate_final_state.
  destruct (Exec.elem_of_guard_discard (E := string) s Hpn) as [q Hq].
  eapply Exec.elem_of_bind_intro; [exact Hq|]. cbv beta. rewrite Herrs. apply Exec.elem_of_mret.
Qed.

(** One transition of the promise-first runner. *)
Theorem run_transition_promise_first_sim fuel (s1 s2 s1' : PState.t TState.t Ev.t n) r1 :
  st_sim s1 s2 → VMViews.state_ok s1 →
  Exec.elem_of_results (s1', r1)
    (CPState.run_transition_promise_first_uncached isem prom term fuel s1) →
  ∃ s2' r2, Exec.elem_of_results (s2', r2)
      (CPState.run_transition_promise_first_uncached isem prom term fuel s2) ∧
    st_sim s1' s2' ∧ option_map (λ f, projT1 f) r1 = option_map (λ f, projT1 f) r2.
Proof.
  intros Hs Hok Hrun. pose proof Hs as (Himem & Hmem & Hstates).
  destruct r1 as [fsig|].
  - apply (PromiseFirstCurrent.run_transition_promise_first_some_inv (prom := prom)) in Hrun
      as (tstates & st0 & pt & -> & Hfin & Hval & ->).
    apply validate_final_state_inv in Hval as (-> & Hpn & Herrs).
    assert (Hchoice : ∀ i, ∃ t2,
      t2 ∈ CPState.final_states prom
        (PromiseFirstCurrent.promise_first_execution_results (prom := prom) isem term fuel s2 !!! i) ∧
      ts_sim (tstates !!! i) t2).
    { intro i. specialize (Hfin i).
      rewrite PromiseFirstCurrent.promise_first_execution_results_lookup in Hfin |- *.
      change (CPState.initmem s2) with (PState.initmem s2).
      change (CPState.events s2) with (PState.events s2).
      rewrite <- Himem, <- Hmem. eapply enum_final_sim; [apply Hstates|exact Hfin]. }
    destruct (vec_choice _ Hchoice) as [tstates2 Htstates2].
    set (st0_2 := {| CPState.tstates := tstates2; CPState.initmem := CPState.initmem s2;
                     CPState.events := CPState.events s2 |}).
    set (st0 := {| CPState.tstates := tstates; CPState.initmem := CPState.initmem s1;
                   CPState.events := CPState.events s1 |}) in *.
    assert (Hs0 : st_sim st0 st0_2).
    { split; [exact Himem|]. split; [exact Hmem|]. intro i. apply Htstates2. }
    assert (pt2 : CPState.terminated prom term st0_2).
    { pose proof (terminated_sim bbm term st0 st0_2 Hs0) as Ht.
      pose proof pt as pt'. unfold CPState.terminated, PState.terminated in Ht, pt' |- *.
      rewrite <- Ht. exact pt'. }
    assert (Hok0 : ∀ tid, ∃ bound, VMCacheState.cache_ok bound (PState.tstate tid st0)).
    { intro tid. specialize (Hfin tid).
      rewrite PromiseFirstCurrent.promise_first_execution_results_lookup in Hfin.
      eapply enum_final_ok; [apply Hok|exact Hfin]. }
    unfold st0_2, st0 in *.
    exists s2, (Some (CPState.to_final_archState (CPState.make_final prom term _ pt2))).
    split; [|split; [exact Hs|]].
    + apply (PromiseFirstCurrent.run_transition_promise_first_some_intro (prom := prom)).
      * apply Exec.elem_of_mchoosel. apply cprodn_spec. intro i.
        rewrite vlookup_map. apply Htstates2.
      * apply validate_final_state_intro.
        -- rewrite <- (nopromises_sim bbm st0 st0_2 Hs0). exact Hpn.
        -- apply (proj1 (check_valid_end_sim_any st0 st0_2 Hs0 Hok0)). exact Herrs.
    + cbn. f_equal. apply (to_archState_sim bbm), Hs0.
  - apply (PromiseFirstCurrent.run_transition_promise_first_none_inv (prom := prom)) in Hrun
      as (tid & ev & nst & Hev & Hpromise & ->).
    destruct (promise_sim bbm ev s1 s2 nst Hs Hpromise) as [nst2 [Hp2 Hs']].
    exists nst2, None. split; [|split; [exact Hs'|reflexivity]].
    eapply (PromiseFirstCurrent.run_transition_promise_first_none_intro (prom := prom));
      [|exact Hp2|reflexivity].
    rewrite PromiseFirstCurrent.promise_first_execution_results_lookup in Hev |- *.
    change (CPState.initmem s2) with (PState.initmem s2).
    change (CPState.events s2) with (PState.events s2).
    rewrite <- Himem, <- Hmem. eapply enum_promises_sim; [apply Hstates|exact Hev].
Qed.

(** Transitions of either runner from a reachable state, on a simulated state. *)
Theorem reachable_transition_sim initMs use_pf fuel (s1 s2 s1' : PState.t TState.t Ev.t n) r1 :
  PromiseFirstReachable prom isem term initMs use_pf s1 → st_sim s1 s2 →
  Exec.elem_of_results (s1', r1)
    ((if use_pf then CPState.run_transition_promise_first_uncached isem prom term fuel
      else CPState.run_transition isem prom term fuel) s1) →
  ∃ s2' r2, Exec.elem_of_results (s2', r2)
      ((if use_pf then CPState.run_transition_promise_first_uncached isem prom term fuel
        else CPState.run_transition isem prom term fuel) s2) ∧
    st_sim s1' s2' ∧ option_map (λ f, projT1 f) r1 = option_map (λ f, projT1 f) r2.
Proof.
  intros Hreach Hs. pose proof (VMViews.reachable_ok bbm isem term initMs use_pf s1 Hreach) as Hok.
  destruct use_pf.
  - apply run_transition_promise_first_sim; assumption.
  - apply run_transition_sim'; assumption.
Qed.
End PromiseFirst.


End VMCacheSimOutcome.

(** * Merged translation results do not depend on allocation order

    Thread 0 starts with TTBR0_EL1 = 0, whose level-0 slot is invalid. A
    root at 0x2000 maps VA 0 through the table at 0x1000 to a level-1 block.
    Thread 1 writes the same table descriptor to address 0, so after the write
    both roots map VA 0 to the same block.

    - Direct order: thread 0 writes TTBR0_EL1 = 0x2000 at view 0, then thread 1
      promises the write at timestamp 1.
    - Promise-first order: the write is promised first, then the TTBR0_EL1
      write at view 0 rolls back to 0 and refills.

    Both caches have the same histories, roots and ETS ([cache_sim]), and the
    unmerged lookups are permutations ([lookup_perm]). The global level-1 row
    holds the two block entries in opposite allocation orders. When
    [TLB.Result.merge] kept the first root and path of each mergeable class,
    it kept root 0x2000 in the direct order and root 0 in the promise-first
    order, and [run_trans_start] stored that root in [IIS.trs]. Merging now
    keeps the smallest walk, so both orders give root 0. *)
Module VMCacheSimMergeWitness.
Import VMPromising VMCacheSim.
Open Scope stdpp.
Open Scope bv.

Definition imem : memoryMap :=
  ∅ |> mem_insert 0 8 0 |> mem_insert 4096 8 1 |> mem_insert 8192 8 4099.
Definition regs : registerMap :=
  ∅ |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
    |> reg_insert ID_AA64MMFR1_EL1 0.
Definition write := Ev.Msg (Msg.make 1 0 8 4099).
Definition root : bv 16 * bv 64 * bool := (0, 8192, false).
Definition fallback := TLB.make TLB.VATLB.init ∅ ∅ [] 0.
Definition start : TLB.t :=
  match TLB.init 0 imem regs with Ok cache => cache | Error _ => fallback end.
Definition direct_root : TLB.t :=
  match TLB.fill_asid_root 0 imem [] root 0 start with Ok (c, _) => c | Error _ => fallback end.
Definition direct : TLB.t :=
  match TLB.fill_promise 0 imem [write] write direct_root with
  | Ok (c, _) => c | Error _ => fallback end.
Definition promised : TLB.t :=
  match TLB.fill_promise 0 imem [write] write start with Ok (c, _) => c | Error _ => fallback end.
Definition replayed : TLB.t :=
  match TLB.fill_asid_root 0 imem [write] root 0 promised with
  | Ok (c, _) => c | Error _ => fallback end.

Lemma start_ok : TLB.init 0 imem regs = Ok start.
Proof. reflexivity. Qed.
Lemma direct_root_ok : TLB.fill_asid_root 0 imem [] root 0 start = Ok (direct_root, ()).
Proof. reflexivity. Qed.
Lemma direct_ok : TLB.fill_promise 0 imem [write] write direct_root = Ok (direct, ()).
Proof. reflexivity. Qed.
Lemma promised_ok : TLB.fill_promise 0 imem [write] write start = Ok (promised, ()).
Proof. reflexivity. Qed.
Lemma replayed_ok : TLB.fill_asid_root 0 imem [write] root 0 promised = Ok (replayed, ()).
Proof. reflexivity. Qed.

Lemma start_wf : wf start.
Proof.
  split; [exact (VMCacheIndexed.init 0 imem regs start start_ok)|].
  exact (VMCacheLastTLBI.unique_init 0 imem regs start start_ok).
Qed.

Lemma direct_wf : wf direct.
Proof.
  destruct start_wf as [Hvalid Hunique]. split.
  - eapply VMCacheIndexed.fill_promise; [|exact direct_ok].
    eapply VMCacheIndexed.fill_asid_root; [exact Hvalid|exact direct_root_ok].
  - eapply VMCacheLastTLBI.unique_fill_promise; [|exact direct_ok].
    eapply VMCacheLastTLBI.unique_fill_asid_root; [exact Hunique|exact direct_root_ok].
Qed.

Lemma replayed_wf : wf replayed.
Proof.
  destruct start_wf as [Hvalid Hunique]. split.
  - eapply VMCacheIndexed.fill_asid_root; [|exact replayed_ok].
    eapply VMCacheIndexed.fill_promise; [exact Hvalid|exact promised_ok].
  - eapply VMCacheLastTLBI.unique_fill_asid_root; [|exact replayed_ok].
    eapply VMCacheLastTLBI.unique_fill_promise; [exact Hunique|exact promised_ok].
Qed.

(* Injecting the concrete caches would unfold and compute them. *)
Lemma ok_pair_inj {E A B} (x y : A) (u v : B) : @Ok E _ (x, u) = Ok (y, v) → x = y.
Proof. intro H. injection H as Hx _. exact Hx. Qed.

Theorem direct_replayed_sim : cache_sim direct replayed.
Proof.
  destruct start_wf as [Hvalid Hunique].
  assert (Hroots : Forall (λ entry : (bv 16 * bv 64 * bool) * nat, (entry.2 ≤ length (@nil Ev.t))%nat)
    (TLB.asid_roots start)) by (vm_compute; repeat constructor).
  destruct (VMCacheContext.replay_promise_before_asid_root 0 imem [] write root 0 start promised
    direct_root direct (le_n 0) Hvalid Hunique Hroots promised_ok direct_root_ok direct_ok)
    as [ending [Hrun Hobs]].
  rewrite replayed_ok in Hrun. apply ok_pair_inj in Hrun. subst ending.
  split; [exact Hobs|]. split; [exact direct_wf|exact replayed_wf].
Qed.

Definition lookup cache := TLB.lookup 0 imem [write] cache false false 0 0 0 1 0.

Lemma direct_lookup : Exec.results (lookup direct) =
  [TLB.Result.make 8192 [4099; 1] 0 1 None; TLB.Result.make 0 [4099; 1] 1 1 None].
Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.

Lemma replayed_lookup : Exec.results (lookup replayed) =
  [TLB.Result.make 0 [4099; 1] 1 1 None; TLB.Result.make 8192 [4099; 1] 0 1 None].
Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.

(** Before merging kept the smallest walk, the direct order merged to root
    0x2000 and the promise-first order to root 0. *)
Lemma direct_merged : TLB.Result.merge (Exec.results (lookup direct)) =
  [TLB.Result.make 0 [4099; 1] 0 1 None].
Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.

Lemma replayed_merged : TLB.Result.merge (Exec.results (lookup replayed)) =
  [TLB.Result.make 0 [4099; 1] 0 1 None].
Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.

Theorem merge_agrees_on_simulated_caches :
  cache_sim direct replayed ∧
  Exec.results (lookup direct) ≡ₚ Exec.results (lookup replayed) ∧
  TLB.Result.merge (Exec.results (lookup direct)) =
    TLB.Result.merge (Exec.results (lookup replayed)).
Proof.
  split; [exact direct_replayed_sim|]. split.
  - unfold lookup.
    exact (proj1 (lookup_perm 0 imem [write] false false 0 0 0 1 direct replayed 0 direct_replayed_sim)).
  - rewrite direct_merged, replayed_merged. reflexivity.
Qed.

End VMCacheSimMergeWitness.
