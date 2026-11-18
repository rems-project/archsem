(******************************************************************************)
(* Thread steps over a history with a removed TLBI                            *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheIndexed PromiseFirstSailVMCacheSim
  PromiseFirstSailVMCacheOrder PromiseFirstSailVMCacheHistory PromiseFirstSailVMCacheExchange
  PromiseFirstSailVMSwapRemove.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

(** The removal direction of the exchange simulation at the level of thread
    states, for a thread [tid] that is not the recipient of the TLBI
    [Ev.Tlbi tlbi rc k] at timestamp [p = S (length r)] of the longer history
    [l ++ Ev.Tlbi tlbi rc k :: r]. The shorter thread state equals
    [ts_map (unshift p)] of the longer one outside the cache; the caches are
    related up to [VMCacheSim.cache_sim] after [tlb_map (unshift p)].

    The cache of the longer state carries the invariant [TI]: it is ordered
    and bounded by the history length, invariant [J] of VMSwapRemove holds
    while no context synchronization at or after [p] happened ([vcse < p]),
    and roots of time [p] exist only after an MSR or a CSE at [p]
    ([p ≤ vcse ⊔ vmsr]). With it every context change of the longer state has
    a counterpart at [unshift p] of its time. *)

Module VMSwapRemoveRun.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemove.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma unshift_max p a b : unshift p (a `max` b) = unshift p a `max` unshift p b.
Proof. unfold unshift. repeat case_decide; lia. Qed.

(** * Cache steps with the invariant *)

Section Steps.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation q := (length r).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).

Definition TI (l : Memory.t) (vc vm : nat) (c : TLB.t) : Prop :=
  VMCacheOrder.good (length (l ++ e :: r)) c ∧ (vc < p → J imem l r tlbi rc k c) ∧
  (proots r c ≠ [] → p ≤ vc `max` vm).

Lemma TI_mono l vc vm vc' vm' c : vc ≤ vc' → vm ≤ vm' → TI l vc vm c → TI l vc' vm' c.
Proof.
  clear Hrc. intros H1 H2 (Hg & HJ & Hr). split; [exact Hg|]. split; [intro; apply HJ; lia|].
  intro H. specialize (Hr H). lia.
Qed.

Lemma fill_asid_root_step l root t vc vm c d c' :
  vc ≤ t → t ≤ vm → t ≤ length (l ++ e :: r) → TI l vc vm c →
  VMCacheSim.cache_sim (tlb_map g c) d →
  TLB.fill_asid_root tid imem (l ++ e :: r) root t c = Ok (c', ()) →
  ∃ d', TLB.fill_asid_root tid imem (l ++ r) root (g t) d = Ok (d', ()) ∧
    VMCacheSim.cache_sim (tlb_map g c') d' ∧ TI l vc vm c'.
Proof using Hrc.
  intros Hvc Hvm Hlen (Hg & HJ & Hpr) Hsim Hrun.
  assert (Hlen' : t ≤ S (length (l ++ r))) by (rewrite !length_app in *; cbn in *; lia).
  assert (HTI : TI l vc vm c').
  { split; [|split].
    - pose proof (VMCacheOrder.good_fill_asid_root _ _ _ _ _ _ _ _ Hg Hrun) as G.
      replace (t `max` length (l ++ e :: r)) with (length (l ++ e :: r)) in G by lia. exact G.
    - intro Hlt. destruct (decide (t ≤ q)) as [Hle|Hgt].
      + exact (J_fill_asid_root_below tid imem l r tlbi rc k Hrc root t _ c c' Hle Hg Hrun).
      + destruct (decide (t = p)) as [->|Hne].
        * exact (J_fill_asid_root_p tid imem l r tlbi rc k root _ c c' (HJ Hlt) Hg Hrun).
        * exact (J_fill_asid_root_above tid imem l r tlbi rc k root t c c' ltac:(lia)
            (HJ Hlt) Hrun).
    - pose proof (VMCacheExchange.fill_asid_root_roots _ _ _ _ _ _ _ Hrun) as Hroots.
      unfold proots. rewrite Hroots, filter_cons. case_decide as Ht.
      + cbn in Ht. intros _. lia.
      + exact Hpr. }
  destruct (decide (S t ≤ q)) as [Hlt|Hge].
  - destruct (fill_asid_root_remove_sim tid imem l r tlbi rc k Hrc root t Hlt c d c' () Hsim Hrun)
      as [d' [Hd Hs]].
    exists d'. auto.
  - destruct (decide (t = q)) as [->|Hne].
    + assert (HJc : J imem l r tlbi rc k c) by (apply HJ; lia).
      destruct (fill_asid_root_remove_q tid imem l r tlbi rc k Hrc root c d c' () HJc Hsim Hrun)
        as [d' [Hd Hs]].
      exists d'. rewrite unshift_lt by lia. auto.
    + pose proof (fill_asid_root_remove tid imem l r tlbi rc k Hrc root t ltac:(lia) Hlen') as N.
      destruct (wsq_of_natural _ _ _ N (VMCacheSim.fill_asid_root_sim _ _ _ _ _) c d c' ()
        Hsim Hrun) as [d' [Hd Hs]].
      exists d'. auto.
Qed.

Lemma fill_cse_step l ttbr0 ttbr1 v vc vm c d c' :
  vc `max` vm ≤ v → v ≤ length (l ++ e :: r) → TI l vc vm c →
  VMCacheSim.cache_sim (tlb_map g c) d →
  TLB.fill_cse tid imem (l ++ e :: r) v ttbr0 ttbr1 c = Ok (c', ()) →
  ∃ d', TLB.fill_cse tid imem (l ++ r) (g v) ttbr0 ttbr1 d = Ok (d', ()) ∧
    VMCacheSim.cache_sim (tlb_map g c') d' ∧ TI l (v `max` vc) vm c'.
Proof using Hrc.
  intros Hv Hlen (Hg & HJ & Hpr) Hsim Hrun.
  assert (HTI : TI l (v `max` vc) vm c').
  { split; [|split].
    - pose proof (VMCacheOrder.good_fill_cse _ _ _ _ _ _ _ _ _ Hg Hrun) as G.
      replace (v `max` length (l ++ e :: r)) with (length (l ++ e :: r)) in G by lia. exact G.
    - intro Hlt. eapply (J_fill_cse_below tid imem l r tlbi rc k Hrc ttbr0 ttbr1 v); [lia|exact Hg|exact Hrun].
    - intro Hne. destruct (decide (v = p)) as [->|Hvp]; [lia|]. exfalso. apply Hne.
      destruct (fill_cse_inv _ _ _ _ _ _ _ _ Hrun) as [rs [Hrs Hff]].
      pose proof (VMCacheRoots.fill_from_btw _ _ _ rs _ _ _ _ c' () Hff) as Hroots.
      unfold VMCacheRoots.config in Hroots.
      assert (Hr : TLB.asid_roots c' = rs) by (rewrite Hroots; reflexivity).
      unfold proots. rewrite Hr, filter_roots_eq_nil; [reflexivity|].
      intros x Hx. rewrite list.Forall_forall in Hrs. rewrite (Hrs x Hx). exact Hvp. }
  destruct (decide (v = q)) as [->|Hne].
  - assert (HJc : J imem l r tlbi rc k c) by (apply HJ; lia).
    assert (Hnil : proots r c = []).
    { destruct (decide (proots r c = [])) as [E|E]; [exact E|]. specialize (Hpr E). lia. }
    destruct (fill_cse_remove_q tid imem l r tlbi rc k Hrc ttbr0 ttbr1 c d c' () (conj HJc Hnil)
      Hsim Hrun) as [d' [Hd Hs]].
    exists d'. rewrite unshift_lt by lia. auto.
  - pose proof (fill_cse_remove tid imem l r tlbi rc k Hrc v ttbr0 ttbr1 ltac:(cbn; lia)) as N.
    destruct (wsq_of_natural _ _ _ N (VMCacheSim.fill_cse_sim _ _ _ _ _ _) c d c' ()
      Hsim Hrun) as [d' [Hd Hs]].
    exists d'. auto.
Qed.

Lemma fill_promise_step l ev vc vm c d c' :
  TI l vc vm c → VMCacheSim.cache_sim (tlb_map g c) d →
  TLB.fill_promise tid imem (ev :: l ++ e :: r) ev c = Ok (c', ()) →
  ∃ d', TLB.fill_promise tid imem (ev :: l ++ r) ev d = Ok (d', ()) ∧
    VMCacheSim.cache_sim (tlb_map g c') d' ∧ TI (ev :: l) vc vm c'.
Proof.
  clear Hrc. intros (Hg & HJ & Hpr) Hsim Hrun.
  destruct (wsq_of_natural _ _ _ (fill_promise_remove tid imem l r tlbi rc k ev)
    (VMCacheSim.fill_promise_sim _ _ _ _) c d c' () Hsim Hrun) as [d' [Hd Hs]].
  exists d'. split; [exact Hd|]. split; [exact Hs|]. split; [|split].
  - exact (VMCacheOrder.good_fill_promise tid imem (ev :: l ++ e :: r) ev (length (l ++ e :: r))
      c c' ltac:(cbn; lia) Hg Hrun).
  - intro Hlt. exact (J_fill_promise tid imem l r tlbi rc k ev c c' (HJ Hlt) Hrun).
  - pose proof (VMCacheRoots.fill_promise _ _ _ _ c c' () Hrun) as Hroots.
    unfold VMCacheRoots.config in Hroots. unfold proots. rewrite Hroots. exact Hpr.
Qed.
End Steps.

(** * Thread states *)

Lemma ts_map_setv_tlb f o a : ts_map f (setv TState.tlb o a) = setv TState.tlb (tlb_map f <$> o) (ts_map f a).
Proof. destruct a. reflexivity. Qed.

Lemma run_tlb_some_inv upd ts c ts' : TState.tlb ts = Some c → TState.run_tlb upd ts = Ok ts' →
  ∃ c', upd c = Ok (c', ()) ∧ ts' = setv TState.tlb (Some c') ts.
Proof.
  intros Hc Hrun. unfold TState.run_tlb in Hrun. rewrite Hc in Hrun.
  destruct (upd c) as [[c' []]|err] eqn:Hu; cbn in Hrun; [|discriminate].
  injection Hrun as <-. eexists. split; reflexivity.
Qed.

Lemma run_tlb_some_intro upd ts d d' : TState.tlb ts = Some d → upd d = Ok (d', ()) →
  TState.run_tlb upd ts = Ok (setv TState.tlb (Some d') ts).
Proof. intros Hd Hu. unfold TState.run_tlb. rewrite Hd, Hu. reflexivity. Qed.

Lemma run_tlb_none upd ts : TState.tlb ts = None → TState.run_tlb upd ts = Ok ts.
Proof. intro H. unfold TState.run_tlb. rewrite H. reflexivity. Qed.

Lemma othrow_run_inv {A B} (s : string) (o : option A) (kk : A → stateT TLB.t (result string) B) c c' x :
  (othrow s o ≫= kk) c = Ok (c', x) → ∃ a, o = Some a ∧ kk a c = Ok (c', x).
Proof. destruct o as [a|]; [|discriminate]. intro H. exists a. split; [reflexivity|exact H]. Qed.

Section Thread.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation q := (length r).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).

(** The longer thread state [a] and the shorter one [b]. *)
Definition ts_rel (a b : TState.t) : Prop := VMCacheSim.ts_sim (ts_map g a) b.

Definition ts_inv (l : Memory.t) (a : TState.t) : Prop :=
  ∀ c, TState.tlb a = Some c → TI imem r tlbi rc k l (TState.vcse a) (TState.vmsr a) c.

Lemma ts_rel_setv a b c d : ts_rel a b → VMCacheSim.cache_sim (tlb_map g c) d →
  ts_rel (setv TState.tlb (Some c) a) (setv TState.tlb (Some d) b).
Proof.
  clear Hrc. intros [Hb _] Hs. unfold ts_rel. rewrite ts_map_setv_tlb, Hb, VMCacheSim.setv_tlb_twice.
  apply VMCacheSim.ts_sim_setv. exact Hs.
Qed.

Lemma ts_rel_tlb a b c : ts_rel a b → TState.tlb a = Some c →
  ∃ d, TState.tlb b = Some d ∧ VMCacheSim.cache_sim (tlb_map g c) d.
Proof.
  clear Hrc. intros [_ Hs] Hc. rewrite ts_map_tlb, Hc in Hs. cbn in Hs.
  destruct (TState.tlb b) as [d|]; [|contradiction]. eauto.
Qed.

Lemma ts_rel_tlb_none a b : ts_rel a b → TState.tlb a = None → TState.tlb b = None.
Proof.
  clear Hrc. intros [_ Hs] Hc. rewrite ts_map_tlb, Hc in Hs. cbn in Hs.
  destruct (TState.tlb b); [contradiction|reflexivity].
Qed.

(** Every field other than the cache is mapped. *)
Lemma ts_rel_frame a b : ts_rel a b → setv TState.tlb None b = setv TState.tlb None (ts_map g a).
Proof. clear Hrc. intro H. symmetry. exact (VMCacheSim.ts_sim_frame _ _ H). Qed.

Lemma process_event_remove l ev a b a' : ts_rel a b → ts_inv l a →
  TState.process_event tid imem (ev :: l ++ e :: r) ev a = Ok a' →
  ∃ b', TState.process_event tid imem (ev :: l ++ r) ev b = Ok b' ∧ ts_rel a' b' ∧
    ts_inv (ev :: l) a'.
Proof.
  clear Hrc. intros Hrel Hinv Hrun. unfold TState.process_event in Hrun |- *.
  destruct (TState.tlb a) as [c|] eqn:Hc.
  - destruct (ts_rel_tlb _ _ _ Hrel Hc) as [d [Hd Hsim]].
    destruct (run_tlb_some_inv _ _ _ _ Hc Hrun) as [c' [Hf ->]].
    destruct (fill_promise_step tid imem r tlbi rc k l ev _ _ c d c' (Hinv c Hc) Hsim Hf)
      as [d' [Hd' [Hs HTI]]].
    eexists. split; [exact (run_tlb_some_intro _ _ _ _ Hd Hd')|]. split.
    + apply ts_rel_setv; assumption.
    + intros c0 Hc0. cbn in Hc0. injection Hc0 as <-. exact HTI.
  - rewrite (run_tlb_none _ _ Hc) in Hrun. injection Hrun as <-.
    eexists. split; [exact (run_tlb_none _ _ (ts_rel_tlb_none _ _ Hrel Hc))|].
    split; [exact Hrel|]. intros c0 Hc0. rewrite Hc in Hc0. discriminate.
Qed.

Lemma cse_pre_map v a : VMCacheSim.cse_pre (g v) (ts_map g a) = ts_map g (VMCacheSim.cse_pre v a).
Proof.
  clear Hrc. destruct a. unfold VMCacheSim.cse_pre, TState.update, set, ts_map.
  cbn -[unshift regs_map dmap_map fmap map lev_map tlb_map fwd_map xcl_map].
  rewrite <- unshift_max. reflexivity.
Qed.

Theorem cse_remove l v a b a' : ts_rel a b → ts_inv l a →
  TState.vcse a `max` TState.vmsr a ≤ v → v ≤ length (l ++ e :: r) →
  TState.cse imem (l ++ e :: r) tid v a = Ok a' →
  ∃ b', TState.cse imem (l ++ r) tid (g v) b = Ok b' ∧ ts_rel a' b' ∧ ts_inv l a'.
Proof using Hrc.
  intros Hrel Hinv Hv Hlen Hrun.
  pose proof (proj1 Hrel) as Hb. set (ob := TState.tlb b) in Hb.
  rewrite <- (VMCacheSim.setv_tlb_same a) in Hrun.
  rewrite VMCacheSim.cse_shape in Hrun. rewrite Hb, VMCacheSim.cse_shape.
  rewrite cse_pre_map.
  set (X := VMCacheSim.cse_pre v a) in *.
  rewrite !ts_map_read_sreg_direct.
  destruct (TState.tlb a) as [c|] eqn:Hc.
  - destruct (ts_rel_tlb _ _ _ Hrel Hc) as [d [Hd Hsim]]. fold ob in Hd.
    destruct (TState.run_tlb _ (setv TState.tlb (Some c) X)) as [mid|err] eqn:Hmid;
      cbn in Hrun; [|discriminate]. injection Hrun as <-.
    destruct (run_tlb_some_inv _ _ c _ (VMCacheSim.tlb_setv X (Some c)) Hmid) as [c' [Hu ->]].
    apply bind_unit_run in Hu as [c0 [H0 Hu]]. injection H0 as <-.
    apply othrow_run_inv in Hu as [vv0 [Hvv0 Hf]].
    destruct (fill_cse_step tid imem r tlbi rc k Hrc l vv0.1 _ v _ _ c d c'
      ltac:(exact Hv) Hlen (Hinv c Hc) Hsim Hf) as [d' [Hd' [Hs HTI]]].
    set (U := mret () ≫= λ _, othrow "Can't read TTBR0_EL1"
        (vv_map g <$> TState.read_sreg_direct X TTBR0_EL1) ≫= λ ttbr0 : bv 64 * view,
        let ttbr1 := fst <$> (vv_map g <$> TState.read_sreg_direct X TTBR1_EL1) in
        TLB.fill_cse tid imem (l ++ r) (g v) ttbr0.1 ttbr1).
    assert (HU : U d = Ok (d', ())).
    { unfold U. rewrite Hvv0. cbn [fmap option_fmap option_map vv_map fst].
      replace (fst <$> (vv_map g <$> TState.read_sreg_direct X TTBR1_EL1))
        with (fst <$> TState.read_sreg_direct X TTBR1_EL1)
        by (destruct (TState.read_sreg_direct X TTBR1_EL1); reflexivity).
      exact Hd'. }
    rewrite Hd. rewrite (run_tlb_some_intro U (setv TState.tlb (Some d) (ts_map g X)) d d'
      (VMCacheSim.tlb_setv (ts_map g X) (Some d)) HU).
    eexists. split; [reflexivity|]. split.
    + unfold ts_rel. rewrite !ts_map_setv_tlb, !VMCacheSim.setv_tlb_twice.
      apply VMCacheSim.ts_sim_setv. exact Hs.
    + intros c1 Hc1. cbn in Hc1. injection Hc1 as <-. exact HTI.
  - assert (Hob : ob = None).
    { unfold ob. exact (ts_rel_tlb_none _ _ Hrel Hc). }
    rewrite (run_tlb_none _ _ (VMCacheSim.tlb_setv X None)) in Hrun. cbn in Hrun.
    injection Hrun as <-.
    rewrite Hob, (run_tlb_none _ (setv TState.tlb None (ts_map g X))
      (VMCacheSim.tlb_setv (ts_map g X) None)).
    eexists. split; [reflexivity|]. split.
    + unfold ts_rel. rewrite !ts_map_setv_tlb.
      apply VMCacheSim.ts_sim_setv. exact I.
    + intros c1 Hc1. discriminate.
Qed.
End Thread.

(** * System register writes *)

Lemma mapM_map_eq {A B C} (f : B → stateT TLB.t (result string) C) (h : A → B) (xs : list A) :
  mapM f (map h xs) = mapM (f ∘ h) xs.
Proof. induction xs as [|x xs IH]; [reflexivity|]. cbn [mapM map]. rewrite IH. reflexivity. Qed.

Lemma mapM_ext_eq {A B} (f f' : A → stateT TLB.t (result string) B) (xs : list A) :
  (∀ x, f x = f' x) → mapM f xs = mapM f' xs.
Proof. intro H. induction xs as [|x xs IH]; [reflexivity|]. cbn [mapM]. rewrite H, IH. reflexivity. Qed.

Definition wsreg_upd (tid : nat) (imem : memoryMap) (mem : Memory.t) (sreg : reg)
    (val : reg_type sreg) (v : view) (ts : TState.t) : stateT TLB.t (result string) () :=
  match sreg return reg_type sreg → stateT TLB.t (result string) () with
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
  end val.

Lemma add_wsreg_upd tid imem mem sreg val v ts :
  TState.add_wsreg tid imem mem sreg val v ts =
    TState.run_tlb (wsreg_upd tid imem mem sreg val v ts) ts ≫=
    (λ ts, ts |> set TState.levs ((LEv.Wsreg (WSReg.make sreg val v))::.) |> mret (M := result string)).
Proof. reflexivity. Qed.

Section Msr.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation q := (length r).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).

Lemma mapM_step {A} (P : TLB.t → Prop) (fa fb : A → stateT TLB.t (result string) ()) (xs : list A) :
  (∀ x c d c', x ∈ xs → P c → VMCacheSim.cache_sim (tlb_map g c) d → fa x c = Ok (c', ()) →
    ∃ d', fb x d = Ok (d', ()) ∧ VMCacheSim.cache_sim (tlb_map g c') d' ∧ P c') →
  ∀ c d c' ys, P c → VMCacheSim.cache_sim (tlb_map g c) d → mapM fa xs c = Ok (c', ys) →
    ∃ d', mapM fb xs d = Ok (d', ys) ∧ VMCacheSim.cache_sim (tlb_map g c') d' ∧ P c'.
Proof.
  clear Hrc. induction xs as [|x xs IH]; intros Hstep c d c' ys HP Hsim Hrun.
  - cbn in Hrun. injection Hrun as <- <-. exists d. split; [reflexivity|]. auto.
  - cbn [mapM] in Hrun. apply bind_inv in Hrun as [c1 [[] [H1 Hrun]]].
    apply bind_inv in Hrun as [c2 [zs [H2 H3]]]. cbn in H3. injection H3 as <- <-.
    destruct (Hstep x c d c1 ltac:(apply elem_of_cons; left; reflexivity) HP Hsim H1)
      as [d1 [Hd1 [Hs1 HP1]]].
    assert (Hstep' : ∀ x0 c0 d0 c0', x0 ∈ xs → P c0 → VMCacheSim.cache_sim (tlb_map g c0) d0 →
      fa x0 c0 = Ok (c0', ()) →
      ∃ d', fb x0 d0 = Ok (d', ()) ∧ VMCacheSim.cache_sim (tlb_map g c0') d' ∧ P c0').
    { intros x0 c0 d0 c0' Hin. apply Hstep. apply elem_of_cons. right. exact Hin. }
    destruct (IH Hstep' c1 d1 c2 zs HP1 Hs1 H2) as [d2 [Hd2 [Hs2 HP2]]].
    exists d2. split; [|auto]. cbn [mapM].
    apply (bind_intro _ _ d d1 d2 () (() :: zs)); [exact Hd1|].
    apply (bind_intro _ _ d1 d2 d2 zs (() :: zs)); [exact Hd2|reflexivity].
Qed.

Definition ttbr_ok (bound vm : nat) (ts : TState.t) : Prop :=
  (∀ vs, TState.read_sreg_indirect ts TTBR0_EL1 = Some vs → ∀ vv, vv ∈ vs → vv.2 ≤ vm ∧ vv.2 ≤ bound) ∧
  (∀ vs, TState.read_sreg_indirect ts TTBR1_EL1 = Some vs → ∀ vv, vv ∈ vs → vv.2 ≤ vm ∧ vv.2 ≤ bound).

Lemma wsreg_upd_step l sreg val v ts vm c d c' :
  TState.vcse ts ≤ v → v ≤ vm → v ≤ length (l ++ e :: r) →
  ttbr_ok (length (l ++ e :: r)) vm ts →
  TI imem r tlbi rc k l (TState.vcse ts) vm c → VMCacheSim.cache_sim (tlb_map g c) d →
  wsreg_upd tid imem (l ++ e :: r) sreg val v ts c = Ok (c', ()) →
  ∃ d', wsreg_upd tid imem (l ++ r) sreg val (g v) (ts_map g ts) d = Ok (d', ()) ∧
    VMCacheSim.cache_sim (tlb_map g c') d' ∧ TI imem r tlbi rc k l (TState.vcse ts) vm c'.
Proof using Hrc.
  intros Hvc Hvm Hlen [Hok0 Hok1] HTI Hsim Hrun.
  destruct sreg as [r'|r'|r'|r']; unfold wsreg_upd in Hrun |- *;
    try (cbv beta iota zeta in Hrun |- *; injection Hrun as <-; exists d; auto; fail).
  all: destruct r'; cbv beta iota zeta in Hrun |- *;
    try (injection Hrun as <-; exists d; auto; fail).
  - (* TTBR0_EL1 *)
    apply bind_unit_run in Hrun as [c1 [H1 Hrun]].
    destruct (fill_asid_root_step tid imem r tlbi rc k Hrc l _ v _ _ c d c1 Hvc Hvm Hlen HTI Hsim H1)
      as [d1 [Hd1 [Hs1 HTI1]]].
    apply bind_inv in Hrun as [c2 [zs [H2 H3]]]. cbn in H3. injection H3 as <-.
    set (xs := default [] (TState.read_sreg_indirect ts TTBR1_EL1)) in *.
    assert (Hxs : ∀ vv, vv ∈ xs → vv.2 ≤ vm ∧ vv.2 ≤ length (l ++ e :: r)).
    { unfold xs. destruct (TState.read_sreg_indirect ts TTBR1_EL1) as [vs|] eqn:E; cbn.
      - exact (Hok1 vs eq_refl).
      - intros vv Hin. inversion Hin. }
    set (fa := λ '(ttbr1, v1), TLB.fill_asid_root tid imem (l ++ e :: r)
      (bv_extract 48 16 val, ttbr1, true) (v ⊔ v1)) in H2.
    set (fb := λ '(ttbr1, v1), TLB.fill_asid_root tid imem (l ++ r)
      (bv_extract 48 16 val, ttbr1, true) (g (v ⊔ v1))).
    assert (Hstep : ∀ (x : reg_type TTBR1_EL1 * view) y z z', x ∈ xs → TI imem r tlbi rc k l (TState.vcse ts) vm y →
      VMCacheSim.cache_sim (tlb_map g y) z → fa x y = Ok (z', ()) →
      ∃ d', fb x z = Ok (d', ()) ∧ VMCacheSim.cache_sim (tlb_map g z') d' ∧
        TI imem r tlbi rc k l (TState.vcse ts) vm z').
    { intros [ttbr1 v1] y z z' Hin HP Hs Hx. destruct (Hxs _ Hin) as [Hb1 Hb2]. cbn in Hb1, Hb2.
      unfold fa in Hx. unfold fb. cbv beta iota in Hx |- *.
      assert (Hj : v ⊔ v1 = v `max` v1) by reflexivity.
      eapply (fill_asid_root_step tid imem r tlbi rc k Hrc l _ (v ⊔ v1) (TState.vcse ts) vm y z z');
        [rewrite Hj; lia|rewrite Hj; lia|rewrite Hj; lia|exact HP|exact Hs|exact Hx]. }
    destruct (mapM_step _ fa fb xs Hstep c1 d1 c2 zs HTI1 Hs1 H2) as [d2 [Hd2 [Hs2 HTI2]]].
    exists d2. split; [|auto].
    apply (bind_intro _ _ d d1 d2 () ()); [exact Hd1|].
    apply (bind_intro _ _ d1 d2 d2 zs ()); [|reflexivity].
    rewrite ts_map_read_sreg_indirect.
    replace (default [] (map (vv_map g) <$> TState.read_sreg_indirect ts TTBR1_EL1))
      with (map (vv_map g) xs)
      by (unfold xs; destruct (TState.read_sreg_indirect ts TTBR1_EL1); reflexivity).
    rewrite mapM_map_eq. rewrite (mapM_ext_eq _ fb xs); [exact Hd2|]. intros [ttbr1 v1].
    unfold fb. cbn. unfold join, join_nat. rewrite unshift_max. reflexivity.
  - (* TTBR1_EL1 *)
    apply othrow_run_inv in Hrun as [xs [Exs Hrun]].
    apply bind_inv in Hrun as [c2 [zs [H2 H3]]]. cbn in H3. injection H3 as <-.
    assert (Hxs : ∀ vv, vv ∈ xs → vv.2 ≤ vm ∧ vv.2 ≤ length (l ++ e :: r)) by exact (Hok0 xs Exs).
    set (fa := λ x : bv 64 * nat, let '(ttbr0, v0) := x in TLB.fill_asid_root tid imem (l ++ e :: r)
      (bv_extract 48 16 ttbr0, val, true) (v ⊔ v0)) in H2.
    set (fb := λ x : bv 64 * nat, let '(ttbr0, v0) := x in TLB.fill_asid_root tid imem (l ++ r)
      (bv_extract 48 16 ttbr0, val, true) (g (v ⊔ v0))).
    assert (Hstep : ∀ (x : bv (MachineWord.MachineWord.Z_idx 64) * view) y z z', x ∈ xs → TI imem r tlbi rc k l (TState.vcse ts) vm y →
      VMCacheSim.cache_sim (tlb_map g y) z → fa x y = Ok (z', ()) →
      ∃ d', fb x z = Ok (d', ()) ∧ VMCacheSim.cache_sim (tlb_map g z') d' ∧
        TI imem r tlbi rc k l (TState.vcse ts) vm z').
    { intros [ttbr0 v0] y z z' Hin HP Hs Hx. destruct (Hxs _ Hin) as [Hb1 Hb2]. cbn in Hb1, Hb2.
      unfold fa in Hx. unfold fb. cbv beta iota in Hx |- *.
      assert (Hj : v ⊔ v0 = v `max` v0) by reflexivity.
      eapply (fill_asid_root_step tid imem r tlbi rc k Hrc l _ (v ⊔ v0) (TState.vcse ts) vm y z z');
        [rewrite Hj; lia|rewrite Hj; lia|rewrite Hj; lia|exact HP|exact Hs|exact Hx]. }
    destruct (mapM_step _ fa fb xs Hstep c d c2 zs HTI Hsim H2) as [d2 [Hd2 [Hs2 HTI2]]].
    exists d2. split; [|auto].
    rewrite ts_map_read_sreg_indirect, Exs. cbn [fmap option_fmap option_map].
    apply (bind_intro _ _ d d d2 (map (vv_map g) xs) ()); [reflexivity|].
    apply (bind_intro _ _ d d2 d2 zs ()); [|reflexivity].
    rewrite mapM_map_eq. rewrite (mapM_ext_eq _ fb xs); [exact Hd2|]. intros [ttbr0 v0].
    unfold fb. cbn. unfold join, join_nat. rewrite unshift_max. reflexivity.
Qed.
End Msr.

Lemma wsreg_upd_setv tid imem mem sreg val v o ts :
  wsreg_upd tid imem mem sreg val v (setv TState.tlb o ts) = wsreg_upd tid imem mem sreg val v ts.
Proof. reflexivity. Qed.

Lemma set_levs_setv_tlb F o ts :
  set TState.levs F (setv TState.tlb o ts) = setv TState.tlb o (set TState.levs F ts).
Proof. destruct ts. reflexivity. Qed.

Lemma ts_map_set_levs_wsreg f w ts :
  ts_map f (set TState.levs (LEv.Wsreg w ::.) ts) =
  set TState.levs (LEv.Wsreg (wsreg_map f w) ::.) (ts_map f ts).
Proof. destruct ts. reflexivity. Qed.

Lemma ts_rel_set_levs_wsreg r w a b : ts_rel r a b →
  ts_rel r (set TState.levs (LEv.Wsreg w ::.) a)
    (set TState.levs (LEv.Wsreg (wsreg_map (unshift (S (length r))) w) ::.) b).
Proof.
  intro H. unfold ts_rel in *. rewrite ts_map_set_levs_wsreg.
  apply VMCacheSim.ts_sim_inv in H as (ts & c1 & c2 & -> & -> & Hs).
  rewrite !set_levs_setv_tlb. apply VMCacheSim.ts_sim_setv, Hs.
Qed.

Section MsrThread.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).

Theorem add_wsreg_remove l sreg val v a b a' :
  ts_rel r a b → ts_inv imem r tlbi rc k l a →
  TState.vcse a ≤ v → v ≤ length (l ++ e :: r) →
  ttbr_ok (length (l ++ e :: r)) (v `max` TState.vmsr a) a →
  TState.add_wsreg tid imem (l ++ e :: r) sreg val v a = Ok a' →
  ∃ b', TState.add_wsreg tid imem (l ++ r) sreg val (g v) b = Ok b' ∧ ts_rel r a' b' ∧
    ts_inv imem r tlbi rc k l (TState.update TState.vmsr v a').
Proof using Hrc.
  intros Hrel Hinv Hvc Hlen Hok Hrun.
  rewrite add_wsreg_upd in Hrun |- *.
  destruct (TState.run_tlb (wsreg_upd tid imem (l ++ e :: r) sreg val v a) a) as [mid|err] eqn:Hmid;
    cbn in Hrun; [|discriminate]. injection Hrun as <-.
  destruct (TState.tlb a) as [c|] eqn:Hc.
  - destruct (ts_rel_tlb r a b c Hrel Hc) as [d [Hd Hsim]].
    destruct (run_tlb_some_inv _ _ _ _ Hc Hmid) as [c' [Hu ->]].
    destruct (wsreg_upd_step tid imem r tlbi rc k Hrc l sreg val v a (v `max` TState.vmsr a) c d c'
      Hvc ltac:(lia) Hlen Hok (TI_mono imem r tlbi rc k l (TState.vcse a) (TState.vmsr a) (TState.vcse a)
        (v `max` TState.vmsr a) c ltac:(lia) ltac:(lia) (Hinv c Hc))
      Hsim Hu) as [d' [Hd' [Hs HTI]]].
    assert (HU : wsreg_upd tid imem (l ++ r) sreg val (g v) b d = Ok (d', ())).
    { rewrite (proj1 Hrel), wsreg_upd_setv. exact Hd'. }
    rewrite (run_tlb_some_intro _ b d d' Hd HU). cbn.
    eexists. split; [reflexivity|]. split.
    + apply (ts_rel_set_levs_wsreg r (WSReg.make sreg val v)), ts_rel_setv; assumption.
    + intros c1 Hc1. cbn in Hc1. injection Hc1 as <-. exact HTI.
  - rewrite (run_tlb_none _ _ Hc) in Hmid. injection Hmid as <-.
    rewrite (run_tlb_none _ _ (ts_rel_tlb_none r a b Hrel Hc)). cbn.
    eexists. split; [reflexivity|]. split.
    + apply (ts_rel_set_levs_wsreg r (WSReg.make sreg val v)), Hrel.
    + intros c1 Hc1. assert (H : TState.tlb a = Some c1) by exact Hc1. congruence.
Qed.
End MsrThread.

(** * TTBR value views are below [vmsr]

    Every TTBR value a root fill can use comes from an MSR (view at most
    [vmsr] after it) or from the initial registers. *)

Definition msr_inv (a : TState.t) : Prop :=
  (∀ w, LEv.Wsreg w ∈ TState.levs a → WSReg.view w ≤ TState.vmsr a) ∧
  (∀ vv, dmap_lookup (TTBR0_EL1 : reg) (TState.regs a) = Some vv → vv.2 ≤ TState.vmsr a) ∧
  (∀ vv, dmap_lookup (TTBR1_EL1 : reg) (TState.regs a) = Some vv → vv.2 ≤ TState.vmsr a).

Lemma to_val_view_if_view sr w vv : WSReg.to_val_view_if sr w = Some vv → vv.2 = WSReg.view w.
Proof.
  unfold WSReg.to_val_view_if. destruct (decide _); [|discriminate].
  intro H. injection H as <-. reflexivity.
Qed.

Lemma read_sreg_direct_lev_bound V regs (sr : reg) levs :
  (∀ w, LEv.Wsreg w ∈ levs → WSReg.view w ≤ V) → (∀ vv, dmap_lookup sr regs = Some vv → vv.2 ≤ V) →
  ∀ vv, TState.read_sreg_direct_lev regs sr levs = Some vv → vv.2 ≤ V.
Proof.
  intros Hl Hr. induction levs as [|[t|w] levs IH]; cbn [TState.read_sreg_direct_lev].
  - exact Hr.
  - apply IH. intros w Hw. apply Hl. apply elem_of_cons. right. exact Hw.
  - destruct (WSReg.to_val_view_if sr w) as [vv0|] eqn:E.
    + intros vv H. injection H as <-. rewrite (to_val_view_if_view _ _ _ E).
      apply Hl. apply elem_of_cons. left. reflexivity.
    + apply IH. intros w' Hw. apply Hl. apply elem_of_cons. right. exact Hw.
Qed.

Lemma read_sreg_indirect_lev_bound V regs (sr : reg) levs :
  (∀ w, LEv.Wsreg w ∈ levs → WSReg.view w ≤ V) → (∀ vv, dmap_lookup sr regs = Some vv → vv.2 ≤ V) →
  ∀ vs, TState.read_sreg_indirect_lev regs sr levs = Some vs → ∀ vv, vv ∈ vs → vv.2 ≤ V.
Proof.
  intros Hl Hr. induction levs as [|[t|w] levs IH]; cbn [TState.read_sreg_indirect_lev];
    intros vs H vv Hin.
  - destruct (dmap_lookup sr regs) as [x|] eqn:E; rewrite E in H; cbn in H; [|discriminate].
    injection H as <-. apply list_elem_of_singleton in Hin as ->. first [exact (Hr _ E)|exact (Hr _ eq_refl)].
  - destruct (TState.read_sreg_direct_lev regs sr levs) as [x|] eqn:E; try rewrite E in H; cbn in H; [|discriminate].
    injection H as <-. apply list_elem_of_singleton in Hin as ->.
    refine (read_sreg_direct_lev_bound V regs sr levs _ Hr _ E).
    intros w Hw. apply Hl. apply elem_of_cons. right. exact Hw.
  - assert (Hl' : ∀ w', LEv.Wsreg w' ∈ levs → WSReg.view w' ≤ V).
    { intros w' Hw. apply Hl. apply elem_of_cons. right. exact Hw. }
    destruct (TState.read_sreg_indirect_lev regs sr levs) as [rest|] eqn:E; try rewrite E in H; cbn in H; [|discriminate].
    destruct (WSReg.to_val_view_if sr w) as [vv0|] eqn:E2; try rewrite E2 in H; injection H as <-.
    + apply elem_of_cons in Hin as [->|Hin].
      * rewrite (to_val_view_if_view _ _ _ E2). apply Hl. apply elem_of_cons. left. reflexivity.
      * exact (IH Hl' rest eq_refl vv Hin).
    + exact (IH Hl' rest eq_refl vv Hin).
Qed.

Lemma ttbr_ok_of_inv bound v a : msr_inv a → TState.vmsr a ≤ bound →
  ttbr_ok bound (v `max` TState.vmsr a) a.
Proof.
  intros (Hl & H0 & H1) Hb. split; intros vs Hvs vv Hin.
  - pose proof (read_sreg_indirect_lev_bound _ _ _ _ Hl H0 vs Hvs vv Hin). lia.
  - pose proof (read_sreg_indirect_lev_bound _ _ _ _ Hl H1 vs Hvs vv Hin). lia.
Qed.

Lemma run_tlb_frame upd ts ts' : TState.run_tlb upd ts = Ok ts' → ∃ o, ts' = setv TState.tlb o ts.
Proof.
  intro H. destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (run_tlb_some_inv _ _ _ _ Hc H) as [c' [_ ->]]. eauto.
  - rewrite (run_tlb_none _ _ Hc) in H. injection H as <-. exists None.
    rewrite <- Hc. symmetry. apply VMCacheSim.setv_tlb_same.
Qed.

Lemma msr_inv_setv o a : msr_inv a → msr_inv (setv TState.tlb o a).
Proof. destruct a. exact id. Qed.

Lemma msr_inv_process_event tid imem mem ev a a' : msr_inv a →
  TState.process_event tid imem mem ev a = Ok a' → msr_inv a'.
Proof. intros H Hrun. destruct (run_tlb_frame _ _ _ Hrun) as [o ->]. apply msr_inv_setv, H. Qed.

Lemma msr_inv_cse imem mem tid v a a' : msr_inv a → TState.cse imem mem tid v a = Ok a' → msr_inv a'.
Proof.
  intros (Hl & H0 & H1) Hrun. unfold TState.cse in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (run_tlb_frame _ _ _ Hmid) as [o ->]. apply msr_inv_setv.
  destruct a. cbn in *. split; [|split; assumption].
  intros w Hw. apply elem_of_cons in Hw as [Hw|Hw]; [discriminate|exact (Hl w Hw)].
Qed.

Lemma msr_inv_add_wsreg tid imem mem sreg val v a a' : msr_inv a →
  TState.add_wsreg tid imem mem sreg val v a = Ok a' → msr_inv (TState.update TState.vmsr v a').
Proof.
  intros (Hl & H0 & H1) Hrun. rewrite add_wsreg_upd in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (run_tlb_frame _ _ _ Hmid) as [o ->].
  set (a2 := TState.update TState.vmsr v
    (set TState.levs (LEv.Wsreg (WSReg.make sreg val v) ::.) (setv TState.tlb o a))).
  assert (Hv : TState.vmsr a2 = v `max` TState.vmsr a) by reflexivity.
  assert (Hlv : TState.levs a2 = LEv.Wsreg (WSReg.make sreg val v) :: TState.levs a) by reflexivity.
  assert (Hrg : TState.regs a2 = TState.regs a) by reflexivity.
  unfold msr_inv. rewrite Hv, Hlv, Hrg. split; [|split].
  - intros w Hw. apply elem_of_cons in Hw as [Hw|Hw].
    + injection Hw as ->. change (v ≤ v `max` TState.vmsr a). lia.
    + pose proof (Hl w Hw). lia.
  - intros vv Hvv. pose proof (H0 vv Hvv). lia.
  - intros vv Hvv. pose proof (H1 vv Hvv). lia.
Qed.

(** * Errors of the longer state

    On a valid cache over a history of page-local writes, cache maintenance
    succeeds ([SwapFillTotal]); the remaining errors read registers, which
    the shorter state reads alike. *)

Lemma total_run {A} (Q : A → Prop) (m : stateT TLB.t (result string) A) c err :
  SwapFillTotal.total Q m → VMCacheIndexed.valid c → m c = Error err → False.
Proof. intros Ht Hv H. destruct (Ht c Hv) as [c' [x [Hx _]]]. congruence. Qed.

Lemma total_mapM_unit {A} (f : A → stateT TLB.t (result string) ()) xs :
  (∀ x, SwapFillTotal.total (λ _, True) (f x)) → (∀ x, VMCacheIndexed.preserves (f x)) →
  SwapFillTotal.total (λ _, True) (mapM f xs ≫= λ _, mret ()).
Proof.
  intros Ht Hp. eapply SwapFillTotal.total_bind.
  - apply SwapFillTotal.total_mapM; [intros x _; apply Ht|exact Hp].
  - apply VMCacheIndexed.preserves_mapM. exact Hp.
  - intros _ _ c _. exists c, (). split; [reflexivity|exact I].
Qed.

(** A failing register write of the longer state is a failing read of
    TTBR0_EL1 by a TTBR1_EL1 write; every state with the same TTBR0_EL1
    values fails as well. *)
Lemma wsreg_upd_err tid imem mem sreg val v ts c err : Forall SwapFillTotal.ev_ok mem →
  VMCacheIndexed.valid c → wsreg_upd tid imem mem sreg val v ts c = Error err →
  ∀ f mem2 v2 ts2 d, TState.read_sreg_indirect ts2 TTBR0_EL1 =
      map (vv_map f) <$> TState.read_sreg_indirect ts TTBR0_EL1 →
    ∃ err', wsreg_upd tid imem mem2 sreg val v2 ts2 d = Error err'.
Proof.
  intros Hok Hv Hrun f mem2 v2 ts2 d Hts2.
  destruct sreg as [r'|r'|r'|r']; unfold wsreg_upd in Hrun |- *;
    try (cbv beta iota zeta in Hrun; discriminate).
  all: destruct r'; cbv beta iota zeta in Hrun |- *; try discriminate.
  - exfalso. refine (total_run _ _ c err _ Hv Hrun).
    eapply SwapFillTotal.total_bind;
      [apply SwapFillTotal.total_fill_asid_root, Hok|apply VMCacheIndexed.fill_asid_root|].
    intros _ _. apply total_mapM_unit.
    + intros [t1 v1]. apply SwapFillTotal.total_fill_asid_root, Hok.
    + intros [t1 v1]. apply VMCacheIndexed.fill_asid_root.
  - destruct (TState.read_sreg_indirect ts TTBR0_EL1) as [xs|] eqn:E.
    + exfalso. refine (total_run (λ _, True) _ c err _ Hv Hrun).
      apply (SwapFillTotal.total_bind (λ ys, ys = xs)).
      * intros c0 _. exists c0, xs. split; [|reflexivity]. rewrite ?E. reflexivity.
      * apply VMCacheIndexed.preserves_othrow.
      * intros ys ->. apply total_mapM_unit.
        -- intros [t0 v0]. apply SwapFillTotal.total_fill_asid_root, Hok.
        -- intros [t0 v0]. apply VMCacheIndexed.fill_asid_root.
    + rewrite Hts2. try rewrite E. cbn. eexists. reflexivity.
Qed.

Section Errors.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc k).

Lemma ts_rel_valid a b c : ts_rel r a b → TState.tlb a = Some c → VMCacheIndexed.valid c.
Proof.
  intros Hrel Hc. destruct (ts_rel_tlb r a b c Hrel Hc) as [d [_ [_ [Hw _]]]].
  apply wf_tlb_map in Hw. exact (proj1 Hw).
Qed.

Theorem add_wsreg_remove_err l sreg val v a b err :
  ts_rel r a b → Forall SwapFillTotal.ev_ok (l ++ e :: r) →
  TState.add_wsreg tid imem (l ++ e :: r) sreg val v a = Error err →
  ∃ err', TState.add_wsreg tid imem (l ++ r) sreg val (g v) b = Error err'.
Proof.
  intros Hrel Hok Hrun. rewrite add_wsreg_upd in Hrun |- *.
  destruct (TState.tlb a) as [c|] eqn:Hc.
  - destruct (ts_rel_tlb r a b c Hrel Hc) as [d [Hd _]].
    unfold TState.run_tlb in Hrun |- *. rewrite Hc in Hrun. rewrite Hd.
    destruct (wsreg_upd tid imem (l ++ e :: r) sreg val v a c) as [[c' []]|err1] eqn:Hu;
      cbn in Hrun; [discriminate|].
    assert (Hts2 : TState.read_sreg_indirect b TTBR0_EL1 =
      map (vv_map g) <$> TState.read_sreg_indirect a TTBR0_EL1).
    { rewrite (proj1 Hrel). exact (ts_map_read_sreg_indirect g a TTBR0_EL1). }
    destruct (wsreg_upd_err tid imem _ sreg val v a c err1 Hok (ts_rel_valid a b c Hrel Hc) Hu
      g (l ++ r) (g v) b d Hts2) as [err' He].
    rewrite He. cbn. eexists. reflexivity.
  - rewrite (run_tlb_none _ _ Hc) in Hrun. discriminate.
Qed.

Lemma process_event_err tid0 imem0 mem ev a err :
  TState.process_event tid0 imem0 mem ev a = Error err → ∃ c, TState.tlb a = Some c ∧
    ∃ err', TLB.fill_promise tid0 imem0 mem ev c = Error err'.
Proof.
  intro H. unfold TState.process_event, TState.run_tlb in H.
  destruct (TState.tlb a) as [c|]; [|discriminate].
  destruct (TLB.fill_promise tid0 imem0 mem ev c) as [[c' []]|err'] eqn:E; cbn in H; [discriminate|].
  eauto.
Qed.

Theorem process_event_remove_err l ev a b err :
  ts_rel r a b → TState.process_event tid imem (ev :: l ++ e :: r) ev a = Error err →
  ∃ err', TState.process_event tid imem (ev :: l ++ r) ev b = Error err'.
Proof.
  intros Hrel Hrun.
  destruct (process_event_err _ _ _ _ _ _ Hrun) as [c [Hc [err1 He]]].
  destruct (ts_rel_tlb r a b c Hrel Hc) as [d [Hd _]].
  unfold TState.process_event, TState.run_tlb. rewrite Hd.
  destruct (TLB.fill_promise tid imem (ev :: l ++ r) ev d) as [[d' []]|err'] eqn:E;
    [|cbn; eexists; reflexivity].
  exfalso. pose proof (SwapFillTotal.fill_promise_ev_ok _ _ _ _ _ _ E) as Hev.
  exact (total_run _ _ c err1 (SwapFillTotal.total_fill_promise tid imem _ ev Hev)
    (ts_rel_valid a b c Hrel Hc) He).
Qed.

Lemma run_tlb_some_err upd ts c err : TState.tlb ts = Some c → TState.run_tlb upd ts = Error err →
  upd c = Error err.
Proof.
  intros Hc H. unfold TState.run_tlb in H. rewrite Hc in H.
  destruct (upd c) as [[c' []]|e'] eqn:E; [discriminate|]. injection H as ->. reflexivity.
Qed.

Theorem cse_remove_err l v a b err :
  ts_rel r a b → Forall SwapFillTotal.ev_ok (l ++ e :: r) →
  TState.cse imem (l ++ e :: r) tid v a = Error err →
  ∃ err', TState.cse imem (l ++ r) tid (g v) b = Error err'.
Proof.
  intros Hrel Hok Hrun.
  pose proof (proj1 Hrel) as Hb. set (ob := TState.tlb b) in Hb.
  rewrite <- (VMCacheSim.setv_tlb_same a) in Hrun.
  rewrite VMCacheSim.cse_shape in Hrun. rewrite Hb, VMCacheSim.cse_shape.
  rewrite cse_pre_map.
  set (X := VMCacheSim.cse_pre v a) in *.
  rewrite !ts_map_read_sreg_direct.
  destruct (TState.tlb a) as [c|] eqn:Hc.
  - destruct (ts_rel_tlb _ _ _ _ Hrel Hc) as [d [Hd _]]. fold ob in Hd. rewrite Hd.
    destruct (TState.run_tlb _ (setv TState.tlb (Some c) X)) as [mid|err1] eqn:Hmid;
      cbn in Hrun; [discriminate|].
    destruct (TState.read_sreg_direct X TTBR0_EL1) as [vv0|] eqn:E0.
    + exfalso.
      pose proof (run_tlb_some_err _ _ c _ (VMCacheSim.tlb_setv X (Some c)) Hmid) as Hu.
      refine (total_run (λ _, True) _ c err1 _ (ts_rel_valid a b c Hrel Hc) Hu).
      apply (SwapFillTotal.total_bind (λ _, True)); [intros c0 _; exists c0, (); split; reflexivity|
        apply VMCacheIndexed.preserves_ret|intros _ _].
      apply (SwapFillTotal.total_bind (λ y, y = vv0)).
      * intros c0 _. exists c0, vv0. split; [|reflexivity]. rewrite ?E0. reflexivity.
      * apply VMCacheIndexed.preserves_othrow.
      * intros y ->. apply SwapFillTotal.total_fill_cse, Hok.
    + rewrite ?E0. eexists. unfold TState.run_tlb. rewrite VMCacheSim.tlb_setv. reflexivity.
  - rewrite (run_tlb_none _ _ (VMCacheSim.tlb_setv X None)) in Hrun. discriminate.
Qed.
End Errors.

(** * [msr_inv] through the remaining thread-state updates *)

Lemma ttbr0_not_strict : (TTBR0_EL1 : reg) ∉ strict_regs.
Proof.
  unfold strict_regs. intro H. apply elem_of_list_to_set in H.
  repeat (apply elem_of_cons in H as [H|H]; [discriminate H|]). inversion H.
Qed.

Lemma ttbr1_not_strict : (TTBR1_EL1 : reg) ∉ strict_regs.
Proof.
  unfold strict_regs. intro H. apply elem_of_list_to_set in H.
  repeat (apply elem_of_cons in H as [H|H]; [discriminate H|]). inversion H.
Qed.

Lemma ttbr0_not_pc : (TTBR0_EL1 : reg) ≠ pc_reg.
Proof. discriminate. Qed.

Lemma ttbr1_not_pc : (TTBR1_EL1 : reg) ≠ pc_reg.
Proof. discriminate. Qed.

(** [msr_inv] only reads the local events, the registers and [vmsr]. *)
Lemma msr_inv_frame a a' : TState.levs a' = TState.levs a → TState.regs a' = TState.regs a →
  TState.vmsr a ≤ TState.vmsr a' → msr_inv a → msr_inv a'.
Proof.
  intros Hl Hr Hv (H1 & H2 & H3). unfold msr_inv. rewrite Hl, Hr. split; [|split].
  - intros w Hw. pose proof (H1 w Hw). lia.
  - intros vv Hvv. pose proof (H2 vv Hvv). lia.
  - intros vv Hvv. pose proof (H3 vv Hvv). lia.
Qed.

Lemma msr_inv_set_reg (reg : reg) rv a a' : reg ≠ TTBR0_EL1 → reg ≠ TTBR1_EL1 → msr_inv a →
  TState.set_reg reg rv a = Some a' → msr_inv a'.
Proof.
  intros H0 H1 (Hl & Hr0 & Hr1) Hset. unfold TState.set_reg in Hset.
  destruct (decide _); [|discriminate]. injection Hset as <-.
  unfold msr_inv. cbn. split; [exact Hl|split].
  - intros vv Hvv. rewrite dmap_lookup_insert_ne in Hvv by congruence. exact (Hr0 vv Hvv).
  - intros vv Hvv. rewrite dmap_lookup_insert_ne in Hvv by congruence. exact (Hr1 vv Hvv).
Qed.

Lemma msr_inv_set_reg_strict (reg : reg) rv a a' : reg ∈ strict_regs → msr_inv a →
  TState.set_reg reg rv a = Some a' → msr_inv a'.
Proof.
  intro Hs. apply msr_inv_set_reg; intros ->; [apply ttbr0_not_strict|apply ttbr1_not_strict]; exact Hs.
Qed.

Lemma msr_inv_set_reg_pc rv a a' : msr_inv a → TState.set_reg pc_reg rv a = Some a' → msr_inv a'.
Proof. apply msr_inv_set_reg; [apply not_eq_sym, ttbr0_not_pc|apply not_eq_sym, ttbr1_not_pc]. Qed.

Lemma msr_inv_init tid imem iregs ts : TState.init tid imem iregs = Ok ts → msr_inv ts.
Proof.
  intro H. unfold TState.init in H.
  destruct (reg_lookup CurrentEL iregs); cbn in H; [|discriminate].
  unfold guard_or in H. destruct (decide _); cbn in H; [|discriminate].
  destruct (reg_lookup SCTLR_EL1 iregs); cbn in H; [|discriminate].
  match type of H with context [ (if ?c then ?x else ?y) ≫= _ ] =>
    destruct (if c then x else y) as [o|] end; cbn in H; [|discriminate].
  injection H as <-. unfold msr_inv. cbn. split; [|split].
  - intros w Hw. inversion Hw.
  - intros vv Hvv. rewrite dmap_lookup_map in Hvv.
    destruct (dmap_lookup _ iregs); cbn in Hvv; [|discriminate]. injection Hvv as <-. cbn. lia.
  - intros vv Hvv. rewrite dmap_lookup_map in Hvv.
    destruct (dmap_lookup _ iregs); cbn in Hvv; [|discriminate]. injection Hvv as <-. cbn. lia.
Qed.

(** * The invariant at the exchange point *)

Section Init.
Import VMCacheRefill.
Local Notation rolled := VMCacheExchange.rolled.
Context (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc k : nat).
Local Notation p := (S (length r)).
Local Notation q := (length r).

(** Right after the promise of the removed TLBI, the cache is bounded by
    [q] and has no root of time [p]. *)
Lemma J_init c : VMCacheOrder.good q c → proots r c = [] → J imem [] r tlbi rc k c.
Proof.
  intros Hg Hnil. unfold J. rewrite Hnil. exists (rolled q c). split; [apply fill_from_roots_nil|].
  eapply equiv_trans; [apply good_rolled_equiv, (VMCacheOrder.good_mono q); [lia|exact Hg]|].
  apply equiv_sym, good_rolled_equiv, Hg.
Qed.

Lemma TI_init vc vm c : VMCacheOrder.good q c → proots r c = [] →
  TI imem r tlbi rc k [] vc vm c.
Proof.
  intros Hg Hnil. split; [|split].
  - eapply VMCacheOrder.good_mono; [|exact Hg]. cbn. lia.
  - intros _. apply J_init; assumption.
  - intro H. contradiction.
Qed.

(** Roots bounded by [q] are not roots of time [p]. *)
Lemma proots_nil_of_bound c : Forall (λ x, x.2 ≤ q) (TLB.asid_roots c) → proots r c = [].
Proof.
  intro Hb. unfold proots. rewrite filter_roots_eq_nil; [reflexivity|].
  intros x Hx. rewrite list.Forall_forall in Hb. pose proof (Hb x Hx). lia.
Qed.
End Init.

(** * Lookups of one entry under [unshift p]

    The entry history of the longer cache, mapped by [unshift p], gives the
    mapped results of the longer history when the lookup window does not
    start at [p], the history has no TLBI at [p], and loads at [p] only occur
    when the window starts after [p]. PromiseFirstSailVMSwapRemoveEvents
    extends this to windows starting at [p], using ordered histories and
    positive TLBI markers to account for equal-time coalescing. *)

(** The image of a lookup result under a time map. *)
Definition res_map (f : nat → nat) (x : TLB.Result.t) : TLB.Result.t :=
  TLB.Result.make (TLB.Result.ttbr x) (TLB.Result.path x) (f (TLB.Result.tstart x))
    (f (TLB.Result.tend x)) (f <$> TLB.Result.inv_time x).

Section Events.
Context (p : nat) (Hp : 0 < p) (tid : nat) (ifetch : bool) (ttbr : bv 64) (path : list (bv 64)).
Local Notation g := (unshift p).

Lemma unshift_lt_ne a b : b ≠ p → g a < g b ↔ a < b.
Proof using Hp. intro H. apply unshift_lt_iff_ne; assumption. Qed.

Lemma unshift_pred t : t ≠ p → g (pred t) = pred (g t).
Proof. clear Hp. intro. unfold unshift. repeat case_decide; lia. Qed.

Lemma unshift_eq_ne a b : a ≠ p → b ≠ p → g a = g b ↔ a = b.
Proof. clear Hp. intros. unfold unshift. repeat case_decide; lia. Qed.

(** No TLBI event at [p]; loads at [p] only when the window starts after [p]. *)
Definition ev_hyp (tmin : nat) (et : TLB.Entry.event * nat) : Prop :=
  et.2 ≠ p ∨ (et.1 = TLB.Entry.Load ∧ p < tmin).

Lemma get_results_from_events_remove events : ∀ tmax inv tmin,
  tmin ≠ p → Forall (ev_hyp tmin) events →
  TLB.get_results_from_events tid ifetch ttbr path (map_evs g events) (g tmin) (g tmax) (g <$> inv) =
  map (res_map g) (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof using Hp.
  induction events as [events IH] using (induction_ltof1 _ (@length _)).
  unfold ltof in IH. intros tmax inv tmin Hmin Hev.
  destruct events as [|[ev t] events]; cbn [TLB.get_results_from_events map_evs map fst snd].
  all: destruct (decide (tmax < tmin)) as [Hs|Hs];
    destruct (decide (g tmax < g tmin)) as [Hs'|Hs'];
    try (exfalso; pose proof (unshift_lt_ne tmax tmin Hmin); tauto);
    try reflexivity.
  apply list.Forall_cons in Hev as [Ht Hev].
  destruct ev as [|tidt].
  - (* Load *)
    assert (Htt : t ≠ p ∨ p < tmin) by (destruct Ht as [Ht|[_ Ht]]; auto).
    assert (Hlt1 : g tmax < g t ↔ tmax < t).
    { destruct (decide (t = p)) as [->|Hne]; [|apply unshift_lt_ne, Hne].
      destruct Htt as [Htt|Htt]; [lia|]. unfold unshift. repeat case_decide; lia. }
    destruct (decide (tmax < t)) as [Hm|Hm]; destruct (decide (g tmax < g t)) as [Hm'|Hm'];
      try (exfalso; tauto).
    + apply (IH events ltac:(cbn; lia)); [exact Hmin|].
      eapply list.Forall_impl; [exact Hev|]. intros x Hx. exact Hx.
    + assert (Hlt2 : g t < g tmin ↔ t < tmin) by (apply unshift_lt_ne, Hmin).
      destruct (decide (t < tmin)) as [Hl|Hl]; destruct (decide (g t < g tmin)) as [Hl'|Hl'];
        try (exfalso; tauto).
      * reflexivity.
      * assert (Htp : t ≠ p) by (destruct Htt; lia).
        destruct events as [|[[|tidt'] t'] events'];
          cbn [map_evs map fst snd map].
        -- cbn [map]. f_equal. apply (IH [] ltac:(cbn; lia)); [exact Hmin|constructor].
        -- f_equal. apply (IH ((TLB.Entry.Load, t') :: events') ltac:(cbn; lia)); [exact Hmin|].
           exact Hev.
        -- apply list.Forall_cons in Hev as [Ht' Hev'].
           assert (Ht'p : t' ≠ p) by (destruct Ht' as [H|[H _]]; [exact H|discriminate]).
           pose proof (unshift_eq_ne t t' Htp Ht'p) as Heq.
           destruct (decide (t = t' ∧ (ifetch ∨ tidt' = tid))) as [Hc|Hc];
             destruct (decide (g t = g t' ∧ (ifetch ∨ tidt' = tid))) as [Hc'|Hc'];
             try (exfalso; tauto).
           ++ pose proof (IH events' ltac:(cbn; lia) tmax inv tmin Hmin Hev') as Hmerge.
              pose proof (IH ((TLB.Entry.Tlbi tidt', t') :: events')
                ltac:(cbn; lia) tmax inv tmin Hmin ltac:(constructor; assumption)) as Hnormal.
              destruct events' as [|[[|tidt''] t''] events'']; cbn [map_evs map fst snd].
              2: exact Hmerge.
              all: cbn [map]; f_equal; exact Hnormal.
           ++ cbn [map]. f_equal.
              apply (IH ((TLB.Entry.Tlbi tidt', t') :: events') ltac:(cbn; lia)); [exact Hmin|].
              constructor; [exact Ht'|exact Hev'].
  - (* Tlbi *)
    assert (Htp : t ≠ p) by (destruct Ht as [H|[H _]]; [exact H|discriminate]).
    assert (Hm : g (tmax `min` pred t) = g tmax `min` pred (g t)).
    { rewrite unshift_min, unshift_pred by exact Htp. reflexivity. }
    destruct (decide (ifetch ∨ tidt = tid)).
    + rewrite <- Hm. apply (IH events ltac:(cbn; lia)); [exact Hmin|exact Hev].
    + rewrite <- Hm. change (Some (g t)) with (g <$> Some t).
      apply (IH events ltac:(cbn; lia)); [exact Hmin|exact Hev].
Qed.
End Events.

End VMSwapRemoveRun.
