(******************************************************************************)
(* Thread cache and register views around a removed foreign TLBI              *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMCacheSim
  PromiseFirstSailVMCacheLastTLBI PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveHistory PromiseFirstSailVMSwapRemoveEvents.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveState.
Import VMPromising VMCacheLastTLBI.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

(** A load or register view may equal the removed timestamp once CSE has
    reached it. Message timestamps and invalidation deadlines need a separate,
    unconditional exclusion invariant. *)
Definition allowed p limit t := t ≠ p ∨ p ≤ limit.

Lemma allowed_mono p lo hi t : lo ≤ hi → allowed p lo t → allowed p hi t.
Proof. unfold allowed. intros. lia. Qed.
Lemma allowed_zero p limit : 0 < p → allowed p limit 0.
Proof. unfold allowed. lia. Qed.
Lemma allowed_max p limit a b : allowed p limit a → allowed p limit b → allowed p limit (a `max` b).
Proof. unfold allowed. lia. Qed.
Lemma allowed_min p limit a b : allowed p limit a → allowed p limit b → allowed p limit (a `min` b).
Proof. unfold allowed. lia. Qed.
Lemma allowed_current p limit : allowed p limit limit.
Proof. unfold allowed. lia. Qed.
Lemma allowed_load p limit time : allowed p limit time →
  VMSwapRemoveEvents.event_allowed p limit (TLB.Entry.Load, time).
Proof. apply VMSwapRemoveHistory.allowed_load. Qed.

Section Values.
Context (Q : nat → Prop).
Definition regs_ok (regs : dmap reg (λ reg, reg_type reg * view)%type) :=
  ∀ r rv, dmap_lookup r regs = Some rv → Q rv.2.
Definition lev_ok (lev : LEv.t) :=
  match lev with LEv.Cse t => Q t | LEv.Wsreg w => Q (WSReg.view w) end.

Lemma regs_insert regs r rv : regs_ok regs → Q rv.2 → regs_ok (dmap_insert r rv regs).
Proof.
  intros Hregs Hrv k x Hk. rewrite dmap_lookup_insert_case in Hk.
  destruct (decide (r = k)) as [Heq|Hne]; [|exact (Hregs k x Hk)].
  subst k. injection Hk as <-. rewrite ctrans_simpl. exact Hrv.
Qed.

Lemma read_sreg_direct_lev regs sreg levs vv :
  regs_ok regs → Forall lev_ok levs → TState.read_sreg_direct_lev regs sreg levs = Some vv → Q vv.2.
Proof.
  intros Hregs Hlevs. induction Hlevs as [|lev levs Hlev Hlevs IH]; cbn.
  - apply Hregs.
  - destruct lev as [time|wsreg]; [exact IH|].
    destruct (WSReg.to_val_view_if sreg wsreg) as [found|] eqn:Hfound; [|exact IH].
    injection 1 as <-. apply VMViews.to_val_view_if_view in Hfound. rewrite Hfound. exact Hlev.
Qed.

Lemma read_sreg_indirect_lev regs sreg levs vvs : regs_ok regs → Forall lev_ok levs →
  TState.read_sreg_indirect_lev regs sreg levs = Some vvs → ∀ vv, vv ∈ vvs → Q vv.2.
Proof.
  intros Hregs Hlevs. revert vvs. induction Hlevs as [|lev levs Hlev Hlevs IH]; intro vvs; cbn.
  - destruct (dmap_lookup sreg regs) as [found|] eqn:Hfound; [|discriminate].
    cbn. injection 1 as <-. intros vv Hin. apply list_elem_of_singleton in Hin as ->.
    exact (Hregs _ _ Hfound).
  - destruct lev as [time|wsreg].
    + destruct (TState.read_sreg_direct_lev regs sreg levs) as [found|] eqn:Hfound; [|discriminate].
      cbn. injection 1 as <-. intros vv Hin. apply list_elem_of_singleton in Hin as ->.
      eapply read_sreg_direct_lev; eassumption.
    + destruct (TState.read_sreg_indirect_lev regs sreg levs) as [rest|] eqn:Hrest; [|discriminate].
      cbn. destruct (WSReg.to_val_view_if sreg wsreg) as [found|] eqn:Hfound.
      * injection 1 as <-. intros vv Hin. apply elem_of_cons in Hin as [->|Hin]; [|exact (IH _ eq_refl vv Hin)].
        apply VMViews.to_val_view_if_view in Hfound. rewrite Hfound. exact Hlev.
      * injection 1 as <-. exact (IH _ eq_refl).
Qed.
End Values.

Definition sources p (ts : TState.t) :=
  regs_ok (allowed p (TState.vcse ts)) (TState.regs ts) ∧
  Forall (lev_ok (allowed p (TState.vcse ts))) (TState.levs ts).

Lemma indirect_allowed p ts sr vals : sources p ts → TState.read_sreg_indirect ts sr = Some vals →
  ∀ vv, vv ∈ vals → allowed p (TState.vcse ts) vv.2.
Proof. intros [Hregs Hlevs]. apply read_sreg_indirect_lev; assumption. Qed.

Definition cache_at p limit (ts : TState.t) :=
  ∀ c, TState.tlb ts = Some c → VMSwapRemoveHistory.cache_ok p limit c.
Definition cache_state p ts := cache_at p (TState.vcse ts) ts.

Lemma cache_frame p ts ts' : TState.tlb ts' = TState.tlb ts → TState.vcse ts ≤ TState.vcse ts' →
  cache_state p ts → cache_state p ts'.
Proof.
  intros Htlb Hvc H c Hc. rewrite Htlb in Hc. eapply VMSwapRemoveHistory.cache_mono; [exact Hvc|apply H, Hc].
Qed.

Lemma run_tlb_cache p run ts ts' : keeps (VMSwapRemoveHistory.cache_ok p (TState.vcse ts)) run →
  cache_state p ts → TState.run_tlb run ts = Ok ts' → cache_state p ts'.
Proof.
  intros Hkeep Hcache Hrun. unfold TState.run_tlb in Hrun.
  destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (run c) as [[c' []]|err] eqn:Hr; cbn in Hrun; [|discriminate].
    injection Hrun as <-. intros c0 Hc0. cbn in Hc0. injection Hc0 as <-.
    exact (Hkeep c c' () (Hcache c Hc) Hr).
  - injection Hrun as <-. exact Hcache.
Qed.

Lemma process_event_cache p tid imem mem ev ts ts' : length mem ≠ p → cache_state p ts →
  TState.process_event tid imem mem ev ts = Ok ts' → cache_state p ts'.
Proof.
  intros Hlen. apply run_tlb_cache. intros c c' [] Hc Hrun.
  eapply VMSwapRemoveHistory.cache_fill_promise; eassumption.
Qed.

Lemma emit_cache p tid imem mem ev ts ts' : length mem ≠ p → cache_state p ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → cache_state p ts'.
Proof.
  intros Hlen Hcache He. unfold TState.emit_promise in He.
  eapply process_event_cache; [exact Hlen| |exact He].
  destruct (bool_decide _); [destruct ev|]; exact Hcache.
Qed.

Lemma keeps_mapM_in (I : TLB.t → Prop) {A B} (f : A → stateT TLB.t (result string) B) xs :
  (∀ x, x ∈ xs → keeps I (f x)) → keeps I (mapM f xs).
Proof.
  induction xs as [|x xs IH]; intro H; cbn [mapM]; [apply keeps_ret|].
  apply keeps_bind; [apply H; left|intro].
  apply keeps_bind; [apply IH; intros y Hy; apply H; right; exact Hy|intro; apply keeps_ret].
Qed.

Section Removed.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation e := (Ev.Tlbi tlbi rc epoch).

Lemma fill_cse_keeps l time limit ttbr0 ttbr1 : time ≤ limit →
  keeps (VMSwapRemoveHistory.cache_ok p limit)
    (TLB.fill_cse tid imem (l ++ e :: r) time ttbr0 ttbr1).
Proof using Hrc.
  intros Hle old new [] Hold Hrun.
  pose proof (VMSwapRemoveHistory.cache_fill_cse limit tid imem l r tlbi rc epoch time ttbr0 ttbr1
    old new Hrc Hold Hrun) as Hnew. rewrite Nat.max_r in Hnew by exact Hle. exact Hnew.
Qed.

Lemma cse_cache l v ts ts' : cache_state p ts →
  TState.cse imem (l ++ e :: r) tid v ts = Ok ts' → cache_state p ts'.
Proof using Hrc.
  intros Hcache Hrun. unfold TState.cse, mbind, result_bind in Hrun.
  match type of Hrun with (match TState.run_tlb ?run ?pre with _ => _ end) = _ =>
    destruct (TState.run_tlb run pre) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hrun as <-. eapply run_tlb_cache; [| |exact Hmid].
  - apply (keeps_bind _ (mret ())); [apply keeps_ret|intros []].
    apply (keeps_bind _ (othrow _ _)); [apply keeps_othrow|intro].
    apply fill_cse_keeps. change (v ≤ v `max` TState.vcse ts). lia.
  - eapply (cache_frame p ts); [reflexivity| |exact Hcache].
    change (TState.vcse ts ≤ v `max` TState.vcse ts). lia.
Qed.

Lemma wsreg_keeps l sreg val v ts : sources p ts → allowed p (TState.vcse ts) v →
  keeps (VMSwapRemoveHistory.cache_ok p (TState.vcse ts))
    (VMSwapRemoveRun.wsreg_upd tid imem (l ++ e :: r) sreg val v ts).
Proof using Hrc.
  intros Hsources Hv. unfold VMSwapRemoveRun.wsreg_upd.
  assert (Hroot : ∀ root time, allowed p (TState.vcse ts) time →
      keeps (VMSwapRemoveHistory.cache_ok p (TState.vcse ts))
        (TLB.fill_asid_root tid imem (l ++ e :: r) root time)).
  { intros root time Htime old new [] Hold Hrun.
    eapply VMSwapRemoveHistory.cache_fill_asid_root; eassumption. }
  destruct sreg as [reg|reg|reg|reg]; try apply keeps_ret.
  destruct reg; try apply keeps_ret; cbv beta iota zeta.
  - apply keeps_bind; [apply Hroot, Hv|intro].
    apply keeps_bind; [|intro; apply keeps_ret]. apply keeps_mapM_in. intros [ttbr v1] Hin.
    apply Hroot, allowed_max; [exact Hv|].
    destruct (TState.read_sreg_indirect ts TTBR1_EL1) as [vals|] eqn:Hvals; [|inversion Hin].
    exact (indirect_allowed p ts _ _ Hsources Hvals _ Hin).
  - destruct (TState.read_sreg_indirect ts TTBR0_EL1) as [vals|] eqn:Hvals.
    + change (keeps (VMSwapRemoveHistory.cache_ok p (TState.vcse ts)) (mapM (λ '(ttbr0, v0),
        TLB.fill_asid_root tid imem (l ++ e :: r) (bv_extract 48 16 ttbr0, val, true) (v ⊔ v0)) vals;; mret ())).
      apply keeps_bind; [|intro; apply keeps_ret]. apply keeps_mapM_in. intros [ttbr v0] Hin.
      apply Hroot, allowed_max; [exact Hv|].
      exact (indirect_allowed p ts _ _ Hsources Hvals _ Hin).
    + intros old new value Hold Hrun. discriminate.
Qed.
Lemma add_wsreg_cache l sreg val v ts ts' : sources p ts → allowed p (TState.vcse ts) v →
  cache_state p ts → TState.add_wsreg tid imem (l ++ e :: r) sreg val v ts = Ok ts' → cache_state p ts'.
Proof using Hrc.
  intros Hsources Hv Hcache Hrun. rewrite VMSwapRemoveRun.add_wsreg_upd in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. change (cache_state p mid).
  eapply (run_tlb_cache p _ ts mid);
    [exact (wsreg_keeps l sreg val v ts Hsources Hv)|exact Hcache|exact Hmid].
Qed.
End Removed.

Lemma regs_mono p lo hi regs : lo ≤ hi → regs_ok (allowed p lo) regs → regs_ok (allowed p hi) regs.
Proof. intros Hle Hregs r rv Hrv. eapply allowed_mono; [exact Hle|apply Hregs, Hrv]. Qed.
Lemma levs_mono p lo hi levs : lo ≤ hi → Forall (lev_ok (allowed p lo)) levs →
  Forall (lev_ok (allowed p hi)) levs.
Proof.
  intros Hle Hlevs. eapply list.Forall_impl; [exact Hlevs|].
  intros [time|wsreg] H; eapply allowed_mono; eassumption.
Qed.

Lemma sources_set_tlb p o ts : sources p (setv TState.tlb o ts) ↔ sources p ts.
Proof. reflexivity. Qed.

Lemma process_event_sources p tid imem mem ev ts ts' : sources p ts →
  TState.process_event tid imem mem ev ts = Ok ts' → sources p ts'.
Proof.
  intros Hsources Hrun. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hrun) as [o ->]. exact Hsources.
Qed.

Lemma cse_sources p tid imem mem v ts ts' : sources p ts →
  TState.cse imem mem tid v ts = Ok ts' → sources p ts'.
Proof.
  intros [Hregs Hlevs] Hrun. unfold TState.cse in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [o ->].
  change (regs_ok (allowed p (v `max` TState.vcse ts)) (TState.regs ts) ∧
    Forall (lev_ok (allowed p (v `max` TState.vcse ts))) (LEv.Cse v :: TState.levs ts)).
  split; [eapply regs_mono; [|exact Hregs]; lia|]. constructor.
  - change (allowed p (v `max` TState.vcse ts) v). unfold allowed. lia.
  - eapply levs_mono; [|exact Hlevs]. lia.
Qed.

Lemma add_wsreg_sources p tid imem mem sreg val v ts ts' : sources p ts →
  allowed p (TState.vcse ts) v → TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → sources p ts'.
Proof.
  intros [Hregs Hlevs] Hv Hrun. rewrite VMSwapRemoveRun.add_wsreg_upd in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [o ->].
  split; [exact Hregs|]. constructor; [exact Hv|exact Hlevs].
Qed.

Lemma set_reg_sources p reg vv ts ts' : sources p ts → allowed p (TState.vcse ts) vv.2 →
  TState.set_reg reg vv ts = Some ts' → sources p ts'.
Proof.
  intros [Hregs Hlevs] Hv. unfold TState.set_reg. case_decide; [|discriminate]. injection 1 as <-.
  split; [apply regs_insert; assumption|exact Hlevs].
Qed.

Lemma cse_vcse tid imem mem v ts ts' : TState.cse imem mem tid v ts = Ok ts' →
  TState.vcse ts' = v `max` TState.vcse ts.
Proof.
  unfold TState.cse. destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn; [|discriminate].
  injection 1 as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [o ->]. reflexivity.
Qed.
Lemma add_wsreg_vcse tid imem mem sreg val v ts ts' :
  TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → TState.vcse ts' = TState.vcse ts.
Proof.
  rewrite VMSwapRemoveRun.add_wsreg_upd.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn; [|discriminate].
  injection 1 as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [o ->]. reflexivity.
Qed.
Lemma set_reg_frame reg vv ts ts' : TState.set_reg reg vv ts = Some ts' →
  TState.tlb ts' = TState.tlb ts ∧ TState.vcse ts' = TState.vcse ts.
Proof. unfold TState.set_reg. case_decide; [|discriminate]. injection 1 as <-. split; reflexivity. Qed.
End VMSwapRemoveState.
