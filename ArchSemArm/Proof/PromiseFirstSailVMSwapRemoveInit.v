(******************************************************************************)
(* Initialize removal replay when a foreign TLBI is promised                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMCacheState
  PromiseFirstSailVMCacheOrder PromiseFirstSailVMCacheSim PromiseFirstSailVMCacheRefill
  PromiseFirstSailVMCacheContext PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMSwapRemove PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMInstructionReplay
  PromiseFirstSailVMSwapRemoveCore PromiseFirstSailVMSwapRemoveLocal PromiseFirstSailVMSwapRemoveMachine
  PromiseFirstSailVMSwapRemoveDelivery PromiseFirstSailVMSwapRemoveOutcome PromiseFirstSailVMPageWrites
  PromiseFirstSailVMMsrInvariant PromiseFirstSailVMSwapPos PromiseFirstSailVMNormalization PromiseFirstCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveInit.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMSwapRemove.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Lemma list_fixed {A} (f : A → A) xs : Forall (λ x, f x = x) xs → map f xs = xs.
Proof. induction 1; cbn; [reflexivity|congruence]. Qed.
Lemma gmap_fixed {K A} `{Countable K} (f : A → A) (m : gmap K A) :
  map_Forall (λ _, λ x, f x = x) m → f <$> m = m.
Proof.
  intro Hm. apply map_eq. intro key. rewrite lookup_fmap. destruct (m !! key) as [x|] eqn:Hx; cbn; [|reflexivity].
  rewrite (Hm key x Hx). reflexivity.
Qed.

Section Fixed.
Set Default Proof Using "All".
Context (f : nat → nat) (bound : nat).
Hypothesis Hfix : ∀ t, t ≤ bound → f t = t.

Lemma times_fixed xs : Forall (λ t, t ≤ bound) xs → map f xs = xs.
Proof. intro H. apply list_fixed. eapply list.Forall_impl; [exact H|]. intros t Ht. apply Hfix, Ht. Qed.
Lemma regs_fixed regs : VMViews.regs_ok bound regs → regs_map f regs = regs.
Proof.
  intros Hregs. apply dmap_eq. intro reg. unfold regs_map. rewrite dmap_lookup_map.
  destruct (dmap_lookup reg regs) as [[value time]|] eqn:Hlookup; rewrite Hlookup; cbn; [|reflexivity].
  unfold vv_map. cbn. rewrite Hfix; [reflexivity|exact (Hregs reg (value, time) Hlookup)].
Qed.
Lemma lev_fixed lev : VMViews.lev_ok bound lev → lev_map f lev = lev.
Proof.
  destruct lev as [time|[reg val time]]; cbn; intros H; unfold wsreg_map; cbn; rewrite Hfix by exact H; reflexivity.
Qed.
Lemma fwd_fixed item : VMViews.fwd_ok bound item → fwd_map f item = item.
Proof.
  destruct item as [time v byte xcl]. intros [Ht [Hv Hx]]. unfold fwd_map. cbn in *.
  rewrite (Hfix time Ht), (Hfix v Hv). destruct xcl as [t|]; cbn; [rewrite (Hfix t (Hx t eq_refl))|]; reflexivity.
Qed.
Lemma xcl_fixed item : VMViews.xcl_ok bound item → xcl_map f item = item.
Proof.
  destruct item as [time addr size v]. intros [Ht Hv]. unfold xcl_map. cbn in *.
  rewrite (Hfix time Ht), (Hfix v Hv). reflexivity.
Qed.

Lemma ts_frame_fixed ts : VMViews.ts_ok bound ts → setv TState.tlb (TState.tlb ts) (ts_map f ts) = ts.
Proof.
  destruct ts as [wr pt regs levs coh tcoh rd w dmbst dmb dsb spec cse self other msr acq rel fwd xcl ep cache].
  intros Hts. destruct Hts as [Hwr Hpt Hregs Hlevs Hcoh Htcoh Hrd Hw Hdmbst Hdmb Hdsb Hspec Hcse Hself Hother Hmsr Hacq Hrel Hfwd Hxcl Hcache].
  unfold ts_map, setv, set. cbn in *.
  rewrite (times_fixed _ Hwr), (times_fixed _ Hpt), (regs_fixed _ Hregs).
  repeat match goal with H : ?t ≤ bound |- context [f ?t] => rewrite (Hfix t H) end.
  f_equal.
  - apply list_fixed. eapply list.Forall_impl; [exact Hlevs|]. intros lev Hlev. apply lev_fixed, Hlev.
  - apply gmap_fixed. intros key t Ht. apply Hfix, (Hcoh key t Ht).
  - apply gmap_fixed. intros key t Ht. apply Hfix, (Htcoh key t Ht).
  - apply gmap_fixed. intros key item Hitem. apply fwd_fixed, (Hfwd key item Hitem).
  - destruct xcl as [item|]; cbn; [rewrite (xcl_fixed item (Hxcl item eq_refl))|]; reflexivity.
Qed.

Lemma cache_fixed c : VMCacheState.cache_inv bound c → VMRoots.rbound bound c →
  VMCacheSim.cache_sim (tlb_map f c) c.
Proof.
  intros [Hgood [Hunique Hvalid]] Hroots. split; [split; [split|split]|split].
  - reflexivity.
  - intro fe. rewrite history_tlb_map. unfold map_evs. apply list_fixed.
    eapply list.Forall_impl; [apply Hgood|]. intros [event time] Htime. cbn in *. rewrite Hfix by exact Htime. reflexivity.
  - cbn [tlb_map TLB.asid_roots]. apply list_fixed.
    eapply list.Forall_impl; [exact Hroots|]. intros [root time] Htime. cbn in *. rewrite Hfix by exact Htime. reflexivity.
  - reflexivity.
  - apply wf_tlb_map. split; assumption.
  - split; assumption.
Qed.
End Fixed.
Set Default Proof Using "Type".

Section Initial.
Context (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).

Lemma ts_initial ts : VMViews.ts_ok (length r) ts → VMRoots.roots_ok (length r) ts → ts_rel r ts ts.
Proof.
  intros Hbound Hroots. split.
  - symmetry. apply (ts_frame_fixed g (length r)); [intros t Ht; apply unshift_lt; lia|exact Hbound].
  - rewrite ts_map_tlb. destruct (TState.tlb ts) as [c|] eqn:Hc; cbn; [|exact I].
    apply (cache_fixed g (length r)); [intros t Ht; apply unshift_lt; lia|apply (VMViews.ok_cache _ _ Hbound c Hc)|].
    unfold VMRoots.roots_ok in Hroots. rewrite Hc in Hroots. exact Hroots.
Qed.
Lemma core_initial ts : VMViews.ts_ok (length r) ts → VMRoots.roots_ok (length r) ts → msr_inv ts →
  VMSwapRemoveCore.core imem r tlbi rc epoch [] ts.
Proof.
  intros Hbound Hroots Hmsr. split; [|exact Hmsr]. intros c Hc. apply TI_init.
  - apply (VMViews.ok_cache _ _ Hbound c Hc).
  - apply proots_nil_of_bound. unfold VMRoots.roots_ok in Hroots. rewrite Hc in Hroots. exact Hroots.
Qed.

Theorem foreign_initial tid ts ts' : tid ≠ rc → tid ≠ TLBI.tid tlbi →
  VMViews.ts_ok (length r) ts → VMRoots.roots_ok (length r) ts →
  ts_pos ts → VMPageWrites.ts_ok r ts → msr_inv ts →
  TState.emit_promise tid imem (e :: r) e ts = Ok ts' →
  related r tlbi rc epoch (PPState.Make ts' (e :: r) IIS.init) (PPState.Make ts r IIS.init) ∧
  VMSwapRemoveOutcome.ok imem r tlbi rc epoch (PPState.Make ts' (e :: r) IIS.init).
Proof.
  intros Hrc Hissuer Hbound Hroots Hpos Hpage Hmsr Hrun.
  rewrite VMSwapRemoveMachine.emit_foreign in Hrun by assumption. injection Hrun as <-.
  split.
  - split; [exists []; split; reflexivity|]. split; [apply ts_initial; assumption|].
    symmetry. apply VMSwapRemoveDelivery.iis_init.
  - apply (VMSwapRemoveDelivery.pp_init imem r tlbi rc epoch [] ts).
    + eapply (VMViews.ts_ok_mono (length r)); [cbn; lia|exact Hbound].
    + apply (VMSwapRemoveMachine.initial p (length r)); [lia|exact Hbound|].
      intros c Hc. unfold VMRoots.roots_ok in Hroots. rewrite Hc in Hroots. exact Hroots.
    + exact Hpos.
    + destruct Hpage as [Hnone|Hall]; [left; exact Hnone|right; constructor; [exact I|exact Hall]].
    + apply core_initial; assumption.
Qed.
End Initial.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Definition state_ok (st : state) := VMRoots.state_roots st ∧ VMSwapPos.state_pos st ∧
  VMPageWrites.state_ok st ∧ VMMsrInvariant.state_ok st.

Lemma from_archState_ok ms st : PState.from_archState prom ms = Ok st → state_ok st.
Proof.
  intro Hrun. split; [eapply VMRoots.from_archState_roots; exact Hrun|].
  split; [eapply VMSwapPos.from_archState_pos; exact Hrun|].
  split; [eapply VMPageWrites.from_archState_ok|eapply VMMsrInvariant.from_archState_ok]; exact Hrun.
Qed.
Lemma promise_ok ev st st' : state_ok st → PState.promise prom ev st = Ok st' → state_ok st'.
Proof.
  intros [Hroots [Hpos [Hpage Hmsr]]] Hrun. split; [eapply VMRoots.promise_roots; eassumption|].
  split; [eapply VMSwapPos.promise_pos; eassumption|].
  split; [eapply VMPageWrites.promise_ok|eapply VMMsrInvariant.promise_ok]; eassumption.
Qed.
Lemma run_tid_ok isem (tid : fin n) st st' : state_ok st →
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) → state_ok st'.
Proof.
  intros [Hroots [Hpos [Hpage Hmsr]]] Hrun. split.
  - eapply VMRoots.run_tid_roots; [apply Hpage|exact Hroots|exact Hrun].
  - split; [eapply VMSwapPos.run_tid_pos; eassumption|].
    split; [eapply VMPageWrites.run_tid_ok|eapply VMMsrInvariant.run_tid_ok]; eassumption.
Qed.
Theorem raw_trace_ok nondet term st evs st' : state_ok st →
  VMNormalization.RawTrace bbm nondet term st evs st' → state_ok st'.
Proof.
  intros Hok Htrace. induction Htrace as [|evs mid fin ev Htrace IH [_ Hpromise]]; [exact Hok|].
  eapply promise_ok; eassumption.
Qed.
Theorem mixed_rtc_ok nondet term st st' : state_ok st →
  rtc (VMNormalization.Mixed bbm nondet term) st st' → state_ok st'.
Proof.
  intros Hok Hsteps. induction Hsteps as [st|st mid fin Hstep _ IH]; [exact Hok|].
  apply IH. destruct Hstep as [(tid & _ & Hrun)|(ev & _ & Hpromise)].
  - eapply run_tid_ok; eassumption.
  - eapply promise_ok; eassumption.
Qed.

Theorem promise_foreign_initial (tid : fin n) tlbi rc epoch st st' :
  fin_to_nat tid ≠ rc → fin_to_nat tid ≠ TLBI.tid tlbi → state_ok st →
  PState.promise prom (Ev.Tlbi tlbi rc epoch) st = Ok st' →
  related (PState.events st) tlbi rc epoch
    (PPState.Make (PState.tstate tid st') (PState.events st') IIS.init)
    (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init) ∧
  VMSwapRemoveOutcome.ok (PState.initmem st) (PState.events st) tlbi rc epoch
    (PPState.Make (PState.tstate tid st') (PState.events st') IIS.init).
Proof.
  intros Hrc Hissuer [Hroots [Hpos [[Hbounds Hpage] [_ Hmsr]]]] Hrun.
  unfold PState.promise in Hrun.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn in Hrun. injection Hrun as <-.
  unfold PState.tstate at 1 3. cbn.
  eapply foreign_initial;
    [exact Hrc|exact Hissuer|apply Hbounds|apply Hroots|apply Hpos|apply Hpage|apply Hmsr|].
  exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid).
Qed.
Theorem trace_promise_foreign_initial nondet term initMs init evs base (tid : fin n) tlbi rc epoch st st' :
  fin_to_nat tid ≠ rc → fin_to_nat tid ≠ TLBI.tid tlbi →
  PState.from_archState prom initMs = Ok init →
  VMNormalization.RawTrace bbm nondet term init evs base →
  rtc (VMNormalization.Mixed bbm nondet term) base st →
  PState.promise prom (Ev.Tlbi tlbi rc epoch) st = Ok st' →
  related (PState.events st) tlbi rc epoch
    (PPState.Make (PState.tstate tid st') (PState.events st') IIS.init)
    (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init) ∧
  VMSwapRemoveOutcome.ok (PState.initmem st) (PState.events st) tlbi rc epoch
    (PPState.Make (PState.tstate tid st') (PState.events st') IIS.init).
Proof.
  intros Hrc Hissuer Hinit Hraw Hmixed Hpromise.
  eapply promise_foreign_initial; [exact Hrc|exact Hissuer| |exact Hpromise].
  eapply mixed_rtc_ok; [|exact Hmixed]. eapply raw_trace_ok; [|exact Hraw].
  eapply from_archState_ok; exact Hinit.
Qed.
End Machine.
End VMSwapRemoveInit.
