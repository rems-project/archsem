(******************************************************************************)
(* Thread view and cache exclusion through VM handlers                       *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMCacheOrder
  PromiseFirstSailVMSwapRemoveState PromiseFirstSailVMSwapRemoveViews
  PromiseFirstSailVMSwapRemoveHistory PromiseFirstSailVMSwapRemoveRun.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveThread.
Import VMPromising VMSwapRemoveState VMSwapRemoveViews.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

(** This component couples register/dependency views and cache histories to
    the current CSE view. The removal simulation also needs unconditional
    exclusion for promises, message timestamps and invalidation deadlines. *)
Definition thread_ok p ts := ts_ok (allowed p (TState.vcse ts)) ts ∧ cache_state p ts.
Definition local_ok p ts iis := thread_ok p ts ∧ iis_ok (allowed p (TState.vcse ts)) iis.
Definition ok p (pp : PPState.t TState.t Ev.t IIS.t) := local_ok p (PPState.state pp) (PPState.iis pp).

Lemma initial p bound ts iis : bound < p → VMViews.ts_ok bound ts → VMViews.iis_ok bound iis →
  (∀ c, TState.tlb ts = Some c → VMCacheOrder.good bound c ∧
    Forall (λ root, root.2 ≤ bound) (TLB.asid_roots c)) → local_ok p ts iis.
Proof.
  intros Hp Hts Hiis Hcache. split; [split|].
  - eapply ts_before; eassumption.
  - intros c Hc. destruct (Hcache c Hc). eapply VMSwapRemoveHistory.cache_bounded; eassumption.
  - eapply iis_before; eassumption.
Qed.

Lemma frame p ts ts' iis iis' : TState.vcse ts' = TState.vcse ts → TState.tlb ts' = TState.tlb ts →
  ts_ok (allowed p (TState.vcse ts)) ts' → iis_ok (allowed p (TState.vcse ts)) iis' →
  local_ok p ts iis → local_ok p ts' iis'.
Proof.
  intros Hvc Hc Hts Hiis [[_ Hcache] _]. unfold local_ok, thread_ok. rewrite Hvc.
  split; [split; [exact Hts|]|exact Hiis].
  eapply (cache_frame p ts); [exact Hc|rewrite Hvc; lia|exact Hcache].
Qed.

Lemma process_event p tid imem mem ev ts ts' iis : length mem ≠ p → local_ok p ts iis →
  TState.process_event tid imem mem ev ts = Ok ts' → local_ok p ts' iis.
Proof.
  intros Hlen [[Hts Hcache] Hiis] Hrun.
  destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hrun) as [o He].
  assert (Hvc : TState.vcse ts' = TState.vcse ts) by (rewrite He; reflexivity).
  split; [split|]; unfold thread_ok; try rewrite Hvc.
  - eapply VMSwapRemoveViews.process_event; eassumption.
  - eapply process_event_cache; eassumption.
  - exact Hiis.
Qed.

Lemma set_reg p reg vv ts ts' iis : allowed p (TState.vcse ts) vv.2 → local_ok p ts iis →
  TState.set_reg reg vv ts = Some ts' → local_ok p ts' iis.
Proof.
  intros Hv Hok Hrun. destruct (set_reg_frame _ _ _ _ Hrun) as [Htlb Hvc].
  eapply (frame p ts ts' iis); [exact Hvc|exact Htlb| |apply Hok|exact Hok].
  eapply VMSwapRemoveViews.set_reg; [exact Hv|apply Hok|exact Hrun].
Qed.

#[local] Hint Rewrite VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.fst_set_fst VMViews.snd_set_fst VMViews.fst_set_snd VMViews.snd_set_snd
  VMViews.fst_set_snd_field VMViews.snd_set_snd_field : pp_remove.
Ltac simpl_pp := unfold ok, setv in *; autorewrite with pp_remove in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Ltac solve_view :=
  cbn [compose PPState.state PPState.iis fst snd];
  first [assumption | apply allowed_max; solve_view | apply allowed_zero; lia
    | apply view_if_ok; [apply allowed_zero; lia|solve_view]].

Ltac solve_fields :=
  first [assumption
    | apply update_vdmb; [apply allowed_max|solve_view|solve_fields]
    | apply update_vdmbst; [apply allowed_max|solve_view|solve_fields]
    | apply update_vdsb; [apply allowed_max|solve_view|solve_fields]
    | apply update_vmsr; [apply allowed_max|solve_view|solve_fields]
    | apply update_vspec; [apply allowed_max|solve_view|solve_fields]
    | apply next_epoch; solve_fields
    | apply iis_add; [apply allowed_max|solve_view|solve_fields]
    | apply iis_trs; [intros ? H; discriminate H|solve_fields]].

Section Removed.
Context (tid : nat) (imem : memoryMap) (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Hypothesis Hrc : tid ≠ rc.
Local Notation p := (S (length r)).
Local Notation e := (Ev.Tlbi tlbi rc epoch).

Lemma cse l v ts ts' iis : local_ok p ts iis →
  TState.cse imem (l ++ e :: r) tid v ts = Ok ts' → local_ok p ts' (IIS.add v iis).
Proof using Hrc.
  intros [[Hts Hcache] Hiis] Hrun.
  pose proof (cse_vcse _ _ _ _ _ _ Hrun) as Hvc.
  assert (Hv : allowed p (TState.vcse ts') v) by (rewrite Hvc; unfold allowed; lia).
  assert (Hle : TState.vcse ts ≤ TState.vcse ts') by (rewrite Hvc; lia).
  split; [split|].
  - eapply VMSwapRemoveViews.cse; [apply allowed_max|exact Hv| |exact Hrun].
    eapply ts_ok_impl; [intros; eapply allowed_mono; eassumption|exact Hts].
  - eapply cse_cache; eassumption.
  - apply iis_add; [apply allowed_max|exact Hv|].
    eapply iis_ok_impl; [intros; eapply allowed_mono; eassumption|exact Hiis].
Qed.

Lemma add_wsreg l reg val v ts ts' iis : allowed p (TState.vcse ts) v → local_ok p ts iis →
  TState.add_wsreg tid imem (l ++ e :: r) reg val v ts = Ok ts' → local_ok p ts' iis.
Proof using Hrc.
  intros Hv [[Hts Hcache] Hiis] Hrun.
  pose proof (add_wsreg_vcse _ _ _ _ _ _ _ _ Hrun) as Hvc.
  split; [split|]; try rewrite Hvc.
  - eapply VMSwapRemoveViews.add_wsreg; eassumption.
  - eapply add_wsreg_cache; [exact Hrc|apply sources_of_ok, Hts|exact Hv|exact Hcache|exact Hrun].
  - exact Hiis.
Qed.

Lemma run_cse_ok l vmax pp pp' value : PPState.mem pp = l ++ e :: r → ok p pp →
  Exec.elem_of_results (pp', value) (run_cse tid imem vmax pp) → ok p pp'.
Proof using Hrc.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold run_cse in Hrun.
  VMViews.invert; simpl_pp. eapply cse; eassumption.
Qed.

Lemma run_barrier_ok l barrier vmax pp pp' value : PPState.mem pp = l ++ e :: r → ok p pp →
  Exec.elem_of_results (pp', value) (run_barrier tid imem barrier vmax pp) → ok p pp'.
Proof using Hrc.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold run_barrier in Hrun.
  VMViews.invert.
  all: try solve [match goal with H : Exec.elem_of_results _ (run_cse _ _ _ ?initial) |- _ =>
    eapply (run_cse_ok l vmax initial); [reflexivity|exact Hok|exact H] end].
  all: simpl_pp; pose proof Hok as [[Hts Hcache] Hiis]; VMViews.facts Hts; VMViews.facts Hiis.
  all: eapply (frame p ts _ iis); [reflexivity|reflexivity|solve_fields|solve_fields|exact Hok].
Qed.

Lemma run_reg_write_ok l reg racc val pp pp' value : PPState.mem pp = l ++ e :: r → ok p pp →
  Exec.elem_of_results (pp', value) (run_reg_write tid imem reg racc val pp) → ok p pp'.
Proof using Hrc.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold run_reg_write in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: pose proof Hok as [[Hts Hcache] Hiis]; VMViews.facts Hts; VMViews.facts Hiis.
  all: try match goal with H : TState.read_sreg_direct _ _ = Some ?vv |- _ =>
    assert (Hv : allowed p (TState.vcse ts) vv.2)
      by (eapply VMSwapRemoveViews.read_sreg_direct; eassumption); cbn [snd] in Hv end.
  all: match goal with
  | H : TState.add_wsreg _ _ _ ?reg ?val ?v ?before = Ok ?after |- _ =>
      assert (Hafter : local_ok p after iis) by
        (eapply (add_wsreg l reg val v before after iis); [solve_view|exact Hok|exact H]);
      pose proof (add_wsreg_vcse _ _ _ _ _ _ _ _ H) as Hvc
  | H : TState.set_reg ?reg ?vv ?before = Some ?after |- _ =>
      assert (Hbefore : local_ok p before iis) by
        first [exact Hok|eapply (frame p ts _ iis); [reflexivity|reflexivity|solve_fields|exact Hiis|exact Hok]];
      assert (Hafter : local_ok p after iis) by
        (eapply (set_reg p reg vv before after iis); [solve_view|exact Hbefore|exact H]);
      destruct (set_reg_frame _ _ _ _ H) as [_ Hvc]
  end.
  all: try exact Hafter.
  all: pose proof Hafter as [[Hafterts _] Hafteriis].
  all: match type of Hafter with local_ok _ ?after _ =>
    eapply (frame p after _ iis); [reflexivity|reflexivity| | |exact Hafter] end.
  all: first [apply update_vmsr; [apply allowed_max|rewrite Hvc; solve_view|exact Hafterts]
    |apply iis_add; [apply allowed_max|rewrite Hvc; solve_view|exact Hafteriis]].
Qed.

Lemma run_take_exception_ok l fault vmax pp pp' value : PPState.mem pp = l ++ e :: r → ok p pp →
  Exec.elem_of_results (pp', value) (run_take_exception tid imem fault vmax pp) → ok p pp'.
Proof using Hrc.
  intros Hmem Hok Hrun. unfold run_take_exception in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [inv [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [compose] in Hrun.
  destruct (IIS.inv_time (PPState.iis pp)); eapply (run_cse_ok l _ pp); eassumption.
Qed.
End Removed.

Lemma run_reg_read_ok p reg racc ts iis ts' iis' val : 0 < p → local_ok p ts iis →
  Exec.elem_of_results ((ts', iis'), val) (run_reg_read reg racc (ts, iis)) → local_ok p ts' iis'.
Proof.
  intros Hp [[Hts Hcache] Hiis] Hrun.
  destruct (VMSwapRemoveViews.run_reg_read_ok (allowed p (TState.vcse ts))
    (allowed_zero _ _ Hp) (allowed_max _ _) reg racc (ts, iis) (ts', iis') val Hts Hiis Hrun)
    as [He Hiis']. cbn in He, Hiis'. subst ts'. split; [split|]; assumption.
Qed.

Lemma read_pte_ok p pp pp' value : ok p pp → Exec.elem_of_results (pp', value) (read_pte pp) → ok p pp'.
Proof.
  destruct pp as [ts mem iis]. intros [[Hts Hcache] Hiis] Hrun. unfold read_pte in Hrun.
  VMViews.invert; subst; simpl_pp. unfold setv in *.
  cbn [compose PPState.iis] in *.
  match goal with H : IIS.TransRes.pop _ = Ok _ |- _ => apply VMViews.pop_start in H as Hstart end.
  split; [split; assumption|]. apply iis_trs; [|exact Hiis]. intros found Hfound. injection Hfound as <-.
  rewrite Hstart. eapply (ok_trs _ _ Hiis). eassumption.
Qed.

Lemma run_trans_end_ok p trans_end st st' value : 0 < p → local_ok p st.1 st.2 →
  Exec.elem_of_results (st', value) (run_trans_end trans_end st) → local_ok p st'.1 st'.2.
Proof.
  destruct st as [ts iis]. intros Hp Hok Hrun. unfold run_trans_end in Hrun. VMViews.invert; subst.
  all: simpl_pp; pose proof Hok as [[Hts Hcache] Hiis];
    VMViews.facts Hts; VMViews.facts Hiis.
  all: match goal with H : IIS.trs _ = Some ?trs |- _ => pose proof (ok_trs _ _ Hiis trs H) as Hstart end.
  all: eapply (frame p ts _ iis); [reflexivity|reflexivity|solve_fields|solve_fields|exact Hok].
Qed.
End VMSwapRemoveThread.
