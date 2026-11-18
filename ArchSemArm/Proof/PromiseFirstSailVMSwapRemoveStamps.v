(******************************************************************************)
(* Unconditional exclusion of a removed timestamp                            *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMSwapRemoveRun
  PromiseFirstSailVMSwapRemoveViews PromiseFirstSailVMSwapRemoveTimes.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMSwapRemoveStamps.
Import VMPromising.
#[local] Typeclasses Transparent view UMPromising.view.

(** These are promise/message times and invalidation deadlines. They must
    avoid p even after CSE has reached p. Dependency views are handled by
    VMSwapRemoveThread.local_ok. *)
Record ts_ok p (ts : TState.t) : Prop := {
  ok_prom_wr : Forall (λ t, t ≠ p) (TState.prom_wr ts);
  ok_prom_tlbi : Forall (λ t, t ≠ p) (TState.prom_tlbi ts);
  ok_coh : map_Forall (λ _ t, t ≠ p) (TState.coh ts);
  ok_fwdb : map_Forall (λ _ item, FwdItem.time item ≠ p) (TState.fwdb ts);
  ok_xclb : ∀ item, TState.xclb ts = Some item → XclItem.time item ≠ p;
}.
Record iis_ok p (iis : IIS.t) : Prop := {
  ok_inv : ∀ t, IIS.inv_time iis = Some t → t ≠ p;
  ok_rmw : ∀ t acq, IIS.rmw_read iis = Some (t, acq) → t ≠ p;
}.

Lemma ts_before p bound ts : bound < p → VMViews.ts_ok bound ts → ts_ok p ts.
Proof.
  intros Hp Hts. constructor.
  - eapply list.Forall_impl; [exact (VMViews.ok_prom_wr _ _ Hts)|]. intros t Ht. cbn in Ht |- *. lia.
  - eapply list.Forall_impl; [exact (VMViews.ok_prom_tlbi _ _ Hts)|]. intros t Ht. cbn in Ht |- *. lia.
  - intros k t Hk. pose proof (VMViews.ok_coh _ _ Hts k t Hk) as Ht. cbn in Ht. lia.
  - intros k item Hk. destruct (VMViews.ok_fwdb _ _ Hts k item Hk) as [Ht _]. lia.
  - intros item Hitem. destruct (VMViews.ok_xclb _ _ Hts item Hitem) as [Ht _]. lia.
Qed.
Lemma iis_before p bound iis : bound < p → VMViews.iis_ok bound iis → iis_ok p iis.
Proof.
  intros Hp Hiis. constructor.
  - intros t Ht. pose proof (VMViews.ok_inv_time _ _ Hiis t Ht). lia.
  - intros t acq Ht. pose proof (VMViews.ok_rmw_read _ _ Hiis t acq Ht). lia.
Qed.

Ltac by_fields :=
  match goal with H : ts_ok _ ?ts |- ts_ok _ _ => destruct ts, H; constructor; cbn in * end;
  try assumption.

Lemma frame p ts ts' : TState.prom_wr ts' = TState.prom_wr ts →
  TState.prom_tlbi ts' = TState.prom_tlbi ts → TState.coh ts' = TState.coh ts →
  TState.fwdb ts' = TState.fwdb ts → TState.xclb ts' = TState.xclb ts → ts_ok p ts → ts_ok p ts'.
Proof. intros Hwr Htlbi Hcoh Hfwd Hxcl Hts. constructor; rewrite ?Hwr, ?Htlbi, ?Hcoh, ?Hfwd, ?Hxcl; apply Hts. Qed.

Local Notation updates acc := (∀ p v ts, ts_ok p ts → ts_ok p (TState.update acc v ts)).
Lemma update_vrd : updates TState.vrd. Proof. intros. by_fields. Qed.
Lemma update_vwr : updates TState.vwr. Proof. intros. by_fields. Qed.
Lemma update_vdmbst : updates TState.vdmbst. Proof. intros. by_fields. Qed.
Lemma update_vdmb : updates TState.vdmb. Proof. intros. by_fields. Qed.
Lemma update_vdsb : updates TState.vdsb. Proof. intros. by_fields. Qed.
Lemma update_vspec : updates TState.vspec. Proof. intros. by_fields. Qed.
Lemma update_vcse : updates TState.vcse. Proof. intros. by_fields. Qed.
Lemma update_vtlbi_self : updates TState.vtlbi_self. Proof. intros. by_fields. Qed.
Lemma update_vtlbi_other : updates TState.vtlbi_other. Proof. intros. by_fields. Qed.
Lemma update_vmsr : updates TState.vmsr. Proof. intros. by_fields. Qed.
Lemma update_vacq : updates TState.vacq. Proof. intros. by_fields. Qed.
Lemma update_vrel : updates TState.vrel. Proof. intros. by_fields. Qed.

Lemma process_event p tid imem mem ev ts ts' : ts_ok p ts →
  TState.process_event tid imem mem ev ts = Ok ts' → ts_ok p ts'.
Proof.
  intros Hts Hrun. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hrun) as [o ->]. by_fields.
Qed.
Lemma cse p tid imem mem v ts ts' : ts_ok p ts → TState.cse imem mem tid v ts = Ok ts' → ts_ok p ts'.
Proof.
  intros Hts Hrun. unfold TState.cse in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [o ->]. by_fields.
Qed.
Lemma add_wsreg p tid imem mem sreg val v ts ts' : ts_ok p ts →
  TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → ts_ok p ts'.
Proof.
  intros Hts Hrun. rewrite VMSwapRemoveRun.add_wsreg_upd in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [o ->]. by_fields.
Qed.
Lemma set_reg p reg vv ts ts' : ts_ok p ts → TState.set_reg reg vv ts = Some ts' → ts_ok p ts'.
Proof.
  intros Hts. unfold TState.set_reg. case_decide; [|discriminate]. injection 1 as <-. by_fields.
Qed.
Lemma next_epoch p ts : ts_ok p ts → ts_ok p (set TState.dsb_epoch S ts).
Proof. intro Hts. by_fields. Qed.

Lemma emit_promise p tid imem mem ev ts ts' : length mem ≠ p → ts_ok p ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → ts_ok p ts'.
Proof.
  intros Hlen Hts Hrun. unfold TState.emit_promise in Hrun. eapply process_event; [|exact Hrun].
  destruct (bool_decide (Ev.tid ev = tid)); [|exact Hts].
  destruct ev; unfold TState.promise_write, TState.promise_tlbi; by_fields; constructor; assumption.
Qed.
Lemma filter_prom_wr p (P : nat → Prop) `{∀ t, Decision (P t)} ts :
  ts_ok p ts → ts_ok p (set TState.prom_wr (filter P) ts).
Proof. intro Hts. by_fields. apply VMSwapRemoveViews.Forall_filter, ok_prom_wr0. Qed.
Lemma filter_prom_tlbi p (P : nat → Prop) `{∀ t, Decision (P t)} ts :
  ts_ok p ts → ts_ok p (set TState.prom_tlbi (filter P) ts).
Proof. intro Hts. by_fields. apply VMSwapRemoveViews.Forall_filter, ok_prom_tlbi0. Qed.

Lemma update_cohs p avs ts : 0 < p → Forall (λ av, av.2 ≠ p) avs → ts_ok p ts →
  ts_ok p (TState.update_cohs avs ts).
Proof.
  intros Hp Havs Hts. induction Havs as [|[a v] avs Hv Havs IH]; [exact Hts|].
  change (ts_ok p (TState.update_coh a v (TState.update_cohs avs ts))).
  pose proof (VMSwapRemoveViews.lookup_total_ok (λ t, t ≠ p) ltac:(cbn; lia)
    (TState.coh (TState.update_cohs avs ts)) a (ok_coh _ _ IH)) as Hcoh.
  cbn in Hv. unfold TState.update_coh, TState.set_coh. remember (TState.update_cohs avs ts) as mid.
  by_fields. apply map_Forall_insert_2; [cbn; apply VMSwapRemoveTimes.max_avoids; assumption|assumption].
Qed.

Lemma set_fwdbs p addrs n (data : bv n) time vdata xcl ts : time ≠ p → ts_ok p ts →
  ts_ok p (TState.set_fwdbs addrs data time vdata xcl ts).
Proof.
  intros Htime Hts. unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)) as items.
  intro items. revert ts Hts. induction items as [|[addr byte] items IH]; intros ts Hts; [exact Hts|].
  cbn [foldl]. apply IH. unfold TState.set_fwdb. by_fields.
  apply map_Forall_insert_2; [exact Htime|assumption].
Qed.
Lemma set_xclb p time addr size v ts : time ≠ p → ts_ok p ts → ts_ok p (TState.set_xclb time addr size v ts).
Proof.
  intros Htime Hts. unfold TState.set_xclb. by_fields. intros item Hitem. injection Hitem as <-. exact Htime.
Qed.
Lemma clear_xclb p ts : ts_ok p ts → ts_ok p (TState.clear_xclb ts).
Proof. intro Hts. unfold TState.clear_xclb. by_fields. discriminate. Qed.

Ltac iis_fields :=
  match goal with H : iis_ok _ ?iis |- iis_ok _ _ => destruct iis, H; constructor; cbn in * end;
  try assumption.
Lemma iis_init p : iis_ok p IIS.init.
Proof. constructor; discriminate. Qed.
Lemma iis_add p v iis : iis_ok p iis → iis_ok p (IIS.add v iis).
Proof. intro H. iis_fields. Qed.
Lemma iis_trs p trs iis : iis_ok p iis → iis_ok p (setv IIS.trs trs iis).
Proof. intro H. iis_fields. Qed.
Lemma iis_sreg p reg vv iis : iis_ok p iis → iis_ok p (IIS.add_sreg_read reg vv iis).
Proof. intro H. iis_fields. Qed.
Lemma iis_inv p inv iis : (∀ t, inv = Some t → t ≠ p) → iis_ok p iis → iis_ok p (IIS.set_inv_time inv iis).
Proof. intros Hinv H. iis_fields. Qed.
Lemma iis_rmw p rmw iis : (∀ t acq, rmw = Some (t, acq) → t ≠ p) → iis_ok p iis →
  iis_ok p (setv IIS.rmw_read rmw iis).
Proof. intros Hrmw H. iis_fields. Qed.

Lemma read_fwd_time p fwdb macc tread addr found :
  map_Forall (λ _ item, FwdItem.time item ≠ p) fwdb →
  UMPromising.read_fwd fwdb macc tread addr = Some found → found.2 ≠ p.
Proof.
  intros Hfwd. unfold UMPromising.read_fwd. repeat case_match; try discriminate.
  injection 1 as <-. eapply Hfwd; eassumption.
Qed.
End VMSwapRemoveStamps.
