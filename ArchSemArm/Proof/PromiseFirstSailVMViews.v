(******************************************************************************)
(* VM thread views stay within the memory history                             *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstVMExecutionCurrent PromiseFirstSailVMCacheState
  PromiseFirstSailVMReplay PromiseFirstSailVMGuards PromiseFirstSailVMTableReplay
  PromiseFirstSailVMLookup PromiseFirstSailVMRootLookup PromiseFirstSailVMBBMTransport
  PromiseFirstCurrent PromiseFirstEquivCurrent PromiseFirstFreshBroadcast
  PromiseFirstSailSerialization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** Every view of a thread state and of the intra-instruction state is at
    most the memory length, and the thread cache satisfies
    [VMCacheState.cache_ok] at that length. *)
Module VMViews.
Import VMPromising.
#[local] Typeclasses Transparent view UMPromising.view.

Definition le_opt bound (time : option nat) := ∀ t, time = Some t → t ≤ bound.

Definition regs_ok bound (regs : dmap reg (λ reg, reg_type reg * view)%type) :=
  ∀ r rv, dmap_lookup r regs = Some rv → rv.2 ≤ bound.

Definition lev_ok bound (lev : LEv.t) :=
  match lev with
  | LEv.Cse time => time ≤ bound
  | LEv.Wsreg wsreg => WSReg.view wsreg ≤ bound
  end.

Definition fwd_ok bound (item : FwdItem.t) :=
  FwdItem.time item ≤ bound ∧ FwdItem.view item ≤ bound ∧ le_opt bound (FwdItem.xcl_view item).

Definition xcl_ok bound (item : XclItem.t) := XclItem.time item ≤ bound ∧ XclItem.view item ≤ bound.

Record ts_ok bound (ts : TState.t) : Prop := {
  ok_prom_wr : Forall (λ time, time ≤ bound) (TState.prom_wr ts);
  ok_prom_tlbi : Forall (λ time, time ≤ bound) (TState.prom_tlbi ts);
  ok_regs : regs_ok bound (TState.regs ts);
  ok_levs : Forall (lev_ok bound) (TState.levs ts);
  ok_coh : map_Forall (λ _ v, v ≤ bound) (TState.coh ts);
  ok_tcoh : map_Forall (λ _ v, v ≤ bound) (TState.tcoh ts);
  ok_vrd : TState.vrd ts ≤ bound;
  ok_vwr : TState.vwr ts ≤ bound;
  ok_vdmbst : TState.vdmbst ts ≤ bound;
  ok_vdmb : TState.vdmb ts ≤ bound;
  ok_vdsb : TState.vdsb ts ≤ bound;
  ok_vspec : TState.vspec ts ≤ bound;
  ok_vcse : TState.vcse ts ≤ bound;
  ok_vtlbi_self : TState.vtlbi_self ts ≤ bound;
  ok_vtlbi_other : TState.vtlbi_other ts ≤ bound;
  ok_vmsr : TState.vmsr ts ≤ bound;
  ok_vacq : TState.vacq ts ≤ bound;
  ok_vrel : TState.vrel ts ≤ bound;
  ok_fwdb : map_Forall (λ _, fwd_ok bound) (TState.fwdb ts);
  ok_xclb : ∀ item, TState.xclb ts = Some item → xcl_ok bound item;
  ok_cache : VMCacheState.cache_ok bound ts;
}.

Record iis_ok bound (iis : IIS.t) : Prop := {
  ok_strict : IIS.strict iis ≤ bound;
  ok_trs : ∀ trs, IIS.trs iis = Some trs → IIS.TransRes.trans_start trs ≤ bound;
  ok_inv_time : le_opt bound (IIS.inv_time iis);
  ok_rmw_read : ∀ time acq, IIS.rmw_read iis = Some (time, acq) → time ≤ bound;
  ok_sreg_reads : regs_ok bound (IIS.sreg_reads iis);
}.

(** The invariant of an instruction-local state, at its own memory length. *)
Definition ok (ppst : PPState.t TState.t Ev.t IIS.t) :=
  ts_ok (length (PPState.mem ppst)) (PPState.state ppst) ∧
  iis_ok (length (PPState.mem ppst)) (PPState.iis ppst).

(** * Monotonicity *)

Lemma Forall_le_mono bound bound' (l : list nat) :
  bound ≤ bound' → Forall (λ time, time ≤ bound) l → Forall (λ time, time ≤ bound') l.
Proof. intros Hle Hl. eapply list.Forall_impl; [exact Hl|]. cbn. lia. Qed.

Lemma ts_ok_mono bound bound' ts : bound ≤ bound' → ts_ok bound ts → ts_ok bound' ts.
Proof.
  intros Hle []. constructor; try lia.
  - eapply Forall_le_mono; eassumption.
  - eapply Forall_le_mono; eassumption.
  - intros r rv Hr. specialize (ok_regs0 r rv Hr). lia.
  - eapply list.Forall_impl; [eassumption|]. intros []; cbn; lia.
  - intros k v Hk. specialize (ok_coh0 k v Hk). cbn in *. lia.
  - intros k v Hk. specialize (ok_tcoh0 k v Hk). cbn in *. lia.
  - intros k v Hk. destruct (ok_fwdb0 k v Hk) as (? & ? & Hx). split; [lia|]. split; [lia|].
    intros t Ht. specialize (Hx t Ht). lia.
  - intros item Hitem. destruct (ok_xclb0 item Hitem). split; lia.
  - eapply VMCacheState.cache_ok_mono; eassumption.
Qed.

Lemma iis_ok_mono bound bound' iis : bound ≤ bound' → iis_ok bound iis → iis_ok bound' iis.
Proof.
  intros Hle []. constructor; try lia.
  - intros trs Htrs. specialize (ok_trs0 trs Htrs). lia.
  - intros t Ht. specialize (ok_inv_time0 t Ht). lia.
  - intros t acq Ht. specialize (ok_rmw_read0 t acq Ht). lia.
  - intros r rv Hr. specialize (ok_sreg_reads0 r rv Hr). lia.
Qed.

(** * Basic facts *)

Lemma regs_ok_insert bound regs r rv :
  regs_ok bound regs → rv.2 ≤ bound → regs_ok bound (dmap_insert r rv regs).
Proof.
  intros Hregs Hrv k x Hk. rewrite dmap_lookup_insert_case in Hk.
  destruct (decide (r = k)) as [Heq|Hne]; [|exact (Hregs k x Hk)].
  subst k. injection Hk as <-. rewrite ctrans_simpl. exact Hrv.
Qed.

Lemma lookup_total_le bound {K} `{Countable K} (m : gmap K nat) k :
  map_Forall (λ _ v, v ≤ bound) m → m !!! k ≤ bound.
Proof.
  intro Hm. rewrite lookup_total_alt. destruct (m !! k) as [v|] eqn:Hk; cbn; [|lia].
  exact (Hm k v Hk).
Qed.

Lemma to_val_view_if_view sreg wsreg vv :
  WSReg.to_val_view_if sreg wsreg = Some vv → vv.2 = WSReg.view wsreg.
Proof.
  unfold WSReg.to_val_view_if. destruct (decide (WSReg.sreg wsreg = sreg)); [|discriminate]. injection 1 as <-. reflexivity.
Qed.

Lemma read_sreg_direct_lev_ok bound regs sreg levs vv :
  regs_ok bound regs → Forall (lev_ok bound) levs →
  TState.read_sreg_direct_lev regs sreg levs = Some vv → vv.2 ≤ bound.
Proof.
  intros Hregs Hlevs. induction Hlevs as [|lev levs Hlev Hlevs IH]; cbn.
  - apply Hregs.
  - destruct lev as [time|wsreg]; [exact IH|].
    destruct (WSReg.to_val_view_if sreg wsreg) as [found|] eqn:Hfound; [|exact IH].
    injection 1 as <-. apply to_val_view_if_view in Hfound. rewrite Hfound. exact Hlev.
Qed.

Lemma read_sreg_indirect_lev_ok bound regs sreg levs vvs :
  regs_ok bound regs → Forall (lev_ok bound) levs →
  TState.read_sreg_indirect_lev regs sreg levs = Some vvs → ∀ vv, vv ∈ vvs → vv.2 ≤ bound.
Proof.
  intros Hregs Hlevs. revert vvs. induction Hlevs as [|lev levs Hlev Hlevs IH]; intro vvs; cbn.
  - destruct (dmap_lookup sreg regs) as [found|] eqn:Hfound; [|discriminate].
    cbn. injection 1 as <-. intros vv Hin. apply list_elem_of_singleton in Hin as ->.
    exact (Hregs _ _ Hfound).
  - destruct lev as [time|wsreg].
    + destruct (TState.read_sreg_direct_lev regs sreg levs) as [found|] eqn:Hfound; [|discriminate].
      cbn. injection 1 as <-. intros vv Hin. apply list_elem_of_singleton in Hin as ->.
      eapply read_sreg_direct_lev_ok; eassumption.
    + destruct (TState.read_sreg_indirect_lev regs sreg levs) as [rest|] eqn:Hrest; [|discriminate].
      cbn. destruct (WSReg.to_val_view_if sreg wsreg) as [found|] eqn:Hfound.
      * injection 1 as <-. intros vv Hin. apply elem_of_cons in Hin as [->|Hin]; [|exact (IH _ eq_refl vv Hin)].
        apply to_val_view_if_view in Hfound. rewrite Hfound. exact Hlev.
      * injection 1 as <-. exact (IH _ eq_refl).
Qed.

Lemma read_sreg_direct_ok bound ts sreg vv :
  ts_ok bound ts → TState.read_sreg_direct ts sreg = Some vv → vv.2 ≤ bound.
Proof. intros Hok. apply read_sreg_direct_lev_ok; [apply Hok|apply Hok]. Qed.

Lemma read_sreg_indirect_ok bound ts sreg vvs :
  ts_ok bound ts → TState.read_sreg_indirect ts sreg = Some vvs → ∀ vv, vv ∈ vvs → vv.2 ≤ bound.
Proof. intros Hok. apply read_sreg_indirect_lev_ok; [apply Hok|apply Hok]. Qed.

Lemma read_reg_ok bound ts r vv :
  ts_ok bound ts → TState.read_reg ts r = Some vv → vv.2 ≤ bound.
Proof.
  intros Hok. unfold TState.read_reg. case_bool_decide.
  - apply read_sreg_direct_ok, Hok.
  - apply Hok.
Qed.

Lemma roots_ok bound ts :
  ts_ok bound ts →
  VMCacheState.roots_bounded bound (TState.read_sreg_indirect ts TTBR0_EL1) ∧
  VMCacheState.roots_bounded bound (TState.read_sreg_indirect ts TTBR1_EL1).
Proof.
  intros Hok. split; intros root Hin.
  - destruct (TState.read_sreg_indirect ts TTBR0_EL1) as [vvs|] eqn:Hread; [|inversion Hin].
    exact (read_sreg_indirect_ok bound ts _ vvs Hok Hread root Hin).
  - destruct (TState.read_sreg_indirect ts TTBR1_EL1) as [vvs|] eqn:Hread; [|inversion Hin].
    exact (read_sreg_indirect_ok bound ts _ vvs Hok Hread root Hin).
Qed.

(** * Thread state operations *)

Ltac by_fields :=
  match goal with H : ts_ok _ ?ts |- ts_ok _ _ => destruct ts, H; constructor; cbn in * end;
  try assumption; try lia.

Lemma frame_ok bound ts ts' :
  ts_ok bound ts → ts' = setv TState.tlb (TState.tlb ts') ts →
  VMCacheState.cache_ok bound ts' → ts_ok bound ts'.
Proof. intros Hok Hframe Hcache. rewrite Hframe in Hcache |- *. by_fields. Qed.

Local Notation updates acc :=
  (∀ bound v ts, v ≤ bound → ts_ok bound ts → ts_ok bound (TState.update acc v ts)).
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

Lemma update_cohs bound avs ts :
  Forall (λ av, av.2 ≤ bound) avs → ts_ok bound ts → ts_ok bound (TState.update_cohs avs ts).
Proof.
  intros Havs Hok. induction Havs as [|[a v] avs Hv Havs IH]; [exact Hok|].
  change (ts_ok bound (TState.update_coh a v (TState.update_cohs avs ts))).
  pose proof (lookup_total_le bound (TState.coh (TState.update_cohs avs ts)) a (ok_coh _ _ IH)).
  cbn in Hv. unfold TState.update_coh, TState.set_coh.
  remember (TState.update_cohs avs ts) as mid. by_fields.
  apply map_Forall_insert_2; [cbn; apply Nat.max_lub; assumption|assumption].
Qed.

Lemma update_tcohs bound asid offsets v ts :
  v ≤ bound → ts_ok bound ts → ts_ok bound (TState.update_tcohs asid offsets v ts).
Proof.
  intros Hv Hok. induction offsets as [|offset offsets IH]; [exact Hok|].
  change (ts_ok bound (TState.update_tcoh asid offset v (TState.update_tcohs asid offsets v ts))).
  unfold TState.update_tcoh. remember (TState.update_tcohs asid offsets v ts) as mid. by_fields.
  intros k x Hk. destruct (decide ((asid, offset) = k)) as [<-|Hne].
  - rewrite lookup_partial_alter in Hk. rewrite decide_True in Hk by reflexivity. injection Hk as <-.
    match goal with |- context[default 0 ?o] => destruct o as [old|] eqn:Hold end; cbn; [|lia].
    specialize (ok_tcoh0 _ _ Hold). cbn in ok_tcoh0. lia.
  - rewrite lookup_partial_alter_ne in Hk by exact Hne. exact (ok_tcoh0 k x Hk).
Qed.

Lemma foldl_ok {A} bound (f : TState.t → A → TState.t) items ts :
  (∀ ts item, ts_ok bound ts → ts_ok bound (f ts item)) →
  ts_ok bound ts → ts_ok bound (foldl f ts items).
Proof.
  intros Hf. revert ts. induction items as [|item items IH]; intros ts Hok; [exact Hok|].
  cbn. apply IH, Hf, Hok.
Qed.

Lemma set_fwdbs bound addrs n (data : bv n) time vdata xcl ts :
  time ≤ bound → vdata ≤ bound → le_opt bound xcl → ts_ok bound ts →
  ts_ok bound (TState.set_fwdbs addrs data time vdata xcl ts).
Proof.
  intros Htime Hvdata Hxcl. unfold TState.set_fwdbs. apply foldl_ok.
  intros mid [addr byte] Hmid. unfold TState.set_fwdb. by_fields.
  apply map_Forall_insert_2; [|assumption]. split; [exact Htime|]. split; [exact Hvdata|exact Hxcl].
Qed.

Lemma set_xclb bound time addr size v ts :
  time ≤ bound → v ≤ bound → ts_ok bound ts → ts_ok bound (TState.set_xclb time addr size v ts).
Proof.
  intros Htime Hv Hok. unfold TState.set_xclb. by_fields.
  intros item Hitem. injection Hitem as <-. split; assumption.
Qed.

Lemma clear_xclb bound ts : ts_ok bound ts → ts_ok bound (TState.clear_xclb ts).
Proof. intro Hok. unfold TState.clear_xclb. by_fields. discriminate. Qed.

Lemma Forall_filter bound (P : nat → Prop) `{∀ x, Decision (P x)} l :
  Forall (λ time, time ≤ bound) l → Forall (λ time, time ≤ bound) (filter P l).
Proof.
  induction 1 as [|x l Hx Hl IH]; [constructor|].
  rewrite filter_cons. case_decide; [constructor|]; assumption.
Qed.

Lemma filter_prom_wr bound (P : nat → Prop) `{∀ x, Decision (P x)} ts :
  ts_ok bound ts → ts_ok bound (set TState.prom_wr (filter P) ts).
Proof. intro Hok. by_fields. apply Forall_filter, ok_prom_wr0. Qed.

Lemma filter_prom_tlbi bound (P : nat → Prop) `{∀ x, Decision (P x)} ts :
  ts_ok bound ts → ts_ok bound (set TState.prom_tlbi (filter P) ts).
Proof. intro Hok. by_fields. apply Forall_filter, ok_prom_tlbi0. Qed.

Lemma next_epoch bound ts : ts_ok bound ts → ts_ok bound (set TState.dsb_epoch S ts).
Proof. intro Hok. by_fields. Qed.

Lemma set_reg bound r rv ts ts' :
  rv.2 ≤ bound → ts_ok bound ts → TState.set_reg r rv ts = Some ts' → ts_ok bound ts'.
Proof.
  intros Hrv Hok. unfold TState.set_reg. case_decide; [|discriminate].
  injection 1 as <-. by_fields. apply regs_ok_insert; assumption.
Qed.

Lemma process_event tid imem mem ev bound ts ts' :
  bound ≤ length mem → ts_ok bound ts →
  TState.process_event tid imem mem ev ts = Ok ts' → ts_ok (length mem) ts'.
Proof.
  intros Hbound Hok Hrun.
  pose proof (VMCacheState.process_event tid imem mem ev bound ts ts' Hbound (ok_cache _ _ Hok) Hrun).
  eapply frame_ok; [eapply ts_ok_mono; eassumption|eapply VMReadReplay.run_tlb_frame, Hrun|assumption].
Qed.

Lemma emit_promise tid imem mem ev bound ts ts' :
  bound ≤ length mem → ts_ok bound ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → ts_ok (length mem) ts'.
Proof.
  intros Hbound Hok Hrun. unfold TState.emit_promise in Hrun.
  apply (ts_ok_mono _ _ ts Hbound) in Hok.
  eapply (process_event tid imem mem ev (length mem)); [lia| |exact Hrun].
  destruct (bool_decide (Ev.tid ev = tid)); [|exact Hok].
  destruct ev; unfold TState.promise_write, TState.promise_tlbi; by_fields.
  all: constructor; [lia|assumption].
Qed.

Lemma add_wsreg tid imem mem sreg val time ts ts' :
  time ≤ length mem → ts_ok (length mem) ts →
  TState.add_wsreg tid imem mem sreg val time ts = Ok ts' → ts_ok (length mem) ts'.
Proof.
  intros Htime Hok Hrun. destruct (roots_ok _ _ Hok) as [Hroot0 Hroot1].
  pose proof (VMCacheState.add_wsreg tid imem mem sreg val time (length mem) ts ts'
    ltac:(lia) Htime (ok_cache _ _ Hok) Hroot0 Hroot1 Hrun) as Hcache.
  unfold TState.add_wsreg, mbind, result_bind in Hrun.
  match type of Hrun with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hrun as <-. apply VMReadReplay.run_tlb_frame in Hmid.
  rewrite Hmid in Hcache |- *. by_fields.
  all: constructor; [exact Htime|assumption].
Qed.

Lemma cse imem mem tid time ts ts' :
  time ≤ length mem → ts_ok (length mem) ts →
  TState.cse imem mem tid time ts = Ok ts' → ts_ok (length mem) ts'.
Proof.
  intros Htime Hok Hrun.
  pose proof (VMCacheState.cse imem mem tid time (length mem) ts ts'
    Htime (ok_cache _ _ Hok) Hrun) as Hcache.
  unfold TState.cse, mbind, result_bind in Hrun.
  match type of Hrun with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hrun as <-. apply VMReadReplay.run_tlb_frame in Hmid.
  rewrite Hmid in Hcache |- *. by_fields.
  all: constructor; [exact Htime|assumption].
Qed.

Theorem init tid imem iregs ts : TState.init tid imem iregs = Ok ts → ts_ok 0 ts.
Proof.
  intro Hinit. pose proof (VMCacheState.init tid imem iregs ts Hinit) as Hcache.
  revert Hinit Hcache.
  unfold TState.init, othrow, guard_or, mbind, result_bind, fmap, result_fmap.
  destruct (reg_lookup CurrentEL iregs); [|discriminate]. cbn.
  match goal with |- context[match ?d with left _ => _ | right _ => _ end] => destruct d end;
    cbn; [|discriminate].
  destruct (reg_lookup SCTLR_EL1 iregs); [|discriminate]. cbn.
  match goal with |- context[if ?b then _ else _] => destruct b end;
    [destruct (TLB.init tid imem iregs) as [cache|]; [|discriminate]; cbn|].
  all: intros Hts Hcache; injection Hts as <-; constructor; cbn;
    [constructor|constructor| |constructor|apply map_Forall_empty|apply map_Forall_empty|
     lia..|apply map_Forall_empty|discriminate|exact Hcache].
  all: intros reg' rv Hr; rewrite dmap_lookup_map in Hr;
    destruct (dmap_lookup reg' iregs); cbn in Hr; [injection Hr as <-; cbn; lia|discriminate].
Qed.

(** * Intra-instruction state operations *)

Ltac iis_fields :=
  match goal with H : iis_ok _ ?iis |- iis_ok _ _ => destruct iis, H; constructor; cbn in * end;
  try assumption; try lia.

Lemma iis_init : iis_ok 0 IIS.init.
Proof.
  constructor; cbn; try lia; discriminate.
Qed.

Lemma iis_add bound v iis : v ≤ bound → iis_ok bound iis → iis_ok bound (IIS.add v iis).
Proof. intros Hv Hok. iis_fields. Qed.

Lemma iis_set_trs bound tres iis :
  IIS.TransRes.trans_start tres ≤ bound → iis_ok bound iis → iis_ok bound (IIS.set_trs tres iis).
Proof. intros Htres Hok. iis_fields. intros found Hfound. injection Hfound as <-. exact Htres. Qed.

Lemma iis_set_inv_time bound time iis :
  le_opt bound time → iis_ok bound iis → iis_ok bound (IIS.set_inv_time time iis).
Proof. intros Htime Hok. iis_fields. Qed.

Lemma iis_add_sreg_read bound r vv iis :
  vv.2 ≤ bound → iis_ok bound iis → iis_ok bound (IIS.add_sreg_read r vv iis).
Proof. intros Hvv Hok. iis_fields. apply regs_ok_insert; assumption. Qed.

Lemma iis_trs bound found iis :
  (∀ trs, found = Some trs → IIS.TransRes.trans_start trs ≤ bound) → iis_ok bound iis →
  iis_ok bound (set IIS.trs (λ _, found) iis).
Proof. intros Hfound Hok. iis_fields. Qed.

Lemma Forall_cohs bound time (addrs : list address) :
  time ≤ bound → Forall (λ av : address * nat, av.2 ≤ bound) (map (., time) addrs).
Proof. intro Htime. induction addrs; constructor; assumption. Qed.

Lemma iis_rmw_read bound found iis :
  (∀ time acq, found = Some (time, acq) → time ≤ bound) → iis_ok bound iis →
  iis_ok bound (set IIS.rmw_read (λ _, found) iis).
Proof. intros Hfound Hok. iis_fields. Qed.

(** * Outcome handlers *)

Lemma exec_lift_result_inv {St E A} st st' (x : A) (r : result E A) :
  Exec.elem_of_results (st', x) ((mlift r : Exec.t St E A) st) → st' = st ∧ r = Ok x.
Proof.
  destruct r as [a|err].
  - intro H. change ((st', x) ∈ [(st, a)]) in H.
    apply list_elem_of_singleton in H. inversion H. auto.
  - intro H. change ((st', x) ∈ []) in H. inversion H.
Qed.

Ltac invert :=
  repeat match goal with
  | x : unit |- _ => destruct x
  | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  | H : None = Some _ |- _ => inversion H
  | H : Some _ = None |- _ => inversion H
  | H : (_, _) = ?p |- _ => destruct p; inversion H; subst; clear H
  | H : ?p = (_, _) |- _ => destruct p; inversion H; subst; clear H
  | H : Exec.elem_of_results _ (Memory.promise _ _) |- _ =>
      apply VMMemoryGrowth.promise_memory in H as [-> ->]
  | H : Exec.elem_of_results _ ((guard_discard _) _) |- _ =>
      apply Exec.elem_of_guard_discard_inv in H as ->
  | H : Exec.elem_of_results _ ((guard_discard' _) _) |- _ =>
      apply Exec.elem_of_guard_discard_unit_inv in H as ->
  | H : Exec.elem_of_results _ ((guard_or _ _) _) |- _ =>
      apply Exec.elem_of_guard_or_inv in H as ->
  | H : Exec.elem_of_results _ ((_ ≫= _) _) |- _ =>
      apply Exec.elem_of_bind_elim in H as [? [? [? H]]]
  | H : Exec.elem_of_results _ ((mget _) _) |- _ =>
      apply Exec.elem_of_mget_inv in H as [-> ->]
  | H : Exec.elem_of_results _ ((mGet) _) |- _ =>
      apply Exec.elem_of_mGet_inv in H as [-> ->]
  | H : Exec.elem_of_results _ ((mret _) _) |- _ =>
      apply Exec.elem_of_mret_inv in H as [-> ?]
  | H : Exec.elem_of_results _ ((msetv _ _) _) |- _ => unfold msetv in H
  | H : Exec.elem_of_results _ ((mset _ _) _) |- _ =>
      apply Exec.elem_of_mset_inv in H as ->
  | H : Exec.elem_of_results _ ((mSet _) _) |- _ =>
      apply Exec.elem_of_mSet_inv in H as ->
  | H : Exec.elem_of_results _ ((Exec.liftSt _ _) _) |- _ =>
      apply Exec.elem_of_liftSt_inv in H as [? [-> H]]
  | H : Exec.elem_of_results _ ((mlift _) _) |- _ =>
      apply exec_lift_result_inv in H as [-> H]
  | H : Exec.elem_of_results _ ((mlift _) _) |- _ =>
      apply Exec.elem_of_lift_res_inv in H as [-> H]
  | H : Exec.elem_of_results _ ((mchoosel _) _) |- _ =>
      apply Exec.elem_of_mchoosel_inv in H as [-> ?]
  | H : Exec.elem_of_results _ ((mthrow _) _) |- _ =>
      unfold elem_of, Exec.elem_of_results in H; cbn in H; inversion H
  | H : Exec.elem_of_results _ ((mdiscard) _) |- _ =>
      rewrite Exec.mdiscard_eq in H;
      unfold elem_of, Exec.elem_of_results in H; cbn in H; inversion H
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[othrow _ ?opt] => unfold othrow in H end
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[if ?b then _ else _] => destruct b eqn:? end
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[match ?x with _ => _ end] => destruct x eqn:? end
  end.

Section Projections.
Context (ppst : PPState.t TState.t Ev.t IIS.t).
Lemma state_set_state f : PPState.state (set PPState.state f ppst) = f (PPState.state ppst).
Proof. by destruct ppst. Qed.
Lemma mem_set_state f : PPState.mem (set PPState.state f ppst) = PPState.mem ppst.
Proof. by destruct ppst. Qed.
Lemma iis_set_state f : PPState.iis (set PPState.state f ppst) = PPState.iis ppst.
Proof. by destruct ppst. Qed.
Lemma state_set_iis f : PPState.state (set PPState.iis f ppst) = PPState.state ppst.
Proof. by destruct ppst. Qed.
Lemma mem_set_iis f : PPState.mem (set PPState.iis f ppst) = PPState.mem ppst.
Proof. by destruct ppst. Qed.
Lemma iis_set_iis f : PPState.iis (set PPState.iis f ppst) = f (PPState.iis ppst).
Proof. by destruct ppst. Qed.
Lemma state_set_mem f : PPState.state (set PPState.mem f ppst) = PPState.state ppst.
Proof. by destruct ppst. Qed.
Lemma mem_set_mem f : PPState.mem (set PPState.mem f ppst) = f (PPState.mem ppst).
Proof. by destruct ppst. Qed.
Lemma iis_set_mem f : PPState.iis (set PPState.mem f ppst) = PPState.iis ppst.
Proof. by destruct ppst. Qed.
Lemma state_set_state_field {T} (proj : TState.t → T) `{Setter TState.t T proj} f :
  PPState.state (set (proj ∘ PPState.state) f ppst) = set proj f (PPState.state ppst).
Proof. by destruct ppst. Qed.
Lemma mem_set_state_field {T} (proj : TState.t → T) `{Setter TState.t T proj} f :
  PPState.mem (set (proj ∘ PPState.state) f ppst) = PPState.mem ppst.
Proof. by destruct ppst. Qed.
Lemma iis_set_state_field {T} (proj : TState.t → T) `{Setter TState.t T proj} f :
  PPState.iis (set (proj ∘ PPState.state) f ppst) = PPState.iis ppst.
Proof. by destruct ppst. Qed.
Lemma state_set_iis_field {T} (proj : IIS.t → T) `{Setter IIS.t T proj} f :
  PPState.state (set (proj ∘ PPState.iis) f ppst) = PPState.state ppst.
Proof. by destruct ppst. Qed.
Lemma mem_set_iis_field {T} (proj : IIS.t → T) `{Setter IIS.t T proj} f :
  PPState.mem (set (proj ∘ PPState.iis) f ppst) = PPState.mem ppst.
Proof. by destruct ppst. Qed.
Lemma iis_set_iis_field {T} (proj : IIS.t → T) `{Setter IIS.t T proj} f :
  PPState.iis (set (proj ∘ PPState.iis) f ppst) = set proj f (PPState.iis ppst).
Proof. by destruct ppst. Qed.
Lemma state_set_both f :
  PPState.state (set (PPState.state ×× PPState.iis) f ppst) =
    (f (PPState.state ppst, PPState.iis ppst)).1.
Proof.
  destruct ppst as [ts mem iis]. unfold set at 1, Setter_merge. cbn.
  destruct (f (ts, iis)). reflexivity.
Qed.
Lemma mem_set_both f : PPState.mem (set (PPState.state ×× PPState.iis) f ppst) = PPState.mem ppst.
Proof.
  destruct ppst as [ts mem iis]. unfold set at 1, Setter_merge. cbn.
  destruct (f (ts, iis)). reflexivity.
Qed.
Lemma iis_set_both f :
  PPState.iis (set (PPState.state ×× PPState.iis) f ppst) =
    (f (PPState.state ppst, PPState.iis ppst)).2.
Proof.
  destruct ppst as [ts mem iis]. unfold set at 1, Setter_merge. cbn.
  destruct (f (ts, iis)). reflexivity.
Qed.
End Projections.

Section PairProjections.
Context (st : TState.t * IIS.t).
Lemma fst_set_fst f : (set fst f st).1 = f st.1. Proof. by destruct st. Qed.
Lemma snd_set_fst f : (set fst f st).2 = st.2. Proof. by destruct st. Qed.
Lemma fst_set_snd f : (set snd f st).1 = st.1. Proof. by destruct st. Qed.
Lemma snd_set_snd f : (set snd f st).2 = f st.2. Proof. by destruct st. Qed.
Lemma fst_set_snd_field {T} (proj : IIS.t → T) `{Setter IIS.t T proj} f :
  (set (proj ∘ snd) f st).1 = st.1.
Proof. by destruct st. Qed.
Lemma snd_set_snd_field {T} (proj : IIS.t → T) `{Setter IIS.t T proj} f :
  (set (proj ∘ snd) f st).2 = set proj f st.2.
Proof. by destruct st. Qed.
End PairProjections.

Lemma strict_set_rmw_read f iis : IIS.strict (set IIS.rmw_read f iis) = IIS.strict iis.
Proof. by destruct iis. Qed.
Lemma strict_set_trs f iis : IIS.strict (set IIS.trs f iis) = IIS.strict iis.
Proof. by destruct iis. Qed.

#[local] Hint Rewrite strict_set_rmw_read strict_set_trs state_set_state mem_set_state iis_set_state
  state_set_iis mem_set_iis iis_set_iis state_set_mem mem_set_mem iis_set_mem
  state_set_state_field mem_set_state_field iis_set_state_field
  state_set_iis_field mem_set_iis_field iis_set_iis_field
  state_set_both mem_set_both iis_set_both
  fst_set_fst snd_set_fst fst_set_snd snd_set_snd fst_set_snd_field snd_set_snd_field : pp.

Ltac simpl_pp :=
  unfold ok, setv in *; autorewrite with pp in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Lemma cse_candidate_le vpre vmax ts v : v ∈ TState.cse_candidates vpre vmax ts → v ≤ vmax.
Proof.
  intro Hin. pose proof (VMGuardReplay.min_promise_bound vmax ts).
  unfold TState.cse_candidates in Hin. apply elem_of_seq in Hin. lia.
Qed.

(** Expose the fields of every invariant in the context to [lia]. *)
Ltac facts H := let H' := fresh in pose proof H as H'; destruct H'.

Ltac solve_le :=
  cbn [PPState.state PPState.mem PPState.iis length compose] in *;
  unfold setv; autorewrite with pp; cbn;
  unfold join, join_nat, view_if, UMPromising.view_if, view, UMPromising.view in *;
  repeat match goal with |- context[if ?b then _ else _] => destruct b end; lia.

Ltac solve_opt :=
  first [eassumption | let H := fresh in
    unfold le_opt; intros ? H; first [discriminate H|injection H as <-; solve_le]].

Ltac solve_ok :=
  lazymatch goal with
  | |- _ ∧ _ => split; solve_ok
  | |- ts_ok _ ((_ ∘ _) _) => unfold compose; solve_ok
  | |- ts_ok _ (TState.update TState.vrd _ _) => apply update_vrd; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vwr _ _) => apply update_vwr; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vdmbst _ _) => apply update_vdmbst; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vdmb _ _) => apply update_vdmb; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vdsb _ _) => apply update_vdsb; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vspec _ _) => apply update_vspec; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vcse _ _) => apply update_vcse; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vtlbi_self _ _) => apply update_vtlbi_self; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vtlbi_other _ _) => apply update_vtlbi_other; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vmsr _ _) => apply update_vmsr; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vacq _ _) => apply update_vacq; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update TState.vrel _ _) => apply update_vrel; [solve_le|solve_ok]
  | |- ts_ok _ (TState.update_tcohs _ _ _ _) => apply update_tcohs; [solve_le|solve_ok]
  | |- ts_ok _ (TState.set_xclb _ _ _ _ _) => apply set_xclb; [solve_le|solve_le|solve_ok]
  | |- ts_ok _ (TState.clear_xclb _) => apply clear_xclb; solve_ok
  | |- ts_ok _ (TState.set_fwdbs _ _ _ _ _ _) =>
      apply set_fwdbs; [solve_le|solve_le|solve_opt|solve_ok]
  | |- ts_ok _ (TState.update_cohs _ _) =>
      apply update_cohs; [first [eassumption|apply Forall_cohs; solve_le]|solve_ok]
  | |- ts_ok _ (set TState.prom_wr (filter _) _) => apply filter_prom_wr; solve_ok
  | |- ts_ok _ (set TState.prom_tlbi (filter _) _) => apply filter_prom_tlbi; solve_ok
  | |- ts_ok _ (set TState.dsb_epoch S _) => apply next_epoch; solve_ok
  | |- iis_ok _ (set IIS.trs (λ _, _) _) =>
      apply iis_trs; [let H := fresh in intros ? H;
        first [discriminate H|injection H as <-; solve_le]|solve_ok]
  | |- iis_ok _ (set IIS.rmw_read (λ _, _) _) =>
      apply iis_rmw_read; [let H := fresh in intros ? ? H;
        first [discriminate H|injection H as <- <-; solve_le]|solve_ok]
  | |- ts_ok ?bound (TState.make _ _ (TState.regs ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
      let HX := fresh "HX" in assert (HX : ts_ok bound X) by solve_ok;
      destruct HX; constructor; cbn; try assumption; apply Forall_filter; assumption
  | |- iis_ok ?bound (IIS.make (IIS.strict ?X) _ _ _ _) =>
      let HX := fresh "HX" in assert (HX : iis_ok bound X) by solve_ok;
      destruct HX; constructor; cbn; try assumption; discriminate
  | |- iis_ok _ (IIS.add _ _) => apply iis_add; [solve_le|solve_ok]
  | |- iis_ok _ (IIS.set_trs _ _) => apply iis_set_trs; [solve_le|solve_ok]
  | |- iis_ok _ (IIS.set_inv_time _ _) => apply iis_set_inv_time; [solve_opt|solve_ok]
  | |- iis_ok _ (IIS.add_sreg_read _ _ _) => apply iis_add_sreg_read; [solve_le|solve_ok]
  | |- ts_ok _ ?X =>
      match goal with H : ts_ok ?b X |- _ => apply (ts_ok_mono b); [solve_le|exact H] end
  | |- iis_ok _ ?X =>
      match goal with H : iis_ok ?b X |- _ => apply (iis_ok_mono b); [solve_le|exact H] end
  end.

(** Derive invariants and bounds from the results of thread-state operations. *)
Ltac derive bound :=
  repeat match goal with
  | H : _ ∈ TState.cse_candidates _ _ _ |- _ => apply cse_candidate_le in H
  | H : TState.read_sreg_direct ?X _ = Some ?vv |- _ =>
      let Hb := fresh "Hb" in
      assert (Hb : vv.2 ≤ bound) by (eapply read_sreg_direct_ok; [|exact H]; solve_ok);
      cbn [fst snd] in Hb; clear H
  | H : TState.read_reg ?X _ = Some ?vv |- _ =>
      let Hb := fresh "Hb" in
      assert (Hb : vv.2 ≤ bound) by (eapply read_reg_ok; [|exact H]; solve_ok);
      cbn [fst snd] in Hb; clear H
  | H : TState.set_reg _ _ ?X = Some ?Y |- _ =>
      let HY := fresh "Hts" in
      assert (HY : ts_ok bound Y)
        by (eapply set_reg; [| |exact H]; [cbn [fst snd]; solve_le|solve_ok]);
      clear H; facts HY
  | H : TState.add_wsreg _ _ _ _ _ _ ?X = Ok ?Y |- _ =>
      let HY := fresh "Hts" in
      assert (HY : ts_ok bound Y) by (eapply add_wsreg; [| |exact H]; [solve_le|solve_ok]);
      clear H; facts HY
  | H : TState.cse _ _ _ _ ?X = Ok ?Y |- _ =>
      let HY := fresh "Hts" in
      assert (HY : ts_ok bound Y) by (eapply cse; [| |exact H]; [solve_le|solve_ok]);
      clear H; facts HY
  | H : TState.process_event _ _ ?m _ ?X = Ok ?Y |- _ =>
      let HY := fresh "Hts" in
      assert (HY : ts_ok (length m) Y)
        by (eapply (process_event _ _ _ _ bound); [| |exact H]; [solve_le|solve_ok]);
      clear H; facts HY
  | H : Memory.fulfill _ _ _ = Some _ |- _ => apply VMReadReplay.fulfill_bound in H
  | H : TState.xclb ?X = Some _ |- _ =>
      eapply (ok_xclb bound) in H; [|solve_ok]; destruct H
  end.

Lemma run_cse_ok tid imem vmax ppst ppst' r :
  vmax ≤ length (PPState.mem ppst) → ok ppst →
  Exec.elem_of_results (ppst', r) (run_cse tid imem vmax ppst) → ok ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hvmax [Hts Hiis] Hrun. unfold run_cse in Hrun.
  invert. simpl_pp. facts Hts. facts Hiis. derive (length mem).
  solve_ok.
Qed.

Lemma run_barrier_ok tid imem barrier vmax ppst ppst' r :
  vmax ≤ length (PPState.mem ppst) → ok ppst →
  Exec.elem_of_results (ppst', r) (run_barrier tid imem barrier vmax ppst) → ok ppst'.
Proof.
  intros Hvmax Hok Hrun. destruct ppst as [ts mem iis]. unfold run_barrier in Hrun.
  invert. all: try solve [eapply run_cse_ok; [| |eassumption]; eassumption].
  all: destruct Hok as [Hts Hiis]; simpl_pp; facts Hts; facts Hiis; solve_ok.
Qed.

Lemma read_sreg_indirect_ok' bound reg racc st st' vv :
  ts_ok bound st.1 → iis_ok bound st.2 →
  Exec.elem_of_results (st', vv) (read_sreg_indirect reg racc st) →
  st'.1 = st.1 ∧ iis_ok bound st'.2 ∧ vv.2 ≤ bound.
Proof.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold read_sreg_indirect in Hrun.
  invert; subst; simpl_pp.
  - split; [reflexivity|]. split; [exact Hiis|]. eapply (ok_sreg_reads _ _ Hiis); eassumption.
  - match goal with H : ?x ∈ _ |- _ =>
      assert (Hvv : x.2 ≤ bound) by (eapply read_sreg_indirect_ok; eassumption) end.
    split; [reflexivity|]. split; [solve_ok|solve_le].
Qed.

Lemma run_reg_trans_read_ok bound reg racc trs ts ts' vv :
  ts_ok bound ts → Exec.elem_of_results (ts', vv) (run_reg_trans_read reg racc trs ts) →
  ts' = ts ∧ vv.2 ≤ bound.
Proof.
  intros Hts Hrun. unfold run_reg_trans_read in Hrun.
  invert; subst; facts Hts; derive bound; split; try reflexivity; cbn; solve_le.
Qed.

Lemma run_reg_general_read_ok bound reg racc st st' vv :
  ts_ok bound st.1 → iis_ok bound st.2 →
  Exec.elem_of_results (st', vv) (run_reg_general_read reg racc st) →
  st'.1 = st.1 ∧ iis_ok bound st'.2 ∧ vv.2 ≤ bound.
Proof.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold run_reg_general_read in Hrun.
  invert; subst; simpl_pp.
  all: try (eapply (read_sreg_indirect_ok' bound reg racc (ts, iis)); [| |eassumption]; assumption).
  all: facts Hts; derive bound; split; [reflexivity|]; split; [exact Hiis|solve_le].
Qed.

Lemma run_reg_read_ok bound reg racc st st' val :
  ts_ok bound st.1 → iis_ok bound st.2 →
  Exec.elem_of_results (st', val) (run_reg_read reg racc st) →
  ts_ok bound st'.1 ∧ iis_ok bound st'.2.
Proof.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold run_reg_read in Hrun.
  invert; subst; simpl_pp.
  - match goal with H : Exec.elem_of_results _ (run_reg_trans_read _ _ _ _) |- _ =>
      apply (run_reg_trans_read_ok bound) in H as [-> Hv]; [|exact Hts] end.
    split; [exact Hts|]. apply iis_add; [exact Hv|exact Hiis].
  - match goal with H : Exec.elem_of_results _ (run_reg_general_read _ _ _) |- _ =>
      apply (run_reg_general_read_ok bound) in H as (-> & Hiis' & Hv); [|exact Hts|exact Hiis] end.
    split; [exact Hts|]. apply iis_add; [exact Hv|exact Hiis'].
Qed.

Lemma run_reg_write_ok tid imem reg racc val ppst ppst' r :
  ok ppst → Exec.elem_of_results (ppst', r) (run_reg_write tid imem reg racc val ppst) → ok ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros [Hts Hiis] Hrun. unfold run_reg_write in Hrun.
  invert; subst; simpl_pp; facts Hts; facts Hiis; derive (length mem).
  all: solve_ok.
Qed.

Lemma pop_start tres tres' pte :
  IIS.TransRes.pop tres = Ok (tres', pte) →
  IIS.TransRes.trans_start tres' = IIS.TransRes.trans_start tres.
Proof.
  unfold IIS.TransRes.pop. destruct (IIS.TransRes.remaining tres); [discriminate|].
  injection 1 as <- _. reflexivity.
Qed.

Lemma read_pte_ok ppst ppst' r : ok ppst → Exec.elem_of_results (ppst', r) (read_pte ppst) → ok ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros [Hts Hiis] Hrun. unfold read_pte in Hrun.
  invert; subst; simpl_pp. cbn [compose PPState.iis] in *.
  match goal with H : IIS.TransRes.pop _ = Ok _ |- _ => apply pop_start in H as Hstart end.
  split; [exact Hts|]. apply iis_trs; [|exact Hiis]. intros found Hfound. injection Hfound as <-.
  rewrite Hstart. eapply (ok_trs _ _ Hiis). eassumption.
Qed.

Lemma run_trans_end_ok bound trans_end st st' r :
  ts_ok bound st.1 → iis_ok bound st.2 →
  Exec.elem_of_results (st', r) (run_trans_end trans_end st) →
  ts_ok bound st'.1 ∧ iis_ok bound st'.2.
Proof.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold run_trans_end in Hrun.
  invert; subst; simpl_pp; facts Hts; facts Hiis.
  all: match goal with H : IIS.trs _ = Some ?t |- _ =>
    pose proof (ok_trs _ _ Hiis t H) end.
  all: solve_ok.
Qed.

Lemma zip_Forall_snd {A B} (P : B → Prop) (l1 : list A) l2 :
  Forall P l2 → Forall (λ x, P x.2) (zip l1 l2).
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros [|b l2] Hl; cbn; try constructor.
  - inversion Hl; subst; assumption.
  - apply IH. inversion Hl; subst; assumption.
Qed.

Lemma foldr_max_le bound l : Forall (λ v, v ≤ bound) l → foldr Init.Nat.max 0 l ≤ bound.
Proof. induction 1; cbn; [lia|apply Nat.max_lub; assumption]. Qed.

Lemma read_all_ok addr size imem mem tmin candidates candidate :
  Memory.read_all addr size imem mem tmin = Ok candidates → candidate ∈ candidates →
  Forall (λ byte, byte.2 ≤ length mem) candidate.
Proof.
  intros Hread Hin. apply VMTableReplay.read_all_aux_bounded in Hread.
  exact (proj1 (Forall_forall _ _) Hread candidate (proj1 (list_elem_of_In _ _) Hin)).
Qed.

Lemma read_fwd_ok bound fwdb macc tread addr found :
  map_Forall (λ _, fwd_ok bound) fwdb →
  UMPromising.read_fwd fwdb macc tread addr = Some found → found.1.2 ≤ bound ∧ found.2 ≤ bound.
Proof.
  intros Hfwdb. unfold UMPromising.read_fwd. repeat case_match; try discriminate.
  injection 1 as <-. match goal with H : _ !! _ = Some _ |- _ => destruct (Hfwdb _ _ H) as (Ht & Hv & Hx) end.
  unfold FwdItem.read_fwd_view. cbn. repeat case_match; subst; cbn in *;
    try (match goal with H : FwdItem.xcl_view _ = Some ?xv |- _ => rewrite H in Hx end);
    try specialize (Hx _ eq_refl); unfold join, join_nat; lia.
Qed.

Lemma mapped_views {A C} bound (f : A * (bv 8 * nat) → C * nat * nat) addrs candidate :
  (∀ x, x.2.2 ≤ bound → (f x).1.2 ≤ bound ∧ (f x).2 ≤ bound) →
  Forall (λ byte, byte.2 ≤ bound) candidate →
  Forall (λ v, v ≤ bound) (map f (zip addrs candidate)).*1.*2 ∧
  Forall (λ v, v ≤ bound) (map f (zip addrs candidate)).*2.
Proof.
  intros Hf Hcand. apply (zip_Forall_snd _ addrs) in Hcand.
  split; induction Hcand as [|x l Hx Hl IH]; cbn; constructor; try apply IH;
    apply (Hf x Hx).
Qed.

Lemma read_mem_explicit_ok imem addr size macc ppst ppst' r :
  ok ppst → Exec.elem_of_results (ppst', r) (read_mem_explicit imem addr size macc ppst) →
  ok ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros [Hts Hiis] Hrun. unfold read_mem_explicit in Hrun.
  invert; subst; simpl_pp; facts Hts; facts Hiis.
  all: match goal with H : Memory.read_all _ _ _ _ _ = Ok _, Hin : ?c ∈ _ |- _ =>
    pose proof (read_all_ok _ _ _ _ _ _ _ H Hin) as Hcand end.
  all: pose proof (VMTableReplay.max_bytes_bound _ _ Hcand) as Htread.
  all: match goal with |- context[map ?f (zip ?addrs ?cand)] =>
    destruct (mapped_views (length mem) f addrs cand) as [Hviews Htimes]; [|exact Hcand|] end.
  all: try (intros [a [byte twrite]] Hb; cbn in Hb |- *;
    match goal with |- context[default _ ?o] => destruct o eqn:Hfwd end; cbn;
    [eapply read_fwd_ok; eassumption|split; lia]).
  all: match goal with |- context[foldr Init.Nat.max 0 ?l] =>
    assert (Hreads : foldr Init.Nat.max 0 l ≤ length mem) by (apply foldr_max_le; exact Hviews) end.
  all: cbn in Hreads.
  all: apply (zip_Forall_snd _ (addr_range addr size)) in Htimes.
  all: solve_ok.
Qed.

Lemma write_mem_ok tid imem addr size macc data ppst ppst' r :
  ok ppst → Exec.elem_of_results (ppst', r) (write_mem tid imem addr size macc data ppst) →
  ok ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros [Hts Hiis] Hrun. unfold write_mem in Hrun.
  invert; subst; simpl_pp; facts Hts; facts Hiis; derive (length mem).
  all: solve_ok.
Qed.

Lemma materialize_ok tid imem pre tlbi recipient ppst ppst' time created :
  ok ppst →
  Exec.elem_of_results (ppst', (time, created))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient ppst) →
  ok ppst' ∧ time ≤ length (PPState.mem ppst') ∧
  length (PPState.mem ppst) ≤ length (PPState.mem ppst').
Proof.
  destruct ppst as [ts mem iis]. intros [Hts Hiis] Hrun.
  unfold materialize_tlbi_for_recipient in Hrun.
  invert; subst; simpl_pp; facts Hts; facts Hiis; derive (length mem).
  all: split; [solve_ok|split; solve_le].
Qed.

Lemma recipients_ok tid imem pre tlbi recipients vself0 vother0 created0
    ppst ppst' vself vother created :
  ok ppst → vself0 ≤ length (PPState.mem ppst) → vother0 ≤ length (PPState.mem ppst) →
  Exec.elem_of_results (ppst', ((vself, vother), created))
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi)
      ((vself0, vother0), created0) recipients ppst) →
  ok ppst' ∧ vself ≤ length (PPState.mem ppst') ∧ vother ≤ length (PPState.mem ppst').
Proof.
  revert vself0 vother0 created0 ppst.
  induction recipients as [|recipient recipients IH];
    intros vself0 vother0 created0 ppst Hok Hself Hother Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> Heq].
    injection Heq as -> -> ->. auto.
  - cbn [foldlM] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [mid [[[vself1 vother1] created1] [Hstep Htail]]].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time is_new] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> Heq]. injection Heq as Hv1 Hv2 Hc1.
    apply materialize_ok in Hmat as (Hmid & Htime & Hgrow); [|exact Hok].
    eapply IH; [exact Hmid| | |exact Htail]; subst; repeat case_decide; lia.
Qed.

Lemma run_tlbi_ok n tid imem viio tlbi ppst ppst' r :
  ok ppst → viio ≤ length (PPState.mem ppst) →
  Exec.elem_of_results (ppst', r) (run_tlbi n tid imem viio tlbi ppst) → ok ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hok Hviio Hrun. unfold run_tlbi in Hrun.
  invert; subst.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply recipients_ok in H as (Hmid & Hself & Hother); [|exact Hok|cbn; lia|cbn; lia] end.
  all: destruct Hmid as [Hts Hiis]; simpl_pp; facts Hts; facts Hiis; solve_ok.
Qed.

Lemma run_take_exception_ok tid imem fault vmax ppst ppst' r :
  vmax ≤ length (PPState.mem ppst) → ok ppst →
  Exec.elem_of_results (ppst', r) (run_take_exception tid imem fault vmax ppst) → ok ppst'.
Proof.
  intros Hvmax Hok Hrun. unfold run_take_exception in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [inv [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [compose] in Hrun.
  destruct (IIS.inv_time (PPState.iis ppst)) as [t|] eqn:Hinv.
  - eapply run_cse_ok; [|exact Hok|exact Hrun]. exact (ok_inv_time _ _ (proj2 Hok) t Hinv).
  - eapply run_cse_ok; [exact Hvmax|exact Hok|exact Hrun].
Qed.

(** * Translation lookups *)

Definition result_ok bound (result : TLB.Result.t) :=
  TLB.Result.tstart result ≤ bound ∧ le_opt bound (TLB.Result.inv_time result).

Lemma Forall_elem {A} (P : A → Prop) l x : Forall P l → x ∈ l → P x.
Proof.
  intros Hl Hx. induction Hl as [|y l Hy Hl IH]; [inversion Hx|].
  apply elem_of_cons in Hx as [->|Hx]; auto.
Qed.

Lemma events_ok tid ifetch ttbr path bound events tmin tmax inv :
  tmax ≤ bound → le_opt bound inv → Forall (λ event, event.2 ≤ bound) events →
  Forall (result_ok bound)
    (TLB.get_results_from_events tid ifetch ttbr path events tmin tmax inv).
Proof.
  revert tmin tmax inv.
  induction events as [events IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length (TLB.Entry.event * nat)))).
  intros tmin tmax inv Hmax Hinv Hevents.
  destruct events as [|[event time] events].
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); constructor.
  - cbn [TLB.get_results_from_events]. destruct (decide (tmax < tmin)); [constructor|].
    apply Forall_cons_1 in Hevents as [Htime Hevents]. cbn in Htime.
    destruct event.
    + destruct (decide (tmax < time)).
      { apply IH; [unfold ltof; cbn; lia|lia|exact Hinv|exact Hevents]. }
      destruct (decide (time < tmin)).
      { constructor; [split; [cbn; lia|exact Hinv]|constructor]. }
      destruct events as [|[event' time'] rest].
      * constructor; [split; [cbn; lia|exact Hinv]|].
        apply IH; [unfold ltof; cbn; lia|lia|exact Hinv|exact Hevents].
      * destruct event'.
        -- constructor; [split; [cbn; lia|exact Hinv]|].
           apply IH; [unfold ltof; cbn; lia|lia|exact Hinv|exact Hevents].
        -- pose proof Hevents as Hall. apply Forall_cons_1 in Hevents as [_ Hrest].
           destruct (decide (time = time' ∧ (ifetch ∨ tid0 = tid))).
           ++ destruct rest as [|[[|issuer] stamp] rest].
              2: apply IH; [unfold ltof; cbn; lia|lia|exact Hinv|exact Hrest].
              all: constructor; [split; [cbn; lia|exact Hinv]|].
              all: apply IH; [unfold ltof; cbn; lia|lia|exact Hinv|exact Hall].
           ++ constructor; [split; [cbn; lia|exact Hinv]|].
              apply IH; [unfold ltof; cbn; lia|lia|exact Hinv|exact Hall].
    + destruct (decide (ifetch ∨ tid0 = tid)).
      * apply IH; [unfold ltof; cbn; lia|lia|exact Hinv|exact Hevents].
      * apply IH; [unfold ltof; cbn; lia|lia| |exact Hevents].
        intros t Ht. injection Ht as <-. exact Htime.
Qed.

Lemma uncacheable_ok bound results ptes tmin tmax lvl :
  tmin ≤ bound → Forall (result_ok bound) results → Forall (λ pte, pte.2 ≤ bound) ptes →
  Forall (result_ok bound)
    (TLB.get_results_from_events_uncacheable_aux results ptes tmin tmax lvl).
Proof.
  intros Hmin Hresults. revert ptes tmax.
  induction Hresults as [|result results Hhead Htail IH]; intros ptes tmax Hptes; [constructor|].
  destruct result as [ttbr path start stop inv], Hhead as [Hstart Hinv]. cbn in Hstart, Hinv.
  cbn [TLB.get_results_from_events_uncacheable_aux].
  revert tmax. induction Hptes as [|[pte time] ptes Htime Hptes IHptes]; intro tmax; [constructor|].
  cbn [TLB.Result.tstart TLB.Result.tend]. cbn in Htime.
  destruct (decide (Nat.min stop tmax < tmin)); [constructor|].
  destruct (decide (time ≤ start)); destruct (decide (is_tlb_fillable lvl pte));
    try (constructor; [split; cbn; [lia|exact Hinv]|]);
    first [apply IH; constructor; assumption|apply IHptes].
Qed.

Lemma fe_results_ok tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax bound results :
  tmin_unc ≤ bound → tmax ≤ bound → Forall (λ event, event.2 ≤ bound) events →
  TLB.get_result_from_FE tid imem mem ifetch vpn fe events tmin_ok tmin_unc tmax = Ok results →
  Forall (result_ok bound) results.
Proof.
  intros Hunc Hmax Hevents. unfold TLB.get_result_from_FE. case_decide.
  - unfold TLB.get_result_from_table_FE.
    destruct (decide (tmax < tmin_unc)); [injection 1 as <-; constructor|].
    destruct (child_lvl (TLB.FE.lvl fe)) as [lvl|]; [|injection 1 as <-; constructor].
    match goal with |- context[TLB.get_results_from_events ?a ?b ?c ?d ?e ?f ?g ?h] =>
      assert (Hpres : Forall (result_ok bound) (TLB.get_results_from_events a b c d e f g h))
        by (apply events_ok; [exact Hmax|discriminate|exact Hevents]);
      destruct (TLB.get_results_from_events a b c d e f g h) as [|r rs]
    end; [injection 1 as <-; constructor|].
    match goal with |- context[Memory.read_all_pte ?a ?b ?c ?d ?e] =>
      destruct (Memory.read_all_pte a b c d e) as [ptes|err] eqn:Hread end; cbn; [|discriminate].
    injection 1 as <-.
    apply (uncacheable_ok bound (r :: rs) ptes tmin_unc tmax lvl); [exact Hunc|exact Hpres|].
    apply VMTableReplay.read_all_pte_bounded in Hread.
    eapply list.Forall_impl; [exact Hread|]. cbn. lia.
  - unfold TLB.get_result_from_leaf_FE. injection 1 as <-.
    destruct (decide (tmax < tmin_ok)); [constructor|].
    apply events_ok; [exact Hmax|discriminate|exact Hevents].
Qed.

Lemma lookup_ok tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid bound result :
  VMCacheState.cache_inv bound cache → tmin_unc ≤ bound → tmax ≤ bound →
  Exec.elem_of_results result
    (TLB.lookup tid imem mem cache ifetch upper vpn tmin_ok tmin_unc tmax asid) →
  result_ok bound result.
Proof.
  intros [Hgood [Hunique _]] Hunc Hmax Hin.
  apply VMLookupReplay.lookup_witness in Hin as (fe & events & candidates & Hentry & Hget & Hin).
  assert (Hevents : Forall (λ event, event.2 ≤ bound) events).
  { apply VMLookupReplay.get_fes_witness in Hentry as [ctxt [_ Hentry]].
    unfold TLB.VATLB.get_fe in Hentry.
    apply list_elem_of_In, List.in_map_iff in Hentry as [[entry events'] [Heq Hentry]].
    apply list_elem_of_In in Hentry. injection Heq as <- <-.
    rewrite <- (VMBBMTransport.row_history cache ctxt entry events' Hunique Hentry).
    exact (proj2 (Hgood _)). }
  eapply Forall_elem; [|exact Hin]. eapply fe_results_ok; [| | |exact Hget]; assumption.
Qed.

Lemma root_lookup_ok imem mem ts upper vpn ttbr0 tmin_unc tmax bound result :
  ts_ok bound ts → tmin_unc ≤ bound → tmax ≤ bound →
  Exec.elem_of_results result
    (VMRootLookupReplay.root_lookup imem mem ts upper vpn ttbr0 tmin_unc tmax) →
  result_ok bound result.
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
  assert (Hvttbr : vttbr ≤ bound).
  { destruct upper.
    - unfold othrow in Hregs.
      destruct (TState.read_sreg_indirect ts TTBR1_EL1) as [vvs|] eqn:Hvvs; [|discriminate].
      injection Hregs as <-. exact (read_sreg_indirect_ok bound ts _ _ Hts Hvvs _ Hchoice).
    - injection Hregs as <-. apply list_elem_of_singleton in Hchoice.
      injection Hchoice as _ ->. lia. }
  apply VMTableReplay.read_all_pte_bounded in Hread.
  pose proof (Forall_elem _ _ _ Hread Hin) as Hvpte. cbn in Hvpte.
  split; cbn; [unfold join, join_nat; lia|discriminate].
Qed.

Lemma tlb_lookup_ok tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax bound result :
  ts_ok bound ts → tmin_unc ≤ bound → tmax ≤ bound →
  Exec.elem_of_results result
    (TState.tlb_lookup tid imem mem ts ifetch upper vpn asid ttbr0 tmin_ok tmin_unc tmax) →
  result_ok bound result.
Proof.
  intros Hts Hunc Hmax Hin. unfold TState.tlb_lookup in Hin.
  destruct (TState.tlb ts) as [cache|] eqn:Hcache;
    [|unfold Exec.elem_of_results in Hin; cbn in Hin; inversion Hin].
  unfold Exec.elem_of_results, Exec.merge in Hin. cbn [Exec.results] in Hin.
  apply elem_of_app in Hin as [Hin|Hin].
  - eapply lookup_ok; [apply (ok_cache _ _ Hts), Hcache|exact Hunc|exact Hmax|exact Hin].
  - eapply root_lookup_ok; [exact Hts|exact Hunc|exact Hmax|exact Hin].
Qed.

Lemma merge_into_ok bound result results :
  result_ok bound result → Forall (result_ok bound) results →
  Forall (result_ok bound) (TLB.Result.merge_into result results).
Proof.
  intros Hresult Hresults.
  induction Hresults as [|other results Hother Hresults IH]; cbn; [constructor; [exact Hresult|constructor]|].
  case_decide; constructor; try assumption.
  destruct Hother as [Hstart Hinv], Hresult as [Hstart' Hinv']. split.
  - change (Nat.min (TLB.Result.tstart other) (TLB.Result.tstart result) ≤ bound). lia.
  - change (le_opt bound (TLB.Result.inv_time
      (if TLB.Result.walk_lt (TLB.Result.walk result) (TLB.Result.walk other)
       then result else other))).
    destruct (TLB.Result.walk_lt _ _); assumption.
Qed.

Lemma merge_ok bound results :
  Forall (result_ok bound) results → Forall (result_ok bound) (TLB.Result.merge results).
Proof.
  unfold TLB.Result.merge. intro Hresults.
  cut (∀ acc, Forall (result_ok bound) acc →
    Forall (result_ok bound) (foldl (λ acc r, TLB.Result.merge_into r acc) acc results));
    [intro H; apply H; constructor|].
  induction Hresults as [|result results Hresult Hresults IH]; intros acc Hacc; cbn; [exact Hacc|].
  apply IH, merge_into_ok; assumption.
Qed.

Lemma Forall_results {E A} (P : A → Prop) (r : Exec.res E A) :
  (∀ x, Exec.elem_of_results x r → P x) → Forall P (Exec.results r).
Proof.
  destruct r as [results errors]. unfold Exec.elem_of_results. cbn. intro H.
  induction results as [|x results IH]; constructor.
  - apply H. left.
  - apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma run_trans_start_ok tid imem start ppst ppst' r :
  ok ppst → Exec.elem_of_results (ppst', r) (run_trans_start tid imem start ppst) → ok ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros [Hts Hiis] Hrun. unfold run_trans_start in Hrun.
  pose proof (VMGuardReplay.min_promise_bound (length mem) ts) as Hmin.
  invert; subst; simpl_pp; facts Hts; facts Hiis.
  all: try (match goal with H : Exec.elem_of_results _ (read_sreg_indirect ?reg ?racc ?st) |- _ =>
    destruct (read_sreg_indirect_ok' (length mem) reg racc st _ _ Hts Hiis H) as (Hst & Hiis' & _)
    end; cbn in Hst; rewrite Hst).
  all: try (match goal with
    H : Exec.elem_of_results ?x (Exec.make (TLB.Result.merge (Exec.results ?L)) _) |- _ =>
      assert (Hres : result_ok (length mem) x)
        by (eapply Forall_elem; [|exact H]; apply merge_ok, Forall_results;
            intros found Hfound; eapply tlb_lookup_ok; [| | |exact Hfound];
            [exact Hts|solve_le|solve_le]);
      destruct Hres as [Hstart Hinv] end).
  all: solve_ok.
Qed.

Lemma run_outcome_ok n tid imem out ppst ppst' r :
  ok ppst → Exec.elem_of_results (ppst', r) (run_outcome n tid imem out ppst) → ok ppst'.
Proof.
  intros Hok H. funelim (run_outcome n tid imem out ppst).
  all: rewrite <- Heqcall in H.
  all: invert; subst; destruct Hok as [Hts Hiis].
  all: try (split; assumption).
  all: try (match goal with H0 : Exec.elem_of_results _ (run_reg_read ?reg ?racc ?st) |- _ =>
    destruct (run_reg_read_ok _ reg racc st _ _ Hts Hiis H0);
    unfold ok, setv; autorewrite with pp; split; assumption end).
  all: try (match goal with H0 : Exec.elem_of_results _ (run_trans_end ?trans ?st) |- _ =>
    destruct (run_trans_end_ok _ trans st _ _ Hts Hiis H0);
    unfold ok, setv; autorewrite with pp; split; assumption end).
  all: try (eapply run_reg_write_ok; [|eassumption]; split; assumption).
  all: try (eapply read_mem_explicit_ok; [|eassumption]; split; assumption).
  all: try (eapply read_pte_ok; [|eassumption]; split; assumption).
  all: try (eapply write_mem_ok; [|eassumption]; split; assumption).
  all: try (eapply run_trans_start_ok; [|eassumption]; split; assumption).
  all: try (eapply run_barrier_ok; [| |eassumption]; [lia|split; assumption]).
  all: try (eapply run_cse_ok; [| |eassumption]; [lia|split; assumption]).
  all: try (eapply run_take_exception_ok; [| |eassumption]; [lia|split; assumption]).
  all: try (eapply run_tlbi_ok; [| |eassumption]; [split; assumption|exact (ok_strict _ _ Hiis)]).
  all: simpl_pp; facts Hts; facts Hiis; solve_ok.
Qed.

Lemma outcome_memory_growth n (tid : fin n) imem out ppst ppst' r :
  Exec.elem_of_results (ppst', r) (run_outcome n tid imem out ppst) →
  ∃ extra, PPState.mem ppst' = (extra ++ PPState.mem ppst)%list.
Proof.
  destruct r as [r pre]. intro H.
  destruct (VMMemoryGrowth.outcome_memory_growth false n tid imem out ppst ppst' r pre H)
    as [Hsame|[extra [_ [_ [Hnew _]]]]]; [exists []; exact Hsame|exists extra; exact Hnew].
Qed.

(** Every intra-instruction state reachable by running an instruction from a
    state satisfying the invariant satisfies it, and memory grows by a prefix. *)
Theorem instruction_ok n (tid : fin n) imem {A} (mon : iMon A) ppst ppst' ret :
  ok ppst → Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' n tid imem) mon ppst) →
  ok ppst' ∧ ∃ extra, PPState.mem ppst' = (extra ++ PPState.mem ppst)%list.
Proof.
  revert ppst ppst' ret. induction mon as [a|call k IH]; intros ppst ppst' ret Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. split; [exact Hok|exists []; reflexivity].
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (outcome_memory_growth n tid imem out ppst mid (r, pre) Hout) as [extra Hextra].
      destruct (IH r mid ppst' ret (run_outcome_ok n tid imem out ppst mid _ Hok Hout) Htail)
        as [Hfinal [rest Hrest]].
      split; [exact Hfinal|]. exists (rest ++ extra)%list. rewrite Hrest, Hextra, app_assoc. reflexivity.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

(** * Machine states *)

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

(** Every thread state is bounded by the shared history. *)
Definition state_ok (st : state) := ∀ tid, ts_ok (length (PState.events st)) (PState.tstate tid st).

Lemma from_archState_ok ms st : PState.from_archState prom ms = Ok st → state_ok st.
Proof.
  unfold PState.from_archState.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn. injection 1 as <-.
  intro tid. unfold PState.tstate. cbn.
  eapply init. exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid).
Qed.

Lemma promise_ok ev st st' : state_ok st → PState.promise prom ev st = Ok st' → state_ok st'.
Proof.
  intros Hok. unfold PState.promise.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn. injection 1 as <-.
  intro tid. unfold PState.tstate. cbn.
  pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid) as Hts. cbn in Hts.
  eapply emit_promise; [| |exact Hts]; [|apply Hok]. destruct st. cbn. lia.
Qed.

Lemma broadcast_ok (owner : fin n) imem base extra (states states' : vec TState.t n) :
  (∀ i, i ≠ owner → ts_ok (length base) (states !!! i)) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states' →
  states' !!! owner = states !!! owner ∧
  ∀ i, i ≠ owner → ts_ok (length (extra ++ base)) (states' !!! i).
Proof.
  intro Hpre. revert states'. induction extra as [|ev extra IH]; intros states' Hrun.
  - injection Hrun as <-. split; [reflexivity|exact Hpre].
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid;
      [|discriminate].
    cbn [mbind result_bind] in Hrun. destruct (IH mid eq_refl) as [Hown Hrest].
    pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun) as Hlook.
    split.
    + specialize (Hlook owner). cbn in Hlook. rewrite decide_True in Hlook by reflexivity.
      injection Hlook as <-. exact Hown.
    + intros i Hi. specialize (Hlook i). cbn in Hlook. rewrite decide_False in Hlook by exact Hi.
      eapply emit_promise; [| |exact Hlook]; [|apply Hrest, Hi]. cbn. lia.
Qed.

Theorem run_tid_ok isem (tid : fin n) st st' :
  state_ok st → Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) → state_ok st'.
Proof.
  intros Hok Hrun.
  destruct (run_tid_broadcast_decompose prom isem tid st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  assert (Hinit : ok (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init)).
  { split; [apply Hok|]. eapply iis_ok_mono; [|exact iis_init]. lia. }
  destruct (instruction_ok n tid (PState.initmem st) isem _ _ () Hinit Hinst)
    as [[Hts _] [extra Hextra]].
  cbn in Hts, Hextra. subst mem.
  rewrite length_app, Nat.add_sub, take_app_length in Hstates.
  apply broadcast_ok in Hstates as [Hown Hrest];
    [|intros i Hi; rewrite vlookup_insert_ne; [apply Hok|intros ->; contradiction]].
  intro i. unfold PState.tstate. cbn.
  destruct (decide (i = tid)) as [->|Hne].
  - rewrite Hown, vlookup_insert. exact Hts.
  - apply Hrest, Hne.
Qed.

Lemma run_step_ok isem term fuel st st' :
  state_ok st → Exec.elem_of_results (st', ()) (@CPState.run_step isem prom n term fuel st) →
  state_ok st'.
Proof.
  intros Hok Hrun. apply PromiseFirstCurrent.run_step_inv in Hrun
    as [(tid & ev & nst & _ & _ & Hpromise & ->)|(tid & _ & Hrun)].
  - eapply promise_ok; eassumption.
  - eapply run_tid_ok; eassumption.
Qed.

Lemma transition_ok (isem : iMon ()) (term : terminationCondition n) (use_pf : bool) fuel (st st' : state) :
  state_ok st →
  Exec.elem_of_results (st', None)
    ((if use_pf then CPState.run_transition_promise_first_uncached isem prom term fuel
      else CPState.run_transition isem prom term fuel) st) →
  state_ok st'.
Proof.
  intros Hok Hrun. destruct use_pf.
  - apply (PromiseFirstCurrent.run_transition_promise_first_none_inv (prom := prom)) in Hrun
      as (tid & ev & nst & _ & Hpromise & ->).
    eapply promise_ok; eassumption.
  - apply (PromiseFirstCurrent.run_transition_none_inv (prom := prom)) in Hrun as (next & Hstep & ->).
    eapply run_step_ok; eassumption.
Qed.

(** Every state reachable by the promise-first or the direct runner from a
    successful initialisation bounds the views and caches of all threads. *)
Theorem reachable_ok isem term initMs use_pf st :
  PromiseFirstReachable prom isem term initMs use_pf st → state_ok st.
Proof.
  induction 1 as [st Hinit|fuel st st' _ IH Hstep].
  - eapply from_archState_ok; eassumption.
  - eapply transition_ok; eassumption.
Qed.

Corollary reachable_cache_ok isem term initMs use_pf (st : state) tid :
  PromiseFirstReachable prom isem term initMs use_pf st →
  VMCacheState.cache_ok (length (PState.events st)) (PState.tstate tid st).
Proof. intro Hreach. exact (ok_cache _ _ (reachable_ok isem term initMs use_pf st Hreach tid)). Qed.

(** Instruction steps of the Sail serialization, interleaved with promises. *)
Definition Step nondet term (st st' : state) :=
  InstructionTransition prom nondet term st st' ∨ ∃ ev, PState.promise prom ev st = Ok st'.

Theorem steps_ok nondet term st st' :
  state_ok st → rtc (Step nondet term) st st' → state_ok st'.
Proof.
  intros Hok Hsteps. induction Hsteps as [st|st mid fin Hstep _ IH]; [exact Hok|].
  apply IH. destruct Hstep as [(tid & _ & Hrun)|(ev & Hpromise)].
  - eapply run_tid_ok; eassumption.
  - eapply promise_ok; eassumption.
Qed.

Corollary steps_cache_ok nondet term ms (init st : state) tid :
  PState.from_archState prom ms = Ok init → rtc (Step nondet term) init st →
  VMCacheState.cache_ok (length (PState.events st)) (PState.tstate tid st).
Proof.
  intros Hinit Hsteps.
  exact (ok_cache _ _ (steps_ok nondet term init st (from_archState_ok ms init Hinit) Hsteps tid)).
Qed.
End Machine.

End VMViews.
