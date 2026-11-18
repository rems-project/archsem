(******************************************************************************)
(* Predicates on thread and intra-instruction views                           *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapRemoveRun.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapRemoveState.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMSwapRemoveViews.
Import VMPromising VMSwapRemoveState.
#[local] Typeclasses Transparent view UMPromising.view.

Definition opt_ok (Q : nat → Prop) (o : option nat) := ∀ t, o = Some t → Q t.
Definition fwd_ok Q (item : FwdItem.t) :=
  Q (FwdItem.time item) ∧ Q (FwdItem.view item) ∧ opt_ok Q (FwdItem.xcl_view item).
Definition xcl_ok (Q : nat → Prop) (item : XclItem.t) := Q (XclItem.time item) ∧ Q (XclItem.view item).

Record ts_ok (Q : nat → Prop) (ts : TState.t) : Prop := {
  ok_prom_wr : Forall Q (TState.prom_wr ts);
  ok_prom_tlbi : Forall Q (TState.prom_tlbi ts);
  ok_regs : regs_ok Q (TState.regs ts);
  ok_levs : Forall (lev_ok Q) (TState.levs ts);
  ok_coh : map_Forall (λ _ v, Q v) (TState.coh ts);
  ok_tcoh : map_Forall (λ _ v, Q v) (TState.tcoh ts);
  ok_vrd : Q (TState.vrd ts);
  ok_vwr : Q (TState.vwr ts);
  ok_vdmbst : Q (TState.vdmbst ts);
  ok_vdmb : Q (TState.vdmb ts);
  ok_vdsb : Q (TState.vdsb ts);
  ok_vspec : Q (TState.vspec ts);
  ok_vcse : Q (TState.vcse ts);
  ok_vtlbi_self : Q (TState.vtlbi_self ts);
  ok_vtlbi_other : Q (TState.vtlbi_other ts);
  ok_vmsr : Q (TState.vmsr ts);
  ok_vacq : Q (TState.vacq ts);
  ok_vrel : Q (TState.vrel ts);
  ok_fwdb : map_Forall (λ _, fwd_ok Q) (TState.fwdb ts);
  ok_xclb : ∀ item, TState.xclb ts = Some item → xcl_ok Q item;
}.

(** The translation end is an interval cap, not a dependency view. It can
    equal the removed timestamp even while CSE is below it. *)
Record iis_ok (Q : nat → Prop) (iis : IIS.t) : Prop := {
  ok_strict : Q (IIS.strict iis);
  ok_trs : ∀ trs, IIS.trs iis = Some trs → Q (IIS.TransRes.trans_start trs);
  ok_inv_time : opt_ok Q (IIS.inv_time iis);
  ok_rmw_read : ∀ t acq, IIS.rmw_read iis = Some (t, acq) → Q t;
  ok_sreg_reads : regs_ok Q (IIS.sreg_reads iis);
}.

Lemma ts_ok_impl Q R ts : (∀ t, Q t → R t) → ts_ok Q ts → ts_ok R ts.
Proof.
  intros Himp []. constructor; try (apply Himp; assumption).
  - eapply list.Forall_impl; eassumption.
  - eapply list.Forall_impl; eassumption.
  - intros r rv Hrv. apply Himp, (ok_regs0 r rv Hrv).
  - eapply list.Forall_impl; [exact ok_levs0|]. intros [time|w] H; apply Himp, H.
  - intros k v Hk. apply Himp, (ok_coh0 k v Hk).
  - intros k v Hk. apply Himp, (ok_tcoh0 k v Hk).
  - intros k v Hk. destruct (ok_fwdb0 k v Hk) as (Ht & Hv & Hx). split; [apply Himp, Ht|].
    split; [apply Himp, Hv|]. intros t Ht'. apply Himp, (Hx t Ht').
  - intros item Hi. destruct (ok_xclb0 item Hi). split; apply Himp; assumption.
Qed.

Lemma iis_ok_impl Q R iis : (∀ t, Q t → R t) → iis_ok Q iis → iis_ok R iis.
Proof.
  intros Himp []. constructor.
  - apply Himp, ok_strict0.
  - intros t Ht. apply Himp, (ok_trs0 t Ht).
  - intros t Ht. apply Himp, (ok_inv_time0 t Ht).
  - intros t acq Ht. apply Himp, (ok_rmw_read0 t acq Ht).
  - intros r rv Hrv. apply Himp, (ok_sreg_reads0 r rv Hrv).
Qed.

Lemma sources_of_ok p ts : ts_ok (allowed p (TState.vcse ts)) ts → sources p ts.
Proof. intro H. split; apply H. Qed.

Lemma ts_bounded bound ts : VMViews.ts_ok bound ts → ts_ok (λ t, t ≤ bound) ts.
Proof. intros []. constructor; assumption. Qed.
Lemma iis_bounded bound iis : VMViews.iis_ok bound iis → iis_ok (λ t, t ≤ bound) iis.
Proof. intros []. constructor; assumption. Qed.
Lemma ts_before p bound ts : bound < p → VMViews.ts_ok bound ts → ts_ok (allowed p (TState.vcse ts)) ts.
Proof.
  intros Hlt Hts. eapply ts_ok_impl; [|apply ts_bounded, Hts]. unfold allowed. intros; lia.
Qed.
Lemma iis_before p bound limit iis : bound < p → VMViews.iis_ok bound iis → iis_ok (allowed p limit) iis.
Proof.
  intros Hlt Hiis. eapply iis_ok_impl; [|apply iis_bounded, Hiis]. unfold allowed. intros; lia.
Qed.

Section Closed.
Context (Q : nat → Prop) (Qzero : Q 0) (Qmax : ∀ a b, Q a → Q b → Q (a `max` b)).

Ltac by_fields :=
  match goal with H : ts_ok _ ?ts |- ts_ok _ _ => destruct ts, H; constructor; cbn in * end;
  try assumption; try (apply Qmax; assumption).

Lemma frame_ok ts ts' : ts_ok Q ts → (∃ o, ts' = setv TState.tlb o ts) → ts_ok Q ts'.
Proof using. intros Hok [o ->]. by_fields. Qed.

Local Notation updates acc :=
  (∀ v ts, Q v → ts_ok Q ts → ts_ok Q (TState.update acc v ts)).
Lemma update_vrd : updates TState.vrd. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vwr : updates TState.vwr. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vdmbst : updates TState.vdmbst. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vdmb : updates TState.vdmb. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vdsb : updates TState.vdsb. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vspec : updates TState.vspec. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vcse : updates TState.vcse. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vtlbi_self : updates TState.vtlbi_self. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vtlbi_other : updates TState.vtlbi_other. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vmsr : updates TState.vmsr. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vacq : updates TState.vacq. Proof using Qmax. intros. by_fields. Qed.
Lemma update_vrel : updates TState.vrel. Proof using Qmax. intros. by_fields. Qed.

Lemma lookup_total_ok {K} `{Countable K} (m : gmap K nat) k : map_Forall (λ _ v, Q v) m → Q (m !!! k).
Proof using Qzero.
  intro Hm. rewrite lookup_total_alt. destruct (m !! k) as [v|] eqn:Hk; cbn; [apply (Hm k v Hk)|exact Qzero].
Qed.

Lemma update_cohs avs ts : Forall (λ av, Q av.2) avs → ts_ok Q ts → ts_ok Q (TState.update_cohs avs ts).
Proof using Qzero Qmax.
  intros Havs Hok. induction Havs as [|[a v] avs Hv Havs IH]; [exact Hok|].
  change (ts_ok Q (TState.update_coh a v (TState.update_cohs avs ts))).
  pose proof (lookup_total_ok (TState.coh (TState.update_cohs avs ts)) a (ok_coh _ _ IH)) as Hcoh.
  cbn in Hv. unfold TState.update_coh, TState.set_coh.
  remember (TState.update_cohs avs ts) as mid. by_fields.
  apply map_Forall_insert_2; [cbn; apply Qmax; assumption|assumption].
Qed.

Lemma update_tcohs asid offsets v ts : Q v → ts_ok Q ts → ts_ok Q (TState.update_tcohs asid offsets v ts).
Proof using Qzero Qmax.
  intros Hv Hok. induction offsets as [|offset offsets IH]; [exact Hok|].
  change (ts_ok Q (TState.update_tcoh asid offset v (TState.update_tcohs asid offsets v ts))).
  unfold TState.update_tcoh. remember (TState.update_tcohs asid offsets v ts) as mid. by_fields.
  intros k x Hk. destruct (decide ((asid, offset) = k)) as [<-|Hne].
  - rewrite lookup_partial_alter in Hk. rewrite decide_True in Hk by reflexivity. injection Hk as <-.
    apply Qmax; [exact Hv|].
    match goal with |- context[default 0 ?o] => destruct o as [old|] eqn:Hold end; cbn;
      [exact (ok_tcoh0 _ _ Hold)|exact Qzero].
  - rewrite lookup_partial_alter_ne in Hk by exact Hne. exact (ok_tcoh0 k x Hk).
Qed.

Lemma foldl_ok {A} (f : TState.t → A → TState.t) items ts :
  (∀ ts item, ts_ok Q ts → ts_ok Q (f ts item)) → ts_ok Q ts → ts_ok Q (foldl f ts items).
Proof using.
  intros Hf. revert ts. induction items as [|item items IH]; intros ts Hok; [exact Hok|].
  cbn. apply IH, Hf, Hok.
Qed.

Lemma set_fwdbs addrs n (data : bv n) time vdata xcl ts : Q time → Q vdata → opt_ok Q xcl → ts_ok Q ts →
  ts_ok Q (TState.set_fwdbs addrs data time vdata xcl ts).
Proof using.
  intros Htime Hvdata Hxcl. unfold TState.set_fwdbs. apply foldl_ok.
  intros mid [addr byte] Hmid. unfold TState.set_fwdb. by_fields.
  apply map_Forall_insert_2; [|assumption]. split; [exact Htime|]. split; [exact Hvdata|exact Hxcl].
Qed.

Lemma set_xclb time addr size v ts : Q time → Q v → ts_ok Q ts → ts_ok Q (TState.set_xclb time addr size v ts).
Proof using.
  intros Htime Hv Hok. unfold TState.set_xclb. by_fields.
  intros item Hitem. injection Hitem as <-. split; assumption.
Qed.
Lemma clear_xclb ts : ts_ok Q ts → ts_ok Q (TState.clear_xclb ts).
Proof using. intro Hok. unfold TState.clear_xclb. by_fields. discriminate. Qed.

Lemma Forall_filter (P : nat → Prop) `{∀ x, Decision (P x)} l : Forall Q l → Forall Q (filter P l).
Proof using.
  induction 1 as [|x l Hx Hl IH]; [constructor|].
  rewrite filter_cons. case_decide; [constructor|]; assumption.
Qed.
Lemma filter_prom_wr (P : nat → Prop) `{∀ x, Decision (P x)} ts :
  ts_ok Q ts → ts_ok Q (set TState.prom_wr (filter P) ts).
Proof using. intro Hok. by_fields. apply Forall_filter, ok_prom_wr0. Qed.
Lemma filter_prom_tlbi (P : nat → Prop) `{∀ x, Decision (P x)} ts :
  ts_ok Q ts → ts_ok Q (set TState.prom_tlbi (filter P) ts).
Proof using. intro Hok. by_fields. apply Forall_filter, ok_prom_tlbi0. Qed.
Lemma next_epoch ts : ts_ok Q ts → ts_ok Q (set TState.dsb_epoch S ts).
Proof using. intro Hok. by_fields. Qed.
Lemma set_reg r rv ts ts' : Q rv.2 → ts_ok Q ts → TState.set_reg r rv ts = Some ts' → ts_ok Q ts'.
Proof using.
  intros Hrv Hok. unfold TState.set_reg. case_decide; [|discriminate]. injection 1 as <-.
  by_fields. apply regs_insert; assumption.
Qed.

Lemma process_event tid imem mem ev ts ts' : ts_ok Q ts →
  TState.process_event tid imem mem ev ts = Ok ts' → ts_ok Q ts'.
Proof using. intros Hok Hrun. eapply frame_ok; [exact Hok|eapply VMSwapRemoveRun.run_tlb_frame; exact Hrun]. Qed.

Lemma emit_promise tid imem mem ev ts ts' : Q (length mem) → ts_ok Q ts →
  TState.emit_promise tid imem mem ev ts = Ok ts' → ts_ok Q ts'.
Proof using.
  intros Htime Hok Hrun. unfold TState.emit_promise in Hrun. eapply process_event; [|exact Hrun].
  destruct (bool_decide (Ev.tid ev = tid)); [|exact Hok].
  destruct ev; unfold TState.promise_write, TState.promise_tlbi; by_fields.
  all: constructor; assumption.
Qed.

Lemma add_wsreg tid imem mem sreg val time ts ts' : Q time → ts_ok Q ts →
  TState.add_wsreg tid imem mem sreg val time ts = Ok ts' → ts_ok Q ts'.
Proof using.
  intros Htime Hok Hrun. rewrite VMSwapRemoveRun.add_wsreg_upd in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [o ->].
  by_fields. constructor; assumption.
Qed.

Lemma cse imem mem tid time ts ts' : Q time → ts_ok Q ts →
  TState.cse imem mem tid time ts = Ok ts' → ts_ok Q ts'.
Proof using Qmax.
  intros Htime Hok Hrun. unfold TState.cse in Hrun.
  destruct (TState.run_tlb _ _) as [mid|err] eqn:Hmid; cbn in Hrun; [|discriminate].
  injection Hrun as <-. destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hmid) as [o ->].
  by_fields. constructor; assumption.
Qed.

Ltac iis_fields :=
  match goal with H : iis_ok _ ?iis |- iis_ok _ _ => destruct iis, H; constructor; cbn in * end;
  try assumption; try (apply Qmax; assumption).

Lemma iis_init : iis_ok Q IIS.init.
Proof using Qzero. constructor; cbn; try exact Qzero; discriminate. Qed.
Lemma iis_add v iis : Q v → iis_ok Q iis → iis_ok Q (IIS.add v iis).
Proof using Qmax. intros Hv Hok. iis_fields. Qed.
Lemma iis_set_trs tres iis : Q (IIS.TransRes.trans_start tres) → iis_ok Q iis → iis_ok Q (IIS.set_trs tres iis).
Proof using. intros Ht Hok. iis_fields. intros found Hfound. injection Hfound as <-. exact Ht. Qed.
Lemma iis_set_inv_time o iis : opt_ok Q o → iis_ok Q iis → iis_ok Q (IIS.set_inv_time o iis).
Proof using. intros Ho Hok. iis_fields. Qed.
Lemma iis_add_sreg_read r vv iis : Q vv.2 → iis_ok Q iis → iis_ok Q (IIS.add_sreg_read r vv iis).
Proof using. intros Hvv Hok. iis_fields. apply regs_insert; assumption. Qed.
Lemma iis_trs found iis : (∀ trs, found = Some trs → Q (IIS.TransRes.trans_start trs)) →
  iis_ok Q iis → iis_ok Q (setv IIS.trs found iis).
Proof using. intros Hfound Hok. iis_fields. Qed.
Lemma iis_rmw_read found iis : (∀ t acq, found = Some (t, acq) → Q t) →
  iis_ok Q iis → iis_ok Q (setv IIS.rmw_read found iis).
Proof using. intros Hfound Hok. iis_fields. Qed.

Lemma read_sreg_direct ts reg vv : ts_ok Q ts → TState.read_sreg_direct ts reg = Some vv → Q vv.2.
Proof using. intros Hok. apply read_sreg_direct_lev; [apply Hok|apply Hok]. Qed.
Lemma read_sreg_indirect ts reg vvs : ts_ok Q ts → TState.read_sreg_indirect ts reg = Some vvs →
  ∀ vv, vv ∈ vvs → Q vv.2.
Proof using. intros Hok. apply read_sreg_indirect_lev; [apply Hok|apply Hok]. Qed.
Lemma read_reg ts reg vv : ts_ok Q ts → TState.read_reg ts reg = Some vv → Q vv.2.
Proof using.
  intro Hok. unfold TState.read_reg. case_bool_decide; [apply read_sreg_direct, Hok|apply Hok].
Qed.

#[local] Hint Rewrite VMViews.fst_set_fst VMViews.snd_set_fst VMViews.fst_set_snd VMViews.snd_set_snd
  VMViews.fst_set_snd_field VMViews.snd_set_snd_field : pair_views.
Ltac simpl_pair := unfold setv in *; autorewrite with pair_views in *; cbn [fst snd] in *.

Lemma read_sreg_indirect_ok reg racc st st' vv : ts_ok Q st.1 → iis_ok Q st.2 →
  Exec.elem_of_results (st', vv) (VMPromising.read_sreg_indirect reg racc st) →
  st'.1 = st.1 ∧ iis_ok Q st'.2 ∧ Q vv.2.
Proof using.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold VMPromising.read_sreg_indirect in Hrun.
  VMViews.invert; subst; simpl_pair.
  - split; [reflexivity|]. split; [exact Hiis|]. eapply (ok_sreg_reads _ _ Hiis); eassumption.
  - match goal with H : ?x ∈ _ |- _ =>
      assert (Hvv : Q x.2) by (eapply read_sreg_indirect; eassumption) end.
    split; [reflexivity|]. split; [apply iis_add_sreg_read; assumption|exact Hvv].
Qed.

Lemma run_reg_trans_read_ok reg racc trs ts ts' vv : ts_ok Q ts →
  Exec.elem_of_results (ts', vv) (run_reg_trans_read reg racc trs ts) → ts' = ts ∧ Q vv.2.
Proof using Qzero.
  intros Hts Hrun. unfold run_reg_trans_read in Hrun. VMViews.invert; subst.
  all: split; [reflexivity|]; cbn; first [exact Qzero|eapply read_reg; eassumption].
Qed.

Lemma run_reg_general_read_ok reg racc st st' vv : ts_ok Q st.1 → iis_ok Q st.2 →
  Exec.elem_of_results (st', vv) (run_reg_general_read reg racc st) →
  st'.1 = st.1 ∧ iis_ok Q st'.2 ∧ Q vv.2.
Proof using.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold run_reg_general_read in Hrun.
  VMViews.invert; subst; simpl_pair.
  all: try solve [eapply (read_sreg_indirect_ok reg racc (ts, iis)); eassumption].
  all: split; [reflexivity|]; split; [exact Hiis|];
    first [eapply read_sreg_direct; eassumption|eapply read_reg; eassumption].
Qed.

Lemma run_reg_read_ok reg racc st st' val : ts_ok Q st.1 → iis_ok Q st.2 →
  Exec.elem_of_results (st', val) (run_reg_read reg racc st) → st'.1 = st.1 ∧ iis_ok Q st'.2.
Proof using Qzero Qmax.
  destruct st as [ts iis]. intros Hts Hiis Hrun. unfold run_reg_read in Hrun.
  VMViews.invert; subst; simpl_pair.
  - match goal with H : Exec.elem_of_results _ (run_reg_trans_read _ _ _ _) |- _ =>
      apply run_reg_trans_read_ok in H as [-> Hv]; [|exact Hts] end.
    split; [reflexivity|]. apply iis_add; assumption.
  - match goal with H : Exec.elem_of_results _ (run_reg_general_read _ _ _) |- _ =>
      apply run_reg_general_read_ok in H as (-> & Hiis' & Hv); [|exact Hts|exact Hiis] end.
    split; [reflexivity|]. apply iis_add; assumption.
Qed.

Lemma foldr_max_ok xs : Forall Q xs → Q (foldr Init.Nat.max 0 xs).
Proof using Qzero Qmax. induction 1; cbn; [exact Qzero|apply Qmax; assumption]. Qed.
Lemma max_list_ok {A} (f : A → nat) xs : Forall (λ x, Q (f x)) xs → Q (max_list_with f xs).
Proof using Qzero Qmax. induction 1; cbn; [exact Qzero|apply Qmax; assumption]. Qed.
Lemma view_if_ok b v : Q v → Q (view_if b v).
Proof using Qzero. intro Hv. destruct b; [exact Hv|exact Qzero]. Qed.

Lemma read_fwd_ok fwdb macc tread addr found : map_Forall (λ _, fwd_ok Q) fwdb →
  UMPromising.read_fwd fwdb macc tread addr = Some found → Q found.1.2 ∧ Q found.2.
Proof using Qmax.
  intros Hfwdb. unfold UMPromising.read_fwd. repeat case_match; try discriminate.
  injection 1 as <-. match goal with H : _ !! _ = Some _ |- _ =>
    destruct (Hfwdb _ _ H) as (Ht & Hv & Hx) end.
  split; [|exact Ht]. unfold FwdItem.read_fwd_view. cbn.
  destruct (FwdItem.xcl_view _) as [xv|] eqn:Hxv; [destruct (is_rel_acq macc)|].
  - apply Qmax; [exact Hv|apply Hx, eq_refl].
  - exact Hv.
  - exact Hv.
Qed.

Lemma mapped_views {A C} (f : A * (bv 8 * nat) → C * nat * nat) addrs candidate :
  (∀ x, Q x.2.2 → Q (f x).1.2 ∧ Q (f x).2) → Forall (λ byte, Q byte.2) candidate →
  Forall Q (map f (zip addrs candidate)).*1.*2 ∧ Forall Q (map f (zip addrs candidate)).*2.
Proof using.
  intros Hf Hcand. apply (VMViews.zip_Forall_snd _ addrs) in Hcand.
  split; induction Hcand as [|x l Hx Hl IH]; cbn; constructor; try apply IH; apply (Hf x Hx).
Qed.
End Closed.
End VMSwapRemoveViews.
