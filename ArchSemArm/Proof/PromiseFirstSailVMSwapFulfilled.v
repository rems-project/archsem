(******************************************************************************)
(* Fulfilled TLBI handlers across an adjacent promise exchange                *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstVMExecutionCurrent PromiseFirstSailVMViews
  PromiseFirstSailVMCreatingReplay PromiseFirstSailVMTLBINormalization
  PromiseFirstSailVMSwap PromiseFirstSailVMSwapPromises PromiseFirstSailVMSwapCut.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapFulfilled.
Import VMPromising.
#[local] Typeclasses Transparent view UMPromising.view Memory.t.
Local Notation ppState := (PPState.t TState.t Ev.t IIS.t).

Definition lower k v := if decide (v ≤ S k) then min v (pred k) else v.
Lemma lower_le k v : lower k v ≤ v.
Proof. unfold lower. case_decide; lia. Qed.
Lemma lower_guard k pre time : 0 < k → pre < time → lower k pre < VMSwap.swap_time k time.
Proof. unfold lower, VMSwap.swap_time. repeat case_decide; subst; lia. Qed.
Lemma lower_same k v : VMSwapCut.same k v (lower k v).
Proof. unfold lower, VMSwapCut.same. case_decide; lia. Qed.

(** Promise matching and DSB epochs are the fields read by recipient
    materialization. [frame] records every field that it leaves unchanged. *)
Definition related k (a b : ppState) :=
  TState.dsb_epoch (PPState.state b) = TState.dsb_epoch (PPState.state a) ∧
  VMSwapPromises.related k (PPState.mem a) (PPState.mem b)
    (TState.prom_tlbi (PPState.state a)) (TState.prom_tlbi (PPState.state b)).
Definition safe k pre pre' (a : ppState) :=
  ∀ t, t ∈ TState.prom_tlbi (PPState.state a) → pre < t → pre' < VMSwap.swap_time k t.
Definition frame (a a' : ppState) :=
  PPState.mem a' = PPState.mem a ∧ PPState.iis a' = PPState.iis a ∧
  PPState.state a' = setv TState.prom_tlbi (TState.prom_tlbi (PPState.state a')) (PPState.state a).
Lemma frame_refl a : frame a a.
Proof. destruct a as [ts mem iis], ts; repeat split; reflexivity. Qed.
Lemma frame_trans a b c : frame a b → frame b c → frame a c.
Proof.
  intros [Hmb [Hib Hsb]] [Hmc [Hic Hsc]]. split; [congruence|]. split; [congruence|].
  rewrite Hsc, Hsb. destruct (PPState.state a); reflexivity.
Qed.
Lemma safe_lower k pre a : 0 < k → safe k pre (lower k pre) a.
Proof. intros Hk t Hin Hpre. apply lower_guard; assumption. Qed.
Lemma safe_cleared k pre pre' a : 0 < k → VMSwapCut.same k pre pre' →
  k ∉ TState.prom_tlbi (PPState.state a) → S k ∉ TState.prom_tlbi (PPState.state a) →
  safe k pre pre' a.
Proof.
  intros Hk Hsame Hp Hq t Hin Hpre.
  rewrite VMSwapPromises.time_fixed by (intro E; subst; contradiction).
  apply (proj1 (VMSwapCut.same_lt k pre pre' t Hk Hsame
    ltac:(intro E; subst; contradiction) ltac:(intro E; subst; contradiction))), Hpre.
Qed.
Lemma fulfill_member ev proms mem t : Memory.fulfill ev proms mem = Some t → t ∈ proms.
Proof.
  unfold Memory.fulfill, PromMemory.fulfill. rewrite head_reverse. intro H.
  apply last_Some_elem_of in H. apply list_elem_of_filter in H as [_ H]. exact H.
Qed.

Lemma materialize_sim k tid imem pre pre' tlbi rc a b a' time :
  related k a b → safe k pre pre' a →
  Exec.elem_of_results (a', (time, false)) (materialize_tlbi_for_recipient tid imem pre tlbi rc a) →
  ∃ b', Exec.elem_of_results (b', (VMSwap.swap_time k time, false))
      (materialize_tlbi_for_recipient tid imem pre' tlbi rc b) ∧
    related k a' b' ∧ safe k pre pre' a' ∧ frame a a' ∧ frame b b'.
Proof.
  destruct a as [ta ma ia], b as [tb mb ib]. intros [Hepoch Hrel] Hsafe Hrun.
  apply VMCreatingReplay.materialize_fulfilled_inv in Hrun as [Hful [Hpre ->]].
  cbn [PPState.state PPState.mem] in Hepoch, Hrel.
  exists (PPState.Make (set TState.prom_tlbi (filter (λ t, t ≠ VMSwap.swap_time k time)) tb) mb ib).
  split.
  - apply VMTLBINormalization.materialize_fulfilled.
    + rewrite Hepoch, (VMSwapPromises.fulfill_related _ _ _ _ _ _ Hrel), Hful. reflexivity.
    + apply Hsafe; [eapply fulfill_member; exact Hful|exact Hpre].
  - split.
    + split; [exact Hepoch|]. apply VMSwapPromises.fulfill_filter, Hrel.
    + split.
      * intros t Hin Ht. apply list_elem_of_filter in Hin as [_ Hin]. apply Hsafe; assumption.
      * split; repeat split; reflexivity.
Qed.

Lemma recipients_sim k tid imem pre pre' tlbi recipients :
  ∀ a b a' self other self' other' finalself finalother,
  related k a b → safe k pre pre' a →
  VMSwapCut.same k self self' → VMSwapCut.same k other other' →
  Exec.elem_of_results (a', ((finalself, finalother), false))
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) ((self, other), false) recipients a) →
  ∃ b' outself outother,
    Exec.elem_of_results (b', ((outself, outother), false))
      (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre' tlbi) ((self', other'), false) recipients b) ∧
    related k a' b' ∧ safe k pre pre' a' ∧ frame a a' ∧ frame b b' ∧
    VMSwapCut.same k finalself outself ∧ VMSwapCut.same k finalother outother.
Proof.
  induction recipients as [|rc recipients IH]; intros a b a' self other self' other' finalself finalother
    Hrel Hsafe Hself Hother Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> Heq]. injection Heq as <- <-.
    exists b, self', other'. split; [apply Exec.elem_of_mret|].
    split; [exact Hrel|]. split; [exact Hsafe|].
    split; [apply frame_refl|]. split; [apply frame_refl|]. auto.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [acc [Hstep Htail]]].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [next [[time fresh] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->]. cbn in Htail.
    assert (Hfresh : fresh = false).
    { destruct (VMMemoryGrowth.tlbi_recipients_growth _ _ _ _ _ _ _ _ _ _ _ _ _ Htail)
        as [[_ Hflag]|[extra [_ [_ [Hflag _]]]]]; congruence. }
    subst fresh.
    destruct (materialize_sim k tid imem pre pre' tlbi rc a b next time Hrel Hsafe Hmat)
      as [bmid [Hbmat [Hrel' [Hsafe' [Hframea Hframeb]]]]].
    assert (Hs : VMSwapCut.same k (if decide (rc = tid) then max self time else self)
      (if decide (rc = tid) then max self' (VMSwap.swap_time k time) else self')).
    { case_decide; [apply VMSwapCut.same_max; [exact Hself|apply VMSwapCut.swap_same]|exact Hself]. }
    assert (Ho : VMSwapCut.same k (if decide (rc = tid) then other else max other time)
      (if decide (rc = tid) then other' else max other' (VMSwap.swap_time k time))).
    { case_decide; [exact Hother|apply VMSwapCut.same_max; [exact Hother|apply VMSwapCut.swap_same]]. }
    destruct (IH _ _ _ _ _ _ _ _ _ Hrel' Hsafe' Hs Ho Htail)
      as [b' [outself [outother [Hb [Hrel'' [Hsafe'' [Hfa [Hfb [Hfs Hfo]]]]]]]]].
    exists b', outself, outother. split.
    + cbn [foldlM]. eapply Exec.elem_of_bind_intro; [|exact Hb].
      unfold VMMemoryGrowth.tlbi_recipient_step.
      eapply Exec.elem_of_bind_intro; [exact Hbmat|]. apply Exec.elem_of_mret.
    + split; [exact Hrel''|]. split; [exact Hsafe''|].
      split; [eapply frame_trans; eassumption|]. split; [eapply frame_trans; eassumption|]. auto.
Qed.

Definition pre viio (pp : ppState) :=
  TState.vcse (PPState.state pp) ⊔ TState.vdsb (PPState.state pp) ⊔ IIS.strict (PPState.iis pp)
    ⊔ viio ⊔ TState.vspec (PPState.state pp).
Definition kind tid info : result string TLBI.t :=
  let rec := TLBIInfo_rec info in
  match TLBIRecord_op rec with
  | TLBIOp_ALL | TLBIOp_VMALL => Ok (TLBI.All tid)
  | TLBIOp_ASID => Ok (TLBI.Asid tid (TLBIRecord_asid rec))
  | TLBIOp_VAA => Ok (TLBI.Vaa tid (bool_decide (bv_extract 55 1 (TLBIRecord_address rec) = 1%bv))
      (va_to_vpn (TLBIRecord_address rec)) (bool_decide (TLBIRecord_level rec = TLBILevel_Last)))
  | TLBIOp_VA => Ok (TLBI.Va tid (TLBIRecord_asid rec) (bool_decide (bv_extract 55 1 (TLBIRecord_address rec) = 1%bv))
      (va_to_vpn (TLBIRecord_address rec)) (bool_decide (TLBIRecord_level rec = TLBILevel_Last)))
  | _ => Error "Unsupported kind of TLBI"
  end.
Definition recipients n tid info :=
  if decide (TLBIInfo_shareability info = Shareability_NSH) then [tid] else seq 0 n.
Definition finish self other (a : ppState) :=
  PPState.Make (TState.update TState.vtlbi_other other (TState.update TState.vtlbi_self self (PPState.state a)))
    (PPState.mem a) (IIS.add (self ⊔ other) (PPState.iis a)).

Lemma run_inv n tid imem viio info a a' :
  Exec.elem_of_results (a', None) (run_tlbi n tid imem viio info a) →
  TLBIRecord_regime (TLBIInfo_rec info) = Regime_EL10 ∧
  ∃ ev mid self other, kind tid info = Ok ev ∧
    Exec.elem_of_results (mid, ((self, other), false))
      (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem (pre viio a) ev)
        ((0, 0), false) (recipients n tid info) a) ∧ a' = finish self other mid.
Proof.
  destruct a as [ts mem iis]. intro Hrun. unfold run_tlbi in Hrun.
  VMViews.invert; subst; try discriminate.
  all: split; [assumption|].
  all: lazymatch goal with H : Exec.elem_of_results (?mid, ((?self, ?other), false)) (foldlM _ _ _ _) |- _ =>
    eexists _, mid, self, other; split; [unfold kind; rewrite ?Heqt; reflexivity|];
    split; [unfold recipients; rewrite Heqs; exact H|destruct mid; reflexivity] end.
Qed.

Lemma run_intro n tid imem viio info a ev mid self other :
  TLBIRecord_regime (TLBIInfo_rec info) = Regime_EL10 → kind tid info = Ok ev →
  Exec.elem_of_results (mid, ((self, other), false))
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem (pre viio a) ev)
      ((0, 0), false) (recipients n tid info) a) →
  Exec.elem_of_results (finish self other mid, None) (run_tlbi n tid imem viio info a).
Proof.
  intros Hreg Hkind Hrun. unfold run_tlbi.
  destruct (Exec.elem_of_guard_or a "TLBIs in other regimes than EL10 are unsupported" Hreg) as [h Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  unfold kind in Hkind. destruct (TLBIRecord_op (TLBIInfo_rec info)); try discriminate;
    injection Hkind as <-.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  all: eapply Exec.elem_of_bind_intro; [exact Hrun|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  all: destruct mid; apply Exec.elem_of_mret.
Qed.

Definition stable ts :=
  setv TState.prom_tlbi [] (setv TState.vtlbi_self 0 (setv TState.vtlbi_other 0 ts)).
Definition post_frame (a a' : ppState) :=
  PPState.mem a' = PPState.mem a ∧ stable (PPState.state a') = stable (PPState.state a).
Lemma finish_frame a mid self other : frame a mid → post_frame a (finish self other mid).
Proof.
  intros [Hm [Hi Hs]]. split; [exact Hm|]. cbn [finish PPState.state]. rewrite Hs.
  destruct (PPState.state a); reflexivity.
Qed.
Lemma frame_self a mid : frame a mid → TState.vtlbi_self (PPState.state mid) = TState.vtlbi_self (PPState.state a).
Proof. intros [_ [_ ->]]. reflexivity. Qed.
Lemma frame_other a mid : frame a mid → TState.vtlbi_other (PPState.state mid) = TState.vtlbi_other (PPState.state a).
Proof. intros [_ [_ ->]]. reflexivity. Qed.

(** With no fresh recipients, the complete TLBI handler preserves its
    promise correspondence and the three-cut relation on both output views.
    All remaining thread fields, including the cache, stay unchanged on each
    side. The caller separately supplies their relation across the exchange. *)
Theorem run_tlbi_sim k n tid imem viio viio' info a b a' :
  related k a b → safe k (pre viio a) (pre viio' b) a →
  VMSwapCut.same k (TState.vtlbi_self (PPState.state a)) (TState.vtlbi_self (PPState.state b)) →
  VMSwapCut.same k (TState.vtlbi_other (PPState.state a)) (TState.vtlbi_other (PPState.state b)) →
  Exec.elem_of_results (a', None) (run_tlbi n tid imem viio info a) →
  ∃ b', Exec.elem_of_results (b', None) (run_tlbi n tid imem viio' info b) ∧
    related k a' b' ∧ post_frame a a' ∧ post_frame b b' ∧
    VMSwapCut.same k (TState.vtlbi_self (PPState.state a')) (TState.vtlbi_self (PPState.state b')) ∧
    VMSwapCut.same k (TState.vtlbi_other (PPState.state a')) (TState.vtlbi_other (PPState.state b')).
Proof.
  intros Hrel Hsafe Hself Hother Hrun.
  destruct (run_inv _ _ _ _ _ _ _ Hrun) as [Hreg [ev [mid [self [other [Hkind [Hfold ->]]]]]]].
  destruct (recipients_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hrel Hsafe
    (VMSwapCut.same_refl k 0) (VMSwapCut.same_refl k 0) Hfold)
    as [bmid [self' [other' [Hb [Hr [Hg [HaFrame [HbFrame [Hs Ho]]]]]]]]].
  exists (finish self' other' bmid). split; [eapply run_intro; eassumption|].
  split; [exact Hr|]. split; [apply finish_frame, HaFrame|]. split; [apply finish_frame, HbFrame|].
  change (VMSwapCut.same k (max self (TState.vtlbi_self (PPState.state mid)))
      (max self' (TState.vtlbi_self (PPState.state bmid))) ∧
    VMSwapCut.same k (max other (TState.vtlbi_other (PPState.state mid)))
      (max other' (TState.vtlbi_other (PPState.state bmid)))).
  rewrite (frame_self _ _ HaFrame), (frame_self _ _ HbFrame),
    (frame_other _ _ HaFrame), (frame_other _ _ HbFrame).
  split; apply VMSwapCut.same_max; assumption.
Qed.
End VMSwapFulfilled.
