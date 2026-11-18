(******************************************************************************)
(* TLBI promise and view transport, including fresh recipients                *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapFulfilled
  PromiseFirstVMExecutionCurrent PromiseFirstSailVMViews
  PromiseFirstSailVMSwap PromiseFirstSailVMSwapPromises PromiseFirstSailVMSwapCut
  PromiseFirstSailVMTLBINormalization PromiseFirstSailVMCreatingReplay
  PromiseFirstSailVMInstructionReplay PromiseFirstSailVMCacheIndexed PromiseFirstSailVMSwapRemoveRun.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapMaterialize.
Import VMPromising.
#[local] Typeclasses Transparent Memory.t view UMPromising.view.
Local Notation ppState := (PPState.t TState.t Ev.t IIS.t).

Definition valid ts := ∀ c, TState.tlb ts = Some c → VMCacheIndexed.valid c.
Definition bounded (a : ppState) :=
  ∀ t, t ∈ TState.prom_tlbi (PPState.state a) → t ≤ length (PPState.mem a).
(** Materialization needs matching promises, equal history lengths, and
    valid caches. This relation does not assert that the two caches produce
    corresponding translations; that is a separate exchange obligation. *)
Record related k (a b : ppState) := {
  matching : VMSwapFulfilled.related k a b;
  length_eq : length (PPState.mem a) = length (PPState.mem b);
  pair_bound : S k ≤ length (PPState.mem a);
  left_bound : bounded a;
  right_bound : bounded b;
  left_valid : valid (PPState.state a);
  right_valid : valid (PPState.state b);
}.
Definition core ts := setv TState.tlb None (setv TState.prom_tlbi [] ts).
Definition frame (a a' : ppState) :=
  PPState.iis a' = PPState.iis a ∧ core (PPState.state a') = core (PPState.state a).
(** Fresh recipient events extend the two histories by the same prefix. *)
Definition history (a b a' b' : ppState) := ∃ extra : Memory.t,
  PPState.mem a' = extra ++ PPState.mem a ∧ PPState.mem b' = extra ++ PPState.mem b.

Lemma process_valid tid imem mem ev ts ts' : valid ts →
  TState.process_event tid imem mem ev ts = Ok ts' → valid ts'.
Proof.
  intros Hv Hrun. destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (VMSwapRemoveRun.run_tlb_some_inv _ _ _ _ Hc Hrun) as [c' [Hc' ->]].
    intros d Hd. cbn in Hd. injection Hd as <-.
    eapply VMCacheIndexed.fill_promise; [apply Hv, Hc|exact Hc'].
  - unfold TState.process_event in Hrun.
    rewrite (VMSwapRemoveRun.run_tlb_none _ _ Hc) in Hrun. injection Hrun as <-. exact Hv.
Qed.
Lemma process_tlbi_total tid imem mem tlbi rc epoch ts : valid ts →
  ∃ ts', TState.process_event tid imem mem (Ev.Tlbi tlbi rc epoch) ts = Ok ts'.
Proof.
  intro Hv. destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (VMFillTotal.total_fill_promise tid imem mem (Ev.Tlbi tlbi rc epoch) I c (Hv c Hc))
      as [c' [[] [Hc' _]]].
    exists (setv TState.tlb (Some c') ts). eapply VMSwapRemoveRun.run_tlb_some_intro; eassumption.
  - exists ts. apply VMSwapRemoveRun.run_tlb_none, Hc.
Qed.
Lemma filter_fresh (mem : Memory.t) (proms : list nat) :
  (∀ t, t ∈ proms → t ≤ length mem) → filter (λ t, t ≠ S (length mem)) proms = proms.
Proof.
  induction proms as [|t proms IH]; intro Hb; [reflexivity|].
  rewrite filter_cons_True by (pose proof (Hb t ltac:(left)); lia).
  rewrite IH; [reflexivity|]. intros x Hin. apply Hb. right. exact Hin.
Qed.
Lemma set_pending_self ts : setv TState.prom_tlbi (TState.prom_tlbi ts) ts = ts.
Proof. destruct ts; reflexivity. Qed.

Lemma materialize_sim k tid imem pre pre' tlbi rc a b a' time fresh :
  0 < k → related k a b → VMSwapFulfilled.safe k pre pre' a → VMSwapCut.same k pre pre' →
  Exec.elem_of_results (a', (time, fresh)) (materialize_tlbi_for_recipient tid imem pre tlbi rc a) →
  ∃ b', Exec.elem_of_results (b', (VMSwap.swap_time k time, fresh))
      (materialize_tlbi_for_recipient tid imem pre' tlbi rc b) ∧
    related k a' b' ∧ VMSwapFulfilled.safe k pre pre' a' ∧ frame a a' ∧ frame b b' ∧ history a b a' b'.
Proof.
  destruct a as [ta ma ia], b as [tb mb ib]. intros Hk Hr Hsafe Hsame Hrun.
  destruct Hr as [[Hepoch Hmatch] Hlen Hpair Hba Hbb Hva Hvb].
  cbn [PPState.state PPState.mem] in Hepoch, Hmatch, Hlen, Hpair, Hva, Hvb.
  unfold bounded in Hba, Hbb. cbn [PPState.state PPState.mem] in Hba, Hbb.
  destruct fresh.
  - apply VMTLBINormalization.materialize_fresh_inv in Hrun as [Hnone [-> [Hpre [ta' [Ha ->]]]]].
    assert (Hnone' : Memory.fulfill (Ev.Tlbi tlbi rc (TState.dsb_epoch tb)) (TState.prom_tlbi tb) mb = None).
    { rewrite Hepoch, (VMSwapPromises.fulfill_related _ _ _ _ _ _ Hmatch), Hnone. reflexivity. }
    destruct (process_tlbi_total tid imem (Ev.Tlbi tlbi rc (TState.dsb_epoch tb) :: mb)
      tlbi rc (TState.dsb_epoch tb) tb Hvb) as [tb' Hb].
    pose proof (process_valid _ _ _ _ _ _ Hva Ha) as Hva'.
    pose proof (process_valid _ _ _ _ _ _ Hvb Hb) as Hvb'.
    destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Ha) as [ca Ea].
    destruct (VMSwapRemoveRun.run_tlb_frame _ _ _ Hb) as [cb Eb].
    assert (Hta : TState.prom_tlbi ta' = TState.prom_tlbi ta) by (rewrite Ea; reflexivity).
    assert (Htb : TState.prom_tlbi tb' = TState.prom_tlbi tb) by (rewrite Eb; reflexivity).
    assert (Hfa : filter (λ t, t ≠ S (length ma)) (TState.prom_tlbi ta') = TState.prom_tlbi ta')
      by (apply filter_fresh; rewrite Hta; exact Hba).
    assert (Hfb : filter (λ t, t ≠ S (length mb)) (TState.prom_tlbi tb') = TState.prom_tlbi tb')
      by (apply filter_fresh; rewrite Htb; exact Hbb).
    assert (Hpre' : pre' < S (length mb)).
    { rewrite <- Hlen. apply (proj1 (VMSwapCut.same_lt k pre pre' (S (length ma)) Hk Hsame ltac:(lia) ltac:(lia))), Hpre. }
    exists (PPState.Make (set TState.prom_tlbi (filter (λ t, t ≠ S (length mb))) tb')
      (Ev.Tlbi tlbi rc (TState.dsb_epoch tb) :: mb) ib).
    split.
    + rewrite VMSwapPromises.time_fixed by lia. rewrite Hlen.
      apply VMTLBINormalization.materialize_fresh; assumption.
    + change (set TState.prom_tlbi (filter (λ t, t ≠ S (length ma))) ta')
        with (setv TState.prom_tlbi (filter (λ t, t ≠ S (length ma)) (TState.prom_tlbi ta')) ta').
      change (set TState.prom_tlbi (filter (λ t, t ≠ S (length mb))) tb')
        with (setv TState.prom_tlbi (filter (λ t, t ≠ S (length mb)) (TState.prom_tlbi tb')) tb').
      rewrite Hfa, Hfb, !set_pending_self.
      split.
      * constructor.
        -- split; [rewrite Ea, Eb; exact Hepoch|]. cbn [PPState.mem PPState.state].
           rewrite Hta, Htb, Hepoch. apply VMSwapPromises.extend_history; assumption.
        -- cbn [PPState.mem length]. lia.
        -- cbn [PPState.mem length]. lia.
        -- intros t Hin. cbn [PPState.state PPState.mem length] in *. rewrite Hta in Hin. specialize (Hba t Hin). lia.
        -- intros t Hin. cbn [PPState.state PPState.mem length] in *. rewrite Htb in Hin. specialize (Hbb t Hin). lia.
        -- exact Hva'.
        -- exact Hvb'.
      * split.
        -- intros t Hin Ht. cbn [PPState.state] in Hin. rewrite Hta in Hin. apply Hsafe; assumption.
        -- split; [split; [reflexivity|rewrite Ea; reflexivity]|].
           split; [split; [reflexivity|rewrite Eb; reflexivity]|].
           exists [Ev.Tlbi tlbi rc (TState.dsb_epoch ta)]. split; [reflexivity|cbn; rewrite Hepoch; reflexivity].
  - apply VMCreatingReplay.materialize_fulfilled_inv in Hrun as [Hful [Hpre ->]].
    exists (PPState.Make (set TState.prom_tlbi (filter (λ t, t ≠ VMSwap.swap_time k time)) tb) mb ib).
    split.
    + apply VMTLBINormalization.materialize_fulfilled.
      * rewrite Hepoch, (VMSwapPromises.fulfill_related _ _ _ _ _ _ Hmatch), Hful. reflexivity.
      * apply Hsafe; [eapply VMSwapFulfilled.fulfill_member; exact Hful|exact Hpre].
    + split.
      * constructor.
        -- split; [exact Hepoch|]. apply VMSwapPromises.fulfill_filter, Hmatch.
        -- exact Hlen.
        -- exact Hpair.
        -- intros t Hin. apply list_elem_of_filter in Hin as [_ Hin]. apply Hba, Hin.
        -- intros t Hin. apply list_elem_of_filter in Hin as [_ Hin]. apply Hbb, Hin.
        -- exact Hva.
        -- exact Hvb.
      * split.
        -- intros t Hin Ht. apply list_elem_of_filter in Hin as [_ Hin]. apply Hsafe; assumption.
        -- split; [split; reflexivity|]. split; [split; reflexivity|]. exists []; split; reflexivity.
Qed.

Lemma frame_refl a : frame a a.
Proof. split; reflexivity. Qed.
Lemma frame_trans a b c : frame a b → frame b c → frame a c.
Proof. intros [Hia Hca] [Hib Hcb]. split; congruence. Qed.
Lemma history_refl a b : history a b a b.
Proof. exists []; split; reflexivity. Qed.
Lemma history_trans a b a' b' a'' b'' : history a b a' b' → history a' b' a'' b'' → history a b a'' b''.
Proof.
  intros [e [Ha Hb]] [e' [Ha' Hb']]. exists (e' ++ e). rewrite Ha', Hb', Ha, Hb, <- !app_assoc. auto.
Qed.

Lemma recipients_sim k tid imem pre pre' tlbi recipients :
  ∀ a b a' self other self' other' created finalself finalother finalcreated,
  0 < k → related k a b → VMSwapFulfilled.safe k pre pre' a → VMSwapCut.same k pre pre' →
  VMSwapCut.same k self self' → VMSwapCut.same k other other' →
  Exec.elem_of_results (a', ((finalself, finalother), finalcreated))
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) ((self, other), created) recipients a) →
  ∃ b' outself outother,
    Exec.elem_of_results (b', ((outself, outother), finalcreated))
      (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre' tlbi) ((self', other'), created) recipients b) ∧
    related k a' b' ∧ VMSwapFulfilled.safe k pre pre' a' ∧ frame a a' ∧ frame b b' ∧ history a b a' b' ∧
    VMSwapCut.same k finalself outself ∧ VMSwapCut.same k finalother outother.
Proof.
  induction recipients as [|rc recipients IH]; intros a b a' self other self' other' created finalself finalother finalcreated
    Hk Hrel Hsafe Hpre Hself Hother Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> Heq]. injection Heq as <- <- <-.
    exists b, self', other'. split; [apply Exec.elem_of_mret|].
    split; [exact Hrel|]. split; [exact Hsafe|].
    split; [apply frame_refl|]. split; [apply frame_refl|]. split; [apply history_refl|]. auto.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [acc [Hstep Htail]]].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [next [[time fresh] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    destruct (materialize_sim k tid imem pre pre' tlbi rc a b next time fresh Hk Hrel Hsafe Hpre Hmat)
      as [bmid [Hbmat [Hrel' [Hsafe' [Hframea [Hframeb Hhistory]]]]]].
    assert (Hs : VMSwapCut.same k (if decide (rc = tid) then max self time else self)
      (if decide (rc = tid) then max self' (VMSwap.swap_time k time) else self')).
    { case_decide; [apply VMSwapCut.same_max; [exact Hself|apply VMSwapCut.swap_same]|exact Hself]. }
    assert (Ho : VMSwapCut.same k (if decide (rc = tid) then other else max other time)
      (if decide (rc = tid) then other' else max other' (VMSwap.swap_time k time))).
    { case_decide; [exact Hother|apply VMSwapCut.same_max; [exact Hother|apply VMSwapCut.swap_same]]. }
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ Hk Hrel' Hsafe' Hpre Hs Ho Htail)
      as [b' [outself [outother [Hb [Hrel'' [Hsafe'' [Hfa [Hfb [Hhist [Hfs Hfo]]]]]]]]]].
    exists b', outself, outother. split.
    + cbn [foldlM]. eapply Exec.elem_of_bind_intro; [|exact Hb].
      unfold VMMemoryGrowth.tlbi_recipient_step.
      eapply Exec.elem_of_bind_intro; [exact Hbmat|]. apply Exec.elem_of_mret.
    + split; [exact Hrel''|]. split; [exact Hsafe''|].
      split; [eapply frame_trans; eassumption|]. split; [eapply frame_trans; eassumption|].
      split; [eapply history_trans; eassumption|]. auto.
Qed.

Local Notation pre := VMSwapFulfilled.pre.
Local Notation kind := VMSwapFulfilled.kind.
Local Notation recipients := VMSwapFulfilled.recipients.
Local Notation finish := VMSwapFulfilled.finish.
Lemma run_inv n tid imem viio info a a' value :
  Exec.elem_of_results (a', value) (run_tlbi n tid imem viio info a) →
  TLBIRecord_regime (TLBIInfo_rec info) = Regime_EL10 ∧
  ∃ ev mid self other created, kind tid info = Ok ev ∧
    Exec.elem_of_results (mid, ((self, other), created))
      (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem (pre viio a) ev)
        ((0, 0), false) (recipients n tid info) a) ∧
    a' = finish self other mid ∧ value = if created then Some (pre viio a) else None.
Proof.
  destruct a as [ts mem iis]. intro Hrun. unfold run_tlbi in Hrun.
  VMViews.invert; subst; try discriminate.
  all: split; [assumption|].
  all: lazymatch goal with H : Exec.elem_of_results (?mid, ((?self, ?other), ?created)) (foldlM _ _ _ _) |- _ =>
    eexists _, mid, self, other, created; split; [unfold kind; rewrite ?Heqt; reflexivity|];
    split; [unfold recipients; rewrite Heqs; exact H|];
    split; [destruct mid; reflexivity|reflexivity] end.
Qed.
Lemma run_intro n tid imem viio info a ev mid self other created :
  TLBIRecord_regime (TLBIInfo_rec info) = Regime_EL10 → kind tid info = Ok ev →
  Exec.elem_of_results (mid, ((self, other), created))
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem (pre viio a) ev)
      ((0, 0), false) (recipients n tid info) a) →
  Exec.elem_of_results (finish self other mid, if created then Some (pre viio a) else None)
    (run_tlbi n tid imem viio info a).
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

Definition stable ts := setv TState.tlb None (VMSwapFulfilled.stable ts).
Definition post_frame (a a' : ppState) := stable (PPState.state a') = stable (PPState.state a).
Lemma stable_core ts : stable (core ts) = stable ts.
Proof. destruct ts; reflexivity. Qed.
Lemma finish_frame a mid self other : frame a mid → post_frame a (finish self other mid).
Proof.
  intros [Hi Hc]. change (stable (PPState.state mid) = stable (PPState.state a)).
  rewrite <- (stable_core (PPState.state mid)), Hc, stable_core. reflexivity.
Qed.
Lemma frame_self a mid : frame a mid → TState.vtlbi_self (PPState.state mid) = TState.vtlbi_self (PPState.state a).
Proof. intros [_ Hc]. exact (f_equal TState.vtlbi_self Hc). Qed.
Lemma frame_other a mid : frame a mid → TState.vtlbi_other (PPState.state mid) = TState.vtlbi_other (PPState.state a).
Proof. intros [_ Hc]. exact (f_equal TState.vtlbi_other Hc). Qed.
Lemma finish_related k a b self other self' other' : related k a b →
  related k (finish self other a) (finish self' other' b).
Proof. intros []; constructor; assumption. Qed.

(** The handler appends the same fresh events, keeps the pending-promise
    relation, and transports both output views. Fresh materialization may
    change each cache; [post_frame] preserves the other thread fields. *)
Theorem run_tlbi_sim k n tid imem viio viio' info a b a' value :
  0 < k → related k a b → VMSwapFulfilled.safe k (pre viio a) (pre viio' b) a →
  VMSwapCut.same k (pre viio a) (pre viio' b) →
  VMSwapCut.same k (TState.vtlbi_self (PPState.state a)) (TState.vtlbi_self (PPState.state b)) →
  VMSwapCut.same k (TState.vtlbi_other (PPState.state a)) (TState.vtlbi_other (PPState.state b)) →
  Exec.elem_of_results (a', value) (run_tlbi n tid imem viio info a) →
  ∃ b' value', Exec.elem_of_results (b', value') (run_tlbi n tid imem viio' info b) ∧
    related k a' b' ∧ post_frame a a' ∧ post_frame b b' ∧ history a b a' b' ∧
    VMSwapCut.same k (TState.vtlbi_self (PPState.state a')) (TState.vtlbi_self (PPState.state b')) ∧
    VMSwapCut.same k (TState.vtlbi_other (PPState.state a')) (TState.vtlbi_other (PPState.state b')) ∧
    ((value = None ∧ value' = None) ∨ (value = Some (pre viio a) ∧ value' = Some (pre viio' b))).
Proof.
  intros Hk Hrel Hsafe Hpre Hself Hother Hrun.
  destruct (run_inv _ _ _ _ _ _ _ _ Hrun) as [Hreg [ev [mid [self [other [created [Hkind [Hfold [-> ->]]]]]]]]].
  destruct (recipients_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hk Hrel Hsafe Hpre
    (VMSwapCut.same_refl k 0) (VMSwapCut.same_refl k 0) Hfold)
    as [bmid [self' [other' [Hb [Hr [Hg [HaFrame [HbFrame [Hhist [Hs Ho]]]]]]]]]].
  exists (finish self' other' bmid), (if created then Some (pre viio' b) else None).
  split; [eapply run_intro; eassumption|].
  split; [apply finish_related, Hr|]. split; [apply finish_frame, HaFrame|]. split; [apply finish_frame, HbFrame|].
  split; [exact Hhist|].
  match goal with |- _ ∧ _ ∧ ?P =>
  change (VMSwapCut.same k (max self (TState.vtlbi_self (PPState.state mid)))
      (max self' (TState.vtlbi_self (PPState.state bmid))) ∧
    VMSwapCut.same k (max other (TState.vtlbi_other (PPState.state mid)))
      (max other' (TState.vtlbi_other (PPState.state bmid))) ∧ P) end.
  rewrite (frame_self _ _ HaFrame), (frame_self _ _ HbFrame),
    (frame_other _ _ HaFrame), (frame_other _ _ HbFrame).
  split; [apply VMSwapCut.same_max; assumption|]. split; [apply VMSwapCut.same_max; assumption|].
  destruct created; auto.
Qed.

Definition tlbi_pre a := pre (IIS.strict (PPState.iis a)) a.
Definition output_related k a b a' b' :=
  related k a' b' ∧ post_frame a a' ∧ post_frame b b' ∧ history a b a' b' ∧
  VMSwapCut.same k (TState.vtlbi_self (PPState.state a')) (TState.vtlbi_self (PPState.state b')) ∧
  VMSwapCut.same k (TState.vtlbi_other (PPState.state a')) (TState.vtlbi_other (PPState.state b')).

Theorem outcome_sim k n tid imem info a b a' value :
  0 < k → related k a b → VMSwapFulfilled.safe k (tlbi_pre a) (tlbi_pre b) a →
  VMSwapCut.same k (tlbi_pre a) (tlbi_pre b) →
  VMSwapCut.same k (TState.vtlbi_self (PPState.state a)) (TState.vtlbi_self (PPState.state b)) →
  VMSwapCut.same k (TState.vtlbi_other (PPState.state a)) (TState.vtlbi_other (PPState.state b)) →
  Exec.elem_of_results (a', value) (run_outcome' n tid imem (TlbOp info) a) →
  ∃ b', Exec.elem_of_results (b', value) (run_outcome' n tid imem (TlbOp info) b) ∧
    output_related k a b a' b'.
Proof.
  intros Hk Hr Hg Hp Hs Ho Hrun.
  unfold run_outcome' in Hrun. apply Exec.elem_of_fmap_inv in Hrun as [[[] hint] [Heq Hrun]].
  cbn in Heq. subst value. cbn [run_outcome] in Hrun. VMViews.invert; subst.
  lazymatch goal with Htlbi : Exec.elem_of_results (?endpp, ?ret) (run_tlbi _ _ _ _ _ _) |- _ =>
    destruct (run_tlbi_sim k n tid imem _ _ info a b endpp ret Hk Hr Hg Hp Hs Ho Htlbi)
      as [b' [hint' [Hb [Hr' [Hfa [Hfb [Hhist [Hs' [Ho' Hhint]]]]]]]]] end.
  exists b'. split.
  - unfold run_outcome'.
    change (Exec.elem_of_results (b', fst ((), hint')) ((run_outcome n tid imem (TlbOp info) |$> fst) b)).
    apply Exec.elem_of_fmap_intro. cbn [run_outcome].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [exact Hb|]. apply Exec.elem_of_mret.
  - unfold output_related. repeat first [assumption|split].
Qed.
End VMSwapMaterialize.
