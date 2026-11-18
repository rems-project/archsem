(******************************************************************************)
(* Certification promise collection after removing a foreign TLBI             *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMCacheSim PromiseFirstSailVMViews
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup PromiseFirstSailVMSwapInsert
  PromiseFirstSailVMSwapRemoveRun PromiseFirstSailVMSwapRemoveLocal PromiseFirstSailVMSwapRemoveOutcome
  PromiseFirstSailVMSwapRemoveDelivery PromiseFirstSailVMSwapRemoveTrace PromiseFirstSailVMNormalization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveCertification.
Import VMPromising VMSwapSim VMSwapLookup VMSwapRemoveRun VMSwapRemoveLocal VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Section Removed.
Context (r : Memory.t) (tlbi : TLBI.t) (rc epoch : nat).
Local Notation p := (S (length r)).
Local Notation g := (unshift (S (length r))).
Local Notation e := (Ev.Tlbi tlbi rc epoch).
Local Notation R := (related r tlbi rc epoch).

Definition lp_rel (a b : list Ev.t * PPState.t TState.t Ev.t IIS.t) := a.1 = b.1 ∧ R a.2 b.2.

Lemma above_base base v : p ≤ base → (g v ≤ g base ↔ v ≤ base).
Proof. intros Hb. unfold unshift. repeat case_decide; lia. Qed.
Lemma stopping_base base v : p ≤ base → (g base < g v ↔ base < v).
Proof. intros Hb. pose proof (above_base base v Hb) as H. lia. Qed.
Lemma collected_prefix base a b : p ≤ base → R a b →
  take (length (PPState.mem a) - base) (PPState.mem a) =
  take (length (PPState.mem b) - g base) (PPState.mem b).
Proof.
  intros Hb [[l [-> ->]] _]. rewrite unshift_ge by exact Hb.
  assert (Hlen : length (l ++ e :: r) - base = length (l ++ r) - pred base)
    by (rewrite !length_app; cbn; lia).
  assert (Htake : length (l ++ e :: r) - base ≤ length l) by (rewrite length_app; cbn; lia).
  rewrite <- Hlen. rewrite !take_app_le by exact Htake. reflexivity.
Qed.

Lemma lift_at {A B} (V : A → B → Prop) m1 m2 a b : lp_rel a b →
  VMSwapInsert.esim_at R V m1 m2 a.2 b.2 →
  VMSwapInsert.esim_at lp_rel V (Exec.liftSt snd m1) (Exec.liftSt snd m2) a b.
Proof.
  intros [Hprom Hrel] [Hr He]. split.
  - intros a' x Hrun. apply Exec.elem_of_liftSt_inv in Hrun as [mid [-> Hrun]].
    destruct (Hr mid x Hrun) as [mid' [y [Hrun' [Hrel' Hvalue]]]].
    exists (setv snd mid' b), y. split; [apply Exec.elem_of_liftSt, Hrun'|].
    split; [split; assumption|exact Hvalue].
  - intros a' err Hrun.
    change ((a', err) ∈ map (λ '(st, x), (setv snd st a, x)) (Exec.errors (m1 a.2))) in Hrun.
    apply list_elem_of_fmap in Hrun as [[mid err0] [Heq Hrun]]. injection Heq as -> ->.
    destruct (He mid err0 Hrun) as [mid' [err' [Hrun' Hrel']]].
    exists (setv snd mid' b), err'. split; [|split; assumption].
    change ((setv snd mid' b, err') ∈ map (λ '(st, x), (setv snd st b, x)) (Exec.errors (m2 b.2))).
    apply list_elem_of_fmap. exists (mid', err'). split; [reflexivity|exact Hrun'].
Qed.

Section Handler.
Context (bbm : bool) {n : nat} (tid : fin n) (imem : memoryMap) (base : nat).
Hypothesis Hrc : fin_to_nat tid ≠ rc.
Hypothesis Hbase : p ≤ base.
Local Notation prom := (VMPromising bbm).
Local Notation ok := (VMSwapRemoveOutcome.ok imem r tlbi rc epoch).

Lemma outcome_sim out a b : lp_rel a b → ok a.2 →
  VMSwapInsert.esim_at lp_rel eq (CPState.run_outcome_with_promise prom tid imem base out)
    (CPState.run_outcome_with_promise prom tid imem (g base) out) a b.
Proof using Hrc Hbase.
  intros Hrel Hok. unfold CPState.run_outcome_with_promise.
  eapply (VMSwapInsert.esim_at_bind _ (VMSwapRemoveOutcome.out_rel r)).
  - apply lift_at; [exact Hrel|]. eapply VMSwapRemoveOutcome.run_outcome_sim; [exact Hrc|apply Hrel|exact Hok].
  - intros a' b' [ret opt] [ret' opt'] Ha Hb Hr [Hret Hopt]. cbn in Hret, Hopt. subst ret' opt'.
    destruct opt as [pre|]; cbn.
    + destruct (decide (pre ≤ base)) as [Hpre|Hpre].
      * rewrite decide_True by (apply (above_base base pre Hbase), Hpre).
        apply VMSwapInsert.esim_at_mget; [exact Hr|]. cbn [compose].
        rewrite (collected_prefix base a'.2 b'.2 Hbase (proj2 Hr)).
        apply VMSwapInsert.esim_at_of; [|exact Hr].
        eapply (esim_bind _ eq).
        { apply esim_mset. intros [pa sa] [pb sb] [Hp Hs]. split; [cbn in *; congruence|exact Hs]. }
        intros ? ? _. apply esim_ret. reflexivity.
      * rewrite decide_False by (intros H; apply Hpre, (above_base base pre Hbase), H).
        apply VMSwapInsert.esim_at_of; [apply esim_ret; reflexivity|exact Hr].
    + apply VMSwapInsert.esim_at_of; [apply esim_ret; reflexivity|exact Hr].
Qed.

Lemma outcome_ok out a a' value : ok a.2 →
  Exec.elem_of_results (a', value) (CPState.run_outcome_with_promise prom tid imem base out a) → ok a'.2.
Proof using Hrc.
  intros Hok Hrun. unfold CPState.run_outcome_with_promise in Hrun.
  VMViews.invert; subst; cbn in *.
  all: eapply VMSwapRemoveOutcome.run_outcome_ok; eassumption.
Qed.

Theorem cinterp_sim {A} (mon : iMon A) a b : lp_rel a b → ok a.2 →
  VMSwapInsert.esim_at lp_rel eq (cinterp (CPState.run_outcome_with_promise prom tid imem base) mon)
    (cinterp (CPState.run_outcome_with_promise prom tid imem (g base)) mon) a b.
Proof using Hrc Hbase.
  revert a b. induction mon as [value|call k IH]; intros a b Hrel Hok.
  - cbn. apply VMSwapInsert.esim_at_of; [apply esim_ret; reflexivity|exact Hrel].
  - destruct call as [out|[choices]]; cbn.
    + eapply (VMSwapInsert.esim_at_bind _ eq); [apply outcome_sim; assumption|].
      intros a' b' x y Ha Hb Hr <-. apply IH; [exact Hr|eapply outcome_ok; eassumption].
    + eapply (VMSwapInsert.esim_at_bind _ eq).
      * apply VMSwapInsert.esim_at_of; [apply esim_mchoose|exact Hrel].
      * intros a' b' x y Ha Hb Hr <-. apply Exec.elem_of_mchoose_inv in Ha as ->. apply IH; assumption.
Qed.
End Handler.

Lemma reset_rel a b : lp_rel a b →
  lp_rel (setv (PPState.iis ∘ snd) IIS.init a) (setv (PPState.iis ∘ snd) IIS.init b).
Proof.
  destruct a as [pa [ta ma ia]], b as [pb [tb mb ib]]. intros [Hp [Hm [Ht Hi]]].
  split; [exact Hp|]. split; [exact Hm|]. split; [exact Ht|]. symmetry. apply VMSwapRemoveDelivery.iis_init.
Qed.
Lemma reset_ok imem pp : VMSwapRemoveOutcome.ok imem r tlbi rc epoch pp →
  VMSwapRemoveOutcome.ok imem r tlbi rc epoch (setv PPState.iis IIS.init pp).
Proof.
  destruct pp as [ts mem iis]. intros [[Hbounds [[Hthread Hiis] [Hstamps Hstampiis]]] [Hpos [Hpage [l [Hmem Hcore]]]]].
  cbn in Hmem. subst mem. apply VMSwapRemoveDelivery.pp_init;
    [apply Hbounds|split; assumption|exact Hpos|exact Hpage|exact Hcore].
Qed.
Lemma minimum_rel a b : ts_rel r a b → TState.min_new_prom_view b = g (TState.min_new_prom_view a).
Proof.
  intros [Hshape Hcache]. rewrite Hshape. unfold TState.min_new_prom_view, join, join_nat. cbn.
  rewrite !unshift_max. reflexivity.
Qed.
Lemma pc_rel a b : ts_rel r a b → TState.pc b = TState.pc a.
Proof. intros [Hshape Hcache]. rewrite Hshape. change (TState.pc (ts_map g a) = TState.pc a). apply ts_map_pc. Qed.

Section Enumeration.
Context (bbm : bool) {n : nat} (isem : iMon ()) (term : terminationCondition n)
  (tid : fin n) (imem : memoryMap) (base : nat).
Hypothesis Hrc : fin_to_nat tid ≠ rc.
Hypothesis Hbase : p ≤ base.
Local Notation prom := (VMPromising bbm).
Local Notation ok := (VMSwapRemoveOutcome.ok imem r tlbi rc epoch).

Lemma cinterp_ok {A} (mon : iMon A) a a' value : ok a.2 →
  Exec.elem_of_results (a', value) (cinterp (CPState.run_outcome_with_promise prom tid imem base) mon a) → ok a'.2.
Proof using Hrc.
  revert a a' value. induction mon as [ret|call k IH]; intros a a' value Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hok.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      eapply IH; [eapply outcome_ok; eassumption|exact Htail].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [ret [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

Theorem run_to_termination_sim fuel a b : lp_rel a b → ok a.2 →
  VMSwapInsert.esim_at lp_rel eq (CPState.run_to_termination isem prom term tid imem fuel base)
    (CPState.run_to_termination isem prom term tid imem fuel (g base)) a b.
Proof using Hrc Hbase.
  revert a b. induction fuel as [|fuel IH]; intros a b Hrel Hok; cbn [CPState.run_to_termination].
  all: apply VMSwapInsert.esim_at_mget; [exact Hrel|].
  all: cbn [compose].
  all: pose proof (proj1 (proj2 (proj2 Hrel))) as Hts.
  all: change (Promising.tState_min_new_prom_view prom) with TState.min_new_prom_view.
  all: rewrite (minimum_rel _ _ Hts).
  all: match goal with |- VMSwapInsert.esim_at _ _ (if ?d then _ else _) _ _ _ =>
    destruct d as [Hearly|Hearly] end.
  all: match goal with |- VMSwapInsert.esim_at _ _ _ (if ?d then _ else _) _ _ =>
    destruct d as [Hearly'|Hearly'] end.
  all: pose proof (stopping_base base (TState.min_new_prom_view (PPState.state a.2)) Hbase) as Hstop.
  all: try solve [exfalso; tauto].
  all: try solve [apply VMSwapInsert.esim_at_of; [apply esim_ret; reflexivity|exact Hrel]].
  all: unfold CPState.terminated_ts; change (Promising.tState_pc prom) with TState.pc; rewrite (pc_rel _ _ Hts).
  all: destruct (pc_terminated _ _).
  all: try solve [apply VMSwapInsert.esim_at_of; [apply esim_ret; reflexivity|exact Hrel]].
  eapply (VMSwapInsert.esim_at_bind _ eq).
  - apply VMSwapInsert.esim_at_of; [apply esim_msetv; intros; apply reset_rel; assumption|exact Hrel].
  - intros a' b' u u' Ha Hb Hr <-. destruct u.
    apply Exec.elem_of_mset_inv in Ha as ->.
    eapply (VMSwapInsert.esim_at_bind _ eq).
    + eapply cinterp_sim; [exact Hrc|exact Hbase|exact Hr|apply reset_ok, Hok].
    + intros a'' b'' x y Hrun Hrun' Hr' <-. apply IH; [exact Hr'|].
      eapply cinterp_ok; [|exact Hrun]. apply reset_ok, Hok.
Qed.
End Enumeration.

Section Candidates.
Context (bbm : bool) {n : nat} (isem : iMon ()) (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).

Theorem enum_raw_promises_sim (tid : fin n) imem fuel ts1 ts2 mem1 mem2 ev :
  fin_to_nat tid ≠ rc →
  R (PPState.Make ts1 mem1 IIS.init) (PPState.Make ts2 mem2 IIS.init) →
  VMSwapRemoveOutcome.ok imem r tlbi rc epoch (PPState.Make ts1 mem1 IIS.init) →
  ev ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid imem fuel ts1 mem1) →
  ev ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid imem fuel ts2 mem2).
Proof.
  intros Hrc Hrel Hok.
  assert (Hbase : p ≤ length mem1).
  { destruct Hrel as [[l [Ha Hb]] _]. cbn in Ha. rewrite Ha, length_app. cbn; lia. }
  pose proof (VMSwapRemoveOutcome.mem_length r tlbi rc epoch _ _ Hrel) as Hlen.
  cbn in Hlen.
  assert (Hinit : lp_rel ([], PPState.Make ts1 mem1 IIS.init) ([], PPState.Make ts2 mem2 IIS.init))
    by (split; [reflexivity|exact Hrel]).
  destruct (run_to_termination_sim bbm isem term tid imem (length mem1) Hrc Hbase fuel _ _ Hinit Hok)
    as [Hr He].
  unfold CPState.enumerate_results. cbn [CPState.promises]. rewrite <- Hlen.
  intro H. apply (proj2 (elem_of_remove_dups _ _)). apply (proj1 (elem_of_remove_dups _ _)) in H.
  apply (proj1 (concat_elem _ _)) in H as (l & Hl & Hx). apply (proj2 (concat_elem _ _)).
  exists l. split; [|exact Hx].
  apply elem_of_app in Hl as [Hl|Hl]; apply elem_of_app.
  - left. unfold Exec.success_state_list in *.
    apply list_elem_of_fmap in Hl as [[l' st] [-> Hl]].
    apply list_elem_of_fmap in Hl as [[[l'' st'] ret] [Heq Hl]]. injection Heq as -> ->.
    destruct (Hr (l'', st') ret Hl) as ((l2 & st2) & ret2 & Hin2 & [Hl2 _] & <-).
    cbn in Hl2. subst l2.
    apply list_elem_of_fmap. exists (l'', st2). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((l'', st2), ret). split; [reflexivity|exact Hin2].
  - right. apply list_elem_of_fmap in Hl as [[l' st] [-> Hl]].
    apply list_elem_of_fmap in Hl as [[[l'' st'] err] [Heq Hl]]. injection Heq as -> ->.
    destruct (He (l'', st') err Hl) as ((l2 & st2) & err2 & Hin2 & [Hl2 _]).
    cbn in Hl2. subst l2.
    apply list_elem_of_fmap. exists (l'', st2). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((l'', st2), err2). split; [reflexivity|exact Hin2].
Qed.
End Candidates.

Theorem raw_candidate_sim bbm nondet {n} (term : terminationCondition n) (tid : fin n)
    (s1 s2 : PState.t TState.t Ev.t n) l fuel ev :
  fin_to_nat tid ≠ rc → PState.initmem s1 = PState.initmem s2 →
  PState.events s1 = l ++ e :: r → PState.events s2 = l ++ r →
  ts_rel r (PState.tstate tid s1) (PState.tstate tid s2) →
  VMSwapRemoveTrace.ok tid r tlbi rc epoch s1 →
  VMNormalization.RawCandidate bbm nondet term s1 tid fuel ev →
  VMNormalization.RawCandidate bbm nondet term s2 tid fuel ev.
Proof.
  intros Hrc Him Hm1 Hm2 Hts Hok. unfold VMNormalization.RawCandidate. rewrite <- Him.
  eapply enum_raw_promises_sim; [exact Hrc| |eapply VMSwapRemoveTrace.pp_ok; exact Hok].
  split; [exists l; split; assumption|]. split; [exact Hts|].
  symmetry. apply VMSwapRemoveDelivery.iis_init.
Qed.
End Removed.
End VMSwapRemoveCertification.
