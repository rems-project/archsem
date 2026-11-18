(******************************************************************************)
(* Replaying translations up to walk addresses                                *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From SailTinyArm Require Import System.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstMemoryCurrent PromiseFirstSailCurrent PromiseFirstVMExecutionCurrent
  PromiseFirstSailRead PromiseFirstSailVMViews PromiseFirstSailVMCacheSim
  PromiseFirstSailVMDirect PromiseFirstSailVMNormalization PromiseFirstSailNoFuel
  PromiseFirstSailVMInstructionReplay PromiseFirstSailVMEventValidity.
From ArchSemArm.Proof Require Import PromiseFirstSailVMWalkSail.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** [TLB.Result.merge] may replace the walk of a translation by another walk
    with the same leaf descriptor and the same non-address bits in each table
    descriptor. This file relates instruction states whose current
    translations differ in this way ([VMWalkReplay.SR]) and composes the
    per-outcome replay of [VMInstructionReplay] with the walk insensitivity of
    the Sail instruction ([VMWalkSail.TSafe]). The remaining obligation is the
    translation start ([VMWalkReplay.StepStartW]): the replay selects a
    translation related to the original one by [SR]. *)

Module VMWalkReplay.
Import VMPromising VMCacheSim VMCacheSimOutcome VMInstructionReplay VMWalkSail.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Local Notation ppstate := (PPState.t TState.t Ev.t IIS.t).

(** * Related translations *)

Fixpoint prel (lvl : nat) (l1 l2 : list (bv 64)) : Prop :=
  match l1, l2 with
  | [], [] => True
  | x1 :: l1, x2 :: l2 => rel_at lvl x1 x2 ∧ prel (S lvl) l1 l2
  | _, _ => False
  end.

Definition root_rel (rr : reg) (o1 o2 : option {r : reg & reg_type r}) : Prop :=
  (o1 = None ∧ o2 = None) ∨
  (∃ x1 x2, o1 = Some (existT rr x1) ∧ o2 = Some (existT rr x2)).

Definition trel (rr : reg) (lvl : nat) (t1 t2 : IIS.TransRes.t) : Prop :=
  IIS.TransRes.trans_start t1 = IIS.TransRes.trans_start t2 ∧
  IIS.TransRes.trans_end t1 = IIS.TransRes.trans_end t2 ∧
  root_rel rr (IIS.TransRes.root t1) (IIS.TransRes.root t2) ∧
  prel lvl (IIS.TransRes.remaining t1) (IIS.TransRes.remaining t2).

(** [q] is [v] with the current translation replaced by a related one, [lvl]
    descriptors of the walk having been read. *)
Definition SR (rr : reg) (lvl : nat) (v q : ppstate) : Prop :=
  ∃ t1 t2, IIS.trs (PPState.iis v) = Some t1 ∧ trel rr lvl t1 t2 ∧
    q = PPState.Make (PPState.state v) (PPState.mem v)
      (setv IIS.trs (Some t2) (PPState.iis v)).

(** * Steps of related states *)

Section SRSteps.
Context {n : nat} (tid : fin n) (imem : memoryMap).

Ltac fwd := repeat first [
    apply Exec.elem_of_mret
  | apply exec_guard_or_bind_intro; [assumption|]
  | apply Exec.elem_of_mget | apply Exec.elem_of_mGet | apply Exec.elem_of_mset
  | apply Exec.elem_of_liftSt
  | progress (cbn [fst snd compose othrow projT1 projT2])
  | eapply Exec.elem_of_bind_intro ].

Lemma trans_read_char reg racc t ts st' x view :
  Exec.elem_of_results (st', (x, view)) (run_reg_trans_read reg racc t ts) ↔
  st' = ts ∧ racc = None ∧ ∃ r, IIS.TransRes.root t = Some r ∧
    ((∃ e : projT1 r = reg, x = ctrans e (projT2 r) ∧ view = 0) ∨
     (projT1 r ≠ reg ∧ reg ∈ strict_regs ∧ TState.read_reg ts reg = Some (x, view))).
Proof.
  split.
  - unfold run_reg_trans_read. intro H.
    destruct racc as [id|].
    { apply Exec.elem_of_bind_elim in H as [? [Hp _]].
      exfalso. apply Hp. eexists. reflexivity. }
    VMViews.invert.
    all: split; [reflexivity|].
    all: split; [reflexivity|].
    all: eexists; split; [reflexivity|].
    + subst. left. exists eq_refl. split; reflexivity.
    + right. subst. split; [assumption|]. split; assumption.
  - intros (-> & -> & r & Hr & [(e & -> & ->)|(Hne & Hs & Hreg)]);
      unfold run_reg_trans_read.
    all: apply exec_guard_or_bind_intro; [intros []; discriminate|].
    all: rewrite Hr; cbn [othrow].
    all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]; cbv beta.
    + destruct (decide (projT1 r = reg)) as [e'|]; [|contradiction].
      assert (e' = e) as -> by apply proof_irrel. apply Exec.elem_of_mret.
    + destruct (decide (projT1 r = reg)); [contradiction|].
      fwd. rewrite Hreg. apply Exec.elem_of_mret.
Qed.

Lemma reg_read_char reg racc ts iis t st' x :
  IIS.trs iis = Some t →
  Exec.elem_of_results (st', x) (run_reg_read reg racc (ts, iis)) ↔
  ∃ view, st' = (ts, IIS.add view iis) ∧
    Exec.elem_of_results (ts, (x, view)) (run_reg_trans_read reg racc t ts).
Proof.
  intro Ht. split.
  - unfold run_reg_read. intro H.
    apply Exec.elem_of_bind_elim in H as [s1 [[x' view] [HB Hrest]]].
    apply Exec.elem_of_bind_elim in Hrest as [s2 [[] [Hset Hret]]].
    apply Exec.elem_of_mset_inv in Hset as ->.
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    apply Exec.elem_of_bind_elim in HB as [s0 [iis0 [Hget HB]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [snd] in HB. rewrite Ht in HB.
    apply Exec.elem_of_liftSt_inv in HB as [t' [-> HB]].
    pose proof HB as HB'. apply trans_read_char in HB' as [-> _].
    exists view. split; [reflexivity|exact HB].
  - intros (view & -> & HB). unfold run_reg_read.
    eapply Exec.elem_of_bind_intro with (a := (x, view)).
    + eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]. cbn [snd]. rewrite Ht.
      exact (Exec.elem_of_liftSt (ts, iis) ts _ fst _ HB).
    + cbv beta iota. eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
      apply Exec.elem_of_mret.
Qed.

Lemma sr_reg_read rr lvl reg racc v q v' x pre :
  SR rr lvl v q →
  Exec.elem_of_results (v', (x, pre)) (run_outcome n tid imem (RegRead reg racc) v) →
  ∃ q' x', Exec.elem_of_results (q', (x', pre)) (run_outcome n tid imem (RegRead reg racc) q) ∧
    SR rr lvl v' q' ∧ (reg ≠ rr → x = x').
Proof.
  intros (t1 & t2 & Ht1 & (Hs & He & Hroot & Hp) & ->) Hrun.
  destruct v as [ts m iis]. cbn [PPState.iis PPState.state PPState.mem] in *.
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [val [Hlift Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> Hx]. injection Hx as -> ->.
  apply Exec.elem_of_liftSt_inv in Hlift as [[ts' iis'] [-> Hrr]].
  apply (reg_read_char _ _ _ _ _ _ _ Ht1) in Hrr as (view & Hst & Htr). injection Hst as -> ->.
  pose proof Htr as Htr'. apply trans_read_char in Htr' as (_ & -> & r & Hr & Hcase).
  destruct Hroot as [[Hr1 Hr2]|(x1 & x2 & Hr1 & Hr2)]; [congruence|].
  rewrite Hr1 in Hr. injection Hr as <-. cbn [projT1 projT2] in Hcase.
  cbn [PPState.state PPState.iis] in Htr, Hcase.
  set (r2 := existT rr x2 : {r : Arch.reg & reg_type r}).
  assert (Hq : ∃ x', Exec.elem_of_results (ts, (x', view)) (run_reg_trans_read reg None t2 ts) ∧
      (reg ≠ rr → val = x')).
  { destruct Hcase as [(e & -> & ->)|(Hne & Hst & Hreg)].
    - exists (ctrans e x2). split; [|intros Hne; exfalso; exact (Hne (eq_sym e))].
      apply trans_read_char. split; [reflexivity|]. split; [reflexivity|].
      exists r2. split; [exact Hr2|]. left. exists e. split; reflexivity.
    - exists val. split; [|reflexivity].
      apply trans_read_char. split; [reflexivity|]. split; [reflexivity|].
      exists r2. split; [exact Hr2|]. right. auto. }
  destruct Hq as (x' & Hq & Hxx).
  exists (PPState.Make ts m (setv IIS.trs (Some t2) (IIS.add view iis))), x'.
  split; [|split; [|exact Hxx]].
  - assert (HR : Exec.elem_of_results ((ts, IIS.add view (setv IIS.trs (Some t2) iis)), x')
        (run_reg_read reg None (ts, setv IIS.trs (Some t2) iis))).
    { apply (reg_read_char _ _ _ _ t2). { reflexivity. }
      exists view. split; [reflexivity|exact Hq]. }
    pose proof (Exec.elem_of_liftSt (PPState.Make ts m (setv IIS.trs (Some t2) iis)) _ x'
      (PPState.state ×× PPState.iis) _ HR) as HL.
    eapply Exec.elem_of_bind_intro; [exact HL|]. apply Exec.elem_of_mret.
  - exists t1, t2. split; [exact Ht1|]. split; [repeat split; auto; right; eauto|].
    reflexivity.
Qed.

Lemma sr_read_pte rr lvl v q v' h :
  SR rr lvl v q → Exec.elem_of_results (v', h) (read_pte v) →
  ∃ q' h', Exec.elem_of_results (q', h') (read_pte q) ∧ SR rr (S lvl) v' q' ∧ rel_at lvl h h'.
Proof.
  intros (t1 & t2 & Ht1 & (Hs & He & Hroot & Hp) & ->) Hrun.
  destruct v as [ts m iis]. cbn [PPState.iis PPState.state PPState.mem] in *.
  unfold read_pte in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [s1 [o [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn in Hrun. rewrite Ht1 in Hrun.
  cbn [othrow] in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [s2 [t [Hret Hrun]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [s3 [[nt h0] [Hpop Hrun]]].
  apply exec_lift_result_inv in Hpop as [-> Hpop].
  apply Exec.elem_of_bind_elim in Hrun as [s4 [[] [Hset Hret]]].
  unfold msetv in Hset. apply Exec.elem_of_mset_inv in Hset as ->.
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  unfold IIS.TransRes.pop in Hpop.
  destruct (IIS.TransRes.remaining t1) as [|h1 tl1] eqn:Hr1; [discriminate|].
  injection Hpop as <- <-.
  destruct (IIS.TransRes.remaining t2) as [|h2 tl2] eqn:Hr2; cbn in Hp; [contradiction|].
  destruct Hp as [Hh Htl].
  exists (PPState.Make ts m (setv IIS.trs (Some (setv IIS.TransRes.remaining tl2 t2)) iis)), h2.
  split; [|split; [|exact Hh]].
  - unfold read_pte.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]. cbn. cbn [othrow].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
    eapply Exec.elem_of_bind_intro with (a := (setv IIS.TransRes.remaining tl2 t2, h2)).
    + apply exec_lift_result. unfold IIS.TransRes.pop. rewrite Hr2. reflexivity.
    + cbv beta iota. eapply Exec.elem_of_bind_intro; [unfold msetv; apply Exec.elem_of_mset|].
      apply Exec.elem_of_mret.
  - exists (setv IIS.TransRes.remaining tl1 t1), (setv IIS.TransRes.remaining tl2 t2).
    split; [reflexivity|]. split; [repeat split; cbn; assumption|]. reflexivity.
Qed.

Lemma sr_mem_read rr lvl mr mr2 v q v' r1 pre :
  MemReq.access_kind mr2 = MemReq.access_kind mr →
  MemReq.address_space mr2 = MemReq.address_space mr →
  MemReq.size mr2 = MemReq.size mr → MemReq.num_tag mr2 = MemReq.num_tag mr →
  is_ifetch (MemReq.access_kind mr) = false → is_explicit (MemReq.access_kind mr) = false →
  SR rr lvl v q →
  Exec.elem_of_results (v', (r1, pre)) (run_outcome n tid imem (MemRead mr) v) →
  ∃ q' r2, Exec.elem_of_results (q', (r2, pre))
      (run_outcome n tid imem (MemRead mr2) q) ∧
    SR rr (S lvl) v' q' ∧ mres_rel lvl r1 r2.
Proof.
  intros Hk Hsp Hsz Hnt Hif Hexp Hsr Hrun.
  destruct mr as [macc addr pas size [|tags]], mr2 as [macc2 addr2 pas2 size2 nt2];
    cbn in Hk, Hsp, Hsz, Hnt, Hif, Hexp; subst macc2 pas2 size2 nt2;
    simp run_outcome in Hrun |- *; [|exfalso; VMViews.invert].
  apply Exec.elem_of_bind_elim in Hrun as [s1 [Hpas [Hg Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hg as ->.
  rewrite Hif, Hexp in Hrun. destruct (is_ttw macc) eqn:Httw; [|exfalso; VMViews.invert].
  apply Exec.elem_of_bind_elim in Hrun as [s2 [Hs8 [Hg Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hg as ->.
  apply Exec.elem_of_bind_elim in Hrun as [s3 [h [Hpte Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> Hr]. injection Hr as -> ->.
  destruct (sr_read_pte _ _ _ _ _ _ Hsr Hpte) as (q' & h' & Hq & Hsr' & Hh).
  eexists q', _. split; [|split; [exact Hsr'|]].
  - apply exec_guard_or_bind_intro; [exact Hpas|]. rewrite ?Hif, ?Hexp, ?Httw.
    destruct (Exec.elem_of_guard_or (E:=string) q "TTW read of size other than 8" Hs8)
      as [Hs8' Hguard].
    eapply Exec.elem_of_bind_intro; [exact Hguard|].
    eapply Exec.elem_of_bind_intro; [exact Hq|].
    replace Hs8' with Hs8 by apply proof_irrel. apply Exec.elem_of_mret.
  - eexists h, h', _, _, _, _. split; [reflexivity|]. split; [reflexivity|].
    rewrite !bv_unsigned_ctrans. auto.
Qed.

Lemma trans_end_trs te ts iis t1 t2 :
  IIS.TransRes.trans_start t1 = IIS.TransRes.trans_start t2 →
  IIS.TransRes.trans_end t1 = IIS.TransRes.trans_end t2 →
  run_trans_end te (ts, setv IIS.trs (Some t2) iis) =
  run_trans_end te (ts, setv IIS.trs (Some t1) iis).
Proof.
  destruct t1 as [s1 e1 r1 l1], t2 as [s2 e2 r2 l2]. cbn. intros -> ->.
  destruct iis. reflexivity.
Qed.

Lemma sr_trans_end rr lvl te v q v' r :
  SR rr lvl v q →
  Exec.elem_of_results (v', r) (run_outcome n tid imem (TranslationEnd te) v) →
  Exec.elem_of_results (v', r) (run_outcome n tid imem (TranslationEnd te) q).
Proof.
  intros (t1 & t2 & Ht1 & (Hs & He & _ & _) & ->) Hrun.
  destruct v as [ts m iis]. cbn [PPState.iis PPState.state PPState.mem] in *.
  simp run_outcome in Hrun |- *.
  assert (Hiis : iis = setv IIS.trs (Some t1) iis).
  { destruct iis; cbn in Ht1 |- *. subst. reflexivity. }
  apply Exec.elem_of_bind_elim in Hrun as [mid [x [Hlift Hrest]]].
  apply Exec.elem_of_liftSt_inv in Hlift as [st' [-> Hin]]. cbn in Hin.
  assert (Heq : setv (PPState.state ×× PPState.iis) st'
      (PPState.Make ts m (setv IIS.trs (Some t2) iis)) =
    setv (PPState.state ×× PPState.iis) st' (PPState.Make ts m iis)) by reflexivity.
  eapply Exec.elem_of_bind_intro with (st' := setv (PPState.state ×× PPState.iis) st'
    (PPState.Make ts m (setv IIS.trs (Some t2) iis))) (a := x).
  - apply (Exec.elem_of_liftSt (PPState.Make ts m (setv IIS.trs (Some t2) iis)) st' x
      (PPState.state ×× PPState.iis) (run_trans_end te)).
    cbn. rewrite (trans_end_trs te ts iis t1 t2 Hs He), <- Hiis. exact Hin.
  - rewrite Heq. exact Hrest.
Qed.

End SRSteps.

Lemma sim_sr_commute rr lvl a b c :
  pp_sim a b → SR rr lvl b c → ∃ b', SR rr lvl a b' ∧ pp_sim b' c.
Proof.
  intros (Hm & Hi & Hs) (t1 & t2 & Ht1 & Ht & ->).
  exists (PPState.Make (PPState.state a) (PPState.mem a) (setv IIS.trs (Some t2) (PPState.iis a))).
  split.
  - exists t1, t2. rewrite Hi. auto.
  - split; [exact Hm|]. split; [cbn; rewrite Hi; reflexivity|exact Hs].
Qed.

(** * Composition with the per-outcome replay *)

Section Compose.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Local Notation Exact := (Exact tid imem mem ev).
Local Notation Rel := (Rel tid imem mem ev).

(** Original state [p], replay state [q]: an exact image of [p] whose current
    translation is replaced by a related one, up to cache simulation. *)
Definition RelW rr lvl (p q : ppstate) :=
  ∃ q0 q1, Exact p q0 ∧ SR rr lvl q0 q1 ∧ pp_sim q1 q.

(** An invariant of the original states kept by every outcome; the
    translation start may assume it. *)
Context (Sh : ppstate → Prop).

Definition ShStep : Prop :=
  ∀ out p p' r, VMViews.ok p → Sh p →
    Exec.elem_of_results (p', r) (run_outcome n tid imem out p) → Sh p'.

(** The translation-start obligation: the replay selects a translation
    related to the original one. *)
Definition StepStartW : Prop :=
  ∀ s p p' r q0, VMViews.ok p → VMRoots.pok p → Sh p → Exact p q0 →
    PPState.mem p' = mem → emits tid imem mem ev (PPState.state p') →
    Exec.elem_of_results (p', r) (run_outcome n tid imem (TranslationStart s) p) →
    ∃ q0' v rr, Exec.elem_of_results (q0', r) (run_outcome n tid imem (TranslationStart s) q0) ∧
      is_ttbr rr ∧ Exact p' v ∧ SR rr 0 v q0'.

Context (Hstep : ∀ out, not_start out → StepReplayR tid imem mem ev out).
Context (Hsh : ShStep).
Context (Hstart : StepStartW).

Lemma rel_after_step out p p' r q :
  not_start out → VMViews.ok p → VMRoots.pok p → Rel p q → fetch_ok imem ev out p →
  PPState.mem p' = mem → emits tid imem mem ev (PPState.state p') →
  Exec.elem_of_results (p', r) (run_outcome n tid imem out p) →
  ∃ q', Exec.elem_of_results (q', r) (run_outcome n tid imem out q) ∧ Rel p' q'.
Proof using Hstep.
  intros Hns Hok Hroots [q0 [Hex Hsim]] Hf Hm He Hrun.
  destruct (Hstep out Hns p p' r q0 Hok Hroots Hex Hf Hm He Hrun) as [q0' [Hrun0 [q1 [Hex1 Hsim1]]]].
  destruct (run_outcome_simulation n tid imem out q0 q q0' r Hsim Hrun0) as [q' [Hrun' Hsim']].
  exists q'. split; [exact Hrun'|]. exists q1. split; [exact Hex1|].
  eapply pp_sim_trans; eassumption.
Qed.

Lemma mid_mem {A} (out : outcome) (k : eff_ret out → iMon A) p mid r pre pf ret :
  PPState.mem p = mem →
  Exec.elem_of_results (mid, (r, pre)) (run_outcome n tid imem out p) →
  Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) (k r) mid) →
  PPState.mem pf = mem → PPState.mem mid = mem.
Proof.
  intros Hm Hout Htail Hmf.
  destruct (VMViews.outcome_memory_growth n tid imem out p mid _ Hout) as [x1 Hx1].
  destruct (VMFinalCertification.instruction_memory_suffix tid imem (k r) mid pf ret Htail)
    as [x2 Hx2].
  rewrite Hmf, Hx1, Hm, app_assoc in Hx2. apply (f_equal length) in Hx2.
  rewrite length_app in Hx2. destruct (x2 ++ x1)%list eqn:Hx; [|cbn in Hx2; lia].
  apply app_eq_nil in Hx as [_ ->]. rewrite Hx1, Hm. reflexivity.
Qed.

Lemma cinterp_next_inv {A} (out : outcome) (k : eff_ret out → iMon A) p pf ret :
  Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) (Next (inl out) k) p) →
  ∃ mid r pre, Exec.elem_of_results (mid, (r, pre)) (run_outcome n tid imem out p) ∧
    Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) (k r) mid).
Proof.
  intro Hrun. cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
  apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
  eauto.
Qed.

Lemma cinterp_next_intro {A} (out : outcome) (k : eff_ret out → iMon A) q q' r pre qf ret :
  Exec.elem_of_results (q', (r, pre)) (run_outcome n tid imem out q) →
  Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) (k r) q') →
  Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) (Next (inl out) k) q).
Proof.
  intros Hq Hqf. cbn. eapply Exec.elem_of_bind_intro; [|exact Hqf].
  apply (Exec.elem_of_fmap_intro _ _ (r, pre) _ fst Hq).
Qed.

Lemma cinterp_choice_inv {A} (c : MChoice) (k : eff_ret c → iMon A) p pf ret :
  Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) (Next (inr c) k) p) →
  ∃ r, Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) (k r) p).
Proof.
  destruct c as [choices]. intro Hrun. cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [i [Hchoose Htail]]].
  apply Exec.elem_of_mchoose_inv in Hchoose as ->. eauto.
Qed.

Lemma cinterp_choice_intro {A} (c : MChoice) (k : eff_ret c → iMon A) q qf ret r :
  Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) (k r) q) →
  Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) (Next (inr c) k) q).
Proof.
  destruct c as [choices]. intro Hqf. cbn.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|exact Hqf].
Qed.


Theorem walk_replay {A} :
  (∀ (mon : iMon A), TSafe mon → ∀ p pf ret q,
    fetches tid imem ev mon p → VMViews.ok p → VMRoots.pok p → Sh p → PPState.mem p = mem →
    Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) mon p) →
    PPState.mem pf = mem → emits tid imem mem ev (PPState.state pf) → Rel p q →
    ∃ qf, Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) mon q) ∧ Rel pf qf) ∧
  (∀ rr lvl (t1 t2 : iMon A), WSafe rr lvl t1 t2 → ∀ p pf ret q,
    fetches tid imem ev t1 p → VMViews.ok p → VMRoots.pok p → Sh p → PPState.mem p = mem →
    Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) t1 p) →
    PPState.mem pf = mem → emits tid imem mem ev (PPState.state pf) → RelW rr lvl p q →
    ∃ qf, Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) t2 q) ∧ Rel pf qf).
Proof using Hstep Hsh Hstart.
  apply (TW_mut A (λ mon _, ∀ p pf ret q, _) (λ rr lvl t1 t2 _, ∀ p pf ret q, _)).
  - (* TSRet *)
    intros a p pf ret q _ _ _ _ _ Hrun _ _ Hrel. cbn in Hrun |- *.
    apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    exists q. split; [apply Exec.elem_of_mret|exact Hrel].
  - (* TSNext *)
    intros out k Hns _ IH p pf ret q Hf Hok Hroots HSh Hm Hrun Hmf He Hrel.
    apply cinterp_next_inv in Hrun as (mid & r & pre & Hout & Htail).
    destruct Hf as [Hfo Hfk].
    pose proof (VMViews.run_outcome_ok n tid imem out p mid _ Hok Hout) as Hok'.
    pose proof (mid_mem out k p mid r pre pf ret Hm Hout Htail Hmf) as Hmid.
    pose proof (cinterp_emits tid imem mem ev (k r) mid pf ret Hok' Htail He) as He'.
    pose proof (VMRoots.run_outcome_roots n tid imem out p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh out p mid _ Hok HSh Hout) as HSh'.
    destruct (rel_after_step out p mid (r, pre) q Hns Hok Hroots Hrel Hfo Hmid He' Hout)
      as [q' [Hq' Hrel']].
    destruct (IH r mid pf ret q' (Hfk mid r pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf He Hrel')
      as [qf [Hqf Hrelf]].
    exists qf. split; [|exact Hrelf]. eapply cinterp_next_intro; eassumption.
  - (* TSChoice *)
    intros c k _ IH p pf ret q Hf Hok Hroots HSh Hm Hrun Hmf He Hrel.
    apply cinterp_choice_inv in Hrun as [r Htail].
    destruct (IH r p pf ret q (Hf r) Hok Hroots HSh Hm Htail Hmf He Hrel) as [qf [Hqf Hrelf]].
    exists qf. split; [|exact Hrelf]. eapply cinterp_choice_intro; exact Hqf.
  - (* TSStart *)
    intros s k _ IH p pf ret q Hf Hok Hroots HSh Hm Hrun Hmf He [q0 [Hex Hsim]].
    apply cinterp_next_inv in Hrun as (mid & r & pre & Hout & Htail). destruct r.
    destruct Hf as [_ Hfk].
    pose proof (VMViews.run_outcome_ok n tid imem _ p mid _ Hok Hout) as Hok'.
    pose proof (mid_mem (TranslationStart s) k p mid () pre pf ret Hm Hout Htail Hmf) as Hmid.
    pose proof (cinterp_emits tid imem mem ev (k ()) mid pf ret Hok' Htail He) as He'.
    pose proof (VMRoots.run_outcome_roots n tid imem _ p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh _ p mid _ Hok HSh Hout) as HSh'.
    destruct (Hstart s p mid _ q0 Hok Hroots HSh Hex Hmid He' Hout)
      as (q0' & v & rr & Hrun0 & Httbr & Hexv & Hsr).
    destruct (run_outcome_simulation n tid imem _ q0 q q0' _ Hsim Hrun0) as [q' [Hq' Hsim']].
    destruct (IH rr Httbr mid pf ret q' (Hfk mid () pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf He
      (ex_intro _ v (ex_intro _ q0' (conj Hexv (conj Hsr Hsim'))))) as [qf [Hqf Hrelf]].
    exists qf. split; [|exact Hrelf]. eapply cinterp_next_intro; eassumption.
  - (* WSRead *)
    intros rr lvl reg racc k1 k2 _ IH p pf ret q Hf Hok Hroots HSh Hm Hrun Hmf He
      (q0 & q1 & Hex & Hsr & Hsim).
    apply cinterp_next_inv in Hrun as (mid & x & pre & Hout & Htail).
    destruct Hf as [Hfo Hfk].
    pose proof (VMViews.run_outcome_ok n tid imem _ p mid _ Hok Hout) as Hok'.
    pose proof (mid_mem (RegRead reg racc) k1 p mid x pre pf ret Hm Hout Htail Hmf) as Hmid.
    pose proof (cinterp_emits tid imem mem ev (k1 x) mid pf ret Hok' Htail He) as He'.
    pose proof (VMRoots.run_outcome_roots n tid imem _ p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh _ p mid _ Hok HSh Hout) as HSh'.
    destruct (Hstep (RegRead reg racc) ltac:(intros ? [=]) p mid _ q0 Hok Hroots Hex Hfo Hmid He' Hout)
      as [q0' [Hrun0 [q00 [Hex' Hsim0]]]].
    destruct (sr_reg_read tid imem rr lvl reg racc q0 q1 q0' x pre Hsr Hrun0)
      as (q1' & x' & Hrun1 & Hsr' & Hxx).
    destruct (run_outcome_simulation n tid imem _ q1 q q1' _ Hsim Hrun1) as [q' [Hq' Hsim']].
    destruct (sim_sr_commute rr lvl q00 q0' q1' Hsim0 Hsr') as [b [Hsrb Hsimb]].
    destruct (IH x x' Hxx mid pf ret q' (Hfk mid x pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf He
      (ex_intro _ q00 (ex_intro _ b (conj Hex' (conj Hsrb (pp_sim_trans _ _ _ Hsimb Hsim'))))))
      as [qf [Hqf Hrelf]].
    exists qf. split; [|exact Hrelf]. eapply cinterp_next_intro; eassumption.
  - (* WSMem *)
    intros rr lvl mr mr2 k1 k2 Hk Hsp Hsz Hnt Hif Hexp _ IH p pf ret q Hf Hok Hroots HSh Hm Hrun
      Hmf He (q0 & q1 & Hex & Hsr & Hsim).
    apply cinterp_next_inv in Hrun as (mid & x & pre & Hout & Htail).
    destruct Hf as [Hfo Hfk].
    pose proof (VMViews.run_outcome_ok n tid imem _ p mid _ Hok Hout) as Hok'.
    pose proof (mid_mem (MemRead mr) k1 p mid x pre pf ret Hm Hout Htail Hmf) as Hmid.
    pose proof (cinterp_emits tid imem mem ev (k1 x) mid pf ret Hok' Htail He) as He'.
    pose proof (VMRoots.run_outcome_roots n tid imem _ p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh _ p mid _ Hok HSh Hout) as HSh'.
    destruct (Hstep (MemRead mr) ltac:(intros ? [=]) p mid _ q0 Hok Hroots Hex Hfo Hmid He' Hout)
      as [q0' [Hrun0 [q00 [Hex' Hsim0]]]].
    destruct (sr_mem_read tid imem rr lvl mr mr2 q0 q1 q0' x pre Hk Hsp Hsz Hnt Hif Hexp Hsr Hrun0)
      as (q1' & x' & Hrun1 & Hsr' & Hxx).
    destruct (run_outcome_simulation n tid imem _ q1 q q1' _ Hsim Hrun1) as [q' [Hq' Hsim']].
    destruct (sim_sr_commute rr (S lvl) q00 q0' q1' Hsim0 Hsr') as [b [Hsrb Hsimb]].
    destruct (IH x x' Hxx mid pf ret q' (Hfk mid x pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf He
      (ex_intro _ q00 (ex_intro _ b (conj Hex' (conj Hsrb (pp_sim_trans _ _ _ Hsimb Hsim'))))))
      as [qf [Hqf Hrelf]].
    exists qf. split; [|exact Hrelf]. eapply cinterp_next_intro; eassumption.
  - (* WSEnd *)
    intros rr lvl te k _ IH p pf ret q Hf Hok Hroots HSh Hm Hrun Hmf He
      (q0 & q1 & Hex & Hsr & Hsim).
    apply cinterp_next_inv in Hrun as (mid & x & pre & Hout & Htail).
    destruct Hf as [Hfo Hfk].
    pose proof (VMViews.run_outcome_ok n tid imem _ p mid _ Hok Hout) as Hok'.
    pose proof (mid_mem (TranslationEnd te) k p mid x pre pf ret Hm Hout Htail Hmf) as Hmid.
    pose proof (cinterp_emits tid imem mem ev (k x) mid pf ret Hok' Htail He) as He'.
    pose proof (VMRoots.run_outcome_roots n tid imem _ p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh _ p mid _ Hok HSh Hout) as HSh'.
    destruct (Hstep (TranslationEnd te) ltac:(intros ? [=]) p mid _ q0 Hok Hroots Hex Hfo Hmid He' Hout)
      as [q0' [Hrun0 [q00 [Hex' Hsim0]]]].
    pose proof (sr_trans_end tid imem rr lvl te q0 q1 q0' _ Hsr Hrun0) as Hrun1.
    destruct (run_outcome_simulation n tid imem _ q1 q q0' _ Hsim Hrun1) as [q' [Hq' Hsim']].
    destruct (IH x mid pf ret q' (Hfk mid x pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf He
      (ex_intro _ q00 (conj Hex' (pp_sim_trans _ _ _ Hsim0 Hsim')))) as [qf [Hqf Hrelf]].
    exists qf. split; [|exact Hrelf]. eapply cinterp_next_intro; eassumption.
  - (* WSFail *)
    intros rr lvl s k t p pf ret q _ _ _ _ _ Hrun.
    apply cinterp_next_inv in Hrun as (mid & x & pre & Hout & _).
    exfalso. simp run_outcome in Hout. VMViews.invert.
  - (* WSChoice *)
    intros rr lvl c k1 k2 _ IH p pf ret q Hf Hok Hroots HSh Hm Hrun Hmf He Hrel.
    apply cinterp_choice_inv in Hrun as [r Htail].
    destruct (IH r p pf ret q (Hf r) Hok Hroots HSh Hm Htail Hmf He Hrel) as [qf [Hqf Hrelf]].
    exists qf. split; [|exact Hrelf]. eapply cinterp_choice_intro; exact Hqf.
Qed.

End Compose.

(** * The per-outcome replays apart from the translation start *)

Section NotStart.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma step_cache_op c : StepReplay tid imem mem ev (CacheOp c).
Proof. intros p p' r q0 _ _ _ _ _ Hrun. exfalso. simp run_outcome in Hrun. VMViews.invert. Qed.

Lemma steps_not_start out : not_start out → StepReplayR tid imem mem ev out.
Proof.
  intro Hns. destruct out;
    first [apply StepReplay_R;
        first [apply step_trans_end|apply step_announce|apply step_fail|apply step_barrier
          |apply step_return|apply step_take|apply step_reg_read|apply step_mem_read
          |apply step_mem_write|apply step_tlbi|apply step_cache_op]
      |apply step_reg_write
      |exfalso; eapply Hns; reflexivity].
Qed.
End NotStart.

(** * The fixed-history clause from the translation-start obligation *)

Section Sail.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).

(** An invariant of the states of a thread running a Sail instruction, kept
    by every outcome and holding at every Sail thread prefix. *)
Context (Sh : fin n → memoryMap → ppstate → Prop).

Definition ShInvariant : Prop :=
  (∀ (tid : fin n) imem, ShStep tid imem (Sh tid imem)) ∧
  (∀ (tid : fin n) imem ts mem,
    SailThreadPrefix (VMPromising bbm) nondet term initMs tid imem
      (PPState.Make ts mem IIS.init) (sail_tiny_arm_sem nondet) →
    Sh tid imem (PPState.Make ts mem IIS.init)).

Context (HSh : ShInvariant).

Theorem fixed_history_replay_walk (tid : fin n) imem ts mem ts' iis' ev :
  StepStartW tid imem mem ev (Sh tid imem) →
  VMSailNoSelfModifying bbm nondet term initMs code →
  SailThreadPrefix (VMPromising bbm) nondet term initMs tid imem
    (PPState.Make ts mem IIS.init) (sail_tiny_arm_sem nondet) →
  VMViews.ts_ok (length mem) ts →
  event_misses_code VMPromisingReadByte code ev →
  Exec.elem_of_results (PPState.Make ts' mem iis', ())
    (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
      (PPState.Make ts mem IIS.init)) →
  ∀ ts'_e, TState.emit_promise tid imem (ev :: mem) ev ts' = Ok ts'_e →
  ∃ ts_e ppst,
    TState.emit_promise tid imem (ev :: mem) ev ts = Ok ts_e ∧
    Exec.elem_of_results (ppst, ())
      (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
        (PPState.Make ts_e (ev :: mem) IIS.init)) ∧
    PPState.mem ppst = ev :: mem ∧ ts_sim ts'_e (PPState.state ppst).
Proof using HSh.
  intros Hstart Hsafe Hprefix Hts Hmiss Hrun ts'_e He'.
  set (p := PPState.Make ts mem IIS.init).
  assert (Hok : VMViews.ok p).
  { split; [exact Hts|]. eapply VMViews.iis_ok_mono; [|apply VMViews.iis_init]. lia. }
  destruct (cinterp_emits tid imem mem ev _ p _ () Hok Hrun (ex_intro _ _ He')) as [ts_e He].
  set (q := PPState.Make ts_e (ev :: mem) IIS.init).
  assert (Hrel : Rel tid imem mem ev p q).
  { apply exact_rel; [exact Hok|]. split; [reflexivity|].
    exists ts_e, 0, None. split; [exact He|]. split; [cbn; discriminate|].
    split; [left; reflexivity|]. reflexivity. }
  destruct (VMRoots.prefix_roots bbm nondet term initMs tid imem _ _ Hprefix) as [_ Hroots].
  destruct (proj1 (walk_replay tid imem mem ev (Sh tid imem) (steps_not_start tid imem mem ev)
    (proj1 HSh tid imem) Hstart)
    _ (sail_tiny_arm_sem_tsafe nondet) p _ () q
    (prefix_fetches bbm nondet term initMs code tid imem mem ev _ p Hsafe Hmiss Hprefix)
    Hok Hroots (proj2 HSh tid imem ts mem Hprefix) eq_refl Hrun eq_refl (ex_intro _ _ He') Hrel)
    as [qf [Hqf [q1 [Hex Hsim]]]].
  exists ts_e, qf. split; [exact He|]. split; [exact Hqf|].
  destruct Hex as [_ [issued [stop [inv [He1 [_ [_ ->]]]]]]].
  cbn in He1. rewrite He' in He1. injection He1 as <-.
  destruct Hsim as (Hm & _ & Hs). split; [symmetry; exact Hm|exact Hs].
Qed.

(** The translation-start obligation for every replay. *)
Definition StartReplay : Prop :=
  ∀ (tid : fin n) imem mem ev, VMEventValidity.event_positive ev →
    StepStartW tid imem mem ev (Sh tid imem).

Theorem instruction_promise_replay_walk :
  StartReplay → CreatingReplay bbm nondet term initMs code →
  VMNormalization.VMInstructionPromiseReplay bbm nondet term initMs code.
Proof using HSh.
  intros Hstart Hcreate tid imem ts mem ts' mem' iis' ev Hsafe Hprefix Hts Hmiss Hrun.
  split; [eapply Hcreate; eassumption|].
  intros -> Hpositive. eapply fixed_history_replay_walk; [apply Hstart, Hpositive|eassumption..].
Qed.

Corollary final_state_equiv_walk :
  StartReplay → CreatingReplay bbm nondet term initMs code →
  VMNormalization.VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  (∀ initPs fuel returned fsig,
    PState.from_archState (VMPromising bbm) initMs = Ok initPs →
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) (VMPromising bbm) n)
        fuel term initMs initPs) →
    VMNormalization.VMNormalizationSearchesComplete bbm nondet term initMs (projT1 fsig)) →
  (∀ fuel fs (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf_uncached (VMPromising bbm) (sail_tiny_arm_sem nondet)
        fuel n term initMs →
    PromiseFirstSearchesCompleteFromInitial (VMPromising bbm) nondet term initMs fuel) →
  VMPromisingFinalStateEquiv bbm (sail_tiny_arm_sem nondet) term initMs.
Proof using HSh.
  intros Hstart Hcreate. apply VMNormalization.VMSail_promise_first_final_state_equiv.
  apply instruction_promise_replay_walk; assumption.
Qed.
End Sail.
End VMWalkReplay.
