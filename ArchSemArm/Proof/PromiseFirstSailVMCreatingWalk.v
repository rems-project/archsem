(******************************************************************************)
(* The creating replay with translations related up to walk addresses        *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstSailNoFuel PromiseFirstSailCurrent
  PromiseFirstVMExecutionCurrent PromiseFirstSailExecution PromiseFirstSailVMViews
  PromiseFirstSailVMCacheSim PromiseFirstSailVMNormalization PromiseFirstSailVMDirect
  PromiseFirstSailVMInstructionReplay PromiseFirstSailVMCreatingReplay
  PromiseFirstSailVMWalkSail PromiseFirstSailVMWalkReplay PromiseFirstSailVMEventValidity.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** [VMCreatingReplay.creating_cinterp] with the translation start replayed up
    to walk addresses: the replay of the outcomes before the update follows
    [VMWalkReplay.walk_replay], with [ExactOwn] in place of [Exact]. The
    remaining obligation is [StartOwnReplayW], the translation start after an
    event of the same thread. *)

Module VMCreatingWalk.
Import VMPromising VMCacheSim VMCacheSimOutcome VMInstructionReplay VMCreatingReplay
  VMWalkSail VMWalkReplay.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Local Notation ppstate := (PPState.t TState.t Ev.t IIS.t).

Section Main.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Local Notation ExactOwn := (ExactOwn tid imem mem ev).
Local Notation RelOwn := (RelOwn tid imem mem ev).

Definition RelOwnW rr lvl (p q : ppstate) :=
  ∃ q0 q1, ExactOwn p q0 ∧ SR rr lvl q0 q1 ∧ pp_sim q1 q.

Context (Sh : ppstate → Prop).

Definition StepStartOwnW : Prop :=
  ∀ s p p' r q0, VMViews.ok p → VMRoots.pok p → Sh p → ExactOwn p q0 →
    PPState.mem p' = mem → emits tid imem mem ev (PPState.state p') →
    Exec.elem_of_results (p', r) (run_outcome n tid imem (TranslationStart s) p) →
    ∃ q0' v rr, Exec.elem_of_results (q0', r) (run_outcome n tid imem (TranslationStart s) q0) ∧
      is_ttbr rr ∧ ExactOwn p' v ∧ SR rr 0 v q0'.

Context (Hsh : ShStep tid imem Sh).
Context (Hstart : StepStartOwnW).
Context (Hcre : ∀ out, CreatingOutcome tid imem mem ev out).

Lemma own_step out : not_start out → StepReplayOwn tid imem mem ev out.
Proof.
  intro Hns. apply step_own_of_R; [|apply steps_not_start, Hns].
  destruct out; cbn; try exact I. eapply Hns. reflexivity.
Qed.

Lemma no_update_contra {A} (out : outcome) (k : eff_ret out → iMon A) p mid r pre pf ret evs :
  IEffectNoUpdate (inl out) → (∀ r, IMonNoUpdate (k r)) → PPState.mem p = mem →
  Exec.elem_of_results (mid, (r, pre)) (run_outcome n tid imem out p) →
  Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) (k r) mid) →
  PPState.mem pf = (evs ++ ev :: mem)%list → False.
Proof.
  intros Ho Ht Hm Hout Htail Hmf.
  pose proof (VMSailMemory.outcome_no_update_mem n tid imem out p mid r pre Ho Hout) as Hmid.
  pose proof (vm_no_update_memory tid imem _ _ _ _ (Ht r) Htail) as Hpf.
  rewrite Hmf, Hmid, Hm in Hpf. exact (app_cons_len mem ev evs Hpf).
Qed.

Theorem creating_walk {A} :
  (∀ (mon : iMon A), TSafe mon → ∀ p pf ret q evs,
    IMonAtMostOneUpdate mon → fetches tid imem ev mon p → VMViews.ok p → VMRoots.pok p → Sh p →
    PPState.mem p = mem →
    Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) mon p) →
    PPState.mem pf = (evs ++ ev :: mem)%list → RelOwn p q →
    ∃ qf, Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) mon q) ∧ pp_sim pf qf) ∧
  (∀ rr lvl (t1 t2 : iMon A), WSafe rr lvl t1 t2 → ∀ p pf ret q evs,
    IMonAtMostOneUpdate t1 → fetches tid imem ev t1 p → VMViews.ok p → VMRoots.pok p → Sh p →
    PPState.mem p = mem →
    Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) t1 p) →
    PPState.mem pf = (evs ++ ev :: mem)%list → RelOwnW rr lvl p q →
    ∃ qf, Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) t2 q) ∧ pp_sim pf qf).
Proof using Hsh Hstart Hcre.
  apply (TW_mut A (λ mon _, ∀ p pf ret q evs, _) (λ rr lvl t1 t2 _, ∀ p pf ret q evs, _)).
  - (* TSRet *)
    intros a p pf ret q evs _ _ _ _ _ Hm Hrun Hmf _. cbn in Hrun.
    apply Exec.elem_of_mret_inv in Hrun as [-> _]. exfalso.
    rewrite Hm in Hmf. exact (app_cons_len mem ev evs (eq_sym Hmf)).
  - (* TSNext *)
    intros out k Hns _ IH p pf ret q evs Hshape Hf Hok Hroots HSh Hm Hrun Hmf Hrel.
    apply cinterp_next_inv in Hrun as (mid & r & pre & Hout & Htail).
    destruct Hf as [Hfo Hfk].
    pose proof (VMViews.run_outcome_ok n tid imem out p mid _ Hok Hout) as Hok'.
    pose proof (VMRoots.run_outcome_roots n tid imem out p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh out p mid _ Hok HSh Hout) as HSh'.
    destruct Hshape as [[Ho Ht]|Ht].
    + pose proof (VMSailMemory.outcome_no_update_mem n tid imem out p mid r pre Ho Hout) as Hmid.
      rewrite Hm in Hmid.
      pose proof (creating_emits tid imem mem ev Hcre (k r) mid pf ret evs (Ht r) Hok' Hmid Htail Hmf)
        as He'.
      destruct Hrel as [q0 [Hown Hsim]].
      destruct (own_step out Hns p mid (r, pre) q0 Hok Hroots Hown Hfo Hmid He' Hout)
        as [q0' [Hq0 [q1 [Hown1 Hsim1]]]].
      destruct (run_outcome_simulation n tid imem out q0 q q0' (r, pre) Hsim Hq0)
        as [q' [Hq' Hsim']].
      destruct (IH r mid pf ret q' evs (Ht r) (Hfk mid r pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf
        (ex_intro _ q1 (conj Hown1 (pp_sim_trans _ _ _ Hsim1 Hsim')))) as [qf [Hqf Hpf]].
      exists qf. split; [|exact Hpf]. eapply cinterp_next_intro; eassumption.
    + pose proof (vm_no_update_memory tid imem _ _ _ _ (Ht r) Htail) as Hmid.
      destruct (Hcre out p mid (r, pre) evs Hm Hout (eq_trans (eq_sym Hmid) Hmf))
        as [_ [issued [r' [He [Hc Hr']]]]].
      destruct Hrel as [q0 [[_ [issued0 [He0 ->]]] Hsim]].
      rewrite He in He0. injection He0 as <-.
      destruct (run_outcome_simulation n tid imem out _ q mid r' Hsim Hc) as [q' [Hq' Hsim']].
      destruct (instruction_sim n tid imem (k r) mid q' pf ret Hsim' Htail) as [qf [Hqf Hpf]].
      exists qf. split; [|exact Hpf].
      destruct r' as [r0 pre0]. cbn in Hr'. subst r0.
      eapply cinterp_next_intro; eassumption.
  - (* TSChoice *)
    intros c k _ IH p pf ret q evs Hshape Hf Hok Hroots HSh Hm Hrun Hmf Hrel.
    apply cinterp_choice_inv in Hrun as [r Htail].
    destruct Hshape as [[_ Ht]|Ht].
    + destruct (IH r p pf ret q evs (Ht r) (Hf r) Hok Hroots HSh Hm Htail Hmf Hrel) as [qf [Hqf Hpf]].
      exists qf. split; [|exact Hpf]. eapply cinterp_choice_intro; exact Hqf.
    + exfalso. pose proof (vm_no_update_memory tid imem _ _ _ _ (Ht r) Htail) as Hmid.
      rewrite Hmf, Hm in Hmid. exact (app_cons_len mem ev evs Hmid).
  - (* TSStart *)
    intros s k _ IH p pf ret q evs Hshape Hf Hok Hroots HSh Hm Hrun Hmf [q0 [Hown Hsim]].
    apply cinterp_next_inv in Hrun as (mid & r & pre & Hout & Htail). destruct r.
    destruct Hf as [_ Hfk].
    destruct Hshape as [[Ho Ht]|Ht];
      [|exfalso; exact (no_update_contra (TranslationStart s) k p mid () pre pf ret evs I Ht Hm Hout Htail Hmf)].
    pose proof (VMViews.run_outcome_ok n tid imem _ p mid _ Hok Hout) as Hok'.
    pose proof (VMRoots.run_outcome_roots n tid imem _ p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh _ p mid _ Hok HSh Hout) as HSh'.
    pose proof (VMSailMemory.outcome_no_update_mem n tid imem (TranslationStart s) p mid () pre Ho Hout) as Hmid.
    rewrite Hm in Hmid.
    pose proof (creating_emits tid imem mem ev Hcre (k ()) mid pf ret evs (Ht ()) Hok' Hmid Htail Hmf)
      as He'.
    destruct (Hstart s p mid _ q0 Hok Hroots HSh Hown Hmid He' Hout)
      as (q0' & v & rr & Hrun0 & Httbr & Hexv & Hsr).
    destruct (run_outcome_simulation n tid imem _ q0 q q0' _ Hsim Hrun0) as [q' [Hq' Hsim']].
    destruct (IH rr Httbr mid pf ret q' evs (Ht ()) (Hfk mid () pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf
      (ex_intro _ v (ex_intro _ q0' (conj Hexv (conj Hsr Hsim'))))) as [qf [Hqf Hpf]].
    exists qf. split; [|exact Hpf]. eapply cinterp_next_intro; eassumption.
  - (* WSRead *)
    intros rr lvl reg racc k1 k2 _ IH p pf ret q evs Hshape Hf Hok Hroots HSh Hm Hrun Hmf
      (q0 & q1 & Hown & Hsr & Hsim).
    apply cinterp_next_inv in Hrun as (mid & x & pre & Hout & Htail).
    destruct Hf as [Hfo Hfk].
    destruct Hshape as [[Ho Ht]|Ht];
      [|exfalso; exact (no_update_contra (RegRead reg racc) k1 p mid x pre pf ret evs I Ht Hm Hout Htail Hmf)].
    pose proof (VMViews.run_outcome_ok n tid imem _ p mid _ Hok Hout) as Hok'.
    pose proof (VMRoots.run_outcome_roots n tid imem _ p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh _ p mid _ Hok HSh Hout) as HSh'.
    pose proof (VMSailMemory.outcome_no_update_mem n tid imem (RegRead reg racc) p mid x pre Ho Hout) as Hmid.
    rewrite Hm in Hmid.
    pose proof (creating_emits tid imem mem ev Hcre (k1 x) mid pf ret evs (Ht x) Hok' Hmid Htail Hmf)
      as He'.
    destruct (own_step (RegRead reg racc) ltac:(intros ? [=]) p mid _ q0 Hok Hroots Hown Hfo Hmid He' Hout)
      as [q0' [Hrun0 [q00 [Hown' Hsim0]]]].
    destruct (sr_reg_read tid imem rr lvl reg racc q0 q1 q0' x pre Hsr Hrun0)
      as (q1' & x' & Hrun1 & Hsr' & Hxx).
    destruct (run_outcome_simulation n tid imem _ q1 q q1' _ Hsim Hrun1) as [q' [Hq' Hsim']].
    destruct (sim_sr_commute rr lvl q00 q0' q1' Hsim0 Hsr') as [b [Hsrb Hsimb]].
    destruct (IH x x' Hxx mid pf ret q' evs (Ht x) (Hfk mid x pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf
      (ex_intro _ q00 (ex_intro _ b (conj Hown' (conj Hsrb (pp_sim_trans _ _ _ Hsimb Hsim'))))))
      as [qf [Hqf Hpf]].
    exists qf. split; [|exact Hpf]. eapply cinterp_next_intro; eassumption.
  - (* WSMem *)
    intros rr lvl mr mr2 k1 k2 Hk Hsp Hsz Hnt Hif Hexp _ IH p pf ret q evs Hshape Hf Hok Hroots
      HSh Hm Hrun Hmf (q0 & q1 & Hown & Hsr & Hsim).
    apply cinterp_next_inv in Hrun as (mid & x & pre & Hout & Htail).
    destruct Hf as [Hfo Hfk].
    destruct Hshape as [[Ho Ht]|Ht];
      [|exfalso; exact (no_update_contra (MemRead mr) k1 p mid x pre pf ret evs I Ht Hm Hout Htail Hmf)].
    pose proof (VMViews.run_outcome_ok n tid imem _ p mid _ Hok Hout) as Hok'.
    pose proof (VMRoots.run_outcome_roots n tid imem _ p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh _ p mid _ Hok HSh Hout) as HSh'.
    pose proof (VMSailMemory.outcome_no_update_mem n tid imem (MemRead mr) p mid x pre Ho Hout) as Hmid.
    rewrite Hm in Hmid.
    pose proof (creating_emits tid imem mem ev Hcre (k1 x) mid pf ret evs (Ht x) Hok' Hmid Htail Hmf)
      as He'.
    destruct (own_step (MemRead mr) ltac:(intros ? [=]) p mid _ q0 Hok Hroots Hown Hfo Hmid He' Hout)
      as [q0' [Hrun0 [q00 [Hown' Hsim0]]]].
    destruct (sr_mem_read tid imem rr lvl mr mr2 q0 q1 q0' x pre Hk Hsp Hsz Hnt Hif Hexp Hsr Hrun0)
      as (q1' & x' & Hrun1 & Hsr' & Hxx).
    destruct (run_outcome_simulation n tid imem _ q1 q q1' _ Hsim Hrun1) as [q' [Hq' Hsim']].
    destruct (sim_sr_commute rr (S lvl) q00 q0' q1' Hsim0 Hsr') as [b [Hsrb Hsimb]].
    destruct (IH x x' Hxx mid pf ret q' evs (Ht x) (Hfk mid x pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf
      (ex_intro _ q00 (ex_intro _ b (conj Hown' (conj Hsrb (pp_sim_trans _ _ _ Hsimb Hsim'))))))
      as [qf [Hqf Hpf]].
    exists qf. split; [|exact Hpf]. eapply cinterp_next_intro; eassumption.
  - (* WSEnd *)
    intros rr lvl te k _ IH p pf ret q evs Hshape Hf Hok Hroots HSh Hm Hrun Hmf
      (q0 & q1 & Hown & Hsr & Hsim).
    apply cinterp_next_inv in Hrun as (mid & x & pre & Hout & Htail).
    destruct Hf as [Hfo Hfk].
    destruct Hshape as [[Ho Ht]|Ht];
      [|exfalso; exact (no_update_contra (TranslationEnd te) k p mid x pre pf ret evs I Ht Hm Hout Htail Hmf)].
    pose proof (VMViews.run_outcome_ok n tid imem _ p mid _ Hok Hout) as Hok'.
    pose proof (VMRoots.run_outcome_roots n tid imem _ p mid _ Hok Hroots Hout) as Hroots'.
    pose proof (Hsh _ p mid _ Hok HSh Hout) as HSh'.
    pose proof (VMSailMemory.outcome_no_update_mem n tid imem (TranslationEnd te) p mid x pre Ho Hout) as Hmid.
    rewrite Hm in Hmid.
    pose proof (creating_emits tid imem mem ev Hcre (k x) mid pf ret evs (Ht x) Hok' Hmid Htail Hmf)
      as He'.
    destruct (own_step (TranslationEnd te) ltac:(intros ? [=]) p mid _ q0 Hok Hroots Hown Hfo Hmid He' Hout)
      as [q0' [Hrun0 [q00 [Hown' Hsim0]]]].
    pose proof (sr_trans_end tid imem rr lvl te q0 q1 q0' _ Hsr Hrun0) as Hrun1.
    destruct (run_outcome_simulation n tid imem _ q1 q q0' _ Hsim Hrun1) as [q' [Hq' Hsim']].
    destruct (IH x mid pf ret q' evs (Ht x) (Hfk mid x pre Hout) Hok' Hroots' HSh' Hmid Htail Hmf
      (ex_intro _ q00 (conj Hown' (pp_sim_trans _ _ _ Hsim0 Hsim')))) as [qf [Hqf Hpf]].
    exists qf. split; [|exact Hpf]. eapply cinterp_next_intro; eassumption.
  - (* WSFail *)
    intros rr lvl s k t p pf ret q evs _ _ _ _ _ _ Hrun.
    apply cinterp_next_inv in Hrun as (mid & x & pre & Hout & _).
    exfalso. simp run_outcome in Hout. VMViews.invert.
  - (* WSChoice *)
    intros rr lvl c k1 k2 _ IH p pf ret q evs Hshape Hf Hok Hroots HSh Hm Hrun Hmf Hrel.
    apply cinterp_choice_inv in Hrun as [r Htail].
    destruct Hshape as [[_ Ht]|Ht].
    + destruct (IH r p pf ret q evs (Ht r) (Hf r) Hok Hroots HSh Hm Htail Hmf Hrel) as [qf [Hqf Hpf]].
      exists qf. split; [|exact Hpf]. eapply cinterp_choice_intro; exact Hqf.
    + exfalso. pose proof (vm_no_update_memory tid imem _ _ _ _ (Ht r) Htail) as Hmid.
      rewrite Hmf, Hm in Hmid. exact (app_cons_len mem ev evs Hmid).
Qed.
End Main.

Section Final.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).

Context (Sh : fin n → memoryMap → ppstate → Prop).
Context (HSh : ShInvariant bbm nondet term initMs Sh).

(** The translation-start obligation after an event of the same thread. *)
Definition StartOwnReplayW : Prop :=
  ∀ (tid : fin n) imem mem ev, VMEventValidity.event_positive ev →
    Ev.tid ev = (tid : nat) → StepStartOwnW tid imem mem ev (Sh tid imem).

Theorem creating_replay_walk :
  StartOwnReplayW → CreatingReplay bbm nondet term initMs code.
Proof using HSh.
  intros Hstart tid imem ts mem ts' mem' iis' ev Hsafe Hprefix Hts Hmiss Hrun evs ->.
  set (p := PPState.Make ts mem IIS.init) in *.
  pose proof (VMEventValidity.sail_fresh_event_positive nondet tid imem p _ evs ev Hrun eq_refl)
    as Hpositive.
  assert (Hok : VMViews.ok p).
  { split; [exact Hts|]. eapply VMViews.iis_ok_mono; [|apply VMViews.iis_init]. lia. }
  pose proof (creating_outcome tid imem mem ev (creating_tlbi tid imem mem ev)) as Hcre.
  assert (Hown : Ev.tid ev = (tid : nat)).
  { destruct (VMSail_instruction_one_updating_outcome bbm nondet tid imem p _ Hrun) as [Hsame|Hw].
    - exfalso. cbn in Hsame. exact (app_cons_len mem ev evs Hsame).
    - destruct Hw as [out [before [after [r [pre [_ [Hb [Ha Hout]]]]]]]].
      cbn in Hb, Ha. exact (proj1 (Hcre out before after (r, pre) evs Hb Hout Ha)). }
  destruct (creating_emits tid imem mem ev Hcre _ p _ () evs (sail_tiny_arm_at_most_one_update nondet)
    Hok eq_refl Hrun eq_refl) as [ts_e He].
  set (q := PPState.Make ts_e (ev :: mem) IIS.init).
  assert (Hrel : RelOwn tid imem mem ev p q).
  { exists q. split; [split; [reflexivity|]; exists ts_e; split; [exact He|reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|]. cbn.
    apply (VMNormalization.ts_ok_sim_refl (length (ev :: mem))).
    eapply VMViews.emit_promise; [|exact Hts|exact He]. cbn. lia. }
  destruct (VMRoots.prefix_roots bbm nondet term initMs tid imem _ _ Hprefix) as [_ Hroots].
  destruct (proj1 (creating_walk tid imem mem ev (Sh tid imem) (proj1 HSh tid imem)
    (Hstart tid imem mem ev Hpositive Hown) Hcre)
    _ (sail_tiny_arm_sem_tsafe nondet) p _ () q evs
    (sail_tiny_arm_at_most_one_update nondet)
    (prefix_fetches bbm nondet term initMs code tid imem mem ev _ p Hsafe Hmiss Hprefix)
    Hok Hroots (proj2 HSh tid imem ts mem Hprefix) eq_refl Hrun eq_refl Hrel)
    as [qf [Hqf (Hm & _ & Hs)]].
  exists ts_e, qf. split; [exact He|]. split; [exact Hqf|].
  cbn in Hm, Hs. split; [symmetry; exact Hm|exact Hs].
Qed.

(** The single-instruction replay obligation from the two translation-start
    obligations. *)
Corollary instruction_promise_replay_walks :
  StartReplay Sh → StartOwnReplayW →
  VMNormalization.VMInstructionPromiseReplay bbm nondet term initMs code.
Proof using HSh.
  intros Hstart Hown.
  apply (instruction_promise_replay_walk bbm nondet term initMs code Sh HSh); [exact Hstart|].
  apply creating_replay_walk, Hown.
Qed.

Corollary final_state_equiv_walks :
  StartReplay Sh → StartOwnReplayW →
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
  intros Hstart Hown. apply (final_state_equiv_walk bbm nondet term initMs code Sh HSh);
    [exact Hstart|].
  apply creating_replay_walk, Hown.
Qed.
End Final.
End VMCreatingWalk.
