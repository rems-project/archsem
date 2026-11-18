From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstSailNoFuel PromiseFirstSailCurrent
  PromiseFirstVMExecutionCurrent PromiseFirstSailExecution PromiseFirstSailVMViews
  PromiseFirstSailVMTransEnd PromiseFirstSailVMTranslation PromiseFirstSailVMCacheSim
  PromiseFirstSailVMNormalization PromiseFirstSailVMWriteNormalization PromiseFirstSailRead
  PromiseFirstSailVMReplay PromiseFirstSailVMTLBINormalization
  PromiseFirstSailVMInstructionReplay.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** This file discharges the creating clause of
    [VMNormalization.VMInstructionPromiseReplay]
    ([VMInstructionReplay.CreatingReplay]).

    A Sail instruction performs at most one memory or TLB update
    ([sail_tiny_arm_at_most_one_update]). When that update creates the event
    [ev] as its oldest new event, promising [ev] before the instruction
    replays the instruction as follows.

    - The outcomes before the update run on the original history. They replay
      by the fixed-history per-outcome replays ([StepReplayR]), strengthened
      to [StepReplayOwn]: the instruction-local state of the replay equals the
      original one. Outcomes other than a translation start keep the
      invalidation deadline and the end of the current translation interval
      ([outcome_iis_keep]), so [StepReplayR] gives [StepReplayOwn] for them
      ([step_own_of_R]). For a translation start this is the premise
      [TransStartOwnReplay].
    - The update becomes the fulfilment of [ev] with the same post-state
      ([creating_mem_write] from [write_fresh_normalization];
      [creating_tlbi] from [materialize_fresh_normalization] for the first
      fresh recipient, with the earlier recipients fulfilled as before).
    - The rest of the instruction performs no update and continues on
      simulated states ([instruction_sim]). *)
Module VMCreatingReplay.
Import VMPromising VMCacheSim VMCacheSimOutcome VMInstructionReplay.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view othrow.
#[local] Instance exec_unfold : Exec.Unfold := {}.

(** * Outcomes other than a translation start keep the translation interval *)

Definition iis_keep (a b : IIS.t) : Prop :=
  IIS.inv_time b = IIS.inv_time a ∧
  (IIS.trs b = None ∨
    fmap IIS.TransRes.trans_end (IIS.trs b) = fmap IIS.TransRes.trans_end (IIS.trs a)).

Definition not_trans_start (out : outcome) : Prop :=
  match out with TranslationStart _ => False | _ => True end.

Lemma keep_refl a : iis_keep a a.
Proof. split; [reflexivity|right; reflexivity]. Qed.

Lemma keep_trans a b c : iis_keep a b → iis_keep b c → iis_keep a c.
Proof.
  intros [Hi1 Ht1] [Hi2 Ht2]. split; [congruence|].
  destruct Ht2 as [Hn|He2]; [left; exact Hn|].
  destruct Ht1 as [Hn|He1]; [|right; congruence].
  destruct (IIS.trs c) eqn:Hc; [|left; reflexivity].
  rewrite Hn in He2. discriminate.
Qed.

Ltac keep_close :=
  repeat match goal with p : PPState.t _ _ _ |- _ => destruct p end;
  repeat match goal with p : (TState.t * IIS.t)%type |- _ => destruct p end;
  repeat match goal with i : IIS.t |- _ => destruct i end;
  repeat match goal with t : IIS.TransRes.t |- _ => destruct t end;
  cbn in *; subst; unfold iis_keep; cbn;
  first [split; [reflexivity|right; reflexivity] | split; [reflexivity|left; reflexivity]].

Lemma keep_read_mem imem addr size macc p p' r :
  Exec.elem_of_results (p', r) (read_mem_explicit imem addr size macc p) →
  iis_keep (PPState.iis p) (PPState.iis p').
Proof. intro H. unfold read_mem_explicit in H. VMMemoryGrowth.invert_execution; keep_close. Qed.

Lemma keep_read_pte p p' r :
  Exec.elem_of_results (p', r) (read_pte p) → iis_keep (PPState.iis p) (PPState.iis p').
Proof.
  intro H. unfold read_pte in H. VMMemoryGrowth.invert_execution.
  all: repeat match goal with p : PPState.t _ _ _ |- _ => destruct p end.
  all: repeat match goal with i : IIS.t |- _ => destruct i end.
  all: cbn in *; subst.
  all: match goal with Hp : context [IIS.TransRes.pop ?t] |- _ =>
    destruct t as [a1 a2 a3 [|h tl]]; cbn in Hp end.
  all: match goal with Hp : Exec.elem_of_results _ _ |- _ => hnf in Hp; cbn in Hp end.
  - exfalso. inversion H2.
  - apply list_elem_of_singleton in H2. injection H2 as -> ->.
    split; [reflexivity|right; reflexivity].
Qed.

Lemma keep_reg_write tid imem reg racc val p p' r :
  Exec.elem_of_results (p', r) (run_reg_write tid imem reg racc val p) →
  iis_keep (PPState.iis p) (PPState.iis p').
Proof. intro H. unfold run_reg_write in H. VMMemoryGrowth.invert_execution; keep_close. Qed.

Lemma keep_cse tid imem vmax p p' r :
  Exec.elem_of_results (p', r) (run_cse tid imem vmax p) → iis_keep (PPState.iis p) (PPState.iis p').
Proof. intro H. unfold run_cse in H. VMMemoryGrowth.invert_execution; keep_close. Qed.

Lemma keep_barrier tid imem b vmax p p' r :
  Exec.elem_of_results (p', r) (run_barrier tid imem b vmax p) →
  iis_keep (PPState.iis p) (PPState.iis p').
Proof.
  intro H. unfold run_barrier in H. VMMemoryGrowth.invert_execution; try keep_close.
  all: eapply keep_cse; eassumption.
Qed.

Lemma keep_take tid imem fault vmax p p' r :
  Exec.elem_of_results (p', r) (run_take_exception tid imem fault vmax p) →
  iis_keep (PPState.iis p) (PPState.iis p').
Proof.
  intro H. unfold run_take_exception in H. VMMemoryGrowth.invert_execution.
  all: eapply keep_cse; eassumption.
Qed.

Lemma keep_write_mem tid imem addr size macc data p p' r :
  Exec.elem_of_results (p', r) (write_mem tid imem addr size macc data p) →
  iis_keep (PPState.iis p) (PPState.iis p').
Proof. intro H. unfold write_mem in H. VMMemoryGrowth.invert_execution; keep_close. Qed.

Lemma keep_materialize tid imem pre tlbi recipient p p' r :
  Exec.elem_of_results (p', r) (materialize_tlbi_for_recipient tid imem pre tlbi recipient p) →
  PPState.iis p' = PPState.iis p.
Proof.
  intro H. unfold materialize_tlbi_for_recipient in H. VMMemoryGrowth.invert_execution.
  all: repeat match goal with p : PPState.t _ _ _ |- _ => destruct p end; cbn in *; subst; reflexivity.
Qed.

Lemma keep_recipients tid imem pre tlbi recipients acc p p' r :
  Exec.elem_of_results (p', r)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients p) →
  PPState.iis p' = PPState.iis p.
Proof.
  revert acc p. induction recipients as [|x xs IH]; intros acc p Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. reflexivity.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [a [Hstep Htail]]].
    rewrite (IH _ _ Htail). destruct acc as [[vs vo] c].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [m2 [[t b] [Hm Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _]. eapply keep_materialize; exact Hm.
Qed.

Lemma keep_tlbi n tid imem viio tlbi p p' r :
  Exec.elem_of_results (p', r) (run_tlbi n tid imem viio tlbi p) →
  iis_keep (PPState.iis p) (PPState.iis p').
Proof.
  intro H. unfold run_tlbi in H. VMMemoryGrowth.invert_execution.
  all: try match goal with Hr : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    epose proof (keep_recipients tid imem _ _ _ _ _ _ _ Hr) as Hiis; clear Hr end.
  all: match goal with Hiis : PPState.iis ?x = _ |- _ =>
    destruct x as [s6 m6 i6]; cbn in Hiis |- *; subst i6 end.
  all: destruct (PPState.iis p); split; [reflexivity|right; reflexivity].
Qed.

Ltac keep_finish :=
  repeat match goal with p : PPState.t _ _ _ |- _ => destruct p end;
  repeat match goal with p : (TState.t * IIS.t)%type |- _ => destruct p end;
  repeat match goal with i : IIS.t |- _ => destruct i end;
  cbn in *; subst; unfold iis_keep; cbn;
  first [split; [reflexivity|right; reflexivity] | split; [reflexivity|left; reflexivity]].

Lemma outcome_iis_keep n tid imem out p p' r :
  not_trans_start out →
  Exec.elem_of_results (p', r) (run_outcome n tid imem out p) →
  iis_keep (PPState.iis p) (PPState.iis p').
Proof.
  intros Hnt H. funelim (run_outcome n tid imem out p).
  all: rewrite <- Heqcall in H.
  all: cbn in Hnt; try contradiction.
  all: VMMemoryGrowth.invert_execution.
  all: try keep_finish.
  all: try match goal with Hx : Exec.elem_of_results _ (run_reg_read _ _ _) |- _ =>
    destruct out as [ts0 m0 i0]; destruct x1 as [ts1 i1];
    apply reg_read_fields in Hx as (_ & Ht & Hi); cbn in *;
    split; [exact Hi|right; rewrite Ht; reflexivity] end.
  all: try match goal with Hx : Exec.elem_of_results (?x, _) (run_trans_end _ _) |- _ =>
    destruct out as [ts0 m0 i0]; destruct x as [ts1 i1]; cbn in Hx |- *;
    apply trans_end_fields in Hx as (_ & _ & _ & Hn & Hi);
    split; [exact Hi|left; exact Hn] end.
  all: first [eapply keep_read_mem; eassumption | eapply keep_read_pte; eassumption
    | eapply keep_reg_write; eassumption | eapply keep_barrier; eassumption
    | eapply keep_take; eassumption | eapply keep_write_mem; eassumption
    | eapply keep_tlbi; eassumption | eapply keep_cse; eassumption | idtac].
Qed.

Local Notation ppstate := (PPState.t TState.t Ev.t IIS.t).

Section Own.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Definition ExactOwn (p q0 : ppstate) : Prop :=
  PPState.mem p = mem ∧ ∃ issued,
    TState.emit_promise tid imem (ev :: mem) ev (PPState.state p) = Ok issued ∧
    q0 = PPState.Make issued (ev :: mem) (PPState.iis p).

Definition RelOwn (p q : ppstate) := ∃ q0, ExactOwn p q0 ∧ pp_sim q0 q.

Definition StepReplayOwn out : Prop :=
  ∀ p p' r q0, VMViews.ok p → VMRoots.pok p → ExactOwn p q0 → fetch_ok imem ev out p →
    PPState.mem p' = mem → emits tid imem mem ev (PPState.state p') →
    Exec.elem_of_results (p', r) (run_outcome n tid imem out p) →
    ∃ q0', Exec.elem_of_results (q0', r) (run_outcome n tid imem out q0) ∧ RelOwn p' q0'.

Lemma exact_of_own p q0 : ExactOwn p q0 → Exact tid imem mem ev p q0.
Proof.
  intros [Hm [issued [He ->]]]. split; [exact Hm|].
  exists issued, (match IIS.trs (PPState.iis p) with Some t => IIS.TransRes.trans_end t | None => 0 end),
    (IIS.inv_time (PPState.iis p)).
  split; [exact He|]. split; [intros trs Htrs; rewrite Htrs; lia|].
  split; [left; reflexivity|]. f_equal.
  destruct (PPState.iis p) as [s [[a b c d]|] i rr sr]; reflexivity.
Qed.

Lemma interval_keep stop inv (a b : IIS.t) :
  iis_keep a b → iis_keep a (VMTransEndReplay.interval_iis stop inv b) →
  VMTransEndReplay.interval_iis stop inv b = b.
Proof.
  destruct a as [s ta i rr sr], b as [s' tb i' rr' sr'].
  unfold iis_keep, VMTransEndReplay.interval_iis; cbn.
  intros [Hi1 Ht1] [Hi2 Ht2]. subst.
  destruct tb as [[b1 b2 b3 b4]|]; cbn in *; [|reflexivity].
  destruct Ht1 as [Ht1|Ht1]; [discriminate|]. destruct Ht2 as [Ht2|Ht2]; [discriminate|].
  rewrite <- Ht1 in Ht2. injection Ht2 as ->. reflexivity.
Qed.

Lemma step_own_of_R out : not_trans_start out → StepReplayR tid imem mem ev out → StepReplayOwn out.
Proof.
  intros Hnt Hstep p p' r q0 Hok Hroots Hown Hf Hm He Hrun.
  destruct (Hstep p p' r q0 Hok Hroots (exact_of_own p q0 Hown) Hf Hm He Hrun)
    as [q0' [Hrun0 [q1 [Hex Hsim]]]].
  exists q0'. split; [exact Hrun0|]. exists q1. split; [|exact Hsim].
  pose proof (outcome_iis_keep n tid imem out p p' r Hnt Hrun) as Kp.
  pose proof (outcome_iis_keep n tid imem out q0 q0' r Hnt Hrun0) as Kq.
  destruct Hown as [_ [issued0 [_ ->]]]. cbn [PPState.iis] in Kq.
  destruct Hex as [Hm' [issued [stop [inv [He1 [_ [_ ->]]]]]]].
  split; [exact Hm'|]. exists issued. split; [exact He1|]. f_equal.
  destruct Hsim as (_ & Hi & _). cbn [PPState.iis] in Hi. rewrite <- Hi in Kq.
  exact (interval_keep stop inv _ _ Kp Kq).
Qed.
End Own.


Section Creating.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

(** The outcome that creates [ev] as its oldest new event becomes the
    fulfilment of [ev] once [ev] is promised before it. *)
Definition CreatingOutcome out : Prop :=
  ∀ p p' r evs, PPState.mem p = mem →
    Exec.elem_of_results (p', r) (run_outcome n tid imem out p) →
    PPState.mem p' = (evs ++ ev :: mem)%list →
    Ev.tid ev = (tid : nat) ∧ ∃ issued r',
      TState.emit_promise tid imem (ev :: mem) ev (PPState.state p) = Ok issued ∧
      Exec.elem_of_results (p', r')
        (run_outcome n tid imem out (PPState.Make issued (ev :: mem) (PPState.iis p))) ∧
      r'.1 = r.1.

Lemma app_cons_len (evs : list Ev.t) : (evs ++ ev :: mem)%list ≠ mem.
Proof. intro H. apply (f_equal length) in H. rewrite length_app in H. cbn in H. lia. Qed.

Lemma creating_mem_write mr v t : CreatingOutcome (MemWrite mr v t).
Proof.
  intros p p' r evs Hm Hrun Hm'.
  destruct p as [ts m iis]. cbn in Hm. subst m.
  destruct mr as [macc addr space size [|tagsz]];
    simp run_outcome in Hrun; VMMemoryGrowth.invert_execution.
  match goal with H : Exec.elem_of_results _ (write_mem _ _ _ _ _ _ _) |- _ => rename H into Hw end.
  match goal with H : context [is_explicit macc] |- _ => rename H into Hexp end.
  pose proof Hw as Hg. apply VMMemoryGrowth.write_mem_growth in Hg as [Hsame|[pre [Hmw [-> _]]]].
  { exfalso. cbn in Hsame. rewrite Hm' in Hsame. exact (app_cons_len evs Hsame). }
  cbn in Hmw. rewrite Hm' in Hmw.
  assert (Hev : evs = [] ∧ ev = Ev.Msg (Msg.make tid addr size v)).
  { destruct evs as [|e evs]; cbn in Hmw.
    - injection Hmw as ->. auto.
    - exfalso. injection Hmw as _ Hmw. apply (f_equal length) in Hmw.
      rewrite length_app in Hmw. cbn in Hmw. lia. }
  destruct Hev as [-> ->].
  destruct (VMWriteNormalization.write_fresh_normalization tid imem addr size macc v ts mem iis _ pre Hw)
    as [issued [He Hw']].
  split; [reflexivity|]. exists issued, (Ok (), None). split; [exact He|]. split; [|reflexivity].
  simp run_outcome. apply exec_guard_or_bind_intro; [reflexivity|].
  apply exec_guard_or_bind_intro; [exact Hexp|].
  eapply Exec.elem_of_bind_intro; [exact Hw'|]. apply Exec.elem_of_mret.
Qed.

Lemma creating_outcome : (∀ tlbi, CreatingOutcome (TlbOp tlbi)) → ∀ out, CreatingOutcome out.
Proof.
  intros Htlbi out. destruct out; try apply creating_mem_write; try apply Htlbi.
  all: intros p p' [r pre] evs Hm Hrun Hm'; exfalso.
  all: pose proof (VMSailMemory.outcome_no_update_mem n tid imem _ p p' r pre I Hrun) as Heq.
  all: rewrite Hm', Hm in Heq; exact (app_cons_len evs Heq).
Qed.

Lemma vm_no_update_memory {A} (mon : iMon A) p p' ret :
  IMonNoUpdate mon → Exec.elem_of_results (p', ret) (cinterp (run_outcome' n tid imem) mon p) →
  PPState.mem p' = PPState.mem p.
Proof.
  intros Hm Hr. refine (no_update_instruction_memory (VMPromising false) tid imem _ mon p p' ret Hm Hr).
  intros. eapply VMSailMemory.outcome_no_update_mem; eassumption.
Qed.

Section Main.
Context (Hstep : ∀ out, IEffectNoUpdate (inl out) → StepReplayOwn tid imem mem ev out).
Context (Hcre : ∀ out, CreatingOutcome out).

Lemma creating_emits {A} (mon : iMon A) p pf ret evs :
  IMonAtMostOneUpdate mon → VMViews.ok p → PPState.mem p = mem →
  Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) mon p) →
  PPState.mem pf = (evs ++ ev :: mem)%list → emits tid imem mem ev (PPState.state p).
Proof using Hcre.
  revert p. induction mon as [a|call k IH]; intros p Hshape Hok Hm Hrun Hmf.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exfalso.
    rewrite Hm in Hmf. exact (app_cons_len evs (eq_sym Hmf)).
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      pose proof (VMViews.run_outcome_ok n tid imem out p mid _ Hok Hout) as Hok'.
      destruct Hshape as [[Ho Ht]|Ht].
      * pose proof (VMSailMemory.outcome_no_update_mem n tid imem out p mid r pre Ho Hout) as Hmid.
        eapply (step_back tid imem mem ev out p mid (r, pre) Hok Hout).
        eapply (IH r mid (Ht r) Hok'); [congruence|exact Htail|exact Hmf].
      * pose proof (vm_no_update_memory _ _ _ _ (Ht r) Htail) as Hmid.
        destruct (Hcre out p mid (r, pre) evs Hm Hout (eq_trans (eq_sym Hmid) Hmf))
          as [_ [issued [_ [He _]]]].
        exists issued. exact He.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [i [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      destruct Hshape as [[_ Ht]|Ht].
      * exact (IH i p (Ht i) Hok Hm Htail Hmf).
      * exfalso. pose proof (vm_no_update_memory _ _ _ _ (Ht i) Htail) as Hmid.
        rewrite Hmf, Hm in Hmid. exact (app_cons_len evs Hmid).
Qed.

Lemma creating_cinterp {A} (mon : iMon A) p pf ret q evs :
  IMonAtMostOneUpdate mon → fetches tid imem ev mon p → VMViews.ok p → VMRoots.pok p →
  PPState.mem p = mem →
  Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) mon p) →
  PPState.mem pf = (evs ++ ev :: mem)%list → RelOwn tid imem mem ev p q →
  ∃ qf, Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) mon q) ∧ pp_sim pf qf.
Proof using Hstep Hcre.
  revert p q. induction mon as [a|call k IH]; intros p q Hshape Hf Hok Hroots Hm Hrun Hmf Hrel.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exfalso.
    rewrite Hm in Hmf. exact (app_cons_len evs (eq_sym Hmf)).
  - destruct call as [out|[choices]]; cbn in Hrun, Hf |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct Hf as [Hfo Hfk].
      pose proof (VMViews.run_outcome_ok n tid imem out p mid _ Hok Hout) as Hok'.
      pose proof (VMRoots.run_outcome_roots n tid imem out p mid _ Hok Hroots Hout) as Hroots'.
      destruct Hshape as [[Ho Ht]|Ht].
      * pose proof (VMSailMemory.outcome_no_update_mem n tid imem out p mid r pre Ho Hout) as Hmid.
        rewrite Hm in Hmid.
        pose proof (creating_emits (k r) mid pf ret evs (Ht r) Hok' Hmid Htail Hmf) as He'.
        destruct Hrel as [q0 [Hown Hsim]].
        destruct (Hstep out Ho p mid (r, pre) q0 Hok Hroots Hown Hfo Hmid He' Hout)
          as [q0' [Hq0 [q1 [Hown1 Hsim1]]]].
        destruct (run_outcome_simulation n tid imem out q0 q q0' (r, pre) Hsim Hq0)
          as [q' [Hq' Hsim']].
        assert (Hrel' : RelOwn tid imem mem ev mid q').
        { exists q1. split; [exact Hown1|]. eapply pp_sim_trans; eassumption. }
        destruct (IH r mid q' (Ht r) (Hfk mid r pre Hout) Hok' Hroots' Hmid Htail Hmf Hrel')
          as [qf [Hqf Hpf]].
        exists qf. split; [|exact Hpf].
        eapply Exec.elem_of_bind_intro; [|exact Hqf].
        apply (Exec.elem_of_fmap_intro _ _ (r, pre) _ fst Hq').
      * pose proof (vm_no_update_memory _ _ _ _ (Ht r) Htail) as Hmid.
        destruct (Hcre out p mid (r, pre) evs Hm Hout (eq_trans (eq_sym Hmid) Hmf))
          as [_ [issued [r' [He [Hc Hr']]]]].
        destruct Hrel as [q0 [[_ [issued0 [He0 ->]]] Hsim]].
        rewrite He in He0. injection He0 as <-.
        destruct (run_outcome_simulation n tid imem out _ q mid r' Hsim Hc) as [q' [Hq' Hsim']].
        destruct (instruction_sim n tid imem (k r) mid q' pf ret Hsim' Htail) as [qf [Hqf Hpf]].
        exists qf. split; [|exact Hpf].
        eapply Exec.elem_of_bind_intro; [|exact Hqf].
        cbn in Hr'. rewrite <- Hr'.
        apply (Exec.elem_of_fmap_intro _ _ r' _ fst Hq').
    + apply Exec.elem_of_bind_elim in Hrun as [mid [i [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      destruct Hshape as [[_ Ht]|Ht].
      * destruct (IH i p q (Ht i) (Hf i) Hok Hroots Hm Htail Hmf Hrel) as [qf [Hqf Hpf]].
        exists qf. split; [|exact Hpf].
        eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|exact Hqf].
      * exfalso. pose proof (vm_no_update_memory _ _ _ _ (Ht i) Htail) as Hmid.
        rewrite Hmf, Hm in Hmid. exact (app_cons_len evs Hmid).
Qed.
End Main.

End Creating.

#[local] Existing Instance PromMemory.lookup_inst.

Lemma fulfill_other e ev (mem : list Ev.t) pending : e ≠ ev →
  Memory.fulfill e (S (length mem) :: pending) (ev :: mem) = Memory.fulfill e pending mem.
Proof.
  intro Hne. unfold Memory.fulfill, PromMemory.fulfill.
  rewrite filter_cons_False.
  2: { change (S (length mem)) with (length (ev :: mem)). rewrite PromMemory.lookup_latest.
       intros [= ->]. exact (Hne eq_refl). }
  f_equal. f_equal. apply list_filter_iff. intro t.
  destruct (decide (t ≤ length mem)) as [Hle|Hgt].
  - rewrite PromMemory.lookup_cons_old by exact Hle. reflexivity.
  - assert (Hn : (mem : PromMemory.t Ev.t) !! t = None).
    { unfold lookup, PromMemory.lookup_inst. destruct (t =? 0)%stdpp; [reflexivity|].
      replace (t <=? length mem) with false by (symmetry; apply Nat.leb_gt; lia). reflexivity. }
    rewrite Hn. split; [|discriminate]. intro H. exfalso.
    destruct (decide (t = length (ev :: mem))) as [->|Hne2].
    + rewrite PromMemory.lookup_latest in H. injection H as ->. exact (Hne eq_refl).
    + unfold lookup, PromMemory.lookup_inst in H. destruct (t =? 0)%stdpp; [discriminate|].
      replace (t <=? length (ev :: mem)) with false in H
        by (symmetry; apply Nat.leb_gt; cbn in *; lia). discriminate.
Qed.

Lemma fulfill_le e (mem : list Ev.t) pending t :
  Memory.fulfill e pending mem = Some t → t ≤ length mem.
Proof.
  unfold Memory.fulfill, PromMemory.fulfill. rewrite head_reverse. intro H.
  apply last_Some_elem_of in H. apply list_elem_of_filter in H as [Hl _].
  unfold lookup, PromMemory.lookup_inst in Hl. destruct (t =? 0)%stdpp; [discriminate|].
  destruct (t <=? length mem) eqn:Hle; [apply Nat.leb_le in Hle; exact Hle|discriminate].
Qed.

Lemma process_event_set_tlbi tid imem mem ev f ts :
  TState.process_event tid imem mem ev (set TState.prom_tlbi f ts) =
    set TState.prom_tlbi f <$> TState.process_event tid imem mem ev ts.
Proof.
  unfold TState.process_event, TState.run_tlb.
  change (TState.tlb (set TState.prom_tlbi f ts)) with (TState.tlb ts).
  destruct (TState.tlb ts) as [cache|].
  - destruct (TLB.fill_promise tid imem mem ev cache) as [[next []]|err]; reflexivity.
  - reflexivity.
Qed.

Lemma filter_promise_tlbi time t ts : t ≠ time →
  set TState.prom_tlbi (filter (λ x, x ≠ t)) (TState.promise_tlbi time ts) =
  TState.promise_tlbi time (set TState.prom_tlbi (filter (λ x, x ≠ t)) ts).
Proof.
  intro Hne. destruct ts. unfold TState.promise_tlbi. cbn.
  rewrite decide_True by congruence. reflexivity.
Qed.

Lemma materialize_fulfilled_inv tid imem pre tlbi recipient ts mem iis p' time :
  Exec.elem_of_results (p', (time, false))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient (PPState.Make ts mem iis)) →
  Memory.fulfill (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts)) (TState.prom_tlbi ts) mem = Some time ∧
  pre < time ∧ p' = PPState.Make (set TState.prom_tlbi (filter (λ t, t ≠ time)) ts) mem iis.
Proof.
  intro Hrun. unfold materialize_tlbi_for_recipient in Hrun.
  VMMemoryGrowth.invert_execution; cbn in *; subst; try discriminate.
  repeat split; try assumption; reflexivity.
Qed.

Section Fold.
Context (tid : nat) (imem : memoryMap) (pre : nat) (tlbi : TLBI.t).
Local Notation step := (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi).

Lemma fold_flag rs vs vo c c0 p p' res :
  Exec.elem_of_results (p', res) (foldlM step ((vs, vo), c) rs p) →
  ∃ c', Exec.elem_of_results (p', (res.1, c')) (foldlM step ((vs, vo), c0) rs p).
Proof.
  revert vs vo c c0 p. induction rs as [|x xs IH]; intros vs vo c c0 p Hrun.
  - cbn in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    exists c0. apply Exec.elem_of_mret.
  - cbn [foldlM] in Hrun |- *. apply Exec.elem_of_bind_elim in Hrun as [mid [a [Hstep Htail]]].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [m2 [[t b] [Hm Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    destruct (IH _ _ _ (c0 || b) _ Htail) as [c' Hc'].
    exists c'. eapply Exec.elem_of_bind_intro; [|exact Hc'].
    unfold VMMemoryGrowth.tlbi_recipient_step.
    eapply Exec.elem_of_bind_intro; [exact Hm|]. apply Exec.elem_of_mret.
Qed.

Lemma app_cons_inv (l1 l2 : list Ev.t) x y m :
  (l1 ++ x :: m)%list = (l2 ++ y :: m)%list → x = y.
Proof.
  intro H. rewrite !cons_middle, !app_assoc in H. apply app_inv_tail in H.
  apply app_inj_tail in H as [_ ->]. reflexivity.
Qed.

Lemma fold_creating rs acc ts (mem : list Ev.t) iis p' res evs ev :
  NoDup rs →
  Exec.elem_of_results (p', res) (foldlM step acc rs (PPState.Make ts mem iis)) →
  TLBI.tid tlbi = tid → PPState.mem p' = (evs ++ ev :: mem)%list →
  (∃ rc, rc ∈ rs ∧ ev = Ev.Tlbi tlbi rc (TState.dsb_epoch ts)) ∧
  ∃ issued res',
    TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued ∧
    Exec.elem_of_results (p', res') (foldlM step acc rs (PPState.Make issued (ev :: mem) iis)) ∧
    res'.1 = res.1.
Proof.
  intros Hnd Hrun Howner Hm'. revert acc ts p' res Hnd Hrun Hm'.
  induction rs as [|x xs IH]; intros acc ts p' res Hnd Hrun Hm'.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exfalso. cbn in Hm'.
    apply (f_equal length) in Hm'. rewrite length_app in Hm'. cbn in Hm'. lia.
  - apply list.NoDup_cons in Hnd as [Hx Hnd].
    cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [a [Hstep Htail]]].
    destruct acc as [[vs vo] c].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [m2 [[t b] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    destruct b.
    + (* the first fresh recipient creates [ev] *)
      pose proof (VMMemoryGrowth.materialize_tlbi_growth _ _ _ _ _ _ _ _ _ Hmat) as Hg. cbn in Hg.
      destruct (VMTLBINormalization.materialize_fresh_inv _ _ _ _ _ _ _ _ _ _ Hmat)
        as [_ [-> [_ [nx [_ ->]]]]].
      destruct res as [[r1 r2] r3].
      destruct (VMMemoryGrowth.tlbi_recipients_growth _ _ _ _ _ _ _ _ _ _ _ _ _ Htail)
        as [[Hsame _]|[extra [_ [Hextra _]]]].
      all: cbn in Hsame || cbn in Hextra.
      all: assert (Hev : ev = Ev.Tlbi tlbi x (TState.dsb_epoch ts)).
      all: try (rewrite Hm' in Hsame; exact (app_cons_inv evs [] _ _ mem Hsame)).
      all: try (rewrite Hm' in Hextra; exact (app_cons_inv evs extra _ _ mem Hextra)).
      all: subst ev.
      all: destruct (VMTLBINormalization.materialize_fresh_normalization tid imem pre tlbi x ts mem iis
        _ _ Howner Hmat) as [issued [He Hmat']].
      all: split; [exists x; split; [left|]; reflexivity|].
      all: destruct (fold_flag xs _ _ (c || true) (c || false) _ _ _ Htail) as [c' Hc'].
      all: exists issued, ((r1, r2), c'); split; [exact He|]; split; [|reflexivity].
      all: cbn [foldlM]; eapply Exec.elem_of_bind_intro; [|exact Hc'].
      all: unfold VMMemoryGrowth.tlbi_recipient_step.
      all: eapply Exec.elem_of_bind_intro; [exact Hmat'|]; apply Exec.elem_of_mret.
    + (* a fulfilled recipient keeps memory *)
      apply materialize_fulfilled_inv in Hmat as [Hful [Hpre ->]].
      destruct (IH _ _ p' res Hnd Htail Hm') as [[rc [Hrc Hev]] [issued1 [res' [He1 [Hrun1 Hres]]]]].
      cbn in Hev.
      assert (Hne : Ev.Tlbi tlbi x (TState.dsb_epoch ts) ≠ ev).
      { rewrite Hev. intros [= Heq]. subst rc. exact (Hx Hrc). }
      split; [exists rc; split; [right; exact Hrc|exact Hev]|].
      assert (Hown : Ev.tid ev = tid) by (rewrite Hev; exact Howner).
      unfold TState.emit_promise in He1 |- *.
      rewrite bool_decide_true in He1 |- * by exact Hown. rewrite Hev in He1 |- *.
      rewrite VMTLBINormalization.process_event_pending, process_event_set_tlbi in He1.
      rewrite VMTLBINormalization.process_event_pending.
      rewrite <- Hev in He1 |- *.
      destruct (TState.process_event tid imem (ev :: mem) ev ts) as [nx|err] eqn:Hnx;
        cbn in He1; [|discriminate]. injection He1 as <-.
      exists (TState.promise_tlbi (length (ev :: mem)) nx), res'.
      split; [reflexivity|]. split; [|exact Hres].
      pose proof (VMReadReplay.run_tlb_frame _ ts nx Hnx) as Hframe.
      pose proof (fulfill_le _ _ _ _ Hful) as Ht.
      cbn [foldlM]. eapply Exec.elem_of_bind_intro; [|exact Hrun1].
      unfold VMMemoryGrowth.tlbi_recipient_step.
      assert (Hmat2 : Exec.elem_of_results
        (PPState.Make (TState.promise_tlbi (S (length mem))
          (set TState.prom_tlbi (filter (λ t0, t0 ≠ t)) nx)) (ev :: mem) iis, (t, false))
        (materialize_tlbi_for_recipient tid imem pre tlbi x
          (PPState.Make (TState.promise_tlbi (length (ev :: mem)) nx) (ev :: mem) iis))).
      2: { eapply Exec.elem_of_bind_intro; [exact Hmat2|]. apply Exec.elem_of_mret. }
      rewrite <- (filter_promise_tlbi (S (length mem)) t nx) by lia.
      apply VMTLBINormalization.materialize_fulfilled; [|exact Hpre].
      rewrite Hframe. cbn [length].
      change (TState.dsb_epoch (TState.promise_tlbi (S (length mem)) (setv TState.tlb (TState.tlb nx) ts)))
        with (TState.dsb_epoch ts).
      change (TState.prom_tlbi (TState.promise_tlbi (S (length mem)) (setv TState.tlb (TState.tlb nx) ts)))
        with (S (length mem) :: TState.prom_tlbi ts).
      rewrite fulfill_other by exact Hne. exact Hful.
Qed.
End Fold.

Section Tlbi.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma creating_tlbi tlbi : CreatingOutcome tid imem mem ev (TlbOp tlbi).
Proof.
  intros p p' r evs Hm Hrun Hm'. destruct p as [ts m iis]. cbn in Hm. subst m.
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [s1 [viio [Hg Hrun]]].
  apply Exec.elem_of_mget_inv in Hg as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [s2 [vopt [Ht Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  unfold run_tlbi in Ht.
  apply Exec.elem_of_bind_elim in Ht as [s3 [u [Hguard Ht]]].
  revert Ht. VMMemoryGrowth.invert_execution. intro Ht.
  apply Exec.elem_of_bind_elim in Ht as [s4 [ts0 [Hg Ht]]].
  apply Exec.elem_of_mget_inv in Hg as [-> ->].
  apply Exec.elem_of_bind_elim in Ht as [s5 [iis0 [Hg Ht]]].
  apply Exec.elem_of_mget_inv in Hg as [-> ->].
  apply Exec.elem_of_bind_elim in Ht as [s6 [tlbiev [Hev Ht]]].
  revert Ht. VMMemoryGrowth.invert_execution. all: intro Ht.
  all: apply Exec.elem_of_bind_elim in Ht as [s7 [[[vs vo] c] [Hfold Ht]]].
  all: revert Hfold; VMMemoryGrowth.invert_execution; intro Hfold.
  all: subst tlbiev.
  all: destruct s7 as [s7s s7m s7i]; cbn in Hm'.
  all: assert (Hnd : ∀ P (d : Decision P), NoDup (if d then [fin_to_nat tid] else seq 0 n))
    by (intros P d; destruct d; [apply NoDup_singleton|apply NoDup_seq]).
  all: pose proof (fold_creating tid imem _ _ _ _ ts mem iis _ _ evs ev (Hnd _ _) Hfold eq_refl Hm')
    as [[rc [Hrc Hevc]] [issued [[[vs' vo'] c'] [He [Hfold' Hres]]]]].
  all: cbn in Hres; injection Hres as -> ->.
  all: split; [rewrite Hevc; reflexivity|].
  all: assert (Hunit : ∀ x : unit * option view, x.1 = ((), vopt).1) by (intros [[] ?]; reflexivity).
  all: pose proof (VMTransEndReplay.emit_promise_frame _ _ _ _ _ _ He) as Hframe.
  all: set (W := TState.prom_wr issued) in Hframe; set (T := TState.prom_tlbi issued) in Hframe;
    set (C := TState.tlb issued) in Hframe; clearbody W T C; subst issued.
  all: eexists; eexists; split; [exact He|]; split; [|apply Hunit].
  all: simp run_outcome.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  all: eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
  all: unfold run_tlbi; apply exec_guard_or_bind_intro; [exact u|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  all: cbn [PPState.state PPState.iis]; rewrite Heqt.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  all: eapply Exec.elem_of_bind_intro; [exact Hfold'|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  all: apply Exec.elem_of_mret.
Qed.
End Tlbi.

Section Final.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).

(** The replay of a translation start after an event of the same thread was
    promised keeps the instruction-local state exactly. *)
Definition TransStartOwnReplay : Prop :=
  ∀ (tid : fin n) imem mem ev tsi, Ev.tid ev = (tid : nat) →
    StepReplayOwn tid imem mem ev (TranslationStart tsi).

(** The clause (a) of [VMNormalization.VMInstructionPromiseReplay]: the
    instruction creating [ev] as its oldest event replays after [ev] is
    promised. *)
Theorem creating_replay :
  FixedOutcomeReplay (n := n) → TransStartOwnReplay →
  CreatingReplay bbm nondet term initMs code.
Proof.
  intros Hfixed Hstart tid imem ts mem ts' mem' iis' ev Hsafe Hprefix Hts Hmiss Hrun evs ->.
  set (p := PPState.Make ts mem IIS.init) in *.
  assert (Hok : VMViews.ok p).
  { split; [exact Hts|]. eapply VMViews.iis_ok_mono; [|apply VMViews.iis_init]. lia. }
  pose proof (creating_outcome tid imem mem ev (creating_tlbi tid imem mem ev)) as Hcre.
  assert (Hown : Ev.tid ev = (tid : nat)).
  { destruct (VMSail_instruction_one_updating_outcome bbm nondet tid imem p _ Hrun) as [Hsame|Hw].
    - exfalso. cbn in Hsame. exact (app_cons_len mem ev evs Hsame).
    - destruct Hw as [out [before [after [r [pre [_ [Hb [Ha Hout]]]]]]]].
      cbn in Hb, Ha. exact (proj1 (Hcre out before after (r, pre) evs Hb Hout Ha)). }
  assert (Hstep : ∀ out, IEffectNoUpdate (inl out) → StepReplayOwn tid imem mem ev out).
  { intros out Ho. destruct out; cbn in Ho; try contradiction.
    all: first [apply Hstart; exact Hown
      |apply step_own_of_R; [exact I|apply (steps_of_uncovered tid imem mem ev (Hfixed tid imem mem ev))]]. }
  destruct (creating_emits tid imem mem ev Hcre _ p _ () evs (sail_tiny_arm_at_most_one_update nondet)
    Hok eq_refl Hrun eq_refl) as [ts_e He].
  set (q := PPState.Make ts_e (ev :: mem) IIS.init).
  assert (Hrel : RelOwn tid imem mem ev p q).
  { exists q. split; [split; [reflexivity|]; exists ts_e; split; [exact He|reflexivity]|].
    split; [reflexivity|]. split; [reflexivity|]. cbn.
    apply (VMNormalization.ts_ok_sim_refl (length (ev :: mem))).
    eapply VMViews.emit_promise; [|exact Hts|exact He]. cbn. lia. }
  destruct (VMRoots.prefix_roots bbm nondet term initMs tid imem _ _ Hprefix) as [_ Hroots].
  destruct (creating_cinterp tid imem mem ev Hstep Hcre _ p _ () q evs
    (sail_tiny_arm_at_most_one_update nondet)
    (prefix_fetches bbm nondet term initMs code tid imem mem ev _ p Hsafe Hmiss Hprefix)
    Hok Hroots eq_refl Hrun eq_refl Hrel) as [qf [Hqf (Hm & _ & Hs)]].
  exists ts_e, qf. split; [exact He|]. split; [exact Hqf|].
  cbn in Hm, Hs. split; [symmetry; exact Hm|exact Hs].
Qed.

(** The single-instruction replay obligation of the normalization, with the
    fixed-history clause from the per-outcome replays. *)
Corollary instruction_promise_replay_own :
  FixedOutcomeReplay (n := n) → TransStartOwnReplay →
  VMNormalization.VMInstructionPromiseReplay bbm nondet term initMs code.
Proof.
  intros Hfixed Hstart. apply instruction_promise_replay; [exact Hfixed|].
  apply creating_replay; assumption.
Qed.

(** [VMInstructionReplay.final_state_equiv] with its creating premise discharged. *)
Corollary final_state_equiv_own :
  FixedOutcomeReplay (n := n) → TransStartOwnReplay →
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
Proof.
  intros Hfixed Hstart. apply final_state_equiv; [exact Hfixed|].
  apply creating_replay; assumption.
Qed.
End Final.

End VMCreatingReplay.
