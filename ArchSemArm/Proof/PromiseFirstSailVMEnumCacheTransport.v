(******************************************************************************)
(* Transport cached certification across ignored VM promises                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstExecutionCurrent
  PromiseFirstSailVMViews PromiseFirstSailVMInstructionReplay PromiseFirstSailVMSwapLookup
  PromiseFirstSailVMSwapInsert PromiseFirstSailVMSwapInsertCertification
  PromiseFirstSailVMSwapRemoveCertification PromiseFirstSailVMSwapRemoveMachine
  PromiseFirstSailVMSwapRemoveInit PromiseFirstSailVMSwapInitial
  PromiseFirstSailVMSwapPos PromiseFirstSailVMPageWrites.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module VMCacheTransport.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

Lemma ignored ev tid : Ev.affects ev tid = false →
  ∃ tlbi rc epoch, ev = Ev.Tlbi tlbi rc epoch ∧ tid ≠ rc ∧ tid ≠ TLBI.tid tlbi.
Proof.
  destruct ev as [msg|tlbi rc epoch]; [discriminate|].
  cbn [Ev.affects]. intro H. apply bool_decide_eq_false in H.
  exists tlbi, rc, epoch. repeat split; tauto.
Qed.

Section Machine.
Context (bbm : bool) {n : nat} (isem : iMon ()) (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation good := (@VMSwapRemoveInit.state_ok n).

Lemma ignored_thread (tid : fin n) ev (a b : state) :
  Ev.affects ev tid = false → PState.promise prom ev a = Ok b →
  PState.tstate tid b = PState.tstate tid a.
Proof.
  intros Hignore Hpromise. destruct (ignored ev tid Hignore) as (tlbi & rc & epoch & -> & Hrc & Howner).
  unfold PState.promise in Hpromise.
  destruct (vimapM _ _) as [states|err] eqn:Hmap; [|discriminate]. cbn in Hpromise.
  injection Hpromise as <-. unfold PState.tstate. cbn.
  pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid) as Hthread.
  cbn in Hthread. rewrite VMSwapRemoveMachine.emit_foreign in Hthread by assumption.
  injection Hthread as <-. reflexivity.
Qed.

Theorem ignored_candidates (tid : fin n) ev (a b : state) fuel candidate :
  good a → Ev.affects ev tid = false → PState.promise prom ev a = Ok b →
  (candidate ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid
    (PState.initmem a) fuel (PState.tstate tid a) (PState.events a)) ↔
   candidate ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid
    (PState.initmem b) fuel (PState.tstate tid b) (PState.events b))).
Proof.
  intros Hok Hignore Hpromise.
  pose proof (ignored_thread tid ev a b Hignore Hpromise) as Hts.
  destruct (ignored ev tid Hignore) as (tlbi & rc & epoch & Hev & Hrc & Howner). subst ev.
  destruct (PromiseFirstCurrent.promise_success prom (Ev.Tlbi tlbi rc epoch) a b Hpromise)
    as [Himem [Hmem Hthreads]].
  destruct (VMSwapRemoveInit.promise_foreign_initial bbm tid tlbi rc epoch a b
    Hrc Howner Hok Hpromise) as [Hremove Hinv].
  split.
  - rewrite Himem, Hts, Hmem.
    eapply (VMSwapInsertCertification.enum_raw_promises_sim (PState.events a)
      tlbi rc epoch bbm isem term tid (PState.initmem a) fuel
      (PState.tstate tid a) (PState.tstate tid a) (PState.events a)
      (Ev.Tlbi tlbi rc epoch :: PState.events a) candidate); [exact Hrc| |].
    + split; [exists []; split; reflexivity|]. split.
      * symmetry. apply VMSwapInitial.shift_initial; [apply Hok|apply Hok].
      * split; [apply VMSwapLookup.iis_rel_init; lia|apply Hok].
    + split; [apply Hok|]. eapply VMViews.iis_ok_mono; [|apply VMViews.iis_init]. cbn; lia.
  - rewrite Himem. eapply (VMSwapRemoveCertification.enum_raw_promises_sim (PState.events a)
      tlbi rc epoch bbm isem term tid (PState.initmem a) fuel
      (PState.tstate tid b) (PState.tstate tid a) (PState.events b) (PState.events a) candidate);
      [exact Hrc|exact Hremove|exact Hinv].
Qed.
Definition IgnoredStep (tid : fin n) (a b : state) :=
  ∃ ev, Ev.affects ev tid = false ∧ PState.promise prom ev a = Ok b.

Lemma ignored_step_good tid a b : good a → IgnoredStep tid a b → good b.
Proof.
  intros Hok (ev & Hignore & Hpromise). eapply VMSwapRemoveInit.promise_ok; eassumption.
Qed.

Theorem ignored_trace_candidates tid a b fuel candidate : good a → rtc (IgnoredStep tid) a b →
  (candidate ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid
    (PState.initmem a) fuel (PState.tstate tid a) (PState.events a)) ↔
   candidate ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid
    (PState.initmem b) fuel (PState.tstate tid b) (PState.events b))).
Proof.
  intros Hok Hsteps. induction Hsteps as [a|a mid b Hstep Htail IH]; [reflexivity|].
  destruct Hstep as (ev & Hignore & Hpromise).
  eapply iff_trans; [exact (ignored_candidates tid ev a mid fuel candidate Hok Hignore Hpromise)|].
  apply IH. eapply VMSwapRemoveInit.promise_ok; eassumption.
Qed.

Definition thread_good (mem : Memory.t) ts := VMViews.ts_ok (length mem) ts ∧
  VMRoots.roots_ok (length mem) ts ∧ VMSwapLookup.ts_pos ts.

Lemma initial_ok mem ts : thread_good mem ts → VMViews.ok (PPState.Make ts mem IIS.init).
Proof.
  intros [Hv _]. split; [exact Hv|]. eapply VMViews.iis_ok_mono; [|apply VMViews.iis_init]. cbn; lia.
Qed.

Lemma fixed_instruction_good (tid : fin n) imem mem ts ts' iis : thread_good mem ts →
  Exec.elem_of_results (PPState.Make ts' mem iis, ())
    (cinterp (run_outcome' n tid imem) isem (PPState.Make ts mem IIS.init)) → thread_good mem ts'.
Proof.
  intros Hgood Hrun. pose proof (initial_ok mem ts Hgood) as Hok. split.
  - pose proof (VMViews.instruction_ok n tid imem isem _ _ () Hok Hrun) as [[Hv _] _]. exact Hv.
  - split.
    + exact (VMRoots.instruction_roots n tid imem isem _ _ () Hok (proj1 (proj2 Hgood)) Hrun).
    + exact (VMSwapPos.instruction_pos n tid imem isem
        (PPState.Make ts mem IIS.init) (PPState.Make ts' mem iis) () (proj2 (proj2 Hgood)) Hrun).
Qed.

Theorem fixed_instruction_insert (tid : fin n) imem mem (tlbi : TLBI.t) (rc epoch : nat) ts ts' iis :
  fin_to_nat tid ≠ rc → thread_good mem ts →
  Exec.elem_of_results (PPState.Make ts' mem iis, ())
    (cinterp (run_outcome' n tid imem) isem (PPState.Make ts mem IIS.init)) →
  ∃ iis', Exec.elem_of_results (PPState.Make ts' (Ev.Tlbi tlbi rc epoch :: mem) iis', ())
    (cinterp (run_outcome' n tid imem) isem
      (PPState.Make ts (Ev.Tlbi tlbi rc epoch :: mem) IIS.init)).
Proof.
  intros Hrc Hgood Hrun.
  assert (Hrel : VMSwapInsert.pp_rel mem tlbi rc epoch (PPState.Make ts mem IIS.init)
    (PPState.Make ts (Ev.Tlbi tlbi rc epoch :: mem) IIS.init)).
  { split; [exists []; split; reflexivity|]. split.
    - symmetry. apply VMSwapInitial.shift_initial; apply Hgood.
    - split; [apply VMSwapLookup.iis_rel_init; lia|apply Hgood]. }
  destruct (VMSwapInsert.instruction_insert_sim mem tlbi rc epoch n tid imem Hrc isem
    _ _ Hrel (initial_ok mem ts Hgood)) as [Hr _].
  destruct (Hr _ () Hrun) as ([newts newmem newiis] & Hnew & (extra & Hmem & Hmem') & Hts & Hrest).
  cbn in Hmem, Hmem', Hts.
  assert (Hextra : extra = []).
  { apply length_zero_iff_nil. apply (f_equal (@length Ev.t)) in Hmem. rewrite length_app in Hmem. lia. }
  subst extra. cbn in Hmem'. subst newmem.
  pose proof (fixed_instruction_good tid imem mem ts ts' iis Hgood Hrun) as Hgood'.
  rewrite (VMSwapInitial.shift_initial mem ts' (proj1 Hgood') (proj1 (proj2 Hgood'))) in Hts.
  subst newts. exists newiis. exact Hnew.
Qed.

Theorem fixed_thread_insert (tid : fin n) imem mem (tlbi : TLBI.t) (rc epoch : nat) ts final :
  fin_to_nat tid ≠ rc → thread_good mem ts →
  ThreadInstructionExecution prom tid imem isem term mem ts final →
  ThreadInstructionExecution prom tid imem isem term (Ev.Tlbi tlbi rc epoch :: mem) ts final.
Proof.
  intros Hrc Hgood Hrun. induction Hrun as [ts Hterm|ts mid final iis Hterm Hinst Htail IH].
  - constructor. exact Hterm.
  - destruct (fixed_instruction_insert tid imem mem tlbi rc epoch ts mid iis Hrc Hgood Hinst)
      as [iis' Hinst'].
    eapply ThreadInstructionExecution_step; [exact Hterm|exact Hinst'|].
    apply IH. exact (fixed_instruction_good tid imem mem ts mid iis Hgood Hinst).
Qed.

Lemma ignored_thread_execution (tid : fin n) ev (a b : state) final : good a →
  Ev.affects ev tid = false → PState.promise prom ev a = Ok b →
  ThreadInstructionExecution prom tid (PState.initmem a) isem term (PState.events a)
    (PState.tstate tid a) final →
  ThreadInstructionExecution prom tid (PState.initmem b) isem term (PState.events b)
    (PState.tstate tid b) final.
Proof.
  intros Hok Hignore Hpromise Hrun.
  pose proof (ignored_thread tid ev a b Hignore Hpromise) as Hts.
  destruct (ignored ev tid Hignore) as (tlbi & rc & epoch & -> & Hrc & Howner).
  destruct (PromiseFirstCurrent.promise_success prom (Ev.Tlbi tlbi rc epoch) a b Hpromise)
    as [Himem [Hmem Hthreads]].
  rewrite Himem, Hmem, Hts. apply fixed_thread_insert; [exact Hrc| |exact Hrun].
  split; [apply Hok|]. split; apply Hok.
Qed.

Theorem ignored_trace_execution (tid : fin n) (a b : state) final : good a → rtc (IgnoredStep tid) a b →
  ThreadInstructionExecution prom tid (PState.initmem a) isem term (PState.events a)
    (PState.tstate tid a) final →
  ThreadInstructionExecution prom tid (PState.initmem b) isem term (PState.events b)
    (PState.tstate tid b) final.
Proof.
  intros Hok Hsteps. induction Hsteps as [a|a mid b Hstep Htail IH]; intro Hrun; [exact Hrun|].
  destruct Hstep as (ev & Hignore & Hpromise).
  apply IH; [eapply VMSwapRemoveInit.promise_ok; eassumption|].
  exact (ignored_thread_execution tid ev a mid final Hok Hignore Hpromise Hrun).
Qed.
End Machine.
End VMCacheTransport.
