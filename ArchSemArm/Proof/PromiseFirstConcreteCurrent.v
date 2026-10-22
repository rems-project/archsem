(******************************************************************************)
(* Current concrete hooks for the Arm promising models                       *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSem Require Import GenPromising.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstMemoryCurrent PromiseFirstExecutionCurrent
  PromiseFirstVMExecutionCurrent.

#[local] Open Scope stdpp.

(** The UM model has total initialization and total promise emission.  These
    equalities expose that fact through the current result-valued interface. *)
Lemma UMPromising_tState_init_ok (tid : nat) (mem : memoryMap)
    (regs : registerMap) :
  Promising.tState_init UMPromising tid mem regs =
    Ok (UMPromising.TState.init mem regs).
Proof.
  reflexivity.
Qed.

Lemma UMPromising_emit_promise_ok (tid : nat) (initmem : memoryMap)
    (mem : PromMemory.t Msg.t) (msg : Msg.t)
    (ts : UMPromising.TState.t) :
  Promising.emit_promise UMPromising tid initmem mem msg ts =
    Ok (if bool_decide (Msg.tid msg = tid) then
          UMPromising.TState.promise (length mem) ts
        else ts).
Proof.
  reflexivity.
Qed.

Local Lemma vimapM_total_result {A B E n} (xs : vec A n)
    (f : fin n → A → result E B) :
  (∀ i x, ∃ y, f i x = Ok y) →
  ∃ ys, vimapM f xs = Ok ys.
Proof.
  revert f. induction xs as [|x n xs IH]; intros f Htotal.
  - exists [#]. reflexivity.
  - destruct (Htotal 0%fin x) as [y Hy].
    destruct (IH (f ∘ FS) (λ i a, Htotal (FS i) a)) as [ys Hys].
    cbn [vimapM]. rewrite Hy, Hys. cbn. eexists. reflexivity.
Qed.

Lemma UMPromising_promise_exists {n}
    (msg : Msg.t) (st : PState.t UMPromising.TState.t Msg.t n) :
  ∃ st', PState.promise UMPromising msg st = Ok st'.
Proof.
  destruct st as [states imem mem].
  unfold PState.promise. cbn.
  destruct (vimapM_total_result states
    (λ tid ts, Promising.emit_promise UMPromising (tid : nat) imem
      (msg :: mem) msg ts)) as [states' Hstates].
  - intros tid ts. rewrite UMPromising_emit_promise_ok. eexists. reflexivity.
  - rewrite Hstates. cbn. eexists. reflexivity.
Qed.

Lemma UMPromising_initialization_success {n : nat}
    (ms : archState n) (st : PState.t UMPromising.TState.t Msg.t n) :
  PState.from_archState UMPromising ms = Ok st →
  PState.initmem st = archState.memory ms ∧
  PState.events st = [] ∧
  ∀ tid : fin n,
    Promising.tState_init UMPromising (tid : nat)
      (archState.memory ms) (archState.regs ms !!! tid) =
    Ok (PState.tstate tid st).
Proof.
  apply PromiseFirstCurrent.initialization_success.
Qed.

Lemma UMPromising_promise_success {n : nat}
    (ev : Msg.t) (st st' : PState.t UMPromising.TState.t Msg.t n) :
  PState.promise UMPromising ev st = Ok st' →
  PState.initmem st' = PState.initmem st ∧
  PState.events st' = ev :: PState.events st ∧
  ∀ tid : fin n,
    Promising.emit_promise UMPromising (tid : nat)
      (PState.initmem st) (ev :: PState.events st) ev
      (PState.tstate tid st) = Ok (PState.tstate tid st').
Proof.
  apply PromiseFirstCurrent.promise_success.
Qed.

(** VM initialization and promise emission are intentionally left result
    valued: TLB initialization and promise processing can fail.  The generic
    current lemmas therefore carry the successful [Ok] premises explicitly. *)
Lemma VMPromising_initialization_success {bbm : bool} {n : nat}
    (ms : archState n) (st : PState.t VMPromising.TState.t Ev.t n) :
  PState.from_archState (VMPromising.VMPromising bbm) ms = Ok st →
  PState.initmem st = archState.memory ms ∧
  PState.events st = [] ∧
  ∀ tid : fin n,
    Promising.tState_init (VMPromising.VMPromising bbm) (tid : nat)
      (archState.memory ms) (archState.regs ms !!! tid) =
    Ok (PState.tstate tid st).
Proof.
  apply PromiseFirstCurrent.initialization_success.
Qed.

Lemma VMPromising_tState_init_result {bbm : bool} (tid : nat)
    (mem : memoryMap) (regs : registerMap) :
  Promising.tState_init (VMPromising.VMPromising bbm) tid mem regs =
    VMPromising.TState.init tid mem regs.
Proof.
  reflexivity.
Qed.

Lemma VMPromising_emit_promise_result {bbm : bool} (tid : nat)
    (imem : memoryMap) (mem : VMPromising.Memory.t) (ev : Ev.t)
    (ts : VMPromising.TState.t) :
  Promising.emit_promise (VMPromising.VMPromising bbm) tid imem mem ev ts =
    VMPromising.TState.emit_promise tid imem mem ev ts.
Proof.
  reflexivity.
Qed.

Lemma VMPromising_promise_success {bbm : bool} {n : nat}
    (ev : Ev.t) (st st' : PState.t VMPromising.TState.t Ev.t n) :
  PState.promise (VMPromising.VMPromising bbm) ev st = Ok st' →
  PState.initmem st' = PState.initmem st ∧
  PState.events st' = ev :: PState.events st ∧
  ∀ tid : fin n,
    Promising.emit_promise (VMPromising.VMPromising bbm) (tid : nat)
      (PState.initmem st) (ev :: PState.events st) ev
      (PState.tstate tid st) = Ok (PState.tstate tid st').
Proof.
  apply PromiseFirstCurrent.promise_success.
Qed.

Lemma UMPromising_emit_promise_control_preserved tid imem mem ev ts ts' :
  Promising.emit_promise UMPromising tid imem mem ev ts = Ok ts' →
  UMPromising.TState.pc ts' = UMPromising.TState.pc ts ∧
  UMPromising.TState.min_new_prom_view ts' =
    UMPromising.TState.min_new_prom_view ts.
Proof.
  rewrite UMPromising_emit_promise_ok.
  destruct (bool_decide (Msg.tid ev = tid)); intro H;
    inversion H; subst; split; reflexivity.
Qed.

Lemma VMPromising_run_tlb_control_preserved upd ts ts' :
  VMPromising.TState.run_tlb upd ts = Ok ts' →
  VMPromising.TState.pc ts' = VMPromising.TState.pc ts ∧
  VMPromising.TState.min_new_prom_view ts' =
    VMPromising.TState.min_new_prom_view ts.
Proof.
  unfold VMPromising.TState.run_tlb.
  destruct (VMPromising.TState.tlb ts) as [tlb|].
  - destruct (upd tlb) as [[tlb' []]|err]; cbn; [|discriminate].
    intro H. inversion H; subst. split; reflexivity.
  - intro H. inversion H; subst. split; reflexivity.
Qed.

Lemma VMPromising_emit_promise_control_preserved bbm tid imem mem ev ts ts' :
  Promising.emit_promise (VMPromising.VMPromising bbm) tid imem mem ev ts = Ok ts' →
  VMPromising.TState.pc ts' = VMPromising.TState.pc ts ∧
  VMPromising.TState.min_new_prom_view ts' =
    VMPromising.TState.min_new_prom_view ts.
Proof.
  rewrite VMPromising_emit_promise_result.
  unfold VMPromising.TState.emit_promise, VMPromising.TState.process_event.
  destruct (bool_decide (Ev.tid ev = tid)).
  - destruct ev; intro H;
      apply VMPromising_run_tlb_control_preserved in H; exact H.
  - apply VMPromising_run_tlb_control_preserved.
Qed.

Lemma UMPromising_promise_control_preserved {n}
    ev (st st' : PState.t UMPromising.TState.t Msg.t n) :
  PState.promise UMPromising ev st = Ok st' →
  ∀ tid : fin n,
    UMPromising.TState.pc (PState.tstate tid st') =
      UMPromising.TState.pc (PState.tstate tid st) ∧
    UMPromising.TState.min_new_prom_view (PState.tstate tid st') =
      UMPromising.TState.min_new_prom_view (PState.tstate tid st).
Proof.
  intro Hpromise.
  destruct (UMPromising_promise_success ev st st' Hpromise) as [_ [_ Hhooks]].
  intro tid.
  eapply UMPromising_emit_promise_control_preserved. apply Hhooks.
Qed.

Lemma VMPromising_promise_control_preserved bbm {n}
    ev (st st' : PState.t VMPromising.TState.t Ev.t n) :
  PState.promise (VMPromising.VMPromising bbm) ev st = Ok st' →
  ∀ tid : fin n,
    VMPromising.TState.pc (PState.tstate tid st') =
      VMPromising.TState.pc (PState.tstate tid st) ∧
    VMPromising.TState.min_new_prom_view (PState.tstate tid st') =
      VMPromising.TState.min_new_prom_view (PState.tstate tid st).
Proof.
  intro Hpromise.
  destruct (VMPromising_promise_success ev st st' Hpromise) as [_ [_ Hhooks]].
  intro tid.
  eapply VMPromising_emit_promise_control_preserved. apply Hhooks.
Qed.

Lemma UMPromising_filter_promises_subset n tid mem candidates ev :
  ev ∈ Promising.filter_promises UMPromising n tid mem candidates →
  ev ∈ candidates.
Proof. exact (λ H, H). Qed.

Lemma VMPromising_filter_promises_subset bbm n tid mem candidates ev :
  ev ∈ Promising.filter_promises (VMPromising.VMPromising bbm)
    n tid mem candidates →
  ev ∈ candidates.
Proof.
  cbn [Promising.filter_promises VMPromising.VMPromising].
  unfold VMPromising.filter_tlbi_promises.
  destruct mem as [|prev mem]; [exact (λ H, H)|].
  destruct (Ev.get_tlbi_recipient prev); [|exact (λ H, H)].
  intro Hin. apply list_elem_of_filter in Hin. exact (proj2 Hin).
Qed.

Lemma UMPromising_promise_first_prefix_to_direct
    isem {n} (term : terminationCondition n) initMs st :
  PromiseFirstReachable UMPromising isem term initMs true st →
  PromiseFirstReachable UMPromising isem term initMs false st.
Proof.
  apply promise_first_reachable_to_direct.
  intros. eapply UMPromising_filter_promises_subset. eassumption.
Qed.

Lemma VMPromising_promise_first_prefix_to_direct
    bbm isem {n} (term : terminationCondition n) initMs st :
  PromiseFirstReachable (VMPromising.VMPromising bbm) isem term initMs true st →
  PromiseFirstReachable (VMPromising.VMPromising bbm) isem term initMs false st.
Proof.
  apply promise_first_reachable_to_direct.
  intros. eapply VMPromising_filter_promises_subset. eassumption.
Qed.

Lemma UMPromising_enumerated_promise_misses_code
    isem {n} (term : terminationCondition n) initMs code use_pf st tid fuel
    (msg : Promising.mEvent UMPromising) :
  UMPromisingNoSelfModifying isem term initMs code →
  PromiseFirstReachable UMPromising isem term initMs use_pf st →
  msg ∈ (CPState.enumerate_results isem UMPromising term tid (PState.initmem st)
    fuel (PState.tstate tid st) (PState.events st)).(CPState.promises UMPromising) →
  event_misses_code Msg.read_byte code msg.
Proof.
  apply no_self_modifying_enumerated_promise.
  intros. eapply UMPromising_filter_promises_subset. eassumption.
Qed.

Lemma VMPromising_enumerated_promise_misses_code
    bbm isem {n} (term : terminationCondition n) initMs code use_pf st tid fuel
    (ev : Promising.mEvent (VMPromising.VMPromising bbm)) :
  VMPromisingNoSelfModifying bbm isem term initMs code →
  PromiseFirstReachable (VMPromising.VMPromising bbm) isem term initMs use_pf st →
  ev ∈ (CPState.enumerate_results isem (VMPromising.VMPromising bbm) term tid
    (PState.initmem st) fuel (PState.tstate tid st) (PState.events st))
      .(CPState.promises (VMPromising.VMPromising bbm)) →
  event_misses_code VMPromisingReadByte code ev.
Proof.
  apply no_self_modifying_enumerated_promise.
  intros. eapply VMPromising_filter_promises_subset. eassumption.
Qed.

(** A certified candidate can be moved before an instruction fetch whose
    physical byte range is in the immutable code region.  These equalities
    include failed fetch results and do not require a nonempty write. *)
Lemma UMPromising_enumerated_promise_ifetch
    isem {n} (term : terminationCondition n) initMs code use_pf st tid fuel
    (msg : Promising.mEvent UMPromising) addr :
  UMPromisingNoSelfModifying isem term initMs code →
  PromiseFirstReachable UMPromising isem term initMs use_pf st →
  msg ∈ (CPState.enumerate_results isem UMPromising term tid (PState.initmem st)
    fuel (PState.tstate tid st) (PState.events st)).(CPState.promises UMPromising) →
  code_covers_range code addr 4 →
  UMPromising.read_ifetch addr (PState.initmem st) (msg :: PState.events st) =
  UMPromising.read_ifetch addr (PState.initmem st) (PState.events st).
Proof.
  intros Hsafe Hreach Hcandidate Hcode.
  pose proof (UMPromising_enumerated_promise_misses_code isem term initMs code
    use_pf st tid fuel msg Hsafe Hreach Hcandidate) as Hmiss.
  unfold UMPromising.read_ifetch, UMPromising.Memory.read_initial.
  rewrite (read_initial_cons_code_miss Some code addr 4
    (PState.initmem st) (PState.events st) msg).
  - reflexivity.
  - lia.
  - exact Hcode.
  - intros msg' Heq. inversion Heq; subst. exact Hmiss.
Qed.

Lemma VMPromising_enumerated_promise_ifetch
    bbm isem {n} (term : terminationCondition n) initMs code use_pf st tid fuel
    (ev : Promising.mEvent (VMPromising.VMPromising bbm)) addr :
  VMPromisingNoSelfModifying bbm isem term initMs code →
  PromiseFirstReachable (VMPromising.VMPromising bbm) isem term initMs use_pf st →
  ev ∈ (CPState.enumerate_results isem (VMPromising.VMPromising bbm) term tid
    (PState.initmem st) fuel (PState.tstate tid st) (PState.events st))
      .(CPState.promises (VMPromising.VMPromising bbm)) →
  code_covers_range code addr 4 →
  VMPromising.read_imem (PState.initmem st) addr (ev :: PState.events st) =
  VMPromising.read_imem (PState.initmem st) addr (PState.events st).
Proof.
  intros Hsafe Hreach Hcandidate Hcode.
  pose proof (VMPromising_enumerated_promise_misses_code bbm isem term initMs code
    use_pf st tid fuel ev Hsafe Hreach Hcandidate) as Hmiss.
  unfold VMPromising.read_imem, VMPromising.Memory.read_initial.
  rewrite (read_initial_cons_code_miss Ev.get_msg code addr 4
    (PState.initmem st) (PState.events st) ev).
  - reflexivity.
  - lia.
  - exact Hcode.
  - intros msg Hmsg a Ha.
    specialize (Hmiss a Ha). unfold VMPromisingReadByte in Hmiss.
    rewrite Hmsg in Hmiss. exact Hmiss.
Qed.

(** Every UM final candidate has an instruction execution at the original
    shared history.  This uses the concrete write semantics, without an
    assumed execution transformation or a memory-preservation premise. *)
Lemma UMPromising_enumerated_final_thread_execution
    isem {n} (term : terminationCondition n) (tid : fin n)
    initmem fuel ts mem (ts' : Promising.tState UMPromising) :
  ts' ∈ (CPState.enumerate_results isem UMPromising term tid initmem fuel ts mem)
    .(CPState.final_states UMPromising) →
  ThreadInstructionExecution UMPromising tid initmem isem term mem ts ts'.
Proof.
  apply enumerated_final_thread_execution.
  exact UMMemoryGrowth.outcome_memory_growth.
Qed.

Lemma VMPromising_enumerated_final_thread_execution
    bbm isem {n} (term : terminationCondition n) (tid : fin n)
    initmem fuel ts mem (ts' : Promising.tState (VMPromising.VMPromising bbm)) :
  ts' ∈ (CPState.enumerate_results isem (VMPromising.VMPromising bbm) term tid
    initmem fuel ts mem).(CPState.final_states (VMPromising.VMPromising bbm)) →
  ThreadInstructionExecution (VMPromising.VMPromising bbm) tid initmem
    isem term mem ts ts'.
Proof.
  apply enumerated_final_thread_execution.
  exact (VMMemoryGrowth.outcome_memory_growth bbm).
Qed.

(** Conditional adapters.  The execution transforms remain to be proved for
    programs satisfying the corresponding no-self-modification predicate. *)
Lemma UMPromising_equiv_from_current_obligations
    (isem : iMon ()) {n} (term : terminationCondition n) initMs
    (Htransform : UMPromisingExecutionTransforms isem term initMs) :
  UMPromisingFinalStateEquiv isem term initMs.
Proof.
  exact (promise_first_equiv_from_execution_transforms
    UMPromising isem term initMs Htransform).
Qed.

Lemma VMPromising_equiv_from_current_obligations
    (bbm : bool) (isem : iMon ()) {n} (term : terminationCondition n) initMs
    (Htransform : VMPromisingExecutionTransforms bbm isem term initMs) :
  VMPromisingFinalStateEquiv bbm isem term initMs.
Proof.
  exact (promise_first_equiv_from_execution_transforms
    (VMPromising.VMPromising bbm) isem term initMs Htransform).
Qed.
