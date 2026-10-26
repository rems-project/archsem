(******************************************************************************)
(* A Sail VM counterexample to unrestricted direct-to-promise-first inclusion *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstSailNoFuel PromiseFirstSailSerialization.
Open Scope stdpp.
Open Scope bv.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis.

Module VMSailTLBIOrder.

Local Lemma ok_injective {E A} (x y : A) : @Ok E A x = Ok y → x = y.
Proof. injection 1. trivial. Qed.

(** Two VMALLE1IS instructions separated by DSB ISH. Thread 1 is already
    terminated but remains a broadcast recipient. Translation is enabled,
    BBM validation is disabled, and the program performs no memory writes. *)
Definition regs : registerMap :=
  ∅ |> reg_insert _PC 0x3000
    |> reg_insert SCTLR_EL1 1 |> reg_insert TCR_EL1 0
    |> reg_insert TTBR0_EL1 0 |> reg_insert ID_AA64MMFR1_EL1 0
    |> reg_insert CurrentEL 1.
Definition imem : memoryMap :=
  ∅ |> mem_insert 0 8 4099 |> mem_insert 4096 8 1025
    |> mem_insert 0x3000 4 0xd508831f |> mem_insert 0x3004 4 0xd5033b9f |> mem_insert 0x3008 4 0xd508831f.
Definition initial : archState 2 :=
  {| archState.regs := [# regs; regs |> reg_insert _PC 0x300c]; archState.memory := imem;
     archState.address_space := PAS_NonSecure |}.
Definition term : terminationCondition 2 := [# [0x300c]; [0x300c]].
Definition prom := VMPromising false.
#[local] Typeclasses Transparent prom.
Definition isem := sail_tiny_arm_sem false.
Definition event0 := Ev.Tlbi (TLBI.All 0) 0.
Definition event1 := Ev.Tlbi (TLBI.All 0) 1.
Definition fallback := TState.make [] [] ∅ [] ∅ ∅
  0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat ∅ None None.
Definition init_ps : PState.t TState.t Ev.t 2 :=
  match PState.from_archState prom initial with
  | Ok st => st | Error _ => PState.Make [# fallback; fallback] imem [] end.
Definition issue ev (st : PState.t TState.t Ev.t 2) :=
  match PState.promise prom ev st with Ok next => next | Error _ => st end.
Definition p0 := issue event0 init_ps.
Definition p1 := issue event1 init_ps.
Definition p01 := issue event1 p0.
Definition p011 := issue event1 p01.

Inductive Stage := Initial | First0 | First1 | FirstBoth | Second1.
Definition at_stage (stage : Stage) :=
  match stage with
  | Initial => init_ps | First0 => p0 | First1 => p1
  | FirstBoth => p01 | Second1 => p011
  end.
Definition height (stage : Stage) : nat :=
  match stage with Initial => 3 | First0 => 2 | FirstBoth => 1 | _ => 0 end.
Definition allowed (stage : Stage) : list Ev.t :=
  match stage with
  | Initial => [event1; event0]
  | First0 | FirstBoth => [event1]
  | _ => []
  end.
Definition enumerate fuel tid (stage : Stage) :=
  let st := at_stage stage in
  CPState.enumerate_results isem prom term tid
    (PState.initmem st) fuel (PState.tstate tid st) (PState.events st).

Lemma initialization : PState.from_archState prom initial = Ok init_ps.
Proof.
  assert (Hok : (match PState.from_archState prom initial with
    | Ok _ => true | Error _ => false end) = true) by (vm_compute; reflexivity).
  unfold init_ps. destruct (PState.from_archState prom initial); [reflexivity|discriminate].
Qed.

Lemma issue_succeeds ev st :
  (match PState.promise prom ev st with Ok _ => true | Error _ => false end) = true →
  PState.promise prom ev st = Ok (issue ev st).
Proof. unfold issue. destruct (PState.promise prom ev st); [reflexivity|discriminate]. Qed.

Lemma next_stage stage (ev : Ev.t) : ev ∈ allowed stage →
  ∃ next, PState.promise prom ev (at_stage stage) = Ok (at_stage next) ∧
    (height next < height stage)%nat.
Proof.
  destruct stage; cbn [allowed]; intro Hin.
  - apply elem_of_cons in Hin as [->|Hin].
    + exists First1. split; [apply issue_succeeds; vm_compute; reflexivity|cbn; lia].
    + apply list_elem_of_singleton in Hin. subst ev.
      exists First0. split; [apply issue_succeeds; vm_compute; reflexivity|cbn; lia].
  - apply list_elem_of_singleton in Hin. subst ev.
    exists FirstBoth. split; [apply issue_succeeds; vm_compute; reflexivity|cbn; lia].
  - inversion Hin.
  - apply list_elem_of_singleton in Hin. subst ev.
    exists Second1. split; [apply issue_succeeds; vm_compute; reflexivity|cbn; lia].
  - inversion Hin.
Qed.

(** The complete searches contain no final state for the active thread.
    The two terminal prefix states contain no further candidate either. *)
Lemma complete_search_shape stage :
  (enumerate 3 0%fin stage).(CPState.promises prom) = allowed stage ∧
  (enumerate 3 0%fin stage).(CPState.final_states prom) = [] ∧
  (enumerate 3 0%fin stage).(CPState.errors prom) = [] ∧
  (enumerate 3 0%fin stage).(CPState.out_of_fuel prom) = false.
Proof. destruct stage; vm_compute; repeat split; reflexivity. Qed.

(** Both recipients of the second instruction are found by certification.
    The production filter removes recipient 0 because the preceding promise
    went to recipient 1, despite that promise belonging to the first TLBI. *)
Lemma second_tlbi_raw_candidates :
  let search := CPState.run_to_termination isem prom term 0%fin
    (PState.initmem p01) 3 (length (PState.events p01))
    ([], PPState.Make (PState.tstate 0%fin p01) (PState.events p01) IIS.init) in
  remove_dups (List.concat ((Exec.success_state_list search).*1 ++
    (Exec.errors search).*1.*1)) = [event1; event0].
Proof. vm_compute; reflexivity. Qed.

Lemma recipient_filter_discards_second_zero :
  filter_tlbi_promises 2 0 [event1; event0] [event1; event0] = [event1].
Proof. vm_compute; reflexivity. Qed.

Lemma searches_complete stage : CertificationCompleteAt prom false term 3%nat (at_stage stage).
Proof.
  intro tid. inv_fin tid.
  - exact (proj2 (proj2 (proj2 (complete_search_shape stage)))).
  - intro tid. inv_fin tid.
    + destruct stage; vm_compute; reflexivity.
    + intro tid. inv_fin tid.
Qed.

(** Short searches are checked separately: candidate lists extracted from a
    truncated search need not be monotone in fuel in the general runner. *)
Lemma short_search_shape fuel stage : (fuel ≤ 2)%nat →
  bool_decide ((enumerate fuel 0%fin stage).(CPState.promises prom) ⊆ allowed stage) = true ∧
  (enumerate fuel 0%fin stage).(CPState.final_states prom) = [].
Proof.
  destruct fuel as [|[|[|fuel]]]; intro Hfuel; [..|lia];
    destruct stage; vm_compute; split; reflexivity.
Qed.

Lemma active_search_shape fuel stage :
  (enumerate fuel 0%fin stage).(CPState.promises prom) ⊆ allowed stage ∧
  (enumerate fuel 0%fin stage).(CPState.final_states prom) = [].
Proof.
  destruct (decide (fuel ≤ 2)%nat) as [Hsmall|Hlarge].
  - destruct (short_search_shape fuel stage Hsmall) as [Hproms Hfinal].
    split; [exact (bool_decide_eq_true_1 _ Hproms)|exact Hfinal].
  - unfold enumerate.
    rewrite <- (complete_enumeration_fuel_irrelevant prom isem term 0%fin
      (PState.initmem (at_stage stage)) 3 fuel (PState.tstate 0%fin (at_stage stage))
      (PState.events (at_stage stage)) ltac:(lia) (searches_complete stage 0%fin)).
    change ((enumerate 3 0%fin stage).(CPState.promises prom) ⊆ allowed stage ∧
      (enumerate 3 0%fin stage).(CPState.final_states prom) = []).
    destruct (complete_search_shape stage) as [Hproms [Hfinal _]].
    rewrite Hproms, Hfinal. split; [reflexivity|reflexivity].
Qed.

Lemma inactive_search_empty fuel stage :
  (enumerate fuel 1%fin stage).(CPState.promises prom) = [].
Proof. destruct fuel as [|fuel]; destruct stage; vm_compute; reflexivity. Qed.

Local Lemma thread_cases (tid : fin 2) : tid = 0%fin ∨ tid = 1%fin.
Proof.
  inv_fin tid; [left; reflexivity|]. intro tid. inv_fin tid;
    [right; reflexivity|intro tid; inv_fin tid].
Qed.

Local Opaque at_stage initial init_ps p0 p1 p01 p011 isem term prom.

(** This invariant covers every successful promise-first transition, at every
    fuel, including short and incomplete certification searches. *)
Lemma transition_closed fuel stage next res :
  Exec.elem_of_results (next, res)
    (CPState.run_transition_promise_first isem prom term fuel (at_stage stage)) →
  res = None ∧ ∃ next_stage, next = at_stage next_stage ∧
    (height next_stage < height stage)%nat.
Proof.
  intro Hstep. destruct res as [fsig|].
  - destruct (run_transition_promise_first_some_inv (prom := prom) isem term fuel
      (at_stage stage) next fsig Hstep) as [states [final [pt [_ [Hstates _]]]]].
    specialize (Hstates 0%fin). rewrite promise_first_execution_results_lookup in Hstates.
    change (states !!! 0%fin ∈ (enumerate fuel 0%fin stage).(CPState.final_states prom)) in Hstates.
    rewrite (proj2 (active_search_shape fuel stage)) in Hstates. inversion Hstates.
  - split; [reflexivity|].
    destruct (run_transition_promise_first_none_inv (prom := prom) isem term fuel
      (at_stage stage) next Hstep) as [tid [ev [nst [Hcandidate [Hpromise Hnext]]]]].
    rewrite promise_first_execution_results_lookup in Hcandidate.
    change (ev ∈ (enumerate fuel tid stage).(CPState.promises prom)) in Hcandidate.
    assert (Hallowed : ev ∈ allowed stage).
    { destruct (thread_cases tid) as [Htid | Htid]; subst tid.
      - exact (proj1 (active_search_shape fuel stage) ev Hcandidate).
      - rewrite inactive_search_empty in Hcandidate. inversion Hcandidate. }
    destruct (next_stage stage ev Hallowed) as [s [Hemit Hheight]].
    rewrite Hemit in Hpromise. injection Hpromise as Heq. subst nst.
    exists s. auto.
Qed.

Theorem no_promise_first_run fuel stage returned fsig :
  ¬ Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom 2) fuel term initial (at_stage stage)).
Proof.
  revert stage. induction fuel as [|fuel IH]; intros stage Hrun.
  - cbn [opModel.run] in Hrun. change ((returned, fsig) ∈ []) in Hrun. inversion Hrun.
  - cbn [opModel.run] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [next [res [Hstep Htail]]].
    destruct (transition_closed (S fuel) stage next res Hstep) as [-> [s [-> _]]].
    exact (IH s Htail).
Qed.

(** With at least six runner steps, every search on every reachable prefix
    is complete. There are at most three promise transitions, and each local
    search is complete at fuel three. No terminating result exists even with
    this unbounded family of complete searches. *)
Theorem all_searches_complete fuel stage :
  (3 + height stage ≤ fuel)%nat →
  PromiseFirstSearchesComplete prom false term fuel (at_stage stage).
Proof.
  revert stage. induction fuel as [|fuel IH]; intros stage Hfuel; [lia|].
  split.
  - eapply certification_complete_more_fuel; [|apply searches_complete]. lia.
  - intros next Hstep.
    destruct (transition_closed (S fuel) stage next None Hstep) as [_ [s [-> Hheight]]].
    apply IH. lia.
Qed.

Local Transparent at_stage initial init_ps p0 p1 p01 p011 isem term prom.

Definition execute (st : PState.t TState.t Ev.t 2) :=
  match Exec.results (PState.run_tid isem prom 0%fin st) with
  | (next, ()) :: _ => next | [] => st
  end.
Definition after_first := execute init_ps.
Definition after_dsb := execute after_first.
Definition direct_final := execute after_dsb.

Local Lemma execute_success st :
  length (Exec.results (PState.run_tid isem prom 0%fin st)) = 1%nat →
  Exec.elem_of_results (execute st, ()) (PState.run_tid isem prom 0%fin st).
Proof.
  unfold execute.
  destruct (Exec.results (PState.run_tid isem prom 0%fin st)) as [|[next []] rest] eqn:Hresults;
    [discriminate|]. intro Hcount.
  unfold Exec.elem_of_results. rewrite Hresults. left; reflexivity.
Qed.

Lemma direct_instructions :
  InstructionTransition prom false term init_ps after_first ∧
  InstructionTransition prom false term after_first after_dsb ∧
  InstructionTransition prom false term after_dsb direct_final.
Proof.
  split.
  - exists 0%fin. split; [vm_compute; reflexivity|].
    apply execute_success; vm_compute; reflexivity.
  - split.
    + exists 0%fin. split; [vm_compute; reflexivity|].
      apply execute_success; vm_compute; reflexivity.
    + exists 0%fin. split; [vm_compute; reflexivity|].
      apply execute_success; vm_compute; reflexivity.
Qed.

(** These are the certification budgets used by the direct runner along
    the three-instruction witness below. The final step only validates. *)
Lemma direct_searches_complete :
  CertificationCompleteAt prom false term 4%nat init_ps ∧
  CertificationCompleteAt prom false term 3%nat after_first ∧
  CertificationCompleteAt prom false term 2%nat after_dsb.
Proof.
  repeat split; intro tid; destruct (thread_cases tid) as [Htid | Htid]; subst tid;
    vm_compute; reflexivity.
Qed.

Lemma direct_terminated : CPState.terminated prom term direct_final.
Proof. vm_compute; exact I. Qed.
Lemma direct_valid : Exec.elem_of_results (direct_final, ())
  (CPState.validate_final prom direct_final direct_final).
Proof.
  assert (Hnone : CPState.nopromises prom direct_final) by (vm_compute; exact I).
  assert (Hvalid : CPState.check_valid_end prom direct_final = []) by (vm_compute; reflexivity).
  unfold CPState.validate_final. rewrite Hvalid.
  destruct (Exec.elem_of_guard_discard (E := string) direct_final Hnone) as [pt Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|apply Exec.elem_of_mret].
Qed.
Definition direct_result := CPState.to_final_archState
  (CPState.make_final prom term direct_final direct_terminated).

(** The memory history contains only broadcast invalidations. In particular,
    every code byte is unchanged, including the fetched instructions. *)
Lemma direct_history :
  PState.events direct_final = [event1; event0; event1; event0].
Proof. vm_compute; reflexivity. Qed.
Lemma direct_history_preserves_all_code (code : code_region) :
  no_self_modifying_history VMPromisingReadByte code (PState.events direct_final).
Proof.
  rewrite direct_history. intros ev Hin.
  assert (Hev : ev = event0 ∨ ev = event1) by set_solver.
  destruct Hev as [Hev | Hev]; subst ev; intros addr Hcode; reflexivity.
Qed.

Local Opaque init_ps after_first after_dsb direct_final isem term prom.

(** The direct runner executes the three actual Sail instructions and
    validates termination in four transitions, with complete searches. *)
Lemma direct_run : Exec.elem_of_results (direct_final, direct_result)
  (opModel.run (@CPState.opmodel isem prom 2) 4 term initial init_ps).
Proof.
  destruct direct_instructions as [Hfirst [Hdsb Hsecond]].
  cbn [opModel.run].
  eapply Exec.elem_of_bind_intro with (st' := after_first) (a := None).
  - exact (instruction_transition_any_fuel prom false term 4 init_ps after_first Hfirst).
  - eapply Exec.elem_of_bind_intro with (st' := after_dsb) (a := None).
    + exact (instruction_transition_any_fuel prom false term 3 after_first after_dsb Hdsb).
    + eapply Exec.elem_of_bind_intro with (st' := direct_final) (a := None).
      * exact (instruction_transition_any_fuel prom false term 2 after_dsb direct_final Hsecond).
      * eapply Exec.elem_of_bind_intro.
        -- exact (run_transition_some_intro (prom := prom) isem term 1
             direct_final direct_final direct_terminated direct_valid).
        -- apply Exec.elem_of_mret.
Qed.

Lemma direct_has_result : ∃ returned fsig,
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem prom 2) 4 term initial init_ps).
Proof. exists direct_final, direct_result. exact direct_run. Qed.

Theorem direct_without_promise_first : ∃ returned fsig,
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem prom 2) 4 term initial init_ps) ∧
  ∀ fuel pf_returned,
    ¬ Exec.elem_of_results (pf_returned, fsig)
      (opModel.run (@CPState.opmodel_pf isem prom 2) fuel term initial init_ps).
Proof.
  destruct direct_has_result as [returned [fsig Hrun]].
  exists returned, fsig. split; [exact Hrun|].
  intros fuel pf_returned. exact (no_promise_first_run fuel Initial pf_returned fsig).
Qed.

Local Opaque initial.

(** The contradiction is at the architectural model boundary, so it is
    observable even though TLB and promise metadata are erased there. *)
Theorem architectural_counterexample :
  ∃ fs (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈ Promising_to_Modelc prom isem 4 2%nat term initial ∧
    ∀ fuel, archModel.Res.FinalState fs pt ∉ Promising_to_Modelc_pf prom isem fuel 2%nat term initial.
Proof.
  destruct direct_has_result as [returned [[fs pt] Hrun]].
  exists fs, pt. split.
  - exact (direct_final_state_intro (prom := prom) isem term initial 4
      init_ps initialization returned fs pt Hrun).
  - intros fuel Hpf.
    destruct (promise_first_final_state_inv (prom := prom) isem term initial fuel fs pt Hpf)
      as [start [Hinit [pf_returned [fsig [Hpf_run _]]]]].
    rewrite initialization in Hinit. apply ok_injective in Hinit. subst start.
    exact (no_promise_first_run fuel Initial pf_returned fsig Hpf_run).
Qed.

Corollary complete_searches_do_not_restore_inclusion :
  (∀ fuel, (6 ≤ fuel)%nat →
    PromiseFirstSearchesComplete prom false term fuel init_ps) ∧
  ∃ returned fsig,
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel isem prom 2) 4 term initial init_ps) ∧
    ∀ fuel pf_returned, ¬ Exec.elem_of_results (pf_returned, fsig)
      (opModel.run (@CPState.opmodel_pf isem prom 2) fuel term initial init_ps).
Proof.
  split; [|exact direct_without_promise_first].
  intros fuel Hfuel. exact (all_searches_complete fuel Initial Hfuel).
Qed.

End VMSailTLBIOrder.
