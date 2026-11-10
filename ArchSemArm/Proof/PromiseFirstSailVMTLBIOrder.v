(******************************************************************************)
(* The epoch filter admits DSB-separated broadcast TLBIs *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstSailNoFuel PromiseFirstSailSerialization.
Open Scope stdpp.
Open Scope bv.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis.

Module VMSailTLBIOrder.

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
Definition event0 := Ev.Tlbi (TLBI.All 0) 0 0.
Definition event1 := Ev.Tlbi (TLBI.All 0) 1 0.
Definition fallback := TState.make [] [] ∅ [] ∅ ∅
  0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat ∅ None 0%nat None.
Definition init_ps : PState.t TState.t Ev.t 2 :=
  match PState.from_archState prom initial with
  | Ok st => st | Error _ => PState.Make [# fallback; fallback] imem [] end.
Definition issue ev (st : PState.t TState.t Ev.t 2) :=
  match PState.promise prom ev st with Ok next => next | Error _ => st end.
Definition event0_next := Ev.Tlbi (TLBI.All 0) 0 1.
Definition event1_next := Ev.Tlbi (TLBI.All 0) 1 1.

Lemma initialization : PState.from_archState prom initial = Ok init_ps.
Proof.
  assert (Hok : (match PState.from_archState prom initial with
    | Ok _ => true | Error _ => false end) = true) by (vm_compute; reflexivity).
  unfold init_ps. destruct (PState.from_archState prom initial); [reflexivity|discriminate].
Qed.

Lemma epoch_filter_keeps_second_zero :
  event0_next ∈ filter_commuting_promises 2 0 [event1; event0]
    [event1_next; event0_next].
Proof. vm_compute. right; left; reflexivity. Qed.

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
Local Lemma thread_cases (tid : fin 2) : tid = 0%fin ∨ tid = 1%fin.
Proof.
  inv_fin tid; [left; reflexivity|]. intro tid. inv_fin tid;
    [right; reflexivity|intro tid; inv_fin tid].
Qed.

Lemma direct_searches_complete :
  CertificationCompleteAt prom false term 4%nat init_ps ∧
  CertificationCompleteAt prom false term 3%nat after_first ∧
  CertificationCompleteAt prom false term 2%nat after_dsb.
Proof.
  repeat split; intro tid; destruct (thread_cases tid) as [Htid | Htid]; subst tid; vm_compute; reflexivity.
Qed.

Lemma direct_terminated : CPState.terminated prom term direct_final.
Proof. vm_compute; exact I. Qed.
Lemma direct_valid : Exec.elem_of_results (direct_final, ())
  (CPState.validate_final_state prom direct_final direct_final).
Proof.
  assert (Hnone : CPState.nopromises prom direct_final) by (vm_compute; exact I).
  assert (Hvalid : CPState.check_valid_end prom direct_final = []) by (vm_compute; reflexivity).
  unfold CPState.validate_final_state. rewrite Hvalid.
  destruct (Exec.elem_of_guard_discard (E := string) direct_final Hnone) as [pt Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|apply Exec.elem_of_mret].
Qed.
Definition direct_result := CPState.to_final_archState
  (CPState.make_final prom term direct_final direct_terminated).

Lemma direct_history :
  PState.events direct_final = [event1_next; event0_next; event1; event0].
Proof. vm_compute; reflexivity. Qed.

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

Definition cached_initial := CPState.PFMake prom init_ps (vreplicate 2 None).

Definition cached_results fuel (pst : CPState.pf_t prom (n := 2)) :=
  let st := CPState.pstate prom pst in
  vimap (λ tid ts, if CPState.enum_cache prom pst !!! tid is Some res then res
    else CPState.enumerate_results isem prom term tid (PState.initmem st)
      fuel ts (PState.events st)) (PState.tstates st).
Definition cached_issue fuel ev (pst : CPState.pf_t prom (n := 2)) :=
  CPState.PFMake prom (issue ev (CPState.pstate prom pst))
    (vimap (λ tid res, if Ev.affects ev tid then None else Some res)
      (cached_results fuel pst)).
Definition c0 := cached_issue 7 event0 cached_initial.
Definition c01 := cached_issue 6 event1 c0.
Definition c010 := cached_issue 5 event0_next c01.
Definition c0101 := cached_issue 4 event1_next c010.

Lemma cached_promise_step fuel ev pst :
  ev ∈ filter_commuting_promises 2 0 (PState.events (CPState.pstate prom pst))
    (CPState.promises prom (cached_results fuel pst !!! 0%fin)) →
  PState.promise prom ev (CPState.pstate prom pst) = Ok (issue ev (CPState.pstate prom pst)) →
  Exec.elem_of_results (cached_issue fuel ev pst, None)
    (CPState.run_transition_promise_first isem prom term fuel pst).
Proof.
  intros Hcandidate Hpromise. unfold CPState.run_transition_promise_first.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  eapply Exec.elem_of_bind_intro with (a := 0%nat);
    [apply Exec.elem_of_mchoosel; cbn; set_solver|].
  eapply Exec.elem_of_bind_intro with (a := 0%fin).
  { unfold mchoosef. apply Exec.elem_of_mchoosel. apply Exec.elem_of_fin_enum. }
  eapply Exec.elem_of_bind_intro with (a := ev).
  { apply Exec.elem_of_lift_res. unfold CPState.choose_promise.
    apply Exec.elem_of_res_mchoosel. exact Hcandidate. }
  eapply Exec.elem_of_bind_intro with (a := issue ev (CPState.pstate prom pst)).
  { apply (proj2 (PromiseFirstCurrent.lift_result_success _ _ _ _)). auto. }
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mSetv|apply Exec.elem_of_mret].
Qed.

Local Ltac compute_candidate :=
  match goal with |- ?P => apply (bool_decide_eq_true_1 P) end; vm_compute; reflexivity.
Local Ltac compute_issue :=
  unfold issue; match goal with |- ?p = _ =>
    let H := fresh in assert (H : (match p with Ok _ => true | Error _ => false end) = true)
      by (vm_compute; reflexivity);
    destruct p; [reflexivity|discriminate]
  end.

Lemma cached_prefix :
  Exec.elem_of_results (c0, None)
    (CPState.run_transition_promise_first isem prom term 7 cached_initial) ∧
  Exec.elem_of_results (c01, None)
    (CPState.run_transition_promise_first isem prom term 6 c0) ∧
  Exec.elem_of_results (c010, None)
    (CPState.run_transition_promise_first isem prom term 5 c01) ∧
  Exec.elem_of_results (c0101, None)
    (CPState.run_transition_promise_first isem prom term 4 c010).
Proof.
  split.
  - apply (cached_promise_step 7 event0 cached_initial); [compute_candidate|compute_issue].
  - split.
    + apply (cached_promise_step 6 event1 c0); [compute_candidate|compute_issue].
    + split.
      * apply (cached_promise_step 5 event0_next c01); [compute_candidate|compute_issue].
      * apply (cached_promise_step 4 event1_next c010); [compute_candidate|compute_issue].
Qed.

Lemma cached_final_step : ∃ next fsig, Exec.elem_of_results (next, Some fsig)
    (CPState.run_transition_promise_first isem prom term 3 c0101).
Proof.
  assert (H : List.existsb (λ p, if p.2 is Some _ then true else false)
    (Exec.results (CPState.run_transition_promise_first isem prom term 3 c0101)) = true)
    by (vm_compute; reflexivity).
  apply List.existsb_exists in H as [[next [fsig|]] [Hin H]]; [|discriminate].
  exists next, fsig. apply list_elem_of_In. exact Hin.
Qed.

(** Each local search is evaluated separately; the runner proof follows the
    four selected promises and the final batch without enumerating all paths. *)
Theorem cached_runner_has_final : ∃ returned fsig,
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel_pf isem prom 2) 7 term initial cached_initial).
Proof.
  destruct cached_prefix as [H0 [H1 [H2 H3]]].
  destruct cached_final_step as [next [fsig Hfinal]].
  exists next, fsig. cbn [opModel.run].
  eapply Exec.elem_of_bind_intro; [exact H0|].
  eapply Exec.elem_of_bind_intro; [exact H1|].
  eapply Exec.elem_of_bind_intro; [exact H2|].
  eapply Exec.elem_of_bind_intro; [exact H3|].
  eapply Exec.elem_of_bind_intro; [exact Hfinal|apply Exec.elem_of_mret].
Qed.

End VMSailTLBIOrder.
