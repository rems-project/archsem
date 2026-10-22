(******************************************************************************)
(* Fuel bounds for completed sail-tiny-arm certifications *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Local Opaque sail_tiny_arm_sem.
#[local] Existing Instance Promising.mEvent_eq_dec.

Section Certification.
Context (prom : Promising.Model) (nondet : bool) {n : nat}
  (term : terminationCondition n) (tid : fin n) (initmem : memoryMap).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation ppState :=
  (PPState.t prom.(Promising.tState) prom.(Promising.mEvent) prom.(Promising.iis)).

Lemma completed_certification_more_fuel fuel fuel' base proms (ppst : ppState)
    proms' ppst' ending :
  fuel ≤ fuel' → ending ≠ CPState.OutOfFuel →
  Exec.elem_of_results ((proms', ppst'), ending)
    (CPState.run_to_termination isem prom term tid initmem fuel base (proms, ppst)) →
  Exec.elem_of_results ((proms', ppst'), ending)
    (CPState.run_to_termination isem prom term tid initmem fuel' base (proms, ppst)).
Proof.
  revert fuel' proms ppst proms' ppst' ending.
  induction fuel as [|fuel IH]; intros [|fuel'] proms [ts mem iis]
    proms' ppst' ending Hfuel Hending Hrun; try lia.
  all: cbn [CPState.run_to_termination] in Hrun |- *.
  all: apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  all: apply Exec.elem_of_mget_inv in Hget as [-> ->].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  all: cbn -[CPState.terminated_ts] in Hrun |- *.
  all: destruct (decide (base < prom.(Promising.tState_min_new_prom_view) ts));
    [exact Hrun|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
    rewrite Hterm in Hrun |- *; [exact Hrun|].
  - exact Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [_ Heq]. contradiction.
  - apply Exec.elem_of_bind_elim in Hrun as [reset [[] [Hreset Hrun]]].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_bind_elim in Hrun as [[proms_mid pp_mid] [[] [Hinst Htail]]].
    eapply Exec.elem_of_bind_intro; [exact Hinst|].
    eapply IH; [lia|exact Hending|exact Htail].
Qed.

Lemma final_candidate_more_fuel fuel fuel' ts mem ts' :
  fuel ≤ fuel' →
  ts' ∈ (CPState.enumerate_results isem prom term tid initmem fuel ts mem)
    .(CPState.final_states prom) →
  ts' ∈ (CPState.enumerate_results isem prom term tid initmem fuel' ts mem)
    .(CPState.final_states prom).
Proof.
  intros Hfuel Hcandidate.
  apply (proj1 (enumerate_results_final_state_witness isem term tid
    initmem fuel ts mem ts')) in Hcandidate.
  destruct Hcandidate as [ppst [Hstate Hrun]].
  apply (proj2 (enumerate_results_final_state_witness isem term tid
    initmem fuel' ts mem ts')).
  exists ppst. split; [exact Hstate|].
  eapply completed_certification_more_fuel; [exact Hfuel|discriminate|exact Hrun].
Qed.

(** Extending a truncated exploration preserves its exact state and collected
    promises at the splice. The continuation keeps the original base. *)
Lemma out_of_fuel_certification_continue fuel extra base proms (ppst : ppState)
    proms_mid ppst_mid proms' ppst' ending :
  Exec.elem_of_results ((proms_mid, ppst_mid), CPState.OutOfFuel)
    (CPState.run_to_termination isem prom term tid initmem fuel base (proms, ppst)) →
  Exec.elem_of_results ((proms', ppst'), ending)
    (CPState.run_to_termination isem prom term tid initmem extra base
      (proms_mid, ppst_mid)) →
  Exec.elem_of_results ((proms', ppst'), ending)
    (CPState.run_to_termination isem prom term tid initmem (fuel + extra) base
      (proms, ppst)).
Proof.
  revert proms ppst.
  induction fuel as [|fuel IH]; intros proms [ts mem iis] Hprefix Hsuffix.
  - cbn [CPState.run_to_termination] in Hprefix.
    apply Exec.elem_of_bind_elim in Hprefix as [mid [ts0 [Hget Hprefix]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    cbn -[CPState.terminated_ts] in Hprefix.
    destruct (decide (base < prom.(Promising.tState_min_new_prom_view) ts)).
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
      rewrite Hterm in Hprefix.
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    apply Exec.elem_of_mret_inv in Hprefix as [Heq _].
    injection Heq as <- <-. exact Hsuffix.
  - cbn [CPState.run_to_termination] in Hprefix |- *.
    apply Exec.elem_of_bind_elim in Hprefix as [mid [ts0 [Hget Hprefix]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn -[CPState.terminated_ts] in Hprefix |- *.
    destruct (decide (base < prom.(Promising.tState_min_new_prom_view) ts)).
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
      rewrite Hterm in Hprefix |- *.
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    apply Exec.elem_of_bind_elim in Hprefix as [reset [[] [Hreset Hprefix]]].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_bind_elim in Hprefix
      as [[proms_next ppst_next] [[] [Hinst Hprefix]]].
    eapply Exec.elem_of_bind_intro; [exact Hinst|].
    eapply IH; eassumption.
Qed.
End Certification.

Definition StablePromiseCandidate (prom : Promising.Model) (nondet : bool)
    {n} (term : terminationCondition n) (tid : fin n) initmem ts mem ev : Prop :=
  ∃ threshold, ∀ fuel, threshold ≤ fuel →
    ev ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) prom term tid
      initmem fuel ts mem).(CPState.promises prom).

Definition FilterRetainsMembership (prom : Promising.Model) : Prop :=
  ∀ n tid mem xs ys ev,
    ev ∈ prom.(Promising.filter_promises) n tid mem xs → ev ∈ ys →
    ev ∈ prom.(Promising.filter_promises) n tid mem ys.

Lemma UM_filter_retains_membership : FilterRetainsMembership UMPromising.
Proof. intros n tid mem xs ys ev _ Hin. exact Hin. Qed.
Lemma VM_filter_retains_membership bbm :
  FilterRetainsMembership (VMPromising.VMPromising bbm).
Proof.
  intros n tid mem xs ys ev Haccept Hin.
  cbn [Promising.filter_promises VMPromising.VMPromising] in *.
  unfold VMPromising.filter_tlbi_promises in *.
  destruct mem as [|prev mem]; [exact Hin|].
  destruct (Ev.get_tlbi_recipient prev); [|exact Hin].
  apply list_elem_of_filter in Haccept as [Hpred _].
  apply list_elem_of_filter. split; assumption.
Qed.

Lemma collected_promise_in_raw_candidates prom nondet {n}
    (term : terminationCondition n) (tid : fin n) initmem fuel ts mem ev proms ppst ending :
  ev ∈ proms →
  Exec.elem_of_results ((proms, ppst), ending)
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) prom term tid initmem
      fuel (length mem) ([], PPState.Make ts mem prom.(Promising.iis_init))) →
  let res := CPState.run_to_termination (sail_tiny_arm_sem nondet) prom term tid initmem
      fuel (length mem) ([], PPState.Make ts mem prom.(Promising.iis_init)) in
  ev ∈ remove_dups (List.concat
    ((Exec.success_state_list res).*1 ++ (Exec.errors res).*1.*1)).
Proof.
  intros Hev Hrun. apply elem_of_remove_dups.
  apply list_elem_of_In, List.in_concat. exists proms. split.
  - apply list_elem_of_In, elem_of_app. left.
    apply list_elem_of_fmap. exists (proms, ppst). split; [reflexivity|].
    unfold Exec.success_state_list.
    apply list_elem_of_fmap. exists ((proms, ppst), ending). split; [reflexivity|exact Hrun].
  - apply list_elem_of_In. exact Hev.
Qed.

(** A candidate with a completed certification path persists at every larger
    fuel. OutOfFuel paths are deliberately excluded: their extension remains
    a separate Sail execution obligation. *)
Lemma completed_candidate_is_stable prom nondet {n}
    (term : terminationCondition n) (tid : fin n) initmem fuel ts mem ev proms ppst ending :
  FilterRetainsMembership prom →
  ev ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) prom term tid initmem
    fuel ts mem).(CPState.promises prom) →
  ev ∈ proms → ending ≠ CPState.OutOfFuel →
  Exec.elem_of_results ((proms, ppst), ending)
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) prom term tid initmem
      fuel (length mem) ([], PPState.Make ts mem prom.(Promising.iis_init))) →
  StablePromiseCandidate prom nondet term tid initmem ts mem ev.
Proof.
  intros Hfilter Haccept Hev Hend Hrun.
  exists fuel. intros fuel' Hfuel.
  unfold CPState.enumerate_results in Haccept |- *. cbn in Haccept |- *.
  eapply Hfilter; [exact Haccept|].
  eapply collected_promise_in_raw_candidates; [exact Hev|].
  eapply completed_certification_more_fuel; eassumption.
Qed.

(** Error branches are retained by enumeration and are stable at larger fuel. *)
Lemma exec_res_error_bind {E A B} (err : E) (e : Exec.res E A) (k : A → Exec.res E B) :
  err ∈ Exec.errors (e ≫= k) ↔
    err ∈ Exec.errors e ∨ ∃ a, a ∈ Exec.results e ∧ err ∈ Exec.errors (k a).
Proof.
  destruct e as [rs es]. unfold mbind, Exec.res_mbind_inst.
  cbn. induction rs as [|a rs IH].
  - cbn. set_solver.
  - cbn [map foldr]. unfold Exec.merge. cbn [Exec.errors Exec.results].
    split.
    + intros H. apply elem_of_app in H as [H|H].
      * right. exists a. split; [apply elem_of_cons; left; reflexivity|exact H].
      * apply IH in H as [H|[b [Hb Hk]]]; [left; exact H|].
        right. exists b. split; [apply elem_of_cons; right; exact Hb|exact Hk].
    + intros [H|[b [Hb Hk]]].
      * apply elem_of_app. right. apply IH. left. exact H.
      * apply elem_of_cons in Hb as [->|Hb].
        -- apply elem_of_app. left. exact Hk.
        -- apply elem_of_app. right. apply IH. right. exists b. split; assumption.
Qed.

Lemma exec_error_bind {St E A B} (err : St * E)
    (e : Exec.t St E A) (k : A → Exec.t St E B) st :
  err ∈ Exec.errors ((e ≫= k) st) ↔
    err ∈ Exec.errors (e st) ∨ ∃ mid a,
      Exec.elem_of_results (mid, a) (e st) ∧ err ∈ Exec.errors (k a mid).
Proof.
  change (err ∈ Exec.errors ((e st) ≫= (λ '(mid, a), k a mid)) ↔
    err ∈ Exec.errors (e st) ∨ ∃ mid a,
      Exec.elem_of_results (mid, a) (e st) ∧ err ∈ Exec.errors (k a mid)).
  split.
  - intros H. apply exec_res_error_bind in H as [H|[[mid a] [Hin Herr]]]; [left; exact H|].
    right. exists mid, a. split; assumption.
  - intro H. apply exec_res_error_bind.
    destruct H as [H|[mid [a [Hin Herr]]]]; [left; exact H|].
    right. exists (mid, a). split; assumption.
Qed.

Lemma failed_certification_more_fuel prom nondet {n}
    (term : terminationCondition n) (tid : fin n) initmem fuel fuel' base proms ppst
    proms' ppst' err :
  fuel ≤ fuel' →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) prom term tid initmem
      fuel base (proms, ppst)) →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) prom term tid initmem
      fuel' base (proms, ppst)).
Proof.
  revert fuel' proms ppst.
  induction fuel as [|fuel IH]; intros [|fuel'] proms [ts mem iis] Hfuel Hrun; try lia.
  all: cbn [CPState.run_to_termination] in Hrun |- *.
  all: apply exec_error_bind in Hrun as [Hbad|[mid [ts0 [Hget Hrun]]]];
    [change (((proms', ppst'), err) ∈ []) in Hbad; inversion Hbad|].
  all: apply Exec.elem_of_mget_inv in Hget as [-> ->].
  all: apply exec_error_bind; right;
    eexists (proms, PPState.Make ts mem iis), ts; split;
    [exact (Exec.elem_of_mget (proms, PPState.Make ts mem iis) (PPState.state ∘ snd))|].
  all: cbn -[CPState.terminated_ts] in Hrun |- *.
  all: destruct (decide (base < prom.(Promising.tState_min_new_prom_view) ts));
    [exact Hrun|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
    rewrite Hterm in Hrun |- *; [exact Hrun|].
  - exact Hrun.
  - change (((proms', ppst'), err) ∈ []) in Hrun. inversion Hrun.
  - apply exec_error_bind in Hrun as [Hbad|[reset [[] [Hreset Hrun]]]];
      [change (((proms', ppst'), err) ∈ []) in Hbad; inversion Hbad|].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply exec_error_bind; right. eexists _, (). split; [apply Exec.elem_of_mset|].
    apply exec_error_bind in Hrun as [Hbad|[[proms_mid pp_mid] [[] [Hinst Htail]]]].
    + apply exec_error_bind. left. exact Hbad.
    + apply exec_error_bind. right. exists (proms_mid, pp_mid), (). split; [exact Hinst|].
      apply IH; [lia|exact Htail].
Qed.

Lemma failed_candidate_is_stable prom nondet {n}
    (term : terminationCondition n) (tid : fin n) initmem fuel ts mem ev proms ppst err :
  FilterRetainsMembership prom →
  ev ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) prom term tid initmem
    fuel ts mem).(CPState.promises prom) →
  ev ∈ proms →
  ((proms, ppst), err) ∈ Exec.errors
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) prom term tid initmem
      fuel (length mem) ([], PPState.Make ts mem prom.(Promising.iis_init))) →
  StablePromiseCandidate prom nondet term tid initmem ts mem ev.
Proof.
  intros Hfilter Haccept Hev Hrun. exists fuel. intros fuel' Hfuel.
  unfold CPState.enumerate_results in Haccept |- *. cbn in Haccept |- *.
  eapply Hfilter; [exact Haccept|].
  apply elem_of_remove_dups, list_elem_of_In, List.in_concat. exists proms. split.
  - apply list_elem_of_In, elem_of_app. right.
    apply list_elem_of_fmap. exists (proms, ppst). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((proms, ppst), err). split; [reflexivity|].
    eapply failed_certification_more_fuel; eassumption.
  - apply list_elem_of_In. exact Hev.
Qed.

(** Every remaining fuel-stability obligation has an OutOfFuel witness. *)
Lemma candidate_stable_or_out_of_fuel prom nondet {n}
    (term : terminationCondition n) (tid : fin n) initmem fuel ts mem ev :
  (∀ candidates event,
    event ∈ prom.(Promising.filter_promises) n tid mem candidates → event ∈ candidates) →
  FilterRetainsMembership prom →
  ev ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) prom term tid initmem
    fuel ts mem).(CPState.promises prom) →
  StablePromiseCandidate prom nondet term tid initmem ts mem ev ∨
  ∃ proms ppst, ev ∈ proms ∧ Exec.elem_of_results ((proms, ppst), CPState.OutOfFuel)
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) prom term tid initmem
      fuel (length mem) ([], PPState.Make ts mem prom.(Promising.iis_init))).
Proof.
  intros Hsubset Hfilter Hcandidate.
  destruct (enumerate_results_promise_witness (sail_tiny_arm_sem nondet)
    term tid initmem fuel ts mem ev Hsubset Hcandidate)
    as [proms [ppst [Hev [[ending Hrun]|[err Hrun]]]]].
  - destruct ending.
    + left. eapply completed_candidate_is_stable with (ending := CPState.Terminated);
        [exact Hfilter|exact Hcandidate|exact Hev|discriminate|exact Hrun].
    + right. exists proms, ppst. split; assumption.
    + left. eapply completed_candidate_is_stable with (ending := CPState.StoppedEarly);
        [exact Hfilter|exact Hcandidate|exact Hev|discriminate|exact Hrun].
  - left. eapply failed_candidate_is_stable; eassumption.
Qed.

Lemma out_of_fuel_certification_flag prom nondet {n}
    (term : terminationCondition n) (tid : fin n) initmem fuel ts mem proms ppst :
  Exec.elem_of_results ((proms, ppst), CPState.OutOfFuel)
    (CPState.run_to_termination (sail_tiny_arm_sem nondet) prom term tid initmem
      fuel (length mem) ([], PPState.Make ts mem prom.(Promising.iis_init))) →
  (CPState.enumerate_results (sail_tiny_arm_sem nondet) prom term tid initmem
    fuel ts mem).(CPState.out_of_fuel prom) = true.
Proof.
  intro Hrun. unfold CPState.enumerate_results. cbn.
  apply bool_decide_eq_true_2. exists CPState.OutOfFuel. split; [|exact I].
  apply list_elem_of_fmap. exists ((proms, ppst), CPState.OutOfFuel).
  split; [reflexivity|exact Hrun].
Qed.

Lemma fully_explored_candidate_is_stable prom nondet {n}
    (term : terminationCondition n) (tid : fin n) initmem fuel ts mem ev :
  (∀ candidates event,
    event ∈ prom.(Promising.filter_promises) n tid mem candidates → event ∈ candidates) →
  FilterRetainsMembership prom →
  (CPState.enumerate_results (sail_tiny_arm_sem nondet) prom term tid initmem
    fuel ts mem).(CPState.out_of_fuel prom) = false →
  ev ∈ (CPState.enumerate_results (sail_tiny_arm_sem nondet) prom term tid initmem
    fuel ts mem).(CPState.promises prom) →
  StablePromiseCandidate prom nondet term tid initmem ts mem ev.
Proof.
  intros Hsubset Hfilter Hcomplete Hcandidate.
  destruct (candidate_stable_or_out_of_fuel prom nondet term tid initmem fuel ts mem ev
    Hsubset Hfilter Hcandidate) as [Hstable|[proms [ppst [_ Hrun]]]]; [exact Hstable|].
  pose proof (out_of_fuel_certification_flag prom nondet term tid initmem fuel ts mem
    proms ppst Hrun) as Hflag. congruence.
Qed.
