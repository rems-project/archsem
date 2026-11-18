(******************************************************************************)
(* Successful transitions of the VM runner with per-thread enumeration caches *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstSailVMCacheSim.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
Module VMEnumCacheSteps.
Import VMPromising.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis Memory.t.
Section Cache.
Context (bbm : bool) {n : nat} (isem : iMon ()) (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation pfstate := (@CPState.pf_t prom n).

Definition effective fuel (pst : pfstate) :=
  let st := CPState.pstate prom pst in
  vimap (λ tid ts, if CPState.enum_cache prom pst !!! tid is Some res then res else
    CPState.enumerate_results isem prom term tid (PState.initmem st) fuel ts (PState.events st))
    (PState.tstates st).

Definition advance fuel (pst : pfstate) ev next :=
  CPState.PFMake prom next (vimap (λ tid res, if Ev.affects ev tid then None else Some res)
    (effective fuel pst)).

Lemma none_inv fuel (pst pst' : pfstate) :
  Exec.elem_of_results (pst', None) (CPState.run_transition_promise_first isem prom term fuel pst) →
  ∃ (tid : fin n) ev next,
    ev ∈ prom.(Promising.filter_promises) n tid (PState.events (CPState.pstate prom pst))
      (CPState.promises prom (effective fuel pst !!! tid)) ∧
    PState.promise prom ev (CPState.pstate prom pst) = Ok next ∧
    pst' = advance fuel pst ev next.
Proof.
  unfold CPState.run_transition_promise_first. intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as (pst0 & read & Hget & Hrest).
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  fold (effective fuel pst) in Hrest.
  apply Exec.elem_of_bind_elim in Hrest as (pst1 & opt & Hopt & Hbranch).
  apply Exec.elem_of_mchoosel_inv in Hopt as [-> Hopt].
  destruct opt as [|[|[|opt]]]; cbn beta iota zeta in Hbranch.
  - apply Exec.elem_of_bind_elim in Hbranch as (pst2 & tid & Htid & Hrest).
    apply Exec.elem_of_mchoosel_inv in Htid as [-> _].
    apply Exec.elem_of_bind_elim in Hrest as (pst3 & ev & Hev & Hrest).
    apply Exec.elem_of_lift_res_inv in Hev as [-> Hev].
    unfold CPState.choose_promise in Hev. apply Exec.elem_of_res_mchoosel_inv in Hev.
    apply Exec.elem_of_bind_elim in Hrest as (pst4 & next & Hpromise & Hrest).
    apply Exec.elem_of_lift_res_inv in Hpromise as [-> Hpromise].
    apply PromiseFirstCurrent.lift_result_res_success in Hpromise.
    apply Exec.elem_of_bind_elim in Hrest as (pst5 & u & Hset & Hret).
    destruct u. apply Exec.elem_of_mSetv_inv in Hset. subst pst5.
    apply Exec.elem_of_mret_inv in Hret as [Hreturned _].
    exists tid, ev, next. split; [exact Hev|]. split; [exact Hpromise|exact Hreturned].
  - apply Exec.elem_of_bind_elim in Hbranch as (pst2 & states & Hstates & Hrest).
    apply Exec.elem_of_bind_elim in Hrest as (pst3 & pt & Hguard & Hrest).
    apply Exec.elem_of_bind_elim in Hrest as (pst4 & u & Hvalidate & Hret).
    apply Exec.elem_of_mret_inv in Hret as [_ Hsome]. discriminate.
  - apply Exec.elem_of_bind_elim in Hbranch as (pst2 & err & Herr & Hthrow).
    inversion Hthrow.
  - match type of Hbranch with context [if ?b then _ else _] => destruct b end;
      inversion Hbranch.
Qed.

Lemma validate_result (st : state) :
  Exec.elem_of_results () (CPState.validate_final prom st) →
  Exec.elem_of_results (st, ()) (CPState.validate_final_state prom st st).
Proof.
  unfold CPState.validate_final. intro H.
  apply Exec.elem_of_res_bind_elim in H as [pt [Hguard Htail]].
  apply VMCacheSimOutcome.validate_final_state_intro; [exact pt|].
  destruct (CPState.check_valid_end prom st) as [|err errs]; [reflexivity|].
  apply Exec.elem_of_res_bind_elim in Htail as [e [_ Hthrow]]. inversion Hthrow.
Qed.

Lemma some_inv fuel (pst pst' : pfstate) fsig :
  Exec.elem_of_results (pst', Some fsig) (CPState.run_transition_promise_first isem prom term fuel pst) →
  ∃ (states : vec TState.t n)
    (pt : CPState.terminated prom term (PState.Make states
      (PState.initmem (CPState.pstate prom pst)) (PState.events (CPState.pstate prom pst)))),
    (∀ tid, states !!! tid ∈ CPState.final_states prom (effective fuel pst !!! tid)) ∧
    Exec.elem_of_results () (CPState.validate_final prom (PState.Make states
      (PState.initmem (CPState.pstate prom pst)) (PState.events (CPState.pstate prom pst)))) ∧
    fsig = CPState.to_final_archState (CPState.make_final prom term _ pt).
Proof.
  intro Hrun. unfold CPState.run_transition_promise_first in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as (p0 & read & Hget & Hrun).
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  fold (effective fuel pst) in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as (p1 & opt & Hopt & Hbranch).
  apply Exec.elem_of_mchoosel_inv in Hopt as [-> Hopt].
  destruct opt as [|[|[|opt]]]; cbn beta iota zeta in Hbranch.
  - repeat match type of Hbranch with Exec.elem_of_results _ ((_ ≫= _) _) =>
      apply Exec.elem_of_bind_elim in Hbranch as (? & ? & ? & Hbranch) end.
    apply Exec.elem_of_mret_inv in Hbranch as [_ Hnone]. discriminate.
  - apply Exec.elem_of_bind_elim in Hbranch as (p2 & states & Hstates & Hbranch).
    apply Exec.elem_of_mchoosel_inv in Hstates as [-> Hstates].
    apply Exec.elem_of_bind_elim in Hbranch as (p3 & pt & Hguard & Hbranch).
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hbranch as (p4 & u & Hvalid & Hret).
    destruct u. apply Exec.elem_of_lift_res_inv in Hvalid as [-> Hvalid].
    apply Exec.elem_of_mret_inv in Hret as [_ Hsome]. injection Hsome as Hsig. subst fsig.
    exists states, pt. split; [|auto].
    intro tid. pose proof (proj1 (cprodn_spec _ states) Hstates tid) as Hin.
    rewrite vlookup_map in Hin. exact Hin.
  - apply Exec.elem_of_bind_elim in Hbranch as (p2 & err & Herr & Hthrow). inversion Hthrow.
  - match type of Hbranch with context [if ?b then _ else _] => destruct b end; inversion Hbranch.
Qed.

Lemma cached_promise fuel (pst : pfstate) (tid : fin n) ev next :
  ev ∈ prom.(Promising.filter_promises) n tid (PState.events (CPState.pstate prom pst))
    (CPState.promises prom (effective fuel pst !!! tid)) →
  PState.promise prom ev (CPState.pstate prom pst) = Ok next →
  Exec.elem_of_results (advance fuel pst ev next, None)
    (CPState.run_transition_promise_first isem prom term fuel pst).
Proof.
  intros Hin Hpromise. unfold CPState.run_transition_promise_first.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  eapply Exec.elem_of_bind_intro with (a := 0%nat);
    [apply Exec.elem_of_mchoosel; cbn; set_solver|].
  eapply Exec.elem_of_bind_intro with (a := tid);
    [apply Exec.elem_of_mchoosel, Exec.elem_of_fin_enum|].
  eapply Exec.elem_of_bind_intro with (a := ev).
  { apply Exec.elem_of_lift_res. unfold CPState.choose_promise.
    apply Exec.elem_of_res_mchoosel. exact Hin. }
  eapply Exec.elem_of_bind_intro with (a := next).
  { apply (proj2 (PromiseFirstCurrent.lift_result_success _ _ _ _)). auto. }
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mSetv|apply Exec.elem_of_mret].
Qed.

Lemma cached_batch fuel (pst : pfstate) (states : vec TState.t n)
    (pt : CPState.terminated prom term (PState.Make states (PState.initmem (CPState.pstate prom pst))
      (PState.events (CPState.pstate prom pst)))) :
  (∀ tid, states !!! tid ∈ CPState.final_states prom (effective fuel pst !!! tid)) →
  Exec.elem_of_results () (CPState.validate_final prom (PState.Make states
    (PState.initmem (CPState.pstate prom pst)) (PState.events (CPState.pstate prom pst)))) →
  Exec.elem_of_results (pst, Some (CPState.to_final_archState (CPState.make_final prom term _ pt)))
    (CPState.run_transition_promise_first isem prom term fuel pst).
Proof.
  intros Hfinal Hvalid. unfold CPState.run_transition_promise_first.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  eapply Exec.elem_of_bind_intro with (a := 1%nat);
    [apply Exec.elem_of_mchoosel; cbn; set_solver|].
  eapply Exec.elem_of_bind_intro with (a := states).
  { apply Exec.elem_of_mchoosel, (proj2 (cprodn_spec _ _)).
    intro tid. rewrite vlookup_map. apply Hfinal. }
  destruct (Exec.elem_of_guard_discard (E := string) pst pt) as [pt' Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_lift_res, Hvalid|].
  replace pt' with pt by apply proof_irrelevance. apply Exec.elem_of_mret.
Qed.
End Cache.
End VMEnumCacheSteps.
