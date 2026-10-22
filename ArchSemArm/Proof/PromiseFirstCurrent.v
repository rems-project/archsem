(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst.

#[local] Open Scope nat.
#[local] Open Scope stdpp.

(** Facts about the current result-valued promising interface.  Success
    premises retain the failure checks in initialization and promise emission. *)
Module PromiseFirstCurrent.

Lemma lift_result_success {St E A} (st st' : St) (a : A)
    (r : result E A) :
  Exec.elem_of_results (st', a) ((mlift r : Exec.t St E A) st) ↔
  st' = st ∧ r = Ok a.
Proof.
  destruct r; unfold Exec.elem_of_results; cbn; set_solver.
Qed.

Lemma lift_result_res_success {E A} (a : A) (r : result E A) :
  Exec.elem_of_results a (mlift r : Exec.res E A) ↔ r = Ok a.
Proof.
  destruct r; unfold Exec.elem_of_results; cbn; set_solver.
Qed.

Lemma vimapM_result_lookup {A B E n} (xs : vec A n)
    (f : fin n → A → result E B) (ys : vec B n) :
  vimapM f xs = Ok ys →
  ∀ i, f i (xs !!! i) = Ok (ys !!! i).
Proof.
  revert f ys.
  induction xs as [|x n xs IH]; intros f ys Hmap i.
  - inversion i.
  - cbn in Hmap.
    destruct (f 0%fin x) as [y|e] eqn:Hy; [|discriminate].
    destruct (vimapM (f ∘ FS) xs) as [zs|e] eqn:Hzs;
      [|discriminate].
    cbn in Hmap. inversion Hmap; subst ys.
    dependent destruction i.
    + exact Hy.
    + exact (IH _ _ Hzs i).
Qed.

Section States.
Context (prom : Promising.Model) {n : nat}.
Local Notation state := (PState.t prom.(Promising.tState) prom.(Promising.mEvent) n).

Lemma promise_success (ev : prom.(Promising.mEvent)) (st st' : state) :
  PState.promise prom ev st = Ok st' →
  PState.initmem st' = PState.initmem st ∧
  PState.events st' = ev :: PState.events st ∧
  ∀ (tid : fin n),
    prom.(Promising.emit_promise) (tid : nat) (PState.initmem st)
      (ev :: PState.events st) ev (PState.tstate tid st) =
    Ok (PState.tstate tid st').
Proof.
  destruct st as [ts imem mem].
  unfold PState.promise; cbn.
  destruct (vimapM
    (λ tid s, Promising.emit_promise prom tid imem (ev :: mem) ev s) ts)
    as [ts'|err] eqn:Hmap; [|discriminate].
  cbn. intro H; inversion H; subst st'; clear H.
  split; [reflexivity|]. split; [reflexivity|].
  pose proof (vimapM_result_lookup ts
    (λ tid s, Promising.emit_promise prom (tid : nat) imem (ev :: mem) ev s)
    ts' Hmap) as Hlookup.
  exact Hlookup.
Qed.

Lemma initialization_success (ms : archState n) (st : state) :
  PState.from_archState prom ms = Ok st →
  PState.initmem st = archState.memory ms ∧
  PState.events st = [] ∧
  ∀ (tid : fin n), prom.(Promising.tState_init) (tid : nat) (archState.memory ms)
    (archState.regs ms !!! tid) = Ok (PState.tstate tid st).
Proof.
  unfold PState.from_archState.
  destruct (vimapM
    (λ tid rm, Promising.tState_init prom tid (archState.memory ms) rm)
    (archState.regs ms)) as [ts|err] eqn:Hmap; [|discriminate].
  cbn. intro H; inversion H; subst st; clear H.
  split; [reflexivity|]. split; [reflexivity|].
  pose proof (vimapM_result_lookup (archState.regs ms)
    (λ tid rm, Promising.tState_init prom (tid : nat)
      (archState.memory ms) rm)
    ts Hmap) as Hlookup.
  exact Hlookup.
Qed.
End States.

End PromiseFirstCurrent.

(** A code region is immutable along a promising history when every event in
    that history leaves every byte in the region unreadable as a write.  The
    predicate is intentionally parameterized by the event reader so that the
    UM and VM event types use the same statement. *)
Definition code_region := address → Prop.

Definition event_misses_code {ev : Type}
    (read_byte : address → ev → option (bv 8))
    (code : code_region) (event : ev) : Prop :=
  ∀ addr, code addr → read_byte addr event = None.

Definition no_self_modifying_history {ev : Type}
    (read_byte : address → ev → option (bv 8))
    (code : code_region) (events : list ev) : Prop :=
  ∀ event, event ∈ events → event_misses_code read_byte code event.

(** The vector enumerated by one promise-first transition.  Naming this
    expression makes the successful branch usable without unfolding a large
    [let] expression at every call site. *)
Definition promise_first_execution_results
    {prom : Promising.Model} (isem : iMon ()) {n : nat}
    (term : terminationCondition n) (fuel : nat)
    (st : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n) :
    vec (CPState.EnumerationResult prom) n :=
  vmap (λ '(tid, ts),
      CPState.enumerate_results isem prom term tid
        (CPState.initmem st) fuel ts (CPState.events st))
    (venumerate (CPState.tstates st)).

Lemma promise_first_execution_results_lookup
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st : PState.t prom.(Promising.tState)
      prom.(Promising.mEvent) n) (tid : fin n) :
  promise_first_execution_results isem term fuel st !!! tid =
  CPState.enumerate_results isem prom term tid
    (CPState.initmem st) fuel (PState.tstate tid st)
    (CPState.events st).
Proof.
  unfold promise_first_execution_results.
  rewrite vlookup_map.
  rewrite lookup_fun_to_vec.
  cbn.
  reflexivity.
Qed.

(** A terminated thread is enumerated as a final state once the early-stop
    guard has been discharged.  The guard is part of the current executable
    model, so the lower-bound premise is explicit in this statement. *)
Lemma run_to_termination_terminated_initial
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (fuel base : nat)
    (ppst : PPState.t prom.(Promising.tState)
      prom.(Promising.mEvent) prom.(Promising.iis)) :
  (prom.(Promising.tState_min_new_prom_view)
      (PPState.state ppst) <= base)%nat →
  CPState.terminated_ts prom (term !!! tid) (PPState.state ppst) = true →
  Exec.elem_of_results (([], ppst), CPState.Terminated)
    ((@CPState.run_to_termination isem prom n term tid initmem
        fuel base) ([], ppst)).
Proof.
  intros Hbase Hterm.
  destruct fuel as [|fuel].
  - cbn.
    eapply Exec.elem_of_bind_intro.
    + apply Exec.elem_of_mget.
    + destruct (decide
          (base < prom.(Promising.tState_min_new_prom_view)
             (PPState.state ppst))) as [Hlt|Hnlt].
      * exfalso. lia.
      * rewrite (decide_False _ _ Hnlt).
        rewrite Hterm.
        apply Exec.elem_of_mret.
  - cbn.
    eapply Exec.elem_of_bind_intro.
    + apply Exec.elem_of_mget.
    + destruct (decide
          (base < prom.(Promising.tState_min_new_prom_view)
             (PPState.state ppst))) as [Hlt|Hnlt].
      * exfalso. lia.
      * rewrite (decide_False _ _ Hnlt).
        rewrite Hterm.
        apply Exec.elem_of_mret.
Qed.

Lemma enumerate_results_terminated_final_state
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (fuel : nat) (ts : prom.(Promising.tState))
    (mem : PromMemory.t prom.(Promising.mEvent)) :
  (prom.(Promising.tState_min_new_prom_view) ts <= length mem)%nat →
  CPState.terminated_ts prom (term !!! tid) ts = true →
  ts ∈ (CPState.enumerate_results isem prom term tid initmem fuel ts mem).(CPState.final_states prom).
Proof.
  intros Hbase Hterm.
  unfold CPState.enumerate_results.
  set (ppst := PPState.Make ts mem prom.(Promising.iis_init)).
  set (res := (@CPState.run_to_termination isem prom n term tid initmem
    fuel (length mem)) ([], ppst)).
  assert (Hrun : Exec.elem_of_results (([], ppst), CPState.Terminated) res).
  {
    subst res.
    apply run_to_termination_terminated_initial.
    - exact Hbase.
    - exact Hterm.
  }
  cbn.
  apply list_elem_of_omap.
  exists (([], ppst), CPState.Terminated).
  split; [exact Hrun|].
  cbn.
  reflexivity.
Qed.

(** A final-state candidate comes from a terminated exploration with an empty
    collected-promise list.  In particular, OutOfFuel and StoppedEarly do not
    provide final-state witnesses. *)
Lemma enumerate_results_final_state_witness
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) fuel ts mem ts' :
  ts' ∈ (CPState.enumerate_results isem prom term tid initmem fuel ts mem)
    .(CPState.final_states prom) ↔
  ∃ ppst,
    PPState.state ppst = ts' ∧
    Exec.elem_of_results (([], ppst), CPState.Terminated)
      (CPState.run_to_termination isem prom term tid initmem fuel (length mem)
        ([], PPState.Make ts mem prom.(Promising.iis_init))).
Proof.
  unfold CPState.enumerate_results. cbn.
  split.
  - intro Hin. apply list_elem_of_omap in Hin.
    destruct Hin as [[[new_proms ppst] ending] [Hrun Hstate]].
    destruct ending; [|discriminate|discriminate].
    destruct new_proms; [|discriminate].
    cbn in Hstate. inversion Hstate; subst.
    exists ppst. split; [reflexivity|exact Hrun].
  - intros [ppst [Hstate Hrun]].
    apply list_elem_of_omap.
    exists (([], ppst), CPState.Terminated).
    split; [exact Hrun|]. cbn. f_equal. exact Hstate.
Qed.

(** Promise filtering may remove candidates, but must not invent events.  Each
    retained candidate has an exploration witness, which may end in an error. *)
Lemma enumerate_results_promise_witness
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) fuel ts mem ev :
  (∀ candidates event,
    event ∈ prom.(Promising.filter_promises) n tid mem candidates →
    event ∈ candidates) →
  ev ∈ (CPState.enumerate_results isem prom term tid initmem fuel ts mem)
    .(CPState.promises prom) →
  ∃ new_proms ppst,
    ev ∈ new_proms ∧
    ((∃ ending, Exec.elem_of_results ((new_proms, ppst), ending)
      (CPState.run_to_termination isem prom term tid initmem fuel (length mem)
        ([], PPState.Make ts mem prom.(Promising.iis_init)))) ∨
     (∃ err, ((new_proms, ppst), err) ∈ Exec.errors
      (CPState.run_to_termination isem prom term tid initmem fuel (length mem)
        ([], PPState.Make ts mem prom.(Promising.iis_init))))).
Proof.
  intros Hfilter Hin.
  unfold CPState.enumerate_results in Hin.
  cbn in Hin.
  apply Hfilter in Hin.
  apply elem_of_remove_dups in Hin.
  apply list_elem_of_In in Hin.
  apply List.in_concat in Hin as [new_proms [Hsource Hev]].
  apply list_elem_of_In in Hsource.
  apply list_elem_of_In in Hev.
  apply elem_of_app in Hsource as [Hsource|Hsource].
  - apply list_elem_of_fmap in Hsource as [[new_proms' ppst] [Heq Hsource]].
    cbn in Heq. subst new_proms'.
    unfold Exec.success_state_list in Hsource.
    apply list_elem_of_fmap in Hsource as [[pair ending] [Heq Hrun]].
    cbn in Heq. subst pair.
    exists new_proms, ppst. split; [exact Hev|].
    left. exists ending. exact Hrun.
  - apply list_elem_of_fmap in Hsource as [[new_proms' ppst] [Heq Hsource]].
    cbn in Heq. subst new_proms'.
    apply list_elem_of_fmap in Hsource as [[pair err] [Heq Hrun]].
    cbn in Heq. subst pair.
    exists new_proms, ppst. split; [exact Hev|].
    right. exists err. exact Hrun.
Qed.

Lemma enumerate_results_terminated_promises
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) fuel ts mem :
  CPState.terminated_ts prom (term !!! tid) ts = true →
  (CPState.enumerate_results isem prom term tid initmem fuel ts mem)
    .(CPState.promises prom) =
  prom.(Promising.filter_promises) n tid mem [].
Proof.
  intro Hterm.
  unfold CPState.enumerate_results.
  destruct fuel; cbn [CPState.run_to_termination];
    unfold mget, mGet, mcall, mbind, fmap,
      Exec.mbind_inst, Exec.fmap_inst, Exec.st_call_MState,
      Exec.res_mbind_inst, Exec.res_fmap_inst;
    cbn -[CPState.terminated_ts];
    rewrite Hterm;
    destruct (decide (length mem < prom.(Promising.tState_min_new_prom_view) ts)%nat);
    reflexivity.
Qed.

Lemma no_self_modifying_history_cons {ev : Type}
    (read_byte : address → ev → option (bv 8)) code event events :
  event_misses_code read_byte code event →
  no_self_modifying_history read_byte code events →
  no_self_modifying_history read_byte code (event :: events).
Proof.
  intros Hevent Hhistory event' Hevent'.
  apply elem_of_cons in Hevent' as [->|Hevent']; [exact Hevent|].
  apply Hhistory.
  exact Hevent'.
Qed.

Lemma no_self_modifying_history_nil {ev : Type}
    (read_byte : address → ev → option (bv 8)) (code : code_region) :
  no_self_modifying_history read_byte code [] .
Proof.
  intros event Hmem.
  inversion Hmem.
Qed.

Lemma no_self_modifying_history_app {ev : Type}
    (read_byte : address → ev → option (bv 8)) code events1 events2 :
  no_self_modifying_history read_byte code events1 →
  no_self_modifying_history read_byte code events2 →
  no_self_modifying_history read_byte code (events1 ++ events2).
Proof.
  intros H1 H2 event Hmem.
  apply elem_of_app in Hmem as [Hmem|Hmem].
  - apply H1. exact Hmem.
  - apply H2. exact Hmem.
Qed.

(** Membership conversion for the current result-valued executable model.  The
    lemma exposes the successful execution witness hidden by
    [archModel.Res.from_exec]. *)
Lemma final_state_from_exec_inv {St : Type} {n : nat}
    {term : terminationCondition n}
    (e : Exec.t St string {s & archState.is_terminated term s})
    st fs pt :
  archModel.Res.FinalState fs pt ∈ archModel.Res.from_exec e st →
  ∃ st' fsig,
    Exec.elem_of_results (st', fsig) (e st) ∧
    projT1 fsig = fs.
Proof.
  unfold archModel.Res.from_exec.
  unfold elem_of, listset_elem_of.
  cbn.
  intro Hin.
  rewrite list_elem_of_fmap in Hin.
  destruct Hin as [res [Hres Hin]].
  destruct res as [fsig|err].
  - rewrite list_elem_of_fmap in Hin.
    destruct Hin as [[st' res] [Hres_snd Hin]].
    cbn in Hres_snd.
    subst res.
    unfold Exec.to_stateful_result_list in Hin.
    destruct (e st) as [rs es] eqn:Heq.
    cbn in Hin.
    apply elem_of_app in Hin as [Hin|Hin].
    + rewrite list_elem_of_fmap in Hin.
      destruct Hin as [[st0 fsig0] [Heq_pair Hin]].
      inversion Heq_pair; subst st0 fsig0.
      exists st', fsig.
      split.
      * unfold elem_of, Exec.elem_of_results.
        exact Hin.
      * destruct fsig as [fs0 pt0].
        cbn in Hres |- *.
        inversion Hres.
        reflexivity.
    + rewrite list_elem_of_fmap in Hin.
      destruct Hin as [[st_err err0] [Heq_pair _]].
      inversion Heq_pair.
  - cbn in Hres.
    inversion Hres.
Qed.

Lemma final_state_from_exec_intro {St : Type} {n : nat}
    {term : terminationCondition n}
    (e : Exec.t St string {s & archState.is_terminated term s})
    st st' fs pt :
  Exec.elem_of_results
    (st', existT (P := archState.is_terminated term) fs pt) (e st) →
  archModel.Res.FinalState fs pt ∈ archModel.Res.from_exec e st.
Proof.
  unfold archModel.Res.from_exec.
  unfold elem_of, listset_elem_of.
  cbn.
  intro Hrun.
  rewrite list_elem_of_fmap.
  exists (Ok (existT (P := archState.is_terminated term) fs pt)).
  split; [reflexivity|].
  rewrite list_elem_of_fmap.
  exists (st', Ok (existT (P := archState.is_terminated term) fs pt)).
  split; [reflexivity|].
  unfold Exec.to_stateful_result_list.
  destruct (e st) as [rs es] eqn:Heq.
  cbn.
  apply elem_of_app.
  left.
  rewrite list_elem_of_fmap.
  exists (st', existT (P := archState.is_terminated term) fs pt).
  split; [reflexivity|].
  unfold elem_of, Exec.elem_of_results in Hrun.
  exact Hrun.
Qed.

Lemma direct_final_state_inv {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n)
    (fuel : nat) (fs : archState n) (pt : archState.is_terminated term fs) :
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc prom isem fuel n term initMs →
  ∃ initPs, PState.from_archState prom initMs = Ok initPs ∧
    ∃ st' fsig,
      Exec.elem_of_results (st', fsig)
        ((opModel.run (@CPState.opmodel isem prom n) fuel term initMs) initPs) ∧
      projT1 fsig = fs.
Proof.
  unfold Promising_to_Modelc, opModel.to_archModel.
  cbn.
  destruct (PState.from_archState prom initMs) as [initPs|err] eqn:Hinit.
  - intro Hfinal.
    destruct
      (final_state_from_exec_inv
         (opModel.run (@CPState.opmodel isem prom n) fuel term initMs)
         initPs fs pt Hfinal) as [st' [fsig [Hrun Hfs]]].
    exists initPs. split; [reflexivity|].
    exists st', fsig. split; [exact Hrun|exact Hfs].
  - intro Hfinal.
    set_unfold in Hfinal.
    inversion Hfinal.
Qed.

Lemma direct_final_state_intro {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n)
    (fuel : nat) (initPs : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (Hinit : PState.from_archState prom initMs = Ok initPs)
    (st' : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n)
    (fs : archState n) (pt : archState.is_terminated term fs) :
  Exec.elem_of_results
      (st', existT (P := archState.is_terminated term) fs pt)
      ((opModel.run (@CPState.opmodel isem prom n) fuel term initMs) initPs) →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc prom isem fuel n term initMs.
Proof.
  unfold Promising_to_Modelc, opModel.to_archModel.
  cbn.
  rewrite Hinit.
  apply final_state_from_exec_intro.
Qed.

Lemma promise_first_final_state_inv {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n)
    (fuel : nat) (fs : archState n) (pt : archState.is_terminated term fs) :
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc_pf prom isem fuel n term initMs →
  ∃ initPs, PState.from_archState prom initMs = Ok initPs ∧
    ∃ st' fsig,
      Exec.elem_of_results (st', fsig)
        ((opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs) initPs) ∧
      projT1 fsig = fs.
Proof.
  unfold Promising_to_Modelc_pf, opModel.to_archModel.
  cbn.
  destruct (PState.from_archState prom initMs) as [initPs|err] eqn:Hinit.
  - intro Hfinal.
    destruct
      (final_state_from_exec_inv
         (opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs)
         initPs fs pt Hfinal) as [st' [fsig [Hrun Hfs]]].
    exists initPs. split; [reflexivity|].
    exists st', fsig. split; [exact Hrun|exact Hfs].
  - intro Hfinal.
    set_unfold in Hfinal.
    inversion Hfinal.
Qed.

Lemma promise_first_final_state_intro {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (initMs : archState n)
    (fuel : nat) (initPs : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (Hinit : PState.from_archState prom initMs = Ok initPs)
    (st' : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n)
    (fs : archState n) (pt : archState.is_terminated term fs) :
  Exec.elem_of_results
      (st', existT (P := archState.is_terminated term) fs pt)
      ((opModel.run (@CPState.opmodel_pf isem prom n) fuel term initMs) initPs) →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc_pf prom isem fuel n term initMs.
Proof.
  unfold Promising_to_Modelc_pf, opModel.to_archModel.
  cbn.
  rewrite Hinit.
  apply final_state_from_exec_intro.
Qed.

(** A successful [Some] result of the direct transition can only come from
    the final branch.  Keeping this inversion lemma next to the result-set
    lemmas makes the current result-valued runner usable by the concrete
    execution transformation proof. *)
Lemma run_transition_some_inv {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (fsig : {s & archState.is_terminated term s}) :
  Exec.elem_of_results (st', Some fsig)
    ((@CPState.run_transition isem prom n term fuel) st) →
  ∃ (pt : CPState.terminated prom term st),
    Exec.elem_of_results (st', ())
      ((CPState.validate_final prom st) st) ∧
    fsig = CPState.to_final_archState
      (CPState.make_final prom term st pt).
Proof.
  unfold CPState.run_transition.
  intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [st0 [st0' [Hget Hbranch]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  destruct (decide (CPState.terminated prom term st)) as [pt|Hnot].
  - cbn in Hbranch.
    apply Exec.elem_of_bind_elim in Hbranch as [st1 [u [Hvalidate Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> Hfinal].
    inversion Hfinal; subst fsig.
    destruct u.
    exists pt. split; [exact Hvalidate|reflexivity].
  - cbn in Hbranch.
    apply Exec.elem_of_bind_elim in Hbranch as [st1 [u [Hstep Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [_ Hnone].
    discriminate Hnone.
Qed.

Lemma run_transition_some_intro {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (pt : CPState.terminated prom term st)
    (Hvalidate : Exec.elem_of_results (st', ())
      ((CPState.validate_final prom st) st)) :
  Exec.elem_of_results
    (st', Some (CPState.to_final_archState
      (CPState.make_final prom term st pt)))
    ((@CPState.run_transition isem prom n term fuel) st).
Proof.
  unfold CPState.run_transition.
  eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
  - apply Exec.elem_of_mGet.
  - destruct (decide (CPState.terminated prom term st)) as [pt'|Hnot].
    + eapply Exec.elem_of_bind_intro with (st' := st') (a := tt).
      * exact Hvalidate.
      * assert (pt' = pt) by apply proof_irrelevance.
        subst pt'.
        apply Exec.elem_of_mret.
    + exfalso.
      exact (Hnot pt).
Qed.

Lemma run_transition_none_inv {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) :
  Exec.elem_of_results (st', None)
    ((@CPState.run_transition isem prom n term fuel) st) →
  ∃ st_step,
    Exec.elem_of_results (st_step, ())
      ((@CPState.run_step isem prom n term fuel) st) ∧
    st' = st_step.
Proof.
  unfold CPState.run_transition.
  intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [st0 [st0' [Hget Hbranch]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  destruct (decide (CPState.terminated prom term st)) as [pt|Hnot].
  - cbn in Hbranch.
    apply Exec.elem_of_bind_elim in Hbranch as [st1 [u [Hvalidate Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [_ Hsome].
    discriminate Hsome.
  - cbn in Hbranch.
    apply Exec.elem_of_bind_elim in Hbranch as [st_step [u [Hstep Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> Hnone].
    destruct u.
    exists st_step.
    split; [exact Hstep|reflexivity].
Qed.

Lemma cpromise_tid_inv {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat) (tid : fin n)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) :
  Exec.elem_of_results (st', ())
    ((@CPState.cpromise_tid isem prom n term fuel tid) st) →
  ∃ ev nst,
    Exec.elem_of_results ev
      (@CPState.promise_select_tid isem prom n term fuel st tid) ∧
    PState.promise prom ev st = Ok nst ∧
    st' = nst.
Proof.
  unfold CPState.cpromise_tid.
  intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [st0 [st0' [Hget Htail]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Htail as [st_ev [ev [Hev Htail]]].
  apply Exec.elem_of_lift_res_inv in Hev as [-> Hev].
  apply Exec.elem_of_bind_elim in Htail as [st_nst [nst [Hpromise Hset]]].
  apply Exec.elem_of_lift_res_inv in Hpromise as [-> Hpromise].
  apply PromiseFirstCurrent.lift_result_res_success in Hpromise as Hpromise.
  apply Exec.elem_of_mSetv_inv in Hset as ->.
  exists ev, nst.
  repeat split; try assumption.
Qed.

Lemma promise_select_tid_inv {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st : PState.t prom.(Promising.tState)
      prom.(Promising.mEvent) n) (tid : fin n) ev :
  Exec.elem_of_results ev
    (@CPState.promise_select_tid isem prom n term fuel st tid) →
  ev ∈ (CPState.enumerate_results isem prom term tid
          (CPState.initmem st) fuel (PState.tstate tid st)
          (PState.events st)).(CPState.promises prom).
Proof.
  unfold CPState.promise_select_tid.
  destruct (CPState.enumerate_results isem prom term tid
      (CPState.initmem st) fuel (PState.tstate tid st)
      (PState.events st))
    as [promises final_states errors out_of_fuel] eqn:Henum.
  destruct out_of_fuel.
  - intro Hin.
    apply Exec.elem_of_res_bind_elim in Hin as [b [_ Hbranch]].
    destruct b.
    + unfold mthrow, Exec.res_throw_inst in Hbranch.
      cbn in Hbranch.
      inversion Hbranch.
    + apply Exec.elem_of_res_mchoosel_inv in Hbranch.
      exact Hbranch.
  - intro Hin.
    apply Exec.elem_of_res_mchoosel_inv in Hin.
    exact Hin.
Qed.

Lemma promise_select_tid_intro {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st : PState.t prom.(Promising.tState)
      prom.(Promising.mEvent) n) (tid : fin n) ev :
  ev ∈ (CPState.enumerate_results isem prom term tid
          (CPState.initmem st) fuel (PState.tstate tid st)
          (PState.events st)).(CPState.promises prom) →
  Exec.elem_of_results ev
    (@CPState.promise_select_tid isem prom n term fuel st tid).
Proof.
  unfold CPState.promise_select_tid.
  destruct (CPState.enumerate_results isem prom term tid
      (CPState.initmem st) fuel (PState.tstate tid st)
      (PState.events st))
    as [promises final_states errors out_of_fuel] eqn:Henum.
  intro Hev.
  cbn in Hev.
  destruct out_of_fuel.
  - eapply Exec.elem_of_res_bind_intro with (a := false).
    + change (Exec.elem_of_results false
        (mchoosef bool : Exec.res string bool)).
      unfold mchoosef.
      apply Exec.elem_of_res_mchoosel.
      set_solver.
    + apply Exec.elem_of_res_mchoosel.
      exact Hev.
  - apply Exec.elem_of_res_mchoosel.
    exact Hev.
Qed.

Lemma run_step_inv {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) :
  Exec.elem_of_results (st', ())
    ((@CPState.run_step isem prom n term fuel) st) →
  (∃ tid (ev : prom.(Promising.mEvent)) nst,
      CPState.terminated_tid prom term st tid = false ∧
      Exec.elem_of_results ev
        (@CPState.promise_select_tid isem prom n term fuel st tid) ∧
      PState.promise prom ev st = Ok nst ∧
      st' = nst) ∨
  (∃ tid,
      CPState.terminated_tid prom term st tid = false ∧
      Exec.elem_of_results (st', ())
        ((@CPState.run_tid isem prom n tid) st)).
Proof.
  unfold CPState.run_step.
  intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [st0 [st_read [Hget Htail]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Htail as [st_tid [tid [Htid Hafter_tid]]].
  apply Exec.elem_of_mchoose_inv in Htid as ->.
  destruct (CPState.terminated_tid prom term st tid) eqn:Hterm_tid.
  - unfold mdiscard in Hafter_tid.
    unfold elem_of, Exec.elem_of_results in Hafter_tid.
    cbn in Hafter_tid.
    inversion Hafter_tid.
  - apply Exec.elem_of_bind_elim in Hafter_tid
      as [st_choice [promise [Hchoose Hafter_promise]]].
    apply Exec.elem_of_mchoosel_inv in Hchoose as [-> _].
    destruct promise.
    + apply cpromise_tid_inv in Hafter_promise
        as [ev [nst [Hev [Hpromise Hstate]]]].
      left.
      exists tid, ev, nst.
      repeat split; try assumption.
    + right.
      exists tid.
      split; [exact Hterm_tid|exact Hafter_promise].
Qed.

Lemma cpromise_tid_intro {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat) (tid : fin n)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) (ev : prom.(Promising.mEvent))
    (nst : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (Hev : Exec.elem_of_results ev
      (@CPState.promise_select_tid isem prom n term fuel st tid))
    (Hpromise : PState.promise prom ev st = Ok nst)
    (Hstate : st' = nst) :
  Exec.elem_of_results (st', ())
    ((@CPState.cpromise_tid isem prom n term fuel tid) st).
Proof.
  unfold CPState.cpromise_tid.
  eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
  - apply Exec.elem_of_mGet.
  - eapply Exec.elem_of_bind_intro with (st' := st) (a := ev).
    + apply Exec.elem_of_lift_res.
      exact Hev.
    + eapply Exec.elem_of_bind_intro with (st' := st) (a := nst).
      * apply (proj2 (PromiseFirstCurrent.lift_result_success
            st st nst (PState.promise prom ev st))).
        split; [reflexivity|exact Hpromise].
      * rewrite Hstate.
        apply Exec.elem_of_mSetv.
Qed.

Lemma run_transition_promise_first_none_inv
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) :
  Exec.elem_of_results (st', None)
    ((@CPState.run_transition_promise_first isem prom n term fuel) st) →
  ∃ tid ev nst,
    ev ∈ (CPState.promises prom
      (promise_first_execution_results isem term fuel st !!! tid)) ∧
    PState.promise prom ev st = Ok nst ∧
    st' = nst.
Proof.
  unfold CPState.run_transition_promise_first.
  intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [st0 [opt [Hget Hchoice]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hchoice as [st1 [opt' [Hopt Hbranch]]].
  apply Exec.elem_of_mchoosel_inv in Hopt as [-> Hopt].
  cbn in Hopt.
  destruct opt' as [|[|[|opt']]]; cbn in Hbranch.
  - apply Exec.elem_of_bind_elim in Hbranch as [st2 [tid [Htid Hrest]]].
    apply Exec.elem_of_mchoosel_inv in Htid as [-> _].
    apply Exec.elem_of_bind_elim in Hrest as [st3 [ev [Hev Hrest]]].
    apply Exec.elem_of_mchoosel_inv in Hev as [-> Hev].
    apply Exec.elem_of_bind_elim in Hrest as [st4 [nst [Hpromise Hrest]]].
    apply Exec.elem_of_lift_res_inv in Hpromise as [-> Hpromise].
    apply PromiseFirstCurrent.lift_result_res_success in Hpromise as Hpromise.
    apply Exec.elem_of_bind_elim in Hrest as [st5 [u [Hset Hret]]].
    destruct u.
    assert (Hset_state : st5 = nst).
    { unfold elem_of, Exec.elem_of_results in Hset.
      cbn in Hset.
      apply list_elem_of_singleton in Hset.
      inversion Hset; reflexivity. }
    rewrite Hset_state in Hret.
    pose proof (Exec.elem_of_mret_inv nst st' None None Hret)
      as [Hret_state Hnone].
    exists tid, ev, nst.
    split; [|split].
    + cbn [promise_first_execution_results].
      exact Hev.
    + exact Hpromise.
    + exact Hret_state.
  - apply Exec.elem_of_bind_elim in Hbranch as [st2 [ts [Hstates Hrest]]].
    apply Exec.elem_of_bind_elim in Hrest as [st3 [pt [Hguard Hrest]]].
    apply Exec.elem_of_bind_elim in Hrest as [st4 [u [Hvalidate Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [_ Hsome].
    discriminate Hsome.
  - apply Exec.elem_of_bind_elim in Hbranch as [st2 [err [Herr Hthrow]]].
    unfold mthrow, Exec.throw_inst in Hthrow.
    unfold elem_of, Exec.elem_of_results in Hthrow.
    cbn in Hthrow.
    set_solver.
  - destruct (bool_decide
      (∃ x ∈ map (CPState.out_of_fuel prom)
        (vmap (λ '(tid, ts),
          CPState.enumerate_results isem prom term tid
            (CPState.initmem st) fuel ts (CPState.events st))
          (venumerate (CPState.tstates st))), (x : bool))) eqn:Hfuel.
    + unfold mthrow, Exec.throw_inst in Hbranch.
      unfold elem_of, Exec.elem_of_results in Hbranch.
      cbn in Hbranch.
      set_solver.
    + unfold mdiscard in Hbranch.
      unfold elem_of, Exec.elem_of_results in Hbranch.
      cbn in Hbranch.
      inversion Hbranch.
Qed.

Lemma run_transition_promise_first_none_intro
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (tid : fin n) (ev : prom.(Promising.mEvent))
    (nst : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (Hev : ev ∈ (CPState.promises prom
      (promise_first_execution_results isem term fuel st !!! tid)))
    (Hpromise : PState.promise prom ev st = Ok nst)
    (Hstate : st' = nst) :
  Exec.elem_of_results (st', None)
    ((@CPState.run_transition_promise_first isem prom n term fuel) st).
Proof.
  unfold CPState.run_transition_promise_first.
  eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
  - apply Exec.elem_of_mGet.
  - eapply Exec.elem_of_bind_intro with (st' := st) (a := 0%nat).
    + change (Exec.elem_of_results (st, 0%nat)
        ((mchoosel (seq 0 4) : Exec.t _ string nat) st)).
      apply Exec.elem_of_mchoosel.
      cbn. set_solver.
    + eapply Exec.elem_of_bind_intro with (st' := st) (a := tid).
      * change (Exec.elem_of_results (st, tid)
          ((mchoosef (fin n) : Exec.t _ string (fin n)) st)).
        unfold mchoosef.
        apply Exec.elem_of_mchoosel.
        apply Exec.elem_of_fin_enum.
      * eapply Exec.elem_of_bind_intro with (st' := st) (a := ev).
        { change (Exec.elem_of_results (st, ev)
            ((mchoosel (CPState.promises prom
              (promise_first_execution_results isem term fuel st !!! tid)) :
                Exec.t _ string _) st)).
          apply Exec.elem_of_mchoosel.
          exact Hev. }
        { eapply Exec.elem_of_bind_intro with (st' := st) (a := nst).
          { apply (proj2 (PromiseFirstCurrent.lift_result_success
                st st nst (PState.promise prom ev st))).
            split; [reflexivity|exact Hpromise]. }
          { eapply Exec.elem_of_bind_intro with (st' := nst) (a := tt).
            { apply Exec.elem_of_mSetv. }
            { rewrite Hstate.
              apply Exec.elem_of_mret. } } }
Qed.

Lemma run_step_intro {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) (tid : fin n) :
  CPState.terminated_tid prom term st tid = false →
  ((∃ ev nst,
      Exec.elem_of_results ev
        (@CPState.promise_select_tid isem prom n term fuel st tid) ∧
      PState.promise prom ev st = Ok nst ∧
      st' = nst) ∨
   Exec.elem_of_results (st', ())
     ((@CPState.run_tid isem prom n tid) st)) →
  Exec.elem_of_results (st', ())
    ((@CPState.run_step isem prom n term fuel) st).
Proof.
  intros Hterm Hx.
  unfold CPState.run_step.
  eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
  - apply Exec.elem_of_mGet.
  - eapply Exec.elem_of_bind_intro with (st' := st) (a := tid).
    + change (Exec.elem_of_results (st, tid)
        ((mchoose n : Exec.t _ string (fin n)) st)).
      apply Exec.elem_of_mchoose.
    + rewrite Hterm.
      destruct Hx as [[ev [nst [Hev [Hpromise Hstate]]]]|Hrun].
      * eapply Exec.elem_of_bind_intro with (st' := st) (a := true).
        { change (Exec.elem_of_results (st, true)
            ((mchoosel (enum bool) : Exec.t _ string bool) st)).
          apply Exec.elem_of_mchoosel.
          cbn. set_solver. }
        { apply cpromise_tid_intro with (ev := ev) (nst := nst).
          - exact Hev.
          - exact Hpromise.
          - exact Hstate. }
      * eapply Exec.elem_of_bind_intro with (st' := st) (a := false).
        { change (Exec.elem_of_results (st, false)
            ((mchoosel (enum bool) : Exec.t _ string bool) st)).
          apply Exec.elem_of_mchoosel.
          cbn. set_solver. }
        { exact Hrun. }
Qed.

Lemma promise_first_none_to_direct_none
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) fuel
    (st st' : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n) :
  (∀ (tid : fin n) candidates ev,
    ev ∈ prom.(Promising.filter_promises) n tid (PState.events st) candidates →
    ev ∈ candidates) →
  Exec.elem_of_results (st', None)
    (CPState.run_transition_promise_first isem prom term fuel st) →
  Exec.elem_of_results (st', None)
    (CPState.run_transition isem prom term fuel st).
Proof.
  intros Hfilter Hpf.
  destruct (run_transition_promise_first_none_inv isem term fuel st st' Hpf)
    as [tid [ev [nst [Hcandidate [Hpromise Hstate]]]]].
  rewrite promise_first_execution_results_lookup in Hcandidate.
  assert (Htid : CPState.terminated_tid prom term st tid = false).
  {
    destruct (CPState.terminated_tid prom term st tid) eqn:Hterm; [|reflexivity].
    exfalso.
    unfold CPState.terminated_tid in Hterm.
    rewrite (enumerate_results_terminated_promises isem term tid
      (PState.initmem st) fuel (PState.tstate tid st) (PState.events st) Hterm)
      in Hcandidate.
    apply (Hfilter tid []) in Hcandidate. inversion Hcandidate.
  }
  unfold CPState.run_transition.
  eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
  - apply Exec.elem_of_mGet.
  - destruct (decide (CPState.terminated prom term st)) as [Hall|Hnot].
    + exfalso.
      unfold CPState.terminated, fforallb in Hall.
      apply true_eq_true in Hall.
      pose proof (proj1 (@List.forallb_forall (fin n)
        (CPState.terminated_tid prom term st) (enum (fin n))) Hall) as Hall'.
      assert (Hin : List.In tid (enum (fin n))).
      { apply list_elem_of_In. apply Exec.elem_of_fin_enum. }
      specialize (Hall' tid Hin).
      rewrite Htid in Hall'. discriminate.
    + eapply Exec.elem_of_bind_intro with (st' := st') (a := tt).
      * eapply run_step_intro with (tid := tid); [exact Htid|].
        left. exists ev, nst. split.
        -- apply promise_select_tid_intro. exact Hcandidate.
        -- split; assumption.
      * apply Exec.elem_of_mret.
Qed.

Lemma direct_promise_step_to_promise_first_none
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) (tid : fin n)
    (ev : prom.(Promising.mEvent))
    (nst : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) :
  CPState.terminated_tid prom term st tid = false →
  Exec.elem_of_results ev
    (@CPState.promise_select_tid isem prom n term fuel st tid) →
  PState.promise prom ev st = Ok nst →
  st' = nst →
  Exec.elem_of_results (st', None)
    ((@CPState.run_transition_promise_first isem prom n term fuel) st).
Proof.
  intros Hterm Hev Hpromise Hstate.
  eapply run_transition_promise_first_none_intro.
  - rewrite promise_first_execution_results_lookup.
    apply promise_select_tid_inv in Hev.
    exact Hev.
  - exact Hpromise.
  - exact Hstate.
Qed.

Lemma direct_none_to_promise_first_none_or_run_tid
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n) :
  Exec.elem_of_results (st', None)
    ((@CPState.run_transition isem prom n term fuel) st) →
  Exec.elem_of_results (st', None)
    ((@CPState.run_transition_promise_first isem prom n term fuel) st) ∨
  ∃ tid,
    CPState.terminated_tid prom term st tid = false ∧
    Exec.elem_of_results (st', ())
      ((@CPState.run_tid isem prom n tid) st).
Proof.
  intro Hrun.
  apply run_transition_none_inv in Hrun as [st_step [Hstep ->]].
  apply run_step_inv in Hstep.
  destruct Hstep as
    [[tid [ev [nst [Hterm [Hev [Hpromise Hstate]]]]]]|[tid [Hterm Hrun_tid]]].
  - left.
    eapply direct_promise_step_to_promise_first_none.
    + exact Hterm.
    + exact Hev.
    + exact Hpromise.
    + exact Hstate.
  - right.
    exists tid. split; [exact Hterm|exact Hrun_tid].
Qed.

(** The corresponding inversion for the promise-first runner records the
    selected vector of thread states.  The promise-first branch is the only
    branch that can return [Some]; the other choices return [None], an error,
    or discard the execution. *)
Lemma run_transition_promise_first_some_inv
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (fsig : {s & archState.is_terminated term s}) :
  Exec.elem_of_results (st', Some fsig)
    ((@CPState.run_transition_promise_first isem prom n term fuel) st) →
  ∃ (tstates : vec prom.(Promising.tState) n)
    (st0 : PState.t prom.(Promising.tState)
      prom.(Promising.mEvent) n)
    (pt : CPState.terminated prom term st0),
    st0 = {| CPState.tstates := tstates;
             CPState.initmem := CPState.initmem st;
             CPState.events := CPState.events st |} ∧
    (∀ tid, tstates !!! tid ∈
      (promise_first_execution_results isem term fuel st !!! tid)
        .(CPState.final_states prom)) ∧
    Exec.elem_of_results (st', ())
      ((CPState.validate_final prom st0) st) ∧
    fsig = CPState.to_final_archState
      (CPState.make_final prom term st0 pt).
Proof.
  unfold CPState.run_transition_promise_first.
  intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [st0 [opt [Hget Hchoice]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hchoice as [st1 [opt' [Hopt Hbranch]]].
  apply Exec.elem_of_mchoosel_inv in Hopt as [-> Hopt].
  cbn in Hopt.
  destruct opt' as [|[|[|opt']]]; cbn in Hbranch.
  - apply Exec.elem_of_bind_elim in Hbranch as [st2 [tid [Htid Hrest]]].
    apply Exec.elem_of_bind_elim in Hrest as [st3 [next_ev [Hnext Hrest]]].
    apply Exec.elem_of_bind_elim in Hrest as [st4 [nst [Hpromise Hrest]]].
    apply Exec.elem_of_bind_elim in Hrest as [st5 [u [Hset Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [_ Hnone].
    discriminate Hnone.
  - apply Exec.elem_of_bind_elim in Hbranch as [st2 [ts [Hstates Hrest]]].
    apply Exec.elem_of_bind_elim in Hrest as [st3 [term_proof [Hguard Hrest]]].
    apply Exec.elem_of_bind_elim in Hrest as [st4 [u [Hvalidate Hret]]].
    apply Exec.elem_of_mchoosel_inv in Hstates as [-> Hstates].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_mret_inv in Hret as [-> Hfinal].
    inversion Hfinal; subst fsig.
    destruct u.
    exists ts.
    exists {| CPState.tstates := ts;
              CPState.initmem := CPState.initmem st;
              CPState.events := CPState.events st |}.
    exists term_proof.
    split; [reflexivity|].
    split.
    + pose proof (proj1 (cprodn_spec _ ts) Hstates) as Hlookup.
      intro tid. specialize (Hlookup tid).
      rewrite vlookup_map in Hlookup. exact Hlookup.
    + split; [exact Hvalidate|reflexivity].
  - apply Exec.elem_of_bind_elim in Hbranch as [st2 [err [Herr Hthrow]]].
    unfold mthrow, Exec.throw_inst in Hthrow.
    unfold elem_of, Exec.elem_of_results in Hthrow.
    cbn in Hthrow.
    set_solver.
  - destruct (bool_decide
      (∃ x ∈ map (CPState.out_of_fuel prom)
        (vmap (λ '(tid, ts),
          CPState.enumerate_results isem prom term tid
            (CPState.initmem st) fuel ts (CPState.events st))
          (venumerate (CPState.tstates st))), (x : bool))) eqn:Hfuel.
    + unfold mthrow, Exec.throw_inst in Hbranch.
      unfold elem_of, Exec.elem_of_results in Hbranch.
      cbn in Hbranch.
      set_solver.
    + unfold mdiscard in Hbranch.
      unfold elem_of, Exec.elem_of_results in Hbranch.
      cbn in Hbranch.
      inversion Hbranch.
Qed.

Lemma run_transition_promise_first_some_intro
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (tstates : vec prom.(Promising.tState) n)
    (pt : CPState.terminated prom term
      {| CPState.tstates := tstates;
         CPState.initmem := CPState.initmem st;
         CPState.events := CPState.events st |})
    (Hstates : Exec.elem_of_results (st, tstates)
      ((mchoosel
        (cprodn (vmap (CPState.final_states prom)
          (promise_first_execution_results isem term fuel st))) :
        Exec.t _ string (vec (Promising.tState prom) n)) st))
    (Hvalidate : Exec.elem_of_results (st', ())
      ((CPState.validate_final prom
        {| CPState.tstates := tstates;
           CPState.initmem := CPState.initmem st;
           CPState.events := CPState.events st |}) st)) :
  Exec.elem_of_results
    (st', Some (CPState.to_final_archState
      (CPState.make_final prom term
        {| CPState.tstates := tstates;
           CPState.initmem := CPState.initmem st;
           CPState.events := CPState.events st |} pt)))
    ((@CPState.run_transition_promise_first isem prom n term fuel) st).
Proof.
  unfold CPState.run_transition_promise_first.
  eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
  - apply Exec.elem_of_mGet.
  - eapply Exec.elem_of_bind_intro with (st' := st) (a := 1%nat).
    + change (Exec.elem_of_results (st, 1%nat)
        ((mchoosel (seq 0 4) : Exec.t _ string nat) st)).
      apply Exec.elem_of_mchoosel.
      cbn. set_solver.
    + eapply Exec.elem_of_bind_intro with (st' := st) (a := tstates).
      * cbn [promise_first_execution_results].
        exact Hstates.
      * eapply Exec.elem_of_bind_intro with (st' := st) (a := pt).
        -- change (Exec.elem_of_results (st, pt)
            ((guard_discard (CPState.terminated prom term
              {| CPState.tstates := tstates;
                 CPState.initmem := CPState.initmem st;
                 CPState.events := CPState.events st |}) :
                Exec.t _ string _) st)).
          destruct (Exec.elem_of_guard_discard
            (St := PState.t prom.(Promising.tState)
              prom.(Promising.mEvent) n) (E := string) st pt)
            as [pt' Hguard].
          assert (pt' = pt) by apply proof_irrelevance.
          subst pt'.
          exact Hguard.
        -- eapply Exec.elem_of_bind_intro with (st' := st') (a := tt).
          ++ exact Hvalidate.
          ++ apply Exec.elem_of_mret.
Qed.

(** If every current thread is already terminated and the early-stop guard is
    discharged for every thread, the promise-first final branch can select the
    current vector of thread states. *)
Lemma promise_first_final_step_initial
    {prom : Promising.Model} (isem : iMon ())
    {n : nat} (term : terminationCondition n) (fuel : nat)
    (st st' : PState.t prom.(Promising.tState)
        prom.(Promising.mEvent) n)
    (Hterm : CPState.terminated prom term st)
    (Hbase : ∀ tid : fin n,
      prom.(Promising.tState_min_new_prom_view)
        (PState.tstate tid st) <= length (PState.events st))
    (Hterminated : ∀ tid : fin n,
      CPState.terminated_tid prom term st tid = true)
    (Hvalidate : Exec.elem_of_results (st', ())
      ((CPState.validate_final prom st) st)) :
  Exec.elem_of_results
    (st', Some (CPState.to_final_archState
      (CPState.make_final prom term st Hterm)))
    ((@CPState.run_transition_promise_first isem prom n term fuel) st).
Proof.
  destruct st as [tstates initmem events].
  assert (Hstates : Exec.elem_of_results
      ({| CPState.tstates := tstates;
          CPState.initmem := initmem;
          CPState.events := events |}, tstates)
      ((mchoosel
        (cprodn (vmap (CPState.final_states prom)
          (promise_first_execution_results isem term fuel
            {| CPState.tstates := tstates;
               CPState.initmem := initmem;
               CPState.events := events |}))) :
        Exec.t _ string (vec (Promising.tState prom) n))
       {| CPState.tstates := tstates;
          CPState.initmem := initmem;
          CPState.events := events |})).
  {
    apply Exec.elem_of_mchoosel.
    apply (proj2 (cprodn_spec _ _)).
    intro tid.
    rewrite vlookup_map.
    rewrite promise_first_execution_results_lookup.
    apply enumerate_results_terminated_final_state.
    - apply Hbase.
    - apply Hterminated.
  }
  eapply run_transition_promise_first_some_intro
    with (st := {| CPState.tstates := tstates;
                   CPState.initmem := initmem;
                   CPState.events := events |})
         (st' := st') (tstates := tstates) (pt := Hterm).
  - exact Hstates.
  - exact Hvalidate.
Qed.
