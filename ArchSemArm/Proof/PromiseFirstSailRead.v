(******************************************************************************)
(* Replaying UM reads after adding a promised message to the history          *)
(******************************************************************************)

(** Successful reads retain their byte/timestamp candidate when the memory
    grows by one event. The successful read itself supplies the time bound
    needed for the new pending-promise guard. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstExecutionCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Lemma read_all_aux_success_nonempty {E} (get_msg : E → option Msg.t)
    addr size imem mem tmin tmax candidates :
  PromMemory.read_all_aux get_msg addr size imem mem tmin tmax = Ok candidates →
  candidates ≠ [].
Proof.
  revert mem candidates. induction tmax as [|tmax IH]; intros [|ev mem] candidates Hrun;
    cbn [PromMemory.read_all_aux] in Hrun.
  all: match type of Hrun with context[if ?b then _ else _] =>
    destruct b eqn:Heq end.
  all: try discriminate.
  all: try (match type of Hrun with context[PromMemory.read_from_aux ?f ?a ?s ?i ?m ?t] =>
    destruct (PromMemory.read_from_aux f a s i m t) end;
    cbn in Hrun; inversion Hrun; discriminate).
  destruct (PromMemory.read_all_aux get_msg addr size imem mem tmin tmax)
    as [prev|err] eqn:Hprev; cbn in Hrun; [|discriminate].
  destruct (get_msg ev) as [msg|]; cbn in Hrun.
  - match type of Hrun with context[if ?b then _ else _] => destruct b end; cbn in Hrun.
    + inversion Hrun; discriminate.
    + match type of Hrun with context[if ?b then _ else _] => destruct b end; cbn in Hrun.
      * destruct prev; cbn in Hrun; [discriminate|]. inversion Hrun; discriminate.
      * injection Hrun as ->. eapply IH. exact Hprev.
  - injection Hrun as ->. eapply IH. exact Hprev.
Qed.

Lemma read_all_cons_preserves_candidates {E} (get_msg : E → option Msg.t)
    addr size imem mem ev tmin candidates :
  tmin ≤ length mem →
  PromMemory.read_all get_msg addr size imem mem tmin = Ok candidates →
  ∃ candidates',
    PromMemory.read_all get_msg addr size imem (ev :: mem) tmin = Ok candidates' ∧
    ∀ candidate, candidate ∈ candidates → candidate ∈ candidates'.
Proof.
  intros Hmin Hread.
  pose proof (read_all_aux_success_nonempty get_msg addr size imem mem tmin
    (length mem) candidates Hread) as Hnonempty.
  unfold PromMemory.read_all. cbn [length PromMemory.read_all_aux].
  assert ((S (length mem) =? tmin)%stdpp = false) as Hneq by (apply bool_decide_eq_false_2; lia).
  rewrite Hneq. change (PromMemory.read_all_aux get_msg addr size imem mem tmin (length mem)
    = Ok candidates) in Hread.
  rewrite Hread. cbn.
  destruct (get_msg ev) as [msg|].
  - match goal with |- context[if ?b then _ else _] => destruct b end.
    + eexists. split; [reflexivity|]. intros candidate Hin. right. exact Hin.
    + match goal with |- context[if ?b then _ else _] => destruct b end.
      * destruct candidates as [|candidate rest]; [contradiction|].
        eexists. split; [reflexivity|]. intros c Hin. right. exact Hin.
      * exists candidates. split; [reflexivity|auto].
  - exists candidates. split; [reflexivity|auto].
Qed.

Lemma read_all_aux_success_bound {E} (get_msg : E → option Msg.t)
    addr size imem mem tmin tmax candidates :
  PromMemory.read_all_aux get_msg addr size imem mem tmin tmax = Ok candidates →
  tmin ≤ tmax.
Proof.
  revert mem candidates. induction tmax as [|tmax IH]; intros [|ev mem] candidates Hrun;
    cbn [PromMemory.read_all_aux] in Hrun.
  all: match type of Hrun with context[if ?b then _ else _] =>
    destruct b eqn:Heq end;
    [apply bool_decide_eq_true_1 in Heq; lia|].
  all: try discriminate.
  destruct (PromMemory.read_all_aux get_msg addr size imem mem tmin tmax)
    as [prev|err] eqn:Hprev; cbn in Hrun; [|discriminate].
  specialize (IH _ _ Hprev). lia.
Qed.

Lemma exec_lift_result_inv {St E A} st st' (x : A) (r : result E A) :
  Exec.elem_of_results (st', x) ((mlift r : Exec.t St E A) st) →
  st' = st ∧ r = Ok x.
Proof.
  destruct r as [a|err].
  - intro H. change ((st', x) ∈ [(st, a)]) in H.
    apply list_elem_of_singleton in H. inversion H. auto.
  - intro H. change ((st', x) ∈ []) in H. inversion H.
Qed.
Lemma exec_lift_result {St E A} st (x : A) (r : result E A) :
  r = Ok x → Exec.elem_of_results (st, x) ((mlift r : Exec.t St E A) st).
Proof. intros ->. change ((st, x) ∈ [(st, x)]). left; reflexivity. Qed.

Lemma exec_guard_discard_bind_intro {St E A} {P : Prop} `{Decision P}
    (st : St) (res : St * A) (tail : Exec.t St E A) :
  P → Exec.elem_of_results res (tail st) →
  Exec.elem_of_results res ((guard_discard P;; tail) st).
Proof.
  destruct res as [st' a]. intros HP Htail. destruct (Exec.elem_of_guard_discard (E:=E) st HP)
    as [p Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|exact Htail].
Qed.

Module UMReadReplay.
Import UMPromising.
#[local] Typeclasses Transparent Memory.t othrow.

Definition add_pending_message (msg : Msg.t) (p : nat)
    (ppst : PPState.t TState.t Msg.t IIS.t) :=
  PPState.Make (TState.promise p (PPState.state ppst))
    (msg :: PPState.mem ppst) (PPState.iis ppst).

Lemma promise_update_cohs avs p ts :
  TState.update_cohs avs (TState.promise p ts) =
  TState.promise p (TState.update_cohs avs ts).
Proof.
  unfold TState.update_cohs. revert ts.
  induction avs as [|[a v] avs IH]; intro ts; cbn; [reflexivity|].
  rewrite IH.
  assert (Hcoh : ∀ ts0, TState.update_coh a v (TState.promise p ts0) =
    TState.promise p (TState.update_coh a v ts0)) by (intros []; reflexivity).
  apply Hcoh.
Qed.

Lemma read_mem_after_promise addr size macc imem msg ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (read_mem addr size macc imem ppst) →
  let p := S (length (PPState.mem ppst)) in
  Exec.elem_of_results (add_pending_message msg p ppst', ret)
    (read_mem addr size macc imem (add_pending_message msg p ppst)).
Proof.
  destruct ppst as [ts mem iis]. cbn. intro Hrun.
  unfold read_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [vaddr [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [Hnp [Hguard Hrun]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  apply Exec.elem_of_bind_elim in Hrun as [mid [mem0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [candidates [Hread Hrun]]].
  apply exec_lift_result_inv in Hread as [-> Hread].
  apply Exec.elem_of_bind_elim in Hrun as [mid [candidate [Hchoice Htail]]].
  apply Exec.elem_of_mchoosel_inv in Hchoice as [-> Hin].
  cbn in Hread.
  pose proof (read_all_aux_success_bound Some _ _ _ _ _ _ _ Hread) as Hmin.
  destruct (read_all_cons_preserves_candidates Some addr size imem mem msg _ candidates
    Hmin Hread) as [new_candidates [Hread' Hsubset]].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [add_pending_message].
  assert (Hnp' : TState.no_promises_until (IIS.strict iis)
    (TState.promise (S (length mem)) ts)).
  { intros t Ht. apply elem_of_cons in Ht as [->|Ht].
    - cbn in Hmin. unfold join, join_nat in Hmin. lia.
    - apply Hnp, Ht. }
  destruct (Exec.elem_of_guard_discard (E:=string)
    (add_pending_message msg (S (length mem)) (PPState.Make ts mem iis)) Hnp')
    as [Hnp'' Hguard'].
  eapply Exec.elem_of_bind_intro; [exact Hguard'|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [add_pending_message TState.promise].
  eapply Exec.elem_of_bind_intro with (a := new_candidates).
  - apply exec_lift_result. exact Hread'.
  - eapply Exec.elem_of_bind_intro with (a := candidate).
    + apply Exec.elem_of_mchoosel, Hsubset, Hin.
    + cbn [add_pending_message PPState.state PPState.mem PPState.iis TState.promise] in *.
      UMMemoryGrowth.invert_execution.
      all: subst ret.
      all: cbn [add_pending_message].
      all: repeat first
        [ eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
        | eapply exec_guard_discard_bind_intro;
          [destruct ts; assumption|] ].
      all: unfold add_pending_message; cbn.
      all: rewrite promise_update_cohs.
      all: apply Exec.elem_of_mret.
Qed.
End UMReadReplay.

(** The concrete memory-read outcome includes instruction fetches. Fetch
    replay requires the code bytes to be preserved by the new message. *)
Lemma exec_guard_or_bind_intro {St E A} {P : Prop} `{Decision P}
    (err : E) (st : St) (res : St * A) (tail : Exec.t St E A) :
  P → Exec.elem_of_results res (tail st) →
  Exec.elem_of_results res ((guard_or err P;; tail) st).
Proof.
  destruct res as [st' a]. intros HP Htail.
  destruct (Exec.elem_of_guard_or (E:=E) st err HP) as [p Hguard].
  eapply Exec.elem_of_bind_intro; [exact Hguard|exact Htail].
Qed.

Module UMOutcomeReplay.
Import UMPromising UMReadReplay.
#[local] Typeclasses Transparent Memory.t othrow.

Lemma mem_read_after_promise tid imem req msg ppst ppst' ret pre :
  (is_ifetch (MemReq.access_kind req) = true →
    MemReq.size req = 4%N →
    read_ifetch (MemReq.address req) imem (msg :: PPState.mem ppst) =
    read_ifetch (MemReq.address req) imem (PPState.mem ppst)) →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome tid imem (MemRead req) ppst) →
  let p := S (length (PPState.mem ppst)) in
  Exec.elem_of_results (add_pending_message msg p ppst', (ret, pre))
    (run_outcome tid imem (MemRead req) (add_pending_message msg p ppst)).
Proof.
  destruct req as [macc addr pas size tags].
  destruct tags as [|tags]; cbn; intros Hfetch Hrun.
  2: { simp run_outcome in Hrun. UMMemoryGrowth.invert_execution. }
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [Hpas [Hguard Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  eapply exec_guard_or_bind_intro; [exact Hpas|].
  destruct (is_ifetch macc) eqn:Hif.
  - apply Exec.elem_of_bind_elim in Hrun as [mid [Hsize [Hguard Hrun]]].
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hrun as [mid [mem [Hget Hrun]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as [mid [opcode [Hread Hrun]]].
    apply Exec.elem_of_lift_res_inv in Hread as [-> Hread].
    apply Exec.elem_of_mret_inv in Hrun as [-> Heq].
    injection Heq as -> ->.
    destruct (Exec.elem_of_guard_or (E:=string)
      (add_pending_message msg (S (length (PPState.mem ppst))) ppst)
      "Ifetch read of size other than 4" Hsize) as [Hsize' Hguard].
    replace Hsize' with Hsize in Hguard by apply proof_irrel.
    eapply Exec.elem_of_bind_intro; [exact Hguard|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro with (a := opcode).
    + apply Exec.elem_of_lift_res. cbn.
      rewrite (Hfetch eq_refl Hsize). exact Hread.
    + apply Exec.elem_of_mret.
  - destruct (is_explicit macc) eqn:Hexpl.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [val [Hread Hrun]]].
      apply Exec.elem_of_mret_inv in Hrun as [-> Heq].
      injection Heq as -> ->.
      eapply Exec.elem_of_bind_intro; [eapply read_mem_after_promise; exact Hread|].
      apply Exec.elem_of_mret.
    + UMMemoryGrowth.invert_execution.
Qed.
End UMOutcomeReplay.
