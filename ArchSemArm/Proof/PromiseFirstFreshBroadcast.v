(******************************************************************************)
(* Fresh instruction events update every thread that observes the history    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent
  PromiseFirstExecutionCurrent PromiseFirstSailOwnership.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Existing Instance PState.PState_PPState_set.

Lemma vimapM_identity {A E n} (xs : vec A n) (f : fin n → A → result E A) :
  (∀ i x, f i x = Ok x) → vimapM f xs = Ok xs.
Proof.
  revert f. induction xs as [|x n xs IH]; intros f Hf; cbn [vimapM]; [reflexivity|].
  rewrite Hf, IH by (intros; apply Hf). reflexivity.
Qed.

Lemma run_tid_broadcast_decompose (prom : Promising.Model) isem {n} (tid : fin n)
    (st st' : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n) :
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) →
  ∃ ts mem iis states,
    Exec.elem_of_results (PPState.Make ts mem iis, ())
      (cinterp (λ out, prom.(Promising.handle_outcome) n tid (PState.initmem st) out |$> fst)
        isem (PPState.Make (PState.tstate tid st) (PState.events st) prom.(Promising.iis_init))) ∧
    PState.broadcast_fresh prom tid (PState.initmem st) (PState.events st)
      (take (length mem - length (PState.events st)) mem)
      (vinsert tid ts (PState.tstates st)) = Ok states ∧
    st' = PState.Make states (PState.initmem st) mem.
Proof.
  unfold PState.run_tid. intro Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [st0 [Hget Hrun]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[] [Hinst Hrun]]].
  apply Exec.elem_of_liftSt_inv in Hinst as [[ts mem iis] [Hmid Hinst]].
  subst mid.
  apply Exec.elem_of_bind_elim in Hrun as [mid [next [Hget Hrun]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [states [Hstates Hrun]]].
  apply PromiseFirstCurrent.lift_result_success in Hstates as [-> Hstates].
  apply Exec.elem_of_mset_inv in Hrun as ->.
  exists ts, mem, iis, states. split; [exact Hinst|].
  split; [exact Hstates|]. destruct st; reflexivity.
Qed.

Lemma run_tid_broadcast_intro (prom : Promising.Model) isem {n} (tid : fin n)
    (st : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n) ts mem iis states :
  Exec.elem_of_results (PPState.Make ts mem iis, ())
    (cinterp (λ out, prom.(Promising.handle_outcome) n tid (PState.initmem st) out |$> fst)
      isem (PPState.Make (PState.tstate tid st) (PState.events st) prom.(Promising.iis_init))) →
  PState.broadcast_fresh prom tid (PState.initmem st) (PState.events st)
    (take (length mem - length (PState.events st)) mem)
    (vinsert tid ts (PState.tstates st)) = Ok states →
  Exec.elem_of_results (PState.Make states (PState.initmem st) mem, ())
    (PState.run_tid isem prom tid st).
Proof.
  intros Hinst Hstates. unfold PState.run_tid.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  eapply Exec.elem_of_bind_intro.
  - exact (Exec.elem_of_liftSt st (PPState.Make ts mem iis) ()
      (PState.PState_PPState prom tid)
      (cinterp (λ out, prom.(Promising.handle_outcome) n tid (PState.initmem st) out |$> fst)
        isem) Hinst).
  - eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
    eapply Exec.elem_of_bind_intro.
    + apply PromiseFirstCurrent.lift_result_success. split; [reflexivity|exact Hstates].
    + destruct st. exact (Exec.elem_of_mset _ PState.tstates (λ _, states)).
Qed.

Lemma run_tid_decompose_fixed (prom : Promising.Model) isem {n} (tid : fin n)
    (st st' : PState.t prom.(Promising.tState) prom.(Promising.mEvent) n) :
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) →
  PState.events st' = PState.events st →
  ∃ ts mem iis,
    Exec.elem_of_results (PPState.Make ts mem iis, ())
      (cinterp (λ out, prom.(Promising.handle_outcome) n tid (PState.initmem st) out |$> fst)
        isem (PPState.Make (PState.tstate tid st) (PState.events st) prom.(Promising.iis_init))) ∧
    st' = PState.Make (vinsert tid ts (PState.tstates st)) (PState.initmem st) mem.
Proof.
  intros Hrun Hmem.
  destruct (run_tid_broadcast_decompose prom isem tid st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  cbn in Hmem. subst mem.
  rewrite Nat.sub_diag in Hstates. cbn [take PState.broadcast_fresh] in Hstates.
  injection Hstates as <-. eauto.
Qed.

#[local] Typeclasses Transparent UMPromising Promising.mEvent Promising.tState Promising.iis.
Lemma UM_broadcast_fresh {n} (tid : fin n) imem base extra (states : vec UMPromising.TState.t n) :
  UMCollectedOwnership.owned tid extra →
  PState.broadcast_fresh UMPromising tid imem base extra states = Ok states.
Proof.
  revert states. induction extra as [|ev extra IH]; intros states Howned; [reflexivity|].
  apply Forall_cons in Howned as [Howner Howned].
  cbn [PState.broadcast_fresh]. rewrite IH by exact Howned.
  cbn [mbind result_bind]. apply vimapM_identity. intros other ts.
  destruct (decide (other = tid)) as [->|Hne]; [reflexivity|].
  rewrite UMPromising_emit_promise_ok, bool_decide_false; [reflexivity|].
  rewrite Howner. intro Heq. apply Hne, fin_to_nat_inj. symmetry. exact Heq.
Qed.

Lemma UM_instruction_owned {n A} (tid : fin n) imem (mon : iMon A) ppst ppst' ret :
  Exec.elem_of_results (ppst', ret)
    (cinterp (λ out, UMPromising.(Promising.handle_outcome) n tid imem out |$> fst) mon ppst) →
  UMCollectedOwnership.owned tid
    (take (length (PPState.mem ppst') - length (PPState.mem ppst)) (PPState.mem ppst')).
Proof.
  intro Hrun.
  destruct (collect_instruction_complete UMPromising tid imem (length (PPState.mem ppst))
    mon [] ppst ppst' ret Hrun) as [proms Hcollect].
  pose proof (UMCollectedOwnership.collect_instruction_owned tid imem (PPState.mem ppst)
    mon [] ppst proms ppst' ret ltac:(constructor)
    ltac:(exists []; split; [reflexivity|constructor]) Hcollect) as [_ Howned].
  apply UMCollectedOwnership.owned_suffix_take, Howned.
Qed.

Lemma run_tid_decompose_um isem {n} (tid : fin n)
    (st st' : PState.t UMPromising.TState.t Msg.t n) :
  Exec.elem_of_results (st', ()) (PState.run_tid isem UMPromising tid st) →
  ∃ ts mem iis,
    Exec.elem_of_results (PPState.Make ts mem iis, ())
      (cinterp (λ out, UMPromising.(Promising.handle_outcome) n tid (PState.initmem st) out |$> fst)
        isem (PPState.Make (PState.tstate tid st) (PState.events st) UMPromising.(Promising.iis_init))) ∧
    st' = PState.Make (vinsert tid ts (PState.tstates st)) (PState.initmem st) mem.
Proof.
  intro Hrun. destruct (run_tid_broadcast_decompose UMPromising isem tid st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  pose proof (UM_instruction_owned tid (PState.initmem st) isem _ _ () Hinst) as Howned.
  rewrite UM_broadcast_fresh in Hstates by exact Howned.
  injection Hstates as <-. eauto.
Qed.
