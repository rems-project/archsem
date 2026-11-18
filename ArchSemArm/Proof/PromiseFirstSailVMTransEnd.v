(******************************************************************************)
(* Completing a VM translation after extending its valid interval            *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstVMExecutionCurrent
  PromiseFirstSailVMCacheConfig PromiseFirstSailVMReplay PromiseFirstSailRead
  PromiseFirstSailVMTranslation.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMTransEndReplay.
Import VMPromising.

Definition frame (writes tlbis : list nat) (cache : option TLB.t) (ts : TState.t) :=
  ts |> setv TState.prom_wr writes |> setv TState.prom_tlbi tlbis |> setv TState.tlb cache.

Lemma emit_promise_frame tid imem mem ev ts issued :
  TState.emit_promise tid imem mem ev ts = Ok issued →
  issued = frame (TState.prom_wr issued) (TState.prom_tlbi issued) (TState.tlb issued) ts.
Proof.
  unfold TState.emit_promise, TState.process_event. intro Hpromise.
  apply VMReadReplay.run_tlb_frame in Hpromise.
  destruct (bool_decide (Ev.tid ev = tid)); [destruct ev|];
    rewrite Hpromise; destruct ts; reflexivity.
Qed.

Lemma tcohs_after_promise tid imem mem ev ts issued asid offsets old_inv new_inv :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok issued →
  (∀ offset ∈ offsets, TState.get_tcoh asid offset ts ≤ length mem) →
  VMTranslationReplay.inv_after (length mem) old_inv new_inv →
  TState.tcohs_before_inv_time asid offsets old_inv ts →
  TState.tcohs_before_inv_time asid offsets new_inv issued.
Proof.
  intros Hpromise Hbound Hinv Hguard.
  pose proof (emit_promise_frame tid imem (ev :: mem) ev ts issued Hpromise) as Hframe.
  unfold TState.tcohs_before_inv_time in *.
  destruct new_inv as [deadline|]; [|exact I].
  intros offset Hin.
  rewrite Hframe. change (TState.get_tcoh asid offset ts < deadline).
  eapply (VMTranslationReplay.inv_after_access (length mem) old_inv (Some deadline)
    (TState.get_tcoh asid offset ts)); [exact Hinv|apply Hbound, Hin|].
  destruct old_inv; [apply Hguard, Hin|exact I].
Qed.

Definition interval_iis stop inv iis :=
  iis |> set IIS.trs (fmap (setv IIS.TransRes.trans_end stop))
      |> setv IIS.inv_time inv.
Definition interval_state ev writes tlbis cache stop inv
    (ppst : PPState.t TState.t Ev.t IIS.t) :=
  PPState.Make (frame writes tlbis cache (PPState.state ppst))
    (ev :: PPState.mem ppst) (interval_iis stop inv (PPState.iis ppst)).

(** Consuming descriptors from the selected walk is independent of the
    interval's end and invalidation deadline. The descriptor path is fixed. *)
Theorem read_pte_interval ev writes tlbis cache stop inv ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (read_pte ppst) →
  Exec.elem_of_results
    (interval_state ev writes tlbis cache stop inv ppst', ret)
    (read_pte (interval_state ev writes tlbis cache stop inv ppst)).
Proof.
  destruct ppst as [ts mem iis]. intro Hrun. unfold read_pte in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [opt [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  cbn [compose PPState.iis] in Hrun.
  destruct (IIS.trs iis) as [trs|] eqn:Htrs.
  2: { unfold othrow in Hrun. VMMemoryGrowth.invert_execution. }
  unfold othrow in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [tr [Hret Hrun]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[tr val] [Hpop Hrun]]].
  apply exec_lift_result_inv in Hpop as [-> Hpop].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[] [Hset Hrun]]].
  apply Exec.elem_of_mset_inv in Hset as ->.
  apply Exec.elem_of_mret_inv in Hrun as [-> ->].
  unfold IIS.TransRes.pop in Hpop.
  destruct (IIS.TransRes.remaining trs) as [|pte rest] eqn:Hpath; [discriminate|].
  injection Hpop as <- <-.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [compose].
  change (IIS.trs (PPState.iis (interval_state ev writes tlbis cache stop inv
    (PPState.Make ts mem iis)))) with
    ((setv IIS.TransRes.trans_end stop) <$> IIS.trs iis).
  rewrite Htrs. cbn [fmap option_fmap othrow].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  eapply Exec.elem_of_bind_intro.
  - apply exec_lift_result. unfold IIS.TransRes.pop.
    change (IIS.TransRes.remaining (setv IIS.TransRes.trans_end stop trs))
      with (IIS.TransRes.remaining trs).
    rewrite Hpath. reflexivity.
  - eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    unfold interval_state, interval_iis. cbn [PPState.state PPState.mem PPState.iis].
    apply Exec.elem_of_mret.
Qed.

(** Translation completion reads the start and end of the selected interval.
    A later end preserves successful and faulting completions, including ETS3
    ordering. Promise lists, the TLB and the future invalidation deadline can
    change without changing the architectural effects of this outcome. *)
Theorem translation_end_larger_interval trans_end ts iis ts' iis' trs stop
    writes tlbis cache inv :
  IIS.trs iis = Some trs → IIS.TransRes.trans_end trs ≤ stop →
  TState.ets3 (frame writes tlbis cache ts) = TState.ets3 ts →
  Exec.elem_of_results ((ts', iis'), ()) (run_trans_end trans_end (ts, iis)) →
  Exec.elem_of_results ((frame writes tlbis cache ts', setv IIS.inv_time inv iis'), ())
    (run_trans_end trans_end
      (frame writes tlbis cache ts,
        iis |> setv IIS.trs (Some (setv IIS.TransRes.trans_end stop trs))
            |> setv IIS.inv_time inv)).
Proof.
  intros Htrs Hstop Hets Hrun.
  unfold run_trans_end in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [iis0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  cbn -[mset msetv mret TState.update IIS.add] in Hrun. rewrite Htrs in Hrun.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [frame IIS.trs IIS.TransRes.trans_start IIS.TransRes.trans_end].
  destruct (decide (FaultRecord_statuscode (AddressDescriptor_fault trans_end) = Fault_None)).
  - VMMemoryGrowth.invert_execution.
    apply Exec.elem_of_mret_inv in Hrun as [Heq _].
    injection Heq as Hts Hiis. subst ts' iis'.
    repeat (eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]).
    apply Exec.elem_of_mret.
  - VMMemoryGrowth.invert_execution.
    all: try solve [unfold Exec.elem_of_results in Hrun; cbn in Hrun; inversion Hrun].
    cbn [frame] in Hets.
    cbn [frame].
    repeat (eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]).
    cbn -[mset mret IIS.add TState.ets3].
    rewrite Hets.
    change (IIS.TransRes.trans_end (setv IIS.TransRes.trans_end stop trs)) with stop.
    change (IIS.TransRes.trans_start (setv IIS.TransRes.trans_end stop trs))
      with (IIS.TransRes.trans_start trs).
    change (TState.vrd (frame writes tlbis cache ts)) with (TState.vrd ts).
    change (TState.vwr (frame writes tlbis cache ts)) with (TState.vwr ts).
    repeat match goal with H : (_ <=? _) = true |- _ => apply Nat.leb_le in H end.
    match goal with |- context[?test <=? stop] =>
      assert (Htest : (test <=? stop) = true) by (apply Nat.leb_le; lia);
      rewrite Htest
    end.
    apply Exec.elem_of_mset_inv in Hrun as Heq.
    injection Heq as Hts Hiis. subst ts' iis'.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
    unfold Exec.elem_of_results. cbn. apply list_elem_of_singleton.
    destruct ts, iis; reflexivity.
Qed.

Corollary translation_end_after_promise tid imem mem ev trans_end ts issued
    iis ts' iis' trs stop inv :
  TState.emit_promise tid imem mem ev ts = Ok issued →
  IIS.trs iis = Some trs → IIS.TransRes.trans_end trs ≤ stop →
  Exec.elem_of_results ((ts', iis'), ()) (run_trans_end trans_end (ts, iis)) →
  Exec.elem_of_results
    ((frame (TState.prom_wr issued) (TState.prom_tlbi issued) (TState.tlb issued) ts',
      setv IIS.inv_time inv iis'), ())
    (run_trans_end trans_end
      (issued, iis |> setv IIS.trs (Some (setv IIS.TransRes.trans_end stop trs))
                   |> setv IIS.inv_time inv)).
Proof.
  intros Hpromise Htrs Hstop Hrun.
  pose proof (emit_promise_frame tid imem mem ev ts issued Hpromise) as Hframe.
  pose proof (VMCacheConfig.emit_promise_ets tid imem mem ev ts issued Hpromise) as [_ Hets].
  assert (Hets' : TState.ets3
    (frame (TState.prom_wr issued) (TState.prom_tlbi issued) (TState.tlb issued) ts) =
    TState.ets3 ts) by (rewrite <- Hframe; exact Hets).
  pose proof (translation_end_larger_interval trans_end ts iis ts' iis' trs stop
    (TState.prom_wr issued) (TState.prom_tlbi issued) (TState.tlb issued) inv
    Htrs Hstop Hets' Hrun) as Hreplay.
  rewrite <- Hframe in Hreplay. exact Hreplay.
Qed.
End VMTransEndReplay.
