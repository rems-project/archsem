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

(** Replaying the current UM write handler after promising its new event.
    This ports the concrete write replay proof to the current timestamp
    lookup, message record, and exclusive-monitor record. It does not assume
    an instruction or whole-execution transformation. *)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstExecutionCurrent
  PromiseFirstSailExecution.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Typeclasses Transparent Memory.t Memory.exclusive.
#[local] Existing Instance PromMemory.lookup_inst.
#[local] Existing Instance PromMemory.exclusive_dec.
Module UMSailReplay.
Import UMPromising.

Lemma memory_fulfill_none_no_match msg prom mem t :
  Memory.fulfill msg prom mem = None →
  t ∈ prom →
  mem !! t ≠ Some msg.
Proof.
  unfold Memory.fulfill, PromMemory.fulfill.
  rewrite head_reverse.
  intro Hfulfill.
  apply last_None in Hfulfill.
  intros Hprom Hlookup.
  pose proof (filter_nil_not_elem_of
    (λ t, mem !! t = Some msg) prom t Hfulfill Hlookup) as Hnot.
  exact (Hnot Hprom).
Qed.

Lemma last_cons_all_eq {A} (x : A) (l : list A) :
  (∀ y, y ∈ l → y = x) →
  last (x :: l) = Some x.
Proof.
  induction l as [|a l IH]; intro Hall.
  - reflexivity.
  - rewrite last_cons_cons.
    assert (a = x) by (apply Hall; left; reflexivity).
    subst a.
    apply IH.
    intros y Hy.
    apply Hall.
    right.
    exact Hy.
Qed.

Lemma memory_fulfill_after_promise msg prom mem :
  Memory.fulfill msg prom mem = None →
  Memory.fulfill msg (length (msg :: mem) :: prom) (msg :: mem) =
  Some (length (msg :: mem)).
Proof.
  intro Hfulfill.
  set (time := length (msg :: mem)).
  assert (Hno_match : ∀ t, t ∈ prom → mem !! t ≠ Some msg).
  { intros t Hprom.
    eapply memory_fulfill_none_no_match; eauto. }
  unfold Memory.fulfill, PromMemory.fulfill.
  rewrite head_reverse.
  rewrite filter_cons_True.
  - apply last_cons_all_eq.
    intros t Hmatch.
    rewrite list_elem_of_filter in Hmatch.
    destruct Hmatch as [Hlookup Hprom].
    apply PromMemory.lookup_cons_inv_same in Hlookup as [Hold_lookup|Htime].
    + exfalso.
      eapply Hno_match; eauto.
    + exact Htime.
  - subst time.
    apply PromMemory.lookup_latest.
Qed.

Lemma TState_filter_prom_after_promise v ts :
  set TState.prom (filter (λ t, t ≠ v)) (TState.promise v ts) =
  set TState.prom (filter (λ t, t ≠ v)) ts.
Proof.
  destruct ts.
  unfold TState.promise.
  cbn.
  rewrite decide_False by congruence.
  reflexivity.
Qed.

Lemma elem_of_unfolded_ppstate_mset_state st mem iis upd :
  Exec.elem_of_results (PPState.Make (upd st) mem iis, ())
    ((((λ s : PPState.t TState.t Msg.t IIS.t,
          {| Exec.results := [(s, s)]; Exec.errors := [] |})
        : Exec.t (PPState.t TState.t Msg.t IIS.t) string
            (PPState.t TState.t Msg.t IIS.t))
      ≫= λ s : PPState.t TState.t Msg.t IIS.t,
            ((λ _ : PPState.t TState.t Msg.t IIS.t,
                {| Exec.results := [(set PPState.state upd s, ())];
                   Exec.errors := [] |})
             : Exec.t (PPState.t TState.t Msg.t IIS.t) string unit))
       (PPState.Make st mem iis)).
Proof.
  change (PPState.Make (upd st) mem iis)
    with (set PPState.state upd (PPState.Make st mem iis)).
  apply Exec.elem_of_unfolded_mset.
Qed.

Ltac inv_exec_result :=
  repeat match goal with
  | x : unit |- _ => destruct x
  | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  | H : None = Some _ |- _ => inversion H
  | H : Some _ = None |- _ => inversion H
  | H : (_, _) = ?p |- _ => destruct p; inversion H; subst; clear H
  | H : ?p = (_, _) |- _ => destruct p; inversion H; subst; clear H
  | H : context[decide (Is_true (is_explicit ?macc))] |- _ =>
      destruct (decide (Is_true (is_explicit macc))) eqn:?
  | H : context[decide (is_explicit ?macc = true)] |- _ =>
      destruct (decide (is_explicit macc = true)) eqn:?
  | H : context[decide (is_explicit ?macc)] |- _ =>
      destruct (decide (is_explicit macc)) eqn:?
  | H : Exec.elem_of_results _ ((guard_discard _) _) |- _ =>
      apply Exec.elem_of_guard_discard_inv in H as ->
  | H : Exec.elem_of_results _ ((guard_discard' _) _) |- _ =>
      apply Exec.elem_of_guard_discard_unit_inv in H as ->
  | H : Exec.elem_of_results _ ((guard_or _ _) _) |- _ =>
      let Hp := fresh "Hguard_or" in
      pose proof (Exec.elem_of_guard_or_prop _ _ _ _ H) as Hp;
      apply Exec.elem_of_guard_or_inv in H as ->
  | H : Exec.elem_of_results _ ((_ ≫= _) _) |- _ =>
      apply Exec.elem_of_bind_elim in H as [? [? [? H]]]
  | H : Exec.elem_of_results _ ((mget _) _) |- _ =>
      apply Exec.elem_of_mget_inv in H as [-> ->]
  | H : Exec.elem_of_results _ ((mGet) _) |- _ =>
      apply Exec.elem_of_mGet_inv in H as [-> ->]
  | H : Exec.elem_of_results _ ((mret _) _) |- _ =>
      apply Exec.elem_of_mret_inv in H as [-> ?]
  | H : Exec.elem_of_results _ ((msetv _ _) _) |- _ =>
      unfold msetv in H
  | H : Exec.elem_of_results _ ((mset _ _) _) |- _ =>
      apply Exec.elem_of_mset_inv in H as ->
  | H : Exec.elem_of_results _ ((mSet _) _) |- _ =>
      apply Exec.elem_of_mSet_inv in H as ->
  | H : Exec.elem_of_results _ ((Exec.liftSt _ _) _) |- _ =>
      apply Exec.elem_of_liftSt_inv in H as [? [-> H]]
  | H : Exec.elem_of_results _ ((mlift _) _) |- _ =>
      apply Exec.elem_of_lift_res_inv in H as [-> H]
  | H : Exec.elem_of_results _ ((mchoosel _) _) |- _ =>
      apply Exec.elem_of_mchoosel_inv in H as [-> _]
  | H : Exec.elem_of_results _ ((mthrow _) _) |- _ =>
      unfold elem_of, Exec.elem_of_results in H; cbn in H; inversion H
  | H : Exec.elem_of_results _ ((mdiscard) _) |- _ =>
      rewrite Exec.mdiscard_eq in H;
      unfold elem_of, Exec.elem_of_results in H; cbn in H; inversion H
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[othrow _ ?opt] => unfold othrow in H end
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[if ?b then _ else _] => destruct b eqn:? end
  | H : Exec.elem_of_results _ ?e |- _ =>
      lazymatch e with context[match ?x with _ => _ end] => destruct x eqn:? end
  end.

Lemma memory_promise_inv msg mem mem' time :
  Exec.elem_of_results (mem', time) (Memory.promise msg mem) →
  mem' = msg :: mem ∧ time = length (msg :: mem).
Proof. apply UMMemoryGrowth.promise_memory. Qed.

Lemma memory_exclusive_cons_latest_old tid addr size tread msg mem :
  Memory.exclusive tid addr size tread (length (msg :: mem)) mem →
  Memory.exclusive tid addr size tread (length (msg :: mem)) (msg :: mem).
Proof.
  unfold Memory.exclusive, PromMemory.exclusive.
  replace (length (msg :: mem) - 1)%nat with (length mem) by (cbn; lia).
  rewrite PromMemory.cut_before_cons_old by lia. auto.
Qed.

Lemma fulfill_after_TState_promise msg ts mem :
  Memory.fulfill msg (TState.prom ts) mem = None →
  Memory.fulfill msg
    (TState.prom (TState.promise (length (msg :: mem)) ts)) (msg :: mem) =
  Some (length (msg :: mem)).
Proof.
  destruct ts.
  cbn.
  apply memory_fulfill_after_promise.
Qed.

Lemma elem_of_unfolded_ppstate_mset_prom
    (st : TState.t) (mem : Memory.t) (iis : IIS.t) upd :
  Exec.elem_of_results
    (PPState.Make (set TState.prom upd st) mem iis, ())
    ((mset (TState.prom ∘ PPState.state) upd :
        Exec.t (PPState.t TState.t Msg.t IIS.t) string unit)
       (PPState.Make st mem iis)).
Proof.
  change (PPState.Make (set TState.prom upd st) mem iis)
    with (set (TState.prom ∘ PPState.state) upd
            (PPState.Make st mem iis)).
  apply Exec.elem_of_unfolded_mset.
Qed.

Lemma write_mem_promise_replay_one tid addr size macc data ppst ppst' vpre :
  Exec.elem_of_results (ppst', Some vpre)
    (write_mem tid addr size macc data ppst) →
  let msg := Msg.make tid addr size data in
  PPState.mem ppst' = msg :: PPState.mem ppst ∧
  (vpre ≤ length (PPState.mem ppst))%nat ∧
  Exec.elem_of_results (ppst', None)
    (write_mem tid addr size macc data
       (PPState.Make
          (TState.promise (length (msg :: PPState.mem ppst))
             (PPState.state ppst))
          (msg :: PPState.mem ppst)
          (PPState.iis ppst))).
Proof.
  destruct ppst as [ts mem iis].
  cbn.
  intro Hrun.
  unfold write_mem in Hrun.
  set (msg := Msg.make tid addr size data) in *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_mem [mem0 [Hget_mem Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_mem as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_pair [[time new_promise] [Hmatch Hrun]]].
  destruct (Memory.fulfill msg (TState.prom ts) mem) as [tfulfilled|]
    eqn:Hfulfill.
  - exfalso.
    cbn in Hmatch.
    rewrite Hfulfill in Hmatch.
    apply Exec.elem_of_mret_inv in Hmatch as [-> Hpair_eq].
    inversion Hpair_eq; subst time new_promise.
    cbn in Hrun.
    inv_exec_result.
  - cbn in Hmatch.
    rewrite Hfulfill in Hmatch.
    apply Exec.elem_of_bind_elim in Hmatch as
      [pp_prom [time_prom [Hpromise Hpair]]].
    apply Exec.elem_of_liftSt_inv in Hpromise as
      [mem1 [Hpp_prom Hpromise]].
    destruct (memory_promise_inv msg mem mem1 time_prom Hpromise)
      as [-> Htime_prom].
    subst pp_prom.
    apply Exec.elem_of_mret_inv in Hpair as [-> Hpair_eq].
    inversion Hpair_eq; subst time new_promise.
    subst time_prom.
    set (pnew := length (msg :: mem)).
    set (iis_write :=
      if is_atomic_rmw macc then
        set IIS.rmw_read (λ _ : option (nat * bool), None) iis
      else iis).
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_rmw [read_acquire [Hrmw Hrun]]].
    assert (Hstrict_write : IIS.strict iis_write = IIS.strict iis).
    { subst iis_write.
      destruct (is_atomic_rmw macc); reflexivity. }
    assert (Hpp_rmw : pp_rmw = PPState.Make ts (msg :: mem) iis_write).
    {
      subst iis_write.
      destruct (is_atomic_rmw macc) eqn:Hatomic_macc.
      - cbn in Hrmw.
          apply Exec.elem_of_bind_elim in Hrmw as
            [pp_rmw_get [rmw_read_opt [Hget_rmw Hrmw]]].
          apply Exec.elem_of_mget_inv in Hget_rmw as [-> Hrmw_read_opt_eq].
          cbn in Hrmw_read_opt_eq.
          apply Exec.elem_of_bind_elim in Hrmw as
            [pp_read [[tread_rmw read_acquire0] [Hread Hrmw]]].
          unfold othrow in Hread.
          destruct rmw_read_opt as [[tread0 read_acquire1]|]
            eqn:Hrmw_read_opt; cbn in Hread.
        2: {
          unfold mthrow, Exec.throw_inst, elem_of, Exec.elem_of_results in Hread.
          cbn in Hread.
          exfalso.
          exact (not_elem_of_nil _ Hread).
        }
        apply Exec.elem_of_mret_inv in Hread as [-> Hread_eq].
        inversion Hread_eq; subst.
        apply Exec.elem_of_bind_elim in Hrmw as
          [pp_guard [[] [Hguard Hrmw]]].
        apply Exec.elem_of_guard_discard_unit_inv in Hguard as ->.
          apply Exec.elem_of_bind_elim in Hrmw as
            [pp_clear [[] [Hclear Hrmw]]].
          unfold msetv in Hclear.
          apply Exec.elem_of_mset_inv in Hclear as Hclear_eq.
          subst pp_clear.
          apply Exec.elem_of_mret_inv in Hrmw as [Hpp_rmw_eq Hret].
          inversion Hret; subst read_acquire.
          exact Hpp_rmw_eq.
      - apply Exec.elem_of_mret_inv in Hrmw as [-> Hret].
        inversion Hret; subst read_acquire.
        reflexivity.
    }
    assert (Hrmw_replay :
      Exec.elem_of_results
        (PPState.Make (TState.promise pnew ts) (msg :: mem) iis_write,
         read_acquire)
          (((if is_atomic_rmw macc then
              rmw_read_opt ← mget (IIS.rmw_read ∘ PPState.iis);
              '(tread, read_acquire) ←
                othrow "RMW write without a read" rmw_read_opt;
              guard_discard' (Memory.exclusive tid addr size tread pnew
                (msg :: mem));;
              msetv (IIS.rmw_read ∘ PPState.iis) None;;
              mret read_acquire
            else mret false) :
            Exec.t (PPState.t TState.t Msg.t IIS.t) string bool)
             (PPState.Make (TState.promise pnew ts) (msg :: mem) iis))).
    {
      subst iis_write.
      destruct (is_atomic_rmw macc) eqn:Hatomic_macc.
      - cbn in Hrmw |- *.
          apply Exec.elem_of_bind_elim in Hrmw as
            [pp_rmw_get [rmw_read_opt [Hget_rmw Hrmw]]].
          apply Exec.elem_of_mget_inv in Hget_rmw as [-> Hrmw_read_opt_eq].
          cbn in Hrmw_read_opt_eq.
          apply Exec.elem_of_bind_elim in Hrmw as
            [pp_read [[tread_rmw read_acquire0] [Hread Hrmw]]].
          unfold othrow in Hread.
          destruct rmw_read_opt as [[tread0 read_acquire1]|]
            eqn:Hrmw_read_opt; cbn in Hread.
        2: {
          unfold mthrow, Exec.throw_inst, elem_of, Exec.elem_of_results in Hread.
          cbn in Hread.
          exfalso.
          exact (not_elem_of_nil _ Hread).
        }
          apply Exec.elem_of_mret_inv in Hread as [-> Hread_eq].
          inversion Hread_eq; subst.
          assert (Hrmw_read_iis :
            IIS.rmw_read iis = Some (tread0, read_acquire1)).
          { symmetry.
            exact Hrmw_read_opt_eq. }
        apply Exec.elem_of_bind_elim in Hrmw as
          [pp_guard [[] [Hguard Hrmw]]].
        pose proof (Exec.elem_of_guard_discard_unit_prop _ _ Hguard)
          as Hexclusive_rmw.
        apply Exec.elem_of_guard_discard_unit_inv in Hguard as ->.
          apply Exec.elem_of_bind_elim in Hrmw as
            [pp_clear [[] [Hclear Hrmw]]].
          unfold msetv in Hclear.
          apply Exec.elem_of_mset_inv in Hclear as Hclear_eq.
          subst pp_clear.
            apply Exec.elem_of_mret_inv in Hrmw as [_ Hret].
          inversion Hret; subst read_acquire.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
              (a := Some (tread0, read_acquire1)).
          + rewrite <- Hrmw_read_iis.
            change (S (length mem)) with pnew.
            apply (Exec.elem_of_mget (E:=string)
              (PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
              (IIS.rmw_read ∘ PPState.iis)).
        + cbn.
          eapply Exec.elem_of_bind_intro with
            (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
                (a := (tread0, read_acquire1)).
              * unfold othrow.
                apply Exec.elem_of_mret.
          * cbn.
            eapply Exec.elem_of_bind_intro with
              (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
              (a := ()).
            -- apply Exec.elem_of_guard_discard_unit.
               subst pnew.
               apply memory_exclusive_cons_latest_old.
               exact Hexclusive_rmw.
            -- cbn.
               eapply Exec.elem_of_bind_intro with
                 (st' := PPState.Make (TState.promise pnew ts)
                   (msg :: mem)
                   (set IIS.rmw_read (λ _ : option (nat * bool), None) iis))
                 (a := ()).
               ++ unfold msetv.
                  change (PPState.Make (TState.promise pnew ts)
                    (msg :: mem)
                    (set IIS.rmw_read (λ _ : option (nat * bool), None) iis))
                    with
                    (set (IIS.rmw_read ∘ PPState.iis)
                       (λ _ : option (nat * bool), None)
                       (PPState.Make (TState.promise pnew ts)
                          (msg :: mem) iis)).
                  apply Exec.elem_of_mset.
                 ++ cbn.
                    apply Exec.elem_of_mret.
        - apply Exec.elem_of_mret_inv in Hrmw as [_ Hret].
          inversion Hret; subst read_acquire.
          apply Exec.elem_of_mret.
    }
    subst pp_rmw.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_vdata [vdata [Hget_vdata Hrun]]].
    apply Exec.elem_of_mget_inv in Hget_vdata as [-> ->].
    try rewrite Hstrict_write in *.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_guard [pguard [Hguard Hrun]]].
    pose proof pguard as Hpre.
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    destruct Hpre as [Hvpre_lt Hcoh].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_promset [[] [Hpromset Hrun]]].
    apply Exec.elem_of_mset_inv in Hpromset as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_cohs [[] [Hcohs Hrun]]].
    apply Exec.elem_of_mset_inv in Hcohs as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_vwr [[] [Hvwr Hrun]]].
    apply Exec.elem_of_mset_inv in Hvwr as ->.
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_vrel [[] [Hvrel Hrun]]].
      apply Exec.elem_of_mset_inv in Hvrel as ->.
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_rmw_acq [[] [Hrmw_acq Hrun]]].
      assert (Hrmw_acq_mem : PPState.mem pp_rmw_acq = msg :: mem).
      {
        destruct (is_atomic_rmw macc && is_rel_acq macc && read_acquire)
          eqn:Hrmw_acq_bool.
        - unfold elem_of, Exec.elem_of_results in Hrmw_acq.
          cbn in Hrmw_acq.
          apply list_elem_of_singleton in Hrmw_acq.
          inversion Hrmw_acq; subst.
          destruct ts; cbn in *; reflexivity.
        - apply Exec.elem_of_mret_inv in Hrmw_acq as [-> _].
          destruct ts; cbn in *; reflexivity.
      }
      assert (Hupdate_coh_xclb :
        ∀ a v ts0,
          TState.xclb (TState.update_coh a v ts0) =
          TState.xclb ts0).
      { intros a v ts0. destruct ts0. reflexivity. }
      assert (Hset_prom_xclb :
        ∀ upd ts0,
          TState.xclb (set TState.prom upd ts0) = TState.xclb ts0).
      { intros upd ts0. destruct ts0. reflexivity. }
      assert (Hupdate_vwr_xclb :
        ∀ v ts0,
          TState.xclb (TState.update TState.vwr v ts0) =
          TState.xclb ts0).
      { intros v ts0. destruct ts0. reflexivity. }
      assert (Hupdate_vrel_xclb :
        ∀ v ts0,
          TState.xclb (TState.update TState.vrel v ts0) =
          TState.xclb ts0).
      { intros v ts0. destruct ts0. reflexivity. }
      assert (Hupdate_vacq_xclb :
        ∀ v ts0,
          TState.xclb (TState.update TState.vacq v ts0) =
          TState.xclb ts0).
      { intros v ts0. destruct ts0. reflexivity. }
      assert (Hupdate_cohs_xclb :
        ∀ avs ts0,
          TState.xclb (TState.update_cohs avs ts0) =
          TState.xclb ts0).
      {
        induction avs as [|[a v] avs IH]; intro ts0; cbn.
        - reflexivity.
        - rewrite Hupdate_coh_xclb.
          apply IH.
      }
      assert (Hrmw_acq_xclb :
        TState.xclb (PPState.state pp_rmw_acq) = TState.xclb ts).
      {
        destruct (is_atomic_rmw macc && is_rel_acq macc && read_acquire)
          eqn:Hrmw_acq_bool.
        - unfold elem_of, Exec.elem_of_results in Hrmw_acq.
          cbn in Hrmw_acq.
          apply list_elem_of_singleton in Hrmw_acq.
          inversion Hrmw_acq; subst.
          cbn -[TState.update TState.update_cohs].
          rewrite Hupdate_vacq_xclb.
          rewrite Hupdate_vrel_xclb.
          rewrite Hupdate_vwr_xclb.
          rewrite Hupdate_cohs_xclb.
          rewrite Hset_prom_xclb.
          reflexivity.
        - apply Exec.elem_of_mret_inv in Hrmw_acq as [-> _].
          cbn -[TState.update TState.update_cohs].
          rewrite Hupdate_vrel_xclb.
          rewrite Hupdate_vwr_xclb.
          rewrite Hupdate_cohs_xclb.
          rewrite Hset_prom_xclb.
          reflexivity.
      }
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_xcl [xcl [Hxcl Hrun]]].
    assert (Hpre_promise :
      (IIS.strict iis
        ⊔ TState.vcap (TState.promise (length (msg :: mem)) ts)
        ⊔ (TState.vdmbst (TState.promise (length (msg :: mem)) ts)
           ⊔ TState.vdmb (TState.promise (length (msg :: mem)) ts)
           ⊔ TState.visb (TState.promise (length (msg :: mem)) ts)
           ⊔ TState.vacq (TState.promise (length (msg :: mem)) ts)
           ⊔ view_if (is_rel_acq macc)
                (TState.vrd (TState.promise (length (msg :: mem)) ts)
                 ⊔ TState.vwr (TState.promise (length (msg :: mem)) ts)))
        < length (msg :: mem) ∧
       ∀ a ∈ addr_range addr size,
         (TState.coh (TState.promise (length (msg :: mem)) ts) !!! a
          < length (msg :: mem))%nat)%nat).
      { destruct ts.
        cbn in *.
        split.
        - rewrite Hstrict_write in Hvpre_lt.
          exact Hvpre_lt.
        - exact Hcoh. }
    destruct (is_exclusive macc) eqn:Hexcl.
    + destruct (TState.xclb ts) as [xclb_entry|] eqn:Hxclb.
      * destruct xclb_entry as [tread raddr rsize xview]. cbn in Hxcl.
        apply Exec.elem_of_bind_elim in Hxcl as
          [pp_clear [[] [Hclear Hxcl]]].
        apply Exec.elem_of_mset_inv in Hclear as ->.
        destruct (decide (addr = raddr ∧ size = rsize)) as [Haddr|Haddr]
          eqn:Hdec.
        -- rewrite Hdec in Hxcl.
           apply Exec.elem_of_bind_elim in Hxcl as
             [pp_excl [[] [Hexclusive_guard Hxcl]]].
           pose proof (Exec.elem_of_guard_discard_unit_prop
             _ _ Hexclusive_guard) as Hexclusive.
           apply Exec.elem_of_guard_discard_unit_inv in Hexclusive_guard as ->.
           apply Exec.elem_of_mret_inv in Hxcl as [-> Hxcl_ret].
           inversion Hxcl_ret; subst xcl.
           apply Exec.elem_of_bind_elim in Hrun as
             [pp_fwdb [[] [Hfwdb Hrun]]].
           apply Exec.elem_of_mset_inv in Hfwdb as ->.
             apply Exec.elem_of_mret_inv in Hrun as [-> Hret].
             inversion Hret; subst vpre.
             split.
             ++ destruct pp_rmw_acq as [rmw_ts rmw_mem rmw_iis].
                cbn in Hrmw_acq_mem |- *.
                exact Hrmw_acq_mem.
           ++ split.
                ** cbn in Hvpre_lt. lia.
                ** { unfold write_mem.
                   eapply Exec.elem_of_bind_intro.
                     --- apply (Exec.elem_of_mget (E:=string)
                                     (PPState.Make
                                        (TState.promise (length (msg :: mem)) ts)
                                     (msg :: mem) iis)
                         PPState.state).
                 --- cbn.
                       eapply Exec.elem_of_bind_intro with
                                   (st' := PPState.Make
                                     (TState.promise (length (msg :: mem)) ts)
                                     (msg :: mem) iis)
                       (a := msg :: mem).
                     +++ apply (Exec.elem_of_mget (E:=string)
                           (PPState.Make
                              (TState.promise (length (msg :: mem)) ts)
                                     (msg :: mem) iis)
                           PPState.mem).
                     +++ cbn.
                         rewrite fulfill_after_TState_promise by exact Hfulfill.
                         cbn.
                         eapply Exec.elem_of_bind_intro with
                           (st' := PPState.Make
                             (TState.promise (length (msg :: mem)) ts)
                                     (msg :: mem) iis)
                           (a := (length (msg :: mem), false)).
                           *** apply Exec.elem_of_mret.
                           *** cbn.
                               eapply Exec.elem_of_bind_intro with
                                 (st' := PPState.Make
                                   (TState.promise (length (msg :: mem)) ts)
                                   (msg :: mem) iis_write)
                                 (a := read_acquire).
                               { change (length (msg :: mem)) with pnew.
                                 exact Hrmw_replay. }
                               cbn.
                               eapply Exec.elem_of_bind_intro with
                                 (st' := PPState.Make
                                   (TState.promise (length (msg :: mem)) ts)
                                   (msg :: mem) iis_write)
                                 (a := IIS.strict iis).
                               { rewrite <- Hstrict_write.
                                 apply (Exec.elem_of_mget (E:=string)
                                   (PPState.Make
                                     (TState.promise (length (msg :: mem)) ts)
                                     (msg :: mem) iis_write)
                                   (IIS.strict ∘ PPState.iis)). }
                             cbn.
                             destruct (Exec.elem_of_guard_discard
                               (St:=PPState.t TState.t Msg.t IIS.t)
                               (E:=string)
                               (P:=
                                  (IIS.strict iis
                                   ⊔ TState.vcap
                                       (TState.promise (length (msg :: mem)) ts)
                                   ⊔
                                     (TState.vdmbst
                                        (TState.promise (length (msg :: mem)) ts)
                                      ⊔ TState.vdmb
                                          (TState.promise (length (msg :: mem)) ts)
                                      ⊔ TState.visb
                                          (TState.promise (length (msg :: mem)) ts)
                                      ⊔ TState.vacq
                                          (TState.promise (length (msg :: mem)) ts)
                                      ⊔ view_if (is_rel_acq macc)
                                           (TState.vrd
                                              (TState.promise
                                                 (length (msg :: mem)) ts)
                                            ⊔ TState.vwr
                                                (TState.promise
                                                   (length (msg :: mem)) ts)))
                                   < length (msg :: mem) ∧
                                  ∀ a ∈ addr_range addr size,
                                    (TState.coh
                                       (TState.promise (length (msg :: mem)) ts)
                                       !!! a < length (msg :: mem))%nat)%nat)
                                 (PPState.Make
                                    (TState.promise (length (msg :: mem)) ts)
                                    (msg :: mem) iis_write)
                                 Hpre_promise) as [pguard' Hguard'].
                             eapply Exec.elem_of_bind_intro with
                                 (st' := PPState.Make
                                   (TState.promise (length (msg :: mem)) ts)
                                   (msg :: mem) iis_write)
                                 (a := pguard').
                             { exact Hguard'. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                                 (st' := PPState.Make
                                   (set TState.prom
                                      (filter
                                         (λ t : nat,
                                            t ≠ length (msg :: mem))) ts)
                                   (msg :: mem) iis_write)
                               (a := ()).
                             { rewrite <- TState_filter_prom_after_promise.
                               apply elem_of_unfolded_ppstate_mset_prom. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := PPState.Make
                                 (TState.update_cohs
                                    (map (., length (msg :: mem))
                                       (addr_range addr size))
                                      (set TState.prom
                                         (filter
                                            (λ t : nat,
                                               t ≠ length (msg :: mem))) ts))
                                   (msg :: mem) iis_write)
                               (a := ()).
                             { apply elem_of_unfolded_ppstate_mset_state. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := PPState.Make
                                 (TState.update TState.vwr
                                    (length (msg :: mem))
                                    (TState.update_cohs
                                       (map (., length (msg :: mem))
                                          (addr_range addr size))
                                         (set TState.prom
                                            (filter
                                               (λ t : nat,
                                                  t ≠ length (msg :: mem))) ts)))
                                   (msg :: mem) iis_write)
                               (a := ()).
                             { apply elem_of_unfolded_ppstate_mset_state. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := PPState.Make
                                 (TState.update TState.vrel
                                    (view_if (is_rel_acq macc)
                                       (length (msg :: mem)))
                                    (TState.update TState.vwr
                                       (length (msg :: mem))
                                       (TState.update_cohs
                                          (map (., length (msg :: mem))
                                             (addr_range addr size))
                                          (set TState.prom
                                               (filter
                                                  (λ t : nat,
                                                     t ≠ length (msg :: mem)))
                                               ts))))
                                   (msg :: mem) iis_write)
                               (a := ()).
                             { apply elem_of_unfolded_ppstate_mset_state. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := pp_rmw_acq)
                               (a := ()).
                               { exact Hrmw_acq. }
                               cbn.
                               rewrite Hexcl.
                               replace (TState.xclb
                                 (TState.promise (length (msg :: mem)) ts))
                                 with (TState.xclb ts) by (destruct ts; reflexivity).
                               rewrite Hxclb.
                               eapply Exec.elem_of_bind_intro with (a := Some xview).
                             { eapply Exec.elem_of_bind_intro with (a := ()).
                               - apply elem_of_unfolded_ppstate_mset_state.
                               - cbn.
                                 destruct (decide (addr = raddr ∧ size = rsize))
                                   as [Haddr_replay|Hneq] eqn:Hdec_replay;
                                   [|contradiction].
                                 rewrite Hdec_replay.
                                 eapply Exec.elem_of_bind_intro.
                                 + apply Exec.elem_of_guard_discard_unit.
                                   apply memory_exclusive_cons_latest_old.
                                   exact Hexclusive.
                                 + cbn.
                                   apply Exec.elem_of_mret. }
                             cbn.
                             destruct ts as
                               [prom0 regs0 coh0 vrd0 vwr0 vdmbst0 vdmb0
                                vcap0 visb0 vacq0 vrel0 fwdb0 xclb0].
                               cbn in Hxclb.
                               inversion Hxclb; subst xclb0.
                               cbn in *.
                               rewrite <- Hstrict_write.
                               eapply Exec.elem_of_bind_intro.
                             { apply elem_of_unfolded_ppstate_mset_state. }
                             cbn.
                             apply Exec.elem_of_mret. }
        -- exfalso.
           rewrite Hdec in Hxcl.
           apply Exec.elem_of_fmap_inv in Hxcl as [? [_ Hempty]].
           unfold elem_of, Exec.elem_of_results in Hempty.
           cbn in Hempty.
           inversion Hempty.
      * exfalso.
        apply Exec.elem_of_fmap_inv in Hxcl as [? [_ Hempty]].
        unfold elem_of, Exec.elem_of_results in Hempty.
        cbn in Hempty.
        inversion Hempty.
    + apply Exec.elem_of_mret_inv in Hxcl as [-> Hxcl_ret].
      inversion Hxcl_ret; subst xcl.
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_fwdb [[] [Hfwdb Hrun]]].
      apply Exec.elem_of_mset_inv in Hfwdb as ->.
      apply Exec.elem_of_mret_inv in Hrun as [-> Hret].
        inversion Hret; subst vpre.
        split.
        * destruct pp_rmw_acq as [rmw_ts rmw_mem rmw_iis].
          cbn in Hrmw_acq_mem |- *.
          exact Hrmw_acq_mem.
        * split.
          -- cbn in Hvpre_lt. lia.
          -- { unfold write_mem.
               eapply Exec.elem_of_bind_intro.
               ++ apply (Exec.elem_of_mget (E:=string)
                    (PPState.Make
                       (TState.promise (length (msg :: mem)) ts)
                       (msg :: mem) iis)
                    PPState.state).
               ++ cbn.
                  eapply Exec.elem_of_bind_intro.
                  ** apply (Exec.elem_of_mget (E:=string)
                       (PPState.Make
                          (TState.promise (length (msg :: mem)) ts)
                          (msg :: mem) iis)
                       PPState.mem).
                  ** cbn.
                     rewrite fulfill_after_TState_promise by exact Hfulfill.
                     cbn.
                     eapply Exec.elem_of_bind_intro with
                       (st' := PPState.Make
                         (TState.promise (length (msg :: mem)) ts)
                         (msg :: mem) iis)
                       (a := (length (msg :: mem), false)).
                     --- apply Exec.elem_of_mret.
                     --- cbn.
                         eapply Exec.elem_of_bind_intro with
                           (st' := PPState.Make
                             (TState.promise (length (msg :: mem)) ts)
                             (msg :: mem) iis_write)
                           (a := read_acquire).
                         { change (length (msg :: mem)) with pnew.
                           exact Hrmw_replay. }
                         cbn.
                         eapply Exec.elem_of_bind_intro with
                           (st' := PPState.Make
                             (TState.promise (length (msg :: mem)) ts)
                             (msg :: mem) iis_write)
                           (a := IIS.strict iis).
                         { rewrite <- Hstrict_write.
                           apply (Exec.elem_of_mget (E:=string)
                             (PPState.Make
                               (TState.promise (length (msg :: mem)) ts)
                               (msg :: mem) iis_write)
                             (IIS.strict ∘ PPState.iis)). }
                         cbn.
                         destruct (Exec.elem_of_guard_discard
                           (St:=PPState.t TState.t Msg.t IIS.t)
                           (E:=string)
                           (P:=
                              (IIS.strict iis
                               ⊔ TState.vcap
                                   (TState.promise (length (msg :: mem)) ts)
                               ⊔
                                 (TState.vdmbst
                                    (TState.promise (length (msg :: mem)) ts)
                                  ⊔ TState.vdmb
                                      (TState.promise (length (msg :: mem)) ts)
                                  ⊔ TState.visb
                                      (TState.promise (length (msg :: mem)) ts)
                                  ⊔ TState.vacq
                                      (TState.promise (length (msg :: mem)) ts)
                                  ⊔ view_if (is_rel_acq macc)
                                       (TState.vrd
                                          (TState.promise
                                             (length (msg :: mem)) ts)
                                        ⊔ TState.vwr
                                            (TState.promise
                                               (length (msg :: mem)) ts)))
                               < length (msg :: mem) ∧
                              ∀ a ∈ addr_range addr size,
                                (TState.coh
                                   (TState.promise (length (msg :: mem)) ts)
                                   !!! a < length (msg :: mem))%nat)%nat)
                           (PPState.Make
                              (TState.promise (length (msg :: mem)) ts)
                              (msg :: mem) iis_write)
                           Hpre_promise) as [pguard' Hguard'].
                         eapply Exec.elem_of_bind_intro.
                         *** exact Hguard'.
                         *** cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := PPState.Make
                                 (set TState.prom
                                    (filter
                                       (λ t : nat,
                                          t ≠ length (msg :: mem))) ts)
                                 (msg :: mem) iis_write)
                               (a := ()).
                             { rewrite <- TState_filter_prom_after_promise.
                               apply elem_of_unfolded_ppstate_mset_prom. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := PPState.Make
                                 (TState.update_cohs
                                    (map (., length (msg :: mem))
                                       (addr_range addr size))
                                    (set TState.prom
                                       (filter
                                          (λ t : nat,
                                             t ≠ length (msg :: mem))) ts))
                                 (msg :: mem) iis_write)
                               (a := ()).
                             { apply elem_of_unfolded_ppstate_mset_state. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := PPState.Make
                                 (TState.update TState.vwr
                                    (length (msg :: mem))
                                    (TState.update_cohs
                                       (map (., length (msg :: mem))
                                          (addr_range addr size))
                                       (set TState.prom
                                          (filter
                                             (λ t : nat,
                                                t ≠ length (msg :: mem))) ts)))
                                 (msg :: mem) iis_write)
                               (a := ()).
                             { apply elem_of_unfolded_ppstate_mset_state. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := PPState.Make
                                 (TState.update TState.vrel
                                    (view_if (is_rel_acq macc)
                                       (length (msg :: mem)))
                                    (TState.update TState.vwr
                                       (length (msg :: mem))
                                       (TState.update_cohs
                                          (map (., length (msg :: mem))
                                             (addr_range addr size))
                                          (set TState.prom
                                             (filter
                                                (λ t : nat,
                                                   t ≠ length (msg :: mem)))
                                             ts))))
                                 (msg :: mem) iis_write)
                               (a := ()).
                             { apply elem_of_unfolded_ppstate_mset_state. }
                             cbn.
                             eapply Exec.elem_of_bind_intro with
                               (st' := pp_rmw_acq)
                               (a := ()).
                             { exact Hrmw_acq. }
                             cbn.
                             rewrite Hexcl.
                               eapply Exec.elem_of_bind_intro with (a := None).
                             { apply Exec.elem_of_mret. }
                             cbn.
                             rewrite <- Hstrict_write.
                             eapply Exec.elem_of_bind_intro.
                             { apply elem_of_unfolded_ppstate_mset_state. }
                             cbn.
                             apply Exec.elem_of_mret. }
Qed.


Lemma run_outcome_memwrite_replay_from_write tid initmem
    macc addr addr_space size val tags ppst ppst' vpre :
  addr_space = PAS_NonSecure →
  is_explicit macc →
  Exec.elem_of_results (ppst', Some vpre)
    (write_mem tid addr size macc val ppst) →
  ∃ event,
    PPState.mem ppst' = event :: PPState.mem ppst ∧
    Msg.tid event = tid ∧
    (vpre ≤ length (PPState.mem ppst))%nat ∧
    Exec.elem_of_results (ppst', (Ok (), None))
      (run_outcome tid initmem
         (MemWrite (MemReq.make macc addr addr_space size 0) val tags)
         (PPState.Make
            (TState.promise (length (event :: PPState.mem ppst))
               (PPState.state ppst))
            (event :: PPState.mem ppst)
            (PPState.iis ppst))).
Proof.
  intros Haddr_space Hexplicit Hwrite.
  destruct (write_mem_promise_replay_one
    tid addr size macc val ppst ppst' vpre Hwrite) as
    [Hmem [Hle Hwrite_replay]].
  exists (Msg.make tid addr size val).
  split; [exact Hmem|].
  split; [reflexivity|].
  split; [exact Hle|].
  simp run_outcome.
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
    (P:=addr_space = PAS_NonSecure)
    (PPState.Make
       (TState.promise
          (length (Msg.make tid addr size val :: PPState.mem ppst))
          (PPState.state ppst))
       (Msg.make tid addr size val :: PPState.mem ppst)
       (PPState.iis ppst))
    "Access outside Non-Secure" Haddr_space) as [p_ns' Hns'].
  eapply Exec.elem_of_bind_intro.
  - exact Hns'.
  - cbn.
    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
      (P:=is_explicit macc)
      (PPState.Make
         (TState.promise
            (length (Msg.make tid addr size val :: PPState.mem ppst))
            (PPState.state ppst))
         (Msg.make tid addr size val :: PPState.mem ppst)
         (PPState.iis ppst))
      "Only explicit writes are supported" Hexplicit) as [p_exp' Hexp'].
    eapply Exec.elem_of_bind_intro.
    + exact Hexp'.
    + cbn.
      eapply Exec.elem_of_bind_intro.
      * exact Hwrite_replay.
      * cbn.
        apply Exec.elem_of_mret.
Qed.

Lemma run_outcome_memwrite_promise_replay_one tid initmem
    macc addr addr_space size val tags ppst ppst' vpre :
  Exec.elem_of_results (ppst', (Ok (), Some vpre))
    (run_outcome tid initmem
       (MemWrite (MemReq.make macc addr addr_space size 0) val tags) ppst) →
  ∃ event,
    PPState.mem ppst' = event :: PPState.mem ppst ∧
    Msg.tid event = tid ∧
    (vpre ≤ length (PPState.mem ppst))%nat ∧
    Exec.elem_of_results (ppst', (Ok (), None))
      (run_outcome tid initmem
         (MemWrite (MemReq.make macc addr addr_space size 0) val tags)
         (PPState.Make
            (TState.promise (length (event :: PPState.mem ppst))
               (PPState.state ppst))
            (event :: PPState.mem ppst)
            (PPState.iis ppst))).
Proof.
  intro Hrun.
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ns [p_ns [Hns Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hns) as Haddr_space.
  apply Exec.elem_of_guard_or_inv in Hns as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_exp [p_exp [Hexp Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hexp) as Hexplicit.
  apply Exec.elem_of_guard_or_inv in Hexp as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [ppw [vpre_opt [Hwrite Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> Hret].
  inversion Hret; subst vpre_opt.
  destruct (write_mem_promise_replay_one
    tid addr size macc val ppst ppw vpre Hwrite) as
    [Hmem [Hle Hwrite_replay]].
  exists (Msg.make tid addr size val).
  split; [exact Hmem|].
  split; [reflexivity|].
  split; [exact Hle|].
  simp run_outcome.
    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
      (P:=addr_space = PAS_NonSecure)
      (PPState.Make
         (TState.promise
            (length (Msg.make tid addr size val :: PPState.mem ppst))
            (PPState.state ppst))
         (Msg.make tid addr size val :: PPState.mem ppst)
         (PPState.iis ppst))
      "Access outside Non-Secure" Haddr_space) as [p_ns' Hns'].
    eapply Exec.elem_of_bind_intro.
    + exact Hns'.
    + cbn.
      destruct (Exec.elem_of_guard_or
        (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
        (P:=is_explicit macc)
        (PPState.Make
           (TState.promise
              (length (Msg.make tid addr size val :: PPState.mem ppst))
              (PPState.state ppst))
           (Msg.make tid addr size val :: PPState.mem ppst)
           (PPState.iis ppst))
        "Only explicit writes are supported" Hexplicit) as [p_exp' Hexp'].
      eapply Exec.elem_of_bind_intro.
      * exact Hexp'.
      * cbn.
        eapply Exec.elem_of_bind_intro.
        -- exact Hwrite_replay.
        -- cbn.
           apply Exec.elem_of_mret.
Qed.

Lemma run_outcome_promise_replay_one tid initmem out ppst ppst'
    (eret : eff_ret out) vpre :
  Exec.elem_of_results (ppst', (eret, Some vpre))
    (run_outcome tid initmem out ppst) →
  ∃ event,
    PPState.mem ppst' = event :: PPState.mem ppst ∧
    Msg.tid event = tid ∧
    (vpre ≤ length (PPState.mem ppst))%nat ∧
    Exec.elem_of_results (ppst', (eret, None))
      (run_outcome tid initmem out
         (PPState.Make
            (TState.promise (length (event :: PPState.mem ppst))
               (PPState.state ppst))
            (event :: PPState.mem ppst)
            (PPState.iis ppst))).
Proof.
  intro Hrun.
  dependent destruction out;
    try solve [exfalso; simp run_outcome in Hrun; inv_exec_result].
  - exfalso.
    destruct mr as [macc addr addr_space size num_tag].
    destruct num_tag as [|num_tag];
      simp run_outcome in Hrun; inv_exec_result.
  - destruct mr as [macc addr addr_space size num_tag].
    destruct num_tag as [|num_tag].
    + destruct eret as [u|abort] eqn:Heret.
      * destruct u.
        exact (run_outcome_memwrite_promise_replay_one
          tid initmem macc addr addr_space size value tags
          ppst ppst' vpre Hrun).
      * exfalso.
        simp run_outcome in Hrun.
        inv_exec_result.
    + exfalso.
      simp run_outcome in Hrun.
      inv_exec_result.
  - exfalso.
    destruct b as [dsb|dmb|[]|[]|[]|[]].
    + destruct (DxB_types dsb) eqn:?;
        simp run_outcome in Hrun; cbn in Hrun; inv_exec_result.
    + destruct (DxB_types dmb) eqn:?;
        simp run_outcome in Hrun; cbn in Hrun; inv_exec_result.
    + simp run_outcome in Hrun; cbn in Hrun; inv_exec_result.
    + simp run_outcome in Hrun; inv_exec_result.
    + simp run_outcome in Hrun; inv_exec_result.
    + simp run_outcome in Hrun; inv_exec_result.
Qed.


Ltac solve_max_le :=
  first [apply Nat.le_refl |
    match goal with
    | |- Nat.max _ _ ≤ _ => apply Nat.max_lub; solve_max_le
    | |- ?x ≤ Nat.max ?a ?b =>
      first [eapply (Nat.le_trans x a); [solve_max_le|apply Nat.le_max_l] |
        eapply (Nat.le_trans x b); [solve_max_le|apply Nat.le_max_r]]
    end].
Lemma write_mem_new_order_view_bound tid addr size macc val ppst ppst' pre :
  Exec.elem_of_results (ppst', Some pre) (write_mem tid addr size macc val ppst) →
  IIS.strict (PPState.iis ppst) ⊔ TState.min_new_prom_view (PPState.state ppst) ≤ pre.
Proof.
  destruct ppst as [ts mem iis]. intro Hrun.
  unfold write_mem in Hrun.
  UMMemoryGrowth.invert_execution; subst; try discriminate.
  all: cbn; unfold TState.min_new_prom_view, join, join_nat; cbn.
  all: solve_max_le.
Qed.

Lemma run_outcome_new_order_view_bound tid imem out ppst ppst' ret pre :
  Exec.elem_of_results (ppst', (ret, Some pre)) (run_outcome tid imem out ppst) →
  IIS.strict (PPState.iis ppst) ⊔ TState.min_new_prom_view (PPState.state ppst) ≤ pre.
Proof.
  intro Hrun. funelim (run_outcome tid imem out ppst).
  all: rewrite <- Heqcall in Hrun.
  all: UMMemoryGrowth.invert_execution; subst; try discriminate.
  all: eapply write_mem_new_order_view_bound; eassumption.
Qed.

End UMSailReplay.

(** The unique updating outcome of an actual Sail instruction can be replayed
    after promising its new message. The surrounding instruction prefix and
    suffix are not transformed by this lemma. *)
Lemma UMSail_instruction_updating_outcome_replay nondet {n} (tid : fin n)
    initmem ppst ppst' :
  Exec.elem_of_results (ppst', ())
    (cinterp (UMPromising.run_outcome' tid initmem) (sail_tiny_arm_sem nondet) ppst) →
  PPState.mem ppst' ≠ PPState.mem ppst →
  ∃ msg out before after ret pre,
    Msg.tid msg = (tid : nat) ∧
    PPState.mem ppst' = msg :: PPState.mem ppst ∧
    PPState.mem before = PPState.mem ppst ∧
    PPState.mem after = PPState.mem ppst' ∧
    pre ≤ length (PPState.mem ppst) ∧
    Exec.elem_of_results (after, (ret, Some pre))
      (UMPromising.run_outcome tid initmem out before) ∧
    Exec.elem_of_results (after, (ret, None))
      (UMPromising.run_outcome tid initmem out
        (PPState.Make
          (UMPromising.TState.promise (S (length (PPState.mem ppst))) (PPState.state before))
          (msg :: PPState.mem before) (PPState.iis before))).
Proof.
  intros Hrun Hchanged.
  assert (Hone : PPState.mem ppst' = PPState.mem ppst ∨
    UpdatingOutcomeWitness UMPromising tid initmem (PPState.mem ppst) (PPState.mem ppst')).
  { eapply (one_update_instruction_memory UMPromising tid initmem).
    - intros. eapply UMSailMemory.outcome_no_update_mem; eassumption.
    - apply sail_tiny_arm_at_most_one_update.
    - exact Hrun. }
  destruct Hone as [Hsame|[out [before [after [ret [vpre [_ [Hbefore [Hafter Hout]]]]]]]]];
    [contradiction|].
  destruct (UMMemoryGrowth.outcome_memory_growth n tid initmem out before after ret vpre Hout)
    as [Hsame|[extra [pre [_ [_ [Hpre _]]]]]].
  - rewrite Hbefore, Hafter in Hsame. contradiction.
  - subst vpre.
    destruct (UMSailReplay.run_outcome_promise_replay_one
      tid initmem out before after ret pre Hout) as [msg [Hmem [Htid [Hbound Hreplay]]]].
    exists msg, out, before, after, ret, pre.
    rewrite Hbefore in Hbound. rewrite Hbefore, Hafter in Hmem.
    repeat split; try assumption.
    rewrite <- Hbefore. exact Hreplay.
Qed.
