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

From ASCommon Require Import Options.
From ASCommon Require Import Common GRel Exec FMon StateT HVec.

From ArchSem Require Import GenPromising.
Require Import ArmInst VMPromising.

#[local] Open Scope list.
#[local] Open Scope nat.
#[local] Open Scope stdpp.

Import Promising.

#[local] Typeclasses Transparent Memory.t.

Lemma promise_event_newer_than_mem ev (mem : Memory.t) :
  (length mem < length (ev :: mem))%nat.
Proof.
  cbn.
  lia.
Qed.

Lemma promise_event_lookup_latest ev (mem : Memory.t) :
  ((ev :: mem : Memory.t) !! length (ev :: mem)) = Some ev.
Proof.
  apply PromMemory.lookup_latest.
Qed.

Lemma promise_event_lookup_old ev (mem : Memory.t) t :
  (t ≤ length mem)%nat →
  ((ev :: mem : Memory.t) !! t) = mem !! t.
Proof.
  apply PromMemory.lookup_cons_old.
Qed.

Lemma promise_event_cut_before_old ev (mem : Memory.t) t :
  (t ≤ length mem)%nat →
  Memory.cut_before t (ev :: mem) = Memory.cut_before t mem.
Proof.
  apply PromMemory.cut_before_cons_old.
Qed.

Definition VMPromising_promise_ppstate (bbm_param : BBM.param)
    tid initmem ev ppst : PPState.t TState.t Ev.t IIS.t :=
  let mem := ev :: PPState.mem ppst in
  PPState.Make
    (emit_promise' tid initmem mem ev (PPState.state ppst))
    mem
    (PPState.iis ppst).

Definition TState_promise_event (ev : Ev.t) (p : view) : TState.t → TState.t :=
  if ev is Ev.Msg _ then TState.promise_write p else TState.promise_tlbi p.

Lemma VMPromising_promise_ppstate_mem (bbm_param : BBM.param)
    tid initmem ev ppst :
  PPState.mem
    (VMPromising_promise_ppstate bbm_param tid initmem ev ppst) =
  ev :: PPState.mem ppst.
Proof.
  reflexivity.
Qed.

Lemma VMPromising_promise_ppstate_old_mem_lt (bbm_param : BBM.param)
    tid initmem ev ppst :
  (length (PPState.mem ppst) <
   length (PPState.mem
     (VMPromising_promise_ppstate bbm_param tid initmem ev ppst)))%nat.
Proof.
  cbn.
  lia.
Qed.

Lemma TState_reg_map_promise (ev : Ev.t) v ts :
  TState.reg_map (TState_promise_event ev v ts) = TState.reg_map ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma VMPromising_promise_tid_reg_map (bbm_param : BBM.param) {n}
    (tid_p tid : fin n) (ev : Ev.t) (st : CPState.t TState.t Ev.t n) :
  TState.reg_map
    (CPState.tstate tid
       (CPState.promise_tid (VMPromising bbm_param) tid_p ev st)) =
  TState.reg_map (CPState.tstate tid st).
Proof.
  destruct st as [tstates initmem events].
  unfold CPState.promise_tid, CPState.tstate.
  cbn.
  destruct (decide (tid = tid_p)) as [->|Hne].
  - autorewrite with vec.
    apply TState_reg_map_promise.
  - unfold alter.
    cbn.
    rewrite vlookup_insert_ne by congruence.
    reflexivity.
Qed.

Lemma VMPromising_terminated_tid_promise (bbm_param : BBM.param) {n}
    (term : terminationCondition n) (tid_p tid : fin n)
    (ev : Ev.t) (st : CPState.t TState.t Ev.t n) :
  CPState.terminated_tid (VMPromising bbm_param) term
    (CPState.promise_tid (VMPromising bbm_param) tid_p ev st) tid =
  CPState.terminated_tid (VMPromising bbm_param) term st tid.
Proof.
  unfold CPState.terminated_tid.
  cbn.
  rewrite VMPromising_promise_tid_reg_map.
  reflexivity.
Qed.

Lemma TState_promise_update_vspec (ev : Ev.t) p v ts :
  TState.update TState.vspec v (TState_promise_event ev p ts) =
  TState_promise_event ev p (TState.update TState.vspec v ts).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_update_vdmb (ev : Ev.t) p v ts :
  TState.update TState.vdmb v (TState_promise_event ev p ts) =
  TState_promise_event ev p (TState.update TState.vdmb v ts).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_update_vdmbst (ev : Ev.t) p v ts :
  TState.update TState.vdmbst v (TState_promise_event ev p ts) =
  TState_promise_event ev p (TState.update TState.vdmbst v ts).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_update_vdsb (ev : Ev.t) p v ts :
  TState.update TState.vdsb v (TState_promise_event ev p ts) =
  TState_promise_event ev p (TState.update TState.vdsb v ts).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_update_vcse (ev : Ev.t) p v ts :
  TState.update TState.vcse v (TState_promise_event ev p ts) =
  TState_promise_event ev p (TState.update TState.vcse v ts).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_update_vmsr (ev : Ev.t) p v ts :
  TState.update TState.vmsr v (TState_promise_event ev p ts) =
  TState_promise_event ev p (TState.update TState.vmsr v ts).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vrd (ev : Ev.t) p ts :
  TState.vrd (TState_promise_event ev p ts) = TState.vrd ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vwr (ev : Ev.t) p ts :
  TState.vwr (TState_promise_event ev p ts) = TState.vwr ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vdmb (ev : Ev.t) p ts :
  TState.vdmb (TState_promise_event ev p ts) = TState.vdmb ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vdmbst (ev : Ev.t) p ts :
  TState.vdmbst (TState_promise_event ev p ts) = TState.vdmbst ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vspec (ev : Ev.t) p ts :
  TState.vspec (TState_promise_event ev p ts) = TState.vspec ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vdsb (ev : Ev.t) p ts :
  TState.vdsb (TState_promise_event ev p ts) = TState.vdsb ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vcse (ev : Ev.t) p ts :
  TState.vcse (TState_promise_event ev p ts) = TState.vcse ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vmsr (ev : Ev.t) p ts :
  TState.vmsr (TState_promise_event ev p ts) = TState.vmsr ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vacq (ev : Ev.t) p ts :
  TState.vacq (TState_promise_event ev p ts) = TState.vacq ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vrel (ev : Ev.t) p ts :
  TState.vrel (TState_promise_event ev p ts) = TState.vrel ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_cse (ev : Ev.t) p v ts :
  TState.cse v (TState_promise_event ev p ts) =
  TState_promise_event ev p (TState.cse v ts).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_add_wsreg (ev : Ev.t) p reg val v ts :
  TState.add_wsreg reg val v (TState_promise_event ev p ts) =
  TState_promise_event ev p (TState.add_wsreg reg val v ts).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_relaxed_write (ev : Ev.t) p reg val vpost ts :
  TState.update TState.vmsr vpost
    (TState.add_wsreg reg val vpost (TState_promise_event ev p ts)) =
  TState_promise_event ev p
    (TState.update TState.vmsr vpost
       (TState.add_wsreg reg val vpost ts)).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_relaxed_write_pc (ev : Ev.t) p reg val vreg vpost ts :
  TState.update TState.vmsr vpost
    (TState.add_wsreg reg val vpost
       (TState.update TState.vspec vreg (TState_promise_event ev p ts))) =
  TState_promise_event ev p
    (TState.update TState.vmsr vpost
       (TState.add_wsreg reg val vpost
          (TState.update TState.vspec vreg ts))).
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_set_reg_promise (ev : Ev.t) p reg rv ts ts' :
  TState.set_reg reg rv ts = Some ts' →
  TState.set_reg reg rv (TState_promise_event ev p ts) =
  Some (TState_promise_event ev p ts').
Proof.
  destruct ts as [prom_wr prom_tlbi regs levs coh vrd vwr vdmbst vdmb vdsb
    vspec vcse vtlbi vmsr vacq vrel fwdb xclb].
  unfold TState.set_reg, TState_promise_event.
  cbn.
  destruct ev; cbn;
  destruct (decide (is_Some (dmap_lookup reg regs))) as [Hsome|Hnone];
    cbn; intro Hset; inversion Hset; subst; reflexivity.
Qed.

Lemma elem_of_seq_bounds_mono x lo hi hi' :
  (hi ≤ hi')%nat →
  x ∈ seq_bounds lo hi →
  x ∈ seq_bounds lo hi'.
Proof.
  unfold seq_bounds.
  rewrite !elem_of_seq.
  lia.
Qed.

Lemma TState_min_promise_le_succ vmax ts :
  (TState.min_promise vmax ts ≤ S vmax)%nat.
Proof.
  unfold TState.min_promise.
  induction (TState.prom_wr ts ++ TState.prom_tlbi ts) as [|p ps IH];
    cbn; lia.
Qed.

Lemma foldr_min_gt_inv v base ps :
  (v < foldr (λ p acc, min acc p) base ps)%nat →
  (v < base)%nat ∧ ∀ p, p ∈ ps → (v < p)%nat.
Proof.
  induction ps as [|p ps IH]; cbn; intro Hlt.
  - split; [exact Hlt|].
    intros p' Hp'.
    apply not_elem_of_nil in Hp'.
    contradiction.
  - assert (Hp : (v < p)%nat) by lia.
    assert (Hps : (v < foldr (λ p acc, min acc p) base ps)%nat) by lia.
    pose proof (IH Hps) as [Hbase Hmem].
    split; [exact Hbase|].
    intros p' Hp'.
    apply elem_of_cons in Hp' as [->|Hp']; [exact Hp|].
    apply Hmem.
    exact Hp'.
Qed.

Lemma foldr_min_gt v base ps :
  (v < base)%nat →
  (∀ p, p ∈ ps → (v < p)%nat) →
  (v < foldr (λ p acc, min acc p) base ps)%nat.
Proof.
  induction ps as [|p ps IH]; cbn; intros Hbase Hmem.
  - exact Hbase.
  - assert (Hp : (v < p)%nat).
    { apply Hmem.
      apply elem_of_cons; left; reflexivity. }
    assert (Hps : (v < foldr (λ p acc, min acc p) base ps)%nat).
    { apply IH; [exact Hbase|].
      intros p' Hp'.
      apply Hmem.
      apply elem_of_cons; right; exact Hp'. }
    lia.
Qed.

Lemma TState_cse_candidate_vpre_le_vmax vpre vmax ts v :
  v ∈ TState.cse_candidates vpre vmax ts →
  (vpre ≤ vmax)%nat.
Proof.
  unfold TState.cse_candidates.
  rewrite elem_of_seq.
  pose proof (TState_min_promise_le_succ vmax ts).
  lia.
Qed.

Lemma TState_cse_candidate_promise_event ev vpre vmax p ts v :
  (vmax < p)%nat →
  v ∈ TState.cse_candidates vpre vmax ts →
  v ∈ TState.cse_candidates vpre p (TState_promise_event ev p ts).
Proof.
  intros Hlt Hin.
  unfold TState.cse_candidates in Hin |- *.
  rewrite elem_of_seq in Hin.
  destruct Hin as [Hvpre Hvold].
  pose proof (TState_min_promise_le_succ vmax ts) as Hmin_old_le.
  assert (Hvold_min : (v < TState.min_promise vmax ts)%nat) by lia.
  assert (Hv_lt_p : (v < p)%nat) by lia.
  unfold TState.min_promise in Hvold_min.
  pose proof
    (foldr_min_gt_inv v (vmax + 1)
       (TState.prom_wr ts ++ TState.prom_tlbi ts) Hvold_min)
    as [_ Hold].
  rewrite elem_of_seq.
  split; [exact Hvpre|].
  assert
    (Hvnew_min :
       (v < TState.min_promise p (TState_promise_event ev p ts))%nat).
  { unfold TState.min_promise, TState_promise_event.
    destruct ev as [msg|tlbi]; destruct ts; cbn in *.
    - assert
        (Hold_new :
           (v < foldr (λ p acc : nat, acc `min` p) (p + 1)
                  (prom_wr ++ prom_tlbi))%nat).
      { apply foldr_min_gt; [lia|exact Hold]. }
      lia.
    - apply foldr_min_gt; [lia|].
      intros p' Hp'.
      apply elem_of_app in Hp' as [Hp'|Hp'].
      + apply Hold. apply elem_of_app. left. exact Hp'.
      + apply elem_of_cons in Hp' as [->|Hp']; [exact Hv_lt_p|].
        apply Hold. apply elem_of_app. right. exact Hp'. }
  lia.
Qed.

Lemma TState_cse_candidate_promise_event_same_bound ev vpre vmax p ts v :
  (vmax < p)%nat →
  v ∈ TState.cse_candidates vpre vmax ts →
  v ∈ TState.cse_candidates vpre vmax (TState_promise_event ev p ts).
Proof.
  intros Hlt Hin.
  unfold TState.cse_candidates in Hin |- *.
  rewrite elem_of_seq in Hin.
  destruct Hin as [Hvpre Hvold].
  pose proof (TState_min_promise_le_succ vmax ts) as Hmin_old_le.
  assert (Hvold_min : (v < TState.min_promise vmax ts)%nat) by lia.
  assert (Hv_lt_p : (v < p)%nat) by lia.
  unfold TState.min_promise in Hvold_min.
  pose proof
    (foldr_min_gt_inv v (vmax + 1)
       (TState.prom_wr ts ++ TState.prom_tlbi ts) Hvold_min)
    as [Hbase_old Hold].
  rewrite elem_of_seq.
  split; [exact Hvpre|].
  assert
    (Hvnew_min :
       (v < TState.min_promise vmax (TState_promise_event ev p ts))%nat).
  { unfold TState.min_promise, TState_promise_event.
    destruct ev as [msg|tlbi]; destruct ts; cbn in *.
    - assert
        (Hold_new :
           (v < foldr (λ p acc : nat, acc `min` p) (vmax + 1)
                  (prom_wr ++ prom_tlbi))%nat).
      { apply foldr_min_gt; [exact Hbase_old|exact Hold]. }
      lia.
    - apply foldr_min_gt; [exact Hbase_old|].
      intros p' Hp'.
      apply elem_of_app in Hp' as [Hp'|Hp'].
      + apply Hold. apply elem_of_app. left. exact Hp'.
      + apply elem_of_cons in Hp' as [->|Hp']; [exact Hv_lt_p|].
        apply Hold. apply elem_of_app. right. exact Hp'. }
  lia.
Qed.

Lemma TState_no_promises_until_promise_event ev v p ts :
  TState.no_promises_until v ts →
  (v < p)%nat →
  TState.no_promises_until v (TState_promise_event ev p ts).
Proof.
  unfold TState.no_promises_until, TState_promise_event.
  destruct ev as [msg|tlbi]; destruct ts; cbn; intros Hno Hlt p' Hp'.
  - apply elem_of_cons in Hp' as [->|Hp']; [exact Hlt|].
    apply Hno. exact Hp'.
  - apply elem_of_app in Hp' as [Hp'|Hp'].
    + apply Hno. apply elem_of_app. left. exact Hp'.
    + apply elem_of_cons in Hp' as [->|Hp']; [exact Hlt|].
      apply Hno. apply elem_of_app. right. exact Hp'.
Qed.

Lemma TState_read_sreg_direct_promise (ev : Ev.t) p ts reg :
  TState.read_sreg_direct (TState_promise_event ev p ts) reg =
  TState.read_sreg_direct ts reg.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_read_sreg_indirect_promise (ev : Ev.t) p ts reg :
  TState.read_sreg_indirect (TState_promise_event ev p ts) reg =
  TState.read_sreg_indirect ts reg.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_read_reg_promise (ev : Ev.t) p ts reg :
  TState.read_reg (TState_promise_event ev p ts) reg = TState.read_reg ts reg.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma ets3_promise (ev : Ev.t) p ts :
  ets3 (TState_promise_event ev p ts) = ets3 ts.
Proof.
  unfold ets3.
  rewrite TState_read_reg_promise.
  reflexivity.
Qed.

Lemma read_fault_vpre_promise_state (ev : Ev.t) p is_acq trans_time
    ts iis ts' iis' v :
  Exec.elem_of_results ((ts', iis'), v)
    (read_fault_vpre is_acq trans_time (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), v)
    (read_fault_vpre is_acq trans_time (TState_promise_event ev p ts, iis)).
Proof.
  intro Hrun.
  unfold read_fault_vpre in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_iis [iis0 [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  apply Exec.elem_of_mret_inv in Hrun as [Heq Hv].
  inversion Heq; subst ts' iis'.
  inversion Hv; subst v.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
  - apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := iis).
    + apply (Exec.elem_of_mget (E:=string)
        (TState_promise_event ev p ts, iis) snd).
    + cbn.
      rewrite TState_promise_vdmb, TState_promise_vdsb,
        TState_promise_vcse, TState_promise_vacq,
        TState_promise_vrel, TState_promise_vmsr.
      apply Exec.elem_of_mret.
Qed.

Lemma read_fault_vpre_state is_acq trans_time ts iis ts' iis' v :
  Exec.elem_of_results ((ts', iis'), v)
    (read_fault_vpre is_acq trans_time (ts, iis)) →
  ts' = ts ∧ iis' = iis.
Proof.
  intro Hrun.
  unfold read_fault_vpre in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_iis [iis0 [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  apply Exec.elem_of_mret_inv in Hrun as [Heq _].
  inversion Heq; subst.
  split; reflexivity.
Qed.

Lemma write_fault_vpre_promise_state (ev : Ev.t) p is_rel trans_time
    ts iis ts' iis' v :
  Exec.elem_of_results ((ts', iis'), v)
    (write_fault_vpre is_rel trans_time (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), v)
    (write_fault_vpre is_rel trans_time (TState_promise_event ev p ts, iis)).
Proof.
  intro Hrun.
  unfold write_fault_vpre in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_iis [iis0 [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  apply Exec.elem_of_mret_inv in Hrun as [Heq Hv].
  inversion Heq; subst ts' iis'.
  inversion Hv; subst v.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
  - apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := iis).
    + apply (Exec.elem_of_mget (E:=string)
        (TState_promise_event ev p ts, iis) snd).
    + cbn.
      rewrite TState_promise_vspec, TState_promise_vdmbst,
        TState_promise_vdmb, TState_promise_vdsb,
        TState_promise_vcse, TState_promise_vacq,
        TState_promise_vrd, TState_promise_vwr,
        TState_promise_vmsr.
      apply Exec.elem_of_mret.
Qed.

Lemma write_fault_vpre_state is_rel trans_time ts iis ts' iis' v :
  Exec.elem_of_results ((ts', iis'), v)
    (write_fault_vpre is_rel trans_time (ts, iis)) →
  ts' = ts ∧ iis' = iis.
Proof.
  intro Hrun.
  unfold write_fault_vpre in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_iis [iis0 [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  apply Exec.elem_of_mret_inv in Hrun as [Heq _].
  inversion Heq; subst.
  split; reflexivity.
Qed.

Lemma run_cse_future_promise_state (ev : Ev.t) p vmax ts iis ts' iis' u :
  (vmax < p)%nat →
  Exec.elem_of_results ((ts', iis'), u) (run_cse vmax (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), u)
    (run_cse p (TState_promise_event ev p ts, iis)).
Proof.
  intros Hlt Hrun.
  unfold run_cse in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_iis [iis0 [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  cbn in Hrun.
  set (vpre :=
    IIS.strict iis ⊔
    (((TState.vspec ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)
       ⊔ TState.vmsr ts)) in *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_guard [Hno_promises [Hguard Hrun]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_choose [vpost [Hchoose Hrun]]].
  apply Exec.elem_of_mchoosel_inv in Hchoose as [-> Hin].
  apply Exec.elem_of_bind_elim in Hrun as
    [st_cse [[] [Hcse Hrun]]].
  apply Exec.elem_of_mSet_inv in Hcse as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_get_iis [st_mid [Hget_iis Hrun]]].
  apply Exec.elem_of_mGet_inv in Hget_iis as [-> ->].
  unfold elem_of, Exec.elem_of_results in Hrun.
  cbn in Hrun.
  apply elem_of_list_singleton in Hrun.
  inversion Hrun; subst ts' iis' u.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
  - apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := iis).
    + apply (Exec.elem_of_mget (E:=string)
        (TState_promise_event ev p ts, iis) snd).
    + cbn.
      rewrite TState_promise_vspec, TState_promise_vcse,
        TState_promise_vdsb, TState_promise_vmsr.
      fold vpre.
      assert (Hvpre_lt_p : (vpre < p)%nat).
      { eapply Nat.le_lt_trans; [|exact Hlt].
        eapply TState_cse_candidate_vpre_le_vmax.
        exact Hin. }
      destruct (Exec.elem_of_guard_discard
        (St:=TState.t * IIS.t) (E:=string)
        (P:=TState.no_promises_until vpre
              (TState_promise_event ev p ts))
        (TState_promise_event ev p ts, iis))
        as [Hno_promises' Hguard'].
      { apply TState_no_promises_until_promise_event; assumption. }
      eapply Exec.elem_of_bind_intro with
        (e := guard_discard
                (TState.no_promises_until vpre
                   (TState_promise_event ev p ts)))
        (st' := (TState_promise_event ev p ts, iis))
        (a := Hno_promises').
      * exact Hguard'.
      * cbn.
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev p ts, iis)) (a := vpost).
        -- apply Exec.elem_of_mchoosel.
           eapply TState_cse_candidate_promise_event; [exact Hlt|exact Hin].
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p (TState.cse vpost ts), iis))
             (a := ()).
        --- rewrite <- TState_promise_cse.
            change (TState.cse vpost (TState_promise_event ev p ts), iis)
              with (set fst (TState.cse vpost) (TState_promise_event ev p ts, iis)).
            apply Exec.elem_of_mset.
        --- change
             (Exec.elem_of_results
                (set snd (IIS.add vpost)
                   (TState_promise_event ev p (TState.cse vpost ts), iis), ())
                ((mset snd (IIS.add vpost) :
                    Exec.t (TState.t * IIS.t) string unit)
                   (TState_promise_event ev p (TState.cse vpost ts), iis))).
           eapply (@Exec.elem_of_mset
             (TState.t * IIS.t)%type string IIS.t
                (TState_promise_event ev p (TState.cse vpost ts), iis)
             snd _ (IIS.add vpost)).
Qed.

Lemma run_cse_promise_state (ev : Ev.t) p vmax ts iis ts' iis' u :
  (vmax < p)%nat →
  Exec.elem_of_results ((ts', iis'), u) (run_cse vmax (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), u)
    (run_cse vmax (TState_promise_event ev p ts, iis)).
Proof.
  intros Hlt Hrun.
  unfold run_cse in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_iis [iis0 [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  cbn in Hrun.
  set (vpre :=
    IIS.strict iis ⊔
    (((TState.vspec ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)
       ⊔ TState.vmsr ts)) in *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_guard [Hno_promises [Hguard Hrun]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_choose [vpost [Hchoose Hrun]]].
  apply Exec.elem_of_mchoosel_inv in Hchoose as [-> Hin].
  apply Exec.elem_of_bind_elim in Hrun as
    [st_cse [[] [Hcse Hrun]]].
  apply Exec.elem_of_mSet_inv in Hcse as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_get_iis [st_mid [Hget_iis Hrun]]].
  apply Exec.elem_of_mGet_inv in Hget_iis as [-> ->].
  unfold elem_of, Exec.elem_of_results in Hrun.
  cbn in Hrun.
  apply elem_of_list_singleton in Hrun.
  inversion Hrun; subst ts' iis' u.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
  - apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := iis).
    + apply (Exec.elem_of_mget (E:=string)
        (TState_promise_event ev p ts, iis) snd).
    + cbn.
      rewrite TState_promise_vspec, TState_promise_vcse,
        TState_promise_vdsb, TState_promise_vmsr.
      fold vpre.
      assert (Hvpre_lt_p : (vpre < p)%nat).
      { eapply Nat.le_lt_trans; [|exact Hlt].
        eapply TState_cse_candidate_vpre_le_vmax.
        exact Hin. }
      destruct (Exec.elem_of_guard_discard
        (St:=TState.t * IIS.t) (E:=string)
        (P:=TState.no_promises_until vpre
              (TState_promise_event ev p ts))
        (TState_promise_event ev p ts, iis))
        as [Hno_promises' Hguard'].
      { apply TState_no_promises_until_promise_event; assumption. }
      eapply Exec.elem_of_bind_intro with
        (e := guard_discard
                (TState.no_promises_until vpre
                   (TState_promise_event ev p ts)))
        (st' := (TState_promise_event ev p ts, iis))
        (a := Hno_promises').
      * exact Hguard'.
      * cbn.
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev p ts, iis)) (a := vpost).
        -- apply Exec.elem_of_mchoosel.
           eapply TState_cse_candidate_promise_event_same_bound;
             [exact Hlt|exact Hin].
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p (TState.cse vpost ts), iis))
             (a := ()).
        --- rewrite <- TState_promise_cse.
            change (TState.cse vpost (TState_promise_event ev p ts), iis)
              with (set fst (TState.cse vpost) (TState_promise_event ev p ts, iis)).
            apply Exec.elem_of_mset.
        --- change
             (Exec.elem_of_results
                (set snd (IIS.add vpost)
                   (TState_promise_event ev p (TState.cse vpost ts), iis), ())
                ((mset snd (IIS.add vpost) :
                    Exec.t (TState.t * IIS.t) string unit)
                   (TState_promise_event ev p (TState.cse vpost ts), iis))).
           eapply (@Exec.elem_of_mset
             (TState.t * IIS.t)%type string IIS.t
             (TState_promise_event ev p (TState.cse vpost ts), iis)
             snd _ (IIS.add vpost)).
Qed.

Lemma run_take_exception_future_promise_state (ev : Ev.t) p vmax fault ts iis
    ts' iis' u :
  (∀ inv_time, IIS.inv_time iis = Some inv_time → (inv_time < p)%nat) →
  (vmax < p)%nat →
  Exec.elem_of_results ((ts', iis'), u)
    (run_take_exception fault vmax (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), u)
    (run_take_exception fault p (TState_promise_event ev p ts, iis)).
Proof.
  intros Hinv_lt Hlt Hrun.
  unfold run_take_exception in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_iis [iis0 [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  cbn in Hrun.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := iis).
  - apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) snd).
  - cbn.
    destruct (IIS.inv_time iis) as [inv_time|] eqn:Hinv.
    + eapply run_cse_promise_state.
      * apply Hinv_lt.
        reflexivity.
      * exact Hrun.
    + eapply run_cse_future_promise_state.
      * exact Hlt.
      * exact Hrun.
Qed.

Lemma run_trans_end_promise_state (ev : Ev.t) p trans_end ts iis ts' iis' u :
  Exec.elem_of_results ((ts', iis'), u)
    (run_trans_end trans_end (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), u)
    (run_trans_end trans_end (TState_promise_event ev p ts, iis)).
Proof.
  intro Hrun.
  destruct u.
  unfold run_trans_end in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_iis [iis0 [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  cbn in Hrun.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
  - apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := iis).
    + apply (Exec.elem_of_mget (E:=string)
        (TState_promise_event ev p ts, iis) snd).
    + cbn.
      destruct (IIS.trs iis) as [trs|] eqn:Htrs.
      2: {
        unfold elem_of, Exec.elem_of_results in Hrun.
        cbn in Hrun.
        inversion Hrun.
      }
	      destruct
	        (decide (FaultRecord_statuscode (AddressDescriptor_fault trans_end)
	                 = Fault_None)) as [Hno_fault|Hfault].
	      * apply Exec.elem_of_bind_elim in Hrun as
	          [st_add [[] [Hadd Hrun]]].
	        apply Exec.elem_of_mset_inv in Hadd as ->.
	        change (set snd (IIS.add (IIS.TransRes.time trs)) (ts, iis))
	          with (ts, IIS.add (IIS.TransRes.time trs) iis) in Hrun.
	        unfold msetv in Hrun.
	        change
	          (Exec.elem_of_results (ts', iis', ())
	             ((mset (IIS.trs ∘ snd)
	                 (λ _ : option IIS.TransRes.t, None) :
	                 Exec.t (TState.t * IIS.t) string unit)
	                (ts, IIS.add (IIS.TransRes.time trs) iis))) in Hrun.
	        apply Exec.elem_of_mset_inv in Hrun as Heq.
	        inversion Heq; subst ts' iis'.
	        eapply Exec.elem_of_bind_intro with
	          (st' := (TState_promise_event ev p ts,
	                   IIS.add (IIS.TransRes.time trs) iis))
	          (a := ()).
	        -- change (TState_promise_event ev p ts,
	                IIS.add (IIS.TransRes.time trs) iis)
	             with
	             (set snd (IIS.add (IIS.TransRes.time trs))
	                (TState_promise_event ev p ts, iis)).
	           apply Exec.elem_of_mset.
	        -- unfold msetv.
	           change
	             (Exec.elem_of_results
	                (set (IIS.trs ∘ snd) (λ _ : option IIS.TransRes.t, None)
	                   (TState_promise_event ev p ts,
	                    IIS.add (IIS.TransRes.time trs) iis), ())
	                ((mset (IIS.trs ∘ snd)
	                    (λ _ : option IIS.TransRes.t, None) :
	                     Exec.t (TState.t * IIS.t) string unit)
	                   (TState_promise_event ev p ts,
	                    IIS.add (IIS.TransRes.time trs) iis))).
	           apply Exec.elem_of_mset.
      * apply Exec.elem_of_bind_elim in Hrun as
          [st_ets [is_ets3 [Hets Hrun]]].
        apply Exec.elem_of_lift_res_inv in Hets as [-> Hets].
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev p ts, iis)) (a := is_ets3).
        -- apply Exec.elem_of_lift_res.
           rewrite ets3_promise.
           exact Hets.
        -- cbn.
	           destruct
	             (is_ets3 &&
	              (IIS.TransRes.time trs <?
	               max (TState.vrd ts) (TState.vwr ts))) eqn:Hdiscard.
           ++ unfold elem_of, Exec.elem_of_results in Hrun.
              rewrite Hdiscard in Hrun.
              cbn in Hrun.
              exfalso.
              apply (not_elem_of_nil ((ts', iis'), ())).
              exact Hrun.
           ++ rewrite Hdiscard in Hrun.
              cbn in Hrun.
              apply Exec.elem_of_bind_elim in Hrun as
                [st_add_trans [[] [Hadd_trans Hrun]]].
              apply Exec.elem_of_mset_inv in Hadd_trans as ->.
              apply Exec.elem_of_bind_elim in Hrun as
                [st_read [read_view [Hread Hrun]]].
              change (set snd (IIS.add (IIS.TransRes.time trs)) (ts, iis))
                with (ts, IIS.add (IIS.TransRes.time trs) iis) in Hread.
              destruct st_read as [ts_read iis_read0].
              pose proof (read_fault_vpre_state _ _ _ _ _ _ _ Hread)
                as [-> ->].
              apply Exec.elem_of_bind_elim in Hrun as
                [st_add_read [[] [Hadd_read Hrun]]].
              apply Exec.elem_of_mset_inv in Hadd_read as ->.
              apply Exec.elem_of_bind_elim in Hrun as
                [st_write [write_view [Hwrite Hrun]]].
              change
                (set snd
                   (IIS.add
                      (view_if
                         (AccessDescriptor_read
                            (FaultRecord_access
                               (AddressDescriptor_fault trans_end)))
                         read_view))
                   (ts, IIS.add (IIS.TransRes.time trs) iis))
                with
                (ts,
                 IIS.add
                   (view_if
                      (AccessDescriptor_read
                         (FaultRecord_access
                            (AddressDescriptor_fault trans_end)))
                      read_view)
                   (IIS.add (IIS.TransRes.time trs) iis)) in Hwrite.
              destruct st_write as [ts_write iis_write0].
              pose proof (write_fault_vpre_state _ _ _ _ _ _ _ Hwrite)
                as [-> ->].
              apply Exec.elem_of_bind_elim in Hrun as
                [st_add_write [[] [Hadd_write Hrun]]].
              apply Exec.elem_of_mset_inv in Hadd_write as Hadd_write_eq.
              change
                (Exec.elem_of_results (ts', iis', ())
                   ((mset (IIS.trs ∘ snd)
                       (λ _ : option IIS.TransRes.t, None) :
                       Exec.t (TState.t * IIS.t) string unit)
                      (st_add_write))) in Hrun.
              apply Exec.elem_of_mset_inv in Hrun as Heq.
              inversion Heq; subst ts' iis'.
              subst st_add_write.
              set (iis_trans := IIS.add (IIS.TransRes.time trs) iis).
              set (is_read :=
                AccessDescriptor_read
                  (FaultRecord_access (AddressDescriptor_fault trans_end))).
              set (is_acq :=
                AccessDescriptor_acqsc
                  (FaultRecord_access (AddressDescriptor_fault trans_end))).
              set (iis_read :=
                IIS.add (view_if is_read read_view) iis_trans).
              set (is_write :=
                AccessDescriptor_write
                  (FaultRecord_access (AddressDescriptor_fault trans_end))).
              set (is_rel :=
                AccessDescriptor_relsc
                  (FaultRecord_access (AddressDescriptor_fault trans_end))).
              rewrite TState_promise_vrd.
              rewrite TState_promise_vwr.
              rewrite Hdiscard.
              cbn.
              eapply Exec.elem_of_bind_intro with
                (st' := (TState_promise_event ev p ts, iis_trans)) (a := ()).
              ** subst iis_trans.
                 change
                   (Exec.elem_of_results
                      (set snd (IIS.add (IIS.TransRes.time trs))
                         (TState_promise_event ev p ts, iis), ())
                      ((mset snd (IIS.add (IIS.TransRes.time trs)) :
                          Exec.t (TState.t * IIS.t) string unit)
                         (TState_promise_event ev p ts, iis))).
                 apply Exec.elem_of_mset.
              ** cbn.
                 eapply Exec.elem_of_bind_intro with
                   (st' := (TState_promise_event ev p ts, iis_trans))
                   (a := read_view).
                 --- subst is_acq iis_trans.
                     eapply read_fault_vpre_promise_state.
                     exact Hread.
                 --- cbn.
                     eapply Exec.elem_of_bind_intro with
                       (st' := (TState_promise_event ev p ts, iis_read)) (a := ()).
                     +++ subst iis_read.
                         change
                           (Exec.elem_of_results
                              (set snd
                                 (IIS.add (view_if is_read read_view))
                                 (TState_promise_event ev p ts, iis_trans), ())
                              ((mset snd
                                  (IIS.add (view_if is_read read_view)) :
                                  Exec.t (TState.t * IIS.t) string unit)
                                 (TState_promise_event ev p ts, iis_trans))).
                         apply Exec.elem_of_mset.
                     +++ cbn.
                         eapply Exec.elem_of_bind_intro with
                           (st' := (TState_promise_event ev p ts, iis_read))
                           (a := write_view).
                         *** subst is_rel iis_read.
                             eapply write_fault_vpre_promise_state.
                             exact Hwrite.
                         *** cbn.
                             set (iis_write :=
                               IIS.add (view_if is_write write_view)
                                 iis_read).
                             eapply Exec.elem_of_bind_intro with
                               (st' := (TState_promise_event ev p ts, iis_write))
                               (a := ()).
                             ---- subst iis_write.
                                  change
                                    (Exec.elem_of_results
                                       (set snd
                                          (IIS.add
                                             (view_if is_write write_view))
                                          (TState_promise_event ev p ts, iis_read), ())
                                       ((mset snd
                                           (IIS.add
                                              (view_if is_write write_view)) :
                                           Exec.t (TState.t * IIS.t) string unit)
                                          (TState_promise_event ev p ts, iis_read))).
                                  apply Exec.elem_of_mset.
                             ---- cbn.
                                  unfold msetv.
                                  change
                                    (Exec.elem_of_results
                                       (set (IIS.trs ∘ snd)
                                          (λ _ : option IIS.TransRes.t, None)
                                          (TState_promise_event ev p ts, iis_write), ())
                                       ((mset (IIS.trs ∘ snd)
                                           (λ _ : option IIS.TransRes.t,
                                             None) :
                                           Exec.t (TState.t * IIS.t) string
                                             unit)
                                          (TState_promise_event ev p ts, iis_write))).
                                  apply Exec.elem_of_mset.
Qed.

Lemma run_barrier_dmb_promise_state (ev : Ev.t) p vmax dmb ts iis ts' iis' u :
  Exec.elem_of_results ((ts', iis'), u)
    (run_barrier (Barrier_DMB dmb) vmax (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), u)
    (run_barrier (Barrier_DMB dmb) p (TState_promise_event ev p ts, iis)).
Proof.
  intro Hrun.
  unfold run_barrier in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  destruct dmb.(DxB_types) eqn:Hdmb.
  - set (vpost := TState.vrd ts ⊔ TState.vcse ts ⊔ TState.vdsb ts).
    apply Exec.elem_of_bind_elim in Hrun as
      [st_state [[] [Hstate Hrun]]].
    apply Exec.elem_of_mset_inv in Hstate as ->.
    unfold elem_of, Exec.elem_of_results in Hrun.
    cbn in Hrun.
    apply elem_of_list_singleton in Hrun.
    inversion Hrun; subst ts' iis' u.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
    + apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
    + cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p (TState.update TState.vdmb vpost ts), iis))
      (a := ()).
      * subst vpost.
      rewrite <- TState_promise_update_vdmb.
      change (TState.update TState.vdmb
                ((TState.vrd ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)
                (TState_promise_event ev p ts), iis)
        with
        (set fst
           (TState.update TState.vdmb
              ((TState.vrd ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts))
           (TState_promise_event ev p ts, iis)).
      apply Exec.elem_of_mset.
      * change
        (Exec.elem_of_results
           (set snd
              (IIS.add ((TState.vrd ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts))
              (TState_promise_event ev p
                 (TState.update TState.vdmb
                    ((TState.vrd ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts) ts),
               iis), ())
           ((mset snd
               (IIS.add
                  ((TState.vrd ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)) :
                Exec.t (TState.t * IIS.t) string unit)
              (TState_promise_event ev p
                 (TState.update TState.vdmb
                    ((TState.vrd ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts) ts),
               iis))).
      apply Exec.elem_of_mset.
  - set (vpost := TState.vwr ts ⊔ TState.vcse ts ⊔ TState.vdsb ts).
    apply Exec.elem_of_bind_elim in Hrun as
      [st_state [[] [Hstate Hrun]]].
    apply Exec.elem_of_mset_inv in Hstate as ->.
    unfold elem_of, Exec.elem_of_results in Hrun.
    cbn in Hrun.
    apply elem_of_list_singleton in Hrun.
    inversion Hrun; subst ts' iis' u.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
    + apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
    + cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p (TState.update TState.vdmbst vpost ts), iis))
      (a := ()).
      * subst vpost.
      rewrite <- TState_promise_update_vdmbst.
      change (TState.update TState.vdmbst
                ((TState.vwr ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)
                (TState_promise_event ev p ts), iis)
        with
        (set fst
           (TState.update TState.vdmbst
              ((TState.vwr ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts))
           (TState_promise_event ev p ts, iis)).
      apply Exec.elem_of_mset.
      * change
        (Exec.elem_of_results
           (set snd
              (IIS.add ((TState.vwr ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts))
              (TState_promise_event ev p
                 (TState.update TState.vdmbst
                    ((TState.vwr ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts) ts),
               iis), ())
           ((mset snd
               (IIS.add
                  ((TState.vwr ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)) :
                Exec.t (TState.t * IIS.t) string unit)
              (TState_promise_event ev p
                 (TState.update TState.vdmbst
                    ((TState.vwr ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts) ts),
               iis))).
      apply Exec.elem_of_mset.
  - set (vpost :=
      TState.vrd ts ⊔ TState.vwr ts ⊔ TState.vcse ts ⊔ TState.vdsb ts).
    apply Exec.elem_of_bind_elim in Hrun as
      [st_state [[] [Hstate Hrun]]].
    apply Exec.elem_of_mset_inv in Hstate as ->.
    unfold elem_of, Exec.elem_of_results in Hrun.
    cbn in Hrun.
    apply elem_of_list_singleton in Hrun.
    inversion Hrun; subst ts' iis' u.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
    + apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
    + cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p (TState.update TState.vdmb vpost ts), iis))
      (a := ()).
      * subst vpost.
      rewrite <- TState_promise_update_vdmb.
      change (TState.update TState.vdmb
                (((TState.vrd ts ⊔ TState.vwr ts) ⊔ TState.vcse ts)
                   ⊔ TState.vdsb ts)
                (TState_promise_event ev p ts), iis)
        with
        (set fst
           (TState.update TState.vdmb
              (((TState.vrd ts ⊔ TState.vwr ts) ⊔ TState.vcse ts)
                 ⊔ TState.vdsb ts))
           (TState_promise_event ev p ts, iis)).
      apply Exec.elem_of_mset.
      * change
        (Exec.elem_of_results
           (set snd
              (IIS.add
                 (((TState.vrd ts ⊔ TState.vwr ts) ⊔ TState.vcse ts)
                    ⊔ TState.vdsb ts))
              (TState_promise_event ev p
                 (TState.update TState.vdmb
                    (((TState.vrd ts ⊔ TState.vwr ts) ⊔ TState.vcse ts)
                       ⊔ TState.vdsb ts) ts), iis), ())
           ((mset snd
               (IIS.add
                  (((TState.vrd ts ⊔ TState.vwr ts) ⊔ TState.vcse ts)
                     ⊔ TState.vdsb ts)) :
                Exec.t (TState.t * IIS.t) string unit)
              (TState_promise_event ev p
                 (TState.update TState.vdmb
                    (((TState.vrd ts ⊔ TState.vwr ts) ⊔ TState.vcse ts)
                       ⊔ TState.vdsb ts) ts), iis))).
      apply Exec.elem_of_mset.
Qed.

Lemma run_barrier_dsb_promise_state (ev : Ev.t) p vmax dsb ts iis ts' iis' u :
  Exec.elem_of_results ((ts', iis'), u)
    (run_barrier (Barrier_DSB dsb) vmax (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), u)
    (run_barrier (Barrier_DSB dsb) p (TState_promise_event ev p ts, iis)).
Proof.
  intro Hrun.
  unfold run_barrier in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_guard [p_domain [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hdomain.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
  - apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
  - cbn.
    destruct (Exec.elem_of_guard_or
      (St:=TState.t * IIS.t) (E:=string)
      (P:=DxB_domain dsb ≠ MBReqDomain_Nonshareable)
      (TState_promise_event ev p ts, iis)
      "Non-shareable barrier are not supported" Hdomain) as
      [p_domain' Hguard'].
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := p_domain').
    + exact Hguard'.
    + cbn.
      destruct dsb.(DxB_types) eqn:Hdsb.
      * set (vpost := TState.vrd ts ⊔ TState.vcse ts ⊔ TState.vdsb ts).
        apply Exec.elem_of_bind_elim in Hrun as
          [st_state [[] [Hstate Hrun]]].
        apply Exec.elem_of_mset_inv in Hstate as ->.
        unfold elem_of, Exec.elem_of_results in Hrun.
        cbn in Hrun.
        apply elem_of_list_singleton in Hrun.
        inversion Hrun; subst ts' iis' u.
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev p
                     (TState.update TState.vdsb vpost ts), iis))
          (a := ()).
        -- rewrite <- TState_promise_update_vdsb.
           change (TState.update TState.vdsb vpost (TState_promise_event ev p ts), iis)
             with
             (set fst (TState.update TState.vdsb vpost)
                (TState_promise_event ev p ts, iis)).
           apply Exec.elem_of_mset.
        -- change
             (Exec.elem_of_results
                (set snd (IIS.add vpost)
                   (TState_promise_event ev p
                      (TState.update TState.vdsb vpost ts), iis), ())
                ((mset snd (IIS.add vpost) :
                    Exec.t (TState.t * IIS.t) string unit)
                   (TState_promise_event ev p
                      (TState.update TState.vdsb vpost ts), iis))).
           apply Exec.elem_of_mset.
      * set (vpost := TState.vwr ts ⊔ TState.vcse ts ⊔ TState.vdsb ts).
        apply Exec.elem_of_bind_elim in Hrun as
          [st_state [[] [Hstate Hrun]]].
        apply Exec.elem_of_mset_inv in Hstate as ->.
        unfold elem_of, Exec.elem_of_results in Hrun.
        cbn in Hrun.
        apply elem_of_list_singleton in Hrun.
        inversion Hrun; subst ts' iis' u.
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev p
                     (TState.update TState.vdsb vpost ts), iis))
          (a := ()).
        -- rewrite <- TState_promise_update_vdsb.
           change (TState.update TState.vdsb vpost (TState_promise_event ev p ts), iis)
             with
             (set fst (TState.update TState.vdsb vpost)
                (TState_promise_event ev p ts, iis)).
           apply Exec.elem_of_mset.
        -- change
             (Exec.elem_of_results
                (set snd (IIS.add vpost)
                   (TState_promise_event ev p
                      (TState.update TState.vdsb vpost ts), iis), ())
                ((mset snd (IIS.add vpost) :
                    Exec.t (TState.t * IIS.t) string unit)
                   (TState_promise_event ev p
                      (TState.update TState.vdsb vpost ts), iis))).
           apply Exec.elem_of_mset.
      * set (vpost :=
          TState.vrd ts ⊔ TState.vwr ts ⊔ TState.vdmb ts ⊔
          TState.vdmbst ts ⊔ TState.vcse ts ⊔ TState.vdsb ts ⊔
          TState.vtlbi ts).
        apply Exec.elem_of_bind_elim in Hrun as
          [st_state [[] [Hstate Hrun]]].
        apply Exec.elem_of_mset_inv in Hstate as ->.
        unfold elem_of, Exec.elem_of_results in Hrun.
        cbn in Hrun.
        apply elem_of_list_singleton in Hrun.
        inversion Hrun; subst ts' iis' u.
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev p
                     (TState.update TState.vdsb vpost ts), iis))
          (a := ()).
        -- rewrite <- TState_promise_update_vdsb.
           change (TState.update TState.vdsb vpost (TState_promise_event ev p ts), iis)
             with
             (set fst (TState.update TState.vdsb vpost)
                (TState_promise_event ev p ts, iis)).
           apply Exec.elem_of_mset.
        -- change
             (Exec.elem_of_results
                (set snd (IIS.add vpost)
                   (TState_promise_event ev p
                      (TState.update TState.vdsb vpost ts), iis), ())
                ((mset snd (IIS.add vpost) :
                    Exec.t (TState.t * IIS.t) string unit)
                   (TState_promise_event ev p
                      (TState.update TState.vdsb vpost ts), iis))).
           apply Exec.elem_of_mset.
Qed.

Lemma run_reg_general_read_promise_state (ev : Ev.t) p reg racc ts iis ts' iis' rv :
  Exec.elem_of_results ((ts', iis'), rv)
    (run_reg_general_read reg racc (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), rv)
    (run_reg_general_read reg racc (TState_promise_event ev p ts, iis)).
Proof.
  intro Hrun.
  unfold run_reg_general_read in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  cbn in Hrun.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
  - apply (Exec.elem_of_mget (E:=string)
      (TState_promise_event ev p ts, iis) fst).
  - cbn.
    destruct (decide (reg ∈ relaxed_regs)) as [Hrel|Hnrel] eqn:Hrel_dec.
    + rewrite Hrel_dec in Hrun.
      cbn in Hrun.
      destruct (decide (is_Some racc)) as [Hracc|Hnracc]
        eqn:Hracc_dec.
      * cbn in Hrun.
        rewrite TState_read_sreg_direct_promise.
        rewrite Hrel_dec.
        destruct (TState.read_sreg_direct ts reg) as [rv0|] eqn:Hread.
        -- apply Exec.elem_of_mret_inv in Hrun as [Heq Hrv].
           inversion Heq; subst ts' iis'.
           inversion Hrv; subst rv0.
           apply Exec.elem_of_mret.
        -- unfold elem_of, Exec.elem_of_results in Hrun.
           cbn in Hrun.
           inversion Hrun.
      * cbn in Hrun.
        rewrite TState_read_sreg_indirect_promise.
        rewrite Hrel_dec.
        destruct (TState.read_sreg_indirect ts reg) as [rvs|] eqn:Hread.
        -- apply Exec.elem_of_bind_elim in Hrun as
             [st_vals [valvs [Hvals Hchoose]]].
           apply Exec.elem_of_mret_inv in Hvals as [Heq Hvalvs].
           inversion Heq; subst st_vals.
           inversion Hvalvs; subst valvs.
           apply Exec.elem_of_mchoosel_inv in Hchoose as [Heq Hin].
           inversion Heq; subst ts' iis'.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p ts, iis)) (a := rvs).
           ++ apply Exec.elem_of_mret.
           ++ apply Exec.elem_of_mchoosel.
              exact Hin.
        -- unfold elem_of, Exec.elem_of_results in Hrun.
           cbn in Hrun.
           inversion Hrun.
    + rewrite Hrel_dec in Hrun.
      cbn in Hrun.
      rewrite TState_read_reg_promise.
      rewrite Hrel_dec.
      destruct (TState.read_reg ts reg) as [rv0|] eqn:Hread.
      * apply Exec.elem_of_mret_inv in Hrun as [Heq Hrv].
        inversion Heq; subst ts' iis'.
        inversion Hrv; subst rv0.
        apply Exec.elem_of_mret.
      * unfold elem_of, Exec.elem_of_results in Hrun.
        cbn in Hrun.
        inversion Hrun.
Qed.

Lemma run_reg_trans_read_promise_state (ev : Ev.t) p reg racc trs ts ts' rv :
  Exec.elem_of_results (ts', rv)
    (run_reg_trans_read reg racc trs ts) →
  Exec.elem_of_results (TState_promise_event ev p ts', rv)
    (run_reg_trans_read reg racc trs (TState_promise_event ev p ts)).
Proof.
  intro Hrun.
  unfold run_reg_trans_read in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_guard [p_racc [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hracc.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  destruct (Exec.elem_of_guard_or
    (St:=TState.t) (E:=string) (P:=¬ is_Some racc)
    (TState_promise_event ev p ts)
    "Register read during the translation should be implicit" Hracc) as
    [p_racc' Hguard'].
  eapply Exec.elem_of_bind_intro with
    (st' := TState_promise_event ev p ts) (a := p_racc').
  - exact Hguard'.
  - cbn.
    apply Exec.elem_of_bind_elim in Hrun as
      [st_root [root [Hroot Hrun]]].
    unfold othrow in Hroot.
    destruct (IIS.TransRes.root trs) as [root0|] eqn:Hroot_eq.
    2: {
      unfold elem_of, Exec.elem_of_results in Hroot.
      cbn in Hroot.
      inversion Hroot.
    }
    apply Exec.elem_of_mret_inv in Hroot as [-> Hroot].
    inversion Hroot; subst root0.
    eapply Exec.elem_of_bind_intro with
      (st' := TState_promise_event ev p ts) (a := root).
    + unfold othrow.
      apply Exec.elem_of_mret.
    + cbn.
      destruct (decide (root.T1 = reg)) as [Heq_reg|Hneq_reg]
        eqn:Hreg_dec.
      * cbn in Hrun.
        apply Exec.elem_of_mret_inv in Hrun as [Heq Hrv].
        inversion Heq; subst ts'.
        inversion Hrv; subst rv.
        apply Exec.elem_of_mret.
      * cbn in Hrun.
        apply Exec.elem_of_bind_elim in Hrun as
          [st_read [ts0 [Hget Hrun]]].
        apply Exec.elem_of_mGet_inv in Hget as [-> ->].
        eapply Exec.elem_of_bind_intro with
          (st' := TState_promise_event ev p ts) (a := TState_promise_event ev p ts).
        -- apply Exec.elem_of_mGet.
        -- cbn.
           apply Exec.elem_of_bind_elim in Hrun as
             [st_guard2 [p_regs [Hguard2 Hrun]]].
           pose proof
             (Exec.elem_of_guard_or_prop _ _ _ _ Hguard2) as Hregs.
           apply Exec.elem_of_guard_or_inv in Hguard2 as ->.
           destruct (Exec.elem_of_guard_or
             (St:=TState.t) (E:=string)
             (P:=reg ∉ strict_regs ∧ reg ∉ relaxed_regs)
             (TState_promise_event ev p ts)
             ("The register should niether be relaxed nor strict: " ++
                pretty reg)%string Hregs) as [p_regs' Hguard2'].
           eapply Exec.elem_of_bind_intro with
             (st' := TState_promise_event ev p ts) (a := p_regs').
           ++ exact Hguard2'.
           ++ cbn.
              rewrite TState_read_reg_promise.
              unfold othrow in Hrun |- *.
              destruct (TState.read_reg ts reg) as [rv0|] eqn:Hread.
              ** apply Exec.elem_of_mret_inv in Hrun as [Heq Hrv].
                 inversion Heq; subst ts'.
                 inversion Hrv; subst rv0.
                 apply Exec.elem_of_mret.
              ** unfold elem_of, Exec.elem_of_results in Hrun.
                 cbn in Hrun.
                 inversion Hrun.
Qed.

Lemma run_reg_read_promise_state (ev : Ev.t) p reg racc ts iis ts' iis' val :
  Exec.elem_of_results ((ts', iis'), val)
    (run_reg_read reg racc (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), val)
    (run_reg_read reg racc (TState_promise_event ev p ts, iis)).
Proof.
  intro Hrun.
  unfold run_reg_read in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_read [[val0 view] [Hread Hrun]]].
  apply Exec.elem_of_bind_elim in Hread as
    [st_iis [iis0 [Hiis Hread]]].
  apply Exec.elem_of_mget_inv in Hiis as [-> ->].
  cbn in Hread.
  destruct (IIS.trs iis) as [trs|] eqn:Htrs.
  - apply Exec.elem_of_liftSt_inv in Hread as [ts_mid [Heq Hread]].
    inversion Heq; subst st_read.
    apply Exec.elem_of_bind_elim in Hrun as
      [st_iis' [[] [Hset Hret]]].
    apply Exec.elem_of_mset_inv in Hset as ->.
    apply Exec.elem_of_mret_inv in Hret as [Heq Hval].
    inversion Heq; subst ts' iis'.
    inversion Hval; subst val0.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts_mid, iis)) (a := (val, view)).
    + eapply Exec.elem_of_bind_intro with
        (st' := (TState_promise_event ev p ts, iis)) (a := iis).
      * apply (Exec.elem_of_mget (E:=string)
          (TState_promise_event ev p ts, iis) snd).
      * cbn.
        rewrite Htrs.
        change (TState_promise_event ev p ts_mid, iis) with
          (setv fst (TState_promise_event ev p ts_mid) (TState_promise_event ev p ts, iis)).
        eapply (Exec.elem_of_liftSt
          (TState_promise_event ev p ts, iis)
          (TState_promise_event ev p ts_mid)
          (val, view)
          fst).
        eapply run_reg_trans_read_promise_state.
        exact Hread.
    + cbn.
      eapply Exec.elem_of_bind_intro with
        (st' := (TState_promise_event ev p ts_mid, IIS.add view iis)) (a := ()).
      * change (TState_promise_event ev p ts_mid, IIS.add view iis) with
          (set snd (IIS.add view) (TState_promise_event ev p ts_mid, iis)).
        apply Exec.elem_of_mset.
      * cbn.
        apply Exec.elem_of_mret.
  - destruct st_read as [ts_mid iis_mid].
    apply Exec.elem_of_bind_elim in Hrun as
      [st_iis' [[] [Hset Hret]]].
    apply Exec.elem_of_mset_inv in Hset as ->.
    apply Exec.elem_of_mret_inv in Hret as [Heq Hval].
    inversion Heq; subst ts' iis'.
    inversion Hval; subst val0.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts_mid, iis_mid)) (a := (val, view)).
    + eapply Exec.elem_of_bind_intro with
        (st' := (TState_promise_event ev p ts, iis)) (a := iis).
      * apply (Exec.elem_of_mget (E:=string)
          (TState_promise_event ev p ts, iis) snd).
      * cbn.
        rewrite Htrs.
        eapply run_reg_general_read_promise_state.
        exact Hread.
    + cbn.
      eapply Exec.elem_of_bind_intro with
        (st' := (TState_promise_event ev p ts_mid, IIS.add view iis_mid)) (a := ()).
      * change (TState_promise_event ev p ts_mid, IIS.add view iis_mid) with
          (set snd (IIS.add view) (TState_promise_event ev p ts_mid, iis_mid)).
        apply Exec.elem_of_mset.
      * cbn.
        apply Exec.elem_of_mret.
Qed.

Lemma msetv_ppstate_state_result ts
    (ppst : PPState.t TState.t Ev.t IIS.t) :
  Exec.elem_of_results (setv PPState.state ts ppst, ())
    ((msetv PPState.state ts :
        Exec.t (PPState.t TState.t Ev.t IIS.t) string unit) ppst).
Proof.
  unfold msetv, setv.
  apply Exec.elem_of_mset.
Qed.

Lemma run_reg_write_promise_state (ev : Ev.t) p reg racc val ppst ppst' mem_new :
  Exec.elem_of_results (ppst', ()) (run_reg_write reg racc val ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), ())
    (run_reg_write reg racc val
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intro Hrun.
  destruct ppst as [ts mem iis].
  cbn in *.
  unfold run_reg_write in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_known [p_known [Hknown Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hknown)
    as Hknown_prop.
  apply Exec.elem_of_guard_or_inv in Hknown as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_racc [p_racc [Hracc Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hracc)
    as Hracc_prop.
  apply Exec.elem_of_guard_or_inv in Hracc as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_iis [iis0 [Hiis Hrun]]].
  apply Exec.elem_of_mget_inv in Hiis as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts0 [Hts Hrun]]].
  apply Exec.elem_of_mget_inv in Hts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vreg [vreg' [Hvreg Hrun]]].
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
    (P:=¬ is_reg_unknown reg)
    (PPState.Make (TState_promise_event ev p ts) mem_new iis)
    ("Cannot write to unknown register " ++ pretty reg)%string
    Hknown_prop) as [p_known' Hknown'].
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
    (P:=racc = None)
    (PPState.Make (TState_promise_event ev p ts) mem_new iis)
    "Non trivial write reg access types unsupported" Hracc_prop) as
    [p_racc' Hracc'].
  eapply Exec.elem_of_bind_intro with
    (st' := PPState.Make (TState_promise_event ev p ts) mem_new iis)
    (a := p_known').
  - exact Hknown'.
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make (TState_promise_event ev p ts) mem_new iis)
      (a := p_racc').
    + exact Hracc'.
    + cbn.
      eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make (TState_promise_event ev p ts) mem_new iis)
        (a := iis).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make (TState_promise_event ev p ts) mem_new iis) PPState.iis).
      * cbn.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make (TState_promise_event ev p ts) mem_new iis)
          (a := TState_promise_event ev p ts).
        -- apply (Exec.elem_of_mget (E:=string)
             (PPState.Make (TState_promise_event ev p ts) mem_new iis)
             PPState.state).
        -- cbn.
           destruct (reg =? pc_reg) eqn:Hpc.
           ++ apply Exec.elem_of_bind_elim in Hvreg as
                [pp_vspec [[] [Hvspec Hvreg]]].
              apply Exec.elem_of_mset_inv in Hvspec as ->.
              apply Exec.elem_of_mret_inv in Hvreg as [-> Hvreg].
              inversion Hvreg; subst vreg'.
              cbn in Hrun.
              eapply Exec.elem_of_bind_intro with
                (st' := PPState.Make
                          (TState.update TState.vspec (IIS.strict iis)
                             (TState_promise_event ev p ts))
                          mem_new iis)
                (a := 0%nat).
              ** eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState.update TState.vspec (IIS.strict iis)
                                (TState_promise_event ev p ts))
                             mem_new iis)
                   (a := ()).
                 --- change
                       (PPState.Make
                          (TState.update TState.vspec (IIS.strict iis)
                             (TState_promise_event ev p ts))
                          mem_new iis)
                       with
                       (set PPState.state
                          (TState.update TState.vspec (IIS.strict iis))
                          (PPState.Make (TState_promise_event ev p ts)
                             mem_new iis)).
                     apply Exec.elem_of_mset.
                 --- cbn.
                     apply Exec.elem_of_mret.
              ** cbn.
                 destruct (decide (reg ∈ relaxed_regs)) as [Hrel|Hnrel]
                   eqn:Hrel_dec.
                 --- rewrite Hrel_dec in Hrun.
                     cbn in Hrun.
                     apply Exec.elem_of_bind_elim in Hrun as
                       [pp_read [[val_read view] [Hread Hrun]]].
                     unfold othrow in Hread.
                     destruct (TState.read_sreg_direct ts reg)
                       as [[val0 view0]|] eqn:Hread_eq.
                     ++++ cbn in Hread.
                       apply Exec.elem_of_mret_inv in Hread as [-> Hread].
                       inversion Hread; subst val0 view0.
                       apply Exec.elem_of_bind_elim in Hrun as
                         [pp_ws [[] [Hws Hrun]]].
                       apply Exec.elem_of_mset_inv in Hws as ->.
                       apply Exec.elem_of_bind_elim in Hrun as
                         [pp_vmsr [[] [Hvmsr Hrun]]].
                       apply Exec.elem_of_mset_inv in Hvmsr as ->.
                       apply Exec.elem_of_mset_inv in Hrun as ->.
                       rewrite Hrel_dec.
                       rewrite TState_read_sreg_direct_promise.
                       rewrite Hread_eq.
                       cbn.
                       eapply Exec.elem_of_bind_intro with
                         (st' := PPState.Make
                                   (TState.update TState.vspec
                                      (IIS.strict iis)
                                      (TState_promise_event ev p ts))
                                   mem_new iis)
                         (a := (val_read, view)).
                       { apply Exec.elem_of_mret. }
                       cbn.
                       rewrite !TState_promise_vcse.
                       rewrite !TState_promise_vspec.
                       rewrite !TState_promise_vdsb.
                       eapply Exec.elem_of_bind_intro with
                         (st' := PPState.Make
                                   (TState.add_wsreg reg val_read
                                      (0 ⊔ (TState.vcse ts
                                            ⊔ TState.vspec ts
                                            ⊔ TState.vdsb ts ⊔ view))
                                      (TState.update TState.vspec
                                         (IIS.strict iis)
                                         (TState_promise_event ev p ts)))
                                   mem_new iis)
                         (a := ()).
                       {
                         change
                           (PPState.Make
                              (TState.add_wsreg reg val_read
                                 (0 ⊔ (TState.vcse ts
                                       ⊔ TState.vspec ts
                                       ⊔ TState.vdsb ts ⊔ view))
                                 (TState.update TState.vspec
                                    (IIS.strict iis)
                                    (TState_promise_event ev p ts)))
                              mem_new iis)
                           with
                           (set PPState.state
                              (TState.add_wsreg reg val_read
                                 (0 ⊔ (TState.vcse ts
                                       ⊔ TState.vspec ts
                                       ⊔ TState.vdsb ts ⊔ view)))
                              (PPState.Make
                                 (TState.update TState.vspec
                                    (IIS.strict iis)
                                    (TState_promise_event ev p ts))
                                 mem_new iis)).
                         apply Exec.elem_of_mset.
                       }
                       cbn.
                       eapply Exec.elem_of_bind_intro with
                         (st' := PPState.Make
                                   (TState.update TState.vmsr
                                      (0 ⊔ (TState.vcse ts
                                            ⊔ TState.vspec ts
                                            ⊔ TState.vdsb ts ⊔ view))
                                      (TState.add_wsreg reg val_read
                                         (0 ⊔ (TState.vcse ts
                                               ⊔ TState.vspec ts
                                               ⊔ TState.vdsb ts ⊔ view))
                                         (TState.update TState.vspec
                                            (IIS.strict iis)
                                            (TState_promise_event ev p ts))))
                                   mem_new iis)
                         (a := ()).
                       {
                         change
                           (PPState.Make
                              (TState.update TState.vmsr
                                 (0 ⊔ (TState.vcse ts
                                       ⊔ TState.vspec ts
                                       ⊔ TState.vdsb ts ⊔ view))
                                 (TState.add_wsreg reg val_read
                                    (0 ⊔ (TState.vcse ts
                                          ⊔ TState.vspec ts
                                          ⊔ TState.vdsb ts ⊔ view))
                                    (TState.update TState.vspec
                                       (IIS.strict iis)
                                       (TState_promise_event ev p ts))))
                              mem_new iis)
                           with
                           (set PPState.state
                              (TState.update TState.vmsr
                                 (0 ⊔ (TState.vcse ts
                                       ⊔ TState.vspec ts
                                       ⊔ TState.vdsb ts ⊔ view)))
                              (PPState.Make
                                 (TState.add_wsreg reg val_read
                                    (0 ⊔ (TState.vcse ts
                                          ⊔ TState.vspec ts
                                          ⊔ TState.vdsb ts ⊔ view))
                                    (TState.update TState.vspec
                                       (IIS.strict iis)
                                       (TState_promise_event ev p ts)))
                                 mem_new iis)).
                         apply Exec.elem_of_mset.
                       }
                       cbn.
                       rewrite <- TState_promise_relaxed_write_pc.
                       change
                         (PPState.Make
                            (TState.update TState.vmsr
                               (0 ⊔ (TState.vcse ts ⊔ TState.vspec ts
                                     ⊔ TState.vdsb ts ⊔ view))
                               (TState.add_wsreg reg val_read
                                  (0 ⊔ (TState.vcse ts
                                        ⊔ TState.vspec ts
                                        ⊔ TState.vdsb ts ⊔ view))
                                  (TState.update TState.vspec
                                     (IIS.strict iis)
                                     (TState_promise_event ev p ts))))
                            mem_new (IIS.add
                              (0 ⊔ (TState.vcse ts ⊔ TState.vspec ts
                                    ⊔ TState.vdsb ts ⊔ view)) iis))
                         with
                         (set PPState.iis
                            (IIS.add
                              (0 ⊔ (TState.vcse ts ⊔ TState.vspec ts
                                    ⊔ TState.vdsb ts ⊔ view)))
                            (PPState.Make
                               (TState.update TState.vmsr
                                  (0 ⊔ (TState.vcse ts ⊔ TState.vspec ts
                                        ⊔ TState.vdsb ts ⊔ view))
                                  (TState.add_wsreg reg val_read
                                     (0 ⊔ (TState.vcse ts
                                           ⊔ TState.vspec ts
                                           ⊔ TState.vdsb ts ⊔ view))
                                     (TState.update TState.vspec
                                        (IIS.strict iis)
                                        (TState_promise_event ev p ts))))
                               mem_new iis)).
                       change
                         (Exec.elem_of_results
                            (set PPState.iis
                               (IIS.add
                                  (0 ⊔ (TState.vcse ts
                                        ⊔ TState.vspec ts
                                        ⊔ TState.vdsb ts ⊔ view)))
                               (PPState.Make
                                  (TState.update TState.vmsr
                                     (0 ⊔ (TState.vcse ts
                                           ⊔ TState.vspec ts
                                           ⊔ TState.vdsb ts ⊔ view))
                                     (TState.add_wsreg reg val_read
                                        (0 ⊔ (TState.vcse ts
                                              ⊔ TState.vspec ts
                                              ⊔ TState.vdsb ts ⊔ view))
                                        (TState.update TState.vspec
                                           (IIS.strict iis)
                                           (TState_promise_event ev p ts))))
                                  mem_new iis), ())
                            ((mset PPState.iis
                                (IIS.add
                                  (0 ⊔ (TState.vcse ts
                                        ⊔ TState.vspec ts
                                        ⊔ TState.vdsb ts ⊔ view))):
                                Exec.t
                                  (PPState.t TState.t Ev.t IIS.t)
                                  string unit)
                               (PPState.Make
                                  (TState.update TState.vmsr
                                     (0 ⊔ (TState.vcse ts
                                           ⊔ TState.vspec ts
                                           ⊔ TState.vdsb ts ⊔ view))
                                     (TState.add_wsreg reg val_read
                                        (0 ⊔ (TState.vcse ts
                                              ⊔ TState.vspec ts
                                              ⊔ TState.vdsb ts ⊔ view))
                                        (TState.update TState.vspec
                                           (IIS.strict iis)
                                           (TState_promise_event ev p ts))))
                                  mem_new iis))).
                       apply Exec.elem_of_mset.
                     ++++ cbn in Hread.
                       exfalso.
                       apply (not_elem_of_nil (pp_read, (val_read, view))).
                       exact Hread.
                 --- rewrite Hrel_dec in Hrun.
                     cbn in Hrun.
                     apply Exec.elem_of_bind_elim in Hrun as
                       [pp_nts [nts [Hsetreg Hrun]]].
                     unfold othrow in Hsetreg.
                     destruct (TState.set_reg reg (val, 0%nat) ts)
                       as [nts0|] eqn:Hsetreg_eq.
                     ++++ rewrite Hsetreg_eq in Hsetreg.
                       cbn in Hsetreg.
                       apply Exec.elem_of_mret_inv in Hsetreg as
                         [-> Hsetreg].
                       inversion Hsetreg; subst nts0.
                       unfold msetv in Hrun.
                       apply Exec.elem_of_mSet_inv in Hrun as ->.
                       rewrite Hrel_dec.
                       rewrite (TState_set_reg_promise p reg
                         (val, 0%nat) ts nts Hsetreg_eq).
                       cbn.
                       eapply Exec.elem_of_bind_intro with
                         (st' := PPState.Make
                                   (TState.update TState.vspec
                                      (IIS.strict iis)
                                      (TState_promise_event ev p ts))
                                   mem_new iis)
                         (a := TState_promise_event ev p nts).
                       { apply Exec.elem_of_mret. }
                       cbn.
                       change
                         (Exec.elem_of_results
                            (PPState.Make (TState_promise_event ev p nts)
                               mem_new iis, ())
                            ((msetv PPState.state
                                (TState_promise_event ev p nts) :
                                Exec.t
                                  (PPState.t TState.t Ev.t IIS.t)
                                  string unit)
                               (PPState.Make
                                  (TState.update TState.vspec
                                     (IIS.strict iis)
                                     (TState_promise_event ev p ts))
                                  mem_new iis))).
                       change (PPState.Make (TState_promise_event ev p nts)
                                 mem_new iis)
                         with
                         (setv PPState.state (TState_promise_event ev p nts)
                            (PPState.Make
                               (TState.update TState.vspec
                                  (IIS.strict iis)
                                  (TState_promise_event ev p ts))
                               mem_new iis)).
                       apply msetv_ppstate_state_result.
                     ++++ rewrite Hsetreg_eq in Hsetreg.
                       cbn in Hsetreg.
                       exfalso.
                       apply (not_elem_of_nil (pp_nts, nts)).
                       exact Hsetreg.
           ++ apply Exec.elem_of_mret_inv in Hvreg as [-> Hvreg].
              inversion Hvreg; subst vreg'.
              cbn in Hrun.
              eapply Exec.elem_of_bind_intro with
                (st' := PPState.Make (TState_promise_event ev p ts) mem_new iis)
                (a := IIS.strict iis).
              ** apply Exec.elem_of_mret.
              ** cbn.
                 destruct (decide (reg ∈ relaxed_regs)) as [Hrel|Hnrel]
                   eqn:Hrel_dec.
                 --- rewrite Hrel_dec in Hrun.
                     cbn in Hrun.
                     apply Exec.elem_of_bind_elim in Hrun as
                       [pp_read [[val_read view] [Hread Hrun]]].
                     unfold othrow in Hread.
                     destruct (TState.read_sreg_direct ts reg)
                       as [[val0 view0]|] eqn:Hread_eq.
                     ++++ cbn in Hread.
                       apply Exec.elem_of_mret_inv in Hread as [-> Hread].
                       inversion Hread; subst val0 view0.
                       apply Exec.elem_of_bind_elim in Hrun as
                         [pp_ws [[] [Hws Hrun]]].
                       apply Exec.elem_of_mset_inv in Hws as ->.
                       apply Exec.elem_of_bind_elim in Hrun as
                         [pp_vmsr [[] [Hvmsr Hrun]]].
                       apply Exec.elem_of_mset_inv in Hvmsr as ->.
                       apply Exec.elem_of_mset_inv in Hrun as ->.
                       rewrite Hrel_dec.
                       rewrite TState_read_sreg_direct_promise.
                       rewrite Hread_eq.
                       cbn.
                       eapply Exec.elem_of_bind_intro with
                         (st' := PPState.Make (TState_promise_event ev p ts)
                                   mem_new iis)
                         (a := (val_read, view)).
                       { apply Exec.elem_of_mret. }
                       cbn.
                       rewrite !TState_promise_vcse.
                       rewrite !TState_promise_vspec.
                       rewrite !TState_promise_vdsb.
                       eapply Exec.elem_of_bind_intro with
                         (st' := PPState.Make
                                   (TState.add_wsreg reg val_read
                                      (IIS.strict iis
                                       ⊔ (TState.vcse ts
                                          ⊔ TState.vspec ts
                                          ⊔ TState.vdsb ts ⊔ view))
                                      (TState_promise_event ev p ts))
                                   mem_new iis)
                         (a := ()).
                       {
                         change
                           (PPState.Make
                              (TState.add_wsreg reg val_read
                                 (IIS.strict iis
                                  ⊔ (TState.vcse ts
                                     ⊔ TState.vspec ts
                                     ⊔ TState.vdsb ts ⊔ view))
                                 (TState_promise_event ev p ts))
                              mem_new iis)
                           with
                           (set PPState.state
                              (TState.add_wsreg reg val_read
                                 (IIS.strict iis
                                  ⊔ (TState.vcse ts
                                     ⊔ TState.vspec ts
                                     ⊔ TState.vdsb ts ⊔ view)))
                              (PPState.Make (TState_promise_event ev p ts)
                                 mem_new iis)).
                         apply Exec.elem_of_mset.
                       }
                       cbn.
                       eapply Exec.elem_of_bind_intro with
                         (st' := PPState.Make
                                   (TState.update TState.vmsr
                                      (IIS.strict iis
                                       ⊔ (TState.vcse ts
                                          ⊔ TState.vspec ts
                                          ⊔ TState.vdsb ts ⊔ view))
                                      (TState.add_wsreg reg val_read
                                         (IIS.strict iis
                                          ⊔ (TState.vcse ts
                                             ⊔ TState.vspec ts
                                             ⊔ TState.vdsb ts ⊔ view))
                                         (TState_promise_event ev p ts)))
                                   mem_new iis)
                         (a := ()).
                       {
                         change
                           (PPState.Make
                              (TState.update TState.vmsr
                                 (IIS.strict iis
                                  ⊔ (TState.vcse ts
                                     ⊔ TState.vspec ts
                                     ⊔ TState.vdsb ts ⊔ view))
                                 (TState.add_wsreg reg val_read
                                    (IIS.strict iis
                                     ⊔ (TState.vcse ts
                                        ⊔ TState.vspec ts
                                        ⊔ TState.vdsb ts ⊔ view))
                                    (TState_promise_event ev p ts)))
                              mem_new iis)
                           with
                           (set PPState.state
                              (TState.update TState.vmsr
                                 (IIS.strict iis
                                  ⊔ (TState.vcse ts
                                     ⊔ TState.vspec ts
                                     ⊔ TState.vdsb ts ⊔ view)))
                              (PPState.Make
                                 (TState.add_wsreg reg val_read
                                    (IIS.strict iis
                                     ⊔ (TState.vcse ts
                                        ⊔ TState.vspec ts
                                        ⊔ TState.vdsb ts ⊔ view))
                                    (TState_promise_event ev p ts))
                                 mem_new iis)).
                         apply Exec.elem_of_mset.
                       }
                       cbn.
                       rewrite <- TState_promise_relaxed_write.
                       change
                         (Exec.elem_of_results
                            (set PPState.iis
                               (IIS.add
                                  (IIS.strict iis
                                   ⊔ (TState.vcse ts
                                      ⊔ TState.vspec ts
                                      ⊔ TState.vdsb ts ⊔ view)))
                               (PPState.Make
                                  (TState.update TState.vmsr
                                     (IIS.strict iis
                                      ⊔ (TState.vcse ts
                                         ⊔ TState.vspec ts
                                         ⊔ TState.vdsb ts ⊔ view))
                                     (TState.add_wsreg reg val_read
                                        (IIS.strict iis
                                         ⊔ (TState.vcse ts
                                            ⊔ TState.vspec ts
                                            ⊔ TState.vdsb ts ⊔ view))
                                        (TState_promise_event ev p ts)))
                                  mem_new iis), ())
                            ((mset PPState.iis
                                (IIS.add
                                  (IIS.strict iis
                                   ⊔ (TState.vcse ts
                                      ⊔ TState.vspec ts
                                      ⊔ TState.vdsb ts ⊔ view))):
                                Exec.t
                                  (PPState.t TState.t Ev.t IIS.t)
                                  string unit)
                               (PPState.Make
                                  (TState.update TState.vmsr
                                     (IIS.strict iis
                                      ⊔ (TState.vcse ts
                                         ⊔ TState.vspec ts
                                         ⊔ TState.vdsb ts ⊔ view))
                                     (TState.add_wsreg reg val_read
                                        (IIS.strict iis
                                         ⊔ (TState.vcse ts
                                            ⊔ TState.vspec ts
                                            ⊔ TState.vdsb ts ⊔ view))
                                        (TState_promise_event ev p ts)))
                                  mem_new iis))).
                       apply Exec.elem_of_mset.
                     ++++ cbn in Hread.
                       exfalso.
                       apply (not_elem_of_nil (pp_read, (val_read, view))).
                       exact Hread.
                 --- rewrite Hrel_dec in Hrun.
                     cbn in Hrun.
                     apply Exec.elem_of_bind_elim in Hrun as
                       [pp_nts [nts [Hsetreg Hrun]]].
                     unfold othrow in Hsetreg.
                     destruct
                       (TState.set_reg reg (val, IIS.strict iis) ts)
                       as [nts0|] eqn:Hsetreg_eq.
                     ++++ cbn in Hsetreg.
                       apply Exec.elem_of_mret_inv in Hsetreg as
                         [-> Hsetreg].
                       inversion Hsetreg; subst nts0.
                       unfold msetv in Hrun.
                       apply Exec.elem_of_mSet_inv in Hrun as ->.
                       rewrite Hrel_dec.
                       rewrite (TState_set_reg_promise p reg
                         (val, IIS.strict iis) ts nts Hsetreg_eq).
                       cbn.
                       eapply Exec.elem_of_bind_intro with
                         (st' := PPState.Make (TState_promise_event ev p ts)
                                   mem_new iis)
                         (a := TState_promise_event ev p nts).
                       { apply Exec.elem_of_mret. }
                       cbn.
                       change
                         (Exec.elem_of_results
                            (PPState.Make (TState_promise_event ev p nts)
                               mem_new iis, ())
                            ((msetv PPState.state
                                (TState_promise_event ev p nts) :
                                Exec.t
                                  (PPState.t TState.t Ev.t IIS.t)
                                  string unit)
                               (PPState.Make (TState_promise_event ev p ts)
                                  mem_new iis))).
                       change (PPState.Make (TState_promise_event ev p nts)
                                 mem_new iis)
                         with
                         (setv PPState.state (TState_promise_event ev p nts)
                            (PPState.Make (TState_promise_event ev p ts)
                               mem_new iis)).
                       apply msetv_ppstate_state_result.
                     ++++ cbn in Hsetreg.
                       exfalso.
                       apply (not_elem_of_nil (pp_nts, nts)).
                       exact Hsetreg.
Qed.

Definition outcome_future_promise_stable_promised (bbm_param : BBM.param)
    tid initmem (ev : Ev.t) (out : outcome) : Prop :=
  ∀ ppst ppst' (eret : eff_ret out),
    Exec.elem_of_results (ppst', eret)
      ((run_outcome tid initmem out |$> fst) ppst) →
    Exec.elem_of_results
      (VMPromising_promise_ppstate bbm_param
         tid initmem ev ppst', eret)
      ((run_outcome tid initmem out |$> fst)
         (VMPromising_promise_ppstate bbm_param
            tid initmem ev ppst)).

Definition run_trans_start_future_promise_stable
    (bbm_param : BBM.param) tid initmem (ev : Ev.t)
    (trans_start : TranslationStartInfo) : Prop :=
  ∀ ppst ppst',
    Exec.elem_of_results (ppst', ())
      (run_trans_start trans_start tid
         (Memory.initial_from_memMap initmem) ppst) →
    Exec.elem_of_results
      (VMPromising_promise_ppstate bbm_param
         tid initmem ev ppst', ())
      (run_trans_start trans_start tid
         (Memory.initial_from_memMap initmem)
         (VMPromising_promise_ppstate bbm_param
            tid initmem ev ppst)).

Fixpoint imon_future_promise_stable_promised (bbm_param : BBM.param)
    tid initmem (ev : Ev.t) A (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next call k =>
      match call with
      | inl out =>
          outcome_future_promise_stable_promised
            bbm_param tid initmem ev out ∧
          ∀ eret,
            imon_future_promise_stable_promised
              bbm_param tid initmem ev A (k eret)
      | inr _ =>
          ∀ ret,
            imon_future_promise_stable_promised
              bbm_param tid initmem ev A (k ret)
      end
  end.

Lemma reg_read_outcome_promise_state_fmap (ev : Ev.t) tid initmem reg racc
    ppst ppst' p mem_new eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (RegRead reg racc) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (RegRead reg racc) |$> fst)
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intro Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_read [val [Hread Hrun]]].
  apply Exec.elem_of_liftSt_inv in Hread as [stiis' [Heq Hread]].
  destruct stiis' as [ts' iis'].
  apply Exec.elem_of_mret_inv in Hrun as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct ppst as [ts mem iis].
  cbn in *.
  change (setv (PPState.state ×× PPState.iis) (ts', iis')
            (PPState.Make ts mem iis))
    with (PPState.Make ts' mem iis') in Heq.
  inversion Heq; subst pp_read.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev p ts') mem_new iis',
          (val, None))
         (run_outcome tid initmem (RegRead reg racc)
            (PPState.Make (TState_promise_event ev p ts) mem_new iis))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := Exec.liftSt (PPState.state ×× PPState.iis)
              (run_reg_read reg racc))
      (st' := PPState.Make (TState_promise_event ev p ts') mem_new iis')
      (a := val).
    - change (PPState.Make (TState_promise_event ev p ts') mem_new iis')
        with
        (setv (PPState.state ×× PPState.iis)
           (TState_promise_event ev p ts', iis')
           (PPState.Make (TState_promise_event ev p ts) mem_new iis)).
      eapply (@Exec.elem_of_liftSt
        (PPState.t TState.t Ev.t IIS.t) (TState.t * IIS.t)%type string _
        (PPState.Make (TState_promise_event ev p ts) mem_new iis)
        (TState_promise_event ev p ts', iis') val
        (PPState.state ×× PPState.iis) _
        (run_reg_read reg racc)).
      eapply run_reg_read_promise_state.
      exact Hread.
    - cbn.
      apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma reg_read_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev reg racc :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (RegRead reg racc).
Proof.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_read [val [Hread Hraw]]].
    apply Exec.elem_of_liftSt_inv in Hread as [stiis' [Heq _]].
    apply Exec.elem_of_mret_inv in Hraw as [Heq_ret _].
    inversion Heq_ret; subst ppst'.
    destruct ppst as [ts mem iis].
    destruct stiis' as [ts' iis'].
    cbn in *.
    change (setv (PPState.state ×× PPState.iis) (ts', iis')
              (PPState.Make ts mem iis))
      with (PPState.Make ts' mem iis') in Heq.
    inversion Heq.
    reflexivity.
  }
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  rewrite Hmem.
  eapply reg_read_outcome_promise_state_fmap.
  exact Hrun.
Qed.

Lemma reg_write_outcome_promise_state_fmap (ev : Ev.t) tid initmem reg racc val
    ppst ppst' p mem_new eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (RegWrite reg racc val) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (RegWrite reg racc val) |$> fst)
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intro Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_write [[] [Hwrite Hrun]]].
  apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev p (PPState.state pp_write))
            mem_new (PPState.iis pp_write), ((), None))
         (run_outcome tid initmem (RegWrite reg racc val)
            (PPState.Make (TState_promise_event ev p (PPState.state ppst))
               mem_new (PPState.iis ppst)))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := run_reg_write reg racc val)
      (st' := PPState.Make (TState_promise_event ev p (PPState.state pp_write))
                mem_new (PPState.iis pp_write))
      (a := ()).
    - eapply run_reg_write_promise_state.
      exact Hwrite.
    - cbn.
      apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma reg_write_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev reg racc val :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (RegWrite reg racc val).
Proof.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_write [[] [Hwrite Hraw]]].
    apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
    inversion Heq; subst ppst'.
    inversion Hret; subst eret0 vpre_opt.
    eapply run_reg_write_preserves_mem.
    exact Hwrite.
  }
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  rewrite Hmem.
  eapply reg_write_outcome_promise_state_fmap.
  exact Hrun.
Qed.

Lemma mem_read_ifetch_outcome_promise_state_fmap (ev : Ev.t) tid initmem addr macc
    addr_space ppst ppst' p eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (MemRead (MemReq.make macc addr addr_space 4 0))
        |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       (PPState.mem ppst') (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (MemRead (MemReq.make macc addr addr_space 4 0))
        |$> fst)
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          (PPState.mem ppst) (PPState.iis ppst))).
Proof.
  intro Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [p_nss [Hguard Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_read [opcode [Hread Hrun]]].
  apply Exec.elem_of_liftSt_inv in Hread as [mem' [Heq Hread]].
  apply Exec.elem_of_mret_inv in Hrun as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct ppst as [ts mem iis].
  cbn in *.
  change (setv PPState.mem mem' (PPState.Make ts mem iis))
    with (PPState.Make ts mem' iis) in Heq.
  inversion Heq; subst pp_read.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev p ts) mem' iis,
          (Ok (opcode, 0%bv), None))
         (run_outcome tid initmem
            (MemRead (MemReq.make macc addr addr_space 4 0))
            (PPState.Make (TState_promise_event ev p ts) mem iis))).
  {
    simp run_outcome.
    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
      (P:=addr_space = PAS_NonSecure)
      (PPState.Make (TState_promise_event ev p ts) mem iis)
      "Access outside Non-Secure" p_nss) as [p_nss' Hguard'].
    eapply Exec.elem_of_bind_intro with
      (e := guard_or "Access outside Non-Secure"
              (addr_space = PAS_NonSecure))
      (st' := PPState.Make (TState_promise_event ev p ts) mem iis)
      (a := p_nss').
    - exact Hguard'.
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := Exec.liftSt PPState.mem
                (run_mem_read4 addr macc
                   (Memory.initial_from_memMap initmem)))
        (st' := PPState.Make (TState_promise_event ev p ts) mem' iis)
        (a := opcode).
      + change (PPState.Make (TState_promise_event ev p ts) mem' iis)
          with
          (setv PPState.mem mem'
             (PPState.Make (TState_promise_event ev p ts) mem iis)).
        eapply (@Exec.elem_of_liftSt
          (PPState.t TState.t Ev.t IIS.t) Memory.t string _
          (PPState.Make (TState_promise_event ev p ts) mem iis)
          mem' opcode PPState.mem _
          (run_mem_read4 addr macc
             (Memory.initial_from_memMap initmem))).
        exact Hread.
      + cbn.
        apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma mem_read_ifetch_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem code ev addr macc addr_space :
  event_misses_code code ev →
  ifetch_in_code code addr 4 →
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (MemRead (MemReq.make macc addr addr_space 4 0)).
Proof.
  intros Hmiss Hifetch ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_guard [p_nss [Hguard Hraw]]].
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    cbn in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_read [opcode [Hread Hraw]]].
    apply Exec.elem_of_liftSt_inv in Hread as [mem' [Heq Hread]].
    apply Exec.elem_of_mret_inv in Hraw as [Heq_ret Hret].
    inversion Heq_ret; subst ppst'.
    destruct ppst as [ts mem iis].
    cbn in *.
    change (setv PPState.mem mem' (PPState.Make ts mem iis))
      with (PPState.Make ts mem' iis) in Heq.
    inversion Heq; subst.
    eapply run_mem_read4_preserves_mem.
    exact Hread.
  }
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  set (p := length (ev :: PPState.mem ppst)).
  pose proof
    (mem_read_ifetch_outcome_promise_state_fmap
       tid initmem addr macc addr_space ppst ppst' p eret Hrun)
    as Hpromise.
  pose proof
    (run_outcome_future_promise_stable_fmap
       tid initmem code addr macc addr_space
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          (PPState.mem ppst) (PPState.iis ppst))
       (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
          (PPState.mem ppst') (PPState.iis ppst'))
       ev eret Hmiss Hifetch Hpromise) as Hfuture.
  subst p.
  cbn in Hfuture |- *.
  rewrite Hmem in Hfuture.
  rewrite Hmem.
  exact Hfuture.
Qed.

Lemma return_exception_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    ReturnException.
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_mem [mem0 [Hmem_get Hraw]]].
  apply Exec.elem_of_mget_inv in Hmem_get as [-> ->].
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_cse [[] [Hcse Hraw]]].
  apply Exec.elem_of_liftSt_inv in Hcse as [stiis' [Heq Hcse]].
  destruct stiis' as [ts' iis'].
  apply Exec.elem_of_mret_inv in Hraw as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct ppst as [ts mem iis].
  cbn in *.
  change (setv (PPState.state ×× PPState.iis) (ts', iis')
            (PPState.Make ts mem iis))
    with (PPState.Make ts' mem iis') in Heq.
  inversion Heq; subst pp_cse.
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
            (ev :: mem) iis', ((), None))
         (run_outcome tid initmem ReturnException
            (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
               (ev :: mem) iis))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := (mget PPState.mem :
               Exec.t (PPState.t TState.t Ev.t IIS.t) string Memory.t))
      (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)
      (a := ev :: mem).
    - apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
           (ev :: mem) iis) PPState.mem).
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := Exec.liftSt (PPState.state ×× PPState.iis)
                (run_cse (length (ev :: mem))))
        (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
                  (ev :: mem) iis')
        (a := ()).
      + change
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
             (ev :: mem) iis')
          with
          (setv (PPState.state ×× PPState.iis)
             (TState_promise_event ev (length (ev :: mem)) ts', iis')
             (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)).
        eapply (@Exec.elem_of_liftSt
          (PPState.t TState.t Ev.t IIS.t) (TState.t * IIS.t)%type
          string unit
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
             (ev :: mem) iis)
          (TState_promise_event ev (length (ev :: mem)) ts', iis') ()
          (PPState.state ×× PPState.iis) _
          (run_cse (length (ev :: mem)))).
        eapply (run_cse_future_promise_state
          (length (ev :: mem)) (length mem)).
        * cbn.
          lia.
        * exact Hcse.
      + cbn.
        apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma barrier_isb_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (Barrier (Barrier_ISB ())).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_mem [mem0 [Hmem_get Hraw]]].
  apply Exec.elem_of_mget_inv in Hmem_get as [-> ->].
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_barrier [[] [Hbarrier Hraw]]].
  apply Exec.elem_of_liftSt_inv in Hbarrier as [stiis' [Heq Hbarrier]].
  destruct stiis' as [ts' iis'].
  cbn in Hbarrier.
  apply Exec.elem_of_mret_inv in Hraw as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct ppst as [ts mem iis].
  cbn in *.
  unfold run_barrier in Hbarrier.
  cbn in Hbarrier.
  apply Exec.elem_of_bind_elim in Hbarrier as
    [st_bar_ts [ts0 [Hbar_get Hbarrier]]].
  apply Exec.elem_of_mget_inv in Hbar_get as [-> ->].
  cbn in Hbarrier.
  change (setv (PPState.state ×× PPState.iis) (ts', iis')
            (PPState.Make ts mem iis))
    with (PPState.Make ts' mem iis') in Heq.
  inversion Heq; subst pp_barrier.
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
            (ev :: mem) iis', ((), None))
         (run_outcome tid initmem (Barrier (Barrier_ISB ()))
            (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
               (ev :: mem) iis))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := (mget PPState.mem :
               Exec.t (PPState.t TState.t Ev.t IIS.t) string Memory.t))
      (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)
      (a := ev :: mem).
    - apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
           (ev :: mem) iis) PPState.mem).
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := Exec.liftSt (PPState.state ×× PPState.iis)
                (run_barrier (Barrier_ISB ()) (length (ev :: mem))))
        (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
                  (ev :: mem) iis')
        (a := ()).
      + change
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
             (ev :: mem) iis')
          with
          (setv (PPState.state ×× PPState.iis)
             (TState_promise_event ev (length (ev :: mem)) ts', iis')
             (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)).
        eapply (@Exec.elem_of_liftSt
          (PPState.t TState.t Ev.t IIS.t) (TState.t * IIS.t)%type
          string unit
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
             (ev :: mem) iis)
          (TState_promise_event ev (length (ev :: mem)) ts', iis') ()
          (PPState.state ×× PPState.iis) _
          (run_barrier (Barrier_ISB ()) (length (ev :: mem)))).
        unfold run_barrier.
        cbn.
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev (length (ev :: mem)) ts, iis))
          (a := TState_promise_event ev (length (ev :: mem)) ts).
        * apply (Exec.elem_of_mget (E:=string)
            (TState_promise_event ev (length (ev :: mem)) ts, iis) fst).
        * cbn.
          eapply (run_cse_future_promise_state
            (length (ev :: mem)) (length mem)).
          -- cbn.
             lia.
          -- exact Hbarrier.
      + cbn.
        apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma barrier_dmb_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev dmb :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (Barrier (Barrier_DMB dmb)).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_mem [mem0 [Hmem_get Hraw]]].
  apply Exec.elem_of_mget_inv in Hmem_get as [-> ->].
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_barrier [[] [Hbarrier Hraw]]].
  apply Exec.elem_of_liftSt_inv in Hbarrier as [stiis' [Heq Hbarrier]].
  destruct stiis' as [ts' iis'].
  apply Exec.elem_of_mret_inv in Hraw as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct ppst as [ts mem iis].
  cbn in *.
  change (setv (PPState.state ×× PPState.iis) (ts', iis')
            (PPState.Make ts mem iis))
    with (PPState.Make ts' mem iis') in Heq.
  inversion Heq; subst pp_barrier.
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
            (ev :: mem) iis', ((), None))
         (run_outcome tid initmem (Barrier (Barrier_DMB dmb))
            (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
               (ev :: mem) iis))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := (mget PPState.mem :
               Exec.t (PPState.t TState.t Ev.t IIS.t) string Memory.t))
      (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)
      (a := ev :: mem).
    - apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
           (ev :: mem) iis) PPState.mem).
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := Exec.liftSt (PPState.state ×× PPState.iis)
                (run_barrier (Barrier_DMB dmb) (length (ev :: mem))))
        (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
                  (ev :: mem) iis')
        (a := ()).
      + change
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
             (ev :: mem) iis')
          with
          (setv (PPState.state ×× PPState.iis)
             (TState_promise_event ev (length (ev :: mem)) ts', iis')
             (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)).
        eapply (@Exec.elem_of_liftSt
          (PPState.t TState.t Ev.t IIS.t) (TState.t * IIS.t)%type
          string unit
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
             (ev :: mem) iis)
          (TState_promise_event ev (length (ev :: mem)) ts', iis') ()
          (PPState.state ×× PPState.iis) _
          (run_barrier (Barrier_DMB dmb) (length (ev :: mem)))).
        eapply run_barrier_dmb_promise_state.
        exact Hbarrier.
      + cbn.
        apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma barrier_dsb_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev dsb :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (Barrier (Barrier_DSB dsb)).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_mem [mem0 [Hmem_get Hraw]]].
  apply Exec.elem_of_mget_inv in Hmem_get as [-> ->].
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_barrier [[] [Hbarrier Hraw]]].
  apply Exec.elem_of_liftSt_inv in Hbarrier as [stiis' [Heq Hbarrier]].
  destruct stiis' as [ts' iis'].
  apply Exec.elem_of_mret_inv in Hraw as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct ppst as [ts mem iis].
  cbn in *.
  change (setv (PPState.state ×× PPState.iis) (ts', iis')
            (PPState.Make ts mem iis))
    with (PPState.Make ts' mem iis') in Heq.
  inversion Heq; subst pp_barrier.
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
            (ev :: mem) iis', ((), None))
         (run_outcome tid initmem (Barrier (Barrier_DSB dsb))
            (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
               (ev :: mem) iis))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := (mget PPState.mem :
               Exec.t (PPState.t TState.t Ev.t IIS.t) string Memory.t))
      (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)
      (a := ev :: mem).
    - apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
           (ev :: mem) iis) PPState.mem).
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := Exec.liftSt (PPState.state ×× PPState.iis)
                (run_barrier (Barrier_DSB dsb) (length (ev :: mem))))
        (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
                  (ev :: mem) iis')
        (a := ()).
      + change
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
             (ev :: mem) iis')
          with
          (setv (PPState.state ×× PPState.iis)
             (TState_promise_event ev (length (ev :: mem)) ts', iis')
             (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)).
        eapply (@Exec.elem_of_liftSt
          (PPState.t TState.t Ev.t IIS.t) (TState.t * IIS.t)%type
          string unit
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
             (ev :: mem) iis)
          (TState_promise_event ev (length (ev :: mem)) ts', iis') ()
          (PPState.state ×× PPState.iis) _
          (run_barrier (Barrier_DSB dsb) (length (ev :: mem)))).
        eapply run_barrier_dsb_promise_state.
        exact Hbarrier.
      + cbn.
        apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma take_exception_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev fault :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (TakeException fault).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_mem [mem0 [Hmem_get Hraw]]].
  apply Exec.elem_of_mget_inv in Hmem_get as [-> ->].
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_take [[] [Htake Hraw]]].
  apply Exec.elem_of_liftSt_inv in Htake as [stiis' [Heq Htake]].
  destruct stiis' as [ts' iis'].
  apply Exec.elem_of_mret_inv in Hraw as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct ppst as [ts mem iis].
  cbn in *.
  change (setv (PPState.state ×× PPState.iis) (ts', iis')
            (PPState.Make ts mem iis))
    with (PPState.Make ts' mem iis') in Heq.
  inversion Heq; subst pp_take.
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
            (ev :: mem) iis', ((), None))
         (run_outcome tid initmem (TakeException fault)
            (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
               (ev :: mem) iis))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := (mget PPState.mem :
               Exec.t (PPState.t TState.t Ev.t IIS.t) string Memory.t))
      (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)
      (a := ev :: mem).
    - apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
           (ev :: mem) iis) PPState.mem).
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := Exec.liftSt (PPState.state ×× PPState.iis)
                (run_take_exception fault (length (ev :: mem))))
        (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
                  (ev :: mem) iis')
        (a := ()).
      + change
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
             (ev :: mem) iis')
          with
          (setv (PPState.state ×× PPState.iis)
             (TState_promise_event ev (length (ev :: mem)) ts', iis')
             (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
                (ev :: mem) iis)).
        eapply (@Exec.elem_of_liftSt
          (PPState.t TState.t Ev.t IIS.t) (TState.t * IIS.t)%type
          string unit
          (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
             (ev :: mem) iis)
          (TState_promise_event ev (length (ev :: mem)) ts', iis') ()
          (PPState.state ×× PPState.iis) _
          (run_take_exception fault (length (ev :: mem)))).
        eapply (run_take_exception_future_promise_state
          (length (ev :: mem)) (length mem)).
        * cbn.
          lia.
        * exact Htake.
      + cbn.
        apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma translation_start_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev trans_start :
  run_trans_start_future_promise_stable
    bbm_param tid initmem ev trans_start →
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (TranslationStart trans_start).
Proof.
  intros Hstable ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_trans [[] [Htrans Hraw]]].
  apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  assert
    (Hfull :
       Exec.elem_of_results
         (VMPromising_promise_ppstate bbm_param
            tid initmem ev pp_trans, ((), None))
         (run_outcome tid initmem (TranslationStart trans_start)
            (VMPromising_promise_ppstate bbm_param
               tid initmem ev ppst))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (st' := VMPromising_promise_ppstate bbm_param
                tid initmem ev pp_trans)
      (a := ()).
    - apply Hstable.
      exact Htrans.
    - cbn.
      apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma translation_end_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev trans_end :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (TranslationEnd trans_end).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_trans [[] [Htrans Hraw]]].
  apply Exec.elem_of_liftSt_inv in Htrans as [stiis' [Heq Htrans]].
  destruct stiis' as [ts' iis'].
  apply Exec.elem_of_mret_inv in Hraw as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct ppst as [ts mem iis].
  cbn in *.
  change (setv (PPState.state ×× PPState.iis) (ts', iis')
            (PPState.Make ts mem iis))
    with (PPState.Make ts' mem iis') in Heq.
  inversion Heq; subst pp_trans.
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
            (ev :: mem) iis', ((), None))
         (run_outcome tid initmem (TranslationEnd trans_end)
            (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
               (ev :: mem) iis))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := Exec.liftSt (PPState.state ×× PPState.iis)
              (run_trans_end trans_end))
      (st' := PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
                (ev :: mem) iis')
      (a := ()).
    - change
        (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts')
           (ev :: mem) iis')
        with
        (setv (PPState.state ×× PPState.iis)
           (TState_promise_event ev (length (ev :: mem)) ts', iis')
           (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
              (ev :: mem) iis)).
      eapply (@Exec.elem_of_liftSt
        (PPState.t TState.t Ev.t IIS.t) (TState.t * IIS.t)%type
        string unit
        (PPState.Make (TState_promise_event ev (length (ev :: mem)) ts)
           (ev :: mem) iis)
        (TState_promise_event ev (length (ev :: mem)) ts', iis') ()
        (PPState.state ×× PPState.iis) _
        (run_trans_end trans_end)).
      eapply run_trans_end_promise_state.
      exact Htrans.
    - cbn.
      apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma mem_write_addr_announce_outcome_promise_state_fmap (ev : Ev.t) tid initmem req
    ppst ppst' p mem_new eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (MemWriteAddrAnnounce req) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (MemWriteAddrAnnounce req) |$> fst)
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intro Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vaddr [vaddr [Hvaddr Hrun]]].
  apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_state [[] [Hstate Hrun]]].
  apply Exec.elem_of_mset_inv in Hstate as ->.
  apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  rewrite <- TState_promise_update_vspec.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make
            (TState.update TState.vspec (IIS.strict (PPState.iis ppst))
               (TState_promise_event ev p (PPState.state ppst)))
            mem_new (PPState.iis ppst), ((), None))
         (run_outcome tid initmem (MemWriteAddrAnnounce req)
            (PPState.Make (TState_promise_event ev p (PPState.state ppst))
               mem_new (PPState.iis ppst)))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := (mget (IIS.strict ∘ PPState.iis) :
               Exec.t (PPState.t TState.t Ev.t IIS.t) string nat))
      (st' := PPState.Make (TState_promise_event ev p (PPState.state ppst))
                mem_new (PPState.iis ppst))
      (a := IIS.strict (PPState.iis ppst)).
    - apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event ev p (PPState.state ppst))
           mem_new (PPState.iis ppst)) (IIS.strict ∘ PPState.iis)).
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.update TState.vspec
                     (IIS.strict (PPState.iis ppst))
                     (TState_promise_event ev p (PPState.state ppst)))
                  mem_new (PPState.iis ppst))
        (a := ()).
      + change
          (PPState.Make
             (TState.update TState.vspec
                (IIS.strict (PPState.iis ppst))
                (TState_promise_event ev p (PPState.state ppst)))
             mem_new (PPState.iis ppst))
          with
          (set PPState.state
             (TState.update TState.vspec (IIS.strict (PPState.iis ppst)))
             (PPState.Make (TState_promise_event ev p (PPState.state ppst))
                mem_new (PPState.iis ppst))).
        apply Exec.elem_of_mset.
      + cbn.
        apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  apply elem_of_list_singleton.
  reflexivity.
Qed.

Lemma mem_write_addr_announce_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev req :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (MemWriteAddrAnnounce req).
Proof.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_vaddr [vaddr [Hvaddr Hraw]]].
    apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_state [[] [Hstate Hraw]]].
    apply Exec.elem_of_mset_inv in Hstate as ->.
    apply Exec.elem_of_mret_inv in Hraw as [Heq _].
    inversion Heq; subst ppst'.
    reflexivity.
  }
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  rewrite Hmem.
  eapply mem_write_addr_announce_outcome_promise_state_fmap.
  exact Hrun.
Qed.

Lemma generic_fail_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev s :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (GenericFail s).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  unfold elem_of, Exec.elem_of_results in Hraw.
  cbn in Hraw.
  exfalso.
  apply (not_elem_of_nil (ppst', (eret0, vpre_opt))).
  exact Hraw.
Qed.

Lemma cache_op_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) tid initmem ev cop :
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (CacheOp cop).
Proof.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  unfold elem_of, Exec.elem_of_results in Hraw.
  cbn in Hraw.
  exfalso.
  apply (not_elem_of_nil (ppst', (eret0, vpre_opt))).
  exact Hraw.
Qed.

Lemma VMPromising_imon_future_promise_stable_promised_to_cmon
    (bbm_param : BBM.param) {n} (tid : fin n) initmem ev A
    (mon : iMon A) :
  imon_future_promise_stable_promised
    bbm_param (tid : nat) initmem ev A mon →
  CPState.cmon_handle_outcome_promise_ppstate_stable
    (VMPromising bbm_param) tid initmem ev A mon.
Proof.
  revert mon.
  induction mon as [a|call k IH]; intro Hstable.
  - cbn.
    exact I.
  - cbn in Hstable |- *.
    destruct call as [out|choice].
    + destruct Hstable as [Hout Hk].
      split.
      * exact Hout.
      * intro eret.
        apply IH.
        apply Hk.
    + intro ret.
      apply IH.
      apply Hstable.
Qed.

Lemma VMPromising_run_tid_promise_same_stable_from_imon
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) (tid : fin n) initmem ev st st' :
  initmem = CPState.initmem st →
  imon_future_promise_stable_promised
    bbm_param (tid : nat) initmem ev () isem →
  Exec.elem_of_results (st', ())
    (CPState.run_tid isem (VMPromising bbm_param) tid st) →
  Exec.elem_of_results
    (CPState.promise_tid (VMPromising bbm_param) tid ev st', ())
    (CPState.run_tid isem (VMPromising bbm_param) tid
       (CPState.promise_tid (VMPromising bbm_param) tid ev st)).
Proof.
  intros Hinit Hstable Hrun.
  eapply CPState.run_tid_promise_same_stable_mon.
  - exact Hinit.
  - apply (VMPromising_imon_future_promise_stable_promised_to_cmon
      bbm_param tid initmem ev () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Lemma VMPromising_run_to_termination_plain_promise_same_stable_from_imon
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) (tid : fin n)
    initmem ev fuel ppst ppst' b :
  imon_future_promise_stable_promised
    bbm_param (tid : nat) initmem ev () isem →
  Exec.elem_of_results (ppst', b)
    (CPState.run_to_termination_plain isem (VMPromising bbm_param) term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (VMPromising_promise_ppstate bbm_param
       tid initmem ev ppst', b)
    (CPState.run_to_termination_plain isem (VMPromising bbm_param) term
       tid initmem fuel
       (VMPromising_promise_ppstate bbm_param
          tid initmem ev ppst)).
Proof.
  intros Hstable Hrun.
  eapply CPState.run_to_termination_plain_promise_ppstate_stable_mon.
  - intro ppst0.
    destruct ppst0 as [ts mem iis0].
    cbn.
    rewrite TState_reg_map_promise.
    reflexivity.
  - apply (VMPromising_imon_future_promise_stable_promised_to_cmon
      bbm_param tid initmem ev () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Record VMPromising_tail_stable (bbm_param : BBM.param) {n}
    (isem : iMon ()) : Prop := {
    VMPromising_tail_same_promise_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (ev : Ev.t),
        imon_future_promise_stable_promised
          bbm_param (tid : nat) initmem ev () isem;
  }.

Fixpoint VMPromising_Sail_promised_stable (bbm_param : BBM.param)
    tid initmem ev nondet {A eo} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      imon_future_promise_stable_promised
        bbm_param tid initmem ev _ (Sail_outcome_interp nondet out) ∧
      ∀ ret,
        VMPromising_Sail_promised_stable
          bbm_param tid initmem ev nondet (k ret)
  end.

Lemma VMPromising_imon_promised_stable_bind
    (bbm_param : BBM.param) tid initmem ev
    {A B} (mon : iMon A) (k : A → iMon B) :
  imon_future_promise_stable_promised
    bbm_param tid initmem ev A mon →
  (∀ a,
    imon_future_promise_stable_promised
      bbm_param tid initmem ev B (k a)) →
  imon_future_promise_stable_promised
    bbm_param tid initmem ev B (a ← mon; k a).
Proof.
  revert k.
  induction mon as [a|call kmon IH]; intros k Hmon Hk; cbn in Hmon |- *.
  - apply Hk.
  - destruct call as [out|choice].
    + destruct Hmon as [Hout Hmon].
      split.
      * exact Hout.
      * intro eret.
        apply IH.
        -- apply Hmon.
        -- exact Hk.
    + intro ret.
      apply IH.
      * apply Hmon.
      * exact Hk.
Qed.

Lemma VMPromising_iMon_from_Sail_promised_stable
    (bbm_param : BBM.param) tid initmem ev nondet
    {A eo} (smon : SI.iMon eo A) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet smon →
  imon_future_promise_stable_promised
    bbm_param tid initmem ev A (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|out k IH]; cbn.
  - intro Hstable.
    exact I.
  - rename H into Hind.
    intros [Hout Hk].
    eapply VMPromising_imon_promised_stable_bind.
    + exact Hout.
    + intro eret.
      apply Hind.
      apply Hk.
Qed.

Record VMPromising_Sail_tail_stable (bbm_param : BBM.param)
    {n eo} nondet (smon : SI.iMon eo ()) : Prop := {
    VMPromising_Sail_tail_same_promise_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (ev : Ev.t),
        VMPromising_Sail_promised_stable
          bbm_param (tid : nat) initmem ev nondet smon;
  }.

Record VMPromising_Sail_same_promise_stable (bbm_param : BBM.param)
    {n eo} nondet (smon : SI.iMon eo ()) : Prop := {
    VMPromising_Sail_same_promised_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (ev : Ev.t),
        VMPromising_Sail_promised_stable
          bbm_param (tid : nat) initmem ev nondet smon;
  }.

Record VMPromising_read_code_translation_stability
    (bbm_param : BBM.param) (tid : nat)
    (initmem : memoryMap) (code : code_region) (ev : Ev.t) : Prop := {
    VMPromising_read_code_ifetch_stable :
      ∀ (addr : address) (macc : mem_acc)
          (addr_space : addr_space),
        event_misses_code code ev ∧ ifetch_in_code code addr 4;
    VMPromising_read_code_data_read_stable :
      ∀ (addr : address) (macc : mem_acc)
          (addr_space : addr_space),
        outcome_future_promise_stable_promised bbm_param tid initmem ev
          (MemRead (MemReq.make macc addr addr_space 8 0));
    VMPromising_read_code_translation_start_stable :
      ∀ trans_start,
        run_trans_start_future_promise_stable
          bbm_param tid initmem ev trans_start;
    VMPromising_read_code_tlbop_stable :
      ∀ tlbi,
        outcome_future_promise_stable_promised bbm_param tid initmem ev
          (TlbOp tlbi);
  }.

Lemma VMPromising_mem_read_ifetch_promised_stable_from_read_code_translation
    bbm_param tid initmem code ev addr macc addr_space :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (MemRead (MemReq.make macc addr addr_space 4 0)).
Proof.
  intro Hstable.
  destruct Hstable as [Hifetch _ _ _].
  destruct (Hifetch addr macc addr_space) as [Hmiss Hin].
  eapply mem_read_ifetch_outcome_future_promise_stable_promised.
  - exact Hmiss.
  - exact Hin.
Qed.

Lemma VMPromising_mem_read_data_promised_stable_from_read_code_translation
    bbm_param tid initmem code ev addr macc addr_space :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (MemRead (MemReq.make macc addr addr_space 8 0)).
Proof.
  intro Hstable.
  destruct Hstable as [_ Hread _ _].
  apply Hread.
Qed.

Lemma VMPromising_translation_start_promised_stable_from_read_code_translation
    bbm_param tid initmem code ev trans_start :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (TranslationStart trans_start).
Proof.
  intro Hstable.
  destruct Hstable as [_ _ Htrans _].
  apply translation_start_outcome_future_promise_stable_promised.
  apply Htrans.
Qed.

Lemma VMPromising_tlbop_promised_stable_from_read_code_translation
    bbm_param tid initmem code ev tlbi :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  outcome_future_promise_stable_promised bbm_param tid initmem ev
    (TlbOp tlbi).
Proof.
  intro Hstable.
  destruct Hstable as [_ _ _ Htlb].
  apply Htlb.
Qed.

Lemma VMPromising_tail_stable_from_Sail (bbm_param : BBM.param)
    {n eo} nondet (smon : SI.iMon eo ()) :
  VMPromising_Sail_tail_stable bbm_param (n:=n) nondet smon →
  VMPromising_tail_stable
    bbm_param (n:=n) (iMon_from_Sail nondet smon).
Proof.
  intro Hstable.
  constructor.
  intros tid initmem ev.
  apply VMPromising_iMon_from_Sail_promised_stable.
  apply VMPromising_Sail_tail_same_promise_stable.
  exact Hstable.
Qed.

Lemma VMPromising_tail_stable_from_Sail_same (bbm_param : BBM.param)
    {n eo} nondet (smon : SI.iMon eo ()) :
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet smon →
  VMPromising_tail_stable
    bbm_param (n:=n) (iMon_from_Sail nondet smon).
Proof.
  intro Hstable.
  constructor.
  intros tid initmem ev.
  apply VMPromising_iMon_from_Sail_promised_stable.
  apply VMPromising_Sail_same_promised_stable.
  exact Hstable.
Qed.

Lemma VMPromising_Sail_tail_stable_from_same_promise_stable
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ()) :
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet smon →
  VMPromising_Sail_tail_stable bbm_param (n:=n) nondet smon.
Proof.
  intro Hstable.
  constructor.
  intros tid initmem ev.
  apply VMPromising_Sail_same_promised_stable.
  exact Hstable.
Qed.

Lemma VMPromising_Sail_same_promise_stable_from_tail_stable
    (bbm_param : BBM.param) {n eo} nondet (smon : SI.iMon eo ()) :
  VMPromising_Sail_tail_stable bbm_param (n:=n) nondet smon →
  VMPromising_Sail_same_promise_stable
    bbm_param (n:=n) nondet smon.
Proof.
  intro Hstable.
  constructor.
  intros tid initmem ev.
  apply VMPromising_Sail_tail_same_promise_stable.
  exact Hstable.
Qed.

Lemma VMPromising_tail_stable_run_tid_promise_same
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (ev : Ev.t) st st' :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  initmem = CPState.initmem st →
  Exec.elem_of_results
    (st', ()) (CPState.run_tid isem (VMPromising bbm_param) tid st) →
  Exec.elem_of_results
    (CPState.promise_tid (VMPromising bbm_param) tid ev st', ())
    (CPState.run_tid isem (VMPromising bbm_param) tid
       (CPState.promise_tid (VMPromising bbm_param) tid ev st)).
Proof.
  intros Hstable Hinit Hrun.
  destruct Hstable as [Hsame].
  eapply (VMPromising_run_tid_promise_same_stable_from_imon
    bbm_param isem term tid initmem ev st st').
  - exact Hinit.
  - exact (Hsame tid initmem ev).
  - exact Hrun.
Qed.

Lemma VMPromising_tail_stable_run_to_termination_plain_promise_same
    (bbm_param : BBM.param) {n} (isem : iMon ())
    (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (ev : Ev.t) fuel ppst ppst' b :
  VMPromising_tail_stable bbm_param (n:=n) isem →
  Exec.elem_of_results (ppst', b)
    (CPState.run_to_termination_plain isem (VMPromising bbm_param) term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (VMPromising_promise_ppstate bbm_param
       tid initmem ev ppst', b)
    (CPState.run_to_termination_plain isem (VMPromising bbm_param) term
       tid initmem fuel
       (VMPromising_promise_ppstate bbm_param
          tid initmem ev ppst)).
Proof.
  intros Hstable Hrun.
  destruct Hstable as [Hsame].
  eapply
    (VMPromising_run_to_termination_plain_promise_same_stable_from_imon
      bbm_param isem term tid initmem ev fuel ppst ppst' b).
  - exact (Hsame tid initmem ev).
  - exact Hrun.
Qed.

Lemma VMPromising_replayable (bbm_param : BBM.param) :
    Promising.Replayable (VMPromising bbm_param).
Proof.
  constructor.
  - intros tid0 initmem0 out ppst ppst' eret H.
    exact (run_outcome_none_preserves_mem
      tid0 initmem0 out ppst ppst' eret H).
  - intros tid0 initmem0 out ppst ppst' eret vpre H.
    destruct (run_outcome_promise_replay_one
      tid0 initmem0 out ppst ppst' eret vpre H) as
      [event [Hmem [Htid [Hlt Hreplay]]]].
    exists event.
    repeat split; try assumption.
    unfold VMPromising_promise_ppstate.
    cbn.
    rewrite Hmem in Hreplay.
    cbn in Hreplay.
    exact Hreplay.
Qed.

Lemma VMPromising_handle_outcome_no_promise_non_mem_write_tlb
    (bbm_param : BBM.param) {n} (tid : fin n) initmem out :
  (∀ mr (val : bv (8 * mr.(MemReq.size)))
      (tags : bv mr.(MemReq.num_tag)),
    out ≠ MemWrite mr val tags) →
  (∀ tlbi, out ≠ TlbOp tlbi) →
  CPState.handle_outcome_no_promise
    (VMPromising bbm_param) tid initmem out.
Proof.
  intros Hnot_write Hnot_tlb ppst ppst' eret vpre Hrun.
  cbn in Hrun.
  eapply run_outcome_no_promise_non_mem_write_tlb; eauto.
Qed.

Definition VMPromising_Sail_outcome_no_promise {eo A}
    (out : SI.outcome eo A) : Prop :=
  match out with
  | SI.MemWrite _ _ _ => False
  | SI.TlbOp _ => False
  | _ => True
  end.

Fixpoint VMPromising_Sail_no_promise {eo A}
    (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      VMPromising_Sail_outcome_no_promise out ∧
      ∀ ret, VMPromising_Sail_no_promise (k ret)
  end.

Fixpoint VMPromising_Sail_at_most_one_promise {eo A}
    (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      (VMPromising_Sail_outcome_no_promise out ∧
       ∀ ret, VMPromising_Sail_at_most_one_promise (k ret)) ∨
      (∀ ret, VMPromising_Sail_no_promise (k ret))
  end.

Definition VMPromising_Sail_outcome_promised_stable
    (bbm_param : BBM.param) tid initmem ev nondet
    {eo A} (out : SI.outcome eo A) : Prop :=
  imon_future_promise_stable_promised bbm_param tid initmem ev _
    (Sail_outcome_interp nondet out).

Fixpoint VMPromising_Sail_prefix_promised_stable
    (bbm_param : BBM.param) tid initmem ev nondet
    {eo A} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      (VMPromising_Sail_outcome_no_promise out ∧
       VMPromising_Sail_outcome_promised_stable
         bbm_param tid initmem ev nondet out ∧
       ∀ ret,
         VMPromising_Sail_prefix_promised_stable
           bbm_param tid initmem ev nondet (k ret)) ∨
      (∀ ret, VMPromising_Sail_no_promise (k ret))
  end.

Lemma VMPromising_Sail_at_most_one_promise_from_no_promise {eo A}
    (smon : SI.iMon eo A) :
  VMPromising_Sail_no_promise smon →
  VMPromising_Sail_at_most_one_promise smon.
Proof.
  induction smon as [a|T out k IH]; intro Hno_promise.
  - exact I.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    left.
    split.
    + exact Hout.
    + intro ret.
      apply IH.
      apply Htail.
Qed.

Lemma VMPromising_Sail_no_promise_bind {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_no_promise mon →
  (∀ a, VMPromising_Sail_no_promise (k a)) →
  VMPromising_Sail_no_promise (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hno_promise Hk.
  - cbn.
    apply Hk.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    split.
    + exact Hout.
    + intro ret.
      eapply IH.
      * apply Htail.
      * exact Hk.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_bind_no_left {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_no_promise mon →
  (∀ a, VMPromising_Sail_at_most_one_promise (k a)) →
  VMPromising_Sail_at_most_one_promise (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hno_promise Hk.
  - cbn.
    apply Hk.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    left.
    split.
    + exact Hout.
    + intro ret.
      eapply IH.
      * apply Htail.
      * exact Hk.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_bind_no_right {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_at_most_one_promise mon →
  (∀ a, VMPromising_Sail_no_promise (k a)) →
  VMPromising_Sail_at_most_one_promise (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hat_most Hk.
  - cbn.
    apply VMPromising_Sail_at_most_one_promise_from_no_promise.
    apply Hk.
  - cbn in Hat_most |- *.
    destruct Hat_most as [[Hout Htail_at_most]|Htail_no].
    + left.
      split.
      * exact Hout.
      * intro ret.
        eapply IH.
        -- apply Htail_at_most.
        -- exact Hk.
    + right.
      intro ret.
      apply VMPromising_Sail_no_promise_bind.
      * apply Htail_no.
      * exact Hk.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_from_no_promise
    (bbm_param : BBM.param) tid initmem ev nondet
    {eo A} (smon : SI.iMon eo A) :
  VMPromising_Sail_no_promise smon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet smon.
Proof.
  induction smon as [a|T out k IH]; intro Hno.
  - exact I.
  - cbn in Hno |- *.
    destruct Hno as [_ Htail_no].
    right.
    exact Htail_no.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_bind_no_left
    (bbm_param : BBM.param) tid initmem ev nondet
    {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  (∀ a,
    VMPromising_Sail_prefix_promised_stable
      bbm_param tid initmem ev nondet (k a)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hno Hstable Hk.
  - cbn.
    apply Hk.
  - cbn in Hno, Hstable |- *.
    destruct Hno as [Hout_no Htail_no].
    destruct Hstable as [Hout_stable Htail_stable].
    left.
    split.
    + exact Hout_no.
    + split.
      * exact Hout_stable.
      * intro ret.
        eapply IH.
        -- apply Htail_no.
        -- apply Htail_stable.
        -- exact Hk.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_bind_no_right
    (bbm_param : BBM.param) tid initmem ev nondet
    {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet mon →
  (∀ a, VMPromising_Sail_no_promise (k a)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hstable Hk.
  - cbn.
    apply VMPromising_Sail_prefix_promised_stable_from_no_promise.
    apply Hk.
  - cbn in Hstable |- *.
    destruct Hstable as
      [[Hout_no [Hout_stable Htail_stable]]|Htail_no].
    + left.
      split.
      * exact Hout_no.
      * split.
        -- exact Hout_stable.
        -- intro ret.
           eapply IH.
           ++ apply Htail_stable.
           ++ exact Hk.
    + right.
      intro ret.
      apply VMPromising_Sail_no_promise_bind.
      * apply Htail_no.
      * exact Hk.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_from_at_most_one_stable
    (bbm_param : BBM.param) tid initmem ev nondet
    {eo A} (smon : SI.iMon eo A) :
  VMPromising_Sail_at_most_one_promise smon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet smon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet smon.
Proof.
  induction smon as [a|T out k IH]; intros Hat_most Hstable.
  - exact I.
  - cbn in Hat_most, Hstable |- *.
    destruct Hstable as [Hout_stable Htail_stable].
    destruct Hat_most as [[Hout_no Htail_at_most]|Htail_no].
    + left.
      split.
      * exact Hout_no.
      * split.
        -- exact Hout_stable.
        -- intro ret.
           eapply IH.
           ++ apply Htail_at_most.
           ++ apply Htail_stable.
    + right.
      exact Htail_no.
Qed.

Lemma VMPromising_Sail_no_promise_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  VMPromising_Sail_no_promise mon →
  (∀ e, VMPromising_Sail_no_promise (h e)) →
  VMPromising_Sail_no_promise (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hno_promise Hh.
  - exact I.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    destruct out; cbn in Hout |- *; try contradiction;
      try (split; [exact Hout|];
           intro ret; apply IH; [apply Htail|exact Hh]).
    apply Hh.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  VMPromising_Sail_at_most_one_promise mon →
  (∀ e, VMPromising_Sail_no_promise (h e)) →
  VMPromising_Sail_at_most_one_promise
    (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hat_most Hh.
  - exact I.
  - cbn in Hat_most |- *.
    destruct out; cbn in Hat_most |- *;
      try (destruct Hat_most as [[Hout Htail_at_most]|Htail_no];
           [left; split;
            [exact Hout
            |intro ret; apply IH; [apply Htail_at_most|exact Hh]]
           |right; intro ret;
            apply VMPromising_Sail_no_promise_try_catch;
            [apply Htail_no|exact Hh]]).
    apply VMPromising_Sail_at_most_one_promise_from_no_promise.
    apply Hh.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_try_catch_no_left
    (bbm_param : BBM.param) tid initmem ev nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  (∀ e, VMPromising_Sail_no_promise (h e)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hno Hstable Hh.
  - exact I.
  - cbn in Hno, Hstable |- *.
    destruct out; cbn in Hno, Hstable |- *;
      try
        (destruct Hno as [Hout_no Htail_no];
         destruct Hstable as [Hout_stable Htail_stable];
         left; split;
         [exact Hout_no
         |split;
          [exact Hout_stable
          |intro ret; apply IH;
           [apply Htail_no|apply Htail_stable|exact Hh]]]).
    all: apply VMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply Hh.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_try_catch_no_right
    (bbm_param : BBM.param) tid initmem ev nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet mon →
  (∀ e, VMPromising_Sail_no_promise (h e)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hstable Hh.
  - exact I.
  - cbn in Hstable |- *.
    destruct out; cbn in Hstable |- *;
      try
        (destruct Hstable as
           [[Hout_no [Hout_stable Htail_stable]]|Htail_no];
         [left; split;
          [exact Hout_no
          |split;
           [exact Hout_stable
           |intro ret; apply IH; [apply Htail_stable|exact Hh]]]
         |right; intro ret;
          apply VMPromising_Sail_no_promise_try_catch;
          [apply Htail_no|exact Hh]]).
    all: apply VMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply Hh.
Qed.

Lemma VMPromising_Sail_no_promise_returnm {A E} (a : A) :
  VMPromising_Sail_no_promise (System_types.Defs.returnm (E:=E) a).
Proof. exact I. Qed.

Lemma VMPromising_Sail_no_promise_fail {A E} msg :
  VMPromising_Sail_no_promise (System_types.Defs.fail (E:=E) (A:=A) msg).
Proof.
  cbn [System_types.Defs.fail].
  split; [exact I|].
  intro ret.
  destruct ret.
Qed.

Lemma VMPromising_Sail_no_promise_throw {A E} (e : E) :
  VMPromising_Sail_no_promise (System_types.Defs.throw (A:=A) e).
Proof.
  cbn [System_types.Defs.throw].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_exit {A E} :
  VMPromising_Sail_no_promise (System_types.Defs.exit (A:=A) (E:=E) tt).
Proof.
  cbn [System_types.Defs.exit].
  apply VMPromising_Sail_no_promise_fail.
Qed.

Lemma VMPromising_Sail_no_promise_liftR {A R E}
    (mon : System_types.Defs.monad E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_no_promise (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.liftR].
  eapply VMPromising_Sail_no_promise_try_catch.
  - exact Hmon.
  - intro.
    apply VMPromising_Sail_no_promise_throw.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_liftR {A R E}
    (mon : System_types.Defs.monad E A) :
  VMPromising_Sail_at_most_one_promise mon →
  VMPromising_Sail_at_most_one_promise
    (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.liftR].
  eapply VMPromising_Sail_at_most_one_promise_try_catch.
  - exact Hmon.
  - intro.
    apply VMPromising_Sail_no_promise_throw.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_liftR_no_left
    (bbm_param : BBM.param) tid initmem ev nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.liftR (R:=R) mon).
Proof.
  intros Hno Hstable.
  cbn [System_types.Defs.liftR].
  eapply VMPromising_Sail_prefix_promised_stable_try_catch_no_left.
  - exact Hno.
  - exact Hstable.
  - intro.
    apply VMPromising_Sail_no_promise_throw.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_liftR_no_right
    (bbm_param : BBM.param) tid initmem ev nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hstable.
  cbn [System_types.Defs.liftR].
  eapply VMPromising_Sail_prefix_promised_stable_try_catch_no_right.
  - exact Hstable.
  - intro.
    apply VMPromising_Sail_no_promise_throw.
Qed.

Lemma VMPromising_Sail_no_promise_catch_early_return {A E}
    (mon : System_types.Defs.monadR A E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_no_promise
    (System_types.Defs.catch_early_return mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.catch_early_return].
  eapply VMPromising_Sail_no_promise_try_catch.
  - exact Hmon.
  - intros [a|e].
    + apply VMPromising_Sail_no_promise_returnm.
    + apply VMPromising_Sail_no_promise_throw.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_catch_early_return {A E}
    (mon : System_types.Defs.monadR A E A) :
  VMPromising_Sail_at_most_one_promise mon →
  VMPromising_Sail_at_most_one_promise
    (System_types.Defs.catch_early_return mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.catch_early_return].
  eapply VMPromising_Sail_at_most_one_promise_try_catch.
  - exact Hmon.
  - intros [a|e].
    + apply VMPromising_Sail_no_promise_returnm.
    + apply VMPromising_Sail_no_promise_throw.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right
    (bbm_param : BBM.param) tid initmem ev nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.catch_early_return mon).
Proof.
  intro Hstable.
  cbn [System_types.Defs.catch_early_return].
  eapply VMPromising_Sail_prefix_promised_stable_try_catch_no_right.
  - exact Hstable.
  - intros [a|e].
    + apply VMPromising_Sail_no_promise_returnm.
    + apply VMPromising_Sail_no_promise_throw.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_catch_early_return_no_left
    (bbm_param : BBM.param) tid initmem ev nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.catch_early_return mon).
Proof.
  intros Hno Hstable.
  cbn [System_types.Defs.catch_early_return].
  eapply VMPromising_Sail_prefix_promised_stable_try_catch_no_left.
  - exact Hno.
  - exact Hstable.
  - intros [a|e].
    + apply VMPromising_Sail_no_promise_returnm.
    + apply VMPromising_Sail_no_promise_throw.
Qed.

Lemma VMPromising_Sail_no_promise_bind0 {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_no_promise tail →
  VMPromising_Sail_no_promise (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail.
  cbn [System_types.Defs.bind0].
  eapply VMPromising_Sail_no_promise_bind.
  - exact Hmon.
  - intro.
    exact Htail.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_bind0_no_left {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_at_most_one_promise tail →
  VMPromising_Sail_at_most_one_promise
    (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail.
  cbn [System_types.Defs.bind0].
  eapply VMPromising_Sail_at_most_one_promise_bind_no_left.
  - exact Hmon.
  - intro.
    exact Htail.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_bind0_no_left
    (bbm_param : BBM.param) tid initmem ev nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet tail →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon_no Hmon_stable Htail.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
  - exact Hmon_no.
  - exact Hmon_stable.
  - intro.
    exact Htail.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_bind0_no_right
    (bbm_param : BBM.param) tid initmem ev nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_no_promise tail →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail_no.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_no_right.
  - exact Hmon.
  - intro.
    exact Htail_no.
Qed.

Lemma VMPromising_Sail_promised_stable_bind
    (bbm_param : BBM.param) tid initmem ev nondet {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  (∀ a,
    VMPromising_Sail_promised_stable
      bbm_param tid initmem ev nondet (k a)) →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hmon Hk.
  - cbn.
    apply Hk.
  - cbn in Hmon |- *.
    destruct Hmon as [Hout Htail].
    split.
    + exact Hout.
    + intro ret.
      eapply IH.
      * apply Htail.
      * exact Hk.
Qed.

Lemma VMPromising_Sail_promised_stable_try_catch
    (bbm_param : BBM.param) tid initmem ev nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  (∀ e,
    VMPromising_Sail_promised_stable
      bbm_param tid initmem ev nondet (h e)) →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hmon Hh.
  - exact I.
  - cbn in Hmon |- *.
    destruct out; cbn in Hmon |- *;
      try
        (destruct Hmon as [Hout Htail];
         split;
         [exact Hout
         |intro ret; apply IH; [apply Htail|exact Hh]]).
    all: apply Hh.
Qed.

Lemma VMPromising_Sail_promised_stable_throw
    (bbm_param : BBM.param) tid initmem ev nondet {A E} (e : E) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.throw (A:=A) e).
Proof.
  unfold System_types.Defs.throw.
  cbn [VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mthrow, iMon_throw, mcall_noret, mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply generic_fail_outcome_future_promise_stable_promised.
    + intros [].
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_liftR
    (bbm_param : BBM.param) tid initmem ev nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.liftR].
  eapply VMPromising_Sail_promised_stable_try_catch.
  - exact Hmon.
  - intro.
    apply VMPromising_Sail_promised_stable_throw.
Qed.

Lemma VMPromising_Sail_promised_stable_catch_early_return
    (bbm_param : BBM.param) tid initmem ev nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.catch_early_return mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.catch_early_return].
  eapply VMPromising_Sail_promised_stable_try_catch.
  - exact Hmon.
  - intros [a|e].
    + exact I.
    + apply VMPromising_Sail_promised_stable_throw.
Qed.

Lemma VMPromising_Sail_promised_stable_bind0
    (bbm_param : BBM.param) tid initmem ev nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet mon →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet tail →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply VMPromising_Sail_promised_stable_bind.
  - exact Hmon.
  - intro.
    exact Htail.
Qed.

Lemma VMPromising_Sail_promised_stable_foreach_ZM_up'
    (bbm_param : BBM.param) tid initmem ev nondet {E Vars}
    from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars,
    VMPromising_Sail_promised_stable
      bbm_param tid initmem ev nondet (body z vars)) →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.foreach_ZM_up' from to step fuel vars body).
Proof.
  revert from vars.
  induction fuel as [|fuel IH]; intros from vars Hbody.
  - cbn [System_types.Defs.foreach_ZM_up'].
    destruct (Z.leb from to); exact I.
  - cbn [System_types.Defs.foreach_ZM_up'].
    destruct (Z.leb from to).
    + cbn [System_types.Defs.bind].
      eapply VMPromising_Sail_promised_stable_bind.
      * apply Hbody.
      * intro vars'.
        apply IH.
        apply Hbody.
    + exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_foreach_ZM_up
    (bbm_param : BBM.param) tid initmem ev nondet {E Vars}
    from to step (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars,
    VMPromising_Sail_promised_stable
      bbm_param tid initmem ev nondet (body z vars)) →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.foreach_ZM_up from to step vars body).
Proof.
  cbn [System_types.Defs.foreach_ZM_up].
  apply VMPromising_Sail_promised_stable_foreach_ZM_up'.
Qed.

Lemma VMPromising_Sail_no_promise_read_reg {E} reg :
  VMPromising_Sail_no_promise (System_types.Defs.read_reg (e:=E) reg).
Proof.
  cbn [System_types.Defs.read_reg].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_write_reg {E} reg value :
  VMPromising_Sail_no_promise
    (System_types.Defs.write_reg (e:=E) reg value).
Proof.
  cbn [System_types.Defs.write_reg].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_read_reg_ref {A E}
    (ref : Values.register_ref A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.read_reg_ref (e:=E) ref).
Proof.
  cbn [System_types.Defs.read_reg_ref].
  apply VMPromising_Sail_no_promise_read_reg.
Qed.

Lemma VMPromising_Sail_no_promise_reg_deref {A E}
    (ref : Values.register_ref A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.reg_deref (e:=E) ref).
Proof.
  cbn [System_types.Defs.reg_deref].
  apply VMPromising_Sail_no_promise_read_reg_ref.
Qed.

Lemma VMPromising_Sail_no_promise_write_reg_ref {A E}
    (ref : Values.register_ref A) (v : A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.write_reg_ref (e:=E) ref v).
Proof.
  cbn [System_types.Defs.write_reg_ref].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_sail_mem_read {E n nt} req :
  VMPromising_Sail_no_promise
    (System_types.Defs.sail_mem_read (e:=E) (n:=n) (nt:=nt) req).
Proof.
  cbn [System_types.Defs.sail_mem_read].
  split; [exact I|].
  intros [[data tags]|abort].
  all: exact I.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_sail_mem_write
    {E n nt} req value tags :
  VMPromising_Sail_at_most_one_promise
    (System_types.Defs.sail_mem_write
       (e:=E) (n:=n) (nt:=nt) req value tags).
Proof.
  cbn [System_types.Defs.sail_mem_write].
  right.
  intros [[]|abort].
  all: exact I.
Qed.

Lemma VMPromising_Sail_no_promise_sail_barrier {E} b :
  VMPromising_Sail_no_promise (System_types.Defs.sail_barrier (e:=E) b).
Proof.
  cbn [System_types.Defs.sail_barrier].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_sail_translation_start {E} ts :
  VMPromising_Sail_no_promise
    (System_types.Defs.sail_translation_start (e:=E) ts).
Proof.
  cbn [System_types.Defs.sail_translation_start].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_sail_translation_end {E} te :
  VMPromising_Sail_no_promise
    (System_types.Defs.sail_translation_end (e:=E) te).
Proof.
  cbn [System_types.Defs.sail_translation_end].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_sail_take_exception {E} exn :
  VMPromising_Sail_no_promise
    (System_types.Defs.sail_take_exception (e:=E) exn).
Proof.
  cbn [System_types.Defs.sail_take_exception].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_sail_tlbi {E} tlbi :
  VMPromising_Sail_at_most_one_promise
    (System_types.Defs.sail_tlbi (e:=E) tlbi).
Proof.
  cbn [System_types.Defs.sail_tlbi].
  right.
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_choose_range {E} descr lo hi :
  VMPromising_Sail_no_promise
    (System_types.Defs.choose_range (E:=E) descr lo hi).
Proof.
  cbn [System_types.Defs.choose_range].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_choose_from_list {A E} descr
    (xs : list A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.choose_from_list (E:=E) descr xs).
Proof.
  cbn [System_types.Defs.choose_from_list System_types.Defs.bind].
  apply VMPromising_Sail_no_promise_bind.
  - apply VMPromising_Sail_no_promise_choose_range.
  - intro idx.
    destruct (nth_error xs (Z.to_nat idx)).
    + apply VMPromising_Sail_no_promise_returnm.
    + apply VMPromising_Sail_no_promise_fail.
Qed.

Lemma VMPromising_Sail_no_promise_internal_pick {A E} (xs : list A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.internal_pick (e:=E) xs).
Proof.
  cbn [System_types.Defs.internal_pick].
  apply VMPromising_Sail_no_promise_choose_from_list.
Qed.

Lemma VMPromising_Sail_no_promise_foreach_ZM_up' {E Vars}
    from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, VMPromising_Sail_no_promise (body z vars)) →
  VMPromising_Sail_no_promise
    (System_types.Defs.foreach_ZM_up' from to step fuel vars body).
Proof.
  revert from vars.
  induction fuel as [|fuel IH]; intros from vars Hbody.
  - cbn [System_types.Defs.foreach_ZM_up'].
    destruct (Z.leb from to); apply VMPromising_Sail_no_promise_returnm.
  - cbn [System_types.Defs.foreach_ZM_up'].
    destruct (Z.leb from to).
    + cbn [System_types.Defs.bind].
      apply VMPromising_Sail_no_promise_bind.
      * apply Hbody.
      * intro vars'.
        apply IH.
        apply Hbody.
    + apply VMPromising_Sail_no_promise_returnm.
Qed.

Lemma VMPromising_Sail_no_promise_foreach_ZM_up {E Vars}
    from to step (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, VMPromising_Sail_no_promise (body z vars)) →
  VMPromising_Sail_no_promise
    (System_types.Defs.foreach_ZM_up from to step vars body).
Proof.
  cbn [System_types.Defs.foreach_ZM_up].
  apply VMPromising_Sail_no_promise_foreach_ZM_up'.
Qed.

Ltac VMPromising_Sail_simpl :=
  cbn [System_types.Defs.returnm System_types.Defs.fail
       System_types.Defs.throw System_types.Defs.exit
       System_types.Defs.early_return System_types.Defs.assert_exp
       System_types.Defs.assert_exp' System_types.Defs.sail_mem_read
       System_types.Defs.sail_mem_write System_types.Defs.sail_barrier
       System_types.Defs.sail_translation_start
       System_types.Defs.sail_translation_end
       System_types.Defs.sail_take_exception System_types.Defs.sail_tlbi
       System_types.Defs.choose_range System_types.Defs.choose_from_list
       System_types.Defs.internal_pick System_types.Defs.read_reg
       System_types.Defs.write_reg System_types.Defs.read_reg_ref
       System_types.Defs.reg_deref System_types.Defs.write_reg_ref
       System_types.Defs.foreach_ZM_up System_types.Defs.foreach_ZM_up'
       System_types.Defs.autocast_m System_types.Defs.returnR
       System_types.returnM System_types.returnR] in *;
  unfold System_types.returnM, System_types.returnR,
    System_types.Defs.returnR, System_types.Defs.early_return,
    System_types.Defs.autocast_m, System.fail in *;
  unfold System_types.Defs.bind, System_types.Defs.bind0 in *.

Ltac solve_VMPromising_Sail_no_promise_src :=
  lazymatch goal with
  | |- True => exact I
  | |- VMPromising_Sail_no_promise (System_types.Interface.Ret _) =>
      exact I
  | |- VMPromising_Sail_no_promise (System_types.Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_no_promise (Defs.returnR _ _) =>
      exact I
  | |- _ ∧ _ =>
      split; solve_VMPromising_Sail_no_promise_src
  | |- ∀ _, _ =>
      intro; solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.assert_exp' ?b _) =>
      destruct b;
      [apply VMPromising_Sail_no_promise_returnm
      |apply VMPromising_Sail_no_promise_fail]
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.assert_exp ?b _) =>
      destruct b;
      [apply VMPromising_Sail_no_promise_returnm
      |apply VMPromising_Sail_no_promise_fail]
  | |- VMPromising_Sail_no_promise (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      eapply VMPromising_Sail_no_promise_bind;
      [solve_VMPromising_Sail_no_promise_src
      |intro; solve_VMPromising_Sail_no_promise_src]
  | |- VMPromising_Sail_no_promise (Defs.bind _ _) =>
      unfold Defs.bind;
      eapply VMPromising_Sail_no_promise_bind;
      [solve_VMPromising_Sail_no_promise_src
      |intro; solve_VMPromising_Sail_no_promise_src]
  | |- VMPromising_Sail_no_promise
        (System_types.Interface.iMon_bind _ _) =>
      eapply VMPromising_Sail_no_promise_bind;
      [solve_VMPromising_Sail_no_promise_src
      |intro; solve_VMPromising_Sail_no_promise_src]
  | |- VMPromising_Sail_no_promise
        (Interface.iMon_bind _ _) =>
      eapply VMPromising_Sail_no_promise_bind;
      [solve_VMPromising_Sail_no_promise_src
      |intro; solve_VMPromising_Sail_no_promise_src]
  | |- VMPromising_Sail_no_promise (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_no_promise_bind0;
      [solve_VMPromising_Sail_no_promise_src
      |solve_VMPromising_Sail_no_promise_src]
  | |- VMPromising_Sail_no_promise (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_no_promise_bind0;
      [solve_VMPromising_Sail_no_promise_src
      |solve_VMPromising_Sail_no_promise_src]
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.try_catch _ _) =>
      eapply VMPromising_Sail_no_promise_try_catch;
      [solve_VMPromising_Sail_no_promise_src
      |intro; solve_VMPromising_Sail_no_promise_src]
  | |- VMPromising_Sail_no_promise (System_types.Defs.liftR _) =>
      apply VMPromising_Sail_no_promise_liftR;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (Defs.liftR _) =>
      apply VMPromising_Sail_no_promise_liftR;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.catch_early_return _) =>
      apply VMPromising_Sail_no_promise_catch_early_return;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System_types.Defs.returnm _) =>
      apply VMPromising_Sail_no_promise_returnm
  | |- VMPromising_Sail_no_promise (System_types.Defs.fail _) =>
      apply VMPromising_Sail_no_promise_fail
  | |- VMPromising_Sail_no_promise (Defs.fail _) =>
      apply VMPromising_Sail_no_promise_fail
  | |- VMPromising_Sail_no_promise (System_types.Defs.throw _) =>
      apply VMPromising_Sail_no_promise_throw
  | |- VMPromising_Sail_no_promise (Defs.throw _) =>
      apply VMPromising_Sail_no_promise_throw
  | |- VMPromising_Sail_no_promise (System_types.Defs.exit _) =>
      apply VMPromising_Sail_no_promise_exit
  | |- VMPromising_Sail_no_promise (System_types.Defs.read_reg _) =>
      apply VMPromising_Sail_no_promise_read_reg
  | |- VMPromising_Sail_no_promise (Defs.read_reg _) =>
      apply VMPromising_Sail_no_promise_read_reg
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.write_reg _ _) =>
      apply VMPromising_Sail_no_promise_write_reg
  | |- VMPromising_Sail_no_promise (Defs.write_reg _ _) =>
      apply VMPromising_Sail_no_promise_write_reg
  | |- VMPromising_Sail_no_promise (Defs.early_return _) =>
      unfold Defs.early_return;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.read_reg_ref _) =>
      apply VMPromising_Sail_no_promise_read_reg_ref
  | |- VMPromising_Sail_no_promise (System_types.Defs.reg_deref _) =>
      apply VMPromising_Sail_no_promise_reg_deref
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.write_reg_ref _ _) =>
      apply VMPromising_Sail_no_promise_write_reg_ref
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.sail_mem_read _) =>
      apply VMPromising_Sail_no_promise_sail_mem_read
  | |- VMPromising_Sail_no_promise (System.read_memory _ _ _) =>
      unfold System.read_memory;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.iFetch _ _) =>
      unfold System.iFetch;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.rMem _ _ _) =>
      unfold System.rMem;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.rX _) =>
      unfold System.rX;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.wX _ _) =>
      unfold System.wX;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.rW _) =>
      unfold System.rW;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.wW _ _) =>
      unfold System.wW;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.rXS _ _) =>
      unfold System.rXS;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.wXS _ _ _) =>
      unfold System.wXS;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.rPC _) =>
      unfold System.rPC;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.wPC _) =>
      unfold System.wPC;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.create_writeAccessDescriptor _) =>
      unfold System.create_writeAccessDescriptor;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.create_readAccessDescriptor _) =>
      unfold System.create_readAccessDescriptor;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.create_iFetchAccessDescriptor _) =>
      unfold System.create_iFetchAccessDescriptor;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.get_translation_base_address _) =>
      unfold System.get_translation_base_address;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.ASID_read _) =>
      unfold System.ASID_read;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.create_AccessDescriptorTTW _ _) =>
      unfold System.create_AccessDescriptorTTW;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.pgt_walk _ _) =>
      unfold System.pgt_walk, System.get_translation_base_address,
        System.create_AccessDescriptorTTW, System.read_memory;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.take_exception _ _) =>
      unfold System.take_exception;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.handle_fault _) =>
      unfold System.handle_fault, System.take_exception;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.translate_address _ _) =>
      unfold System.translate_address, System.pgt_walk,
        System.get_translation_base_address,
        System.create_AccessDescriptorTTW, System.ASID_read;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.decode_bitwise_op _) =>
      unfold System.decode_bitwise_op;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.decode_bitmask _ _ _) =>
      unfold System.decode_bitmask;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.decode _) =>
      unfold System.decode, System.decode_bitwise_op,
        System.decode_bitmask, System.fail;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_SupervisorCall _) =>
      unfold System.execute_SupervisorCall;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.execute_Sub _ _ _ _) =>
      unfold System.execute_Sub;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.execute_Nop _) =>
      unfold System.execute_Nop;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.execute_Movz _ _ _ _) =>
      unfold System.execute_Movz;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.execute_Load _ _ _ _) =>
      unfold System.execute_Load;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_InstructionSynchronizationBarrier _) =>
      unfold System.execute_InstructionSynchronizationBarrier;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_ExceptionReturn _) =>
      unfold System.execute_ExceptionReturn;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_DataSynchronizationBarrier _ _) =>
      unfold System.execute_DataSynchronizationBarrier;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_DataMemoryBarrier _ _) =>
      unfold System.execute_DataMemoryBarrier;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_CompareAndBranch _ _ _ _) =>
      unfold System.execute_CompareAndBranch;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.execute_Branch _) =>
      unfold System.execute_Branch;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_BitwiseLogic _ _ _ _ _) =>
      unfold System.execute_BitwiseLogic;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.execute_Add _ _ _ _) =>
      unfold System.execute_Add;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.autocast_m _) =>
      unfold System_types.Defs.autocast_m;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.sail_barrier _) =>
      apply VMPromising_Sail_no_promise_sail_barrier
  | |- VMPromising_Sail_no_promise (System.dataMemoryBarrier _ _) =>
      unfold System.dataMemoryBarrier;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.dataSynchronizationBarrer _ _) =>
      unfold System.dataSynchronizationBarrer;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.instructionSynchronizationBarrier _) =>
      unfold System.instructionSynchronizationBarrier;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.sail_translation_start _) =>
      apply VMPromising_Sail_no_promise_sail_translation_start
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.sail_translation_end _) =>
      apply VMPromising_Sail_no_promise_sail_translation_end
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.sail_take_exception _) =>
      apply VMPromising_Sail_no_promise_sail_take_exception
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.choose_range _ _ _) =>
      apply VMPromising_Sail_no_promise_choose_range
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.choose_from_list _ _) =>
      apply VMPromising_Sail_no_promise_choose_from_list
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.internal_pick _) =>
      apply VMPromising_Sail_no_promise_internal_pick
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.foreach_ZM_up _ _ _ _ _) =>
      apply VMPromising_Sail_no_promise_foreach_ZM_up;
      intros; solve_VMPromising_Sail_no_promise_src
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_VMPromising_Sail_no_promise_src
  | |- context[if ?x then _ else _] =>
      destruct x; solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise _ =>
      progress VMPromising_Sail_simpl;
      solve_VMPromising_Sail_no_promise_src
  end.

Lemma VMPromising_Sail_no_promise_execute_Load size t n op :
  VMPromising_Sail_no_promise (System.execute_Load size t n op).
Proof.
  unfold System.execute_Load.
  apply VMPromising_Sail_no_promise_catch_early_return.
  cbn [System_types.Defs.bind].
  eapply VMPromising_Sail_no_promise_bind.
  - solve_VMPromising_Sail_no_promise_src.
  - intro accdesc.
    cbn [System_types.Defs.bind].
    eapply VMPromising_Sail_no_promise_bind.
    + destruct op; solve_VMPromising_Sail_no_promise_src.
    + intro vaddr.
      cbn [System_types.Defs.bind].
      eapply VMPromising_Sail_no_promise_bind.
      * solve_VMPromising_Sail_no_promise_src.
      * intro addr_opt.
        cbn [System_types.Defs.bind].
        eapply VMPromising_Sail_no_promise_bind.
        -- destruct addr_opt; solve_VMPromising_Sail_no_promise_src.
        -- intro addr.
           cbn [System_types.Defs.bind].
           eapply VMPromising_Sail_no_promise_bind.
           ++ solve_VMPromising_Sail_no_promise_src.
           ++ intro pc.
              cbn [System_types.Defs.bind System_types.Defs.bind0].
              eapply VMPromising_Sail_no_promise_bind.
              ** solve_VMPromising_Sail_no_promise_src.
              ** intro.
                 solve_VMPromising_Sail_no_promise_src.
Qed.

Ltac solve_VMPromising_Sail_at_most_one_promise_src :=
  lazymatch goal with
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.sail_mem_write _ _ _) =>
      apply VMPromising_Sail_at_most_one_promise_sail_mem_write
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.sail_tlbi _) =>
      apply VMPromising_Sail_at_most_one_promise_sail_tlbi
  | |- VMPromising_Sail_at_most_one_promise (System.wMem _ _ _ _) =>
      unfold System.wMem;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.autocast_m _) =>
      unfold System_types.Defs.autocast_m;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_SupervisorCall _) =>
      unfold System.execute_SupervisorCall;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_Sub _ _ _ _) =>
      unfold System.execute_Sub;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_Store _ _ _ _) =>
      unfold System.execute_Store;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise (System.execute_Nop _) =>
      unfold System.execute_Nop;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_Movz _ _ _ _) =>
      unfold System.execute_Movz;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_Load _ _ _ _) =>
      unfold System.execute_Load;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_InstructionSynchronizationBarrier _) =>
      unfold System.execute_InstructionSynchronizationBarrier;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_ExceptionReturn _) =>
      unfold System.execute_ExceptionReturn;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_DataSynchronizationBarrier _ _) =>
      unfold System.execute_DataSynchronizationBarrier;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_DataMemoryBarrier _ _) =>
      unfold System.execute_DataMemoryBarrier;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_CompareAndBranch _ _ _ _) =>
      unfold System.execute_CompareAndBranch;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise (System.execute_Branch _) =>
      unfold System.execute_Branch;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_TLBInvalidation _ _) =>
      unfold System.execute_TLBInvalidation;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_BitwiseLogic _ _ _ _ _) =>
      unfold System.execute_BitwiseLogic;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_Add _ _ _ _) =>
      unfold System.execute_Add;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_src
         |intro; solve_VMPromising_Sail_at_most_one_promise_src]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_src
         |intro; solve_VMPromising_Sail_no_promise_src]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_src
         |intro; solve_VMPromising_Sail_at_most_one_promise_src]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_src
         |intro; solve_VMPromising_Sail_no_promise_src]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_src
      |solve_VMPromising_Sail_at_most_one_promise_src]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.liftR _) =>
      apply VMPromising_Sail_at_most_one_promise_liftR;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return _) =>
      apply VMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_VMPromising_Sail_at_most_one_promise_src
  | |- context[if ?x then _ else _] =>
      destruct x; solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise _ =>
      first
        [progress VMPromising_Sail_simpl;
         solve_VMPromising_Sail_at_most_one_promise_src
        |apply VMPromising_Sail_at_most_one_promise_from_no_promise;
         solve_VMPromising_Sail_no_promise_src]
  end.

Lemma VMPromising_Sail_at_most_one_promise_fetch_and_execute :
  VMPromising_Sail_at_most_one_promise (System.fetch_and_execute tt).
Proof.
  unfold System.fetch_and_execute, System.execute,
    System.execute_TLBInvalidation, System.execute_SupervisorCall,
    System.execute_Sub, System.execute_Store, System.execute_Nop,
    System.execute_Movz, System.execute_Load,
    System.execute_InstructionSynchronizationBarrier,
    System.execute_ExceptionReturn,
    System.execute_DataSynchronizationBarrier,
    System.execute_DataMemoryBarrier, System.execute_CompareAndBranch,
    System.execute_Branch, System.execute_BitwiseLogic, System.execute_Add,
    System.translate_address, System.pgt_walk, System.handle_fault,
    System.take_exception, System.decode, System.decode_bitwise_op,
    System.decode_bitmask, System.decodeDataBarrier, System.decodeTLBI,
    System.get_translation_base_address, System.create_AccessDescriptorTTW,
    System.ASID_read, System.read_memory, System.rMem, System.wMem,
    System.iFetch, System.rX, System.wX, System.rW, System.wW,
    System.rXS, System.wXS, System.rPC, System.wPC,
    System.create_writeAccessDescriptor,
    System.create_readAccessDescriptor,
    System.create_iFetchAccessDescriptor,
    System.dataMemoryBarrier, System.dataSynchronizationBarrer,
    System.instructionSynchronizationBarrier, System.reportTLBI,
    System.fail.
  solve_VMPromising_Sail_at_most_one_promise_src.
Qed.

Lemma VMPromising_Sail_promised_stable_returnm
    bbm_param tid initmem ev nondet {A E} (a : A) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet (System_types.Defs.returnm (E:=E) a).
Proof.
  exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_fail
    bbm_param tid initmem ev nondet {A E} msg :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.fail (E:=E) (A:=A) msg).
Proof.
  cbn [System_types.Defs.fail VMPromising_Sail_promised_stable
       Sail_outcome_interp].
  split.
  - unfold mthrow, iMon_throw, mcall_noret, mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply generic_fail_outcome_future_promise_stable_promised.
    + intros [].
  - intros [].
Qed.

Lemma VMPromising_Sail_promised_stable_exit
    bbm_param tid initmem ev nondet {A E} :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.exit (A:=A) (E:=E) tt).
Proof.
  cbn [System_types.Defs.exit].
  apply VMPromising_Sail_promised_stable_fail.
Qed.

Lemma VMPromising_Sail_promised_stable_read_reg
    bbm_param tid initmem ev nondet {E} reg :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.read_reg (e:=E) reg).
Proof.
  cbn [System_types.Defs.read_reg VMPromising_Sail_promised_stable
       Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply reg_read_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_write_reg
    bbm_param tid initmem ev nondet {E} reg value :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.write_reg (e:=E) reg value).
Proof.
  cbn [System_types.Defs.write_reg VMPromising_Sail_promised_stable
       Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply reg_write_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_read_reg_ref
    bbm_param tid initmem ev nondet {A E}
    (ref : Values.register_ref A) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.read_reg_ref (e:=E) ref).
Proof.
  cbn [System_types.Defs.read_reg_ref].
  apply VMPromising_Sail_promised_stable_read_reg.
Qed.

Lemma VMPromising_Sail_promised_stable_reg_deref
    bbm_param tid initmem ev nondet {A E}
    (ref : Values.register_ref A) :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.reg_deref (e:=E) ref).
Proof.
  cbn [System_types.Defs.reg_deref].
  apply VMPromising_Sail_promised_stable_read_reg_ref.
Qed.

Lemma VMPromising_Sail_promised_stable_rX
    bbm_param tid initmem ev nondet n :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet (System.rX n).
Proof.
  unfold System.rX.
  destruct (System.neq_int n 31).
  - apply VMPromising_Sail_promised_stable_reg_deref.
  - cbn [System_types.returnM].
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_mem_read_ifetch
    bbm_param tid initmem code ev nondet {E} req :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_mem_read (e:=E) (n:=4) (nt:=0) req).
Proof.
  intro Hstable.
  cbn [System_types.Defs.sail_mem_read
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + eapply
        VMPromising_mem_read_ifetch_promised_stable_from_read_code_translation.
      exact Hstable.
    + intros [[data tags]|abort]; exact I.
  - intros [[data tags]|abort]; exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_mem_read_data
    bbm_param tid initmem code ev nondet {E} req :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_mem_read (e:=E) (n:=8) (nt:=0) req).
Proof.
  intro Hstable.
  cbn [System_types.Defs.sail_mem_read
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + eapply
        VMPromising_mem_read_data_promised_stable_from_read_code_translation.
      exact Hstable.
    + intros [[data tags]|abort]; exact I.
  - intros [[data tags]|abort]; exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_barrier_dmb
    bbm_param tid initmem ev nondet {E} dmb :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_barrier (e:=E) (Barrier_DMB dmb)).
Proof.
  cbn [System_types.Defs.sail_barrier
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply barrier_dmb_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_barrier_dsb
    bbm_param tid initmem ev nondet {E} dsb :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_barrier (e:=E) (Barrier_DSB dsb)).
Proof.
  cbn [System_types.Defs.sail_barrier
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply barrier_dsb_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_barrier_isb
    bbm_param tid initmem ev nondet {E} u :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_barrier (e:=E) (Barrier_ISB u)).
Proof.
  destruct u.
  cbn [System_types.Defs.sail_barrier
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply barrier_isb_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_translation_start
    bbm_param tid initmem code ev nondet {E} ts :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_translation_start (e:=E) ts).
Proof.
  intro Hstable.
  cbn [System_types.Defs.sail_translation_start
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + eapply VMPromising_translation_start_promised_stable_from_read_code_translation.
      exact Hstable.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_translation_end
    bbm_param tid initmem ev nondet {E} te :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_translation_end (e:=E) te).
Proof.
  cbn [System_types.Defs.sail_translation_end
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply translation_end_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_take_exception
    bbm_param tid initmem ev nondet {E} exn :
  VMPromising_Sail_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_take_exception (e:=E) exn).
Proof.
  cbn [System_types.Defs.sail_take_exception
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply take_exception_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_sail_mem_write
    bbm_param tid initmem ev nondet {E n nt} req value tags :
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_mem_write
       (e:=E) (n:=n) (nt:=nt) req value tags).
Proof.
  cbn [System_types.Defs.sail_mem_write].
  right.
  intros [[]|abort].
  all: exact I.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_sail_tlbi
    bbm_param tid initmem ev nondet {E} tlbi :
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System_types.Defs.sail_tlbi (e:=E) tlbi).
Proof.
  cbn [System_types.Defs.sail_tlbi].
  right.
  intro.
  exact I.
Qed.

Ltac solve_VMPromising_Sail_promised_stable_read_code_translation :=
  lazymatch goal with
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Interface.Ret _) =>
      exact I
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.returnm _) =>
      apply VMPromising_Sail_promised_stable_returnm
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.early_return _) =>
      unfold System_types.Defs.early_return;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.early_return _) =>
      unfold Defs.early_return;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.fail _) =>
      apply VMPromising_Sail_promised_stable_fail
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.fail _) =>
      apply VMPromising_Sail_promised_stable_fail
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.throw _) =>
      apply VMPromising_Sail_promised_stable_throw
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.throw _) =>
      apply VMPromising_Sail_promised_stable_throw
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.exit _) =>
      apply VMPromising_Sail_promised_stable_exit
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.assert_exp' ?b _) =>
      destruct b;
      [apply VMPromising_Sail_promised_stable_returnm
      |apply VMPromising_Sail_promised_stable_fail]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.assert_exp ?b _) =>
      destruct b;
      [apply VMPromising_Sail_promised_stable_returnm
      |apply VMPromising_Sail_promised_stable_fail]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.read_reg _) =>
      apply VMPromising_Sail_promised_stable_read_reg
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.read_reg _) =>
      apply VMPromising_Sail_promised_stable_read_reg
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.write_reg _ _) =>
      apply VMPromising_Sail_promised_stable_write_reg
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.write_reg _ _) =>
      apply VMPromising_Sail_promised_stable_write_reg
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.read_reg_ref _) =>
      cbn [System_types.Defs.read_reg_ref];
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.reg_deref _) =>
      cbn [System_types.Defs.reg_deref];
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.write_reg_ref _ _) =>
      cbn [System_types.Defs.write_reg_ref];
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_mem_read _) =>
      first
        [eapply
           VMPromising_Sail_promised_stable_sail_mem_read_ifetch;
         exact Hstable
        |eapply VMPromising_Sail_promised_stable_sail_mem_read_data;
         exact Hstable]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_barrier (Barrier_DMB _)) =>
      apply VMPromising_Sail_promised_stable_sail_barrier_dmb
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_barrier (Barrier_DSB _)) =>
      apply VMPromising_Sail_promised_stable_sail_barrier_dsb
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_barrier (Barrier_ISB _)) =>
      apply VMPromising_Sail_promised_stable_sail_barrier_isb
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_translation_start _) =>
      eapply VMPromising_Sail_promised_stable_sail_translation_start;
      exact Hstable
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_translation_end _) =>
      apply VMPromising_Sail_promised_stable_sail_translation_end
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_take_exception _) =>
      apply VMPromising_Sail_promised_stable_sail_take_exception
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.read_memory _ _ _) =>
      unfold System.read_memory;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.iFetch _ _) =>
      unfold System.iFetch;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.rMem _ _ _) =>
      unfold System.rMem;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.rX _) =>
      unfold System.rX;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.wX _ _) =>
      unfold System.wX;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.rW _) =>
      unfold System.rW;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.wW _ _) =>
      unfold System.wW;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.rXS _ _) =>
      unfold System.rXS;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.wXS _ _ _) =>
      unfold System.wXS;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.rPC _) =>
      unfold System.rPC;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.wPC _) =>
      unfold System.wPC;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.create_writeAccessDescriptor _) =>
      unfold System.create_writeAccessDescriptor;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.create_readAccessDescriptor _) =>
      unfold System.create_readAccessDescriptor;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.create_iFetchAccessDescriptor _) =>
      unfold System.create_iFetchAccessDescriptor;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.dataMemoryBarrier _ _) =>
      unfold System.dataMemoryBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.dataSynchronizationBarrer _ _) =>
      unfold System.dataSynchronizationBarrer;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.instructionSynchronizationBarrier _) =>
      unfold System.instructionSynchronizationBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.autocast_m _) =>
      unfold System_types.Defs.autocast_m;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.autocast_m _) =>
      unfold Defs.autocast_m;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.take_exception _ _) =>
      unfold System.take_exception;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.handle_fault _) =>
      unfold System.handle_fault;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.translate_address _ _) =>
      unfold System.translate_address, System.pgt_walk,
        System.get_translation_base_address,
        System.create_AccessDescriptorTTW, System.ASID_read;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.decode_bitwise_op _) =>
      unfold System.decode_bitwise_op;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.decode_bitmask _ _ _) =>
      unfold System.decode_bitmask;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ (System.decode _) =>
      unfold System.decode, System.decode_bitwise_op,
        System.decode_bitmask, System.fail;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_SupervisorCall _) =>
      unfold System.execute_SupervisorCall;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_Sub _ _ _ _) =>
      unfold System.execute_Sub;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_Nop _) =>
      unfold System.execute_Nop;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_Movz _ _ _ _) =>
      unfold System.execute_Movz;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_Load _ _ _ _) =>
      unfold System.execute_Load;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _
        (System.execute_InstructionSynchronizationBarrier _) =>
      unfold System.execute_InstructionSynchronizationBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_ExceptionReturn _) =>
      unfold System.execute_ExceptionReturn;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _
        (System.execute_DataSynchronizationBarrier _ _) =>
      unfold System.execute_DataSynchronizationBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_DataMemoryBarrier _ _) =>
      unfold System.execute_DataMemoryBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_CompareAndBranch _ _ _ _) =>
      unfold System.execute_CompareAndBranch;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_Branch _) =>
      unfold System.execute_Branch;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_BitwiseLogic _ _ _ _ _) =>
      unfold System.execute_BitwiseLogic;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System.execute_Add _ _ _ _) =>
      unfold System.execute_Add;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      eapply VMPromising_Sail_promised_stable_bind;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.bind _ _) =>
      unfold Defs.bind;
      eapply VMPromising_Sail_promised_stable_bind;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Interface.iMon_bind _ _) =>
      eapply VMPromising_Sail_promised_stable_bind;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Interface.iMon_bind _ _) =>
      eapply VMPromising_Sail_promised_stable_bind;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_promised_stable_bind0;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_promised_stable_bind0;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.try_catch _ _) =>
      eapply VMPromising_Sail_promised_stable_try_catch;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.liftR _) =>
      apply VMPromising_Sail_promised_stable_liftR;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (Defs.liftR _) =>
      apply VMPromising_Sail_promised_stable_liftR;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.catch_early_return _) =>
      apply VMPromising_Sail_promised_stable_catch_early_return;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.foreach_ZM_up _ _ _ _ _) =>
      apply VMPromising_Sail_promised_stable_foreach_ZM_up;
      intros;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ (System_types.Defs.foreach_ZM_up' _ _ _ _ _ _) =>
      apply VMPromising_Sail_promised_stable_foreach_ZM_up';
      intros;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- context[match ?x with _ => _ end] =>
      destruct x;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- context[if ?x then _ else _] =>
      destruct x;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ =>
      progress VMPromising_Sail_simpl;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  end.

Ltac solve_VMPromising_Sail_no_promise_src_prefix :=
  solve_VMPromising_Sail_no_promise_src.

Ltac solve_VMPromising_Sail_promised_stable_prefix :=
  solve_VMPromising_Sail_promised_stable_read_code_translation.

Ltac VMPromising_Sail_unfold_execute_helpers :=
  unfold System.execute_TLBInvalidation, System.execute_SupervisorCall,
    System.execute_Sub, System.execute_Store, System.execute_Nop,
    System.execute_Movz, System.execute_Load,
    System.execute_InstructionSynchronizationBarrier,
    System.execute_ExceptionReturn,
    System.execute_DataSynchronizationBarrier,
    System.execute_DataMemoryBarrier, System.execute_CompareAndBranch,
    System.execute_Branch, System.execute_BitwiseLogic, System.execute_Add,
    System.translate_address, System.pgt_walk, System.handle_fault,
    System.take_exception, System.decode, System.decode_bitwise_op,
    System.decode_bitmask, System.decodeDataBarrier, System.decodeTLBI,
    System.get_translation_base_address, System.create_AccessDescriptorTTW,
    System.ASID_read, System.read_memory, System.rMem, System.wMem,
    System.iFetch, System.rX, System.wX, System.rW, System.wW,
    System.rXS, System.wXS, System.rPC, System.wPC,
    System.create_writeAccessDescriptor,
    System.create_readAccessDescriptor,
    System.create_iFetchAccessDescriptor,
    System.dataMemoryBarrier, System.dataSynchronizationBarrer,
    System.instructionSynchronizationBarrier, System.reportTLBI,
    System.fail.

Ltac solve_VMPromising_Sail_at_most_one_promise_expanded :=
  VMPromising_Sail_unfold_execute_helpers;
  solve_VMPromising_Sail_at_most_one_promise_src.

Ltac solve_VMPromising_Sail_prefix_from_at_most_one_stable :=
  eapply VMPromising_Sail_prefix_promised_stable_from_at_most_one_stable;
  [first
     [solve_VMPromising_Sail_at_most_one_promise_expanded
     |solve_VMPromising_Sail_at_most_one_promise_src]
  |first
     [solve_VMPromising_Sail_promised_stable_read_code_translation
     |VMPromising_Sail_unfold_execute_helpers;
      solve_VMPromising_Sail_promised_stable_read_code_translation]].

Ltac solve_VMPromising_Sail_prefix_promised_stable_read_code_translation :=
  lazymatch goal with
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Interface.Ret _) =>
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.returnm _) =>
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.early_return _) =>
      unfold System_types.Defs.early_return;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.early_return _) =>
      unfold Defs.early_return;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.fail _) =>
      apply VMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply VMPromising_Sail_no_promise_fail
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.throw _) =>
      apply VMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply VMPromising_Sail_no_promise_throw
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_mem_write _ _ _) =>
      apply VMPromising_Sail_prefix_promised_stable_sail_mem_write
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.sail_mem_write _ _ _) =>
      apply VMPromising_Sail_prefix_promised_stable_sail_mem_write
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.sail_tlbi _) =>
      apply VMPromising_Sail_prefix_promised_stable_sail_tlbi
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.sail_tlbi _) =>
      apply VMPromising_Sail_prefix_promised_stable_sail_tlbi
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System.wMem _ _ _ _) =>
      unfold System.wMem;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System.reportTLBI _ _ _) =>
      unfold System.reportTLBI;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System.execute _) =>
      unfold System.execute;
      repeat match goal with
      | p : _ * _ |- _ => destruct p; cbn [System.execute]
      | u : unit |- _ => destruct u; cbn [System.execute]
      end;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System.execute_Store _ _ _ _) =>
      unfold System.execute_Store;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System.execute_TLBInvalidation _ _) =>
      unfold System.execute_TLBInvalidation;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply VMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_VMPromising_Sail_no_promise_src_prefix
         |solve_VMPromising_Sail_promised_stable_prefix
         |intro;
          solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
        |eapply VMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
         |intro; solve_VMPromising_Sail_no_promise_src_prefix]]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.bind _ _) =>
      unfold Defs.bind;
      first
        [eapply VMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_VMPromising_Sail_no_promise_src_prefix
         |solve_VMPromising_Sail_promised_stable_prefix
         |intro;
          solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
        |eapply VMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
         |intro; solve_VMPromising_Sail_no_promise_src_prefix]]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_VMPromising_Sail_no_promise_src_prefix
         |solve_VMPromising_Sail_promised_stable_prefix
         |intro;
          solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
        |eapply VMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
         |intro; solve_VMPromising_Sail_no_promise_src_prefix]]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_VMPromising_Sail_no_promise_src_prefix
         |solve_VMPromising_Sail_promised_stable_prefix
         |intro;
          solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
        |eapply VMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
         |intro; solve_VMPromising_Sail_no_promise_src_prefix]]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_prefix_promised_stable_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_src_prefix
      |solve_VMPromising_Sail_promised_stable_prefix
      |solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_prefix_promised_stable_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_src_prefix
      |solve_VMPromising_Sail_promised_stable_read_code_translation
      |solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- context[Defs.bind] =>
      unfold Defs.bind;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.liftR _) =>
      first
        [eapply VMPromising_Sail_prefix_promised_stable_liftR_no_left;
         [solve_VMPromising_Sail_no_promise_src_prefix
         |solve_VMPromising_Sail_promised_stable_prefix]
        |eapply VMPromising_Sail_prefix_promised_stable_liftR_no_right;
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (Defs.liftR _) =>
      first
        [eapply VMPromising_Sail_prefix_promised_stable_liftR_no_left;
         [solve_VMPromising_Sail_no_promise_src_prefix
         |solve_VMPromising_Sail_promised_stable_prefix]
        |eapply VMPromising_Sail_prefix_promised_stable_liftR_no_right;
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ (System_types.Defs.catch_early_return _) =>
      first
        [eapply
         VMPromising_Sail_prefix_promised_stable_catch_early_return_no_left;
         [solve_VMPromising_Sail_no_promise_src_prefix
         |solve_VMPromising_Sail_promised_stable_read_code_translation]
        |eapply
           VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right;
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- context[match ?x with _ => _ end] =>
      destruct x;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- context[if ?x then _ else _] =>
      destruct x;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable _ _ _ _ _ _ =>
      first
        [progress cbn [System_types.Defs.bind Defs.bind];
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
        |progress VMPromising_Sail_simpl;
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
        |apply VMPromising_Sail_prefix_promised_stable_from_no_promise;
         solve_VMPromising_Sail_no_promise_src_prefix]
  end.

Lemma VMPromising_Sail_prefix_promised_stable_execute_Store
    bbm_param tid initmem code ev nondet size t n op :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System.execute_Store size t n op).
Proof.
  intro Hstable.
  unfold System.execute_Store.
  eapply VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
  - solve_VMPromising_Sail_no_promise_src.
  - solve_VMPromising_Sail_promised_stable_read_code_translation.
  - intro accdesc.
    cbn [System_types.Defs.bind].
    eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
    + destruct op; solve_VMPromising_Sail_no_promise_src.
    + destruct op; cbn [System_types.Defs.bind].
      * eapply VMPromising_Sail_promised_stable_bind.
        -- apply VMPromising_Sail_promised_stable_liftR.
           apply VMPromising_Sail_promised_stable_rX.
        -- intro.
           eapply VMPromising_Sail_promised_stable_bind.
           ++ apply VMPromising_Sail_promised_stable_liftR.
              apply VMPromising_Sail_promised_stable_rX.
           ++ intro.
              exact I.
      * eapply VMPromising_Sail_promised_stable_bind.
        -- apply VMPromising_Sail_promised_stable_liftR.
           apply VMPromising_Sail_promised_stable_rX.
        -- intro.
           exact I.
    + intro vaddr.
      cbn [System_types.Defs.bind].
      eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
      * solve_VMPromising_Sail_no_promise_src.
      * solve_VMPromising_Sail_promised_stable_read_code_translation.
      * intro addr_opt.
        cbn [System_types.Defs.bind].
        eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
        -- destruct addr_opt; solve_VMPromising_Sail_no_promise_src.
        -- destruct addr_opt;
             solve_VMPromising_Sail_promised_stable_read_code_translation.
        -- intro addr.
           cbn [System_types.Defs.bind].
           eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
           ++ solve_VMPromising_Sail_no_promise_src.
           ++ solve_VMPromising_Sail_promised_stable_read_code_translation.
           ++ intro pc.
              cbn [System_types.Defs.bind System_types.Defs.bind0].
              eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
              ** solve_VMPromising_Sail_no_promise_src.
              ** eapply VMPromising_Sail_promised_stable_bind.
                 --- apply VMPromising_Sail_promised_stable_liftR.
                     apply VMPromising_Sail_promised_stable_write_reg.
                 --- intro.
                     apply VMPromising_Sail_promised_stable_liftR.
                     apply VMPromising_Sail_promised_stable_rX.
              ** intro value.
                 eapply
                   VMPromising_Sail_prefix_promised_stable_liftR_no_right.
                 unfold System.wMem.
                 solve_VMPromising_Sail_prefix_promised_stable_read_code_translation.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_execute_TLBInvalidation
    bbm_param tid initmem code ev nondet op t :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet
    (System.execute_TLBInvalidation op t).
Proof.
  intro Hstable.
  unfold System.execute_TLBInvalidation.
  eapply VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
  - solve_VMPromising_Sail_no_promise_src.
  - apply VMPromising_Sail_promised_stable_liftR.
    apply VMPromising_Sail_promised_stable_read_reg.
  - intro pc.
    cbn [System_types.Defs.bind System_types.Defs.bind0].
    eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
    + solve_VMPromising_Sail_no_promise_src.
    + eapply VMPromising_Sail_promised_stable_bind.
      * apply VMPromising_Sail_promised_stable_liftR.
        apply VMPromising_Sail_promised_stable_write_reg.
      * intro.
        destruct op; cbn [System_types.Defs.bind];
          first
            [exact I
            |eapply VMPromising_Sail_promised_stable_bind;
             [apply VMPromising_Sail_promised_stable_liftR;
              apply VMPromising_Sail_promised_stable_rX
             |intro; exact I]
            |unfold System_types.Defs.early_return;
             apply VMPromising_Sail_promised_stable_throw].
    + intros [va asid].
      eapply VMPromising_Sail_prefix_promised_stable_liftR_no_right.
      unfold System.reportTLBI.
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_fetch_and_execute_from_read_code_translation
    bbm_param tid initmem code ev nondet :
  VMPromising_read_code_translation_stability
    bbm_param tid initmem code ev →
  VMPromising_Sail_prefix_promised_stable
    bbm_param tid initmem ev nondet (System.fetch_and_execute tt).
Proof.
  intro Hstable.
  unfold System.fetch_and_execute.
  eapply VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
  - solve_VMPromising_Sail_no_promise_src.
  - solve_VMPromising_Sail_promised_stable_read_code_translation.
  - intro accdesc.
    cbn [System_types.Defs.bind].
    eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
    + solve_VMPromising_Sail_no_promise_src.
    + solve_VMPromising_Sail_promised_stable_read_code_translation.
    + intro pc.
      cbn [System_types.Defs.bind].
      eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
      * solve_VMPromising_Sail_no_promise_src.
      * solve_VMPromising_Sail_promised_stable_read_code_translation.
      * intro addr_opt.
        cbn [System_types.Defs.bind].
        eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
        -- destruct addr_opt; solve_VMPromising_Sail_no_promise_src.
        -- destruct addr_opt;
             solve_VMPromising_Sail_promised_stable_read_code_translation.
        -- intro addr_ret.
           cbn [System_types.Defs.bind].
           eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
           ++ solve_VMPromising_Sail_no_promise_src.
           ++ solve_VMPromising_Sail_promised_stable_read_code_translation.
           ++ intro machineCode.
              cbn [System_types.Defs.bind].
              eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
              ** solve_VMPromising_Sail_no_promise_src.
              ** solve_VMPromising_Sail_promised_stable_read_code_translation.
              ** intro instr_opt.
                 destruct instr_opt as [instr|].
                 { eapply
                     VMPromising_Sail_prefix_promised_stable_liftR_no_right.
                   unfold System.execute;
                   destruct instr; cbn [System.execute];
                   repeat match goal with
                   | p : _ * _ |- _ => destruct p; cbn [System.execute]
                   | u : unit |- _ => destruct u; cbn [System.execute]
                   end;
                   [ apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     apply VMPromising_Sail_no_promise_execute_Load
                   | eapply
                       VMPromising_Sail_prefix_promised_stable_execute_Store;
                     exact Hstable
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | eapply
                       VMPromising_Sail_prefix_promised_stable_execute_TLBInvalidation;
                     exact Hstable
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src
                   | apply
                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
                     solve_VMPromising_Sail_no_promise_src ]. }
                 { apply
                     VMPromising_Sail_prefix_promised_stable_from_no_promise.
                   solve_VMPromising_Sail_no_promise_src. }
Qed.

Ltac solve_VMPromising_no_promise_outcome :=
  eapply VMPromising_handle_outcome_no_promise_non_mem_write_tlb;
  [intros ? ? ? Hneq; discriminate Hneq
  | intros ? Hneq; discriminate Hneq].

Ltac solve_VMPromising_cmon_no_promise :=
  repeat progress (
    cbn [Sail_outcome_interp Sail_choose Sail_nochoose
         mcall_noret mdiscard mchoosef mchoosel mchoose] in *;
    unfold mret, mbind, fmap, mthrow, mcall, mcallM,
      mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
      iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
    cbn in *);
  repeat match goal with
  | H : Empty_set |- _ => destruct H
  | H : False |- _ => contradiction
  | |- context[if ?b then _ else _] => destruct b; cbn in *
  | |- CPState.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- CPState.handle_outcome_no_promise (VMPromising _) _ _ _ =>
      solve_VMPromising_no_promise_outcome
  end.

Ltac solve_VMPromising_cmon_at_most_one :=
  repeat progress (
    cbn [Sail_outcome_interp Sail_choose Sail_nochoose
         mcall_noret mdiscard mchoosef mchoosel mchoose] in *;
    unfold mret, mbind, fmap, mthrow, mcall, mcallM,
      mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
      iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
    cbn in *);
  repeat match goal with
  | H : Empty_set |- _ => destruct H
  | H : False |- _ => contradiction
  | |- context[if ?b then _ else _] => destruct b; cbn in *
  | |- CPState.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- CPState.cmon_at_most_one_promise _ _ _ _ _ => progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- CPState.handle_outcome_no_promise (VMPromising _) _ _ _ =>
      solve_VMPromising_no_promise_outcome
  | |- _ ∨ _ =>
      first [left; split; [solve_VMPromising_no_promise_outcome|]
            | right; solve_VMPromising_cmon_no_promise]
  end.

Ltac solve_VMPromising_cmon_at_most_one_prefix :=
  repeat progress (
    cbn [Sail_outcome_interp Sail_choose Sail_nochoose
         mcall_noret mdiscard mchoosef mchoosel mchoose] in *;
    unfold mret, mbind, fmap, mthrow, mcall, mcallM,
      mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
      iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
    cbn in *);
  repeat match goal with
  | H : Empty_set |- _ => destruct H
  | H : False |- _ => contradiction
  | |- context[if ?b then _ else _] => destruct b; cbn in *
  | |- CPState.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- CPState.cmon_at_most_one_promise_prefix_stable _ _ _ _ _ _ =>
      progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- _ ∨ _ => right; solve_VMPromising_cmon_no_promise
  end.

Lemma VMPromising_Sail_outcome_no_promise_interp
    (bbm_param : BBM.param) {n eo A}
    (tid : fin n) initmem nondet (out : SI.outcome eo A) :
  VMPromising_Sail_outcome_no_promise out →
  CPState.cmon_no_promise (VMPromising bbm_param) tid initmem A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; intro Hout; try contradiction;
    solve_VMPromising_cmon_no_promise.
  all: destruct ty; solve_VMPromising_cmon_no_promise.
Qed.

Lemma VMPromising_Sail_outcome_at_most_one_promise_interp
    (bbm_param : BBM.param) {n eo A}
    (tid : fin n) initmem nondet (out : SI.outcome eo A) :
  CPState.cmon_at_most_one_promise
    (VMPromising bbm_param) tid initmem A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; solve_VMPromising_cmon_at_most_one.
  all: destruct ty; solve_VMPromising_cmon_at_most_one.
Qed.

Lemma VMPromising_Sail_outcome_at_most_one_prefix_stable_interp
    (bbm_param : BBM.param) {n eo A}
    (tid : fin n) initmem ev nondet (out : SI.outcome eo A) :
  CPState.cmon_at_most_one_promise_prefix_stable
    (VMPromising bbm_param) tid initmem ev A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; solve_VMPromising_cmon_at_most_one_prefix.
  all: destruct ty; solve_VMPromising_cmon_at_most_one_prefix.
Qed.

Lemma VMPromising_iMon_from_Sail_no_promise
    (bbm_param : BBM.param) {n eo A}
    (tid : fin n) initmem nondet (smon : SI.iMon eo A) :
  VMPromising_Sail_no_promise smon →
  CPState.cmon_no_promise (VMPromising bbm_param) tid initmem A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hno_promise.
  - exact I.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    eapply CPState.cmon_no_promise_bind.
    + apply VMPromising_Sail_outcome_no_promise_interp.
      exact Hout.
    + intro ret.
      apply IH.
      apply Htail.
Qed.

Lemma VMPromising_iMon_from_Sail_at_most_one_promise
    (bbm_param : BBM.param) {n eo A}
    (tid : fin n) initmem nondet (smon : SI.iMon eo A) :
  VMPromising_Sail_at_most_one_promise smon →
  CPState.cmon_at_most_one_promise
    (VMPromising bbm_param) tid initmem A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hat_most.
  - exact I.
  - cbn in Hat_most |- *.
    destruct Hat_most as [[Hout Htail_at_most]|Htail_no_promise].
    + eapply CPState.cmon_at_most_one_promise_bind_no_left.
      * apply VMPromising_Sail_outcome_no_promise_interp.
        exact Hout.
      * intro ret.
        apply IH.
        apply Htail_at_most.
    + eapply CPState.cmon_at_most_one_promise_bind_no_right.
      * apply VMPromising_Sail_outcome_at_most_one_promise_interp.
      * intro ret.
        apply VMPromising_iMon_from_Sail_no_promise.
        apply Htail_no_promise.
Qed.

Lemma VMPromising_iMon_from_Sail_prefix_promised_stable
    (bbm_param : BBM.param) {n eo A}
    (tid : fin n) initmem ev nondet (smon : SI.iMon eo A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param (tid : nat) initmem ev nondet smon →
  CPState.cmon_at_most_one_promise_prefix_stable
    (VMPromising bbm_param) tid initmem ev A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hstable.
  - exact I.
  - cbn in Hstable |- *.
    destruct Hstable as
      [[Hout_no [Hout_stable Htail_stable]]|Htail_no_promise].
    + eapply CPState.cmon_at_most_one_promise_prefix_stable_bind_no_left.
      * apply VMPromising_Sail_outcome_no_promise_interp.
        exact Hout_no.
      * apply VMPromising_imon_future_promise_stable_promised_to_cmon.
        exact Hout_stable.
      * intro ret.
        apply IH.
        apply Htail_stable.
    + eapply CPState.cmon_at_most_one_promise_prefix_stable_bind_no_right.
      * apply VMPromising_Sail_outcome_at_most_one_prefix_stable_interp.
      * intro ret.
        apply VMPromising_iMon_from_Sail_no_promise.
        apply Htail_no_promise.
Qed.
