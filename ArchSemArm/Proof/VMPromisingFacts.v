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
From ArchSemArm Require Import ArmInst VMPromising.

#[local] Open Scope list.
#[local] Open Scope nat.
#[local] Open Scope stdpp.

Import Promising.

#[local] Typeclasses Transparent Memory.t.
#[local] Typeclasses Transparent view.

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

Definition code_region := address → Prop.

Definition event_read_byte (a : address) (ev : Ev.t) : option (bv 8) :=
  match ev with
  | Ev.Msg msg => Msg.read_byte a msg
  | Ev.Tlbi _ _ => None
  end.

Definition event_misses_code (code : code_region) (ev : Ev.t) : Prop :=
  ∀ a, code a → event_read_byte a ev = None.

Definition ifetch_in_code (code : code_region) (addr : address) (size : N) :
    Prop :=
  ∀ a, a ∈ addr_range addr size → code a.

Definition event_misses_ifetch (ev : Ev.t) (addr : address) (size : N) :
    Prop :=
  ∀ a, a ∈ addr_range addr size → event_read_byte a ev = None.

Lemma event_misses_code_ifetch code ev addr size :
  event_misses_code code ev →
  ifetch_in_code code addr size →
  event_misses_ifetch ev addr size.
Proof.
  intros Hmiss Hifetch a Ha.
  apply Hmiss.
  apply Hifetch.
  exact Ha.
Qed.

Lemma read_last_cons_miss addr init mem ev :
  event_read_byte addr ev = None →
  Memory.read_last addr init (ev :: mem) = Memory.read_last addr init mem.
Proof.
  destruct ev as [msg|tlbi recipient]; cbn.
  - intro Hmiss.
    rewrite Hmiss.
    reflexivity.
  - reflexivity.
Qed.

Lemma read_initial_cons_miss addr init mem ev :
  event_read_byte addr ev = None →
  Memory.read_initial addr init (ev :: mem) = Memory.read_initial addr init mem.
Proof.
  intro Hmiss.
  unfold Memory.read_initial.
  rewrite (read_last_cons_miss addr init mem ev Hmiss).
  reflexivity.
Qed.

Lemma read_imem_cons_miss addr init mem ev :
  event_misses_ifetch ev addr 4 →
  read_imem addr init (ev :: mem) = read_imem addr init mem.
Proof.
  intro Hmiss.
  unfold read_imem.
  set (addrs := addr_range addr 4).
  assert (Hall : ∀ a, a ∈ addrs → event_read_byte a ev = None).
  { intros a Ha.
    subst addrs.
    apply Hmiss.
    exact Ha. }
  assert
    (Hbytes :
       (for a in addrs do
          Memory.read_initial a init (ev :: mem)
        end) =
       (for a in addrs do
          Memory.read_initial a init mem
        end)).
  { induction addrs as [|a addrs IH].
    - reflexivity.
    - cbn.
      rewrite read_initial_cons_miss.
      + rewrite IH.
        * reflexivity.
        * intros a' Ha'.
          apply Hall.
          right.
          exact Ha'.
      + apply Hall.
        apply elem_of_cons.
        left.
        reflexivity. }
  subst addrs.
  rewrite Hbytes.
  reflexivity.
Qed.

Lemma read_imem_cons_misses_code code addr init mem ev :
  event_misses_code code ev →
  ifetch_in_code code addr 4 →
  read_imem addr init (ev :: mem) = read_imem addr init mem.
Proof.
  intros Hmiss Hifetch.
  apply read_imem_cons_miss.
  eapply event_misses_code_ifetch; eauto.
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

Lemma TState_promise_vtlbi_self (ev : Ev.t) p ts :
  TState.vtlbi_self (TState_promise_event ev p ts) =
  TState.vtlbi_self ts.
Proof.
  destruct ev, ts; reflexivity.
Qed.

Lemma TState_promise_vtlbi_other (ev : Ev.t) p ts :
  TState.vtlbi_other (TState_promise_event ev p ts) =
  TState.vtlbi_other ts.
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

Lemma TState_no_write_promises_until_promise_event ev v p ts :
  TState.no_write_promises_until v ts →
  (v < p)%nat →
  TState.no_write_promises_until v (TState_promise_event ev p ts).
Proof.
  unfold TState.no_write_promises_until, TState_promise_event.
  destruct ev as [msg|tlbi]; destruct ts; cbn; intros Hno Hlt p' Hp'.
  - apply elem_of_cons in Hp' as [->|Hp']; [exact Hlt|].
    apply Hno. exact Hp'.
  - apply Hno. exact Hp'.
Qed.

Definition ppstate_control_times_le
    (ppst : PPState.t TState.t Ev.t IIS.t) : Prop :=
  (IIS.strict (PPState.iis ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vrd (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vwr (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vspec (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vcse (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vdsb (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vmsr (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vdmb (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vdmbst (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vtlbi_self (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vtlbi_other (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vacq (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vrel (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (∀ inv_time,
    IIS.inv_time (PPState.iis ppst) = Some inv_time →
    (inv_time ≤ length (PPState.mem ppst))%nat).

Lemma ppstate_control_inv_time_le ppst inv_time :
  ppstate_control_times_le ppst →
  IIS.inv_time (PPState.iis ppst) = Some inv_time →
  (inv_time ≤ length (PPState.mem ppst))%nat.
Proof.
  unfold ppstate_control_times_le.
  intros Hcontrol Hinv_time.
  intuition eauto.
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
        TState_promise_vmsr.
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
      destruct (IIS.trans_active iis) eqn:Hactive.
      2: {
        unfold elem_of, Exec.elem_of_results in Hrun.
        try rewrite Hactive in Hrun.
        cbn in Hrun.
        exfalso.
        apply (not_elem_of_nil ((ts', iis'), ())).
        exact Hrun.
      }
      destruct (IIS.trs iis) as [trs|] eqn:Htrs.
      2: {
        unfold elem_of, Exec.elem_of_results in Hrun.
        try rewrite Hactive in Hrun.
        try rewrite Htrs in Hrun.
        cbn in Hrun.
        exfalso.
        apply (not_elem_of_nil ((ts', iis'), ())).
        exact Hrun.
      }
      cbn in Hrun.
      apply Exec.elem_of_bind_elim in Hrun as
        [st_trs [trs0 [Htrs_ret Hrun]]].
      apply Exec.elem_of_mret_inv in Htrs_ret as [-> ->].
      cbn in Hrun.
      eapply Exec.elem_of_bind_intro with
        (st' := (TState_promise_event ev p ts, iis)) (a := trs).
      { apply Exec.elem_of_mret. }
      cbn.
      destruct
        (decide (FaultRecord_statuscode (AddressDescriptor_fault trans_end)
                 = Fault_None)) as [Hno_fault|Hfault].
	      * apply Exec.elem_of_bind_elim in Hrun as
	          [st_add [[] [Hadd Hrun]]].
	        apply Exec.elem_of_mset_inv in Hadd as ->.
	        change (set snd (IIS.add (IIS.TransRes.trans_start trs)) (ts, iis))
	          with (ts, IIS.add (IIS.TransRes.trans_start trs) iis) in Hrun.
	        unfold msetv in Hrun.
	        change
	          (Exec.elem_of_results (ts', iis', ())
	             ((mset snd IIS.finish_trans :
	                 Exec.t (TState.t * IIS.t) string unit)
	                (ts, IIS.add (IIS.TransRes.trans_start trs) iis))) in Hrun.
	        apply Exec.elem_of_mset_inv in Hrun as Heq.
	        inversion Heq; subst ts' iis'.
	        eapply Exec.elem_of_bind_intro with
	          (st' := (TState_promise_event ev p ts,
	                   IIS.add (IIS.TransRes.trans_start trs) iis))
	          (a := ()).
	        -- change (TState_promise_event ev p ts,
	                IIS.add (IIS.TransRes.trans_start trs) iis)
	             with
	             (set snd (IIS.add (IIS.TransRes.trans_start trs))
	                (TState_promise_event ev p ts, iis)).
	           apply Exec.elem_of_mset.
	        -- unfold msetv.
	           change
	             (Exec.elem_of_results
	                (set snd IIS.finish_trans
	                   (TState_promise_event ev p ts,
	                    IIS.add (IIS.TransRes.trans_start trs) iis), ())
	                ((mset snd IIS.finish_trans :
	                     Exec.t (TState.t * IIS.t) string unit)
	                   (TState_promise_event ev p ts,
	                    IIS.add (IIS.TransRes.trans_start trs) iis))).
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
           set (is_ifetch :=
             AccessDescriptor_acctype
               (FaultRecord_access (AddressDescriptor_fault trans_end)) =?
             AccessType_IFETCH).
           set (trans_time :=
             max (IIS.TransRes.trans_start trs)
               (view_if (is_ets3 && negb is_ifetch)
                  (max (TState.vrd ts) (TState.vwr ts)))).
           destruct (trans_time <=? IIS.TransRes.trans_end trs)
             eqn:Htrans_bound.
           ++ rewrite Htrans_bound in Hrun.
              cbn in Hrun.
              apply Exec.elem_of_bind_elim in Hrun as
                [st_add_trans [[] [Hadd_trans Hrun]]].
              apply Exec.elem_of_mset_inv in Hadd_trans as ->.
              apply Exec.elem_of_bind_elim in Hrun as
                [st_read [read_view [Hread Hrun]]].
              change (set snd (IIS.add trans_time) (ts, iis))
                with (ts, IIS.add trans_time iis) in Hread.
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
                   (ts, IIS.add trans_time iis))
                with
                (ts,
                 IIS.add
                   (view_if
                      (AccessDescriptor_read
                         (FaultRecord_access
                            (AddressDescriptor_fault trans_end)))
                      read_view)
                   (IIS.add trans_time iis)) in Hwrite.
              destruct st_write as [ts_write iis_write0].
              pose proof (write_fault_vpre_state _ _ _ _ _ _ _ Hwrite)
                as [-> ->].
	              apply Exec.elem_of_bind_elim in Hrun as
	                [st_add_write [[] [Hadd_write Hrun]]].
	              apply Exec.elem_of_mset_inv in Hadd_write as Hadd_write_eq.
	              change
	                (Exec.elem_of_results (ts', iis', ())
	                   ((mset snd IIS.finish_trans :
	                       Exec.t (TState.t * IIS.t) string unit)
	                      (st_add_write))) in Hrun.
              apply Exec.elem_of_mset_inv in Hrun as Heq.
              inversion Heq; subst ts' iis'.
              subst st_add_write.
              set (iis_trans := IIS.add trans_time iis).
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
              subst trans_time.
              rewrite Htrans_bound.
              cbn.
              eapply Exec.elem_of_bind_intro with
                (st' := (TState_promise_event ev p ts, iis_trans)) (a := ()).
              ** subst iis_trans.
                 change
                   (Exec.elem_of_results
                      (set snd (IIS.add
                         (max (IIS.TransRes.trans_start trs)
                            (view_if (is_ets3 && negb is_ifetch)
                               (max (TState.vrd ts) (TState.vwr ts)))))
                         (TState_promise_event ev p ts, iis), ())
                      ((mset snd (IIS.add
                          (max (IIS.TransRes.trans_start trs)
                             (view_if (is_ets3 && negb is_ifetch)
                                (max (TState.vrd ts) (TState.vwr ts))))) :
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
	                                       (set snd IIS.finish_trans
	                                          (TState_promise_event ev p ts, iis_write), ())
	                                       ((mset snd IIS.finish_trans :
	                                          Exec.t (TState.t * IIS.t) string
	                                             unit)
	                                          (TState_promise_event ev p ts, iis_write))).
                                  apply Exec.elem_of_mset.
           ++ unfold elem_of, Exec.elem_of_results in Hrun.
              rewrite Htrans_bound in Hrun.
              cbn in Hrun.
              exfalso.
              apply (not_elem_of_nil ((ts', iis'), ())).
              exact Hrun.
Qed.

(*
  Direct DMB/DSB promised-stability would require a bound such as
  [vpost < p]. POPL27 semantics does not guard barriers with [vpost <= vmax],
  so these strong arbitrary-state lemmas are not available without changing
  executable semantics. Prefix proofs handle barriers through the no-promise
  route instead.

Lemma run_barrier_dmb_promise_state (ev : Ev.t) p vmax dmb ts iis ts' iis' u :
  (vmax < p)%nat →
  Exec.elem_of_results ((ts', iis'), u)
    (run_barrier (Barrier_DMB dmb) vmax (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), u)
    (run_barrier (Barrier_DMB dmb) p (TState_promise_event ev p ts, iis)).
Proof.
  intros Hvmax_lt Hrun.
  unfold run_barrier in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  destruct dmb.(DxB_types) eqn:Hdmb.
  - set (vpost := Nat.max (Nat.max (TState.vrd ts) (TState.vcse ts)) (TState.vdsb ts)).
    apply Exec.elem_of_bind_elim in Hrun as
      [st_bound [bound_pf [Hbound Hrun]]].
    apply Exec.elem_of_guard_discard_inv in Hbound as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [st_guard [guard_pf [Hguard Hrun]]].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [st_state [unit_val [Hstate Hrun]]].
    destruct unit_val.
    apply Exec.elem_of_mset_inv in Hstate as ->.
    unfold elem_of, Exec.elem_of_results in Hrun.
    cbn in Hrun.
    apply elem_of_list_singleton in Hrun.
    inversion Hrun; subst ts' iis' u.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
    + apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
    + cbn.
      rewrite TState_promise_vrd, TState_promise_vcse,
        TState_promise_vdsb.
      fold vpost.
      destruct (Exec.elem_of_guard_discard
        (St:=TState.t * IIS.t) (E:=string)
        (P:=(vpost <= p)%nat)
        (TState_promise_event ev p ts, iis)) as
        [bound_pf' Hbound'].
      { eapply Nat.le_trans; [exact bound_pf|lia]. }
      eapply Exec.elem_of_bind_intro with
        (e := guard_discard (vpost <= p)%nat)
        (st' := (TState_promise_event ev p ts, iis))
        (a := bound_pf').
      * exact Hbound'.
      * cbn.
        destruct (@Exec.elem_of_guard_discard
          (TState.t * IIS.t)%type string
          (TState.no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState.Decision_no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState_promise_event ev p ts, iis)) as
          [guard_pf' Hguard'].
        { apply TState_no_write_promises_until_promise_event; [exact guard_pf|].
          eapply Nat.le_lt_trans; [exact bound_pf|exact Hvmax_lt]. }
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard
                  (TState.no_write_promises_until vpost
                     (TState_promise_event ev p ts)))
          (st' := (TState_promise_event ev p ts, iis))
          (a := guard_pf').
        -- exact Hguard'.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p
                        (TState.update TState.vdmb vpost ts), iis))
             (a := ()).
           ++ subst vpost.
              rewrite <- TState_promise_update_vdmb.
              change (TState.update TState.vdmb
                        ((TState.vrd ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)
                        (TState_promise_event ev p ts), iis)
                with
                (set fst
                   (TState.update TState.vdmb
                      ((TState.vrd ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts))
                   (TState_promise_event ev p ts, iis)).
              unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
           ++ unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
  - set (vpost := Nat.max (Nat.max (TState.vwr ts) (TState.vcse ts)) (TState.vdsb ts)).
    apply Exec.elem_of_bind_elim in Hrun as
      [st_bound [bound_pf [Hbound Hrun]]].
    apply Exec.elem_of_guard_discard_inv in Hbound as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [st_guard [guard_pf [Hguard Hrun]]].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [st_state [unit_val [Hstate Hrun]]].
    destruct unit_val.
    apply Exec.elem_of_mset_inv in Hstate as ->.
    unfold elem_of, Exec.elem_of_results in Hrun.
    cbn in Hrun.
    apply elem_of_list_singleton in Hrun.
    inversion Hrun; subst ts' iis' u.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
    + apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
    + cbn.
      rewrite TState_promise_vwr, TState_promise_vcse,
        TState_promise_vdsb.
      fold vpost.
      destruct (Exec.elem_of_guard_discard
        (St:=TState.t * IIS.t) (E:=string)
        (P:=(vpost <= p)%nat)
        (TState_promise_event ev p ts, iis)) as
        [bound_pf' Hbound'].
      { eapply Nat.le_trans; [exact bound_pf|lia]. }
      eapply Exec.elem_of_bind_intro with
        (e := guard_discard (vpost <= p)%nat)
        (st' := (TState_promise_event ev p ts, iis))
        (a := bound_pf').
      * exact Hbound'.
      * cbn.
        destruct (@Exec.elem_of_guard_discard
          (TState.t * IIS.t)%type string
          (TState.no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState.Decision_no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState_promise_event ev p ts, iis)) as
          [guard_pf' Hguard'].
        { apply TState_no_write_promises_until_promise_event; [exact guard_pf|].
          eapply Nat.le_lt_trans; [exact bound_pf|exact Hvmax_lt]. }
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard
                  (TState.no_write_promises_until vpost
                     (TState_promise_event ev p ts)))
          (st' := (TState_promise_event ev p ts, iis))
          (a := guard_pf').
        -- exact Hguard'.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p
                        (TState.update TState.vdmbst vpost ts), iis))
             (a := ()).
           ++ subst vpost.
              rewrite <- TState_promise_update_vdmbst.
              change (TState.update TState.vdmbst
                        ((TState.vwr ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)
                        (TState_promise_event ev p ts), iis)
                with
                (set fst
                   (TState.update TState.vdmbst
                      ((TState.vwr ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts))
                   (TState_promise_event ev p ts, iis)).
              unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
           ++ unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
  - set (vpost := Nat.max (Nat.max (Nat.max (TState.vrd ts) (TState.vwr ts)) (TState.vcse ts)) (TState.vdsb ts)).
    apply Exec.elem_of_bind_elim in Hrun as
      [st_bound [bound_pf [Hbound Hrun]]].
    apply Exec.elem_of_guard_discard_inv in Hbound as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [st_guard [guard_pf [Hguard Hrun]]].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [st_state [unit_val [Hstate Hrun]]].
    destruct unit_val.
    apply Exec.elem_of_mset_inv in Hstate as ->.
    unfold elem_of, Exec.elem_of_results in Hrun.
    cbn in Hrun.
    apply elem_of_list_singleton in Hrun.
    inversion Hrun; subst ts' iis' u.
    eapply Exec.elem_of_bind_intro with
      (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
    + apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
    + cbn.
      rewrite TState_promise_vrd, TState_promise_vwr,
        TState_promise_vcse, TState_promise_vdsb.
      fold vpost.
      destruct (Exec.elem_of_guard_discard
        (St:=TState.t * IIS.t) (E:=string)
        (P:=(vpost <= p)%nat)
        (TState_promise_event ev p ts, iis)) as
        [bound_pf' Hbound'].
      { eapply Nat.le_trans; [exact bound_pf|lia]. }
      eapply Exec.elem_of_bind_intro with
        (e := guard_discard (vpost <= p)%nat)
        (st' := (TState_promise_event ev p ts, iis))
        (a := bound_pf').
      * exact Hbound'.
      * cbn.
        destruct (@Exec.elem_of_guard_discard
          (TState.t * IIS.t)%type string
          (TState.no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState.Decision_no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState_promise_event ev p ts, iis)) as
          [guard_pf' Hguard'].
        { apply TState_no_write_promises_until_promise_event; [exact guard_pf|].
          eapply Nat.le_lt_trans; [exact bound_pf|exact Hvmax_lt]. }
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard
                  (TState.no_write_promises_until vpost
                     (TState_promise_event ev p ts)))
          (st' := (TState_promise_event ev p ts, iis))
          (a := guard_pf').
        -- exact Hguard'.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p
                        (TState.update TState.vdmb vpost ts), iis))
             (a := ()).
           ++ subst vpost.
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
              unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
           ++ unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
Qed.

Lemma run_barrier_dsb_promise_state (ev : Ev.t) p vmax dsb ts iis ts' iis' u :
  (vmax < p)%nat →
  Exec.elem_of_results ((ts', iis'), u)
    (run_barrier (Barrier_DSB dsb) vmax (ts, iis)) →
  Exec.elem_of_results ((TState_promise_event ev p ts', iis'), u)
    (run_barrier (Barrier_DSB dsb) p (TState_promise_event ev p ts, iis)).
Proof.
  intros Hvmax_lt Hrun.
  unfold run_barrier in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [st_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  cbn in Hrun.
  eapply Exec.elem_of_bind_intro with
    (st' := (TState_promise_event ev p ts, iis)) (a := TState_promise_event ev p ts).
  - apply (Exec.elem_of_mget (E:=string) (TState_promise_event ev p ts, iis) fst).
  - cbn.
    destruct dsb.(DxB_types) eqn:Hdsb.
    + set (vpost := Nat.max (Nat.max (TState.vrd ts) (TState.vcse ts)) (TState.vdsb ts)).
      apply Exec.elem_of_bind_elim in Hrun as
        [st_bound [bound_pf [Hbound Hrun]]].
      apply Exec.elem_of_guard_discard_inv in Hbound as ->.
      apply Exec.elem_of_bind_elim in Hrun as
        [st_guard [guard_pf [Hguard Hrun]]].
      apply Exec.elem_of_guard_discard_inv in Hguard as ->.
      apply Exec.elem_of_bind_elim in Hrun as
        [st_state [unit_val [Hstate Hrun]]].
      destruct unit_val.
      apply Exec.elem_of_mset_inv in Hstate as ->.
      unfold elem_of, Exec.elem_of_results in Hrun.
      cbn in Hrun.
      apply elem_of_list_singleton in Hrun.
      inversion Hrun; subst ts' iis' u.
      rewrite TState_promise_vrd, TState_promise_vcse,
        TState_promise_vdsb.
      fold vpost.
      destruct (Exec.elem_of_guard_discard
        (St:=TState.t * IIS.t) (E:=string)
        (P:=(vpost <= p)%nat)
        (TState_promise_event ev p ts, iis)) as
        [bound_pf' Hbound'].
      { eapply Nat.le_trans; [exact bound_pf|lia]. }
      eapply Exec.elem_of_bind_intro with
        (e := guard_discard (vpost <= p)%nat)
        (st' := (TState_promise_event ev p ts, iis))
        (a := bound_pf').
      * exact Hbound'.
      * cbn.
        destruct (@Exec.elem_of_guard_discard
          (TState.t * IIS.t)%type string
          (TState.no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState.Decision_no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState_promise_event ev p ts, iis)) as
          [guard_pf' Hguard'].
        { apply TState_no_write_promises_until_promise_event; [exact guard_pf|].
          eapply Nat.le_lt_trans; [exact bound_pf|exact Hvmax_lt]. }
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard
                  (TState.no_write_promises_until vpost
                     (TState_promise_event ev p ts)))
          (st' := (TState_promise_event ev p ts, iis))
          (a := guard_pf').
        -- exact Hguard'.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p
                        (TState.update TState.vdsb vpost ts), iis))
             (a := ()).
           ++ rewrite <- TState_promise_update_vdsb.
              change (TState.update TState.vdsb vpost
                        (TState_promise_event ev p ts), iis)
                with
                (set fst (TState.update TState.vdsb vpost)
                   (TState_promise_event ev p ts, iis)).
              unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
           ++ unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
    + set (vpost := Nat.max (Nat.max (TState.vwr ts) (TState.vcse ts)) (TState.vdsb ts)).
      apply Exec.elem_of_bind_elim in Hrun as
        [st_bound [bound_pf [Hbound Hrun]]].
      apply Exec.elem_of_guard_discard_inv in Hbound as ->.
      apply Exec.elem_of_bind_elim in Hrun as
        [st_guard [guard_pf [Hguard Hrun]]].
      apply Exec.elem_of_guard_discard_inv in Hguard as ->.
      apply Exec.elem_of_bind_elim in Hrun as
        [st_state [unit_val [Hstate Hrun]]].
      destruct unit_val.
      apply Exec.elem_of_mset_inv in Hstate as ->.
      unfold elem_of, Exec.elem_of_results in Hrun.
      cbn in Hrun.
      apply elem_of_list_singleton in Hrun.
      inversion Hrun; subst ts' iis' u.
      rewrite TState_promise_vwr, TState_promise_vcse,
        TState_promise_vdsb.
      fold vpost.
      destruct (Exec.elem_of_guard_discard
        (St:=TState.t * IIS.t) (E:=string)
        (P:=(vpost <= p)%nat)
        (TState_promise_event ev p ts, iis)) as
        [bound_pf' Hbound'].
      { eapply Nat.le_trans; [exact bound_pf|lia]. }
      eapply Exec.elem_of_bind_intro with
        (e := guard_discard (vpost <= p)%nat)
        (st' := (TState_promise_event ev p ts, iis))
        (a := bound_pf').
      * exact Hbound'.
      * cbn.
        destruct (@Exec.elem_of_guard_discard
          (TState.t * IIS.t)%type string
          (TState.no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState.Decision_no_write_promises_until vpost
             (TState_promise_event ev p ts))
          (TState_promise_event ev p ts, iis)) as
          [guard_pf' Hguard'].
        { apply TState_no_write_promises_until_promise_event; [exact guard_pf|].
          eapply Nat.le_lt_trans; [exact bound_pf|exact Hvmax_lt]. }
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard
                  (TState.no_write_promises_until vpost
                     (TState_promise_event ev p ts)))
          (st' := (TState_promise_event ev p ts, iis))
          (a := guard_pf').
        -- exact Hguard'.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p
                        (TState.update TState.vdsb vpost ts), iis))
             (a := ()).
           ++ rewrite <- TState_promise_update_vdsb.
              change (TState.update TState.vdsb vpost
                        (TState_promise_event ev p ts), iis)
                with
                (set fst (TState.update TState.vdsb vpost)
                   (TState_promise_event ev p ts, iis)).
              unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
           ++ unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
    + set (vtlbi :=
        if decide (DxB_domain dsb = MBReqDomain_Nonshareable)
        then TState.vtlbi_self ts
        else Nat.max (TState.vtlbi_self ts) (TState.vtlbi_other ts)).
      set (vpost :=
        Nat.max
          (Nat.max
            (Nat.max
              (Nat.max
                (Nat.max
                  (Nat.max (TState.vrd ts) (TState.vwr ts))
                  (TState.vdmb ts))
                (TState.vdmbst ts))
              (TState.vcse ts))
            (TState.vdsb ts))
          vtlbi).
      apply Exec.elem_of_bind_elim in Hrun as
        [st_bound [bound_pf [Hbound Hrun]]].
      apply Exec.elem_of_guard_discard_inv in Hbound as ->.
      apply Exec.elem_of_bind_elim in Hrun as
        [st_guard [guard_pf [Hguard Hrun]]].
      apply Exec.elem_of_guard_discard_inv in Hguard as ->.
      apply Exec.elem_of_bind_elim in Hrun as
        [st_state [unit_val [Hstate Hrun]]].
      destruct unit_val.
      apply Exec.elem_of_mset_inv in Hstate as ->.
      unfold elem_of, Exec.elem_of_results in Hrun.
      cbn in Hrun.
      apply elem_of_list_singleton in Hrun.
      inversion Hrun; subst ts' iis' u.
      rewrite TState_promise_vrd, TState_promise_vwr,
        TState_promise_vdmb, TState_promise_vdmbst,
        TState_promise_vcse, TState_promise_vdsb,
        TState_promise_vtlbi_self, TState_promise_vtlbi_other.
      fold vtlbi vpost.
      destruct (Exec.elem_of_guard_discard
        (St:=TState.t * IIS.t) (E:=string)
        (P:=(vpost <= p)%nat)
        (TState_promise_event ev p ts, iis)) as
        [bound_pf' Hbound'].
      { eapply Nat.le_trans; [exact bound_pf|lia]. }
      eapply Exec.elem_of_bind_intro with
        (e := guard_discard (vpost <= p)%nat)
        (st' := (TState_promise_event ev p ts, iis))
        (a := bound_pf').
      * exact Hbound'.
      * cbn.
        destruct (@Exec.elem_of_guard_discard
          (TState.t * IIS.t)%type string
          (TState.no_promises_until vpost
             (TState_promise_event ev p ts))
          (TState.Decision_no_promises_until vpost
             (TState_promise_event ev p ts))
          (TState_promise_event ev p ts, iis)) as
          [guard_pf' Hguard'].
        { apply TState_no_promises_until_promise_event; [exact guard_pf|].
          eapply Nat.le_lt_trans; [exact bound_pf|exact Hvmax_lt]. }
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard
                  (TState.no_promises_until vpost
                     (TState_promise_event ev p ts)))
          (st' := (TState_promise_event ev p ts, iis))
          (a := guard_pf').
        -- exact Hguard'.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (st' := (TState_promise_event ev p
                        (TState.update TState.vdsb vpost ts), iis))
             (a := ()).
           ++ rewrite <- TState_promise_update_vdsb.
              change (TState.update TState.vdsb vpost
                        (TState_promise_event ev p ts), iis)
                with
                (set fst (TState.update TState.vdsb vpost)
                   (TState_promise_event ev p ts, iis)).
              unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
           ++ unfold elem_of, Exec.elem_of_results.
              cbn.
              apply elem_of_list_singleton.
              reflexivity.
Qed.

*)

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
	             (P:=reg ∈ strict_regs)
	             (TState_promise_event ev p ts)
	             ("The register should be strict: " ++
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
  destruct (IIS.trans_active iis) eqn:Hactive.
  - destruct (IIS.trs iis) as [trs|] eqn:Htrs.
    2: {
      unfold elem_of, Exec.elem_of_results in Hread.
      try rewrite Hactive in Hread.
      try rewrite Htrs in Hread.
      cbn in Hread.
      exfalso.
      apply (not_elem_of_nil (st_read, (val0, view))).
      exact Hread.
    }
    cbn in Hread.
    apply Exec.elem_of_bind_elim in Hread as
      [st_trs [trs0 [Htrs_ret Hread]]].
    apply Exec.elem_of_mret_inv in Htrs_ret as [-> ->].
    cbn in Hread.
    apply Exec.elem_of_liftSt_inv in Hread as [ts_mid [Heq Hread]].
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
        rewrite Hactive, Htrs.
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev p ts, iis)) (a := trs).
        -- apply Exec.elem_of_mret.
        -- cbn.
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
        rewrite Hactive.
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
  (length (PPState.mem ppst) <= length mem_new)%nat →
  (length (PPState.mem ppst) < p)%nat →
  (IIS.strict (PPState.iis ppst) <= length (PPState.mem ppst))%nat →
  Exec.elem_of_results (ppst', ()) (run_reg_write reg racc val ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), ())
    (run_reg_write reg racc val
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intros Hmem_le Hmem_lt Hstrict_le Hrun.
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
    [pp_iis [iis0 [Hiis Hrun]]].
  apply Exec.elem_of_mget_inv in Hiis as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts0 [Hts Hrun]]].
  apply Exec.elem_of_mget_inv in Hts as [-> ->].
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
    (P:=¬ is_reg_unknown reg)
    (PPState.Make (TState_promise_event ev p ts) mem_new iis)
      ("Cannot write to unknown register " ++ pretty reg)%string
      Hknown_prop) as [p_known' Hknown'].
  eapply Exec.elem_of_bind_intro with
    (st' := PPState.Make (TState_promise_event ev p ts) mem_new iis)
    (a := p_known').
  - exact Hknown'.
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make (TState_promise_event ev p ts) mem_new iis)
      (a := iis).
    + apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event ev p ts) mem_new iis) PPState.iis).
    + cbn.
      eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make (TState_promise_event ev p ts) mem_new iis)
        (a := TState_promise_event ev p ts).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make (TState_promise_event ev p ts) mem_new iis)
          PPState.state).
      * cbn.
        destruct racc as [racc|]; cbn in Hrun |- *.
        -- apply Exec.elem_of_bind_elim in Hrun as
             [pp_vpost [vpost_run [Hvpost Hrun]]].
           destruct (decide (reg ∈ relaxed_regs)) as [Hrel|Hnrel]
             eqn:Hrel_dec.
           ++ rewrite Hrel_dec in Hvpost.
              cbn in Hvpost.
              apply Exec.elem_of_bind_elim in Hvpost as
                [pp_read [rv_read [Hread Hvpost]]].
              destruct rv_read as [val_read view].
              unfold othrow in Hread.
              destruct (TState.read_sreg_direct ts reg)
                as [rv0|] eqn:Hread_eq.
              ** cbn in Hread.
                 destruct rv0 as [val0 view0].
                 apply Exec.elem_of_mret_inv in Hread as [-> Hread].
                 inversion Hread; subst val0 view0.
                 apply Exec.elem_of_bind_elim in Hvpost as
                   [pp_ws [[] [Hws Hvpost]]].
                 apply Exec.elem_of_mset_inv in Hws as ->.
                 apply Exec.elem_of_mret_inv in Hvpost as [-> Hvpost].
                 inversion Hvpost; subst vpost_run.
                 apply Exec.elem_of_bind_elim in Hrun as
                   [pp_vmsr [[] [Hvmsr Hrun]]].
                 apply Exec.elem_of_mset_inv in Hvmsr as ->.
                 apply Exec.elem_of_mset_inv in Hrun as ->.
                 rewrite Hrel_dec.
                 rewrite TState_read_sreg_direct_promise.
                 rewrite Hread_eq.
                 cbn.
                 rewrite !TState_promise_vcse.
                 rewrite !TState_promise_vspec.
                 rewrite !TState_promise_vdsb.
                 set (vpost :=
                   Nat.max
                     (Nat.max (IIS.strict iis)
                        (Nat.max (Nat.max (TState.vcse ts) (TState.vspec ts))
                           (TState.vdsb ts)))
                     view).
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState.add_wsreg reg val vpost
                                (TState_promise_event ev p ts))
                             mem_new iis)
                   (a := vpost).
                 {
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make (TState_promise_event ev p ts)
                             mem_new iis)
                   (a := (val_read, view)).
                 { apply Exec.elem_of_mret. }
                 cbn.
                 fold vpost.
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState.add_wsreg reg val vpost
                                (TState_promise_event ev p ts))
                             mem_new iis)
                   (a := ()).
                 { change
                     (PPState.Make
                        (TState.add_wsreg reg val vpost
                           (TState_promise_event ev p ts))
                        mem_new iis)
                     with
                     (set PPState.state
                        (TState.add_wsreg reg val vpost)
                        (PPState.Make (TState_promise_event ev p ts)
                           mem_new iis)).
                   apply Exec.elem_of_mset. }
                 cbn.
                 apply Exec.elem_of_mret.
                 }
                 cbn.
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState.update TState.vmsr vpost
                                (TState.add_wsreg reg val vpost
                                   (TState_promise_event ev p ts)))
                             mem_new iis)
                   (a := ()).
                 { change
                     (PPState.Make
                        (TState.update TState.vmsr vpost
                           (TState.add_wsreg reg val vpost
                              (TState_promise_event ev p ts)))
                        mem_new iis)
                     with
                     (set PPState.state
                        (TState.update TState.vmsr vpost)
                        (PPState.Make
                           (TState.add_wsreg reg val vpost
                              (TState_promise_event ev p ts))
                           mem_new iis)).
                   apply Exec.elem_of_mset. }
                 cbn.
                 rewrite <- TState_promise_relaxed_write.
                 change
                   (PPState.Make
                      (TState.update TState.vmsr vpost
                         (TState.add_wsreg reg val vpost
                            (TState_promise_event ev p ts)))
                      mem_new (IIS.add vpost iis))
                   with
                   (set PPState.iis (IIS.add vpost)
                      (PPState.Make
                         (TState.update TState.vmsr vpost
                            (TState.add_wsreg reg val vpost
                               (TState_promise_event ev p ts)))
                         mem_new iis)).
                 unfold elem_of, Exec.elem_of_results.
                 cbn.
                 apply elem_of_list_singleton.
                 reflexivity.
              ** cbn in Hread.
                 exfalso.
                 apply (not_elem_of_nil (pp_read, (val_read, view))).
                 exact Hread.
           ++ rewrite Hrel_dec in Hvpost.
              cbn in Hvpost.
              destruct (decide (reg ∈ strict_regs)) as [Hstrict|Hnstrict]
                eqn:Hstrict_dec.
              ** rewrite Hstrict_dec in Hvpost.
                 cbn in Hvpost.
                 apply Exec.elem_of_bind_elim in Hvpost as
                   [pp_nts [nts [Hsetreg Hvpost]]].
                 unfold othrow in Hsetreg.
                 set (vpost :=
                   (IIS.strict iis
                    ⊔ ((TState.vcse ts ⊔ TState.vspec ts) ⊔ TState.vdsb ts)
                    : view)) in *.
                 destruct (TState.set_reg reg (val, vpost) ts)
                   as [nts0|] eqn:Hsetreg_eq.
                 --- cbn in Hsetreg.
                     apply Exec.elem_of_mret_inv in Hsetreg as
                       [-> Hsetreg].
                     inversion Hsetreg; subst nts0.
                     unfold msetv in Hvpost.
                     apply Exec.elem_of_bind_elim in Hvpost as
                       [pp_set [[] [Hset Hvpost]]].
                     apply Exec.elem_of_mSet_inv in Hset as ->.
                     apply Exec.elem_of_mret_inv in Hvpost as [-> Hvpost].
                     inversion Hvpost; subst vpost_run.
                     apply Exec.elem_of_bind_elim in Hrun as
                       [pp_vmsr [[] [Hvmsr Hrun]]].
                     apply Exec.elem_of_mset_inv in Hvmsr as ->.
                     apply Exec.elem_of_mset_inv in Hrun as ->.
                     rewrite Hrel_dec.
                     rewrite Hstrict_dec.
                     cbn.
                     rewrite !TState_promise_vcse.
                     rewrite !TState_promise_vspec.
                     rewrite !TState_promise_vdsb.
                     fold vpost.
                     rewrite (TState_set_reg_promise ev p reg
                       (val, vpost) ts nts Hsetreg_eq).
                     cbn.
                     eapply Exec.elem_of_bind_intro with
                       (st' := PPState.Make (TState_promise_event ev p nts)
                                 mem_new iis)
                       (a := vpost).
                     {
                     eapply Exec.elem_of_bind_intro with
                       (st' := PPState.Make (TState_promise_event ev p ts)
                                 mem_new iis)
                       (a := TState_promise_event ev p nts).
                     { apply Exec.elem_of_mret. }
                     cbn.
                     eapply Exec.elem_of_bind_intro with
                       (st' := PPState.Make (TState_promise_event ev p nts)
                                 mem_new iis)
                       (a := ()).
                     { change (PPState.Make (TState_promise_event ev p nts)
                                  mem_new iis)
                         with
                         (setv PPState.state (TState_promise_event ev p nts)
                            (PPState.Make (TState_promise_event ev p ts)
                               mem_new iis)).
                       apply msetv_ppstate_state_result. }
                     cbn.
                     apply Exec.elem_of_mret.
                     }
                     cbn.
                     eapply Exec.elem_of_bind_intro with
                       (st' := PPState.Make
                                 (TState.update TState.vmsr vpost
                                    (TState_promise_event ev p nts))
                                 mem_new iis)
                       (a := ()).
                     { change
                         (PPState.Make
                            (TState.update TState.vmsr vpost
                               (TState_promise_event ev p nts))
                            mem_new iis)
                         with
                         (set PPState.state
                            (TState.update TState.vmsr vpost)
                            (PPState.Make (TState_promise_event ev p nts)
                               mem_new iis)).
                       apply Exec.elem_of_mset. }
                     cbn.
                     rewrite <- TState_promise_update_vmsr.
                     change
                       (PPState.Make
                          (TState.update TState.vmsr vpost
                             (TState_promise_event ev p nts))
                          mem_new (IIS.add vpost iis))
                       with
                       (set PPState.iis (IIS.add vpost)
                          (PPState.Make
                             (TState.update TState.vmsr vpost
                                (TState_promise_event ev p nts))
                             mem_new iis)).
                     unfold elem_of, Exec.elem_of_results.
                     cbn.
                     apply elem_of_list_singleton.
                     reflexivity.
                 --- cbn in Hsetreg.
                     exfalso.
                     apply (not_elem_of_nil (pp_nts, nts)).
                     exact Hsetreg.
              ** rewrite Hstrict_dec in Hvpost.
                 cbn in Hvpost.
                 unfold elem_of, Exec.elem_of_results in Hvpost.
                 cbn in Hvpost.
                 inversion Hvpost.
        -- destruct (reg =? pc_reg) eqn:Hpc.
           ++ apply Exec.elem_of_bind_elim in Hrun as
                [pp_guard [guard_pf [Hguard Hrun]]].
              apply Exec.elem_of_guard_discard_inv in Hguard as ->.
              apply Exec.elem_of_bind_elim in Hrun as
                [pp_vspec [[] [Hvspec Hrun]]].
              apply Exec.elem_of_mset_inv in Hvspec as ->.
              apply Exec.elem_of_bind_elim in Hrun as
                [pp_ts2 [ts2 [Hts2 Hrun]]].
              apply Exec.elem_of_mget_inv in Hts2 as [-> ->].
              apply Exec.elem_of_bind_elim in Hrun as
                [pp_nts [nts [Hsetreg Hrun]]].
              unfold othrow in Hsetreg.
              destruct (TState.set_reg reg (val, 0%nat)
                (TState.update TState.vspec (IIS.strict iis) ts))
                as [nts0|] eqn:Hsetreg_eq.
              ** cbn in Hsetreg.
                 rewrite Hsetreg_eq in Hsetreg.
                 cbn in Hsetreg.
                 apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
                 inversion Hsetreg; subst nts0.
	                 unfold msetv in Hrun.
	                 apply Exec.elem_of_mSet_inv in Hrun as ->.
	                 cbn.
	                 destruct (@Exec.elem_of_guard_discard
	                   (PPState.t TState.t Ev.t IIS.t) string
	                   (TState.no_promises_until (IIS.strict iis)
                      (TState_promise_event ev p ts))
                   (TState.Decision_no_promises_until (IIS.strict iis)
                      (TState_promise_event ev p ts))
		                   (PPState.Make (TState_promise_event ev p ts) mem_new iis))
		                   as [guard_pf' Hguard'].
		                 { apply TState_no_promises_until_promise_event; [exact guard_pf|].
		                   eapply Nat.le_lt_trans; [exact Hstrict_le|exact Hmem_lt]. }
                 eapply Exec.elem_of_bind_intro with
                   (e := guard_discard
                           (TState.no_promises_until (IIS.strict iis)
                              (TState_promise_event ev p ts)))
                   (st' := PPState.Make (TState_promise_event ev p ts)
                             mem_new iis)
                   (a := guard_pf').
                 { exact Hguard'. }
                 cbn.
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState.update TState.vspec (IIS.strict iis)
                                (TState_promise_event ev p ts))
                             mem_new iis)
                   (a := ()).
                 { change
                     (PPState.Make
                        (TState.update TState.vspec (IIS.strict iis)
                           (TState_promise_event ev p ts))
                        mem_new iis)
                     with
                     (set PPState.state
                        (TState.update TState.vspec (IIS.strict iis))
                        (PPState.Make (TState_promise_event ev p ts)
                           mem_new iis)).
                   apply Exec.elem_of_mset. }
                 cbn.
                 rewrite TState_promise_update_vspec.
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState_promise_event ev p
                                (TState.update TState.vspec
                                   (IIS.strict iis) ts))
                             mem_new iis)
                   (a := TState_promise_event ev p
                           (TState.update TState.vspec (IIS.strict iis) ts)).
                 { apply (Exec.elem_of_mget (E:=string)
                     (PPState.Make
                        (TState_promise_event ev p
                           (TState.update TState.vspec (IIS.strict iis) ts))
                        mem_new iis) PPState.state). }
                 cbn.
                 rewrite (TState_set_reg_promise ev p reg
                   (val, 0%nat)
                   (TState.update TState.vspec (IIS.strict iis) ts)
                   nts Hsetreg_eq).
                 cbn.
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState_promise_event ev p
                                (TState.update TState.vspec
                                   (IIS.strict iis) ts))
                             mem_new iis)
                   (a := TState_promise_event ev p nts).
                 { apply Exec.elem_of_mret. }
                 cbn.
                 change (PPState.Make (TState_promise_event ev p nts)
                           mem_new iis)
                   with
                   (setv PPState.state (TState_promise_event ev p nts)
                      (PPState.Make
                         (TState_promise_event ev p
                            (TState.update TState.vspec
                               (IIS.strict iis) ts))
                         mem_new iis)).
                 apply msetv_ppstate_state_result.
              ** rewrite Hsetreg_eq in Hsetreg.
                 cbn in Hsetreg.
                 exfalso.
                 apply (not_elem_of_nil (pp_nts, nts)).
                 exact Hsetreg.
           ++ cbn in Hrun.
              destruct (decide (reg ∈ strict_regs)) as [Hstrict|Hnstrict]
                eqn:Hstrict_dec.
              ** rewrite Hstrict_dec in Hrun.
                 cbn in Hrun.
                 apply Exec.elem_of_bind_elim in Hrun as
                   [pp_nts [nts [Hsetreg Hrun]]].
                 unfold othrow in Hsetreg.
                 destruct
	                   (TState.set_reg reg (val, IIS.strict iis) ts)
	                   as [nts0|] eqn:Hsetreg_eq.
	                 --- cbn in Hsetreg.
	                     apply Exec.elem_of_mret_inv in Hsetreg as
	                       [-> Hsetreg].
	                     inversion Hsetreg; subst nts0.
	                     unfold msetv in Hrun.
	                     apply Exec.elem_of_mSet_inv in Hrun as ->.
	                     rewrite Hstrict_dec.
                     cbn.
                     rewrite (TState_set_reg_promise ev p reg
                       (val, IIS.strict iis) ts nts Hsetreg_eq).
                     cbn.
                     eapply Exec.elem_of_bind_intro with
                       (st' := PPState.Make (TState_promise_event ev p ts)
                                 mem_new iis)
                       (a := TState_promise_event ev p nts).
                     { apply Exec.elem_of_mret. }
                     cbn.
                     change (PPState.Make (TState_promise_event ev p nts)
                               mem_new iis)
                       with
                       (setv PPState.state (TState_promise_event ev p nts)
                          (PPState.Make (TState_promise_event ev p ts)
                             mem_new iis)).
                     apply msetv_ppstate_state_result.
                 --- cbn in Hsetreg.
                     exfalso.
                     apply (not_elem_of_nil (pp_nts, nts)).
                     exact Hsetreg.
              ** rewrite Hstrict_dec in Hrun.
                 cbn in Hrun.
                 unfold elem_of, Exec.elem_of_results in Hrun.
                 cbn in Hrun.
                 inversion Hrun.
Qed.

Lemma run_reg_write_preserves_mem reg racc val ppst ppst' u :
  Exec.elem_of_results (ppst', u) (run_reg_write reg racc val ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro Hrun.
  destruct ppst as [ts mem iis].
  unfold run_reg_write in Hrun.
  cbn in *.
  repeat match goal with
  | x : unit |- _ => destruct x
  | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  | H : None = Some _ |- _ => inversion H
  | H : Some _ = None |- _ => inversion H
  | H : Exec.elem_of_results _ ((guard_discard _) _) |- _ =>
      apply Exec.elem_of_guard_discard_inv in H as ->
  | H : Exec.elem_of_results _ ((guard_or _ _) _) |- _ =>
      apply Exec.elem_of_guard_or_inv in H as ->
  | H : Exec.elem_of_results _ ((_ ≫= _) _) |- _ =>
      apply Exec.elem_of_bind_elim in H as [? [? [? H]]]
  | H : Exec.elem_of_results _ ((mget _) _) |- _ =>
      apply Exec.elem_of_mget_inv in H as [-> ->]
  | H : Exec.elem_of_results _ ((mret _) _) |- _ =>
      apply Exec.elem_of_mret_inv in H as [-> ?]
  | H : Exec.elem_of_results _ ((msetv _ _) _) |- _ =>
      unfold msetv in H
  | H : Exec.elem_of_results _ ((mset _ _) _) |- _ =>
      apply Exec.elem_of_mset_inv in H as ->
  | H : Exec.elem_of_results _ ((mSet _) _) |- _ =>
      apply Exec.elem_of_mSet_inv in H as ->
  | H : Exec.elem_of_results _ ((mthrow _) _) |- _ =>
      unfold mthrow, Exec.throw_inst, elem_of, Exec.elem_of_results in H;
      cbn in H; apply not_elem_of_nil in H; contradiction
  | H : Exec.elem_of_results _ ((othrow _ _) _) |- _ =>
      unfold othrow in H; cbn in H
  | H : Exec.elem_of_results _ {| Exec.results := [(_, _)]; Exec.errors := [] |} |- _ =>
      unfold elem_of, Exec.elem_of_results in H;
      cbn in H;
      apply elem_of_list_singleton in H;
      inversion H; subst; clear H
  | H : context[let '(_, _) := ?p in _] |- _ =>
      destruct p
  | H : context[match ?o with Some _ => _ | None => _ end] |- _ =>
      destruct o eqn:?
  | H : context[if ?b then _ else _] |- _ =>
      destruct b eqn:?
  | |- _ => cbn
  end;
  reflexivity.
Qed.

Definition outcome_future_promise_stable_promised (bbm_param : BBM.param)
    n_threads tid initmem (ev : Ev.t) (out : outcome) : Prop :=
  ∀ ppst ppst' (eret : eff_ret out),
    Exec.elem_of_results (ppst', eret)
      ((run_outcome n_threads tid initmem out |$> fst) ppst) →
    Exec.elem_of_results
      (VMPromising_promise_ppstate bbm_param
         tid initmem ev ppst', eret)
      ((run_outcome n_threads tid initmem out |$> fst)
         (VMPromising_promise_ppstate bbm_param
            tid initmem ev ppst)).

Definition run_trans_start_future_promise_stable
    (bbm_param : BBM.param) tid initmem (ev : Ev.t)
    (trans_start : TranslationStartInfo) : Prop :=
  ∀ ppst ppst',
    Exec.elem_of_results (ppst', ())
      (run_trans_start trans_start tid
         (initmem) ppst) →
    Exec.elem_of_results
      (VMPromising_promise_ppstate bbm_param
         tid initmem ev ppst', ())
      (run_trans_start trans_start tid
         (initmem)
         (VMPromising_promise_ppstate bbm_param
            tid initmem ev ppst)).

Fixpoint imon_future_promise_stable_promised (bbm_param : BBM.param)
    n_threads tid initmem (ev : Ev.t) A (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next call k =>
      match call with
      | inl out =>
          outcome_future_promise_stable_promised
            bbm_param n_threads tid initmem ev out ∧
          ∀ eret,
            imon_future_promise_stable_promised
              bbm_param n_threads tid initmem ev A (k eret)
      | inr _ =>
          ∀ ret,
            imon_future_promise_stable_promised
              bbm_param n_threads tid initmem ev A (k ret)
      end
  end.

Lemma reg_read_outcome_promise_state_fmap (ev : Ev.t) n_threads tid initmem reg racc
    ppst ppst' p mem_new eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome n_threads tid initmem (RegRead reg racc) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome n_threads tid initmem (RegRead reg racc) |$> fst)
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
         (run_outcome n_threads tid initmem (RegRead reg racc)
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
    (bbm_param : BBM.param) n_threads tid initmem ev reg racc :
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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

Lemma reg_write_outcome_promise_state_fmap (ev : Ev.t) n_threads tid initmem reg racc val
    ppst ppst' p mem_new eret :
  (length (PPState.mem ppst) <= length mem_new)%nat →
  (length (PPState.mem ppst) < p)%nat →
  (IIS.strict (PPState.iis ppst) <= length (PPState.mem ppst))%nat →
  Exec.elem_of_results (ppst', eret)
    ((run_outcome n_threads tid initmem (RegWrite reg racc val) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome n_threads tid initmem (RegWrite reg racc val) |$> fst)
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intros Hmem_le Hmem_lt Hstrict_le Hrun.
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
         (run_outcome n_threads tid initmem (RegWrite reg racc val)
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
	      * exact Hmem_le.
	      * exact Hmem_lt.
	      * exact Hstrict_le.
	      * exact Hwrite.
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
    (bbm_param : BBM.param) n_threads tid initmem ev reg racc val :
  (∀ ppst, ppstate_control_times_le ppst) →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
    (RegWrite reg racc val).
Proof.
  intro Hcontrol.
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
	  eapply (reg_write_outcome_promise_state_fmap
	    ev n_threads tid initmem reg racc val).
	  - cbn. lia.
	  - cbn. lia.
	  - destruct (Hcontrol ppst) as [Hstrict_le _].
	    exact Hstrict_le.
	  - exact Hrun.
Qed.

Lemma mem_read_ifetch_outcome_promise_state_fmap (ev : Ev.t) n_threads tid initmem addr macc
    addr_space ppst ppst' p eret :
  is_ifetch macc = true →
  Exec.elem_of_results (ppst', eret)
    ((run_outcome n_threads tid initmem (MemRead (MemReq.make macc addr addr_space 4 0))
        |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       (PPState.mem ppst') (PPState.iis ppst'), eret)
    ((run_outcome n_threads tid initmem (MemRead (MemReq.make macc addr addr_space 4 0))
        |$> fst)
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          (PPState.mem ppst) (PPState.iis ppst))).
Proof.
  intros Hifetch Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [p_nss [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hnss.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  subst addr_space.
  cbn in Hrun.
  rewrite Hifetch in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_size [p_size [Hsize Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hsize) as Hsize_eq.
  apply Exec.elem_of_guard_or_inv in Hsize as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_mem [mem0 [Hmem Hrun]]].
  apply Exec.elem_of_mget_inv in Hmem as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_opcode [opcode [Hopcode Hrun]]].
  apply Exec.elem_of_lift_res_inv in Hopcode as [-> Hopcode].
  apply Exec.elem_of_mret_inv in Hrun as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  destruct ppst as [ts mem iis].
  cbn in *.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev p ts) mem iis,
          (eret0, vpre_opt))
         (run_outcome n_threads tid initmem
            (MemRead (MemReq.make macc addr PAS_NonSecure 4 0))
            (PPState.Make (TState_promise_event ev p ts) mem iis))).
  {
    simp run_outcome.
    rewrite Hifetch.
    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
      (P:=PAS_NonSecure = PAS_NonSecure)
      (PPState.Make (TState_promise_event ev p ts) mem iis)
      "Access outside Non-Secure" eq_refl) as [p_nss' Hguard'].
    eapply Exec.elem_of_bind_intro with
      (e := guard_or "Access outside Non-Secure"
              (PAS_NonSecure = PAS_NonSecure))
      (st' := PPState.Make (TState_promise_event ev p ts) mem iis)
      (a := p_nss').
    - exact Hguard'.
    - cbn.
      destruct (Exec.elem_of_guard_or
        (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
        (P:=(4 = 4)%N)
        (PPState.Make (TState_promise_event ev p ts) mem iis)
        "Ifetch read of size other than 4" eq_refl) as [p_size' Hsize'].
      eapply Exec.elem_of_bind_intro with
        (e := guard_or "Ifetch read of size other than 4" (4 = 4)%N)
        (st' := PPState.Make (TState_promise_event ev p ts) mem iis)
        (a := p_size').
      + exact Hsize'.
      + cbn.
        eapply Exec.elem_of_bind_intro with
          (e := (mget PPState.mem :
                   Exec.t (PPState.t TState.t Ev.t IIS.t) string Memory.t))
          (st' := PPState.Make (TState_promise_event ev p ts) mem iis)
          (a := mem).
        * apply (Exec.elem_of_mget (E:=string)
            (PPState.Make (TState_promise_event ev p ts) mem iis)
            PPState.mem).
        * cbn.
          eapply Exec.elem_of_bind_intro with
            (e := mlift (read_imem addr initmem mem))
            (st' := PPState.Make (TState_promise_event ev p ts) mem iis)
            (a := opcode).
          -- apply Exec.elem_of_lift_res.
             exact Hopcode.
	          -- cbn.
	             rewrite (proof_irrelevance _ p_size' p_size).
	             rewrite Hret.
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
    (bbm_param : BBM.param) n_threads tid initmem code ev addr macc addr_space :
  is_ifetch macc = true →
  event_misses_code code ev →
  ifetch_in_code code addr 4 →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
    (MemRead (MemReq.make macc addr addr_space 4 0)).
Proof.
  intros Hifetch Hmiss Hcode ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_guard [p_nss [Hguard Hraw]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hnss.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  subst addr_space.
  cbn in Hraw.
  rewrite Hifetch in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_size [p_size [Hsize Hraw]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hsize) as Hsize_eq.
  apply Exec.elem_of_guard_or_inv in Hsize as ->.
  cbn in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_mem [mem0 [Hmem_get Hraw]]].
  apply Exec.elem_of_mget_inv in Hmem_get as [-> ->].
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_opcode [opcode [Hopcode Hraw]]].
  apply Exec.elem_of_lift_res_inv in Hopcode as [-> Hopcode].
  apply Exec.elem_of_mret_inv in Hraw as [Heq_ret Hret].
  inversion Heq_ret; subst ppst'.
  destruct ppst as [ts mem iis].
  cbn in *.
  unfold VMPromising_promise_ppstate, VMPromising.
  cbn.
  set (p := length (ev :: mem)).
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make (TState_promise_event ev p ts) (ev :: mem) iis,
          (eret0, vpre_opt))
         (run_outcome n_threads tid initmem
            (MemRead (MemReq.make macc addr PAS_NonSecure 4 0))
            (PPState.Make (TState_promise_event ev p ts)
               (ev :: mem) iis))).
  {
    simp run_outcome.
    rewrite Hifetch.
    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
      (P:=PAS_NonSecure = PAS_NonSecure)
      (PPState.Make (TState_promise_event ev p ts) (ev :: mem) iis)
      "Access outside Non-Secure" eq_refl) as [p_nss' Hguard'].
    eapply Exec.elem_of_bind_intro with
      (e := guard_or "Access outside Non-Secure"
              (PAS_NonSecure = PAS_NonSecure))
      (st' := PPState.Make (TState_promise_event ev p ts)
                (ev :: mem) iis)
      (a := p_nss').
    - exact Hguard'.
    - cbn.
      destruct (Exec.elem_of_guard_or
        (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
        (P:=(4 = 4)%N)
        (PPState.Make (TState_promise_event ev p ts) (ev :: mem) iis)
        "Ifetch read of size other than 4" eq_refl) as [p_size' Hsize'].
      eapply Exec.elem_of_bind_intro with
        (e := guard_or "Ifetch read of size other than 4" (4 = 4)%N)
        (st' := PPState.Make (TState_promise_event ev p ts)
                  (ev :: mem) iis)
        (a := p_size').
      + exact Hsize'.
      + cbn.
        eapply Exec.elem_of_bind_intro with
          (e := (mget PPState.mem :
                   Exec.t (PPState.t TState.t Ev.t IIS.t) string Memory.t))
          (st' := PPState.Make (TState_promise_event ev p ts)
                    (ev :: mem) iis)
          (a := ev :: mem).
        * apply (Exec.elem_of_mget (E:=string)
            (PPState.Make (TState_promise_event ev p ts)
               (ev :: mem) iis) PPState.mem).
        * cbn.
          eapply Exec.elem_of_bind_intro with
            (e := mlift (read_imem addr initmem (ev :: mem)))
            (st' := PPState.Make (TState_promise_event ev p ts)
                      (ev :: mem) iis)
            (a := opcode).
          -- apply Exec.elem_of_lift_res.
             rewrite (read_imem_cons_misses_code code addr initmem mem ev
               Hmiss Hcode).
             exact Hopcode.
          -- cbn.
             rewrite (proof_irrelevance _ p_size' p_size).
             rewrite Hret.
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

Lemma return_exception_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) n_threads tid initmem ev :
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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
         (run_outcome n_threads tid initmem ReturnException
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
	          ev (length (ev :: mem)) (length mem)).
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

Lemma take_exception_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) n_threads tid initmem ev fault :
  (∀ ppst, ppstate_control_times_le ppst) →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
    (TakeException fault).
Proof.
  intros Hcontrol ppst ppst' eret Hrun.
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
         (run_outcome n_threads tid initmem (TakeException fault)
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
        unfold run_take_exception in Hcse |- *.
        cbn in Hcse |- *.
        apply Exec.elem_of_bind_elim in Hcse as
          [stiis_iis [iis0 [Hget_iis Hcse]]].
        apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
        eapply Exec.elem_of_bind_intro with
          (st' := (TState_promise_event ev (length (ev :: mem)) ts, iis))
          (a := iis).
        { apply (Exec.elem_of_mget (E:=string)
            (TState_promise_event ev (length (ev :: mem)) ts, iis) snd). }
        cbn.
        cbn in Hcse.
        destruct (IIS.inv_time iis) as [inv_time|] eqn:Hinv_time.
        * eapply (run_cse_promise_state ev (length (ev :: mem)) inv_time).
          -- cbn.
             eapply Nat.le_lt_trans.
             ++ eapply ppstate_control_inv_time_le.
                ** apply (Hcontrol (PPState.Make ts mem iis)).
                ** exact Hinv_time.
             ++ cbn.
                lia.
          -- exact Hcse.
        * eapply (run_cse_future_promise_state
            ev (length (ev :: mem)) (length mem)).
          -- cbn.
             lia.
          -- exact Hcse.
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
    (bbm_param : BBM.param) n_threads tid initmem ev :
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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
         (run_outcome n_threads tid initmem (Barrier (Barrier_ISB ()))
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
	            ev (length (ev :: mem)) (length mem)).
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

(*
Lemma barrier_dmb_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) n_threads tid initmem ev dmb :
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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
         (run_outcome n_threads tid initmem (Barrier (Barrier_DMB dmb))
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
	        eapply (run_barrier_dmb_promise_state
	          ev (length (ev :: mem)) (length mem)).
        * cbn. lia.
        * exact Hbarrier.
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
    (bbm_param : BBM.param) n_threads tid initmem ev dsb :
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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
         (run_outcome n_threads tid initmem (Barrier (Barrier_DSB dsb))
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
	        eapply (run_barrier_dsb_promise_state
	          ev (length (ev :: mem)) (length mem)).
        * cbn. lia.
        * exact Hbarrier.
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

*)

Lemma translation_start_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) n_threads tid initmem ev trans_start :
  run_trans_start_future_promise_stable
    bbm_param tid initmem ev trans_start →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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
         (run_outcome n_threads tid initmem (TranslationStart trans_start)
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
    (bbm_param : BBM.param) n_threads tid initmem ev trans_end :
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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
         (run_outcome n_threads tid initmem (TranslationEnd trans_end)
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

Lemma mem_write_addr_announce_outcome_promise_state_fmap (ev : Ev.t) n_threads
    tid initmem req ppst ppst' p mem_new eret :
  (IIS.strict (PPState.iis ppst) <= length mem_new)%nat →
  (IIS.strict (PPState.iis ppst) < p)%nat →
  Exec.elem_of_results (ppst', eret)
    ((run_outcome n_threads tid initmem (MemWriteAddrAnnounce req) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState_promise_event ev p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome n_threads tid initmem (MemWriteAddrAnnounce req) |$> fst)
       (PPState.Make (TState_promise_event ev p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intros Hmem_new_bound Hvaddr_lt Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vaddr [vaddr [Hvaddr Hrun]]].
  apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts [Hts Hrun]]].
  apply Exec.elem_of_mget_inv in Hts as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [Hno_write [Hguard Hrun]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  cbn in Hrun.
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
         (run_outcome n_threads tid initmem (MemWriteAddrAnnounce req)
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
	            (e := (mget PPState.state :
	                     Exec.t (PPState.t TState.t Ev.t IIS.t) string TState.t))
	            (st' := PPState.Make
	                      (TState_promise_event ev p (PPState.state ppst))
	                      mem_new (PPState.iis ppst))
	            (a := TState_promise_event ev p (PPState.state ppst)).
	      + apply (Exec.elem_of_mget (E:=string)
	              (PPState.Make
	                 (TState_promise_event ev p (PPState.state ppst))
	                 mem_new (PPState.iis ppst)) PPState.state).
	      + cbn.
	             destruct (Exec.elem_of_guard_discard
	               (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
	               (P:=TState.no_write_promises_until
                     (IIS.strict (PPState.iis ppst))
                     (TState_promise_event ev p (PPState.state ppst)))
               (PPState.Make
                  (TState_promise_event ev p (PPState.state ppst))
                  mem_new (PPState.iis ppst)))
	               as [Hno_write' Hguard'].
	             { apply TState_no_write_promises_until_promise_event;
	                 [exact Hno_write|exact Hvaddr_lt]. }
	             eapply Exec.elem_of_bind_intro with
               (e := guard_discard
                       (TState.no_write_promises_until
                          (IIS.strict (PPState.iis ppst))
                          (TState_promise_event ev p
                             (PPState.state ppst))))
	               (st' := PPState.Make
	                         (TState_promise_event ev p (PPState.state ppst))
	                         mem_new (PPState.iis ppst))
	               (a := Hno_write').
	             * exact Hguard'.
	             * cbn.
	                eapply Exec.elem_of_bind_intro with
	                  (st' := PPState.Make
	                            (TState.update TState.vspec
                               (IIS.strict (PPState.iis ppst))
                               (TState_promise_event ev p
                                  (PPState.state ppst)))
                            mem_new (PPState.iis ppst))
                  (a := ()).
                { change
                    (PPState.Make
                       (TState.update TState.vspec
                          (IIS.strict (PPState.iis ppst))
                          (TState_promise_event ev p
                             (PPState.state ppst)))
                       mem_new (PPState.iis ppst))
                    with
                    (set PPState.state
                       (TState.update TState.vspec
                          (IIS.strict (PPState.iis ppst)))
                       (PPState.Make
                          (TState_promise_event ev p (PPState.state ppst))
                          mem_new (PPState.iis ppst))).
	                  apply Exec.elem_of_mset. }
	                { cbn.
	                  apply Exec.elem_of_mret. }
	  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - reflexivity.
Qed.

Lemma mem_write_addr_announce_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) n_threads tid initmem ev req :
  (∀ ppst, ppstate_control_times_le ppst) →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
    (MemWriteAddrAnnounce req).
Proof.
  intro Hcontrol.
  intros ppst ppst' eret Hrun.
  assert
    (Hmem : PPState.mem ppst' = PPState.mem ppst).
	  {
	    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
	    simp run_outcome in Hraw.
	    apply Exec.elem_of_bind_elim in Hraw as
	      [pp_vaddr [vaddr [Hvaddr Hraw]]].
	    apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
	    cbn in Hraw.
	    apply Exec.elem_of_bind_elim in Hraw as
	      [pp_ts [ts [Hts Hraw]]].
    apply Exec.elem_of_mget_inv in Hts as [-> ->].
    cbn in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_guard [Hno_write [Hguard Hraw]]].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    cbn in Hraw.
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
	  - destruct (Hcontrol ppst) as [Hstrict_le _].
	    cbn.
	    lia.
	  - destruct (Hcontrol ppst) as [Hstrict_le _].
	    cbn.
	    lia.
	  - exact Hrun.
Qed.

Lemma generic_fail_outcome_future_promise_stable_promised
    (bbm_param : BBM.param) n_threads tid initmem ev s :
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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
    (bbm_param : BBM.param) n_threads tid initmem ev cop :
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
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
    bbm_param n (tid : nat) initmem ev A mon →
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
    bbm_param n (tid : nat) initmem ev () isem →
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
    bbm_param n (tid : nat) initmem ev () isem →
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
          bbm_param n (tid : nat) initmem ev () isem;
  }.

Fixpoint VMPromising_Sail_promised_stable (bbm_param : BBM.param)
    n_threads tid initmem ev nondet {A eo} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      imon_future_promise_stable_promised
        bbm_param n_threads tid initmem ev _ (Sail_outcome_interp nondet out) ∧
      ∀ ret,
        VMPromising_Sail_promised_stable
          bbm_param n_threads tid initmem ev nondet (k ret)
  end.

Lemma VMPromising_imon_promised_stable_bind
    (bbm_param : BBM.param) n_threads tid initmem ev
    {A B} (mon : iMon A) (k : A → iMon B) :
  imon_future_promise_stable_promised
    bbm_param n_threads tid initmem ev A mon →
  (∀ a,
    imon_future_promise_stable_promised
      bbm_param n_threads tid initmem ev B (k a)) →
  imon_future_promise_stable_promised
    bbm_param n_threads tid initmem ev B (a ← mon; k a).
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet
    {A eo} (smon : SI.iMon eo A) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet smon →
  imon_future_promise_stable_promised
    bbm_param n_threads tid initmem ev A (iMon_from_Sail nondet smon).
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
          bbm_param n (tid : nat) initmem ev nondet smon;
  }.

Record VMPromising_Sail_same_promise_stable (bbm_param : BBM.param)
    {n eo} nondet (smon : SI.iMon eo ()) : Prop := {
    VMPromising_Sail_same_promised_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (ev : Ev.t),
        VMPromising_Sail_promised_stable
          bbm_param n (tid : nat) initmem ev nondet smon;
  }.

Record VMPromising_read_code_translation_stability
    (bbm_param : BBM.param) (n_threads tid : nat)
    (initmem : memoryMap) (code : code_region) (ev : Ev.t) : Prop := {
    VMPromising_read_code_ifetch_stable :
      ∀ (addr : address) (macc : mem_acc)
          (addr_space : addr_space),
        event_misses_code code ev ∧ ifetch_in_code code addr 4;
    VMPromising_read_code_data_read_stable :
      ∀ (addr : address) (macc : mem_acc)
          (addr_space : addr_space) size,
        outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
          (MemRead (MemReq.make macc addr addr_space size 0));
    VMPromising_read_code_translation_start_stable :
      ∀ trans_start,
        run_trans_start_future_promise_stable
          bbm_param tid initmem ev trans_start;
    VMPromising_read_code_tlbop_stable :
      ∀ tlbi,
        outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
          (TlbOp tlbi);
    VMPromising_read_code_control_bound :
      ∀ (ppst : PPState.t TState.t Ev.t IIS.t),
        ppstate_control_times_le ppst;
  }.

Lemma VMPromising_mem_read_ifetch_promised_stable_from_read_code_translation
    bbm_param n_threads tid initmem code ev addr macc addr_space :
  is_ifetch macc = true →
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
    (MemRead (MemReq.make macc addr addr_space 4 0)).
Proof.
  intros Hmacc Hstable.
  destruct Hstable as [Hifetch _ _ _ _].
  destruct (Hifetch addr macc addr_space) as [Hmiss Hin].
  eapply mem_read_ifetch_outcome_future_promise_stable_promised.
  - exact Hmacc.
  - exact Hmiss.
  - exact Hin.
Qed.

Lemma VMPromising_mem_read_data_promised_stable_from_read_code_translation
    bbm_param n_threads tid initmem code ev addr macc addr_space size :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
    (MemRead (MemReq.make macc addr addr_space size 0)).
Proof.
  intro Hstable.
  destruct Hstable as [_ Hread _ _ _].
  apply Hread.
Qed.

Lemma VMPromising_translation_start_promised_stable_from_read_code_translation
    bbm_param n_threads tid initmem code ev trans_start :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
    (TranslationStart trans_start).
Proof.
  intro Hstable.
  destruct Hstable as [_ _ Htrans _ _].
  apply translation_start_outcome_future_promise_stable_promised.
  apply Htrans.
Qed.

Lemma VMPromising_tlbop_promised_stable_from_read_code_translation
    bbm_param n_threads tid initmem code ev tlbi :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  outcome_future_promise_stable_promised bbm_param n_threads tid initmem ev
    (TlbOp tlbi).
Proof.
  intro Hstable.
  destruct Hstable as [_ _ _ Htlb _].
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

#[local] Typeclasses Transparent othrow.
#[local] Instance exec_unfold : Exec.Unfold := {}.

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
  | H : Exec.elem_of_results _ ((_ <$> _) _) |- _ =>
      apply Exec.elem_of_fmap_inv in H as [? [-> H]]
  | H : Exec.elem_of_results _
          {| Exec.results := [(_, _)]; Exec.errors := [] |} |- _ =>
      unfold elem_of, Exec.elem_of_results in H; cbn in H;
      apply elem_of_list_singleton in H; inversion H; subst; clear H
  | H : Exec.elem_of_results _ ((update_tcoh_for_access _ _ _) _) |- _ =>
      unfold update_tcoh_for_access in H
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

Lemma elem_of_unfolded_ppstate_mset_state st mem iis upd :
  Exec.elem_of_results (PPState.Make (upd st) mem iis, ())
    ((((λ s : PPState.t TState.t Ev.t IIS.t,
          {| Exec.results := [(s, s)]; Exec.errors := [] |})
        : Exec.t (PPState.t TState.t Ev.t IIS.t) string
            (PPState.t TState.t Ev.t IIS.t))
      ≫= λ s : PPState.t TState.t Ev.t IIS.t,
            ((λ _ : PPState.t TState.t Ev.t IIS.t,
                {| Exec.results := [(set PPState.state upd s, ())];
                   Exec.errors := [] |})
             : Exec.t (PPState.t TState.t Ev.t IIS.t) string unit))
       (PPState.Make st mem iis)).
Proof.
  change (PPState.Make (upd st) mem iis)
    with (set PPState.state upd (PPState.Make st mem iis)).
  apply Exec.elem_of_unfolded_mset.
Qed.

Lemma elem_of_unfolded_ppstate_mset_iis st mem iis upd :
  Exec.elem_of_results (PPState.Make st mem (upd iis), ())
    ((((λ s : PPState.t TState.t Ev.t IIS.t,
          {| Exec.results := [(s, s)]; Exec.errors := [] |})
        : Exec.t (PPState.t TState.t Ev.t IIS.t) string
            (PPState.t TState.t Ev.t IIS.t))
      ≫= λ s : PPState.t TState.t Ev.t IIS.t,
            ((λ _ : PPState.t TState.t Ev.t IIS.t,
                {| Exec.results := [(set PPState.iis upd s, ())];
                   Exec.errors := [] |})
             : Exec.t (PPState.t TState.t Ev.t IIS.t) string unit))
       (PPState.Make st mem iis)).
Proof.
  change (PPState.Make st mem (upd iis))
    with (set PPState.iis upd (PPState.Make st mem iis)).
  apply Exec.elem_of_unfolded_mset.
Qed.

Lemma elem_of_guard_discard_proof {St E P} `{Decision P} st (p : P) :
  Exec.elem_of_results (st, p) ((guard_discard P : Exec.t St E P) st).
Proof.
  unfold guard_discard.
  destruct (decide P) as [p'|Hnp].
  - replace p with p' by apply proof_irrelevance.
    apply Exec.elem_of_mret.
  - contradiction.
Qed.

Lemma memory_fulfill_none_no_match
    (ev : Ev.t) (prom : list view) (mem : Memory.t) (t : view) :
  Memory.fulfill ev prom mem = None →
  t ∈ prom →
  (mem : PromMemory.t Ev.t) !! (t : nat) ≠ Some ev.
Proof.
  unfold Memory.fulfill.
  rewrite list_basics.head_reverse.
  intro Hfulfill.
  apply list_basics.last_None in Hfulfill.
  intros Hprom Hlookup.
  pose proof (list_basics.filter_nil_not_elem_of
    (λ t, (mem : PromMemory.t Ev.t) !! (t : nat) = Some ev)
    prom t Hfulfill Hlookup) as Hnot.
  exact (Hnot Hprom).
Qed.

Lemma last_cons_all_eq {A} (x : A) (l : list A) :
  (∀ y, y ∈ l → y = x) →
  list_basics.last (x :: l) = Some x.
Proof.
  induction l as [|a l IH]; intro Hall.
  - reflexivity.
  - rewrite list_basics.last_cons_cons.
    assert (a = x) by (apply Hall; left; reflexivity).
    subst a.
    apply IH.
    intros y Hy.
    apply Hall.
    right.
    exact Hy.
Qed.

Lemma last_Some_elem {A} (x : A) (l : list A) :
  list_basics.last l = Some x →
  x ∈ l.
Proof.
  induction l as [|a l IH]; cbn.
  - discriminate.
  - destruct l as [|b l].
    + cbn.
      intro H.
      inversion H; subst.
      apply elem_of_list_singleton.
      reflexivity.
    + rewrite list_basics.last_cons_cons.
      intro H.
      apply elem_of_cons.
      right.
      apply IH.
      exact H.
Qed.

Lemma memory_fulfill_some_lookup
    (ev : Ev.t) (prom : list view) (mem : Memory.t) time :
  Memory.fulfill ev prom mem = Some time →
  (mem : PromMemory.t Ev.t) !! (time : nat) = Some ev.
Proof.
  unfold Memory.fulfill.
  rewrite list_basics.head_reverse.
  intro Hfulfill.
  pose proof (last_Some_elem time _ Hfulfill) as Hin.
  rewrite list_basics.elem_of_list_filter in Hin.
  destruct Hin as [Hlookup _].
  exact Hlookup.
Qed.

Lemma memory_fulfill_after_promise
    (ev : Ev.t) (prom : list view) (mem : Memory.t) :
  Memory.fulfill ev prom mem = None →
  Memory.fulfill ev (length (ev :: mem) :: prom) (ev :: mem) =
  Some (length (ev :: mem)).
Proof.
  intro Hfulfill.
  set (time := length (ev :: mem)).
  assert (Hno_match :
    ∀ t : view, t ∈ prom →
      (mem : PromMemory.t Ev.t) !! (t : nat) ≠ Some ev).
  { intros t Hprom.
    eapply memory_fulfill_none_no_match; eauto. }
  unfold Memory.fulfill.
  rewrite list_basics.head_reverse.
  rewrite list_basics.filter_cons_True.
  - apply last_cons_all_eq.
    intros t Hmatch.
    rewrite list_basics.elem_of_list_filter in Hmatch.
    destruct Hmatch as [Hlookup Hprom].
    apply PromMemory.lookup_cons_inv_same in Hlookup as [Hold_lookup|Htime].
    + exfalso.
      eapply Hno_match; eauto.
    + exact Htime.
  - subst time.
    apply PromMemory.lookup_latest.
Qed.

Lemma prommemory_lookup_some_le (ev : Ev.t) (mem : Memory.t) t :
  (mem : PromMemory.t Ev.t) !! t = Some ev →
  (t ≤ length mem)%nat.
Proof.
  intro Hlookup.
  unfold lookup, PromMemory.lookup_inst in Hlookup.
  repeat match type of Hlookup with
  | context[if ?b then _ else _] => destruct b eqn:? in Hlookup
  end; try discriminate Hlookup.
  match goal with
  | Hle : (t <=? length mem)%nat = true |- _ =>
      apply Nat.leb_le in Hle;
      exact Hle
  end.
Qed.

Lemma prommemory_lookup_cons_ne (ev ev' : Ev.t) (mem : Memory.t) t :
  ev' ≠ ev →
  ((ev' :: mem : Memory.t) !! t = Some ev ↔
   (mem : Memory.t) !! t = Some ev).
Proof.
  intro Hne.
  split.
  - intro Hlookup.
    destruct t as [|t].
    + unfold lookup, PromMemory.lookup_inst in Hlookup.
      cbn in Hlookup.
      discriminate Hlookup.
    + unfold lookup, PromMemory.lookup_inst in Hlookup |- *.
      cbn [length] in Hlookup.
      destruct (S t =? 0)%nat eqn:Hzero; [discriminate|].
      destruct (S t <=? S (length mem))%nat eqn:Hnew;
        [|discriminate].
      apply Nat.leb_le in Hnew.
      destruct (S t <=? length mem)%nat eqn:Hold.
      * apply Nat.leb_le in Hold.
        replace (S t <=? length mem)%nat with true
          by (symmetry; apply Nat.leb_le; exact Hold).
        replace (S (length mem) - S t)%nat
          with (S (length mem - S t))%nat in Hlookup by lia.
        rewrite nth_error_cons_succ in Hlookup.
        exact Hlookup.
      * apply Nat.leb_gt in Hold.
        replace (S (length mem) - S t)%nat with 0%nat in Hlookup
          by lia.
        cbn in Hlookup.
        inversion Hlookup.
        contradiction.
  - intro Hlookup.
    pose proof (prommemory_lookup_some_le ev mem t Hlookup) as Hle.
    rewrite PromMemory.lookup_cons_old by exact Hle.
    exact Hlookup.
Qed.

Lemma memory_fulfill_cons_unrelated
    (ev ev' : Ev.t) (prom : list view) (mem : Memory.t) :
  ev' ≠ ev →
  Memory.fulfill ev (length (ev' :: mem) :: prom) (ev' :: mem) =
  Memory.fulfill ev prom mem.
Proof.
  intro Hne.
  unfold Memory.fulfill.
  rewrite !list_basics.head_reverse.
  assert
    (Hfilter :
       filter (λ t : view,
           ((ev' :: mem : Memory.t) !! (t : nat)) = Some ev) prom =
       filter (λ t : view,
           ((mem : Memory.t) !! (t : nat)) = Some ev) prom).
  {
    induction prom as [|t prom IH]; cbn; [reflexivity|].
    destruct (decide (((ev' :: mem : Memory.t) !! (t : nat)) = Some ev))
      as [Hnew|Hnew];
    destruct (decide (((mem : Memory.t) !! (t : nat)) = Some ev))
      as [Hold|Hold].
    - rewrite IH.
      reflexivity.
    - exfalso.
      apply Hold.
      apply prommemory_lookup_cons_ne in Hnew; [exact Hnew|exact Hne].
    - exfalso.
      apply Hnew.
      apply prommemory_lookup_cons_ne; [exact Hne|exact Hold].
    - exact IH.
  }
  rewrite list_basics.filter_cons_False.
  - rewrite Hfilter.
    reflexivity.
  - rewrite PromMemory.lookup_latest.
    congruence.
Qed.

Lemma memory_fulfill_cons_mem_unrelated
    (ev ev' : Ev.t) (prom : list view) (mem : Memory.t) :
  ev' ≠ ev →
  Memory.fulfill ev prom (ev' :: mem) = Memory.fulfill ev prom mem.
Proof.
  intro Hne.
  unfold Memory.fulfill.
  rewrite !list_basics.head_reverse.
  assert
    (Hfilter :
       filter (λ t : view,
           ((ev' :: mem : Memory.t) !! (t : nat)) = Some ev) prom =
       filter (λ t : view,
           ((mem : Memory.t) !! (t : nat)) = Some ev) prom).
  {
    induction prom as [|t prom IH]; cbn; [reflexivity|].
    destruct (decide (((ev' :: mem : Memory.t) !! (t : nat)) = Some ev))
      as [Hnew|Hnew];
    destruct (decide (((mem : Memory.t) !! (t : nat)) = Some ev))
      as [Hold|Hold].
    - rewrite IH.
      reflexivity.
    - exfalso.
      apply Hold.
      apply prommemory_lookup_cons_ne in Hnew; [exact Hnew|exact Hne].
    - exfalso.
      apply Hnew.
      apply prommemory_lookup_cons_ne; [exact Hne|exact Hold].
    - exact IH.
  }
  rewrite Hfilter.
  reflexivity.
Qed.

Lemma memory_promise_inv ev mem mem' time :
  Exec.elem_of_results (mem', time) (Memory.promise ev mem) →
  mem' = ev :: mem ∧ time = length (ev :: mem).
Proof.
  intro H.
  unfold Memory.promise in H.
  inv_exec_result.
  split; [reflexivity|lia].
Qed.

Lemma memory_exclusive_cons_latest_old tid addr size tread ev mem :
  Memory.exclusive tid addr size tread (length (ev :: mem)) mem →
  Memory.exclusive tid addr size tread (length (ev :: mem)) (ev :: mem).
Proof.
  unfold Memory.exclusive.
  intros Hexclusive ev' Hin Hoverlap.
  cbn in Hexclusive |- *.
  change (length (ev :: mem)) with (S (length mem)) in Hin.
  replace (S (length mem) - 1)%nat with (length mem) in Hin by lia.
  replace (S (length mem) - 1)%nat with (length mem) in Hexclusive by lia.
  unfold Memory.cut_after, Memory.cut_before in Hexclusive.
  unfold Memory.cut_after, Memory.cut_before in Hin.
  replace (length mem - 0)%nat with (length mem) in Hexclusive by lia.
  rewrite PromMemory.cut_before_cons_old in Hin by lia.
  apply (Hexclusive ev').
  - exact Hin.
  - exact Hoverlap.
Qed.

Lemma fulfill_after_TState_promise_write (msg : Msg.t) ts mem :
  Memory.fulfill msg (TState.prom_wr ts) mem = None →
  Memory.fulfill msg
    (TState.prom_wr
       (TState.promise_write (length ((Ev.Msg msg) :: mem)) ts))
    ((Ev.Msg msg) :: mem) =
  Some (length ((Ev.Msg msg) :: mem)).
Proof.
  destruct ts.
  cbn.
  apply memory_fulfill_after_promise.
Qed.

Lemma fulfill_after_TState_promise_tlbi ev ts mem :
  Memory.fulfill ev (TState.prom_tlbi ts) mem = None →
  Memory.fulfill ev
    (TState.prom_tlbi
       (TState.promise_tlbi (length (ev :: mem)) ts))
    (ev :: mem) =
  Some (length (ev :: mem)).
Proof.
  destruct ts.
  cbn.
  apply memory_fulfill_after_promise.
Qed.

Lemma elem_of_unfolded_ppstate_mset_prom_wr
    (st : TState.t) (mem : Memory.t) (iis : IIS.t) upd :
  Exec.elem_of_results
    (PPState.Make (set TState.prom_wr upd st) mem iis, ())
    ((mset (TState.prom_wr ∘ PPState.state) upd :
        Exec.t (PPState.t TState.t Ev.t IIS.t) string unit)
       (PPState.Make st mem iis)).
Proof.
  change (PPState.Make (set TState.prom_wr upd st) mem iis)
    with (set (TState.prom_wr ∘ PPState.state) upd
            (PPState.Make st mem iis)).
  apply Exec.elem_of_unfolded_mset.
Qed.

Lemma elem_of_unfolded_ppstate_mset_prom_tlbi
    (st : TState.t) (mem : Memory.t) (iis : IIS.t) upd :
  Exec.elem_of_results
    (PPState.Make (set TState.prom_tlbi upd st) mem iis, ())
    ((mset (TState.prom_tlbi ∘ PPState.state) upd :
        Exec.t (PPState.t TState.t Ev.t IIS.t) string unit)
       (PPState.Make st mem iis)).
Proof.
  change (PPState.Make (set TState.prom_tlbi upd st) mem iis)
    with (set (TState.prom_tlbi ∘ PPState.state) upd
            (PPState.Make st mem iis)).
  apply Exec.elem_of_unfolded_mset.
Qed.

Lemma TState_filter_prom_wr_after_promise_write (v : view) ts :
  set TState.prom_wr
    (filter (λ t : view, (t : nat) ≠ (v : nat)))
    (TState.promise_write v ts) =
  set TState.prom_wr
    (filter (λ t : view, (t : nat) ≠ (v : nat))) ts.
Proof.
  destruct ts.
  unfold TState.promise_write.
  cbn.
  rewrite decide_False by congruence.
  reflexivity.
Qed.

Lemma TState_update_tcoh_after_promise_write asid page_offset v p ts :
  TState.update_tcoh asid page_offset v (TState.promise_write p ts) =
  TState.promise_write p (TState.update_tcoh asid page_offset v ts).
Proof.
  destruct ts; reflexivity.
Qed.

Lemma TState_update_tcohs_after_promise_write asid page_offsets v p ts :
  TState.update_tcohs asid page_offsets v (TState.promise_write p ts) =
  TState.promise_write p (TState.update_tcohs asid page_offsets v ts).
Proof.
  unfold TState.update_tcohs.
  induction page_offsets as [|page_offset page_offsets IH]; cbn.
  - reflexivity.
  - rewrite IH.
    apply TState_update_tcoh_after_promise_write.
Qed.

Lemma TState_tcohs_before_inv_time_after_promise_write
    asid page_offsets inv_time p ts :
  TState.tcohs_before_inv_time asid page_offsets inv_time ts →
  TState.tcohs_before_inv_time asid page_offsets inv_time
    (TState.promise_write p ts).
Proof.
  destruct inv_time as [inv_t|]; cbn; [|done].
  intros H page_offset Hin.
  destruct ts.
  exact (H page_offset Hin).
Qed.

Lemma TState_filter_prom_tlbi_after_promise_tlbi (v : view) ts :
  set TState.prom_tlbi
    (filter (λ t : view, (t : nat) ≠ (v : nat)))
    (TState.promise_tlbi v ts) =
  set TState.prom_tlbi
    (filter (λ t : view, (t : nat) ≠ (v : nat))) ts.
Proof.
  destruct ts.
  unfold TState.promise_tlbi.
  cbn.
  rewrite decide_False by congruence.
  reflexivity.
Qed.

Lemma TState_filter_prom_tlbi_after_other_promise_event
    (ev : Ev.t) (p time : view) ts :
  (p : nat) ≠ (time : nat) →
  set TState.prom_tlbi
    (filter (λ t : view, (t : nat) ≠ (time : nat)))
    (TState_promise_event ev p ts) =
  TState_promise_event ev p
    (set TState.prom_tlbi
       (filter (λ t : view, (t : nat) ≠ (time : nat))) ts).
Proof.
  intros Hne.
  destruct ev as [msg|tlbi recipient]; destruct ts; cbn.
  - reflexivity.
  - rewrite decide_True by exact Hne.
    reflexivity.
Qed.

Lemma PPState_mem_set_state_read upd
    (ppst : PPState.t TState.t Ev.t IIS.t) :
  PPState.mem (set PPState.state upd ppst) = PPState.mem ppst.
Proof.
  destruct ppst; reflexivity.
Qed.

Lemma PPState_mem_set_rmw_read upd
    (ppst : PPState.t TState.t Ev.t IIS.t) :
  PPState.mem (set (IIS.rmw_read ∘ PPState.iis) upd ppst) =
  PPState.mem ppst.
Proof.
  destruct ppst; reflexivity.
Qed.

Lemma PPState_mem_same_state_choices {A E} (ts : TState.t)
    (mem : PromMemory.t Ev.t) (iis : IIS.t) (choice : A)
    choices (ppst : PPState.t TState.t Ev.t IIS.t) res :
  Exec.elem_of_results (ppst, res)
    ({| Exec.results :=
         (PPState.Make ts mem iis, choice)
         :: (pair (PPState.Make ts mem iis) <$> choices);
       Exec.errors := ([] : list E) |} :
       Exec.res E (PPState.t TState.t Ev.t IIS.t * A)) →
  PPState.mem ppst = mem.
Proof.
  unfold elem_of, Exec.elem_of_results.
  cbn.
  intro Hin.
  apply elem_of_cons in Hin as [Heq | Hin].
  - inversion Heq; subst; reflexivity.
  - rewrite elem_of_list_fmap in Hin.
    destruct Hin as [? [Heq _]].
    inversion Heq; subst; reflexivity.
Qed.

Lemma PPState_prom_wr_cohs_vwr_as_sets filter cohs time
    (base : PPState.t TState.t Ev.t IIS.t) :
  PPState.Make
    (TState.update TState.vwr time
       (TState.update_cohs cohs
          (set TState.prom_wr filter (PPState.state base))))
    (PPState.mem base) (PPState.iis base) =
  set PPState.state (TState.update TState.vwr time)
    (set PPState.state (TState.update_cohs cohs)
       (set (TState.prom_wr ∘ PPState.state) filter base)).
Proof.
  destruct base; reflexivity.
Qed.

Lemma update_tcoh_for_access_guard_inv size inv_time ts mem iis ppst' :
  Exec.elem_of_results (ppst', ())
    (update_tcoh_for_access size inv_time ts
       (PPState.Make ts mem iis)) →
  match IIS.trs iis with
  | Some trs =>
      TState.tcohs_before_inv_time (IIS.TransRes.asid trs)
        (TState.va_page_offsets (IIS.TransRes.va_addr trs) size)
        inv_time ts
  | None => True
  end.
Proof.
  intro Hrun.
  unfold update_tcoh_for_access in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_trs [trs_opt [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  cbn in Hrun.
  destruct (IIS.trs iis) as [trs|] eqn:Htrs; [|exact I].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [Hguard_prop [Hguard _]]].
  exact Hguard_prop.
Qed.

Lemma update_tcoh_for_access_after_promise_write size inv_time ts mem iis p :
  (match IIS.trs iis with
   | Some trs =>
       TState.tcohs_before_inv_time (IIS.TransRes.asid trs)
         (TState.va_page_offsets (IIS.TransRes.va_addr trs) size)
         inv_time ts
   | None => True
   end) →
  Exec.elem_of_results
    ((match IIS.trs iis with
      | Some trs =>
          PPState.Make
            (TState.update_tcohs (IIS.TransRes.asid trs)
               (TState.va_page_offsets (IIS.TransRes.va_addr trs) size)
               (IIS.TransRes.trans_start trs)
               (TState.promise_write p ts))
            mem iis
      | None => PPState.Make (TState.promise_write p ts) mem iis
      end), ())
    (update_tcoh_for_access size inv_time (TState.promise_write p ts)
       (PPState.Make (TState.promise_write p ts) mem iis)).
Proof.
  intro Hguard.
  unfold update_tcoh_for_access.
  eapply Exec.elem_of_bind_intro with
    (st' := PPState.Make (TState.promise_write p ts) mem iis)
    (a := IIS.trs iis).
  { apply (Exec.elem_of_mget (E:=string)
      (PPState.Make (TState.promise_write p ts) mem iis)
      (IIS.trs ∘ PPState.iis)). }
  cbn.
  destruct (IIS.trs iis) as [trs|] eqn:Htrs.
  - destruct (Exec.elem_of_guard_discard
        (E:=string)
        (PPState.Make (TState.promise_write p ts) mem iis)
        (TState_tcohs_before_inv_time_after_promise_write
           (IIS.TransRes.asid trs)
           (TState.va_page_offsets (IIS.TransRes.va_addr trs) size)
           inv_time p ts Hguard)) as [Hguard' Hguard_run].
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make (TState.promise_write p ts) mem iis)
      (a := Hguard').
    + exact Hguard_run.
    + cbn.
      change
        (Exec.elem_of_results
           (set PPState.state
              (TState.update_tcohs (IIS.TransRes.asid trs)
                 (TState.va_page_offsets (IIS.TransRes.va_addr trs) size)
                 (IIS.TransRes.trans_start trs))
              (PPState.Make (TState.promise_write p ts) mem iis), ())
           ((mset PPState.state
               (TState.update_tcohs (IIS.TransRes.asid trs)
                  (TState.va_page_offsets (IIS.TransRes.va_addr trs) size)
                  (IIS.TransRes.trans_start trs)) :
               Exec.t (PPState.t TState.t Ev.t IIS.t) string unit)
              (PPState.Make (TState.promise_write p ts) mem iis))).
      apply Exec.elem_of_mset.
  - apply Exec.elem_of_mret.
Qed.

Lemma read_mem_explicit_preserves_mem addr size macc init ppst ppst' res :
  Exec.elem_of_results (ppst', res)
    (read_mem_explicit addr size macc init ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  destruct ppst as [ts mem iis].
  cbn.
  intro H.
  unfold read_mem_explicit in H.
  cbn in H.
  inv_exec_result;
    repeat match goal with
    | H : Exec.elem_of_results (?st', ?v)
            {| Exec.results := (?st0, _) :: ?xs;
               Exec.errors := [] |} |- _ =>
        unfold elem_of, Exec.elem_of_results in H; cbn in H;
        destruct H as [H | H];
        [inversion H; subst; clear H
        | rewrite elem_of_list_fmap in H;
          destruct H as [? [H _]];
          inversion H; subst; clear H]
    end;
    try match goal with
    | H3 : Exec.elem_of_results (?choice_st, _)
             {| Exec.results := ({| PPState.state := ts;
                                    PPState.mem := mem;
                                    PPState.iis := iis |}, _) :: ?xs;
                Exec.errors := [] |} |- _ =>
        assert (PPState.mem choice_st = mem) as Hchoice_mem;
        [ unfold elem_of, Exec.elem_of_results in H3; cbn in H3;
          destruct H3 as [H3 | H3];
          [inversion H3; subst; reflexivity
          | rewrite elem_of_list_fmap in H3;
            destruct H3 as [? [H3 _]];
            inversion H3; subst; reflexivity]
        | idtac ]
    end;
    rewrite ?PPState_mem_set_state_read, ?PPState_mem_set_rmw_read in *;
    repeat match goal with
    | Hmem : PPState.mem ?choice_st = ?base_mem
      |- context [PPState.mem ?choice_st] =>
        rewrite Hmem
    end;
    try solve [
      unfold elem_of, Exec.elem_of_results in H3; cbn in H3;
      destruct H3 as [H3 | H3];
      [inversion H3; subst; reflexivity
      | rewrite elem_of_list_fmap in H3;
        destruct H3 as [? [H3 _]];
        inversion H3; subst; reflexivity]
    ];
    try solve [
      exact (PPState_mem_same_state_choices
        (E:=PPState.t TState.t Ev.t IIS.t * string)
        ts mem iis _ _ x6 x H3)
    ];
    try solve [
      match goal with
      | Hchoice : Exec.elem_of_results (?choice_st, _) _
        |- PPState.mem ?choice_st = mem =>
          unfold elem_of, Exec.elem_of_results in Hchoice; cbn in Hchoice;
          destruct Hchoice as [Hchoice | Hchoice];
          [inversion Hchoice; subst; reflexivity
          | rewrite elem_of_list_fmap in Hchoice;
            destruct Hchoice as [? [Hchoice _]];
            inversion Hchoice; subst; reflexivity]
      end
    ];
    cbn; reflexivity.
Qed.

Lemma write_mem_none_preserves_mem tid addr size macc data ppst ppst' :
  Exec.elem_of_results (ppst', None)
    (write_mem tid addr size macc data ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H.
  unfold write_mem in H.
  inv_exec_result; reflexivity.
Qed.

Lemma write_mem_promise_replay_one tid addr size macc data ppst ppst' vpre :
  Exec.elem_of_results (ppst', Some vpre)
    (write_mem tid addr size macc data ppst) →
  let msg := Msg.make size tid addr data in
  PPState.mem ppst' = Ev.Msg msg :: PPState.mem ppst ∧
  (vpre ≤ length (PPState.mem ppst))%nat ∧
  Exec.elem_of_results (ppst', None)
    (write_mem tid addr size macc data
       (PPState.Make
          (TState.promise_write (length (Ev.Msg msg :: PPState.mem ppst))
             (PPState.state ppst))
          (Ev.Msg msg :: PPState.mem ppst)
          (PPState.iis ppst))).
Proof.
  destruct ppst as [ts mem iis].
  cbn.
  intro Hrun.
  unfold write_mem in Hrun.
  set (msg := Msg.make size tid addr data) in *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_mem [mem0 [Hget_mem Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_mem as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_pair [[time new_promise] [Hmatch Hrun]]].
  destruct (Memory.fulfill msg (TState.prom_wr ts) mem) as [tfulfilled|]
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
    destruct (memory_promise_inv (Ev.Msg msg) mem mem1 time_prom Hpromise)
      as [-> Htime_prom].
    subst pp_prom.
    apply Exec.elem_of_mret_inv in Hpair as [-> Hpair_eq].
    inversion Hpair_eq; subst time new_promise.
    subst time_prom.
    set (pnew := length (Ev.Msg msg :: mem)).
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
    assert (Hpp_rmw :
      pp_rmw = PPState.Make ts (Ev.Msg msg :: mem) iis_write).
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
        (PPState.Make (TState.promise_write pnew ts) (Ev.Msg msg :: mem)
           iis_write, read_acquire)
        (((if is_atomic_rmw macc then
            rmw_read_opt ← mget (IIS.rmw_read ∘ PPState.iis);
            '(tread, read_acquire) ←
              othrow "RMW write without a read" rmw_read_opt;
            guard_discard' (Memory.exclusive tid addr size tread pnew
              (Ev.Msg msg :: mem));;
            msetv (IIS.rmw_read ∘ PPState.iis) None;;
            mret read_acquire
          else mret false) :
          Exec.t (PPState.t TState.t Ev.t IIS.t) string bool)
           (PPState.Make (TState.promise_write pnew ts)
              (Ev.Msg msg :: mem) iis))).
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
          (st' := PPState.Make (TState.promise_write pnew ts)
             (Ev.Msg msg :: mem) iis)
          (a := Some (tread0, read_acquire1)).
        + rewrite <- Hrmw_read_iis.
          change (length (Ev.Msg msg :: mem)) with pnew.
          apply (Exec.elem_of_mget (E:=string)
            (PPState.Make (TState.promise_write pnew ts)
               (Ev.Msg msg :: mem) iis)
            (IIS.rmw_read ∘ PPState.iis)).
        + cbn.
          eapply Exec.elem_of_bind_intro with
            (st' := PPState.Make (TState.promise_write pnew ts)
               (Ev.Msg msg :: mem) iis)
            (a := (tread0, read_acquire1)).
          * unfold othrow.
            apply Exec.elem_of_mret.
          * cbn.
            eapply Exec.elem_of_bind_intro with
              (st' := PPState.Make (TState.promise_write pnew ts)
                 (Ev.Msg msg :: mem) iis)
              (a := ()).
            -- apply Exec.elem_of_guard_discard_unit.
               subst pnew.
               apply memory_exclusive_cons_latest_old.
               exact Hexclusive_rmw.
            -- cbn.
               eapply Exec.elem_of_bind_intro with
                 (st' := PPState.Make (TState.promise_write pnew ts)
                   (Ev.Msg msg :: mem)
                   (set IIS.rmw_read (λ _ : option (nat * bool), None) iis))
                 (a := ()).
               ++ unfold msetv.
                  change (PPState.Make (TState.promise_write pnew ts)
                    (Ev.Msg msg :: mem)
                    (set IIS.rmw_read (λ _ : option (nat * bool), None) iis))
                    with
                    (set (IIS.rmw_read ∘ PPState.iis)
                       (λ _ : option (nat * bool), None)
                       (PPState.Make (TState.promise_write pnew ts)
                          (Ev.Msg msg :: mem) iis)).
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
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_inv_time [inv_time [Hget_inv_time Hrun]]].
    apply Exec.elem_of_mget_inv in Hget_inv_time as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_inv_guard [[] [Hinv_guard Hrun]]].
    pose proof (Exec.elem_of_guard_discard_unit_prop
      _ _ Hinv_guard) as Hinv_prop.
    apply Exec.elem_of_guard_discard_unit_inv in Hinv_guard as ->.
	    apply Exec.elem_of_bind_elim in Hrun as
	      [pp_promset [[] [Hpromset Hrun]]].
	    assert (pp_promset =
	      match IIS.trs iis_write with
	      | Some trs =>
	          set PPState.state
	            (TState.update_tcohs (IIS.TransRes.asid trs)
	               (TState.va_page_offsets (IIS.TransRes.va_addr trs) size)
	               (IIS.TransRes.trans_start trs))
	            (PPState.Make ts (Ev.Msg msg :: mem) iis_write)
	      | None => PPState.Make ts (Ev.Msg msg :: mem) iis_write
	      end) as ->.
	    {
	      unfold update_tcoh_for_access in Hpromset.
	      apply Exec.elem_of_bind_elim in Hpromset as
	        [pp_trs [trs_opt [Hget_trs Hpromset]]].
	      apply Exec.elem_of_mget_inv in Hget_trs as [-> ->].
	      cbn in Hpromset.
	      destruct (IIS.trs iis_write) as [trs|] eqn:Htrs.
	      - apply Exec.elem_of_bind_elim in Hpromset as
	          [pp_tcoh_guard [Htcoh_guard_wit [Htcoh_guard Hpromset]]].
	        apply Exec.elem_of_guard_discard_inv in Htcoh_guard as ->.
	        apply Exec.elem_of_mset_inv in Hpromset as ->.
	        reflexivity.
	      - apply Exec.elem_of_mret_inv in Hpromset as [-> _].
	        reflexivity.
	    }
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
	    assert (Hrmw_acq_mem : PPState.mem pp_rmw_acq = Ev.Msg msg :: mem).
	    {
	      destruct (is_atomic_rmw macc && is_rel_acq macc && read_acquire)
	        eqn:Hrmw_acq_bool.
      - unfold elem_of, Exec.elem_of_results in Hrmw_acq.
        cbn in Hrmw_acq.
        apply elem_of_list_singleton in Hrmw_acq.
        inversion Hrmw_acq; subst.
        destruct (IIS.trs iis_write); destruct ts; cbn in *; reflexivity.
	      - apply Exec.elem_of_mret_inv in Hrmw_acq as [-> _].
	        destruct (IIS.trs iis_write); destruct ts; cbn in *; reflexivity.
	    }
	    apply Exec.elem_of_bind_elim in Hrun as
	      [pp_acq [[] [Hacq Hrun]]].
	    assert (Hacq_mem : PPState.mem pp_acq = Ev.Msg msg :: mem).
	    {
	      destruct (is_atomic_rmw macc && is_rel_acq macc && read_acquire)
	        eqn:Hacq_bool.
	      - apply Exec.elem_of_mset_inv in Hacq as ->.
	        rewrite PPState_mem_set_state_read.
	        exact Hrmw_acq_mem.
	      - apply Exec.elem_of_mret_inv in Hacq as [-> _].
	        exact Hrmw_acq_mem.
	    }
	    set (ts_tcoh :=
	      match IIS.trs iis_write with
	      | Some trs =>
	          TState.update_tcohs (IIS.TransRes.asid trs)
	            (TState.va_page_offsets (IIS.TransRes.va_addr trs) size)
	            (IIS.TransRes.trans_start trs) ts
	      | None => ts
	      end) in Hrmw_acq.
	    apply Exec.elem_of_bind_elim in Hrun as
	      [pp_xcl [xcl [Hxcl Hrun]]].
    pose proof Hpre as Hpre_promise.
    destruct (is_exclusive macc) eqn:Hexcl.
    + destruct (TState.xclb ts) as [xclb_entry|] eqn:Hxclb.
      * destruct xclb_entry as [[[tread raddr] rsize] xview].
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
		           ++ destruct pp_acq as [acq_ts acq_mem acq_iis].
		              cbn in Hacq_mem |- *.
		              exact Hacq_mem.
           ++ split.
              ** cbn in Hpre. lia.
	              ** { unfold write_mem.
	                 eapply Exec.elem_of_bind_intro.
	                 --- apply (Exec.elem_of_mget (E:=string)
	                       (PPState.Make
	                          (TState.promise_write (length (Ev.Msg msg :: mem)) ts)
	                          (Ev.Msg msg :: mem) iis)
	                       PPState.state).
	                 --- cbn.
	                     eapply Exec.elem_of_bind_intro with
	                       (st' := PPState.Make
	                         (TState.promise_write (length (Ev.Msg msg :: mem)) ts)
	                         (Ev.Msg msg :: mem) iis)
	                       (a := Ev.Msg msg :: mem).
	                     +++ apply (Exec.elem_of_mget (E:=string)
	                           (PPState.Make
	                              (TState.promise_write
	                                 (length (Ev.Msg msg :: mem)) ts)
	                              (Ev.Msg msg :: mem) iis)
	                           PPState.mem).
	                     +++ cbn.
	                         rewrite fulfill_after_TState_promise_write
	                           by exact Hfulfill.
	                         cbn.
	                         eapply Exec.elem_of_bind_intro with
	                           (st' := PPState.Make
	                             (TState.promise_write
	                                (length (Ev.Msg msg :: mem)) ts)
	                             (Ev.Msg msg :: mem) iis)
	                           (a := (length (Ev.Msg msg :: mem), false)).
	                         *** apply Exec.elem_of_mret.
	                         *** cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.promise_write
	                                    (length (Ev.Msg msg :: mem)) ts)
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := read_acquire).
	                             { change (length (Ev.Msg msg :: mem)) with pnew.
	                               exact Hrmw_replay. }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.promise_write
	                                    (length (Ev.Msg msg :: mem)) ts)
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := IIS.strict iis).
	                             { rewrite <- Hstrict_write.
	                               apply (Exec.elem_of_mget (E:=string)
	                                 (PPState.Make
	                                   (TState.promise_write
	                                      (length (Ev.Msg msg :: mem)) ts)
	                                   (Ev.Msg msg :: mem) iis_write)
	                                 (IIS.strict ∘ PPState.iis)). }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro.
	                             { apply elem_of_guard_discard_proof. }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.promise_write
	                                    (length (Ev.Msg msg :: mem)) ts)
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := IIS.inv_time iis_write).
	                             { apply (Exec.elem_of_mget (E:=string)
	                                 (PPState.Make
	                                   (TState.promise_write
	                                      (length (Ev.Msg msg :: mem)) ts)
	                                   (Ev.Msg msg :: mem) iis_write)
	                                 (IIS.inv_time ∘ PPState.iis)). }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.promise_write
	                                    (length (Ev.Msg msg :: mem)) ts)
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := ()).
		                             { apply Exec.elem_of_guard_discard_unit.
		                               exact Hinv_prop. }
		                             cbn.
		                             eapply Exec.elem_of_bind_intro with
		                               (st' :=
		                                  match IIS.trs iis_write with
		                                  | Some trs =>
		                                      PPState.Make
		                                        (TState.update_tcohs
		                                           (IIS.TransRes.asid trs)
		                                           (TState.va_page_offsets
		                                              (IIS.TransRes.va_addr trs) size)
		                                           (IIS.TransRes.trans_start trs)
		                                           (TState.promise_write
		                                              (length (Ev.Msg msg :: mem)) ts))
		                                        (Ev.Msg msg :: mem) iis_write
		                                  | None =>
		                                      PPState.Make
		                                        (TState.promise_write
		                                           (length (Ev.Msg msg :: mem)) ts)
		                                        (Ev.Msg msg :: mem) iis_write
		                                  end)
		                               (a := ()).
		                             { apply update_tcoh_for_access_after_promise_write.
		                               eapply update_tcoh_for_access_guard_inv.
		                               exact Hpromset. }
		                             cbn.
			                             eapply Exec.elem_of_bind_intro with
			                               (st' := PPState.Make
			                                 (set TState.prom_wr
			                                    (filter
			                                       (λ t : view,
			                                          (t : nat) ≠
			                                          (length (Ev.Msg msg :: mem) : nat))) ts_tcoh)
		                                 (Ev.Msg msg :: mem) iis_write)
		                               (a := ()).
		                             { replace
		                                 (PPState.Make
		                                    (set TState.prom_wr
		                                       (filter
		                                          (λ t : view,
		                                             (t : nat) ≠
		                                             (length (Ev.Msg msg :: mem) : nat)))
		                                       ts_tcoh)
		                                    (Ev.Msg msg :: mem) iis_write)
		                                 with
		                                 (set (TState.prom_wr ∘ PPState.state)
		                                    (filter
		                                       (λ t : view,
		                                          (t : nat) ≠
		                                          (length (Ev.Msg msg :: mem) : nat)))
		                                    (match IIS.trs iis_write with
		                                     | Some trs =>
		                                         PPState.Make
		                                           (TState.update_tcohs
		                                              (IIS.TransRes.asid trs)
		                                              (TState.va_page_offsets
		                                                 (IIS.TransRes.va_addr trs) size)
		                                              (IIS.TransRes.trans_start trs)
		                                              (TState.promise_write
		                                                 (length (Ev.Msg msg :: mem)) ts))
		                                           (Ev.Msg msg :: mem) iis_write
		                                     | None =>
		                                         PPState.Make
		                                           (TState.promise_write
		                                              (length (Ev.Msg msg :: mem)) ts)
		                                           (Ev.Msg msg :: mem) iis_write
		                                     end)).
		                               - apply Exec.elem_of_mset.
		                               - subst ts_tcoh.
			                                 destruct (IIS.trs iis_write) as [trs|]; cbn.
			                                 + rewrite TState_update_tcohs_after_promise_write.
			                                   destruct (TState.update_tcohs
			                                     (IIS.TransRes.asid trs)
			                                     (TState.va_page_offsets
			                                        (IIS.TransRes.va_addr trs) size)
			                                     (IIS.TransRes.trans_start trs) ts);
			                                     cbn.
			                                   rewrite decide_False by congruence.
			                                   reflexivity.
			                                 + destruct ts; cbn.
			                                   rewrite decide_False by congruence.
			                                   reflexivity. }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.update_cohs
		                                    (map (., length (Ev.Msg msg :: mem))
		                                       (addr_range addr size))
		                                    (set TState.prom_wr
		                                       (filter
		                                          (λ t : view,
		                                             (t : nat) ≠
		                                             (length (Ev.Msg msg :: mem) : nat)))
		                                       ts_tcoh))
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := ()).
	                             { apply elem_of_unfolded_ppstate_mset_state. }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.update TState.vwr
	                                    (length (Ev.Msg msg :: mem))
	                                    (TState.update_cohs
	                                       (map (., length (Ev.Msg msg :: mem))
	                                          (addr_range addr size))
		                                       (set TState.prom_wr
		                                          (filter
		                                             (λ t : view,
		                                                (t : nat) ≠
		                                                (length (Ev.Msg msg :: mem) :
		                                                   nat)))
		                                          ts_tcoh)))
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := ()).
		                             { apply elem_of_unfolded_ppstate_mset_state. }
		                             cbn.
			                             eapply Exec.elem_of_bind_intro with
			                               (st' := pp_rmw_acq)
			                               (a := ()).
				                             { subst ts_tcoh.
				                               destruct (IIS.trs iis_write);
				                                 destruct ts; cbn in *;
				                                 exact Hrmw_acq. }
		                             cbn.
		                             eapply Exec.elem_of_bind_intro with
		                               (st' := pp_acq)
		                               (a := ()).
		                             { exact Hacq. }
		                             cbn.
		                             rewrite Hexcl.
	                             replace (TState.xclb
	                               (TState.promise_write
	                                  (length (Ev.Msg msg :: mem)) ts))
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
		                               [prom_wr0 prom_tlbi0 regs0 levs0 coh0 tcoh0 vrd0 vwr0
		                                vdmbst0 vdmb0 vdsb0 vspec0 vcse0 vtlbi_self0
		                                vtlbi_other0 vmsr0 vacq0 vrel0 fwdb0 xclb0].
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
		      * destruct pp_acq as [acq_ts acq_mem acq_iis].
		        cbn in Hacq_mem |- *.
		        exact Hacq_mem.
      * split.
        -- cbn in Hpre. lia.
	        -- { unfold write_mem.
	           eapply Exec.elem_of_bind_intro.
	           ++ apply (Exec.elem_of_mget (E:=string)
	                (PPState.Make
	                   (TState.promise_write (length (Ev.Msg msg :: mem)) ts)
	                   (Ev.Msg msg :: mem) iis)
	                PPState.state).
	           ++ cbn.
	              eapply Exec.elem_of_bind_intro.
	              ** apply (Exec.elem_of_mget (E:=string)
	                   (PPState.Make
	                      (TState.promise_write (length (Ev.Msg msg :: mem)) ts)
	                      (Ev.Msg msg :: mem) iis)
	                   PPState.mem).
	              ** cbn.
	                 rewrite fulfill_after_TState_promise_write by exact Hfulfill.
	                 cbn.
	                 eapply Exec.elem_of_bind_intro.
	                 --- apply Exec.elem_of_mret.
	                 --- cbn.
	                     eapply Exec.elem_of_bind_intro with
	                       (st' := PPState.Make
	                         (TState.promise_write (length (Ev.Msg msg :: mem)) ts)
	                         (Ev.Msg msg :: mem) iis_write)
	                       (a := read_acquire).
	                     +++ change (length (Ev.Msg msg :: mem)) with pnew.
	                         exact Hrmw_replay.
	                     +++ cbn.
	                         eapply Exec.elem_of_bind_intro with
	                           (st' := PPState.Make
	                             (TState.promise_write
	                                (length (Ev.Msg msg :: mem)) ts)
	                             (Ev.Msg msg :: mem) iis_write)
	                           (a := IIS.strict iis).
	                         *** rewrite <- Hstrict_write.
	                             apply (Exec.elem_of_mget (E:=string)
	                               (PPState.Make
	                                 (TState.promise_write
	                                    (length (Ev.Msg msg :: mem)) ts)
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (IIS.strict ∘ PPState.iis)).
	                         *** cbn.
	                             eapply Exec.elem_of_bind_intro.
	                             { apply elem_of_guard_discard_proof. }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.promise_write
	                                    (length (Ev.Msg msg :: mem)) ts)
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := IIS.inv_time iis_write).
	                             { apply (Exec.elem_of_mget (E:=string)
	                                 (PPState.Make
	                                   (TState.promise_write
	                                      (length (Ev.Msg msg :: mem)) ts)
	                                   (Ev.Msg msg :: mem) iis_write)
	                                 (IIS.inv_time ∘ PPState.iis)). }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.promise_write
	                                    (length (Ev.Msg msg :: mem)) ts)
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := ()).
		                             { apply Exec.elem_of_guard_discard_unit.
		                               exact Hinv_prop. }
		                             cbn.
		                             eapply Exec.elem_of_bind_intro with
		                               (st' :=
		                                  match IIS.trs iis_write with
		                                  | Some trs =>
		                                      PPState.Make
		                                        (TState.update_tcohs
		                                           (IIS.TransRes.asid trs)
		                                           (TState.va_page_offsets
		                                              (IIS.TransRes.va_addr trs) size)
		                                           (IIS.TransRes.trans_start trs)
		                                           (TState.promise_write
		                                              (length (Ev.Msg msg :: mem)) ts))
		                                        (Ev.Msg msg :: mem) iis_write
		                                  | None =>
		                                      PPState.Make
		                                        (TState.promise_write
		                                           (length (Ev.Msg msg :: mem)) ts)
		                                        (Ev.Msg msg :: mem) iis_write
		                                  end)
		                               (a := ()).
		                             { apply update_tcoh_for_access_after_promise_write.
		                               eapply update_tcoh_for_access_guard_inv.
		                               exact Hpromset. }
		                             cbn.
		                             eapply Exec.elem_of_bind_intro with
		                               (st' := PPState.Make
		                                 (set TState.prom_wr
		                                    (filter
		                                       (λ t : view,
		                                          (t : nat) ≠
		                                          (length (Ev.Msg msg :: mem) : nat))) ts_tcoh)
		                                 (Ev.Msg msg :: mem) iis_write)
		                               (a := ()).
		                             { replace
		                                 (PPState.Make
		                                    (set TState.prom_wr
		                                       (filter
		                                          (λ t : view,
		                                             (t : nat) ≠
		                                             (length (Ev.Msg msg :: mem) : nat)))
		                                       ts_tcoh)
		                                    (Ev.Msg msg :: mem) iis_write)
		                                 with
		                                 (set (TState.prom_wr ∘ PPState.state)
		                                    (filter
		                                       (λ t : view,
		                                          (t : nat) ≠
		                                          (length (Ev.Msg msg :: mem) : nat)))
		                                    (match IIS.trs iis_write with
		                                     | Some trs =>
		                                         PPState.Make
		                                           (TState.update_tcohs
		                                              (IIS.TransRes.asid trs)
		                                              (TState.va_page_offsets
		                                                 (IIS.TransRes.va_addr trs) size)
		                                              (IIS.TransRes.trans_start trs)
		                                              (TState.promise_write
		                                                 (length (Ev.Msg msg :: mem)) ts))
		                                           (Ev.Msg msg :: mem) iis_write
		                                     | None =>
		                                         PPState.Make
		                                           (TState.promise_write
		                                              (length (Ev.Msg msg :: mem)) ts)
		                                           (Ev.Msg msg :: mem) iis_write
		                                     end)).
		                               - apply Exec.elem_of_mset.
		                               - subst ts_tcoh.
		                                 destruct (IIS.trs iis_write) as [trs|]; cbn.
		                                 + rewrite TState_update_tcohs_after_promise_write.
		                                   destruct (TState.update_tcohs
		                                     (IIS.TransRes.asid trs)
		                                     (TState.va_page_offsets
		                                        (IIS.TransRes.va_addr trs) size)
		                                     (IIS.TransRes.trans_start trs) ts);
		                                     cbn.
		                                   rewrite decide_False by congruence.
		                                   reflexivity.
		                                 + destruct ts; cbn.
		                                   rewrite decide_False by congruence.
		                                   reflexivity. }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.update_cohs
		                                    (map (., length (Ev.Msg msg :: mem))
		                                       (addr_range addr size))
		                                    (set TState.prom_wr
		                                       (filter
		                                          (λ t : view,
		                                             (t : nat) ≠
		                                             (length (Ev.Msg msg :: mem) : nat)))
		                                       ts_tcoh))
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := ()).
	                             { apply elem_of_unfolded_ppstate_mset_state. }
	                             cbn.
	                             eapply Exec.elem_of_bind_intro with
	                               (st' := PPState.Make
	                                 (TState.update TState.vwr
	                                    (length (Ev.Msg msg :: mem))
	                                    (TState.update_cohs
	                                       (map (., length (Ev.Msg msg :: mem))
	                                          (addr_range addr size))
		                                       (set TState.prom_wr
		                                          (filter
		                                             (λ t : view,
		                                                (t : nat) ≠
		                                                (length (Ev.Msg msg :: mem) :
		                                                   nat)))
		                                          ts_tcoh)))
	                                 (Ev.Msg msg :: mem) iis_write)
	                               (a := ()).
	                             { apply elem_of_unfolded_ppstate_mset_state. }
	                             cbn.
			                             eapply Exec.elem_of_bind_intro with
			                               (st' := pp_rmw_acq)
		                               (a := ()).
		                             { subst ts_tcoh.
		                               destruct (IIS.trs iis_write);
		                                 destruct ts; cbn in *;
		                                 exact Hrmw_acq. }
		                             cbn.
		                             eapply Exec.elem_of_bind_intro with
		                               (st' := pp_acq)
		                               (a := ()).
		                             { exact Hacq. }
		                             cbn.
		                             rewrite Hexcl.
	                             eapply Exec.elem_of_bind_intro.
	                             { apply Exec.elem_of_mret. }
	                             cbn.
	                             rewrite <- Hstrict_write.
	                             eapply Exec.elem_of_bind_intro.
	                             { apply elem_of_unfolded_ppstate_mset_state. }
	                             cbn.
	                             apply Exec.elem_of_mret. }
Unshelve.
all: try destruct ts; cbn in *;
  try rewrite Hstrict_write in *;
  try rewrite <- Hstrict_write in *;
  try exact Hpre_promise;
  try exact Hpre.
Qed.

Lemma read_pte_preserves_mem ppst ppst' val :
  Exec.elem_of_results (ppst', val) (read_pte ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H.
  unfold read_pte in H.
  inv_exec_result; reflexivity.
Qed.

Lemma PPState_mem_setv_state_iis (x : TState.t * IIS.t)
    (ppst : PPState.t TState.t Ev.t IIS.t) :
  PPState.mem (setv (PPState.state ×× PPState.iis) x ppst) =
  PPState.mem ppst.
Proof.
  destruct ppst, x; reflexivity.
Qed.

Lemma PPState_mem_set_state upd (ppst : PPState.t TState.t Ev.t IIS.t) :
  PPState.mem (set PPState.state upd ppst) = PPState.mem ppst.
Proof.
  destruct ppst; reflexivity.
Qed.

Lemma PPState_mem_set_iis upd (ppst : PPState.t TState.t Ev.t IIS.t) :
  PPState.mem (set PPState.iis upd ppst) = PPState.mem ppst.
Proof.
  destruct ppst; reflexivity.
Qed.

Lemma materialize_tlbi_for_recipient_false_preserves_mem
    vpre tlbiev recipient ppst ppst' time :
  Exec.elem_of_results (ppst', (time, false))
    (materialize_tlbi_for_recipient vpre tlbiev recipient ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H.
  unfold materialize_tlbi_for_recipient in H.
  inv_exec_result; reflexivity.
Qed.

Definition run_tlbi_recipient_step_bool vpre tlbiev tid
    : (view * view) * bool → nat →
      Exec.t (PPState.t TState.t Ev.t IIS.t) string ((view * view) * bool) :=
  λ '((vself, vother), created_new_tlbi_events) recipient,
  '(time, is_new_tlbi_event) ←
    materialize_tlbi_for_recipient vpre tlbiev recipient;
  let vself := if decide (recipient = tid) then max vself time else vself in
  let vother := if decide (recipient = tid) then vother else max vother time in
  mret ((vself, vother), created_new_tlbi_events || is_new_tlbi_event).

Definition run_tlbi_recipients_bool vpre tlbiev tid recipients :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string ((view * view) * bool) :=
  foldlM (run_tlbi_recipient_step_bool vpre tlbiev tid)
    ((0%nat, 0%nat), false) recipients.

Lemma run_tlbi_recipients_true_not_false recipients vpre tlbiev tid
    vself0 vother0 ppst ppst' vself vother :
  Exec.elem_of_results (ppst', ((vself, vother), false))
    (foldlM (run_tlbi_recipient_step_bool vpre tlbiev tid)
       ((vself0, vother0), true) recipients ppst) →
  False.
Proof.
  revert vself0 vother0 ppst ppst' vself vother.
  induction recipients as [|recipient recipients IH];
    intros vself0 vother0 ppst ppst' vself vother Hrun; cbn in Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [_ Hret].
    inversion Hret; subst.
  - apply Exec.elem_of_bind_elim in Hrun as
      [pp_mid [[[vself_mid vother_mid] created_mid] [Hstep Htail]]].
    unfold run_tlbi_recipient_step_bool in Hstep.
    cbn in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as
      [pp_mat [[time is_new] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> Hret].
    inversion Hret; subst vself_mid vother_mid created_mid.
    eapply IH.
    exact Htail.
Qed.

Lemma run_tlbi_recipients_false_preserves_mem recipients vpre tlbiev tid
    vself0 vother0 ppst ppst' vself vother :
  Exec.elem_of_results (ppst', ((vself, vother), false))
    (foldlM (run_tlbi_recipient_step_bool vpre tlbiev tid)
       ((vself0, vother0), false) recipients ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  revert vself0 vother0 ppst ppst' vself vother.
  induction recipients as [|recipient recipients IH];
    intros vself0 vother0 ppst ppst' vself vother Hrun; cbn in Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [-> _].
    reflexivity.
  - apply Exec.elem_of_bind_elim in Hrun as
      [pp_mid [[[vself_mid vother_mid] created_mid] [Hstep Htail]]].
    assert (Hcreated_mid : created_mid = false).
    { destruct created_mid; [|reflexivity].
      exfalso.
      eapply run_tlbi_recipients_true_not_false.
      exact Htail. }
    unfold run_tlbi_recipient_step_bool in Hstep.
    cbn in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as
      [pp_mat [[time is_new] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> Hret].
    destruct is_new.
    { inversion Hret; subst created_mid.
      discriminate. }
    { inversion Hret; subst vself_mid vother_mid created_mid.
      transitivity (PPState.mem pp_mat).
      - eapply IH.
        exact Htail.
      - eapply materialize_tlbi_for_recipient_false_preserves_mem.
        exact Hmat. }
Qed.

Lemma run_tlbi_recipients_inline_false_preserves_mem
    recipients vpre tlbiev tid
    vself0 vother0 ppst ppst' vself vother :
  Exec.elem_of_results (ppst', ((vself, vother), false))
    (foldlM
       (λ '((vself, vother), created_new_tlbi_events) recipient,
          '(time, is_new_tlbi_event) ←
            materialize_tlbi_for_recipient vpre tlbiev recipient;
          let vself :=
            if decide (recipient = tid) then max vself time else vself in
          let vother :=
            if decide (recipient = tid) then vother else max vother time in
          mret ((vself, vother),
            created_new_tlbi_events || is_new_tlbi_event))
       ((vself0, vother0), false) recipients ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro Hrun.
  cbn in Hrun.
  eapply (run_tlbi_recipients_false_preserves_mem
    recipients vpre tlbiev tid vself0 vother0).
  unfold run_tlbi_recipient_step_bool.
  exact Hrun.
Qed.

Lemma run_tlbi_none_preserves_mem n_threads tid viio tlbi ppst ppst' :
  Exec.elem_of_results (ppst', None)
    (run_tlbi n_threads tid viio tlbi ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H.
  unfold run_tlbi in H.
  apply Exec.elem_of_bind_elim in H as
    [pp_regime [p_regime [Hregime H]]].
  apply Exec.elem_of_guard_or_inv in Hregime as ->.
  apply Exec.elem_of_bind_elim in H as
    [pp_ts [ts [Hget_ts H]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in H as
    [pp_iis [iis [Hget_iis H]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  set (vpre0 :=
    TState.vcse (PPState.state ppst) ⊔
    TState.vdsb (PPState.state ppst) ⊔
    IIS.strict (PPState.iis ppst) ⊔ viio ⊔
    TState.vspec (PPState.state ppst)) in *.
  apply Exec.elem_of_bind_elim in H as
    [pp_tlbiev [tlbiev [Htlbiev H]]].
  destruct (TLBIRecord_op (TLBIInfo_rec tlbi)) eqn:Hop; cbn in Htlbiev;
    try solve [inv_exec_result].
  all: apply Exec.elem_of_mret_inv in Htlbiev as [-> Htlbiev_ret];
    inversion Htlbiev_ret; subst tlbiev.
  all: set (recipients :=
    if decide (TLBIInfo_shareability tlbi = Shareability_NSH)
    then [tid] else seq 0 n_threads) in *.
  all: apply Exec.elem_of_bind_elim in H as
    [pp_rec [[[vself vother] created] [Hrec H]]].
  all: apply Exec.elem_of_bind_elim in H as
    [pp_state [[] [Hset_state H]]].
  all: apply Exec.elem_of_mset_inv in Hset_state as ->.
  all: apply Exec.elem_of_bind_elim in H as
    [pp_iis [[] [Hset_iis H]]].
  all: apply Exec.elem_of_mset_inv in Hset_iis as ->.
  all: apply Exec.elem_of_mret_inv in H as [Heq Hret].
  all: inversion Heq; subst ppst'.
  all: destruct created; cbn in Hret; inversion Hret.
  all: rewrite ?PPState_mem_set_iis, ?PPState_mem_set_state.
  all: eapply run_tlbi_recipients_inline_false_preserves_mem;
    exact Hrec.
Qed.

Lemma materialize_tlbi_for_recipient_promise_replay_one
    (bbm_param : BBM.param) tid initmem vpre tlbiev recipient
    ppst ppst' time :
  Exec.elem_of_results (ppst', (time, true))
    (materialize_tlbi_for_recipient vpre tlbiev recipient ppst) →
  let event := Ev.Tlbi tlbiev recipient in
  PPState.mem ppst' = event :: PPState.mem ppst ∧
  (vpre ≤ length (PPState.mem ppst))%nat ∧
  Exec.elem_of_results (ppst', (time, false))
    (materialize_tlbi_for_recipient vpre tlbiev recipient
       (Promising.promise_ppstate_event
          (VMPromising bbm_param) tid initmem event ppst)).
Proof.
  destruct ppst as [ts mem iis].
  cbn.
  intro Hrun.
  unfold materialize_tlbi_for_recipient in Hrun.
  set (event := Ev.Tlbi tlbiev recipient) in *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_mem [mem0 [Hget_mem Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_mem as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_pair [[time0 is_new] [Hmatch Hrun]]].
  destruct (Memory.fulfill event (TState.prom_tlbi ts) mem) as [tfulfilled|]
    eqn:Hfulfill.
  - cbn in Hmatch.
    rewrite Hfulfill in Hmatch.
    apply Exec.elem_of_mret_inv in Hmatch as [-> Hpair].
    inversion Hpair; subst is_new.
    cbn in Hrun.
    inv_exec_result.
  - cbn in Hmatch.
    rewrite Hfulfill in Hmatch.
    apply Exec.elem_of_bind_elim in Hmatch as
      [pp_prom [time_prom [Hpromise Hpair]]].
    apply Exec.elem_of_liftSt_inv in Hpromise as
      [mem1 [Hpp_prom Hpromise]].
    destruct (memory_promise_inv event mem mem1 time_prom Hpromise)
      as [-> Htime_prom].
    subst pp_prom.
    apply Exec.elem_of_mret_inv in Hpair as [-> Hpair].
    inversion Hpair; subst time0 is_new.
    subst time_prom.
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_guard [Hguard_prop [Hguard Hrun]]].
    pose proof Hguard_prop as Hvpre_lt.
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_promset [[] [Hpromset Hrun]]].
    apply Exec.elem_of_mset_inv in Hpromset as ->.
    apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
    inversion Heq; subst ppst'.
    inversion Hret; subst time.
    split; [reflexivity|].
    split; [cbn in Hvpre_lt; lia|].
    unfold Promising.promise_ppstate_event.
    unfold VMPromising.
    cbn.
    unfold emit_promise'.
    cbn.
    unfold materialize_tlbi_for_recipient.
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make
        (TState.promise_tlbi (length (event :: mem)) ts)
        (event :: mem) iis)
      (a := TState.promise_tlbi (length (event :: mem)) ts).
    { apply (Exec.elem_of_mget (E:=string)
        (PPState.Make
          (TState.promise_tlbi (length (event :: mem)) ts)
          (event :: mem) iis) PPState.state). }
    cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make
        (TState.promise_tlbi (length (event :: mem)) ts)
        (event :: mem) iis)
      (a := event :: mem).
    { apply (Exec.elem_of_mget (E:=string)
        (PPState.Make
          (TState.promise_tlbi (length (event :: mem)) ts)
          (event :: mem) iis) PPState.mem). }
    cbn.
    rewrite fulfill_after_TState_promise_tlbi by exact Hfulfill.
    eapply Exec.elem_of_bind_intro.
    { apply Exec.elem_of_mret. }
    cbn.
    eapply Exec.elem_of_bind_intro.
    { apply (elem_of_guard_discard_proof
        (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
        (P:=(vpre < length (event :: mem))%nat)
        (PPState.Make
          (TState.promise_tlbi (length (event :: mem)) ts)
          (event :: mem) iis)
        Hvpre_lt). }
    cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make
        (set TState.prom_tlbi
           (filter (λ t : view, (t : nat) ≠ length (event :: mem)))
           ts)
        (event :: mem) iis)
      (a := ()).
    { rewrite <- TState_filter_prom_tlbi_after_promise_tlbi.
      apply elem_of_unfolded_ppstate_mset_prom_tlbi. }
    cbn.
    apply Exec.elem_of_mret.
Qed.

Lemma materialize_tlbi_for_recipient_promise_unrelated_stable
    (bbm_param : BBM.param) tid initmem vpre tlbiev recipient
    extra ppst ppst' time :
  extra ≠ Ev.Tlbi tlbiev recipient →
  Exec.elem_of_results (ppst', (time, false))
    (materialize_tlbi_for_recipient vpre tlbiev recipient ppst) →
  Exec.elem_of_results
    (Promising.promise_ppstate_event
       (VMPromising bbm_param) tid initmem extra ppst', (time, false))
    (materialize_tlbi_for_recipient vpre tlbiev recipient
       (Promising.promise_ppstate_event
          (VMPromising bbm_param) tid initmem extra ppst)).
Proof.
  destruct ppst as [ts mem iis].
  cbn.
  intros Hne Hrun.
  unfold materialize_tlbi_for_recipient in Hrun.
  set (event := Ev.Tlbi tlbiev recipient) in *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_mem [mem0 [Hget_mem Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_mem as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_pair [[time0 is_new] [Hmatch Hrun]]].
  destruct (Memory.fulfill event (TState.prom_tlbi ts) mem) as [tfulfilled|]
    eqn:Hfulfill.
  - cbn in Hmatch.
    rewrite Hfulfill in Hmatch.
    apply Exec.elem_of_mret_inv in Hmatch as [-> Hpair].
    inversion Hpair; subst time0 is_new.
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_guard [Hguard_prop [Hguard Hrun]]].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_promset [[] [Hpromset Hrun]]].
    apply Exec.elem_of_mset_inv in Hpromset as ->.
    apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
    inversion Heq; subst ppst'.
    inversion Hret; subst time.
    unfold Promising.promise_ppstate_event.
    unfold VMPromising.
    cbn.
    unfold emit_promise'.
    cbn.
    unfold materialize_tlbi_for_recipient.
    set (p := length (extra :: mem)).
    assert (Htime_le : (tfulfilled ≤ length mem)%nat).
    { apply memory_fulfill_some_lookup in Hfulfill.
      eapply prommemory_lookup_some_le.
      exact Hfulfill. }
    assert (Hp_ne : (p : nat) ≠ (tfulfilled : nat)).
    { subst p.
      cbn.
      lia. }
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make
        (TState_promise_event extra p ts) (extra :: mem) iis)
      (a := TState_promise_event extra p ts).
    { apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event extra p ts)
          (extra :: mem) iis) PPState.state). }
    cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make
        (TState_promise_event extra p ts) (extra :: mem) iis)
      (a := extra :: mem).
    { apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState_promise_event extra p ts)
          (extra :: mem) iis) PPState.mem). }
    cbn.
    destruct extra as [msg_extra|tlbi_extra recipient_extra].
    + cbn.
      rewrite memory_fulfill_cons_mem_unrelated by exact Hne.
      rewrite Hfulfill.
      eapply Exec.elem_of_bind_intro.
      * apply Exec.elem_of_mret.
        * cbn.
          eapply Exec.elem_of_bind_intro.
          -- apply (elem_of_guard_discard_proof
               (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
               (P:=(vpre < tfulfilled)%nat)
               (PPState.Make
                 (TState.promise_write p ts)
                 (Ev.Msg msg_extra :: mem) iis)
               Hguard_prop).
          -- cbn.
             eapply Exec.elem_of_bind_intro with
             (st' := PPState.Make
               (TState_promise_event (Ev.Msg msg_extra) p
                 (set TState.prom_tlbi
                    (filter (λ t : view, (t : nat) ≠ (tfulfilled : nat)))
                    ts))
               (Ev.Msg msg_extra :: mem) iis)
             (a := ()).
           ++ rewrite <-
                (TState_filter_prom_tlbi_after_other_promise_event
                   (Ev.Msg msg_extra) p tfulfilled ts Hp_ne).
              apply elem_of_unfolded_ppstate_mset_prom_tlbi.
           ++ cbn.
              apply Exec.elem_of_mret.
    + cbn.
      rewrite memory_fulfill_cons_unrelated by exact Hne.
      rewrite Hfulfill.
      eapply Exec.elem_of_bind_intro.
      * apply Exec.elem_of_mret.
        * cbn.
          eapply Exec.elem_of_bind_intro.
          -- apply (elem_of_guard_discard_proof
               (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
               (P:=(vpre < tfulfilled)%nat)
               (PPState.Make
                 (TState.promise_tlbi p ts)
                 (Ev.Tlbi tlbi_extra recipient_extra :: mem) iis)
               Hguard_prop).
          -- cbn.
             eapply Exec.elem_of_bind_intro with
             (st' := PPState.Make
               (TState_promise_event (Ev.Tlbi tlbi_extra recipient_extra) p
                 (set TState.prom_tlbi
                    (filter (λ t : view, (t : nat) ≠ (tfulfilled : nat)))
                    ts))
               (Ev.Tlbi tlbi_extra recipient_extra :: mem) iis)
             (a := ()).
           ++ rewrite <-
                (TState_filter_prom_tlbi_after_other_promise_event
                   (Ev.Tlbi tlbi_extra recipient_extra) p tfulfilled ts Hp_ne).
              apply elem_of_unfolded_ppstate_mset_prom_tlbi.
           ++ cbn.
              apply Exec.elem_of_mret.
  - cbn in Hmatch.
    rewrite Hfulfill in Hmatch.
    apply Exec.elem_of_bind_elim in Hmatch as
      [pp_prom [time_prom [Hpromise Hpair]]].
    apply Exec.elem_of_liftSt_inv in Hpromise as
      [mem1 [Hpp_prom Hpromise]].
    destruct (memory_promise_inv event mem mem1 time_prom)
      as [_ Htime_prom]; [exact Hpromise|].
    subst pp_prom.
    apply Exec.elem_of_mret_inv in Hpair as [-> Hpair].
    inversion Hpair; subst is_new.
    cbn in Hrun.
    inv_exec_result.
Qed.

Lemma VMPromising_promise_ppstate_events_app
    (bbm_param : BBM.param) tid initmem
    (events1 events2 : list Ev.t) ppst :
  Promising.promise_ppstate_events (VMPromising bbm_param) tid initmem
    (events1 ++ events2) ppst =
  Promising.promise_ppstate_events (VMPromising bbm_param) tid initmem
    events1
    (Promising.promise_ppstate_events (VMPromising bbm_param) tid initmem
       events2 ppst).
Proof.
  induction events1 as [|event events1 IH]; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma VMPromising_promise_ppstate_events_mem
    (bbm_param : BBM.param) tid initmem (events : list Ev.t) ppst :
  PPState.mem
    (Promising.promise_ppstate_events (VMPromising bbm_param) tid initmem
       events ppst) =
  events ++ PPState.mem ppst.
Proof.
  induction events as [|event events IH]; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma VMPromising_promise_ppstate_events_iis
    (bbm_param : BBM.param) tid initmem (events : list Ev.t) ppst :
  PPState.iis
    (Promising.promise_ppstate_events (VMPromising bbm_param) tid initmem
       events ppst) =
  PPState.iis ppst.
Proof.
  induction events as [|event events IH]; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma emit_promise_vcse tid initmem mem event ts :
  TState.vcse (emit_promise' tid initmem mem event ts) =
  TState.vcse ts.
Proof.
  unfold emit_promise'.
  destruct event; destruct ts;
    unfold TState.promise_write, TState.promise_tlbi;
    cbn;
    reflexivity.
Qed.

Lemma emit_promise_vdsb tid initmem mem event ts :
  TState.vdsb (emit_promise' tid initmem mem event ts) =
  TState.vdsb ts.
Proof.
  unfold emit_promise'.
  destruct event; destruct ts;
    unfold TState.promise_write, TState.promise_tlbi;
    cbn;
    reflexivity.
Qed.

Lemma emit_promise_vspec tid initmem mem event ts :
  TState.vspec (emit_promise' tid initmem mem event ts) =
  TState.vspec ts.
Proof.
  unfold emit_promise'.
  destruct event; destruct ts;
    unfold TState.promise_write, TState.promise_tlbi;
    cbn;
    reflexivity.
Qed.

Lemma VMPromising_promise_ppstate_events_vcse
    (bbm_param : BBM.param) tid initmem (events : list Ev.t) ppst :
  TState.vcse
    (PPState.state
       (Promising.promise_ppstate_events (VMPromising bbm_param) tid initmem
          events ppst)) =
  TState.vcse (PPState.state ppst).
Proof.
  induction events as [|event events IH]; cbn.
  - reflexivity.
  - rewrite <- IH.
    unfold emit_promise'.
    remember (Promising.promise_ppstate_events
      (VMPromising bbm_param) tid initmem events ppst) as pp_tail.
    destruct pp_tail as [ts_tail mem_tail iis_tail].
    destruct ts_tail.
    destruct event;
      unfold TState.promise_write, TState.promise_tlbi;
      cbn;
      reflexivity.
Qed.

Lemma VMPromising_promise_ppstate_events_vdsb
    (bbm_param : BBM.param) tid initmem (events : list Ev.t) ppst :
  TState.vdsb
    (PPState.state
       (Promising.promise_ppstate_events (VMPromising bbm_param) tid initmem
          events ppst)) =
  TState.vdsb (PPState.state ppst).
Proof.
  induction events as [|event events IH]; cbn.
  - reflexivity.
  - rewrite <- IH.
    unfold emit_promise'.
    remember (Promising.promise_ppstate_events
      (VMPromising bbm_param) tid initmem events ppst) as pp_tail.
    destruct pp_tail as [ts_tail mem_tail iis_tail].
    destruct ts_tail.
    destruct event;
      unfold TState.promise_write, TState.promise_tlbi;
      cbn;
      reflexivity.
Qed.

Lemma VMPromising_promise_ppstate_events_vspec
    (bbm_param : BBM.param) tid initmem (events : list Ev.t) ppst :
  TState.vspec
    (PPState.state
       (Promising.promise_ppstate_events (VMPromising bbm_param) tid initmem
          events ppst)) =
  TState.vspec (PPState.state ppst).
Proof.
  induction events as [|event events IH]; cbn.
  - reflexivity.
  - rewrite <- IH.
    unfold emit_promise'.
    remember (Promising.promise_ppstate_events
      (VMPromising bbm_param) tid initmem events ppst) as pp_tail.
    destruct pp_tail as [ts_tail mem_tail iis_tail].
    destruct ts_tail.
    destruct event;
      unfold TState.promise_write, TState.promise_tlbi;
      cbn;
      reflexivity.
Qed.

Lemma materialize_tlbi_for_recipient_promise_events_stable
    (bbm_param : BBM.param) tid initmem vpre tlbiev recipient
    (events : list Ev.t) ppst ppst' time :
  (∀ extra, extra ∈ events → extra ≠ Ev.Tlbi tlbiev recipient) →
  Exec.elem_of_results (ppst', (time, false))
    (materialize_tlbi_for_recipient vpre tlbiev recipient ppst) →
  Exec.elem_of_results
    (Promising.promise_ppstate_events
       (VMPromising bbm_param) tid initmem events ppst', (time, false))
    (materialize_tlbi_for_recipient vpre tlbiev recipient
       (Promising.promise_ppstate_events
          (VMPromising bbm_param) tid initmem events ppst)).
Proof.
  revert ppst ppst' time.
  induction events as [|extra events IH]; intros ppst ppst' time Hall Hrun.
  - cbn.
    exact Hrun.
  - cbn.
    eapply materialize_tlbi_for_recipient_promise_unrelated_stable.
    + apply Hall.
      apply elem_of_cons.
      left.
      reflexivity.
    + eapply IH.
      * intros extra' Hextra'.
        apply Hall.
        apply elem_of_cons.
        right.
        exact Hextra'.
      * exact Hrun.
Qed.

Lemma materialize_tlbi_for_recipient_promise_replay_events
    (bbm_param : BBM.param) tid initmem vpre tlbiev recipient
    (events : list Ev.t) ppst ppst' time :
  (∀ extra, extra ∈ events → extra ≠ Ev.Tlbi tlbiev recipient) →
  Exec.elem_of_results (ppst', (time, true))
    (materialize_tlbi_for_recipient vpre tlbiev recipient ppst) →
  let event := Ev.Tlbi tlbiev recipient in
  PPState.mem ppst' = event :: PPState.mem ppst ∧
  (vpre ≤ length (PPState.mem ppst))%nat ∧
  Exec.elem_of_results
    (Promising.promise_ppstate_events
       (VMPromising bbm_param) tid initmem events ppst', (time, false))
    (materialize_tlbi_for_recipient vpre tlbiev recipient
       (Promising.promise_ppstate_events
          (VMPromising bbm_param) tid initmem (events ++ [event]) ppst)).
Proof.
  intros Hall Hrun.
  destruct (materialize_tlbi_for_recipient_promise_replay_one
    bbm_param tid initmem vpre tlbiev recipient ppst ppst' time Hrun)
    as [Hmem [Hle Hreplay]].
  split; [exact Hmem|].
  split; [exact Hle|].
  rewrite VMPromising_promise_ppstate_events_app.
  cbn.
  eapply materialize_tlbi_for_recipient_promise_events_stable.
  - exact Hall.
  - exact Hreplay.
Qed.

Lemma run_tlbi_recipients_bool_promise_replay_aux
    (bbm_param : BBM.param) tid initmem vpre tlbiev recipients
    ppst ppst' vself0 vother0 vself vother
    (created0 final_created : bool) :
  NoDup recipients →
  Exec.elem_of_results (ppst', ((vself, vother), final_created))
    (foldlM (run_tlbi_recipient_step_bool vpre tlbiev tid)
       ((vself0, vother0), created0) recipients ppst) →
  ∃ events,
    (events = [] → final_created = created0) ∧
    PPState.mem ppst' = events ++ PPState.mem ppst ∧
    (∀ event, event ∈ events →
      ∃ recipient, recipient ∈ recipients ∧ event = Ev.Tlbi tlbiev recipient) ∧
    (events ≠ [] → (vpre ≤ length (PPState.mem ppst))%nat) ∧
    Exec.elem_of_results
      (ppst', ((vself, vother), false))
      (foldlM (run_tlbi_recipient_step_bool vpre tlbiev tid)
         ((vself0, vother0), false) recipients
         (Promising.promise_ppstate_events
            (VMPromising bbm_param) tid initmem events ppst)).
Proof.
  revert ppst ppst' vself0 vother0 vself vother created0 final_created.
  induction recipients as [|recipient recipients IH];
    intros ppst ppst' vself0 vother0 vself vother
      created0 final_created Hnodup Hrun; cbn in Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [-> Hret].
    inversion Hret; subst vself vother final_created.
    exists [].
    split; [intros _; reflexivity|].
    split; [reflexivity|].
    split.
    + intros event Hevent.
      inversion Hevent.
    + split.
      * intros Hnonempty.
        contradiction.
      * cbn.
        apply Exec.elem_of_mret.
  - inversion Hnodup as [|recipient' recipients' Hnotin Hnodup_tail].
    subst recipient' recipients'.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_mid [[[vself_mid vother_mid] created_mid] [Hstep Htail]]].
    unfold run_tlbi_recipient_step_bool in Hstep.
    cbn in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as
      [pp_mat [[time is_new] [Hmat Hstep_ret]]].
    apply Exec.elem_of_mret_inv in Hstep_ret as [-> Hstep_ret].
    destruct is_new eqn:His_new.
    + replace (created0 || true) with true in Hstep_ret
        by (destruct created0; reflexivity).
      inversion Hstep_ret; subst vself_mid vother_mid created_mid.
      destruct (IH pp_mat ppst'
        (if decide (recipient = tid) then max vself0 time else vself0)
        (if decide (recipient = tid) then vother0 else max vother0 time)
        vself vother true final_created Hnodup_tail Htail) as
        [tail_events
          [Hempty_tail [Hmem_tail [Hall_tail [Hle_tail Hreplay_tail]]]]].
      assert (Htail_unrelated :
        ∀ extra, extra ∈ tail_events → extra ≠ Ev.Tlbi tlbiev recipient).
      { intros extra Hextra Heq.
        destruct (Hall_tail extra Hextra) as
          [recipient_tail [Hrecipient_tail ->]].
        inversion Heq; subst.
        contradiction. }
      destruct (materialize_tlbi_for_recipient_promise_replay_events
        bbm_param tid initmem vpre tlbiev recipient tail_events
        ppst pp_mat time Htail_unrelated Hmat) as
        [Hmem_step [Hle_step Hmat_replay]].
      exists (tail_events ++ [Ev.Tlbi tlbiev recipient]).
      split.
      * intro Hempty.
        destruct tail_events; inversion Hempty.
      * split.
        -- rewrite Hmem_tail.
           rewrite Hmem_step.
           rewrite <- app_assoc.
           reflexivity.
        -- split.
           ++ intros event Hevent.
              apply elem_of_app in Hevent as [Hevent|Hevent].
              ** destruct (Hall_tail event Hevent) as
                   [recipient_tail [Hrecipient_tail Heq]].
                 exists recipient_tail.
                 split; [|exact Heq].
                 apply elem_of_cons.
                 right.
                 exact Hrecipient_tail.
              ** apply elem_of_list_singleton in Hevent.
                 subst event.
                 exists recipient.
                 split.
                 --- apply elem_of_cons.
                     left.
                     reflexivity.
                 --- reflexivity.
           ++ split.
              ** intros _.
                 exact Hle_step.
              ** eapply Exec.elem_of_bind_intro.
                 --- unfold run_tlbi_recipient_step_bool.
                     cbn.
                     eapply Exec.elem_of_bind_intro.
                     +++ exact Hmat_replay.
                     +++ cbn.
                         apply Exec.elem_of_mret.
                 --- cbn.
                     exact Hreplay_tail.
    + replace (created0 || false) with created0 in Hstep_ret
        by (destruct created0; reflexivity).
      inversion Hstep_ret; subst vself_mid vother_mid created_mid.
      destruct (IH pp_mat ppst'
        (if decide (recipient = tid) then max vself0 time else vself0)
        (if decide (recipient = tid) then vother0 else max vother0 time)
        vself vother created0 final_created
        Hnodup_tail Htail) as
        [tail_events
          [Hempty_tail [Hmem_tail [Hall_tail [Hle_tail Hreplay_tail]]]]].
      assert (Htail_unrelated :
        ∀ extra, extra ∈ tail_events → extra ≠ Ev.Tlbi tlbiev recipient).
      { intros extra Hextra Heq.
        destruct (Hall_tail extra Hextra) as
          [recipient_tail [Hrecipient_tail ->]].
        inversion Heq; subst.
        contradiction. }
      pose proof (materialize_tlbi_for_recipient_false_preserves_mem
        vpre tlbiev recipient ppst pp_mat time Hmat) as Hmem_step.
      pose proof
        (materialize_tlbi_for_recipient_promise_events_stable
          bbm_param tid initmem vpre tlbiev recipient tail_events
          ppst pp_mat time Htail_unrelated Hmat) as Hmat_replay.
      exists tail_events.
      split; [exact Hempty_tail|].
      split.
      * rewrite Hmem_tail.
        rewrite Hmem_step.
        reflexivity.
      * split.
        -- intros event Hevent.
           destruct (Hall_tail event Hevent) as
             [recipient_tail [Hrecipient_tail Heq]].
           exists recipient_tail.
           split; [|exact Heq].
           apply elem_of_cons.
           right.
           exact Hrecipient_tail.
        -- split.
           ++ intros Hnonempty.
              rewrite <- Hmem_step.
              apply Hle_tail.
              exact Hnonempty.
           ++ eapply Exec.elem_of_bind_intro.
              ** unfold run_tlbi_recipient_step_bool.
                 cbn.
                 eapply Exec.elem_of_bind_intro.
                 --- exact Hmat_replay.
                 --- cbn.
                     apply Exec.elem_of_mret.
              ** cbn.
                 exact Hreplay_tail.
Qed.

Lemma run_tlbi_recipients_bool_promise_replay
    (bbm_param : BBM.param) tid initmem vpre tlbiev recipients
    ppst ppst' vself vother :
  NoDup recipients →
  Exec.elem_of_results (ppst', ((vself, vother), true))
    (run_tlbi_recipients_bool vpre tlbiev tid recipients ppst) →
  ∃ events,
  events ≠ [] ∧
  PPState.mem ppst' = events ++ PPState.mem ppst ∧
  (∀ event, event ∈ events →
    ∃ recipient, recipient ∈ recipients ∧ event = Ev.Tlbi tlbiev recipient) ∧
  (vpre ≤ length (PPState.mem ppst))%nat ∧
  Exec.elem_of_results (ppst', ((vself, vother), false))
    (run_tlbi_recipients_bool vpre tlbiev tid recipients
       (Promising.promise_ppstate_events
          (VMPromising bbm_param) tid initmem events ppst)).
Proof.
  intros Hnodup Hrun.
  unfold run_tlbi_recipients_bool in Hrun |- *.
  destruct (run_tlbi_recipients_bool_promise_replay_aux
    bbm_param tid initmem vpre tlbiev recipients ppst ppst'
    0%nat 0%nat vself vother false true Hnodup Hrun) as
    [events [Hempty [Hmem [Hall [Hle Hreplay]]]]].
  exists events.
  assert (Hnonempty : events ≠ []).
  { intro Hnil.
    specialize (Hempty Hnil).
    discriminate. }
  split; [exact Hnonempty|].
  split; [exact Hmem|].
  split; [exact Hall|].
  split.
  - apply Hle.
    exact Hnonempty.
  - exact Hreplay.
Qed.

Lemma Exec_mapM_preserves_state {St A B}
    (f : A → Exec.t St string B) l st st' bs :
  (∀ a st0 st1 b,
    Exec.elem_of_results (st1, b) (f a st0) →
    st1 = st0) →
  Exec.elem_of_results (st', bs) ((mapM f l : Exec.t St string (list B)) st) →
  st' = st.
Proof.
  intros Hf Hrun.
  revert st st' bs Hrun.
  induction l as [|a l IH]; intros st st' bs Hrun; cbn in Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [-> _].
    reflexivity.
  - apply Exec.elem_of_bind_elim in Hrun as
      [st_a [b [Ha Hrun]]].
    apply Exec.elem_of_bind_elim in Hrun as
      [st_l [bs' [Hl Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    transitivity st_a.
    + eapply IH.
      exact Hl.
    + eapply Hf.
      exact Ha.
Qed.

Lemma trans_res_map_preserves_mem {A}
    (f : A → Exec.t (PPState.t TState.t Ev.t IIS.t) string
           (IIS.TransRes.t * option nat))
    entries ppst ppst' res :
  (∀ entry ppst0 ppst1 r,
    Exec.elem_of_results (ppst1, r) (f entry ppst0) →
    ppst1 = ppst0) →
  Exec.elem_of_results (ppst', res)
    ((mapM f entries :
        Exec.t (PPState.t TState.t Ev.t IIS.t) string
          (list (IIS.TransRes.t * option nat))) ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intros Hf Hrun.
  enough (ppst' = ppst) by congruence.
  eapply Exec_mapM_preserves_state; eauto.
Qed.

Lemma trans_valid_res_preserves_mem (ttbr : reg) (va : bv 64)
    (va_addr : address) (asid : bv 16)
    (is_ifetch : bool)
    (entries : list (bv 64 * list (bv 64) * nat * nat * option nat))
    (ppst ppst' : PPState.t TState.t Ev.t IIS.t) res :
  Exec.elem_of_results (ppst', res)
    ((for @{Exec.t (PPState.t TState.t Ev.t IIS.t) string}
        (val_ttbr, path, start_time, end_time, ti) in entries do
        val_ttbr ← othrow
          "TTBR value type does not match with the value from the translation"
          (val_to_regval ttbr val_ttbr);
        let root := (Some (existT ttbr val_ttbr)) in
        let ti := if is_ifetch then None else ti in
        mret $
          (IIS.TransRes.make
            (va_to_vpn va) va_addr asid start_time end_time root path, ti)
      end) ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  revert ppst ppst' res.
  induction entries as [|entry entries IH]; intros ppst ppst' res Hrun;
    cbn in Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [-> _].
    reflexivity.
  - destruct entry as [[[[val_ttbr path] start_time] end_time] ti].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_body [res_body [Hbody Htail]]].
    assert (Hbody_state : pp_body = ppst).
    { unfold othrow in Hbody.
      inv_exec_result; reflexivity. }
    subst pp_body.
    apply Exec.elem_of_bind_elim in Htail as
      [pp_tail [res_tail [Htail Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply IH.
    exact Htail.
Qed.

Lemma trans_valid_res_ifetch_preserves_mem (ttbr : reg) (va : bv 64)
    (va_addr : address) (asid : bv 16)
    (entries : list (bv 64 * list (bv 64) * nat * nat * option nat))
    (ppst ppst' : PPState.t TState.t Ev.t IIS.t) res :
  Exec.elem_of_results (ppst', res)
    ((for @{Exec.t (PPState.t TState.t Ev.t IIS.t) string}
        (val_ttbr, path, start_time, end_time, _) in entries do
        val_ttbr ← othrow
          "TTBR value type does not match with the value from the translation"
          (val_to_regval ttbr val_ttbr);
        let root := (Some (existT ttbr val_ttbr)) in
        mret $
          (IIS.TransRes.make
            (va_to_vpn va) va_addr asid start_time end_time root path,
           (None : option nat))
      end) ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  revert ppst ppst' res.
  induction entries as [|entry entries IH]; intros ppst ppst' res Hrun;
    cbn in Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [-> _].
    reflexivity.
  - destruct entry as [[[[val_ttbr path] start_time] end_time] ti].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_body [res_body [Hbody Htail]]].
    assert (Hbody_state : pp_body = ppst).
    { unfold othrow in Hbody.
      inv_exec_result; reflexivity. }
    subst pp_body.
    apply Exec.elem_of_bind_elim in Htail as
      [pp_tail [res_tail [Htail Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply IH.
    exact Htail.
Qed.

Lemma trans_invalid_res_preserves_mem (ttbr : reg) (va : bv 64)
    (va_addr : address) (asid : bv 16)
    (entries : list (bv 64 * list (bv 64) * nat * nat * option nat))
    (ppst ppst' : PPState.t TState.t Ev.t IIS.t) res :
  Exec.elem_of_results (ppst', res)
    ((for @{Exec.t (PPState.t TState.t Ev.t IIS.t) string}
        (val_ttbr, path, start_time, end_time, ti) in entries do
        val_ttbr ← othrow
          "TTBR value type does not match with the value from the translation"
          (val_to_regval ttbr val_ttbr);
        let root := (Some (existT ttbr val_ttbr)) in
        mret $
          (IIS.TransRes.make
            (va_to_vpn va) va_addr asid start_time end_time root path, ti)
      end) ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  revert ppst ppst' res.
  induction entries as [|entry entries IH]; intros ppst ppst' res Hrun;
    cbn in Hrun.
  - apply Exec.elem_of_mret_inv in Hrun as [-> _].
    reflexivity.
  - destruct entry as [[[[val_ttbr path] start_time] end_time] ti].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_body [res_body [Hbody Htail]]].
    assert (Hbody_state : pp_body = ppst).
    { unfold othrow in Hbody.
      inv_exec_result; reflexivity. }
    subst pp_body.
    apply Exec.elem_of_bind_elim in Htail as
      [pp_tail [res_tail [Htail Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply IH.
    exact Htail.
Qed.

Lemma run_trans_start_preserves_mem trans_start tid initmem ppst ppst' u :
  Exec.elem_of_results (ppst', u)
    (run_trans_start trans_start tid initmem ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H.
  unfold run_trans_start in H.
  inv_exec_result;
    rewrite ?PPState_mem_set_iis;
    try reflexivity.
  all: repeat match goal with
  | Hmap : Exec.elem_of_results _ _ |- _ =>
      progress (first
        [eapply trans_valid_res_ifetch_preserves_mem in Hmap
        |eapply trans_invalid_res_preserves_mem in Hmap
        |eapply trans_valid_res_preserves_mem in Hmap])
  end.
  all: rewrite ?PPState_mem_set_iis, ?PPState_mem_set_state,
      ?PPState_mem_set_state_read in *.
  all: repeat match goal with
  | Hmem : PPState.mem ?st1 = PPState.mem ?st0
    |- context [PPState.mem ?st1] =>
      rewrite Hmem
  end.
  all: try congruence; try reflexivity.
Qed.

Lemma run_outcome_none_preserves_mem n_threads tid initmem out ppst ppst'
    (eret : eff_ret out) :
  Exec.elem_of_results (ppst', (eret, None))
    (run_outcome n_threads tid initmem out ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H.
  funelim (run_outcome n_threads tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: inv_exec_result; try solve [destruct ppst; reflexivity].
  all: try solve [eapply run_reg_write_preserves_mem; eauto].
  all: try solve [eapply read_mem_explicit_preserves_mem; eauto].
  all: try solve [eapply read_pte_preserves_mem; eauto].
  all: try solve [eapply write_mem_none_preserves_mem; eauto].
  all: try solve [eapply run_tlbi_none_preserves_mem; eauto].
  all: try solve [eapply run_trans_start_preserves_mem; eauto].
  all: try solve [rewrite PPState_mem_setv_state_iis; reflexivity].
  all: cbn; reflexivity.
Qed.

Lemma run_outcome_memwrite_promise_replay_one n_threads tid initmem
    macc addr addr_space size val tags ppst ppst' vpre :
  Exec.elem_of_results (ppst', (Ok (), Some vpre))
    (run_outcome n_threads tid initmem
       (MemWrite (MemReq.make macc addr addr_space size 0) val tags) ppst) →
  ∃ event,
    PPState.mem ppst' = event :: PPState.mem ppst ∧
    Ev.tid event = tid ∧
    (vpre ≤ length (PPState.mem ppst))%nat ∧
    Exec.elem_of_results (ppst', (Ok (), None))
      (run_outcome n_threads tid initmem
         (MemWrite (MemReq.make macc addr addr_space size 0) val tags)
         (PPState.Make
            (emit_promise' tid initmem
               (event :: PPState.mem ppst) event (PPState.state ppst))
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
  exists (Ev.Msg (Msg.make size tid addr val)).
  split; [exact Hmem|].
  split; [reflexivity|].
  split; [exact Hle|].
  simp run_outcome.
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
    (P:=addr_space = PAS_NonSecure)
    (PPState.Make
       (emit_promise' tid initmem
          (Ev.Msg (Msg.make size tid addr val) :: PPState.mem ppst)
          (Ev.Msg (Msg.make size tid addr val))
          (PPState.state ppst))
       (Ev.Msg (Msg.make size tid addr val) :: PPState.mem ppst)
       (PPState.iis ppst))
    "Access outside Non-Secure" Haddr_space) as [p_ns' Hns'].
  eapply Exec.elem_of_bind_intro.
  - exact Hns'.
  - cbn.
    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
      (P:=is_explicit macc)
      (PPState.Make
         (emit_promise' tid initmem
            (Ev.Msg (Msg.make size tid addr val) :: PPState.mem ppst)
            (Ev.Msg (Msg.make size tid addr val))
            (PPState.state ppst))
         (Ev.Msg (Msg.make size tid addr val) :: PPState.mem ppst)
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

Lemma run_tlbi_promise_replay_events
    (bbm_param : BBM.param) n_threads tid initmem viio tlbi
    ppst ppst' vpre_ret :
  Exec.elem_of_results (ppst', Some vpre_ret)
    (run_tlbi n_threads tid viio tlbi ppst) →
  ∃ events,
    events ≠ [] ∧
    PPState.mem ppst' = events ++ PPState.mem ppst ∧
    (∀ event, event ∈ events → Ev.tid event = tid) ∧
    (vpre_ret ≤ length (PPState.mem ppst))%nat ∧
    Exec.elem_of_results (ppst', None)
      (run_tlbi n_threads tid viio tlbi
         (Promising.promise_ppstate_events
            (VMPromising bbm_param) tid initmem events ppst)).
Proof.
  intro Hrun.
  unfold run_tlbi in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_regime [p_regime [Hregime Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hregime) as Hregime_prop.
  apply Exec.elem_of_guard_or_inv in Hregime as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_iis [iis [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  set (vpre0 :=
    TState.vcse (PPState.state ppst) ⊔
    TState.vdsb (PPState.state ppst) ⊔
    IIS.strict (PPState.iis ppst) ⊔ viio ⊔
    TState.vspec (PPState.state ppst)) in *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_tlbiev [tlbiev [Htlbiev Hrun]]].
  destruct (TLBIRecord_op (TLBIInfo_rec tlbi)) eqn:Hop; cbn in Htlbiev;
    try solve [inv_exec_result].
  all: apply Exec.elem_of_mret_inv in Htlbiev as [-> Htlbiev_ret];
    inversion Htlbiev_ret; subst tlbiev.
  all: set (recipients :=
    if decide (TLBIInfo_shareability tlbi = Shareability_NSH)
    then [tid] else seq 0 n_threads) in *.
  all: apply Exec.elem_of_bind_elim in Hrun as
    [pp_rec [[[vself vother] created] [Hrec Hrun]]].
  all: apply Exec.elem_of_bind_elim in Hrun as
    [pp_state [[] [Hset_state Hrun]]].
  all: apply Exec.elem_of_mset_inv in Hset_state as ->.
  all: apply Exec.elem_of_bind_elim in Hrun as
    [pp_iis [[] [Hset_iis Hrun]]].
  all: apply Exec.elem_of_mset_inv in Hset_iis as ->.
  all: apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
  all: inversion Heq; subst ppst'.
  all: destruct created eqn:Hcreated;
    cbn in Hret; inversion Hret; subst vpre_ret.
  all: assert (Hnodup : NoDup recipients).
  all: try (subst recipients;
    destruct (decide (TLBIInfo_shareability tlbi = Shareability_NSH));
    [constructor; [intro Hin; inversion Hin|constructor]
    |apply NoDup_seq]).
  all: destruct (run_tlbi_recipients_bool_promise_replay
    bbm_param tid initmem vpre0 _ recipients ppst pp_rec
    vself vother Hnodup Hrec) as
    [events [Hnonempty [Hmem [Hall [Hle Hrec_replay]]]]].
  all: exists events.
  all: split; [exact Hnonempty|].
  all: split.
  all: try (rewrite ?PPState_mem_set_iis, ?PPState_mem_set_state; exact Hmem).
  all: split.
  all: try (intros event' Hevent';
    destruct (Hall event' Hevent') as [recipient [Hrecipient ->]];
    cbn; reflexivity).
  all: split; [exact Hle|].
  all: unfold run_tlbi.
  all: destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Ev.t IIS.t) (E:=string)
    (P:=TLBIRecord_regime (TLBIInfo_rec tlbi) = Regime_EL10)
    (Promising.promise_ppstate_events
       (VMPromising bbm_param) tid initmem events ppst)
    "TLBIs in other regimes than EL10 are unsupported" Hregime_prop)
    as [p_regime' Hregime'].
  all: eapply Exec.elem_of_bind_intro; [exact Hregime'|cbn].
  all: eapply Exec.elem_of_bind_intro with
    (a := PPState.state
      (Promising.promise_ppstate_events
         (VMPromising bbm_param) tid initmem events ppst)).
  all: try (apply (Exec.elem_of_mget (E:=string)
    (Promising.promise_ppstate_events
       (VMPromising bbm_param) tid initmem events ppst)
    PPState.state)).
  all: cbn.
  all: eapply Exec.elem_of_bind_intro with
    (a := PPState.iis
      (Promising.promise_ppstate_events
         (VMPromising bbm_param) tid initmem events ppst)).
  all: try (apply (Exec.elem_of_mget (E:=string)
    (Promising.promise_ppstate_events
       (VMPromising bbm_param) tid initmem events ppst)
    PPState.iis)).
  all: cbn.
  all: fold (Promising.promise_ppstate_events
    (VMPromising bbm_param) tid initmem events ppst).
  all: rewrite ?emit_promise_vcse, ?emit_promise_vdsb, ?emit_promise_vspec.
  all: rewrite ?VMPromising_promise_ppstate_events_vcse,
    ?VMPromising_promise_ppstate_events_vdsb,
    ?VMPromising_promise_ppstate_events_vspec,
    ?VMPromising_promise_ppstate_events_iis.
  all: rewrite Hop.
  all: cbn.
  all: eapply Exec.elem_of_bind_intro.
  all: try apply Exec.elem_of_mret.
  all: cbn.
  all: fold recipients.
  all: eapply Exec.elem_of_bind_intro; [exact Hrec_replay|cbn].
  all: eapply Exec.elem_of_bind_intro.
  all: try apply Exec.elem_of_mset.
  all: cbn.
  all: eapply Exec.elem_of_bind_intro.
  all: try apply Exec.elem_of_mset.
  all: cbn.
  all: apply Exec.elem_of_mret.
Qed.

Lemma run_outcome_tlbop_promise_replay_events
    (bbm_param : BBM.param) n_threads tid initmem tlbi
    ppst ppst' vpre :
  Exec.elem_of_results (ppst', ((), Some vpre))
    (run_outcome n_threads tid initmem (TlbOp tlbi) ppst) →
  ∃ events,
    events ≠ [] ∧
    PPState.mem ppst' = events ++ PPState.mem ppst ∧
    (∀ event, event ∈ events → Ev.tid event = tid) ∧
    (vpre ≤ length (PPState.mem ppst))%nat ∧
    Exec.elem_of_results (ppst', ((), None))
      (run_outcome n_threads tid initmem (TlbOp tlbi)
         (Promising.promise_ppstate_events
            (VMPromising bbm_param) tid initmem events ppst)).
Proof.
  intro Hrun.
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_iis [viio [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_tlbi [vpre_opt [Htlbi Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> Hret].
  inversion Hret; subst vpre_opt.
  destruct (run_tlbi_promise_replay_events
    bbm_param n_threads tid initmem (IIS.strict (PPState.iis ppst))
    tlbi ppst pp_tlbi vpre Htlbi) as
    [events [Hnonempty [Hmem [Htid [Hle Htlbi_replay]]]]].
  exists events.
  split; [exact Hnonempty|].
  split; [exact Hmem|].
  split; [exact Htid|].
  split; [exact Hle|].
  simp run_outcome.
  eapply Exec.elem_of_bind_intro with
    (a := IIS.strict
      (PPState.iis
        (Promising.promise_ppstate_events
           (VMPromising bbm_param) tid initmem events ppst))).
  - apply (Exec.elem_of_mget (E:=string)
      (Promising.promise_ppstate_events
         (VMPromising bbm_param) tid initmem events ppst)
      (IIS.strict ∘ PPState.iis)).
  - cbn.
    rewrite VMPromising_promise_ppstate_events_iis.
    eapply Exec.elem_of_bind_intro.
    + exact Htlbi_replay.
    + cbn.
      apply Exec.elem_of_mret.
Qed.

Lemma VMPromising_replayable (bbm_param : BBM.param) :
    Promising.Replayable (VMPromising bbm_param).
Proof.
  constructor.
  - intros n tid0 initmem0 out ppst ppst' eret Hrun.
    cbn in Hrun.
    exact (run_outcome_none_preserves_mem
      n tid0 initmem0 out ppst ppst' eret Hrun).
  - intros n tid0 initmem0 out ppst ppst' eret vpre Hrun.
    cbn in Hrun.
    dependent destruction out;
      try solve [exfalso; simp run_outcome in Hrun; inv_exec_result].
    + exfalso.
      lazymatch goal with
      | mr : MemReq.t |- _ =>
          destruct mr as [macc addr addr_space size num_tag]
      end.
      destruct num_tag as [|num_tag];
        simp run_outcome in Hrun; inv_exec_result.
    + lazymatch goal with
      | mr : MemReq.t |- _ =>
          destruct mr as [macc addr addr_space size num_tag]
      end.
      destruct num_tag as [|num_tag].
      * destruct eret as [u|abort] eqn:Heret.
        -- destruct u.
           destruct (run_outcome_memwrite_promise_replay_one
             n tid0 initmem0 macc addr addr_space size value tags
             ppst ppst' vpre Hrun) as
             [event [Hmem [Htid [Hlt Hreplay]]]].
           exists [event].
           split; [discriminate|].
           split; [cbn; exact Hmem|].
           split.
           ++ intros event' Hevent'.
              apply elem_of_list_singleton in Hevent'.
              subst event'.
              exact Htid.
           ++ split; [exact Hlt|].
              cbn.
              exact Hreplay.
        -- exfalso.
           simp run_outcome in Hrun.
           inv_exec_result.
      * exfalso.
        simp run_outcome in Hrun.
        inv_exec_result.
    + destruct eret.
      lazymatch type of Hrun with
      | context[TlbOp ?tlbi] =>
          destruct (run_outcome_tlbop_promise_replay_events
            bbm_param n tid0 initmem0 tlbi ppst ppst' vpre Hrun) as
            [events [Hnonempty [Hmem [Htid [Hlt Hreplay]]]]]
      end.
      exists events.
      split; [exact Hnonempty|].
      split; [exact Hmem|].
      split; [exact Htid|].
      split; [exact Hlt|].
      exact Hreplay.
Qed.

Lemma run_outcome_no_promise_non_mem_write_tlb n_threads tid initmem out :
  (∀ mr (val : bv (8 * mr.(MemReq.size)))
      (tags : bv mr.(MemReq.num_tag)),
    out ≠ MemWrite mr val tags) →
  (∀ tlbi, out ≠ TlbOp tlbi) →
  ∀ ppst ppst' (eret : eff_ret out) vpre,
    Exec.elem_of_results (ppst', (eret, Some vpre))
      (run_outcome n_threads tid initmem out ppst) →
    False.
Proof.
  intros Hnot_write Hnot_tlb ppst ppst' eret vpre H.
  funelim (run_outcome n_threads tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: try solve [exfalso; eapply Hnot_write; reflexivity].
  all: try solve [exfalso; eapply Hnot_tlb; reflexivity].
  all: try solve [inv_exec_result].
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet
    {eo A} (out : SI.outcome eo A) : Prop :=
  imon_future_promise_stable_promised bbm_param n_threads tid initmem ev _
    (Sail_outcome_interp nondet out).

Fixpoint VMPromising_Sail_prefix_promised_stable
    (bbm_param : BBM.param) n_threads tid initmem ev nondet
    {eo A} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      (VMPromising_Sail_outcome_no_promise out ∧
       VMPromising_Sail_outcome_promised_stable
         bbm_param n_threads tid initmem ev nondet out ∧
       ∀ ret,
         VMPromising_Sail_prefix_promised_stable
           bbm_param n_threads tid initmem ev nondet (k ret)) ∨
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet
    {eo A} (smon : SI.iMon eo A) :
  VMPromising_Sail_no_promise smon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet smon.
Proof.
  induction smon as [a|T out k IH]; intro Hno.
  - exact I.
  - cbn in Hno |- *.
    destruct Hno as [_ Htail_no].
    right.
    exact Htail_no.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_bind_no_left
    (bbm_param : BBM.param) n_threads tid initmem ev nondet
    {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  (∀ a,
    VMPromising_Sail_prefix_promised_stable
      bbm_param n_threads tid initmem ev nondet (k a)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet (SI.iMon_bind mon k).
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet
    {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  (∀ a, VMPromising_Sail_no_promise (k a)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet (SI.iMon_bind mon k).
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet
    {eo A} (smon : SI.iMon eo A) :
  VMPromising_Sail_at_most_one_promise smon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet smon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet smon.
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  (∀ e, VMPromising_Sail_no_promise (h e)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  (∀ e, VMPromising_Sail_no_promise (h e)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  VMPromising_Sail_no_promise mon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet tail →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_no_promise tail →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  (∀ a,
    VMPromising_Sail_promised_stable
      bbm_param n_threads tid initmem ev nondet (k a)) →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet (SI.iMon_bind mon k).
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  (∀ e,
    VMPromising_Sail_promised_stable
      bbm_param n_threads tid initmem ev nondet (h e)) →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E} (e : E) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet mon →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet tail →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {E Vars}
    from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars,
    VMPromising_Sail_promised_stable
      bbm_param n_threads tid initmem ev nondet (body z vars)) →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    (bbm_param : BBM.param) n_threads tid initmem ev nondet {E Vars}
    from to step (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars,
    VMPromising_Sail_promised_stable
      bbm_param n_threads tid initmem ev nondet (body z vars)) →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.foreach_ZM_up from to step vars body).
Proof.
  cbn [System_types.Defs.foreach_ZM_up].
  apply VMPromising_Sail_promised_stable_foreach_ZM_up'.
Qed.

Lemma VMPromising_Sail_no_promise_read_reg {E}
    (reg : System_types.Arch.reg) :
  VMPromising_Sail_no_promise
    (System_types.Defs.read_reg (e:=E) reg).
Proof.
  cbn [System_types.Defs.read_reg].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_write_reg {E}
    (reg : System_types.Arch.reg) (value : System_types.Arch.reg_type reg) :
  VMPromising_Sail_no_promise
    (System_types.Defs.write_reg (e:=E) reg value).
Proof.
  cbn [System_types.Defs.write_reg].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_read_reg_ref {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.read_reg_ref (e:=E) ref).
Proof.
  cbn [System_types.Defs.read_reg_ref].
  apply VMPromising_Sail_no_promise_read_reg.
Qed.

Lemma VMPromising_Sail_no_promise_reg_deref {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.reg_deref (e:=E) ref).
Proof.
  cbn [System_types.Defs.reg_deref].
  apply VMPromising_Sail_no_promise_read_reg_ref.
Qed.

Lemma VMPromising_Sail_no_promise_write_reg_ref {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) (v : A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.write_reg_ref (e:=E) ref v).
Proof.
  cbn [System_types.Defs.write_reg_ref].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_sail_sys_reg_read {A E}
    id (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.sail_sys_reg_read (e:=E) id ref).
Proof.
  cbn [System_types.Defs.sail_sys_reg_read].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_sail_sys_reg_write {A E}
    id (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) (v : A) :
  VMPromising_Sail_no_promise
    (System_types.Defs.sail_sys_reg_write (e:=E) id ref v).
Proof.
  cbn [System_types.Defs.sail_sys_reg_write].
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

Lemma VMPromising_Sail_no_promise_choose_bool {E} descr :
  VMPromising_Sail_no_promise
    (System_types.Defs.choose_bool (E:=E) descr).
Proof.
  cbn [System_types.Defs.choose_bool].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma VMPromising_Sail_no_promise_undefined_bool {E} u :
  VMPromising_Sail_no_promise
    (System_types.Defs.undefined_bool (E:=E) u).
Proof.
  cbn [System_types.Defs.undefined_bool].
  apply VMPromising_Sail_no_promise_choose_bool.
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
       System_types.Defs.choose_range System_types.Defs.choose_bool
       System_types.Defs.undefined_bool System_types.Defs.choose_from_list
       System_types.Defs.internal_pick System_types.Defs.read_reg
       System_types.Defs.write_reg System_types.Defs.read_reg_ref
       System_types.Defs.reg_deref System_types.Defs.write_reg_ref
       System_types.Defs.sail_sys_reg_read
       System_types.Defs.sail_sys_reg_write
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
        (System_types.Defs.sail_sys_reg_read _ _) =>
      apply VMPromising_Sail_no_promise_sail_sys_reg_read
  | |- VMPromising_Sail_no_promise
        (Defs.sail_sys_reg_read _ _) =>
      apply VMPromising_Sail_no_promise_sail_sys_reg_read
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.sail_sys_reg_write _ _ _) =>
      apply VMPromising_Sail_no_promise_sail_sys_reg_write
  | |- VMPromising_Sail_no_promise
        (Defs.sail_sys_reg_write _ _ _) =>
      apply VMPromising_Sail_no_promise_sail_sys_reg_write
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
  | |- VMPromising_Sail_no_promise (System.rXS _ _) =>
      unfold System.rXS;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.wXS _ _ _) =>
      unfold System.wXS;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.check_load_store_alignment _ _) =>
      unfold System.check_load_store_alignment;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.rPC _) =>
      unfold System.rPC;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.wPC _) =>
      unfold System.wPC;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.create_writeAccessDescriptor _ _) =>
      unfold System.create_writeAccessDescriptor;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.create_RMWAccessDescriptor _ _ _) =>
      unfold System.create_RMWAccessDescriptor;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.create_readAccessDescriptor _ _ _) =>
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
  | |- VMPromising_Sail_no_promise (System.lookup_sys_reg _) =>
      unfold System.lookup_sys_reg, System.lookup_sys_reg64, System.fail;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.read_sys_reg_accessor _ ?accessor) =>
      destruct accessor;
      unfold System.read_sys_reg_accessor, System.lookup_sys_reg64,
        System.fail;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.write_sys_reg_accessor _ ?accessor _) =>
      destruct accessor;
      unfold System.write_sys_reg_accessor, System.lookup_sys_reg64,
        System.fail;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.translate_address _ _) =>
      unfold System.translate_address, System.pgt_walk,
        System.get_translation_base_address,
        System.create_AccessDescriptorTTW, System.ASID_read;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.decode_bitmask _ _ _ _) =>
      unfold System.decode_bitmask;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.decode _) =>
      unfold System.decode, System.decodeLoadStoreRegister,
        System.decodeLoadStoreImmediate, System.decodeAddSubExt,
        System.decodeAddSubImm, System.decodeAddSubShift,
        System.decodeCompareAndBranch, System.decodeTestAndBranch,
        System.decodeDataBarrier, System.decodeTLBI,
        System.decodeSystemRegisterMove,
        System.decode_bitwise_op, System.decode_bitmask, System.fail;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_SupervisorCall _) =>
      unfold System.execute_SupervisorCall;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.execute_Nop _) =>
      unfold System.execute_Nop;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise (System.execute_Movz _ _ _ _) =>
      unfold System.execute_Movz;
      solve_VMPromising_Sail_no_promise_src
  | |- VMPromising_Sail_no_promise
        (System.execute_Load _ _ _ _ _ _ _) =>
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
        (Defs.choose_range _ _ _) =>
      apply VMPromising_Sail_no_promise_choose_range
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.choose_bool _) =>
      apply VMPromising_Sail_no_promise_choose_bool
  | |- VMPromising_Sail_no_promise
        (Defs.choose_bool _) =>
      apply VMPromising_Sail_no_promise_choose_bool
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.undefined_bool _) =>
      apply VMPromising_Sail_no_promise_undefined_bool
  | |- VMPromising_Sail_no_promise
        (Defs.undefined_bool _) =>
      apply VMPromising_Sail_no_promise_undefined_bool
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.choose_from_list _ _) =>
      apply VMPromising_Sail_no_promise_choose_from_list
  | |- VMPromising_Sail_no_promise
        (Defs.choose_from_list _ _) =>
      apply VMPromising_Sail_no_promise_choose_from_list
  | |- VMPromising_Sail_no_promise
        (System_types.Defs.internal_pick _) =>
      apply VMPromising_Sail_no_promise_internal_pick
  | |- VMPromising_Sail_no_promise
        (Defs.internal_pick _) =>
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
  | |- ?G => fail 0 G
  end.

Ltac solve_VMPromising_Sail_no_promise_exec :=
  lazymatch goal with
  | |- VMPromising_Sail_no_promise (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      eapply VMPromising_Sail_no_promise_bind;
      [solve_VMPromising_Sail_no_promise_exec
      |intro; solve_VMPromising_Sail_no_promise_exec]
  | |- VMPromising_Sail_no_promise (Defs.bind _ _) =>
      unfold Defs.bind;
      eapply VMPromising_Sail_no_promise_bind;
      [solve_VMPromising_Sail_no_promise_exec
      |intro; solve_VMPromising_Sail_no_promise_exec]
  | |- VMPromising_Sail_no_promise
        (System_types.Interface.iMon_bind _ _) =>
      eapply VMPromising_Sail_no_promise_bind;
      [solve_VMPromising_Sail_no_promise_exec
      |intro; solve_VMPromising_Sail_no_promise_exec]
  | |- VMPromising_Sail_no_promise (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_no_promise_bind0;
      [solve_VMPromising_Sail_no_promise_exec
      |solve_VMPromising_Sail_no_promise_exec]
  | |- VMPromising_Sail_no_promise (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_no_promise_bind0;
      [solve_VMPromising_Sail_no_promise_exec
      |solve_VMPromising_Sail_no_promise_exec]
  | |- VMPromising_Sail_no_promise (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply VMPromising_Sail_no_promise_liftR;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (@Defs.liftR ?A ?R ?E ?mon) =>
      change (VMPromising_Sail_no_promise
        (@System_types.Defs.liftR A R E mon));
      apply VMPromising_Sail_no_promise_liftR;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply VMPromising_Sail_no_promise_catch_early_return;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (@Defs.catch_early_return ?A ?E ?mon) =>
      change (VMPromising_Sail_no_promise
        (System_types.Defs.catch_early_return mon));
      apply VMPromising_Sail_no_promise_catch_early_return;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System_types.Defs.read_reg _) =>
      apply VMPromising_Sail_no_promise_read_reg
  | |- VMPromising_Sail_no_promise (Defs.read_reg _) =>
      apply VMPromising_Sail_no_promise_read_reg
  | |- VMPromising_Sail_no_promise (System_types.Defs.write_reg _ _) =>
      apply VMPromising_Sail_no_promise_write_reg
  | |- VMPromising_Sail_no_promise (Defs.write_reg _ _) =>
      apply VMPromising_Sail_no_promise_write_reg
  | |- VMPromising_Sail_no_promise (System_types.Defs.reg_deref _) =>
      apply VMPromising_Sail_no_promise_reg_deref
  | |- VMPromising_Sail_no_promise (Defs.reg_deref _) =>
      apply VMPromising_Sail_no_promise_reg_deref
  | |- VMPromising_Sail_no_promise (System.rX _) =>
      unfold System.rX; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.wX _ _) =>
      unfold System.wX; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.rSP _) =>
      unfold System.rSP; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.wSP _) =>
      unfold System.wSP; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.rSPS _) =>
      unfold System.rSPS; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.wSPS _ _) =>
      unfold System.wSPS; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.rXS _ _) =>
      unfold System.rXS; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.wXS _ _ _) =>
      unfold System.wXS; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.rPC _) =>
      unfold System.rPC; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.wPC _) =>
      unfold System.wPC; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.rN _) =>
      unfold System.rN; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.rZ _) =>
      unfold System.rZ; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.rC _) =>
      unfold System.rC; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.rV _) =>
      unfold System.rV; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.condition_holds _) =>
      unfold System.condition_holds, System.rN, System.rZ, System.rC,
        System.rV, System_types.Defs.and_boolM,
        System_types.Defs.or_boolM;
      match goal with
      | |- VMPromising_Sail_no_promise (match ?cond with _ => _ end) =>
          destruct cond; solve_VMPromising_Sail_no_promise_exec
      | _ => solve_VMPromising_Sail_no_promise_exec
      end
  | |- VMPromising_Sail_no_promise (System.decode _) =>
      unfold System.decode, System.decodeLoadStoreRegister,
        System.decodeLoadStoreImmediate, System.decodeAddSubExt,
        System.decodeAddSubImm, System.decodeAddSubShift,
        System.decodeCompareAndBranch, System.decodeTestAndBranch,
        System.decodeDataBarrier, System.decodeTLBI,
        System.decodeSystemRegisterMove,
        System.decode_bitwise_op, System.decode_bitmask, System.fail;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.eval_operand _ _) =>
      unfold System.eval_operand, System.shift_reg;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.shift_reg _ _ _) =>
      unfold System.shift_reg; solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise
        (System.check_load_store_alignment _ _) =>
      unfold System.check_load_store_alignment;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System_types.returnM _) =>
      cbn [System_types.returnM];
      exact I
  | |- VMPromising_Sail_no_promise
        (System.create_readAccessDescriptor _ _ _) =>
      unfold System.create_readAccessDescriptor;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise
        (System.create_writeAccessDescriptor _ _) =>
      unfold System.create_writeAccessDescriptor;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise
        (System.create_RMWAccessDescriptor _ _ _) =>
      unfold System.create_RMWAccessDescriptor;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise (System.lookup_sys_reg _) =>
      unfold System.lookup_sys_reg, System.lookup_sys_reg64, System.fail;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise
        (System.read_sys_reg_accessor _ ?accessor) =>
      destruct accessor;
      unfold System.read_sys_reg_accessor, System.lookup_sys_reg64,
        System.fail;
      solve_VMPromising_Sail_no_promise_exec
  | |- VMPromising_Sail_no_promise
        (System.write_sys_reg_accessor _ ?accessor _) =>
      destruct accessor;
      unfold System.write_sys_reg_accessor, System.lookup_sys_reg64,
        System.fail;
      solve_VMPromising_Sail_no_promise_exec
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_VMPromising_Sail_no_promise_exec
  | |- context[if ?x then _ else _] =>
      destruct x; solve_VMPromising_Sail_no_promise_exec
  | _ => solve_VMPromising_Sail_no_promise_src
  end.

Lemma VMPromising_Sail_no_promise_execute_Load
    size t n op acquire rcpc exclusive :
  VMPromising_Sail_no_promise
    (System.execute_Load size t n op acquire rcpc exclusive).
Proof.
  unfold System.execute_Load.
  solve_VMPromising_Sail_no_promise_exec.
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
        (System.execute_Store _ _ _ _ _ _) =>
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
        (System.execute_Load _ _ _ _ _ _ _) =>
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
        (System.execute_TLBInvalidation _ _ _ _) =>
      unfold System.execute_TLBInvalidation;
      solve_VMPromising_Sail_at_most_one_promise_src
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec
         |intro; solve_VMPromising_Sail_at_most_one_promise_src]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_src
         |intro; solve_VMPromising_Sail_no_promise_exec]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec
         |intro; solve_VMPromising_Sail_at_most_one_promise_src]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_src
         |intro; solve_VMPromising_Sail_no_promise_exec]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_exec
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
         solve_VMPromising_Sail_no_promise_exec]
  end.

Ltac solve_VMPromising_Sail_at_most_one_promise_exec :=
  lazymatch goal with
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.sail_mem_write _ _ _) =>
      apply VMPromising_Sail_at_most_one_promise_sail_mem_write
  | |- VMPromising_Sail_at_most_one_promise
        (Defs.sail_mem_write _ _ _) =>
      apply VMPromising_Sail_at_most_one_promise_sail_mem_write
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.sail_tlbi _) =>
      apply VMPromising_Sail_at_most_one_promise_sail_tlbi
  | |- VMPromising_Sail_at_most_one_promise
        (Defs.sail_tlbi _) =>
      apply VMPromising_Sail_at_most_one_promise_sail_tlbi
  | |- VMPromising_Sail_at_most_one_promise (System.wMem _ _ _ _) =>
      unfold System.wMem;
      solve_VMPromising_Sail_at_most_one_promise_exec
  | |- VMPromising_Sail_at_most_one_promise
        (System.reportTLBI _ _ _ _ _) =>
      unfold System.reportTLBI;
      solve_VMPromising_Sail_at_most_one_promise_exec
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec
         |intro; solve_VMPromising_Sail_at_most_one_promise_exec]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_exec
         |intro; solve_VMPromising_Sail_no_promise_exec]]
  | |- VMPromising_Sail_at_most_one_promise (Defs.bind _ _) =>
      unfold Defs.bind;
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec
         |intro; solve_VMPromising_Sail_at_most_one_promise_exec]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_exec
         |intro; solve_VMPromising_Sail_no_promise_exec]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec
         |intro; solve_VMPromising_Sail_at_most_one_promise_exec]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_exec
         |intro; solve_VMPromising_Sail_no_promise_exec]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_exec
      |solve_VMPromising_Sail_at_most_one_promise_exec]
  | |- VMPromising_Sail_at_most_one_promise (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_exec
      |solve_VMPromising_Sail_at_most_one_promise_exec]
  | |- VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply VMPromising_Sail_at_most_one_promise_liftR;
      solve_VMPromising_Sail_at_most_one_promise_exec
  | |- VMPromising_Sail_at_most_one_promise (@Defs.liftR ?A ?R ?E ?mon) =>
      change (VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR A R E mon));
      apply VMPromising_Sail_at_most_one_promise_liftR;
      solve_VMPromising_Sail_at_most_one_promise_exec
  | |- VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply VMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_VMPromising_Sail_at_most_one_promise_exec
  | |- VMPromising_Sail_at_most_one_promise
        (@Defs.catch_early_return ?A ?E ?mon) =>
      change (VMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return mon));
      apply VMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_VMPromising_Sail_at_most_one_promise_exec
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_VMPromising_Sail_at_most_one_promise_exec
  | |- context[if ?x then _ else _] =>
      destruct x; solve_VMPromising_Sail_at_most_one_promise_exec
  | |- VMPromising_Sail_at_most_one_promise _ =>
      apply VMPromising_Sail_at_most_one_promise_from_no_promise;
      solve_VMPromising_Sail_no_promise_exec
  | |- ?G => fail 0 G
  end.

Lemma VMPromising_Sail_no_promise_execute_SupervisorCall imm16 :
  VMPromising_Sail_no_promise (System.execute_SupervisorCall imm16).
Proof.
  unfold System.execute_SupervisorCall.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_execute_Store
    size t n offset release s :
  VMPromising_Sail_at_most_one_promise
    (System.execute_Store size t n offset release s).
Proof.
  unfold System.execute_Store.
  solve_VMPromising_Sail_at_most_one_promise_exec.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_execute_AtomicRMW
    size s t n op acq rel :
  VMPromising_Sail_at_most_one_promise
    (System.execute_AtomicRMW size s t n op acq rel).
Proof.
  unfold System.execute_AtomicRMW.
  solve_VMPromising_Sail_at_most_one_promise_exec.
Qed.

Lemma VMPromising_Sail_at_most_one_promise_execute_TLBInvalidation
    op shareability t vmid :
  VMPromising_Sail_at_most_one_promise
    (System.execute_TLBInvalidation op shareability t vmid).
Proof.
  unfold System.execute_TLBInvalidation.
  solve_VMPromising_Sail_at_most_one_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_Nop :
  VMPromising_Sail_no_promise (System.execute_Nop tt).
Proof.
  unfold System.execute_Nop.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_Movz sf d imm hw :
  VMPromising_Sail_no_promise (System.execute_Movz sf d imm hw).
Proof.
  unfold System.execute_Movz.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_ISB :
  VMPromising_Sail_no_promise
    (System.execute_InstructionSynchronizationBarrier tt).
Proof.
  unfold System.execute_InstructionSynchronizationBarrier.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_ExceptionReturn :
  VMPromising_Sail_no_promise (System.execute_ExceptionReturn tt).
Proof.
  unfold System.execute_ExceptionReturn.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_DSB domain types :
  VMPromising_Sail_no_promise
    (System.execute_DataSynchronizationBarrier domain types).
Proof.
  unfold System.execute_DataSynchronizationBarrier.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_DMB domain types :
  VMPromising_Sail_no_promise
    (System.execute_DataMemoryBarrier domain types).
Proof.
  unfold System.execute_DataMemoryBarrier.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_CompareAndBranch
    sf t offset iszero :
  VMPromising_Sail_no_promise
    (System.execute_CompareAndBranch sf t offset iszero).
Proof.
  unfold System.execute_CompareAndBranch.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_TestAndBranch
    t bit_pos offset iszero :
  VMPromising_Sail_no_promise
    (System.execute_TestAndBranch t bit_pos offset iszero).
Proof.
  unfold System.execute_TestAndBranch.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_Branch offset :
  VMPromising_Sail_no_promise (System.execute_Branch offset).
Proof.
  unfold System.execute_Branch.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_ConditionalBranch offset cond :
  VMPromising_Sail_no_promise
    (System.execute_ConditionalBranch offset cond).
Proof.
  unfold System.execute_ConditionalBranch.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_PCRelativeAddress
    page d offset :
  VMPromising_Sail_no_promise
    (System.execute_PCRelativeAddress page d offset).
Proof.
  unfold System.execute_PCRelativeAddress.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_BranchRegister n :
  VMPromising_Sail_no_promise (System.execute_BranchRegister n).
Proof.
  unfold System.execute_BranchRegister.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_BitwiseLogic
    sf op d n op2 :
  VMPromising_Sail_no_promise
    (System.execute_BitwiseLogic sf op d n op2).
Proof.
  unfold System.execute_BitwiseLogic.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_BitfieldMove
    sf signd d n imms immr :
  VMPromising_Sail_no_promise
    (System.execute_BitfieldMove sf signd d n imms immr).
Proof.
  unfold System.execute_BitfieldMove.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_AddSub sf op s d n m :
  VMPromising_Sail_no_promise
    (System.execute_AddSub sf op s d n m).
Proof.
  unfold System.execute_AddSub, System.eval_operand, System.shift_reg.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Lemma VMPromising_Sail_no_promise_execute_SystemRegisterMove
    is_read sys_reg_id t :
  VMPromising_Sail_no_promise
    (System.execute_SystemRegisterMove is_read sys_reg_id t).
Proof.
  unfold System.execute_SystemRegisterMove.
  solve_VMPromising_Sail_no_promise_exec.
Qed.

Ltac solve_VMPromising_Sail_no_promise_instr :=
  lazymatch goal with
  | |- VMPromising_Sail_no_promise
        (System.execute_SupervisorCall _) =>
      apply VMPromising_Sail_no_promise_execute_SupervisorCall
  | |- VMPromising_Sail_no_promise (System.execute_Nop ?u) =>
      destruct u; apply VMPromising_Sail_no_promise_execute_Nop
  | |- VMPromising_Sail_no_promise (System.execute_Movz _ _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_Movz
  | |- VMPromising_Sail_no_promise (System.execute_Load _ _ _ _ _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_Load
  | |- VMPromising_Sail_no_promise
        (System.execute_InstructionSynchronizationBarrier ?u) =>
      destruct u; apply VMPromising_Sail_no_promise_execute_ISB
  | |- VMPromising_Sail_no_promise
        (System.execute_ExceptionReturn ?u) =>
      destruct u; apply VMPromising_Sail_no_promise_execute_ExceptionReturn
  | |- VMPromising_Sail_no_promise
        (System.execute_DataSynchronizationBarrier _ _) =>
      apply VMPromising_Sail_no_promise_execute_DSB
  | |- VMPromising_Sail_no_promise
        (System.execute_DataMemoryBarrier _ _) =>
      apply VMPromising_Sail_no_promise_execute_DMB
  | |- VMPromising_Sail_no_promise
        (System.execute_CompareAndBranch _ _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_CompareAndBranch
  | |- VMPromising_Sail_no_promise
        (System.execute_TestAndBranch _ _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_TestAndBranch
  | |- VMPromising_Sail_no_promise (System.execute_Branch _) =>
      apply VMPromising_Sail_no_promise_execute_Branch
  | |- VMPromising_Sail_no_promise
        (System.execute_ConditionalBranch _ _) =>
      apply VMPromising_Sail_no_promise_execute_ConditionalBranch
  | |- VMPromising_Sail_no_promise
        (System.execute_PCRelativeAddress _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_PCRelativeAddress
  | |- VMPromising_Sail_no_promise
        (System.execute_BranchRegister _) =>
      apply VMPromising_Sail_no_promise_execute_BranchRegister
  | |- VMPromising_Sail_no_promise
        (System.execute_BitwiseLogic _ _ _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_BitwiseLogic
  | |- VMPromising_Sail_no_promise
        (System.execute_BitfieldMove _ _ _ _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_BitfieldMove
  | |- VMPromising_Sail_no_promise (System.execute_AddSub _ _ _ _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_AddSub
  | |- VMPromising_Sail_no_promise
        (System.execute_SystemRegisterMove _ _ _) =>
      apply VMPromising_Sail_no_promise_execute_SystemRegisterMove
  | _ => solve_VMPromising_Sail_no_promise_exec
  end.

Ltac solve_VMPromising_Sail_at_most_one_promise_instr :=
  lazymatch goal with
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_Store _ _ _ _ _ _) =>
      apply VMPromising_Sail_at_most_one_promise_execute_Store
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_AtomicRMW _ _ _ _ _ _ _) =>
      apply VMPromising_Sail_at_most_one_promise_execute_AtomicRMW
  | |- VMPromising_Sail_at_most_one_promise
        (System.execute_TLBInvalidation _ _ _ _) =>
      apply VMPromising_Sail_at_most_one_promise_execute_TLBInvalidation
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_instr
         |intro; solve_VMPromising_Sail_at_most_one_promise_instr]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_instr
         |intro; solve_VMPromising_Sail_no_promise_instr]]
  | |- VMPromising_Sail_at_most_one_promise (Defs.bind _ _) =>
      unfold Defs.bind;
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_instr
         |intro; solve_VMPromising_Sail_at_most_one_promise_instr]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_instr
         |intro; solve_VMPromising_Sail_no_promise_instr]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_instr
         |intro; solve_VMPromising_Sail_at_most_one_promise_instr]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_instr
         |intro; solve_VMPromising_Sail_no_promise_instr]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_instr
      |solve_VMPromising_Sail_at_most_one_promise_instr]
  | |- VMPromising_Sail_at_most_one_promise (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_instr
      |solve_VMPromising_Sail_at_most_one_promise_instr]
  | |- VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply VMPromising_Sail_at_most_one_promise_liftR;
      solve_VMPromising_Sail_at_most_one_promise_instr
  | |- VMPromising_Sail_at_most_one_promise (@Defs.liftR ?A ?R ?E ?mon) =>
      change (VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR A R E mon));
      apply VMPromising_Sail_at_most_one_promise_liftR;
      solve_VMPromising_Sail_at_most_one_promise_instr
  | |- VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply VMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_VMPromising_Sail_at_most_one_promise_instr
  | |- VMPromising_Sail_at_most_one_promise
        (@Defs.catch_early_return ?A ?E ?mon) =>
      change (VMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return mon));
      apply VMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_VMPromising_Sail_at_most_one_promise_instr
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_VMPromising_Sail_at_most_one_promise_instr
  | |- context[if ?x then _ else _] =>
      destruct x; solve_VMPromising_Sail_at_most_one_promise_instr
  | _ =>
      apply VMPromising_Sail_at_most_one_promise_from_no_promise;
      solve_VMPromising_Sail_no_promise_instr
  end.

Lemma VMPromising_Sail_at_most_one_promise_execute instr :
  VMPromising_Sail_at_most_one_promise (System.execute instr).
Proof.
  unfold System.execute.
  destruct instr; cbn [System.execute].
  all: repeat match goal with
  | p : _ * _ |- _ => destruct p; cbn [System.execute]
  | u : unit |- _ => destruct u; cbn [System.execute]
  end.
  all: solve_VMPromising_Sail_at_most_one_promise_instr.
Qed.

Ltac solve_VMPromising_Sail_at_most_one_promise_fetch :=
  lazymatch goal with
  | |- VMPromising_Sail_at_most_one_promise (System.execute _) =>
      apply VMPromising_Sail_at_most_one_promise_execute
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_instr
         |intro; solve_VMPromising_Sail_at_most_one_promise_fetch]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_fetch
         |intro; solve_VMPromising_Sail_no_promise_instr]]
  | |- VMPromising_Sail_at_most_one_promise (Defs.bind _ _) =>
      unfold Defs.bind;
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_instr
         |intro; solve_VMPromising_Sail_at_most_one_promise_fetch]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_fetch
         |intro; solve_VMPromising_Sail_no_promise_instr]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_VMPromising_Sail_no_promise_instr
         |intro; solve_VMPromising_Sail_at_most_one_promise_fetch]
        |eapply VMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_VMPromising_Sail_at_most_one_promise_fetch
         |intro; solve_VMPromising_Sail_no_promise_instr]]
  | |- VMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_instr
      |solve_VMPromising_Sail_at_most_one_promise_fetch]
  | |- VMPromising_Sail_at_most_one_promise (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_instr
      |solve_VMPromising_Sail_at_most_one_promise_fetch]
  | |- VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply VMPromising_Sail_at_most_one_promise_liftR;
      solve_VMPromising_Sail_at_most_one_promise_fetch
  | |- VMPromising_Sail_at_most_one_promise (@Defs.liftR ?A ?R ?E ?mon) =>
      change (VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR A R E mon));
      apply VMPromising_Sail_at_most_one_promise_liftR;
      solve_VMPromising_Sail_at_most_one_promise_fetch
  | |- VMPromising_Sail_at_most_one_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply VMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_VMPromising_Sail_at_most_one_promise_fetch
  | |- VMPromising_Sail_at_most_one_promise
        (@Defs.catch_early_return ?A ?E ?mon) =>
      change (VMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return mon));
      apply VMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_VMPromising_Sail_at_most_one_promise_fetch
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_VMPromising_Sail_at_most_one_promise_fetch
  | |- context[if ?x then _ else _] =>
      destruct x; solve_VMPromising_Sail_at_most_one_promise_fetch
  | _ => solve_VMPromising_Sail_at_most_one_promise_instr
  end.

Lemma VMPromising_Sail_at_most_one_promise_fetch_and_execute :
  VMPromising_Sail_at_most_one_promise (System.fetch_and_execute tt).
Proof.
  unfold System.fetch_and_execute.
  solve_VMPromising_Sail_at_most_one_promise_fetch.
Qed.

Lemma VMPromising_Sail_promised_stable_returnm
    bbm_param n_threads tid initmem ev nondet {A E} (a : A) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.returnm (E:=E) a).
Proof.
  exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_fail
    bbm_param n_threads tid initmem ev nondet {A E} msg :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    bbm_param n_threads tid initmem ev nondet {A E} :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.exit (A:=A) (E:=E) tt).
Proof.
  cbn [System_types.Defs.exit].
  apply VMPromising_Sail_promised_stable_fail.
Qed.

Lemma VMPromising_Sail_promised_stable_read_reg
    bbm_param n_threads tid initmem ev nondet {E}
    (reg : System_types.Arch.reg) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    bbm_param n_threads tid initmem ev nondet {E}
    (reg : System_types.Arch.reg) (value : System_types.Arch.reg_type reg) :
  (∀ ppst, ppstate_control_times_le ppst) →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.write_reg (e:=E) reg value).
Proof.
  intro Hcontrol.
  cbn [System_types.Defs.write_reg VMPromising_Sail_promised_stable
       Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
	    split.
    + apply reg_write_outcome_future_promise_stable_promised.
      exact Hcontrol.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_read_reg_ref
    bbm_param n_threads tid initmem ev nondet {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.read_reg_ref (e:=E) ref).
Proof.
  cbn [System_types.Defs.read_reg_ref].
  apply VMPromising_Sail_promised_stable_read_reg.
Qed.

Lemma VMPromising_Sail_promised_stable_reg_deref
    bbm_param n_threads tid initmem ev nondet {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.reg_deref (e:=E) ref).
Proof.
  cbn [System_types.Defs.reg_deref].
  apply VMPromising_Sail_promised_stable_read_reg_ref.
Qed.

Lemma VMPromising_Sail_promised_stable_write_reg_ref
    bbm_param n_threads tid initmem ev nondet {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) (v : A) :
  (∀ ppst, ppstate_control_times_le ppst) →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.write_reg_ref (e:=E) ref v).
Proof.
  intro Hcontrol.
  cbn [System_types.Defs.write_reg_ref].
  apply VMPromising_Sail_promised_stable_write_reg.
  exact Hcontrol.
Qed.

Lemma VMPromising_Sail_promised_stable_rX
    bbm_param n_threads tid initmem ev nondet n :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet (System.rX n).
Proof.
  unfold System.rX.
  destruct (System.neq_int n 31).
  - apply VMPromising_Sail_promised_stable_reg_deref.
  - cbn [System_types.returnM].
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_rSP
    bbm_param n_threads tid initmem ev nondet :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet (System.rSP tt).
Proof.
  unfold System.rSP.
  cbn [System_types.Defs.bind Defs.bind].
  eapply VMPromising_Sail_promised_stable_bind.
  - apply VMPromising_Sail_promised_stable_read_reg.
  - intro spsel.
    match goal with
    | |- context[if ?b then _ else _] => destruct b
    end.
    + apply VMPromising_Sail_promised_stable_read_reg.
    + cbn [System_types.Defs.bind Defs.bind].
      eapply VMPromising_Sail_promised_stable_bind.
      * apply VMPromising_Sail_promised_stable_read_reg.
      * intro current_el.
        repeat match goal with
        | |- context[if ?b then _ else _] => destruct b
        end;
        apply VMPromising_Sail_promised_stable_read_reg.
Qed.

Lemma VMPromising_Sail_promised_stable_rXS
    bbm_param n_threads tid initmem ev nondet n size :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet (System.rXS n size).
Proof.
  unfold System.rXS.
  eapply VMPromising_Sail_promised_stable_bind.
  - apply VMPromising_Sail_promised_stable_rX.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_shift_reg
    bbm_param n_threads tid initmem ev nondet {N} v sh amount :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System.shift_reg (N:=N) v sh amount).
Proof.
  unfold System.shift_reg, System.fail.
  destruct sh.
  all: try exact I.
  cbn [System_types.Defs.bind Defs.bind
       System_types.Defs.assert_exp' Defs.assert_exp'].
  eapply VMPromising_Sail_promised_stable_bind.
  - apply VMPromising_Sail_promised_stable_fail.
  - intro.
    apply VMPromising_Sail_promised_stable_exit.
Qed.

Lemma VMPromising_Sail_promised_stable_eval_operand
    bbm_param n_threads tid initmem ev nondet size op :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System.eval_operand size op).
Proof.
  unfold System.eval_operand.
  destruct op as [[[n ext] shift]|[[n sh] amount]|imm].
  - eapply VMPromising_Sail_promised_stable_bind.
    + apply VMPromising_Sail_promised_stable_rX.
    + intro.
      exact I.
  - eapply VMPromising_Sail_promised_stable_bind.
    + apply VMPromising_Sail_promised_stable_rXS.
    + intro.
      apply VMPromising_Sail_promised_stable_shift_reg.
  - exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_mem_read_ifetch
    bbm_param n_threads tid initmem code ev nondet {E} req :
  is_ifetch (ConcurrencyInterfaceTypesV2.Mem_request_access_kind req) = true →
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.sail_mem_read (e:=E) (n:=4) (nt:=0) req).
Proof.
  intros Hifetch Hstable.
  cbn [System_types.Defs.sail_mem_read
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + eapply
        VMPromising_mem_read_ifetch_promised_stable_from_read_code_translation.
      * exact Hifetch.
      * exact Hstable.
    + intros [[data tags]|abort]; exact I.
  - intros [[data tags]|abort]; exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_sail_mem_read_data
    bbm_param n_threads tid initmem code ev nondet {E n} req :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.sail_mem_read (e:=E) (n:=n) (nt:=0) req).
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

(*
Lemma VMPromising_Sail_promised_stable_sail_barrier_dmb
    bbm_param n_threads tid initmem ev nondet {E} dmb :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    bbm_param n_threads tid initmem ev nondet {E} dsb :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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

*)

Lemma VMPromising_Sail_promised_stable_sail_barrier_isb
    bbm_param n_threads tid initmem ev nondet {E} u :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    bbm_param n_threads tid initmem code ev nondet {E} ts :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    bbm_param n_threads tid initmem ev nondet {E} te :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
    bbm_param n_threads tid initmem ev nondet {E} exn :
  (∀ ppst, ppstate_control_times_le ppst) →
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.sail_take_exception (e:=E) exn).
Proof.
  intro Hcontrol.
  cbn [System_types.Defs.sail_take_exception
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  split.
  - unfold mcall.
    cbn [imon_future_promise_stable_promised].
    split.
    + apply take_exception_outcome_future_promise_stable_promised.
      exact Hcontrol.
    + intro.
      exact I.
  - intro.
    exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_choose_bool
    bbm_param n_threads tid initmem ev nondet {E} descr :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.choose_bool (E:=E) descr).
Proof.
  cbn [System_types.Defs.choose_bool
       VMPromising_Sail_promised_stable Sail_outcome_interp].
  destruct nondet;
    cbn [Sail_choose Sail_nochoose mchoosef mchoose mret
         imon_future_promise_stable_promised].
  - split.
    + unfold mchoosef, mchoosel, mchoose, mcall, fmap,
        fMon_fmap, fMon_bind, fMon_call, mret.
      cbn [imon_future_promise_stable_promised].
      intro.
      exact I.
    + intro.
      exact I.
  - split.
    + exact I.
    + intro.
      exact I.
Qed.

Lemma VMPromising_Sail_promised_stable_undefined_bool
    bbm_param n_threads tid initmem ev nondet {E} u :
  VMPromising_Sail_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.undefined_bool (E:=E) u).
Proof.
  cbn [System_types.Defs.undefined_bool].
  apply VMPromising_Sail_promised_stable_choose_bool.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_sail_mem_write
    bbm_param n_threads tid initmem ev nondet {E n nt} req value tags :
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.sail_mem_write
       (e:=E) (n:=n) (nt:=nt) req value tags).
Proof.
  cbn [System_types.Defs.sail_mem_write].
  right.
  intros [[]|abort].
  all: exact I.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_sail_tlbi
    bbm_param n_threads tid initmem ev nondet {E} tlbi :
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
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
        _ _ _ _ _ _ (System_types.Interface.Ret _) =>
      exact I
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.returnM _) =>
      cbn [System_types.returnM];
      exact I
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (returnM _) =>
      cbn [returnM System_types.returnM];
      exact I
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.returnm _) =>
      apply VMPromising_Sail_promised_stable_returnm
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.early_return _) =>
      unfold System_types.Defs.early_return;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.early_return _) =>
      unfold Defs.early_return;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.fail _) =>
      apply VMPromising_Sail_promised_stable_fail
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.fail _) =>
      apply VMPromising_Sail_promised_stable_fail
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.throw _) =>
      apply VMPromising_Sail_promised_stable_throw
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.throw _) =>
      apply VMPromising_Sail_promised_stable_throw
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.exit _) =>
      apply VMPromising_Sail_promised_stable_exit
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.assert_exp' ?b _) =>
      destruct b;
      [apply VMPromising_Sail_promised_stable_returnm
      |apply VMPromising_Sail_promised_stable_fail]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.assert_exp ?b _) =>
      destruct b;
      [apply VMPromising_Sail_promised_stable_returnm
      |apply VMPromising_Sail_promised_stable_fail]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.read_reg _) =>
      apply VMPromising_Sail_promised_stable_read_reg
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.read_reg _) =>
      apply VMPromising_Sail_promised_stable_read_reg
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.write_reg _ _) =>
      apply VMPromising_Sail_promised_stable_write_reg;
      intros ppst;
      eapply VMPromising_read_code_control_bound;
      exact Hstable
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.write_reg _ _) =>
      apply VMPromising_Sail_promised_stable_write_reg;
      intros ppst;
      eapply VMPromising_read_code_control_bound;
      exact Hstable
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.read_reg_ref _) =>
      cbn [System_types.Defs.read_reg_ref];
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.reg_deref _) =>
      cbn [System_types.Defs.reg_deref];
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.write_reg_ref _ _) =>
      apply VMPromising_Sail_promised_stable_write_reg_ref;
      intros ppst;
      eapply VMPromising_read_code_control_bound;
      exact Hstable
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.sail_mem_read _) =>
      first
        [eapply
           VMPromising_Sail_promised_stable_sail_mem_read_ifetch;
         [vm_compute; reflexivity
         |exact Hstable]
        |eapply VMPromising_Sail_promised_stable_sail_mem_read_data;
         exact Hstable
        ]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.sail_barrier (Barrier_ISB _)) =>
      apply VMPromising_Sail_promised_stable_sail_barrier_isb
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.sail_translation_start _) =>
      eapply VMPromising_Sail_promised_stable_sail_translation_start;
      exact Hstable
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.sail_translation_end _) =>
      apply VMPromising_Sail_promised_stable_sail_translation_end
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.sail_take_exception _) =>
      apply VMPromising_Sail_promised_stable_sail_take_exception;
      intros ppst;
      eapply VMPromising_read_code_control_bound;
      exact Hstable
  | Hstable : VMPromising_read_code_translation_stability _ _ _ _ _ _
    |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.sail_take_exception _) =>
      apply VMPromising_Sail_promised_stable_sail_take_exception;
      intros ppst;
      eapply VMPromising_read_code_control_bound;
      exact Hstable
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.choose_bool _) =>
      apply VMPromising_Sail_promised_stable_choose_bool
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.choose_bool _) =>
      apply VMPromising_Sail_promised_stable_choose_bool
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.undefined_bool _) =>
      apply VMPromising_Sail_promised_stable_undefined_bool
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.undefined_bool _) =>
      apply VMPromising_Sail_promised_stable_undefined_bool
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.read_memory _ _ _) =>
      unfold System.read_memory;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.iFetch _ _) =>
      unfold System.iFetch;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.rMem _ _ _) =>
      unfold System.rMem;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.rX _) =>
      unfold System.rX;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.wX _ _) =>
      unfold System.wX;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.rSP _) =>
      apply VMPromising_Sail_promised_stable_rSP
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.wSP _) =>
      unfold System.wSP;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.rSPS _) =>
      unfold System.rSPS;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.wSPS _ _) =>
      unfold System.wSPS;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.rXS _ _) =>
      apply VMPromising_Sail_promised_stable_rXS
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.wXS _ _ _) =>
      unfold System.wXS;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.rPC _) =>
      unfold System.rPC;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.wPC _) =>
      unfold System.wPC;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.eval_operand _ _) =>
      apply VMPromising_Sail_promised_stable_eval_operand
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.shift_reg _ _ _) =>
      apply VMPromising_Sail_promised_stable_shift_reg
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.check_load_store_alignment _ _) =>
      unfold System.check_load_store_alignment;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.create_writeAccessDescriptor _ _) =>
      unfold System.create_writeAccessDescriptor;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.create_RMWAccessDescriptor _ _ _) =>
      unfold System.create_RMWAccessDescriptor;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.create_readAccessDescriptor _ _ _) =>
      unfold System.create_readAccessDescriptor;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.create_iFetchAccessDescriptor _) =>
      unfold System.create_iFetchAccessDescriptor;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.dataMemoryBarrier _ _) =>
      unfold System.dataMemoryBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.dataSynchronizationBarrer _ _) =>
      unfold System.dataSynchronizationBarrer;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.instructionSynchronizationBarrier _) =>
      unfold System.instructionSynchronizationBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.autocast_m _) =>
      unfold System_types.Defs.autocast_m;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.autocast_m _) =>
      unfold Defs.autocast_m;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.take_exception _ _) =>
      unfold System.take_exception;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.handle_fault _) =>
      unfold System.handle_fault;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.translate_address _ _) =>
      unfold System.translate_address, System.pgt_walk,
        System.get_translation_base_address,
        System.create_AccessDescriptorTTW, System.ASID_read;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.decode_bitmask _ _ _ _) =>
      unfold System.decode_bitmask;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ (System.decode _) =>
      unfold System.decode, System.decodeLoadStoreRegister,
        System.decodeLoadStoreImmediate, System.decodeAddSubExt,
        System.decodeAddSubImm, System.decodeAddSubShift,
        System.decodeCompareAndBranch, System.decodeTestAndBranch,
        System.decodeDataBarrier, System.decodeTLBI,
        System.decodeSystemRegisterMove,
        System.decode_bitwise_op, System.decode_bitmask, System.fail;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.execute_SupervisorCall _) =>
      unfold System.execute_SupervisorCall;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.execute_Nop _) =>
      unfold System.execute_Nop;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.execute_Movz _ _ _ _) =>
      unfold System.execute_Movz;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.execute_Load _ _ _ _ _ _ _) =>
      unfold System.execute_Load;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _
        (System.execute_InstructionSynchronizationBarrier _) =>
      unfold System.execute_InstructionSynchronizationBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.execute_ExceptionReturn _) =>
      unfold System.execute_ExceptionReturn;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _
        (System.execute_DataSynchronizationBarrier _ _) =>
      unfold System.execute_DataSynchronizationBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.execute_DataMemoryBarrier _ _) =>
      unfold System.execute_DataMemoryBarrier;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.execute_CompareAndBranch _ _ _ _) =>
      unfold System.execute_CompareAndBranch;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System.execute_Branch _) =>
      unfold System.execute_Branch;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      eapply VMPromising_Sail_promised_stable_bind;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.bind _ _) =>
      unfold Defs.bind;
      eapply VMPromising_Sail_promised_stable_bind;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Interface.iMon_bind _ _) =>
      eapply VMPromising_Sail_promised_stable_bind;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Interface.iMon_bind _ _) =>
      eapply VMPromising_Sail_promised_stable_bind;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_promised_stable_bind0;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_promised_stable_bind0;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.try_catch _ _) =>
      eapply VMPromising_Sail_promised_stable_try_catch;
      [solve_VMPromising_Sail_promised_stable_read_code_translation
      |intro; solve_VMPromising_Sail_promised_stable_read_code_translation]
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.liftR _) =>
      apply VMPromising_Sail_promised_stable_liftR;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (Defs.liftR _) =>
      apply VMPromising_Sail_promised_stable_liftR;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.catch_early_return _) =>
      apply VMPromising_Sail_promised_stable_catch_early_return;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.foreach_ZM_up _ _ _ _ _) =>
      apply VMPromising_Sail_promised_stable_foreach_ZM_up;
      intros;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable
        _ _ _ _ _ _ (System_types.Defs.foreach_ZM_up' _ _ _ _ _ _) =>
      apply VMPromising_Sail_promised_stable_foreach_ZM_up';
      intros;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- context[match ?x with _ => _ end] =>
      destruct x;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- context[if ?x then _ else _] =>
      destruct x;
      solve_VMPromising_Sail_promised_stable_read_code_translation
  | |- VMPromising_Sail_promised_stable _ _ _ _ _ _ _ =>
      first
        [progress VMPromising_Sail_simpl;
         solve_VMPromising_Sail_promised_stable_read_code_translation
        |match goal with
         | |- ?G => fail 100 "VMP stable stuck:" G
         end]
  end.

Ltac solve_VMPromising_Sail_no_promise_exec_prefix :=
  solve_VMPromising_Sail_no_promise_exec.

Ltac solve_VMPromising_Sail_promised_stable_prefix :=
  solve_VMPromising_Sail_promised_stable_read_code_translation.

Ltac VMPromising_Sail_unfold_execute_helpers :=
  unfold System.execute_TLBInvalidation, System.execute_SupervisorCall,
    System.execute_Store, System.execute_Nop,
    System.execute_Movz, System.execute_Load,
    System.execute_InstructionSynchronizationBarrier,
    System.execute_ExceptionReturn,
    System.execute_DataSynchronizationBarrier,
    System.execute_DataMemoryBarrier, System.execute_CompareAndBranch,
    System.execute_Branch,
    System.translate_address, System.pgt_walk, System.handle_fault,
    System.take_exception, System.decode, System.decode_bitwise_op,
    System.decode_bitmask, System.decodeDataBarrier, System.decodeTLBI,
    System.get_translation_base_address, System.create_AccessDescriptorTTW,
    System.ASID_read, System.read_memory, System.rMem, System.wMem,
    System.iFetch, System.rX, System.wX,
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
        _ _ _ _ _ _ (System_types.Interface.Ret _) =>
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.returnM _) =>
      cbn [System_types.returnM];
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (returnM _) =>
      cbn [returnM System_types.returnM];
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.returnm _) =>
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.returnR _ _) =>
      exact I
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.early_return _) =>
      unfold System_types.Defs.early_return;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.early_return _) =>
      unfold Defs.early_return;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.fail _) =>
      apply VMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply VMPromising_Sail_no_promise_fail
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.throw _) =>
      apply VMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply VMPromising_Sail_no_promise_throw
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.sail_mem_write _ _ _) =>
      apply VMPromising_Sail_prefix_promised_stable_sail_mem_write
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.sail_mem_write _ _ _) =>
      apply VMPromising_Sail_prefix_promised_stable_sail_mem_write
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.sail_tlbi _) =>
      apply VMPromising_Sail_prefix_promised_stable_sail_tlbi
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.sail_tlbi _) =>
      apply VMPromising_Sail_prefix_promised_stable_sail_tlbi
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System.wMem _ _ _ _) =>
      unfold System.wMem;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System.reportTLBI _ _ _ _ _) =>
      unfold System.reportTLBI;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System.execute _) =>
      unfold System.execute;
      repeat match goal with
      | p : _ * _ |- _ => destruct p; cbn [System.execute]
      | u : unit |- _ => destruct u; cbn [System.execute]
      end;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System.execute_Store _ _ _ _ _ _) =>
      unfold System.execute_Store;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System.execute_TLBInvalidation _ _ _ _) =>
      unfold System.execute_TLBInvalidation;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply VMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec_prefix
         |solve_VMPromising_Sail_promised_stable_prefix
         |intro;
          solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
        |eapply VMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
         |intro; solve_VMPromising_Sail_no_promise_exec_prefix]]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.bind _ _) =>
      unfold Defs.bind;
      first
        [eapply VMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec_prefix
         |solve_VMPromising_Sail_promised_stable_prefix
         |intro;
          solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
        |eapply VMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
         |intro; solve_VMPromising_Sail_no_promise_exec_prefix]]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec_prefix
         |solve_VMPromising_Sail_promised_stable_prefix
         |intro;
          solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
        |eapply VMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
         |intro; solve_VMPromising_Sail_no_promise_exec_prefix]]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Interface.iMon_bind _ _) =>
      first
        [eapply VMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_VMPromising_Sail_no_promise_exec_prefix
         |solve_VMPromising_Sail_promised_stable_prefix
         |intro;
          solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
        |eapply VMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
         |intro; solve_VMPromising_Sail_no_promise_exec_prefix]]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.bind0 _ _) =>
      eapply VMPromising_Sail_prefix_promised_stable_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_exec_prefix
      |solve_VMPromising_Sail_promised_stable_prefix
      |solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply VMPromising_Sail_prefix_promised_stable_bind0_no_left;
      [solve_VMPromising_Sail_no_promise_exec_prefix
      |solve_VMPromising_Sail_promised_stable_read_code_translation
      |solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- context[Defs.bind] =>
      unfold Defs.bind;
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.liftR _) =>
      first
        [eapply VMPromising_Sail_prefix_promised_stable_liftR_no_left;
         [solve_VMPromising_Sail_no_promise_exec_prefix
         |solve_VMPromising_Sail_promised_stable_prefix]
        |eapply VMPromising_Sail_prefix_promised_stable_liftR_no_right;
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (Defs.liftR _) =>
      first
        [eapply VMPromising_Sail_prefix_promised_stable_liftR_no_left;
         [solve_VMPromising_Sail_no_promise_exec_prefix
         |solve_VMPromising_Sail_promised_stable_prefix]
        |eapply VMPromising_Sail_prefix_promised_stable_liftR_no_right;
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation]
  | |- VMPromising_Sail_prefix_promised_stable
        _ _ _ _ _ _ (System_types.Defs.catch_early_return _) =>
      first
        [eapply
         VMPromising_Sail_prefix_promised_stable_catch_early_return_no_left;
         [solve_VMPromising_Sail_no_promise_exec_prefix
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
  | |- VMPromising_Sail_prefix_promised_stable _ _ _ _ _ _ _ =>
      first
        [progress cbn [System_types.Defs.bind Defs.bind];
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
        |progress VMPromising_Sail_simpl;
         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation
        |apply VMPromising_Sail_prefix_promised_stable_from_no_promise;
         solve_VMPromising_Sail_no_promise_exec_prefix
        |match goal with
         | |- ?G => fail 100 "VMP prefix stable stuck:" G
         end]
  end.

Lemma VMPromising_Sail_prefix_promised_stable_execute_Store
    bbm_param n_threads tid initmem code ev nondet
    size t n offset release s :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System.execute_Store size t n offset release s).
Proof.
  intro Hstable.
  unfold System.execute_Store.
  eapply VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
  - solve_VMPromising_Sail_no_promise_exec.
  - solve_VMPromising_Sail_promised_stable_read_code_translation.
  - intro exclusive.
    cbn [System_types.Defs.bind].
    eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
    + solve_VMPromising_Sail_no_promise_exec.
    + solve_VMPromising_Sail_promised_stable_read_code_translation.
    + intro accdesc.
      cbn [System_types.Defs.bind].
      eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
      * destruct (Z.eqb n 31); solve_VMPromising_Sail_no_promise_exec.
      * destruct (Z.eqb n 31).
        -- apply VMPromising_Sail_promised_stable_liftR.
           apply VMPromising_Sail_promised_stable_rSP.
        -- apply VMPromising_Sail_promised_stable_liftR.
           apply VMPromising_Sail_promised_stable_rX.
      * intro base.
        cbn [System_types.Defs.bind].
        eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
        -- solve_VMPromising_Sail_no_promise_exec.
        -- apply VMPromising_Sail_promised_stable_liftR.
           apply VMPromising_Sail_promised_stable_eval_operand.
        -- intro offset_value.
           cbn [System_types.Defs.bind].
           eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
           ++ solve_VMPromising_Sail_no_promise_exec.
           ++ eapply VMPromising_Sail_promised_stable_bind0.
              ** apply VMPromising_Sail_promised_stable_liftR.
                 unfold System.check_load_store_alignment.
                 solve_VMPromising_Sail_promised_stable_read_code_translation.
              ** apply VMPromising_Sail_promised_stable_liftR.
                 unfold System.translate_address, System.pgt_walk,
                   System.get_translation_base_address,
                   System.create_AccessDescriptorTTW, System.ASID_read.
                 solve_VMPromising_Sail_promised_stable_read_code_translation.
           ++ intro addr_opt.
              cbn [System_types.Defs.bind].
              eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
              ** destruct addr_opt; solve_VMPromising_Sail_no_promise_exec.
              ** destruct addr_opt;
                   solve_VMPromising_Sail_promised_stable_read_code_translation.
              ** intro addr.
                 cbn [System_types.Defs.bind System_types.Defs.bind0].
                 eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
                 --- solve_VMPromising_Sail_no_promise_exec.
                 --- apply VMPromising_Sail_promised_stable_liftR.
                     apply VMPromising_Sail_promised_stable_read_reg.
                 --- intro pc.
                     cbn [System_types.Defs.bind System_types.Defs.bind0].
                     eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
                     +++ solve_VMPromising_Sail_no_promise_exec.
                     +++ eapply VMPromising_Sail_promised_stable_bind0.
                         *** apply VMPromising_Sail_promised_stable_liftR.
                             apply VMPromising_Sail_promised_stable_write_reg.
                             intros ppst.
                             eapply VMPromising_read_code_control_bound.
                             exact Hstable.
                         *** apply VMPromising_Sail_promised_stable_liftR.
                             apply VMPromising_Sail_promised_stable_rX.
                     +++ intro value.
                         eapply
                           VMPromising_Sail_prefix_promised_stable_liftR_no_right.
                         unfold System.wMem.
                         solve_VMPromising_Sail_prefix_promised_stable_read_code_translation.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_execute_AtomicRMW
    bbm_param n_threads tid initmem code ev nondet
    size s t n op acq rel :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System.execute_AtomicRMW size s t n op acq rel).
Proof.
  intro Hstable.
  unfold System.execute_AtomicRMW.
  eapply VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
  - solve_VMPromising_Sail_no_promise_exec.
  - solve_VMPromising_Sail_promised_stable_read_code_translation.
  - intro accdesc.
    cbn [System_types.Defs.bind].
    eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
    + destruct (Z.eqb n 31); solve_VMPromising_Sail_no_promise_exec.
    + destruct (Z.eqb n 31).
      * apply VMPromising_Sail_promised_stable_liftR.
        apply VMPromising_Sail_promised_stable_rSP.
      * apply VMPromising_Sail_promised_stable_liftR.
        apply VMPromising_Sail_promised_stable_rX.
    + intro vaddr.
      cbn [System_types.Defs.bind].
      eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
      * solve_VMPromising_Sail_no_promise_exec.
      * solve_VMPromising_Sail_promised_stable_read_code_translation.
      * intro addr_opt.
        cbn [System_types.Defs.bind].
        eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
        -- destruct addr_opt; solve_VMPromising_Sail_no_promise_exec.
        -- destruct addr_opt;
             solve_VMPromising_Sail_promised_stable_read_code_translation.
        -- intro addr.
           cbn [System_types.Defs.bind System_types.Defs.bind0].
           eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
           ++ solve_VMPromising_Sail_no_promise_exec.
           ++ apply VMPromising_Sail_promised_stable_liftR.
              apply VMPromising_Sail_promised_stable_read_reg.
           ++ intro pc.
              cbn [System_types.Defs.bind System_types.Defs.bind0].
              eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
              ** solve_VMPromising_Sail_no_promise_exec.
              ** solve_VMPromising_Sail_promised_stable_read_code_translation.
              ** intro old_value.
                 cbn [System_types.Defs.bind System_types.Defs.bind0].
                 eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
                 --- solve_VMPromising_Sail_no_promise_exec.
                 --- eapply VMPromising_Sail_promised_stable_bind0.
	                     { apply VMPromising_Sail_promised_stable_liftR.
	                       unfold System.wX.
	                       destruct (System.neq_int t 31).
	                       - apply VMPromising_Sail_promised_stable_write_reg_ref.
	                         intros ppst.
	                         eapply VMPromising_read_code_control_bound.
	                         exact Hstable.
	                       - exact I. }
                     { apply VMPromising_Sail_promised_stable_liftR.
                       apply VMPromising_Sail_promised_stable_rX. }
	                 --- intro operand_reg.
	                     cbn [System_types.Defs.bind].
	                     eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
	                     { destruct op; solve_VMPromising_Sail_no_promise_exec. }
	                     { destruct op;
	                         solve_VMPromising_Sail_promised_stable_read_code_translation. }
	                     { intro new_value.
	                       eapply
	                         VMPromising_Sail_prefix_promised_stable_liftR_no_right.
	                       unfold System.wMem.
	                       solve_VMPromising_Sail_prefix_promised_stable_read_code_translation. }
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_execute_TLBInvalidation
    bbm_param n_threads tid initmem code ev nondet op shareability t vmid :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System.execute_TLBInvalidation op shareability t vmid).
Proof.
  intro Hstable.
  unfold System.execute_TLBInvalidation.
  eapply VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
  - solve_VMPromising_Sail_no_promise_exec.
  - apply VMPromising_Sail_promised_stable_liftR.
    apply VMPromising_Sail_promised_stable_read_reg.
  - intro pc.
    cbn [System_types.Defs.bind System_types.Defs.bind0].
    eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
    + solve_VMPromising_Sail_no_promise_exec.
	    + eapply VMPromising_Sail_promised_stable_bind0.
	      * apply VMPromising_Sail_promised_stable_liftR.
	        apply VMPromising_Sail_promised_stable_write_reg.
	        intros ppst.
	        eapply VMPromising_read_code_control_bound.
	        exact Hstable.
      * destruct op; cbn [System_types.Defs.bind].
        all: try exact I.
        all: try (eapply VMPromising_Sail_promised_stable_bind;
                  [apply VMPromising_Sail_promised_stable_liftR;
                   apply VMPromising_Sail_promised_stable_rX
                  |intro; exact I]).
        all: unfold System_types.Defs.early_return;
          apply VMPromising_Sail_promised_stable_throw.
    + intros [va asid].
      eapply VMPromising_Sail_prefix_promised_stable_liftR_no_right.
      unfold System.reportTLBI.
      solve_VMPromising_Sail_prefix_promised_stable_read_code_translation.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_bind_liftR_create_iFetchAccessDescriptor
    bbm_param n_threads tid initmem ev nondet {B}
    (k : AccessDescriptor → System_types.Defs.monad (unit + unit)%type B) :
  (∀ accdesc,
    is_ifetch accdesc = true →
    VMPromising_Sail_prefix_promised_stable
      bbm_param n_threads tid initmem ev nondet (k accdesc)) →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet
    (System_types.Defs.bind
       (System_types.Defs.liftR (R:=unit)
          (System.create_iFetchAccessDescriptor tt))
       k).
Proof.
  intro Hk.
  unfold System.create_iFetchAccessDescriptor.
  cbn [System_types.Defs.liftR System_types.Defs.try_catch
       System_types.Defs.bind System_types.returnM
       System_types.Defs.returnm System_types.read_reg
       System_types.Interface.iMon_bind
       Defs.liftR Defs.try_catch Defs.bind Defs.returnm
       Defs.read_reg returnM Interface.iMon_bind].
  left.
  split.
  - exact I.
  - split.
    + unfold VMPromising_Sail_outcome_promised_stable.
      cbn [Sail_outcome_interp].
      unfold mcall.
      cbn [imon_future_promise_stable_promised].
      split.
      * apply reg_read_outcome_future_promise_stable_promised.
      * intro.
        exact I.
    + intro current_el.
    apply Hk.
    vm_compute.
    reflexivity.
Qed.

Lemma VMPromising_Sail_prefix_promised_stable_fetch_and_execute_from_read_code_translation
    bbm_param n_threads tid initmem code ev nondet :
  VMPromising_read_code_translation_stability
    bbm_param n_threads tid initmem code ev →
  VMPromising_Sail_prefix_promised_stable
    bbm_param n_threads tid initmem ev nondet (System.fetch_and_execute tt).
Proof.
  intro Hstable.
  unfold System.fetch_and_execute.
  eapply VMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply VMPromising_Sail_prefix_promised_stable_bind_liftR_create_iFetchAccessDescriptor.
  intro accdesc.
  intro Hacc_ifetch.
    cbn [System_types.Defs.bind].
    eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
    + solve_VMPromising_Sail_no_promise_exec.
    + solve_VMPromising_Sail_promised_stable_read_code_translation.
    + intro pc.
      cbn [System_types.Defs.bind].
      eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
      * solve_VMPromising_Sail_no_promise_exec.
      * solve_VMPromising_Sail_promised_stable_read_code_translation.
      * intro addr_opt.
        cbn [System_types.Defs.bind].
        eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
        -- destruct addr_opt; solve_VMPromising_Sail_no_promise_exec.
        -- destruct addr_opt;
             solve_VMPromising_Sail_promised_stable_read_code_translation.
        -- intro addr_ret.
           cbn [System_types.Defs.bind].
           eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
           ++ solve_VMPromising_Sail_no_promise_exec.
           ++ apply VMPromising_Sail_promised_stable_liftR.
              unfold System.iFetch, System.read_memory.
              cbn [System_types.Defs.bind].
              eapply VMPromising_Sail_promised_stable_bind.
              ** eapply
                   VMPromising_Sail_promised_stable_sail_mem_read_ifetch.
                 --- exact Hacc_ifetch.
                 --- exact Hstable.
              ** intros [[bytes tags]|fault].
                 --- exact I.
                 --- apply VMPromising_Sail_promised_stable_exit.
           ++ intro machineCode.
              cbn [System_types.Defs.bind].
              eapply VMPromising_Sail_prefix_promised_stable_bind_no_left.
              ** solve_VMPromising_Sail_no_promise_exec.
              ** solve_VMPromising_Sail_promised_stable_read_code_translation.
              ** intro instr.
                 eapply
                   VMPromising_Sail_prefix_promised_stable_liftR_no_right.
                 unfold System.execute;
                 destruct instr; cbn [System.execute];
                 repeat match goal with
                 | p : _ * _ |- _ => destruct p; cbn [System.execute]
                 | u : unit |- _ => destruct u; cbn [System.execute]
                 end;
                 lazymatch goal with
                 | |- VMPromising_Sail_prefix_promised_stable
                       _ _ _ _ _ _ (System.execute_Store _ _ _ _ _ _) =>
                     eapply
                       VMPromising_Sail_prefix_promised_stable_execute_Store;
                     exact Hstable
                 | |- VMPromising_Sail_prefix_promised_stable
                       _ _ _ _ _ _
                       (System.execute_TLBInvalidation _ _ _ _) =>
                     eapply
                       VMPromising_Sail_prefix_promised_stable_execute_TLBInvalidation;
                     exact Hstable
                 | |- VMPromising_Sail_prefix_promised_stable
                       _ _ _ _ _ _ (System.execute_AtomicRMW _ _ _ _ _ _ _) =>
                     eapply
                       VMPromising_Sail_prefix_promised_stable_execute_AtomicRMW;
                     exact Hstable
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_Load _ _ _ _ _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_Load
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_BitwiseLogic _ _ _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_BitwiseLogic
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_Movz _ _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_Movz
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_BitfieldMove _ _ _ _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_BitfieldMove
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_AddSub _ _ _ _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_AddSub
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_CompareAndBranch _ _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_CompareAndBranch
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_TestAndBranch _ _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_TestAndBranch
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_Branch _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_Branch
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_ConditionalBranch _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_ConditionalBranch
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_PCRelativeAddress _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_PCRelativeAddress
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_BranchRegister _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_BranchRegister
	                 | |- VMPromising_Sail_prefix_promised_stable
	                       _ _ _ _ _ _ (System.execute_SystemRegisterMove _ _ _) =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     apply VMPromising_Sail_no_promise_execute_SystemRegisterMove
	                 | _ =>
	                     apply
	                       VMPromising_Sail_prefix_promised_stable_from_no_promise;
	                     solve_VMPromising_Sail_no_promise_exec
	                 end.
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
    bbm_param n (tid : nat) initmem ev nondet smon →
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
