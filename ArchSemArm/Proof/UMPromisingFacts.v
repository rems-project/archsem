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
From ASCommon Require Import Common Exec FMon StateT.

From ArchSem Require Import GenPromising.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import GenPromisingProof.

#[local] Open Scope stdpp.

Import Promising.

#[local] Typeclasses Transparent Memory.t.

Lemma memory_read_last_cons_miss addr init mem msg :
  Msg.read_byte addr msg = None →
  Memory.read_last addr init (msg :: mem) = Memory.read_last addr init mem.
Proof.
  intro Hmiss.
  cbn.
  rewrite Hmiss.
  reflexivity.
Qed.

Lemma memory_read_initial_cons_miss addr init mem msg :
  Msg.read_byte addr msg = None →
  Memory.read_initial addr init (msg :: mem) =
  Memory.read_initial addr init mem.
Proof.
  intro Hmiss.
  unfold Memory.read_initial.
  rewrite memory_read_last_cons_miss by exact Hmiss.
  reflexivity.
Qed.

Lemma memory_read_from_cons_old addr size tread init mem msg :
  (tread ≤ length mem)%nat →
  Memory.read_from addr size tread init (msg :: mem) =
  Memory.read_from addr size tread init mem.
Proof.
  intro Hle.
  unfold Memory.read_from, Memory.cut_before.
  rewrite PromMemoryFacts.cut_before_cons_old by exact Hle.
  reflexivity.
Qed.

Lemma memory_fulfill_none_no_match msg prom mem t :
  Memory.fulfill msg prom mem = None →
  t ∈ prom →
  mem !! t ≠ Some msg.
Proof.
  unfold Memory.fulfill.
  rewrite list_basics.head_reverse.
  intro Hfulfill.
  apply list_basics.last_None in Hfulfill.
  intros Hprom Hlookup.
  pose proof (list_basics.filter_nil_not_elem_of
    (λ t, mem !! t = Some msg) prom t Hfulfill Hlookup) as Hnot.
  exact (Hnot Hprom).
Qed.

Lemma last_cons_all_eq {A} (x : A) (l : list A) :
  (∀ y, y ∈ l → y = x) →
  last (x :: l) = Some x.
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
  unfold Memory.fulfill.
  rewrite list_basics.head_reverse.
  rewrite list_basics.filter_cons_True.
  - apply last_cons_all_eq.
    intros t Hmatch.
    rewrite list_basics.elem_of_list_filter in Hmatch.
    destruct Hmatch as [Hlookup Hprom].
    apply PromMemoryFacts.lookup_cons_inv_same in Hlookup
      as [Hold_lookup|Htime].
    + exfalso.
      eapply Hno_match; eauto.
    + exact Htime.
  - subst time.
    apply PromMemoryFacts.lookup_latest.
Qed.

Lemma TState_promise_update_vcap p v ts :
  TState.update TState.vcap v (TState.promise p ts) =
  TState.promise p (TState.update TState.vcap v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_coh p loc v ts :
  TState.update_coh loc v (TState.promise p ts) =
  TState.promise p (TState.update_coh loc v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_cohs avs p ts :
  TState.update_cohs avs (TState.promise p ts) =
  TState.promise p (TState.update_cohs avs ts).
Proof.
  unfold TState.update_cohs.
  revert ts.
  induction avs as [|[a v] avs IH]; intro ts; cbn.
  - reflexivity.
  - rewrite IH.
    apply TState_promise_update_coh.
Qed.

Lemma TState_promise_update_vrd p v ts :
  TState.update TState.vrd v (TState.promise p ts) =
  TState.promise p (TState.update TState.vrd v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vwr p v ts :
  TState.update TState.vwr v (TState.promise p ts) =
  TState.promise p (TState.update TState.vwr v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vacq p v ts :
  TState.update TState.vacq v (TState.promise p ts) =
  TState.promise p (TState.update TState.vacq v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vrel p v ts :
  TState.update TState.vrel v (TState.promise p ts) =
  TState.promise p (TState.update TState.vrel v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vdmb p v ts :
  TState.update TState.vdmb v (TState.promise p ts) =
  TState.promise p (TState.update TState.vdmb v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vdmbst p v ts :
  TState.update TState.vdmbst v (TState.promise p ts) =
  TState.promise p (TState.update TState.vdmbst v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_visb p v ts :
  TState.update TState.visb v (TState.promise p ts) =
  TState.promise p (TState.update TState.visb v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_set_xclb p tread addr size vpost ts :
  TState.set_xclb tread addr size vpost (TState.promise p ts) =
  TState.promise p (TState.set_xclb tread addr size vpost ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_clear_xclb p ts :
  TState.clear_xclb (TState.promise p ts) =
  TState.promise p (TState.clear_xclb ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_set_fwdb p addr fi ts :
  TState.set_fwdb addr fi (TState.promise p ts) =
  TState.promise p (TState.set_fwdb addr fi ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_set_fwdbs p addrs time vdata xcl ts :
  TState.set_fwdbs addrs time vdata xcl (TState.promise p ts) =
  TState.promise p (TState.set_fwdbs addrs time vdata xcl ts).
Proof.
  unfold TState.set_fwdbs.
  induction addrs as [|addr addrs IH]; cbn.
  - reflexivity.
  - rewrite IH.
    apply TState_promise_set_fwdb.
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

Lemma TState_set_reg_promise p reg rv ts ts' :
  TState.set_reg reg rv ts = Some ts' →
  TState.set_reg reg rv (TState.promise p ts) =
  Some (TState.promise p ts').
Proof.
  destruct ts as [prom regs coh vrd vwr vdmbst vdmb vcap visb vacq vrel
    fwdb xclb].
  unfold TState.set_reg, TState.promise.
  cbn.
  destruct (decide (is_Some (dmap_lookup reg regs))) as [Hsome|Hnone];
    cbn; intro Hset; inversion Hset; subst; reflexivity.
Qed.

Lemma TState_set_reg_promise_update_vcap p v reg rv ts ts' :
  TState.set_reg reg rv (TState.update TState.vcap v ts) = Some ts' →
  TState.set_reg reg rv
    (TState.update TState.vcap v (TState.promise p ts)) =
  Some (TState.promise p ts').
Proof.
  rewrite TState_promise_update_vcap.
  apply TState_set_reg_promise.
Qed.

Definition code_region := address → Prop.

Definition event_misses_code (code : code_region) (msg : Msg.t) : Prop :=
  ∀ a, code a → Msg.read_byte a msg = None.

Definition ifetch_in_code (code : code_region) (addr : address) (size : N) :
    Prop :=
  ∀ a, a ∈ addr_range addr size → code a.

Definition event_misses_ifetch (msg : Msg.t) (addr : address) (size : N) :
    Prop :=
  ∀ a, a ∈ addr_range addr size → Msg.read_byte a msg = None.

Lemma event_misses_code_ifetch code msg addr size :
  event_misses_code code msg →
  ifetch_in_code code addr size →
  event_misses_ifetch msg addr size.
Proof.
  intros Hmiss Hifetch a Ha.
  apply Hmiss.
  apply Hifetch.
  exact Ha.
Qed.

Lemma read_imem_cons_miss addr init mem msg :
  event_misses_ifetch msg addr 4 →
  read_imem addr init (msg :: mem) = read_imem addr init mem.
Proof.
  intro Hmiss.
  unfold read_imem.
  set (addrs := addr_range addr 4).
  assert (Hall : ∀ a, a ∈ addrs → Msg.read_byte a msg = None).
  { intros a Ha.
    subst addrs.
    apply Hmiss.
    exact Ha. }
  assert
    (Hbytes :
       (for a in addrs do
          Memory.read_initial a init (msg :: mem)
        end) =
       (for a in addrs do
          Memory.read_initial a init mem
        end)).
  { induction addrs as [|a addrs IH].
    - reflexivity.
    - cbn.
      rewrite memory_read_initial_cons_miss.
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

Lemma read_imem_cons_misses_code code addr init mem msg :
  event_misses_code code msg →
  ifetch_in_code code addr 4 →
  read_imem addr init (msg :: mem) = read_imem addr init mem.
Proof.
  intros Hmiss Hifetch.
  apply read_imem_cons_miss.
  eapply event_misses_code_ifetch; eauto.
Qed.

Lemma read_candidates_cons_old addr size vpre mem msg t :
  (vpre ≤ length mem)%nat →
  t ∈ read_candidates addr size vpre mem →
  t ∈ read_candidates addr size vpre (msg :: mem).
Proof.
  intros Hle Ht.
  unfold read_candidates in Ht |- *.
  rewrite PromMemoryFacts.cut_after_with_timestamps_cons_old by exact Hle.
  cbn.
  destruct (decide (addr_overlap addr size (Msg.addr msg) (Msg.size msg)));
    set_solver.
Qed.

Lemma read_candidates_time_le addr size vpre mem t :
  (vpre ≤ length mem)%nat →
  t ∈ read_candidates addr size vpre mem →
  (t ≤ length mem)%nat.
Proof.
  intros Hle Ht.
  unfold read_candidates in Ht.
  apply elem_of_cons in Ht as [->|Ht]; [exact Hle|].
  rewrite elem_of_list_omap in Ht.
  destruct Ht as [[msg t0] [Hin Hsome]].
  destruct (decide (addr_overlap addr size (Msg.addr msg) (Msg.size msg)));
    cbn in Hsome; inversion Hsome; subst t0.
  eapply PromMemoryFacts.cut_after_with_timestamps_time_le.
  exact Hin.
Qed.

Definition fwdb_times_le (mem : Memory.t) (ts : TState.t) : Prop :=
  ∀ a fwd, ts.(TState.fwdb) !! a = Some fwd →
    (fwd.(FwdItem.time) ≤ length mem)%nat.

Definition read_mem_vpre (vaddr : view) (macc : mem_acc) (ts : TState.t) :
    view :=
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  vaddr ⊔ vbob.

Lemma read_mem_vpre_promise vaddr macc v ts :
  read_mem_vpre vaddr macc (TState.promise v ts) =
  read_mem_vpre vaddr macc ts.
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma fwdb_times_le_promise mem v ts :
  fwdb_times_le mem (TState.promise v ts) ↔ fwdb_times_le mem ts.
Proof.
  destruct ts.
  unfold fwdb_times_le.
  cbn.
  split; auto.
Qed.

Lemma read_fwd_cons_old fwdb macc mem tread a msg :
  (∀ fwd, fwdb !! a = Some fwd →
    (fwd.(FwdItem.time) ≤ length mem)%nat) →
  read_fwd fwdb macc (msg :: mem) tread a =
  read_fwd fwdb macc mem tread a.
Proof.
  intros Hbound.
  unfold read_fwd.
  destruct (fwdb !! a) as [fwd|] eqn:Hfwd; [|reflexivity].
  destruct (tread <? FwdItem.time fwd)%nat; [|reflexivity].
  rewrite PromMemoryFacts.lookup_cons_old
    by (apply (Hbound fwd); reflexivity).
  reflexivity.
Qed.

Lemma read_fwd_list_cons_old fwdb macc mem tread addrs raws msg :
  (∀ a fwd, a ∈ addrs → fwdb !! a = Some fwd →
    (fwd.(FwdItem.time) ≤ length mem)%nat) →
  (for ar in zip addrs raws do
     let '(a, raw) := ar in
     read_fwd fwdb macc (msg :: mem) tread a
       |$> default (raw.1, tread, raw.2)
   end) =
  (for ar in zip addrs raws do
     let '(a, raw) := ar in
     read_fwd fwdb macc mem tread a
       |$> default (raw.1, tread, raw.2)
   end).
Proof.
  revert raws.
  induction addrs as [|a addrs IH]; intros [|raw raws] Hbound;
    cbn; try reflexivity.
  rewrite read_fwd_cons_old.
  - rewrite IH.
    + reflexivity.
    + intros a' fwd Ha' Hfwd.
      apply (Hbound a' fwd); [right; exact Ha'|exact Hfwd].
  - intros fwd Hfwd.
    apply (Hbound a fwd); [left; reflexivity|exact Hfwd].
Qed.

Lemma read_fwd_list_cons_old_nested fwdb macc mem tread addrs raws msg :
  (∀ a fwd, a ∈ addrs → fwdb !! a = Some fwd →
    (fwd.(FwdItem.time) ≤ length mem)%nat) →
  (for (a, (byte, twrite)) in zip addrs raws do
     read_fwd fwdb macc (msg :: mem) tread a
       |$> default (byte, tread, twrite)
   end) =
  (for (a, (byte, twrite)) in zip addrs raws do
     read_fwd fwdb macc mem tread a
       |$> default (byte, tread, twrite)
   end).
Proof.
  revert raws.
  induction addrs as [|a addrs IH]; intros [|[byte twrite] raws] Hbound;
    cbn; try reflexivity.
  rewrite read_fwd_cons_old.
  - rewrite IH.
    + reflexivity.
    + intros a' fwd Ha' Hfwd.
      apply (Hbound a' fwd); [right; exact Ha'|exact Hfwd].
  - intros fwd Hfwd.
    apply (Hbound a fwd); [left; reflexivity|exact Hfwd].
Qed.

Definition UMPromising_promise_ppstate (tid : nat) (initmem : memoryMap) msg
    (ppst : PPState.t TState.t Msg.t IIS.t) :
    PPState.t TState.t Msg.t IIS.t :=
  let mem := msg :: PPState.mem ppst in
  PPState.Make
    (TState.promise (length mem) (PPState.state ppst))
    mem
    (PPState.iis ppst).

Lemma UMPromising_promise_ppstate_eq_CPState {n} (tid : fin n)
    initmem msg ppst :
  UMPromising_promise_ppstate tid initmem msg ppst =
  CPStateProof.promise_ppstate UMPromising tid initmem msg ppst.
Proof.
  destruct ppst.
  reflexivity.
Qed.

Definition ppstate_read_times_le macc
    (ppst : PPState.t TState.t Msg.t IIS.t) : Prop :=
  (read_mem_vpre (IIS.strict (PPState.iis ppst)) macc
     (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  fwdb_times_le (PPState.mem ppst) (PPState.state ppst).

Definition ppstate_control_times_le
    (ppst : PPState.t TState.t Msg.t IIS.t) : Prop :=
  (IIS.strict (PPState.iis ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vrd (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vwr (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  (TState.vcap (PPState.state ppst) ≤ length (PPState.mem ppst))%nat.

Lemma TState_no_promises_until_promise v p ts :
  (v < p)%nat →
  TState.no_promises_until v ts →
  TState.no_promises_until v (TState.promise p ts).
Proof.
  intros Hvp Hnp p0 Hp0.
  apply elem_of_cons in Hp0 as [->|Hp0].
  - exact Hvp.
  - apply Hnp.
    exact Hp0.
Qed.

Lemma ppstate_read_times_le_promise macc p ppst :
  ppstate_read_times_le macc
    (PPState.Make (TState.promise p (PPState.state ppst))
       (PPState.mem ppst) (PPState.iis ppst)) ↔
  ppstate_read_times_le macc ppst.
Proof.
  destruct ppst as [ts mem iis].
  unfold ppstate_read_times_le.
  cbn.
  rewrite read_mem_vpre_promise.
  rewrite fwdb_times_le_promise.
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

Lemma elem_of_unfolded_ppstate_mset_iis st mem iis upd :
  Exec.elem_of_results (PPState.Make st mem (upd iis), ())
    ((((λ s : PPState.t TState.t Msg.t IIS.t,
          {| Exec.results := [(s, s)]; Exec.errors := [] |})
        : Exec.t (PPState.t TState.t Msg.t IIS.t) string
            (PPState.t TState.t Msg.t IIS.t))
      ≫= λ s : PPState.t TState.t Msg.t IIS.t,
            ((λ _ : PPState.t TState.t Msg.t IIS.t,
                {| Exec.results := [(set PPState.iis upd s, ())];
                   Exec.errors := [] |})
             : Exec.t (PPState.t TState.t Msg.t IIS.t) string unit))
       (PPState.Make st mem iis)).
Proof.
  change (PPState.Make st mem (upd iis))
    with (set PPState.iis upd (PPState.Make st mem iis)).
  apply Exec.elem_of_unfolded_mset.
Qed.

Lemma read_mem_promise_cons_old addr size macc init msg ppst ppst' res :
  ppstate_read_times_le macc ppst →
  Exec.elem_of_results (ppst', res) (read_mem addr size macc init ppst) →
  Exec.elem_of_results
    (UMPromising_promise_ppstate 0 init msg ppst', res)
    (read_mem addr size macc init
       (UMPromising_promise_ppstate 0 init msg ppst)).
Proof.
  destruct ppst as [ts mem iis].
  intros [Hvpre Hfwdb] Hrun.
  unfold UMPromising_promise_ppstate in *.
  cbn in *.
  set (pnew := length (msg :: mem)).
  unfold read_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_iis [vaddr [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_np [p_np [Hnp_guard Hrun]]].
  pose proof p_np as Hnp.
  apply Exec.elem_of_guard_discard_inv in Hnp_guard as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_mem [mem0 [Hget_mem Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_mem as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_choose [tread [Hchoose Hrun]]].
  apply Exec.elem_of_fmap_inv in Hchoose as [idx [Htread_eq Hchoose]].
  assert (pp_choose = PPState.Make ts mem iis) as ->.
  { unfold elem_of, Exec.elem_of_results in Hchoose.
    cbn in Hchoose.
    apply elem_of_cons in Hchoose as [Heq|Hchoose].
    - inversion Heq.
      reflexivity.
    - rewrite elem_of_list_fmap in Hchoose.
      destruct Hchoose as [idx' [Heq _]].
      inversion Heq.
      reflexivity. }
  assert
    (Htread :
       (list_to_vec
          (read_candidates addr size (read_mem_vpre (IIS.strict iis) macc ts)
             mem) !!! idx) ∈
       read_candidates addr size (read_mem_vpre (IIS.strict iis) macc ts) mem).
  { apply elem_of_list_lookup.
    exists (idx : nat).
    pose proof
      (proj1
         (vlookup_lookup
            (list_to_vec
               (read_candidates addr size
                  (read_mem_vpre (IIS.strict iis) macc ts) mem))
            idx
            (list_to_vec
               (read_candidates addr size
                  (read_mem_vpre (IIS.strict iis) macc ts) mem) !!! idx))
         eq_refl) as Hlookup.
    rewrite vec_to_list_to_vec in Hlookup.
    exact Hlookup. }
  rewrite <- Htread_eq in Htread.
  pose proof (read_candidates_time_le addr size
    (read_mem_vpre (IIS.strict iis) macc ts) mem tread Hvpre Htread)
    as Htread_le.
  pose proof (read_candidates_cons_old addr size
    (read_mem_vpre (IIS.strict iis) macc ts) mem msg tread Hvpre Htread)
    as Htread_new.
  set (iis_rmw :=
    if is_atomic_rmw macc then
      set IIS.rmw_read (λ _ : option (nat * bool),
        Some (tread, is_rel_acq macc)) iis
    else iis).
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_rmw [u [Hrmw Hrun]]].
  destruct u.
  assert (Hpp_rmw : pp_rmw = PPState.Make ts mem iis_rmw).
  {
    subst iis_rmw.
    destruct (is_atomic_rmw macc) eqn:Hatomic_macc.
    - unfold msetv in Hrmw.
      apply Exec.elem_of_mset_inv in Hrmw as ->.
      reflexivity.
    - apply Exec.elem_of_mret_inv in Hrmw as [-> _].
      reflexivity.
  }
  subst pp_rmw.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_raw [raw_bytes [Hraw Hrun]]].
  unfold othrow in Hraw.
  destruct (Memory.read_from addr size tread init mem) as [raw_bytes0|]
    eqn:Hread_old; rewrite Hread_old in Hraw; cbn in Hraw.
  2: {
    unfold mthrow, Exec.throw_inst, elem_of, Exec.elem_of_results in Hraw.
    cbn in Hraw.
    exfalso.
    exact (not_elem_of_nil _ Hraw).
  }
  apply Exec.elem_of_mret_inv in Hraw as [-> Hraw_eq].
  inversion Hraw_eq; subst raw_bytes0.
  pose proof (memory_read_from_cons_old addr size tread init mem msg Htread_le)
    as Hread_from.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_bytes [fwd_bytes [Hbytes Hrun]]].
  apply Exec.elem_of_lift_res_inv in Hbytes as [-> Hbytes].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_coh [pcoh [Hcoh Hrun]]].
  pose proof pcoh as Hcoh_prop.
  apply Exec.elem_of_guard_discard_inv in Hcoh as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_cohs [[] [Hcohs Hrun]]].
  apply Exec.elem_of_mset_inv in Hcohs as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vrd [[] [Hvrd Hrun]]].
  apply Exec.elem_of_mset_inv in Hvrd as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vacq [[] [Hvacq Hrun]]].
  apply Exec.elem_of_mset_inv in Hvacq as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vcap [[] [Hvcap Hrun]]].
  apply Exec.elem_of_mset_inv in Hvcap as ->.

  eapply Exec.elem_of_bind_intro with
    (e := (mget PPState.state :
             Exec.t (PPState.t TState.t Msg.t IIS.t) string TState.t))
    (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
    (a := TState.promise pnew ts).
  - apply (Exec.elem_of_mget (E:=string)
      (PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
      PPState.state).
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (e := (mget (IIS.strict ∘ PPState.iis) :
               Exec.t (PPState.t TState.t Msg.t IIS.t) string view))
      (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
      (a := IIS.strict iis).
    + apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
        (IIS.strict ∘ PPState.iis)).
    + cbn.
        assert (Hnp_promise :
          TState.no_promises_until (IIS.strict iis) (TState.promise pnew ts)).
        { intros p Hin.
          apply elem_of_cons in Hin as [->|Hin].
          - subst pnew.
            assert (Hstrict :
              (IIS.strict iis ≤ read_mem_vpre (IIS.strict iis) macc ts)%nat).
            { unfold read_mem_vpre.
              apply Nat.le_max_l. }
            apply Nat.lt_succ_r.
            etransitivity; [exact Hstrict|exact Hvpre].
          - apply Hnp.
            exact Hin. }
        destruct (Exec.elem_of_guard_discard
          (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
          (P:=TState.no_promises_until (IIS.strict iis)
                (TState.promise pnew ts))
          (PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
          Hnp_promise) as [p_np' Hnp'].
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard
                  (TState.no_promises_until (IIS.strict iis)
                     (TState.promise pnew ts)))
          (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
          (a := p_np').
        -- exact Hnp'.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (e := (mget PPState.mem :
                      Exec.t (PPState.t TState.t Msg.t IIS.t) string Memory.t))
             (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
             (a := msg :: mem).
           ++ apply (Exec.elem_of_mget (E:=string)
                (PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
                PPState.mem).
           ++ cbn.
              eapply Exec.elem_of_bind_intro with
                (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
                (a := tread).
              ** change (Exec.elem_of_results
                   (PPState.Make (TState.promise pnew ts) (msg :: mem) iis, tread)
                   ((mchoosel
                       (read_candidates addr size
                          (read_mem_vpre (IIS.strict iis) macc ts)
                          (msg :: mem)) :
                      Exec.t (PPState.t TState.t Msg.t IIS.t) string nat)
                     (PPState.Make (TState.promise pnew ts) (msg :: mem) iis))).
	                 apply Exec.elem_of_mchoosel.
	                 exact Htread_new.
		              ** cbn.
	                         unfold msetv, mset, mSet.
	                         eapply Exec.elem_of_bind_intro with
	                           (st' := PPState.Make (TState.promise pnew ts)
	                                    (msg :: mem) iis_rmw)
	                           (a := ()).
	                         --- unfold iis_rmw.
	                             destruct (is_atomic_rmw macc) eqn:Hatomic_macc.
	                             { change (S (length mem)) with pnew.
	                               change (PPState.Make (TState.promise pnew ts)
	                                 (msg :: mem)
	                                 (set IIS.rmw_read
	                                    (λ _ : option (nat * bool),
	                                      Some (tread, is_rel_acq macc)) iis))
	                                 with
	                                 (set (IIS.rmw_read ∘ PPState.iis)
	                                    (λ _ : option (nat * bool),
	                                      Some (tread, is_rel_acq macc))
	                                    (PPState.Make (TState.promise pnew ts)
	                                       (msg :: mem) iis)).
	                               apply (Exec.elem_of_unfolded_mset
	                                 (E:=string)
	                                 (PPState.Make (TState.promise pnew ts)
	                                 (msg :: mem) iis)
	                                 (IIS.rmw_read ∘ PPState.iis)
	                                 (λ _ : option (nat * bool),
	                                    Some (tread, is_rel_acq macc))). }
	                             { apply Exec.elem_of_mret. }
	                         --- cbn.
	                 eapply Exec.elem_of_bind_intro with
	                   (e := othrow "Memory read of unmapped bytes"
	                           (Memory.read_from addr size tread init (msg :: mem)))
	                   (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis_rmw)
	                   (a := raw_bytes).
		                 +++ unfold othrow.
		                     rewrite Hread_from.
		                     rewrite Hread_old.
		                     apply Exec.elem_of_mret.
	                 +++ cbn.
	                     eapply Exec.elem_of_bind_intro with
                       (e := mlift
                         (for (addr0, (byte, twrite)) in
                            zip (addr_range addr size) raw_bytes do
                            read_fwd (TState.fwdb (TState.promise pnew ts))
                              macc (msg :: mem) tread addr0
                              |$> default (byte, tread, twrite)
                          end))
	                       (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis_rmw)
	                       (a := fwd_bytes).
		                     *** apply Exec.elem_of_lift_res.
	                         cbn.
	                         replace (TState.fwdb (TState.promise pnew ts))
	                           with (TState.fwdb ts) by (destruct ts; reflexivity).
	                         rewrite (read_fwd_list_cons_old_nested
	                           (TState.fwdb ts) macc mem tread
	                           (addr_range addr size) raw_bytes msg).
	                         { exact Hbytes. }
	                         intros a fwd _ Hfwd.
	                         exact (Hfwdb a fwd Hfwd).
	                     *** cbn.
                         assert (Hcoh_promise :
                           ∀ '(a, t) ∈ zip (addr_range addr size) fwd_bytes.*2,
                             (TState.coh (TState.promise pnew ts) !!! a ≤ t)%nat).
                         { intros [a t] Hin.
                           destruct ts.
                           cbn in Hcoh_prop |- *.
                           apply (Hcoh_prop (a, t) Hin). }
                         destruct (Exec.elem_of_guard_discard
                           (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
                           (P:=∀ '(a, t) ∈ zip (addr_range addr size) fwd_bytes.*2,
                                (TState.coh (TState.promise pnew ts) !!! a ≤ t)%nat)
	                           (PPState.Make (TState.promise pnew ts) (msg :: mem) iis_rmw)
	                           Hcoh_promise) as [pcoh' Hcoh'].
                         eapply Exec.elem_of_bind_intro with
                           (e := guard_discard
                             (∀ '(a, t) ∈ zip (addr_range addr size) fwd_bytes.*2,
                                (TState.coh (TState.promise pnew ts) !!! a ≤ t)%nat))
	                           (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis_rmw)
	                           (a := pcoh').
	                         ---- exact Hcoh'.
	                         ---- cbn.
                             set (vpost :=
                               read_mem_vpre (IIS.strict iis) macc ts ⊔
                               foldr max 0%nat fwd_bytes.*1.*2).
                             eapply Exec.elem_of_bind_intro
                               with
                                 (st' := PPState.Make
                                   (TState.promise pnew
                                      (TState.update_cohs
                                         (zip (addr_range addr size) fwd_bytes.*2) ts))
	                                   (msg :: mem) iis_rmw)
	                                 (a := ()).
		                             ++++ rewrite <- TState_promise_update_cohs.
	                                  change (S (length mem)) with pnew.
	                                  change
	                                    ({|
	                                      PPState.state :=
	                                        TState.update_cohs
	                                          (zip (addr_range addr size)
	                                             fwd_bytes.*2)
	                                          (TState.promise pnew ts);
	                                      PPState.mem := msg :: mem;
		                                      PPState.iis := iis_rmw
		                                    |})
	                                    with
	                                    (set PPState.state
	                                       (TState.update_cohs
	                                          (zip (addr_range addr size)
	                                             fwd_bytes.*2))
		                                       (PPState.Make (TState.promise pnew ts)
		                                          (msg :: mem) iis_rmw)).
		                                  apply (Exec.elem_of_unfolded_mset (E:=string)
		                                    (PPState.Make (TState.promise pnew ts)
		                                       (msg :: mem) iis_rmw)
		                                    PPState.state
	                                    (TState.update_cohs
	                                       (zip (addr_range addr size)
	                                          fwd_bytes.*2))).
	                             ++++ cbn.
                                  eapply Exec.elem_of_bind_intro
                                    with
                                      (st' := PPState.Make
                                        (TState.promise pnew
                                          (TState.update TState.vrd vpost
                                            (TState.update_cohs
                                              (zip (addr_range addr size) fwd_bytes.*2)
                                              ts)))
	                                        (msg :: mem) iis_rmw)
                                      (a := ()).
		                                  { rewrite <- TState_promise_update_vrd.
		                                    change (S (length mem)) with pnew.
		                                    apply elem_of_unfolded_ppstate_mset_state. }
                                  cbn.
                                  eapply Exec.elem_of_bind_intro
                                    with
                                      (st' := PPState.Make
                                        (TState.promise pnew
                                          (TState.update TState.vacq
                                            (view_if (is_rel_acq macc) vpost)
                                            (TState.update TState.vrd vpost
                                              (TState.update_cohs
                                                (zip (addr_range addr size)
                                                  fwd_bytes.*2) ts))))
	                                        (msg :: mem) iis_rmw)
                                      (a := ()).
		                                  { rewrite <- TState_promise_update_vacq.
		                                    change (S (length mem)) with pnew.
		                                    apply elem_of_unfolded_ppstate_mset_state. }
                                  cbn.
                                  eapply Exec.elem_of_bind_intro
                                    with
                                      (st' := PPState.Make
                                        (TState.promise pnew
                                          (TState.update TState.vcap (IIS.strict iis)
                                            (TState.update TState.vacq
                                              (view_if (is_rel_acq macc) vpost)
                                              (TState.update TState.vrd vpost
                                                (TState.update_cohs
                                                  (zip (addr_range addr size)
                                                    fwd_bytes.*2) ts)))))
	                                          (msg :: mem) iis_rmw)
                                      (a := ()).
		                                  { rewrite <- TState_promise_update_vcap.
		                                    change (S (length mem)) with pnew.
		                                    apply elem_of_unfolded_ppstate_mset_state. }
                                  cbn.
                                  destruct (is_exclusive macc) eqn:Hexcl.
                                  { cbn in Hrun.
	                                    apply Exec.elem_of_bind_elim in Hrun as
	                                      [pp_xcl [[] [Hxcl Hrun]]].
	                                    apply Exec.elem_of_mset_inv in Hxcl as ->.
	                                    apply Exec.elem_of_bind_elim in Hrun as
	                                      [pp_iis [[] [Hiis Hrun]]].
	                                    apply Exec.elem_of_mset_inv in Hiis as ->.
	                                    apply Exec.elem_of_mret_inv in Hrun as [-> ->].
	                                    eapply Exec.elem_of_bind_intro
                                      with
                                        (st' := PPState.Make
                                          (TState.promise pnew
                                            (TState.set_xclb tread addr size vpost
                                              (TState.update TState.vcap
                                                (IIS.strict iis)
                                                (TState.update TState.vacq
                                                  (view_if (is_rel_acq macc) vpost)
                                                  (TState.update TState.vrd vpost
                                                    (TState.update_cohs
                                                      (zip (addr_range addr size)
                                                        fwd_bytes.*2) ts))))))
	                                          (msg :: mem) iis_rmw)
                                        (a := ()).
		                                    - rewrite <- TState_promise_set_xclb.
		                                      change (S (length mem)) with pnew.
		                                      apply elem_of_unfolded_ppstate_mset_state.
                                    - cbn.
                                      eapply Exec.elem_of_bind_intro with
                                        (st' := PPState.Make
                                          (TState.promise pnew
                                            (TState.set_xclb tread addr size vpost
                                              (TState.update TState.vcap
                                                (IIS.strict iis)
                                                (TState.update TState.vacq
                                                  (view_if (is_rel_acq macc) vpost)
                                                  (TState.update TState.vrd vpost
                                                    (TState.update_cohs
                                                      (zip (addr_range addr size)
                                                        fwd_bytes.*2) ts))))))
	                                          (msg :: mem) (IIS.add vpost iis_rmw))
                                        (a := ()).
		                                      + change (S (length mem)) with pnew.
		                                        apply elem_of_unfolded_ppstate_mset_iis.
                                      + cbn.
                                        apply Exec.elem_of_mret. }
	                                  { cbn in Hrun.
	                                    apply Exec.elem_of_bind_elim in Hrun as
	                                      [pp_skip [[] [Hskip Hrun]]].
	                                    apply Exec.elem_of_mret_inv in Hskip as [-> _].
	                                    apply Exec.elem_of_bind_elim in Hrun as
	                                      [pp_iis [[] [Hiis Hrun]]].
	                                    apply Exec.elem_of_mset_inv in Hiis as ->.
	                                    apply Exec.elem_of_mret_inv in Hrun as [-> ->].
	                                    eapply Exec.elem_of_bind_intro with
	                                      (st' := PPState.Make
	                                        (TState.promise pnew
	                                          (TState.update TState.vcap (IIS.strict iis)
	                                            (TState.update TState.vacq
	                                              (view_if (is_rel_acq macc) vpost)
	                                              (TState.update TState.vrd vpost
	                                                (TState.update_cohs
	                                                  (zip (addr_range addr size)
	                                                    fwd_bytes.*2) ts)))))
	                                        (msg :: mem) iis_rmw)
	                                      (a := ()).
		                                    - apply Exec.elem_of_mret.
	                                    - cbn.
	                                      eapply Exec.elem_of_bind_intro with
	                                        (st' := PPState.Make
	                                          (TState.promise pnew
	                                            (TState.update TState.vcap (IIS.strict iis)
	                                              (TState.update TState.vacq
	                                                (view_if (is_rel_acq macc) vpost)
	                                                (TState.update TState.vrd vpost
	                                                  (TState.update_cohs
	                                                    (zip (addr_range addr size)
	                                                      fwd_bytes.*2) ts)))))
	                                          (msg :: mem) (IIS.add vpost iis_rmw))
	                                        (a := ()).
			                                      + change (S (length mem)) with pnew.
			                                        apply elem_of_unfolded_ppstate_mset_iis.
	                                      + cbn.
	                                        apply Exec.elem_of_mret. }
Qed.

Lemma read_mem_cons_event_old addr size macc init msg ppst ppst' res :
  ppstate_read_times_le macc ppst →
  Exec.elem_of_results (ppst', res) (read_mem addr size macc init ppst) →
  Exec.elem_of_results
    (CPStateProof.cons_event_ppstate UMPromising msg ppst', res)
    (read_mem addr size macc init
       (CPStateProof.cons_event_ppstate UMPromising msg ppst)).
Proof.
  destruct ppst as [ts mem iis].
  intros [Hvpre Hfwdb] Hrun.
  cbn in *.
  unfold read_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts0 [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_iis [vaddr [Hget_iis Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_iis as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_np [p_np [Hnp_guard Hrun]]].
  pose proof p_np as Hnp.
  apply Exec.elem_of_guard_discard_inv in Hnp_guard as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_mem [mem0 [Hget_mem Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_mem as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_choose [tread [Hchoose Hrun]]].
  apply Exec.elem_of_fmap_inv in Hchoose as [idx [Htread_eq Hchoose]].
  assert (pp_choose = PPState.Make ts mem iis) as ->.
  { unfold elem_of, Exec.elem_of_results in Hchoose.
    cbn in Hchoose.
    apply elem_of_cons in Hchoose as [Heq|Hchoose].
    - inversion Heq.
      reflexivity.
    - rewrite elem_of_list_fmap in Hchoose.
      destruct Hchoose as [idx' [Heq _]].
      inversion Heq.
      reflexivity. }
  assert
    (Htread :
       (list_to_vec
          (read_candidates addr size (read_mem_vpre (IIS.strict iis) macc ts)
             mem) !!! idx) ∈
       read_candidates addr size (read_mem_vpre (IIS.strict iis) macc ts) mem).
  { apply elem_of_list_lookup.
    exists (idx : nat).
    pose proof
      (proj1
         (vlookup_lookup
            (list_to_vec
               (read_candidates addr size
                  (read_mem_vpre (IIS.strict iis) macc ts) mem))
            idx
            (list_to_vec
               (read_candidates addr size
                  (read_mem_vpre (IIS.strict iis) macc ts) mem) !!! idx))
         eq_refl) as Hlookup.
    rewrite vec_to_list_to_vec in Hlookup.
    exact Hlookup. }
  rewrite <- Htread_eq in Htread.
  pose proof (read_candidates_time_le addr size
    (read_mem_vpre (IIS.strict iis) macc ts) mem tread Hvpre Htread)
    as Htread_le.
  pose proof (read_candidates_cons_old addr size
    (read_mem_vpre (IIS.strict iis) macc ts) mem msg tread Hvpre Htread)
    as Htread_new.
  set (iis_rmw :=
    if is_atomic_rmw macc then
      set IIS.rmw_read (λ _ : option (nat * bool),
        Some (tread, is_rel_acq macc)) iis
    else iis).
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_rmw [u [Hrmw Hrun]]].
  destruct u.
  assert (Hpp_rmw : pp_rmw = PPState.Make ts mem iis_rmw).
  {
    subst iis_rmw.
    destruct (is_atomic_rmw macc) eqn:Hatomic_macc.
    - unfold msetv in Hrmw.
      apply Exec.elem_of_mset_inv in Hrmw as ->.
      reflexivity.
    - apply Exec.elem_of_mret_inv in Hrmw as [-> _].
      reflexivity.
  }
  subst pp_rmw.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_raw [raw_bytes [Hraw Hrun]]].
  unfold othrow in Hraw.
  destruct (Memory.read_from addr size tread init mem) as [raw_bytes0|]
    eqn:Hread_old.
  2: {
    rewrite Hread_old in Hraw.
    unfold mthrow, Exec.throw_inst, elem_of, Exec.elem_of_results in Hraw.
    cbn in Hraw.
    exfalso.
    exact (not_elem_of_nil _ Hraw).
  }
  rewrite Hread_old in Hraw.
  apply Exec.elem_of_mret_inv in Hraw as [-> Hraw_eq].
  inversion Hraw_eq; subst raw_bytes0.
  pose proof (memory_read_from_cons_old addr size tread init mem msg Htread_le)
    as Hread_from.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_bytes [fwd_bytes [Hbytes Hrun]]].
  apply Exec.elem_of_lift_res_inv in Hbytes as [-> Hbytes].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_coh [pcoh [Hcoh Hrun]]].
  pose proof pcoh as Hcoh_prop.
  apply Exec.elem_of_guard_discard_inv in Hcoh as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_cohs [[] [Hcohs Hrun]]].
  apply Exec.elem_of_mset_inv in Hcohs as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vrd [[] [Hvrd Hrun]]].
  apply Exec.elem_of_mset_inv in Hvrd as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vacq [[] [Hvacq Hrun]]].
  apply Exec.elem_of_mset_inv in Hvacq as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vcap [[] [Hvcap Hrun]]].
  apply Exec.elem_of_mset_inv in Hvcap as ->.

  eapply Exec.elem_of_bind_intro with
      (e := (mget PPState.state :
               Exec.t (PPState.t TState.t Msg.t IIS.t) string TState.t))
      (st' := PPState.Make ts (msg :: mem) iis)
      (a := ts).
  - apply (Exec.elem_of_mget (E:=string)
      (PPState.Make ts (msg :: mem) iis)
      PPState.state).
  - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := (mget (IIS.strict ∘ PPState.iis) :
                 Exec.t (PPState.t TState.t Msg.t IIS.t) string view))
	        (st' := PPState.Make ts (msg :: mem) iis)
        (a := IIS.strict iis).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make ts (msg :: mem) iis)
          (IIS.strict ∘ PPState.iis)).
      * cbn.
        destruct (Exec.elem_of_guard_discard
          (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
          (P:=TState.no_promises_until (IIS.strict iis) ts)
          (PPState.Make ts (msg :: mem) iis)
          Hnp) as [p_np' Hnp'].
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard (TState.no_promises_until (IIS.strict iis) ts))
          (st' := PPState.Make ts (msg :: mem) iis)
          (a := p_np').
        -- exact Hnp'.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (e := (mget PPState.mem :
                      Exec.t (PPState.t TState.t Msg.t IIS.t) string Memory.t))
             (st' := PPState.Make ts (msg :: mem) iis)
             (a := msg :: mem).
           ++ apply (Exec.elem_of_mget (E:=string)
                (PPState.Make ts (msg :: mem) iis)
                PPState.mem).
           ++ cbn.
              eapply Exec.elem_of_bind_intro with
                (st' := PPState.Make ts (msg :: mem) iis)
                (a := tread).
              ** change (Exec.elem_of_results
                   (PPState.Make ts (msg :: mem) iis, tread)
                   ((mchoosel
                       (read_candidates addr size
                          (read_mem_vpre (IIS.strict iis) macc ts)
                          (msg :: mem)) :
                      Exec.t (PPState.t TState.t Msg.t IIS.t) string nat)
                     (PPState.Make ts (msg :: mem) iis))).
                 apply Exec.elem_of_mchoosel.
                 exact Htread_new.
	              ** cbn.
	                 unfold msetv, mset, mSet.
	                 eapply Exec.elem_of_bind_intro with
	                   (st' := PPState.Make ts (msg :: mem) iis_rmw)
	                   (a := ()).
	                 --- unfold iis_rmw.
	                     destruct (is_atomic_rmw macc) eqn:Hatomic_macc.
	                     { change (PPState.Make ts (msg :: mem)
	                         (set IIS.rmw_read
	                            (λ _ : option (nat * bool),
	                              Some (tread, is_rel_acq macc)) iis))
	                         with
	                         (set (IIS.rmw_read ∘ PPState.iis)
	                            (λ _ : option (nat * bool),
	                              Some (tread, is_rel_acq macc))
	                            (PPState.Make ts (msg :: mem) iis)).
	                       apply (Exec.elem_of_unfolded_mset
	                         (E:=string)
	                         (PPState.Make ts (msg :: mem) iis)
	                         (IIS.rmw_read ∘ PPState.iis)
	                         (λ _ : option (nat * bool),
	                            Some (tread, is_rel_acq macc))). }
	                     { apply Exec.elem_of_mret. }
	                 --- cbn.
	                 eapply Exec.elem_of_bind_intro with
	                   (e := othrow "Memory read of unmapped bytes"
	                           (Memory.read_from addr size tread init (msg :: mem)))
	                   (st' := PPState.Make ts (msg :: mem) iis_rmw)
	                   (a := raw_bytes).
	                 +++ unfold othrow.
                     rewrite Hread_from.
                     rewrite Hread_old.
                     apply Exec.elem_of_mret.
	                 +++ cbn.
                     eapply Exec.elem_of_bind_intro with
	                       (e := mlift
	                         (for (addr0, (byte, twrite)) in
	                            zip (addr_range addr size) raw_bytes do
	                            read_fwd (TState.fwdb ts)
	                              macc (msg :: mem) tread addr0
	                              |$> default (byte, tread, twrite)
	                          end))
	                       (st' := PPState.Make ts (msg :: mem) iis_rmw)
	                       (a := fwd_bytes).
	                     *** apply Exec.elem_of_lift_res.
                         rewrite (read_fwd_list_cons_old_nested
                           (TState.fwdb ts) macc mem tread
                           (addr_range addr size) raw_bytes msg).
                         { exact Hbytes. }
                         intros a fwd _ Hfwd.
                         exact (Hfwdb a fwd Hfwd).
	                     *** cbn.
	                         destruct (Exec.elem_of_guard_discard
	                           (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
	                           (P:=∀ '(a, t) ∈ zip (addr_range addr size) fwd_bytes.*2,
	                                (TState.coh ts !!! a ≤ t)%nat)
	                           (PPState.Make ts (msg :: mem) iis_rmw)
	                           Hcoh_prop) as [pcoh' Hcoh'].
                         eapply Exec.elem_of_bind_intro with
                           (e := guard_discard
                             (∀ '(a, t) ∈ zip (addr_range addr size) fwd_bytes.*2,
                                (TState.coh ts !!! a ≤ t)%nat))
	                           (st' := PPState.Make ts (msg :: mem) iis_rmw)
                           (a := pcoh').
	                         ---- exact Hcoh'.
	                         ---- cbn.
                             set (vpost :=
                               read_mem_vpre (IIS.strict iis) macc ts ⊔
                               foldr max 0%nat fwd_bytes.*1.*2).
                             eapply Exec.elem_of_bind_intro
                               with
                                 (st' := PPState.Make
                                   (TState.update_cohs
                                      (zip (addr_range addr size) fwd_bytes.*2)
                                      ts)
	                                        (msg :: mem) iis_rmw)
	                                      (a := ()).
	                             ++++ apply elem_of_unfolded_ppstate_mset_state.
	                             ++++ cbn.
                                  eapply Exec.elem_of_bind_intro
                                    with
                                      (st' := PPState.Make
                                        (TState.update TState.vrd vpost
                                          (TState.update_cohs
                                            (zip (addr_range addr size)
                                              fwd_bytes.*2) ts))
	                                        (msg :: mem) iis_rmw)
	                                      (a := ()).
                                  { apply elem_of_unfolded_ppstate_mset_state. }
                                  cbn.
                                  eapply Exec.elem_of_bind_intro
                                    with
                                      (st' := PPState.Make
                                        (TState.update TState.vacq
                                          (view_if (is_rel_acq macc) vpost)
                                          (TState.update TState.vrd vpost
                                            (TState.update_cohs
                                              (zip (addr_range addr size)
                                                fwd_bytes.*2) ts)))
	                                          (msg :: mem) iis_rmw)
	                                        (a := ()).
                                  { apply elem_of_unfolded_ppstate_mset_state. }
                                  cbn.
                                  eapply Exec.elem_of_bind_intro
                                    with
                                      (st' := PPState.Make
                                        (TState.update TState.vcap (IIS.strict iis)
                                          (TState.update TState.vacq
                                            (view_if (is_rel_acq macc) vpost)
                                            (TState.update TState.vrd vpost
                                              (TState.update_cohs
                                                (zip (addr_range addr size)
                                                  fwd_bytes.*2) ts))))
	                                        (msg :: mem) iis_rmw)
                                      (a := ()).
                                  { apply elem_of_unfolded_ppstate_mset_state. }
                                  cbn.
                                  destruct (is_exclusive macc) eqn:Hexcl.
                                  { cbn in Hrun.
                                    apply Exec.elem_of_bind_elim in Hrun as
                                      [pp_xcl [[] [Hxcl Hrun]]].
                                    apply Exec.elem_of_mset_inv in Hxcl as ->.
                                    apply Exec.elem_of_bind_elim in Hrun as
                                      [pp_iis [[] [Hiis Hrun]]].
                                    apply Exec.elem_of_mset_inv in Hiis as ->.
                                    apply Exec.elem_of_mret_inv in Hrun as [-> ->].
                                    eapply Exec.elem_of_bind_intro
                                      with
                                        (st' := PPState.Make
                                          (TState.set_xclb tread addr size vpost
                                            (TState.update TState.vcap
                                              (IIS.strict iis)
                                              (TState.update TState.vacq
                                                (view_if (is_rel_acq macc) vpost)
                                                (TState.update TState.vrd vpost
                                                  (TState.update_cohs
                                                    (zip (addr_range addr size)
                                                      fwd_bytes.*2) ts)))))
	                                          (msg :: mem) iis_rmw)
                                        (a := ()).
                                    - apply elem_of_unfolded_ppstate_mset_state.
                                    - cbn.
                                      eapply Exec.elem_of_bind_intro with
                                        (st' := PPState.Make
                                          (TState.set_xclb tread addr size vpost
                                            (TState.update TState.vcap
                                              (IIS.strict iis)
                                              (TState.update TState.vacq
                                                (view_if (is_rel_acq macc) vpost)
                                                (TState.update TState.vrd vpost
                                                  (TState.update_cohs
                                                    (zip (addr_range addr size)
                                                      fwd_bytes.*2) ts)))))
	                                          (msg :: mem) (IIS.add vpost iis_rmw))
	                                        (a := ()).
                                      + apply elem_of_unfolded_ppstate_mset_iis.
                                      + cbn.
                                        apply Exec.elem_of_mret. }
                                  { cbn in Hrun.
                                    apply Exec.elem_of_bind_elim in Hrun as
                                      [pp_skip [[] [Hskip Hrun]]].
                                    apply Exec.elem_of_mret_inv in Hskip as [-> _].
                                    apply Exec.elem_of_bind_elim in Hrun as
                                      [pp_iis [[] [Hiis Hrun]]].
                                    apply Exec.elem_of_mset_inv in Hiis as ->.
                                    apply Exec.elem_of_mret_inv in Hrun as [-> ->].
                                    eapply Exec.elem_of_bind_intro with
                                      (st' := PPState.Make
                                        (TState.update TState.vcap (IIS.strict iis)
                                          (TState.update TState.vacq
                                            (view_if (is_rel_acq macc) vpost)
                                            (TState.update TState.vrd vpost
                                              (TState.update_cohs
                                                (zip (addr_range addr size)
                                                  fwd_bytes.*2) ts))))
		                                        (msg :: mem) iis_rmw)
		                                      (a := ()).
	                                    - apply Exec.elem_of_mret.
                                    - cbn.
                                      eapply Exec.elem_of_bind_intro with
                                        (st' := PPState.Make
                                          (TState.update TState.vcap (IIS.strict iis)
                                            (TState.update TState.vacq
                                              (view_if (is_rel_acq macc) vpost)
                                              (TState.update TState.vrd vpost
                                                (TState.update_cohs
                                                  (zip (addr_range addr size)
                                                    fwd_bytes.*2) ts))))
		                                          (msg :: mem) (IIS.add vpost iis_rmw))
		                                        (a := ()).
                                      + apply elem_of_unfolded_ppstate_mset_iis.
                                      + cbn.
                                        apply Exec.elem_of_mret. }
Qed.

Lemma TState_reg_map_promise v ts :
  TState.reg_map (TState.promise v ts) = TState.reg_map ts.
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma UMPromising_promise_tid_reg_map {n} (tid_p tid : fin n)
    (msg : Msg.t) (st : CPState.t TState.t Msg.t n) :
  TState.reg_map
    (CPState.tstate tid
       (CPState.promise_tid UMPromising tid_p msg st)) =
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

Lemma UMPromising_terminated_tid_promise {n}
    (term : terminationCondition n) (tid_p tid : fin n)
    (msg : Msg.t) (st : CPState.t TState.t Msg.t n) :
  CPState.terminated_tid UMPromising term
    (CPState.promise_tid UMPromising tid_p msg st) tid =
  CPState.terminated_tid UMPromising term st tid.
Proof.
  unfold CPState.terminated_tid.
  cbn.
  rewrite UMPromising_promise_tid_reg_map.
  reflexivity.
Qed.

Definition outcome_future_promise_stable_promised tid initmem
    (msg : Msg.t) (out : outcome) : Prop :=
  ∀ ppst ppst' (eret : eff_ret out),
    Exec.elem_of_results (ppst', eret)
      ((run_outcome tid initmem out |$> fst) ppst) →
    Exec.elem_of_results
      (UMPromising_promise_ppstate tid initmem msg ppst', eret)
      ((run_outcome tid initmem out |$> fst)
         (UMPromising_promise_ppstate tid initmem msg ppst)).

Fixpoint imon_future_promise_stable_promised tid initmem
    (msg : Msg.t) A (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next call k =>
      match call with
      | inl out =>
          outcome_future_promise_stable_promised tid initmem msg out ∧
          ∀ eret,
            imon_future_promise_stable_promised tid initmem msg A (k eret)
      | inr _ =>
          ∀ ret,
            imon_future_promise_stable_promised tid initmem msg A (k ret)
      end
  end.

Definition outcome_future_promise_stable_fmap tid initmem
    (code : code_region) msg
    (out : outcome) : Prop :=
  ∀ ppst ppst' (eret : eff_ret out),
    Exec.elem_of_results (ppst', eret)
      ((run_outcome tid initmem out |$> fst) ppst) →
    Exec.elem_of_results
      (CPStateProof.cons_event_ppstate UMPromising msg ppst', eret)
      ((run_outcome tid initmem out |$> fst)
         (CPStateProof.cons_event_ppstate UMPromising msg ppst)).

Fixpoint imon_future_promise_stable_fmap tid initmem
    (code : code_region) msg
    A (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next call k =>
      match call with
      | inl out =>
          outcome_future_promise_stable_fmap tid initmem code msg out ∧
          ∀ eret,
            imon_future_promise_stable_fmap tid initmem code msg A (k eret)
      | inr _ =>
          ∀ ret,
            imon_future_promise_stable_fmap tid initmem code msg A (k ret)
      end
  end.

Lemma run_outcome_mem_read_promise_cons_old_fmap tid initmem code msg
    addr size macc addr_space ppst ppst' eret :
  (is_ifetch macc = true →
    event_misses_code code msg ∧ ifetch_in_code code addr size) →
  (is_ifetch macc = false →
    is_explicit macc = true →
    ppstate_read_times_le macc ppst) →
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem
        (MemRead (MemReq.make macc addr addr_space size 0)) |$> fst) ppst) →
  Exec.elem_of_results
    (UMPromising_promise_ppstate tid initmem msg ppst', eret)
    ((run_outcome tid initmem
        (MemRead (MemReq.make macc addr addr_space size 0)) |$> fst)
       (UMPromising_promise_ppstate tid initmem msg ppst)).
Proof.
  intros Hifetch_assume Hread_bound Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  destruct ppst as [ts mem iis].
  unfold UMPromising_promise_ppstate in *.
  cbn in *.
  set (pnew := length (msg :: mem)).
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [p_addr_space [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard)
    as Haddr_space.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  subst addr_space.
  cbn in Hrun.
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
    (P:=@eq Arch.addr_space PAS_NonSecure PAS_NonSecure)
    (PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
    "Access outside Non-Secure" eq_refl) as
    [p_addr_space' Hguard'].
  destruct (is_ifetch macc) eqn:Hifetch.
  - apply Exec.elem_of_bind_elim in Hrun as
      [pp_size [p_size [Hsize Hrun]]].
    pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hsize) as Hsize_eq.
    apply Exec.elem_of_guard_or_inv in Hsize as ->.
    subst size.
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_mem [mem0 [Hmem Hrun]]].
    apply Exec.elem_of_mget_inv in Hmem as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_opcode [opcode [Hopcode Hrun]]].
    apply Exec.elem_of_lift_res_inv in Hopcode as [-> Hopcode].
    apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
    inversion Heq; subst ppst'.
    destruct (Hifetch_assume eq_refl) as [Hmisses Hcode].
    assert
      (Hfull :
        Exec.elem_of_results
          (PPState.Make (TState.promise pnew ts) (msg :: mem) iis,
           (eret0, vpre_opt))
          (run_outcome tid initmem
             (MemRead (MemReq.make macc addr PAS_NonSecure 4 0))
             (PPState.Make (TState.promise pnew ts) (msg :: mem) iis))).
    {
      simp run_outcome.
      rewrite Hifetch.
      eapply Exec.elem_of_bind_intro with
        (e := guard_or "Access outside Non-Secure"
                (PAS_NonSecure = PAS_NonSecure))
        (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
        (a := p_addr_space').
      - exact Hguard'.
      - cbn.
        destruct (Exec.elem_of_guard_or
          (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
          (P:=(4 = 4)%N)
          (PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
          "Ifetch read of size other than 4" eq_refl) as
          [p_size' Hsize'].
        eapply Exec.elem_of_bind_intro with
          (e := guard_or "Ifetch read of size other than 4" (4 = 4)%N)
          (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
          (a := p_size').
        + exact Hsize'.
        + cbn.
          eapply Exec.elem_of_bind_intro with
            (e := (mget PPState.mem :
                     Exec.t (PPState.t TState.t Msg.t IIS.t) string Memory.t))
            (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
            (a := msg :: mem).
          * apply (Exec.elem_of_mget (E:=string)
              (PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
              PPState.mem).
          * cbn.
            eapply Exec.elem_of_bind_intro with
              (e := mlift (read_imem addr initmem (msg :: mem)))
              (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
              (a := opcode).
            -- apply Exec.elem_of_lift_res.
               rewrite (read_imem_cons_misses_code code addr initmem mem msg
                 Hmisses Hcode).
               exact Hopcode.
            -- cbn.
               rewrite (proof_irrelevance _ p_size' eq_refl).
               rewrite Hret.
               apply Exec.elem_of_mret.
    }
    simp run_outcome in Hfull.
    rewrite Hifetch in Hfull.
    cbn in Hfull.
    unfold elem_of, Exec.elem_of_results.
    unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
    cbn in Hfull |- *.
    set_unfold.
    eapply elem_of_list_fmap_1_alt.
    + exact Hfull.
    + reflexivity.
  - destruct (is_explicit macc) eqn:Hexplicit.
    + apply Exec.elem_of_bind_elim in Hrun as
        [pp_val [val [Hread Hrun]]].
      apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
      inversion Heq; subst ppst'.
      inversion Hret; subst eret0 vpre_opt.
      pose proof
        (read_mem_promise_cons_old addr size macc initmem msg
           (PPState.Make ts mem iis) pp_val val
           (Hread_bound eq_refl eq_refl) Hread) as Hread_promise.
      cbn in Hread_promise.
      assert
        (Hfull :
          Exec.elem_of_results
            (UMPromising_promise_ppstate tid initmem msg pp_val,
             (Ok (val, 0%bv), None))
	            (run_outcome tid initmem
	               (MemRead (MemReq.make macc addr PAS_NonSecure size 0))
	               (PPState.Make (TState.promise pnew ts) (msg :: mem) iis))).
      {
        simp run_outcome.
        rewrite Hifetch.
        rewrite Hexplicit.
	        eapply Exec.elem_of_bind_intro with
	          (e := guard_or "Access outside Non-Secure"
	                  (PAS_NonSecure = PAS_NonSecure))
          (st' := PPState.Make (TState.promise pnew ts) (msg :: mem) iis)
          (a := p_addr_space').
        - exact Hguard'.
        - cbn.
          eapply Exec.elem_of_bind_intro with
            (e := read_mem addr size macc initmem)
            (st' := UMPromising_promise_ppstate tid initmem msg pp_val)
            (a := val).
          + exact Hread_promise.
          + cbn.
            apply Exec.elem_of_mret.
      }
      simp run_outcome in Hfull.
      rewrite Hifetch in Hfull.
      rewrite Hexplicit in Hfull.
      cbn in Hfull.
      unfold elem_of, Exec.elem_of_results.
      unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
      cbn in Hfull |- *.
      set_unfold.
      eapply elem_of_list_fmap_1_alt.
      * exact Hfull.
      * reflexivity.
    + exfalso.
      unfold mthrow, Exec.throw_inst, elem_of, Exec.elem_of_results in Hrun.
      cbn in Hrun.
      exact (not_elem_of_nil _ Hrun).
Qed.

Lemma mem_read_outcome_future_promise_stable_promised tid initmem code msg
    addr size macc addr_space :
  (is_ifetch macc = true →
    event_misses_code code msg ∧ ifetch_in_code code addr size) →
  (∀ ppst,
    is_ifetch macc = false →
    is_explicit macc = true →
    ppstate_read_times_le macc ppst) →
  outcome_future_promise_stable_promised tid initmem msg
    (MemRead (MemReq.make macc addr addr_space size 0)).
Proof.
  intros Hifetch_assume Hread_bound ppst ppst' eret Hrun.
  eapply run_outcome_mem_read_promise_cons_old_fmap.
  - exact Hifetch_assume.
  - intros Hifetch Hexplicit.
    apply Hread_bound; assumption.
  - exact Hrun.
Qed.

Lemma run_outcome_mem_read_cons_event_fmap tid initmem code msg
    addr size macc addr_space ppst ppst' eret :
  (is_ifetch macc = true →
    event_misses_code code msg ∧ ifetch_in_code code addr size) →
  (is_ifetch macc = false →
    is_explicit macc = true →
    ppstate_read_times_le macc ppst) →
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem
        (MemRead (MemReq.make macc addr addr_space size 0)) |$> fst) ppst) →
  Exec.elem_of_results
    (CPStateProof.cons_event_ppstate UMPromising msg ppst', eret)
    ((run_outcome tid initmem
        (MemRead (MemReq.make macc addr addr_space size 0)) |$> fst)
       (CPStateProof.cons_event_ppstate UMPromising msg ppst)).
Proof.
  intros Hifetch_assume Hread_bound Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  destruct ppst as [ts mem iis].
  cbn in *.
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [p_addr_space [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard)
    as Haddr_space.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  subst addr_space.
  cbn in Hrun.
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
    (P:=@eq Arch.addr_space PAS_NonSecure PAS_NonSecure)
    (PPState.Make ts (msg :: mem) iis)
    "Access outside Non-Secure" eq_refl) as
    [p_addr_space' Hguard'].
  destruct (is_ifetch macc) eqn:Hifetch.
  - apply Exec.elem_of_bind_elim in Hrun as
      [pp_size [p_size [Hsize Hrun]]].
    pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hsize) as Hsize_eq.
    apply Exec.elem_of_guard_or_inv in Hsize as ->.
    subst size.
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_mem [mem0 [Hmem Hrun]]].
    apply Exec.elem_of_mget_inv in Hmem as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_opcode [opcode [Hopcode Hrun]]].
    apply Exec.elem_of_lift_res_inv in Hopcode as [-> Hopcode].
    apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
    inversion Heq; subst ppst'.
    destruct (Hifetch_assume eq_refl) as [Hmisses Hcode].
    assert
      (Hfull :
        Exec.elem_of_results
          (PPState.Make ts (msg :: mem) iis, (eret0, vpre_opt))
          (run_outcome tid initmem
             (MemRead (MemReq.make macc addr PAS_NonSecure 4 0))
             (PPState.Make ts (msg :: mem) iis))).
    {
      simp run_outcome.
      rewrite Hifetch.
      eapply Exec.elem_of_bind_intro with
        (e := guard_or "Access outside Non-Secure"
                (PAS_NonSecure = PAS_NonSecure))
        (st' := PPState.Make ts (msg :: mem) iis)
        (a := p_addr_space').
      - exact Hguard'.
      - cbn.
        destruct (Exec.elem_of_guard_or
          (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
          (P:=(4 = 4)%N)
          (PPState.Make ts (msg :: mem) iis)
          "Ifetch read of size other than 4" eq_refl) as
          [p_size' Hsize'].
        eapply Exec.elem_of_bind_intro with
          (e := guard_or "Ifetch read of size other than 4" (4 = 4)%N)
          (st' := PPState.Make ts (msg :: mem) iis)
          (a := p_size').
        + exact Hsize'.
        + cbn.
          eapply Exec.elem_of_bind_intro with
            (e := (mget PPState.mem :
                     Exec.t (PPState.t TState.t Msg.t IIS.t) string Memory.t))
            (st' := PPState.Make ts (msg :: mem) iis)
            (a := msg :: mem).
          * apply (Exec.elem_of_mget (E:=string)
              (PPState.Make ts (msg :: mem) iis)
              PPState.mem).
          * cbn.
            eapply Exec.elem_of_bind_intro with
              (e := mlift (read_imem addr initmem (msg :: mem)))
              (st' := PPState.Make ts (msg :: mem) iis)
              (a := opcode).
            -- apply Exec.elem_of_lift_res.
               rewrite (read_imem_cons_misses_code code addr initmem mem msg
                 Hmisses Hcode).
               exact Hopcode.
            -- cbn.
               rewrite (proof_irrelevance _ p_size' eq_refl).
               rewrite Hret.
               apply Exec.elem_of_mret.
    }
    simp run_outcome in Hfull.
    rewrite Hifetch in Hfull.
    cbn in Hfull.
    unfold elem_of, Exec.elem_of_results.
    unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
    cbn in Hfull |- *.
    set_unfold.
    eapply elem_of_list_fmap_1_alt.
    + exact Hfull.
    + reflexivity.
  - destruct (is_explicit macc) eqn:Hexplicit.
    + apply Exec.elem_of_bind_elim in Hrun as
        [pp_val [val [Hread Hrun]]].
      apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
      inversion Heq; subst ppst'.
      inversion Hret; subst eret0 vpre_opt.
      pose proof
        (read_mem_cons_event_old addr size macc initmem msg
           (PPState.Make ts mem iis) pp_val val
           (Hread_bound eq_refl eq_refl) Hread) as Hread_cons.
      cbn in Hread_cons.
      assert
        (Hfull :
          Exec.elem_of_results
            (CPStateProof.cons_event_ppstate UMPromising msg pp_val,
             (Ok (val, 0%bv), None))
            (run_outcome tid initmem
               (MemRead (MemReq.make macc addr PAS_NonSecure size 0))
               (PPState.Make ts (msg :: mem) iis))).
      {
        simp run_outcome.
        rewrite Hifetch.
        rewrite Hexplicit.
        eapply Exec.elem_of_bind_intro with
          (e := guard_or "Access outside Non-Secure"
                  (PAS_NonSecure = PAS_NonSecure))
          (st' := PPState.Make ts (msg :: mem) iis)
          (a := p_addr_space').
        - exact Hguard'.
        - cbn.
          eapply Exec.elem_of_bind_intro with
            (e := read_mem addr size macc initmem)
            (st' := CPStateProof.cons_event_ppstate UMPromising msg pp_val)
            (a := val).
          + exact Hread_cons.
          + cbn.
            apply Exec.elem_of_mret.
      }
      simp run_outcome in Hfull.
      rewrite Hifetch in Hfull.
      rewrite Hexplicit in Hfull.
      cbn in Hfull.
      unfold elem_of, Exec.elem_of_results.
      unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
      cbn in Hfull |- *.
      set_unfold.
      eapply elem_of_list_fmap_1_alt.
      * exact Hfull.
      * reflexivity.
    + exfalso.
      unfold mthrow, Exec.throw_inst, elem_of, Exec.elem_of_results in Hrun.
      cbn in Hrun.
      exact (not_elem_of_nil _ Hrun).
Qed.

Lemma mem_read_outcome_future_promise_stable_fmap tid initmem code msg
    addr size macc addr_space :
  (is_ifetch macc = true →
    event_misses_code code msg ∧ ifetch_in_code code addr size) →
  (∀ ppst,
    is_ifetch macc = false →
    is_explicit macc = true →
    ppstate_read_times_le macc ppst) →
  outcome_future_promise_stable_fmap tid initmem code msg
    (MemRead (MemReq.make macc addr addr_space size 0)).
Proof.
  intros Hifetch_assume Hread_bound ppst ppst' eret Hrun.
  eapply run_outcome_mem_read_cons_event_fmap.
  - exact Hifetch_assume.
  - intros Hifetch Hexplicit.
    apply Hread_bound; assumption.
  - exact Hrun.
Qed.

Lemma reg_read_outcome_promise_state_fmap tid initmem reg racc
    ppst ppst' p mem_new eret :
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (RegRead reg racc) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState.promise p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (RegRead reg racc) |$> fst)
       (PPState.Make (TState.promise p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intro Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [p_racc [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hracc.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_reg [[val view] [Hreg Hrun]]].
  unfold othrow in Hreg.
  destruct (dmap_lookup reg (TState.regs (PPState.state ppst)))
    as [[val0 view0]|] eqn:Hlookup.
  2: {
    unfold elem_of, Exec.elem_of_results in Hreg.
    cbn in Hreg.
    inversion Hreg.
  }
  apply Exec.elem_of_mret_inv in Hreg as [-> Hreg].
  inversion Hreg; subst val0 view0.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_iis [[] [Hiis Hrun]]].
  apply Exec.elem_of_mset_inv in Hiis as ->.
  apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
    (P:=racc = None)
    (PPState.Make (TState.promise p (PPState.state ppst))
       mem_new (PPState.iis ppst))
    "Non trivial reg access types unsupported" Hracc) as
    [p_racc' Hguard'].
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make
            (TState.promise p (PPState.state ppst))
            mem_new (IIS.add view (PPState.iis ppst)),
          (val, None))
         (run_outcome tid initmem (RegRead reg racc)
            (PPState.Make (TState.promise p (PPState.state ppst))
               mem_new (PPState.iis ppst)))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := guard_or "Non trivial reg access types unsupported"
              (racc = None))
      (st' := PPState.Make (TState.promise p (PPState.state ppst))
                mem_new (PPState.iis ppst))
      (a := p_racc').
    - exact Hguard'.
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := (mget PPState.state :
                 Exec.t (PPState.t TState.t Msg.t IIS.t) string TState.t))
        (st' := PPState.Make (TState.promise p (PPState.state ppst))
                  mem_new (PPState.iis ppst))
        (a := TState.promise p (PPState.state ppst)).
      + apply (Exec.elem_of_mget (E:=string)
          (PPState.Make (TState.promise p (PPState.state ppst))
             mem_new (PPState.iis ppst)) PPState.state).
      + cbn.
        rewrite Hlookup.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make (TState.promise p (PPState.state ppst))
                    mem_new (PPState.iis ppst))
          (a := (val, view)).
        * apply Exec.elem_of_mret.
        * cbn.
          eapply Exec.elem_of_bind_intro with
            (st' := PPState.Make (TState.promise p (PPState.state ppst))
                      mem_new (IIS.add view (PPState.iis ppst)))
            (a := ()).
          -- change
               (PPState.Make (TState.promise p (PPState.state ppst))
                  mem_new (IIS.add view (PPState.iis ppst)))
               with
               (set PPState.iis (IIS.add view)
                  (PPState.Make (TState.promise p (PPState.state ppst))
                     mem_new (PPState.iis ppst))).
             apply Exec.elem_of_mset.
          -- cbn.
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

Lemma reg_read_outcome_future_promise_stable_promised tid initmem msg
    reg racc :
  outcome_future_promise_stable_promised tid initmem msg
    (RegRead reg racc).
Proof.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_guard [p_racc [Hguard Hraw]]].
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    cbn in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_ts [ts [Hget Hraw]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_reg [[val view] [Hreg Hraw]]].
    unfold othrow in Hreg.
    destruct (dmap_lookup reg (TState.regs (PPState.state ppst)))
      as [[val0 view0]|] eqn:Hlookup.
    2: {
      unfold elem_of, Exec.elem_of_results in Hreg.
      cbn in Hreg.
      inversion Hreg.
    }
    apply Exec.elem_of_mret_inv in Hreg as [-> Hreg].
    inversion Hreg; subst val0 view0.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_iis [[] [Hiis Hraw]]].
    apply Exec.elem_of_mset_inv in Hiis as ->.
    apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
    inversion Heq; subst ppst'.
    reflexivity.
  }
  unfold UMPromising_promise_ppstate, UMPromising.
  cbn.
  rewrite Hmem.
  eapply reg_read_outcome_promise_state_fmap.
  exact Hrun.
Qed.

Lemma msetv_ppstate_state_result ts
    (ppst : PPState.t TState.t Msg.t IIS.t) :
  Exec.elem_of_results (setv PPState.state ts ppst, ())
    ((msetv PPState.state ts :
        Exec.t (PPState.t TState.t Msg.t IIS.t) string unit) ppst).
Proof.
  unfold msetv, setv.
  apply Exec.elem_of_mset.
Qed.

Lemma elem_of_guard_mset_state_after_promise
    (ppst : PPState.t TState.t Msg.t IIS.t) mem_new p v upd :
  (v < p)%nat →
  TState.no_promises_until v (PPState.state ppst) →
  Exec.elem_of_results
    (PPState.Make (upd (TState.promise p (PPState.state ppst)))
       mem_new (PPState.iis ppst), ())
    (((guard_discard
         (TState.no_promises_until v
            (TState.promise p (PPState.state ppst))) :
         Exec.t (PPState.t TState.t Msg.t IIS.t) string
           (TState.no_promises_until v
              (TState.promise p (PPState.state ppst)))) ≫=
      λ _ : TState.no_promises_until v
              (TState.promise p (PPState.state ppst)),
        (((λ s : PPState.t TState.t Msg.t IIS.t,
             {| Exec.results := [(s, s)]; Exec.errors := [] |})
          : Exec.t (PPState.t TState.t Msg.t IIS.t) string
              (PPState.t TState.t Msg.t IIS.t))
         ≫= λ s : PPState.t TState.t Msg.t IIS.t,
              ((λ _ : PPState.t TState.t Msg.t IIS.t,
                  {| Exec.results := [(set PPState.state upd s, ())];
                     Exec.errors := [] |})
               : Exec.t (PPState.t TState.t Msg.t IIS.t) string unit)))
       (PPState.Make (TState.promise p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intros Hlt Hnp.
  assert
    (Hnp_promise :
       TState.no_promises_until v
         (TState.promise p (PPState.state ppst))).
  { eapply TState_no_promises_until_promise; eauto. }
  destruct (Exec.elem_of_guard_discard
    (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
    (P:=TState.no_promises_until v
          (TState.promise p (PPState.state ppst)))
    (PPState.Make (TState.promise p (PPState.state ppst))
       mem_new (PPState.iis ppst))
    Hnp_promise) as [Hnp' Hguard].
  eapply Exec.elem_of_bind_intro with
    (e := guard_discard
            (TState.no_promises_until v
               (TState.promise p (PPState.state ppst))))
    (st' := PPState.Make (TState.promise p (PPState.state ppst))
              mem_new (PPState.iis ppst))
    (a := Hnp').
  - exact Hguard.
  - cbn.
    apply elem_of_unfolded_ppstate_mset_state.
Qed.

Lemma elem_of_guard_mset_mret_state_after_promise
    (ppst : PPState.t TState.t Msg.t IIS.t) mem_new p v upd :
  (v < p)%nat →
  TState.no_promises_until v (PPState.state ppst) →
  Exec.elem_of_results
    (PPState.Make (upd (TState.promise p (PPState.state ppst)))
       mem_new (PPState.iis ppst), ((), None))
    (((guard_discard
         (TState.no_promises_until v
            (TState.promise p (PPState.state ppst))) :
         Exec.t (PPState.t TState.t Msg.t IIS.t) string
           (TState.no_promises_until v
              (TState.promise p (PPState.state ppst)))) ≫=
      λ _ : TState.no_promises_until v
              (TState.promise p (PPState.state ppst)),
        ((((λ s : PPState.t TState.t Msg.t IIS.t,
             {| Exec.results := [(s, s)]; Exec.errors := [] |})
          : Exec.t (PPState.t TState.t Msg.t IIS.t) string
              (PPState.t TState.t Msg.t IIS.t))
         ≫= λ s : PPState.t TState.t Msg.t IIS.t,
              ((λ _ : PPState.t TState.t Msg.t IIS.t,
                  {| Exec.results := [(set PPState.state upd s, ())];
                     Exec.errors := [] |})
               : Exec.t (PPState.t TState.t Msg.t IIS.t) string unit))
         ≫= λ _ : unit,
              (mret ((), None) :
                Exec.t (PPState.t TState.t Msg.t IIS.t) string
                  (unit * option view))))
       (PPState.Make (TState.promise p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intros Hlt Hnp.
  assert
    (Hnp_promise :
       TState.no_promises_until v
         (TState.promise p (PPState.state ppst))).
  { eapply TState_no_promises_until_promise; eauto. }
  destruct (Exec.elem_of_guard_discard
    (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
    (P:=TState.no_promises_until v
          (TState.promise p (PPState.state ppst)))
    (PPState.Make (TState.promise p (PPState.state ppst))
       mem_new (PPState.iis ppst))
    Hnp_promise) as [Hnp' Hguard].
  eapply Exec.elem_of_bind_intro with
    (e := guard_discard
            (TState.no_promises_until v
               (TState.promise p (PPState.state ppst))))
    (st' := PPState.Make (TState.promise p (PPState.state ppst))
              mem_new (PPState.iis ppst))
    (a := Hnp').
  - exact Hguard.
  - cbn.
    eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make (upd (TState.promise p (PPState.state ppst)))
                mem_new (PPState.iis ppst))
      (a := ()).
    + apply elem_of_unfolded_ppstate_mset_state.
    + cbn.
      apply Exec.elem_of_mret.
Qed.

Lemma reg_write_outcome_promise_state_fmap tid initmem reg racc val
    ppst ppst' p mem_new eret :
  (IIS.strict (PPState.iis ppst) < p)%nat →
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (RegWrite reg racc val) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState.promise p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (RegWrite reg racc val) |$> fst)
       (PPState.Make (TState.promise p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intros Hstrict_lt Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [p_racc [Hguard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hracc.
  apply Exec.elem_of_guard_or_inv in Hguard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vreg [vreg [Hvreg Hrun]]].
  apply Exec.elem_of_mget_inv in Hvreg as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vreg' [vreg' [Hvreg' Hrun]]].
  destruct (reg =? pc_reg) eqn:Hpc.
  - apply Exec.elem_of_bind_elim in Hvreg' as
      [pp_ts0 [ts0 [Hget_ts0 Hvreg']]].
    apply Exec.elem_of_mget_inv in Hget_ts0 as [-> ->].
    apply Exec.elem_of_bind_elim in Hvreg' as
      [pp_guard [Hnp [Hguard Hvreg']]].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hvreg' as
      [pp_vcap [[] [Hvcap Hvreg']]].
    apply Exec.elem_of_mset_inv in Hvcap as ->.
    apply Exec.elem_of_mret_inv in Hvreg' as [-> Hvreg'].
    inversion Hvreg'; subst vreg'.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_ts [ts [Hget Hrun]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_nts [nts [Hsetreg Hrun]]].
    unfold othrow in Hsetreg.
    cbn in Hsetreg.
    change
      (PPState.state
         (set PPState.state
            (TState.update TState.vcap (IIS.strict (PPState.iis ppst)))
            ppst))
      with
      (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
         (PPState.state ppst)) in Hsetreg.
    destruct
      (TState.set_reg reg (val, 0%nat)
         (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
            (PPState.state ppst))) as [nts0|] eqn:Hsetreg_eq.
    + rewrite Hsetreg_eq in Hsetreg.
      cbn in Hsetreg.
      apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
      inversion Hsetreg; subst nts0.
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_set [[] [Hset Hrun]]].
      unfold msetv in Hset.
      apply Exec.elem_of_mSet_inv in Hset as ->.
      apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
      inversion Heq; subst ppst'.
      inversion Hret; subst eret0 vpre_opt.
      destruct (Exec.elem_of_guard_or
        (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
        (P:=racc = None)
        (PPState.Make (TState.promise p (PPState.state ppst))
           mem_new (PPState.iis ppst))
        "Non trivial reg access types unsupported" Hracc) as
        [p_racc' Hguard'].
      assert
        (Hfull :
           Exec.elem_of_results
             (PPState.Make (TState.promise p nts)
                mem_new (PPState.iis ppst), ((), None))
             (run_outcome tid initmem (RegWrite reg racc val)
                (PPState.Make (TState.promise p (PPState.state ppst))
                   mem_new (PPState.iis ppst)))).
      {
        simp run_outcome.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make (TState.promise p (PPState.state ppst))
                    mem_new (PPState.iis ppst))
          (a := p_racc').
        - exact Hguard'.
        - cbn.
          eapply Exec.elem_of_bind_intro with
            (st' := PPState.Make (TState.promise p (PPState.state ppst))
                      mem_new (PPState.iis ppst))
            (a := IIS.strict (PPState.iis ppst)).
          + apply (Exec.elem_of_mget (E:=string)
              (PPState.Make (TState.promise p (PPState.state ppst))
                 mem_new (PPState.iis ppst)) (IIS.strict ∘ PPState.iis)).
          + cbn.
            rewrite Hpc.
            set (pp_prom :=
              PPState.Make (TState.promise p (PPState.state ppst))
                mem_new (PPState.iis ppst)).
            set (pp_vcap :=
              set PPState.state
                (TState.update TState.vcap (IIS.strict (PPState.iis ppst)))
                pp_prom).
            eapply Exec.elem_of_bind_intro
              with (st' := pp_vcap) (a := 0%nat).
            * eapply Exec.elem_of_bind_intro
                with (st' := pp_prom)
                     (a := TState.promise p (PPState.state ppst)).
              -- subst pp_prom.
                 apply (Exec.elem_of_mget (E:=string)
                   (PPState.Make (TState.promise p (PPState.state ppst))
                      mem_new (PPState.iis ppst)) PPState.state).
              -- cbn.
                 assert
                   (Hnp_promise :
                      TState.no_promises_until
                        (IIS.strict (PPState.iis ppst))
                        (TState.promise p (PPState.state ppst))).
                 { intros p0 Hp0.
                   apply elem_of_cons in Hp0 as [->|Hp0].
                   - exact Hstrict_lt.
                   - apply Hnp.
                     exact Hp0. }
                 destruct (Exec.elem_of_guard_discard
                   (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
                   (P:=TState.no_promises_until
                         (IIS.strict (PPState.iis ppst))
                         (TState.promise p (PPState.state ppst)))
                   pp_prom Hnp_promise) as [Hnp' Hnp_guard].
                 eapply Exec.elem_of_bind_intro
                   with
                     (e := guard_discard
                             (TState.no_promises_until
                                (IIS.strict (PPState.iis ppst))
                                (TState.promise p (PPState.state ppst))))
                     (st' := pp_prom) (a := Hnp').
                 ++ exact Hnp_guard.
                 ++ cbn.
                    eapply Exec.elem_of_bind_intro
                      with (st' := pp_vcap) (a := ()).
                    ** subst pp_vcap pp_prom.
                       apply Exec.elem_of_mset.
                    ** cbn.
                       apply Exec.elem_of_mret.
            * subst pp_vcap pp_prom.
              cbn.
              eapply Exec.elem_of_bind_intro with
                (st' := PPState.Make
                          (TState.update TState.vcap
                             (IIS.strict (PPState.iis ppst))
                             (TState.promise p (PPState.state ppst)))
                          mem_new (PPState.iis ppst))
                (a := PPState.state
                        (PPState.Make
                           (TState.update TState.vcap
                              (IIS.strict (PPState.iis ppst))
                              (TState.promise p (PPState.state ppst)))
                           mem_new (PPState.iis ppst))).
              -- apply (Exec.elem_of_mget (E:=string)
                   (PPState.Make
                      (TState.update TState.vcap
                         (IIS.strict (PPState.iis ppst))
                         (TState.promise p (PPState.state ppst)))
                      mem_new (PPState.iis ppst)) PPState.state).
              -- cbn.
                 rewrite (TState_set_reg_promise_update_vcap p
                   (IIS.strict (PPState.iis ppst)) reg (val, 0%nat)
                   (PPState.state ppst) nts Hsetreg_eq).
                 eapply Exec.elem_of_bind_intro with
                   (st' := PPState.Make
                             (TState.update TState.vcap
                                (IIS.strict (PPState.iis ppst))
                                (TState.promise p (PPState.state ppst)))
                             mem_new (PPState.iis ppst))
                   (a := TState.promise p nts).
                 ++ apply Exec.elem_of_mret.
                 ++ cbn.
                 eapply Exec.elem_of_bind_intro with
	                   (st' := PPState.Make (TState.promise p nts)
	                             mem_new (PPState.iis ppst))
	                   (a := ()).
	                 ** change
                        (PPState.Make (TState.promise p nts) mem_new
                           (PPState.iis ppst))
                        with
                        (set PPState.state
                           (λ _ : TState.t, TState.promise p nts)
                           (PPState.Make
                              (TState.update TState.vcap
                                 (IIS.strict (PPState.iis ppst))
                                 (TState.promise p (PPState.state ppst)))
                              mem_new (PPState.iis ppst))).
                      apply Exec.elem_of_mset.
	                 ** cbn.
	                    apply Exec.elem_of_mret.
      }
      simp run_outcome in Hfull.
      rewrite Hpc in Hfull.
      unfold elem_of, Exec.elem_of_results.
      unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
      cbn in Hfull |- *.
      set_unfold.
      eapply elem_of_list_fmap_1_alt.
      * exact Hfull.
      * reflexivity.
    + unfold elem_of, Exec.elem_of_results in Hsetreg.
      rewrite Hsetreg_eq in Hsetreg.
      cbn in Hsetreg.
      exfalso.
      apply (not_elem_of_nil (pp_nts, nts)).
      exact Hsetreg.
  - apply Exec.elem_of_mret_inv in Hvreg' as [-> Hvreg'].
    inversion Hvreg'; subst vreg'.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_ts [ts [Hget Hrun]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_nts [nts [Hsetreg Hrun]]].
    unfold othrow in Hsetreg.
    destruct
      (TState.set_reg reg (val, IIS.strict (PPState.iis ppst))
         (PPState.state ppst)) as [nts0|] eqn:Hsetreg_eq.
    + rewrite Hsetreg_eq in Hsetreg.
      cbn in Hsetreg.
      apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
      inversion Hsetreg; subst nts0.
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_set [[] [Hset Hrun]]].
      unfold msetv in Hset.
      apply Exec.elem_of_mSet_inv in Hset as ->.
      apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
      inversion Heq; subst ppst'.
      inversion Hret; subst eret0 vpre_opt.
      destruct (Exec.elem_of_guard_or
        (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
        (P:=racc = None)
        (PPState.Make (TState.promise p (PPState.state ppst))
           mem_new (PPState.iis ppst))
        "Non trivial reg access types unsupported" Hracc) as
        [p_racc' Hguard'].
      assert
        (Hfull :
           Exec.elem_of_results
             (PPState.Make (TState.promise p nts)
                mem_new (PPState.iis ppst), ((), None))
             (run_outcome tid initmem (RegWrite reg racc val)
                (PPState.Make (TState.promise p (PPState.state ppst))
                   mem_new (PPState.iis ppst)))).
      {
        simp run_outcome.
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make (TState.promise p (PPState.state ppst))
                    mem_new (PPState.iis ppst))
          (a := p_racc').
        - exact Hguard'.
        - cbn.
          eapply Exec.elem_of_bind_intro with
            (st' := PPState.Make (TState.promise p (PPState.state ppst))
                      mem_new (PPState.iis ppst))
            (a := IIS.strict (PPState.iis ppst)).
          + apply (Exec.elem_of_mget (E:=string)
              (PPState.Make (TState.promise p (PPState.state ppst))
                 mem_new (PPState.iis ppst)) (IIS.strict ∘ PPState.iis)).
          + cbn.
            rewrite Hpc.
            eapply Exec.elem_of_bind_intro with
              (st' := PPState.Make (TState.promise p (PPState.state ppst))
                        mem_new (PPState.iis ppst))
              (a := IIS.strict (PPState.iis ppst)).
	            * apply Exec.elem_of_mret.
	            * cbn.
	              eapply Exec.elem_of_bind_intro with
	                (st' := PPState.Make (TState.promise p (PPState.state ppst))
	                          mem_new (PPState.iis ppst))
	                (a := PPState.state
                          (PPState.Make
                             (TState.promise p (PPState.state ppst))
                             mem_new (PPState.iis ppst))).
	              -- apply (Exec.elem_of_mget (E:=string)
                     (PPState.Make (TState.promise p (PPState.state ppst))
                        mem_new (PPState.iis ppst)) PPState.state).
	              -- cbn.
                   rewrite (TState_set_reg_promise p reg
                     (val, IIS.strict (PPState.iis ppst))
                     (PPState.state ppst) nts Hsetreg_eq).
                   eapply Exec.elem_of_bind_intro with
                     (st' := PPState.Make
                               (TState.promise p (PPState.state ppst))
                               mem_new (PPState.iis ppst))
                     (a := TState.promise p nts).
                   ++ apply Exec.elem_of_mret.
                   ++ cbn.
	                 eapply Exec.elem_of_bind_intro with
		                   (st' := PPState.Make (TState.promise p nts)
		                             mem_new (PPState.iis ppst))
		                   (a := ()).
	                 ** change
                        (PPState.Make (TState.promise p nts) mem_new
                           (PPState.iis ppst))
                        with
                        (set PPState.state
                           (λ _ : TState.t, TState.promise p nts)
                           (PPState.Make
                              (TState.promise p (PPState.state ppst))
                              mem_new (PPState.iis ppst))).
                      apply Exec.elem_of_mset.
	                 ** cbn.
	                    apply Exec.elem_of_mret.
      }
      simp run_outcome in Hfull.
      rewrite Hpc in Hfull.
      unfold elem_of, Exec.elem_of_results.
      unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
      cbn in Hfull |- *.
      set_unfold.
      eapply elem_of_list_fmap_1_alt.
      * exact Hfull.
      * reflexivity.
    + unfold elem_of, Exec.elem_of_results in Hsetreg.
      rewrite Hsetreg_eq in Hsetreg.
      cbn in Hsetreg.
      exfalso.
      apply (not_elem_of_nil (pp_nts, nts)).
      exact Hsetreg.
Qed.

Lemma reg_write_outcome_future_promise_stable_promised tid initmem msg
    reg racc val :
  (∀ ppst, ppstate_control_times_le ppst) →
  outcome_future_promise_stable_promised tid initmem msg
    (RegWrite reg racc val).
Proof.
  intro Hcontrol.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_guard [p_racc [Hguard Hraw]]].
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    cbn in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_vreg [vreg [Hvreg Hraw]]].
    apply Exec.elem_of_mget_inv in Hvreg as [-> ->].
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_vreg' [vreg' [Hvreg' Hraw]]].
    destruct (reg =? pc_reg) eqn:Hpc.
    - apply Exec.elem_of_bind_elim in Hvreg' as
        [pp_ts0 [ts0 [Hget_ts0 Hvreg']]].
      apply Exec.elem_of_mget_inv in Hget_ts0 as [-> ->].
      apply Exec.elem_of_bind_elim in Hvreg' as
        [pp_guard [Hnp [Hguard Hvreg']]].
      apply Exec.elem_of_guard_discard_inv in Hguard as ->.
      apply Exec.elem_of_bind_elim in Hvreg' as
        [pp_vcap [[] [Hvcap Hvreg']]].
      apply Exec.elem_of_mset_inv in Hvcap as ->.
      apply Exec.elem_of_mret_inv in Hvreg' as [-> Hvreg'].
      inversion Hvreg'; subst vreg'.
      apply Exec.elem_of_bind_elim in Hraw as
        [pp_ts [ts [Hget Hraw]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      apply Exec.elem_of_bind_elim in Hraw as
        [pp_nts [nts [Hsetreg Hraw]]].
      unfold othrow in Hsetreg.
      cbn in Hsetreg.
      change
        (PPState.state
           (set PPState.state
              (TState.update TState.vcap (IIS.strict (PPState.iis ppst)))
              ppst))
        with
        (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
           (PPState.state ppst)) in Hsetreg.
      destruct
        (TState.set_reg reg (val, 0%nat)
           (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
              (PPState.state ppst))) as [nts0|] eqn:Hsetreg_eq.
      + rewrite Hsetreg_eq in Hsetreg.
        cbn in Hsetreg.
        apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
        inversion Hsetreg; subst nts0.
        apply Exec.elem_of_bind_elim in Hraw as
          [pp_set [[] [Hset Hraw]]].
        unfold msetv in Hset.
        apply Exec.elem_of_mSet_inv in Hset as ->.
        apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
        inversion Heq; subst ppst'; reflexivity.
      + unfold elem_of, Exec.elem_of_results in Hsetreg.
        rewrite Hsetreg_eq in Hsetreg.
        cbn in Hsetreg.
        exfalso; apply (not_elem_of_nil (pp_nts, nts)); exact Hsetreg.
    -
      apply Exec.elem_of_mret_inv in Hvreg' as [-> Hvreg'].
      inversion Hvreg'; subst vreg'.
      apply Exec.elem_of_bind_elim in Hraw as
        [pp_ts [ts [Hget Hraw]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      apply Exec.elem_of_bind_elim in Hraw as
        [pp_nts [nts [Hsetreg Hraw]]].
      unfold othrow in Hsetreg.
      destruct
        (TState.set_reg reg (val, IIS.strict (PPState.iis ppst))
           (PPState.state ppst)) as [nts0|] eqn:Hsetreg_eq.
      + rewrite Hsetreg_eq in Hsetreg.
        cbn in Hsetreg.
        apply Exec.elem_of_mret_inv in Hsetreg as [-> Hsetreg].
        inversion Hsetreg; subst nts0.
        apply Exec.elem_of_bind_elim in Hraw as
          [pp_set [[] [Hset Hraw]]].
        unfold msetv in Hset.
        apply Exec.elem_of_mSet_inv in Hset as ->.
        apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
        inversion Heq; subst ppst'; reflexivity.
      + unfold elem_of, Exec.elem_of_results in Hsetreg.
        rewrite Hsetreg_eq in Hsetreg.
        cbn in Hsetreg.
        exfalso; apply (not_elem_of_nil (pp_nts, nts)); exact Hsetreg.
  }
  unfold UMPromising_promise_ppstate, UMPromising.
  cbn.
  rewrite Hmem.
  eapply reg_write_outcome_promise_state_fmap.
  - destruct (Hcontrol ppst) as [Hstrict_le _].
    cbn.
    lia.
  - exact Hrun.
Qed.

Lemma mem_write_addr_announce_outcome_promise_state_fmap tid initmem req
    ppst ppst' p mem_new eret :
  (IIS.strict (PPState.iis ppst) < p)%nat →
  Exec.elem_of_results (ppst', eret)
    ((run_outcome tid initmem (MemWriteAddrAnnounce req) |$> fst) ppst) →
  Exec.elem_of_results
    (PPState.Make (TState.promise p (PPState.state ppst'))
       mem_new (PPState.iis ppst'), eret)
    ((run_outcome tid initmem (MemWriteAddrAnnounce req) |$> fst)
       (PPState.Make (TState.promise p (PPState.state ppst))
          mem_new (PPState.iis ppst))).
Proof.
  intros Hstrict_lt Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
  simp run_outcome in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_vaddr [vaddr [Hvaddr Hrun]]].
  apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_ts [ts [Hget_ts Hrun]]].
  apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_guard [Hnp [Hguard Hrun]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [pp_state [[] [Hstate Hrun]]].
  apply Exec.elem_of_mset_inv in Hstate as ->.
  apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  assert
    (Hfull :
       Exec.elem_of_results
         (PPState.Make
            (TState.promise p
               (TState.update TState.vcap (IIS.strict (PPState.iis ppst))
                  (PPState.state ppst)))
            mem_new (PPState.iis ppst), ((), None))
         (run_outcome tid initmem (MemWriteAddrAnnounce req)
            (PPState.Make (TState.promise p (PPState.state ppst))
               mem_new (PPState.iis ppst)))).
  {
    simp run_outcome.
    eapply Exec.elem_of_bind_intro with
      (e := (mget (IIS.strict ∘ PPState.iis) :
               Exec.t (PPState.t TState.t Msg.t IIS.t) string nat))
      (st' := PPState.Make (TState.promise p (PPState.state ppst))
                mem_new (PPState.iis ppst))
      (a := IIS.strict (PPState.iis ppst)).
    - apply (Exec.elem_of_mget (E:=string)
        (PPState.Make (TState.promise p (PPState.state ppst))
           mem_new (PPState.iis ppst)) (IIS.strict ∘ PPState.iis)).
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := (mget PPState.state :
                 Exec.t (PPState.t TState.t Msg.t IIS.t) string TState.t))
        (st' := PPState.Make (TState.promise p (PPState.state ppst))
                  mem_new (PPState.iis ppst))
        (a := TState.promise p (PPState.state ppst)).
      + apply (Exec.elem_of_mget (E:=string)
          (PPState.Make (TState.promise p (PPState.state ppst))
             mem_new (PPState.iis ppst)) PPState.state).
      + cbn.
        assert
          (Hnp_promise :
             TState.no_promises_until
               (IIS.strict (PPState.iis ppst))
               (TState.promise p (PPState.state ppst))).
        { eapply TState_no_promises_until_promise; eauto. }
        destruct (Exec.elem_of_guard_discard
          (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
          (P:=TState.no_promises_until
                (IIS.strict (PPState.iis ppst))
                (TState.promise p (PPState.state ppst)))
          (PPState.Make (TState.promise p (PPState.state ppst))
             mem_new (PPState.iis ppst))
          Hnp_promise) as [Hnp' Hnp_guard].
        eapply Exec.elem_of_bind_intro with
          (e := guard_discard
                  (TState.no_promises_until
                     (IIS.strict (PPState.iis ppst))
                     (TState.promise p (PPState.state ppst))))
          (st' := PPState.Make (TState.promise p (PPState.state ppst))
                    mem_new (PPState.iis ppst))
          (a := Hnp').
        * exact Hnp_guard.
        * cbn.
          eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise p
                     (TState.update TState.vcap
                        (IIS.strict (PPState.iis ppst))
                        (PPState.state ppst)))
                  mem_new (PPState.iis ppst))
        (a := ()).
          -- change
          (PPState.Make
             (TState.promise p
                (TState.update TState.vcap
                   (IIS.strict (PPState.iis ppst))
                   (PPState.state ppst)))
             mem_new (PPState.iis ppst))
          with
          (PPState.Make
             (TState.update TState.vcap
                (IIS.strict (PPState.iis ppst))
                (TState.promise p (PPState.state ppst)))
             mem_new (PPState.iis ppst)).
        change
          (PPState.Make
             (TState.update TState.vcap
                (IIS.strict (PPState.iis ppst))
                (TState.promise p (PPState.state ppst)))
             mem_new (PPState.iis ppst))
          with
             (set PPState.state
                (TState.update TState.vcap (IIS.strict (PPState.iis ppst)))
                (PPState.Make (TState.promise p (PPState.state ppst))
                   mem_new (PPState.iis ppst))).
             apply Exec.elem_of_mset.
          -- cbn.
             apply Exec.elem_of_mret.
  }
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  cbn in Hfull |- *.
  set_unfold.
  eapply elem_of_list_fmap_1_alt.
  - exact Hfull.
  - cbn.
    rewrite <- TState_promise_update_vcap.
    reflexivity.
Qed.

Lemma mem_write_addr_announce_outcome_future_promise_stable_promised
    tid initmem msg req :
  (∀ ppst, ppstate_control_times_le ppst) →
  outcome_future_promise_stable_promised tid initmem msg
    (MemWriteAddrAnnounce req).
Proof.
  intro Hcontrol.
  intros ppst ppst' eret Hrun.
  assert (Hmem : PPState.mem ppst' = PPState.mem ppst).
  {
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
    simp run_outcome in Hraw.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_vaddr [vaddr [Hvaddr Hraw]]].
    apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_ts [ts [Hget_ts Hraw]]].
    apply Exec.elem_of_mget_inv in Hget_ts as [-> ->].
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_guard [Hnp [Hguard Hraw]]].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in Hraw as
      [pp_state [[] [Hstate Hraw]]].
    apply Exec.elem_of_mset_inv in Hstate as ->.
    apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
    inversion Heq; subst ppst'.
    reflexivity.
  }
  unfold UMPromising_promise_ppstate, UMPromising.
  cbn.
  rewrite Hmem.
  eapply mem_write_addr_announce_outcome_promise_state_fmap.
  - destruct (Hcontrol ppst) as [Hstrict_le _].
    cbn.
    lia.
  - exact Hrun.
Qed.

Lemma barrier_dmb_outcome_future_promise_stable_promised tid initmem msg
    dmb :
  (∀ ppst, ppstate_control_times_le ppst) →
  outcome_future_promise_stable_promised tid initmem msg
    (Barrier (Barrier_DMB dmb)).
Proof.
  intro Hcontrol.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as [pp_ts [ts [Hget Hraw]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  destruct dmb.(DxB_types) eqn:Hdmb.
  all: apply Exec.elem_of_bind_elim in Hraw as
    [pp_state [[] [Hbar Hraw]]].
  all: apply Exec.elem_of_bind_elim in Hbar as
    [pp_guard [Hnp [Hguard Hstate]]].
  all: apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  all: apply Exec.elem_of_mset_inv in Hstate as ->.
  all: apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
  all: inversion Heq; subst ppst'.
  all: inversion Hret; subst eret0 vpre_opt.
  all: unfold UMPromising_promise_ppstate, UMPromising; cbn.
  all: unfold elem_of, Exec.elem_of_results.
  all: unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  all: set_unfold; cbn; simp run_outcome; cbn; rewrite Hdmb; cbn.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmb
                  (TState.vrd (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
      * cbn.
        change (TState.vrd
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
          with (TState.vrd (PPState.state ppst)).
	        eapply Exec.elem_of_bind_intro with
	          (st' := PPState.Make
	                    (TState.update TState.vdmb
	                       (TState.vrd (PPState.state ppst))
	                       (TState.promise (S (length (PPState.mem ppst)))
	                          (PPState.state ppst)))
	                    (msg :: PPState.mem ppst) (PPState.iis ppst))
	          (a := ()).
	        -- eapply elem_of_guard_mset_state_after_promise.
	           ++ destruct (Hcontrol ppst) as [_ [Hvrd _]].
	              cbn in *.
	              lia.
	           ++ exact Hnp.
	        -- cbn.
	           apply Exec.elem_of_mret.
    + cbn.
      rewrite TState_promise_update_vdmb.
      reflexivity.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmbst
                  (TState.vwr (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
      * cbn.
        change (TState.vwr
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
          with (TState.vwr (PPState.state ppst)).
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make
                    (TState.update TState.vdmbst
                       (TState.vwr (PPState.state ppst))
                       (TState.promise (S (length (PPState.mem ppst)))
                          (PPState.state ppst)))
                    (msg :: PPState.mem ppst) (PPState.iis ppst))
          (a := ()).
        -- eapply elem_of_guard_mset_state_after_promise.
           ++ destruct (Hcontrol ppst) as [_ [_ [Hvwr _]]].
              cbn in *.
              lia.
           ++ exact Hnp.
        -- cbn.
           apply Exec.elem_of_mret.
    + cbn.
      rewrite TState_promise_update_vdmbst.
      reflexivity.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmb
                  (TState.vrd (PPState.state ppst) ⊔
                   TState.vwr (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
      * cbn.
        change (TState.vrd
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
          with (TState.vrd (PPState.state ppst)).
        change (TState.vwr
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
          with (TState.vwr (PPState.state ppst)).
        eapply Exec.elem_of_bind_intro with
          (st' := PPState.Make
                    (TState.update TState.vdmb
                       (TState.vrd (PPState.state ppst) ⊔
                        TState.vwr (PPState.state ppst))
                       (TState.promise (S (length (PPState.mem ppst)))
                          (PPState.state ppst)))
                    (msg :: PPState.mem ppst) (PPState.iis ppst))
          (a := ()).
        -- eapply elem_of_guard_mset_state_after_promise.
           ++ destruct (Hcontrol ppst) as [_ [Hvrd [Hvwr _]]].
              cbn in *.
              change (TState.vrd (PPState.state ppst) ⊔
                      TState.vwr (PPState.state ppst))
                with (Nat.max (TState.vrd (PPState.state ppst))
                        (TState.vwr (PPState.state ppst))).
              lia.
           ++ exact Hnp.
        -- cbn.
           apply Exec.elem_of_mret.
    + cbn.
      rewrite TState_promise_update_vdmb.
      reflexivity.
Qed.

Lemma barrier_isb_outcome_future_promise_stable_promised tid initmem msg :
  (∀ ppst, ppstate_control_times_le ppst) →
  outcome_future_promise_stable_promised tid initmem msg
    (Barrier (Barrier_ISB ())).
Proof.
  intro Hcontrol.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as [pp_ts [ts [Hget Hraw]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_guard [Hnp [Hguard Hraw]]].
  apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  apply Exec.elem_of_bind_elim in Hraw as
    [pp_state [[] [Hstate Hraw]]].
  apply Exec.elem_of_mset_inv in Hstate as ->.
  apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
  inversion Heq; subst ppst'.
  inversion Hret; subst eret0 vpre_opt.
  unfold UMPromising_promise_ppstate, UMPromising.
  cbn.
  unfold elem_of, Exec.elem_of_results.
  unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  set_unfold.
  cbn.
  simp run_outcome.
  cbn.
  eapply elem_of_list_fmap_1_alt with
    (x := (PPState.Make
             (TState.update TState.visb (TState.vcap (PPState.state ppst))
                (TState.promise (S (length (PPState.mem ppst)))
                   (PPState.state ppst)))
             (msg :: PPState.mem ppst) (PPState.iis ppst),
           ((), None))).
  - eapply Exec.elem_of_bind_intro with
      (st' := PPState.Make
                (TState.promise (S (length (PPState.mem ppst)))
                   (PPState.state ppst))
                (msg :: PPState.mem ppst) (PPState.iis ppst))
      (a := TState.promise (S (length (PPState.mem ppst)))
              (PPState.state ppst)).
    + apply (Exec.elem_of_mget (E:=string)
        (PPState.Make
           (TState.promise (S (length (PPState.mem ppst)))
              (PPState.state ppst))
           (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
    + cbn.
	      change (TState.vcap
	                (TState.promise (S (length (PPState.mem ppst)))
	                   (PPState.state ppst)))
	        with (TState.vcap (PPState.state ppst)).
	      assert
	        (Hnp_promise :
	           TState.no_promises_until
	             (TState.vcap (PPState.state ppst))
	             (TState.promise (S (length (PPState.mem ppst)))
	                (PPState.state ppst))).
	      { eapply TState_no_promises_until_promise.
	        - destruct (Hcontrol ppst) as [_ [_ [_ Hvcap]]].
	          cbn in *.
	          lia.
	        - exact Hnp. }
	      destruct (Exec.elem_of_guard_discard
	        (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
	        (P:=TState.no_promises_until
	              (TState.vcap (PPState.state ppst))
	              (TState.promise (S (length (PPState.mem ppst)))
	                 (PPState.state ppst)))
	        (PPState.Make
	           (TState.promise (S (length (PPState.mem ppst)))
	              (PPState.state ppst))
	           (msg :: PPState.mem ppst) (PPState.iis ppst))
	        Hnp_promise) as [Hnp' Hguard'].
	      eapply Exec.elem_of_bind_intro with
	        (e := guard_discard
	                (TState.no_promises_until
	                   (TState.vcap (PPState.state ppst))
	                   (TState.promise (S (length (PPState.mem ppst)))
	                      (PPState.state ppst))))
	        (st' := PPState.Make
	                  (TState.promise (S (length (PPState.mem ppst)))
	                     (PPState.state ppst))
	                  (msg :: PPState.mem ppst) (PPState.iis ppst))
	        (a := Hnp').
	      * exact Hguard'.
	      * cbn.
	        eapply Exec.elem_of_bind_intro with
	          (st' := PPState.Make
	                    (TState.update TState.visb
	                       (TState.vcap (PPState.state ppst))
	                       (TState.promise (S (length (PPState.mem ppst)))
	                          (PPState.state ppst)))
	                    (msg :: PPState.mem ppst) (PPState.iis ppst))
	          (a := ()).
	        -- apply elem_of_unfolded_ppstate_mset_state.
	        -- cbn.
	           apply Exec.elem_of_mret.
  - cbn.
    rewrite TState_promise_update_visb.
    reflexivity.
Qed.

Lemma UMPromising_imon_future_promise_stable_to_cmon {n}
    (tid : fin n) initmem code msg A (mon : iMon A) :
  imon_future_promise_stable_fmap (tid : nat) initmem code msg A mon →
  CPStateProof.cmon_handle_outcome_cons_event_stable UMPromising
    tid initmem msg A mon.
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

Lemma UMPromising_run_tid_cons_event_stable_from_imon {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    initmem code msg st st' :
  initmem = CPState.initmem st →
  imon_future_promise_stable_fmap (tid : nat) initmem code msg () isem →
  Exec.elem_of_results (st', ()) (CPState.run_tid isem UMPromising tid st) →
  Exec.elem_of_results
    (CPStateProof.cons_event_state UMPromising msg st', ())
    (CPState.run_tid isem UMPromising tid
       (CPStateProof.cons_event_state UMPromising msg st)).
Proof.
  intros Hinit Hstable Hrun.
  eapply CPStateProof.run_tid_cons_event_stable_mon.
  - exact Hinit.
  - apply (UMPromising_imon_future_promise_stable_to_cmon
      tid initmem code msg () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Lemma UMPromising_run_to_termination_plain_cons_event_stable_from_imon {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    initmem code msg fuel ppst ppst' b :
  imon_future_promise_stable_fmap (tid : nat) initmem code msg () isem →
  Exec.elem_of_results (ppst', b)
    (CPStateProof.run_to_termination_plain isem UMPromising term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (CPStateProof.cons_event_ppstate UMPromising msg ppst', b)
    (CPStateProof.run_to_termination_plain isem UMPromising term
       tid initmem fuel
       (CPStateProof.cons_event_ppstate UMPromising msg ppst)).
Proof.
  intros Hstable Hrun.
  eapply CPStateProof.run_to_termination_plain_cons_event_stable_mon.
  - apply (UMPromising_imon_future_promise_stable_to_cmon
      tid initmem code msg () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Lemma UMPromising_imon_future_promise_stable_promised_to_cmon {n}
    (tid : fin n) initmem msg A (mon : iMon A) :
  imon_future_promise_stable_promised (tid : nat) initmem msg A mon →
  CPStateProof.cmon_handle_outcome_promise_ppstate_stable UMPromising
    tid initmem msg A mon.
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

Lemma UMPromising_run_tid_promise_same_stable_from_imon {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    initmem msg st st' :
  initmem = CPState.initmem st →
  imon_future_promise_stable_promised
    (tid : nat) initmem msg () isem →
  Exec.elem_of_results (st', ()) (CPState.run_tid isem UMPromising tid st) →
  Exec.elem_of_results
    (CPState.promise_tid UMPromising tid msg st', ())
    (CPState.run_tid isem UMPromising tid
       (CPState.promise_tid UMPromising tid msg st)).
Proof.
  intros Hinit Hstable Hrun.
  eapply CPStateProof.run_tid_promise_same_stable_mon.
  - exact Hinit.
  - apply (UMPromising_imon_future_promise_stable_promised_to_cmon
      tid initmem msg () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Lemma UMPromising_run_to_termination_plain_promise_same_stable_from_imon {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    initmem msg fuel ppst ppst' b :
  imon_future_promise_stable_promised
    (tid : nat) initmem msg () isem →
  Exec.elem_of_results (ppst', b)
    (CPStateProof.run_to_termination_plain isem UMPromising term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (UMPromising_promise_ppstate tid initmem msg ppst', b)
    (CPStateProof.run_to_termination_plain isem UMPromising term
       tid initmem fuel
       (UMPromising_promise_ppstate tid initmem msg ppst)).
Proof.
  intros Hstable Hrun.
  rewrite !UMPromising_promise_ppstate_eq_CPState.
  eapply CPStateProof.run_to_termination_plain_promise_ppstate_stable_mon.
  - intro ppst0.
    destruct ppst0 as [ts mem iis0].
    cbn.
    rewrite TState_reg_map_promise.
    reflexivity.
  - apply (UMPromising_imon_future_promise_stable_promised_to_cmon
      tid initmem msg () isem).
    exact Hstable.
  - exact Hrun.
Qed.

Record UMPromising_tail_stable {n} (isem : iMon ()) : Prop := {
    UMPromising_tail_same_promise_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (msg : Msg.t),
        imon_future_promise_stable_promised
          (tid : nat) initmem msg () isem;
    UMPromising_tail_future_event_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (code : code_region)
          (msg : Msg.t),
        imon_future_promise_stable_fmap
          (tid : nat) initmem code msg () isem;
  }.

Fixpoint UMPromising_Sail_promised_stable tid initmem msg nondet
    {A eo} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      imon_future_promise_stable_promised tid initmem msg _
        (Sail_outcome_interp nondet out) ∧
      ∀ ret,
        UMPromising_Sail_promised_stable tid initmem msg nondet (k ret)
  end.

Fixpoint UMPromising_Sail_fmap_stable tid initmem code msg nondet
    {A eo} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      imon_future_promise_stable_fmap tid initmem code msg _
        (Sail_outcome_interp nondet out) ∧
      ∀ ret,
        UMPromising_Sail_fmap_stable tid initmem code msg nondet (k ret)
  end.

Lemma UMPromising_imon_promised_stable_bind tid initmem msg
    {A B} (mon : iMon A) (k : A → iMon B) :
  imon_future_promise_stable_promised tid initmem msg A mon →
  (∀ a, imon_future_promise_stable_promised tid initmem msg B (k a)) →
  imon_future_promise_stable_promised tid initmem msg B
    (a ← mon; k a).
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

Lemma UMPromising_imon_fmap_stable_bind tid initmem code msg
    {A B} (mon : iMon A) (k : A → iMon B) :
  imon_future_promise_stable_fmap tid initmem code msg A mon →
  (∀ a, imon_future_promise_stable_fmap tid initmem code msg B (k a)) →
  imon_future_promise_stable_fmap tid initmem code msg B (a ← mon; k a).
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

Lemma UMPromising_iMon_from_Sail_promised_stable tid initmem msg nondet
    {A eo} (smon : SI.iMon eo A) :
  UMPromising_Sail_promised_stable tid initmem msg nondet smon →
  imon_future_promise_stable_promised tid initmem msg A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|out k IH]; cbn.
  - intro Hstable.
    exact I.
  - rename H into Hind.
    intros [Hout Hk].
    eapply UMPromising_imon_promised_stable_bind.
    + exact Hout.
    + intro eret.
      apply Hind.
      apply Hk.
Qed.

Lemma UMPromising_iMon_from_Sail_fmap_stable tid initmem code msg nondet
    {A eo} (smon : SI.iMon eo A) :
  UMPromising_Sail_fmap_stable tid initmem code msg nondet smon →
  imon_future_promise_stable_fmap tid initmem code msg A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|out k IH]; cbn.
  - intro Hstable.
    exact I.
  - rename H into Hind.
    intros [Hout Hk].
    eapply UMPromising_imon_fmap_stable_bind.
    + exact Hout.
    + intro eret.
      apply Hind.
      apply Hk.
Qed.

Record UMPromising_Sail_tail_stable {n eo} nondet
    (smon : SI.iMon eo ()) : Prop := {
    UMPromising_Sail_tail_same_promise_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (msg : Msg.t),
        UMPromising_Sail_promised_stable
          (tid : nat) initmem msg nondet smon;
    UMPromising_Sail_tail_future_event_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (code : code_region)
          (msg : Msg.t),
        UMPromising_Sail_fmap_stable
          (tid : nat) initmem code msg nondet smon;
  }.

Record UMPromising_Sail_same_promise_stable {n eo} nondet
    (smon : SI.iMon eo ()) : Prop := {
    UMPromising_Sail_same_promised_stable :
      ∀ (tid : fin n) (initmem : memoryMap) (msg : Msg.t),
        UMPromising_Sail_promised_stable
          (tid : nat) initmem msg nondet smon;
  }.

Record UMPromising_read_code_stability (tid : nat)
    (initmem : memoryMap) (code : code_region) (msg : Msg.t) : Prop := {
    UMPromising_read_code_ifetch_stable :
      ∀ (addr : address) (size : N) (macc : mem_acc)
          (addr_space : addr_space),
        is_ifetch macc = true →
        event_misses_code code msg ∧ ifetch_in_code code addr size;
    UMPromising_read_code_explicit_read_bound :
      ∀ (ppst : PPState.t TState.t Msg.t IIS.t)
          (addr : address) (size : N) (macc : mem_acc)
          (addr_space : addr_space),
        is_ifetch macc = false →
        is_explicit macc = true →
        ppstate_read_times_le macc ppst;
    UMPromising_read_code_control_bound :
      ∀ (ppst : PPState.t TState.t Msg.t IIS.t),
        ppstate_control_times_le ppst;
  }.

Lemma UMPromising_mem_read_promised_stable_from_read_code
    tid initmem code msg addr size macc addr_space :
  UMPromising_read_code_stability tid initmem code msg →
  outcome_future_promise_stable_promised tid initmem msg
    (MemRead (MemReq.make macc addr addr_space size 0)).
Proof.
  intro Hstable.
  destruct Hstable as [Hifetch Hbound Hcontrol].
  apply mem_read_outcome_future_promise_stable_promised with
    (code := code).
  - apply (Hifetch addr size macc addr_space).
  - intros ppst Hnot_ifetch Hexplicit.
    eapply Hbound; eauto.
Qed.

Lemma UMPromising_mem_read_fmap_stable_from_read_code
    tid initmem code msg addr size macc addr_space :
  UMPromising_read_code_stability tid initmem code msg →
  outcome_future_promise_stable_fmap tid initmem code msg
    (MemRead (MemReq.make macc addr addr_space size 0)).
Proof.
  intro Hstable.
  destruct Hstable as [Hifetch Hbound Hcontrol].
  apply mem_read_outcome_future_promise_stable_fmap.
  - apply (Hifetch addr size macc addr_space).
  - intros ppst Hnot_ifetch Hexplicit.
    eapply Hbound; eauto.
Qed.

Ltac solve_UMPromising_unsupported_promised_stable :=
  intros ppst ppst' eret Hrun;
  cbn in Hrun;
  unfold mthrow, Exec.throw_inst, Exec.res_throw_inst in Hrun;
  unfold elem_of, Exec.elem_of_results in Hrun;
  cbn in Hrun;
  inversion Hrun.

Lemma UMPromising_cache_op_outcome_future_promise_stable_promised
    tid initmem msg cop :
  outcome_future_promise_stable_promised tid initmem msg
    (CacheOp cop).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_tlbop_outcome_future_promise_stable_promised
    tid initmem msg tlbi :
  outcome_future_promise_stable_promised tid initmem msg
    (TlbOp tlbi).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_take_exception_outcome_future_promise_stable_promised
    tid initmem msg fault :
  outcome_future_promise_stable_promised tid initmem msg
    (TakeException fault).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_return_exception_outcome_future_promise_stable_promised
    tid initmem msg :
  outcome_future_promise_stable_promised tid initmem msg ReturnException.
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_translation_start_outcome_future_promise_stable_promised
    tid initmem msg ts :
  outcome_future_promise_stable_promised tid initmem msg
    (TranslationStart ts).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_translation_end_outcome_future_promise_stable_promised
    tid initmem msg te :
  outcome_future_promise_stable_promised tid initmem msg
    (TranslationEnd te).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_barrier_dsb_outcome_future_promise_stable_promised
    tid initmem msg dsb :
  (∀ ppst, ppstate_control_times_le ppst) →
  outcome_future_promise_stable_promised tid initmem msg
    (Barrier (Barrier_DSB dsb)).
Proof.
  intro Hcontrol.
  intros ppst ppst' eret Hrun.
  apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hraw]].
  simp run_outcome in Hraw.
  apply Exec.elem_of_bind_elim in Hraw as [pp_ts [ts [Hget Hraw]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  destruct dsb.(DxB_types) eqn:Hdsb.
  all: apply Exec.elem_of_bind_elim in Hraw as
    [pp_guard [Hnp [Hguard Hraw]]].
  all: apply Exec.elem_of_guard_discard_inv in Hguard as ->.
  all: apply Exec.elem_of_bind_elim in Hraw as
    [pp_state [[] [Hstate Hraw]]].
  all: apply Exec.elem_of_mset_inv in Hstate as ->.
  all: apply Exec.elem_of_mret_inv in Hraw as [Heq Hret].
  all: inversion Heq; subst ppst'.
  all: inversion Hret; subst eret0 vpre_opt.
  all: unfold UMPromising_promise_ppstate, UMPromising; cbn.
  all: unfold elem_of, Exec.elem_of_results.
  all: unfold fmap, Exec.fmap_inst, Exec.res_fmap_inst.
  all: set_unfold; cbn; simp run_outcome; cbn; rewrite Hdsb; cbn.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmb
                  (TState.vrd (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
	             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
	      * cbn.
	        change (TState.vrd
	                  (TState.promise (S (length (PPState.mem ppst)))
	                     (PPState.state ppst)))
	          with (TState.vrd (PPState.state ppst)).
		        eapply elem_of_guard_mset_mret_state_after_promise.
		        -- destruct (Hcontrol ppst) as [_ [Hvrd _]].
		           cbn in *.
		           lia.
		        -- exact Hnp.
    + cbn.
      rewrite TState_promise_update_vdmb.
      reflexivity.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmb
                  (TState.vwr (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
	             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
	      * cbn.
	        change (TState.vwr
	                  (TState.promise (S (length (PPState.mem ppst)))
	                     (PPState.state ppst)))
	          with (TState.vwr (PPState.state ppst)).
		        eapply elem_of_guard_mset_mret_state_after_promise.
		        -- destruct (Hcontrol ppst) as [_ [_ [Hvwr _]]].
		           cbn in *.
		           lia.
		        -- exact Hnp.
    + cbn.
      rewrite TState_promise_update_vdmb.
      reflexivity.
  - eapply elem_of_list_fmap_1_alt with
      (x := (PPState.Make
               (TState.update TState.vdmb
                  (TState.vrd (PPState.state ppst) ⊔
                   TState.vwr (PPState.state ppst))
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst)))
               (msg :: PPState.mem ppst) (PPState.iis ppst),
             ((), None))).
    + eapply Exec.elem_of_bind_intro with
        (st' := PPState.Make
                  (TState.promise (S (length (PPState.mem ppst)))
                     (PPState.state ppst))
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
        (a := TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst)).
      * apply (Exec.elem_of_mget (E:=string)
          (PPState.Make
             (TState.promise (S (length (PPState.mem ppst)))
                (PPState.state ppst))
	             (msg :: PPState.mem ppst) (PPState.iis ppst)) PPState.state).
	      * cbn.
	        change (TState.vrd
	                  (TState.promise (S (length (PPState.mem ppst)))
	                     (PPState.state ppst)))
	          with (TState.vrd (PPState.state ppst)).
	        change (TState.vwr
	                  (TState.promise (S (length (PPState.mem ppst)))
	                     (PPState.state ppst)))
	          with (TState.vwr (PPState.state ppst)).
		        eapply elem_of_guard_mset_mret_state_after_promise.
		        -- destruct (Hcontrol ppst) as [_ [Hvrd [Hvwr _]]].
		           cbn in *.
		           change (TState.vrd (PPState.state ppst) ⊔
		                   TState.vwr (PPState.state ppst))
		             with (Nat.max (TState.vrd (PPState.state ppst))
		                     (TState.vwr (PPState.state ppst))).
		           lia.
		        -- exact Hnp.
    + cbn.
      rewrite TState_promise_update_vdmb.
      reflexivity.
Qed.

Lemma UMPromising_generic_fail_outcome_future_promise_stable_promised
    tid initmem msg s :
  outcome_future_promise_stable_promised tid initmem msg
    (GenericFail s).
Proof.
  intros ppst ppst' [].
Qed.

Lemma UMPromising_mem_read_nonzero_tag_promised_stable tid initmem msg
    addr size macc addr_space tag :
  outcome_future_promise_stable_promised tid initmem msg
    (MemRead (MemReq.make macc addr addr_space size (N.pos tag))).
Proof.
  solve_UMPromising_unsupported_promised_stable.
Qed.

Lemma UMPromising_tail_stable_from_Sail {n eo} nondet
    (smon : SI.iMon eo ()) :
  UMPromising_Sail_tail_stable (n:=n) nondet smon →
  UMPromising_tail_stable (n:=n) (iMon_from_Sail nondet smon).
Proof.
  intro Hstable.
  constructor.
  - intros tid initmem msg.
    apply UMPromising_iMon_from_Sail_promised_stable.
    apply UMPromising_Sail_tail_same_promise_stable.
    exact Hstable.
  - intros tid initmem code msg.
    apply UMPromising_iMon_from_Sail_fmap_stable.
    apply UMPromising_Sail_tail_future_event_stable.
    exact Hstable.
Qed.

Lemma UMPromising_Sail_same_promise_stable_from_tail_stable
    {n eo} nondet (smon : SI.iMon eo ()) :
  UMPromising_Sail_tail_stable (n:=n) nondet smon →
  UMPromising_Sail_same_promise_stable (n:=n) nondet smon.
Proof.
  intro Hstable.
  constructor.
  intros tid initmem msg.
  apply UMPromising_Sail_tail_same_promise_stable.
  exact Hstable.
Qed.

Lemma UMPromising_tail_stable_run_tid_promise_same {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (msg : Msg.t) st st' :
  UMPromising_tail_stable (n:=n) isem →
  initmem = CPState.initmem st →
  Exec.elem_of_results (st', ()) (CPState.run_tid isem UMPromising tid st) →
  Exec.elem_of_results
    (CPState.promise_tid UMPromising tid msg st', ())
    (CPState.run_tid isem UMPromising tid
       (CPState.promise_tid UMPromising tid msg st)).
Proof.
  intros Hstable Hinit Hrun.
  destruct Hstable as [Hsame _].
  eapply (UMPromising_run_tid_promise_same_stable_from_imon
    isem term tid initmem msg st st').
  - exact Hinit.
  - exact (Hsame tid initmem msg).
  - exact Hrun.
Qed.

Lemma UMPromising_tail_stable_run_to_termination_plain_promise_same {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (msg : Msg.t) fuel ppst ppst' b :
  UMPromising_tail_stable (n:=n) isem →
  Exec.elem_of_results (ppst', b)
    (CPStateProof.run_to_termination_plain isem UMPromising term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (UMPromising_promise_ppstate tid initmem msg ppst', b)
    (CPStateProof.run_to_termination_plain isem UMPromising term
       tid initmem fuel
       (UMPromising_promise_ppstate tid initmem msg ppst)).
Proof.
  intros Hstable Hrun.
  destruct Hstable as [Hsame _].
  eapply (UMPromising_run_to_termination_plain_promise_same_stable_from_imon
    isem term tid initmem msg fuel ppst ppst' b).
  - exact (Hsame tid initmem msg).
  - exact Hrun.
Qed.

Lemma UMPromising_tail_stable_run_tid_cons_event {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (code : code_region) (msg : Msg.t) st st' :
  UMPromising_tail_stable (n:=n) isem →
  initmem = CPState.initmem st →
  Exec.elem_of_results (st', ()) (CPState.run_tid isem UMPromising tid st) →
  Exec.elem_of_results
    (CPStateProof.cons_event_state UMPromising msg st', ())
    (CPState.run_tid isem UMPromising tid
       (CPStateProof.cons_event_state UMPromising msg st)).
Proof.
  intros Hstable Hinit Hrun.
  destruct Hstable as [_ Hfuture].
  eapply (UMPromising_run_tid_cons_event_stable_from_imon
    isem term tid initmem code msg st st').
  - exact Hinit.
  - exact (Hfuture tid initmem code msg).
  - exact Hrun.
Qed.

Lemma UMPromising_tail_stable_run_to_termination_plain_cons_event {n}
    (isem : iMon ()) (term : terminationCondition n) (tid : fin n)
    (initmem : memoryMap) (code : code_region) (msg : Msg.t)
    fuel ppst ppst' b :
  UMPromising_tail_stable (n:=n) isem →
  Exec.elem_of_results (ppst', b)
    (CPStateProof.run_to_termination_plain isem UMPromising term
       tid initmem fuel ppst) →
  Exec.elem_of_results
    (CPStateProof.cons_event_ppstate UMPromising msg ppst', b)
    (CPStateProof.run_to_termination_plain isem UMPromising term
       tid initmem fuel
       (CPStateProof.cons_event_ppstate UMPromising msg ppst)).
Proof.
  intros Hstable Hrun.
  destruct Hstable as [_ Hfuture].
  eapply (UMPromising_run_to_termination_plain_cons_event_stable_from_imon
    isem term tid initmem code msg fuel ppst ppst' b).
  - exact (Hfuture tid initmem code msg).
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

Ltac inv_exec_result_until_write :=
  repeat lazymatch goal with
  | H : Exec.elem_of_results _ (write_mem _ _ _ _ _ _) |- _ =>
      fail
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

Lemma read_mem_preserves_mem addr size macc init ppst ppst' res :
  Exec.elem_of_results (ppst', res) (read_mem addr size macc init ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H.
  unfold read_mem in H.
  inv_exec_result; reflexivity.
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

Lemma memory_promise_inv msg mem mem' time :
  Exec.elem_of_results (mem', time) (Memory.promise msg mem) →
  mem' = msg :: mem ∧ time = length (msg :: mem).
Proof.
  intro H.
  unfold Memory.promise in H.
  inv_exec_result.
  split; [reflexivity|lia].
Qed.

Lemma memory_exclusive_cons_latest_old tid addr size tread msg mem :
  Memory.exclusive tid addr size tread (length (msg :: mem)) mem →
  Memory.exclusive tid addr size tread (length (msg :: mem)) (msg :: mem).
Proof.
  unfold Memory.exclusive.
  intros Hexclusive msg' Hin Hoverlap.
  cbn in Hexclusive |- *.
  change (length (msg :: mem)) with (S (length mem)) in Hin.
  replace (S (length mem) - 1)%nat with (length mem) in Hin by lia.
  replace (S (length mem) - 1)%nat with (length mem) in Hexclusive by lia.
  unfold Memory.cut_after, Memory.cut_before in Hexclusive.
  unfold Memory.cut_after, Memory.cut_before in Hin.
  replace (length mem - 0)%nat with (length mem) in Hexclusive by lia.
  rewrite PromMemoryFacts.cut_before_cons_old in Hin by lia.
  apply (Hexclusive msg').
  - exact Hin.
  - exact Hoverlap.
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
  let msg := Msg.make size tid addr data in
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
  set (msg := Msg.make size tid addr data) in *.
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
	        apply elem_of_list_singleton in Hrmw_acq.
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
	        apply elem_of_list_singleton in Hrmw_acq.
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

Lemma run_outcome_none_preserves_mem tid initmem out ppst ppst'
    (eret : eff_ret out) :
  Exec.elem_of_results (ppst', (eret, None))
    (run_outcome tid initmem out ppst) →
  PPState.mem ppst' = PPState.mem ppst.
Proof.
  intro H.
  funelim (run_outcome tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: inv_exec_result; try solve [destruct ppst; reflexivity].
  all: try solve [eapply read_mem_preserves_mem; eauto].
  all: try solve [eapply write_mem_none_preserves_mem; eauto].
  all: cbn; reflexivity.
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
  exists (Msg.make size tid addr val).
  split; [exact Hmem|].
  split; [reflexivity|].
  split; [exact Hle|].
  simp run_outcome.
  destruct (Exec.elem_of_guard_or
    (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
    (P:=addr_space = PAS_NonSecure)
    (PPState.Make
       (TState.promise
          (length (Msg.make size tid addr val :: PPState.mem ppst))
          (PPState.state ppst))
       (Msg.make size tid addr val :: PPState.mem ppst)
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
            (length (Msg.make size tid addr val :: PPState.mem ppst))
            (PPState.state ppst))
         (Msg.make size tid addr val :: PPState.mem ppst)
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
  exists (Msg.make size tid addr val).
  split; [exact Hmem|].
  split; [reflexivity|].
  split; [exact Hle|].
  simp run_outcome.
    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
      (P:=addr_space = PAS_NonSecure)
      (PPState.Make
         (TState.promise
            (length (Msg.make size tid addr val :: PPState.mem ppst))
            (PPState.state ppst))
         (Msg.make size tid addr val :: PPState.mem ppst)
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
              (length (Msg.make size tid addr val :: PPState.mem ppst))
              (PPState.state ppst))
           (Msg.make size tid addr val :: PPState.mem ppst)
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

Lemma UMPromising_replayable : PromisingProof.Replayable UMPromising.
Proof.
  constructor.
  - intros n tid0 initmem0 out ppst ppst' eret H.
    exact (run_outcome_none_preserves_mem
      tid0 initmem0 out ppst ppst' eret H).
  - intros n tid0 initmem0 out ppst ppst' eret vpre H.
    destruct (run_outcome_promise_replay_one
      tid0 initmem0 out ppst ppst' eret vpre H) as
      [event [Hmem [Htid [Hlt Hreplay]]]].
    exists [event].
    split; [discriminate|].
    split; [cbn; exact Hmem|].
    split.
    + intros event' Hevent'.
      apply elem_of_list_singleton in Hevent'.
      subst event'.
      exact Htid.
    + split; [exact Hlt|].
      unfold PromisingProof.promise_ppstate_event.
      unfold UMPromising_promise_ppstate.
      cbn.
      exact Hreplay.
Qed.

Lemma run_outcome_no_promise_non_mem_write tid initmem out :
  (∀ mr (val : bv (8 * mr.(MemReq.size)))
      (tags : bv mr.(MemReq.num_tag)),
    out ≠ MemWrite mr val tags) →
  ∀ ppst ppst' (eret : eff_ret out) vpre,
    Exec.elem_of_results (ppst', (eret, Some vpre))
      (run_outcome tid initmem out ppst) →
    False.
Proof.
  intros Hnot ppst ppst' eret vpre H.
  funelim (run_outcome tid initmem out ppst).
  all: rewrite <- Heqcall in H.
  all: try solve [exfalso; eapply Hnot; reflexivity].
  all: try solve [inv_exec_result].
Qed.

Lemma UMPromising_handle_outcome_no_promise_non_mem_write {n}
    (tid : fin n) initmem out :
  (∀ mr (val : bv (8 * mr.(MemReq.size)))
      (tags : bv mr.(MemReq.num_tag)),
    out ≠ MemWrite mr val tags) →
  CPStateProof.handle_outcome_no_promise UMPromising tid initmem out.
Proof.
  intros Hnot ppst ppst' eret vpre Hrun.
  cbn in Hrun.
  eapply run_outcome_no_promise_non_mem_write; eauto.
Qed.

Definition UMPromising_Sail_outcome_no_promise {eo A}
    (out : SI.outcome eo A) : Prop :=
  match out with
  | SI.MemWrite _ _ _ => False
  | _ => True
  end.

Fixpoint UMPromising_Sail_no_promise {eo A}
    (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      UMPromising_Sail_outcome_no_promise out ∧
      ∀ ret, UMPromising_Sail_no_promise (k ret)
  end.

Fixpoint UMPromising_Sail_at_most_one_promise {eo A}
    (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      (UMPromising_Sail_outcome_no_promise out ∧
       ∀ ret, UMPromising_Sail_at_most_one_promise (k ret)) ∨
      (∀ ret, UMPromising_Sail_no_promise (k ret))
  end.

Definition UMPromising_Sail_outcome_promised_stable tid initmem msg
    nondet {eo A} (out : SI.outcome eo A) : Prop :=
  imon_future_promise_stable_promised tid initmem msg _
    (Sail_outcome_interp nondet out).

Fixpoint UMPromising_Sail_prefix_promised_stable tid initmem msg
    nondet {eo A} (smon : SI.iMon eo A) : Prop :=
  match smon with
  | SI.Ret _ => True
  | SI.Next out k =>
      (UMPromising_Sail_outcome_no_promise out ∧
       UMPromising_Sail_outcome_promised_stable
         tid initmem msg nondet out ∧
       ∀ ret,
         UMPromising_Sail_prefix_promised_stable
           tid initmem msg nondet (k ret)) ∨
      (∀ ret, UMPromising_Sail_no_promise (k ret))
  end.

Lemma UMPromising_Sail_outcome_promised_stable_from_read_code
    tid initmem code msg nondet {eo A} (out : SI.outcome eo A) :
  UMPromising_read_code_stability tid initmem code msg →
  UMPromising_Sail_outcome_no_promise out →
  UMPromising_Sail_outcome_promised_stable
    tid initmem msg nondet out.
Proof.
  intros Hstable Hno.
  destruct out as
    [reg acc | reg acc val | rr | wr val tags | aa | opcode
    | sz pa | bar | cop | tlbi | fault | | ts | te | extra | s
    | | | ct | | message];
    cbn in Hno;
    cbn [UMPromising_Sail_outcome_promised_stable
         Sail_outcome_interp Sail_choose Sail_nochoose];
    try contradiction.
  - split.
    + apply reg_read_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply reg_write_outcome_future_promise_stable_promised.
      intros ppst.
      eapply UMPromising_read_code_control_bound.
      exact Hstable.
    + intro.
      exact I.
  - match goal with
    | rr : SI.MemReq.t |- _ =>
        destruct rr as [macc addr addr_space size nt]
    end.
    cbn [MemReq_from_sail].
    destruct nt as [|tag].
    + split.
      * eapply UMPromising_mem_read_promised_stable_from_read_code.
        exact Hstable.
      * intros [[]|abort]; exact I.
    + split.
      * apply UMPromising_mem_read_nonzero_tag_promised_stable.
      * intros [[]|abort]; exact I.
  - split.
    + apply mem_write_addr_announce_outcome_future_promise_stable_promised.
      intros ppst.
      eapply UMPromising_read_code_control_bound.
      exact Hstable.
    + intro.
      exact I.
  - exact I.
  - exact I.
  - destruct bar as [dsb|dmb|[]|[]|[]|[]].
    + split.
      * apply UMPromising_barrier_dsb_outcome_future_promise_stable_promised.
        intros ppst.
        eapply UMPromising_read_code_control_bound.
        exact Hstable.
      * intro; exact I.
    + split.
      * apply barrier_dmb_outcome_future_promise_stable_promised.
        intros ppst.
        eapply UMPromising_read_code_control_bound.
        exact Hstable.
      * intro; exact I.
    + split.
      * apply barrier_isb_outcome_future_promise_stable_promised.
        intros ppst.
        eapply UMPromising_read_code_control_bound.
        exact Hstable.
      * intro; exact I.
    + split.
      * solve_UMPromising_unsupported_promised_stable.
      * intro; exact I.
    + split.
      * solve_UMPromising_unsupported_promised_stable.
      * intro; exact I.
    + split.
      * solve_UMPromising_unsupported_promised_stable.
      * intro; exact I.
  - split.
    + apply UMPromising_cache_op_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_tlbop_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_take_exception_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_return_exception_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_translation_start_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_translation_end_outcome_future_promise_stable_promised.
    + intro.
      exact I.
  - split.
    + apply UMPromising_generic_fail_outcome_future_promise_stable_promised.
    + intros [].
  - split.
    + apply UMPromising_generic_fail_outcome_future_promise_stable_promised.
    + intros [].
  - exact I.
  - split.
    + apply UMPromising_generic_fail_outcome_future_promise_stable_promised.
    + intros [].
  - destruct nondet; destruct ct; cbn [Sail_choose Sail_nochoose].
    all: repeat match goal with
    | |- context[decide (?P)] => destruct (decide P)
    | |- context[match decide ?P with _ => _ end] => destruct (decide P)
    | |- context[if ?x then _ else _] => destruct x
    end.
    all: repeat progress (
      unfold mret, mbind, fmap, mthrow, mcall, mcallM,
        mcall_repl, MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
        iMon_throw, fMon_ret, fMon_bind, fMon_fmap, fMon_call,
        mchoosef, mchoosel, mchoose in *;
      cbn in *).
    all: repeat match goal with
    | H : Empty_set |- _ => destruct H
    | |- imon_future_promise_stable_promised _ _ _ _
           (if decide (?P) then _ else _) =>
        destruct (decide P); cbn
    | |- True => exact I
    | |- _ ∧ _ => split
    | |- ∀ _, _ => intro
    | |- outcome_future_promise_stable_promised _ _ _ (GenericFail _) =>
        apply UMPromising_generic_fail_outcome_future_promise_stable_promised
    end.
  - cbn [mdiscard mchoosel mchoose].
    repeat progress (
      unfold mret, mbind, fmap, mcall, mcallM,
        MCall_SubEff, sub_eff, SubEff_suml, SubEff_sumr,
        fMon_ret, fMon_bind, fMon_fmap, fMon_call in *;
      cbn in *).
    repeat match goal with
    | H : fin 0 |- _ => destruct H
    | |- True => exact I
    | |- ∀ _, _ => intro
    end.
  - exact I.
Qed.

Lemma UMPromising_Sail_promised_stable_from_no_promise_read_code
    tid initmem code msg nondet {eo A} (smon : SI.iMon eo A) :
  UMPromising_read_code_stability tid initmem code msg →
  UMPromising_Sail_no_promise smon →
  UMPromising_Sail_promised_stable tid initmem msg nondet smon.
Proof.
  induction smon as [a|T out k IH]; intros Hstable Hno.
  - exact I.
  - cbn in Hno |- *.
    destruct Hno as [Hout_no Htail_no].
    split.
    + apply UMPromising_Sail_outcome_promised_stable_from_read_code
        with (code := code).
      * exact Hstable.
      * exact Hout_no.
    + intro ret.
      apply IH.
      * exact Hstable.
      * apply Htail_no.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_from_no_promise {eo A}
    (smon : SI.iMon eo A) :
  UMPromising_Sail_no_promise smon →
  UMPromising_Sail_at_most_one_promise smon.
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

Lemma UMPromising_Sail_no_promise_bind {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_no_promise mon →
  (∀ a, UMPromising_Sail_no_promise (k a)) →
  UMPromising_Sail_no_promise (SI.iMon_bind mon k).
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

Lemma UMPromising_Sail_at_most_one_promise_bind_no_left {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_no_promise mon →
  (∀ a, UMPromising_Sail_at_most_one_promise (k a)) →
  UMPromising_Sail_at_most_one_promise (SI.iMon_bind mon k).
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

Lemma UMPromising_Sail_at_most_one_promise_bind_no_right {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_at_most_one_promise mon →
  (∀ a, UMPromising_Sail_no_promise (k a)) →
  UMPromising_Sail_at_most_one_promise (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hat_most Hk.
  - cbn.
    apply UMPromising_Sail_at_most_one_promise_from_no_promise.
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
      apply UMPromising_Sail_no_promise_bind.
      * apply Htail_no.
      * exact Hk.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_from_no_promise
    tid initmem msg nondet {eo A} (smon : SI.iMon eo A) :
  UMPromising_Sail_no_promise smon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet smon.
Proof.
  induction smon as [a|T out k IH]; intro Hno.
  - exact I.
  - cbn in Hno |- *.
    destruct Hno as [_ Htail_no].
    right.
    exact Htail_no.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_from_at_most_one_read_code
    tid initmem code msg nondet {eo A} (smon : SI.iMon eo A) :
  UMPromising_read_code_stability tid initmem code msg →
  UMPromising_Sail_at_most_one_promise smon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet smon.
Proof.
  intros Hstable Hat_most.
  induction smon as [a|T out k IH].
  - exact I.
  - cbn in Hat_most |- *.
    destruct Hat_most as [[Hout_no Htail_at_most]|Htail_no].
    + left.
      split.
      * exact Hout_no.
      * split.
        -- eapply UMPromising_Sail_outcome_promised_stable_from_read_code;
             eassumption.
        -- intro ret.
           apply IH.
           apply Htail_at_most.
    + right.
      exact Htail_no.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_bind_no_left
    tid initmem msg nondet {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable
    tid initmem msg nondet mon →
  (∀ a,
    UMPromising_Sail_prefix_promised_stable
      tid initmem msg nondet (k a)) →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (SI.iMon_bind mon k).
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

Lemma UMPromising_Sail_prefix_promised_stable_bind_no_right
    tid initmem msg nondet {eo A B}
    (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet mon →
  (∀ a, UMPromising_Sail_no_promise (k a)) →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (SI.iMon_bind mon k).
Proof.
  revert B k.
  induction mon as [a|T out kmon IH]; intros B k Hstable Hk.
  - cbn.
    apply UMPromising_Sail_prefix_promised_stable_from_no_promise.
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
      apply UMPromising_Sail_no_promise_bind.
      * apply Htail_no.
      * exact Hk.
Qed.

Lemma UMPromising_Sail_no_promise_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  UMPromising_Sail_no_promise mon →
  (∀ e, UMPromising_Sail_no_promise (h e)) →
  UMPromising_Sail_no_promise (System_types.Defs.try_catch mon h).
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

Lemma UMPromising_Sail_at_most_one_promise_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  UMPromising_Sail_at_most_one_promise mon →
  (∀ e, UMPromising_Sail_no_promise (h e)) →
  UMPromising_Sail_at_most_one_promise
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
            apply UMPromising_Sail_no_promise_try_catch;
            [apply Htail_no|exact Hh]]).
    apply UMPromising_Sail_at_most_one_promise_from_no_promise.
    apply Hh.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_try_catch_no_left
    tid initmem msg nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable tid initmem msg nondet mon →
  (∀ e, UMPromising_Sail_no_promise (h e)) →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.try_catch mon h).
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
    all: apply UMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply Hh.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_try_catch_no_right
    tid initmem msg nondet {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  UMPromising_Sail_prefix_promised_stable tid initmem msg nondet mon →
  (∀ e, UMPromising_Sail_no_promise (h e)) →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.try_catch mon h).
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
          apply UMPromising_Sail_no_promise_try_catch;
          [apply Htail_no|exact Hh]]).
    all: apply UMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply Hh.
Qed.

Lemma UMPromising_Sail_no_promise_returnm {A E}
    (a : A) :
  UMPromising_Sail_no_promise (System_types.Defs.returnm (E:=E) a).
Proof. exact I. Qed.

Lemma UMPromising_Sail_no_promise_fail {A E} msg :
  UMPromising_Sail_no_promise (System_types.Defs.fail (A:=A) (E:=E) msg).
Proof.
  cbn [System_types.Defs.fail].
  split; [exact I|].
  intros [].
Qed.

Lemma UMPromising_Sail_no_promise_throw {A E} (e : E) :
  UMPromising_Sail_no_promise (System_types.Defs.throw (A:=A) e).
Proof.
  cbn [System_types.Defs.throw].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_exit {A E} :
  UMPromising_Sail_no_promise
    (System_types.Defs.exit (A:=A) (E:=E) tt).
Proof.
  cbn [System_types.Defs.exit].
  apply UMPromising_Sail_no_promise_fail.
Qed.

Lemma UMPromising_Sail_no_promise_liftR {A R E}
    (mon : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_no_promise (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.liftR].
  eapply UMPromising_Sail_no_promise_try_catch.
  - exact Hmon.
  - intro.
    apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_liftR {A R E}
    (mon : System_types.Defs.monad E A) :
  UMPromising_Sail_at_most_one_promise mon →
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.liftR].
  eapply UMPromising_Sail_at_most_one_promise_try_catch.
  - exact Hmon.
  - intro.
    apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_liftR_no_left
    tid initmem msg nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.liftR (R:=R) mon).
Proof.
  intros Hno Hstable.
  cbn [System_types.Defs.liftR].
  eapply UMPromising_Sail_prefix_promised_stable_try_catch_no_left.
  - exact Hno.
  - exact Hstable.
  - intro.
    apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_liftR_no_right
    tid initmem msg nondet {A R E}
    (mon : System_types.Defs.monad E A) :
  UMPromising_Sail_prefix_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.liftR (R:=R) mon).
Proof.
  intro Hstable.
  cbn [System_types.Defs.liftR].
  eapply UMPromising_Sail_prefix_promised_stable_try_catch_no_right.
  - exact Hstable.
  - intro.
    apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_no_promise_catch_early_return {A E}
    (mon : System_types.Defs.monadR A E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_no_promise
    (System_types.Defs.catch_early_return mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.catch_early_return].
  eapply UMPromising_Sail_no_promise_try_catch.
  - exact Hmon.
  - intros [a|e].
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_catch_early_return {A E}
    (mon : System_types.Defs.monadR A E A) :
  UMPromising_Sail_at_most_one_promise mon →
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.catch_early_return mon).
Proof.
  intro Hmon.
  cbn [System_types.Defs.catch_early_return].
  eapply UMPromising_Sail_at_most_one_promise_try_catch.
  - exact Hmon.
  - intros [a|e].
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_catch_early_return_no_right
    tid initmem msg nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  UMPromising_Sail_prefix_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.catch_early_return mon).
Proof.
  intro Hstable.
  cbn [System_types.Defs.catch_early_return].
  eapply UMPromising_Sail_prefix_promised_stable_try_catch_no_right.
  - exact Hstable.
  - intros [a|e].
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_catch_early_return_no_left
    tid initmem msg nondet {A E}
    (mon : System_types.Defs.monadR A E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.catch_early_return mon).
Proof.
  intros Hno Hstable.
  cbn [System_types.Defs.catch_early_return].
  eapply UMPromising_Sail_prefix_promised_stable_try_catch_no_left.
  - exact Hno.
  - exact Hstable.
  - intros [a|e].
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_throw.
Qed.

Lemma UMPromising_Sail_no_promise_bind0 {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_no_promise tail →
  UMPromising_Sail_no_promise (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  apply UMPromising_Sail_no_promise_bind.
  - exact Hmon.
  - intro.
    exact Htail.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_bind0_no_left {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_at_most_one_promise tail →
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply UMPromising_Sail_at_most_one_promise_bind_no_left.
  - exact Hmon.
  - intro.
    exact Htail.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_bind0_no_left
    tid initmem msg nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  UMPromising_Sail_no_promise mon →
  UMPromising_Sail_promised_stable tid initmem msg nondet mon →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet tail →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon_no Hmon_stable Htail.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
  - exact Hmon_no.
  - exact Hmon_stable.
  - intro.
    exact Htail.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_bind0_no_right
    tid initmem msg nondet {A E}
    (mon : System_types.Defs.monad E unit)
    (tail : System_types.Defs.monad E A) :
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet mon →
  UMPromising_Sail_no_promise tail →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System_types.Defs.bind0 mon tail).
Proof.
  intros Hmon Htail_no.
  cbn [System_types.Defs.bind0 System_types.Defs.bind].
  eapply UMPromising_Sail_prefix_promised_stable_bind_no_right.
  - exact Hmon.
  - intro.
    exact Htail_no.
Qed.

Lemma UMPromising_Sail_no_promise_read_reg {E}
    (reg : System_types.Arch.reg) :
  UMPromising_Sail_no_promise
    (System_types.Defs.read_reg (e:=E) reg).
Proof.
  cbn [System_types.Defs.read_reg].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_write_reg {E}
    (reg : System_types.Arch.reg) (v : System_types.Arch.reg_type reg) :
  UMPromising_Sail_no_promise
    (System_types.Defs.write_reg (e:=E) reg v).
Proof.
  cbn [System_types.Defs.write_reg].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_read_reg_ref {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.read_reg_ref (e:=E) ref).
Proof.
  cbn [System_types.Defs.read_reg_ref].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_reg_deref {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.reg_deref (e:=E) ref).
Proof.
  cbn [System_types.Defs.reg_deref].
  apply UMPromising_Sail_no_promise_read_reg_ref.
Qed.

Lemma UMPromising_Sail_no_promise_write_reg_ref {A E}
    (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) (v : A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.write_reg_ref (e:=E) ref v).
Proof.
  cbn [System_types.Defs.write_reg_ref].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_sys_reg_read {A E}
    id (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_sys_reg_read (e:=E) id ref).
Proof.
  cbn [System_types.Defs.sail_sys_reg_read].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_sys_reg_write {A E}
    id (ref : @Values.register_ref System_types.Arch.reg System_types.Arch.reg_type A) (v : A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_sys_reg_write (e:=E) id ref v).
Proof.
  cbn [System_types.Defs.sail_sys_reg_write].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_mem_read {E n nt}
    req :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_mem_read (e:=E) (n:=n) (nt:=nt) req).
Proof.
  cbn [System_types.Defs.sail_mem_read].
  split; [exact I|].
  intros [[data tags]|abort].
  all: exact I.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_sail_mem_write {E n nt}
    req value tags :
  UMPromising_Sail_at_most_one_promise
    (System_types.Defs.sail_mem_write
       (e:=E) (n:=n) (nt:=nt) req value tags).
Proof.
  cbn [System_types.Defs.sail_mem_write].
  right.
  intros [[]|abort].
  all: exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_barrier {E} b :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_barrier (e:=E) b).
Proof.
  cbn [System_types.Defs.sail_barrier].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_translation_start {E} ts :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_translation_start (e:=E) ts).
Proof.
  cbn [System_types.Defs.sail_translation_start].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_translation_end {E} te :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_translation_end (e:=E) te).
Proof.
  cbn [System_types.Defs.sail_translation_end].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_take_exception {E} exn :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_take_exception (e:=E) exn).
Proof.
  cbn [System_types.Defs.sail_take_exception].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_sail_tlbi {E} tlbi :
  UMPromising_Sail_no_promise
    (System_types.Defs.sail_tlbi (e:=E) tlbi).
Proof.
  cbn [System_types.Defs.sail_tlbi].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_choose_range {E} descr lo hi :
  UMPromising_Sail_no_promise
    (System_types.Defs.choose_range (E:=E) descr lo hi).
Proof.
  cbn [System_types.Defs.choose_range].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_choose_bool {E} descr :
  UMPromising_Sail_no_promise
    (System_types.Defs.choose_bool (E:=E) descr).
Proof.
  cbn [System_types.Defs.choose_bool].
  split; [exact I|].
  intro.
  exact I.
Qed.

Lemma UMPromising_Sail_no_promise_undefined_bool {E} u :
  UMPromising_Sail_no_promise
    (System_types.Defs.undefined_bool (E:=E) u).
Proof.
  cbn [System_types.Defs.undefined_bool].
  apply UMPromising_Sail_no_promise_choose_bool.
Qed.

Lemma UMPromising_Sail_no_promise_choose_from_list {A E} descr
    (xs : list A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.choose_from_list (E:=E) descr xs).
Proof.
  cbn [System_types.Defs.choose_from_list System_types.Defs.bind].
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_choose_range.
  - intro idx.
    destruct (nth_error xs (Z.to_nat idx)).
    + apply UMPromising_Sail_no_promise_returnm.
    + apply UMPromising_Sail_no_promise_fail.
Qed.

Lemma UMPromising_Sail_no_promise_internal_pick {A E}
    (xs : list A) :
  UMPromising_Sail_no_promise
    (System_types.Defs.internal_pick (e:=E) xs).
Proof.
  cbn [System_types.Defs.internal_pick].
  apply UMPromising_Sail_no_promise_choose_from_list.
Qed.

Lemma UMPromising_Sail_no_promise_foreach_ZM_up' {E Vars}
    from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, UMPromising_Sail_no_promise (body z vars)) →
  UMPromising_Sail_no_promise
    (System_types.Defs.foreach_ZM_up' from to step fuel vars body).
Proof.
  revert from vars.
  induction fuel as [|fuel IH]; intros from vars Hbody.
  - cbn [System_types.Defs.foreach_ZM_up'].
    destruct (from <=? to); apply UMPromising_Sail_no_promise_returnm.
  - cbn [System_types.Defs.foreach_ZM_up'].
    destruct (from <=? to).
    + cbn [System_types.Defs.bind].
      apply UMPromising_Sail_no_promise_bind.
      * apply Hbody.
      * intro vars'.
        apply IH.
        apply Hbody.
    + apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_foreach_ZM_up {E Vars}
    from to step (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, UMPromising_Sail_no_promise (body z vars)) →
  UMPromising_Sail_no_promise
    (System_types.Defs.foreach_ZM_up from to step vars body).
Proof.
  cbn [System_types.Defs.foreach_ZM_up].
  apply UMPromising_Sail_no_promise_foreach_ZM_up'.
Qed.

Ltac UMPromising_Sail_simpl :=
	  cbn [System_types.Defs.returnm System_types.Defs.fail
	       System_types.Defs.throw System_types.Defs.exit
	       System_types.Defs.early_return
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
	       System_types.Defs.autocast_m
	       System_types.returnM System_types.returnR
	       System_types.Defs.returnR] in *;
  unfold System_types.returnM, System_types.returnR,
    System_types.Defs.returnR, System_types.Defs.early_return,
    System_types.Defs.autocast_m, System.fail in *;
  unfold System_types.Defs.bind, System_types.Defs.bind0 in *.

Ltac solve_UMPromising_Sail_no_promise :=
  lazymatch goal with
	  | |- True => exact I
	  | |- UMPromising_Sail_no_promise
	        (System_types.Interface.Ret _) =>
	      exact I
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.returnR _ _) =>
	      exact I
	  | |- UMPromising_Sail_no_promise
	        (Defs.returnR _ _) =>
	      exact I
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.assert_exp' ?b _) =>
	      destruct b;
	      [apply UMPromising_Sail_no_promise_returnm
	      |apply UMPromising_Sail_no_promise_fail]
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.assert_exp ?b _) =>
	      destruct b;
	      [apply UMPromising_Sail_no_promise_returnm
	      |apply UMPromising_Sail_no_promise_fail]
	  | |- _ ∧ _ =>
	      split; solve_UMPromising_Sail_no_promise
	  | |- ∀ _, _ =>
	      intro; solve_UMPromising_Sail_no_promise
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.bind _ _) =>
	      unfold System_types.Defs.bind;
	      eapply UMPromising_Sail_no_promise_bind;
	      [solve_UMPromising_Sail_no_promise
	      |intro; solve_UMPromising_Sail_no_promise]
	  | |- UMPromising_Sail_no_promise
	        (Defs.bind _ _) =>
	      unfold Defs.bind;
	      eapply UMPromising_Sail_no_promise_bind;
	      [solve_UMPromising_Sail_no_promise
	      |intro; solve_UMPromising_Sail_no_promise]
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.bind0 _ _) =>
	      eapply UMPromising_Sail_no_promise_bind0;
	      [solve_UMPromising_Sail_no_promise
	      |solve_UMPromising_Sail_no_promise]
	  | |- UMPromising_Sail_no_promise
	        (Defs.bind0 _ _) =>
	      unfold Defs.bind0;
	      eapply UMPromising_Sail_no_promise_bind0;
	      [solve_UMPromising_Sail_no_promise
	      |solve_UMPromising_Sail_no_promise]
	  | |- UMPromising_Sail_no_promise
	        (System_types.Interface.iMon_bind _ _) =>
	      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise
      |intro; solve_UMPromising_Sail_no_promise]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.try_catch _ _) =>
      eapply UMPromising_Sail_no_promise_try_catch;
      [solve_UMPromising_Sail_no_promise
      |intro; solve_UMPromising_Sail_no_promise]
  | |- UMPromising_Sail_no_promise
        (Defs.try_catch _ _) =>
      eapply UMPromising_Sail_no_promise_try_catch;
      [solve_UMPromising_Sail_no_promise
      |intro; solve_UMPromising_Sail_no_promise]
  | |- UMPromising_Sail_no_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (@Defs.liftR ?A ?R ?E ?mon) =>
      change (UMPromising_Sail_no_promise
        (@System_types.Defs.liftR A R E mon));
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (Defs.catch_early_return _) =>
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.returnm _) =>
      apply UMPromising_Sail_no_promise_returnm
  | |- UMPromising_Sail_no_promise
        (Defs.returnm _) =>
      apply UMPromising_Sail_no_promise_returnm
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.fail _) =>
      apply UMPromising_Sail_no_promise_fail
  | |- UMPromising_Sail_no_promise
        (Defs.fail _) =>
      apply UMPromising_Sail_no_promise_fail
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.throw _) =>
      apply UMPromising_Sail_no_promise_throw
  | |- UMPromising_Sail_no_promise
        (Defs.throw _) =>
      apply UMPromising_Sail_no_promise_throw
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.exit _) =>
      apply UMPromising_Sail_no_promise_exit
  | |- UMPromising_Sail_no_promise
        (Defs.exit _) =>
      apply UMPromising_Sail_no_promise_exit
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.read_reg _) =>
      apply UMPromising_Sail_no_promise_read_reg
  | |- UMPromising_Sail_no_promise
        (Defs.read_reg _) =>
      apply UMPromising_Sail_no_promise_read_reg
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.write_reg _ _) =>
      apply UMPromising_Sail_no_promise_write_reg
  | |- UMPromising_Sail_no_promise
        (Defs.write_reg _ _) =>
      apply UMPromising_Sail_no_promise_write_reg
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.early_return _) =>
      unfold System_types.Defs.early_return;
      solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (Defs.early_return _) =>
      unfold Defs.early_return;
      solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.read_reg_ref _) =>
      apply UMPromising_Sail_no_promise_read_reg_ref
  | |- UMPromising_Sail_no_promise
        (Defs.read_reg_ref _) =>
      apply UMPromising_Sail_no_promise_read_reg_ref
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.reg_deref _) =>
      apply UMPromising_Sail_no_promise_reg_deref
  | |- UMPromising_Sail_no_promise
        (Defs.reg_deref _) =>
      apply UMPromising_Sail_no_promise_reg_deref
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.write_reg_ref _ _) =>
      apply UMPromising_Sail_no_promise_write_reg_ref
  | |- UMPromising_Sail_no_promise
        (Defs.write_reg_ref _ _) =>
      apply UMPromising_Sail_no_promise_write_reg_ref
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_sys_reg_read _ _) =>
      apply UMPromising_Sail_no_promise_sail_sys_reg_read
  | |- UMPromising_Sail_no_promise
        (Defs.sail_sys_reg_read _ _) =>
      apply UMPromising_Sail_no_promise_sail_sys_reg_read
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_sys_reg_write _ _ _) =>
      apply UMPromising_Sail_no_promise_sail_sys_reg_write
  | |- UMPromising_Sail_no_promise
        (Defs.sail_sys_reg_write _ _ _) =>
      apply UMPromising_Sail_no_promise_sail_sys_reg_write
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_mem_read _) =>
      apply UMPromising_Sail_no_promise_sail_mem_read
  | |- UMPromising_Sail_no_promise
        (Defs.sail_mem_read _) =>
      apply UMPromising_Sail_no_promise_sail_mem_read
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_barrier _) =>
      apply UMPromising_Sail_no_promise_sail_barrier
  | |- UMPromising_Sail_no_promise
        (Defs.sail_barrier _) =>
      apply UMPromising_Sail_no_promise_sail_barrier
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_translation_start _) =>
      apply UMPromising_Sail_no_promise_sail_translation_start
  | |- UMPromising_Sail_no_promise
        (Defs.sail_translation_start _) =>
      apply UMPromising_Sail_no_promise_sail_translation_start
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.sail_translation_end _) =>
      apply UMPromising_Sail_no_promise_sail_translation_end
  | |- UMPromising_Sail_no_promise
        (Defs.sail_translation_end _) =>
      apply UMPromising_Sail_no_promise_sail_translation_end
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.sail_take_exception _) =>
	      apply UMPromising_Sail_no_promise_sail_take_exception
	  | |- UMPromising_Sail_no_promise
	        (Defs.sail_take_exception _) =>
	      apply UMPromising_Sail_no_promise_sail_take_exception
	  | |- UMPromising_Sail_no_promise
	        (System_types.Defs.sail_tlbi _) =>
	      apply UMPromising_Sail_no_promise_sail_tlbi
	  | |- UMPromising_Sail_no_promise
	        (Defs.sail_tlbi _) =>
	      apply UMPromising_Sail_no_promise_sail_tlbi
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.choose_range _ _ _) =>
      apply UMPromising_Sail_no_promise_choose_range
  | |- UMPromising_Sail_no_promise
        (Defs.choose_range _ _ _) =>
      apply UMPromising_Sail_no_promise_choose_range
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.choose_bool _) =>
      apply UMPromising_Sail_no_promise_choose_bool
  | |- UMPromising_Sail_no_promise
        (Defs.choose_bool _) =>
      apply UMPromising_Sail_no_promise_choose_bool
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.undefined_bool _) =>
      apply UMPromising_Sail_no_promise_undefined_bool
  | |- UMPromising_Sail_no_promise
        (Defs.undefined_bool _) =>
      apply UMPromising_Sail_no_promise_undefined_bool
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.choose_from_list _ _) =>
      apply UMPromising_Sail_no_promise_choose_from_list
  | |- UMPromising_Sail_no_promise
        (Defs.choose_from_list _ _) =>
      apply UMPromising_Sail_no_promise_choose_from_list
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.internal_pick _) =>
      apply UMPromising_Sail_no_promise_internal_pick
  | |- UMPromising_Sail_no_promise
        (Defs.internal_pick _) =>
      apply UMPromising_Sail_no_promise_internal_pick
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.foreach_ZM_up _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_foreach_ZM_up;
      intros; solve_UMPromising_Sail_no_promise
  | |- UMPromising_Sail_no_promise
        (Defs.foreach_ZM_up _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_foreach_ZM_up;
      intros; solve_UMPromising_Sail_no_promise
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_no_promise
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_no_promise
	  | |- UMPromising_Sail_no_promise _ =>
	      progress UMPromising_Sail_simpl;
	      solve_UMPromising_Sail_no_promise
	  end.

Ltac solve_UMPromising_Sail_at_most_one_promise :=
	  lazymatch goal with
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Interface.Ret _) =>
	      exact I
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Defs.returnR _ _) =>
	      exact I
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Defs.bind _ _) =>
	      unfold System_types.Defs.bind;
	      first
	        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
	         [solve_UMPromising_Sail_no_promise
	         |intro; solve_UMPromising_Sail_at_most_one_promise]
	        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
	         [solve_UMPromising_Sail_at_most_one_promise
	         |intro; solve_UMPromising_Sail_no_promise]]
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Defs.bind0 _ _) =>
	      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
	      [solve_UMPromising_Sail_no_promise
	      |solve_UMPromising_Sail_at_most_one_promise]
	  | |- UMPromising_Sail_at_most_one_promise
	        (System_types.Interface.iMon_bind _ _) =>
	      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise
         |intro; solve_UMPromising_Sail_at_most_one_promise]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise
         |intro; solve_UMPromising_Sail_no_promise]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.try_catch _ _) =>
      eapply UMPromising_Sail_at_most_one_promise_try_catch;
      [solve_UMPromising_Sail_at_most_one_promise
      |intro; solve_UMPromising_Sail_no_promise]
  | |- UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise
  | |- UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.sail_mem_write _ _ _) =>
      apply UMPromising_Sail_at_most_one_promise_sail_mem_write
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise
  | |- UMPromising_Sail_at_most_one_promise _ =>
      first
        [progress UMPromising_Sail_simpl;
         solve_UMPromising_Sail_at_most_one_promise
        |apply UMPromising_Sail_at_most_one_promise_from_no_promise;
         solve_UMPromising_Sail_no_promise]
  end.

Lemma UMPromising_Sail_no_promise_create_writeAccessDescriptor
    release exclusive :
  UMPromising_Sail_no_promise
    (System.create_writeAccessDescriptor release exclusive).
Proof.
  unfold System.create_writeAccessDescriptor, System_types.Defs.bind.
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_read_reg.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_create_readAccessDescriptor
    acquire rcpc exclusive :
  UMPromising_Sail_no_promise
    (System.create_readAccessDescriptor acquire rcpc exclusive).
Proof.
  unfold System.create_readAccessDescriptor, System_types.Defs.bind.
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_read_reg.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_create_RMWAccessDescriptor
    modop acquire release :
  UMPromising_Sail_no_promise
    (System.create_RMWAccessDescriptor modop acquire release).
Proof.
  unfold System.create_RMWAccessDescriptor, System_types.Defs.bind.
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_read_reg.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_create_iFetchAccessDescriptor :
  UMPromising_Sail_no_promise
    (System.create_iFetchAccessDescriptor tt).
Proof.
  unfold System.create_iFetchAccessDescriptor, System_types.Defs.bind.
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_read_reg.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_rX n :
  UMPromising_Sail_no_promise (System.rX n).
Proof.
  unfold System.rX.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_wX n value :
  UMPromising_Sail_no_promise (System.wX n value).
Proof.
  unfold System.wX.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_rPC :
  UMPromising_Sail_no_promise (System.rPC tt).
Proof.
  unfold System.rPC.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_wPC pc :
  UMPromising_Sail_no_promise (System.wPC pc).
Proof.
  unfold System.wPC.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_read_memory N addr accdesc :
  UMPromising_Sail_no_promise (System.read_memory N addr accdesc).
Proof.
  unfold System.read_memory.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_iFetch addr accdesc :
  UMPromising_Sail_no_promise (System.iFetch addr accdesc).
Proof.
  unfold System.iFetch.
  apply UMPromising_Sail_no_promise_read_memory.
Qed.

Lemma UMPromising_Sail_no_promise_rMem N addr accdesc :
  UMPromising_Sail_no_promise (System.rMem N addr accdesc).
Proof.
  unfold System.rMem.
  apply UMPromising_Sail_no_promise_read_memory.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_wMem N addr value accdesc :
  UMPromising_Sail_at_most_one_promise
    (System.wMem N addr value accdesc).
Proof.
  unfold System.wMem.
  solve_UMPromising_Sail_at_most_one_promise.
Qed.

Lemma UMPromising_Sail_no_promise_dataMemoryBarrier domain types :
  UMPromising_Sail_no_promise (System.dataMemoryBarrier domain types).
Proof.
  unfold System.dataMemoryBarrier.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_dataSynchronizationBarrer
    domain types :
  UMPromising_Sail_no_promise
    (System.dataSynchronizationBarrer domain types).
Proof.
  unfold System.dataSynchronizationBarrer.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_instructionSynchronizationBarrier :
  UMPromising_Sail_no_promise (System.instructionSynchronizationBarrier tt).
Proof.
  unfold System.instructionSynchronizationBarrier.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_reportTLBI
    op shareability addr asid vmid :
  UMPromising_Sail_no_promise
    (System.reportTLBI op shareability addr asid vmid).
Proof.
  unfold System.reportTLBI.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_rXS n size :
  UMPromising_Sail_no_promise (System.rXS n size).
Proof.
  unfold System.rXS.
  apply UMPromising_Sail_no_promise_bind.
  - apply UMPromising_Sail_no_promise_rX.
  - intro.
    apply UMPromising_Sail_no_promise_returnm.
Qed.

Lemma UMPromising_Sail_no_promise_wXS n size value :
  UMPromising_Sail_no_promise (System.wXS n size value).
Proof.
  unfold System.wXS.
  apply UMPromising_Sail_no_promise_wX.
Qed.

Lemma UMPromising_Sail_no_promise_get_translation_base_address varange :
  UMPromising_Sail_no_promise
    (System.get_translation_base_address varange).
Proof.
  unfold System.get_translation_base_address.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_ASID_read :
  UMPromising_Sail_no_promise (System.ASID_read tt).
Proof.
  unfold System.ASID_read.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_create_AccessDescriptorTTW
    toplevel varange :
  UMPromising_Sail_no_promise
    (System.create_AccessDescriptorTTW toplevel varange).
Proof.
  unfold System.create_AccessDescriptorTTW.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_pgt_walk va accdesc :
  UMPromising_Sail_no_promise (System.pgt_walk va accdesc).
Proof.
  unfold System.pgt_walk, System.get_translation_base_address,
    System.create_AccessDescriptorTTW, System.read_memory.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_take_exception target_el fault :
  UMPromising_Sail_no_promise
    (System.take_exception target_el fault).
Proof.
  unfold System.take_exception.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_handle_fault addrdesc :
  UMPromising_Sail_no_promise (System.handle_fault addrdesc).
Proof.
  unfold System.handle_fault, System.take_exception.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_lookup_sys_reg sys_reg_id :
  UMPromising_Sail_no_promise (System.lookup_sys_reg sys_reg_id).
Proof.
  unfold System.lookup_sys_reg, System.lookup_sys_reg64, System.fail.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_read_sys_reg_accessor
    sys_reg_id accessor :
  UMPromising_Sail_no_promise
    (System.read_sys_reg_accessor sys_reg_id accessor).
Proof.
  destruct accessor;
    unfold System.read_sys_reg_accessor, System.lookup_sys_reg64,
      System.fail;
    solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_write_sys_reg_accessor
    sys_reg_id accessor value :
  UMPromising_Sail_no_promise
    (System.write_sys_reg_accessor sys_reg_id accessor value).
Proof.
  destruct accessor;
    unfold System.write_sys_reg_accessor, System.lookup_sys_reg64,
      System.fail;
    solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_condition_holds cond :
  UMPromising_Sail_no_promise (System.condition_holds cond).
Proof.
  unfold System.condition_holds, System.rN, System.rZ, System.rC, System.rV,
    System_types.Defs.and_boolM, System_types.Defs.or_boolM.
  destruct cond; solve_UMPromising_Sail_no_promise.
Qed.

Ltac solve_UMPromising_Sail_no_promise_addr :=
  lazymatch goal with
  | |- UMPromising_Sail_no_promise
        (System.get_translation_base_address _) =>
      apply UMPromising_Sail_no_promise_get_translation_base_address
  | |- UMPromising_Sail_no_promise (System.ASID_read _) =>
      apply UMPromising_Sail_no_promise_ASID_read
  | |- UMPromising_Sail_no_promise
        (System.create_AccessDescriptorTTW _ _) =>
      apply UMPromising_Sail_no_promise_create_AccessDescriptorTTW
  | |- UMPromising_Sail_no_promise (System.pgt_walk _ _) =>
      apply UMPromising_Sail_no_promise_pgt_walk
  | |- UMPromising_Sail_no_promise (System.take_exception _ _) =>
      apply UMPromising_Sail_no_promise_take_exception
  | |- UMPromising_Sail_no_promise (System.handle_fault _) =>
      apply UMPromising_Sail_no_promise_handle_fault
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_addr
      |intro; solve_UMPromising_Sail_no_promise_addr]
  | |- UMPromising_Sail_no_promise
        (System_types.Interface.iMon_bind _ _) =>
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_addr
      |intro; solve_UMPromising_Sail_no_promise_addr]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_no_promise_bind0;
      [solve_UMPromising_Sail_no_promise_addr
      |solve_UMPromising_Sail_no_promise_addr]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.try_catch _ _) =>
      eapply UMPromising_Sail_no_promise_try_catch;
      [solve_UMPromising_Sail_no_promise_addr
      |intro; solve_UMPromising_Sail_no_promise_addr]
  | |- UMPromising_Sail_no_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise_addr
  | |- UMPromising_Sail_no_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise_addr
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_no_promise_addr
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_no_promise_addr
  | _ => solve_UMPromising_Sail_no_promise
  end.

Lemma UMPromising_Sail_no_promise_translate_address va accdesc :
  UMPromising_Sail_no_promise (System.translate_address va accdesc).
Proof.
  unfold System.translate_address.
  solve_UMPromising_Sail_no_promise_addr.
Qed.

Lemma UMPromising_Sail_no_promise_decode_bitmask N imms immr immediate :
  UMPromising_Sail_no_promise
    (System.decode_bitmask N imms immr immediate).
Proof.
  unfold System.decode_bitmask.
  solve_UMPromising_Sail_no_promise.
Qed.

Lemma UMPromising_Sail_no_promise_decode v :
  UMPromising_Sail_no_promise (System.decode v).
Proof.
  unfold System.decode, System.decodeLoadStoreRegister,
    System.decodeLoadStoreImmediate, System.decodeAddSubExt,
    System.decodeAddSubImm, System.decodeAddSubShift,
    System.decodeCompareAndBranch, System.decodeTestAndBranch,
    System.decodeDataBarrier, System.decodeTLBI,
    System.decodeSystemRegisterMove,
    System.decode_bitwise_op, System.decode_bitmask,
    System.fail.
  solve_UMPromising_Sail_no_promise.
Qed.

Ltac solve_UMPromising_Sail_no_promise_exec :=
  lazymatch goal with
  | |- UMPromising_Sail_no_promise (System.rX _) =>
      apply UMPromising_Sail_no_promise_rX
  | |- UMPromising_Sail_no_promise (System.wX _ _) =>
      apply UMPromising_Sail_no_promise_wX
  | |- UMPromising_Sail_no_promise (System.rSP _) =>
      unfold System.rSP; solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise (System.wSP _) =>
      unfold System.wSP; solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise (System.rSPS _) =>
      unfold System.rSPS; solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise (System.wSPS _ _) =>
      unfold System.wSPS; solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise (System.rXS _ _) =>
      apply UMPromising_Sail_no_promise_rXS
  | |- UMPromising_Sail_no_promise (System.wXS _ _ _) =>
      apply UMPromising_Sail_no_promise_wXS
  | |- UMPromising_Sail_no_promise (System.eval_operand _ _) =>
      unfold System.eval_operand, System.shift_reg;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise (System.shift_reg _ _ _) =>
      unfold System.shift_reg; solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise
        (System.check_load_store_alignment _ _) =>
      unfold System.check_load_store_alignment;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise (System.rPC _) =>
      apply UMPromising_Sail_no_promise_rPC
  | |- UMPromising_Sail_no_promise (System.wPC _) =>
      apply UMPromising_Sail_no_promise_wPC
  | |- UMPromising_Sail_no_promise
        (System.create_writeAccessDescriptor _ _) =>
      apply UMPromising_Sail_no_promise_create_writeAccessDescriptor
  | |- UMPromising_Sail_no_promise
        (System.create_readAccessDescriptor _ _ _) =>
      apply UMPromising_Sail_no_promise_create_readAccessDescriptor
  | |- UMPromising_Sail_no_promise
        (System.create_RMWAccessDescriptor _ _ _) =>
      apply UMPromising_Sail_no_promise_create_RMWAccessDescriptor
  | |- UMPromising_Sail_no_promise
        (System.create_iFetchAccessDescriptor _) =>
      apply UMPromising_Sail_no_promise_create_iFetchAccessDescriptor
  | |- UMPromising_Sail_no_promise (System.read_memory _ _ _) =>
      apply UMPromising_Sail_no_promise_read_memory
  | |- UMPromising_Sail_no_promise (System.iFetch _ _) =>
      apply UMPromising_Sail_no_promise_iFetch
  | |- UMPromising_Sail_no_promise (System.rMem _ _ _) =>
      apply UMPromising_Sail_no_promise_rMem
  | |- UMPromising_Sail_no_promise (System.dataMemoryBarrier _ _) =>
      apply UMPromising_Sail_no_promise_dataMemoryBarrier
  | |- UMPromising_Sail_no_promise
        (System.dataSynchronizationBarrer _ _) =>
      apply UMPromising_Sail_no_promise_dataSynchronizationBarrer
  | |- UMPromising_Sail_no_promise
        (System.instructionSynchronizationBarrier ?u) =>
      destruct u;
      apply UMPromising_Sail_no_promise_instructionSynchronizationBarrier
  | |- UMPromising_Sail_no_promise (System.reportTLBI _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_reportTLBI
  | |- UMPromising_Sail_no_promise (System.take_exception _ _) =>
      apply UMPromising_Sail_no_promise_take_exception
  | |- UMPromising_Sail_no_promise (System.handle_fault _) =>
      apply UMPromising_Sail_no_promise_handle_fault
  | |- UMPromising_Sail_no_promise (System.lookup_sys_reg _) =>
      apply UMPromising_Sail_no_promise_lookup_sys_reg
  | |- UMPromising_Sail_no_promise (System.read_sys_reg_accessor _ _) =>
      apply UMPromising_Sail_no_promise_read_sys_reg_accessor
  | |- UMPromising_Sail_no_promise
        (System.write_sys_reg_accessor _ _ _) =>
      apply UMPromising_Sail_no_promise_write_sys_reg_accessor
  | |- UMPromising_Sail_no_promise (System.condition_holds _) =>
      apply UMPromising_Sail_no_promise_condition_holds
  | |- UMPromising_Sail_no_promise (System.translate_address _ _) =>
      apply UMPromising_Sail_no_promise_translate_address
  | |- UMPromising_Sail_no_promise (System.decode_bitmask _ _ _ _) =>
      apply UMPromising_Sail_no_promise_decode_bitmask
  | |- UMPromising_Sail_no_promise (System.decode _) =>
      apply UMPromising_Sail_no_promise_decode
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_exec
      |intro; solve_UMPromising_Sail_no_promise_exec]
  | |- UMPromising_Sail_no_promise
        (Defs.bind _ _) =>
      unfold Defs.bind;
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_exec
      |intro; solve_UMPromising_Sail_no_promise_exec]
  | |- UMPromising_Sail_no_promise
        (System_types.Interface.iMon_bind _ _) =>
      eapply UMPromising_Sail_no_promise_bind;
      [solve_UMPromising_Sail_no_promise_exec
      |intro; solve_UMPromising_Sail_no_promise_exec]
  | |- UMPromising_Sail_no_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_no_promise_bind0;
      [solve_UMPromising_Sail_no_promise_exec
      |solve_UMPromising_Sail_no_promise_exec]
  | |- UMPromising_Sail_no_promise
        (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply UMPromising_Sail_no_promise_bind0;
      [solve_UMPromising_Sail_no_promise_exec
      |solve_UMPromising_Sail_no_promise_exec]
  | |- UMPromising_Sail_no_promise
        (@Defs.liftR ?A ?R ?E ?mon) =>
      change (UMPromising_Sail_no_promise
        (@System_types.Defs.liftR A R E mon));
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise
        (@Defs.catch_early_return ?A ?E ?mon) =>
      change (UMPromising_Sail_no_promise
        (System_types.Defs.catch_early_return mon));
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise
        (@Defs.liftR ?A ?R ?E ?mon) =>
      change (UMPromising_Sail_no_promise
        (@System_types.Defs.liftR A R E mon));
      apply UMPromising_Sail_no_promise_liftR;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise
        (@Defs.catch_early_return ?A ?E ?mon) =>
      change (UMPromising_Sail_no_promise
        (System_types.Defs.catch_early_return mon));
      apply UMPromising_Sail_no_promise_catch_early_return;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_no_promise
        (Defs.early_return _) =>
      unfold Defs.early_return;
      solve_UMPromising_Sail_no_promise_exec
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_no_promise_exec
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_no_promise_exec
  | _ => solve_UMPromising_Sail_no_promise
  end.

Ltac solve_UMPromising_Sail_at_most_one_promise_exec :=
  lazymatch goal with
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Interface.Ret _) =>
      exact I
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.returnR _ _) =>
      exact I
  | |- UMPromising_Sail_at_most_one_promise
        (Defs.returnR _ _) =>
      exact I
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.early_return _) =>
      apply UMPromising_Sail_at_most_one_promise_from_no_promise;
      unfold System_types.Defs.early_return;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_at_most_one_promise
        (Defs.early_return _) =>
      apply UMPromising_Sail_at_most_one_promise_from_no_promise;
      unfold Defs.early_return;
      solve_UMPromising_Sail_no_promise_exec
  | |- UMPromising_Sail_at_most_one_promise (System.wMem _ _ _ _) =>
      apply UMPromising_Sail_at_most_one_promise_wMem
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_exec
         |intro; solve_UMPromising_Sail_at_most_one_promise_exec]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_exec
         |intro; solve_UMPromising_Sail_no_promise_exec]]
  | |- UMPromising_Sail_at_most_one_promise
        (Defs.bind _ _) =>
      unfold Defs.bind;
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_exec
         |intro; solve_UMPromising_Sail_at_most_one_promise_exec]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_exec
         |intro; solve_UMPromising_Sail_no_promise_exec]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_exec
         |intro; solve_UMPromising_Sail_at_most_one_promise_exec]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_exec
         |intro; solve_UMPromising_Sail_no_promise_exec]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_exec
      |solve_UMPromising_Sail_at_most_one_promise_exec]
  | |- UMPromising_Sail_at_most_one_promise
        (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_exec
      |solve_UMPromising_Sail_at_most_one_promise_exec]
  | |- UMPromising_Sail_at_most_one_promise
        (@Defs.liftR ?A ?R ?E ?mon) =>
      change (UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR A R E mon));
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise_exec
  | |- UMPromising_Sail_at_most_one_promise
        (@Defs.catch_early_return ?A ?E ?mon) =>
      change (UMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return mon));
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise_exec
  | |- UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise_exec
  | |- UMPromising_Sail_at_most_one_promise
        (@Defs.liftR ?A ?R ?E ?mon) =>
      change (UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR A R E mon));
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise_exec
  | |- UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise_exec
  | |- UMPromising_Sail_at_most_one_promise
        (@Defs.catch_early_return ?A ?E ?mon) =>
      change (UMPromising_Sail_at_most_one_promise
        (System_types.Defs.catch_early_return mon));
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise_exec
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_exec
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_exec
  | _ =>
      apply UMPromising_Sail_at_most_one_promise_from_no_promise;
      solve_UMPromising_Sail_no_promise_exec
  end.

Lemma UMPromising_Sail_no_promise_execute_TLBInvalidation
    op shareability t vmid :
  UMPromising_Sail_no_promise
    (System.execute_TLBInvalidation op shareability t vmid).
Proof.
  unfold System.execute_TLBInvalidation.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_SupervisorCall imm16 :
  UMPromising_Sail_no_promise (System.execute_SupervisorCall imm16).
Proof.
  unfold System.execute_SupervisorCall.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_execute_Store
    size t n offset release s :
  UMPromising_Sail_at_most_one_promise
    (System.execute_Store size t n offset release s).
Proof.
  unfold System.execute_Store.
  solve_UMPromising_Sail_at_most_one_promise_exec.
Qed.

Lemma UMPromising_Sail_at_most_one_promise_execute_AtomicRMW
    size s t n op acq rel :
  UMPromising_Sail_at_most_one_promise
    (System.execute_AtomicRMW size s t n op acq rel).
Proof.
  unfold System.execute_AtomicRMW.
  solve_UMPromising_Sail_at_most_one_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Nop :
  UMPromising_Sail_no_promise (System.execute_Nop tt).
Proof.
  unfold System.execute_Nop.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Movz sf d imm hw :
  UMPromising_Sail_no_promise (System.execute_Movz sf d imm hw).
Proof.
  unfold System.execute_Movz.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Load
    size t n offset acquire rcpc exclusive :
  UMPromising_Sail_no_promise
    (System.execute_Load size t n offset acquire rcpc exclusive).
Proof.
  unfold System.execute_Load.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_ISB :
  UMPromising_Sail_no_promise
    (System.execute_InstructionSynchronizationBarrier tt).
Proof.
  unfold System.execute_InstructionSynchronizationBarrier.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_ExceptionReturn :
  UMPromising_Sail_no_promise (System.execute_ExceptionReturn tt).
Proof.
  unfold System.execute_ExceptionReturn.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_DSB domain types :
  UMPromising_Sail_no_promise
    (System.execute_DataSynchronizationBarrier domain types).
Proof.
  unfold System.execute_DataSynchronizationBarrier.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_DMB domain types :
  UMPromising_Sail_no_promise
    (System.execute_DataMemoryBarrier domain types).
Proof.
  unfold System.execute_DataMemoryBarrier.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_CompareAndBranch
    sf t offset iszero :
  UMPromising_Sail_no_promise
    (System.execute_CompareAndBranch sf t offset iszero).
Proof.
  unfold System.execute_CompareAndBranch.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_TestAndBranch
    t bit_pos offset iszero :
  UMPromising_Sail_no_promise
    (System.execute_TestAndBranch t bit_pos offset iszero).
Proof.
  unfold System.execute_TestAndBranch.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_Branch offset :
  UMPromising_Sail_no_promise (System.execute_Branch offset).
Proof.
  unfold System.execute_Branch.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_ConditionalBranch offset cond :
  UMPromising_Sail_no_promise
    (System.execute_ConditionalBranch offset cond).
Proof.
  unfold System.execute_ConditionalBranch.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_PCRelativeAddress
    page d offset :
  UMPromising_Sail_no_promise
    (System.execute_PCRelativeAddress page d offset).
Proof.
  unfold System.execute_PCRelativeAddress.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_BranchRegister n :
  UMPromising_Sail_no_promise (System.execute_BranchRegister n).
Proof.
  unfold System.execute_BranchRegister.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_BitwiseLogic
    sf op d n op2 :
  UMPromising_Sail_no_promise
    (System.execute_BitwiseLogic sf op d n op2).
Proof.
  unfold System.execute_BitwiseLogic.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_BitfieldMove
    sf signd d n imms immr :
  UMPromising_Sail_no_promise
    (System.execute_BitfieldMove sf signd d n imms immr).
Proof.
  unfold System.execute_BitfieldMove.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_AddSub sf op s d n m :
  UMPromising_Sail_no_promise
    (System.execute_AddSub sf op s d n m).
Proof.
  unfold System.execute_AddSub, System.eval_operand, System.shift_reg.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Lemma UMPromising_Sail_no_promise_execute_SystemRegisterMove
    is_read sys_reg_id t :
  UMPromising_Sail_no_promise
    (System.execute_SystemRegisterMove is_read sys_reg_id t).
Proof.
  unfold System.execute_SystemRegisterMove.
  solve_UMPromising_Sail_no_promise_exec.
Qed.

Ltac destruct_unit :=
  match goal with
  | u : unit |- _ => destruct u
  end.

Ltac solve_UMPromising_Sail_no_promise_instr :=
  lazymatch goal with
  | |- UMPromising_Sail_no_promise
        (System.execute_TLBInvalidation _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_TLBInvalidation
  | |- UMPromising_Sail_no_promise
        (System.execute_SupervisorCall _) =>
      apply UMPromising_Sail_no_promise_execute_SupervisorCall
  | |- UMPromising_Sail_no_promise (System.execute_Nop ?u) =>
      destruct u; apply UMPromising_Sail_no_promise_execute_Nop
  | |- UMPromising_Sail_no_promise (System.execute_Movz _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_Movz
  | |- UMPromising_Sail_no_promise (System.execute_Load _ _ _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_Load
  | |- UMPromising_Sail_no_promise
        (System.execute_InstructionSynchronizationBarrier ?u) =>
      destruct u; apply UMPromising_Sail_no_promise_execute_ISB
  | |- UMPromising_Sail_no_promise
        (System.execute_ExceptionReturn ?u) =>
      destruct u;
      apply UMPromising_Sail_no_promise_execute_ExceptionReturn
  | |- UMPromising_Sail_no_promise
        (System.execute_DataSynchronizationBarrier _ _) =>
      apply UMPromising_Sail_no_promise_execute_DSB
  | |- UMPromising_Sail_no_promise
        (System.execute_DataMemoryBarrier _ _) =>
      apply UMPromising_Sail_no_promise_execute_DMB
  | |- UMPromising_Sail_no_promise
        (System.execute_CompareAndBranch _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_CompareAndBranch
  | |- UMPromising_Sail_no_promise
        (System.execute_TestAndBranch _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_TestAndBranch
  | |- UMPromising_Sail_no_promise (System.execute_Branch _) =>
      apply UMPromising_Sail_no_promise_execute_Branch
  | |- UMPromising_Sail_no_promise
        (System.execute_ConditionalBranch _ _) =>
      apply UMPromising_Sail_no_promise_execute_ConditionalBranch
  | |- UMPromising_Sail_no_promise
        (System.execute_PCRelativeAddress _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_PCRelativeAddress
  | |- UMPromising_Sail_no_promise
        (System.execute_BranchRegister _) =>
      apply UMPromising_Sail_no_promise_execute_BranchRegister
  | |- UMPromising_Sail_no_promise
        (System.execute_BitwiseLogic _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_BitwiseLogic
  | |- UMPromising_Sail_no_promise
        (System.execute_BitfieldMove _ _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_BitfieldMove
  | |- UMPromising_Sail_no_promise (System.execute_AddSub _ _ _ _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_AddSub
  | |- UMPromising_Sail_no_promise
        (System.execute_SystemRegisterMove _ _ _) =>
      apply UMPromising_Sail_no_promise_execute_SystemRegisterMove
  | _ => solve_UMPromising_Sail_no_promise_exec
  end.

Ltac solve_UMPromising_Sail_at_most_one_promise_instr :=
  lazymatch goal with
  | |- UMPromising_Sail_at_most_one_promise
        (System.execute_Store _ _ _ _ _ _) =>
      apply UMPromising_Sail_at_most_one_promise_execute_Store
  | |- UMPromising_Sail_at_most_one_promise
        (System.execute_AtomicRMW _ _ _ _ _ _ _) =>
      apply UMPromising_Sail_at_most_one_promise_execute_AtomicRMW
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |intro; solve_UMPromising_Sail_at_most_one_promise_instr]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_instr
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |intro; solve_UMPromising_Sail_at_most_one_promise_instr]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_instr
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_instr
      |solve_UMPromising_Sail_at_most_one_promise_instr]
  | |- UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise_instr
  | |- UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise_instr
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_instr
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_instr
  | _ =>
      apply UMPromising_Sail_at_most_one_promise_from_no_promise;
      solve_UMPromising_Sail_no_promise_instr
  end.

Lemma UMPromising_Sail_at_most_one_promise_execute instr :
  UMPromising_Sail_at_most_one_promise (System.execute instr).
Proof.
  unfold System.execute.
  destruct instr; cbn [System.execute].
  all: repeat match goal with
  | p : _ * _ |- _ => destruct p; cbn [System.execute]
  | u : unit |- _ => destruct u; cbn [System.execute]
  end.
  all: solve_UMPromising_Sail_at_most_one_promise_instr.
Qed.

Ltac solve_UMPromising_Sail_at_most_one_promise_fetch :=
  lazymatch goal with
  | |- UMPromising_Sail_at_most_one_promise (System.execute _) =>
      apply UMPromising_Sail_at_most_one_promise_execute
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind;
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |intro; solve_UMPromising_Sail_at_most_one_promise_fetch]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_fetch
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply UMPromising_Sail_at_most_one_promise_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |intro; solve_UMPromising_Sail_at_most_one_promise_fetch]
        |eapply UMPromising_Sail_at_most_one_promise_bind_no_right;
         [solve_UMPromising_Sail_at_most_one_promise_fetch
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_at_most_one_promise
        (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_at_most_one_promise_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_instr
      |solve_UMPromising_Sail_at_most_one_promise_fetch]
  | |- UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      apply UMPromising_Sail_at_most_one_promise_liftR;
      solve_UMPromising_Sail_at_most_one_promise_fetch
  | |- UMPromising_Sail_at_most_one_promise
        (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      apply UMPromising_Sail_at_most_one_promise_catch_early_return;
      solve_UMPromising_Sail_at_most_one_promise_fetch
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_fetch
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_at_most_one_promise_fetch
  | _ => solve_UMPromising_Sail_at_most_one_promise_instr
  end.

Lemma UMPromising_Sail_at_most_one_promise_fetch_and_execute :
  UMPromising_Sail_at_most_one_promise (System.fetch_and_execute tt).
Proof.
  unfold System.fetch_and_execute.
  solve_UMPromising_Sail_at_most_one_promise_fetch.
Qed.

Lemma UMPromising_Sail_prefix_promised_stable_sail_mem_write
    tid initmem msg nondet {E n nt} req value tags :
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet
    (System_types.Defs.sail_mem_write
       (e:=E) (n:=n) (nt:=nt) req value tags).
Proof.
  cbn [System_types.Defs.sail_mem_write].
  right.
  intros [[]|abort].
  all: exact I.
Qed.

Ltac solve_UMPromising_Sail_promised_stable_read_code :=
  eapply UMPromising_Sail_promised_stable_from_no_promise_read_code;
  [eassumption|solve_UMPromising_Sail_no_promise_instr].

Ltac solve_UMPromising_Sail_prefix_promised_stable_read_code :=
  lazymatch goal with
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Interface.Ret _) =>
      exact I
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.returnR _ _) =>
      exact I
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (Defs.returnR _ _) =>
      exact I
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.early_return _) =>
      unfold System_types.Defs.early_return;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (Defs.early_return _) =>
      unfold Defs.early_return;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (Defs.fail _) =>
      apply UMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply UMPromising_Sail_no_promise_fail
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (Defs.throw _) =>
      apply UMPromising_Sail_prefix_promised_stable_from_no_promise;
      apply UMPromising_Sail_no_promise_throw
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.sail_mem_write _ _ _) =>
      apply UMPromising_Sail_prefix_promised_stable_sail_mem_write
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (Defs.sail_mem_write _ _ _) =>
      apply UMPromising_Sail_prefix_promised_stable_sail_mem_write
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System.wMem _ _ _ _) =>
      unfold System.wMem;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System.execute_Store _ _ _ _ _ _) =>
      unfold System.execute_Store;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System.execute_AtomicRMW _ _ _ _ _ _ _) =>
      unfold System.execute_AtomicRMW;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System.execute _) =>
      unfold System.execute;
      repeat match goal with
      | p : _ * _ |- _ => destruct p; cbn [System.execute]
      | u : unit |- _ => destruct u; cbn [System.execute]
      end;
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (@Defs.bind _ _ _ (if ?x then _ else _) _) =>
      destruct x; solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (@Defs.bind _ _ _ (match ?x with _ => _ end) _) =>
      destruct x; solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable
        ?tid ?initmem ?msg ?nondet (@Defs.bind ?A ?B ?E ?mon ?k) =>
      change (UMPromising_Sail_prefix_promised_stable tid initmem msg nondet
        (SI.iMon_bind mon k));
      first
        [refine (@UMPromising_Sail_prefix_promised_stable_bind_no_left
           tid initmem msg nondet E A B mon k _ _ _);
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |refine (@UMPromising_Sail_prefix_promised_stable_bind_no_right
           tid initmem msg nondet E A B mon k _ _);
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.bind ?mon _) =>
      unfold System_types.Defs.bind;
      first
        [eapply UMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (Defs.bind ?mon _) =>
      unfold Defs.bind;
      first
        [eapply UMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Interface.iMon_bind _ _) =>
      first
        [eapply UMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (System_types.Defs.bind0 _ _) =>
      eapply UMPromising_Sail_prefix_promised_stable_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_instr
      |solve_UMPromising_Sail_promised_stable_read_code
      |solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (Defs.bind0 _ _) =>
      unfold Defs.bind0;
      eapply UMPromising_Sail_prefix_promised_stable_bind0_no_left;
      [solve_UMPromising_Sail_no_promise_instr
      |solve_UMPromising_Sail_promised_stable_read_code
      |solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (@System_types.Defs.liftR ?A ?R ?E ?mon) =>
      first
        [eapply UMPromising_Sail_prefix_promised_stable_liftR_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_liftR_no_right;
         solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable
        ?tid ?initmem ?msg ?nondet (@Defs.liftR ?A ?R ?E ?mon) =>
      change (UMPromising_Sail_prefix_promised_stable tid initmem msg nondet
        (@System_types.Defs.liftR A R E mon));
      first
        [eapply UMPromising_Sail_prefix_promised_stable_liftR_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_liftR_no_right;
         solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable
        _ _ _ _ (@System_types.Defs.catch_early_return ?A ?E ?mon) =>
      first
        [eapply
           UMPromising_Sail_prefix_promised_stable_catch_early_return_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code]
        |eapply
           UMPromising_Sail_prefix_promised_stable_catch_early_return_no_right;
         solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable
        ?tid ?initmem ?msg ?nondet
        (@Defs.catch_early_return ?A ?E ?mon) =>
      change (UMPromising_Sail_prefix_promised_stable tid initmem msg nondet
        (System_types.Defs.catch_early_return mon));
      first
        [eapply
           UMPromising_Sail_prefix_promised_stable_catch_early_return_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code]
        |eapply
           UMPromising_Sail_prefix_promised_stable_catch_early_return_no_right;
         solve_UMPromising_Sail_prefix_promised_stable_read_code]
  | |- UMPromising_Sail_prefix_promised_stable _ _ _ _ _ =>
      progress cbn [System_types.Defs.bind Defs.bind];
      first
        [eapply UMPromising_Sail_prefix_promised_stable_bind_no_left;
         [solve_UMPromising_Sail_no_promise_instr
         |solve_UMPromising_Sail_promised_stable_read_code
         |intro; solve_UMPromising_Sail_prefix_promised_stable_read_code]
        |eapply UMPromising_Sail_prefix_promised_stable_bind_no_right;
         [solve_UMPromising_Sail_prefix_promised_stable_read_code
         |intro; solve_UMPromising_Sail_no_promise_instr]]
  | |- context[match ?x with _ => _ end] =>
      destruct x; solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- context[if ?x then _ else _] =>
      destruct x; solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable _ _ _ _ _ =>
      progress cbn [System_types.Defs.bind];
      solve_UMPromising_Sail_prefix_promised_stable_read_code
  | |- UMPromising_Sail_prefix_promised_stable _ _ _ _ _ =>
      first
        [progress UMPromising_Sail_simpl;
         solve_UMPromising_Sail_prefix_promised_stable_read_code
        |apply UMPromising_Sail_prefix_promised_stable_from_no_promise;
         solve_UMPromising_Sail_no_promise_instr]
  end.

Lemma UMPromising_Sail_prefix_promised_stable_fetch_and_execute_from_read_code
    tid initmem code msg nondet :
  UMPromising_read_code_stability tid initmem code msg →
  UMPromising_Sail_prefix_promised_stable
    tid initmem msg nondet (System.fetch_and_execute tt).
Proof.
  intro Hstable.
  unfold System.fetch_and_execute.
  eapply UMPromising_Sail_prefix_promised_stable_catch_early_return_no_right.
  cbn [System_types.Defs.bind].
  eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
  - solve_UMPromising_Sail_no_promise_instr.
  - solve_UMPromising_Sail_promised_stable_read_code.
  - intro accdesc.
    cbn [System_types.Defs.bind].
    eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
    + solve_UMPromising_Sail_no_promise_instr.
    + solve_UMPromising_Sail_promised_stable_read_code.
    + intro pc.
      cbn [System_types.Defs.bind].
      eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
      * solve_UMPromising_Sail_no_promise_instr.
      * solve_UMPromising_Sail_promised_stable_read_code.
      * intro addr_opt.
        cbn [System_types.Defs.bind].
        eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
        -- destruct addr_opt; solve_UMPromising_Sail_no_promise_instr.
        -- destruct addr_opt; solve_UMPromising_Sail_promised_stable_read_code.
        -- intro addr_ret.
           cbn [System_types.Defs.bind].
           eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
           ++ solve_UMPromising_Sail_no_promise_instr.
           ++ solve_UMPromising_Sail_promised_stable_read_code.
           ++ intro machineCode.
              cbn [System_types.Defs.bind].
              eapply UMPromising_Sail_prefix_promised_stable_bind_no_left.
              ** solve_UMPromising_Sail_no_promise_instr.
              ** solve_UMPromising_Sail_promised_stable_read_code.
              ** intro instr.
                 eapply
                   UMPromising_Sail_prefix_promised_stable_liftR_no_right.
                 unfold System.execute;
                 destruct instr; cbn [System.execute];
                 repeat match goal with
                 | p : _ * _ |- _ => destruct p; cbn [System.execute]
                 | u : unit |- _ => destruct u; cbn [System.execute]
                 end;
                 try (apply
                   UMPromising_Sail_prefix_promised_stable_from_no_promise;
                   solve_UMPromising_Sail_no_promise_instr);
                 try (eapply
                   UMPromising_Sail_prefix_promised_stable_from_at_most_one_read_code;
                   [eassumption
                   |solve_UMPromising_Sail_at_most_one_promise_instr]);
                 solve_UMPromising_Sail_prefix_promised_stable_read_code.
Qed.

Ltac solve_UMPromising_no_promise_outcome :=
  eapply UMPromising_handle_outcome_no_promise_non_mem_write;
  intros ? ? ? Hneq; discriminate Hneq.

Ltac solve_UMPromising_cmon_no_promise :=
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
  | |- CPStateProof.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- CPStateProof.handle_outcome_no_promise UMPromising _ _ _ =>
      solve_UMPromising_no_promise_outcome
  end.

Ltac solve_UMPromising_cmon_at_most_one :=
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
  | |- CPStateProof.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- CPStateProof.cmon_at_most_one_promise _ _ _ _ _ => progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- CPStateProof.handle_outcome_no_promise UMPromising _ _ _ =>
      solve_UMPromising_no_promise_outcome
  | |- _ ∨ _ =>
      first [left; split; [solve_UMPromising_no_promise_outcome|]
            | right; solve_UMPromising_cmon_no_promise]
  end.

Ltac solve_UMPromising_cmon_at_most_one_prefix :=
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
  | |- CPStateProof.cmon_no_promise _ _ _ _ _ => progress cbn
  | |- CPStateProof.cmon_at_most_one_promise_prefix_stable _ _ _ _ _ _ =>
      progress cbn
  | |- True => exact I
  | |- _ ∧ _ => split
  | |- ∀ _, _ => intro
  | |- _ ∨ _ => right; solve_UMPromising_cmon_no_promise
  end.

Lemma UMPromising_Sail_outcome_no_promise_interp {n eo A}
    (tid : fin n) initmem nondet (out : SI.outcome eo A) :
  UMPromising_Sail_outcome_no_promise out →
  CPStateProof.cmon_no_promise UMPromising tid initmem A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; intro Hout; try contradiction;
    solve_UMPromising_cmon_no_promise.
  all: destruct ty; solve_UMPromising_cmon_no_promise.
Qed.

Lemma UMPromising_Sail_outcome_at_most_one_promise_interp {n eo A}
    (tid : fin n) initmem nondet (out : SI.outcome eo A) :
  CPStateProof.cmon_at_most_one_promise UMPromising tid initmem A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; solve_UMPromising_cmon_at_most_one.
  all: destruct ty; solve_UMPromising_cmon_at_most_one.
Qed.

Lemma UMPromising_Sail_outcome_at_most_one_prefix_stable_interp
    {n eo A} (tid : fin n) initmem msg nondet
    (out : SI.outcome eo A) :
  CPStateProof.cmon_at_most_one_promise_prefix_stable
    UMPromising tid initmem msg A
    (Sail_outcome_interp nondet out).
Proof.
  destruct out; solve_UMPromising_cmon_at_most_one_prefix.
  all: destruct ty; solve_UMPromising_cmon_at_most_one_prefix.
Qed.

Lemma UMPromising_iMon_from_Sail_no_promise {n eo A}
    (tid : fin n) initmem nondet (smon : SI.iMon eo A) :
  UMPromising_Sail_no_promise smon →
  CPStateProof.cmon_no_promise UMPromising tid initmem A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hno_promise.
  - exact I.
  - cbn in Hno_promise |- *.
    destruct Hno_promise as [Hout Htail].
    eapply CPStateProof.cmon_no_promise_bind.
    + apply UMPromising_Sail_outcome_no_promise_interp.
      exact Hout.
    + intro ret.
      apply IH.
      apply Htail.
Qed.

Lemma UMPromising_iMon_from_Sail_at_most_one_promise {n eo A}
    (tid : fin n) initmem nondet (smon : SI.iMon eo A) :
  UMPromising_Sail_at_most_one_promise smon →
  CPStateProof.cmon_at_most_one_promise UMPromising tid initmem A
    (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hat_most.
  - exact I.
  - cbn in Hat_most |- *.
    destruct Hat_most as [[Hout Htail_at_most]|Htail_no_promise].
    + eapply CPStateProof.cmon_at_most_one_promise_bind_no_left.
      * apply UMPromising_Sail_outcome_no_promise_interp.
        exact Hout.
      * intro ret.
        apply IH.
        apply Htail_at_most.
    + eapply CPStateProof.cmon_at_most_one_promise_bind_no_right.
      * apply UMPromising_Sail_outcome_at_most_one_promise_interp.
      * intro ret.
        apply UMPromising_iMon_from_Sail_no_promise.
        apply Htail_no_promise.
Qed.

Lemma UMPromising_iMon_from_Sail_prefix_promised_stable
    {n eo A} (tid : fin n) initmem msg nondet
    (smon : SI.iMon eo A) :
  UMPromising_Sail_prefix_promised_stable
    (tid : nat) initmem msg nondet smon →
  CPStateProof.cmon_at_most_one_promise_prefix_stable
    UMPromising tid initmem msg A (iMon_from_Sail nondet smon).
Proof.
  induction smon as [a|T out k IH]; intro Hstable.
  - exact I.
  - cbn in Hstable |- *.
    destruct Hstable as
      [[Hout_no [Hout_stable Htail_stable]]|Htail_no_promise].
    + eapply CPStateProof.cmon_at_most_one_promise_prefix_stable_bind_no_left.
      * apply UMPromising_Sail_outcome_no_promise_interp.
        exact Hout_no.
      * apply UMPromising_imon_future_promise_stable_promised_to_cmon.
        exact Hout_stable.
      * intro ret.
        apply IH.
        apply Htail_stable.
    + eapply CPStateProof.cmon_at_most_one_promise_prefix_stable_bind_no_right.
      * apply UMPromising_Sail_outcome_at_most_one_prefix_stable_interp.
      * intro ret.
        apply UMPromising_iMon_from_Sail_no_promise.
        apply Htail_no_promise.
Qed.
