(******************************************************************************)
(* VM reads and fulfilled writes under a future event and updated cache       *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstExecutionCurrent PromiseFirstVMExecutionCurrent
  PromiseFirstSailRead PromiseFirstSailFulfilled PromiseFirstSailCertification
  PromiseFirstSailScheduling PromiseFirstConcreteCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

Module VMReadReplay.
Import VMPromising.
#[local] Typeclasses Transparent Memory.t othrow view UMPromising.view.
Definition add_event (ev : Ev.t) (tlb : option TLB.t)
    (ppst : PPState.t TState.t Ev.t IIS.t) :=
  PPState.Make (setv TState.tlb tlb (PPState.state ppst))
    (ev :: PPState.mem ppst) (PPState.iis ppst).

Lemma run_tlb_frame upd ts ts' :
  TState.run_tlb upd ts = Ok ts' →
  ts' = setv TState.tlb (TState.tlb ts') ts.
Proof.
  unfold TState.run_tlb.
  destruct (TState.tlb ts) as [old|] eqn:Htlb.
  - destruct (upd old) as [[new []]|err]; cbn; [|discriminate].
    intro H. inversion H; subst. reflexivity.
  - intro H. injection H as <-. destruct ts. reflexivity.
Qed.

Lemma emit_foreign_event_frame tid imem mem ev ts ts' :
  Ev.tid ev ≠ tid → TState.emit_promise tid imem mem ev ts = Ok ts' →
  ts' = setv TState.tlb (TState.tlb ts') ts.
Proof.
  intros Hforeign Hpromise. unfold TState.emit_promise in Hpromise.
  rewrite bool_decide_false in Hpromise by exact Hforeign.
  eapply run_tlb_frame. exact Hpromise.
Qed.

Lemma update_cohs_tlb avs tlb ts :
  TState.update_cohs avs (setv TState.tlb tlb ts) =
  setv TState.tlb tlb (TState.update_cohs avs ts).
Proof.
  induction avs as [|[a v] avs IH]; [reflexivity|].
  change (TState.update_coh a v (TState.update_cohs avs (setv TState.tlb tlb ts)) =
    setv TState.tlb tlb (TState.update_coh a v (TState.update_cohs avs ts))).
  rewrite IH. reflexivity.
Qed.

Local Opaque TState.update_cohs.

Lemma read_explicit_after_event addr size macc imem ev tlb ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (read_mem_explicit imem addr size macc ppst) →
  Exec.elem_of_results (add_event ev tlb ppst', ret)
    (read_mem_explicit imem addr size macc (add_event ev tlb ppst)).
Proof.
  destruct ppst as [ts mem iis]. intro Hrun.
  unfold read_mem_explicit in Hrun |- *.
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
  pose proof (read_all_aux_success_bound Ev.get_msg _ _ _ _ _ _ _ Hread) as Hmin.
  destruct (read_all_cons_preserves_candidates Ev.get_msg addr size imem mem ev _ candidates
    Hmin Hread) as [new_candidates [Hread' Hsubset]].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply exec_guard_discard_bind_intro; [exact Hnp|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [add_event].
  eapply Exec.elem_of_bind_intro with (a := new_candidates).
  - apply exec_lift_result. exact Hread'.
  - eapply Exec.elem_of_bind_intro with (a := candidate).
    + apply Exec.elem_of_mchoosel, Hsubset, Hin.
    + cbn [add_event PPState.state PPState.mem PPState.iis] in *.
      UMFulfilledReplay.invert_execution_with_guards.
      all: subst ret.
      all: cbn [add_event].
      all: repeat first
        [ eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_guard_discard_unit; assumption|]
        | eapply exec_guard_discard_bind_intro; [assumption|] ].
      all: unfold Exec.elem_of_results; cbn [Exec.results mret Exec.mret_inst Exec.res_mret_inst];
        apply list_elem_of_singleton; f_equal.
      all: cbn [add_event PPState.state PPState.mem PPState.iis compose].
      all: cbn; rewrite update_cohs_tlb; reflexivity.
Qed.

#[local] Existing Instance PromMemory.lookup_inst.
#[local] Existing Instance PromMemory.exclusive_dec.

Lemma fulfill_after_event msg future prom mem :
  (∀ t ∈ prom, t ≤ length mem) →
  Memory.fulfill msg prom (future :: mem) = Memory.fulfill msg prom mem.
Proof.
  intro Hbound. unfold Memory.fulfill, PromMemory.fulfill.
  f_equal. f_equal. induction prom as [|t prom IH]; [reflexivity|].
  rewrite !filter_cons.
  rewrite PromMemory.lookup_cons_old by (apply Hbound; set_solver).
  rewrite IH by (intros; apply Hbound; set_solver). reflexivity.
Qed.

Lemma fulfill_bound msg prom mem time :
  Memory.fulfill msg prom mem = Some time → time ≤ length mem.
Proof.
  unfold Memory.fulfill, PromMemory.fulfill. rewrite head_reverse.
  intro H. apply last_Some_elem_of in H. apply list_elem_of_filter in H as [Hlookup _].
  unfold lookup, PromMemory.lookup_inst in Hlookup.
  destruct (time =? 0)%stdpp; [discriminate|].
  destruct (time <=? length mem)%nat eqn:Hle; [apply Nat.leb_le, Hle|discriminate].
Qed.

Lemma exclusive_before_future tid addr size tread time ev mem :
  time ≤ length mem →
  Memory.exclusive tid addr size tread time (ev :: mem) =
  Memory.exclusive tid addr size tread time mem.
Proof.
  intro Htime. unfold Memory.exclusive, PromMemory.exclusive.
  rewrite PromMemory.cut_before_cons_old by lia. reflexivity.
Qed.

Lemma set_fwdbs_tlb addrs n (data : bv n) time vdata xcl tlb ts :
  TState.set_fwdbs addrs data time vdata xcl (setv TState.tlb tlb ts) =
  setv TState.tlb tlb (TState.set_fwdbs addrs data time vdata xcl ts).
Proof.
  unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)).
  intro pairs. revert ts. induction pairs as [|[addr byte] pairs IH]; intro ts; cbn.
  - reflexivity.
  - rewrite <- IH. f_equal; destruct ts; reflexivity.
Qed.
Local Opaque TState.set_fwdbs.

Lemma write_fulfilled_after_event tid imem addr size macc data ev tlb ppst ppst' :
  (∀ t ∈ TState.prom_wr (PPState.state ppst), t ≤ length (PPState.mem ppst)) →
  Exec.elem_of_results (ppst', None) (write_mem tid imem addr size macc data ppst) →
  Exec.elem_of_results (add_event ev tlb ppst', None)
    (write_mem tid imem addr size macc data (add_event ev tlb ppst)).
Proof.
  destruct ppst as [ts mem iis]. cbn. intros Hbound Hrun.
  unfold write_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [mem0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[time fresh] [Hfulfill Hrun]]].
  destruct (Memory.fulfill (Ev.Msg (Msg.make tid addr size data)) (TState.prom_wr ts) mem)
    as [t|] eqn:Hlookup.
  all: cbn [PPState.state PPState.mem] in Hfulfill; rewrite Hlookup in Hfulfill.
  2: { exfalso. VMMemoryGrowth.invert_execution; cbn in *; discriminate. }
  apply Exec.elem_of_mret_inv in Hfulfill as [-> Heq]. inversion Heq; subst time fresh.
  pose proof (fulfill_bound _ _ _ _ Hlookup) as Htime.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [add_event PPState.state PPState.mem].
  rewrite fulfill_after_event by exact Hbound.
  change (TState.prom_wr (setv TState.tlb tlb ts)) with (TState.prom_wr ts).
  rewrite Hlookup.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  UMFulfilledReplay.invert_execution_with_guards; subst; try discriminate.
  all: cbn [PPState.state PPState.mem PPState.iis compose] in *.
  all: repeat first
    [ apply Exec.elem_of_guard_discard_unit;
        first [rewrite exclusive_before_future by assumption; assumption | assumption]
    | apply Exec.elem_of_mret
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_guard_discard_unit;
        first [rewrite exclusive_before_future by assumption; assumption | assumption]|]
    | eapply exec_guard_discard_bind_intro; [assumption|]
    | match goal with H : ?x = _ |- context[?x] => progress rewrite H end
    | progress cbn [add_event PPState.state PPState.iis PPState.mem compose othrow]
    | progress change (TState.xclb (setv TState.tlb tlb ts)) with (TState.xclb ts)
    | match goal with
      | |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) => eapply Exec.elem_of_bind_intro
      end ].
  all: unfold Exec.elem_of_results; cbn [Exec.results mret Exec.mret_inst Exec.res_mret_inst];
    apply list_elem_of_singleton; f_equal.
  all: cbn.
  all: fold (set TState.prom_wr (filter (λ v : nat, v ≠ t)) (setv TState.tlb tlb ts)).
  all: change (set TState.prom_wr (filter (λ v : nat, v ≠ t)) (setv TState.tlb tlb ts))
    with (setv TState.tlb tlb (set TState.prom_wr (filter (λ v : nat, v ≠ t)) ts)).
  all: rewrite update_cohs_tlb.
  all: unfold add_event; cbn [PPState.state PPState.mem PPState.iis].
  all: rewrite <- set_fwdbs_tlb; reflexivity.
Qed.

Lemma read_pte_after_event ev tlb ppst ppst' ret :
  Exec.elem_of_results (ppst', ret) (read_pte ppst) →
  Exec.elem_of_results (add_event ev tlb ppst', ret) (read_pte (add_event ev tlb ppst)).
Proof.
  destruct ppst as [ts mem iis]. intro Hrun. unfold read_pte in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [opt [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  cbn [compose PPState.iis] in Hrun.
  destruct (IIS.trs iis) as [tres|] eqn:Htrs.
  2: { unfold othrow in Hrun. VMMemoryGrowth.invert_execution. }
  unfold othrow in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [tr [Hret Hrun]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[tr val] [Hpop Hrun]]].
  apply exec_lift_result_inv in Hpop as [-> Hpop].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[] [Hset Hrun]]].
  apply Exec.elem_of_mset_inv in Hset as ->.
  apply Exec.elem_of_mret_inv in Hrun as [-> ->].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [add_event PPState.iis compose]. rewrite Htrs. cbn [othrow].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  eapply Exec.elem_of_bind_intro; [apply exec_lift_result; exact Hpop|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  apply Exec.elem_of_mret.
Qed.

Lemma mem_read_after_event n tid imem req ev tlb ppst ppst' ret pre :
  (is_ifetch (MemReq.access_kind req) = true →
    MemReq.size req = 4%N →
    read_imem imem (MemReq.address req) (ev :: PPState.mem ppst) =
    read_imem imem (MemReq.address req) (PPState.mem ppst)) →
  Exec.elem_of_results (ppst', (ret, pre)) (run_outcome n tid imem (MemRead req) ppst) →
  Exec.elem_of_results (add_event ev tlb ppst', (ret, pre))
    (run_outcome n tid imem (MemRead req) (add_event ev tlb ppst)).
Proof.
  destruct req as [macc addr pas size tags].
  destruct tags as [|tags]; intros Hfetch Hrun.
  2: { simp run_outcome in Hrun. VMMemoryGrowth.invert_execution. }
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
    destruct (Exec.elem_of_guard_or (E:=string) (add_event ev tlb ppst)
      "Ifetch read of size other than 4" Hsize) as [Hsize' Hguard].
    replace Hsize' with Hsize in Hguard by apply proof_irrel.
    eapply Exec.elem_of_bind_intro; [exact Hguard|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro with (a := opcode).
    + apply Exec.elem_of_lift_res. cbn.
      rewrite (Hfetch Hif Hsize). exact Hread.
    + apply Exec.elem_of_mret.
  - destruct (is_explicit macc) eqn:Hexpl.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [val [Hread Hrun]]].
      apply Exec.elem_of_mret_inv in Hrun as [-> Heq].
      injection Heq as -> ->.
      eapply Exec.elem_of_bind_intro; [eapply read_explicit_after_event; exact Hread|].
      apply Exec.elem_of_mret.
    + destruct (is_ttw macc) eqn:Httw.
      * apply Exec.elem_of_bind_elim in Hrun as [mid [Hsize [Hguard Hrun]]].
        apply Exec.elem_of_guard_or_inv in Hguard as ->.
        apply Exec.elem_of_bind_elim in Hrun as [mid [val [Hread Hrun]]].
        apply Exec.elem_of_mret_inv in Hrun as [-> Heq]. injection Heq as -> ->.
        destruct (Exec.elem_of_guard_or (E:=string) (add_event ev tlb ppst)
          "TTW read of size other than 8" Hsize) as [Hsize' Hguard].
        replace Hsize' with Hsize in Hguard by apply proof_irrel.
        eapply Exec.elem_of_bind_intro; [exact Hguard|].
        eapply Exec.elem_of_bind_intro; [eapply read_pte_after_event; exact Hread|].
        apply Exec.elem_of_mret.
      * VMMemoryGrowth.invert_execution.
Qed.
End VMReadReplay.

#[local] Typeclasses Transparent VMPromising.VMPromising Promising.mEvent Promising.tState Promising.iis.
#[local] Typeclasses Transparent VMPromising.Memory.t VMPromising.view UMPromising.view.

(** The cache supplied to replay is the result of the actual global promise
    operation. A foreign event preserves this thread's pending lists. *)
Theorem VMSail_foreign_event_explicit_read bbm {n} (tid : fin n)
    st next ev addr size macc iis ppst' ret :
  Ev.tid ev ≠ (tid : nat) →
  PState.promise (VMPromising.VMPromising bbm) ev st = Ok next →
  Exec.elem_of_results (ppst', ret)
    (VMPromising.read_mem_explicit (PState.initmem st) addr size macc
      (PPState.Make (PState.tstate tid st) (PState.events st) iis)) →
  Exec.elem_of_results
    (VMReadReplay.add_event ev (VMPromising.TState.tlb (PState.tstate tid next)) ppst', ret)
    (VMPromising.read_mem_explicit (PState.initmem next) addr size macc
      (PPState.Make (PState.tstate tid next) (PState.events next) iis)).
Proof.
  intros Hforeign Hpromise Hread.
  destruct (VMPromising_promise_success ev st next Hpromise) as [Himem [Hmem Hstates]].
  specialize (Hstates tid).
  pose proof (VMReadReplay.emit_foreign_event_frame (tid : nat) (PState.initmem st)
    (ev :: PState.events st) ev (PState.tstate tid st) (PState.tstate tid next)
    Hforeign Hstates) as Hstate.
  rewrite Himem, Hmem.
  assert (Hinitial :
    PPState.Make (PState.tstate tid next) (ev :: PState.events st) iis =
    VMReadReplay.add_event ev (VMPromising.TState.tlb (PState.tstate tid next))
      (PPState.Make (PState.tstate tid st) (PState.events st) iis)).
  { unfold VMReadReplay.add_event. cbn. f_equal. exact Hstate. }
  rewrite Hinitial.
  apply VMReadReplay.read_explicit_after_event. exact Hread.
Qed.

Theorem VMSail_foreign_event_fulfilled_write bbm {n} (tid : fin n)
    st next ev addr size macc data iis ppst' :
  Ev.tid ev ≠ (tid : nat) →
  PState.promise (VMPromising.VMPromising bbm) ev st = Ok next →
  (∀ t ∈ VMPromising.TState.prom_wr (PState.tstate tid st), t ≤ length (PState.events st)) →
  Exec.elem_of_results (ppst', None)
    (VMPromising.write_mem (tid : nat) (PState.initmem st) addr size macc data
      (PPState.Make (PState.tstate tid st) (PState.events st) iis)) →
  Exec.elem_of_results
    (VMReadReplay.add_event ev (VMPromising.TState.tlb (PState.tstate tid next)) ppst', None)
    (VMPromising.write_mem (tid : nat) (PState.initmem next) addr size macc data
      (PPState.Make (PState.tstate tid next) (PState.events next) iis)).
Proof.
  intros Hforeign Hpromise Hbound Hwrite.
  destruct (VMPromising_promise_success ev st next Hpromise) as [Himem [Hmem Hstates]].
  specialize (Hstates tid).
  pose proof (VMReadReplay.emit_foreign_event_frame (tid : nat) (PState.initmem st)
    (ev :: PState.events st) ev (PState.tstate tid st) (PState.tstate tid next)
    Hforeign Hstates) as Hstate.
  rewrite Himem, Hmem.
  assert (Hinitial :
    PPState.Make (PState.tstate tid next) (ev :: PState.events st) iis =
    VMReadReplay.add_event ev (VMPromising.TState.tlb (PState.tstate tid next))
      (PPState.Make (PState.tstate tid st) (PState.events st) iis)).
  { unfold VMReadReplay.add_event. cbn. f_equal. exact Hstate. }
  rewrite Hinitial.
  apply VMReadReplay.write_fulfilled_after_event; assumption.
Qed.
