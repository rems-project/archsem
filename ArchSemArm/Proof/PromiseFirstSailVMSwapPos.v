(******************************************************************************)
(* Positive TLBI times in the caches of reachable VM states                   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstSailVMViews
  PromiseFirstFreshBroadcast PromiseFirstVMExecutionCurrent
  PromiseFirstSailVMSwapSim PromiseFirstSailVMSwapLookup.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** Every thread cache of a reachable state records TLBI events at positive
    timestamps ([VMSwapLookup.ts_pos]). A cache changes only by
    [TState.run_tlb] of an entry fill at initialisation, event delivery,
    context synchronization and translation-root writes, all of which keep
    positive times when the history is non-empty. The walk follows the
    handlers of [VMPromising.run_outcome]: every handler output thread state
    has the cache of the input, or of a state produced by one of these
    operations. *)

Module VMSwapPos.
Import VMPromising VMSwapSim VMSwapLookup.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

(** * Thread-state operations *)

Lemma ts_pos_eq ts ts' : TState.tlb ts' = TState.tlb ts → ts_pos ts → ts_pos ts'.
Proof. intros E H c Hc. apply H. rewrite <- E. exact Hc. Qed.

Lemma set_reg_pos r rv ts ts' : ts_pos ts → TState.set_reg r rv ts = Some ts' → ts_pos ts'.
Proof.
  intros Hts. unfold TState.set_reg. case_decide; [|discriminate].
  injection 1 as <-. exact Hts.
Qed.

Lemma add_wsreg_pos tid imem mem sreg val v ts ts' : ts_pos ts →
  TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → ts_pos ts'.
Proof.
  intros Hts Hrun. unfold TState.add_wsreg, mbind, result_bind in Hrun.
  match type of Hrun with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hrun as <-. apply (ts_pos_eq mid); [reflexivity|].
  refine (run_tlb_pos _ _ _ _ Hts Hmid).
  destruct sreg as [r|r|r|r]; try apply pres_ret.
  destruct r; try apply pres_ret; cbv beta iota zeta.
  - apply pres_bind; [apply pres_fill_asid_root|intros _].
    apply pres_bind; [|intro; apply pres_ret].
    apply pres_mapM. intros [ttbr1 v1]. apply pres_fill_asid_root.
  - apply pres_bind; [apply pres_othrow|intro].
    apply pres_bind; [|intro; apply pres_ret].
    apply pres_mapM. intros [ttbr0 v0]. apply pres_fill_asid_root.
Qed.

(** * Outcome handlers *)

Definition pp_pos (ppst : PPState.t TState.t Ev.t IIS.t) := ts_pos (PPState.state ppst).

Lemma update_cohs_tlb avs ts : TState.tlb (TState.update_cohs avs ts) = TState.tlb ts.
Proof. induction avs as [|[a v] avs IH]; [reflexivity|exact IH]. Qed.

Lemma update_tcohs_tlb asid offs v ts :
  TState.tlb (TState.update_tcohs asid offs v ts) = TState.tlb ts.
Proof. induction offs as [|o offs IH]; [reflexivity|exact IH]. Qed.

Lemma set_fwdbs_tlb addrs n (data : bv n) time vdata xcl ts :
  TState.tlb (TState.set_fwdbs addrs data time vdata xcl ts) = TState.tlb ts.
Proof.
  unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)). intro l.
  revert ts. induction l as [|[a b] l IH]; intro ts; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

(** The cache of a thread state built by setters from [X]. *)
Ltac tlb_eq :=
  first [reflexivity
  | match goal with
    | |- context[TState.update_cohs ?avs ?X] =>
        transitivity (TState.tlb (TState.update_cohs avs X)); [reflexivity|];
        rewrite update_cohs_tlb; tlb_eq
    | |- context[TState.update_tcohs ?a ?o ?v ?X] =>
        transitivity (TState.tlb (TState.update_tcohs a o v X)); [reflexivity|];
        rewrite update_tcohs_tlb; tlb_eq
    | |- context[TState.set_fwdbs ?addrs ?d ?t ?vd ?x ?X] =>
        transitivity (TState.tlb (TState.set_fwdbs addrs d t vd x X)); [reflexivity|];
        rewrite set_fwdbs_tlb; tlb_eq
    end].

Ltac pos_close :=
  unfold pp_pos in *;
  match goal with HX : ts_pos ?X |- ts_pos ?E =>
    apply (ts_pos_eq X E); [tlb_eq|exact HX] end.

Ltac pos_derive :=
  repeat match goal with
  | H : TState.cse _ _ _ _ ?X = Ok ?Y |- _ =>
      let HX := fresh in assert (HX : ts_pos X) by pos_close;
      pose proof (cse_pos _ _ _ _ _ _ HX H); clear H HX
  | H : TState.add_wsreg _ _ _ _ _ _ ?X = Ok ?Y |- _ =>
      let HX := fresh in assert (HX : ts_pos X) by pos_close;
      pose proof (add_wsreg_pos _ _ _ _ _ _ _ _ HX H); clear H HX
  | H : TState.process_event _ _ ?m _ ?X = Ok ?Y |- _ =>
      let HX := fresh in assert (HX : ts_pos X) by pos_close;
      let Hm := fresh in assert (Hm : 0 < length m) by (cbn; lia);
      pose proof (process_event_pos _ _ _ _ _ _ Hm HX H); clear H HX Hm
  | H : TState.set_reg _ _ ?X = Some ?Y |- _ =>
      let HX := fresh in assert (HX : ts_pos X) by pos_close;
      pose proof (set_reg_pos _ _ _ _ HX H); clear H HX
  end.

Ltac pos_solve := VMViews.invert; subst; unfold pp_pos in *; cbn in *; pos_derive; pos_close.

Lemma run_cse_pos tid imem vmax ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (run_cse tid imem vmax ppst) → pp_pos ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hts Hrun. unfold run_cse in Hrun.
  pos_solve.
Qed.

Lemma run_barrier_pos tid imem barrier vmax ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (run_barrier tid imem barrier vmax ppst) →
  pp_pos ppst'.
Proof.
  intros Hok Hrun. destruct ppst as [ts mem iis]. unfold run_barrier in Hrun.
  VMViews.invert.
  all: try solve [eapply run_cse_pos; eassumption].
  all: subst; unfold pp_pos in *; cbn in *; pos_close.
Qed.

Lemma run_reg_read_pos reg racc st st' val :
  Exec.elem_of_results (st', val) (run_reg_read reg racc st) → st'.1 = st.1.
Proof.
  destruct st as [ts iis]. intros Hrun. unfold run_reg_read in Hrun.
  VMViews.invert; subst; cbn in *.
  - unfold run_reg_trans_read in *. VMViews.invert; subst; reflexivity.
  - unfold run_reg_general_read, read_sreg_indirect in *. VMViews.invert; subst; reflexivity.
Qed.

Lemma run_reg_write_pos tid imem reg racc val ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (run_reg_write tid imem reg racc val ppst) →
  pp_pos ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hts Hrun. unfold run_reg_write in Hrun. pos_solve.
Qed.

Lemma read_mem_explicit_pos imem addr size macc ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (read_mem_explicit imem addr size macc ppst) →
  pp_pos ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hts Hrun. unfold read_mem_explicit in Hrun. pos_solve.
Qed.

Lemma read_pte_pos ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (read_pte ppst) → pp_pos ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hts Hrun. unfold read_pte in Hrun. pos_solve.
Qed.

Lemma write_mem_pos tid imem addr size macc data ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (write_mem tid imem addr size macc data ppst) →
  pp_pos ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hts Hrun. unfold write_mem in Hrun. pos_solve.
Qed.

Lemma materialize_pos tid imem pre tlbi recipient ppst ppst' res :
  pp_pos ppst →
  Exec.elem_of_results (ppst', res)
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient ppst) →
  pp_pos ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hts Hrun.
  unfold materialize_tlbi_for_recipient in Hrun. pos_solve.
Qed.

Lemma recipients_pos tid imem pre tlbi recipients acc ppst ppst' res :
  pp_pos ppst →
  Exec.elem_of_results (ppst', res)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients ppst) →
  pp_pos ppst'.
Proof.
  revert acc ppst. induction recipients as [|recipient recipients IH]; intros acc ppst Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hok.
  - cbn [foldlM] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [mid [acc' [Hstep Htail]]].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep. destruct acc as [[vs vo] c].
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time is_new] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply IH; [|exact Htail]. eapply materialize_pos; eassumption.
Qed.

Lemma run_tlbi_pos n tid imem viio tlbi ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (run_tlbi n tid imem viio tlbi ppst) →
  pp_pos ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hok Hrun. unfold run_tlbi in Hrun.
  VMViews.invert; subst.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply recipients_pos in H; [|exact Hok] end.
  all: unfold pp_pos in *; cbn in *; pos_close.
Qed.

Lemma run_take_exception_pos tid imem fault vmax ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (run_take_exception tid imem fault vmax ppst) →
  pp_pos ppst'.
Proof.
  intros Hok Hrun. unfold run_take_exception in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [inv [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [compose] in Hrun.
  destruct (IIS.inv_time (PPState.iis ppst)); eapply run_cse_pos; eassumption.
Qed.

Lemma run_trans_start_pos tid imem start ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (run_trans_start tid imem start ppst) →
  pp_pos ppst'.
Proof.
  destruct ppst as [ts mem iis]. intros Hts Hrun. unfold run_trans_start in Hrun.
  VMViews.invert; subst; cbn in *.
  all: try (match goal with H : Exec.elem_of_results _ (read_sreg_indirect ?reg ?racc ?st) |- _ =>
    unfold read_sreg_indirect in H; VMViews.invert; subst; cbn in * end).
  all: pos_close.
Qed.

Lemma run_trans_end_pos trans_end st st' r :
  Exec.elem_of_results (st', r) (run_trans_end trans_end st) →
  TState.tlb st'.1 = TState.tlb st.1.
Proof.
  destruct st as [ts iis]. intros Hrun. unfold run_trans_end in Hrun.
  VMViews.invert; subst; reflexivity.
Qed.

Lemma run_outcome_pos n tid imem out ppst ppst' r :
  pp_pos ppst → Exec.elem_of_results (ppst', r) (run_outcome n tid imem out ppst) → pp_pos ppst'.
Proof.
  intros Hok H. funelim (run_outcome n tid imem out ppst).
  all: rewrite <- Heqcall in H.
  all: VMViews.invert; subst.
  all: try exact Hok.
  all: try (match goal with H0 : Exec.elem_of_results _ (run_reg_read ?reg ?racc ?st) |- _ =>
    apply run_reg_read_pos in H0; unfold pp_pos in *; match goal with p : PPState.t _ _ _ |- _ => destruct p end; match goal with x : (TState.t * IIS.t)%type |- _ => destruct x end; cbn in *; subst; exact Hok end).
  all: try (match goal with H0 : Exec.elem_of_results _ (run_trans_end ?trans ?st) |- _ =>
    apply run_trans_end_pos in H0; unfold pp_pos in *; match goal with p : PPState.t _ _ _ |- _ => destruct p end; match goal with x : (TState.t * IIS.t)%type |- _ => destruct x end; cbn in *;
    apply (ts_pos_eq _ _ H0); exact Hok end).
  all: try (eapply run_reg_write_pos; eassumption).
  all: try (eapply read_mem_explicit_pos; eassumption).
  all: try (eapply read_pte_pos; eassumption).
  all: try (eapply write_mem_pos; eassumption).
  all: try (eapply run_trans_start_pos; eassumption).
  all: try (eapply run_barrier_pos; eassumption).
  all: try (eapply run_cse_pos; eassumption).
  all: try (eapply run_take_exception_pos; eassumption).
  all: try (eapply run_tlbi_pos; eassumption).
  all: match goal with p : PPState.t _ _ _ |- _ => destruct p end; cbn in *; pos_close.
Qed.

Theorem instruction_pos n (tid : fin n) imem {A} (mon : iMon A) ppst ppst' ret :
  pp_pos ppst → Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' n tid imem) mon ppst) →
  pp_pos ppst'.
Proof.
  revert ppst ppst' ret. induction mon as [a|call k IH]; intros ppst ppst' ret Hok Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hok.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      exact (IH r mid ppst' ret (run_outcome_pos n tid imem out ppst mid _ Hok Hout) Htail).
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

Theorem init_pos tid imem iregs ts : TState.init tid imem iregs = Ok ts → ts_pos ts.
Proof.
  unfold TState.init, othrow, guard_or, mbind, result_bind, fmap, result_fmap.
  destruct (reg_lookup CurrentEL iregs); [|discriminate]. cbn.
  match goal with |- context[match ?d with left _ => _ | right _ => _ end] => destruct d end;
    cbn; [|discriminate].
  destruct (reg_lookup SCTLR_EL1 iregs); [|discriminate]. cbn.
  match goal with |- context[if ?b then _ else _] => destruct b end.
  - destruct (TLB.init tid imem iregs) as [cache|] eqn:Hinit; [|discriminate]. cbn.
    intro Hts. injection Hts as <-. intros c Hc. cbn in Hc. injection Hc as <-.
    eapply pos_tlb_init; exact Hinit.
  - intro Hts. injection Hts as <-. intros c Hc. discriminate.
Qed.

(** * Machine states *)

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Definition state_pos (st : state) := ∀ tid, ts_pos (PState.tstate tid st).

Lemma from_archState_pos ms st : PState.from_archState prom ms = Ok st → state_pos st.
Proof.
  unfold PState.from_archState.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn. injection 1 as <-.
  intro tid. unfold PState.tstate. cbn.
  eapply init_pos. exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid).
Qed.

Lemma promise_pos ev st st' : state_pos st → PState.promise prom ev st = Ok st' → state_pos st'.
Proof.
  intros Hok. unfold PState.promise.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn. injection 1 as <-.
  intro tid. unfold PState.tstate. cbn.
  pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid) as Hts. cbn in Hts.
  eapply emit_promise_pos; [| |exact Hts]; [|apply Hok]. destruct st. cbn. lia.
Qed.

Lemma broadcast_pos (owner : fin n) imem base extra (states states' : vec TState.t n) :
  (∀ i, ts_pos (states !!! i)) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states' →
  ∀ i, ts_pos (states' !!! i).
Proof.
  intro Hpre. revert states'. induction extra as [|ev extra IH]; intros states' Hrun.
  - injection Hrun as <-. exact Hpre.
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid;
      [|discriminate].
    cbn [mbind result_bind] in Hrun. pose proof (IH mid eq_refl) as Hrest.
    pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun) as Hlook.
    intro i. specialize (Hlook i). cbn in Hlook. destruct (decide (i = owner)).
    + injection Hlook as <-. apply Hrest.
    + eapply emit_promise_pos; [| |exact Hlook]; [cbn; lia|apply Hrest].
Qed.

Theorem run_tid_pos isem (tid : fin n) st st' :
  state_pos st → Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) → state_pos st'.
Proof.
  intros Hok Hrun.
  destruct (run_tid_broadcast_decompose prom isem tid st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  assert (Hts : pp_pos (PPState.Make ts mem iis))
    by (eapply instruction_pos; [|exact Hinst]; exact (Hok tid)).
  unfold pp_pos in Hts. cbn in Hts.
  intro i. unfold PState.tstate. cbn. revert i. eapply broadcast_pos; [|exact Hstates].
  intro i. destruct (decide (i = tid)) as [->|Hne].
  - rewrite vlookup_insert. exact Hts.
  - rewrite vlookup_insert_ne by (intros ->; contradiction). apply Hok.
Qed.

End Machine.

End VMSwapPos.
