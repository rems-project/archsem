(******************************************************************************)
(* Replaying one actual Sail VM instruction after a promise                   *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstMemoryCurrent PromiseFirstSailCurrent PromiseFirstVMExecutionCurrent
  PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheIndexed PromiseFirstSailVMCacheTraversal
  PromiseFirstSailVMViews PromiseFirstSailVMReplay PromiseFirstSailVMTranslation
  PromiseFirstSailVMTransEnd PromiseFirstSailVMCacheSim PromiseFirstSailVMDirect
  PromiseFirstSailVMNormalization PromiseFirstSailVMGuards PromiseFirstSailNoFuel
  PromiseFirstSailVMCacheLastTLBI PromiseFirstSailVMCacheContext PromiseFirstSailRead
  PromiseFirstSailFulfilled PromiseFirstSailVMTLBINormalization PromiseFirstSailVMCacheState
  PromiseFirstSailVMCacheHistory PromiseFirstSailVMCacheExchange PromiseFirstFreshBroadcast.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** This file discharges the fixed-history clause of
    [VMNormalization.VMInstructionPromiseReplay] down to one obligation per
    outcome handler ([VMInstructionReplay.StepReplay]).

    - [VMFillTotal]: delivering an event to a valid cache never fails, except
      for a write crossing a page, which fails on every cache.
    - [VMTLBShape]: no outcome removes the thread cache.
    - [VMEmit]: delivery acts only on the promise sets and the cache.
    - [VMInstructionReplay]: delivery before an instruction succeeds when
      delivery after it succeeds, and the replay of a fixed-history instruction
      composes from per-outcome replays ([fixed_history_replay]). The
      replayed state relates to the original one through [Exact]: the event is
      on top of memory, the thread state has received it, the current
      translation may end later and its invalidation deadline may move after
      the original history. A delivered TLBI of another thread moves that
      deadline, which is why the replay obligation does not relate IIS. *)


Module VMFillTotal.
Import VMPromising.
#[local] Existing Instance TLB.Decision_affects.
Local Notation action A := (stateT TLB.t (result string) A).
Local Notation valid := VMCacheIndexed.valid.

Definition total {A} (Q : A → Prop) (run : action A) :=
  ∀ c, valid c → ∃ c' a, run c = Ok (c', a) ∧ Q a.

Lemma total_ret {A} (Q : A → Prop) a : Q a → total Q (mret a).
Proof. intros Hq c Hc. exists c, a. split; [reflexivity|exact Hq]. Qed.
Lemma total_bind {A B} (Q : A → Prop) (R : B → Prop) (m : action A) (k : A → action B) :
  total Q m → VMCacheIndexed.preserves m → (∀ a, Q a → total R (k a)) → total R (m ≫= k).
Proof.
  intros Hm Hp Hk c Hc. destruct (Hm c Hc) as [c1 [a [Hrun Hq]]].
  destruct (Hk a Hq c1 (Hp c c1 a Hc Hrun)) as [c2 [b [Hrun2 Hr]]].
  exists c2, b. split; [|exact Hr].
  unfold mbind, st_bind, result_bind. rewrite Hrun. exact Hrun2.
Qed.
Lemma total_fmap {A B} (Q : A → Prop) (R : B → Prop) (f : A → B) (m : action A) :
  total Q m → (∀ a, Q a → R (f a)) → total R (f <$> m).
Proof.
  intros Hm Hf c Hc. destruct (Hm c Hc) as [c1 [a [Hrun Hq]]].
  exists c1, (f a). split; [|apply Hf, Hq].
  unfold fmap, st_fmap, result_fmap. rewrite Hrun. reflexivity.
Qed.
Lemma total_get {A} (proj : TLB.t → A) : total (λ _, True) (mget proj).
Proof. intros c Hc. exists c, (proj c). split; [reflexivity|exact I]. Qed.
Lemma total_weaken {A} (Q R : A → Prop) (m : action A) :
  total Q m → (∀ a, Q a → R a) → total R m.
Proof. intros Hm Hw c Hc. destruct (Hm c Hc) as [c1 [a [H Hq]]]. eauto. Qed.
Lemma total_mapM {A B} (Q : B → Prop) (f : A → action B) xs :
  (∀ x, x ∈ xs → total Q (f x)) → (∀ x, VMCacheIndexed.preserves (f x)) →
  total (Forall Q) (mapM f xs).
Proof.
  intros Hf Hp. induction xs as [|x xs IH]; cbn [mapM].
  - apply total_ret. constructor.
  - eapply total_bind; [apply Hf; set_solver|apply Hp|]. intros b Hb.
    eapply total_bind; [apply IH; intros; apply Hf; set_solver|apply VMCacheIndexed.preserves_mapM, Hp|].
    intros bs Hbs. apply total_ret. constructor; assumption.
Qed.
Lemma total_set {A} (proj : TLB.t → A) `{Setter _ _ proj} (f : A → A) :
  total (λ _, True) (mset proj f).
Proof. intros c Hc. exists (set proj f c), (). split; [reflexivity|exact I]. Qed.

Lemma total_fill_entry time fe : total (λ _, True) (TLB.fill_entry time fe).
Proof.
  intros c Hc. destruct (VMCacheRefill.fill_entry_total time fe c) as [c' [l H]].
  exists c', l. split; [exact H|exact I].
Qed.

(** A table entry and its level lower bound. *)
Definition deep (k : nat) (fe : TLB.FE.t) :=
  TLB.FE.is_table fe ∧ k ≤ fin_to_nat (TLB.FE.lvl fe).

Lemma table_lvl fe : TLB.FE.is_table fe → fin_to_nat (TLB.FE.lvl fe) ≤ 2.
Proof.
  intro Ht. change (is_table (TLB.FE.lvl fe) (TLB.FE.pte fe)) in Ht. destruct Ht as [Hne _].
  revert Hne. generalize (TLB.FE.lvl fe). intro l. unfold leaf_lvl.
  repeat (inv_fin l; [intros; cbn; lia|intro l]). inv_fin l; [|intro l; inv_fin l].
  intros Hne. exfalso. apply Hne. reflexivity.
Qed.
Lemma child_lvl_table fe : TLB.FE.is_table fe →
  ∃ clvl, child_lvl (TLB.FE.lvl fe) = Some clvl ∧ fin_to_nat clvl = S (fin_to_nat (TLB.FE.lvl fe)).
Proof.
  intro Ht. pose proof (table_lvl fe Ht) as Hle. revert Hle.
  generalize (TLB.FE.lvl fe). intro l.
  inv_fin l; [|intro l; inv_fin l; [|intro l; inv_fin l; [|intro l; inv_fin l; [|intro l; inv_fin l]]]].
  all: intros; first [eexists; split; reflexivity | cbn in *; lia].
Qed.

Lemma total_guard (err : string) (P : Prop) `{Decision P} : P → total (λ _, True) (guard_or err P).
Proof.
  intro Hp. unfold guard_or. destruct (decide P) as [p|]; [|contradiction].
  apply (total_ret (λ _, True)). exact I.
Qed.

Lemma append_ok fe idx pte : TLB.FE.is_table fe → ∃ child, TLB.FE.append fe idx pte = Ok child.
Proof.
  intro Ht. destruct (child_lvl_table fe Ht) as [clvl [Hc _]].
  unfold TLB.FE.append. destruct (inspect (child_lvl (TLB.FE.lvl fe))) as [[l|] Hl];
    [eexists; reflexivity|congruence].
Qed.

Lemma total_fill_from_entry imem mem time fe k :
  deep k fe → total (Forall (deep (S k))) (TLB.fill_from_entry imem mem time fe).
Proof.
  intros [Htab Hk]. unfold TLB.fill_from_entry.
  destruct (child_lvl_table fe Htab) as [clvl [Hc Hlvl]].
  eapply total_bind; [|apply VMCacheIndexed.preserves_guard|].
  { apply total_guard, Htab. }
  intros _ _. eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|].
  intros indexes _.
  eapply total_bind; [|apply VMCacheIndexed.preserves_othrow|].
  { rewrite Hc. apply (total_ret (λ c, c = clvl)). reflexivity. }
  intros ? ->.
  eapply total_fmap; [apply (total_mapM (Forall (deep (S k))))|].
  3: { intros lists Hlists. apply Forall_concat. exact Hlists. }
  2: { intro idx. VMCacheIndexed.solve_index. }
  intros idx _. cbv beta.
  destruct (Memory.read_word _ imem mem time) as [memval|err];
    [|apply total_ret; constructor].
  destruct (decide (is_tlb_fillable clvl memval)); [|apply total_ret; constructor].
  destruct (append_ok fe idx memval Htab) as [child Happ].
  eapply total_bind; [|apply VMCacheIndexed.preserves_lift|].
  { rewrite Happ. apply (total_ret (λ x, x = child)). reflexivity. }
  intros ? ->.
  eapply total_bind; [apply total_fill_entry|apply VMCacheIndexed.preserves_fill_entry|].
  intros [] _; [|apply total_ret; constructor].
  destruct (decide (is_table clvl memval)) as [Ht|]; [|apply total_ret; constructor].
  apply total_ret. constructor; [|constructor]. split.
  - apply (proj2 (VMCacheTraversal.append_table fe idx memval child clvl Hc Happ)), Ht.
  - rewrite (VMCacheTraversal.append_level fe idx memval child clvl Hc Happ). lia.
Qed.

Lemma total_fill_from_entries_step imem mem time entries k :
  Forall (deep k) entries →
  total (Forall (deep (S k))) (TLB.fill_from_entries_step imem mem time entries).
Proof.
  intro Hall. unfold TLB.fill_from_entries_step.
  eapply total_fmap; [apply (total_mapM (Forall (deep (S k))))|].
  - intros fe Hin. apply total_fill_from_entry. rewrite Forall_forall in Hall. apply Hall. apply list_elem_of_In, Hin.
  - intro fe. apply VMCacheIndexed.fill_from_entry.
  - intros lists Hlists. apply Forall_concat. exact Hlists.
Qed.

Lemma deep_three_nil entries : Forall (deep 3) entries → entries = [].
Proof.
  destruct entries as [|fe entries]; [reflexivity|].
  intro H. inversion H as [|? ? [Ht Hk] _]; subst. pose proof (table_lvl fe Ht). lia.
Qed.

Lemma total_fill_from_entries imem mem time entries :
  Forall (deep 0) entries → total (λ _, True) (TLB.fill_from_entries imem mem time entries).
Proof.
  intro Hall. unfold TLB.fill_from_entries.
  eapply total_bind; [apply (total_fill_from_entries_step _ _ _ _ 0 Hall)|
    apply VMCacheIndexed.fill_from_entries_step|]. intros e1 H1.
  eapply total_bind; [apply (total_fill_from_entries_step _ _ _ _ 1 H1)|
    apply VMCacheIndexed.fill_from_entries_step|]. intros e2 H2.
  eapply total_bind; [apply (total_fill_from_entries_step _ _ _ _ 2 H2)|
    apply VMCacheIndexed.fill_from_entries_step|]. intros e3 H3.
  rewrite (deep_three_nil e3 H3). unfold guard_or'.
  eapply total_bind; [|apply VMCacheIndexed.preserves_guard|].
  { apply total_guard. reflexivity. }
  intros _ _. apply total_ret. exact I.
Qed.

Lemma total_fill_root imem mem time roots :
  total (Forall (deep 0)) (TLB.fill_root imem mem time roots).
Proof.
  unfold TLB.fill_root.
  eapply total_fmap; [apply (total_mapM (Forall (deep 0)))|].
  3: { intros lists Hlists. apply Forall_concat. exact Hlists. }
  2: { intros [[asid ttbr] upper]. VMCacheIndexed.solve_index. }
  intros [[asid ttbr] upper] _. cbv beta.
  eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros indexes _.
  eapply total_fmap; [apply (total_mapM (Forall (deep 0)))|].
  3: { intros lists Hlists. apply Forall_concat. exact Hlists. }
  2: { intro idx. VMCacheIndexed.solve_index. }
  intros idx _. cbv beta.
  destruct (Memory.read_word _ imem mem time) as [memval|err]; [|apply total_ret; constructor].
  destruct (decide (is_table 0%fin memval)) as [Ht|]; [|apply total_ret; constructor].
  eapply total_bind; [apply total_fill_entry|apply VMCacheIndexed.preserves_fill_entry|].
  intros [] _; apply total_ret; [|constructor].
  constructor; [|constructor]. split; [exact Ht|cbn; lia].
Qed.

Lemma total_relevant asids page :
  total (Forall (deep 0)) (TLB.get_relevant_entries asids page).
Proof.
  intros c Hc. eexists c, _. split; [reflexivity|].
  apply Forall_forall. intros fe Hin. apply list_elem_of_In in Hin.
  apply list_elem_of_filter in Hin as [_ Hin].
  destruct (Hc page) as [_ Hmem]. apply Hmem in Hin as [Ht _]. split; [exact Ht|lia].
Qed.

Definition ev_ok (ev : Ev.t) : Prop :=
  match ev with
  | Ev.Msg msg => pa_to_pn (Msg.addr msg) =
      pa_to_pn (addr_addN (Msg.addr msg) (N.pred (Msg.size msg)))
  | _ => True
  end.

Lemma total_fill_from_roots imem mem time roots :
  total (λ _, True) (TLB.fill_from_roots imem mem time roots).
Proof.
  unfold TLB.fill_from_roots.
  eapply total_bind; [apply total_fill_root|apply VMCacheIndexed.fill_root|].
  intros entries Hall. apply total_fill_from_entries, Hall.
Qed.

Lemma total_fill_tlbi imem mem time roots tlbi :
  total (λ _, True) (TLB.fill_tlbi imem mem time roots tlbi).
Proof.
  unfold TLB.fill_tlbi. destruct (TLBI.last tlbi).
  - eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros ? _.
    eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros entries _.
    eapply total_bind.
    + eapply total_fmap; [apply (total_mapM (Forall (deep 0)))|].
      3: { intros lists Hlists. apply Forall_concat. exact Hlists. }
      2: { intro fe. apply VMCacheIndexed.preserves_bind; [apply VMCacheIndexed.preserves_alter|].
           intro. apply VMCacheIndexed.relevant_entries. }
      intros fe _. cbv beta.
      eapply total_bind; [apply total_set|apply VMCacheIndexed.preserves_alter|].
      intros _ _. apply total_relevant.
    + apply VMCacheIndexed.preserves_fmap, VMCacheIndexed.preserves_mapM. intro fe.
      apply VMCacheIndexed.preserves_bind; [apply VMCacheIndexed.preserves_alter|].
      intro. apply VMCacheIndexed.relevant_entries.
    + intros parents Hall. apply total_fill_from_entries, Hall.
  - eapply total_bind; [apply total_set|apply VMCacheIndexed.preserves_map_fe|].
    intros _ _. apply total_fill_from_roots.
Qed.

Lemma total_fill_write imem mem time roots msg :
  ev_ok (Ev.Msg msg) → total (λ _, True) (TLB.fill_write imem mem time roots msg).
Proof.
  intro Hok. unfold TLB.fill_write.
  eapply total_bind; [apply total_guard, Hok|apply VMCacheIndexed.preserves_guard|].
  intros _ _.
  eapply total_bind; [apply total_fill_root|apply VMCacheIndexed.fill_root|]. intros l0 H0.
  eapply total_bind; [apply total_relevant|apply VMCacheIndexed.relevant_entries|]. intros l1 H1.
  apply total_fill_from_entries. apply Forall_app. split; assumption.
Qed.

Theorem total_fill_promise tid imem mem ev :
  ev_ok ev → total (λ _, True) (TLB.fill_promise tid imem mem ev).
Proof.
  intro Hok. unfold TLB.fill_promise.
  eapply total_bind; [apply total_get|apply VMCacheIndexed.preserves_get|]. intros roots _.
  unfold TLB.fill_event. destruct ev as [msg|tlbi recipient epoch].
  - apply total_fill_write, Hok.
  - destruct (decide (tid = recipient)); [apply total_fill_tlbi|apply total_ret; exact I].
Qed.

Lemma fill_promise_ev_ok tid imem mem ev c c' :
  TLB.fill_promise tid imem mem ev c = Ok (c', ()) → ev_ok ev.
Proof.
  destruct ev as [msg|]; [|intros; exact I]. cbn [ev_ok].
  unfold TLB.fill_promise, TLB.fill_event, TLB.fill_write.
  unfold mbind, st_bind, result_bind. cbn -[guard_or].
  unfold guard_or. destruct (decide _) as [Hp|]; [intros; exact Hp|discriminate].
Qed.
End VMFillTotal.


Module VMTLBShape.
Import VMPromising.
#[local] Typeclasses Transparent view UMPromising.view.

Definition has_tlb (ts : TState.t) := is_Some (TState.tlb ts).

Lemma run_tlb_shape upd ts ts' : TState.run_tlb upd ts = Ok ts' → has_tlb ts → has_tlb ts'.
Proof.
  intros H Hs. apply VMReadReplay.run_tlb_frame in H as Hf.
  unfold TState.run_tlb in H. unfold has_tlb in *. destruct (TState.tlb ts) as [c|]; [|by destruct Hs].
  destruct (upd c) as [[c' []]|]; cbn in H; [|discriminate]. injection H as <-. eexists; reflexivity.
Qed.
Lemma process_event_shape tid imem mem ev ts ts' :
  TState.process_event tid imem mem ev ts = Ok ts' → has_tlb ts → has_tlb ts'.
Proof. apply run_tlb_shape. Qed.
Lemma cse_shape imem mem tid v ts ts' :
  TState.cse imem mem tid v ts = Ok ts' → has_tlb ts → has_tlb ts'.
Proof.
  unfold TState.cse. unfold mbind, result_bind.
  destruct (TState.run_tlb _ _) as [t|] eqn:H; [|discriminate]. intros [= <-] Hs.
  eapply run_tlb_shape; [exact H|exact Hs].
Qed.
Lemma add_wsreg_shape tid imem mem sreg val v ts ts' :
  TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → has_tlb ts → has_tlb ts'.
Proof.
  unfold TState.add_wsreg. unfold mbind, result_bind.
  destruct (TState.run_tlb _ _) as [t|] eqn:H; [|discriminate]. intros [= <-] Hs.
  apply run_tlb_shape in H; [|exact Hs]. exact H.
Qed.
Lemma set_reg_shape r rv ts ts' : TState.set_reg r rv ts = Some ts' → has_tlb ts → has_tlb ts'.
Proof. unfold TState.set_reg. case_decide; [intros [= <-]; exact id|discriminate]. Qed.

Lemma tlb_update_cohs avs ts : TState.tlb (TState.update_cohs avs ts) = TState.tlb ts.
Proof. induction avs as [|[a v] avs IH]; [reflexivity|]. cbn. exact IH. Qed.
Lemma tlb_update_tcohs asid offs v ts : TState.tlb (TState.update_tcohs asid offs v ts) = TState.tlb ts.
Proof. induction offs as [|o offs IH]; [reflexivity|]. cbn. exact IH. Qed.
Lemma tlb_set_fwdbs addrs n (data : bv n) time vdata xcl ts :
  TState.tlb (TState.set_fwdbs addrs data time vdata xcl ts) = TState.tlb ts.
Proof.
  unfold TState.set_fwdbs. generalize (zip addrs (bv_to_bytes 8 data)) as l. intro l.
  revert ts. induction l as [|[a b] l IH]; intro ts; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.
Ltac shape_side := unfold has_tlb, TState.update, TState.update2 in *; cbn in *; assumption.
Ltac shape_finish :=
  intros; unfold has_tlb in *; cbn [PPState.state PPState.mem PPState.iis fst snd set setv] in *;
  repeat match goal with
  | H : Some _ = TState.set_reg _ _ _ |- _ => symmetry in H
  | H : TState.cse _ _ _ _ ?t = Ok ?t' |- _ => apply cse_shape in H; [|shape_side]
  | H : TState.add_wsreg _ _ _ _ _ _ ?t = Ok ?t' |- _ => apply add_wsreg_shape in H; [|shape_side]
  | H : TState.process_event _ _ _ _ ?t = Ok ?t' |- _ => apply process_event_shape in H; [|shape_side]
  | H : TState.set_reg _ _ ?t = Some ?t' |- _ => apply set_reg_shape in H; [|shape_side]
  end; unfold has_tlb, TState.update, TState.update2 in *; cbn in *; subst; try assumption;
  do 6 try (progress (cbv [set TState.clear_xclb TState.set_xclb setv]; cbn; rewrite ?tlb_update_cohs, ?tlb_update_tcohs, ?tlb_set_fwdbs)); try assumption.

Definition pshape (p : PPState.t TState.t Ev.t IIS.t) := has_tlb (PPState.state p).

Lemma run_cse_shape tid imem vmax p p' r :
  Exec.elem_of_results (p', r) (run_cse tid imem vmax p) → pshape p → pshape p'.
Proof. destruct p as [ts mem iis]. unfold pshape, run_cse. intro Hrun. VMViews.invert. all: shape_finish. Qed.
Lemma run_barrier_shape tid imem b vmax p p' r :
  Exec.elem_of_results (p', r) (run_barrier tid imem b vmax p) → pshape p → pshape p'.
Proof.
  destruct p as [ts mem iis]. unfold run_barrier. intro Hrun. VMViews.invert.
  all: try (eapply run_cse_shape; eassumption). all: unfold pshape; shape_finish.
Qed.
Lemma run_take_exception_shape tid imem f vmax p p' r :
  Exec.elem_of_results (p', r) (run_take_exception tid imem f vmax p) → pshape p → pshape p'.
Proof.
  destruct p as [ts mem iis]. unfold run_take_exception. intro Hrun. VMViews.invert.
  all: eapply run_cse_shape; eassumption.
Qed.
Lemma run_reg_write_shape tid imem reg racc val p p' r :
  Exec.elem_of_results (p', r) (run_reg_write tid imem reg racc val p) → pshape p → pshape p'.
Proof. destruct p as [ts mem iis]. unfold pshape, run_reg_write. intro Hrun. VMViews.invert. all: shape_finish. Qed.
Lemma read_mem_explicit_shape imem addr size macc p p' r :
  Exec.elem_of_results (p', r) (read_mem_explicit imem addr size macc p) → pshape p → pshape p'.
Proof. destruct p as [ts mem iis]. unfold pshape, read_mem_explicit. intro Hrun. VMViews.invert. all: shape_finish. Qed.
Lemma read_pte_shape p p' r :
  Exec.elem_of_results (p', r) (read_pte p) → pshape p → pshape p'.
Proof. destruct p as [ts mem iis]. unfold pshape, read_pte. intro Hrun. VMViews.invert. all: shape_finish. Qed.
Lemma write_mem_shape tid imem addr size macc data p p' r :
  Exec.elem_of_results (p', r) (write_mem tid imem addr size macc data p) → pshape p → pshape p'.
Proof. destruct p as [ts mem iis]. unfold pshape, write_mem. intro Hrun. VMViews.invert. all: shape_finish. Qed.
Lemma read_sreg_indirect_fst reg racc (st st' : TState.t * IIS.t) vv :
  Exec.elem_of_results (st', vv) (read_sreg_indirect reg racc st) → st'.1 = st.1.
Proof. destruct st as [ts iis]. unfold read_sreg_indirect. intro Hrun. VMViews.invert; reflexivity. Qed.
Lemma run_reg_read_fst reg racc (st st' : TState.t * IIS.t) v :
  Exec.elem_of_results (st', v) (run_reg_read reg racc st) → st'.1 = st.1.
Proof.
  destruct st as [ts iis]. unfold run_reg_read, run_reg_general_read, run_reg_trans_read. intro Hrun.
  VMViews.invert; cbn; try reflexivity.
  all: match goal with H : Exec.elem_of_results _ (read_sreg_indirect _ _ _) |- _ =>
    apply read_sreg_indirect_fst in H; cbn in H; subst; reflexivity end.
Qed.
Lemma run_trans_end_shape te (st st' : TState.t * IIS.t) v :
  Exec.elem_of_results (st', v) (run_trans_end te st) → has_tlb st.1 → has_tlb st'.1.
Proof. destruct st as [ts iis]. unfold run_trans_end. intro Hrun. VMViews.invert. all: shape_finish. Qed.
Lemma run_trans_start_shape tid imem s p p' r :
  Exec.elem_of_results (p', r) (run_trans_start tid imem s p) → pshape p → pshape p'.
Proof.
  destruct p as [ts mem iis]. unfold pshape, run_trans_start. intro Hrun. VMViews.invert.
  1: apply (read_sreg_indirect_fst TTBR0_EL1 None) in H0; destruct x3 as [ts3 iis3]; cbv in H0; subst ts3.
  all: shape_finish.
Qed.
Lemma materialize_shape tid imem pre tlbi recipient p p' r :
  Exec.elem_of_results (p', r) (materialize_tlbi_for_recipient tid imem pre tlbi recipient p) →
  pshape p → pshape p'.
Proof.
  destruct p as [ts mem iis]. unfold pshape, materialize_tlbi_for_recipient. intro Hrun.
  VMViews.invert. all: shape_finish.
Qed.
Lemma recipients_shape tid imem pre tlbi recipients acc p p' r :
  Exec.elem_of_results (p', r)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients p) →
  pshape p → pshape p'.
Proof.
  revert acc p. induction recipients as [|recipient recipients IH]; intros acc p Hrun Hs.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hs.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [a [Hstep Htail]]].
    destruct acc as [[vs vo] cr]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    cbv beta iota in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[tm isn] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply IH; [exact Htail|]. eapply materialize_shape; eassumption.
Qed.
Lemma run_tlbi_shape n tid imem viio tlbi p p' r :
  Exec.elem_of_results (p', r) (run_tlbi n tid imem viio tlbi p) → pshape p → pshape p'.
Proof.
  destruct p as [ts mem iis]. unfold run_tlbi. intro Hrun. VMViews.invert.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    intro Hs; apply recipients_shape in H; [|exact Hs] end.
  all: unfold pshape in *; shape_finish.
Qed.

Theorem run_outcome_shape n tid imem out p p' r :
  Exec.elem_of_results (p', r) (run_outcome n tid imem out p) → pshape p → pshape p'.
Proof.
  intros H Hs. funelim (run_outcome n tid imem out p).
  all: rewrite <- Heqcall in H.
  all: VMViews.invert; subst.
  all: try (match goal with H0 : Exec.elem_of_results (?x, _) (run_reg_read _ _ _) |- _ =>
    apply run_reg_read_fst in H0; destruct x as [ts3 iis3]; cbv in H0; subst ts3 end).
  all: try (match goal with H0 : Exec.elem_of_results (?x, _) (run_trans_end _ _) |- _ =>
    apply run_trans_end_shape in H0; [destruct x as [ts3 iis3]; exact H0|exact Hs] end).
  all: try (eapply run_cse_shape; eassumption).
  all: try (eapply run_barrier_shape; eassumption).
  all: try (eapply run_take_exception_shape; eassumption).
  all: try (eapply run_reg_write_shape; eassumption).
  all: try (eapply read_mem_explicit_shape; eassumption).
  all: try (eapply read_pte_shape; eassumption).
  all: try (eapply write_mem_shape; eassumption).
  all: try (eapply run_trans_start_shape; eassumption).
  all: try (eapply run_tlbi_shape; eassumption).
  all: try exact Hs.
Qed.
End VMTLBShape.

Module VMRoots.
Import VMPromising.
#[local] Typeclasses Transparent view UMPromising.view.
Local Notation action A := (stateT TLB.t (result string) A).

Definition rbound bound (c : TLB.t) :=
  Forall (λ e : (bv 16 * bv 64 * bool) * nat, e.2 ≤ bound) (TLB.asid_roots c).
Definition roots_ok bound (ts : TState.t) :=
  match TState.tlb ts with Some c => rbound bound c | None => True end.
Definition pok (p : PPState.t TState.t Ev.t IIS.t) :=
  roots_ok (length (PPState.mem p)) (PPState.state p).

Lemma rbound_mono b b' c : b ≤ b' → rbound b c → rbound b' c.
Proof. intros Hle H. eapply list.Forall_impl; [exact H|]. cbn. lia. Qed.
Lemma roots_ok_mono b b' ts : b ≤ b' → roots_ok b ts → roots_ok b' ts.
Proof. unfold roots_ok. destruct (TState.tlb ts); [apply rbound_mono|auto]. Qed.
Lemma roots_ok_tlb b t t' : TState.tlb t' = TState.tlb t → roots_ok b t → roots_ok b t'.
Proof. unfold roots_ok. intros ->. exact id. Qed.

Definition rstep {A} bound (run : action A) :=
  ∀ c c' x, rbound bound c → run c = Ok (c', x) → rbound bound c'.
Lemma rstep_ret {A} b (x : A) : rstep b (mret x).
Proof.
  intros c c' y H Hr. change (@Ok string _ (c, x) = Ok (c', y)) in Hr.
  injection Hr as <- <-. exact H.
Qed.
Lemma rstep_bind {A B} b (run : action A) (next : A → action B) :
  rstep b run → (∀ x, rstep b (next x)) → rstep b (run ≫= next).
Proof.
  intros Hrun Hnext c c' y Hc Hall. unfold mbind, st_bind, result_bind in Hall.
  destruct (run c) as [[mid x]|err] eqn:Hfirst; [|discriminate].
  exact (Hnext x mid c' y (Hrun c mid x Hc Hfirst) Hall).
Qed.
Lemma rstep_othrow {A} b (err : string) (o : option A) : rstep b (othrow err o).
Proof. destruct o; [apply rstep_ret|]. intros c c' x _ H. discriminate. Qed.
Lemma rstep_some {A B} b (err : string) (v : A) (next : A → action B) :
  rstep b (next v) → rstep b (othrow err (Some v) ≫= next).
Proof. intros H c c' y Hc Hr. exact (H c c' y Hc Hr). Qed.
Lemma rstep_mapM {A B} b (f : A → action B) xs :
  (∀ x, x ∈ xs → rstep b (f x)) → rstep b (mapM f xs).
Proof.
  intro Hf. induction xs as [|x xs IH]; cbn [mapM]; [apply rstep_ret|].
  apply rstep_bind; [apply Hf; left|intro].
  apply rstep_bind; [apply IH; intros y Hy; apply Hf; right; exact Hy|intro]. apply rstep_ret.
Qed.
Lemma rstep_fill_promise b tid imem mem ev : rstep b (TLB.fill_promise tid imem mem ev).
Proof.
  intros c c' [] Hc Hrun. pose proof (VMCacheRoots.fill_promise tid imem mem ev c c' () Hrun) as H.
  unfold VMCacheRoots.config in H. unfold rbound. rewrite H. exact Hc.
Qed.
Lemma rstep_fill_asid_root b tid imem mem root t :
  t ≤ b → rstep b (TLB.fill_asid_root tid imem mem root t).
Proof.
  intros Ht c c' [] Hc Hrun. unfold rbound.
  rewrite (VMCacheExchange.fill_asid_root_roots _ _ _ _ _ _ _ Hrun). constructor; [exact Ht|exact Hc].
Qed.
Lemma rstep_fill_cse b tid imem mem t ttbr0 ttbr1 :
  t ≤ b → rstep b (TLB.fill_cse tid imem mem t ttbr0 ttbr1).
Proof.
  intros Ht c c' [] _ Hrun. unfold rbound.
  rewrite (VMCacheHistory.fill_cse_roots _ _ _ _ _ _ _ _ Hrun).
  destruct ttbr1; repeat constructor; cbn; exact Ht.
Qed.

Lemma run_tlb_roots b run ts ts' :
  rstep b run → roots_ok b ts → TState.run_tlb run ts = Ok ts' → roots_ok b ts'.
Proof.
  intros Hrun Hok Hts. unfold TState.run_tlb in Hts. unfold roots_ok in *.
  destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (run c) as [[c' []]|err] eqn:Hr; cbn in Hts; [|discriminate].
    injection Hts as <-. exact (Hrun c c' () Hok Hr).
  - injection Hts as <-. rewrite Hc. exact I.
Qed.

Lemma process_event_roots b tid imem mem ev ts ts' :
  roots_ok b ts → TState.process_event tid imem mem ev ts = Ok ts' → roots_ok b ts'.
Proof. apply run_tlb_roots, rstep_fill_promise. Qed.

Lemma emit_roots b tid imem mem ev ts ts' :
  roots_ok b ts → TState.emit_promise tid imem mem ev ts = Ok ts' → roots_ok b ts'.
Proof.
  intros Hok He. unfold TState.emit_promise in He. eapply process_event_roots; [|exact He].
  destruct (bool_decide _); [destruct ev|]; exact Hok.
Qed.

Lemma cse_roots b imem mem tid v ts ts' :
  v ≤ b → roots_ok b ts → TState.cse imem mem tid v ts = Ok ts' → roots_ok b ts'.
Proof.
  intros Hv Hok Hcse. unfold TState.cse, mbind, result_bind in Hcse.
  match type of Hcse with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hcse as <-. eapply run_tlb_roots; [| |exact Hmid]; [|exact Hok].
  apply (rstep_bind b (mret ())); [apply rstep_ret|intros []].
  apply (rstep_bind b (othrow _ _)); [apply rstep_othrow|intro].
  apply rstep_fill_cse, Hv.
Qed.

Lemma add_wsreg_roots b tid imem mem sreg val v ts ts' :
  v ≤ b → VMCacheState.roots_bounded b (TState.read_sreg_indirect ts TTBR0_EL1) →
  VMCacheState.roots_bounded b (TState.read_sreg_indirect ts TTBR1_EL1) →
  roots_ok b ts → TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → roots_ok b ts'.
Proof.
  intros Hv H0 H1 Hok Hrun. unfold TState.add_wsreg, mbind, result_bind in Hrun.
  match type of Hrun with (match TState.run_tlb ?run ?state with _ => _ end) = _ =>
    destruct (TState.run_tlb run state) as [mid|err] eqn:Hmid end; [|discriminate].
  injection Hrun as <-. change (roots_ok b mid).
  eapply run_tlb_roots; [| |exact Hmid]; [|exact Hok].
  destruct sreg as [r|r|r|r]; try apply rstep_ret.
  destruct r; try apply rstep_ret; cbv beta iota zeta.
  - apply rstep_bind; [apply rstep_fill_asid_root, Hv|intro].
    apply rstep_bind; [|intro; apply rstep_ret].
    apply rstep_mapM. intros [ttbr1 view] Hin. apply rstep_fill_asid_root.
    specialize (H1 _ Hin). cbn in H1. unfold join, join_nat in *. lia.
  - destruct (TState.read_sreg_indirect ts TTBR0_EL1) as [ttbr0s|] eqn:Hread;
      [|intros c c' x _ Hstep; discriminate].
    apply rstep_some. apply rstep_bind; [|intro; apply rstep_ret].
    apply rstep_mapM. intros [ttbr0 view] Hin. apply rstep_fill_asid_root.
    assert (Hview : view ≤ b) by (apply (H0 (ttbr0, view)); exact Hin).
    unfold join, join_nat in *. lia.
Qed.

Lemma init_roots tid imem iregs ts : TState.init tid imem iregs = Ok ts → roots_ok 0 ts.
Proof.
  unfold TState.init, othrow, guard_or, mbind, result_bind, fmap, result_fmap.
  destruct (reg_lookup CurrentEL iregs); [|discriminate]. cbn.
  match goal with |- context[match ?d with left _ => _ | right _ => _ end] => destruct d end;
    cbn; [|discriminate].
  destruct (reg_lookup SCTLR_EL1 iregs); [|discriminate]. cbn.
  match goal with |- context[if ?b then _ else _] => destruct b end.
  - destruct (TLB.init tid imem iregs) as [cache|] eqn:Hinit; [|discriminate]. cbn.
    intro Hts. injection Hts as <-. unfold roots_ok. cbn.
    unfold TLB.init, othrow, guard_or, mbind, result_bind, fmap, result_fmap in Hinit.
    repeat match type of Hinit with context [match ?x with _ => _ end] =>
      destruct x eqn:?; cbn in Hinit; try discriminate end.
    all: injection Hinit as <-.
    all: match goal with H : TLB.fill_from_roots _ _ _ _ _ = Ok ?v |- _ =>
      destruct v as [c []]; pose proof (VMCacheRoots.fill_from_roots _ _ _ _ _ _ _ H) as Hr;
      unfold VMCacheRoots.config in Hr; unfold rbound; cbn; rewrite Hr; cbn end.
    all: destruct (reg_lookup TTBR1_EL1 iregs); repeat constructor.
  - intro Hts. injection Hts as <-. exact I.
Qed.

Lemma set_reg_tlb r rv t t' : TState.set_reg r rv t = Some t' → TState.tlb t' = TState.tlb t.
Proof. unfold TState.set_reg. case_decide; [intros [= <-]; reflexivity|discriminate]. Qed.

Ltac tlb_eq :=
  cbn; do 3 try (progress (cbv [set TState.clear_xclb TState.set_xclb setv TState.update TState.update2 compose]; cbn;
    rewrite ?VMTLBShape.tlb_update_cohs, ?VMTLBShape.tlb_update_tcohs, ?VMTLBShape.tlb_set_fwdbs));
  repeat match goal with H : TState.tlb _ = TState.tlb _ |- _ => progress rewrite H end;
  reflexivity.

Ltac rfin :=
  cbn [PPState.state PPState.mem PPState.iis] in *;
  repeat match goal with H : ?x = ?y |- _ => is_var x; is_var y; subst x end;
  repeat match goal with
  | H : Some _ = TState.set_reg _ _ _ |- _ => symmetry in H
  | H : TState.set_reg _ _ _ = Some _ |- _ => apply set_reg_tlb in H
  | H : TState.process_event _ _ ?m _ ?t = Ok ?t' |- _ =>
      let Hx := fresh "Hroots" in
      assert (Hx : roots_ok (length m) t')
        by (eapply process_event_roots; [|exact H]; eapply roots_ok_mono;
            [|match goal with Hy : roots_ok _ t |- _ => exact Hy end]; cbn; lia);
      clear H
  end;
  unfold pok in *; cbn [PPState.state PPState.mem PPState.iis fst snd] in *;
  match goal with
  | Hy : roots_ok ?b ?t |- roots_ok ?b' _ =>
      apply (roots_ok_tlb b' t); [tlb_eq|eapply roots_ok_mono; [|exact Hy]; cbn; lia]
  end.

Section Handlers.
Context (tid : nat) (imem : memoryMap).

Lemma run_cse_roots vmax p p' r :
  vmax ≤ length (PPState.mem p) → pok p →
  Exec.elem_of_results (p', r) (run_cse tid imem vmax p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold run_cse. intros Hv Hr Hrun. VMViews.invert.
  match goal with H : _ ∈ TState.cse_candidates _ _ _ |- _ => apply VMViews.cse_candidate_le in H end.
  match goal with H : TState.cse _ _ _ _ _ = Ok ?t |- _ =>
    unfold pok; cbn; eapply cse_roots; [|exact Hr|exact H]; cbn in *; lia end.
Qed.

Lemma run_barrier_roots b vmax p p' r :
  vmax ≤ length (PPState.mem p) → pok p →
  Exec.elem_of_results (p', r) (run_barrier tid imem b vmax p) → pok p'.
Proof.
  intros Hv Hr Hrun. destruct p as [ts mem iis]. unfold run_barrier in Hrun.
  VMViews.invert. all: try solve [eapply run_cse_roots; [| |eassumption]; eassumption].
  all: rfin.
Qed.

Lemma run_take_exception_roots f vmax p p' r :
  vmax ≤ length (PPState.mem p) → VMViews.ok p → pok p →
  Exec.elem_of_results (p', r) (run_take_exception tid imem f vmax p) → pok p'.
Proof.
  intros Hv Hok Hr Hrun. destruct p as [ts mem iis]. unfold run_take_exception in Hrun.
  pose proof (VMViews.ok_inv_time _ _ (proj2 Hok)) as Hi. cbn in Hi.
  VMViews.invert. all: eapply run_cse_roots; [| |eassumption]; [|exact Hr].
  all: cbn; try exact Hv. apply Hi. assumption.
Qed.

Lemma run_reg_write_roots reg racc val p p' r :
  VMViews.ok p → pok p →
  Exec.elem_of_results (p', r) (run_reg_write tid imem reg racc val p) → pok p'.
Proof.
  destruct p as [ts mem iis]. intros [Hts Hiis] Hr Hrun. unfold run_reg_write in Hrun.
  pose proof (VMViews.ok_strict _ _ Hiis). pose proof (VMViews.ok_vcse _ _ Hts).
  pose proof (VMViews.ok_vspec _ _ Hts). pose proof (VMViews.ok_vdsb _ _ Hts).
  unfold pok in Hr. cbn in Hr.
  VMViews.invert.
  all: try match goal with H : TState.read_sreg_direct _ _ = Some ?vv |- _ =>
    pose proof (VMViews.read_sreg_direct_ok _ _ _ _ Hts H) end.
  all: try match goal with H : TState.add_wsreg _ _ _ _ _ _ _ = Ok _ |- _ =>
    eapply add_wsreg_roots in H;
      [| |apply (proj1 (VMViews.roots_ok _ _ Hts))|apply (proj2 (VMViews.roots_ok _ _ Hts))|exact Hr];
      [|cbn in *; unfold join, join_nat in *; lia] end.
  all: rfin.
Qed.

Lemma write_mem_roots addr size macc data p p' r :
  pok p → Exec.elem_of_results (p', r) (write_mem tid imem addr size macc data p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun. unfold write_mem in Hrun.
  VMViews.invert. all: rfin.
Qed.

Lemma materialize_roots pre tlbi recipient p p' r :
  pok p → Exec.elem_of_results (p', r)
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun.
  unfold materialize_tlbi_for_recipient in Hrun. VMViews.invert. all: rfin.
Qed.

Lemma recipients_roots pre tlbi recipients acc p p' r :
  pok p → Exec.elem_of_results (p', r)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients p) → pok p'.
Proof.
  revert acc p. induction recipients as [|recipient recipients IH]; intros acc p Hs Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hs.
  - cbn [foldlM] in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [a [Hstep Htail]]].
    destruct acc as [[vs vo] cr]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    cbv beta iota in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[tm isn] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply IH; [|exact Htail]. eapply materialize_roots; eassumption.
Qed.

Lemma run_tlbi_roots n viio tlbi p p' r :
  pok p → Exec.elem_of_results (p', r) (run_tlbi n tid imem viio tlbi p) → pok p'.
Proof.
  destruct p as [ts mem iis]. intros Hr Hrun. unfold run_tlbi in Hrun. VMViews.invert.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply recipients_roots in H; [|exact Hr] end.
  all: match goal with H : pok ?x |- _ => destruct x; exact H end.
Qed.

Lemma read_explicit_roots addr size macc p p' r :
  pok p → Exec.elem_of_results (p', r) (read_mem_explicit imem addr size macc p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun. unfold read_mem_explicit in Hrun.
  VMViews.invert. all: rfin.
Qed.

Lemma read_pte_roots p p' r : pok p → Exec.elem_of_results (p', r) (read_pte p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun. unfold read_pte in Hrun.
  VMViews.invert. all: rfin.
Qed.

Lemma trans_start_roots s p p' r :
  pok p → Exec.elem_of_results (p', r) (run_trans_start tid imem s p) → pok p'.
Proof.
  destruct p as [ts mem iis]. unfold pok. cbn. intros Hr Hrun. unfold run_trans_start in Hrun.
  VMViews.invert.
  all: try match goal with H : Exec.elem_of_results (?x, ?vv) (read_sreg_indirect ?rg ?ra ?st) |- _ =>
    pose proof (VMTLBShape.read_sreg_indirect_fst rg ra st x vv H) as Hx; clear H;
    destruct x as [ts3 iis3]; cbn in Hx; subst ts3 end.
  all: rfin.
Qed.

Lemma trans_end_tlb te (st st' : TState.t * IIS.t) v :
  Exec.elem_of_results (st', v) (run_trans_end te st) → TState.tlb st'.1 = TState.tlb st.1.
Proof. destruct st as [ts iis]. unfold run_trans_end. intro H. VMViews.invert. all: reflexivity. Qed.
End Handlers.

Theorem run_outcome_roots n tid imem out p p' r :
  VMViews.ok p → pok p → Exec.elem_of_results (p', r) (run_outcome n tid imem out p) → pok p'.
Proof.
  intros Hok Hs H. funelim (run_outcome n tid imem out p).
  all: rewrite <- Heqcall in H.
  all: VMViews.invert; subst.
  all: try (eapply run_barrier_roots; [| |eassumption]; [lia|assumption]).
  all: try (eapply run_cse_roots; [| |eassumption]; [lia|assumption]).
  all: try (eapply run_take_exception_roots; [| | |eassumption]; [lia|assumption|assumption]).
  all: try (eapply run_reg_write_roots; [| |eassumption]; assumption).
  all: try (eapply write_mem_roots; [|eassumption]; assumption).
  all: try (eapply run_tlbi_roots; [|eassumption]; assumption).
  all: try (eapply read_explicit_roots; [|eassumption]; assumption).
  all: try (eapply read_pte_roots; [|eassumption]; assumption).
  all: try (eapply trans_start_roots; [|eassumption]; assumption).
  all: try (match goal with H0 : Exec.elem_of_results (?x, _) (run_reg_read _ _ _) |- _ =>
    apply VMTLBShape.run_reg_read_fst in H0; destruct x; cbn in H0; subst end).
  all: try (match goal with H0 : Exec.elem_of_results (?x, _) (run_trans_end _ _) |- _ =>
    apply trans_end_tlb in H0; destruct x; cbn in H0 end).
  all: try rfin.
  all: match goal with H : pok ?x |- _ => destruct x end.
  all: unfold pok in *; cbn in *.
  all: try (match goal with Hs : roots_ok _ _ |- _ => exact Hs end).
  all: match goal with H0 : TState.tlb ?t = TState.tlb ?s, Hs : roots_ok _ ?s |- _ =>
    exact (roots_ok_tlb _ s t H0 Hs) end.
Qed.

Theorem instruction_roots n (tid : fin n) imem {A} (mon : iMon A) p p' ret :
  VMViews.ok p → pok p →
  Exec.elem_of_results (p', ret) (cinterp (run_outcome' n tid imem) mon p) → pok p'.
Proof.
  revert p p' ret. induction mon as [a|call k IH]; intros p p' ret Hok Hr Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact Hr.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      eapply IH; [eapply VMViews.run_outcome_ok; eassumption|
        eapply run_outcome_roots; eassumption|exact Htail].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t.

Definition state_roots (st : state) :=
  ∀ tid, roots_ok (length (PState.events st)) (PState.tstate tid st).

Lemma from_archState_roots ms st : PState.from_archState prom ms = Ok st → state_roots st.
Proof.
  unfold PState.from_archState.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn. injection 1 as <-.
  intro tid. unfold PState.tstate. cbn. eapply roots_ok_mono; [|eapply init_roots;
    exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid)]. lia.
Qed.

Lemma promise_roots ev st st' : state_roots st → PState.promise prom ev st = Ok st' → state_roots st'.
Proof.
  intros Hok. unfold PState.promise.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; [|discriminate]. cbn. injection 1 as <-.
  intro tid. unfold PState.tstate. cbn.
  pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap tid) as Hts. cbn in Hts.
  eapply emit_roots; [|exact Hts]. eapply roots_ok_mono; [|apply Hok]. destruct st. cbn. lia.
Qed.

Lemma broadcast_roots (owner : fin n) imem base extra (states states' : vec TState.t n) :
  (∀ i, i ≠ owner → roots_ok (length base) (states !!! i)) →
  PState.broadcast_fresh prom owner imem base extra states = Ok states' →
  states' !!! owner = states !!! owner ∧
  ∀ i, i ≠ owner → roots_ok (length (extra ++ base)) (states' !!! i).
Proof.
  intro Hpre. revert states'. induction extra as [|ev extra IH]; intros states' Hrun.
  - injection Hrun as <-. split; [reflexivity|exact Hpre].
  - cbn [PState.broadcast_fresh] in Hrun.
    destruct (PState.broadcast_fresh prom owner imem base extra states) as [mid|err] eqn:Hmid;
      [|discriminate].
    cbn [mbind result_bind] in Hrun. destruct (IH mid eq_refl) as [Hown Hrest].
    pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hrun) as Hlook.
    split.
    + specialize (Hlook owner). cbn in Hlook. rewrite decide_True in Hlook by reflexivity.
      injection Hlook as <-. exact Hown.
    + intros i Hi. specialize (Hlook i). cbn in Hlook. rewrite decide_False in Hlook by exact Hi.
      eapply emit_roots; [|exact Hlook]. eapply roots_ok_mono; [|apply Hrest, Hi]. cbn. lia.
Qed.

Theorem run_tid_roots isem (tid : fin n) st st' :
  VMViews.state_ok st → state_roots st →
  Exec.elem_of_results (st', ()) (PState.run_tid isem prom tid st) → state_roots st'.
Proof.
  intros Hok Hr Hrun.
  destruct (run_tid_broadcast_decompose prom isem tid st st' Hrun)
    as [ts [mem [iis [states [Hinst [Hstates ->]]]]]].
  assert (Hinit : VMViews.ok (PPState.Make (PState.tstate tid st) (PState.events st) IIS.init)).
  { split; [apply Hok|]. eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. lia. }
  pose proof (instruction_roots n tid (PState.initmem st) isem _ _ () Hinit (Hr tid) Hinst) as Hts.
  destruct (VMViews.instruction_ok n tid (PState.initmem st) isem _ _ () Hinit Hinst)
    as [_ [extra Hextra]].
  unfold pok in Hts. cbn in Hts, Hextra. subst mem.
  rewrite length_app, Nat.add_sub, take_app_length in Hstates.
  apply broadcast_roots in Hstates as [Hown Hrest];
    [|intros i Hi; rewrite vlookup_insert_ne; [apply Hr|intros ->; contradiction]].
  intro i. unfold PState.tstate. cbn.
  destruct (decide (i = tid)) as [->|Hne].
  - rewrite Hown, vlookup_insert. exact Hts.
  - apply Hrest, Hne.
Qed.

Lemma run_step_roots isem term fuel st st' :
  VMViews.state_ok st → state_roots st →
  Exec.elem_of_results (st', ()) (@CPState.run_step isem prom n term fuel st) → state_roots st'.
Proof.
  intros Hok Hr Hrun. apply PromiseFirstCurrent.run_step_inv in Hrun
    as [(tid & ev & nst & _ & _ & Hpromise & ->)|(tid & _ & Hrun)].
  - eapply promise_roots; eassumption.
  - eapply run_tid_roots; eassumption.
Qed.

Lemma transition_roots (isem : iMon ()) (term : terminationCondition n) (use_pf : bool) fuel
    (st st' : state) :
  VMViews.state_ok st → state_roots st →
  Exec.elem_of_results (st', None)
    ((if use_pf then CPState.run_transition_promise_first_uncached isem prom term fuel
      else CPState.run_transition isem prom term fuel) st) →
  state_roots st'.
Proof.
  intros Hok Hr Hrun. destruct use_pf.
  - apply (PromiseFirstCurrent.run_transition_promise_first_none_inv (prom := prom)) in Hrun
      as (tid & ev & nst & _ & Hpromise & ->).
    eapply promise_roots; eassumption.
  - apply (PromiseFirstCurrent.run_transition_none_inv (prom := prom)) in Hrun as (next & Hstep & ->).
    eapply run_step_roots; eassumption.
Qed.

Theorem reachable_roots isem term initMs use_pf st :
  PromiseFirstReachable prom isem term initMs use_pf st → state_roots st.
Proof.
  induction 1 as [st Hinit|fuel st st' Hprev IH Hstep].
  - eapply from_archState_roots; eassumption.
  - eapply transition_roots; [|exact IH|exact Hstep].
    eapply VMViews.reachable_ok; exact Hprev.
Qed.
End Machine.

Theorem prefix_roots bbm nondet {n} (term : terminationCondition n) initMs (tid : fin n) imem p mon :
  SailThreadPrefix (VMPromising bbm) nondet term initMs tid imem p mon → VMViews.ok p ∧ pok p.
Proof.
  induction 1 as [use_pf st Hreach _|imem p p' out k ret vpre _ [Hok Hr] Hout|
    imem p choices k i _ IH|imem p _ [Hok Hr] _].
  - split.
    + split; [exact (VMViews.reachable_ok bbm _ _ _ _ _ Hreach tid)|].
      eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. lia.
    + exact (reachable_roots bbm _ _ _ _ _ Hreach tid).
  - split; [eapply VMViews.run_outcome_ok; eassumption|eapply run_outcome_roots; eassumption].
  - exact IH.
  - split; [split; [apply Hok|]|exact Hr].
    eapply VMViews.iis_ok_mono; [|exact VMViews.iis_init]. lia.
Qed.
End VMRoots.

Module VMEmit.
Import VMPromising.
Section EmitSec.
Context (tid : nat) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).
Local Notation emit := (TState.emit_promise tid imem (ev :: mem) ev).

Lemma tlb_pending ts : TState.tlb (VMCacheSim.pending tid (ev :: mem) ev ts) = TState.tlb ts.
Proof. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; reflexivity. Qed.
Lemma emit_pending ts : emit ts = TState.process_event tid imem (ev :: mem) ev (VMCacheSim.pending tid (ev :: mem) ev ts).
Proof. unfold TState.emit_promise, VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; reflexivity. Qed.

Lemma emit_none ts : TState.tlb ts = None → ∃ e, emit ts = Ok e.
Proof.
  intro H. rewrite emit_pending. unfold TState.process_event, TState.run_tlb.
  rewrite tlb_pending, H. eexists; reflexivity.
Qed.
Lemma emit_some_inv ts e c : emit ts = Ok e → TState.tlb ts = Some c →
  ∃ c', TLB.fill_promise tid imem (ev :: mem) ev c = Ok (c', ()).
Proof.
  rewrite emit_pending. unfold TState.process_event, TState.run_tlb. rewrite tlb_pending.
  intros He Hc. rewrite Hc in He.
  destruct (TLB.fill_promise tid imem (ev :: mem) ev c) as [[c' []]|err]; [eauto|discriminate].
Qed.
Lemma emit_some_intro ts c c' : TState.tlb ts = Some c →
  TLB.fill_promise tid imem (ev :: mem) ev c = Ok (c', ()) → ∃ e, emit ts = Ok e.
Proof.
  intros Hc Hf. rewrite emit_pending. unfold TState.process_event, TState.run_tlb.
  rewrite tlb_pending, Hc, Hf. eexists; reflexivity.
Qed.

Lemma pending_fields ts : TState.prom_wr (VMCacheSim.pending tid (ev :: mem) ev ts) =
    ((if bool_decide (Ev.tid ev = tid) then if ev is Ev.Msg _ then [length (ev :: mem)] else [] else [])
      ++ TState.prom_wr ts)%list ∧
  TState.prom_tlbi (VMCacheSim.pending tid (ev :: mem) ev ts) =
    ((if bool_decide (Ev.tid ev = tid) then if ev is Ev.Msg _ then [] else [length (ev :: mem)] else [])
      ++ TState.prom_tlbi ts)%list.
Proof. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; split; reflexivity. Qed.

Lemma pending_frame t : VMCacheSim.pending tid (ev :: mem) ev t =
  setv TState.prom_tlbi (TState.prom_tlbi (VMCacheSim.pending tid (ev :: mem) ev t))
    (setv TState.prom_wr (TState.prom_wr (VMCacheSim.pending tid (ev :: mem) ev t)) t).
Proof. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; destruct t; reflexivity. Qed.

(** Delivery acts only on the promise sets and the cache. *)
Lemma emit_transfer ts ts' issued :
  emit ts = Ok issued → TState.tlb ts' = TState.tlb ts →
  TState.prom_wr ts' = TState.prom_wr ts → TState.prom_tlbi ts' = TState.prom_tlbi ts →
  emit ts' = Ok (VMTransEndReplay.frame (TState.prom_wr issued) (TState.prom_tlbi issued)
    (TState.tlb issued) ts').
Proof.
  rewrite !emit_pending. unfold TState.process_event, TState.run_tlb. rewrite !tlb_pending.
  intros He Ht Hw Hb. rewrite Ht.
  pose proof (pending_fields ts) as [Pw Pb]. pose proof (pending_fields ts') as [Pw' Pb'].
  rewrite Hw in Pw'. rewrite Hb in Pb'. rewrite <- Pw in Pw'. rewrite <- Pb in Pb'.
  rewrite (pending_frame ts'), Pw', Pb'.
  destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (TLB.fill_promise tid imem (ev :: mem) ev c) as [[c' []]|err]; cbn in He |- *;
      [|discriminate]. injection He as <-. reflexivity.
  - cbn in He |- *. injection He as <-. f_equal. unfold VMTransEndReplay.frame.
    rewrite tlb_pending, Hc. destruct ts'; cbn in Ht |- *. subst. reflexivity.
Qed.
End EmitSec.
End VMEmit.


Module VMInstructionReplay.
Import VMPromising VMCacheSim VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Local Notation ppstate := (PPState.t TState.t Ev.t IIS.t).

Lemma pp_sim_trans a b c : pp_sim a b → pp_sim b c → pp_sim a c.
Proof.
  intros (Hm1 & Hi1 & Hs1) (Hm2 & Hi2 & Hs2). split; [congruence|]. split; [congruence|].
  eapply VMNormalization.ts_sim_trans; eassumption.
Qed.

Section Fixed.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Definition emits (ts : TState.t) := ∃ e, TState.emit_promise tid imem (ev :: mem) ev ts = Ok e.

(** The replay state obtained by delivering [ev] to the thread state of an
    original state: memory has [ev] on top, the thread has received [ev], the
    current translation interval may end later and its invalidation deadline
    may move after the original history. *)
Definition Exact (p q0 : ppstate) : Prop :=
  PPState.mem p = mem ∧ ∃ issued stop inv,
    TState.emit_promise tid imem (ev :: mem) ev (PPState.state p) = Ok issued ∧
    (∀ trs, IIS.trs (PPState.iis p) = Some trs → IIS.TransRes.trans_end trs ≤ stop) ∧
    VMTranslationReplay.inv_after (length mem) (IIS.inv_time (PPState.iis p)) inv ∧
    q0 = PPState.Make issued (ev :: mem) (VMTransEndReplay.interval_iis stop inv (PPState.iis p)).

Definition Rel (p q : ppstate) := ∃ q0, Exact p q0 ∧ pp_sim q0 q.

Definition fetch_ok out (p : ppstate) : Prop :=
  match out with
  | MemRead req => is_ifetch req.(MemReq.access_kind) = true → req.(MemReq.size) = 4%N →
      read_imem imem req.(MemReq.address) (ev :: PPState.mem p) =
      read_imem imem req.(MemReq.address) (PPState.mem p)
  | _ => True
  end.

Fixpoint fetches {A} (mon : iMon A) (p : ppstate) : Prop :=
  match mon with
  | Ret _ => True
  | Next (inl out) k => fetch_ok out p ∧
      ∀ p' r pre, Exec.elem_of_results (p', (r, pre)) (run_outcome n tid imem out p) →
        fetches (k r) p'
  | Next (inr _) k => ∀ r, fetches (k r) p
  end.

(** One outcome of a fixed-history instruction replays after the delivery. *)
Definition StepReplay out : Prop :=
  ∀ p p' r q0, VMViews.ok p → Exact p q0 → fetch_ok out p →
    PPState.mem p' = mem → emits (PPState.state p') →
    Exec.elem_of_results (p', r) (run_outcome n tid imem out p) →
    ∃ q0', Exec.elem_of_results (q0', r) (run_outcome n tid imem out q0) ∧ Rel p' q0'.

(** The same obligation for states whose cache roots are bounded by the
    history ([VMRoots.pok]); this holds on every Sail thread prefix. *)
Definition StepReplayR out : Prop :=
  ∀ p p' r q0, VMViews.ok p → VMRoots.pok p → Exact p q0 → fetch_ok out p →
    PPState.mem p' = mem → emits (PPState.state p') →
    Exec.elem_of_results (p', r) (run_outcome n tid imem out p) →
    ∃ q0', Exec.elem_of_results (q0', r) (run_outcome n tid imem out q0) ∧ Rel p' q0'.

Lemma StepReplay_R out : StepReplay out → StepReplayR out.
Proof. intros H p p' r q0 Hok _. exact (H p p' r q0 Hok). Qed.

(** Delivery succeeds before an outcome when it succeeds after it. *)
Definition StepBack out : Prop :=
  ∀ p p' r, VMViews.ok p → Exec.elem_of_results (p', r) (run_outcome n tid imem out p) →
    emits (PPState.state p') → emits (PPState.state p).

Section Compose.
Context (Hstep : ∀ out, StepReplayR out).
Context (Hback : ∀ out, StepBack out).

Lemma rel_step out p p' r q :
  VMViews.ok p → VMRoots.pok p → Rel p q → fetch_ok out p → PPState.mem p' = mem →
  emits (PPState.state p') →
  Exec.elem_of_results (p', r) (run_outcome n tid imem out p) →
  ∃ q', Exec.elem_of_results (q', r) (run_outcome n tid imem out q) ∧ Rel p' q'.
Proof using Hstep.
  intros Hok Hroots [q0 [Hex Hsim]] Hf Hm He Hrun.
  destruct (Hstep out p p' r q0 Hok Hroots Hex Hf Hm He Hrun) as [q0' [Hrun0 [q1 [Hex1 Hsim1]]]].
  destruct (run_outcome_simulation n tid imem out q0 q q0' r Hsim Hrun0) as [q' [Hrun' Hsim']].
  exists q'. split; [exact Hrun'|]. exists q1. split; [exact Hex1|].
  eapply pp_sim_trans; eassumption.
Qed.

Lemma cinterp_back {A} (mon : iMon A) p pf ret :
  VMViews.ok p → Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) mon p) →
  emits (PPState.state pf) → emits (PPState.state p).
Proof using Hback.
  revert p. induction mon as [a|call k IH]; intros p Hok Hrun He.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. exact He.
  - destruct call as [out|[choices]]; cbn in Hrun.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      eapply Hback; [exact Hok|exact Hout|].
      eapply IH; [|exact Htail|exact He]. eapply VMViews.run_outcome_ok; eassumption.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; eassumption.
Qed.

Theorem cinterp_replay {A} (mon : iMon A) p pf ret q :
  fetches mon p → VMViews.ok p → VMRoots.pok p → PPState.mem p = mem →
  Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) mon p) →
  PPState.mem pf = mem → emits (PPState.state pf) → Rel p q →
  ∃ qf, Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) mon q) ∧ Rel pf qf.
Proof using All.
  revert p q. induction mon as [a|call k IH]; intros p q Hf Hok Hroots Hm Hrun Hmf He Hrel.
  - cbn in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    exists q. split; [apply Exec.elem_of_mret|exact Hrel].
  - destruct call as [out|[choices]]; cbn in Hrun, Hf |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct Hf as [Hfo Hfk].
      pose proof (VMViews.run_outcome_ok n tid imem out p mid _ Hok Hout) as Hok'.
      assert (Hmid : PPState.mem mid = mem).
      { destruct (VMViews.outcome_memory_growth n tid imem out p mid _ Hout) as [x1 Hx1].
        destruct (VMFinalCertification.instruction_memory_suffix tid imem (k r) mid pf ret Htail)
          as [x2 Hx2].
        rewrite Hmf, Hx1, Hm, app_assoc in Hx2. apply (f_equal length) in Hx2.
        rewrite length_app in Hx2. destruct (x2 ++ x1)%list eqn:Hx; [|cbn in Hx2; lia].
        apply app_eq_nil in Hx as [_ ->]. rewrite Hx1, Hm. reflexivity. }
      pose proof (cinterp_back (k r) mid pf ret Hok' Htail He) as He'.
      pose proof (VMRoots.run_outcome_roots n tid imem out p mid _ Hok Hroots Hout) as Hroots'.
      destruct (rel_step out p mid (r, pre) q Hok Hroots Hrel Hfo Hmid He' Hout) as [q' [Hq' Hrel']].
      destruct (IH r mid q' (Hfk mid r pre Hout) Hok' Hroots' Hmid Htail Hmf He Hrel')
        as [qf [Hqf Hrelf]].
      exists qf. split; [|exact Hrelf].
      eapply Exec.elem_of_bind_intro; [|exact Hqf].
      apply (Exec.elem_of_fmap_intro _ _ (r, pre) _ fst Hq').
    + apply Exec.elem_of_bind_elim in Hrun as [mid [i [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      destruct (IH i p q (Hf i) Hok Hroots Hm Htail Hmf He Hrel) as [qf [Hqf Hrelf]].
      exists qf. split; [|exact Hrelf].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|exact Hqf].
Qed.
End Compose.

Lemma exact_rel p q0 : VMViews.ok p → Exact p q0 → Rel p q0.
Proof.
  intros Hok Hex. exists q0. split; [exact Hex|].
  destruct Hex as [Hm [issued [stop [inv [He [_ [_ ->]]]]]]].
  split; [reflexivity|]. split; [reflexivity|]. cbn.
  apply (VMNormalization.ts_ok_sim_refl (length (ev :: mem))).
  eapply VMViews.emit_promise; [|apply (proj1 Hok)|exact He]. rewrite Hm. cbn. lia.
Qed.

Lemma step_back out : StepBack out.
Proof.
  intros p p' r Hok Hrun [e He].
  destruct (TState.tlb (PPState.state p)) as [c|] eqn:Hc; [|apply VMEmit.emit_none, Hc].
  destruct (VMTLBShape.run_outcome_shape n tid imem out p p' r Hrun (ex_intro _ c Hc)) as [c' Hc'].
  destruct (VMEmit.emit_some_inv tid imem mem ev _ e c' He Hc') as [c'' Hf].
  pose proof (VMFillTotal.fill_promise_ev_ok _ _ _ _ _ _ Hf) as Hev.
  destruct (VMViews.ok_cache _ _ (proj1 Hok) c Hc) as (_ & _ & Hvalid).
  destruct (VMFillTotal.total_fill_promise tid imem (ev :: mem) ev Hev c Hvalid) as [c2 [[] [Hf2 _]]].
  exact (VMEmit.emit_some_intro tid imem mem ev _ c c2 Hc Hf2).
Qed.

Theorem cinterp_replay_steps {A} (mon : iMon A) p pf ret q :
  (∀ out, StepReplayR out) →
  fetches mon p → VMViews.ok p → VMRoots.pok p → PPState.mem p = mem →
  Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) mon p) →
  PPState.mem pf = mem → emits (PPState.state pf) → Rel p q →
  ∃ qf, Exec.elem_of_results (qf, ret) (cinterp (run_outcome' n tid imem) mon q) ∧ Rel pf qf.
Proof. intro Hstep. apply (cinterp_replay Hstep step_back). Qed.

Lemma cinterp_emits {A} (mon : iMon A) p pf ret :
  VMViews.ok p → Exec.elem_of_results (pf, ret) (cinterp (run_outcome' n tid imem) mon p) →
  emits (PPState.state pf) → emits (PPState.state p).
Proof. apply (cinterp_back step_back). Qed.
End Fixed.

Section Steps.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma interval_none stop inv iis : IIS.trs iis = None →
  VMTransEndReplay.interval_iis stop inv iis = setv IIS.inv_time inv iis.
Proof. destruct iis; cbn. intros ->. reflexivity. Qed.
Lemma interval_some stop inv iis trs : IIS.trs iis = Some trs →
  VMTransEndReplay.interval_iis stop inv iis =
    iis |> setv IIS.trs (Some (setv IIS.TransRes.trans_end stop trs)) |> setv IIS.inv_time inv.
Proof. destruct iis; cbn. intros ->. reflexivity. Qed.

Lemma trans_end_fields te ts iis ts' iis' :
  Exec.elem_of_results ((ts', iis'), ()) (run_trans_end te (ts, iis)) →
  TState.tlb ts' = TState.tlb ts ∧ TState.prom_wr ts' = TState.prom_wr ts ∧
  TState.prom_tlbi ts' = TState.prom_tlbi ts ∧ IIS.trs iis' = None ∧
  IIS.inv_time iis' = IIS.inv_time iis.
Proof.
  intro Hrun. remember (ts', iis') as st' eqn:Hst.
  replace ts' with st'.1 by (subst; reflexivity). replace iis' with st'.2 by (subst; reflexivity).
  clear Hst. unfold run_trans_end in Hrun. VMViews.invert.
  all: repeat split; reflexivity.
Qed.

Lemma step_trans_end te : StepReplay tid imem mem ev (TranslationEnd te).
Proof.
  intros [ts m iis] p' r q0 Hok Hex _ Hm' He' Hrun.
  destruct Hex as [Hm [issued [stop [inv [He [Hstop [Hinv ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv. subst m.
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [[] [Hlift Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  apply Exec.elem_of_liftSt_inv in Hlift as [[ts' iis'] [-> Hte]].
  cbn in Hte.
  destruct (IIS.trs iis) as [trs|] eqn:Htrs.
  2: { exfalso. unfold run_trans_end in Hte. VMViews.invert; cbn in *; congruence. }
  pose proof (trans_end_fields te ts iis ts' iis' Hte) as (Ht & Hw & Hb & Hnone & Hinv').
  pose proof (VMTransEndReplay.translation_end_after_promise tid imem (ev :: mem) ev te ts issued
    iis ts' iis' trs stop inv He Htrs (Hstop trs eq_refl) Hte) as Hrep.
  pose proof (VMEmit.emit_transfer tid imem mem ev ts ts' issued He Ht Hw Hb) as He2.
  eexists. split.
  - simp run_outcome. eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
    apply Exec.elem_of_liftSt. cbn. rewrite (interval_some stop inv iis trs Htrs). exact Hrep.
  - apply exact_rel.
    + eapply (VMViews.run_outcome_ok n tid imem (TranslationEnd te) _ _ (tt, None));
        [exact Hok|]. simp run_outcome.
      eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
      apply Exec.elem_of_liftSt. exact Hte.
    + split; [reflexivity|]. eexists _, 0, inv. split; [exact He2|]. cbn.
      split; [rewrite Hnone; discriminate|]. split; [rewrite Hinv'; exact Hinv|].
      rewrite (interval_none 0 inv iis' Hnone). reflexivity.
Qed.

Lemma guard_discard_bind_intro {St E A} (P : Prop) `{Decision P} st st' (a : A)
    (k : P → Exec.t St E A) :
  P → (∀ p, Exec.elem_of_results (st', a) (k p st)) →
  Exec.elem_of_results (st', a) ((guard_discard P ≫= k) st).
Proof.
  intros Hp Hk. destruct (Exec.elem_of_guard_discard (E := E) st Hp) as [p Hin].
  eapply Exec.elem_of_bind_intro; [exact Hin|apply Hk].
Qed.

Lemma step_announce a : StepReplay tid imem mem ev (MemWriteAddrAnnounce a).
Proof.
  intros [ts m iis] p' r q0 Hok Hex _ Hm' He' Hrun.
  destruct Hex as [Hm [issued [stop [inv [He [Hstop [Hinv ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv. subst m.
  clear Hm' He'. simp run_outcome in Hrun. VMViews.invert.
  match goal with H : TState.no_write_promises_until _ _ |- _ => rename H into Hg end.
  pose proof (VMTransEndReplay.emit_promise_frame _ _ _ _ _ _ He) as Hframe.
  cbn [PPState.state PPState.iis compose] in *.
  assert (Hv : IIS.strict iis ≤ length mem) by apply (VMViews.ok_strict _ _ (proj2 Hok)).
  eexists. split.
  - simp run_outcome.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    apply guard_discard_bind_intro.
    { eapply VMGuardReplay.emit_promise_no_write_promises_until; [exact He|exact Hg|exact Hv]. }
    intros _. eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]. apply Exec.elem_of_mret.
  - apply exact_rel.
    + eapply (VMViews.run_outcome_ok n tid imem (MemWriteAddrAnnounce a)); [exact Hok|].
      simp run_outcome.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
      apply guard_discard_bind_intro; [exact Hg|]. intros _.
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]. apply Exec.elem_of_mret.
    + split; [reflexivity|]. eexists _, stop, inv.
      split; [apply (VMEmit.emit_transfer tid imem mem ev ts _ issued He); reflexivity|].
      split; [exact Hstop|]. split; [exact Hinv|]. cbn.
      rewrite Hframe. reflexivity.
Qed.

Lemma step_fail s : StepReplay tid imem mem ev (GenericFail s).
Proof. intros p p' r q0 _ _ _ _ _ Hrun. simp run_outcome in Hrun. VMViews.invert. Qed.

End Steps.

Section Cse.
Context (tid : nat) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).
Local Notation emit := (TState.emit_promise tid imem (ev :: mem) ev).
Local Notation pend := (VMCacheSim.pending tid (ev :: mem) ev).

Lemma emit_char t e : emit t = Ok e →
  (TState.tlb t = None ∧ e = pend t) ∨
  (∃ c c', TState.tlb t = Some c ∧ TLB.fill_promise tid imem (ev :: mem) ev c = Ok (c', ()) ∧
    e = setv TState.tlb (Some c') (pend t)).
Proof.
  rewrite VMEmit.emit_pending. unfold TState.process_event, TState.run_tlb.
  rewrite VMEmit.tlb_pending. destruct (TState.tlb t) as [c|] eqn:Hc.
  - destruct (TLB.fill_promise tid imem (ev :: mem) ev c) as [[c' []]|err] eqn:Hf;
      cbn; [|discriminate]. intros [= <-]. right. eauto.
  - cbn. intros [= <-]. left. auto.
Qed.

Lemma pend_setv_tlb c t : pend (setv TState.tlb c t) = setv TState.tlb c (pend t).
Proof. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; reflexivity. Qed.
Lemma cse_pre_pend v t : cse_pre v (pend t) = pend (cse_pre v t).
Proof. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; reflexivity. Qed.
Lemma read_sreg_direct_pend t r : TState.read_sreg_direct (pend t) r = TState.read_sreg_direct t r.
Proof. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; reflexivity. Qed.

Lemma cse_replay v ts ts' e' issued :
  v ≤ length mem → (∀ c, TState.tlb ts = Some c → VMCacheIndexed.valid c ∧ VMCacheLastTLBI.unique c) →
  emit ts = Ok issued → TState.cse imem mem tid v ts = Ok ts' → emit ts' = Ok e' →
  ∃ t2, TState.cse imem (ev :: mem) tid v issued = Ok t2 ∧ ts_sim e' t2.
Proof.
  intros Hv Hwf He Hcse He'.
  rewrite <- (setv_tlb_same ts) in Hcse. rewrite cse_shape in Hcse.
  destruct (emit_char ts issued He) as [[Hnone ->]|(c0 & c1 & Hc0 & Hf & ->)].
  - rewrite Hnone in Hcse. unfold TState.run_tlb in Hcse. rewrite tlb_setv in Hcse.
    cbn in Hcse. injection Hcse as <-.
    destruct (emit_char _ e' He') as [[_ ->]|(c & c' & Hc & _)]; [|rewrite tlb_setv in Hc; discriminate].
    rewrite <- (setv_tlb_same (pend ts)), VMEmit.tlb_pending, Hnone, cse_shape.
    unfold TState.run_tlb. rewrite tlb_setv. cbn. eexists. split; [reflexivity|].
    rewrite cse_pre_pend, pend_setv_tlb. apply ts_sim_setv. exact I.
  - destruct (Hwf c0 Hc0) as [Hvalid Hunique].
    rewrite Hc0 in Hcse. unfold TState.run_tlb in Hcse. rewrite tlb_setv in Hcse.
    unfold mbind, result_bind, fmap, result_fmap in Hcse. cbn - [TLB.fill_cse] in Hcse.
    destruct (TState.read_sreg_direct (cse_pre v ts) TTBR0_EL1) as [ttbr0|] eqn:Httbr;
      cbn - [TLB.fill_cse] in Hcse; [|discriminate].
    match type of Hcse with context [TLB.fill_cse ?a ?b ?c ?d ?e ?f c0] =>
      destruct (TLB.fill_cse a b c d e f c0) as [[after []]|err] eqn:Hafter end;
      cbn in Hcse; [|discriminate].
    injection Hcse as <-.
    destruct (emit_char _ e' He') as [[Hn _]|(c & ending & Hc & Hend & ->)];
      [rewrite tlb_setv in Hn; discriminate|]. rewrite tlb_setv in Hc. injection Hc as <-.
    destruct (VMCacheContext.replay_promise_before_cse tid imem mem ev v ttbr0.1
      _ c0 c1 after ending
      Hv Hvalid Hunique Hf Hafter Hend) as [ending' [Hrun Hobs]].
    rewrite cse_shape. unfold TState.run_tlb. rewrite tlb_setv.
    rewrite cse_pre_pend, !read_sreg_direct_pend, Httbr.
    unfold mbind, result_bind, fmap, result_fmap. cbn - [TLB.fill_cse]. rewrite Hrun. cbn.
    eexists. split; [reflexivity|].
    rewrite !pend_setv_tlb, !setv_tlb_twice. apply ts_sim_setv. cbn.
    pose proof (VMCacheIndexed.fill_promise _ _ _ _ _ _ () Hvalid Hf) as Hv1.
    pose proof (VMCacheLastTLBI.unique_fill_promise _ _ _ _ _ _ () Hunique Hf) as Hu1.
    pose proof (VMCacheIndexed.fill_cse _ _ _ _ _ _ _ _ () Hvalid Hafter) as Hva.
    pose proof (VMCacheLastTLBI.unique_fill_cse _ _ _ _ _ _ _ _ () Hunique Hafter) as Hua.
    split; [exact Hobs|]. split.
    + split; [exact (VMCacheIndexed.fill_promise _ _ _ _ _ _ () Hva Hend)|].
      exact (VMCacheLastTLBI.unique_fill_promise _ _ _ _ _ _ () Hua Hend).
    + split; [exact (VMCacheIndexed.fill_cse _ _ _ _ _ _ _ _ () Hv1 Hrun)|].
      exact (VMCacheLastTLBI.unique_fill_cse _ _ _ _ _ _ _ _ () Hu1 Hrun).
Qed.

End Cse.

Section RunCse.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma interval_add stop inv v iis :
  VMTransEndReplay.interval_iis stop inv (IIS.add v iis) =
  IIS.add v (VMTransEndReplay.interval_iis stop inv iis).
Proof. destruct iis; reflexivity. Qed.

Lemma ok_wf p c : VMViews.ok p → TState.tlb (PPState.state p) = Some c →
  VMCacheIndexed.valid c ∧ VMCacheLastTLBI.unique c.
Proof.
  intros Hok Hc. destruct (VMViews.ok_cache _ _ (proj1 Hok) c Hc) as (_ & Hu & Hv). auto.
Qed.

Lemma run_cse_replay vmax vmax' p p' r q0 :
  VMViews.ok p → Exact tid imem mem ev p q0 → vmax ≤ length mem → vmax ≤ vmax' →
  emits tid imem mem ev (PPState.state p') →
  Exec.elem_of_results (p', r) (run_cse tid imem vmax p) →
  ∃ q0', Exec.elem_of_results (q0', r) (run_cse tid imem vmax' q0) ∧ Rel tid imem mem ev p' q0'.
Proof.
  intros Hok Hex Hvmax Hle [e' He'] Hrun.
  destruct p as [ts m iis].
  destruct Hex as [Hm [issued [stop [inv [He [Hstop [Hinv ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv. subst m.
  pose proof (VMViews.ok_strict _ _ (proj2 Hok)) as Hstrict.
  pose proof (proj1 Hok) as Hts.
  unfold run_cse in Hrun. VMViews.invert.
  match goal with H : TState.no_promises_until _ _ |- _ => rename H into Hg end.
  match goal with H : ?x ∈ TState.cse_candidates _ _ _ |- _ => rename H into Hcand; rename x into vpost end.
  match goal with H : TState.cse _ _ _ _ _ = Ok _ |- _ => rename H into Hcse end.
  cbn [PPState.state PPState.mem PPState.iis] in *.
  pose proof (VMViews.cse_candidate_le _ _ _ _ Hcand) as Hvpost.
  cbn in He'.
  assert (Hv7 : vpost ≤ length mem) by lia.
  destruct (cse_replay tid imem mem ev vpost ts _ e' issued Hv7
    (λ c Hc, ok_wf _ c Hok Hc) He Hcse He') as [t2 [Hcse2 Hsim]].
  pose proof (VMTransEndReplay.emit_promise_frame _ _ _ _ _ _ He) as Hframe.
  assert (Hviews : TState.vspec issued = TState.vspec ts ∧ TState.vcse issued = TState.vcse ts ∧
    TState.vdsb issued = TState.vdsb ts ∧ TState.vmsr issued = TState.vmsr ts)
    by (rewrite Hframe; repeat split).
  destruct Hviews as (Hv1 & Hv2 & Hv3 & Hv4).
  assert (Hpre : IIS.strict iis ⊔ ( ( (TState.vspec ts ⊔ TState.vcse ts) ⊔ TState.vdsb ts)
      ⊔ TState.vmsr ts) ≤ length mem).
  { pose proof (VMViews.ok_vspec _ _ Hts). pose proof (VMViews.ok_vcse _ _ Hts).
    pose proof (VMViews.ok_vdsb _ _ Hts). pose proof (VMViews.ok_vmsr _ _ Hts).
    cbn [PPState.mem PPState.state] in *. unfold join, join_nat in *. lia. }
  eexists. split.
  - unfold run_cse.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn [PPState.state PPState.mem PPState.iis].
    change (IIS.strict (VMTransEndReplay.interval_iis stop inv iis)) with (IIS.strict iis).
    rewrite Hv1, Hv2, Hv3, Hv4.
    apply guard_discard_bind_intro.
    { eapply VMGuardReplay.emit_promise_no_promises_until; [exact He|exact Hg|exact Hpre]. }
    intros _.
    eapply Exec.elem_of_bind_intro; [eapply Exec.elem_of_mchoosel|].
    { eapply VMGuardReplay.emit_promise_cse_candidate; [exact He|exact Hvmax|exact Hle|exact Hcand]. }
    eapply Exec.elem_of_bind_intro; [apply exec_lift_result; exact Hcse2|].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]. apply Exec.elem_of_mset.
  - exists (PPState.Make e' (ev :: mem)
      (VMTransEndReplay.interval_iis stop inv (IIS.add vpost iis))).
    split.
    + split; [reflexivity|]. exists e', stop, inv. split; [exact He'|].
      split; [exact Hstop|]. split; [exact Hinv|]. reflexivity.
    + split; [reflexivity|]. split; [cbn; apply interval_add|]. exact Hsim.
Qed.
End RunCse.

Section Exceptions.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma step_return : StepReplay tid imem mem ev ReturnException.
Proof.
  intros p p' r q0 Hok Hex _ Hm' He' Hrun.
  pose proof Hex as [Hp [issued [stop [inv [He [_ [_ Hq0]]]]]]].
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [s1 [m1 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [s2 [[] [Hcse Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  destruct (run_cse_replay tid imem mem ev (length (PPState.mem p)) (length (ev :: mem))
    p s2 () q0 Hok Hex ltac:(rewrite Hp; lia) ltac:(rewrite Hp; cbn; lia) He' Hcse)
    as [q0' [Hq0' Hrel]].
  exists q0'. split; [|exact Hrel]. simp run_outcome.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]. rewrite Hq0. cbn [PPState.mem].
  rewrite <- Hq0. eapply Exec.elem_of_bind_intro; [exact Hq0'|]. apply Exec.elem_of_mret.
Qed.

Lemma step_take f : StepReplay tid imem mem ev (TakeException f).
Proof.
  intros p p' r q0 Hok Hex _ Hm' He' Hrun.
  pose proof Hex as [Hp [issued [stop [inv [He [_ [Hinv Hq0]]]]]]].
  pose proof (VMViews.ok_inv_time _ _ (proj2 Hok)) as Hbound.
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [s1 [m1 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [s2 [[] [Hcse Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  unfold run_take_exception in Hcse.
  apply Exec.elem_of_bind_elim in Hcse as [s3 [it [Hget Hcse]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [compose] in Hcse.
  assert (Hreplay : ∀ vmax vmax', vmax ≤ length mem → vmax ≤ vmax' →
    Exec.elem_of_results (s2, ()) (run_cse tid imem vmax p) →
    IIS.inv_time (PPState.iis q0) = None ∧ vmax' = length (ev :: mem) ∨
    IIS.inv_time (PPState.iis q0) = Some vmax' →
    ∃ q0', Exec.elem_of_results (q0', ((), None))
      (run_outcome n tid imem (TakeException f) q0) ∧ Rel tid imem mem ev s2 q0').
  { intros vmax vmax' H1 H2 Hrun Hsel.
    destruct (run_cse_replay tid imem mem ev vmax vmax' p s2 () q0 Hok Hex H1 H2 He' Hrun)
      as [q0' [Hq0' Hrel]].
    exists q0'. split; [|exact Hrel]. simp run_outcome.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
    unfold run_take_exception.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]. cbn [compose].
    destruct Hsel as [[Hn Hv] | Hs].
    - rewrite Hn. subst vmax'. replace (ev :: mem) with (PPState.mem q0) in Hq0'
        by (rewrite Hq0; reflexivity). exact Hq0'.
    - rewrite Hs. exact Hq0'. }
  assert (Hinv_q : IIS.inv_time (PPState.iis q0) = inv) by (rewrite Hq0; reflexivity).
  destruct (IIS.inv_time (PPState.iis p)) as [t|] eqn:Ht.
  - assert (t ≤ length mem) by (rewrite <- Hp; apply Hbound; reflexivity).
    destruct Hinv as [->|[time [Hlt ->]]].
    + apply (Hreplay t t); [lia|lia|exact Hcse|]. right. exact Hinv_q.
    + apply (Hreplay t time); [lia|lia|exact Hcse|]. right. exact Hinv_q.
  - destruct Hinv as [->|[time [Hlt ->]]].
    + apply (Hreplay (length (PPState.mem p)) (length (ev :: mem)));
        [rewrite Hp; lia|rewrite Hp; cbn; lia|exact Hcse|]. left. split; [exact Hinv_q|reflexivity].
    + apply (Hreplay (length (PPState.mem p)) time);
        [rewrite Hp; lia|rewrite Hp; lia|exact Hcse|]. right. exact Hinv_q.
Qed.
End Exceptions.

Section Barriers.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Section FrameViews.
Context (W T : list nat) (C : option TLB.t) (t : TState.t).
Local Notation F := (VMTransEndReplay.frame W T C t).
Lemma frame_vrd : TState.vrd F = TState.vrd t. Proof. reflexivity. Qed.
Lemma frame_vwr : TState.vwr F = TState.vwr t. Proof. reflexivity. Qed.
Lemma frame_vdmbst : TState.vdmbst F = TState.vdmbst t. Proof. reflexivity. Qed.
Lemma frame_vdmb : TState.vdmb F = TState.vdmb t. Proof. reflexivity. Qed.
Lemma frame_vdsb : TState.vdsb F = TState.vdsb t. Proof. reflexivity. Qed.
Lemma frame_vcse : TState.vcse F = TState.vcse t. Proof. reflexivity. Qed.
Lemma frame_vspec : TState.vspec F = TState.vspec t. Proof. reflexivity. Qed.
Lemma frame_vmsr : TState.vmsr F = TState.vmsr t. Proof. reflexivity. Qed.
Lemma frame_vacq : TState.vacq F = TState.vacq t. Proof. reflexivity. Qed.
Lemma frame_vrel : TState.vrel F = TState.vrel t. Proof. reflexivity. Qed.
Lemma frame_vtlbi_self : TState.vtlbi_self F = TState.vtlbi_self t. Proof. reflexivity. Qed.
Lemma frame_vtlbi_other : TState.vtlbi_other F = TState.vtlbi_other t. Proof. reflexivity. Qed.
End FrameViews.
Ltac frame_views := rewrite ?frame_vrd, ?frame_vwr, ?frame_vdmbst, ?frame_vdmb, ?frame_vdsb,
  ?frame_vcse, ?frame_vspec, ?frame_vmsr, ?frame_vacq, ?frame_vrel, ?frame_vtlbi_self,
  ?frame_vtlbi_other.

Lemma step_isb_like p p' q0 vmax :
  VMViews.ok p → Exact tid imem mem ev p q0 → vmax = length (PPState.mem p) →
  emits tid imem mem ev (PPState.state p') →
  Exec.elem_of_results (p', ()) (run_cse tid imem vmax p) →
  ∃ q0', Exec.elem_of_results (q0', ()) (run_cse tid imem (length (ev :: mem)) q0) ∧
    Rel tid imem mem ev p' q0'.
Proof.
  intros Hok Hex -> He' Hrun. pose proof Hex as [Hp _].
  eapply (run_cse_replay tid imem mem ev); try eassumption; rewrite Hp; cbn; lia.
Qed.

Lemma step_barrier b : StepReplay tid imem mem ev (Barrier b).
Proof.
  intros p p' r q0 Hok Hex _ Hm' He' Hrun.
  pose proof (VMViews.run_outcome_ok _ _ _ _ _ _ _ Hok Hrun) as Hok'.
  pose proof Hex as [Hp [issued [stop [inv [He [Hstop [Hinv Hq0]]]]]]].
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [s1 [m1 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [s2 [[] [Hb Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  assert (Hlift : ∀ q0', Exec.elem_of_results (q0', ())
      (run_barrier tid imem b (length (ev :: mem)) q0) →
    Exec.elem_of_results (q0', ((), None)) (run_outcome n tid imem (Barrier b) q0)).
  { intros q0' H. simp run_outcome.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    replace (PPState.mem q0) with (ev :: mem) by (rewrite Hq0; reflexivity).
    eapply Exec.elem_of_bind_intro; [exact H|]. apply Exec.elem_of_mret. }
  destruct b; repeat match goal with u : unit |- _ => destruct u end;
    unfold run_barrier in Hb |- *.
  all: try solve [exfalso; VMViews.invert].
  all: try solve [apply Exec.elem_of_bind_elim in Hb as [s3 [t3 [Hget Hb]]];
       apply Exec.elem_of_mget_inv in Hget as [-> ->];
       destruct (step_isb_like p s2 q0 _ Hok Hex eq_refl He' Hb) as [q0' [Hq Hrel]];
       exists q0'; split; [|exact Hrel]; apply Hlift; unfold run_barrier;
       eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]; exact Hq].
  all: destruct p as [ts m iis]; cbn [PPState.mem PPState.state PPState.iis] in *; subst m.
  all: pose proof (VMTransEndReplay.emit_promise_frame _ _ _ _ _ _ He) as Hframe.
  all: set (W := TState.prom_wr issued) in Hframe; set (T := TState.prom_tlbi issued) in Hframe;
    set (C := TState.tlb issued) in Hframe; clearbody W T C; subst issued; subst q0.
  all: pose proof (proj1 Hok) as Hts; pose proof (VMViews.ok_vrd _ _ Hts);
    pose proof (VMViews.ok_vwr _ _ Hts); pose proof (VMViews.ok_vcse _ _ Hts);
    pose proof (VMViews.ok_vdsb _ _ Hts); pose proof (VMViews.ok_vdmb _ _ Hts);
    pose proof (VMViews.ok_vdmbst _ _ Hts); pose proof (VMViews.ok_vtlbi_self _ _ Hts);
    pose proof (VMViews.ok_vtlbi_other _ _ Hts).
  all: cbn [PPState.mem PPState.state PPState.iis length] in *.
  all: VMViews.invert.
  all: eexists; split; [apply Hlift; unfold run_barrier;
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]; cbn [PPState.state];
    repeat match goal with H : ?x = _ |- context [match ?x with _ => _ end] => rewrite H end;
    repeat first [
      apply Exec.elem_of_mret |
      apply guard_discard_bind_intro;
        [first [eapply VMGuardReplay.emit_promise_no_write_promises_until
               |eapply VMGuardReplay.emit_promise_no_promises_until];
          [exact He|eassumption|frame_views; unfold join, join_nat in *; repeat case_decide; lia]|intros _] |
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|] |
      apply Exec.elem_of_mset ]|].
  all: apply exact_rel; [exact Hok'|].
  all: split; [reflexivity|]; eexists _, stop, inv.
  all: split; [apply (VMEmit.emit_transfer tid imem mem ev ts _ _ He); reflexivity|].
  all: split; [exact Hstop|]; split; [exact Hinv|].
  all: cbn; rewrite ?interval_add; reflexivity.
Qed.
End Barriers.

Section RegRead.
Context (W T : list nat) (C : option TLB.t) (stop : nat) (inv : option nat).
Local Notation F := (VMTransEndReplay.frame W T C).
Local Notation I := (VMTransEndReplay.interval_iis stop inv).

Lemma root_setv trs : IIS.TransRes.root (setv IIS.TransRes.trans_end stop trs) = IIS.TransRes.root trs.
Proof. reflexivity. Qed.
Lemma trs_interval iis : IIS.trs (I iis) = fmap (setv IIS.TransRes.trans_end stop) (IIS.trs iis).
Proof. reflexivity. Qed.
Lemma sreg_reads_interval iis : IIS.sreg_reads (I iis) = IIS.sreg_reads iis.
Proof. reflexivity. Qed.
Lemma read_reg_frame ts r : TState.read_reg (F ts) r = TState.read_reg ts r.
Proof. reflexivity. Qed.
Lemma read_sreg_direct_frame ts r : TState.read_sreg_direct (F ts) r = TState.read_sreg_direct ts r.
Proof. reflexivity. Qed.
Lemma read_sreg_indirect_frame ts r : TState.read_sreg_indirect (F ts) r = TState.read_sreg_indirect ts r.
Proof. reflexivity. Qed.

Ltac rb_norm := rewrite ?root_setv, ?trs_interval, ?sreg_reads_interval, ?read_reg_frame,
  ?read_sreg_direct_frame, ?read_sreg_indirect_frame.

Ltac rb_step :=
  first [
    apply Exec.elem_of_mret
  | apply exec_guard_or_bind_intro; [assumption|]
  | apply Exec.elem_of_mget | apply Exec.elem_of_mGet | apply Exec.elem_of_mset
  | eapply Exec.elem_of_mchoosel; eassumption
  | apply Exec.elem_of_liftSt
  | progress (cbn [fst snd compose othrow])
  | eapply Exec.elem_of_bind_intro
  | progress rb_norm
  | match goal with H : ?x = _ |- context [?x] =>
      lazymatch x with
      | IIS.trs _ => rewrite H | dmap_lookup _ _ => rewrite H | TState.read_reg _ _ => rewrite H
      | TState.read_sreg_direct _ _ => rewrite H | TState.read_sreg_indirect _ _ => rewrite H
      | IIS.TransRes.root _ => rewrite H | decide _ => rewrite H
      end end
  | progress (cbn [fmap option_fmap option_map]) ].

Lemma trans_read_replay reg racc trs ts t r :
  Exec.elem_of_results (t, r) (run_reg_trans_read reg racc trs ts) →
  t = ts ∧ Exec.elem_of_results (F ts, r)
    (run_reg_trans_read reg racc (setv IIS.TransRes.trans_end stop trs) (F ts)).
Proof.
  unfold run_reg_trans_read. intro H. VMViews.invert.
  all: split; [reflexivity|].
  all: apply exec_guard_or_bind_intro; [assumption|].
  all: rewrite root_setv; match goal with H : IIS.TransRes.root _ = Some _ |- _ => rewrite H end;
    cbn [othrow].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]; cbv beta.
  all: repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.
  all: match goal with H : decide _ = _ |- _ => rewrite H end.
  all: try apply Exec.elem_of_mret.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mGet|].
  all: apply exec_guard_or_bind_intro; [assumption|].
  all: rewrite read_reg_frame; match goal with H : TState.read_reg _ _ = Some _ |- _ => rewrite H end.
  all: apply Exec.elem_of_mret.
Qed.

Lemma indirect_replay reg racc ts iis st' vv :
  Exec.elem_of_results (st', vv) (read_sreg_indirect reg racc (ts, iis)) →
  Exec.elem_of_results ((F st'.1, I st'.2), vv) (read_sreg_indirect reg racc (F ts, I iis)).
Proof.
  unfold read_sreg_indirect. intro H. VMViews.invert.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]; cbn [snd].
  all: rewrite sreg_reads_interval.
  all: match goal with H : dmap_lookup _ _ = _ |- _ => rewrite H end.
  all: repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.
  all: cbn [fst snd]; try apply Exec.elem_of_mret.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]; cbn [fst].
  all: rewrite read_sreg_indirect_frame;
    match goal with H : TState.read_sreg_indirect _ _ = Some _ |- _ => rewrite H end; cbn [othrow].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  all: eapply Exec.elem_of_bind_intro; [eapply Exec.elem_of_mchoosel; eassumption|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  all: apply Exec.elem_of_mret.
Qed.

Lemma reg_read_replay reg racc ts iis st' x :
  Exec.elem_of_results (st', x) (run_reg_read reg racc (ts, iis)) →
  Exec.elem_of_results ((F st'.1, I st'.2), x) (run_reg_read reg racc (F ts, I iis)).
Proof.
  unfold run_reg_read. intro H.
  apply Exec.elem_of_bind_elim in H as [s1 [[v view] [HB Hrest]]].
  apply Exec.elem_of_bind_elim in Hrest as [s2 [[] [Hset Hret]]].
  apply Exec.elem_of_mset_inv in Hset as ->.
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  eapply Exec.elem_of_bind_intro with (st' := (F s1.1, I s1.2)) (a := (v, view)).
  2: { cbv beta iota. eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]. apply Exec.elem_of_mret. }
  apply Exec.elem_of_bind_elim in HB as [s0 [iis0 [Hget HB]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [snd] in HB.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]. cbn [snd].
  rewrite trs_interval. destruct (IIS.trs iis) as [trs|] eqn:Htrs; cbn [fmap option_fmap option_map].
  - apply Exec.elem_of_liftSt_inv in HB as [t [-> HB]].
    apply trans_read_replay in HB as [-> HB]. cbn.
    exact (Exec.elem_of_liftSt (F ts, I iis) (F ts) _ fst _ HB).
  - unfold run_reg_general_read in HB |- *.
    apply Exec.elem_of_bind_elim in HB as [s3 [t3 [Hget HB]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->]. cbn [fst] in HB.
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]. cbn [fst].
    destruct (decide (reg ∈ relaxed_regs)); [destruct (decide (is_Some racc))|].
    + rewrite read_sreg_direct_frame. unfold othrow in HB |- *.
      destruct (TState.read_sreg_direct ts reg); [|VMViews.invert].
      apply Exec.elem_of_mret_inv in HB as [-> ->]. apply Exec.elem_of_mret.
    + apply indirect_replay, HB.
    + rewrite read_reg_frame. unfold othrow in HB |- *.
      destruct (TState.read_reg ts reg); [|VMViews.invert].
      apply Exec.elem_of_mret_inv in HB as [-> ->]. apply Exec.elem_of_mret.
Qed.
End RegRead.

Lemma reg_read_fields reg racc ts iis st' v :
  Exec.elem_of_results (st', v) (run_reg_read reg racc (ts, iis)) →
  st'.1 = ts ∧ IIS.trs st'.2 = IIS.trs iis ∧ IIS.inv_time st'.2 = IIS.inv_time iis.
Proof.
  unfold run_reg_read, run_reg_general_read, run_reg_trans_read, read_sreg_indirect.
  intro H. VMViews.invert. all: repeat split; reflexivity.
Qed.

Section StepRegRead.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma step_reg_read reg racc : StepReplay tid imem mem ev (RegRead reg racc).
Proof.
  intros [ts m iis] p' r q0 Hok Hex _ Hm' He' Hrun.
  pose proof (VMViews.run_outcome_ok _ _ _ _ _ _ _ Hok Hrun) as Hok'.
  destruct Hex as [Hm [issued [stop [inv [He [Hstop [Hinv ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv. subst m.
  pose proof (VMTransEndReplay.emit_promise_frame _ _ _ _ _ _ He) as Hframe.
  set (W := TState.prom_wr issued) in Hframe; set (T := TState.prom_tlbi issued) in Hframe;
    set (C := TState.tlb issued) in Hframe; clearbody W T C; subst issued.
  clear Hm' He'.
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [v [Hlift Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  apply Exec.elem_of_liftSt_inv in Hlift as [[ts' iis'] [-> Hrr]]. cbn in Hrr.
  pose proof (reg_read_replay W T C stop inv reg racc ts iis _ v Hrr) as Hrep. cbn in Hrep.
  destruct (reg_read_fields reg racc ts iis _ v Hrr) as (Hts & Htrs & Hit). cbn in Hts, Htrs, Hit.
  subst ts'.
  exists (PPState.Make (VMTransEndReplay.frame W T C ts) (ev :: mem)
    (VMTransEndReplay.interval_iis stop inv iis')).
  split.
  - simp run_outcome. eapply Exec.elem_of_bind_intro; [|apply Exec.elem_of_mret].
    exact (Exec.elem_of_liftSt _ _ _ (PPState.state ×× PPState.iis) _ Hrep).
  - apply exact_rel; [exact Hok'|]. split; [reflexivity|].
    exists (VMTransEndReplay.frame W T C ts), stop, inv. cbn.
    split; [exact He|]. split; [rewrite Htrs; exact Hstop|]. split; [rewrite Hit; exact Hinv|].
    reflexivity.
Qed.
End StepRegRead.

Section ReadExplicit.
Context (tid : nat) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).
Context (W T : list nat) (C : option TLB.t) (stop : nat) (inv : option nat).
Local Notation F := (VMTransEndReplay.frame W T C).
Local Notation I := (VMTransEndReplay.interval_iis stop inv).

Lemma update_cohs_frame avs t : TState.update_cohs avs (F t) = F (TState.update_cohs avs t).
Proof.
  induction avs as [|[a v] avs IH]; [reflexivity|].
  change (TState.update_coh a v (TState.update_cohs avs (F t)) =
    F (TState.update_coh a v (TState.update_cohs avs t))).
  rewrite IH. reflexivity.
Qed.

Lemma read_explicit_replay addr size macc ts iis p' ret :
  TState.emit_promise tid imem (ev :: mem) ev ts = Ok (F ts) →
  VMTranslationReplay.inv_after (length mem) (IIS.inv_time iis) inv →
  IIS.strict iis ≤ length mem → IIS.strict (PPState.iis p') ≤ length mem →
  Exec.elem_of_results (p', ret)
    (read_mem_explicit imem addr size macc (PPState.Make ts mem iis)) →
  Exec.elem_of_results
    (PPState.Make (F (PPState.state p')) (ev :: mem) (I (PPState.iis p')), ret)
    (read_mem_explicit imem addr size macc (PPState.Make (F ts) (ev :: mem) (I iis))).
Proof.
  intros He Hinv Hstrict Hbound Hrun.
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
  cbn [PPState.state PPState.mem PPState.iis compose] in *.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn [PPState.state PPState.mem PPState.iis compose].
  change (IIS.strict (I iis)) with (IIS.strict iis).
  eapply exec_guard_discard_bind_intro.
  { eapply VMGuardReplay.emit_promise_no_promises_until; [exact He|exact Hnp|].
    exact Hstrict. }
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  eapply Exec.elem_of_bind_intro with (a := new_candidates).
  - apply exec_lift_result. exact Hread'.
  - eapply Exec.elem_of_bind_intro with (a := candidate).
    + apply Exec.elem_of_mchoosel, Hsubset, Hin.
    + cbn [PPState.state PPState.mem PPState.iis] in *.
      UMFulfilledReplay.invert_execution_with_guards.
      all: subst ret.
      all: cbn [PPState.state PPState.mem PPState.iis compose] in *.
      all: destruct Hinv as [Hsame|[t [Hlt Hnew]]]; [rewrite Hsame|rewrite Hnew].
      all: unfold IIS.add in Hbound; simpl in Hbound.
      all: repeat first
        [ eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_guard_discard_unit; assumption|]
        | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_guard_discard_unit;
            match type of Hbound with Init.Nat.max ?x' _ ≤ _ =>
              let Hx := fresh in assert (Hx : x' < t) by (unfold join, join_nat in *; lia);
              exact Hx end|]
        | eapply exec_guard_discard_bind_intro; [assumption|] ].
      all: unfold Exec.elem_of_results; cbn [Exec.results mret Exec.mret_inst Exec.res_mret_inst];
        apply list_elem_of_singleton; f_equal.
      all: cbn; rewrite ?update_cohs_frame; reflexivity.
Qed.
End ReadExplicit.

Lemma update_cohs_fields avs t :
  TState.tlb (TState.update_cohs avs t) = TState.tlb t ∧
  TState.prom_wr (TState.update_cohs avs t) = TState.prom_wr t ∧
  TState.prom_tlbi (TState.update_cohs avs t) = TState.prom_tlbi t.
Proof.
  induction avs as [|[a v] avs IH]; [auto|].
  change (TState.update_cohs ((a, v) :: avs) t) with
    (TState.update_coh a v (TState.update_cohs avs t)). exact IH.
Qed.

Lemma read_explicit_fields imem addr size macc p p' v :
  Exec.elem_of_results (p', v) (read_mem_explicit imem addr size macc p) →
  TState.tlb (PPState.state p') = TState.tlb (PPState.state p) ∧
  TState.prom_wr (PPState.state p') = TState.prom_wr (PPState.state p) ∧
  TState.prom_tlbi (PPState.state p') = TState.prom_tlbi (PPState.state p) ∧
  PPState.mem p' = PPState.mem p ∧
  IIS.trs (PPState.iis p') = IIS.trs (PPState.iis p) ∧
  IIS.inv_time (PPState.iis p') = IIS.inv_time (PPState.iis p).
Proof.
  destruct p as [ts mem iis]. unfold read_mem_explicit. intro H. VMViews.invert.
  all: cbn [PPState.state PPState.mem PPState.iis].
  all: repeat progress rewrite ?VMViews.state_set_state, ?VMViews.state_set_iis, ?VMViews.mem_set_state,
    ?VMViews.mem_set_iis, ?VMViews.iis_set_state, ?VMViews.iis_set_iis,
    ?VMViews.state_set_iis_field, ?VMViews.mem_set_iis_field, ?VMViews.iis_set_iis_field,
    ?VMViews.state_set_state_field, ?VMViews.mem_set_state_field, ?VMViews.iis_set_state_field.
  all: cbn [PPState.state PPState.mem PPState.iis].
  all: match goal with |- context [TState.update_cohs ?avs ?t] =>
    pose proof (update_cohs_fields avs t) as (Ht & Hw & Hb) end.
  all: repeat split; assumption || reflexivity.
Qed.

Lemma pop_end tres ntres v : IIS.TransRes.pop tres = Ok (ntres, v) →
  IIS.TransRes.trans_end ntres = IIS.TransRes.trans_end tres.
Proof.
  unfold IIS.TransRes.pop. destruct (IIS.TransRes.remaining tres); [discriminate|].
  intros [= <- _]. reflexivity.
Qed.

Lemma read_pte_fields p p' v :
  Exec.elem_of_results (p', v) (read_pte p) →
  PPState.state p' = PPState.state p ∧ PPState.mem p' = PPState.mem p ∧
  IIS.inv_time (PPState.iis p') = IIS.inv_time (PPState.iis p) ∧
  ∀ trs', IIS.trs (PPState.iis p') = Some trs' →
    ∃ trs, IIS.trs (PPState.iis p) = Some trs ∧
      IIS.TransRes.trans_end trs' = IIS.TransRes.trans_end trs.
Proof.
  destruct p as [ts mem iis]. unfold read_pte. intro H. VMViews.invert.
  cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros trs' Htrs. simpl in *. injection Htrs as <-. subst.
  eexists. split; [eassumption|]. eapply pop_end; eassumption.
Qed.

Section StepMemRead.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma step_mem_read req : StepReplay tid imem mem ev (MemRead req).
Proof.
  intros [ts m iis] p' r q0 Hok Hex Hf Hm' He' Hrun.
  pose proof (VMViews.run_outcome_ok _ _ _ _ _ _ _ Hok Hrun) as Hok'.
  destruct Hex as [Hm [issued [stop [inv [He [Hstop [Hinv ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv. subst m.
  pose proof (VMTransEndReplay.emit_promise_frame _ _ _ _ _ _ He) as Hframe.
  set (W := TState.prom_wr issued) in Hframe; set (T := TState.prom_tlbi issued) in Hframe;
    set (C := TState.tlb issued) in Hframe; clearbody W T C; subst issued.
  pose proof (VMViews.ok_strict _ _ (proj2 Hok)) as Hstrict. cbn in Hstrict.
  destruct req as [macc addr pas size [|tags]]; simp run_outcome in Hrun |- *;
    [|exfalso; VMViews.invert].
  apply Exec.elem_of_bind_elim in Hrun as [s1 [Hpas [Hg Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hg as ->.
  destruct (is_ifetch macc) eqn:Hif; [|destruct (is_explicit macc) eqn:Hexp;
    [|destruct (is_ttw macc) eqn:Httw]].
  - apply Exec.elem_of_bind_elim in Hrun as [s2 [Hs4 [Hg Hrun]]].
    apply Exec.elem_of_guard_or_inv in Hg as ->.
    apply Exec.elem_of_bind_elim in Hrun as [s3 [m3 [Hget Hrun]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as [s4 [op [Hread Hret]]].
    apply Exec.elem_of_lift_res_inv in Hread as [-> Hread].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    cbn in Hf, Hread. specialize (Hf Hif Hs4).
    eexists. split.
    + apply exec_guard_or_bind_intro; [exact Hpas|].
      destruct (Exec.elem_of_guard_or (E:=string)
        (PPState.Make (VMTransEndReplay.frame W T C ts) (ev :: mem)
          (VMTransEndReplay.interval_iis stop inv iis))
        "Ifetch read of size other than 4" Hs4) as [Hs4' Hguard].
      replace Hs4' with Hs4 in Hguard by apply proof_irrel.
      eapply Exec.elem_of_bind_intro; [exact Hguard|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]. cbn [PPState.mem].
      eapply Exec.elem_of_bind_intro with (a := op).
      * apply Exec.elem_of_lift_res. cbn. rewrite Hf. exact Hread.
      * apply Exec.elem_of_mret.
    + apply exact_rel; [exact Hok'|]. split; [reflexivity|].
      exists (VMTransEndReplay.frame W T C ts), stop, inv. auto.
  - apply Exec.elem_of_bind_elim in Hrun as [s2 [v [Hre Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    pose proof (read_explicit_fields _ _ _ _ _ _ _ Hre) as (Ht & Hw & Hb & Hms & Htrs & Hit).
    cbn [PPState.state PPState.mem PPState.iis] in Ht, Hw, Hb, Hms, Htrs, Hit.
    pose proof (VMViews.ok_strict _ _ (proj2 Hok')) as Hstrict'. rewrite Hms in Hstrict'.
    pose proof (read_explicit_replay tid imem mem ev W T C stop inv addr size macc ts iis s2 v
      He Hinv Hstrict Hstrict' Hre) as Hrep.
    eexists. split.
    + apply exec_guard_or_bind_intro; [exact Hpas|].
      eapply Exec.elem_of_bind_intro; [exact Hrep|]. apply Exec.elem_of_mret.
    + apply exact_rel; [exact Hok'|]. split; [exact Hms|].
      exists (VMTransEndReplay.frame W T C (PPState.state s2)), stop, inv.
      split; [exact (VMEmit.emit_transfer tid imem mem ev ts _ _ He Ht Hw Hb)|].
      split; [rewrite Htrs; exact Hstop|]. split; [rewrite Hit; exact Hinv|]. reflexivity.
  - apply Exec.elem_of_bind_elim in Hrun as [s2 [Hs8 [Hg Hrun]]].
    apply Exec.elem_of_guard_or_inv in Hg as ->.
    apply Exec.elem_of_bind_elim in Hrun as [s3 [v [Hpte Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    pose proof (read_pte_fields _ _ _ Hpte) as (Hst & Hms & Hit & Htrs).
    cbn [PPState.state PPState.mem PPState.iis] in Hst, Hms, Hit, Htrs.
    pose proof (VMTransEndReplay.read_pte_interval ev W T C stop inv _ _ _ Hpte) as Hrep.
    eexists. split.
    + apply exec_guard_or_bind_intro; [exact Hpas|].
      destruct (Exec.elem_of_guard_or (E:=string)
        (PPState.Make (VMTransEndReplay.frame W T C ts) (ev :: mem)
          (VMTransEndReplay.interval_iis stop inv iis))
        "TTW read of size other than 8" Hs8) as [Hs8' Hguard].
      replace Hs8' with Hs8 in Hguard by apply proof_irrel.
      eapply Exec.elem_of_bind_intro; [exact Hguard|].
      eapply Exec.elem_of_bind_intro; [exact Hrep|]. apply Exec.elem_of_mret.
    + apply exact_rel; [exact Hok'|]. split; [exact Hms|].
      exists (VMTransEndReplay.frame W T C ts), stop, inv. cbn [PPState.state].
      rewrite Hst. split; [exact He|]. split.
      * intros trs' Htrs'. destruct (Htrs trs' Htrs') as [trs [Ho Hend]].
        rewrite Hend. exact (Hstop trs Ho).
      * split; [rewrite Hit; exact Hinv|]. unfold VMTransEndReplay.interval_state.
        rewrite ?Hms, ?Hst. reflexivity.
  - exfalso. VMViews.invert.
Qed.
End StepMemRead.

(** * Writes and TLBIs that fulfil an older promise *)

Section WriteFields.
Definition cohs_map (avs : list (address * view)) (c : gmap address view) :=
  foldr (λ '(a, v) c, <[a := max v (c !!! a)]> c) c avs.

Lemma update_cohs_set avs t : TState.update_cohs avs t = set TState.coh (cohs_map avs) t.
Proof.
  induction avs as [|[a v] avs IH]; [destruct t; reflexivity|].
  change (TState.update_coh a v (TState.update_cohs avs t) =
    set TState.coh (cohs_map ((a, v) :: avs)) t).
  rewrite IH. destruct t; reflexivity.
Qed.

Definition fwdbs_map addrs {n} (data : bv n) time vdata xcl (f : gmap address FwdItem.t) :=
  foldl (λ f '(a, byte), <[a := FwdItem.make time vdata byte xcl]> f) f
    (zip addrs (bv_to_bytes 8 data)).

Lemma set_fwdbs_set addrs n (data : bv n) time vdata xcl t :
  TState.set_fwdbs addrs data time vdata xcl t =
  set TState.fwdb (fwdbs_map addrs data time vdata xcl) t.
Proof.
  unfold TState.set_fwdbs, fwdbs_map. generalize (zip addrs (bv_to_bytes 8 data)).
  intro pairs. revert t. induction pairs as [|[a b] pairs IH]; intro t; cbn.
  - destruct t; reflexivity.
  - rewrite IH. destruct t; reflexivity.
Qed.
End WriteFields.

Section Gen.
Context (tid : nat) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).
Local Notation emit := (TState.emit_promise tid imem (ev :: mem) ev).
Local Notation pend := (VMCacheSim.pending tid (ev :: mem) ev).

Lemma pend_frame c t : setv TState.tlb c (pend t) =
  VMTransEndReplay.frame (TState.prom_wr (pend t)) (TState.prom_tlbi (pend t)) c t.
Proof. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; destruct t; reflexivity. Qed.

Lemma emit_transfer_gen ts ts' issued :
  emit ts = Ok issued → TState.tlb ts' = TState.tlb ts →
  emit ts' = Ok (VMTransEndReplay.frame (TState.prom_wr (pend ts')) (TState.prom_tlbi (pend ts'))
    (TState.tlb issued) ts').
Proof.
  rewrite !VMEmit.emit_pending. unfold TState.process_event, TState.run_tlb. rewrite !VMEmit.tlb_pending.
  intros He Ht. rewrite Ht. rewrite <- pend_frame.
  destruct (TState.tlb ts) as [c|] eqn:Hc.
  - destruct (TLB.fill_promise tid imem (ev :: mem) ev c) as [[c' []]|err]; cbn in He |- *;
      [|discriminate]. injection He as <-. reflexivity.
  - cbn in He |- *. injection He as <-. rewrite VMEmit.tlb_pending, Hc, <- Ht.
    rewrite <- (VMEmit.tlb_pending tid mem ev ts'), setv_tlb_same. reflexivity.
Qed.

Lemma emit_self ts issued : emit ts = Ok issued →
  issued = VMTransEndReplay.frame (TState.prom_wr (pend ts)) (TState.prom_tlbi (pend ts))
    (TState.tlb issued) ts.
Proof.
  intro He. pose proof (emit_transfer_gen ts ts issued He eq_refl) as H.
  rewrite He in H. injection H as H. exact H.
Qed.

Lemma pend_filter time ts : time ≤ length mem →
  filter (λ v, v ≠ time) (TState.prom_wr (pend ts)) =
  TState.prom_wr (pend (set TState.prom_wr (filter (λ v, v ≠ time)) ts)).
Proof.
  intro Ht. rewrite !(proj1 (VMEmit.pending_fields _ _ _ _)).
  destruct (bool_decide _); [destruct ev|]; cbn [app]; try reflexivity.
  rewrite filter_cons_True by (cbn; lia). reflexivity.
Qed.

Lemma fulfill_app msg X l m t :
  Memory.fulfill msg l m = Some t → Memory.fulfill msg (X ++ l) m = Some t.
Proof.
  unfold Memory.fulfill, PromMemory.fulfill. intro H. induction X as [|x X IH]; [exact H|].
  cbn [app]. rewrite filter_cons. destruct (decide _); [|exact IH].
  revert IH. rewrite reverse_cons.
  match goal with |- _ → list.head (?L ++ [x]) = _ => destruct L end; cbn; intros; congruence.
Qed.

Lemma pend_char : ∃ Xw Xt, (∀ x, x ∈ Xw → length mem < x) ∧
  ∀ t, pend t = set TState.prom_wr (app Xw) (set TState.prom_tlbi (app Xt) t).
Proof.
  unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|].
  - exists [length (ev :: mem)], []. split.
    + intros x Hx. apply list_elem_of_singleton in Hx. subst. cbn. lia.
    + intro t. destruct t; reflexivity.
  - exists [], [length (ev :: mem)]. split; [intros x Hx; inversion Hx|]. intro t. destruct t; reflexivity.
  - exists [], []. split; [intros x Hx; inversion Hx|]. intro t. destruct t; reflexivity.
Qed.

Lemma pend_char2 : ∃ Xw Xt, (∀ x, x ∈ Xw → length mem < x) ∧ (∀ x, x ∈ Xt → length mem < x) ∧
  ∀ t, pend t = set TState.prom_wr (app Xw) (set TState.prom_tlbi (app Xt) t).
Proof.
  unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|].
  - exists [length (ev :: mem)], []. split; [|split].
    + intros x Hx. apply list_elem_of_singleton in Hx. subst. cbn. lia.
    + intros x Hx; inversion Hx.
    + intro t. destruct t; reflexivity.
  - exists [], [length (ev :: mem)]. split; [|split].
    + intros x Hx; inversion Hx.
    + intros x Hx. apply list_elem_of_singleton in Hx. subst. cbn. lia.
    + intro t. destruct t; reflexivity.
  - exists [], []. split; [intros x Hx; inversion Hx|]. split; [intros x Hx; inversion Hx|].
    intro t. destruct t; reflexivity.
Qed.
End Gen.

Lemma filter_prefix (time : nat) (Xw l : list nat) : (∀ x, x ∈ Xw → time < x) →
  filter (λ v, v ≠ time) (Xw ++ l)%list = (Xw ++ filter (λ v, v ≠ time) l)%list.
Proof.
  intro H. induction Xw as [|x Xw IH]; [reflexivity|]. cbn [app].
  rewrite filter_cons_True by (assert (time < x) by (apply H; set_solver); lia).
  rewrite IH; [reflexivity|]. intros y Hy. apply H. set_solver.
Qed.

Lemma rmw_read_interval stop inv iis :
  IIS.rmw_read (VMTransEndReplay.interval_iis stop inv iis) = IIS.rmw_read iis.
Proof. reflexivity. Qed.
Lemma xclb_frame W T C t : TState.xclb (VMTransEndReplay.frame W T C t) = TState.xclb t.
Proof. reflexivity. Qed.


Section Write.
Context (tid : nat) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).
Context (C : option TLB.t) (stop : nat) (inv : option nat).
Local Notation pend := (VMCacheSim.pending tid (ev :: mem) ev).
Local Notation I := (VMTransEndReplay.interval_iis stop inv).
Local Notation G t := (VMTransEndReplay.frame (TState.prom_wr (pend t)) (TState.prom_tlbi (pend t)) C t).
Local Opaque TState.update_cohs TState.set_fwdbs.

Lemma write_replay addr size macc data ts iis p' r :
  (∀ t ∈ TState.prom_wr ts, t ≤ length mem) →
  VMTranslationReplay.inv_after (length mem) (IIS.inv_time iis) inv →
  PPState.mem p' = mem →
  Exec.elem_of_results (p', r) (write_mem tid imem addr size macc data (PPState.Make ts mem iis)) →
  r = None ∧ TState.tlb (PPState.state p') = TState.tlb ts ∧
  IIS.trs (PPState.iis p') = IIS.trs iis ∧ IIS.inv_time (PPState.iis p') = IIS.inv_time iis ∧
  Exec.elem_of_results (PPState.Make (G (PPState.state p')) (ev :: mem) (I (PPState.iis p')), None)
    (write_mem tid imem addr size macc data (PPState.Make (G ts) (ev :: mem) (I iis))).
Proof.
  intros Hbound Hinv Hm Hrun.
  destruct (pend_char tid mem ev) as (Xw & Xt & HX & Hp). rewrite !Hp.
  unfold write_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [mem0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[time fresh] [Hfulfill Hrun]]].
  cbn [PPState.state PPState.mem] in Hfulfill.
  revert Hfulfill.
  match goal with |- context [Memory.fulfill ?m ?pr ?mm] =>
    destruct (Memory.fulfill m pr mm) as [t|] eqn:Hlookup end; intro Hfulfill.
  2: { exfalso. revert Hm. VMViews.invert.
       all: intro Hm; cbn in Hm; apply (f_equal length) in Hm; cbn in Hm; lia. }
  apply Exec.elem_of_mret_inv in Hfulfill as [-> Heq]. inversion Heq; subst time fresh. clear Heq.
  pose proof (VMReadReplay.fulfill_bound _ _ _ _ Hlookup) as Htime.
  assert (Hlookup' : Memory.fulfill (Ev.Msg (Msg.make tid addr size data)) (Xw ++ TState.prom_wr ts)%list
    (ev :: mem) = Some t).
  { apply fulfill_app. rewrite VMReadReplay.fulfill_after_event by exact Hbound. exact Hlookup. }
  assert (HXt : ∀ x, x ∈ Xw → t < x) by (intros x Hx; specialize (HX x Hx); lia).
  clear Hp HX Hm.
  UMFulfilledReplay.invert_execution_with_guards; subst; try discriminate.
  all: cbn [PPState.state PPState.mem PPState.iis compose] in *.
  all: split; [reflexivity|].
  all: split; [cbn; rewrite ?update_cohs_set, ?set_fwdbs_set; reflexivity|].
  all: split; [reflexivity|]; split; [reflexivity|].
  all: destruct Hinv as [Hsame|[t' [Hlt Hnew]]]; [rewrite Hsame|rewrite Hnew; assert (Hg : t < t') by lia].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  all: cbn [PPState.state PPState.mem VMTransEndReplay.frame setv set TState.prom_wr].
  all: rewrite Hlookup'.
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|].
  all: repeat first
    [ apply Exec.elem_of_guard_discard_unit;
        first [rewrite VMReadReplay.exclusive_before_future by assumption; assumption | assumption | cbn; lia]
    | apply Exec.elem_of_mret
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_guard_discard_unit;
        first [rewrite VMReadReplay.exclusive_before_future by assumption; assumption | assumption | cbn; lia]|]
    | eapply exec_guard_discard_bind_intro; [assumption|]
    | match goal with H : ?x = _ |- context[?x] => progress rewrite H end
    | progress cbn [PPState.state PPState.iis PPState.mem compose othrow]
    | progress rewrite ?rmw_read_interval, ?xclb_frame
    | match goal with
      | |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) => eapply Exec.elem_of_bind_intro
      end ].
  all: unfold Exec.elem_of_results; cbn [Exec.results mret Exec.mret_inst Exec.res_mret_inst];
    apply list_elem_of_singleton; f_equal.
  all: cbn; rewrite ?update_cohs_set, ?set_fwdbs_set; cbn.
  all: rewrite <- filter_prefix by exact HXt; reflexivity.
Qed.
End Write.

Section Tlbi.
Context (tid : nat) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).
Context (C : option TLB.t) (Xw Xt : list nat).
Local Notation H t :=
  (setv TState.tlb C (set TState.prom_wr (app Xw) (set TState.prom_tlbi (app Xt) t))).

Lemma H_filter time t : (∀ x, x ∈ Xt → time < x) →
  set TState.prom_tlbi (filter (λ v, v ≠ time)) (H t) =
  H (set TState.prom_tlbi (filter (λ v, v ≠ time)) t).
Proof. intro HX. destruct t; cbn. rewrite filter_prefix by exact HX. reflexivity. Qed.

Lemma materialize_replay pre tlbi recipient ts iis iisR p' time created :
  (∀ x, x ∈ Xt → length mem < x) →
  (∀ x ∈ TState.prom_tlbi ts, x ≤ length mem) →
  PPState.mem p' = mem →
  Exec.elem_of_results (p', (time, created))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient (PPState.Make ts mem iis)) →
  created = false ∧ time ≤ length mem ∧
  p' = PPState.Make (set TState.prom_tlbi (filter (λ v, v ≠ time)) ts) mem iis ∧
  Exec.elem_of_results
    (PPState.Make (H (set TState.prom_tlbi (filter (λ v, v ≠ time)) ts)) (ev :: mem) iisR,
      (time, false))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient
      (PPState.Make (H ts) (ev :: mem) iisR)).
Proof.
  intros HX Hbound Hm Hrun.
  pose proof (VMMemoryGrowth.materialize_tlbi_growth _ _ _ _ _ _ _ _ _ Hrun) as Hgrow.
  destruct created.
  { exfalso. destruct Hgrow as [epoch [Hg _]]. rewrite Hm in Hg. cbn in Hg.
    apply (f_equal length) in Hg. cbn in Hg. lia. }
  unfold materialize_tlbi_for_recipient in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [mid [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [mem0 [Hget Hrun]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  apply Exec.elem_of_bind_elim in Hrun as [mid [[t fresh] [Hf Hrun]]].
  cbn [PPState.state PPState.mem] in Hf.
  revert Hf. match goal with |- context [Memory.fulfill ?m ?pr ?mm] =>
    destruct (Memory.fulfill m pr mm) as [t'|] eqn:Hlookup end; intro Hf.
  2: { exfalso. clear Hm Hgrow. VMViews.invert. }
  apply Exec.elem_of_mret_inv in Hf as [-> Heq]. injection Heq as <- <-.
  clear Hgrow. revert Hm. VMViews.invert. intros _.
  pose proof (VMReadReplay.fulfill_bound _ _ _ _ Hlookup) as Htime.
  split; [reflexivity|]. split; [exact Htime|]. split; [reflexivity|].
  rewrite <- H_filter by (intros x Hx; specialize (HX x Hx); lia).
  apply VMTLBINormalization.materialize_fulfilled; [|assumption].
  change (Memory.fulfill (Ev.Tlbi tlbi recipient (TState.dsb_epoch ts))
    (Xt ++ TState.prom_tlbi ts)%list (ev :: mem) = Some t).
  apply fulfill_app. rewrite VMReadReplay.fulfill_after_event by exact Hbound. exact Hlookup.
Qed.

Lemma recipients_replay pre tlbi recipients acc ts iis iisR p' res :
  (∀ x, x ∈ Xt → length mem < x) →
  (∀ x ∈ TState.prom_tlbi ts, x ≤ length mem) →
  PPState.mem p' = mem →
  Exec.elem_of_results (p', res)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients
      (PPState.Make ts mem iis)) →
  PPState.iis p' = iis ∧ TState.tlb (PPState.state p') = TState.tlb ts ∧
  Exec.elem_of_results (PPState.Make (H (PPState.state p')) (ev :: mem) iisR, res)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients
      (PPState.Make (H ts) (ev :: mem) iisR)).
Proof.
  intro HX. revert acc ts. induction recipients as [|rc rs IH]; intros acc ts Hbound Hm Hrun.
  - cbn [foldlM] in Hrun |- *. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    split; [reflexivity|]. split; [reflexivity|]. apply Exec.elem_of_mret.
  - cbn [foldlM] in Hrun |- *.
    apply Exec.elem_of_bind_elim in Hrun as [mid [acc1 [Hstep Htail]]].
    destruct acc as [[vs vo] cr]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time isn] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    assert (Hmm : PPState.mem mat = mem).
    { pose proof (VMMemoryGrowth.materialize_tlbi_growth _ _ _ _ _ _ _ _ _ Hmat) as Hg.
      destruct isn; [|exact Hg]. exfalso. destruct Hg as [epoch [Hg _]]. cbn in Hg.
      destruct res as [[? ?] ?].
      destruct (VMMemoryGrowth.tlbi_recipients_growth _ _ _ _ _ _ _ _ _ _ _ _ _ Htail)
        as [[Hg2 _]|[extra [_ [Hg2 _]]]]; rewrite Hm, Hg in Hg2;
        apply (f_equal length) in Hg2; rewrite ?length_app in Hg2; cbn in Hg2; lia. }
    destruct (materialize_replay pre tlbi rc ts iis iisR mat time isn HX Hbound Hmm Hmat)
      as (-> & Htime & -> & Hrep).
    assert (Hbound' : ∀ x ∈ TState.prom_tlbi (set TState.prom_tlbi (filter (λ v, v ≠ time)) ts),
      x ≤ length mem).
    { intros x Hx. cbn in Hx. apply list_elem_of_filter in Hx as [_ Hx]. exact (Hbound x Hx). }
    destruct (IH _ _ Hbound' Hm Htail) as (Hiis & Htlb & Hrep').
    split; [exact Hiis|]. split; [exact Htlb|].
    eapply Exec.elem_of_bind_intro; [|exact Hrep'].
    unfold VMMemoryGrowth.tlbi_recipient_step.
    eapply Exec.elem_of_bind_intro; [exact Hrep|]. apply Exec.elem_of_mret.
Qed.
End Tlbi.

Section StepTlbi.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma step_tlbi tlbi : StepReplay tid imem mem ev (TlbOp tlbi).
Proof.
  intros [ts m iis] p' r q0 Hok Hex _ Hm' He' Hrun.
  pose proof (VMViews.run_outcome_ok _ _ _ _ _ _ _ Hok Hrun) as Hok'.
  destruct Hex as [Hm [issued [stop [inv [He [Hstop [Hinv ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv. subst m.
  pose proof (VMViews.ok_prom_tlbi _ _ (proj1 Hok)) as Hbt. cbn in Hbt.
  assert (Hbound : ∀ x ∈ TState.prom_tlbi ts, x ≤ length mem)
    by (intros x Hx; rewrite Forall_forall in Hbt; apply list_elem_of_In in Hx; exact (Hbt x Hx)).
  clear Hbt.
  pose proof (emit_self _ _ _ _ _ _ He) as Hiss.
  destruct (pend_char2 tid mem ev) as (Xw & Xt & HXw & HX & Hp).
  rewrite !Hp in Hiss.
  remember (TState.tlb issued) as C eqn:HC.
  rewrite Hiss. clear Hiss He'.
  simp run_outcome in Hrun. unfold run_tlbi in Hrun.
  revert Hm' Hok'. VMViews.invert. all: intros Hm' Hok'.
  all: cbn [PPState.state PPState.mem PPState.iis compose] in *.
  all: match goal with Hf : Exec.elem_of_results (?x, _) (foldlM _ _ _ _) |- _ =>
    assert (Hmx : PPState.mem x = mem) by (rewrite <- Hm'; destruct x; reflexivity);
    destruct (recipients_replay tid imem mem ev (TState.tlb issued) Xw Xt _ _ _ _ _ _
      (VMTransEndReplay.interval_iis stop inv iis) _ _ HX Hbound Hmx Hf) as (Hiis & Htlb & Hrep) end.
  all: eexists; split; [simp run_outcome; unfold run_tlbi; repeat first [
      apply Exec.elem_of_mret
    | apply exec_guard_or_bind_intro; [assumption|]
    | eapply Exec.elem_of_bind_intro; [exact Hrep|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
    | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
    | match goal with H : ?x = _ |- context [?x] =>
        lazymatch x with TLBIRecord_op _ => rewrite H | decide _ => rewrite H end end
    | progress subst
    | progress (cbn [PPState.state PPState.iis compose])
    | match goal with |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) =>
        eapply Exec.elem_of_bind_intro end ] |].
  all: apply exact_rel; [exact Hok'|].
  all: split; [exact Hm'|].
  all: eexists _, stop, inv.
  all: split; [eapply emit_transfer_gen; [exact He|]; cbn; exact Htlb|].
  all: split; [intros trs Htrs; apply Hstop; rewrite <- Hiis; exact Htrs|].
  all: split; [rewrite <- Hiis in Hinv; exact Hinv|].
  all: rewrite !Hp.
  all: destruct x10 as [s0 m0 i0]; cbn in Hm'; subst m0; destruct i0; reflexivity.
Qed.
End StepTlbi.

Section StepWrite.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Lemma step_mem_write req val tags : StepReplay tid imem mem ev (MemWrite req val tags).
Proof.
  intros [ts m iis] p' r q0 Hok Hex _ Hm' He' Hrun.
  pose proof (VMViews.run_outcome_ok _ _ _ _ _ _ _ Hok Hrun) as Hok'.
  destruct Hex as [Hm [issued [stop [inv [He [Hstop [Hinv ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv. subst m.
  pose proof (VMViews.ok_prom_wr _ _ (proj1 Hok)) as Hbt. cbn in Hbt.
  assert (Hbound : ∀ x ∈ TState.prom_wr ts, x ≤ length mem)
    by (intros x Hx; rewrite Forall_forall in Hbt; apply list_elem_of_In in Hx; exact (Hbt x Hx)).
  clear Hbt He'.
  pose proof (emit_self _ _ _ _ _ _ He) as Hiss. rewrite Hiss. clear Hiss.
  destruct req as [macc addr pas size [|tags']]; simp run_outcome in Hrun |- *;
    [|exfalso; VMViews.invert].
  apply Exec.elem_of_bind_elim in Hrun as [s1 [Hpas [Hg Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hg as ->.
  apply Exec.elem_of_bind_elim in Hrun as [s1 [Hexp [Hg Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hg as ->.
  apply Exec.elem_of_bind_elim in Hrun as [s2 [vo [Hw Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  destruct (write_replay tid imem mem ev (TState.tlb issued) stop inv _ _ _ _ ts iis _ _
    Hbound Hinv Hm' Hw) as (-> & Htlb & Htrs & Hit & Hrep).
  eexists. split.
  - apply exec_guard_or_bind_intro; [exact Hpas|]. apply exec_guard_or_bind_intro; [exact Hexp|].
    eapply Exec.elem_of_bind_intro; [exact Hrep|]. apply Exec.elem_of_mret.
  - apply exact_rel; [exact Hok'|]. split; [exact Hm'|].
    eexists _, stop, inv. split; [eapply emit_transfer_gen; [exact He|exact Htlb]|].
    split; [intros trs Htrs'; apply Hstop; rewrite <- Htrs; exact Htrs'|].
    split; [rewrite Hit; exact Hinv|]. reflexivity.
Qed.
End StepWrite.

(** * System-register writes *)

Section Rp.
Context (tid : nat) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).
Local Notation action A := (stateT TLB.t (result string) A).
Local Notation L := (length mem).
Local Notation fp := (TLB.fill_promise tid imem (ev :: mem) ev).

Definition winv (c : TLB.t) := wf c ∧ VMRoots.rbound L c.

(** [r] runs on the history [mem], [r'] is the same action on [ev :: mem]. *)
Definition Rp {A} (r r' : action A) :=
  (∀ c c' x, winv c → r c = Ok (c', x) → winv c') ∧
  ∀ c0 c1 d after x ending, winv c0 → fp c0 = Ok (c1, ()) → cache_sim c1 d →
    r c0 = Ok (after, x) → fp after = Ok (ending, ()) →
    ∃ d', r' d = Ok (d', x) ∧ cache_sim ending d'.

Lemma Rp_ret {A} (x : A) : Rp (mret x) (mret x).
Proof.
  split.
  - intros c c' y H Hr. change (@Ok string _ (c, x) = Ok (c', y)) in Hr. injection Hr as <- _. exact H.
  - intros c0 c1 d after y ending _ Hf Hs Hr He.
    change (@Ok string _ (c0, x) = Ok (after, y)) in Hr. injection Hr as <- <-.
    rewrite Hf in He. injection He as <-. exists d. split; [reflexivity|exact Hs].
Qed.

Lemma Rp_bind {A B} (r r' : action A) (k k' : A → action B) :
  Rp r r' → (∀ x, Rp (k x) (k' x)) → Rp (r ≫= k) (r' ≫= k').
Proof.
  intros [Hp Hr] Hk. split.
  - intros c c' y H Hrun. unfold mbind, st_bind, result_bind in Hrun.
    destruct (r c) as [[mid x]|err] eqn:H1; [|discriminate].
    exact (proj1 (Hk x) mid c' y (Hp c mid x H H1) Hrun).
  - intros c0 c1 d after y ending Hw Hf Hs Hrun He.
    unfold mbind, st_bind, result_bind in Hrun |- *.
    destruct (r c0) as [[mid x]|err] eqn:H1; [|discriminate].
    pose proof (Hp c0 mid x Hw H1) as Hwm.
    pose proof (VMFillTotal.fill_promise_ev_ok _ _ _ _ _ _ Hf) as Hev.
    destruct (VMFillTotal.total_fill_promise tid imem (ev :: mem) ev Hev mid (proj1 (proj1 Hwm)))
      as [cm [[] [Hfm _]]].
    destruct (Hr c0 c1 d mid x cm Hw Hf Hs H1 Hfm) as [dm [Hdm Hsm]].
    rewrite Hdm. exact (proj2 (Hk x) mid cm dm after y ending Hwm Hfm Hsm Hrun He).
Qed.

Lemma Rp_some {A B} (err : string) (v : A) (k k' : A → action B) :
  Rp (k v) (k' v) → Rp (othrow err (Some v) ≫= k) (othrow err (Some v) ≫= k').
Proof. intros H. exact H. Qed.

Lemma Rp_mapM {A B} (f f' : A → action B) xs :
  (∀ x, x ∈ xs → Rp (f x) (f' x)) → Rp (mapM f xs) (mapM f' xs).
Proof.
  intro Hf. induction xs as [|x xs IH]; cbn [mapM]; [apply Rp_ret|].
  apply Rp_bind; [apply Hf; left|intro].
  apply Rp_bind; [apply IH; intros y Hy; apply Hf; right; exact Hy|intro]. apply Rp_ret.
Qed.

Lemma Rp_fill_asid_root root t : t ≤ L →
  Rp (TLB.fill_asid_root tid imem mem root t) (TLB.fill_asid_root tid imem (ev :: mem) root t).
Proof.
  intro Ht. split.
  - intros c c' [] [[Hv Hu] Hb] Hrun. split; [split|].
    + eapply VMCacheIndexed.fill_asid_root; [exact Hv|exact Hrun].
    + eapply VMCacheLastTLBI.unique_fill_asid_root; [exact Hu|exact Hrun].
    + exact (VMRoots.rstep_fill_asid_root L tid imem mem root t Ht c c' () Hb Hrun).
  - intros c0 c1 d after [] ending [[Hv Hu] Hb] Hf Hs Hrun He.
    destruct (VMCacheContext.replay_promise_before_asid_root tid imem mem ev root t c0 c1 after ending
      Ht Hv Hu Hb Hf Hrun He) as [ending' [Hrun' Hobs]].
    destruct (fill_asid_root_sim tid imem (ev :: mem) root t c1 d ending' () Hs Hrun')
      as [d' [Hd' Hs']].
    exists d'. split; [exact Hd'|].
    eapply VMNormalization.cache_sim_trans; [|exact Hs'].
    split; [exact Hobs|]. split.
    + assert (Hwa : wf after) by (split;
        [eapply VMCacheIndexed.fill_asid_root; [exact Hv|exact Hrun]
        |eapply VMCacheLastTLBI.unique_fill_asid_root; [exact Hu|exact Hrun]]).
      destruct Hwa as [Hva Hua]. split.
      * exact (VMCacheIndexed.fill_promise _ _ _ _ _ _ () Hva He).
      * exact (VMCacheLastTLBI.unique_fill_promise _ _ _ _ _ _ () Hua He).
    + destruct Hs as [_ [[Hv1 Hu1] _]]. split.
      * eapply VMCacheIndexed.fill_asid_root; [exact Hv1|exact Hrun'].
      * eapply VMCacheLastTLBI.unique_fill_asid_root; [exact Hu1|exact Hrun'].
Qed.

Local Notation emit := (TState.emit_promise tid imem (ev :: mem) ev).
Local Notation pend := (VMCacheSim.pending tid (ev :: mem) ev).

Lemma ts_sim_none t : TState.tlb t = None → ts_sim t t.
Proof. intro H. split; [symmetry; apply setv_tlb_same|rewrite H; exact I]. Qed.

Lemma run_tlb_replay (act act' : action ()) (k : TState.t → TState.t) ts ts' e' issued :
  Rp act act' → (∀ c, TState.tlb ts = Some c → winv c) →
  (∀ t c, k (setv TState.tlb c t) = setv TState.tlb c (k t)) → (∀ t, k (pend t) = pend (k t)) →
  emit ts = Ok issued → (TState.run_tlb act ts ≫= (λ t, mret (k t))) = Ok ts' → emit ts' = Ok e' →
  ∃ t2, (TState.run_tlb act' issued ≫= (λ t, mret (k t))) = Ok t2 ∧ ts_sim e' t2.
Proof.
  intros [Hp Hr] Hw Hk Hkp He Hrun He'.
  assert (Hkt : ∀ t, TState.tlb (k t) = TState.tlb t).
  { intro t. pose proof (Hk t (TState.tlb t)) as H. rewrite setv_tlb_same in H.
    rewrite H. reflexivity. }
  destruct (emit_char tid imem mem ev ts issued He)
    as [[Hnone ->]|(c0 & c1 & Hc0 & Hf & ->)].
  - unfold TState.run_tlb in Hrun. rewrite Hnone in Hrun. cbn in Hrun. injection Hrun as <-.
    destruct (emit_char tid imem mem ev _ e' He') as [[_ ->]|(c & c' & Hc & _)];
      [|rewrite Hkt, Hnone in Hc; discriminate].
    unfold TState.run_tlb. rewrite VMEmit.tlb_pending, Hnone. cbn. eexists. split; [reflexivity|].
    rewrite Hkp. apply ts_sim_none. rewrite VMEmit.tlb_pending, Hkt. exact Hnone.
  - destruct (Hw c0 Hc0) as [[Hv0 Hu0] Hb0].
    unfold TState.run_tlb in Hrun. rewrite Hc0 in Hrun.
    destruct (act c0) as [[after []]|err] eqn:Hact; cbn in Hrun; [|discriminate].
    injection Hrun as <-.
    destruct (emit_char tid imem mem ev _ e' He')
      as [[Hn _]|(c & ending & Hc & Hend & ->)]; [rewrite Hk in Hn; discriminate|].
    rewrite Hk in Hc. cbn in Hc. injection Hc as <-.
    assert (Hw1 : wf c1).
    { split; [exact (VMCacheIndexed.fill_promise _ _ _ _ _ _ () Hv0 Hf)
             |exact (VMCacheLastTLBI.unique_fill_promise _ _ _ _ _ _ () Hu0 Hf)]. }
    destruct (Hr c0 c1 c1 after () ending (conj (conj Hv0 Hu0) Hb0) Hf (cache_sim_refl _ Hw1)
      Hact Hend) as [d' [Hd' Hs]].
    unfold TState.run_tlb. rewrite tlb_setv, Hd'. cbn. eexists. split; [reflexivity|].
    rewrite !setv_tlb_twice, !Hk, Hkp, pend_setv_tlb, setv_tlb_twice.
    apply ts_sim_setv. exact Hs.
Qed.

Lemma read_sreg_indirect_pend t r : TState.read_sreg_indirect (pend t) r = TState.read_sreg_indirect t r.
Proof. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; reflexivity. Qed.

Lemma add_wsreg_replay sreg val v ts ts' e' issued :
  v ≤ length mem →
  VMCacheState.roots_bounded (length mem) (TState.read_sreg_indirect ts TTBR0_EL1) →
  VMCacheState.roots_bounded (length mem) (TState.read_sreg_indirect ts TTBR1_EL1) →
  (∀ c, TState.tlb ts = Some c → winv c) →
  emit ts = Ok issued → TState.add_wsreg tid imem mem sreg val v ts = Ok ts' → emit ts' = Ok e' →
  ∃ t2, TState.add_wsreg tid imem (ev :: mem) sreg val v issued = Ok t2 ∧ ts_sim e' t2.
Proof.
  intros Hv H0 H1 Hw He Hadd He'.
  pose proof (emit_self tid imem mem ev ts issued He) as Hiss.
  rewrite <- (setv_tlb_same ts), add_wsreg_shape, setv_tlb_same in Hadd.
  rewrite <- (setv_tlb_same issued), add_wsreg_shape, setv_tlb_same.
  assert (Hr : ∀ r, TState.read_sreg_indirect issued r = TState.read_sreg_indirect ts r)
    by (intro r; rewrite Hiss; reflexivity).
  rewrite !Hr.
  eapply (run_tlb_replay _ _ (λ t, set TState.levs (cons (LEv.Wsreg (WSReg.make sreg val v))) t));
    [| exact Hw | | | exact He | exact Hadd | exact He'].
  - destruct sreg as [r|r|r|r]; try apply Rp_ret.
    destruct r; try apply Rp_ret; cbv beta iota zeta.
    + apply Rp_bind; [apply Rp_fill_asid_root, Hv|intro].
      apply Rp_bind; [|intro; apply Rp_ret].
      apply Rp_mapM. intros [ttbr1 view] Hin. apply Rp_fill_asid_root.
      specialize (H1 _ Hin). cbn in H1. unfold join, join_nat in *. lia.
    + destruct (TState.read_sreg_indirect ts TTBR0_EL1) as [ttbr0s|] eqn:Hread.
      * apply Rp_some. apply Rp_bind; [|intro; apply Rp_ret].
        apply Rp_mapM. intros [ttbr0 view] Hin. apply Rp_fill_asid_root.
        assert (Hview : view ≤ length mem) by (apply (H0 (ttbr0, view)); exact Hin).
        unfold join, join_nat in *. lia.
      * split; intros; discriminate.
  - intros t c. destruct t; reflexivity.
  - intro t. unfold VMCacheSim.pending. destruct (bool_decide _); [destruct ev|]; destruct t; reflexivity.
Qed.
End Rp.

Lemma strict_interval stop inv iis :
  IIS.strict (VMTransEndReplay.interval_iis stop inv iis) = IIS.strict iis.
Proof. reflexivity. Qed.
Lemma set_reg_frame W T C r rv t t' :
  TState.set_reg r rv t = Some t' →
  TState.set_reg r rv (VMTransEndReplay.frame W T C t) = Some (VMTransEndReplay.frame W T C t').
Proof.
  unfold TState.set_reg. change (TState.regs (VMTransEndReplay.frame W T C t)) with (TState.regs t).
  case_decide; [intros [= <-]; reflexivity|discriminate].
Qed.
Lemma set_reg_eq r rv t t' : TState.set_reg r rv t = Some t' → t' = set TState.regs (dmap_insert r rv) t.
Proof. unfold TState.set_reg. case_decide; [intros [= <-]; reflexivity|discriminate]. Qed.
Lemma update_vspec_frame v W T C t :
  TState.update TState.vspec v (VMTransEndReplay.frame W T C t) =
  VMTransEndReplay.frame W T C (TState.update TState.vspec v t).
Proof. reflexivity. Qed.
Lemma ts_sim_vmsr v a b : ts_sim a b → ts_sim (TState.update TState.vmsr v a) (TState.update TState.vmsr v b).
Proof.
  intros [Hb Hs]. split; [|exact Hs].
  transitivity (TState.update TState.vmsr v (setv TState.tlb (TState.tlb b) a));
    [rewrite <- Hb; reflexivity|destruct a; reflexivity].
Qed.

Section StepRegWrite.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

Ltac rw_step He :=
  first [
    apply Exec.elem_of_mret
  | apply exec_guard_or_bind_intro; [assumption|]
  | eapply Exec.elem_of_bind_intro; [apply exec_lift_result;
      match goal with Hx : TState.add_wsreg _ _ _ _ _ _ _ = Ok _ |- _ => exact Hx end|]
  | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
  | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
  | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
  | apply Exec.elem_of_mset
  | apply guard_discard_bind_intro;
      [eapply VMGuardReplay.emit_promise_no_promises_until; [exact He|match goal with Hg : TState.no_promises_until _ _ |- _ => exact Hg end|rewrite ?strict_interval; lia]|intros _]
  | progress rewrite ?read_sreg_direct_frame, ?update_vspec_frame
  | match goal with H : ?x = _ |- context [?x] => lazymatch x with
      | decide _ => rewrite H | TState.read_sreg_direct _ _ => rewrite H
      | (_ =? _) => rewrite H end end
  | match goal with H : ?x = _ |- context [match ?x with _ => _ end] => is_var x; rewrite H end
  | match goal with Hs : TState.set_reg _ _ _ = Some _ |-
      context [TState.set_reg ?r ?rv (VMTransEndReplay.frame ?W ?T ?C ?t)] =>
      rewrite (set_reg_frame W T C r rv t _ Hs) end
  | progress cbn [PPState.state PPState.iis PPState.mem compose othrow fst snd]
  | match goal with |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) =>
      eapply Exec.elem_of_bind_intro end ].

Ltac rw_step2 He :=
  first [
    apply Exec.elem_of_mret
  | apply exec_guard_or_bind_intro; [assumption|]
  | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|]
  | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|]
  | eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mret|]
  | apply Exec.elem_of_mset
  | apply guard_discard_bind_intro;
      [eapply VMGuardReplay.emit_promise_no_promises_until;
        [exact He|match goal with Hg : TState.no_promises_until _ _ |- _ => exact Hg end|rewrite ?strict_interval; lia]
      |intros _]
  | match goal with H : decide _ = _ |- _ => progress rewrite H end
  | match goal with H : bool_decide _ = _ |- _ => progress rewrite H end
  | progress rewrite ?VMViews.state_set_state, ?update_vspec_frame
  | match goal with Hs : TState.set_reg _ _ _ = Some _ |-
      context [TState.set_reg ?r ?rv (VMTransEndReplay.frame ?W ?T ?C ?t)] =>
      rewrite (set_reg_frame W T C r rv t _ Hs) end
  | progress cbn [PPState.state PPState.iis PPState.mem compose othrow fst snd]
  | match goal with |- Exec.elem_of_results _ (((_ ≫= _) ≫= _) _) =>
      eapply Exec.elem_of_bind_intro end ].

Lemma step_reg_write reg racc val : StepReplayR tid imem mem ev (RegWrite reg racc val).
Proof.
  intros [ts m iis] p' r q0 Hok Hroots Hex _ Hm' He' Hrun.
  pose proof (VMViews.run_outcome_ok _ _ _ _ _ _ _ Hok Hrun) as Hok'.
  destruct Hex as [Hm [issued [stop [inv [He [Hstop [Hinv ->]]]]]]].
  cbn [PPState.mem PPState.state PPState.iis] in Hm, He, Hstop, Hinv. subst m.
  unfold VMRoots.pok in Hroots. cbn in Hroots.
  pose proof Hok as [Hts Hiis]. cbn in Hts, Hiis.
  pose proof (VMViews.ok_strict _ _ Hiis). pose proof (VMViews.ok_vcse _ _ Hts).
  pose proof (VMViews.ok_vspec _ _ Hts). pose proof (VMViews.ok_vdsb _ _ Hts).
  assert (Hw : ∀ c, TState.tlb ts = Some c → winv mem c).
  { intros c Hc. destruct (VMViews.ok_cache _ _ Hts c Hc) as (_ & Hu & Hv).
    split; [split; assumption|]. unfold VMRoots.roots_ok in Hroots. rewrite Hc in Hroots. exact Hroots. }
  pose proof (emit_self tid imem mem ev ts issued He) as Hiss.
  remember (TState.tlb issued) as C eqn:HC. subst issued. clear HC.
  destruct (pend_char2 tid mem ev) as (Xw & Xt & _ & _ & Hp).
  simp run_outcome in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as [s1 [[] [Hwr Hret]]].
  apply Exec.elem_of_mret_inv in Hret as [-> ->].
  unfold run_reg_write in Hwr.
  revert Hm' He' Hok'. VMViews.invert. all: intros Hm' He' Hok'.
  all: cbn [PPState.state PPState.mem PPState.iis] in *.
  all: try match goal with Hd : TState.read_sreg_direct _ _ = Some ?vv |- _ =>
    pose proof (VMViews.read_sreg_direct_ok _ _ _ _ Hts Hd) end.
  (* The MSR to a relaxed register. *)
  1: match goal with Hadd : TState.add_wsreg _ _ _ _ _ ?vp ?t0 = Ok ?nts |- _ =>
    destruct He' as [e2 He2];
    pose proof (emit_transfer_gen tid imem mem ev _ nts e2 He2 eq_refl) as He1;
    assert (Hvp : vp ≤ length mem) by (cbn in *; unfold join, join_nat in *; lia);
    destruct (add_wsreg_replay tid imem mem ev _ _ _ t0 nts _ _ Hvp
      (proj1 (VMViews.roots_ok _ _ Hts)) (proj2 (VMViews.roots_ok _ _ Hts)) Hw He Hadd He1)
      as [t2 [Hrep Hsim]] end.
  1: { eexists; split; [clear Hm' Hok'; simp run_outcome; unfold run_reg_write; do 40 try rw_step He|].
    eexists. split.
    { split; [exact Hm'|]. exists e2, stop, inv. split; [exact He2|].
      split; [intros trs Htrs; apply Hstop; exact Htrs|]. split; [exact Hinv|]. reflexivity. }
    split; [reflexivity|]. split; [cbn; apply interval_add|].
    match type of He1 with TState.emit_promise _ _ _ _ ?x4 = Ok _ =>
      assert (Heq : e2 = TState.update TState.vmsr _ (VMTransEndReplay.frame
        (TState.prom_wr (pending tid (ev :: mem) ev x4))
        (TState.prom_tlbi (pending tid (ev :: mem) ev x4)) (TState.tlb e2) x4))
        by (etransitivity; [exact (emit_self tid imem mem ev _ e2 He2)|];
            rewrite !Hp; destruct x4; reflexivity)
    end.
    cbn [PPState.state]. rewrite Heq. apply ts_sim_vmsr. exact Hsim. }
  all: repeat match goal with H : Some _ = TState.set_reg _ _ _ |- _ => symmetry in H end.
  all: repeat match goal with H : TState.set_reg _ _ _ = Some _ |- _ =>
    progress (rewrite ?VMViews.state_set_state in H; cbn [PPState.state] in H) end.
  all: eexists; split; [clear Hm' Hok' He'; simp run_outcome; unfold run_reg_write; do 30 try rw_step2 He|].
  all: apply exact_rel; [exact Hok'|]. all: split; [exact Hm'|].
  all: repeat match goal with H : ?x = ?y |- _ => is_var x; is_var y; subst x end.
  all: match goal with Hs : TState.set_reg _ _ _ = Some ?t |- _ => apply set_reg_eq in Hs; subst t end.
  all: eexists _, stop, inv.
  all: split; [eapply emit_transfer_gen; [exact He|reflexivity]|].
  all: split; [intros trs Htrs; apply Hstop; exact Htrs|]. all: split; [exact Hinv|].
  all: rewrite !Hp.
  all: repeat match goal with H : ?x = _ |- _ => is_var x; subst x end.
  all: destruct ts, iis; reflexivity.
Qed.
End StepRegWrite.

Section Cover.
Context {n : nat} (tid : fin n) (imem : memoryMap) (mem : list Ev.t) (ev : Ev.t).

(** Outcomes whose replay is proven here. *)
Definition covered (out : outcome) : Prop :=
  match out with
  | TranslationEnd _ | MemWriteAddrAnnounce _ | GenericFail _
  | Barrier _ | ReturnException | TakeException _ | RegRead _ _ | MemRead _
  | MemWrite _ _ _ | TlbOp _ | RegWrite _ _ _ => True
  | _ => False
  end.

Lemma steps_of_uncovered :
  (∀ out, ¬ covered out → StepReplayR tid imem mem ev out) → ∀ out, StepReplayR tid imem mem ev out.
Proof.
  intros H out. destruct out;
    first [apply StepReplay_R;
        first [apply step_trans_end|apply step_announce|apply step_fail|apply step_barrier
          |apply step_return|apply step_take|apply step_reg_read|apply step_mem_read
          |apply step_mem_write|apply step_tlbi]
      |apply step_reg_write
      |apply H; cbn; tauto].
Qed.
End Cover.




Section Sail.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).

Lemma prefix_fetches (tid : fin n) imem (mem : list Ev.t) ev (mon : iMon ()) p :
  VMSailNoSelfModifying bbm nondet term initMs code →
  event_misses_code VMPromisingReadByte code ev →
  SailThreadPrefix (VMPromising bbm) nondet term initMs tid imem p mon →
  fetches tid imem ev mon p.
Proof.
  intros Hsafe Hmiss. revert p. induction mon as [u|call k IH]; intros p Hprefix; [exact I|].
  destruct call as [out|[choices]]; cbn [fetches].
  - split.
    + destruct out; cbn [fetch_ok]; try exact I.
      lazymatch goal with |- is_ifetch (MemReq.access_kind ?mr) = true → _ =>
        intros Hfetch Hsize;
        pose proof (sail_fetch_code_covered _ _ _ _ _ _ Hsafe tid imem p mr k Hprefix Hfetch) as Hcode;
        rewrite Hsize in Hcode;
        unfold read_imem, Memory.read_initial;
        rewrite (read_initial_cons_code_miss Ev.get_msg code (MemReq.address mr) 4
          imem (PPState.mem p) ev); [reflexivity|lia|exact Hcode|]
      end.
      intros msg Hmsg a Ha. specialize (Hmiss a Ha). unfold VMPromisingReadByte in Hmiss.
      rewrite Hmsg in Hmiss. exact Hmiss.
    + intros after ret pre Hout. apply IH. eapply SailThreadPrefix_outcome; [exact Hprefix|exact Hout].
  - intro r. apply IH. eapply SailThreadPrefix_choice. exact Hprefix.
Qed.

Theorem fixed_history_replay (tid : fin n) imem ts mem ts' iis' ev :
  (∀ out, StepReplayR tid imem mem ev out) →
  VMSailNoSelfModifying bbm nondet term initMs code →
  SailThreadPrefix (VMPromising bbm) nondet term initMs tid imem
    (PPState.Make ts mem IIS.init) (sail_tiny_arm_sem nondet) →
  VMViews.ts_ok (length mem) ts →
  event_misses_code VMPromisingReadByte code ev →
  Exec.elem_of_results (PPState.Make ts' mem iis', ())
    (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
      (PPState.Make ts mem IIS.init)) →
  ∀ ts'_e, TState.emit_promise tid imem (ev :: mem) ev ts' = Ok ts'_e →
  ∃ ts_e ppst,
    TState.emit_promise tid imem (ev :: mem) ev ts = Ok ts_e ∧
    Exec.elem_of_results (ppst, ())
      (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
        (PPState.Make ts_e (ev :: mem) IIS.init)) ∧
    PPState.mem ppst = ev :: mem ∧ ts_sim ts'_e (PPState.state ppst).
Proof.
  intros Hstep Hsafe Hprefix Hts Hmiss Hrun ts'_e He'.
  set (p := PPState.Make ts mem IIS.init).
  assert (Hok : VMViews.ok p).
  { split; [exact Hts|]. eapply VMViews.iis_ok_mono; [|apply VMViews.iis_init]. lia. }
  destruct (cinterp_emits tid imem mem ev _ p _ () Hok Hrun (ex_intro _ _ He')) as [ts_e He].
  set (q := PPState.Make ts_e (ev :: mem) IIS.init).
  assert (Hrel : Rel tid imem mem ev p q).
  { apply exact_rel; [exact Hok|]. split; [reflexivity|].
    exists ts_e, 0, None. split; [exact He|]. split; [cbn; discriminate|].
    split; [left; reflexivity|]. reflexivity. }
  destruct (VMRoots.prefix_roots bbm nondet term initMs tid imem _ _ Hprefix) as [_ Hroots].
  destruct (cinterp_replay_steps tid imem mem ev _ p _ () q Hstep
    (prefix_fetches tid imem mem ev _ p Hsafe Hmiss Hprefix) Hok Hroots eq_refl Hrun eq_refl
    (ex_intro _ _ He') Hrel) as [qf [Hqf [q1 [Hex Hsim]]]].
  exists ts_e, qf. split; [exact He|]. split; [exact Hqf|].
  destruct Hex as [_ [issued [stop [inv [He1 [_ [_ ->]]]]]]].
  cbn in He1. rewrite He' in He1. injection He1 as <-.
  destruct Hsim as (Hm & _ & Hs). split; [symmetry; exact Hm|exact Hs].
Qed.
End Sail.

(** * The replay obligation of the normalization *)

Section Bridge.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).

(** Per-outcome replay after any event, for histories the outcome keeps. *)
Definition FixedOutcomeReplay : Prop :=
  ∀ (tid : fin n) imem mem ev out, ¬ covered out → StepReplayR tid imem mem ev out.

(** The creating clause of [VMNormalization.VMInstructionPromiseReplay]. *)
Definition CreatingReplay : Prop :=
  ∀ (tid : fin n) imem ts mem ts' mem' iis' ev,
    VMSailNoSelfModifying bbm nondet term initMs code →
    SailThreadPrefix (VMPromising bbm) nondet term initMs tid imem
      (PPState.Make ts mem IIS.init) (sail_tiny_arm_sem nondet) →
    VMViews.ts_ok (length mem) ts →
    event_misses_code VMPromisingReadByte code ev →
    Exec.elem_of_results (PPState.Make ts' mem' iis', ())
      (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
        (PPState.Make ts mem IIS.init)) →
    ∀ evs, mem' = (evs ++ ev :: mem)%list →
      ∃ ts_e ppst,
        TState.emit_promise tid imem (ev :: mem) ev ts = Ok ts_e ∧
        Exec.elem_of_results (ppst, ())
          (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
            (PPState.Make ts_e (ev :: mem) IIS.init)) ∧
        PPState.mem ppst = mem' ∧ ts_sim ts' (PPState.state ppst).

Theorem instruction_promise_replay :
  FixedOutcomeReplay → CreatingReplay →
  VMNormalization.VMInstructionPromiseReplay bbm nondet term initMs code.
Proof.
  intros Hfixed Hcreate tid imem ts mem ts' mem' iis' ev Hsafe Hprefix Hts Hmiss Hrun.
  split; [eapply Hcreate; eassumption|].
  intros -> Hpositive. eapply fixed_history_replay; [apply steps_of_uncovered, Hfixed|eassumption..].
Qed.

Corollary final_state_equiv :
  FixedOutcomeReplay → CreatingReplay →
  VMNormalization.VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  (∀ initPs fuel returned fsig,
    PState.from_archState (VMPromising bbm) initMs = Ok initPs →
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) (VMPromising bbm) n)
        fuel term initMs initPs) →
    VMNormalization.VMNormalizationSearchesComplete bbm nondet term initMs (projT1 fsig)) →
  (∀ fuel fs (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf_uncached (VMPromising bbm) (sail_tiny_arm_sem nondet)
        fuel n term initMs →
    PromiseFirstSearchesCompleteFromInitial (VMPromising bbm) nondet term initMs fuel) →
  VMPromisingFinalStateEquiv bbm (sail_tiny_arm_sem nondet) term initMs.
Proof.
  intros Hfixed Hcreate. apply VMNormalization.VMSail_promise_first_final_state_equiv.
  apply instruction_promise_replay; assumption.
Qed.
End Bridge.
End VMInstructionReplay.
