(******************************************************************************)
(* Normalizing VM executions into promise-first executions                    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstEquivCurrent
  PromiseFirstExecutionCurrent PromiseFirstVMExecutionCurrent PromiseFirstConcreteCurrent
  PromiseFirstSailCurrent PromiseFirstSailCertification PromiseFirstSailSerialization
  PromiseFirstSailScheduling PromiseFirstSailNoFuel PromiseFirstFreshBroadcast
  PromiseFirstSailVMCacheRefill PromiseFirstSailVMCacheContext PromiseFirstSailVMCacheState
  PromiseFirstSailVMViews PromiseFirstSailVMDirect PromiseFirstSailVMCacheSim
  PromiseFirstSailVMSwap PromiseFirstSailVMEventValidity PromiseFirstSailVMEventCertification.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** This file ports the UM normalization of interleaved direct runs to VM.
    Replaying an instruction after a promise reaches a state equal up to
    observationally equivalent TLB caches ([st_sim]/[pp_sim] of VMCacheSim),
    so every stage carries that simulation instead of equality.

    The development is parameterized by [VMInstructionPromiseReplay], a
    statement about one complete actual Sail instruction. From it, each fresh
    event of an interleaved trace becomes an unreduced promise step, a step
    whose candidate is collected by certification but not yet checked by
    [filter_commuting_promises]. The commutation obligation
    [VMTLBISwapReplay] exchanges an adjacent out-of-order pair of such a
    trace; iterating it along [VMSwap.bubble_sort] makes the trace a
    promise-first trace. [VMSail_full_mixed_normalization] thus moves all
    fresh events and explicit promises of an interleaved trace, in any TLBI
    order, into actual promise-first promise steps from the initial state.
    [VMSail_direct_to_promise_first] transfers the architectural result of an
    actual direct run to the promise-first runner. The final view bound is
    derived from VMViews. The candidate-bearing searches exposed by
    normalization are assumed complete ([VMNormalizationSearchesComplete]).
    [VMSail_promise_first_final_state_equiv] combines this with
    [VMSail_complete_promise_first_final_sound]. *)

Module VMNormalization.
Import VMPromising VMCacheSim VMCacheSimOutcome.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

(** * Simulation of states as an equivalence on well-formed states *)

Lemma ts_ok_min_view bound ts :
  VMViews.ts_ok bound ts → TState.min_new_prom_view ts ≤ bound.
Proof.
  intro Hok. unfold TState.min_new_prom_view.
  pose proof (VMViews.ok_vdsb _ _ Hok). pose proof (VMViews.ok_vspec _ _ Hok).
  pose proof (VMViews.ok_vcse _ _ Hok). unfold join, join_nat in *. lia.
Qed.

Lemma ts_ok_sim_refl bound ts : VMViews.ts_ok bound ts → ts_sim ts ts.
Proof.
  intro Hok. split; [symmetry; apply setv_tlb_same|].
  pose proof (VMViews.ok_cache _ _ Hok) as Hcache.
  destruct (TState.tlb ts) as [c|] eqn:Hc; cbn; [|exact I].
  destruct (Hcache c Hc) as [_ [Hu Hv]]. apply cache_sim_refl. split; assumption.
Qed.

Lemma cache_sim_trans a b c : cache_sim a b → cache_sim b c → cache_sim a c.
Proof.
  unfold cache_sim, VMCacheContext.observational.
  intros [[Hab [Hrab Heab]] [Ha _]] [[Hbc [Hrbc Hebc]] [_ Hc]].
  split; [|split; assumption]. split; [exact (VMCacheRefill.equiv_trans _ _ _ Hab Hbc)|].
  split; [rewrite Hrab; exact Hrbc|rewrite Heab; exact Hebc].
Qed.

Lemma tlb_sim_trans a b c : tlb_sim a b → tlb_sim b c → tlb_sim a c.
Proof.
  destruct a, b, c; cbn; try tauto. apply cache_sim_trans.
Qed.

Lemma ts_sim_trans a b c : ts_sim a b → ts_sim b c → ts_sim a c.
Proof.
  intros [Hb Hab] [Hc Hbc]. split.
  - rewrite Hc, Hb, setv_tlb_twice. reflexivity.
  - eapply tlb_sim_trans; eassumption.
Qed.

Section States.
Context {n : nat}.
Local Notation state := (PState.t TState.t Ev.t n).

Lemma st_sim_refl (s : state) : VMViews.state_ok s → st_sim s s.
Proof.
  intro Hok. split; [reflexivity|]. split; [reflexivity|].
  intro tid. eapply ts_ok_sim_refl, Hok.
Qed.

Lemma st_sim_sym (s1 s2 : state) : st_sim s1 s2 → st_sim s2 s1.
Proof.
  intros (Hi & He & Hs). split; [congruence|]. split; [congruence|].
  intro tid. apply ts_sim_sym, Hs.
Qed.

Lemma st_sim_trans (s1 s2 s3 : state) : st_sim s1 s2 → st_sim s2 s3 → st_sim s1 s3.
Proof.
  intros (Hi & He & Hs) (Hi' & He' & Hs'). split; [congruence|]. split; [congruence|].
  intro tid. eapply ts_sim_trans; [apply Hs|apply Hs'].
Qed.
End States.

(** * Promises on machine states *)

Lemma vimapM_intro {A B E m} (f : fin m → A → result E B) (xs : vec A m) (ys : vec B m) :
  (∀ i, f i (xs !!! i) = Ok (ys !!! i)) → vimapM f xs = Ok ys.
Proof.
  revert f ys. induction xs as [|x m xs IH]; intros f ys.
  - inv_vec ys. reflexivity.
  - inv_vec ys. intros y ys Hf. cbn [vimapM].
    pose proof (Hf 0%fin) as H0. cbn in H0. rewrite H0. cbn.
    rewrite (IH (f ∘ FS) ys (λ i, Hf (FS i))). reflexivity.
Qed.

Lemma run_tlb_frame r ts ts' : TState.run_tlb r ts = Ok ts' → ∃ c, ts' = setv TState.tlb c ts.
Proof.
  unfold TState.run_tlb. destruct (TState.tlb ts) as [c|] eqn:Hc.
  - unfold fmap, result_fmap, mbind, result_bind.
    destruct (r c) as [[c' []]|err]; cbn; [|discriminate].
    injection 1 as <-. eauto.
  - injection 1 as <-. exists (TState.tlb ts). symmetry. apply setv_tlb_same.
Qed.

Lemma emit_promise_pc (t : nat) imem mem ev ts ts' :
  TState.emit_promise t imem mem ev ts = Ok ts' → TState.pc ts' = TState.pc ts.
Proof.
  intro H. pose proof (emit_shape t imem mem ev ts (TState.tlb ts)) as E.
  rewrite setv_tlb_same in E. rewrite E in H.
  apply run_tlb_frame in H as [c ->]. unfold pending.
  destruct (bool_decide _); [destruct ev|]; destruct ts; reflexivity.
Qed.

Section Machine.
Context (bbm : bool) {n : nat}.
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).

Lemma promise_inv ev (s s' : state) : PState.promise prom ev s = Ok s' →
  PState.initmem s' = PState.initmem s ∧ PState.events s' = ev :: PState.events s ∧
  ∀ i : fin n, TState.emit_promise i (PState.initmem s) (ev :: PState.events s) ev
    (PState.tstate i s) = Ok (PState.tstate i s').
Proof.
  unfold PState.promise.
  destruct (vimapM _ _) as [nts|err] eqn:Hmap; cbn; [|discriminate].
  injection 1 as <-. split; [reflexivity|]. split; [reflexivity|].
  intro i. exact (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmap i).
Qed.

Lemma promise_intro ev (s : state) (tss : vec TState.t n) :
  (∀ i : fin n, TState.emit_promise i (PState.initmem s) (ev :: PState.events s) ev
    (PState.tstate i s) = Ok (tss !!! i)) →
  PState.promise prom ev s = Ok (PState.Make tss (PState.initmem s) (ev :: PState.events s)).
Proof.
  intro H. unfold PState.promise. cbn.
  rewrite (vimapM_intro _ _ tss); [reflexivity|]. intro i. apply H.
Qed.

Lemma promise_terminated_tid term ev (s s' : state) t :
  PState.promise prom ev s = Ok s' →
  CPState.terminated_tid prom term s' t = CPState.terminated_tid prom term s t.
Proof.
  intro H. destruct (promise_inv ev s s' H) as [_ [_ Hts]].
  unfold CPState.terminated_tid, CPState.terminated_ts.
  change (pc_terminated (term !!! t) (TState.pc (PState.tstate t s')) =
    pc_terminated (term !!! t) (TState.pc (PState.tstate t s))).
  rewrite (emit_promise_pc _ _ _ _ _ _ (Hts t)). reflexivity.
Qed.

Lemma take_app_last {A} (l r : list A) x :
  take (length (l ++ x :: r)%list - length r) (l ++ x :: r)%list = (l ++ [x])%list.
Proof.
  rewrite length_app. cbn [length].
  replace (length l + S (length r) - length r) with (S (length l)) by lia.
  induction l as [|y l IH]; cbn; [reflexivity|]. f_equal. exact IH.
Qed.

Lemma broadcast_fresh_app_last (owner : fin n) imem base evs ev
    (states states' : vec TState.t n) :
  PState.broadcast_fresh prom owner imem base (evs ++ [ev])%list states = Ok states' →
  ∃ mid,
    vimapM (λ i ts, if decide (i = owner) then mret ts
      else TState.emit_promise i imem (ev :: base) ev ts) states = Ok mid ∧
    PState.broadcast_fresh prom owner imem (ev :: base) evs mid = Ok states'.
Proof.
  revert states'. induction evs as [|e evs IH]; intros states' H.
  - cbn [app PState.broadcast_fresh] in H. cbn [mbind result_bind mret result_ret] in H.
    exists states'. split; [exact H|reflexivity].
  - cbn [app PState.broadcast_fresh] in H |- *.
    destruct (PState.broadcast_fresh prom owner imem base (evs ++ [ev])%list states)
      as [mid'|err] eqn:Hmid'; [|discriminate].
    destruct (IH mid' eq_refl) as [mid [Hmid Hrest]].
    exists mid. split; [exact Hmid|]. rewrite Hrest. cbn [mbind result_bind].
    rewrite <- app_assoc in H. exact H.
Qed.
End Machine.

(** * The single-instruction replay obligation

    A complete actual Sail instruction of thread [tid] runs from an
    instruction boundary [ts] on history [mem] to [ts'] on history [mem'].
    Its replay after an event [ev] was promised with the timestamp
    [S (length mem)] reaches the same history and a thread state related by
    [ts_sim], i.e. equal up to observationally equivalent TLB caches. The
    instruction-local state is not compared: moving a foreign TLBI before a
    load can change the [inv_time] of the lookup result recorded there. The
    promise is delivered to [ts] by the state transformer of
    [PState.promise], [TState.emit_promise].

    - When [ev] is the oldest event created by the instruction, the replay
      reaches a state simulating the original one.
    - When the instruction creates no event, the replay reaches a state
      simulating the original endpoint after [ev] is delivered to it. The
      delivery at the original endpoint is assumed to succeed, and the
      earlier delivery is part of the conclusion. Any write in [ev] has
      positive size, as proved for the certification candidates used here.

    The premises give code immutability, the actual Sail thread prefix of the
    starting state, its view and cache invariant, and immutability of the code
    under [ev]. *)
Definition VMInstructionPromiseReplay (bbm nondet : bool) {n : nat}
    (term : terminationCondition n) (initMs : archState n) (code : code_region) : Prop :=
  ∀ (tid : fin n) imem ts mem ts' mem' iis' ev,
    VMSailNoSelfModifying bbm nondet term initMs code →
    SailThreadPrefix (VMPromising bbm) nondet term initMs tid imem
      (PPState.Make ts mem IIS.init) (sail_tiny_arm_sem nondet) →
    VMViews.ts_ok (length mem) ts →
    event_misses_code VMPromisingReadByte code ev →
    Exec.elem_of_results (PPState.Make ts' mem' iis', ())
      (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
        (PPState.Make ts mem IIS.init)) →
    (∀ evs, mem' = (evs ++ ev :: mem)%list →
      ∃ ts_e ppst,
        TState.emit_promise tid imem (ev :: mem) ev ts = Ok ts_e ∧
        Exec.elem_of_results (ppst, ())
          (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
            (PPState.Make ts_e (ev :: mem) IIS.init)) ∧
        PPState.mem ppst = mem' ∧ ts_sim ts' (PPState.state ppst)) ∧
    (mem' = mem → VMEventValidity.event_positive ev → ∀ ts'_e,
      TState.emit_promise tid imem (ev :: mem) ev ts' = Ok ts'_e →
      ∃ ts_e ppst,
        TState.emit_promise tid imem (ev :: mem) ev ts = Ok ts_e ∧
        Exec.elem_of_results (ppst, ())
          (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet)
            (PPState.Make ts_e (ev :: mem) IIS.init)) ∧
        PPState.mem ppst = ev :: mem ∧ ts_sim ts'_e (PPState.state ppst)).

Lemma tstate_make {n} (u : fin n) (v : vec TState.t n) imem (mem : list Ev.t) :
  PState.tstate u (PState.Make v imem mem) = v !!! u.
Proof. reflexivity. Qed.

(** * Execution traces *)

Section Traces.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n).
Local Notation prom := (VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation Inst := (InstructionTransition prom nondet term).

Definition Fixed (s s' : state) : Prop := Inst s s' ∧ PState.events s' = PState.events s.

Definition PromStep (s s' : state) : Prop :=
  ∃ fuel, Exec.elem_of_results (s', None)
    (CPState.run_transition_promise_first_uncached isem prom term fuel s).

(** A promise step of the unreduced runner: the event is collected by a
    certification run of its thread, before [filter_commuting_promises]. *)
Definition RawCandidate (s : state) (tid : fin n) (fuel : nat) (ev : Ev.t) : Prop :=
  ev ∈ (CPState.enumerate_results isem prom term tid (PState.initmem s) fuel
    (PState.tstate tid s) (PState.events s)).(CPState.promises prom).

Definition RawStep (ev : Ev.t) (s s' : state) : Prop :=
  (∃ tid fuel, RawCandidate s tid fuel ev) ∧ PState.promise prom ev s = Ok s'.

Definition RawPromStep (s s' : state) : Prop := ∃ ev, RawStep ev s s'.

(** Interleavings of instructions and unreduced promise steps. *)
Definition Mixed (s s' : state) : Prop := Inst s s' ∨ RawPromStep s s'.

(** Interleavings of instructions and promise-first promise steps. *)
Definition FMixed (s s' : state) : Prop := Inst s s' ∨ PromStep s s'.

Lemma enumerate_filtered_promises tid imem fuel ts mem :
  (CPState.enumerate_results_filtered isem prom term tid imem fuel ts mem)
    .(CPState.promises prom) =
  filter_commuting_promises n tid mem
    (CPState.enumerate_results isem prom term tid imem fuel ts mem).(CPState.promises prom).
Proof. reflexivity. Qed.

Lemma enumerate_raw_terminated tid imem fuel ts mem :
  CPState.terminated_ts prom (term !!! tid) ts = true →
  (CPState.enumerate_results isem prom term tid imem fuel ts mem).(CPState.promises prom) = [].
Proof.
  intro Hterm. unfold CPState.enumerate_results.
  destruct fuel; cbn [CPState.run_to_termination];
    unfold mget, mGet, mcall, mbind, fmap,
      Exec.mbind_inst, Exec.fmap_inst, Exec.st_call_MState,
      Exec.res_mbind_inst, Exec.res_fmap_inst;
    cbn -[CPState.terminated_ts];
    rewrite Hterm;
    case_decide; reflexivity.
Qed.

Lemma promstep_raw s s' : PromStep s s' → RawPromStep s s'.
Proof.
  intros [fuel Hrun].
  destruct (run_transition_promise_first_none_inv (prom := prom) isem term fuel s s' Hrun)
    as [tid [ev [nst [Hcand [Hp ->]]]]].
  rewrite promise_first_execution_results_lookup in Hcand.
  exists ev. split; [|exact Hp]. exists tid, fuel. unfold RawCandidate.
  change (CPState.initmem s) with (PState.initmem s) in Hcand.
  change (CPState.events s) with (PState.events s) in Hcand.
  rewrite enumerate_filtered_promises in Hcand.
  eapply (VMPromising_filter_promises_subset bbm). exact Hcand.
Qed.

Lemma rawstep_prom ev s s' : RawStep ev s s' →
  (∀ last rest, PState.events s = last :: rest → Ev.out_of_order last ev = false) →
  PromStep s s'.
Proof.
  intros [[tid [fuel Hc]] Hp] Hs. exists fuel.
  eapply (run_transition_promise_first_none_intro (prom := prom))
    with (tid := tid) (ev := ev) (nst := s'); [|exact Hp|reflexivity].
  rewrite promise_first_execution_results_lookup.
  change (CPState.initmem s) with (PState.initmem s).
  change (CPState.events s) with (PState.events s).
  rewrite enumerate_filtered_promises. unfold RawCandidate in Hc.
  unfold filter_commuting_promises.
  destruct (PState.events s) as [|last rest] eqn:He; [exact Hc|].
  apply list_elem_of_filter. split; [|exact Hc]. rewrite (Hs last rest eq_refl). reflexivity.
Qed.

Lemma enum_raw_promises_sim tid imem fuel ts1 ts2 mem ev : ts_sim ts1 ts2 →
  ev ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid imem fuel ts1 mem) →
  ev ∈ CPState.promises prom (CPState.enumerate_results isem prom term tid imem fuel ts2 mem).
Proof.
  intro Hs. destruct (run_to_termination_sim bbm isem term tid imem fuel (length mem))
    as [Hr He].
  pose proof (enum_init_sim ts1 ts2 mem Hs) as Hinit.
  unfold CPState.enumerate_results. cbn [CPState.promises].
  intro H. apply (proj2 (elem_of_remove_dups _ _)). apply (proj1 (elem_of_remove_dups _ _)) in H.
  apply (proj1 (concat_elem _ _)) in H as (l & Hl & Hx). apply (proj2 (concat_elem _ _)).
  exists l. split; [|exact Hx].
  apply elem_of_app in Hl as [Hl|Hl]; apply elem_of_app.
  - left. unfold Exec.success_state_list in *.
    apply list_elem_of_fmap in Hl as [[l' p] [-> Hl]].
    apply list_elem_of_fmap in Hl as [[[l'' p'] r] [Heq Hl]].
    injection Heq as -> ->.
    destruct (Hr _ _ (l'', p') r Hinit Hl) as ((l2 & p2) & r2 & Hin2 & [Hl2 _] & <-).
    cbn in Hl2. subst l2.
    apply list_elem_of_fmap. exists (l'', p2). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((l'', p2), r). split; [reflexivity|exact Hin2].
  - right. apply list_elem_of_fmap in Hl as [[l' p] [-> Hl]].
    apply list_elem_of_fmap in Hl as [[[l'' p'] e] [Heq Hl]]. injection Heq as -> ->.
    destruct (He _ _ (l'', p') e Hinit Hl) as ((l2 & p2) & e2 & Hin2 & [Hl2 _]).
    cbn in Hl2. subst l2.
    apply list_elem_of_fmap. exists (l'', p2). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((l'', p2), e2). split; [reflexivity|exact Hin2].
Qed.

Lemma raw_promise_witness tid imem fuel ts mem ev :
  ev ∈ (CPState.enumerate_results isem prom term tid imem fuel ts mem).(CPState.promises prom) →
  ∃ proms ppst, ev ∈ proms ∧
    ((∃ ending, Exec.elem_of_results ((proms, ppst), ending)
      (CPState.run_to_termination isem prom term tid imem fuel (length mem)
        ([], PPState.Make ts mem IIS.init))) ∨
     (∃ err, ((proms, ppst), err) ∈ Exec.errors
      (CPState.run_to_termination isem prom term tid imem fuel (length mem)
        ([], PPState.Make ts mem IIS.init)))).
Proof.
  unfold CPState.enumerate_results. cbn [CPState.promises].
  intro H. apply (proj1 (elem_of_remove_dups _ _)) in H.
  apply (proj1 (concat_elem _ _)) in H as (l & Hl & Hx).
  apply elem_of_app in Hl as [Hl|Hl].
  - unfold Exec.success_state_list in Hl.
    apply list_elem_of_fmap in Hl as [[l' p] [-> Hl]].
    apply list_elem_of_fmap in Hl as [[[l'' p'] r] [Heq Hl]]. injection Heq as -> ->.
    exists l'', p'. split; [exact Hx|]. left. exists r. exact Hl.
  - apply list_elem_of_fmap in Hl as [[l' p] [-> Hl]].
    apply list_elem_of_fmap in Hl as [[[l'' p'] e] [Heq Hl]]. injection Heq as -> ->.
    exists l'', p'. split; [exact Hx|]. right. exists e. exact Hl.
Qed.

(** Raw candidates of reachable states miss the immutable code. *)
Lemma raw_candidate_misses_code initMs code s tid fuel ev :
  VMPromisingNoSelfModifying bbm isem term initMs code →
  PromiseFirstReachable prom isem term initMs true s →
  RawCandidate s tid fuel ev → event_misses_code VMPromisingReadByte code ev.
Proof.
  intros Hsafe Hreach Hev.
  destruct (raw_promise_witness tid (PState.initmem s) fuel (PState.tstate tid s)
    (PState.events s) ev Hev) as [new_proms [ppst [Hin Hrun]]].
  assert (Hobserved : PromiseFirstObservedHistory prom isem term initMs
    (new_proms ++ PPState.mem ppst)).
  { destruct Hrun as [[ending Hrun]|[err Hrun]].
    - eapply PromiseFirstObservedHistory_success; eauto.
    - eapply PromiseFirstObservedHistory_error; eauto. }
  apply (Hsafe _ Hobserved). apply elem_of_app. left. exact Hin.
Qed.

Lemma inst_ok s s' : VMViews.state_ok s → Inst s s' → VMViews.state_ok s'.
Proof. intros Hok [t [_ Hrun]]. eapply VMViews.run_tid_ok; eassumption. Qed.

Lemma promstep_ok s s' : VMViews.state_ok s → PromStep s s' → VMViews.state_ok s'.
Proof.
  intros Hok [fuel Hrun]. eapply (VMViews.transition_ok bbm isem term true); eassumption.
Qed.

Lemma rawstep_ok ev s s' : VMViews.state_ok s → RawStep ev s s' → VMViews.state_ok s'.
Proof. intros Hok [_ Hp]. eapply VMViews.promise_ok; eassumption. Qed.

Lemma rawstep_memory ev s s' : RawStep ev s s' →
  PState.initmem s' = PState.initmem s ∧ PState.events s' = ev :: PState.events s.
Proof. intros [_ Hp]. destruct (promise_inv bbm ev s s' Hp) as [Hi [He _]]. auto. Qed.

Lemma mixed_ok s s' : VMViews.state_ok s → Mixed s s' → VMViews.state_ok s'.
Proof. intros Hok [H|[ev H]]; [eapply inst_ok|eapply rawstep_ok]; eassumption. Qed.

Lemma mixed_rtc_ok s s' : VMViews.state_ok s → rtc Mixed s s' → VMViews.state_ok s'.
Proof. intros Hok H. induction H; [exact Hok|]. apply IHrtc. eapply mixed_ok; eassumption. Qed.

Lemma inst_memory s s' : Inst s s' →
  PState.initmem s' = PState.initmem s ∧ ∃ extra, PState.events s' = (extra ++ PState.events s)%list.
Proof.
  intros [t [_ Hrun]].
  destruct (run_tid_broadcast_decompose prom isem t s s' Hrun)
    as [ts [mem [iis [states [Hinst [_ ->]]]]]].
  split; [reflexivity|]. cbn [PState.events].
  destruct (VMFinalCertification.instruction_memory_suffix t (PState.initmem s) isem _ _ () Hinst)
    as [extra Hextra]. exists extra. exact Hextra.
Qed.

Lemma promstep_memory s s' : PromStep s s' →
  PState.initmem s' = PState.initmem s ∧ ∃ ev, PState.events s' = ev :: PState.events s.
Proof.
  intros [fuel Hrun].
  destruct (run_transition_promise_first_none_inv (prom := prom) isem term fuel s s' Hrun)
    as [tid [ev [nst [_ [Hpromise ->]]]]].
  destruct (promise_inv bbm ev s nst Hpromise) as [Hi [He _]].
  split; [exact Hi|]. exists ev. exact He.
Qed.

Lemma mixed_memory s s' : Mixed s s' →
  PState.initmem s' = PState.initmem s ∧ ∃ extra, PState.events s' = (extra ++ PState.events s)%list.
Proof.
  intros [H|[ev H]]; [apply inst_memory, H|].
  destruct (rawstep_memory ev s s' H) as [Hi He]. split; [exact Hi|]. exists [ev]. exact He.
Qed.

Lemma mixed_rtc_memory s s' : rtc Mixed s s' →
  PState.initmem s' = PState.initmem s ∧ ∃ extra, PState.events s' = (extra ++ PState.events s)%list.
Proof.
  intro H. induction H as [s|s mid s' Hstep _ [Hi [extra He]]].
  - split; [reflexivity|]. exists []. reflexivity.
  - destruct (mixed_memory s mid Hstep) as [Hi' [extra' He']].
    split; [congruence|]. exists (extra ++ extra')%list. rewrite He, He', app_assoc. reflexivity.
Qed.

Lemma mixed_fixed s s' : Mixed s s' → PState.events s' = PState.events s → Fixed s s'.
Proof.
  intros [H|[ev H]] Hsame; [split; assumption|].
  destruct (rawstep_memory ev s s' H) as [_ He]. rewrite Hsame in He.
  apply (f_equal length) in He. cbn in He. lia.
Qed.

Lemma mixed_rtc_fixed s s' : rtc Mixed s s' → PState.events s' = PState.events s → rtc Fixed s s'.
Proof.
  intro H. induction H as [s|s mid s' Hstep Htail IH]; intro Hsame; [apply rtc_refl|].
  destruct (mixed_rtc_memory mid s' Htail) as [_ [extra He]].
  destruct (mixed_memory s mid Hstep) as [_ [extra' He']].
  assert (Hnil : extra' = []).
  { rewrite He', Hsame in He. apply (f_equal length) in He. rewrite !length_app in He.
    destruct extra'; [reflexivity|cbn in He; lia]. }
  subst extra'. rewrite app_nil_l in He'.
  eapply rtc_l; [exact (mixed_fixed s mid Hstep He')|]. apply IH. congruence.
Qed.

Lemma first_mixed_event s s' : rtc Mixed s s' → PState.events s' ≠ PState.events s →
  ∃ b a, rtc Fixed s b ∧ Mixed b a ∧ PState.events a ≠ PState.events b ∧ rtc Mixed a s'.
Proof.
  intro H. induction H as [s|s mid s' Hstep Htail IH]; intro Hnew; [contradiction|].
  destruct (decide (PState.events mid = PState.events s)) as [Hsame|Hdiff].
  - destruct (IH ltac:(rewrite Hsame; exact Hnew)) as [b [a [Hpre Hrest]]].
    exists b, a. split; [|exact Hrest]. eapply rtc_l; [apply mixed_fixed; eassumption|exact Hpre].
  - exists s, mid. split; [apply rtc_refl|]. auto.
Qed.

Lemma fixed_rtc_ok s s' : VMViews.state_ok s → rtc Fixed s s' → VMViews.state_ok s'.
Proof. intros Hok H. induction H; [exact Hok|]. apply IHrtc. eapply inst_ok; [exact Hok|apply H]. Qed.

Lemma fixed_rtc_mixed s s' : rtc Fixed s s' → rtc Mixed s s'.
Proof. intro H. induction H; [apply rtc_refl|]. eapply rtc_l; [left; apply H|exact IHrtc]. Qed.

Lemma inst_rtc_mixed s s' : rtc Inst s s' → rtc Mixed s s'.
Proof. intro H. induction H; [apply rtc_refl|]. eapply rtc_l; [left; exact H|exact IHrtc]. Qed.

(** Simulated states admit simulated traces. *)
Lemma inst_rtc_sim s1 s2 s1' : st_sim s1 s2 → rtc Inst s1 s1' →
  ∃ s2', rtc Inst s2 s2' ∧ st_sim s1' s2'.
Proof.
  intros Hs H. revert s2 Hs. induction H as [s|s mid s' Hstep _ IH]; intros s2 Hs.
  - exists s2. split; [apply rtc_refl|exact Hs].
  - destruct (instruction_transition_sim bbm nondet term s s2 mid Hs Hstep) as [mid2 [H2 Hmid]].
    destruct (IH mid2 Hmid) as [s2' [Hs2' Hfin]].
    exists s2'. split; [eapply rtc_l; eassumption|exact Hfin].
Qed.

Lemma mixed_sim s1 s2 s1' : st_sim s1 s2 → VMViews.state_ok s1 → Mixed s1 s1' →
  ∃ s2', Mixed s2 s2' ∧ st_sim s1' s2'.
Proof.
  intros Hs Hok [H|[ev [[tid [fuel Hc]] Hp]]].
  - destruct (instruction_transition_sim bbm nondet term s1 s2 s1' Hs H) as [s2' [H2 Hs']].
    exists s2'. split; [left; exact H2|exact Hs'].
  - destruct (promise_sim bbm ev s1 s2 s1' Hs Hp) as [s2' [Hp2 Hs']].
    exists s2'. split; [|exact Hs']. right. exists ev. split; [|exact Hp2].
    exists tid, fuel. destruct Hs as (Hi & He & Hst). unfold RawCandidate in *.
    rewrite <- Hi, <- He. eapply enum_raw_promises_sim; [apply Hst|exact Hc].
Qed.

Lemma mixed_rtc_sim s1 s2 s1' : st_sim s1 s2 → VMViews.state_ok s1 → rtc Mixed s1 s1' →
  ∃ s2', rtc Mixed s2 s2' ∧ st_sim s1' s2'.
Proof.
  intros Hs Hok H. revert s2 Hs. induction H as [s|s mid s' Hstep _ IH]; intros s2 Hs.
  - exists s2. split; [apply rtc_refl|exact Hs].
  - destruct (mixed_sim s s2 mid Hs Hok Hstep) as [mid2 [H2 Hmid]].
    destruct (IH (mixed_ok s mid Hok Hstep) mid2 Hmid) as [s2' [Hs2' Hfin]].
    exists s2'. split; [eapply rtc_l; eassumption|exact Hfin].
Qed.

(** * Thread projections of fixed-history traces *)

Inductive tsteps (tid : fin n) imem (mem : list Ev.t) : nat → TState.t → TState.t → Prop :=
| tsteps_zero ts : tsteps tid imem mem 0 ts ts
| tsteps_succ count ts mid fin iis :
    TState.min_new_prom_view ts ≤ length mem →
    CPState.terminated_ts prom (term !!! tid) ts = false →
    Exec.elem_of_results (PPState.Make mid mem iis, ())
      (cinterp (run_outcome' n tid imem) isem (PPState.Make ts mem IIS.init)) →
    tsteps tid imem mem count mid fin →
    tsteps tid imem mem (S count) ts fin.

Lemma tsteps_trans tid imem mem c1 ts mid : tsteps tid imem mem c1 ts mid →
  ∀ c2 fin, tsteps tid imem mem c2 mid fin → tsteps tid imem mem (c1 + c2) ts fin.
Proof.
  intro H. induction H as [ts|count ts mid' fin' iis Hb Ht Hi Htail IH]; intros c2 fin H2;
    [exact H2|]. cbn. econstructor; [exact Hb|exact Ht|exact Hi|apply IH, H2].
Qed.

Lemma fixed_projection s b : VMViews.state_ok s → rtc Fixed s b →
  PState.initmem b = PState.initmem s ∧ PState.events b = PState.events s ∧
  ∀ tid, ∃ count, tsteps tid (PState.initmem s) (PState.events s) count
    (PState.tstate tid s) (PState.tstate tid b).
Proof.
  intros Hok H. induction H as [s|s mid b Hstep Htail IH].
  - split; [reflexivity|]. split; [reflexivity|]. intro tid. exists 0. constructor.
  - destruct (IH (inst_ok s mid Hok (proj1 Hstep))) as [Hi [He Hthreads]].
    destruct Hstep as [[t [Hterm Hrun]] Hsame].
    destruct (run_tid_decompose_fixed prom isem t s mid Hrun Hsame)
      as [ts' [mem [iis [Hinst Hmid]]]].
    subst mid. cbn [PState.events] in Hsame. subst mem.
    cbn [PState.events PState.initmem] in Hi, He, Hthreads |- *. split; [exact Hi|]. split; [exact He|]. intro tid.
    destruct (Hthreads tid) as [count Hcount]. rewrite tstate_make in Hcount.
    destruct (decide (t = tid)) as [<-|Hne].
    + rewrite vlookup_insert in Hcount. exists (S count).
      econstructor; [|exact Hterm|exact Hinst|exact Hcount].
      apply (ts_ok_min_view _ _ (Hok t)).
    + rewrite vlookup_insert_ne in Hcount by exact Hne. exists count. exact Hcount.
Qed.

(** * Certification of thread prefixes *)

Lemma rtt_step_intro tid imem fuel base proms ts mem iis mid x :
  TState.min_new_prom_view ts ≤ base →
  CPState.terminated_ts prom (term !!! tid) ts = false →
  Exec.elem_of_results (mid, ())
    (cinterp (CPState.run_outcome_with_promise prom tid imem base) isem
      (proms, PPState.Make ts mem IIS.init)) →
  Exec.elem_of_results x (CPState.run_to_termination isem prom term tid imem fuel base mid) →
  Exec.elem_of_results x
    (CPState.run_to_termination isem prom term tid imem (S fuel) base
      (proms, PPState.Make ts mem iis)).
Proof.
  intros Hb Ht Hi Hr. destruct x as [st r].
  cbn [CPState.run_to_termination].
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  cbn -[CPState.terminated_ts]. rewrite decide_False by lia. rewrite Ht.
  eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mset|].
  eapply Exec.elem_of_bind_intro; [exact Hi|apply (retained_candidate_continue prom); exact Hr].
Qed.

Lemma rtt_zero_intro tid imem base proms ts mem iis :
  ∃ r, Exec.elem_of_results ((proms, PPState.Make ts mem iis), r)
    (CPState.run_to_termination isem prom term tid imem 0 base (proms, PPState.Make ts mem iis)).
Proof.
  destruct (decide (base < TState.min_new_prom_view ts)) as [Hb|Hb];
    [|destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Ht].
  all: eexists; cbn [CPState.run_to_termination].
  all: eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
  all: cbn -[CPState.terminated_ts].
  - rewrite decide_True by exact Hb. apply Exec.elem_of_mret.
  - rewrite decide_False by exact Hb. rewrite Ht. apply Exec.elem_of_mret.
  - rewrite decide_False by exact Hb. rewrite Ht. apply Exec.elem_of_mret.
Qed.

Lemma rtt_zero_proms tid imem base proms ppst proms' ppst' r :
  Exec.elem_of_results ((proms', ppst'), r)
    (CPState.run_to_termination isem prom term tid imem 0 base (proms, ppst)) →
  proms' = proms.
Proof.
  intro H. cbn [CPState.run_to_termination] in H.
  apply Exec.elem_of_bind_elim in H as [mid [ts0 [Hget H]]].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  destruct (decide _); [|destruct (CPState.terminated_ts _ _ _)].
  all: apply Exec.elem_of_mret_inv in H as [Heq _]; injection Heq as -> _; reflexivity.
Qed.

Lemma rtt_zero_errors tid imem base proms ppst x :
  x ∈ Exec.errors (CPState.run_to_termination isem prom term tid imem 0 base (proms, ppst)) →
  False.
Proof.
  intro H. cbn [CPState.run_to_termination] in H.
  apply exec_error_bind in H as [H|[mid [ts0 [Hget H]]]];
    [change (x ∈ []) in H; inversion H|].
  apply Exec.elem_of_mget_inv in Hget as [-> ->].
  destruct (decide _); [|destruct (CPState.terminated_ts _ _ _)].
  all: change (x ∈ []) in H; inversion H.
Qed.

Lemma fixed_prefix_truncated tid imem mem count ts fin :
  tsteps tid imem mem count ts fin →
  TState.min_new_prom_view fin ≤ length mem →
  CPState.terminated_ts prom (term !!! tid) fin = false →
  ∀ iis0, ∃ iis,
    Exec.elem_of_results (([], PPState.Make fin mem iis), CPState.OutOfFuel)
      (CPState.run_to_termination isem prom term tid imem count (length mem)
        ([], PPState.Make ts mem iis0)).
Proof.
  intro H. induction H as [ts|count ts mid fin iis Hb Ht Hi Htail IH];
    intros Hbound Hterm iis0.
  - exists iis0. cbn [CPState.run_to_termination].
    eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mget|].
    cbn -[CPState.terminated_ts]. rewrite decide_False by lia. rewrite Hterm.
    apply Exec.elem_of_mret.
  - destruct (IH Hbound Hterm iis) as [last Hlast]. exists last.
    eapply rtt_step_intro; [exact Hb|exact Ht| |exact Hlast].
    exact (VMFinalCertification.collect_unchanged_instruction bbm tid imem isem []
      (PPState.Make ts mem IIS.init) (PPState.Make mid mem iis) () Hi eq_refl).
Qed.

Lemma rtt_iis_irrelevant tid imem fuel ts mem iis iis' :
  TState.min_new_prom_view ts ≤ length mem →
  CPState.terminated_ts prom (term !!! tid) ts = false →
  CPState.run_to_termination isem prom term tid imem (S fuel) (length mem)
    ([], PPState.Make ts mem iis) =
  CPState.run_to_termination isem prom term tid imem (S fuel) (length mem)
    ([], PPState.Make ts mem iis').
Proof.
  intros Hbound Hterm. cbn [CPState.run_to_termination].
  unfold mget, mGet, mcall, mbind, fmap,
    Exec.mbind_inst, Exec.fmap_inst, Exec.st_call_MState,
    Exec.res_mbind_inst, Exec.res_fmap_inst.
  cbn -[CPState.terminated_ts].
  rewrite (decide_False (P := length mem < TState.min_new_prom_view ts))
    by (apply Nat.le_ngt; exact Hbound).
  rewrite Hterm. reflexivity.
Qed.

Lemma rtt_error_continue tid imem fuel extra base proms ppst proms_mid ppst_mid
    proms' ppst' err :
  Exec.elem_of_results ((proms_mid, ppst_mid), CPState.OutOfFuel)
    (CPState.run_to_termination isem prom term tid imem fuel base (proms, ppst)) →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_to_termination isem prom term tid imem extra base (proms_mid, ppst_mid)) →
  ((proms', ppst'), err) ∈ Exec.errors
    (CPState.run_to_termination isem prom term tid imem (fuel + extra) base (proms, ppst)).
Proof.
  revert proms ppst.
  induction fuel as [|fuel IH]; intros proms [ts mem iis] Hprefix Hsuffix.
  - cbn [CPState.run_to_termination] in Hprefix.
    apply Exec.elem_of_bind_elim in Hprefix as [mid [ts0 [Hget Hprefix]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    cbn -[CPState.terminated_ts] in Hprefix.
    destruct (decide (base < TState.min_new_prom_view ts)).
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
      rewrite Hterm in Hprefix.
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    apply Exec.elem_of_mret_inv in Hprefix as [Heq _].
    injection Heq as <- <-. exact Hsuffix.
  - cbn [CPState.run_to_termination] in Hprefix |- *.
    apply Exec.elem_of_bind_elim in Hprefix as [mid [ts0 [Hget Hprefix]]].
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
    apply exec_error_bind; right.
    exists (proms, PPState.Make ts mem iis), ts. split.
    { exact (Exec.elem_of_mget (proms, PPState.Make ts mem iis) (PPState.state ∘ snd)). }
    cbn -[CPState.terminated_ts] in Hprefix |- *.
    destruct (decide (base < TState.min_new_prom_view ts)).
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    destruct (CPState.terminated_ts prom (term !!! tid) ts) eqn:Hterm;
      rewrite Hterm in Hprefix |- *.
    { apply Exec.elem_of_mret_inv in Hprefix as [_ Hbad]. discriminate. }
    apply Exec.elem_of_bind_elim in Hprefix as [reset [[] [Hreset Hprefix]]].
    apply Exec.elem_of_mset_inv in Hreset as ->.
    apply exec_error_bind; right. eexists _, (). split; [apply Exec.elem_of_mset|].
    apply Exec.elem_of_bind_elim in Hprefix
      as [[proms_next ppst_next] [[] [Hinst Hprefix]]].
    apply exec_error_bind; right. exists (proms_next, ppst_next), ().
    split; [exact Hinst|]. rewrite (retained_candidate_errors prom).
    apply (retained_candidate_result prom) in Hprefix as [[_ [_ Hbad]]|Hprefix]; [discriminate|].
    eapply IH; eassumption.
Qed.

(** The oldest event of the first outcome that extends memory is collected. *)
Lemma collect_first_new {A} (tid : fin n) imem (mon : iMon A) proms ppst ppst' ret evs ev :
  Exec.elem_of_results (ppst', ret) (cinterp (run_outcome' n tid imem) mon ppst) →
  PPState.mem ppst' = (evs ++ ev :: PPState.mem ppst)%list →
  ∃ proms', ev ∈ proms' ∧ Exec.elem_of_results ((proms', ppst'), ret)
    (cinterp (CPState.run_outcome_with_promise prom tid imem (length (PPState.mem ppst)))
      mon (proms, ppst)).
Proof.
  revert proms ppst ppst' ret evs.
  induction mon as [a|call k IH]; intros proms ppst ppst' ret evs Hrun Hmem.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _].
    apply (f_equal length) in Hmem. rewrite length_app in Hmem. cbn in Hmem. lia.
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Htail]]].
      apply Exec.elem_of_fmap_inv in Hout as [[r pre] [Heq Hout]]. cbn in Heq. subst res.
      destruct (VMFinalCertification.instruction_memory_suffix tid imem (k r) mid ppst' ret Htail)
        as [later Hlater].
      destruct (VMMemoryGrowth.outcome_memory_growth bbm n tid imem out ppst mid r pre Hout)
        as [Hsame|[added [pre' [Hnonempty [Hadded [-> Hpre]]]]]].
      * pose proof (collect_outcome_intro prom tid imem
          (length (PPState.mem ppst)) out proms ppst mid r pre Hout) as Hcollect.
        rewrite Hsame, Nat.sub_diag in Hcollect. cbn [take app] in Hcollect.
        assert (Hcollect' : Exec.elem_of_results ((proms, mid), r)
          (CPState.run_outcome_with_promise prom tid imem
            (length (PPState.mem ppst)) out (proms, ppst))).
        { destruct pre as [p|]; [destruct (decide (p ≤ length (PPState.mem ppst)))|];
            exact Hcollect. }
        rewrite <- Hsame in Hmem.
        destruct (IH r proms mid ppst' ret evs Htail Hmem) as [proms' [Hin Htail']].
        exists proms'. split; [exact Hin|].
        eapply Exec.elem_of_bind_intro; [exact Hcollect'|]. rewrite <- Hsame. exact Htail'.
      * pose proof (collect_outcome_intro prom tid imem
          (length (PPState.mem ppst)) out proms ppst mid r (Some pre') Hout) as Hcollect.
        rewrite decide_True in Hcollect by exact Hpre.
        rewrite Hadded, length_app, Nat.add_sub, take_app_length in Hcollect.
        destruct (collect_instruction_complete prom tid imem (length (PPState.mem ppst))
          (k r) (added ++ proms)%list mid ppst' ret Htail) as [proms' Htail'].
        destruct (collect_instruction_suffix prom tid imem (length (PPState.mem ppst))
          (k r) _ _ _ _ _ Htail') as [rest Hrest].
        exists proms'. split.
        -- rewrite Hrest. apply elem_of_app. right. apply elem_of_app. left.
           rewrite Hlater, Hadded, app_assoc in Hmem.
           replace (evs ++ ev :: PPState.mem ppst)%list
             with ((evs ++ [ev]) ++ PPState.mem ppst)%list in Hmem
             by (rewrite <- app_assoc; reflexivity).
           apply app_inv_tail in Hmem.
           destruct (exists_last Hnonempty) as [added' [x Hx]]. rewrite Hx in Hmem |- *.
           rewrite app_assoc in Hmem. apply app_inj_tail in Hmem as [_ ->].
           apply elem_of_app. right. left.
        -- eapply Exec.elem_of_bind_intro; [exact Hcollect|exact Htail'].
    + apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      destruct (IH r proms ppst ppst' ret evs Htail Hmem) as [proms' [Hin Hcollect]].
      exists proms'. split; [exact Hin|].
      eapply Exec.elem_of_bind_intro; [apply Exec.elem_of_mchoose|exact Hcollect].
Qed.

Lemma candidate_intro tid imem fuel ts mem ev proms ppst ending :
  ev ∈ proms →
  Exec.elem_of_results ((proms, ppst), ending)
    (CPState.run_to_termination isem prom term tid imem fuel (length mem)
      ([], PPState.Make ts mem IIS.init)) →
  ev ∈ (CPState.enumerate_results isem prom term tid imem fuel ts mem)
    .(CPState.promises prom).
Proof.
  intros Hev Hrun.
  exact (collected_promise_in_raw_candidates prom nondet term tid imem fuel ts mem
    ev proms ppst ending Hev Hrun).
Qed.

Lemma candidate_first_new tid imem mem count ts tsb ts' evs ev iis' :
  tsteps tid imem mem count ts tsb →
  TState.min_new_prom_view tsb ≤ length mem →
  CPState.terminated_ts prom (term !!! tid) tsb = false →
  Exec.elem_of_results (PPState.Make ts' (evs ++ ev :: mem)%list iis', ())
    (cinterp (run_outcome' n tid imem) isem (PPState.Make tsb mem IIS.init)) →
  ev ∈ (CPState.enumerate_results isem prom term tid imem (count + 1) ts mem)
    .(CPState.promises prom).
Proof.
  intros Hsteps Hbound Hterm Hinst.
  destruct (fixed_prefix_truncated tid imem mem count ts tsb Hsteps Hbound Hterm IIS.init)
    as [iis Htr].
  destruct (collect_first_new tid imem isem [] (PPState.Make tsb mem IIS.init)
    (PPState.Make ts' (evs ++ ev :: mem)%list iis') () evs ev Hinst eq_refl)
    as [proms' [Hin Hc]].
  destruct (rtt_zero_intro tid imem (length mem) proms' ts' (evs ++ ev :: mem)%list iis')
    as [r Hz].
  pose proof (rtt_step_intro tid imem 0 (length mem) [] tsb mem iis _ _ Hbound Hterm Hc Hz)
    as Hone.
  eapply candidate_intro; [exact Hin|].
  exact (out_of_fuel_certification_continue prom nondet term tid imem count 1 (length mem)
    [] (PPState.Make ts mem IIS.init) [] (PPState.Make tsb mem iis) proms' _ r Htr Hone).
Qed.

Lemma candidate_before_prefix tid imem mem count ts tsb fuel ev :
  tsteps tid imem mem count ts tsb →
  TState.min_new_prom_view tsb ≤ length mem →
  ev ∈ (CPState.enumerate_results isem prom term tid imem fuel tsb mem)
    .(CPState.promises prom) →
  ev ∈ (CPState.enumerate_results isem prom term tid imem (count + fuel) ts mem)
    .(CPState.promises prom).
Proof.
  intros Hsteps Hbound Hc.
  destruct (CPState.terminated_ts prom (term !!! tid) tsb) eqn:Hterm.
  { rewrite (enumerate_raw_terminated tid imem fuel tsb mem Hterm) in Hc. inversion Hc. }
  destruct (raw_promise_witness tid imem fuel tsb mem ev Hc)
    as [proms [ppst [Hin [[ending Hr]|[err Hr]]]]].
  - destruct fuel as [|fuel].
    { apply rtt_zero_proms in Hr. subst proms. inversion Hin. }
    destruct (fixed_prefix_truncated tid imem mem count ts tsb Hsteps Hbound Hterm IIS.init)
      as [iis Htr].
    rewrite <- (rtt_iis_irrelevant tid imem fuel tsb mem iis IIS.init Hbound Hterm) in Hr.
    pose proof (out_of_fuel_certification_continue prom nondet term tid imem count (S fuel)
      (length mem) [] (PPState.Make ts mem IIS.init) [] (PPState.Make tsb mem iis)
      proms ppst ending Htr Hr) as Hcert.
    exact (collected_promise_in_raw_candidates prom nondet term tid imem (count + S fuel)
      ts mem ev proms ppst ending Hin Hcert).
  - destruct fuel as [|fuel]; [destruct (rtt_zero_errors _ _ _ _ _ _ Hr)|].
    destruct (fixed_prefix_truncated tid imem mem count ts tsb Hsteps Hbound Hterm IIS.init)
      as [iis Htr].
    rewrite <- (rtt_iis_irrelevant tid imem fuel tsb mem iis IIS.init Hbound Hterm) in Hr.
    pose proof (rtt_error_continue tid imem count (S fuel) (length mem) []
      (PPState.Make ts mem IIS.init) [] (PPState.Make tsb mem iis) proms ppst err Htr Hr)
      as Herr.
    unfold CPState.enumerate_results. cbn [CPState.promises].
    apply elem_of_remove_dups, list_elem_of_In, List.in_concat.
    exists proms. split; [|apply list_elem_of_In; exact Hin].
    apply list_elem_of_In, elem_of_app. right.
    apply list_elem_of_fmap. exists (proms, ppst). split; [reflexivity|].
    apply list_elem_of_fmap. exists ((proms, ppst), err). split; [reflexivity|exact Herr].
Qed.

(** * Unreduced promise traces

    [RawTrace s evs s'] promises [evs] (newest first) from [s] by unreduced
    promise steps. *)
Inductive RawTrace (s : state) : list Ev.t → state → Prop :=
| RawTrace_nil : RawTrace s [] s
| RawTrace_cons evs mid s' ev : RawTrace s evs mid → RawStep ev mid s' → RawTrace s (ev :: evs) s'.

Lemma raw_trace_events s evs s' : RawTrace s evs s' →
  PState.initmem s' = PState.initmem s ∧ PState.events s' = (evs ++ PState.events s)%list.
Proof.
  intro H. induction H as [|evs mid s' ev _ [Hi He] Hstep]; [auto|].
  destruct (rawstep_memory ev mid s' Hstep) as [Hi' He']. split; [congruence|].
  rewrite He', He. reflexivity.
Qed.

Lemma raw_trace_ok s evs s' : VMViews.state_ok s → RawTrace s evs s' → VMViews.state_ok s'.
Proof.
  intros Hok H. induction H as [|evs mid s' ev _ IH Hstep]; [exact Hok|].
  eapply rawstep_ok; [exact IH|exact Hstep].
Qed.

Lemma sorted_tail e (l : list Ev.t) : VMSwap.sorted (e :: l) → VMSwap.sorted l.
Proof. intros Hs l1 l2 e1 e2 ->. apply (Hs (e :: l1) l2 e1 e2). reflexivity. Qed.

(** A raw trace with a sorted final history is a promise-first trace. *)
Lemma raw_trace_sorted s evs s' : RawTrace s evs s' →
  VMSwap.sorted (evs ++ PState.events s)%list → rtc PromStep s s'.
Proof.
  intro H. induction H as [|evs mid s' ev Htail IH Hstep]; intro Hs; [apply rtc_refl|].
  cbn [app] in Hs. eapply rtc_r; [apply IH, (sorted_tail ev), Hs|].
  eapply rawstep_prom; [exact Hstep|]. intros last rest Hmid.
  destruct (raw_trace_events s evs mid Htail) as [_ He].
  apply (Hs [] rest last ev). cbn [app]. rewrite <- He, Hmid. reflexivity.
Qed.

(** The final architectural result of a terminated state that passes the
    final validation. *)
Definition FinalResult (final : state) (fs : archState n) : Prop :=
  ∃ pt : CPState.terminated prom term final,
    Exec.elem_of_results (final, ()) (CPState.validate_final_state prom final final) ∧
    projT1 (CPState.to_final_archState (CPState.make_final prom term final pt)) = fs.

Lemma final_result_sim final final' fs :
  st_sim final final' → VMViews.state_ok final → FinalResult final fs → FinalResult final' fs.
Proof.
  intros Hsim Hok [pt [Hvalid <-]].
  assert (pt' : CPState.terminated prom term final').
  { pose proof (terminated_sim bbm term final final' Hsim) as Ht.
    pose proof pt as pt0. unfold CPState.terminated, PState.terminated in Ht, pt0 |- *.
    rewrite <- Ht. exact pt0. }
  exists pt'. split.
  - destruct (validate_final_state_inv bbm final final final Hvalid) as [_ [Hpn Herrs]].
    apply validate_final_state_intro.
    + rewrite <- (nopromises_sim bbm final final' Hsim). exact Hpn.
    + apply (proj1 (state_check_valid_end_sim bbm final final' Hsim Hok)). exact Herrs.
  - cbn. symmetry. apply (to_archState_sim bbm), Hsim.
Qed.
End Traces.

(** * The commutation obligation of the promise reduction

    The promise-first runner rejects a candidate that is [Ev.out_of_order]
    after the newest event ([filter_commuting_promises]). This is sound when
    an adjacent out-of-order pair of an unreduced promise trace from the
    initial state can be exchanged: the exchanged trace is again an unreduced
    trace, and every continuation of the original trace to a validated final
    state has a counterpart after the exchanged trace with the same
    architectural result and history length. VMSwap characterizes the pairs:
    two TLBIs with a smaller recipient last and disjoint affected threads. *)
Definition VMTLBISwapReplay (bbm nondet : bool) {n : nat} (term : terminationCondition n)
    (initMs : archState n) (code : code_region) : Prop :=
  ∀ init l1 l2 e1 e2 b final fs,
    VMSailNoSelfModifying bbm nondet term initMs code →
    PState.from_archState (VMPromising bbm) initMs = Ok init →
    RawTrace bbm nondet term init (l1 ++ e2 :: e1 :: l2)%list b →
    Ev.out_of_order e1 e2 = true →
    rtc (Mixed bbm nondet term) b final → FinalResult bbm term final fs →
    ∃ b' final', RawTrace bbm nondet term init (l1 ++ e1 :: e2 :: l2)%list b' ∧
      rtc (Mixed bbm nondet term) b' final' ∧ FinalResult bbm term final' fs ∧
      length (PState.events final') = length (PState.events final).

(** ** A forward simulation sufficient for the commutation obligation

    [VMTLBISwapSimulation] splits [VMTLBISwapReplay] into local statements
    about one relation [R] between the states after the original and the
    exchanged pair: the two unreduced promise steps can be exchanged up to
    [R], [R] is a forward simulation for unreduced promise steps of the same
    event and for interleaved steps, it keeps the history length, and it
    keeps the validated architectural result. *)
Section SwapSimulation.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation Mixed := (Mixed bbm nondet term).
Local Notation RawStep := (RawStep bbm nondet term).
Local Notation RawTrace := (RawTrace bbm nondet term).
Local Notation FinalResult := (FinalResult bbm term).

Definition VMTLBISwapSimulation : Prop :=
  ∃ R : state → state → Prop,
    (∀ init evs s a b e1 e2,
      VMSailNoSelfModifying bbm nondet term initMs code →
      PState.from_archState prom initMs = Ok init →
      RawTrace init evs s → RawStep e1 s a → RawStep e2 a b →
      Ev.out_of_order e1 e2 = true →
      ∃ a' b', RawStep e2 s a' ∧ RawStep e1 a' b' ∧ R b b') ∧
    (∀ x x' ev y, R x x' → RawStep ev x y → ∃ y', RawStep ev x' y' ∧ R y y') ∧
    (∀ x x' y, R x x' → Mixed x y → ∃ y', Mixed x' y' ∧ R y y') ∧
    (∀ x x', R x x' → length (PState.events x') = length (PState.events x)) ∧
    (∀ x x' fs, R x x' → FinalResult x fs → FinalResult x' fs).

Lemma raw_trace_app s evs1 m evs2 s' :
  RawTrace s evs1 m → RawTrace m evs2 s' → RawTrace s (evs2 ++ evs1)%list s'.
Proof.
  intros H1 H2. induction H2 as [|evs mid s' ev _ IH Hstep]; [exact H1|].
  cbn [app]. econstructor; [exact IH|exact Hstep].
Qed.

Lemma raw_trace_cons_inv s ev evs s' : RawTrace s (ev :: evs) s' →
  ∃ mid, RawTrace s evs mid ∧ RawStep ev mid s'.
Proof. intro H. inversion H; subst. eexists; split; eassumption. Qed.

Lemma raw_trace_split s l1 l2 s' : RawTrace s (l1 ++ l2)%list s' →
  ∃ m, RawTrace s l2 m ∧ RawTrace m l1 s'.
Proof.
  revert s'. induction l1 as [|ev l1 IH]; intros s' H.
  - exists s'. split; [exact H|constructor].
  - cbn [app] in H. apply raw_trace_cons_inv in H as [mid [Htail Hstep]].
    destruct (IH mid Htail) as [m [H1 H2]]. exists m. split; [exact H1|].
    econstructor; eassumption.
Qed.

Theorem swap_simulation_replay :
  VMTLBISwapSimulation → VMTLBISwapReplay bbm nondet term initMs code.
Proof.
  intros (R & Hstart & Hraw & Hmixed & Hlen & Hres)
    init l1 l2 e1 e2 b final fs Hsafe Hinit Htr Hord Hrest Hfin.
  destruct (raw_trace_split _ l1 _ _ Htr) as [c [Hc Hl1]].
  apply raw_trace_cons_inv in Hc as [a [Ha Hac]].
  apply raw_trace_cons_inv in Ha as [s [Hs Hsa]].
  destruct (Hstart init l2 s a c e1 e2 Hsafe Hinit Hs Hsa Hac Hord)
    as [a' [c' [Hsa' [Hac' HR]]]].
  assert (Hl1' : ∃ b', RawTrace c' l1 b' ∧ R b b').
  { clear -Hraw Hl1 HR. induction Hl1 as [|evs mid y ev _ [m' [Hm' HRm]] Hstep].
    - exists c'. split; [constructor|exact HR].
    - destruct (Hraw mid m' ev y HRm Hstep) as [y' [Hy' HRy]].
      exists y'. split; [econstructor; eassumption|exact HRy]. }
  destruct Hl1' as [b' [Hb' HRb]].
  assert (Hcont : ∃ final', rtc Mixed b' final' ∧ R final final').
  { clear -Hmixed Hrest HRb. revert b' HRb.
    induction Hrest as [x|x y z Hxy _ IH]; intros x' HR.
    - exists x'. split; [apply rtc_refl|exact HR].
    - destruct (Hmixed x x' y HR Hxy) as [y' [Hy' HRy]].
      destruct (IH y' HRy) as [z' [Hz' HRz]].
      exists z'. split; [eapply rtc_l; eassumption|exact HRz]. }
  destruct Hcont as [final' [Hfinal' HRf]].
  exists b', final'. split.
  - eapply raw_trace_app; [|exact Hb'].
    econstructor; [econstructor; eassumption|exact Hac'].
  - split; [exact Hfinal'|]. split; [eapply Hres; eassumption|]. apply Hlen, HRf.
Qed.
End SwapSimulation.

(** * Moving the first new event of a trace into a promise *)

Section Replay.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).
Hypothesis Hreplay : VMInstructionPromiseReplay bbm nondet term initMs code.
Local Notation prom := (VMPromising bbm).
Local Notation isem := (sail_tiny_arm_sem nondet).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation Inst := (InstructionTransition prom nondet term).
Local Notation Fixed := (Fixed bbm nondet term).
Local Notation Mixed := (Mixed bbm nondet term).
Local Notation FMixed := (FMixed bbm nondet term).
Local Notation PromStep := (PromStep bbm nondet term).
Local Notation RawStep := (RawStep bbm nondet term).
Local Notation RawTrace := (RawTrace bbm nondet term).
Local Notation FinalResult := (FinalResult bbm term).

(** Every running thread is at an actual Sail instruction boundary. *)
Definition Prefixes (s : state) : Prop :=
  ∀ t, CPState.terminated_tid prom term s t = false →
    SailThreadPrefix prom nondet term initMs t (PState.initmem s)
      (PPState.Make (PState.tstate t s) (PState.events s) IIS.init) isem.

Lemma reachable_prefixes use_pf s :
  PromiseFirstReachable prom isem term initMs use_pf s → Prefixes s.
Proof. intros Hreach t Ht. eapply SailThreadPrefix_start; [exact Hreach|exact Ht]. Qed.

Lemma fixed_prefixes s s' : Prefixes s → Fixed s s' → Prefixes s'.
Proof.
  intros Hpre [[t [Hterm Hrun]] Hsame] u Hu.
  destruct (run_tid_decompose_fixed prom isem t s s' Hrun Hsame)
    as [ts' [mem [iis [Hinst ->]]]].
  cbn [PState.events] in Hsame. subst mem. cbn [PState.initmem PState.events].
  unfold CPState.terminated_tid in Hu. cbn in Hu. rewrite tstate_make in Hu |- *.
  destruct (decide (t = u)) as [<-|Hne].
  - rewrite vlookup_insert in Hu |- *.
    pose proof (sail_instruction_result_prefix prom nondet term initMs t (PState.initmem s)
      isem _ _ (Hpre t Hterm) Hinst) as Hret.
    exact (SailThreadPrefix_next prom nondet term initMs t _ _ Hret Hu).
  - rewrite vlookup_insert_ne in Hu |- * by exact Hne. apply Hpre, Hu.
Qed.

Lemma fixed_rtc_prefixes s s' : Prefixes s → rtc Fixed s s' → Prefixes s'.
Proof. intros Hpre H. induction H; [exact Hpre|]. apply IHrtc. eapply fixed_prefixes; eassumption. Qed.

(** A fixed-history instruction step after a promise. *)
Lemma fixed_step_replay s s1 ev s1e :
  VMSailNoSelfModifying bbm nondet term initMs code → Prefixes s → VMViews.state_ok s →
  event_misses_code VMPromisingReadByte code ev →
  VMEventValidity.event_positive ev →
  Fixed s s1 → PState.promise prom ev s1 = Ok s1e →
  ∃ se y, PState.promise prom ev s = Ok se ∧ Inst se y ∧ st_sim s1e y.
Proof using Hreplay.
  intros Hsafe Hpre Hok Hmiss Hpositive [[t [Hterm Hrun]] Hsame] Hp1.
  pose proof (VMViews.promise_ok bbm ev s1 s1e (VMViews.run_tid_ok bbm isem t s s1 Hok Hrun) Hp1)
    as Hok1e.
  destruct (run_tid_decompose_fixed prom isem t s s1 Hrun Hsame)
    as [ts' [mem [iis' [Hinst ->]]]].
  cbn [PState.events] in Hsame. subst mem.
  destruct (promise_inv bbm ev _ _ Hp1) as [Hi1 [He1 Hts1]].
  cbn [PState.initmem PState.events] in Hi1, He1, Hts1.
  pose proof (Hts1 t) as Ht1. rewrite tstate_make, vlookup_insert in Ht1.
  destruct (Hreplay t (PState.initmem s) (PState.tstate t s) (PState.events s) ts'
    (PState.events s) iis' ev Hsafe (Hpre t Hterm) (Hok t) Hmiss Hinst) as [_ Hb].
  destruct (Hb eq_refl Hpositive _ Ht1) as [ts_e [[ts'' mem'' iis''] [He [Hrun' [Hm Hsim]]]]].
  cbn in Hm, Hsim. subst mem''.
  set (tss := vinsert t ts_e (PState.tstates s1e)).
  assert (Hp : PState.promise prom ev s =
    Ok (PState.Make tss (PState.initmem s) (ev :: PState.events s))).
  { apply promise_intro. intro i. unfold tss. destruct (decide (t = i)) as [<-|Hne].
    - rewrite vlookup_insert. exact He.
    - rewrite vlookup_insert_ne by exact Hne. specialize (Hts1 i).
      rewrite tstate_make, vlookup_insert_ne in Hts1 by exact Hne. exact Hts1. }
  set (se := PState.Make tss (PState.initmem s) (ev :: PState.events s)) in *.
  exists se, (replace_thread prom se t ts''). split; [exact Hp|]. split.
  - exists t. split.
    + rewrite (promise_terminated_tid bbm term ev s se t Hp). exact Hterm.
    + eapply (run_tid_fixed_history prom nondet). unfold se, tss.
      rewrite tstate_make, vlookup_insert. cbn [PState.events PState.initmem]. exact Hrun'.
  - split; [cbn; exact Hi1|]. split; [cbn; exact He1|].
    intro i. unfold replace_thread. rewrite tstate_make.
    destruct (decide (t = i)) as [<-|Hne].
    + rewrite vlookup_insert. exact Hsim.
    + rewrite vlookup_insert_ne by exact Hne. unfold se, tss. cbn [PState.tstates].
      rewrite vlookup_insert_ne by exact Hne. exact (ts_ok_sim_refl _ _ (Hok1e i)).
Qed.

Lemma take_app_full {A} (l r : list A) : take (length (l ++ r)%list - length r) (l ++ r)%list = l.
Proof. rewrite length_app, Nat.add_sub, take_app_length. reflexivity. Qed.

(** The instruction creating the event, after its oldest event was promised. *)
Lemma creating_step_replay s a ev t evs :
  VMSailNoSelfModifying bbm nondet term initMs code → Prefixes s → VMViews.state_ok s →
  event_misses_code VMPromisingReadByte code ev →
  CPState.terminated_tid prom term s t = false →
  Exec.elem_of_results (a, ()) (PState.run_tid isem prom t s) →
  PState.events a = (evs ++ ev :: PState.events s)%list →
  ∃ se a', PState.promise prom ev s = Ok se ∧ Inst se a' ∧ st_sim a a'.
Proof using Hreplay.
  intros Hsafe Hpre Hok Hmiss Hterm Hrun Hmem.
  destruct (run_tid_broadcast_decompose prom isem t s a Hrun)
    as [ts' [mem' [iis' [states [Hinst [Hbr ->]]]]]].
  cbn [PState.events] in Hmem. subst mem'.
  rewrite take_app_last in Hbr.
  destruct (broadcast_fresh_app_last bbm t (PState.initmem s) (PState.events s) evs ev _ _ Hbr)
    as [mid [Hmid Hrest]].
  pose proof (PromiseFirstCurrent.vimapM_result_lookup _ _ _ Hmid) as Hmidl.
  destruct (Hreplay t (PState.initmem s) (PState.tstate t s) (PState.events s) ts'
    (evs ++ ev :: PState.events s)%list iis' ev Hsafe (Hpre t Hterm) (Hok t) Hmiss Hinst)
    as [Ha _].
  destruct (Ha evs eq_refl) as [ts_e [[ts'' mem'' iis''] [He [Hrun' [Hm Hsim]]]]].
  cbn in Hm, Hsim. subst mem''.
  assert (Hmid_t : mid !!! t = ts').
  { specialize (Hmidl t). cbn in Hmidl. rewrite decide_True in Hmidl by reflexivity.
    rewrite vlookup_insert in Hmidl. injection Hmidl as <-. reflexivity. }
  assert (Hmid_o : ∀ i, i ≠ t → TState.emit_promise i (PState.initmem s)
    (ev :: PState.events s) ev (PState.tstate i s) = Ok (mid !!! i)).
  { intros i Hne. specialize (Hmidl i). cbn in Hmidl. rewrite decide_False in Hmidl by exact Hne.
    rewrite vlookup_insert_ne in Hmidl by congruence. exact Hmidl. }
  set (tss := vinsert t ts_e mid).
  assert (Hp : PState.promise prom ev s =
    Ok (PState.Make tss (PState.initmem s) (ev :: PState.events s))).
  { apply promise_intro. intro i. unfold tss. destruct (decide (t = i)) as [<-|Hne].
    - rewrite vlookup_insert. exact He.
    - rewrite vlookup_insert_ne by exact Hne. apply Hmid_o. congruence. }
  set (se := PState.Make tss (PState.initmem s) (ev :: PState.events s)) in *.
  assert (Hstates : ∀ i, ts_sim (mid !!! i) (vinsert t ts'' (PState.tstates se) !!! i)).
  { intro i. destruct (decide (t = i)) as [<-|Hne].
    - rewrite vlookup_insert, Hmid_t. exact Hsim.
    - rewrite vlookup_insert_ne by exact Hne. unfold se, tss. cbn [PState.tstates].
      rewrite vlookup_insert_ne by exact Hne.
      apply (ts_ok_sim_refl (length (ev :: PState.events s))).
      eapply (VMViews.emit_promise i (PState.initmem s) (ev :: PState.events s) ev
        (length (PState.events s))); [cbn; lia|apply Hok|]. apply Hmid_o. congruence. }
  destruct (broadcast_sim bbm t (PState.initmem s) (ev :: PState.events s) evs mid
    (vinsert t ts'' (PState.tstates se)) states Hstates Hrest) as [states2 [Hb2 Hs2]].
  exists se, (PState.Make states2 (PState.initmem se) (evs ++ ev :: PState.events s)%list).
  split; [exact Hp|]. split.
  - exists t. split.
    + rewrite (promise_terminated_tid bbm term ev s se t Hp). exact Hterm.
    + eapply (run_tid_broadcast_intro prom isem t se ts'' _ iis'').
      * unfold se, tss. rewrite tstate_make, vlookup_insert. cbn [PState.events PState.initmem].
        exact Hrun'.
      * unfold se at 2. cbn [PState.events].
        replace (evs ++ ev :: PState.events s)%list with (evs ++ (ev :: PState.events s))%list
          by reflexivity.
        rewrite take_app_full. exact Hb2.
  - split; [reflexivity|]. split; [reflexivity|]. intro i. rewrite !tstate_make. apply Hs2.
Qed.

(** A promise of the event created at the end of a fixed-history prefix can
    be issued before the prefix. *)
Lemma prefix_replay ev s b be :
  VMSailNoSelfModifying bbm nondet term initMs code →
  event_misses_code VMPromisingReadByte code ev →
  VMEventValidity.event_positive ev →
  rtc Fixed s b → Prefixes s → VMViews.state_ok s →
  PState.promise prom ev b = Ok be →
  ∃ se x, PState.promise prom ev s = Ok se ∧ rtc Inst se x ∧ st_sim be x.
Proof using Hreplay.
  intros Hsafe Hmiss Hpositive H. induction H as [s|s s1 b Hstep Htail IH]; intros Hpre Hok Hp.
  - exists be, be. split; [exact Hp|]. split; [apply rtc_refl|].
    apply st_sim_refl. eapply VMViews.promise_ok; eassumption.
  - destruct (IH (fixed_prefixes s s1 Hpre Hstep) (inst_ok bbm nondet term s s1 Hok (proj1 Hstep)) Hp)
      as [s1e [x1 [Hp1 [Hx1 Hsim1]]]].
    destruct (fixed_step_replay s s1 ev s1e Hsafe Hpre Hok Hmiss Hpositive Hstep Hp1)
      as [se [y [Hpe [Hy Hsimy]]]].
    destruct (inst_rtc_sim bbm nondet term s1e y x1 Hsimy Hx1) as [x [Hx Hsimx]].
    exists se, x. split; [exact Hpe|]. split; [eapply rtc_l; eassumption|].
    eapply st_sim_trans; eassumption.
Qed.

(** The first step that adds an event, after a fixed-history prefix from a
    reachable promise-first state, is replaced by an unreduced promise step
    of its oldest event, followed by a replay reaching a simulated state. *)
Lemma first_event_replay s b a :
  VMSailNoSelfModifying bbm nondet term initMs code →
  PromiseFirstReachable prom isem term initMs true s →
  rtc Fixed s b → Mixed b a → PState.events a ≠ PState.events b →
  ∃ ev se x, RawStep ev s se ∧ rtc Inst se x ∧ st_sim a x.
Proof using Hreplay.
  intros Hsafe Hreach Hfix Hstep Hnew.
  pose proof (VMViews.reachable_ok bbm isem term initMs true s Hreach) as Hok.
  pose proof (reachable_prefixes true s Hreach) as Hpre.
  destruct (fixed_projection bbm nondet term s b Hok Hfix) as [Hib [Heb Hthreads]].
  pose proof (fixed_rtc_ok bbm nondet term s b Hok Hfix) as Hokb.
  pose proof (fixed_rtc_prefixes s b Hpre Hfix) as Hpreb.
  pose proof (sail_observed_code_immutable _ _ _ _ _ _ Hsafe) as Hsafe_obs.
  destruct Hstep as [[t [Hterm Hrun]]|[ev [[tid [fuel Hcandb]] Hpb]]].
  - pose proof Hrun as Hrun0.
    destruct (run_tid_broadcast_decompose prom isem t b a Hrun)
      as [ts' [mem' [iis' [states [Hinst [_ Ha]]]]]].
    destruct (VMFinalCertification.instruction_memory_suffix t (PState.initmem b) isem _ _ ()
      Hinst) as [extra Hextra].
    cbn [PPState.mem] in Hextra.
    assert (Hmema : PState.events a = mem') by (rewrite Ha; reflexivity).
    assert (Hne : extra ≠ []).
    { intros ->. apply Hnew. rewrite Hmema, Hextra. reflexivity. }
    destruct (exists_last Hne) as [evs [ev ->]].
    assert (Hmem : PState.events a = (evs ++ ev :: PState.events b)%list).
    { rewrite Hmema, Hextra, <- app_assoc. reflexivity. }
    destruct (Hthreads t) as [count Hsteps].
    rewrite Hextra, <- app_assoc in Hinst. cbn [app] in Hinst.
    rewrite Hib, Heb in Hinst.
    assert (Hcand : RawCandidate bbm nondet term s t (count + 1) ev).
    { eapply (candidate_first_new bbm nondet term t (PState.initmem s) (PState.events s) count
        _ (PState.tstate t b) ts' evs ev iis' Hsteps); [| |exact Hinst].
      - rewrite <- Heb. apply ts_ok_min_view, Hokb.
      - exact Hterm. }
    pose proof (raw_candidate_misses_code bbm nondet term initMs code s t (count + 1) ev
      Hsafe_obs Hreach Hcand) as Hmiss.
    pose proof (VMEventCertification.raw_promise_positive bbm t (PState.initmem s) nondet term
      (count + 1) (PState.tstate t s) (PState.events s) ev Hcand) as Hpositive.
    destruct (creating_step_replay b a ev t evs Hsafe Hpreb Hokb Hmiss Hterm Hrun0 Hmem)
      as [be [a' [Hpb [Hinst' Hsima]]]].
    destruct (prefix_replay ev s b be Hsafe Hmiss Hpositive Hfix Hpre Hok Hpb)
      as [se [x1 [Hps [Hx1 Hsim1]]]].
    destruct (instruction_transition_sim bbm nondet term be x1 a' Hsim1 Hinst')
      as [x [Hx Hsimx]].
    exists ev, se, x. split; [split; [exists t, (count + 1); exact Hcand|exact Hps]|].
    split; [eapply rtc_r; eassumption|]. eapply st_sim_trans; eassumption.
  - unfold RawCandidate in Hcandb. rewrite Hib, Heb in Hcandb.
    destruct (Hthreads tid) as [count Hsteps].
    assert (Hbound : TState.min_new_prom_view (PState.tstate tid b) ≤ length (PState.events s)).
    { rewrite <- Heb. apply ts_ok_min_view, Hokb. }
    pose proof (candidate_before_prefix bbm nondet term tid (PState.initmem s) (PState.events s)
      count (PState.tstate tid s) (PState.tstate tid b) fuel ev Hsteps Hbound Hcandb) as Hcand.
    pose proof (raw_candidate_misses_code bbm nondet term initMs code s tid (count + fuel) ev
      Hsafe_obs Hreach Hcand) as Hmiss.
    pose proof (VMEventCertification.raw_promise_positive bbm tid (PState.initmem s) nondet term
      (count + fuel) (PState.tstate tid s) (PState.events s) ev Hcand) as Hpositive.
    destruct (prefix_replay ev s b a Hsafe Hmiss Hpositive Hfix Hpre Hok Hpb)
      as [se [x [Hps [Hx Hsim]]]].
    exists ev, se, x. split; [split; [exists tid, (count + fuel); exact Hcand|exact Hps]|].
    split; assumption.
Qed.

(** * Sorting unreduced promise traces *)

Lemma from_archState_events (init : state) :
  PState.from_archState prom initMs = Ok init → PState.events init = [].
Proof.
  unfold PState.from_archState. destruct (vimapM _ _) as [nts|err]; cbn; [|discriminate].
  intros [= <-]. reflexivity.
Qed.

Lemma reachable_prom_trace s : PromiseFirstReachable prom isem term initMs true s →
  ∃ init, PState.from_archState prom initMs = Ok init ∧ rtc PromStep init s.
Proof.
  intro H. induction H as [st Hinit|fuel st st' _ [init [Hinit Htr]] Hstep].
  - exists st. split; [exact Hinit|apply rtc_refl].
  - exists init. split; [exact Hinit|]. eapply rtc_r; [exact Htr|]. exists fuel. exact Hstep.
Qed.

Lemma prom_rtc_reachable s s' : PromiseFirstReachable prom isem term initMs true s →
  rtc PromStep s s' → PromiseFirstReachable prom isem term initMs true s'.
Proof.
  intros Hr H. induction H as [s|s mid s' [fuel Hstep] _ IH]; [exact Hr|].
  apply IH. eapply PromiseFirstReachable_step; [exact Hr|exact Hstep].
Qed.

Lemma prom_rtc_raw_trace s s' : rtc PromStep s s' → ∃ evs, RawTrace s evs s'.
Proof.
  intro H. cut (∀ evs0, RawTrace s evs0 s → ∃ evs, RawTrace s evs s').
  { intro Hc. apply (Hc []). constructor. }
  generalize s at 1 3 as s0.
  induction H as [s|s mid s' Hstep _ IH]; intros s0 evs0 Htr; [exists evs0; exact Htr|].
  destruct (promstep_raw bbm nondet term s mid Hstep) as [ev Hraw].
  apply (IH s0 (ev :: evs0)). econstructor; eassumption.
Qed.

(** Iterating [VMTLBISwapReplay] along [VMSwap.bubble_sort] turns an
    unreduced trace from the initial state into a promise-first trace with
    the same continuation results. *)
Lemma raw_trace_sort init :
  VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  PState.from_archState prom initMs = Ok init →
  ∀ L b final fs, RawTrace init L b → rtc Mixed b final → FinalResult final fs →
  ∃ b' final', rtc PromStep init b' ∧ length (PState.events b') = length L ∧
    rtc Mixed b' final' ∧ FinalResult final' fs ∧
    length (PState.events final') = length (PState.events final).
Proof.
  intros Hswap Hsafe Hinit L.
  pose proof (from_archState_events init Hinit) as Hinit_ev.
  induction L as [L IH] using (induction_ltof1 _ VMSwap.inversions). unfold ltof in IH.
  intros b final fs Htr Hrest Hfin.
  destruct (VMSwap.sortedb L) eqn:Hs.
  - exists b, final. split.
    + eapply raw_trace_sorted; [exact Htr|].
      rewrite Hinit_ev, app_nil_r. apply VMSwap.sortedb_sorted, Hs.
    + split; [|auto].
      destruct (raw_trace_events bbm nondet term _ _ _ Htr) as [_ ->].
      rewrite Hinit_ev, app_nil_r. reflexivity.
  - destruct (VMSwap.not_sortedb L Hs) as (l1 & l2 & e1 & e2 & -> & Hord).
    destruct (Hswap init l1 l2 e1 e2 b final fs Hsafe Hinit Htr Hord Hrest Hfin)
      as [b' [final' [Htr' [Hrest' [Hfin' Hlen']]]]].
    destruct (IH _ (VMSwap.swap_step_inversions _ _ (VMSwap.swap_step_intro l1 l2 e1 e2 Hord))
      b' final' fs Htr' Hrest' Hfin') as [b'' [final'' (Hp & Hlb & Hr & Hf & Hl)]].
    exists b'', final''. split; [exact Hp|]. split.
    + rewrite Hlb, !length_app. reflexivity.
    + split; [exact Hr|]. split; [exact Hf|]. rewrite Hl, Hlen'. reflexivity.
Qed.

Local Lemma normalize_bounded budget : ∀ s final fs,
  VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  PromiseFirstReachable prom isem term initMs true s →
  rtc Mixed s final → FinalResult final fs →
  length (PState.events final) ≤ budget + length (PState.events s) →
  ∃ before final', PromiseFirstReachable prom isem term initMs true before ∧
    rtc Fixed before final' ∧ FinalResult final' fs.
Proof using Hreplay.
  induction budget as [|budget IH]; intros s final fs Hswap Hsafe Hreach Htrace Hfin Hbound.
  all: pose proof (VMViews.reachable_ok bbm isem term initMs true s Hreach) as Hok.
  all: destruct (decide (PState.events final = PState.events s)) as [Hsame|Hnew].
  1, 3: exists s, final; split; [exact Hreach|];
    split; [apply (mixed_rtc_fixed bbm nondet term); assumption|exact Hfin].
  - exfalso. destruct (mixed_rtc_memory bbm nondet term s final Htrace) as [_ [extra He]].
    apply Hnew. rewrite He in Hbound |- *. rewrite length_app in Hbound.
    destruct extra; [reflexivity|cbn in Hbound; lia].
  - destruct (first_mixed_event bbm nondet term s final Htrace Hnew)
      as [b [a [Hfix [Hmix [Hchanged Hrest]]]]].
    destruct (first_event_replay s b a Hsafe Hreach Hfix Hmix Hchanged)
      as [ev [se [x [Hstep [Hx Hsim]]]]].
    assert (Hoka : VMViews.state_ok a).
    { eapply (mixed_ok bbm nondet term b); [|exact Hmix].
      eapply (fixed_rtc_ok bbm nondet term s); eassumption. }
    destruct (mixed_rtc_sim bbm nondet term a x final Hsim Hoka Hrest)
      as [final2 [Htrace2 Hsim2]].
    pose proof Hsim2 as (_ & Hevents & _).
    assert (Hfin2 : FinalResult final2 fs).
    { eapply final_result_sim; [exact Hsim2| |exact Hfin].
      eapply (mixed_rtc_ok bbm nondet term); [exact Hoka|exact Hrest]. }
    destruct (reachable_prom_trace s Hreach) as [init [Hinit Hpre]].
    destruct (prom_rtc_raw_trace init s Hpre) as [evs Htr].
    destruct (raw_trace_events bbm nondet term _ _ _ Htr) as [_ Hevs].
    rewrite (from_archState_events init Hinit), app_nil_r in Hevs.
    assert (Htr' : RawTrace init (ev :: evs) se) by (econstructor; eassumption).
    assert (Hcont : rtc Mixed se final2).
    { eapply rtc_trans; [apply (inst_rtc_mixed bbm nondet term); exact Hx|exact Htrace2]. }
    destruct (raw_trace_sort init Hswap Hsafe Hinit (ev :: evs) se final2 fs Htr' Hcont Hfin2)
      as [b' [final3 (Hpb & Hlb & Htr3 & Hfin3 & Hl3)]].
    assert (Hreach_b : PromiseFirstReachable prom isem term initMs true b').
    { eapply prom_rtc_reachable; [apply PromiseFirstReachable_init; exact Hinit|exact Hpb]. }
    apply (IH b' final3 fs Hswap Hsafe Hreach_b Htr3 Hfin3).
    rewrite Hl3, <- Hevents, Hlb. cbn [length]. rewrite <- Hevs, <- plus_n_Sm. exact Hbound.
Qed.

(** Fresh instruction events and unreduced promises of an interleaved VM
    trace from a reachable promise-first state are moved into promise-first
    promise steps from the initial state. The rest is a fixed-history
    instruction suffix reaching the same validated architectural result. *)
Theorem VMSail_full_mixed_normalization s final fs :
  VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  PromiseFirstReachable prom isem term initMs true s →
  rtc Mixed s final → FinalResult final fs →
  ∃ before final', PromiseFirstReachable prom isem term initMs true before ∧
    rtc Fixed before final' ∧ FinalResult final' fs.
Proof using Hreplay.
  intros Hswap Hsafe Hreach Htrace Hfin.
  eapply (normalize_bounded (length (PState.events final))); try eassumption. lia.
Qed.

Lemma direct_run_mixed_trace fuel st returned fsig :
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem prom n) fuel term initMs st) →
  ∃ final (pt : CPState.terminated prom term final),
    rtc Mixed st final ∧
    Exec.elem_of_results (returned, ()) (CPState.validate_final_state prom final final) ∧
    fsig = CPState.to_final_archState (CPState.make_final prom term final pt).
Proof.
  revert st. induction fuel as [|fuel IH]; intros st Hrun.
  - cbn [opModel.run] in Hrun. change ((returned, fsig) ∈ []) in Hrun. inversion Hrun.
  - cbn [opModel.run] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [next [res [Hstep Htail]]].
    destruct res as [result|].
    + apply Exec.elem_of_mret_inv in Htail as [Hreturned Hsig]. subst next result.
      destruct (run_transition_some_inv (prom := prom) isem term (S fuel)
        st returned fsig Hstep) as [pt [Hvalid Hsig]].
      exists st, pt. split; [apply rtc_refl|auto].
    + destruct (IH next Htail) as [final [pt [Htrace Hrest]]].
      exists final, pt. split; [|exact Hrest]. eapply rtc_l; [|exact Htrace].
      destruct (direct_none_to_promise_first_none_or_run_tid (prom := prom)
        isem term (S fuel) st next Hstep) as [Hpromise|Hinst];
        [right; apply (promstep_raw bbm nondet term); exists (S fuel); exact Hpromise
        |left; exact Hinst].
Qed.

(** A certificate exposed by normalization that does not persist at larger
    fuel: its enumeration reports OutOfFuel, and emitting the candidate leaves
    a promise-first continuation to a validated final state with the
    architectural result [fs]. *)
Definition VMTruncatedNormalizationCandidate (fs : archState n) : Prop :=
  ∃ before next fuel tid ev,
    PromiseFirstReachable prom isem term initMs true before ∧
    ev ∈ (CPState.enumerate_results_filtered isem prom term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.promises prom) ∧
    PState.promise prom ev before = Ok next ∧
    (∃ final', rtc FMixed next final' ∧ FinalResult final' fs) ∧
    ¬ StablePromiseCandidate prom nondet term tid (PState.initmem before)
      (PState.tstate tid before) (PState.events before) ev ∧
    (CPState.enumerate_results_filtered isem prom term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.out_of_fuel prom) = true.

(** Completeness of the candidate-bearing searches admitting a promise-first
    continuation to a validated final state with the architectural result
    [fs]. Normalization constructs these searches; they need not be searches
    of the original direct run. *)
Definition VMNormalizationSearchesComplete (fs : archState n) : Prop :=
  ∀ before next fuel tid ev,
    PromiseFirstReachable prom isem term initMs true before →
    ev ∈ (CPState.enumerate_results_filtered isem prom term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.promises prom) →
    PState.promise prom ev before = Ok next →
    (∃ final', rtc FMixed next final' ∧ FinalResult final' fs) →
    (CPState.enumerate_results_filtered isem prom term tid (PState.initmem before)
      fuel (PState.tstate tid before) (PState.events before)).(CPState.out_of_fuel prom) = false.

Lemma normalized_prefix_stable_or_truncated fs s before final' :
  rtc PromStep s before →
  PromiseFirstReachable prom isem term initMs true s →
  rtc Fixed before final' → FinalResult final' fs →
  rtc (StableCertifiedPromiseStep prom nondet term) s before ∨
  VMTruncatedNormalizationCandidate fs.
Proof.
  intro Hprefix. induction Hprefix as [s|s next before [fuel Hstep] Htail IH];
    intros Hreach Hsuffix Hfin.
  - left. apply rtc_refl.
  - destruct (run_transition_promise_first_none_inv (prom := prom) isem term
      fuel s next Hstep) as [tid [ev [nst [Hcandidate [Hpromise Hnext]]]]].
    subst nst. rewrite promise_first_execution_results_lookup in Hcandidate.
    destruct (classic (StablePromiseCandidate prom nondet term tid
      (PState.initmem s) (PState.tstate tid s) (PState.events s) ev))
      as [Hstable|Hunstable].
    + assert (Hreach_next : PromiseFirstReachable prom isem term initMs true next).
      { eapply PromiseFirstReachable_step; eassumption. }
      destruct (IH Hreach_next Hsuffix Hfin) as [Hstable_tail|Hbad]; [left|right; exact Hbad].
      eapply rtc_l; [exists tid, ev; split; [exact Hstable|exact Hpromise]|exact Hstable_tail].
    + right. exists s, next, fuel, tid, ev.
      split; [exact Hreach|]. split; [exact Hcandidate|]. split; [exact Hpromise|]. split.
      * exists final'. split; [|exact Hfin].
        eapply rtc_trans with (y := before).
        -- clear -Htail. induction Htail; [apply rtc_refl|].
           eapply rtc_l; [right; exact H|exact IHHtail].
        -- clear -Hsuffix. induction Hsuffix; [apply rtc_refl|].
           eapply rtc_l; [left; apply H|exact IHHsuffix].
      * split; [exact Hunstable|].
        destruct (candidate_stable_or_out_of_fuel prom nondet term tid
          (PState.initmem s) fuel (PState.tstate tid s) (PState.events s) ev
          ltac:(intros; eapply VMPromising_filter_promises_subset; eassumption)
          (VM_filter_retains_membership bbm) Hcandidate)
          as [Hstable|[proms [ppst [_ Hout]]]]; [contradiction|].
        eapply out_of_fuel_certification_flag; exact Hout.
Qed.

Lemma fixed_rtc_bounded s s' : VMViews.state_ok s → rtc Fixed s s' →
  rtc (VMBoundedFixedHistoryStep bbm nondet term) s s'.
Proof.
  intros Hok H. induction H as [s|s mid s' Hstep Htail IH]; [apply rtc_refl|].
  eapply rtc_l; [|apply IH; eapply (inst_ok bbm nondet term); [exact Hok|apply Hstep]].
  split; [apply Hstep|]. split; [apply Hstep|]. intro tid. apply ts_ok_min_view, Hok.
Qed.

(** No completeness premise: an actual successful direct run of any finite
    number of Sail VM threads from the initial state, with fresh writes,
    TLBIs and explicit promises in any interleaving and in any TLBI order,
    either has a promise-first run with the same architectural final state at
    every sufficiently large fuel, or exposes a truncated normalization
    candidate. *)
Theorem VMSail_direct_to_promise_first_or_truncated fuel st returned fsig :
  VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  PState.from_archState prom initMs = Ok st →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem prom n) fuel term initMs st) →
  (∃ before cost (fsig' : {s & archState.is_terminated term s}),
    (∀ pf_fuel, cost < pf_fuel →
      Exec.elem_of_results (before, fsig')
        (opModel.run (@CPState.opmodel_pf_uncached isem prom n) pf_fuel term initMs st)) ∧
    projT1 fsig' = projT1 fsig) ∨
  VMTruncatedNormalizationCandidate (projT1 fsig).
Proof using Hreplay.
  intros Hswap Hsafe Hinit Hrun.
  pose proof (PromiseFirstReachable_init prom isem term initMs true st Hinit) as Hreach.
  destruct (direct_run_mixed_trace fuel st returned fsig Hrun)
    as [final [pt [Htrace [Hvalid Hsig]]]].
  pose proof (validate_final_preserves_state prom final final returned Hvalid) as Heq.
  subst returned.
  assert (Hfin : FinalResult final (projT1 fsig)).
  { exists pt. split; [exact Hvalid|]. subst fsig. reflexivity. }
  destruct (VMSail_full_mixed_normalization st final (projT1 fsig) Hswap Hsafe Hreach Htrace Hfin)
    as [before [final' [Hreach_b [Hsuffix Hfin']]]].
  destruct (reachable_prom_trace before Hreach_b) as [init [Hinit' Hprefix]].
  rewrite Hinit in Hinit'. injection Hinit' as <-.
  destruct (normalized_prefix_stable_or_truncated (projT1 fsig) st before final' Hprefix Hreach
    Hsuffix Hfin') as [Hstable|Hbad]; [left|right; exact Hbad].
  pose proof (VMViews.reachable_ok bbm isem term initMs true before Hreach_b) as Hok_b.
  pose proof (fixed_rtc_ok bbm nondet term before final' Hok_b Hsuffix) as Hok'.
  destruct Hfin' as [pt' [Hvalid' Hres]].
  destruct (VMSail_fixed_history_final_batch bbm nondet term before final' final' pt'
    (fixed_rtc_bounded before final' Hok_b Hsuffix)
    (λ tid, ts_ok_min_view _ _ (Hok' tid)) Hvalid') as [cert_fuel Hbatch].
  destruct (stable_prefix_promise_first_run prom nondet term initMs st before before cert_fuel
    _ Hstable Hbatch) as [cost Hpf].
  exists before, cost, (CPState.to_final_archState (CPState.make_final prom term final' pt')).
  split; [exact Hpf|exact Hres].
Qed.

Theorem VMSail_direct_to_promise_first fuel st returned fsig :
  VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  PState.from_archState prom initMs = Ok st →
  Exec.elem_of_results (returned, fsig)
    (opModel.run (@CPState.opmodel isem prom n) fuel term initMs st) →
  VMNormalizationSearchesComplete (projT1 fsig) →
  ∃ before cost (fsig' : {s & archState.is_terminated term s}),
    (∀ pf_fuel, cost < pf_fuel →
      Exec.elem_of_results (before, fsig')
        (opModel.run (@CPState.opmodel_pf_uncached isem prom n) pf_fuel term initMs st)) ∧
    projT1 fsig' = projT1 fsig.
Proof using Hreplay.
  intros Hswap Hsafe Hinit Hrun Hcomplete.
  destruct (VMSail_direct_to_promise_first_or_truncated fuel st returned fsig
    Hswap Hsafe Hinit Hrun) as [Hpf|[before [next [search_fuel [tid [ev
      [Hbefore [Hcandidate [Hpromise [Hcont [_ Hout]]]]]]]]]]]; [exact Hpf|].
  specialize (Hcomplete before next search_fuel tid ev Hbefore Hcandidate Hpromise Hcont).
  congruence.
Qed.

Corollary VMSail_full_mixed_final_inclusion fuel initPs returned
    fs (pt : archState.is_terminated term fs) :
  VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  PState.from_archState prom initMs = Ok initPs →
  Exec.elem_of_results (returned, existT fs pt)
    (opModel.run (@CPState.opmodel isem prom n) fuel term initMs initPs) →
  VMNormalizationSearchesComplete fs →
  ∃ cost, ∀ pf_fuel, cost < pf_fuel → ∃ pt',
    archModel.Res.FinalState fs pt' ∈
      Promising_to_Modelc_pf_uncached prom isem pf_fuel n term initMs.
Proof using Hreplay.
  intros Hswap Hsafe Hinit Hrun Hcomplete.
  destruct (VMSail_direct_to_promise_first fuel initPs returned (existT fs pt) Hswap Hsafe
    Hinit Hrun Hcomplete) as [before [cost [[fs' pt'] [Hpf Hfs]]]].
  cbn in Hfs. subst fs'. exists cost. intros pf_fuel Hfuel. exists pt'.
  eapply (promise_first_final_state_intro (prom := prom)); [exact Hinit|apply Hpf, Hfuel].
Qed.
End Replay.

(** * Final-state equivalence

    The direct-to-promise-first direction uses the instruction replay
    obligation, the TLBI commutation obligation and complete normalization
    searches. The reverse direction is
    [VMSail_complete_promise_first_final_sound], which needs complete
    certification searches along the promise-first run. *)
Theorem VMSail_promise_first_final_state_equiv bbm nondet {n}
    (term : terminationCondition n) initMs code :
  VMInstructionPromiseReplay bbm nondet term initMs code →
  VMTLBISwapReplay bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  (∀ initPs fuel returned fsig,
    PState.from_archState (VMPromising bbm) initMs = Ok initPs →
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) (VMPromising bbm) n)
        fuel term initMs initPs) →
    VMNormalizationSearchesComplete bbm nondet term initMs (projT1 fsig)) →
  (∀ fuel fs (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf_uncached (VMPromising bbm) (sail_tiny_arm_sem nondet)
        fuel n term initMs →
    PromiseFirstSearchesCompleteFromInitial (VMPromising bbm) nondet term initMs fuel) →
  VMPromisingFinalStateEquiv bbm (sail_tiny_arm_sem nondet) term initMs.
Proof.
  intros Hreplay Hswap Hsafe Hdirect Hpf fs. split.
  - intros [fuel [pt Hfinal]].
    destruct (direct_final_state_inv (prom := VMPromising bbm) _ term initMs fuel fs pt Hfinal)
      as [initPs [Hinit [returned [fsig [Hrun Hfs]]]]].
    pose proof (Hdirect initPs fuel returned fsig Hinit Hrun) as Hcomplete.
    destruct (VMSail_direct_to_promise_first bbm nondet term initMs code Hreplay fuel initPs
      returned fsig Hswap Hsafe Hinit Hrun Hcomplete)
      as [before [cost [[fs' pt'] [Hrun_pf Heq]]]].
    cbn in Heq. rewrite Hfs in Heq. subst fs'.
    exists (S cost), pt'.
    eapply (promise_first_final_state_intro (prom := VMPromising bbm));
      [exact Hinit|apply Hrun_pf; lia].
  - intros [fuel [pt Hfinal]].
    destruct (VMSail_complete_promise_first_final_sound bbm nondet term initMs fuel fs pt
      (Hpf fuel fs pt Hfinal) Hfinal) as [cost Hdirect_run].
    destruct (Hdirect_run (S cost) ltac:(lia)) as [pt' Hfinal'].
    exists (S cost), pt'. exact Hfinal'.
Qed.

Corollary VMSail_promise_first_final_state_equiv_sim bbm nondet {n}
    (term : terminationCondition n) initMs code :
  VMInstructionPromiseReplay bbm nondet term initMs code →
  VMTLBISwapSimulation bbm nondet term initMs code →
  VMSailNoSelfModifying bbm nondet term initMs code →
  (∀ initPs fuel returned fsig,
    PState.from_archState (VMPromising bbm) initMs = Ok initPs →
    Exec.elem_of_results (returned, fsig)
      (opModel.run (@CPState.opmodel (sail_tiny_arm_sem nondet) (VMPromising bbm) n)
        fuel term initMs initPs) →
    VMNormalizationSearchesComplete bbm nondet term initMs (projT1 fsig)) →
  (∀ fuel fs (pt : archState.is_terminated term fs),
    archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf_uncached (VMPromising bbm) (sail_tiny_arm_sem nondet)
        fuel n term initMs →
    PromiseFirstSearchesCompleteFromInitial (VMPromising bbm) nondet term initMs fuel) →
  VMPromisingFinalStateEquiv bbm (sail_tiny_arm_sem nondet) term initMs.
Proof.
  intros Hreplay Hsim. apply VMSail_promise_first_final_state_equiv; [exact Hreplay|].
  apply swap_simulation_replay, Hsim.
Qed.

End VMNormalization.
