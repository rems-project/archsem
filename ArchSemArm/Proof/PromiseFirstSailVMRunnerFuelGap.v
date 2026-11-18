(******************************************************************************)
(* Recovery of the direct VM runner's previously missing architectural state    *)
(******************************************************************************)
From ASCommon Require Import Options Common CList Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstConcreteCurrent
  PromiseFirstEquivCurrent PromiseFirstCounterexampleCurrent PromiseFirstSailSerialization.

Module VMRunnerFuelRecovery.
Import TwoThreadFinals.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis Memory.t.
Open Scope stdpp. Open Scope bv.
Local Notation prom := (VMPromising true).
Local Notation isem := (sail_tiny_arm_sem false).

(** R1 points to a selector, R3 to a shared word, and R6 to initially
    unmapped bytes. Thread 1 publishes the selector and reads the shared
    word. A nonzero read lets it write four bytes to R6. Thread 0 then has
    an eight-byte store and a four-byte load at that address on its taken
    branch. At the four-byte load the current VM may consult the earlier
    four-byte write when overlaying the later eight-byte store.

    The two thread-0 stores to R3 are P (0) and Q (42). The fall-through
    path creates a short-fuel certificate for Q while P is outstanding.
    It subsequently fails to fulfill P because Q has advanced coherence.
    Thread 1's leading NOPs can execute before Q in the direct runner.
    In the promise-first runner they still count toward its final batch. *)
Definition nops (addrs : list address) (m : memoryMap) :=
  foldl (λ m addr, mem_insert addr 4 0xd503201f m) m addrs.

Definition mem : memoryMap := ∅
  |> mem_insert 0x5000 4 0xf9400022 (* LDR X2,[X1] *)
  |> mem_insert 0x5004 4 0xb50003e2 (* CBNZ X2,0x5080 *)
  |> mem_insert 0x5008 4 0xf9000069 (* STR X9,[X3] (Q) *)
  |> nops [0x500c;0x5010;0x5014;0x5018;0x501c;0x5020;0x5024;0x5028]
  |> mem_insert 0x502c 4 0xf9000060 (* STR X0,[X3] (P) *)
  |> mem_insert 0x5080 4 0xf9000060 (* STR X0,[X3] (P) *)
  |> mem_insert 0x5084 4 0xf90000c0 (* STR X0,[X6] *)
  |> mem_insert 0x5088 4 0xb94000c7 (* LDR W7,[X6] *)
  |> mem_insert 0x508c 4 0xf9000069 (* STR X9,[X3] (Q) *)
  |> nops [0x5100;0x5104;0x5108;0x510c;0x5110;0x5114;0x5118;0x511c]
  |> mem_insert 0x5120 4 0xf900002a (* STR X10,[X1] *)
  |> mem_insert 0x5124 4 0xf9400068 (* LDR X8,[X3] *)
  |> mem_insert 0x5128 4 0xb40000c8 (* CBZ X8,0x5140 *)
  |> mem_insert 0x512c 4 0xb90000c8 (* STR W8,[X6] *)
  |> mem_insert 0x6000 8 0 |> mem_insert 0x6010 8 0.
Definition regs pc : registerMap := ∅ |> reg_insert pc_reg pc |> reg_insert CurrentEL 1
  |> reg_insert SCTLR_EL1 0 |> reg_insert R0 0 |> reg_insert R1 0x6000
  |> reg_insert R2 0 |> reg_insert R3 0x6010 |> reg_insert R6 0x6030
  |> reg_insert R7 0 |> reg_insert R8 0 |> reg_insert R9 42 |> reg_insert R10 1.
Definition initial : archState 2 := {| archState.regs := [#regs 0x5000;regs 0x5100];
  archState.memory := mem; archState.address_space := PAS_NonSecure |}.
Definition term : terminationCondition 2 := [# [0x5090]; [0x5130]].
Definition p := Ev.Msg (Msg.make 0 0x6010 8 0).
Definition q := Ev.Msg (Msg.make 0 0x6010 8 42).
Definition state := PState.t TState.t Ev.t 2.
Definition enum (st : state) tid fuel := CPState.enumerate_results_filtered isem prom term
  tid (PState.initmem st) fuel (PState.tstate tid st) (PState.events st).
Definition init := PState.from_archState prom initial.
Definition cert (st : state) tid fuel ev := if bool_decide (ev ∈ CPState.promises prom (enum st tid fuel))
  then match PState.promise prom ev st with Ok st' => [st'] | Error _ => [] end else [].
Definition inst (st : state) (tid : fin 2) := if CPState.terminated_tid prom term st tid then []
  else (Exec.results (PState.run_tid isem prom tid st)).*1.
Definition valid (st : state) := (bool_decide (CPState.terminated prom term st) && bool_decide (CPState.nopromises prom st))
    && bool_decide (PState.check_valid_end prom st = []).

Open Scope list_scope. Open Scope nat_scope.
Inductive action := Ins (tid : fin 2) | Emit (tid : fin 2) (ev : Ev.t).
Definition choose a fuel st := match a with
  | Ins tid => inst st tid | Emit tid ev => cert st tid fuel ev end.
Lemma choose_step a fuel (st next : state) : List.In next (choose a fuel st) →
  Exec.elem_of_results (next,None) (CPState.run_transition isem prom term fuel st).
Proof.
  destruct a as [tid|tid ev].
  - unfold choose, inst. destruct (CPState.terminated_tid prom term st tid) eqn:Hterm; [contradiction|].
    intros ([mid []] & <- & Hin)%in_map_iff. apply instruction_transition_any_fuel.
    exists tid. split; [exact Hterm|apply list_elem_of_In, Hin].
  - unfold choose, cert. destruct (bool_decide _) eqn:Hcand; [|contradiction].
    destruct (PState.promise prom ev st) as [mid|err] eqn:Hp; [|contradiction].
    intros [<-|[]]. apply (promise_first_none_to_direct_none (prom := prom) isem term fuel st mid).
    + intros. eapply VMPromising_filter_promises_subset; eassumption.
    + eapply run_transition_promise_first_none_intro with (tid := tid) (ev := ev) (nst := mid);
        [|exact Hp|reflexivity]. rewrite promise_first_execution_results_lookup.
      apply (proj1 (bool_decide_eq_true _)), Hcand.
Qed.

Fixpoint replay acts fuel st {struct fuel} := match fuel with 0 => [] | S k =>
  match acts with [] => if valid st then [st] else []
  | a :: rest => flat_map (replay rest k) (choose a (S k) st) end end.
Lemma replay_sound acts fuel (st last : state) : List.In last (replay acts fuel st) →
  ∃ fsig, projT1 fsig = PState.to_archState prom last ∧ Exec.elem_of_results (last,fsig)
    (opModel.run (@CPState.opmodel isem prom 2) fuel term initial st).
Proof.
  revert st acts. induction fuel as [|k IH]; intros st acts H; [inversion H|].
  cbn [replay] in H. cbn [opModel.run]. destruct acts as [|a rest].
  - destruct (valid st) eqn:Hv; [|inversion H]. destruct H as [<-|[]].
    unfold valid in Hv. apply andb_true_iff in Hv as [Hok Hcheck]. apply andb_true_iff in Hok as [pt Hnone].
    apply bool_decide_eq_true in pt, Hnone, Hcheck.
    exists (CPState.to_final_archState (CPState.make_final prom term st pt)). split; [reflexivity|].
    eapply Exec.elem_of_bind_intro; [eapply run_transition_some_intro with (pt := pt)|apply Exec.elem_of_mret].
    unfold CPState.validate_final_state. destruct (Exec.elem_of_guard_discard (E := string) st Hnone) as [pn Hguard].
    eapply Exec.elem_of_bind_intro; [exact Hguard|].
    rewrite Hcheck. apply Exec.elem_of_mret.
  - apply in_flat_map in H as (mid & Hstep & Hlast). destruct (IH mid rest Hlast) as (fsig & Hfs & Hrun).
    exists fsig. split; [exact Hfs|]. eapply Exec.elem_of_bind_intro; [eapply choose_step; exact Hstep|exact Hrun].
Qed.
Definition actions := replicate 9 (Ins 1%fin) ++ [Emit 0%fin p;Emit 0%fin q] ++
  replicate 3 (Ins 1%fin) ++ replicate 6 (Ins 0%fin).
Definition b := Ev.Msg (Msg.make 1 0x6000%bv 8 1%bv).
Definition s := Ev.Msg (Msg.make 1 0x6030%bv 4 42%bv).
Definition t := Ev.Msg (Msg.make 0 0x6030%bv 8 0%bv).
Definition promises := [b;p;q;s;t].

Section PromiseReplay.
Context (model : opModel 2) (events : opModel.state model → list Ev.t).
Fixpoint prefix_finals (expected : list Ev.t) (fuel : nat) (st : opModel.state model)
    {struct fuel} : list (opModel.state model * {fs & archState.is_terminated term fs}) :=
  match fuel with
  | 0 => []
  | S k => flat_map (λ '(next, result),
      match expected, result with
      | [], Some final => [(next, final)]
      | ev :: es, None => if decide (head (events next) = Some ev)
                           then prefix_finals es k next else []
      | _, _ => []
      end) (Exec.results (opModel.step model term initial (S k) st))
  end.
Lemma prefix_finals_sound expected fuel st last fsig :
  (last, fsig) ∈ prefix_finals expected fuel st →
  Exec.elem_of_results (last, fsig) (opModel.run model fuel term initial st).
Proof.
  revert expected st. induction fuel as [|k IH]; intros expected st Hin; [inversion Hin|].
  cbn [prefix_finals] in Hin. apply list_elem_of_In, in_flat_map in Hin as ([next opt] & Hstep & Htail).
  apply list_elem_of_In in Hstep. cbn [opModel.run].
  destruct expected as [|ev es], opt as [final|]; cbn beta iota in Htail; try contradiction.
  - destruct Htail as [Heq|[]]. injection Heq as -> ->.
    eapply Exec.elem_of_bind_intro; [exact Hstep|apply Exec.elem_of_mret].
  - destruct (decide _) in Htail; [|contradiction].
    eapply Exec.elem_of_bind_intro; [exact Hstep|]. apply (IH es), list_elem_of_In, Htail.
Qed.
End PromiseReplay.

Definition direct_finals (st : state) := map (PState.to_archState prom) (replay actions 21 st).
Definition uncached_finals (st : state) := map (λ r, projT1 (snd r))
  (prefix_finals (@CPState.opmodel_pf_uncached isem prom 2) PState.events promises 18 st).
Definition cached_finals (st : state) := map (λ r, projT1 (snd r))
  (prefix_finals (@CPState.opmodel_pf isem prom 2) (PState.events ∘ CPState.pstate prom)
    promises 18 (CPState.PFMake prom st (vreplicate 2 None))).
Definition agrees (st : state) :=
  let uncached := map state_code (uncached_finals st) in
  let cached := map state_code (cached_finals st) in
  existsb (λ fs, bool_decide (state_code fs ∈ uncached ∧ state_code fs ∈ cached))
    (direct_finals st).
Example checked : match init with Ok st => agrees st | Error _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Local Lemma cached_result (initial_state : archState 2) (halt : terminationCondition 2)
    start fuel last fs (pt : archState.is_terminated halt fs) :
  PState.from_archState prom initial_state = Ok start →
  Exec.elem_of_results (last, existT fs pt) (opModel.run (@CPState.opmodel_pf isem prom 2)
    fuel halt initial_state (CPState.PFMake prom start (vreplicate 2 None))) →
  archModel.Res.FinalState fs pt ∈ Promising_to_Modelc_pf prom isem fuel 2 halt initial_state.
Proof.
  intros Hi Hr. unfold Promising_to_Modelc_pf, opModel.to_archModel.
  cbn. rewrite Hi. cbn. eapply final_state_from_exec_intro; exact Hr.
Qed.

(** The same architectural state, including every register and memory byte,
    occurs in the direct run at 21 and both promise-first runs at 18. *)
Theorem recovered_final :
  ∃ fs (pd pu pc : archState.is_terminated term fs),
    archModel.Res.FinalState fs pd ∈ Promising_to_Modelc prom isem 21 2 term initial ∧
    archModel.Res.FinalState fs pu ∈ Promising_to_Modelc_pf_uncached prom isem 18 2 term initial ∧
    archModel.Res.FinalState fs pc ∈ Promising_to_Modelc_pf prom isem 18 2 term initial.
Proof.
  pose proof checked as H. destruct init as [st|err] eqn:Hinit; [|discriminate].
  unfold agrees in H. apply existsb_exists in H as (fs & Hd & Hboth).
  apply bool_decide_eq_true in Hboth as [Hu Hc].
  unfold direct_finals in Hd. apply in_map_iff in Hd as (last & Hfs & Hlast).
  destruct (replay_sound actions 21 st last Hlast) as ([df pd] & Hdf & Hdr).
  cbn in Hdf. rewrite Hfs in Hdf. subst df.
  apply list_elem_of_fmap in Hu as (ufs & Hueq & Hu).
  apply list_elem_of_fmap in Hc as (cfs & Hceq & Hc).
  apply state_code_inj in Hueq, Hceq. subst ufs cfs.
  unfold uncached_finals in Hu. apply list_elem_of_fmap in Hu as ([ul [uf pu]] & Hueq & Hu).
  unfold cached_finals in Hc. apply list_elem_of_fmap in Hc as ([cl [cf pc]] & Hceq & Hc).
  cbn in Hueq, Hceq. subst uf cf. exists fs, pd, pu, pc. split.
  - eapply direct_final_state_intro; [exact Hinit|exact Hdr].
  - split.
    + eapply promise_first_final_state_intro; [exact Hinit|eapply prefix_finals_sound; exact Hu].
    + eapply cached_result; [exact Hinit|eapply prefix_finals_sound; exact Hc].
Qed.
End VMRunnerFuelRecovery.
