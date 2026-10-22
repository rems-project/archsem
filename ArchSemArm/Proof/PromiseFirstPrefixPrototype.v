(******************************************************************************)
(* Experimental preservation of promise-bearing instruction prefixes          *)
(******************************************************************************)

From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst UMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent
  PromiseFirstExecutionCurrent PromiseFirstCounterexampleCurrent.

#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** This module is an experiment, separate from [CPState].  After a successful
    outcome has collected a promise, it retains that prefix as a stopped
    exploration as well as continuing the instruction.  A later discard
    therefore cannot erase the candidate.  Completed instructions use the
    original handlers and states. *)
Module PrefixCapture.
Section Model.
Context (prom : Promising.Model) {n : nat} (tid : fin n) (initmem : memoryMap).
Local Notation mEvent := prom.(Promising.mEvent).
Local Notation ppState :=
  (PPState.t prom.(Promising.tState) mEvent prom.(Promising.iis)).
Local Notation state := (list mEvent * ppState)%type.
Let event_eq_dec := prom.(Promising.mEvent_eq_dec).
Local Existing Instance event_eq_dec.

Definition retain_prefix {A} (continuation : Exec.t state string (option A)) :
    Exec.t state string (option A) :=
  λ st, match fst st with
    | [] => continuation st
    | _ :: _ => Exec.merge (Exec.make [(st, None)] []) (continuation st)
    end.

Fixpoint instruction_prefixes {A} base (mon : iMon A) :
    Exec.t state string (option A) :=
  match mon with
  | Ret a => mret (Some a)
  | Next (inl out) k =>
      r ← CPState.run_outcome_with_promise prom tid initmem base out;
      retain_prefix (instruction_prefixes base (k r))
  | Next (inr choice) k =>
      r ← mcall choice;
      instruction_prefixes base (k r)
  end.

Lemma retain_prefix_some {A} (continuation : Exec.t state string (option A))
    st st' a :
  Exec.elem_of_results (st', Some a) (retain_prefix continuation st) ↔
  Exec.elem_of_results (st', Some a) (continuation st).
Proof.
  unfold retain_prefix. destruct (fst st); [reflexivity|].
  unfold Exec.elem_of_results, Exec.merge. cbn.
  split.
  - intro H. apply elem_of_cons in H as [Heq|H]; [discriminate|exact H].
  - intro H. apply elem_of_cons. right. exact H.
Qed.

Lemma retain_prefix_none {A} (continuation : Exec.t state string (option A))
    st st' :
  Exec.elem_of_results (st', None) (retain_prefix continuation st) ↔
  (fst st ≠ [] ∧ st' = st) ∨
  Exec.elem_of_results (st', None) (continuation st).
Proof.
  unfold retain_prefix. destruct (fst st) eqn:Hproms.
  - split; [auto|]. intros [[H _]|H]; [contradiction|exact H].
  - unfold Exec.elem_of_results, Exec.merge. cbn.
    split.
    + intro H. apply elem_of_cons in H as [Heq|H];
        [left; inversion Heq; split; [discriminate|reflexivity]|auto].
    + intros [[_ ->]|H]; apply elem_of_cons; [left; reflexivity|right; exact H].
Qed.

Lemma instruction_complete {A} base (mon : iMon A) st st' a :
  Exec.elem_of_results (st', Some a) (instruction_prefixes base mon st) ↔
  Exec.elem_of_results (st', a)
    (cinterp (CPState.run_outcome_with_promise prom tid initmem base) mon st).
Proof.
  revert st st' a.
  induction mon as [r|call k IH]; intros st st' a; cbn.
  - split; intro H; apply Exec.elem_of_mret_inv in H as [-> Heq];
      inversion Heq; apply Exec.elem_of_mret.
  - destruct call as [out|[choices]]; split; intro H.
    + apply Exec.elem_of_bind_elim in H as [mid [res [Hout Htail]]].
      apply (proj1 (retain_prefix_some
        (instruction_prefixes base (k res)) mid st' a)) in Htail.
      apply (proj1 (IH _ _ _ _)) in Htail.
      eapply Exec.elem_of_bind_intro; eassumption.
    + apply Exec.elem_of_bind_elim in H as [mid [res [Hout Htail]]].
      eapply Exec.elem_of_bind_intro; [exact Hout|].
      apply (proj2 (retain_prefix_some
        (instruction_prefixes base (k res)) mid st' a)).
      apply (proj2 (IH _ _ _ _)). exact Htail.
    + apply Exec.elem_of_bind_elim in H as [mid [res [Hchoice Htail]]].
      eapply Exec.elem_of_bind_intro; [exact Hchoice|].
      apply (proj1 (IH _ _ _ _)). exact Htail.
    + apply Exec.elem_of_bind_elim in H as [mid [res [Hchoice Htail]]].
      eapply Exec.elem_of_bind_intro; [exact Hchoice|].
      apply (proj2 (IH _ _ _ _)). exact Htail.
Qed.

Lemma instruction_stopped_has_promises {A} base (mon : iMon A) st st' :
  Exec.elem_of_results (st', None) (instruction_prefixes base mon st) →
  fst st' ≠ [].
Proof.
  revert st st'. induction mon as [r|call k IH]; intros st st' H; cbn in H.
  - apply Exec.elem_of_mret_inv in H as [_ Heq]. discriminate.
  - destruct call as [out|[choices]].
    + apply Exec.elem_of_bind_elim in H as [mid [res [Hout Htail]]].
      apply (proj1 (retain_prefix_none
        (instruction_prefixes base (k res)) mid st')) in Htail
        as [[Hnonempty ->]|Htail];
        [exact Hnonempty|eapply IH; exact Htail].
    + apply Exec.elem_of_bind_elim in H as [mid [res [Hchoice Htail]]].
      eapply IH. exact Htail.
Qed.

Fixpoint run_thread (isem : iMon ()) (term : terminationCondition n)
    (fuel base : nat) : Exec.t state string CPState.RunEnd :=
  ts ← mget (PPState.state ∘ snd);
  if decide (base < prom.(Promising.tState_min_new_prom_view) ts) then
    mret CPState.StoppedEarly
  else if CPState.terminated_ts prom (term !!! tid) ts then
    mret CPState.Terminated
  else match fuel with
    | 0 => mret CPState.OutOfFuel
    | S fuel =>
        msetv (PPState.iis ∘ snd) prom.(Promising.iis_init);;
        res ← instruction_prefixes base isem;
        match res with
        | None => mret CPState.StoppedEarly
        | Some () => run_thread isem term fuel base
        end
    end.

Lemma thread_complete isem term fuel base st st' :
  Exec.elem_of_results (st', CPState.Terminated)
    (run_thread isem term fuel base st) ↔
  Exec.elem_of_results (st', CPState.Terminated)
    (CPState.run_to_termination isem prom term tid initmem fuel base st).
Proof.
  revert st st'. induction fuel as [|fuel IH]; intros st st'.
  all: cbn [run_thread CPState.run_to_termination].
  all: split; intro H;
    apply Exec.elem_of_bind_elim in H as [mid [ts [Hget H]]];
    apply Exec.elem_of_mget_inv in Hget as [-> ->].
  all: eapply Exec.elem_of_bind_intro with
    (st' := st) (a := ((PPState.state ∘ snd) st));
    [exact (Exec.elem_of_mget st (PPState.state ∘ snd))|].
  all: cbn [compose] in H |- *.
  all: destruct (decide
    (base < prom.(Promising.tState_min_new_prom_view) (PPState.state (snd st))));
    [exact H|].
  all: destruct (CPState.terminated_ts prom (term !!! tid) (PPState.state (snd st)))
    eqn:Hterm; try rewrite Hterm in H; try rewrite Hterm; try exact H.
  - apply Exec.elem_of_bind_elim in H as [reset [[] [Hreset H]]].
    eapply Exec.elem_of_bind_intro; [exact Hreset|].
    apply Exec.elem_of_bind_elim in H as [after [res [Hinst Htail]]].
    destruct res as [[]|].
    + eapply Exec.elem_of_bind_intro.
      * apply (proj1 (instruction_complete base isem reset after ()));
          exact Hinst.
      * apply (proj1 (IH _ _)). exact Htail.
    + apply Exec.elem_of_mret_inv in Htail as [_ Heq]. discriminate.
  - apply Exec.elem_of_bind_elim in H as [reset [[] [Hreset H]]].
    eapply Exec.elem_of_bind_intro; [exact Hreset|].
    apply Exec.elem_of_bind_elim in H as [after [[] [Hinst Htail]]].
    eapply Exec.elem_of_bind_intro with (a := Some ()).
    + apply (proj2 (instruction_complete base isem reset after ()));
        exact Hinst.
    + apply (proj2 (IH _ _)). exact Htail.
Qed.

Definition enumerate (isem : iMon ()) (term : terminationCondition n)
    (fuel : nat) (ts : prom.(Promising.tState)) (mem : list mEvent) :
    CPState.EnumerationResult prom :=
  let res := run_thread isem term fuel (length mem)
    ([], PPState.Make ts mem prom.(Promising.iis_init)) in
  let candidates := List.concat
    ((Exec.success_state_list res).*1 ++ (Exec.errors res).*1.*1)%list
    |> remove_dups in
  let candidates := prom.(Promising.filter_promises) n tid mem candidates in
  let finals := Exec.results res |>
    omap (λ '((new_proms, st), ending),
      if ending is CPState.Terminated then
        if is_emptyb new_proms then Some (PPState.state st) else None
      else None) in
  let errors := Exec.errors res |>
    omap (λ '((new_proms, _), err), if is_emptyb new_proms then Some err else None) in
  let out_of_fuel := bool_decide (∃ r ∈ (Exec.results res).*2,
    if r is CPState.OutOfFuel then True else False) in
  {| CPState.promises := candidates; CPState.final_states := finals;
     CPState.errors := errors; CPState.out_of_fuel := out_of_fuel |}.

Lemma final_candidates_equivalent isem term fuel ts mem
    (ts' : prom.(Promising.tState)) :
  ts' ∈ (enumerate isem term fuel ts mem).(CPState.final_states prom) ↔
  ts' ∈ (CPState.enumerate_results isem prom term tid initmem fuel ts mem)
    .(CPState.final_states prom).
Proof.
  unfold enumerate, CPState.enumerate_results.
  cbn [CPState.final_states].
  split; intro H; apply list_elem_of_omap in H;
    destruct H as [[[proms ppst] ending] [Hrun Hstate]];
    destruct ending; try discriminate;
    destruct proms; try discriminate;
    apply list_elem_of_omap;
    exists (([], ppst), CPState.Terminated); split; try exact Hstate.
  - apply (proj1 (thread_complete isem term fuel (length mem) _ _)). exact Hrun.
  - apply (proj2 (thread_complete isem term fuel (length mem) _ _)). exact Hrun.
Qed.

End Model.

Section Runner.
Context (prom : Promising.Model) (isem : iMon ()) {n : nat}.
Local Notation state :=
  (PState.t prom.(Promising.tState) prom.(Promising.mEvent) n).

Definition step (term : terminationCondition n) (fuel : nat) :
    Exec.t state string (option {s & archState.is_terminated term s}) :=
  st ← mGet;
  let execution_results := vmap (λ '(tid, ts),
    enumerate prom tid st.(PState.initmem) isem term fuel ts st.(PState.events))
    (venumerate st.(PState.tstates)) in
  opt ← mchoosel (seq 0 4);
  match opt : nat with
  | 0 =>
      tid ← mchoosef (fin n);
      ev ← mchoosel (execution_results !!! tid).(CPState.promises prom);
      nst ← mlift (PState.promise prom ev st);
      mSetv nst;; mret None
  | 1 =>
      states ← mchoosel $ cprodn (vmap (CPState.final_states prom) execution_results);
      let final := PState.Make states st.(PState.initmem) st.(PState.events) in
      pt ← guard_discard $ CPState.terminated prom term final;
      CPState.validate_final prom final;;
      mret (Some (CPState.to_final_archState (CPState.make_final prom term final pt)))
  | 2 =>
      err ← mchoosel $ List.concat (vmap (CPState.errors prom) execution_results);
      mthrow err
  | _ =>
      if bool_decide (∃ x ∈ map (CPState.out_of_fuel prom) execution_results, (x : bool))
      then mthrow "Promise first: out of fuel in enumeration"
      else mdiscard
  end.

Definition model : opModel n :=
  opModel.Make n state (λ _ init, PState.from_archState prom init)
    (λ term _ fuel, step term fuel).
End Runner.
End PrefixCapture.

Module DiscardCounterexampleRepaired.
Import DiscardCounterexample.

Example candidate_preserved_fuel_two :
  length (PrefixCapture.enumerate UMPromising 0%fin imem sem term 2
    (PState.tstate 0%fin init_ps) []).(CPState.promises UMPromising) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example repaired_result_count :
  length (Exec.results
    (opModel.run (@PrefixCapture.model UMPromising sem 2) 4 term init_ms init_ps)) = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(** Encode each field before comparing concrete results.  Register-map
    well-formedness proofs are omitted by [dmap_car]; [state_code_inj] ensures
    that this still compares complete architectural states. *)
Definition state_code (s : archState 2) : positive * positive * vec positive 2 :=
  (encode s.(archState.memory), encode s.(archState.address_space),
    vmap (λ regs, encode (dmap_car regs)) s.(archState.regs)).

Lemma state_code_inj s s' : state_code s = state_code s' → s = s'.
Proof.
  destruct s as [mem space regs], s' as [mem' space' regs'].
  unfold state_code. cbn. intro H.
  injection H as Hmem Hspace Hregs.
  apply encode_inj in Hmem. apply encode_inj in Hspace.
  assert (Hregisters : regs = regs').
  { apply vec_eq. intro tid. apply dmap_eq_car. apply encode_inj.
    pose proof (f_equal (λ v : vec positive 2, v !!! tid) Hregs) as Hlookup.
    cbn beta in Hlookup.
    rewrite !vlookup_map in Hlookup. exact Hlookup. }
  subst. reflexivity.
Qed.

Definition direct_arch_finals : list (archState 2) :=
  map (λ result, projT1 (snd result)) (Exec.results
    (opModel.run (@CPState.opmodel sem UMPromising 2) 5 term init_ms init_ps)).

Definition repaired_arch_finals : list (archState 2) :=
  map (λ result, projT1 (snd result)) (Exec.results
    (opModel.run (@PrefixCapture.model UMPromising sem 2) 4 term init_ms init_ps)).

Example repaired_matches_direct :
  (Listset repaired_arch_finals : listset (archState 2)) ≡ Listset direct_arch_finals.
Proof.
  assert (Hboth : map state_code repaired_arch_finals ⊆ map state_code direct_arch_finals ∧
    map state_code direct_arch_finals ⊆ map state_code repaired_arch_finals).
  { apply (proj1 (bool_decide_eq_true _)). vm_compute. reflexivity. }
  intro fs. change (fs ∈ repaired_arch_finals ↔ fs ∈ direct_arch_finals).
  split; intro Hin.
  - assert (Hcode : state_code fs ∈ map state_code direct_arch_finals).
    { apply (proj1 Hboth). apply list_elem_of_fmap. exists fs. auto. }
    apply list_elem_of_fmap in Hcode as [fs' [Heq Hfinal]].
    apply state_code_inj in Heq. subst. exact Hfinal.
  - assert (Hcode : state_code fs ∈ map state_code repaired_arch_finals).
    { apply (proj2 Hboth). apply list_elem_of_fmap. exists fs. auto. }
    apply list_elem_of_fmap in Hcode as [fs' [Heq Hfinal]].
    apply state_code_inj in Heq. subst. exact Hfinal.
Qed.

End DiscardCounterexampleRepaired.
