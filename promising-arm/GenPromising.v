(** This module define common infrastructure shared between all promising model

    In particular it defined the PromisingModel type that can be used to
    manipulate promising models in a first order manner.
*)


Require SSCCommon.Exec.
Module Exec := SSCCommon.Exec.
Import Exec.Tactics.

Require Import Ensembles.

Require Import Strings.String.

Require Import SSCCommon.Common.

Require Import Relations.
Require Import Program.

Open Scope Z_scope.
Open Scope stdpp_scope.

Require Import ISASem.Interface.

Require Import GenModels.TermModels.



(** This module define the representation of a promising model memory as
    a sequence of events.

    The sequence is 1 indexed so that timestamp 0 represent memory as it was
    initially.

    The current implementation is a list in reverse order but that may change *)
Module PromMemory. (* namespace *)
Section PM.

  Context {ev :Type}.

  (* I'm using a simple list representation. The most recent write is the head
     of the list. *)
  Definition t := list ev.

  (** Definition of the memory numbering. So it can be used with the !! operator
  *)
  Global Instance lookup_inst : Lookup nat ev t := {
      lookup k mem :=
        if k =? 0%nat then None
        else
          let len := List.length mem in
          if (len <? k)%nat then List.nth_error mem (len - k)%nat else None
    }.

  (** Cuts the memory to only the memory that exists before the view, included.
  *)
  Definition cut_before (v : nat) (mem : t) : t :=
    let len := List.length mem in
    (* Here I'm using the m - n = 0 when n > m behavior *)
    drop (len - v) mem.

  (** Cuts the memory to only the memory that exists after the view, excluded.
  *)
  Definition cut_after (v : nat) (mem : t) : t :=
    let len := List.length mem in
    take (len - v) mem.

End PM.
Arguments t : clear implicits.
End PromMemory.

(* to be imported *)
Module Gen (Arch : Arch) (IA : InterfaceT Arch) (TM : TermModelsT Arch IA).
  Import IA.
  Notation iSem := (IA.iSem empOutcome).

  Import TM.

  (** Promising thread *)
  Module PThread. (* namespace *)
    Record t {tState mEvent : Type} :=
      Make {
          tid : nat;
          initmem : memoryMap;
          tstate : tState;
          events : PromMemory.t mEvent;
        }.
    Arguments t : clear implicits.
  End PThread.

  Structure PromisingModel := {
      tState : Type;
      tState_init : memoryMap -> registerMap -> tState;
      tState_regs : tState -> registerMap;
      mEvent : Type;
      run_instr :
        iSem -> PThread.t tState mEvent ->
        Exec.t string (tState * PromMemory.t mEvent);
      allowed_promises : iSem -> PThread.t tState mEvent -> Ensemble mEvent;
      (** I'm not considering that emit_promise can fail or have a
      non-deterministic behaviour *)
      emit_promise : iSem -> PThread.t tState mEvent -> mEvent -> tState;
      memory_snapshot : memoryMap -> PromMemory.t mEvent -> memoryMap;
    }.

  (** This is a basic way of making a promising model executable, so I'll make
      it generic *)
  Structure BasicExecutablePM := {
      pModel :> PromisingModel;
      (** try to compute ALL allowed promises, if that is not possible (not
          enough fuel) then fail with error message.

          Soundness and completeness proofs are required to show that when not failing,
          promise_select effectively computes the allowed_promises set.*)
      promise_select :
      (* fuel *) nat -> iSem -> PThread.t pModel.(tState) pModel.(mEvent) ->
      Exec.t string pModel.(mEvent);

      promise_select_sound :
      forall n sem ft,
        ∀'ev ∈ (promise_select n sem ft), pModel.(allowed_promises) sem ft ev;
      promise_select_complete :
      forall n sem ft,
        Exec.has_results (promise_select n sem ft) ->
        ∀'ev ∈ pModel.(allowed_promises) sem ft, ev ∈ promise_select n sem ft
    }.


  Module PState. (* namespace *)
    Section PS.
      Context {prom : PromisingModel}.
      Context (inst_sem : iSem).
      Local Notation tState := (tState prom).
      Local Notation mEvent := (mEvent prom).
      Local Notation thread := (PThread.t tState mEvent).

      Record t {n : nat} :=
        Make {
            tstates : vec tState n;
            initmem : memoryMap;
            events : PromMemory.t mEvent;
          }.
      Arguments t : clear implicits.
      #[global] Instance set_t {n} : Settable _ :=
        settable! @Make n <tstates;initmem;events>.

    Global Instance lookup {n} : LookupTotal (fin n) thread (t n) :=
      fun tid ps =>
      {|PThread.tid := tid;
        PThread.initmem := ps.(initmem);
        PThread.tstate := ps.(tstates) !!! tid;
        PThread.events := ps.(events) |}.

    Definition update {n : nat} (ft : thread) (ps : t n) :=
      match decide (ft.(PThread.tid) < n)%nat with
      | left prf =>
          let tid := nat_to_fin prf in
          ps |> set tstates <[tid := ft.(PThread.tstate)]>
             |> set events (fun _ => ft.(PThread.events))
      | _ => ps
      end.

    Definition terminated_tid {n} (term : terminationCondition n) (ps : t n)
       (tid : fin n) :=
      ps.(tstates) !!! tid |> prom.(tState_regs) |> term tid.

    Definition terminated {n} (term : terminationCondition n) (ps : t n) :=
      fforallb (terminated_tid term ps).

    Definition run_tid {n} (st: t n) (tid : fin n) :=
      '(ts, mem) ← prom.(run_instr) inst_sem (st !!! tid);
      st |> set tstates <[tid := ts]>
         |> set events (fun _ => mem)
         |> Exec.ret.

    Definition allowed_promises_tid {n} (st : t n) (tid : fin n) :=
      prom.(allowed_promises) inst_sem (st !!! tid).

    Definition promise_tid {n} (st : t n) (tid : fin n) (event : mEvent) :=
      st |> set tstates
                <[tid := prom.(emit_promise) inst_sem (st !!! tid) event]>
         |> set events (event ::.).

    Inductive step {n} (ps : t n) : (t n) -> Prop :=
    | SRun (tid : fin n) (ps' : t n) :
        ps' ∈ (run_tid ps tid) -> step ps ps'
    | SPromise (tid : fin n) (event : mEvent) :
      allowed_promises_tid ps tid event -> step ps (promise_tid ps tid event).

    Definition from_MState {n} (ms: MState.t n) : t n :=
      {|tstates := vmap (prom.(tState_init) ms.(MState.memory)) ms.(MState.regs);
        initmem := ms.(MState.memory);
        events := []|}.

    Definition to_MState {n} (ps: t n) : MState.t n :=
      {| MState.regs := vmap prom.(tState_regs) ps.(tstates);
         MState.memory := prom.(memory_snapshot) ps.(initmem) ps.(events) |}.
    End PS.
    Arguments t : clear implicits.
    End PState.

  Definition Promising_to_Modelnc (prom : PromisingModel) (isem : iSem)
    : Model.nc False :=
    fun n (initMs : MState.init n) (mr : ModelResult.t False n) =>
      let initPs : PState.t prom n := PState.from_MState initMs in
      match mr with
      | ModelResult.FinalState fs =>
          exists finPs, (clos_refl_trans (PState.step isem)) initPs finPs /\
                     fs.(MState.state) = PState.to_MState finPs /\
                     fs.(MState.termCond) = initMs.(MState.termCond)
      | ModelResult.Error s =>
          exists finPs tid, clos_refl_trans (PState.step isem) initPs finPs /\
                         PState.run_tid isem finPs tid = Exec.Error s
      | _ => False
      end.

  (** Computational promising state. Right now it the same type as PState.t but
      with more methods *)
  Module CPState.
    Export PState.
    Section CPS.
    Context {prom : BasicExecutablePM}.
    Context (isem : iSem).
    Context {n : nat}.
    Context (term : terminationCondition n).
    Local Notation tState := (tState prom).
    Local Notation mEvent := (mEvent prom).
    Local Notation thread := (PThread.t tState mEvent).
    Let t := t prom n.

    Definition promise_select_tid (fuel : nat) (st : t)
        (tid : fin n) : Exec.t string mEvent :=
      prom.(promise_select) n isem (st !!! tid).

    (** Take any promising step for that tid and promise it *)
    Definition cpromise_tid (fuel : nat) (st : t) (tid : fin n)
      : Exec.t string t :=
      ev ← promise_select_tid fuel st tid;
      Exec.ret $ promise_tid isem st tid ev.

    (** Run any possible step, this is the most exhaustive and expensive kind of
        search but it is obviously correct. If a thread has reached termination
        no progress is made in the thread (either instruction running or
        promises *)
    Definition run_step (fuel : nat) (st : t) :=
      tid ← Exec.choose (fin n);
      if terminated_tid term st tid then Exec.discard
      else Exec.merge (run_tid isem st tid) (cpromise_tid fuel st tid).

    Definition final := { x : t | terminated term x }.

    Definition make_final (p : t) := exist (terminated term) p.

    Program Definition to_final_MState (f : final) : MState.final n :=
      {|MState.istate :=
          {|MState.state := to_MState f;
            MState.termCond := term|};
        MState.terminated := _ |}.
    Solve All Obligations with hauto db:vec b:on unfold:terminated.

    Program Fixpoint run (fuel : nat) (st : t) :=
      match fuel with
      | 0%nat => Exec.Error "not enough fuel"
      | S fuel =>
          if dec $ terminated term st then Exec.ret (make_final st _)
          else
            nextSt ← run_step fuel st;
            run fuel st
      end.
    Solve All Obligations with hauto b:on.
    End CPS.
  End CPState.
  Arguments CPState.to_final_MState {_ _ _}.


    Definition Promising_to_Modelc (prom : BasicExecutablePM) (isem : iSem)
      (fuel : nat) : Model.c False :=
      fun n (initMs : MState.init n) =>
        let initPs : PState.t prom n := PState.from_MState initMs in
        ModelResult.from_exec
          $ CPState.to_final_MState
          <$> CPState.run isem initMs.(MState.termCond) fuel initPs.

    (* TODO state some soundness lemma between Promising_to_Modelnc and
        Promising_Modelc *)

End Gen.

Module Type GenT (Arch : Arch) (IA : InterfaceT Arch)
  (TM : TermModelsT Arch IA).
  Include Gen Arch IA TM.
End GenT.
