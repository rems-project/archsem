(** This module define common infrastructure shared between all promising model

    In particular it defined the PromisingModel type that can be used to
    manipulate promising models in a first order manner.
*)


Require Import SSCCommon.Exec.

Require Import Ensembles.

Require Import Strings.String.

Require Import SSCCommon.Common.

Require Import Relations.
Require Import Program.

From stdpp Require Import relations.

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

  (** Cuts the memory to only what exists before the timestamp, included.
      The timestamp can still be computed the same way.
  *)
  Definition cut_before (v : nat) (mem : t) : t :=
    let len := List.length mem in
    (* Here I'm using the m - n = 0 when n > m behavior *)
    drop (len - v) mem.

  (** Cuts the memory to only what exists after the timestamp, excluded.
      Beware of timestamp computation. If you need the original timestamps,
      use cut_after_timestamps
   *)
  Definition cut_after (v : nat) (mem : t) : t :=
    let len := List.length mem in
    take (len - v) mem.

  (** Cuts the memory to only what exists after the timestamp, excluded.
      Provide the original timestamps as a additional value.
  *)

  Fixpoint cut_after_with_timestamps (v : nat) (mem : t) : list (ev * nat) :=
    let len := List.length mem in
    if (Nat.leb v len)%nat then []
    else
      match mem with
      | [] => []
      | h :: q => (h, len) :: cut_after_with_timestamps v q
      end.



End PM.
Arguments t : clear implicits.
End PromMemory.

(* to be imported *)
Module Gen (Arch : Arch) (IA : InterfaceT Arch) (TM : TermModelsT Arch IA).
  Import IA.
  Notation outcome := (IA.outcome empOutcome).
  Notation iMon := (IA.iMon empOutcome).
  Notation iSem := (IA.iSem empOutcome).

  Import TM.

  (** Promising thread *)
  Module PThread. (* namespace *)
    Section PT.
      Context {tState mEvent : Type}.
    Record t :=
      make {
          tid : nat;
          initmem : memoryMap;
          tstate : tState;
          events : PromMemory.t mEvent;
        }.
    #[global] Instance eta : Settable t :=
      settable! @make <tid;initmem;tstate;events>.

    Definition promise (ev : mEvent) (pt : t) := set events (ev ::.) pt.

    Definition next_time (pt : t) : nat := length pt.(events).

    End PT.

    Arguments t : clear implicits.
  End PThread.

  Structure PromisingModel {isem : iSem} := {
      tState : Type;
      tState_init : (*tid *) nat -> memoryMap -> registerMap -> tState;
      tState_regs : tState -> registerMap;
      tState_isa_state : tState -> isem.(isa_state);
      tState_nopromises : tState -> bool;
      mEvent : Type;
      pthread := PThread.t tState mEvent;
      run_instr : pthread -> Exec.t string pthread ;
      allowed_promises : pthread -> Ensemble mEvent;
      (** I'm not considering that emit_promise can fail or have a
      non-deterministic behaviour *)
      emit_promise : pthread -> mEvent -> tState;
      memory_snapshot : memoryMap -> PromMemory.t mEvent -> memoryMap;
    }.
  Arguments PromisingModel : clear implicits.


  (** This is a basic way of making a promising model executable, so I'll make
      it generic *)
  Structure BasicExecutablePM {isem : iSem} := {
      pModel :> PromisingModel isem;
      (** try to compute ALL allowed promises, if that is not possible (not
          enough fuel) then fail with error message.

          Soundness and completeness proofs are required to show that when not
          failing, promise_select effectively computes the allowed_promises
          set.*)
      promise_select :
        (* fuel *) nat -> pModel.(pthread) -> Exec.t string pModel.(mEvent);

      promise_select_sound :
      forall n ft,
        ∀'ev ∈ (promise_select n ft),
          pModel.(allowed_promises) ft ev;
      promise_select_complete :
      forall n ft,
        Exec.has_results (promise_select n ft) ->
        ∀'ev ∈ pModel.(allowed_promises) ft,
          ev ∈ promise_select n ft
    }.
  Arguments BasicExecutablePM : clear implicits.


  Module PState. (* namespace *)

    Section PS.
      Context {tState : Type}.
      Context {mEvent : Type}.
      Context {n : nat}.
      Local Notation pthread := (PThread.t tState mEvent).

    Record t :=
      Make {
          tstates : vec tState n;
          initmem : memoryMap;
          events : PromMemory.t mEvent;
        }.
    #[global] Instance set_t : Settable t :=
      settable! @Make <tstates;initmem;events>.

     Global Instance lookup : LookupTotal (fin n) pthread t :=
        fun tid ps =>
        {|PThread.tid := tid;
          PThread.initmem := ps.(initmem);
          PThread.tstate := ps.(tstates) !!! tid;
          PThread.events := ps.(events) |}.

      (** Update a PState for a single thread with a thread state pt *)
      Definition update (pt : pthread) (ps : t) :=
        match decide (pt.(PThread.tid) < n)%nat with
        | left prf =>
            let tid := nat_to_fin prf in
            ps |> set tstates <[tid := pt.(PThread.tstate)]>
              |> set events (fun _ => pt.(PThread.events))
        | _ => ps
        end.
    End PS.
    Arguments t : clear implicits.


    Section PSProm.
      Context {isem : iSem}.
      Context (prom : PromisingModel isem).
      Context {n : nat}.
      Local Notation tState := prom.(tState).
      Local Notation mEvent := prom.(mEvent).
      Local Notation pthread := prom.(pthread).
      Local Notation t := (t tState mEvent n).

      (** Check if a thread has finished according to term *)
      Definition terminated_tid (term : terminationCondition n) (ps : t)
        (tid : fin n) :=
        ps.(tstates) !!! tid |> prom.(tState_regs) |> term tid.

      (** Check if all thread have finished according to term *)
      Definition terminated (term : terminationCondition n) (ps : t) :=
        fforallb (terminated_tid term ps).

      (** Check if a thread has no outstanding promises *)
      Definition nopromises_tid (ps : t) (tid : fin n) :=
        ps.(tstates) !!! tid |> prom.(tState_nopromises).

      (** Check if all threads have no outstanding promises *)
      Definition nopromises (ps : t) := fforallb (nopromises_tid ps).

      (** Run on instruction in specific thread by tid *)
      Definition run_tid (st: t) (tid : fin n) :=
        '(pt) ← prom.(run_instr) (st !!! tid);
        st |> update pt |> Exec.ret.

      (** Compute the set of allowed promises by a thread indexed by tid *)
      Definition allowed_promises_tid (st : t) (tid : fin n) :=
        prom.(allowed_promises) (st !!! tid).

      (** Emit a promise from a thread by tid *)
      Definition promise_tid (st : t) (tid : fin n) (event : mEvent) :=
        st |> set tstates
                  <[tid := prom.(emit_promise) (st !!! tid) event]>
          |> set events (event ::.).

      (** The inductive stepping relation of the promising model *)
      Inductive step (ps : t) : (t) -> Prop :=
      | SRun (tid : fin n) (ps' : t) :
          ps' ∈ (run_tid ps tid) -> step ps ps'
      | SPromise (tid : fin n) (event : mEvent) :
        event ∈ allowed_promises_tid ps tid -> step ps (promise_tid ps tid event).

      Lemma step_promise (ps ps' : t) (tid : fin n) (event : mEvent) :
        event ∈ allowed_promises_tid ps tid ->
        ps' = promise_tid ps tid event ->
        step ps ps'.
      Proof. sauto l:on. Qed.

      (** Create an initial promising state from a generic machine state *)
      Definition from_MState (ms: MState.t n) : t :=
        {|tstates :=
            fun_to_vec
              (fun tid => prom.(tState_init) tid ms.(MState.memory)
                                                  $ ms.(MState.regs) !!! tid);
          initmem := ms.(MState.memory);
          events := []|}.

      (** Convert a promising state to a generic machine state.
          This is a lossy conversion *)
      Definition to_MState (ps: t) : MState.t n :=
        {| MState.regs := vmap prom.(tState_regs) ps.(tstates);
          MState.memory := prom.(memory_snapshot) ps.(initmem) ps.(events) |}.
    End PSProm.

  End PState.

  (** Create a non-computational model from an ISA model and promising model *)
  Definition Promising_to_Modelnc {isem : iSem} (prom : PromisingModel isem)
    : Model.nc False :=
    fun n (initMs : MState.init n) (mr : ModelResult.t False n) =>
      let initPs := PState.from_MState prom initMs in
      match mr with
      | ModelResult.FinalState fs =>
          exists finPs, rtc (PState.step prom) initPs finPs /\
                     fs.(MState.state) = PState.to_MState prom finPs /\
                     fs.(MState.termCond) = initMs.(MState.termCond) /\
                     PState.nopromises prom finPs
      | ModelResult.Error s =>
          exists finPs tid, rtc (PState.step prom) initPs finPs /\
                         PState.run_tid prom finPs tid = Exec.Error s
      | _ => False
      end.

  (** Computational promising state. Right now it the same type as PState.t but
      with more methods *)
  Module CPState.
    Include PState.
    Section CPS.
    Context {isem : iSem}.
    Context (prom : BasicExecutablePM isem).
    Context {n : nat}.
    Context (term : terminationCondition n).
    Local Notation tState := (tState prom).
    Local Notation mEvent := (mEvent prom).
    Local Notation thread := (PThread.t tState mEvent).
    Local Notation t := (t tState mEvent n).

    (** Get a list of possible promising for a thread by tid *)
    Definition promise_select_tid (fuel : nat) (st : t)
        (tid : fin n) : Exec.t string mEvent :=
      prom.(promise_select) n (st !!! tid).

    (** Take any promising step for that tid and promise it *)
    Definition cpromise_tid (fuel : nat) (st : t) (tid : fin n)
      : Exec.t string t :=
      ev ← promise_select_tid fuel st tid;
      Exec.ret $ promise_tid prom st tid ev.

    (** Run any possible step, this is the most exhaustive and expensive kind of
        search but it is obviously correct. If a thread has reached termination
        no progress is made in the thread (either instruction running or
        promises *)
    Definition run_step (fuel : nat) (st : t) :=
      tid ← Exec.choose (fin n);
      if terminated_tid prom term st tid then Exec.discard
      else Exec.merge (run_tid prom st tid) (cpromise_tid fuel st tid).

    (** The type of final promising state return by run *)
    Definition final := { x : t | terminated prom term x }.

    Definition make_final (p : t) := exist (terminated prom term) p.

    (** Convert a final promising state to a generic final state *)
    Program Definition to_final_MState (f : final) : MState.final n :=
      {|MState.istate :=
          {|MState.state := to_MState prom f;
            MState.termCond := term|};
        MState.terminated := _ |}.
    Solve All Obligations with
      hauto unfold:terminated unfold:MState.is_terminated l:on db:vec, brefl.

    (** Computational evaluate all the possible allowed final states according
        to the promising model prom starting from st *)
    Program Fixpoint run (fuel : nat) (st : t) : Exec.t string final :=
      match fuel with
      | 0%nat => Exec.Error "not enough fuel"
      | S fuel =>
          if dec $ terminated prom term st then Exec.ret (make_final st _)
          else
            nextSt ← run_step fuel st;
            run fuel st
      end.
    Solve All Obligations with naive_solver.
    End CPS.
    Arguments final {_} _ {_}.
    Arguments to_final_MState {_ _ _ _}.
  End CPState.


  (** Create a computational model from an ISA model and promising model *)
    Definition Promising_to_Modelc {isem : iSem} (prom : BasicExecutablePM isem)
      (fuel : nat) : Model.c False :=
      fun n (initMs : MState.init n) =>
        let initPs := PState.from_MState prom initMs in
        ModelResult.from_exec
          $ CPState.to_final_MState
          <$> CPState.run prom initMs.(MState.termCond) fuel initPs.

    (* TODO state some soundness lemma between Promising_to_Modelnc and
        Promising_Modelc *)

End Gen.

Module Type GenT (Arch : Arch) (IA : InterfaceT Arch)
  (TM : TermModelsT Arch IA).
  Include Gen Arch IA TM.
End GenT.
