(** This module define common infrastructure shared between all promising model

    In particular it defined the PromisingModel type that can be used to
    manipulate promising models in a first order manner.
*)

Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.Exec.
Require Import SSCCommon.Effects.
Require Import SSCCommon.FMon.
Require Import SSCCommon.StateT.

Require Import Relations.
Require Import Program.

From stdpp Require Import relations.

Open Scope Z_scope.
Open Scope stdpp_scope.

Require Import ISASem.Interface.
Require Import ISASem.Deps.

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
Module Gen (IWD : InterfaceWithDeps) (TM : TermModelsT IWD).
  Import IWD.
  Import TM.
  Notation outcome := (IWD.outcome DepOn.t).
  Notation iMon := (IWD.iMon DepOn.t).
  Notation iSem := (IWD.iSem DepOn.t).

  Structure PromisingModel := {
      tState : Type;
      tState_init : (* tid *) nat → memoryMap → registerMap → tState;
      tState_regs : tState → registerMap;
      tState_nopromises : tState → bool;
      (** Intra instruction thread, reset after each instruction *)
      iis : Type;
      iis_init : iis;
      mEvent : Type;
      handler : (* tid *) nat → memoryMap →
                fHandler outcome
                  (ST.t (tState * PromMemory.t mEvent * iis) (Exec.t string));
      allowed_promises : (* tid *) nat → memoryMap → tState →
                         PromMemory.t mEvent → propset mEvent;
      (** I'm not considering that emit_promise can fail or have a
      non-deterministic behaviour *)
      emit_promise : (* tid *) nat → memoryMap → PromMemory.t mEvent →
                     mEvent → tState → tState;
      memory_snapshot : memoryMap → PromMemory.t mEvent → memoryMap;
    }.
  Arguments PromisingModel : clear implicits.

  (** This is a basic way of making a promising model executable, so I'll make
      it generic *)
  Structure BasicExecutablePM := {
      pModel :> PromisingModel;
      (** try to compute ALL allowed promises, if that is not possible (not
          enough fuel) then fail with error message.

          Soundness and completeness proofs are required to show that when not
          failing, promise_select effectively computes the allowed_promises
          set.*)
      promise_select :
        (* fuel *) nat -> (* tid *) nat → memoryMap → pModel.(tState) →
        PromMemory.t pModel.(mEvent) → Exec.t string pModel.(mEvent);

      promise_select_sound :
      ∀ n tid initMem ts mem,
        ∀'ev ∈ (promise_select n tid initMem ts mem),
          ev ∈ pModel.(allowed_promises) tid initMem ts mem;
      promise_select_complete :
      ∀ n tid initMem ts mem,
        Exec.has_results (promise_select n tid initMem ts mem) →
        ∀'ev ∈ pModel.(allowed_promises) tid initMem ts mem,
          ev ∈ promise_select n tid initMem ts mem
    }.
  Arguments BasicExecutablePM : clear implicits.


  Module PState. (* namespace *)

    Section PS.
      Context {iState : Type}.
      Context {tState : Type}.
      Context {mEvent : Type}.
      Context {n : nat}.

      Record t :=
        Make {
            istates : vec iState n;
            tstates : vec tState n;
            initmem : memoryMap;
            events : PromMemory.t mEvent;
          }.
      #[global] Instance set_t : Settable t :=
        settable! @Make <istates;tstates;initmem;events>.

      Definition istate tid := ((.!!! tid) ∘ istates).
      Definition tstate tid := ((.!!! tid) ∘ tstates).
    End PS.
    Arguments t : clear implicits.


    Section PSProm.
      Context (isem : iSem).
      Context (prom : PromisingModel).
      Context {n : nat}.
      Local Notation tState := prom.(tState).
      Local Notation mEvent := prom.(mEvent).
      Local Notation iState := isem.(isa_state).
      Local Notation t := (t iState tState mEvent n).

      (** Check if a thread has finished according to term *)
      Definition terminated_tid (term : terminationCondition n) (ps : t)
        (tid : fin n) := ps |> tstate tid |> prom.(tState_regs) |> term tid.

      (** Check if all thread have finished according to term *)
      Definition terminated (term : terminationCondition n) (ps : t) :=
        fforallb (terminated_tid term ps).

      (** Check if a thread has no outstanding promises *)
      Definition nopromises_tid (ps : t) (tid : fin n) :=
        ps |> tstate tid |> prom.(tState_nopromises).

      (** Check if all threads have no outstanding promises *)
      Definition nopromises (ps : t) := fforallb (nopromises_tid ps).

      (** Run on instruction in specific thread by tid *)
      Definition run_tid (st: t) (tid : fin n) :=
        let handler := prom.(handler) tid st.(initmem) in
        let sem := (isem.(semantic) (istate tid st)) in
        let init := (tstate tid st, st.(events), prom.(iis_init)) in
        '(ts, mem, iis, ist) ← cinterp handler sem init;
        st |> setv (tstate tid) ts
           |> setv (istate tid) ist
           |> setv events mem
           |> mret.

      (** Compute the set of allowed promises by a thread indexed by tid *)
      Definition allowed_promises_tid (st : t) (tid : fin n) :=
        prom.(allowed_promises) tid st.(initmem) (tstate tid st) st.(events).

      (** Emit a promise from a thread by tid *)
      Definition promise_tid (st : t) (tid : fin n) (event : mEvent) :=
        st |> set (tstate tid)
                  (prom.(emit_promise) tid st.(initmem) st.(events) event)
           |> set events (event ::.).

      (** The inductive stepping relation of the promising model *)
      Inductive step (ps : t) : (t) -> Prop :=
      | SRun (tid : fin n) (ps' : t) :
        ps' ∈ (run_tid ps tid) → step ps ps'
      | SPromise (tid : fin n) (event : mEvent) :
        event ∈ allowed_promises_tid ps tid → step ps (promise_tid ps tid event).

      Lemma step_promise (ps ps' : t) (tid : fin n) (event : mEvent) :
        event ∈ allowed_promises_tid ps tid →
        ps' = promise_tid ps tid event →
        step ps ps'.
      Proof using. sauto l:on. Qed.

      (** Create an initial promising state from a generic machine state *)
      Definition from_MState (ms: MState.t n) : t :=
        {|istates := fun_to_vec isem.(init_state);
          tstates :=
            fun_to_vec
              (λ tid,
                 prom.(tState_init) tid ms.(MState.memory)
                                                  $ ms.(MState.regs) !!! tid);
          initmem := ms.(MState.memory);
          events := []|}.

      (** Convert a promising state to a generic machine state.
          This is a lossy conversion *)
      Definition to_MState (ps: t) : MState.t n :=
        {| MState.regs := vmap (prom.(tState_regs)) ps.(tstates);
          MState.memory := prom.(memory_snapshot) ps.(initmem) ps.(events) |}.
    End PSProm.

  End PState.

  (** Create a non-computational model from an ISA model and promising model *)
  Definition Promising_to_Modelnc (isem : iSem) (prom : PromisingModel)
    : Model.nc False :=
    λ n (initMs : MState.init n),
      {[ mr |
         let initPs := PState.from_MState isem prom initMs in
         match mr with
         | Model.Res.FinalState fs =>
             ∃ finPs, rtc (PState.step isem prom) initPs finPs ∧
                        fs.(MState.state) = PState.to_MState isem prom finPs ∧
                        fs.(MState.termCond) = initMs.(MState.termCond) ∧
                        PState.nopromises isem prom finPs
         | Model.Res.Error s =>
             ∃ finPs tid, rtc (PState.step isem prom) initPs finPs ∧
                            PState.run_tid isem prom finPs tid = Exec.Error s
         | _ => False
         end]}.

  (** Computational promising state. Right now it the same type as PState.t but
      with more methods *)
  Module CPState.
    Include PState.
    Section CPS.
    Context (isem : iSem).
    Context (prom : BasicExecutablePM).
    Context {n : nat}.
    Context (term : terminationCondition n).
    Local Notation tState := (tState prom).
    Local Notation mEvent := (mEvent prom).
    Local Notation iState := isem.(isa_state).
    Local Notation t := (t iState tState mEvent n).

    (** Get a list of possible promising for a thread by tid *)
    Definition promise_select_tid (fuel : nat) (st : t)
        (tid : fin n) : Exec.t string mEvent :=
      prom.(promise_select) n tid (initmem st) (tstate tid st) (events st).

    (** Take any promising step for that tid and promise it *)
    Definition cpromise_tid (fuel : nat) (st : t) (tid : fin n)
      : Exec.t string t :=
      ev ← promise_select_tid fuel st tid;
      Exec.ret $ promise_tid isem prom st tid ev.

    (** Run any possible step, this is the most exhaustive and expensive kind of
        search but it is obviously correct. If a thread has reached termination
        no progress is made in the thread (either instruction running or
        promises *)
    Definition run_step (fuel : nat) (st : t) :=
      tid ← Exec.choose (fin n);
      if terminated_tid isem prom term st tid then Exec.discard
      else Exec.merge (run_tid isem prom st tid) (cpromise_tid fuel st tid).

    (** The type of final promising state return by run *)
    Definition final := { x : t | terminated isem prom term x }.

    Definition make_final (p : t) := exist (terminated isem prom term) p.

    (** Convert a final promising state to a generic final state *)
    Program Definition to_final_MState (f : final) : MState.final n :=
      {|MState.istate :=
          {|MState.state := to_MState isem prom f;
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
          if dec $ terminated isem prom term st then Exec.ret (make_final st _)
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
    Definition Promising_to_Modelc {isem : iSem} (prom : BasicExecutablePM)
      (fuel : nat) : Model.c False :=
      fun n (initMs : MState.init n) =>
        let initPs := PState.from_MState isem prom initMs in
        Model.Res.from_exec
          $ CPState.to_final_MState
          <$> CPState.run isem prom initMs.(MState.termCond) fuel initPs.

    (* TODO state some soundness lemma between Promising_to_Modelnc and
        Promising_Modelc *)

End Gen.

Module Type GenT (IWD : InterfaceWithDeps) (TM : TermModelsT IWD).
  Include Gen IWD TM.
End GenT.
