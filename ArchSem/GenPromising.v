(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
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

(** This module define common infrastructure shared between all promising model

    In particular it defined the PromisingModel type that can be used to
    manipulate promising models in a first order manner.
*)

From ASCommon Require Import Options.
From ASCommon Require Import Common Exec FMon StateT.

Require Import Interface.
Require Import TermModels.



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
          if (k <=? len)%nat then List.nth_error mem (len - k)%nat else None
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
  Fixpoint attach_timestamps (mem : t) : list (ev * nat) :=
    match mem with
    | [] => []
    | h :: q =>
      (h, List.length mem) :: attach_timestamps q
    end.

  Definition cut_after_with_timestamps (v : nat) (mem : t) : list (ev * nat) :=
    take (length mem - v) (attach_timestamps mem).

End PM.
Arguments t : clear implicits.
End PromMemory.
#[export] Typeclasses Transparent PromMemory.t.

(* Partial Promising State *)
Module PPState.
  Section PPS.
  Context {tState : Type}.
  Context {mEvent : Type}.
  Context {iis_t : Type}.

  Record t :=
    Make {
        state : tState;
        mem : PromMemory.t mEvent;
        iis : iis_t;
      }.
  #[global] Instance eta : Settable t :=
    settable! @Make <state;mem;iis>.
  End PPS.
  Arguments t : clear implicits.
End PPState.

(* to be imported *)
Module GenPromising (IWA : InterfaceWithArch) (TM : TermModelsT IWA).
  Import IWA.Arch.
  Import IWA.Interface.
  Import TM.

  Module Promising.

  (** This structure defines a promising model that can share common
      infrastructure define in this file. This structure allows to define 4
      models:
      - The non-certified non-executable version where any promises can be made
        as long as they are all fulfilled by the end
      - The certified non-executable version where promises can only be made if
        there is a sequential trace that lead to that promise being fulfilled.
      - The direct executable model which explores all interleaving of promising and instruction steps
      - The promise-free executable model which does a smarter search based on
        some commutation properties of steps, namely that instruction step of
        different thread commute and that a promise step after an instruction
        step can always be commuted to be before.

      The first one is there for theoretical reason, but it probably can return
      UB on any input, but any non-error behavior it exhibits should also be in
      the certified version, so it can be useful for sanity checking.

      Theoretically the last 3 models are equivalent (up to fuel for the
      executable ones).

      TODO: Figure out generic properties to relate those 4 models.
   *)
  Structure Model := {
      (** The thread state of the model *)
      tState : Type;
      (** Initialize the model thread state from architectural state *)
      tState_init : (* tid *) nat → memoryMap → registerMap → tState;
      (** Get a register map out of a thread state to test the termination
          condition and compute a final state *)
      tState_regs : tState → registerMap;
      (** Check if a thread state has no pending promises, which means that it
          can be explain with the current memory state *)
      tState_nopromises : tState → bool;
      (** Intra instruction state, reset after each instruction *)
      iis : Type;
      iis_init : iis;
      (** The type of memory event, any communication between threads must go here *)
      mEvent : Type;
      mEvent_eq_dec : EqDecision mEvent;
      (** Give the tid that initiated that event *)
      mEvent_tid : mEvent → nat;
      (** The address space this model is built against, we expect non-secure
          for Arm here *)
      address_space : addr_space;
      (** The handler for instruction effects, applies the effect of a single
          outcome to the thread state. If the outcome need one or more event to
          be added,it adds them and return the view of those events in the
          option, otherwise it returns [None] *)
      handle_outcome : (* tid *) nat → (* initial memory *) memoryMap →
                  ∀ out : outcome,
                  Exec.t (PPState.t tState mEvent iis) string
                         (eff_ret out * option nat);
      (** Update the thread state after emission of a promise. The new promise
          has already been added to the memory when calling that function. I'm
          not considering that emit_promise can fail or have a non-deterministic
          behaviour. TODO: Add support for failure *)
      emit_promise : (* tid *) nat → memoryMap → PromMemory.t mEvent →
                     mEvent → tState → tState;
      (** Hook for extra UB checks to be done before returning a final state,
          e.g. BBM checks, return any error string (empty means no errors) *)
      check_valid_end : (* tid *) nat → memoryMap → tState →
                             PromMemory.t mEvent → list string;
      (** Computes the final memory after a certain promising history *)
      memory_snapshot : memoryMap → PromMemory.t mEvent → memoryMap;
    }.
  #[global] Arguments Model : clear implicits.
  End Promising.

  (** To make a promising model executable, one must provide a function that
      compute for each thread a summary of the next actions that can be taken as
      an [ExecutablePMResult]. This summary contains:
      - A list [promises] of certified promises that can be added which should
        be the set defined by [allowed_promises];
      - A list of [final_states] that can reached with the current memory history
        *without* adding new promises;
      - A list of [errors] that can be reached with the current memory history
        *without* adding new promises;
      - If the exploration runs [out_of_fuel]. *)
  (* Record EnumerationResult {mEvent tState} := *)
  (*   { *)
  (*     promises : list mEvent; *)
  (*     final_states : list tState; *)
  (*     errors : list string; *)
  (*     out_of_fuel : bool *)
  (*     }. *)
  (* Arguments EnumerationResult : clear implicits. *)

  (** This is a basic way of making a promising model executable, so I'll make
      it generic *)
  (* Structure Executable := { *)
  (*     pModel :> Model; *)

  (*     (** Run the thread to termination, collecting the possible model *)
  (*     transitions from that thread. See above for the description of what is collected *) *)
  (*     enumerate_promises_and_terminal_states : *)
  (*       (* fuel *) nat → (* tid *) nat → *)
  (*       (* termination condition *) (registerMap → bool) → *)
  (*       memoryMap → pModel.(tState) → PromMemory.t pModel.(mEvent) → *)
  (*       EnumerationResult pModel.(mEvent) pModel.(tState); *)

  (*     enumerate_promises_allowed : *)
  (*       ∀ fuel tid term initMem ts mem epr, *)
  (*         enumerate_promises_and_terminal_states fuel tid term initMem ts mem = epr → *)
  (*         ∀ ev, ev ∈ epr.(promises) ↔ ev ∈ pModel.(allowed_promises) tid initMem ts mem; *)

  (*     terminal_state_no_outstanding_promise : *)
  (*       ∀ fuel tid term initMem ts mem epr, *)
  (*         enumerate_promises_and_terminal_states fuel tid term initMem ts mem = epr → *)
  (*         ∀ tts ∈ epr.(final_states), pModel.(tState_nopromises) tts; *)

  (*     terminal_state_is_terminated : *)
  (*     ∀ fuel tid term initMem ts mem epr, *)
  (*         enumerate_promises_and_terminal_states fuel tid term initMem ts mem = epr → *)
  (*         ∀ tts ∈ epr.(final_states), term (pModel.(tState_regs) tts); *)

  (*     (* TODO: add terminal_state_is_reachable *) *)
  (*   }. *)
  (* Arguments Executable : clear implicits. *)
  (* End PM. *)
  (* Export (coercions) PM. *)

  Module PState. (* namespace *)
    Section PS.
      Context {tState : Type}.
      Context {mEvent : Type}.
      Context {n : nat}.

      Record t :=
        Make {
            tstates : vec tState n;
            initmem : memoryMap;
            events : PromMemory.t mEvent;
          }.
      #[global] Instance set_t : Settable t :=
        settable! @Make <tstates;initmem;events>.

      Definition tstate tid := ((.!!! tid) ∘ tstates).
      #[global] Typeclasses Transparent tstate.
    End PS.
    Arguments t : clear implicits.

    Section PSProm.
      Import Promising.
      Context (isem : iMon ()).
      Context (prom : Model).
      Context {n : nat}.
      Local Notation tState := prom.(tState).
      Local Notation mEvent := prom.(mEvent).
      Local Notation t := (t tState mEvent n).

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

      (** Check if a thread state can be at a valid end *)
      Definition check_valid_end_tid (ps : t) (tid : fin n) :=
        prom.(check_valid_end) tid ps.(initmem) (tstate tid ps) ps.(events).

      (** Check if all thread states can be at a valid end *)
      Definition check_valid_end (ps : t) :=
        List.concat (map (check_valid_end_tid ps) (enum (fin n))).


      Definition PState_PPState tid (pst : t) :
          PPState.t tState mEvent prom.(iis) :=
        PPState.Make (tstate tid pst) pst.(events) prom.(iis_init).

      Instance PState_PPState_set tid : Setter (PState_PPState tid) :=
        λ update_ppst pst,
          let ppst := PState_PPState tid pst |> update_ppst in
          pst
          |> setv (tstate tid) ppst.(PPState.state)
          |> setv events ppst.(PPState.mem).

      (** Run on instruction in specific thread by tid, allowing new promises *)
      Definition run_tid (tid : fin n) : Exec.t t string () :=
        st ← mGet;
        let handler out := prom.(handle_outcome) tid (st.(initmem)) out |$> fst in
        Exec.liftSt (PState_PPState tid) (cinterp handler isem).

      Definition seq_step (tid : fin n) : relation t :=
        λ st1 st2, st2 ∈ Exec.success_state_list $ run_tid tid st1.

      (** Compute the set of allowed promises by a thread indexed by tid *)
      Definition allowed_promises_tid (certified : bool) (st : t) (tid : fin n)
        (ev : mEvent) :
          Prop :=
        if certified then
          let st_plus := set PState.events (ev ::.) st in
          ∃ st', rtc (seq_step tid) st_plus st' ∧
                   nopromises_tid st tid
        else prom.(mEvent_tid) ev = tid.

      (** Emit a promise from a thread by tid *)
      Definition promise_tid (st : t) (tid : fin n) (event : mEvent) :=
        let st := set events (event ::.) st in
        set (tstate tid)
          (prom.(emit_promise) tid st.(initmem) st.(events) event)
          st.

      (** The inductive stepping relation of the promising model *)
      Inductive step (certified : bool) (ps : t) : (t) -> Prop :=
      | SRun (tid : fin n) (ps' : t) :
        (ps', ()) ∈ (run_tid tid ps) → step certified ps ps'
      | SPromise (tid : fin n) (event : mEvent) :
        allowed_promises_tid certified ps tid event →
        step certified ps (promise_tid ps tid event).

      Lemma step_promise certified (ps ps' : t) (tid : fin n) (event : mEvent) :
        allowed_promises_tid certified ps tid event →
        ps' = promise_tid ps tid event →
        step certified ps ps'.
      Proof using. sauto l:on. Qed.

      (** Create an initial promising state from a generic machine state *)
      Definition from_archState (ms: archState n) : t :=
        {|tstates :=
            fun_to_vec
              (λ tid,
                 prom.(tState_init) tid ms.(archState.memory)
                                                  $ ms.(archState.regs) !!! tid);
          initmem := ms.(archState.memory);
          events := []|}.

      (** Convert a promising state to a generic machine state.
          This is a lossy conversion *)
      Definition to_archState (ps: t) : archState n :=
        {|archState.regs := vmap (prom.(tState_regs)) ps.(tstates);
          archState.memory := prom.(memory_snapshot) ps.(initmem) ps.(events);
          archState.address_space := prom.(address_space) |}.
    End PSProm.

  End PState.

  (** Create a non-computational model from an ISA model and promising model *)
  Definition Promising_to_Modelnc (certified : bool) (prom : Promising.Model)
       (isem : iMon ()) : archModel.nc ∅ :=
    λ n term (initMs : archState n),
      {[ mr : archModel.res ∅ n term |
         let initPs := PState.from_archState prom initMs in
         match mr with
         | archModel.Res.FinalState fs _ =>
             ∃ finPs, rtc (PState.step isem prom certified) initPs finPs ∧
                        PState.to_archState prom finPs = fs ∧
                        PState.nopromises prom finPs ∧
                        PState.check_valid_end prom finPs = []
         | archModel.Res.Error s =>
             ∃ finPs,
              rtc (PState.step isem prom certified) initPs finPs ∧
                ((∃ tid, Error s ∈ PState.run_tid isem prom tid finPs)
                  ∨
                 (PState.terminated prom term finPs ∧
                  PState.nopromises prom finPs ∧
                  s ∈ PState.check_valid_end prom finPs))
         | _ => False
         end]}.

  (** Computational promising state. Right now it the same type as PState.t but
      with more methods *)
  Module CPState.
    Include PState.
    Section CPS.
    Import Promising.
    Context (isem : iMon ()).
    Context (prom : Model).
    Context {n : nat}.
    Context (term : terminationCondition n).
    Local Notation tState := (tState prom).
    Local Notation mEvent := (mEvent prom).
    Local Notation iis := (iis prom).
    Local Notation t := (t tState mEvent n).

    Definition mEvent_eq_dec := prom.(mEvent_eq_dec).
    Local Existing Instance mEvent_eq_dec.

    (** The type of final promising state return by run *)
    Definition final := { x : t | terminated prom term x }.

    Definition make_final (p : t) := exist (terminated prom term) p.

    (** Convert a final promising state to a generic final state *)
    Program Definition to_final_archState (f : final) :
        {s & archState.is_terminated term s} :=
      existT (to_archState prom f) _.
    Solve All Obligations with
      hauto unfold:terminated unfold:archState.is_terminated l:on db:vec, brefl.


    Section EnumerateResult.
      Context (tid : fin n) (initmem : memoryMap).
    Definition run_outcome_with_promise (base : nat) (out : outcome) :
      Exec.t (list mEvent * PPState.t tState mEvent iis) string (eff_ret out) :=
      '(res, vpre_opt) ← Exec.liftSt snd $ prom.(handle_outcome) tid initmem out;
      if vpre_opt is Some vpre then
        if decide (vpre ≤ base)%nat then
          mem ← mget (PPState.mem ∘ snd);
          (* Take all promises after base (made by that outcome) and add them to
             the list of possible new promises *)
          mset fst (take (length mem - base) mem ++.);;
          mret res
        else mret res
      else
        mret res.

    Fixpoint run_to_termination (fuel : nat) (base : nat) :
      Exec.t (list mEvent * PPState.t tState mEvent iis) string bool :=
      match fuel with
      | 0%nat =>
          ts ← mget (PPState.state ∘ snd);
          mret (term tid (prom.(tState_regs) ts))
      | S fuel =>
          let handler := run_outcome_with_promise base in
          cinterp handler isem;;
          ts ← mget (PPState.state ∘ snd);
          if term tid (prom.(tState_regs) ts) then
            mret true
          else
            msetv (PPState.iis ∘ snd) prom.(iis_init);;
            run_to_termination fuel base
      end.

    Record EnumerationResult :=
      {
        promises : list mEvent;
        final_states : list tState;
        errors : list string;
        out_of_fuel : bool
        }.

    Definition enumerate_results (fuel : nat) (ts : tState) (mem : PromMemory.t mEvent)
      : EnumerationResult :=
      let base := List.length mem in
      let res :=
        run_to_termination fuel base
          ([], PPState.Make ts mem prom.(iis_init))
      in
      let success_states := Exec.success_state_list res in
      let out_of_fuel := bool_decide (∃ r ∈ (Exec.results res).*2, ¬ (r : bool)) in
      (* let out_of_fuel := true in *)
      let promises := List.concat (success_states.*1) |> remove_dups in
      let tstates :=
        success_states
        |> omap (λ '(new_proms, st),
               if is_emptyb new_proms then Some (PPState.state st)
               else None) in
      let errors :=
        res |> Exec.errors |>
          omap (λ '((new_proms, _), err_msg),
              if is_emptyb new_proms then Some err_msg
              else None) in
      {|promises:=promises;
        final_states:=tstates;
        errors:=errors;
        out_of_fuel:=out_of_fuel|}.
    End EnumerateResult.

    (** Get a list of possible promises for a thread by tid *)
    Definition promise_select_tid (fuel : nat) (st : t)
        (tid : fin n) : Exec.res string mEvent :=
      let (promises, _, _, out_of_fuel) := enumerate_results
                                        tid (initmem st) fuel (tstate tid st) (events st) in
      if out_of_fuel then
        b ← mchoosef;
        if (b : bool) then mthrow "out of fuel" else mchoosel promises
      else mchoosel promises.

    (** Take any promising step for that tid and promise it *)
    Definition cpromise_tid (fuel : nat) (tid : fin n)
      : Exec.t t string () :=
    λ st,
      let res_st :=
        ev ← promise_select_tid fuel st tid;
        mret $ promise_tid prom st tid ev
      in
        Exec.make ((.,()) <$> res_st.(Exec.results)) ((st,.) <$> res_st.(Exec.errors)).

    (** Run any possible step, this is the most exhaustive and expensive kind of
        search but it is obviously correct. If a thread has reached termination
        no progress is made in the thread (either instruction running or
        promises *)
    Definition run_step (fuel : nat) : Exec.t t string () :=
      st ← mGet;
      tid ← mchoose n;
      if terminated_tid prom term st tid then mdiscard
      else
        promise ← mchoosel (enum bool);
        if (promise : bool) then cpromise_tid fuel tid else run_tid isem prom tid.

    (** Computationally evaluate all the possible allowed final states according
        to the promising model prom starting from st *)
    Fixpoint run (fuel : nat) : Exec.t t string final :=
      st ← mGet;
      if decide $ terminated prom term st is left pt then mret (make_final st pt)
      else
        if fuel is S fuel then
          run_step (S fuel);;
          run fuel
        else mthrow "Could not finish running within the size of the fuel".

    (** Computationally evaluate all the possible allowed final states according
        to the promising model prom starting from st with promise-first optimization.
        The size of fuel should be at least (# of promises) + max(# of instructions) + 1 *)
    Fixpoint run_promise_first (fuel : nat) : Exec.t t string final :=
      if fuel is S fuel then
        st ← mGet;
        (* Find out next possible promises or terminating states at the current thread *)
        let execution_results :=
          vmap (λ '(tid, ts),
              enumerate_results tid (initmem st) fuel ts (events st)
            ) (venumerate (tstates st)) in
        opt ← mchoosel (seq 0 4);
        match opt : nat with
        | 0 =>
          '(tid : fin n) ← mchoosef;
          next_ev ← mchoosel (execution_results !!! tid).(promises);
          mSet (λ st, promise_tid prom st tid next_ev);;
          run_promise_first fuel
        | 1 =>
          (* Compute cartesian products of the possible thread states *)
          let tstates_all := cprodn (vmap final_states execution_results) in
          let new_finals :=
            omap (λ tstates,
              let st := Make tstates st.(PState.initmem) st.(PState.events) in
              if decide $ terminated prom term st is left pt
              then Some (make_final st pt)
              else None
              ) tstates_all in
          mchoosel new_finals
        | 2 =>
          let errs := List.concat (vmap errors execution_results) in
          err ← mchoosel errs;
          mthrow err
        | _ =>
          if bool_decide (∃ x ∈ map out_of_fuel execution_results, (x : bool)) then
            mthrow "Promise first: out of fuel in enumeration"
          else mdiscard
        end
      else
        mthrow "Promise first: out of fuel in main loop".

    End CPS.
    Arguments to_final_archState {_ _ _}.
  End CPState.

  (** Create computational models from an ISA model and promising model *)
  Definition Promising_to_Modelc (prom : Promising.Model) (isem : iMon ())
      (fuel : nat) : archModel.c ∅ :=
    λ n term (initMs : archState n),
      PState.from_archState prom initMs |>
      archModel.Res.from_exec
        $ CPState.to_final_archState
        <$> CPState.run isem prom term fuel.

  Definition Promising_to_Modelc_pf (prom : Promising.Model) (isem : iMon ())
      (fuel : nat) : archModel.c ∅ :=
    λ n term (initMs : archState n),
      PState.from_archState prom initMs |>
      archModel.Res.from_exec
        $ CPState.to_final_archState
        <$> CPState.run_promise_first isem prom term fuel.

End GenPromising.

Module Type GenPromisingT (IWA : InterfaceWithArch) (TM : TermModelsT IWA).
  Include GenPromising IWA TM.
End GenPromisingT.
