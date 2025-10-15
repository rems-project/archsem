(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  All files except SailArmInstTypes.v are distributed under the             *)
(*  license below (BSD-2-Clause). The former is distributed                   *)
(*  under a mix of BSD-2-Clause and BSD-3-Clause Clear, as described          *)
(*  in the file header.                                                       *)
(*                                                                            *)
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

Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.Exec.
Require Import ASCommon.Effects.
Require Import ASCommon.FMon.
Require Import ASCommon.HVec.
Require Import ASCommon.StateT.

Require Import Relations.
Require Import Program.

From stdpp Require Import relations.

#[local] Open Scope Z_scope.
#[local] Open Scope stdpp_scope.

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

  Structure PromisingModel := {
      tState : Type;
      tState_init : (* tid *) nat → memoryMap → registerMap → tState;
      tState_regs : tState → registerMap;
      tState_nopromises : tState → bool;
      (** Intra instruction state, reset after each instruction *)
      iis : Type;
      iis_init : iis;
      mEvent : Type;
      address_space : addr_space;
      handler : (* tid *) nat → memoryMap →
                fHandler outcome
                  (Exec.t (PPState.t tState mEvent iis) string);
      allowed_promises : (* tid *) nat → memoryMap → tState →
                         PromMemory.t mEvent → propset mEvent;
      (** Update the thread state after emission of a promise.
          The new promise has been added to the memory when calling that function.
          I'm not considering that emit_promise can fail or have a
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
        (* fuel *) nat → (* tid *) nat →
        (* termination condition *) (registerMap → bool) →
        memoryMap → pModel.(tState) → PromMemory.t pModel.(mEvent) →
        Exec.res string pModel.(mEvent);

      promise_select_sound :
      ∀ fuel tid term initMem ts mem,
        ∀ ev ∈ (promise_select fuel tid term initMem ts mem),
          ev ∈ pModel.(allowed_promises) tid initMem ts mem;
      promise_select_complete :
      ∀ fuel tid term initMem ts mem,
        ¬ Exec.has_error (promise_select fuel tid term initMem ts mem) →
        ∀ ev ∈ pModel.(allowed_promises) tid initMem ts mem,
          ev ∈ promise_select fuel tid term initMem ts mem
    }.
  Arguments BasicExecutablePM : clear implicits.

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
      Context (isem : iMon ()).
      Context (prom : PromisingModel).
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

      Definition PState_PPState tid (pst : t) :
          PPState.t tState mEvent prom.(iis) :=
        PPState.Make (tstate tid pst) pst.(events) prom.(iis_init).

      Instance PState_PPState_set tid : Setter (PState_PPState tid) :=
        λ update_ppst pst,
          let ppst := PState_PPState tid pst |> update_ppst in
          pst
          |> setv (tstate tid) ppst.(PPState.state)
          |> setv events ppst.(PPState.mem).

      (** Run on instruction in specific thread by tid *)
      Definition run_tid (tid : fin n) : Exec.t t string () :=
        st ← mGet;
        let handler := prom.(handler) tid (st.(initmem)) in
        Exec.liftSt (PState_PPState tid) (cinterp handler isem).

      (** Compute the set of allowed promises by a thread indexed by tid *)
      Definition allowed_promises_tid (st : t) (tid : fin n) :=
        prom.(allowed_promises) tid st.(initmem) (tstate tid st) st.(events).

      (** Emit a promise from a thread by tid *)
      Definition promise_tid (st : t) (tid : fin n) (event : mEvent) :=
        let st := set events (event ::.) st in
        set (tstate tid)
          (prom.(emit_promise) tid st.(initmem) st.(events) event)
          st.

      (** The inductive stepping relation of the promising model *)
      Inductive step (ps : t) : (t) -> Prop :=
      | SRun (tid : fin n) (ps' : t) :
        (ps', ()) ∈ (run_tid tid ps) → step ps ps'
      | SPromise (tid : fin n) (event : mEvent) :
        event ∈ allowed_promises_tid ps tid → step ps (promise_tid ps tid event).

      Lemma step_promise (ps ps' : t) (tid : fin n) (event : mEvent) :
        event ∈ allowed_promises_tid ps tid →
        ps' = promise_tid ps tid event →
        step ps ps'.
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
  Definition Promising_to_Modelnc (isem : iMon ()) (prom : PromisingModel)
    : archModel.nc ∅ :=
    λ n term (initMs : archState n),
      {[ mr : archModel.res ∅ n term |
         let initPs := PState.from_archState prom initMs in
         match mr with
         | archModel.Res.FinalState fs _ =>
             ∃ finPs, rtc (PState.step isem prom) initPs finPs ∧
                        PState.to_archState prom finPs = fs ∧
                        PState.nopromises prom finPs
         | archModel.Res.Error s =>
             ∃ finPs tid, rtc (PState.step isem prom) initPs finPs ∧
                            Error s ∈ PState.run_tid isem prom tid finPs
         | _ => False
         end]}.

  (** Computational promising state. Right now it the same type as PState.t but
      with more methods *)
  Module CPState.
    Include PState.
    Section CPS.
    Context (isem : iMon ()).
    Context (prom : BasicExecutablePM).
    Context {n : nat}.
    Context (term : terminationCondition n).
    Local Notation tState := (tState prom).
    Local Notation mEvent := (mEvent prom).
    Local Notation t := (t tState mEvent n).

    (** Get a list of possible promises for a thread by tid *)
    Definition promise_select_tid (fuel : nat) (st : t)
        (tid : fin n) : Exec.res string mEvent :=
      prom.(promise_select) fuel tid (term tid) (initmem st) (tstate tid st) (events st).

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

    (** Run only promise steps. If a thread has reached termination
        no progress is made in the thread (either instruction running or
        promises *)
    Fixpoint run_step_promise_first (fuel : nat) (terminated : fin n -> bool) : Exec.t t string () :=
      st ← mGet;
      let all_terminated := ∀ tid ∈ (enum (fin n)), terminated tid in
      if decide all_terminated then
        mret ()
      else
        if fuel is S fuel then
          tid ← mchoose n;
          if decide $ (terminated tid) then
            run_step_promise_first fuel terminated
          else
            let ev_res := promise_select_tid fuel st tid in
            if decide (Exec.has_error ev_res) then
              run_step_promise_first fuel (λ t, if decide (t = tid) then true else (terminated t))
            else
              let res_st :=
                ev ← ev_res;
                mret $ promise_tid prom st tid ev
              in
              mlift $ Exec.make ((.,()) <$> res_st.(Exec.results)) ((st,.) <$> res_st.(Exec.errors));;
              run_step_promise_first fuel terminated
        else mthrow "Could not finish promise-first within the size of the fuel".

    (** The type of final promising state return by run *)
    Definition final := { x : t | terminated prom term x }.

    Definition make_final (p : t) := exist (terminated prom term) p.


    (** Convert a final promising state to a generic final state *)
    Program Definition to_final_archState (f : final) :
        {s & archState.is_terminated term s} :=
      existT (to_archState prom f) _.
    Solve All Obligations with
      hauto unfold:terminated unfold:archState.is_terminated l:on db:vec, brefl.

    (** Computational evaluate all the possible allowed final states according
        to the promising model prom starting from st *)
    Fixpoint run (fuel : nat) : Exec.t t string final :=
      st ← mGet;
      if decide $ terminated prom term st is left pt then mret (make_final st pt)
      else
        if fuel is S fuel then
          run_step (S fuel);;
          run fuel
        else mthrow "Could not finish running within the size of the fuel".

    (** Computational evaluate all the possible allowed final states according
        to the promising model prom starting from st *)
    Fixpoint run_promise_first (fuel : nat) : Exec.t t string final :=
      st ← mGet;
      if decide $ terminated prom term st is left pt then mret (make_final st pt)
      else
        if fuel is S fuel then
          run_step_promise_first (S fuel);;
          run_promise_first fuel

    (** Computational evaluate all the possible allowed final states according
        to the promising model prom starting from st
        with promise-first optimization *)
    Definition run_promise_first (fuel : nat) : Exec.t t string final :=
      st ← mGet;
      (* Execute promise-first *)
      run_step_promise_first fuel;;

      if decide $ terminated prom term st is left pt then mret (make_final st pt)
      else
        if fuel is S fuel then
          run_step (S fuel);;
          run fuel
        else mthrow "Could not finish running within the size of the fuel".
    End CPS.
    Arguments to_final_archState {_ _ _}.
  End CPState.

  (** Create a computational model from an ISA model and promising model *)
  Definition Promising_to_Modelc (isem : iMon ()) (prom : BasicExecutablePM)
      (fuel : nat) : archModel.c ∅ :=
    fun n term (initMs : archState n) =>
      PState.from_archState prom initMs |>
      archModel.Res.from_exec
        $ CPState.to_final_archState
        <$> CPState.run isem prom term fuel.

  (** Create a computational model from an ISA model and promising model
      with promise-free optimization *)
  Definition Promising_to_Modelc_promise_first (isem : iMon ()) (prom : BasicExecutablePM)
      (fuel : nat) : archModel.c ∅ :=
    fun n term (initMs : archState n) =>
      PState.from_archState prom initMs |>
      archModel.Res.from_exec
        $ CPState.to_final_archState
        <$> CPState.run_promise_first isem prom term fuel.

    (* TODO state some soundness lemma between Promising_to_Modelnc and
        Promising_Modelc *)

End GenPromising.

Module Type GenPromisingT (IWA : InterfaceWithArch) (TM : TermModelsT IWA).
  Include GenPromising IWA TM.
End GenPromisingT.
