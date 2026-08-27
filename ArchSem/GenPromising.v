(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
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




(* to be imported *)
Module GenPromising (Arch : Arch) (Inter : InterfaceT Arch)
    (TM : TermModelsT Arch Inter).
  Import Arch.
  Import Inter.
  Import TM.

  (** A message in the promising model memory. [size] is a field (not a
      parameter) so that [Msg.t] is a plain [Set] and all messages
      can live in one list. *)
  Module Msg.
    Record t : Set :=
      make {
          tid : nat;
          addr : address;
          size : N;
          val : bv (8 * size);
        }.

    #[export] Instance eq_dec : EqDecision t.
    Proof. intros [] []. decide_eq. Defined.

    (** Decides if a msg overlaps with an address range *)
    Definition overlap (a : address) (sz : N) (msg : t) :=
      addr_overlap a sz msg.(addr) msg.(size).
    #[export] Typeclasses Transparent overlap.

    (** Extracts a byte from a message *)
    Definition read_byte (a : address) (msg : t) : option (bv 8) :=
      if decide (addr_in_range (addr msg) (size msg) a) then
        let offset := Z.to_N (bv_unsigned a - bv_unsigned (addr msg)) in
        Some (bv_get_byte 8 offset (val msg))
      else None.
  End Msg.
  Export (hints) Msg.


  (** This module define the representation of a promising model memory as a
      sequence of events.

      The sequence is 1 indexed so that timestamp 0 represent memory as it was
      initially.

      The current implementation is a list in reverse order but that may change
      *)
  Module PromMemory. (* namespace *)
  Section PM.

    Context {ev : Type}.

    (* I'm using a simple list representation. The most recent write is the head
       of the list. *)
    Definition t := list ev.
    #[export] Typeclasses Transparent t.

    (** Definition of the memory numbering. So it can be used with the !!
        operator *)
    #[export] Instance lookup_inst : Lookup nat ev t := {
        lookup k mem :=
          if k =? 0%nat then None
          else
            let len := List.length mem in
            if (k <=? len)%nat then List.nth_error mem (len - k)%nat else None
      }.

    (** Cuts the memory to only what exists before the timestamp, included.
        The timestamp can still be computed the same way. *)
    Definition cut_before (v : nat) (mem : t) : t :=
      let len := List.length mem in
      (* Here I'm using the m - n = 0 when n > m behavior *)
      drop (len - v) mem.

    (** Cuts the memory to only what exists after the timestamp, excluded.
        Beware of timestamp computation. If you need the original timestamps,
        use cut_after_timestamps *)
    Definition cut_after (v : nat) (mem : t) : t :=
      let len := List.length mem in
      take (len - v) mem.

    (** Cuts the memory to only what exists after the timestamp, excluded.
        Provide the original timestamps as a additional value. *)
    Fixpoint attach_timestamps (mem : t) : list (ev * nat) :=
      match mem with
      | [] => []
      | h :: q =>
        (h, List.length mem) :: attach_timestamps q
      end.

    Definition cut_after_with_timestamps (v : nat) (mem : t) : list (ev * nat) :=
      take (length mem - v) (attach_timestamps mem).

    (** Promises an event and adds it at the end of memory *)
    Definition promise (e : ev) : Exec.t t string nat :=
      mSet (cons e);;
      mem ← mGet;
      mret (List.length mem).

    (** Returns a view among a promise set that correspond to an event. The
        oldest matching timestamp is taken. This is because it can be proven
        that fulfilling a more recent timestamp will make the previous promises
        unfulfillable, and thus the corresponding executions would be
        discarded. TODO prove it. *)
    Definition fulfill `{EqDecision ev} (e : ev) (prom : list nat) (mem : t) :
        option nat :=
      prom |> filter (λ t, mem !! t = Some e)
      |> reverse
      |> head.

    (** For model that have events other than [Msg.t], this need to extract the
        [Msg.t] for the generic reading functions to work *)
    Context (get_msg : ev → option Msg.t).
    Section Reading.
      Context (addr : address) (size : N) (imem : memoryMap) .

      (** Reads [size] bytes starting at [addr] from the memory state at
          timestamp [tread]. Assumes that the memory [mem] has size [tread] (the
          more recent events have been cut off). Returns each byte paired with
          its actual write-timestamp [twrite]. Throws if any byte is unmapped.
          *)
      Fixpoint read_from_aux (mem : t) (tread : nat) :
          result string (list (bv 8 * nat)) :=
        match tread with
        | 0%nat =>
            othrow ("Memory read of unmapped bytes at " ++ pretty addr)%string $
              mem_lookup_bytes addr size imem |$> map (.,0%nat)
        | S ntread =>
            if mem is ev :: nmem then
              if get_msg ev is Some msg then
                if decide (msg.(Msg.addr) = addr ∧ msg.(Msg.size) = size) then
                  msg.(Msg.val) |> bv_to_bytes 8 |> map (.,tread) |> mret
                else
                  prev ← read_from_aux nmem ntread;
                  if decide (Msg.overlap addr size msg) then
                    imap (λ idx byte_time,
                        if Msg.read_byte (addr `+Z` Z.of_nat idx)%bv msg
                             is Some byte
                        then (byte, tread)
                        else byte_time) prev |> mret
                  else mret prev
              else read_from_aux nmem ntread
            else mthrow "read_from_aux_invalid_precondition"
        end.

      (** Reads [size] bytes starting at [addr] from the memory state at
          timestamp [tread]. Returns each byte paired with its actual
          write-timestamp [twrite]. Throws if any byte is unmapped. *)
      Definition read_from (mem : t) (tread : nat) :
          result string (list (bv 8 * nat)) :=
        let snap := cut_before tread mem in
        read_from_aux snap tread.

      (** Reads [size] bytes starting at [addr] from the memory state and return
          all possible values observable between [tmin] and [tmax] included.
          This function assumes the length of [mem] is precisely [tmax] and that
          [tmin ≤ tmax]. For each possible read, returns each byte paired with
          its actual write-timestamp [twrite]. Throws if any byte is unmapped. *)
      Fixpoint read_all_aux (mem : t) (tmin tmax: nat) :
          result string (list (list (bv 8 * nat))) :=
        if tmax =? tmin then
          read_from_aux mem tmin |$> (.::[])
        else
          if tmax is S ntmax then
            if mem is ev :: nmem then
              prev ← read_all_aux nmem tmin ntmax;
              if get_msg ev is Some msg then
                if decide (msg.(Msg.addr) = addr ∧ msg.(Msg.size) = size) then
                  mret ((msg.(Msg.val) |> bv_to_bytes 8 |> map (.,tmax)) :: prev)
                else
                  if decide (Msg.overlap addr size msg) then
                    if prev is prevm :: _ then
                      let newm :=
                        imap (λ idx byte_time,
                            if Msg.read_byte (addr `+Z` Z.of_nat idx)%bv msg
                                 is Some byte
                            then (byte, tmax)
                            else byte_time) prevm
                      in mret (newm :: prev)
                    else mthrow "read_all_aux: returned empty list"
                  else mret prev
              else mret prev
            else mthrow "read_all_aux: invalid precondition"
          else mthrow "read_all_aux: invalid precondition".

      (** Reads [size] bytes starting at [addr] from the memory state and
          returns all possible values observable after [tmin] included. For each
          possible read, returns each byte paired with its actual
          write-timestamp [twrite]. Throws if any byte is unmapped. *)
      Definition read_all (mem : t) (tmin : nat) :
          result string (list (list (bv 8 * nat))) :=
        read_all_aux mem tmin (length mem).

      (** Read [size] byte from initial memory. Throws if any byte is unmapped
          or was modified *)
      Definition read_initial (mem : t) : result string (list (bv 8)) :=
        bytes ← read_from_aux mem (length mem);
        for (byte, time) in bytes do
          if time =? 0%nat then mret byte else mthrow "Modified memory"
        end.
    End Reading.

    (** Reads a byte at timestamp [time]. *)
    Definition read_byte (addr : address) (imem : memoryMap) (mem : t)
        (time : nat) : result string (bv 8) :=
      bytes ← read_from addr 1 imem mem time;
      othrow "read_byte: internal error" $ List.head (bytes.*1).

    (** Reads an 8-byte word at timestamp [time]. *)
    Definition read_word (addr : address) (imem : memoryMap) (mem : t)
        (time : nat) : result string (bv 64) :=
      bytes ← read_from addr 8 imem mem time;
      mret (bv_of_bytes 64 bytes.*1).


    (** Transforms an initial [memoryMap] and a promising memory history back to
        a [memoryMap] *)
    Definition to_memMap (imem : memoryMap) (mem : t) : memoryMap :=
      foldr (λ ev mm,
          if get_msg ev is Some msg
          then mem_insert_bv (Msg.addr msg) (Msg.val msg) mm
          else mm) imem mem.

    (** Checks that no overlapping writes have been made by any
        thread other than [tid] in between [tread] and [twrite] *)
    Definition exclusive (tid : nat) (addr : address) (size : N)
        (tread : nat) (twrite : nat) (mem : t) : Prop :=
      ∀ ev ∈ (cut_after tread (cut_before (twrite - 1)%nat mem)),
      if get_msg ev is Some msg
      then Msg.overlap addr size msg → Msg.tid msg = tid
      else true.
    #[export] Instance exclusive_dec tid addr size tread twrite mem :
      Decision (exclusive tid addr size tread twrite mem).
    Proof. unfold exclusive. apply _. Defined.

  End PM.
  Arguments t : clear implicits.
  End PromMemory.
  #[export] Typeclasses Transparent PromMemory.t.

  (* Partial Promising State. The state over which the semantics of individual
     instruction is defined *)
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


  (* Namespace *)
  Module Promising.

  (** This structure defines a promising model that can share common
      infrastructure define in this file. This structure allows to define 4
      models:
      - The non-certified non-executable version where any promises can be made
        as long as they are all fulfilled by the end
      - The certified non-executable version where promises can only be made if
        there is a sequential trace that lead to that promise being fulfilled.
      - The direct executable model which explores all interleaving of promising
        and instruction steps
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
      tState_init : (* tid *) nat → memoryMap → registerMap →
                    result string tState;
      (** Get a register map out of a thread state to compute a final state.
          This is only used once per execution *)
      tState_regs : tState → registerMap;
      (** Get the PC out of a thread state. This is on the hot path: it is
          called at every step to test the termination condition *)
      tState_pc : tState → option (reg_type pc_reg);
      (** [tState_pc] must agree with [tState_regs] *)
      tState_pc_spec :
        ∀ ts, tState_pc ts = reg_lookup pc_reg (tState_regs ts);
      (** Check if a thread state has no pending promises, which means that it
          can be explained with the current memory state *)
      tState_nopromises : tState → bool;
      (** Intra instruction state, reset after each instruction *)
      iis : Type;
      iis_init : iis;
      (** The type of memory event, any communication between threads must go here *)
      mEvent : Type;
      mEvent_eq_dec : EqDecision mEvent;
      (** Give the tid that initiated that event *)
      mEvent_tid : mEvent → nat;
      (** Filter executable promise candidates from a single enumeration run.
          The memory does not yet contain the candidates being selected. *)
      filter_promises : (* num of threads *) nat → (* tid *) nat →
                        PromMemory.t mEvent → list mEvent → list mEvent;
      (** The address space this model is built against, we expect non-secure
          for Arm here *)
      address_space : addr_space;
      (** The handler for instruction effects, applies the effect of a single
          outcome to the thread state. If the outcome need one or more event to
          be added to memory,it adds them and return the view of those events in
          the option, otherwise it returns [None] *)
      handle_outcome : (* num of threads *) nat → (* tid *) nat →
                  (* initial memory *) memoryMap →
                  ∀ out : outcome,
                  Exec.t (PPState.t tState mEvent iis) string
                         (eff_ret out * option nat);
      (** Updates a thread state after emission of a promise. This is called
          once for every thread of the machine, with [tid] being the tid of the
          thread being updated; the thread that made the promise is [mEvent_tid]
          of the event. The new promise has already been added to the memory
          when calling that function. *)
      emit_promise : (* updated thread tid *) nat → memoryMap →
                     PromMemory.t mEvent → mEvent → tState →
                     result string tState;
      (** Hook for extra UB checks to be done before returning a final state,
          e.g. BBM checks. Any returned string is an error, [[]] is success. *)
      check_valid_end : (* tid *) nat → memoryMap → tState →
                             PromMemory.t mEvent → list string;
      (** Computes the final memory after a certain promising history *)
      memory_snapshot : memoryMap → PromMemory.t mEvent → memoryMap;
    }.
  #[global] Arguments Model : clear implicits.
  End Promising.

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

      (** Check if a thread state has reached one of its breakpoints *)
      Definition terminated_ts (bps : list (reg_type pc_reg)) (ts : tState) :=
        pc_terminated bps (prom.(tState_pc) ts).

      (** Check if a thread has finished according to term *)
      Definition terminated_tid (term : terminationCondition n) (ps : t)
        (tid : fin n) := ps |> tstate tid |> terminated_ts (term !!! tid).

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
        let handler out :=
          prom.(handle_outcome) n tid (st.(initmem)) out |$> fst in
        Exec.liftSt (PState_PPState tid) (cinterp handler isem).

      (** Emit a promise, updating every thread state. The thread that made
          the promise is [prom.(mEvent_tid) event] *)
      Definition promise (event : mEvent) (st : t) : result string t :=
        let st := set events (event ::.) st in
        nts ←
          vimapM
            (λ tid ts,
               prom.(emit_promise) tid st.(initmem) st.(events) event ts)
            st.(tstates);
        mret (setv tstates nts st).

      (** The inductive stepping relation of the non-certified promising model
          (non_executable) *)
      Inductive non_cert_step (ps : t) : (t) -> Prop :=
      | SRun (tid : fin n) (ps' : t) :
        (ps', ()) ∈ (run_tid tid ps) → non_cert_step ps ps'
      | SPromise (event : mEvent) (ps' : t) :
        prom.(mEvent_tid) event < n →
        promise event ps = Ok ps' →
        non_cert_step ps ps'.

      (** Create an initial promising state from a generic machine state *)
      Definition from_archState (ms: archState n) : result string t :=
        nts ←
          vimapM
            (λ tid rm, prom.(tState_init) tid ms.(archState.memory) rm)
            ms.(archState.regs);
        mret {|tstates := nts;
               initmem := ms.(archState.memory);
               events := []|}.

      (** Convert a promising state to a generic machine state.
          This is a lossy conversion *)
      Definition to_archState (ps: t) : archState n :=
        {|archState.regs := vmap (prom.(tState_regs)) ps.(tstates);
          archState.memory := prom.(memory_snapshot) ps.(initmem) ps.(events);
          archState.address_space := prom.(address_space) |}.

      Lemma terminated_ts_regs (bps : list (reg_type pc_reg)) (ts : tState) :
        terminated_ts bps ts = regs_terminated bps (prom.(tState_regs) ts).
      Proof using.
        unfold terminated_ts, regs_terminated.
        by rewrite prom.(tState_pc_spec).
      Qed.

      Lemma terminated_tid_archState (term : terminationCondition n) (ps : t)
          (tid : fin n) :
        terminated_tid term ps tid =
          regs_terminated (term !!! tid)
            ((to_archState ps).(archState.regs) !!! tid).
      Proof using.
        unfold terminated_tid, to_archState.
        cbn.
        rewrite vlookup_map.
        apply terminated_ts_regs.
      Qed.

      Lemma terminated_to_archState (term : terminationCondition n) (ps : t) :
        terminated term ps → archState.is_terminated term (to_archState ps).
      Proof using.
        unfold terminated, archState.is_terminated.
        setoid_rewrite <- terminated_tid_archState.
        by bool_unfold.
      Qed.
    End PSProm.


  End PState.

  (** Create a non-computational non-certified model from an ISA model and
      promising model

      This model will create a lot of spurious error but is only intended as a
      proof tool. The goal is that any non-error trace of that model can be
      reproduced in the certified promising model. *)
  Definition Promising_to_Modelnc (prom : Promising.Model) (isem : iMon ()) :
      archModel.nc ∅ :=
    λ n term (initMs : archState n),
      {[ mr : archModel.res ∅ n term |
         match PState.from_archState prom initMs with
         | Error s => mr = archModel.Res.Error s
         | Ok initPs =>
             match mr with
             | archModel.Res.FinalState fs _ =>
                 ∃ finPs, rtc (PState.non_cert_step isem prom) initPs finPs ∧
                            PState.to_archState prom finPs = fs ∧
                            PState.nopromises prom finPs ∧
                            PState.check_valid_end prom finPs = []
             | archModel.Res.Error s =>
                 ∃ finPs,
                  rtc (PState.non_cert_step isem prom) initPs finPs ∧
                    ((∃ tid, Error s ∈ PState.run_tid isem prom tid finPs)
                      ∨
                     (∃ ev,
                         (* This is way too trigger happy *)
                         prom.(Promising.mEvent_tid) ev < n →
                         PState.promise prom ev finPs = Error s)
                      ∨
                     (PState.terminated prom term finPs ∧
                      PState.nopromises prom finPs ∧
                      s ∈ PState.check_valid_end prom finPs))
             | _ => False
             end
         end]}.

  (** Computational promising state. Right now it the same type as PState.t but
      with more methods *)
  Module CPState.
    Import Promising.
    Include PState.
    Section CPS.
    Context (isem : iMon ()).
    Context (prom : Model).
    Context {n : nat}.
    Local Notation tState := (tState prom).
    Local Notation mEvent := (mEvent prom).
    Local Notation iis := (iis prom).
    Local Notation t := (t tState mEvent n).

    Let mEvent_eq_dec := prom.(mEvent_eq_dec).
    Local Existing Instance mEvent_eq_dec.

    Section Steps.
    Context (term : terminationCondition n).

    (** The type of final promising state return by run *)
    Definition final := { x : t | terminated prom term x }.

    Definition make_final (p : t) := exist (terminated prom term) p.

    Definition validate_final (st : t) : Exec.t t string unit :=
      guard_discard $ nopromises prom st;;
      let errs := check_valid_end prom st in
      if errs is [] then
        mret ()
      else
        err ← mchoosel errs;
        mthrow err.

    (** Convert a final promising state to a generic final state *)
    Definition to_final_archState (f : final) :
        {s & archState.is_terminated term s} :=
      existT (to_archState prom (proj1_sig f))
        (terminated_to_archState prom term (proj1_sig f) (proj2_sig f)).


    Section EnumerateResult.
      Context (tid : fin n) (initmem : memoryMap).

      Definition run_outcome_with_promise (base : nat) (out : outcome) :
          Exec.t (list mEvent * PPState.t tState mEvent iis) string
                 (eff_ret out) :=
        '(res, vpre_opt) ←
          Exec.liftSt snd $ prom.(handle_outcome) n tid initmem out;
        if vpre_opt is Some vpre then
          if decide (vpre ≤ base)%nat then
            mem ← mget (PPState.mem ∘ snd);
            (* Take all promises after base (made by that outcome) and add them
               to the list of possible new promises *)
            mset fst (take (length mem - base) mem ++.);;
            mret res
          else mret res
        else
          mret res.

      (** Runs a thread sequentially to termination, collecting all promises
          that had to be made. Returns [false] if it ran out of fuel during
          exploration. [fuel] is the maximum number of instructions to be run.*)
      Fixpoint run_to_termination (fuel : nat) (base : nat) :
          Exec.t (list mEvent * PPState.t tState mEvent iis) string bool :=
        ts ← mget (PPState.state ∘ snd);
        if terminated_ts prom (term !!! tid) ts then
          mret true
        else
          match fuel with
          | 0%nat => mret false
          | S fuel =>
              msetv (PPState.iis ∘ snd) prom.(iis_init);;
              let handler := run_outcome_with_promise base in
              cinterp handler isem;;
              run_to_termination fuel base
          end.

      Record EnumerationResult :=
        {
          promises : list mEvent;
          final_states : list tState;
          errors : list string;
          out_of_fuel : bool
        }.

      (** Enumerate all possible executions for a thread in a given memory.

          [fuel] Is the maximum number of instructions to be run for each
          thread. *)
      Definition enumerate_results (fuel : nat) (ts : tState)
          (mem : PromMemory.t mEvent) : EnumerationResult :=
        let base := List.length mem in
        let res :=
          run_to_termination fuel base
            ([], PPState.Make ts mem prom.(iis_init))
        in
        let success_states := Exec.success_state_list res in
        let out_of_fuel := bool_decide (∃ r ∈ (Exec.results res).*2, ¬ (r : bool)) in
        let promises :=
          List.concat ((success_states.*1) ++ (Exec.errors res).*1.*1)
            |> remove_dups in
        let promises := prom.(filter_promises) n tid mem promises in
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
      let (promises, _, _, out_of_fuel) :=
        enumerate_results tid (initmem st) fuel (tstate tid st) (events st)
      in
      if out_of_fuel then
        b ← mchoosef bool;
        if (b : bool) then mthrow "out of fuel" else mchoosel promises
      else mchoosel promises.

    (** Take any promising step for that tid and promise it *)
    Definition cpromise_tid (fuel : nat) (tid : fin n) : Exec.t t string () :=
      st ← mGet;
      ev ← mlift (promise_select_tid fuel st tid);
      nst ← mlift (promise prom ev st);
      mSetv nst.

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

    (** A single transition of the direct promising model: either the current
        state is final, or any certified promise or instruction step is taken.

        [fuel] is the maximum number of instruction to run in each thread to
        find a certified promise.

        Returning [None] means it was a non-final step *)
    Definition run_transition (fuel : nat) :
        Exec.t t string (option {s & archState.is_terminated term s}) :=
      st ← mGet;
      if decide $ terminated prom term st is left pt then
        validate_final st;;
        mret (Some (to_final_archState (make_final st pt)))
      else
        run_step fuel;;
        mret None.

    (** A single transition of the promise-first promising model.

        It explore executions of all threads collecting promises and either
        choose one of them, or, if it's possible to reach a final state without
        making any new promises, return that final state.

        [fuel] is the maximum number of instruction to be explored for each
        thread.

        Returning [None] means it was a non-final step *)
    Definition run_transition_promise_first (fuel : nat) :
        Exec.t t string (option {s & archState.is_terminated term s}) :=
      st ← mGet;
      (* Find out next possible promises or terminating states for each thread *)
      let execution_results :=
        vmap (λ '(tid, ts),
            enumerate_results tid (initmem st) fuel ts (events st)
          ) (venumerate (tstates st)) in
      opt ← mchoosel (seq 0 4);
      match opt : nat with
      | 0 =>
        tid ← mchoosef (fin n);
        next_ev ← mchoosel (execution_results !!! tid).(promises);
        nst ← mlift (promise prom next_ev st);
        mSetv nst;;
        mret None
      | 1 =>
        (* Compute cartesian products of the possible thread states *)
        tstates ← mchoosel $ cprodn (vmap final_states execution_results);
        (* Lift them into full promising state *)
        let st := Make tstates st.(initmem) st.(events) in
        (* Discard the non-terminated ones *)
        term_proof ← guard_discard $ terminated prom term st;
        validate_final st;;
        mret (Some (to_final_archState (make_final st term_proof)))
      | 2 =>
        let errs := List.concat (vmap errors execution_results) in
        err ← mchoosel errs;
        mthrow err
      | _ =>
        if bool_decide (∃ x ∈ map out_of_fuel execution_results, (x : bool)) then
          mthrow "Promise first: out of fuel in enumeration"
        else mdiscard
      end.
    End Steps.

    (** The promising model as an operational model. Each transition is either a
        promise step or a full instruction step of any thread, which means all
        the interleavings of promises and instructions are explored.

        The required fuel is:
          (# of promises) + # of instructions of all threads + 1 *)
    Definition opmodel : opModel n :=
      let init _ initSt := from_archState prom initSt in
      let step term _ fuel := run_transition term fuel in
      opModel.Make n t init step.

    (** The promise-first promising model as an operational model.

        Transitions are just certified promises until the last transition that
        run all threads instructions to the end in one step.

        The required fuel is (# of promises) + max(# of instructions or 1) *)
    Definition opmodel_pf : opModel n :=
      let init _ initSt := from_archState prom initSt in
      let step term _ fuel := run_transition_promise_first term fuel in
      opModel.Make n t init step.

    End CPS.
    Arguments to_final_archState {_ _ _}.
  End CPState.

  (** Create a computational model from an ISA model and promising model.

      [fuel] needed is one per promise and per instruction of any thread + one
      for the final transition *)
  Definition Promising_to_Modelc (prom : Promising.Model) (isem : iMon ())
      (fuel : nat) : archModel.c ∅ :=
    opModel.to_archModel (@CPState.opmodel isem prom) fuel.

  (** Create a computational model from an ISA model and promising model, using
      the promise-first optimisation *)
  Definition Promising_to_Modelc_pf (prom : Promising.Model) (isem : iMon ())
      (fuel : nat) : archModel.c ∅ :=
    opModel.to_archModel (@CPState.opmodel_pf isem prom) fuel.

End GenPromising.

Module Type GenPromisingT (Arch : Arch) (Inter : InterfaceT Arch)
    (TM : TermModelsT Arch Inter).
  Include GenPromising Arch Inter TM.
End GenPromisingT.
