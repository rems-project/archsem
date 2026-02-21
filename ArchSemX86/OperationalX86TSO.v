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

From ASCommon Require Import Options.
From ASCommon Require Import Common Exec FMon.

From stdpp Require Import base options.

Require Import X86Inst.

(** this is an implementation of the x86-TSO operational concurrency model,
    as defined in https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.pdf *)



(* TSO Model Types*)

Record addr_val : Type := {
    addr: address;
    size: N; (* IN BYTES *)
    val: bv (8 * size)
}.

(* archState + extra fields (buffer and lock)*)
Record machine_state (threads: nat) := {
    Reg : vec registerMap threads; (* Registers for each thread *)
    Mem : memoryMap;
    Buffer : vec (list addr_val) threads; (* Gives the store buffer for each thread. Each buffer is a list of address-value tuples, oldest first *)
    Lock : option (fin threads); (* Global machine lock, indicating when some thread has exclusive access to memory *)
    MemWritten : gset address; (* Set of memory addresses that have been written to *)
    TermThreads : vec bool threads;
    }.

Section Model.
    Context (threads: nat).

    Notation mstate_threads := (machine_state threads).



    (* REG FUNCTIONS *)

    Definition read_reg (tid : fin threads) (reg : reg) (state : mstate_threads) : option (reg_type reg) :=
        let regMap := (Reg threads state !!! tid) in
            dmap_lookup reg regMap.

    Definition write_reg (tid : fin threads) (reg : reg) (val : reg_type reg) (state : mstate_threads)
        : mstate_threads :=
            set (lookup_total tid ∘ Reg threads) (dmap_insert reg val) state.



    (* BUFFER FUNCTIONS *)

    Definition no_pending (x : address) (tid : fin threads) (state : mstate_threads) : bool :=
        let buffer := Buffer threads state !!! tid in
            bool_decide (∀ av ∈ buffer, addr av ≠ x).

    Definition buffer_empty (tid : fin threads) (m : mstate_threads) : bool :=
        match Buffer threads m !!! tid with
        | x :: xs => false
        | [] => true
        end.

    Definition all_buffers_empty (state: mstate_threads): bool :=
        bool_decide (∀ t : fin threads, buffer_empty t state).

    Fixpoint read_from_write_buffer_inner (rev_buffer : list addr_val) (goal_addr: address) (goal_size : N)
        : option (bv (8 * goal_size)) :=
            (* Allow a direct match to be store-forwarded 
            if it is the most recent write to all relevant addresses.
            Underapproximation of store buffering.
            Reverse buffer so that we see most recent writes first *)
            match rev_buffer with
            | x :: xs =>
                let goal_range : gset address := list_to_set (addr_range goal_addr goal_size) in
                let x_range : gset address := list_to_set (addr_range (addr x) (size x)) in
                (* If we have a direct match, then perform store forwarding *)
                if bool_decide (goal_range = x_range) then
                    let unsigned_val := bv_unsigned (val x) in
                    let return_val := Z_to_bv (8 * goal_size) unsigned_val in
                    Some return_val
                (* If we don't have a direct match,
                but some of the desired addresses have been written to,
                then prohibit store forwarding *)
                else if bool_decide (goal_range ∩ x_range ≠ ∅) then
                    None
                else read_from_write_buffer_inner xs goal_addr goal_size
            | _ => None
            end. 

    Definition read_from_write_buffer (tid : fin threads) (addr : address) (size : N) (state : mstate_threads)
        : option (bv (8 * size)) :=
            (* Reverse buffer so that we see most recent writes first *)
            let rev_buffer := rev (Buffer threads state !!! tid) in
            read_from_write_buffer_inner rev_buffer addr size.

    Fixpoint add_to_mem_written (addr : address) (size : nat)
        : Exec.t mstate_threads string unit :=
        match size with
        | S size =>
            (* Add addr to the set of addresses that have been written to in memory*)
            mset (MemWritten threads) (.∪{[addr]});;
            (* Move on to the next byte (if it exists)*)
            add_to_mem_written (addr `+Z` 1)%bv size
        | _ => mret ()
        end.

    Definition add_to_write_buffer (tid : fin threads) (addr : address) (size : N) (val : bv (8 * size))
    (state : mstate_threads) : mstate_threads :=
        set (lookup_total tid ∘ Buffer threads)
            (fun curr_list:
                list addr_val => (curr_list ++ [{|
                    addr := addr;
                    size := size;
                    val := val
                |}])%list)
            state.



    (* MEM FUNCTIONS *)

    Definition mem_addr_modified (addr : address) (size : N) (state : mstate_threads) : bool :=
        (* Returns true if address modified in memory or written to in a store buffer *)
        bool_decide (∃ a ∈ addr_range addr size, a ∈ MemWritten threads state).

    Definition write_mem (addr : address) (size : N) (val : bv (8 * size))
        : Exec.t mstate_threads string unit :=
            (* Check if memory address is mapped*)
            opt ← mget (fun state => mem_lookup addr size (Mem threads state));
            guard_or "Memory isn't mapped to write" (is_Some opt);;
            (* Write to memory *)
            mset (Mem threads) (mem_insert addr size val).



    (* BUFFER AND MEM FUNCTIONS *)

    Definition read_mem_with_store_forwarding (tid : fin threads) (addr : address) (size : N)
        : Exec.t mstate_threads string (bv (8 * size)) :=
            (* Attempt store forwarding *)
            opt ← mget (read_from_write_buffer tid addr size);
            if opt is Some read then
                mret read
            else
                (* Attempt memory read and return read value *)
                opt ← mget (fun state => mem_lookup addr size (Mem threads state));
                read ← othrow ("Memory not found at " ++ pretty addr)%string opt;
                mret read.

    Fixpoint write_buffer_to_mem (buffer: list addr_val) (tid: fin threads)
    : Exec.t mstate_threads string unit :=
        match buffer with
        | [] => mret ()
        | h :: t =>
            write_mem (addr h) (size h) (val h);;
            write_buffer_to_mem t tid
        end.

    Definition empty_write_buffer (tid : fin threads) : Exec.t mstate_threads string unit :=
        buffer ← mget (fun state => (Buffer threads state) !!! tid);
        (* Write all buffer contents to memory *)
        write_buffer_to_mem buffer tid;;
        (* Empty buffer *)
        mset (lookup_total tid ∘ Buffer threads) (fun curr_buffer => []).



    (* LOCK FUNCTIONS*)

    Definition blocked (tid : fin threads) (m : mstate_threads) : bool :=
        let lock := Lock threads m in
            if lock is Some tid' then bool_decide (tid ≠ tid')
            else false.

    Definition thread_has_lock (tid : fin threads) (m : mstate_threads) : bool :=
        let lock := Lock threads m in
            if lock is Some tid' then bool_decide (tid = tid')
            else false.

    Definition acquire_lock (tid : fin threads) (state : mstate_threads) : mstate_threads :=
        set (Lock threads) (fun curr_lock => Some tid) state.

    Definition acquire_lock_conditional (tid : fin threads) : Exec.t mstate_threads string unit :=
        (* Ensure thread can acquire lock: a thread (including thread tid) might already have the lock*)
        lock ← mget (Lock threads);
        guard_discard (lock = None);;
        (* Ensure thread can acquire lock: store buffer might not be empty.
        Hence eagerly empty buffer. Can do this as no other thread has lock *)
        empty_write_buffer tid;;
        (* Acquire lock *)
        mSet (acquire_lock tid).

    Definition release_lock (tid : fin threads) (state : mstate_threads) : mstate_threads :=
        set (Lock threads) (fun curr_lock => None) state.

    Definition release_lock_conditional (tid : fin threads) : Exec.t mstate_threads string unit :=
        (* Make sure we have the lock before releasing it *)
        state ← mGet;
        guard_discard (thread_has_lock tid state);;
        (* Empty write buffer (eager) (other requirement for releasing lock) *)
        empty_write_buffer tid;;
        (* Release lock *)
        mSet (release_lock tid).



    (* OUTCOMES *)

    Section RunOutcome.
        Context (tid : fin threads).

        Notation mstate_threads := (machine_state threads).

        Equations run_outcome (call : outcome) : Exec.t mstate_threads string (eff_ret call) :=
            | RegRead reg racc =>
                opt ← mget (read_reg tid reg);
                othrow ("Register " ++ pretty reg ++ " not found")%string opt
            | RegWrite reg racc val =>
                opt ← mget (read_reg tid reg);
                guard_or ("Writing register " ++ pretty reg ++ " not in initial state")%string (is_Some opt);;
                mSet (write_reg tid reg val)
            | MemRead (MemReq.make macc addr () size 0) =>
                (* Split memory read by access type*)
                if is_ifetch macc then
                    (* Fail ifetch if the location we are attempting to fetch has been modified *)
                    modified ← mget (mem_addr_modified addr size);
                    guard_or "IFetch reading from modified memory" (negb(is_ifetch macc && modified));;
                    (* Read from memory *)
                    opt ← mget (fun state => mem_lookup addr size (Mem threads state));
                    read ← othrow ("Memory not found at " ++ pretty addr)%string opt;
                    mret (Ok (read, bv_0 _))
                else if is_explicit macc then
                    (* Can't explicitly read from memory if we are blocked (some other thread has the lock) *)
                    is_blocked ← mget (blocked tid);
                    guard_discard (negb is_blocked);;
                    (* Acquire lock if needed*)
                    (if is_atomic_rmw macc then
                        acquire_lock_conditional tid
                    else
                        mret ());;
                    (* Attempt store forwarding. Read from memory if store forwarding not possible *)
                    read ← read_mem_with_store_forwarding tid addr size;
                    mret (Ok (read, bv_0 _))
                else
                    mthrow "Memory access type not supported"
            | MemRead _ => mthrow "Unsupported MemRead"
            | MemWrite (MemReq.make macc addr () size 0) val _ =>
                (* Add location to set of written memory addresses *)
                add_to_mem_written addr (N.to_nat size);;
                (* Add write to write buffer *)
                mSet (add_to_write_buffer tid addr size val);;
                (* Handle atomic case (release lock) *)
                (if is_explicit macc && is_atomic_rmw macc then
                    release_lock_conditional tid
                else 
                    mret ());;
                mret (Ok ())
            | MemWrite _ _ _ => mthrow "Unsupported MemWrite"
            | Barrier Barrier_LFENCE => mret ()
            | Barrier _ =>
                (* Write buffer (of thread tid) must be emptied before this instruction can complete.
                Eager execution empties the buffer so that the instruction can complete. *)
                is_blocked ← mget (blocked tid);
                if (is_blocked : bool) then
                    mdiscard
                else
                    empty_write_buffer tid
            | GenericFail msg => mthrow msg
            | _ => mthrow "Unsupported outcome".
    End RunOutcome.

    Definition flush_one_item_buffer (tid : fin threads) : Exec.t mstate_threads string unit :=
        buffer ← mget (fun state : mstate_threads => (Buffer threads state) !!! tid);
        match buffer with
        | [] => mdiscard
        | h :: t =>
            (* Write first entry to memory *)
            write_mem (addr h) (size h) (val h);;
            (* Remove first entry from buffer *)
            mset (lookup_total tid ∘ Buffer threads) (fun curr_buffer => t)
        end.
End Model.

Definition from_archState {nth} (astate : archState nth) : machine_state nth :=
    {|
        Reg := astate.(archState.regs);
        Mem := astate.(archState.memory);
        Buffer := Vector.const [] nth;
        Lock := None;
        MemWritten := ∅;
        TermThreads := Vector.const false nth
    |}.

Definition to_archState {nth} (mstate : machine_state nth) : option (archState nth) :=
    if all_buffers_empty nth mstate && bool_decide (Lock nth mstate = None) then
        Some {|
            archState.regs := Reg nth mstate;
            archState.memory := Mem nth mstate;
            archState.address_space := ()
        |}
    else None.

Definition step {nth} (isem : iMon ()) (term : terminationCondition nth): Exec.t (machine_state nth) string () :=
    (* The transition taken is either a flush to memory or a run_outcome call *)

    (* Get tid *)
    state ← mGet;
    '(exist _ tid _ : {x : fin nth | ((TermThreads nth state !!! x) = false)}) ← mchoosef;

    (* Get step conditions *)
    let regMap := Reg nth state !!! tid in
    let termCondMet := term tid regMap in
    let bufferEmpty := buffer_empty nth tid state in

    (* Get transition type. Only consider transitions that are possible *)
    '(exist _ flush_transition _  : {x : bool | (bufferEmpty = true /\ termCondMet = false /\ x = false) \/ 
                                (termCondMet = true /\ bufferEmpty = false /\ x = true) \/
                                (bufferEmpty = false /\ termCondMet = false)}) ← mchoosef;

    if termCondMet && bufferEmpty then
        (* Terminate thread if there is no more work to do *)
        mset (lookup_total tid ∘ TermThreads nth) (fun x => true)
    else if flush_transition then
        (* Flush one item to memory *)
        flush_one_item_buffer nth tid
    else
        (* Run one outcome *)
        cinterp (run_outcome nth tid) isem.

Fixpoint run_to_term {nth} (fuel : nat) (isem : iMon ()) (term : terminationCondition nth)
    : Exec.t (machine_state nth) string {s : archState nth & archState.is_terminated term s} :=
        (* run until out of fuel or conditions met *)
        if fuel is S fuel then
            step isem term;;
            mstate ← mGet;
            astate ← mget to_archState;
            match astate with
            | Some astate  => 
                if decide (archState.is_terminated term astate) is left p then
                    mret (existT astate p)
                else run_to_term fuel isem term
            | None => run_to_term fuel isem term
            end
        else
            mthrow "Out of fuel".

(** Top-level one-threaded model function that takes fuel (guaranteed
    termination) and an instruction monad, and returns a computational set of
    all possible final states. *)
Definition x86_operational_modelc (fuel : nat) (isem : iMon ()) : (archModel.c ∅) :=
    λ n term (initSt: archState n),
    from_archState initSt
    |> archModel.Res.from_exec (run_to_term fuel isem term).
