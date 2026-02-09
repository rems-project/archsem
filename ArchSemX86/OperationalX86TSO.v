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
Record machine_state_t (threads: nat) := {
    Reg : vec registerMap threads; (* Registers for each thread *)
    Mem : memoryMap;
    Buffer : vec (list addr_val) threads; (* Gives the store buffer for each thread. Each buffer is a list of address-value tuples, most recent first *)
    Lock : option (Fin.t threads); (* Global machine lock, indicating when some thread has exclusive access to memory *)
    MemWritten : gset address; (* Set of memory addresses that have been written to *)
    TermThreads : vec bool threads;
    }.

Definition from_archState {n} (astate : archState n) : machine_state_t n :=
    {|
        Reg := astate.(archState.regs);
        Mem := astate.(archState.memory);
        Buffer := Vector.const [] n;
        Lock := None;
        MemWritten := ∅;
        TermThreads := Vector.const false n
    |}.

Definition to_archState {n} (mstate : machine_state_t n) : archState n :=
    {|
        archState.regs := Reg n mstate;
        archState.memory := Mem n mstate;
        archState.address_space := ()
    |}.

Section Model.
    Context (threads: nat).

    Notation machine_state := (machine_state_t threads).



    (* REG FUNCTIONS *)

    Definition read_reg (tid : Fin.t threads) (reg : reg) (state : machine_state) : option (reg_type reg) :=
        let regMap := (Reg threads state !!! tid) in
            dmap_lookup reg regMap.

    Definition write_reg (tid : Fin.t threads) (reg : reg) (val : reg_type reg) (state : machine_state)
        : machine_state :=
            set (lookup_total tid ∘ Reg threads) (dmap_insert reg val) state.



    (* BUFFER FUNCTIONS *)

    Definition no_pending (x : address) (tid : Fin.t threads) (state : machine_state) : bool :=
        let buffer := Buffer threads state !!! tid in
            bool_decide (∀ av ∈ buffer, addr av ≠ x).

    Definition buffer_empty (tid : Fin.t threads) (m : machine_state) : bool :=
        match Buffer threads m !!! tid with
        | x :: xs => false
        | [] => true
        end.

    Fixpoint read_from_write_buffer_inner (buffer : list addr_val) (u_addr: Z)
        (sz : N) (acc : option (bv (8 * sz))) : option (bv (8 * sz)) :=
            (* A load that forwards from a store must have the same address start point 
            and therefore the same alignment as the store data *)
            match buffer with
            | x :: xs =>
                if bool_decide ((bv_unsigned (addr x) = u_addr) ∧ (Z.of_N (size x) >= Z.of_N sz)) then (
                    let new_val := bv_extract 0 (8 * sz) (val x) in
                        read_from_write_buffer_inner xs u_addr sz (Some new_val)
                )
                else read_from_write_buffer_inner xs u_addr sz acc
            | _ => acc
            end. 

    Definition read_from_write_buffer (tid : Fin.t threads) (addr : address) (size : N) (state : machine_state)
        : option (bv (8 * size)) :=
            read_from_write_buffer_inner (Buffer threads state !!! tid) (bv_unsigned addr) size None.

    Fixpoint add_to_mem_written (addr : address) (size : nat)
        : Exec.t machine_state string unit :=
        match size with
        | S size =>
            (* Add addr to the set of addresses that have been written to in memory*)
            mset (MemWritten threads) (.∪{[addr]});;
            (* Move on to the next byte (if it exists)*)
            add_to_mem_written (addr `+Z` 1)%bv size
        | _ => mret ()
        end.

    Definition add_to_write_buffer (tid : Fin.t threads) (addr : address) (size : N) (val : bv (8 * size))
    (state : machine_state) : machine_state :=
        set (lookup_total tid ∘ Buffer threads)
            (fun curr_list:
                list addr_val => (curr_list ++ [{|
                    addr := addr;
                    size := size;
                    val := val
                |}])%list)
            state.



    (* MEM FUNCTIONS *)

    Definition read_mem (addr : address) (size : N) (state : machine_state) : option (bv (8 * size)) :=
        addr_range addr size
        |$> (fun curr_addr => (Mem threads state) !! curr_addr)
        |> list_of_options
        |$> bv_of_bytes (8 * size).

    Definition mem_addr_modified (addr : address) (size : N) (state : machine_state) : bool :=
        (* Returns true if address modified in memory or written to in a store buffer *)
        bool_decide (∃ a ∈ addr_range addr size, a ∈ MemWritten threads state).

    Fixpoint write_mem_inner (addr : address) (bytes : list (bv 8))
        : Exec.t machine_state string unit :=
            if bytes is byte :: bytes then
                (* Check if memory address is mapped*)
                opt ← mget $ read_mem addr (N.of_nat (length bytes));
                guard_or "Memory isn't mapped to write" (is_Some opt);;
                (* Perform mem write for this byte*)
                msetv (lookup addr ∘ Mem threads) (Some byte);;
                (* Move on to the next byte (if it exists)*)
                write_mem_inner(addr `+Z` 1)%bv bytes
            else mret ().

    Definition write_mem (addr : address) (size : N) (val : bv (8 * size))
        : Exec.t machine_state string unit :=
            bv_to_bytes 8 val
            |> write_mem_inner addr.



    (* BUFFER AND MEM FUNCTIONS *)

    Definition read_mem_with_store_forwarding (tid : Fin.t threads) (macc : mem_acc) (addr : address) (size : N)
        : Exec.t machine_state string (bv (8 * size)) :=
            (* Attempt store forwarding if read is not an instruction fetch *)
            opt ← 
                if is_ifetch macc then 
                    mret None
                else 
                    mget (read_from_write_buffer tid addr size);
            match opt with
            | Some read => 
                mret read
            | None =>
                (* Attempt memory read and return read value *)
                opt ← mget (read_mem addr size);
                read ← othrow ("Memory not found at " ++ pretty addr)%string opt;
                mret read
            end.

    Fixpoint write_buffer_to_mem (buffer: list addr_val) (tid: Fin.t threads)
    : Exec.t machine_state string unit :=
        match buffer with
        | [] => mret ()
        | h :: t =>
            write_mem (addr h) (size h) (val h);;
            write_buffer_to_mem t tid
        end.

    Definition empty_write_buffer (tid : Fin.t threads) : Exec.t machine_state string unit :=
        buffer ← mget (fun state => (Buffer threads state) !!! tid);
        (* Write all buffer contents to memory *)
        write_buffer_to_mem buffer tid;;
        (* Empty buffer *)
        mset (lookup_total tid ∘ Buffer threads) (fun curr_list => []).



    (* LOCK FUNCTIONS*)

    Definition blocked (tid : Fin.t threads) (m : machine_state) : bool :=
        let lock := Lock threads m in
            if lock is Some tid then false
            else if lock is None then false
            else true.

    Definition thread_has_lock (tid : Fin.t threads) (m : machine_state) : bool :=
        match Lock threads m with
        | Some tid => true
        | _ => false
        end.

    Definition acquire_lock (tid : Fin.t threads) (state : machine_state) : machine_state :=
        set (Lock threads) (fun curr_lock => Some tid) state.

    Definition acquire_lock_conditional (tid : Fin.t threads) : Exec.t machine_state string unit :=
        (* Ensure thread can acquire lock: a thread (including thread tid) might already have the lock*)
        lock ← mget (Lock threads);
        if bool_decide (is_Some lock) then mdiscard else mret ();;
        (* Ensure thread can acquire lock: store buffer might not be empty *)
        state ← mGet;
        if negb (buffer_empty tid state) then
            (* Eagerly empty buffer. Can do this as no other thread has lock *)
            empty_write_buffer tid
        else 
            mret ();;
        (* Acquire lock *)
        mSet (acquire_lock tid).

    Definition release_lock (tid : Fin.t threads) (state : machine_state) : machine_state :=
        set (Lock threads) (fun curr_lock => None) state.

    Definition release_lock_conditional (tid : Fin.t threads) : Exec.t machine_state string unit :=
        (* Make sure we have the lock before releasing it *)
        state ← mGet;
        if negb (thread_has_lock tid state) then mdiscard else mret ();;
        (* Empty write buffer (eager) (other requirement for releasing lock) *)
        empty_write_buffer tid;;
        (* Release lock *)
        mSet (release_lock tid).



    (* OUTCOMES *)

    Section RunOutcome.
        Context (tid : Fin.t threads).

        Notation machine_state := (machine_state_t threads).

        Equations run_outcome (call : outcome) : Exec.t machine_state string (eff_ret call) :=
            | RegRead reg racc =>
                opt ← mget (read_reg tid reg);
                othrow ("Register " ++ pretty reg ++ " not found")%string opt
            | RegWrite reg racc val =>
                opt ← mget (read_reg tid reg);
                guard_or ("Writing register " ++ pretty reg ++ " not in initial state")%string (is_Some opt);;
                mSet (write_reg tid reg val)
            | MemRead (MemReq.make macc addr () size 0) =>
                (* Ensure conditions for performing a memory read are satisfied *)
                guard_or "Memory access type not supported" (is_ifetch macc || is_explicit macc);;
                is_blocked ← mget (blocked tid);
                is_no_pending ← (mget (no_pending addr tid));
                if is_blocked || (negb is_no_pending) then mdiscard else mret ();;

                (* Fail ifetch if the location we are attempting to fetch has been modified *)
                modified ← mget (mem_addr_modified addr size);
                guard_or "IFetch reading from modified memory" (negb(is_ifetch macc && modified));;

                (* Acquire lock if needed*)
                (if is_explicit macc && is_atomic_rmw macc then
                    acquire_lock_conditional tid
                else
                    mret ());;

                (* Attempt store forwarding. Read from memory if necessary *)
                read ← read_mem_with_store_forwarding tid macc addr size;
                mret (Ok (read, bv_0 _))
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
                buffer_empty ← mget (buffer_empty tid);
                if (is_blocked : bool) then
                    mdiscard
                else if (buffer_empty : bool) then
                    mret ()
                else
                    empty_write_buffer tid
            | GenericFail msg => mthrow msg
            | _ => mthrow "Unsupported outcome".
    End RunOutcome.

    Definition flush_one_item_buffer (tid : Fin.t threads) : Exec.t machine_state string unit :=
        buffer ← mget (fun state : machine_state => (Buffer threads state) !!! tid);
        match buffer with
        | [] => mdiscard
        | h :: t =>
            (* Write first entry to memory *)
            write_mem (addr h) (size h) (val h);;
            (* Remove first entry from buffer *)
            mset (lookup_total tid ∘ Buffer threads) (fun curr_list => 
                match curr_list with
                | [] => []
                | h :: t => t
                end)
        end.
End Model.

Definition step {nth} (isem : iMon ()) (term : terminationCondition nth): Exec.t (machine_state_t nth) string () :=
    (* The transition taken is either a flush to memory or a run_outcome call *)

    (* Get tid *)
    state ← mGet;
    '(tid_temp : {x : fin nth | ((TermThreads nth state !!! x) = false)}) ← mchoosef;
    let tid := proj1_sig tid_temp in

    (* Get transition type *)
    '(flush_transition : bool) ← mchoosef;

    (* Get step conditions *)
    let regMap := Reg nth state !!! tid in
    let termCondMet := term tid regMap in
    let bufferEmpty := buffer_empty nth tid state in

    if termCondMet && bufferEmpty then
        (* Terminate thread if there is no more work to do *)
        mset (lookup_total tid ∘ TermThreads nth) (fun x => true)
    else if flush_transition then
        (* Flush one item to memory *)
        flush_one_item_buffer nth tid
    else if termCondMet then
        (* If an execution step can't be made, then discard path *)
        mdiscard
    else
        (* Run one outcome *)
        cinterp (run_outcome nth tid) isem.

Fixpoint run_to_term {nth} (fuel : nat) (isem : iMon ()) (term : terminationCondition nth)
    : Exec.t (machine_state_t nth) string {s : archState nth & archState.is_terminated term s} :=
        (* run until out of fuel or conditions met *)
        if fuel is S fuel then
            step isem term;;
            state ← mget to_archState;
            if decide (archState.is_terminated term state) is left p then
                mret (existT state p)
            else
                run_to_term fuel isem term
        else
            mthrow "Out of fuel".

(** Top-level one-threaded model function that takes fuel (guaranteed
    termination) and an instruction monad, and returns a computational set of
    all possible final states. *)
Definition x86_operational_modelc (fuel : nat) (isem : iMon ()) : (archModel.c ∅) :=
    λ n term (initSt: archState n),
    from_archState initSt
    |> archModel.Res.from_exec (run_to_term fuel isem term).
