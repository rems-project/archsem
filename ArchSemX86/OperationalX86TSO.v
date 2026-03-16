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

(** This is an implementation of the x86-TSO operational concurrency model,
    as defined in https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.pdf *)

Section Model.
  (** The number of hardware threads *)
  Context {threads : nat}.

  (** * Types *)

  (** A memory entry in a write-buffer *)
  Record addr_val := {
      addr: address;
      size: N; (* IN BYTES *)
      val: bv (8 * size)
    }.

  (** The TSO model internal state *)
  Record mstate := {
      regs : vec registerMap threads; (* Registers for each thread *)
      mem : memoryMap;

      (* Store buffer for each thread. Each buffer is a list of address-value
        tuples, oldest first *)
      buf : vec (list addr_val) threads;

      (* Global machine lock, indicating when some thread has exclusive access to
        memory *)
      lock : option (fin threads);

      (* Set of memory addresses that have been written to *)
      memWritten : gset address;

      (* Whether a thread is terminated, but not necessarily flushed *)
      termThreads : vec bool threads;
    }.

  (** * Helper functions *)

  (** ** Register functions *)

  Definition read_reg (tid : fin threads) (reg : reg) (state : mstate) :
      option (reg_type reg) :=
    let regMap := (regs state !!! tid) in
    dmap_lookup reg regMap.

  Definition write_reg (tid : fin threads) (reg : reg) (val : reg_type reg)
      (state : mstate) : mstate :=
    set (lookup_total tid ∘ regs) (dmap_insert reg val) state.



  (** ** Buffer functions *)

  Definition no_pending (x : address) (tid : fin threads)
      (state : mstate) : bool :=
    let buffer := buf state !!! tid in
    bool_decide (∀ av ∈ buffer, addr av ≠ x).

  Definition buffer_empty (tid : fin threads) (m : mstate) : bool :=
    if buf m !!! tid is [] then true else false.

  Definition all_buffers_empty (state : mstate) : bool :=
    bool_decide (∀ t : fin threads, buffer_empty t state).

  Fixpoint read_from_write_buffer_inner (rev_buffer : list addr_val)
      (goal_addr: address) (goal_size : N) :
      Exec.t mstate string (option (bv (8 * goal_size))) :=
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
          mret (Some return_val)
        else if bool_decide (goal_range ∩ x_range ≠ ∅) then
          mthrow "Model prohibits programs where mixed-size store forwarding can occur"
        else read_from_write_buffer_inner xs goal_addr goal_size
    | _ => mret None
    end.

  Definition read_from_write_buffer (tid : fin threads) (addr : address) (size : N) :
      Exec.t mstate string (option (bv (8 * size))) :=
    buffer ← mget ((.!!! tid) ∘ buf);
    (* Reverse buffer so that we see most recent writes first *)
    read_from_write_buffer_inner (rev buffer) addr size.

  Fixpoint add_to_mem_written (addr : address) (size : nat) :
      Exec.t mstate string unit :=
    match size with
    | S size =>
        (* Add addr to the set of addresses that have been written to in memory*)
        mset memWritten (.∪{[addr]});;
        (* Move on to the next byte (if it exists)*)
        add_to_mem_written (addr `+Z` 1)%bv size
    | _ => mret ()
    end.

  Definition add_to_write_buffer (tid : fin threads) (addr : address)
      (size : N) (val : bv (8 * size)) (state : mstate) : mstate :=
    set ((.!!! tid) ∘ buf) (.++ [{| addr := addr; size := size; val := val |}])
      state.


  (** ** Memory functions *)

  Definition mem_addr_modified (addr : address) (size : N) (state : mstate) : bool :=
    (* Returns true if address modified in memory or written to in a store buffer *)
    bool_decide (∃ a ∈ addr_range addr size, a ∈ memWritten state).

  Definition write_mem (addr : address) (size : N) (val : bv (8 * size)) :
      Exec.t mstate string unit :=
    (* Check if memory address is mapped*)
    opt ← mget (mem_lookup addr size ∘ mem);
    guard_or "Memory isn't mapped to write" (is_Some opt);;
    (* Write to memory *)
    mset mem (mem_insert addr size val).


  (** ** Buffer and Memory functions *)

  Definition read_mem_with_store_forwarding (tid : fin threads) (addr : address)
      (size : N) : Exec.t mstate string (bv (8 * size)) :=
    (* Attempt store forwarding *)
    opt ← read_from_write_buffer tid addr size;
    if opt is Some read then
      mret read
    else
      (* Attempt memory read and return read value *)
      opt ← mget (mem_lookup addr size ∘ mem);
      read ← othrow ("Memory not found at " ++ pretty addr)%string opt;
      mret read.

  Fixpoint write_buffer_to_mem (buffer: list addr_val) (tid: fin threads) :
      Exec.t mstate string unit :=
    match buffer with
    | [] => mret ()
    | h :: t =>
        write_mem (addr h) (size h) (val h);;
        write_buffer_to_mem t tid
    end.

  Definition empty_write_buffer (tid : fin threads) : Exec.t mstate string unit :=
    buffer ← mget ((.!!! tid) ∘ buf);
    (* Write all buffer contents to memory *)
    write_buffer_to_mem buffer tid;;
    (* Empty buffer *)
    msetv ((.!!! tid) ∘ buf) [].


  (** ** Lock functions *)

  Definition blocked (tid : fin threads) (m : mstate) : bool :=
    if lock m is Some tid' then bool_decide (tid ≠ tid')
    else false.

  Definition thread_has_lock (tid : fin threads) (m : mstate) : bool :=
    if lock m is Some tid' then bool_decide (tid = tid')
    else false.

  Definition acquire_lock (tid : fin threads) (state : mstate) : mstate :=
    setv lock (Some tid) state.

  Definition acquire_lock_conditional (tid : fin threads) :
      Exec.t mstate string unit :=
    (* Ensure thread can acquire lock: a thread (including thread tid) might already have the lock*)
    lock_status ← mget lock;
    guard_discard (lock_status = None);;
    (* Ensure thread can acquire lock: store buffer might not be empty.
       Hence eagerly empty buffer. Can do this as no other thread has lock *)
    empty_write_buffer tid;;
    (* Acquire lock *)
    mSet (acquire_lock tid).

  Definition release_lock (tid : fin threads) (state : mstate) : mstate :=
    setv lock None state.

  Definition release_lock_conditional (tid : fin threads) :
      Exec.t mstate string unit :=
    (* Make sure we have the lock before releasing it *)
    state ← mGet;
    guard_discard (thread_has_lock tid state);;
    (* Empty write buffer (eager) (other requirement for releasing lock) *)
    empty_write_buffer tid;;
    (* Release lock *)
    mSet (release_lock tid).


  (** * Model transitions *)

  (** ** Run outcomes *)

  Section RunOutcome.
    Context (tid : fin threads) (eager : bool).

    Equations run_outcome (call : outcome) : Exec.t mstate string (eff_ret call) :=
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
          (* Fail ifetch if the location we are attempting to fetch has been
             modified *)
          modified ← mget (mem_addr_modified addr size);
          guard_or "IFetch reading from modified memory" (negb modified);;
          (* Read from memory *)
          opt ← mget (mem_lookup addr size ∘ mem);
          read ← othrow ("Memory not found at " ++ pretty addr)%string opt;
          mret (Ok (read, 0%bv))
        else if is_explicit macc then
          (* Cannot eagerly perform memory reads*)
          guard_discard (negb eager);;
          (* Can't explicitly read from memory if we are blocked (some other
             thread has the lock) *)
          is_blocked ← mget (blocked tid);
          guard_discard (negb is_blocked);;
          (* Acquire lock if needed*)
          (if is_atomic_rmw macc then acquire_lock_conditional tid else mret ());;
          (* Attempt store forwarding. Read from memory if store forwarding not
             possible *)
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
        (if is_atomic_rmw macc then
          if eager then
            (* Must discard outcome if eager, as release_lock_conditional requires
              the store buffer to be emptied to complete *)
            mdiscard
          else release_lock_conditional tid
        else mret ());;
        mret (Ok ())
    | MemWrite _ _ _ => mthrow "Unsupported MemWrite"
    | Barrier Barrier_MFENCE =>
        (* Cannot eagerly perform memory barriers*)
        guard_discard (negb eager);;

        (* Write buffer (of thread tid) must be emptied before this instruction
           can complete. *)
        is_blocked ← mget (blocked tid);
        guard_discard (negb is_blocked);;
        empty_write_buffer tid
    | Barrier _ => mret ()
    | GenericFail msg => mthrow msg
    | _ => mthrow "Unsupported outcome".
  End RunOutcome.

  (** ** Flushing transition *)
  Definition flush_one_item_buffer (tid : fin threads) :
      Exec.t mstate string unit :=
    buffer ← mget ((.!!! tid) ∘ buf);
    match buffer with
    | [] => mdiscard
    | h :: t =>
        (* Write first entry to memory *)
        write_mem (addr h) (size h) (val h);;
        (* Remove first entry from buffer *)
        msetv ((.!!! tid) ∘ buf) t
    end.

  Context (isem : iMon ()) (term : terminationCondition threads).

  (** ** Execution step transition *)
  Definition execution_step (tid : fin threads) (eager : bool)
    : Exec.t mstate string () :=
    (* Check if the thread is already marked terminated, in which case there
      is no transition to take. *)
    terminated ← mget ((.!!! tid) ∘ termThreads);
    guard_discard (negb terminated);;

    (* Run one instruction *)
    cinterp (run_outcome tid eager) isem;;
    (* Check if the thread is actually terminated and mark it if so *)
    'regs ← mget ((.!!! tid) ∘ regs);
    if term tid regs then
      (* Mark it as terminated *)
      msetv ((.!!! tid) ∘ termThreads) true
    else
      mret ().

  (** ** Top level transitions *)

  (** This returns [Some tid] when taking a instruction transition because it
      might enable eager transitions *)
  Definition step : Exec.t mstate string (option (fin threads)) :=
    (* The transition taken is either a flush to memory or a run_outcome call,
    for a specific tid *)
    tid ← mchoosef;
    flush_transition ← mchoosef;
    if (flush_transition : bool) then
      (* This function discards if there is nothing to flush. *)
      flush_one_item_buffer tid;;
      mret None
    else
      execution_step tid false;;
      mret (Some tid).

  (** ** Eager transition functions *)
  Definition run_eager_thread_step (tid : fin threads) :
      Exec.t mstate string bool :=
    (* Eagerly run single thread instruction if possible.
      The returned bool is true if the instruction runs successfully *)
    '(terminated : bool) ← mget ((.!!! tid) ∘ termThreads);
    if terminated then
      mret false
    else
      st ← mGet;
      (* Run instruction eagerly. Only bind new outcome if it is successful *)
      let new_outcome := execution_step tid true st in
        if Exec.to_result_list new_outcome is [] then
          mret false
        else
          Exec.lift_res_st new_outcome;;
          mret true.

  Fixpoint run_eager_thread (fuel : nat) (tid : fin threads) :
      Exec.t mstate string nat :=
    (* Run as many instructions as possible for this thread *)
    if fuel is S fuel then
      (* Run instruction eagerly if possible *)
      '(instr_ran : bool) ← run_eager_thread_step tid;
      if instr_ran then
        run_eager_thread fuel tid
      else mret (S fuel)
    else mthrow "Out of fuel".

  Definition run_eager_all (fuel : nat) : Exec.t mstate string nat :=
    (* For each thread, run as many instructions as possible *)
    foldlM run_eager_thread fuel (enum (fin threads)).



  (** * Lift to executable archModel *)

  Definition from_archState (astate : archState threads) : mstate :=
    {|
      regs := astate.(archState.regs);
      mem := astate.(archState.memory);
      buf := Vector.const [] threads;
      lock := None;
      memWritten := ∅;
      termThreads := vimap term astate.(archState.regs);
    |}.

  Definition to_archState (mstate : mstate) : option (archState threads) :=
    if all_buffers_empty mstate && bool_decide (lock mstate = None) then
      Some {|
          archState.regs := regs mstate;
          archState.memory := mem mstate;
          archState.address_space := ()
        |}
    else None.

  Definition to_terminated_archState (mstate : mstate) :
      option {s : archState threads & archState.is_terminated term s} :=
    guard (∀ tid, mstate.(termThreads) !!! tid : bool);;
    astate ← (to_archState mstate);
    if decide (archState.is_terminated term astate) is left p then
      Some (existT astate p)
    else None.

  (** ** No-eager-transitions runner *)

  (** Just take non-eager transition until reaching termination *)
  Fixpoint run_to_term_no_eager (fuel : nat) :
    Exec.t mstate string {s : archState threads & archState.is_terminated term s} :=
    (* run until out of fuel or conditions met *)
    if fuel is S fuel then
      (* Run a non-eager execution step *)
      step;;
      (* Check if termination condition met. If not, execute non-eager step *)
      fstate ← mget to_terminated_archState;
      if fstate is Some fs then mret fs else run_to_term_no_eager fuel
    else mthrow "Out of fuel".


  (** ** Eager-transition-enabled runner *)

  (** [run_to_term_eager_normal fuel] Assumes that no eager transition is
      possible and does a normal transition.

      [run_to_term_eager_eager fuel tid] Does all possible transition in thread
      [tid] then goes back to the "normal" runner. *)
  Fixpoint run_to_term_eager_normal (fuel : nat) :
      Exec.t mstate string _ :=
    (* run until out of fuel or conditions met *)
    if fuel is S fuel then
      (* Run a non-eager execution step *)
      eager_thread ← step;
      if eager_thread is Some tid then
        run_to_term_eager_eager fuel tid
      else
        (* Check if termination condition met. If not, execute non-eager step *)
        fstate ← mget to_terminated_archState;
        if fstate is Some fs then mret fs else run_to_term_eager_normal fuel
    else mthrow "Out of fuel"

  with run_to_term_eager_eager (fuel : nat) (tid : fin threads)  :
      Exec.t mstate string {s : archState threads & archState.is_terminated term s} :=
    if fuel is S fuel then
      (* Try to do eager execution of thread [tid] if possible *)
      '(instr_ran : bool) ← run_eager_thread_step tid;
      if instr_ran then
        (* If we run an eager transition, run another one *)
        run_to_term_eager_eager fuel tid
      else
        (* Otherwise, check if termination condition met. If not, execute
            non-eager step *)
        fstate ← mget to_terminated_archState;
        if fstate is Some fs then mret fs else run_to_term_eager_normal fuel
    else mthrow "Out of fuel".


  (** ** Full model runner *)

  Definition run_to_term (allow_eager : bool) (fuel : nat) :
        Exec.t mstate string
        {s : archState threads & archState.is_terminated term s} :=
    (* If eager transitions allowed, try to eagerly execute each thread,
        as we are in the first iteration *)
    if allow_eager then
      run_eager_all fuel;;
      fstate ← mget to_terminated_archState;
      if fstate is Some fs then mret fs else run_to_term_eager_normal fuel
    else
      run_to_term_no_eager fuel.
End Model.
Arguments mstate : clear implicits.


(** Top-level one-threaded model function that takes fuel (guaranteed
    termination) and an instruction monad, and returns a computational set of
    all possible final states. *)
Definition x86_operational_modelc (fuel : nat) (isem : iMon ()) (allow_eager : bool)
  : (archModel.c ∅) :=
  λ n term (initSt: archState n),
    from_archState term initSt
    |> archModel.Res.from_exec (run_to_term isem term allow_eager fuel).
