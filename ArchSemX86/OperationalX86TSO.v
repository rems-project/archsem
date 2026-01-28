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

Inductive fence: Type :=
| LFence
| SFence
| MFence.

Record addr_val : Type := {
    addr: address;
    size: N;
    val: bv size
}.

(* archState + extra fields (buffer and lock)*)
Record machine_state : Type := {
    R : gmap nat registerMap; (* Registers for each thread *)
    M : memoryMap;
    B : gmap nat (list addr_val); (* Gives the store buffer for each thread. Each buffer is a list of address-value tuples, most recent first *)
    L : option nat (* Global machine lock, indicating when some thread has exclusive access to memory *)
}.

Fixpoint no_pending_inner (x : address) (buffer : (list addr_val)) : bool :=
    match buffer with
    | nil => true
    | h :: t =>
        if decide(addr h = x) then false 
        else no_pending_inner x t
    end.

Definition no_pending (x : address) (tid : nat) (state : machine_state) : option bool :=
    match gmap_lookup tid (B state) with
    | Some buffer => Some (no_pending_inner x buffer)
    | None => None
    end.

Definition blocked (tid : nat) (m : machine_state) : bool :=
    let lock := L m in 
        if lock is Some tid then false
        else if lock is None then false
        else true.

Definition buffer_empty (tid : nat) (m : machine_state) : bool :=
    match gmap_lookup tid (B m) with
    | Some (x :: xs) => false
    | _ => true
    end.

Definition thread_has_lock (tid : nat) (m : machine_state) : bool :=
    match L m with
    | Some tid => true
    | _ => false
    end.
        

Definition read_reg (tid : nat) (reg : reg) (state : machine_state) : option (reg_type reg) :=
    match (gmap_lookup tid (R state)) with
    | Some regMap => dmap_lookup reg regMap
    | None => None
    end.

Definition write_reg (tid : nat) (reg : reg) (val : reg_type reg) (state : machine_state) : machine_state :=
    set (lookup tid ∘ R) (option_map (dmap_insert reg val)) state.

Definition read_mem (addr : address) (size : N) (state : machine_state) : option (bv (8 * size)) :=
    addr_range addr size
    |$> (fun curr_addr => (M state) !! curr_addr)
    |> list_of_options
    |$> bv_of_bytes (8 * size).

Definition add_to_write_buffer (tid : nat) (addr : address) (size : N) (val : bv (8 * size)) 
    (state : machine_state) : machine_state :=
        set (lookup tid ∘ B) 
            (option_map (fun curr_list: 
                list addr_val => (curr_list ++ [{|
                    addr := addr; 
                    size := (8 * size); 
                    val := val
                |}]))%list) 
            state.

Fixpoint write_mem_inner (addr : address) (bytes : list (bv 8)) 
    : Exec.t machine_state string unit :=
        if bytes is byte :: bytes then
            opt ← mget $ read_mem addr (N.of_nat (length bytes));
            guard_or "Memory isn't mapped to write" (is_Some opt);;
            msetv (lookup addr ∘ M) (Some byte);;
            write_mem_inner(addr `+Z` 1)%bv bytes
        else mret ().

Definition write_mem (addr : address) (size : N) (val : bv size)
    : Exec.t machine_state string unit := 
        bv_to_bytes 8 val
        |> write_mem_inner addr.
    
Fixpoint write_buffer_to_mem (buffer: list addr_val) (tid: nat)
    : Exec.t machine_state string unit :=
        match buffer with
        | [] => mret ()
        | h :: t => 
            write_mem (addr h) (size h) (val h);;
            write_buffer_to_mem t tid
        end.

Definition empty_write_buffer (tid : nat) : Exec.t machine_state string unit :=
    buffer ← mget (fun state => gmap_lookup tid (B state));
    match buffer with
    | None => mret ()
    | Some b => 
        (* Write all buffer contents to memory *)
        write_buffer_to_mem b tid;;
        (* Empty buffer *)
        mSet (set (lookup tid ∘ B) (option_map (fun curr_list => [])))
    end.

Definition acquire_lock (tid : nat) (state : machine_state) : machine_state :=
    set L (fun curr_lock => Some tid) state.

Definition release_lock (tid : nat) (state : machine_state) : machine_state :=
    set L (fun curr_lock => None) state.

Section RunOutcome.
  Context (tid : nat) (initmem : memoryMap).

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
        guard_or "Memory access type not supported" (negb(is_ifetch macc || is_explicit macc));;
        is_blocked ← mget (blocked tid);
        option_no_pending ← (mget (no_pending addr tid));
        guard_or ("Thread " ++ pretty tid ++ " has no buffer")%string (is_Some option_no_pending);;
        let is_no_pending := default false option_no_pending in
        if is_blocked || (negb is_no_pending) then
            mthrow ("Thread " ++ pretty tid ++ " is blocked")%string
        else
            (* Acquire lock if needed*)
            (
                if is_explicit macc && is_atomic_rmw macc then (
                    state ← mGet;
                    guard_or 
                        ("Thread " ++ pretty tid ++ " can't acquire lock as its store buffer is not empty")%string
                        (negb(buffer_empty tid state));; 
                    lock ← mget L; 
                    guard_or 
                        ("Thread " ++ pretty tid ++ " attempting to acquire a lock it already has")%string 
                        (is_Some lock);;
                    mSet (acquire_lock tid)
                )
                else mret ()
            );;
            (* Attempt memory read and return read value *)
            opt ← mget (read_mem addr size);
            read ← othrow ("Memory not found at " ++ pretty addr)%string opt;
            mret (Ok (read, bv_0 _))
    | MemWrite (MemReq.make macc addr () size 0) val _ => 
        (* Add write to write buffer *)
        mSet (add_to_write_buffer tid addr size val);;
        (* Handle atomic case (release lock) *)
        (
            if is_explicit macc && is_atomic_rmw macc then 
                (* Make sure we have the lock before releasing it *)
                state ← mGet;
                guard_or
                    ("Thread " ++ pretty tid ++ " attempting to release a lock it doesn't have")%string 
                    (thread_has_lock tid state);;
                (* Empty write buffer (other requirement for releasing lock) *)
                empty_write_buffer tid;;
                (* Release lock *)
                mSet (release_lock tid)
            else mret ()
        );;
        mret (Ok ())
    | _ => mthrow "Unsupported outcome".
End RunOutcome.
