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

Require Import X86Inst.

(** this is an implementation of the x86-TSO operational concurrency model,
    as defined in https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.pdf *)



(* TSO Model Types*)

Definition value: Type := forall (opsize: operand_size), bits opsize.

Inductive fence: Type :=
| LFence
| SFence
| MFence.

(* eid = event id, tid = thread id*)
Inductive event: Type :=
| Write (eid: nat) (tid: nat) (x: address) (v: value)
| Read (eid: nat) (tid: nat) (x: address) (v: value)
| Dequeue (eid: nat) (tid: nat) (x: address) (v: value)
| Fence (eid: nat) (tid: nat) (fence_type: fence)
| Lock (eid: nat) (tid: nat)
| Unlock (eid: nat) (tid: nat).

Definition get_event_id (e: event): nat :=
    match e with
    | Write a _ _ _ => a
    | Read a _ _ _ => a
    | Dequeue a _ _ _ => a
    | Fence a _ _ => a
    | Lock a _ => a
    | Unlock a _ => a
    end.

Definition get_thread_id (e: event): nat :=
    match e with
    | Write _ t _ _ => t
    | Read _ t _ _ => t
    | Dequeue _ t _ _ => t
    | Fence _ t _ => t
    | Lock _ t => t
    | Unlock _ t => t
    end.

Definition get_address (e: event): option address :=
    match e with
    | Write _ _ x _ => Some x
    | Read _ _ x _ => Some x
    | Dequeue _ _ x _ => Some x
    | _ => None
    end.

Definition get_value (e: event): option value :=
    match e with
    | Write _ _ _ v => Some v
    | Read _ _ _ v => Some v
    | Dequeue _ _ _ v => Some v
    | _ => None
    end.

Definition is_read (e: event): bool := 
    match e with
    | Read _ _ _ _ => true
    | _ => false
    end.

Definition is_write (e: event): bool := 
    match e with
    | Write _ _ _ _ => true
    | _ => false
    end.

Definition is_dequeue (e: event): bool :=
    match e with
    | Dequeue _ _ _ _ => true
    | _ => false
    end.

(* archState + extra fields (buffer and lock)*)
Record machine_state: Type := {
    R: gmap nat registerMap; (* Registers for each thread *)
    M: memoryMap;
    B: gmap nat (list {e: event | is_write(e)}); (* Gives the store buffer for each thread. Each buffer is a list of write events, most recent first *)
    L: option nat (* Global machine lock, indicating when some thread has exclusive access to memory *)
}.

Fixpoint no_pending (buffer: list {e: event | is_write(e)}) (x: address): bool :=
    match buffer with
    | nil => true
    | w :: t =>
        if get_address (proj1_sig w) is Some x then false (* proj1_sig extracts the type from the type-proof bundle *)
        else no_pending t x
    end.

Definition not_blocked (m: machine_state) (tid: nat): bool :=
    let lock := L m in 
        if lock is Some tid then true
        else if lock is None then true 
        else false.

Definition read_reg (tid: nat) (reg: reg) (state: machine_state): option (reg_type reg) :=
    match (gmap_lookup tid (R state)) with
    | Some regMap => dmap_lookup reg regMap
    | None => None
    end.

Definition write_reg (tid: nat) (reg: reg) (val: reg_type reg) (state: machine_state): machine_state :=
    set (lookup tid ∘ R) (option_map (dmap_insert reg val)) state.

Section RunOutcome.
  Context (tid : nat) (initmem : memoryMap).

  Equations run_outcome (call : outcome) : Exec.t (machine_state) string (eff_ret call) :=
    | RegRead reg racc =>
        opt ←  mget (read_reg tid reg);
        othrow ("Register " ++ pretty reg ++ " not found")%string opt
    | RegWrite reg racc val =>
        opt ←  mget (read_reg tid reg);
          guard_or ("Writing register " ++ pretty reg ++ " not in initial state")%string $
            is_Some opt;;
        mSet $ write_reg tid reg val.
End RunOutcome.