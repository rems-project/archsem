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
From ASCommon Require Import Common GRel FMon.

Require Import X86Inst.

(** This is an implementation of the x86 user-mode mixed-size Axiomatic model,
  translated from Herd's x86tso-mixed.cat 
  (https://github.com/herd/herdtools7/blob/e8199fce6c4fe36dfa97aebf767465ddac421e28/herd/libdir/x86tso-mixed.cat)
*)

Section Barriers.
  Import Candidate.
  Context {et : exec_type} {nmth : nat}.
  Implicit Type cd : (t et nmth).
  Implicit Type b : barrier.
  #[local] Hint Extern 10 (Decision (?x _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _ _)) => unfold x : typeclass_instances.
  
  Definition is_mfence b := if b is Barrier_MFENCE then True else False.
  Definition mfence cd := collect_all (λ _, is_barrierP is_mfence) cd.
End Barriers.

Section Model.
  Import Candidate.
  Context (regs_whitelist : gset reg).
  Context {nmth : nat}. (* number of threads *)
  Context {ms: exec_type}. (* mixed-size or not *)
  Context (cd : Candidate.t ms nmth).

  (** Generic notation taken from elsewhere *)

  (** ** Thread relations *)
  Notation pe := (pre_exec cd).
  Notation int := (same_thread pe).
  Notation si := (same_instruction_instance cd).

  (** ** Memory *)
  Notation W := (explicit_writes pe).
  Notation R := (explicit_reads pe).
  Notation M := (mem_explicit pe).
  Notation IF := (ifetch_reads pe).
  Notation IR := (init_mem_reads cd).

  Definition co := coherence cd ∩ overlapping cd.
  Definition coi := co ∩ int.
  Definition coe := co ∖ coi.

  Definition rf := reads_from cd⨾⦗R⦘.
  Definition rfi := rf ∩ int.
  Definition rfe := rf ∖ rfi.
  Definition fr := ⦗R⦘⨾from_reads cd.
  Definition fri := fr ∩ int.
  Definition fre := fr ∖ fri.

  (** ** Program-order *)
  Notation po := (instruction_order pe).
  Definition po_loc := po ∩ same_addr cd.

  (** ** Only allow whitelisted regs *)
  Definition is_illegal_reg_write (regs : gset reg) :=
    is_reg_writeP (λ reg acc _, reg ∉ regs).
  #[export] Instance is_illegal_reg_write_dec regs ev :
    Decision (is_illegal_reg_write regs ev).
  Proof. unfold_decide. Defined.

  Definition Illegal_RW := collect_all (λ _, is_illegal_reg_write regs_whitelist) cd.



  (** X86-specific definitions *)

  Notation MFENCE := (mfence cd).

  (** ** Atomic read-modify-write accesses *)
  Notation Wx := (atomic_rmw_writes pe).
  Notation Rx := (atomic_rmw_reads pe).
  Notation rmw := (atomic_update cd).



  (** Start of actual model definition *)

  (** ** Coherence-after *)
  Definition ca := fr ∪ co.

  (** ** Observed-by *)
  Definition obs := rfe ∪ fre ∪ coe.

  (** ** Locally-ordered-before *)
  Definition lob1 := po ∖ (⦗W⦘⨾ po⨾ ⦗R⦘)
    ∪ (⦗W⦘⨾ po⨾ ⦗MFENCE⦘⨾ po⨾ ⦗R⦘)
    ∪ (⦗W⦘⨾ po⨾ ⦗Rx⦘)
    ∪ (⦗Wx⦘⨾ po⨾ ⦗R⦘).
  Definition lob := lob1⁺.

  (** ** Ordered-before *)
  Definition ob1 := (obs⨾ si) ∪ lob.
  Definition ob := ob1⁺.

  (** ** Model axioms *)
  Record consistent := {
      internal_visibility : grel_acyclic (po_loc ∪ ca ∪ rf);
      atomic : rmw ∩ (fre⨾ coe) = ∅;
      external_visibility : grel_irreflexive ob;
    }.
  #[export] Instance consistent_dec : Decision consistent := ltac:(decide_record).

  (** ** Ensure that there is no undefined behaviour *)
  Record not_UB := {
      (* Ensure we are not fetching modified instructions *)
      initial_reads : IF ⊆ IR;

      (* An instruction fetch should not occur "strictly after" a memory event 
        / should not change the state of memory, TODO: clarify *)
      initial_reads_not_delayed : IF ## grel_rng (coherence cd);

      (* Ensure that only whitelisted registers are written to *)
      register_write_permitted : Illegal_RW = ∅; (* TODO: is this necessary *)

      (* Memory events must be explicit or instruction fetch *)
      memory_events_permitted : (mem_events cd) ⊆ M ∪ IF;

      (* We might care about not allowing mixed-size accesses *)
      is_nms' : if ms is NMS then is_nms cd else True;
    }.
  #[export] Instance not_UB_dec : Decision not_UB := ltac:(decide_record).

  Definition consistent_ok := consistent ∧ not_UB.
  #[export] Instance consistent_ok_dec : Decision consistent_ok := ltac:(unfold_decide).
  
End Model.

Require Import ASCommon.CResult.

(** The User x86 axiomatic model *)
Definition axmodel regs_whitelist : Ax.t Candidate.NMS ∅ :=
  λ _ cd, if decide (consistent cd) then
            if decide (not_UB regs_whitelist cd) then Ok Ax.Allowed
            else Error ""
          else Ok Ax.Rejected.

(** The User x86 architecture model *)
Definition archmodel regs_whitelist isem : archModel.nc ∅ :=
  Ax.to_archModel_nc isem (axmodel regs_whitelist).
