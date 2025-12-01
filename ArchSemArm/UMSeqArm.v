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

Require Import ArmInst.
Require Import GenAxiomaticArm.


(** This is an implementation of a user-mode SC Axiomatic model in ARM style.

    This model used the "pa" part of the interface as the main address and does
    not check that that translation makes sense if there is one. However it will
    check that translations and instruction fetchs read from initial memory if
    they exist, and that no writes are made to the address used for
    translations(more exactly that translation reads never read from non-initial
    writes) *)
Import Candidate.
Section UMSeqArm.
  Context (regs_whitelist : gset reg).
  Context {nmth : nat}.
  Context (cd : Candidate.t NMS nmth).

  (** * Arm standard notations *)
  Import AxArmNames.

  (** ** Thread relations *)
  Notation pe := (pre_exec cd).
  Notation int := (same_thread pe).
  Notation si := (same_instruction_instance cd).
  Notation sca := (same_access cd).
  Notation instruction_order := (instruction_order pe).
  Notation full_instruction_order := (full_instruction_order pe).
  Notation iio := (iio pe).

  (** ** Dependencies *)
  Notation addr := (addr cd).
  Notation data := (data cd).
  Notation ctrl := (ctrl cd).

  (** ** Registers *)
  Notation RR := (reg_reads pe).
  Notation RW := (reg_writes pe).
  Notation RE := (RE cd).
  Notation rrf := (reg_reads_from cd).
  Notation rfr := (reg_from_reads cd).
  Notation MSR := (MSR cd).
  Notation MRS := (MRS cd).

  (** ** Barriers *)
  Notation F := (barriers cd).
  Notation ISB := (isb cd).

  (** ** Memory *)
  Notation W := (explicit_writes pe).
  Notation R := (explicit_reads pe).
  Notation M := (mem_explicit pe).
  Notation Wx := (exclusive_writes pe).
  Notation Rx := (exclusive_writes pe).
  Notation L := (rel_acq_rcsc_writes pe).
  Notation A := (rel_acq_rcsc_reads pe).
  Notation Q := (rel_acq_rcpc_reads pe).
  Notation T := (ttw_reads pe).
  Notation IF := (ifetch_reads pe).
  Notation IR := (init_mem_reads cd).

  Notation lxsx := (lxsx cd).
  Notation amo := (atomic_update cd).
  Notation rmw := (rmw cd).

  Notation co := (co cd).
  Notation coi := (coi cd).
  Notation coe := (coe cd).

  Notation rf := (rf cd).
  Notation rfi := (rfi cd).
  Notation rfe := (rfe cd).
  Notation fr := (fr cd).
  Notation fri := (fri cd).
  Notation fre := (fre cd).

  Notation frf := (frf cd).
  Notation frfi := (frfi cd).

  Notation trf := (trf cd).
  Notation trfi := (trfi cd).
  Notation trfe := (trfe cd).
  Notation tfr := (tfr cd).
  Notation tfri := (tfri cd).
  Notation tfre := (tfre cd).

  Notation irf := (irf cd).
  Notation irfi := (irfi cd).
  Notation irfe := (irfe cd).
  Notation ifr := (ifr cd).
  Notation ifri := (ifri cd).
  Notation ifre := (ifre cd).

  (** ** Caches *)
  Notation ICDC := (ICDC cd).
  Notation TLBI := (TLBI cd).
  Notation C := (C cd).

  (** ** Exceptions *)
  Notation TE := (TE cd).
  Notation ERET := (ERET cd).

  (** ** Explicit events *)
  Notation Exp := (Exp cd).
  Notation po := (po cd).
  (* End of copy paste section*)


  Definition is_illegal_reg_write (regs : gset reg) :=
    is_reg_writeP (λ reg acc _, reg ∉ regs ∨ acc ≠ None).
  #[export] Instance is_illegal_reg_write_dec regs ev :
    Decision (is_illegal_reg_write regs ev).
  Proof. unfold_decide. Defined.

  Definition Illegal_RW := collect_all (λ _, is_illegal_reg_write regs_whitelist) cd.

  Definition is_illegal_reg_read (regs : gset reg) :=
    is_reg_writeP (λ reg acc _, acc ≠ None).
  #[export] Instance is_illegal_reg_read_dec regs ev :
    Decision (is_illegal_reg_read regs ev).
  Proof. unfold_decide. Defined.


  Definition Illegal_RR := collect_all (λ _, is_illegal_reg_read regs_whitelist) cd.

  (* TODO This does not distinguishes UB conditions from invalid conditions *)
  Record consistent := {
      total : grel_acyclic (full_instruction_order ∪ fr ∪ co ∪ rf ∪ rfr ∪ rrf);
      atomic : (rmw ∩ (fre⨾ coe)) = ∅;
    }.
  #[export] Instance consistent_dec : Decision consistent := ltac:(decide_record).

  Record not_UB := {
      initial_reads : (T ∪ IF) ⊆ IR;
      register_write_permitted : Illegal_RW = ∅;
      register_read_permitted : Illegal_RR = ∅;
      memory_events_permitted : (mem_events cd) ⊆ M ∪ T ∪ IF;
      is_nms' : is_nms cd;
      no_exceptions: TE ∪ ERET = ∅
    }.
  #[export] Instance not_UB_dec : Decision not_UB := ltac:(decide_record).

  Definition consistent_ok := consistent ∧ not_UB.
  Instance consistent_ok_dec : Decision consistent_ok := ltac:(unfold_decide).

End UMSeqArm.

Require Import ASCommon.CResult.

(** The SC Arm axiomatic model *)
Definition axmodel regs_whitelist : Ax.t NMS ∅ :=
  λ _ cd, if decide (consistent cd) then
            if decide (not_UB regs_whitelist cd) then Ok Ax.Allowed
            else Error ""
          else Ok Ax.Rejected.

(** The SC Arm architecture model *)
Definition archmodel regs_whitelist isem : archModel.nc ∅ :=
  Ax.to_archModel_nc isem (axmodel regs_whitelist).
