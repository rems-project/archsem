(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aarhus University                                       *)
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

Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.GRel.
Require Import ASCommon.FMon.
Require Import RiscVInst.
Require Import GenAxiomaticRiscV.

(** This is an implementation of the RISC-V user-mode Axiomatic model. It does
    not support mixed-size accesses. *)
Section UMRiscV.
  Import Candidate.
  Context (regs_whitelist : gset reg).
  Context {nmth : nat}.
  Context (cd : Candidate.t NMS nmth).

  (** * Arm standard notations *)
  Import AxRiscVNames.

  (** ** Thread relations *)
  Notation pe := (pre_exec cd).
  Notation int := (same_thread pe).
  Notation si := (same_instruction_instance cd).
  Notation sca := (same_access cd).
  Notation po := (instruction_order pe).
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

  (** ** Barriers *)
  Notation fences a b := (fences a b pe).
  Notation fences_tso := (fences_tso pe).
  Notation fences_i := (fences_i pe).

  (** ** Memory *)
  Notation W := (explicit_writes pe).
  Notation R := (explicit_reads pe).
  Notation M := (mem_explicit pe).
  Notation Wx := (exclusive_writes pe).
  Notation Rx := (exclusive_writes pe).
  Notation X := (mem_exclusive pe).
  Notation RL := (RL cd).
  Notation AQ := (AQ cd).
  Notation RCsc := (mem_rel_acq_rcsc pe).
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


  Notation rsw := (rsw cd).

  Notation irf := (irf cd).
  Notation irfi := (irfi cd).
  Notation irfe := (irfe cd).
  Notation ifr := (ifr cd).
  Notation ifri := (ifri cd).
  Notation ifre := (ifre cd).


  (* End of copy paste section*)


  Definition is_illegal_reg_write (regs : gset reg) :=
    is_reg_writeP (λ reg acc _, reg ∉ regs).
  #[export] Instance is_illegal_reg_write_dec regs ev :
    Decision (is_illegal_reg_write regs ev).
  Proof. unfold_decide. Defined.

  Definition Illegal_RW := collect_all (λ _, is_illegal_reg_write regs_whitelist) cd.

  (** * Fence relation *)

  Definition fenced_acc_set fa :=
    match fa with
    | FA_read => R
    | FA_write => W
    | FA_readwrite => M
    end.

  Definition fence_base :=
    ⋃ (input ←@{list} enum fenced_accesses;
       output ←@{list} enum fenced_accesses;
       [⦗fenced_acc_set input⦘⨾po⨾⦗fences input output⦘⨾po⨾⦗fenced_acc_set output⦘]).

  Definition fence :=
    fence_base
    ∪ ⦗W⦘⨾po⨾⦗fences_tso⦘⨾po⨾⦗W⦘
    ∪ ⦗R⦘⨾po⨾⦗fences_tso⦘⨾po⨾⦗M⦘.

  (** * Preserved program order *)

  Definition po_loc := po ∩ same_addr cd.
  Definition po_loc_no_w := po_loc ∖ (po_loc⨾⦗W⦘⨾po_loc).

  Definition ppo :=
    ⦗M⦘⨾po_loc⨾⦗W⦘ (* r1 *)
    ∪ (⦗R⦘⨾po_loc_no_w⨾⦗R⦘)∖rsw (* r2 *)
    ∪ ⦗grel_rng rmw ∪ Wx⦘⨾rfi⨾⦗R⦘ (* r3 *)
    ∪ fence (* r4 *)
    ∪ ⦗AQ⦘⨾po⨾⦗M⦘ (* r5 *)
    ∪ ⦗M⦘⨾po⨾⦗RL⦘ (* r6 *)
    ∪ ⦗RCsc⦘⨾po⨾⦗RCsc⦘ (* r7 *)
    ∪ rmw (* r8 *)
    ∪ ⦗M⦘⨾addr⨾⦗M⦘ (* r9 *)
    ∪ ⦗M⦘⨾data⨾⦗W⦘ (* r10 *)
    ∪ ⦗M⦘⨾ctrl⨾⦗W⦘ (* r11 *)
    ∪ ⦗M⦘⨾(addr ∪ data)⨾⦗W⦘⨾rfi⨾⦗R⦘ (* r12 *)
    ∪ ⦗M⦘⨾addr⨾⦗M⦘⨾po⨾⦗W⦘ (* r13 *).

  (* TODO This does not distinguishes UB conditions from invalid conditions. *)
  Record consistent := {
      memory_coherence : grel_acyclic (co ∪ rf ∪ fr ∪ po_loc);
      register_coherence : reg_coherence cd;
      main_model : grel_acyclic (co ∪ rfe ∪ fr ∪ ppo);
      atomic : (rmw ∩ (fre⨾ coe)) = ∅;
    }.
  #[export] Instance consistent_dec : Decision consistent := ltac:(decide_record).

  Record not_UB := {
      initial_reads : IF ⊆ IR;
      initial_reads_not_delayed : IF ## grel_rng (coherence cd);
      register_write_permitted : Illegal_RW = ∅;
      memory_events_permitted : (mem_events cd) ⊆ M ∪ IF;
      is_nms' : is_nms cd;
    }.
  #[export] Instance not_UB_dec : Decision not_UB := ltac:(decide_record).

  Definition consistent_ok := consistent ∧ not_UB.
  #[export] Instance consistent_ok_dec : Decision consistent_ok := ltac:(unfold_decide).

End UMRiscV.

Require Import ASCommon.CResult.

(** The User RISC-V axiomatic model *)
Definition axmodel regs_whitelist : Ax.t Candidate.NMS ∅ :=
  λ _ cd, if decide (consistent cd) then
            if decide (not_UB regs_whitelist cd) then Ok Ax.Allowed
            else Error ""
          else Ok Ax.Rejected.

(** The User RISC-V architecture model *)
Definition archmodel regs_whitelist isem : Model.nc ∅ :=
  Ax.to_Modelnc isem (axmodel regs_whitelist).
