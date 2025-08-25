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

Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.GRel.
Require Import ASCommon.FMon.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import RiscVInst.

(** * Definition of barriers categories and barrier sets

      This section defines the event sets of RISC-V barrier and the corresponding
      classification.

      This development assumes that all hardware threads are in the same inner
      shareability domain, therefore we identify barriers that are:
      - Full system
      - Outer shareable
      - Inner shareable
      This might need to change when considering device interaction later *)
Section Barriers.
  Import Candidate.
  Context {et : exec_type} {nmth : nat}.
  Implicit Type cd : (pre et nmth).
  Implicit Type b : barrier.
  #[local] Hint Extern 10 (Decision (?x _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _ _)) => unfold x : typeclass_instances.

  Inductive fenced_accesses := FA_read | FA_write | FA_readwrite.
  #[export] Instance fenced_accesses_eq_dec : EqDecision fenced_accesses.
  (* Import ListNotations. *)
  Proof. solve_decision. Defined.
  #[export, refine] Instance fenced_accesses_fin : Finite fenced_accesses := { enum := _}.
  Proof.
    all:clear et.
    - exact [FA_read ; FA_write ; FA_readwrite].
    - sauto q:on.
    - sauto lq:on.
  Qed.

  Definition fence_from (input output : fenced_accesses) : barrier_kind :=
    match input, output with
    | FA_read, FA_read => Barrier_RISCV_r_r
    | FA_read, FA_write => Barrier_RISCV_r_w
    | FA_read, FA_readwrite => Barrier_RISCV_r_rw
    | FA_write, FA_read => Barrier_RISCV_w_r
    | FA_write, FA_write => Barrier_RISCV_w_w
    | FA_write, FA_readwrite => Barrier_RISCV_w_rw
    | FA_readwrite, FA_read => Barrier_RISCV_rw_r
    | FA_readwrite, FA_write => Barrier_RISCV_rw_w
    | FA_readwrite, FA_readwrite => Barrier_RISCV_rw_rw
    end.

  Definition fences (input output : fenced_accesses) cd :=
    collect_all (λ _, is_barrierP (.= fence_from input output)) cd.

  Definition fences_tso cd :=
    collect_all (λ _, is_barrierP (.= Barrier_RISCV_tso)) cd.

  Definition fences_i cd :=
    collect_all (λ _, is_barrierP (.= Barrier_RISCV_i)) cd.

End Barriers.


(** * Standard names and definitions for RISC-V axiomatic models *)
Module AxRiscVNames.
  Import Candidate.
  Section RiscVNames.

  Context {et : exec_type} {nmth : nat}.
  Context `(cd : t et nmth).

  (** ** Thread relations *)
  Notation pe := (pre_exec cd).
  Notation int := (same_thread pe).
  Notation si := (same_instruction_instance cd).
  Notation sca := (same_access cd).
  Notation po := (instruction_order pe).
  Notation full_instruction_order := (full_instruction_order pe).
  Notation iio := (iio pe).

  (** ** Registers *)
  Notation RR := (reg_reads pe).
  Notation RW := (reg_writes pe).
  Definition RE := RR ∪ RW.
  Notation rrf := (reg_reads_from cd).
  Notation rfr := (reg_from_reads cd).

  (** ** Memory *)
  Notation W := (explicit_writes pe).
  Notation R := (explicit_reads pe).
  Notation M := (mem_explicit pe).
  Notation Wx := (exclusive_writes pe).
  Notation Rx := (exclusive_writes pe).
  Notation X := (mem_exclusive pe).
  Definition RL := (rel_acq_rcpc_writes pe) ∪ (rel_acq_rcsc_writes pe).
  Definition AQ := (rel_acq_rcpc_reads pe) ∪ (rel_acq_rcsc_reads pe).
  Notation RCsc := (mem_rel_acq_rcsc pe).
  Notation IF := (ifetch_reads pe).
  Notation IR := (init_mem_reads cd).

  Notation lxsx := (lxsx cd).
  Notation amo := (atomic_update cd).
  Definition rmw := lxsx ∪ amo.

  (* Not necessarily transitive in mixed-size contexts *)
  Definition co := ⦗W⦘⨾coherence cd⨾⦗W⦘ ∩ overlapping cd.
  Definition coi := co ∩ int.
  Definition coe := co ∖ coi.

  Definition rf := reads_from cd⨾⦗R⦘.
  Definition rfi := rf ∩ int.
  Definition rfe := rf ∖ rfi.
  Definition fr := ⦗R⦘⨾from_reads cd.
  Definition fri := fr ∩ int.
  Definition fre := fr ∖ fri.

  (** Reading same write *)
  Definition rsw := (rf ⁻¹⨾rf).

  Definition irf := reads_from cd⨾⦗IF⦘.
  Definition irfi := irf ∩ int.
  Definition irfe := irf ∖ rfi.
  Definition ifr := ⦗IF⦘⨾from_reads cd.
  Definition ifri := ifr ∩ int.
  Definition ifre := ifr ∖ fri.

  (** ** Internal coherence *)

  Record reg_coherence := {
      rrf_internal : rrf ⊆ full_instruction_order;
      rfr_internal : rfr ⊆ not_after cd
    }.
  #[export] Instance reg_coherence_dec : Decision reg_coherence := ltac:(decide_record).
  End RiscVNames.
End AxRiscVNames.
