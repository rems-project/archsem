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
Require Import ArmInst.

(* NOTE: TODO change this.
 This file defines the VMSA and User Arm axiomatic models. It starts with some
 common definitions (in section common_def), followed by module GenArm which
 contains a candidate cd, an inital memory map init_mem, with preliminary common
 wellformedness conditions. Finally, the two modules VMSA and UM contain the two
 models and their specific wellformedness conditions respectively. There are no
 dependencies between the two models.
 *)


(** * Definition of barriers categories and barrier sets

      This section defines the event sets of Arm barrier and the corresponding
      classification. For now only dmbs, dsbs and isbs are supported.

      This development assumes that all hardware threads are in the same inner
      shareability domain, therefore we identify barriers that are:
      - Full system
      - Outer shareable
      - Inner shareable
      This might need to change when considering device interaction later *)
Section Barriers.
  Import Candidate.
  Context {et : exec_type} {nmth : nat}.
  Implicit Type cd : (t et nmth).
  Implicit Type b : barrier.
  #[local] Hint Extern 10 (Decision (?x _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _ _)) => unfold x : typeclass_instances.


  Definition is_isb b := if b is Barrier_ISB _ then True else False.
  Definition isb cd := collect_all (λ _, is_barrierP is_isb) cd.

  Definition is_dsbP (P : MBReqTypes → Prop) b :=
    if b is Barrier_DSB dxb
    then dxb.(DxB_domain) ≠ MBReqDomain_Nonshareable ∧ P dxb.(DxB_types)
    else False.
  Definition is_dsb := is_dsbP (λ _, True).
  Definition is_dsbT t := is_dsbP (.=t).

  Definition is_dsbnshP (P : MBReqTypes → Prop) b :=
    if b is Barrier_DSB dxb
    then dxb.(DxB_domain) = MBReqDomain_Nonshareable ∧ P dxb.(DxB_types)
    else False.
  Definition is_dsbnsh := is_dsbnshP (λ _, True).
  Definition is_dsbnshT t := is_dsbnshP (.=t).

  Definition dsbsy cd :=
    collect_all (λ _, is_barrierP (is_dsbT MBReqTypes_All)) cd.
  Definition dsbst cd :=
    collect_all (λ _, is_barrierP (is_dsbT MBReqTypes_Writes)) cd.
  Definition dsbld cd :=
    collect_all (λ _, is_barrierP (is_dsbT MBReqTypes_Reads)) cd.
  Definition dsb cd := collect_all (λ _, is_barrierP is_dsb) cd.
  Definition dsbnshsy cd :=
    collect_all (λ _, is_barrierP (is_dsbnshT MBReqTypes_All)) cd.
  Definition dsbnshst cd :=
    collect_all (λ _, is_barrierP (is_dsbnshT MBReqTypes_Writes)) cd.
  Definition dsbnshld cd :=
    collect_all (λ _, is_barrierP (is_dsbnshT MBReqTypes_Reads)) cd.
  Definition dsbnsh cd := collect_all (λ _, is_barrierP is_dsbnsh) cd.

  Definition is_dmbP (P : MBReqTypes → Prop) b :=
    if b is Barrier_DMB dxb
    then dxb.(DxB_domain) ≠ MBReqDomain_Nonshareable ∧ P dxb.(DxB_types)
    else False.
  Definition is_dmb := is_dmbP (λ _, True).
  Definition is_dmbT t := is_dmbP (.=t).

  Definition is_dmbnshP (P : MBReqTypes → Prop) b :=
    if b is Barrier_DMB dxb
    then dxb.(DxB_domain) = MBReqDomain_Nonshareable ∧ P dxb.(DxB_types)
    else False.
  Definition is_dmbnsh := is_dmbnshP (λ _, True).
  Definition is_dmbnshT t := is_dmbnshP (.=t).

  Definition dmbsy cd :=
    collect_all (λ _, is_barrierP (is_dmbT MBReqTypes_All)) cd.
  Definition dmbst cd :=
    collect_all (λ _, is_barrierP (is_dmbT MBReqTypes_Writes)) cd.
  Definition dmbld cd :=
    collect_all (λ _, is_barrierP (is_dmbT MBReqTypes_Reads)) cd.
  Definition dmb cd := collect_all (λ _, is_barrierP is_dmb) cd.
  Definition dmbnshsy cd :=
    collect_all (λ _, is_barrierP (is_dmbnshT MBReqTypes_All)) cd.
  Definition dmbnshst cd :=
    collect_all (λ _, is_barrierP (is_dmbnshT MBReqTypes_Writes)) cd.
  Definition dmbnshld cd :=
    collect_all (λ _, is_barrierP (is_dmbnshT MBReqTypes_Reads)) cd.
  Definition dmbnsh cd := collect_all (λ _, is_barrierP is_dmbnsh) cd.

  (** ** Cumulated barriers

      Each of those set collect all barrier that are stronger than the set name *)

  Definition dsb_full cd := dsbsy cd.
  Definition dsb_load cd := dsbld cd ∪ dsbsy cd.
  Definition dsb_store cd := dsbst cd ∪ dsbsy cd.
  Definition dmb_full cd := dmbsy cd ∪ dsbsy cd.
  Definition dmb_load cd := dmbld cd ∪ dmbsy cd ∪ dsb_load cd.
  Definition dmb_store cd := dmbst cd ∪ dmbsy cd ∪ dsb_store cd.

End Barriers.


(** * Standard names and definitions for Arm axiomatic models *)
Module AxArmNames.
  Import Candidate.
  Section ArmNames.

  Context {et : exec_type} {nmth : nat}.
  Context `(cd : t et nmth).

  (** ** Thread relations *)
  Notation pe := (pre_exec cd).
  Notation int := (same_thread pe).
  Notation si := (same_instruction_instance cd).
  Notation sca := (same_access cd).
  Notation instruction_order := (instruction_order pe).
  Notation full_instruction_order := (full_instruction_order pe).
  Notation iio := (iio pe).

  (** ** Registers *)
  Notation RR := (reg_reads pe).
  Notation RW := (reg_writes pe).
  Definition RE := RR ∪ RW.
  Notation rrf := (reg_reads_from cd).
  Notation rfr := (reg_from_reads cd).

  Definition is_msr := is_reg_writeP (λ _ o _, is_Some o).
  #[export] Typeclasses Transparent is_msr.
  Definition MSR := collect_all (λ _, is_msr) cd.
  Definition is_mrs := is_reg_readP (λ _ o _, is_Some o).
  #[export] Typeclasses Transparent is_mrs.
  Definition MRS := collect_all (λ _, is_mrs) cd.

  (** ** Barriers *)
  Notation F := (barriers cd).
  Notation ISB := (isb cd).

  (** ** Memory *)
  Notation W := (explicit_writes pe).
  Notation R := (explicit_reads pe).
  Notation M := (mem_explicit pe).
  Notation Wx := (exclusive_writes pe).
  Notation Rx := (exclusive_writes pe).
  Notation L := (rel_acq_writes pe).
  Notation A := (rel_acq_reads pe).
  Notation Q := (acq_rcpc_reads pe).
  Notation T := (ttw_reads pe).
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

  Definition frf := fr⨾rf ∩ overlapping cd.
  Definition frfi := frf ∩ int.

  Definition trf := reads_from cd⨾⦗T⦘.
  Definition trfi := trf ∩ int.
  Definition trfe := trf ∖ rfi.
  Definition tfr := ⦗T⦘⨾from_reads cd.
  Definition tfri := tfr ∩ int.
  Definition tfre := tfr ∖ fri.

  Definition irf := reads_from cd⨾⦗IF⦘.
  Definition irfi := irf ∩ int.
  Definition irfe := irf ∖ rfi.
  Definition ifr := ⦗IF⦘⨾from_reads cd.
  Definition ifri := ifr ∩ int.
  Definition ifre := ifr ∖ fri.



  (** ** Caches *)
  Definition ICDC := collect_all (λ _ ev, is_cacheop ev) cd.
  Definition TLBI := collect_all (λ _ ev, is_tlbop ev) cd.
  Definition C := ICDC ∪ TLBI.

  (** ** Exceptions *)

  Definition TE := collect_all (λ _ event, is_take_exception event) cd.
  Definition ERET := collect_all (λ _ event, is_return_exception event) cd.

  (** ** Explicit events *)

  (** Explicit events are events that are the "main" event of an instruction

      TODO: TE and ERET ? *)
  Definition Exp := MRS ∪ MSR ∪ M ∪ F ∪ C.

  Definition po := ⦗Exp⦘⨾instruction_order⨾⦗Exp⦘.

  (* A MemRead with ttw and value 0 *)
  Definition is_translation_read_fault :=
    is_mem_readP (λ n rr val _, is_ttw rr.(ReadReq.access_kind) ∧ bv_extract 0 1 val = 0%bv).
  #[export] Instance is_translation_read_fault_dec ev :
    Decision (is_translation_read_fault ev).
  Proof. unfold_decide. Defined.

  (* translation-common.cat#L10 *)
  Definition T_f := collect_all (λ _ event, is_translation_read_fault event) cd.
  Typeclasses Opaque T_f.

  Lemma T_f_in_T : T_f ⊆ T.
  Proof.
    unfold T_f, T, ttw_reads, reads_by_kind.
    set_unfold. unfold is_mem_read_kindP.
    setoid_rewrite is_mem_readP_spec.
    naive_solver.
  Qed.


  (** ** Internal coherence *)

  (** Statement of internal for explicit memory accesses. This ignores the
  existence of implicit writes as none of our model allows them for now *)
  Record exp_internal := {
      rfi_internal : rfi ⊆ not_after cd; (* CoRW1: important, rfi not in ob *)
      coi_internal : coi ⊆ not_after cd; (* CoWW: Also in ob via lws ∪ co*)
      fri_internal : fri ⊆ not_after cd; (* CoWR0: Also in ob via lrs ∪ fr*)
      frfi_internal : frfi ⊆ not_after cd; (* CoRR: important R;po-loc;R not in ob *)
      (* CoRW2: not here as implied by ob (with co⨾rfe⨾lws) *)
    }.

  Record reg_internal := {
      rrf_internal : rrf ⊆ full_instruction_order;
      rfr_internal : rfr ⊆ not_after cd
    }.


  End ArmNames.
End AxArmNames.
