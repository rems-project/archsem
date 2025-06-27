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

Require Import Strings.String.

From stdpp Require Import decidable.

Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.GRel.

Require Import ASCommon.FMon.
Require Import ArmInst.
Require Import GenAxiomaticArm.
Require UMArm.
Module UM := UMArm.
Require VMSA22Arm.
Module VMSA := VMSA22Arm.

Import Interface.
Import Candidate.
Import AxArmNames.


Definition ISA_trans_can_fail (isem : iMon ()) :=
  ∀ lt : list iEvent,
  cmatch isem (lt, FTERet ()) →
  ∀ i ev,
  lt !! i = Some ev →
  is_mem_read_kindP is_ttw ev →
  ∃ j acc v, (i < j)%nat ∧ lt !! j = Some (RegWrite pc_reg acc v &→ ()).

Section Phase1.
  (** Unfold relational equality [r = s] into [∀ x y, (x, y) ∈ r ↔ (x, y) ∈ s]
      instead of a single value *)
  Import SetUnfoldPair.

  (** Do set unfolding of [x ∈ S] in cdestruct automatically *)
  Import CDestrUnfoldElemOf.

  (** Take the candidate as a parameter *)
  Variable nmth : nat.
  Variable cd : Candidate.t NMS nmth.

  (** * Arm standard notations *)

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
  Notation Rx := (exclusive_reads pe).
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

  Notation T_f := (T_f cd).

  (** ** Theorem parameters hypotheses *)

  (** The first parameter is the candidate execution [cd] and was already
      declared for the notations *)

  (** Those are the registers that can be written, the theorem is generic over
      them, suprisingly, no hypotheses on them were required *)
  Variable regs_whitelist : gset reg.

  (** The candidate must we wellformed *)
  Hypothesis cd_wf: wf cd.
  Hypothesis cd_complete : ISA_complete cd.

  (** We also take an instruction semantic [isem] as a parameter that must
      accept the candidate execution *)
  Variable isem : iMon ().
  Hypothesis cd_isem_match : ISA_match cd isem.

  (** This instruction semantic must have the property that any translation is
      followed by a PC write, in other-words, an instruction cannot commit on
      not taking an exception before finishing all translations. *)
  Hypothesis isem_trans_can_fail : ISA_trans_can_fail isem.

  (** In addition we require that translation read from initial memory *)
  Hypothesis initial_TTW_reads : T ⊆ init_mem_reads cd.
  Hypothesis TTW_reads_not_delayed : T ## grel_rng (coherence cd).

  (** And we require that there is no fault, TLBIs or MSRs, those can be deduce
      from a more high-level hypotheses such that "pure EL0 execution" later. *)
  Hypothesis no_exceptions : TE ∪ ERET = ∅.
  Hypothesis no_tf : T_f = ∅.
  Hypothesis no_tlbi : TLBI = ∅.
  Hypothesis no_msr : MSR = ∅.



  (** ** Boiler-plate lemmas *)


  Instance TE_obv_false x : ObvFalse (x ∈ TE).
  Proof using no_exceptions. clear - no_exceptions. tcclean. set_solver. Qed.
  Instance ERET_obv_false x : ObvFalse (x ∈ ERET).
  Proof using no_exceptions. clear - no_exceptions. tcclean. set_solver. Qed.
  Instance TLBI_obv_false x : ObvFalse (x ∈ TLBI).
  Proof using no_tlbi. clear - no_tlbi. tcclean. set_solver. Qed.
  Instance MSR_obv_false x : ObvFalse (x ∈ MSR).
  Proof using no_msr. clear - no_msr. tcclean. set_solver. Qed.
  Instance T_f_obv_false x : ObvFalse (x ∈ T_f).
  Proof using no_tf. clear - no_tf. tcclean. set_solver. Qed.

  Instance ContextChange_obv_false x : ObvFalse (x ∈ VMSA.ContextChange cd).
  Proof using no_msr no_exceptions.
    tcclean. unfold VMSA.ContextChange.
    cdestruct |- ** # CDestrSplitGoal.
  Qed.

  (** Since Translations read from initial memory, all trf related relations are
      empty *)
  Lemma trf_empty : trf = ∅.
  Proof using initial_TTW_reads.
    clear - initial_TTW_reads.
    unfold trf, init_mem_reads in *.
    set_solver.
  Qed.
  Instance trf_obv_false x : ObvFalse (x ∈ trf).
  Proof using initial_TTW_reads.
    clear - initial_TTW_reads.
    tcclean. destruct x. set_solver ## trf_empty.
  Qed.
  Instance trfi_obv_false x : ObvFalse (x ∈ trfi).
  Proof using initial_TTW_reads.
    clear - initial_TTW_reads.
    tcclean. destruct x. unfold trfi. set_solver ## trf_empty.
  Qed.
  Instance trfe_obv_false x : ObvFalse (x ∈ trfe).
  Proof using initial_TTW_reads.
    clear - initial_TTW_reads.
    tcclean. destruct x. unfold trfe. set_solver ## trf_empty.
  Qed.

  (** ** Equivalence proofs *)

  Lemma UM_VMSA_obs : VMSA.obs cd = UM.obs cd.
  Proof using initial_TTW_reads.
    clear - initial_TTW_reads.
    unfold VMSA.obs, UM.obs, trfe, VMSA.wco.
    set_solver ##trf_empty.
  Qed.
  Lemma UM_VMSA_aob : VMSA.aob cd = UM.aob cd.
  Proof. reflexivity. Qed.


  #[global] Hint Constants Opaque : rewrite.
  (** ** T;instruction_order in ctrl *)
  Lemma T_iio_pc_write : ∀ x ∈ T, ∃ y ∈ (pc_writes cd), (x, y) ∈ iio.
  Proof using cd_isem_match cd_complete isem_trans_can_fail.
    intros teid Ht.
    unfold T, reads_by_kind in Ht.
    cdestruct Ht.
    destruct teid as [tid iid ieid byte].
    unfold lookup, lookup_eid_pre, lookup_iEvent in H.
    cdestruct byte, H as tr tre ?? # CDestrEqOpt.
    opose proof* ISA_complete_use; [eassumption .. | deintro; cdestruct tre |- ?].
    opose proof* ISA_match_use as Hc; [eassumption .. |].
    opose proof* (isem_trans_can_fail _ Hc ieid) as H'; [eassumption .. |].
    cdestruct H'.
    exists (EID.make tid iid x None).
    unfold pc_writes. apply set_unfold_2 # UnfoldEidRels.
    unfold is_Some,lookup,lookup_eid_pre, lookup_iEvent.
    repeat setoid_rewrite eq_some_unfold.
    sauto lq:on rew:off.
  Qed.

  Lemma T_instruction_order_ctrl : ⦗T⦘⨾instruction_order ⊆ ctrl.
  Proof using cd_isem_match cd_complete isem_trans_can_fail.
    clear - cd_isem_match cd_complete isem_trans_can_fail.
    apply set_unfold_2. cbn.
    cdestruct |- ** as x y HT ?.
    specialize (T_iio_pc_write _ HT) as H'.
    cdestruct H' as z??.
    assert (x ∈ mem_reads pe). {
      revert HT. clear. unfold T, reads_by_kind, mem_reads.
      set_unfold. cdestruct |- **. naive_solver. }
    assert ((z, y) ∈ instruction_order). {
      set_unfold # UnfoldEidRels. intuition lia. }
    unfold ctrl. set_solver.
  Qed.

  Section NoCacheOp_implies_ob1_equal.

    Hypothesis (NoCacheOp : C = ∅).

    Instance C_obv_false x : ObvFalse (x ∈ C).
    Proof using NoCacheOp. clear - NoCacheOp. tcclean. set_solver. Qed.

    Lemma UM_to_VMSA_dob : VMSA.dob cd ⊆ UM.dob cd ∪ ⦗T⦘⨾instruction_order.
    Proof using initial_TTW_reads.
      clear - initial_TTW_reads.
      unfold VMSA.dob, UM.dob, VMSA.speculative, UM.speculative, trfi in *.
      set_solver ## trf_empty.
    Qed.

    Lemma UM_to_VMSA_bob : VMSA.bob cd = UM.bob cd.
    Proof using NoCacheOp no_msr no_exceptions.
      clear -NoCacheOp no_msr no_exceptions.
      unfold VMSA.bob, UM.bob. set_solver.
    Qed.

    Lemma VMSA_tob_empty : VMSA.tob cd = ∅.
    Proof using initial_TTW_reads no_tf.
      clear - initial_TTW_reads no_tf.
      unfold VMSA.tob, trfi.
      set_solver ## trf_empty.
    Qed.

    Instance VMSA_tob_obv_false x : ObvFalse (x ∈ VMSA.tob cd).
    Proof using initial_TTW_reads no_tf.
      clear - initial_TTW_reads no_tf.
      tcclean. destruct x. set_solver ## VMSA_tob_empty.
    Qed.

    Lemma VMSA_TLBIS1_empty : VMSA.TLBI_S1 cd = ∅.
    Proof using no_tlbi.
      clear - no_tlbi.
      unfold TLBI, VMSA.TLBI_S1 in *.
      set_unfold.
      unfold VMSA.has_tlbi_op.
      setoid_rewrite is_tlbopP_spec.
      setoid_rewrite is_tlbopP_spec in no_tlbi.
      naive_solver.
    Qed.

    Lemma VMSA_TLBIS2_empty : VMSA.TLBI_S2 cd = ∅.
    Proof using no_tlbi.
      clear - no_tlbi.
      unfold TLBI, VMSA.TLBI_S2 in *.
      set_unfold.
      unfold VMSA.has_tlbi_op.
      setoid_rewrite is_tlbopP_spec.
      setoid_rewrite is_tlbopP_spec in no_tlbi.
      naive_solver.
    Qed.

    Lemma VMSA_obtlbi_translate_empty : VMSA.obtlbi_translate cd = ∅.
    Proof using no_tlbi.
      clear - no_tlbi.
      unfold VMSA.obtlbi_translate.
      set_solver ## VMSA_TLBIS1_empty ##VMSA_TLBIS2_empty.
    Qed.

    Lemma VMSA_obtlbi_empty : VMSA.obtlbi cd = ∅.
    Proof using no_tlbi.
      clear - no_tlbi.
      unfold VMSA.obtlbi.
      set_solver ## VMSA_obtlbi_translate_empty.
    Qed.

    Instance VMSA_obtlbi_obv_false x : ObvFalse (x ∈ VMSA.obtlbi cd).
    Proof using no_tlbi.
      clear - no_tlbi.
      tcclean. destruct x. set_solver ## VMSA_obtlbi_empty.
    Qed.

    Lemma UM_to_VM_speculative : UM.speculative cd = VMSA.speculative cd.
    Proof using cd_isem_match cd_complete isem_trans_can_fail.
      clear - cd_isem_match cd_complete isem_trans_can_fail.
      unfold UM.speculative, VMSA.speculative.
      set_solver ## T_instruction_order_ctrl.
    Qed.

    Lemma VMSA_ctxob_simpl :
      VMSA.ctxob cd ⊆ UM.dob cd ∪ UM.bob cd.
    Proof using no_msr no_exceptions cd_isem_match cd_complete isem_trans_can_fail.
      clear - no_msr no_exceptions cd_isem_match cd_complete isem_trans_can_fail.
      unfold VMSA.ctxob, VMSA.CSE, VMSA.ContextChange,
        UM.dob, UM.bob.
      rewrite <- UM_to_VM_speculative.
      set_solver.
    Qed.

    Lemma VMSA_Fault_T_empty : VMSA.Fault_T cd = ∅.
    Proof using no_exceptions.
      clear - no_exceptions.
      unfold VMSA.Fault_T, TE in *.
      set_unfold.
      setoid_rewrite is_take_exceptionP_spec in no_exceptions.
      setoid_rewrite VMSA.is_faultP_spec.
      naive_solver.
    Qed.

    Lemma VMSA_obfault_empty : VMSA.obfault cd = ∅.
    Proof using no_exceptions.
      clear - no_exceptions.
      unfold VMSA.obfault.
      set_solver ## VMSA_Fault_T_empty.
    Qed.

    Instance VMSA_obfault_obv_false x : ObvFalse (x ∈ VMSA.obfault cd).
    Proof using no_exceptions.
      clear - no_exceptions.
      tcclean. destruct x. set_solver ## VMSA_obfault_empty.
    Qed.

    Lemma VMSA_obETS_empty : VMSA.obETS cd = ∅.
    Proof using no_exceptions no_tlbi.
      clear - no_exceptions no_tlbi.
      unfold VMSA.obETS.
      set_solver ## VMSA_obfault_empty.
    Qed.

    Instance VMSA_obETS_obv_false x : ObvFalse (x ∈ VMSA.obETS cd).
    Proof using no_exceptions no_tlbi.
      clear - no_exceptions no_tlbi.
      tcclean. destruct x. set_solver ## VMSA_obETS_empty.
    Qed.

    Lemma VMSA_UM_ob1 : VMSA.ob1 cd = UM.ob1 cd.
    Proof using NoCacheOp no_tlbi no_tf no_msr no_exceptions initial_TTW_reads
      isem_trans_can_fail cd_complete cd_isem_match.
      apply set_unfold_2.
      intros x y.
      unfold VMSA.ob1, VMSA.dob, VMSA.bob, VMSA.ctxob, VMSA.CSE,
        UM.ob1, UM.dob, UM.bob.
      rewrite UM_VMSA_obs, UM_VMSA_aob, UM_to_VM_speculative.
      apply set_unfold_2.
      split.
      all: cdestruct |- ** # CDestrSplitGoal.
      all: cbn.
      all: hauto lq:on rew:off.
      (* alternative *)
      (* all: try (repeat (split || eexists || (left + right)); eassumption). *)
    Qed.

    Lemma VMSA_UM_ob : VMSA.ob cd = UM.ob cd.
    Proof using NoCacheOp no_tlbi no_tf no_msr no_exceptions initial_TTW_reads
      isem_trans_can_fail cd_complete cd_isem_match.
      unfold VMSA.ob, UM.ob. f_equal. exact VMSA_UM_ob1.
    Qed.

  End NoCacheOp_implies_ob1_equal.

  Theorem VMUM_phase1:
    UM.consistent regs_whitelist cd ↔ VMSA.consistent regs_whitelist cd.
    split; intros []; split.
    all: try (rewrite VMSA_UM_ob in *).
    all: try (apply set_unfold_2; solve [cdestruct |- **]).
    all: try (try unfold C in *; set_solver).
  Qed.

End Phase1.



