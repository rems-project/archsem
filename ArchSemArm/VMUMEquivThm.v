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

From ASCommon Require Import Options.
From ASCommon Require Import Common GRel FMon.

Require Import ArmInst.

(* Re-import needed otherwise filter gets shadowed *)
From stdpp Require Import base vector.

Require Import GenAxiomaticArm.

Require UMArm.
Module UM := UMArm.
Require VMSA22Arm.
Module VMSA := VMSA22Arm.

Import Interface.
Import Candidate.
Import AxArmNames.

Require Import ASCommon.CResult.


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

  (** In addition we require that translation read from initial memory *)
  Hypothesis initial_TTW_reads : T ⊆ init_mem_reads cd.

  (** Technically the model could require co to only contain write and TLBIs and
  still state the same things (that's what other models outside ArchSem do),
  however being more generic is useful, up to a point. In particular we can't
  allow translation to be delayed by coherence, but we also don't expect any
  models in the future that would require TTW reads to be in coherence. *)
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
    Proof using  cd_complete.
      clear - cd_complete.
      unfold UM.speculative, VMSA.speculative.
      set_solver.
    Qed.

    Lemma VMSA_ctxob_simpl :
      VMSA.ctxob cd ⊆ UM.dob cd ∪ UM.bob cd.
    Proof using no_msr no_exceptions cd_complete.
      clear - no_msr no_exceptions cd_complete.
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
      cd_complete.
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
      cd_complete.
      unfold VMSA.ob, UM.ob. f_equal. exact VMSA_UM_ob1.
    Qed.

  End NoCacheOp_implies_ob1_equal.

  Theorem VMUM_phase1:
    UM.consistent_ok regs_whitelist cd ↔ VMSA.consistent_ok regs_whitelist cd.
  Proof using TTW_reads_not_delayed cd_complete cd_wf initial_TTW_reads
              no_exceptions no_msr no_tf no_tlbi.
    split; intros [[] []]; split; split.
    all: try (rewrite VMSA_UM_ob in *).
    all: try (apply set_unfold_2; solve [cdestruct |- **]).
    all: try (try unfold C in *; set_solver).
  Qed.

End Phase1.

(** * Phase 2

    In Phase 2 we want to prove that the user-mode model based on physical
    addresses (with constant page-tables) does not create more unwanted
    behaviours than the user-mode model based on virtual addresses (with no
    translation). This require "Importing" a few ISA model properties from
    Isabelle as axioms. *)

(** ** ISA traces manipulation functions

    Those function must match exactly the Isabelle definition since Axioms
    proven in Isabelle depend on those. *)

Record trace_erasure_state :=
  { last_translation_info : option TranslationStartInfo;
    last_translation_result : option AddressDescriptor;
    inside_translation : bool;
    (* translation_error : bool; *)
  }.
#[global] Instance tes_eta : Settable _ :=
  settable! Build_trace_erasure_state
  <last_translation_info; last_translation_result;
    inside_translation>.

Definition initial_tes :=
  {|last_translation_info := None;
    last_translation_result := None;
    inside_translation := false;
    (* translation_error := false; *)
  |}.

Definition reconstruct_translated_va (tes : trace_erasure_state) (pa : bv 56) :
    option (bv 64) :=
  match tes.(last_translation_info), tes.(last_translation_result) with
  | Some tsi, Some desc =>
      let result_pa := FullAddress_address (AddressDescriptor_paddress desc) in
      let offset := (pa - result_pa)%bv in
      let orig_va := TranslationStartInfo_va tsi in
      Some (orig_va + bv_sign_extend 64 offset)%bv
  | _,_=> None
  end.

(* Definition erase_mem_request (tes : trace_erasure_state) *)
(*     (rr : MemReq.t) : option (MemReq.t) := *)
(*   if reconstruct_translated_va tes rr.(MemReq.address) is Some va then *)
(*     rr *)
(*       |> setv MemReq.address (bv_extract 0 56 va) *)
(*       |> setv MemReq.address_space PAS_NonSecure *)
(*       |> Some *)
(*   else None. *)

Section ArmTranslationErasure.

  Variant erasure_result :=
  | Keep (tes : trace_erasure_state) (ev : iEvent)
  | Drop (tes : trace_erasure_state)
  | Error.

  Section EraseIEvent.
    Context (tes : trace_erasure_state).
    Equations erase_iEvent  (ev : iEvent) : erasure_result :=
    | TranslationStart ts &→ () =>
        if inside_translation tes
        then Error
        else
          tes
          |> setv inside_translation true
          |> setv last_translation_info (Some ts)
          |> setv last_translation_result None
          |> Drop
    | TranslationEnd res &→ () =>
        if decide (inside_translation tes ∧ last_translation_info tes ≠ None)
        then
          tes
          |> setv inside_translation false
          |> setv last_translation_result (Some res)
          |> Drop
        else Error
    | MemRead mr &→ res =>
        if inside_translation tes then
          if decide (mr.(MemReq.size) = 8%N ∧ mr.(MemReq.num_tag) = 0%N)
          then Drop tes else Error
        else
          if reconstruct_translated_va tes mr.(MemReq.address) is Some va then
            Keep tes (MemRead (setv MemReq.address (bv_extract 0 56 va) mr)
                      &→ res)
          else Error
    | MemWriteAddrAnnounce mr &→ () =>
        if inside_translation tes then Error
        else
          if reconstruct_translated_va tes mr.(MemReq.address) is Some va then
            Keep tes (MemWriteAddrAnnounce
                        (setv MemReq.address (bv_extract 0 56 va) mr)
                      &→ ())
          else Error
    | MemWrite mr val tags &→ res =>
        if inside_translation tes then Error
        else
          if reconstruct_translated_va tes mr.(MemReq.address) is Some va then
            Keep tes (MemWrite
                        (setv MemReq.address (bv_extract 0 56 va) mr)
                        val tags
                      &→ res)
          else Error
    | _ => Error.
  End EraseIEvent.

  Fixpoint trace_erasure_list (tes : trace_erasure_state) (pos : nat)
      (vm : list iEvent) : option (list (iEvent * nat)) :=
    match vm with
    | [] => Some []
    | hd :: tl =>
        match erase_iEvent tes hd with
        | Keep tes' ev => ((ev,pos)::.) <$> trace_erasure_list tes' (S pos) tl
        | Drop tes' => trace_erasure_list tes' (S pos) tl
        | Error => None
        end
    end.

  Definition trace_erasure (vm : iTrace ()) : option (iTrace () * list nat) :=
    let '(vm_list, vm_end) := vm in
    if vm_end is FTEStop _ then None else
      if trace_erasure_list initial_tes 0 vm_list is Some p then
        Some ((p.*1, vm_end), p.*2)
      else None.
End ArmTranslationErasure.

  (* TODO add system register removal *)

Section Phase2.
  Import AxArmNames.

  Notation T := ttw_reads.

  Variable nth : nat.
  Variable vm_isem : iMon ().
  Variable um_isem : iMon ().
  Variable ttw_charac :
    registerMap → memoryMap → bv 48 → option (gset address * option address).

  (** Register that are allowed to change in user mode *)
  Variable user_registers : gset reg.
  (** Register that impact translation, defined in Isabelle *)
  Variable system_registers : gset reg.
  Hypothesis user_system_register_disjoint : user_registers ## system_registers.

  (** This is defined in Isabelle. The would be generated for specific
     configuration (s1ttw params) for both the Lower and Upper region, and the
     union of those contraints would be crammed in this function *)
  Variable config_assms : ∀ r : reg, reg_type r → bool.
  Hypothesis config_assms_ignore_user :
    ∀ r : reg, r ∉ system_registers → ∀ rv : reg_type r, config_assms r rv.

  Import CDestrUnfoldElemOf.

  Definition rm_config_assms (rm : registerMap) : Prop :=
    ∀ r rv, dmap_lookup r rm = Some rv → config_assms r rv.
  #[refine] Instance rm_config_assms_dec rm : Decision (rm_config_assms rm) :=
    dec_if (decide (∀ rrv ∈ dmap_to_list rm, config_assms rrv.T1 rrv.T2)).
  Proof using.
    all: deintro.
    all: clear - rm.
    all: unfold rm_config_assms.
    - abstract (intros Hi r rv H; ospecialize (Hi (existT r rv) _); set_solver).
    - abstract (apply ssrbool.contra_not; set_solver).
  Defined.

  Definition trc_config_assms (trc : iTrace ()) : Prop :=
    ∀ r racc rv, RegRead r racc &→ rv ∈ trc.1 → config_assms r rv.

  Definition is_AT_trans_start :=
    is_trans_startP (λ ts,
        ts.(TranslationStartInfo_accdesc).(AccessDescriptor_acctype) ≠ AccessType_AT).
  Instance is_AT_trans_start_dec ev : Decision (is_AT_trans_start ev).
  Proof. unfold_decide. Defined.

  Definition non_AT_trans_start :=
    is_trans_startP (λ ts,
        ts.(TranslationStartInfo_accdesc).(AccessDescriptor_acctype) = AccessType_AT).
  Instance non_AT_trans_start_dec ev : Decision (non_AT_trans_start ev).
  Proof. unfold_decide. Defined.

  Definition is_faulting_trans_end :=
    is_trans_endP (λ te,
        te.(AddressDescriptor_fault).(FaultRecord_statuscode) ≠ Fault_None).
  Instance is_faulting_trans_end_dec ev : Decision (is_faulting_trans_end ev).
  Proof. unfold_decide. Defined.

  Definition non_faulting_trans_end :=
    is_trans_endP (λ te,
        te.(AddressDescriptor_fault).(FaultRecord_statuscode) = Fault_None).
  Instance non_faulting_trans_end_dec ev : Decision (non_faulting_trans_end ev).
  Proof. unfold_decide. Defined.

  Definition is_abort ev := is_Some (get_abort ev).
  Instance is_abort_dec ev : Decision (is_abort ev).
  Proof. unfold_decide. Defined.

  Definition trc_terminated (trc : iTrace ()) := trc.2 = FTERet ().

  (** All trace properties needed for our unproven assumptions. *)
  Record trc_assms (trc : iTrace()) : Prop := {
      trc_terminated': trc_terminated trc;
      trc_config_assms': trc_config_assms trc;
      trc_no_at : ∀ ev ∈ trc.1, ¬ is_AT_trans_start ev;
      trc_no_fault : ∀ ev ∈ trc.1, ¬ is_take_exception ev;
      trc_no_abort : ∀ ev ∈ trc.1, ¬ is_abort ev;
    }.


  (** ** Unproven assumptions *)

  Definition footprint_in_page {n} (va : bv n) (size : N) :=
    bv_extract 0 12 va = bv_extract 0 12 (va `+Z` Z.of_N size).

  Definition single_page_trans_footprint (trc : iTrace ()) : Prop :=
    ∀ ts,
      TranslationStart ts &→ () ∈ trc.1 →
      (0 ≤ ts.(TranslationStartInfo_size))%Z →
      footprint_in_page
        ts.(TranslationStartInfo_va)
             (Z.to_N ts.(TranslationStartInfo_size)).

  Context (Hsingle_page_trans_footprint :
            ∀ trc, trc_assms trc → cmatch vm_isem trc →
                   single_page_trans_footprint trc).
  Definition non_AT_Tf_implies_fault (trc : iTrace ()) : Prop :=
    ∀ i j ts ttw,
    i < j →
    trc.1 !! i = Some ts →
    non_AT_trans_start ts →
    trc.1 !! j = Some ttw →
    is_translation_read_fault ttw ->
    ∃ k ev, j < k ∧ trc.1 !! k = Some ev ∧ is_take_exception ev.

  Context (Hnon_AT_Tf_implies_fault :
            ∀ trc, trc_assms trc → cmatch vm_isem trc →
                   non_AT_Tf_implies_fault trc).

  (** Defined whether a given subtrace is a translation subtrace *)

  Definition get_trans_subtrace_info (strc : list iEvent) :
    option (trans_start * trans_end) :=
    let te_idx := (length strc) - 1 in
    guard (∀ ev ∈ (drop 1 (take te_idx strc)),
             (¬ is_trans_start ev) ∧ ¬ is_trans_end ev);;
    ts_ev ← strc !! 0;
    ts ← get_trans_start ts_ev;
    te_ev ← strc !! te_idx;
    te ← get_trans_end te_ev;
    Some (ts, te).

  Definition is_trans_subtrace (strc : list iEvent) :=
    is_Some (get_trans_subtrace_info strc).

  (** Defines what a translation subtrace of an instruction trace is *)
  Definition trans_subtrace strc (trc : iTrace ()) : Prop :=
    is_trans_subtrace strc ∧ contig_sublist strc trc.1.

  Definition non_faulting_trans_read_only (trc : iTrace ()) : Prop:=
    ∀ strc,
      trans_subtrace strc trc →
      ∀ ev ∈ strc,
      match ev with
      | RegWrite _ _ _ &→ () => False
      | MemWrite _ _ _ &→ _ => False
      | RegRead r _ &→ _ => r ∈ system_registers
      | _ => True
      end.

  Context (Hnon_faulting_trans_read_only :
            ∀ trc, trc_assms trc → cmatch vm_isem trc →
                   non_faulting_trans_read_only trc).

  Definition trc_TTW_size_8 (trc : iTrace ()) : Prop :=
    ∀ ev ∈ trc.1,
    ∀ mreq,
    get_mem_req ev = Some mreq →
    is_ttw mreq.(MemReq.access_kind) →
    mreq.(MemReq.size) = 8%N.

  Context (HTTW_size_8 :
            ∀ trc, trc_assms trc → cmatch vm_isem trc →
                   trc_TTW_size_8 trc).

  (** ** Isabelle proven properties *)

  Definition trace_read_system_from_regMap (rm : registerMap) (trc : list iEvent) :=
    ∀ ev ∈ trc,
    if ev is RegRead r _ &→ rv then
      r ∈ system_registers → rm !d! r = Some rv
    else True.

  (** This is equivalent to [trace_satisfied_assms] in Isabelle *)
  Record isa_trace_satisfies_assms (rm : registerMap) (trc : iTrace ()) : Prop := {
      trc_assms' :> trc_assms trc;
      trc_TTW_size_8' : trc_TTW_size_8 trc;
      trc_non_faulting_trans_read_only' : non_faulting_trans_read_only trc;
      rm_config_assms' : rm_config_assms rm;
      trace_read_system : trace_read_system_from_regMap rm trc.1;
      }.

  Hypothesis ttw_charac_restrict_memory :
    ∀ (rm : registerMap) (mm : memoryMap),
    rm_config_assms rm →
    ∀ va f popt,
    ttw_charac rm mm va = Some (f, popt) →
    ttw_charac rm (map_restrict mm f) va = Some (f, popt).

  Hypothesis ttw_charac_widen_memory :
    ∀ (rm : registerMap) (mm : memoryMap) (mm' : memoryMap),
    rm_config_assms rm →
    mm ⊆ mm' →
    ∀ va res,
    ttw_charac rm mm va = Some res →
    ttw_charac rm mm' va = Some res.

  (* From the Isabelle lemma of the same name *)
  Hypothesis ttw_charac_footprint_in_memory :
    ∀ (rm : registerMap) (mm : memoryMap),
    rm_config_assms rm →
    ∀ va f popt,
    ttw_charac rm mm va = Some (f, popt) →
    f ⊆ dom mm.

  (* From the Isabelle function of the same name *)
  Definition change_page_offset (offset : bv 12) `(addr : bv n) :=
    bv_concat n (bv_extract 12 (n - 12) addr) offset.

  (* From the Isabelle lemma of the same name *)
  Hypothesis ttw_charac_change_page_offset :
    ∀ (rm : registerMap) (mm : memoryMap),
    rm_config_assms rm →
    ∀ va offset,
    ttw_charac rm mm (change_page_offset offset va) =
      ttw_charac rm mm va |$>@{option}
        (λ '(f, res), (f, res |$> change_page_offset offset)).


  Definition trace_read_from_memMap (mm : memoryMap) (trc : list iEvent) :=
    ∀ ev ∈ trc,
    if ev is MemRead mr &→ Ok (val, _) then
      mem_lookup mr.(MemReq.address) mr.(MemReq.size) mm = Some val
    else True.

  Notation desc_fault te := te.(AddressDescriptor_fault).(FaultRecord_statuscode).
  Notation desc_addr te := te.(AddressDescriptor_paddress).(FullAddress_address).

  Definition trace_read_footprint (trc : list iEvent) : gset address.
    Admitted.

  (* From the Isabelle lemma of the same name *)
  Hypothesis ttw_charac_characterises_translation_subtraces :
    ∀ trc rm,
    cmatch vm_isem trc →
    isa_trace_satisfies_assms rm trc →
    ∀ strc : list iEvent,
    contig_sublist strc trc.1 →
    ∀ ts te,
    get_trans_subtrace_info strc = Some (ts, te) →
    ∀ mm,
    trace_read_from_memMap mm strc →
    ts.(TranslationStartInfo_accdesc).(AccessDescriptor_el) = 0%bv →
    desc_fault te = Fault_None →
    ttw_charac rm mm (bv_extract 0 48 ts.(TranslationStartInfo_va)) =
      Some (trace_read_footprint strc, Some (desc_addr te)).

  (* TODO: Add other Isabelle lemmas *)


  Definition regs_lift (rm : registerMap) : registerMap :=
    dmap_restrict rm user_registers.

  Section MStateLift.
    Variable vm_st : archState nth.

    Definition sys_regs : registerMap :=
      match nth with
      | 0 => λ _, ∅
      | S n0 =>
          λ vm_st, dmap_restrict (vm_st.(archState.regs) !!! 0%fin) system_registers
      end vm_st.

    Notation vm_memory := vm_st.(archState.memory).

    Definition ttw_charac_st : bv 48 → option (gset address * option address) :=
      ttw_charac sys_regs vm_memory.

    (* This is a galactic algorithm, not meant to be actually run. To make it
       computable, one would need to do a somewhat smart walk of the page tables *)
    Definition mem_lift : memoryMap :=
      foldr (λ va nmm,
          if ttw_charac_st va is Some (_, Some p) then
            if vm_memory !! p is Some b then
              <[bv_zero_extend 56 va := b]> nmm
            else nmm
          else nmm) ∅ (enum (bv 48)).

    Definition mstate_lift : archState nth :=
      archState.Make mem_lift PAS_NonSecure (vmap regs_lift vm_st.(archState.regs)).
  End MStateLift.

  Definition pre_lift_and_rel (pe : pre NMS nth) :
      option (pre NMS nth * list (list (list nat))) :=
    let new_init_st := mstate_lift pe.(Candidate.init) in
    pe.(Candidate.events)
    |> vmap (fmap (M := list) trace_erasure)
    |> vmap list_of_options
    |> vec_of_options
    |$> vmap (λ inp : list (iTrace () * list nat), (inp.*1, inp.*2))
    |$> (λ vec,
          (make_pre NMS new_init_st (vmap fst vec),
          (vec_to_list vec).*2)).

  Definition pre_lift pe := (pre_lift_and_rel pe) |$> fst.

  Definition lift_eid_from_list (l : list (list (list nat))) (eid : EID.t) :=
    thread ← l !! eid.(EID.tid);
    instr ← thread !! eid.(EID.iid);
    new_ieid ← instr !! eid.(EID.ieid);
    mret (setv EID.ieid new_ieid eid).

  Definition lift_rel_from_list l (rel : grel EID.t) :=
    grel_omap (lift_eid_from_list l) rel.

  Definition cand_lift cd :=
    '(pe, l) ← pre_lift_and_rel cd;
    Some (Candidate.make NMS pe
            (lift_rel_from_list l cd.(reads_from))
            (lift_rel_from_list l cd.(reg_reads_from))
            (lift_rel_from_list l cd.(coherence))
            (lift_rel_from_list l cd.(lxsx))).

  Section WithVMCD.
    Context (vm_cd : Candidate.t NMS nth).

    Hypothesis vm_cd_wf : wf vm_cd.
    Hypothesis vm_cd_ISA_match : ISA_match vm_cd vm_isem.
    (* Is is okay to instance with user_registers here? *)
    Hypothesis vm_cd_consistent_ok : VMSA.consistent_ok user_registers vm_cd.
    Hypothesis vm_cd_ISA_complete : ISA_complete vm_cd.

    Notation sys_regs := (sys_regs vm_cd.(Candidate.init)).
    Notation vm_memory := vm_cd.(Candidate.init).(archState.memory).
    Notation m_c := (ttw_charac_st vm_cd.(Candidate.init)).

    Section FullThm.
      Definition EL_is_always_EL0 : Prop.
      Proof using vm_cd.
        (* TODO: Need to standardize currentEL on all models *)
      Admitted.

      Definition at_EL0 : Prop :=
        EL_is_always_EL0 ∧ TE vm_cd = ∅ ∧ ERET vm_cd = ∅ ∧
          ∀ eid ev, vm_cd !! eid = Some ev → ¬ (is_faulting_trans_end ev).

      Context (Hat_EL0 : at_EL0).

      Definition same_sys_regs : Prop.
      Proof using vm_cd.
        (* TODO filter each registerMap on system_register set) *)
      Admitted.
      Context (Hsame_sys_regs : same_sys_regs).

      Context (Hconfig_check : rm_config_assms sys_regs).


      Definition injectivity : Prop :=
        ∀ (v v' : bv 48) (p : address) (f f' : gset address),
        m_c v = Some (f, Some p) → m_c v' = Some(f', Some p) → v = v'.
      Context (Hinjectivity : injectivity).

      Definition system_memory_footprint : gset address :=
        ⋃(enum (bv 48) |$> m_c |$> λ o, if o is Some (f, _) then f else ∅).
      Definition system_memory :=
        map_restrict vm_memory system_memory_footprint.
      Definition user_memory_footprint : gset address :=
        ⋃(enum (bv 48) |$> m_c |$> λ o, if o is Some (_, Some p) then {[p]} else ∅).
      Definition user_memory :=
        map_restrict vm_memory user_memory_footprint.

      Definition no_self_mapping : Prop :=
        user_memory_footprint ## system_memory_footprint.
      Context (Hno_self_mapping : no_self_mapping).

      Definition aborts :=
        collect_all (λ _, is_abort) vm_cd.

      Context (Hno_abort : aborts = ∅).

      Context (no_MSR : MSR vm_cd = ∅).

      Context (Hno_cache_op_tlb_op : C vm_cd = ∅).

      Definition AT_trans_start :=
        collect_all (λ _, is_AT_trans_start) vm_cd.

      Context (Hno_AT : AT_trans_start = ∅).

      Hypothesis TTW_reads_not_delayed : T vm_cd ## grel_rng (coherence vm_cd).

      (* TODO If we want to talk about terminated candidate, we need properties
              of termination condition *)

      (** ** Apply Phase 1 *)

      Definition In_Trans : gset EID.t.
        (* Events inside a translation *)
      Admitted.


      (* Lemma 15 *)
      Lemma initial_TTW_reg_reads :
        In_Trans ∩ reg_reads vm_cd ∩ grel_rng (reg_reads_from vm_cd) = ∅.
      Admitted.

      (* Lemma 16 *)
      Lemma initial_TTW_reads : T vm_cd ⊆ init_mem_reads vm_cd.
      Admitted.

      Lemma Phase1_applied : UM.consistent_ok user_registers vm_cd.
        eapply VMUM_phase1.
        all: try assumption.
        - apply initial_TTW_reads.
        - unfold at_EL0 in *. clear - Hat_EL0; set_solver.
        - admit. (* Need no_AT, non_AT_Tf_implies_fault and no fault (at_EL0) *)
        - unfold C in *. revert Hno_cache_op_tlb_op. set_solver.
      Admitted.


      (** ** Actual Phase 2 *)

      Lemma UM_lifted_success : is_Some (cand_lift vm_cd).
      Admitted.

      Section ActualPhase2.
        Variable um_cd : Candidate.t NMS nth.
        Hypothesis um_cd_is_lifted : cand_lift vm_cd = Some um_cd.

        Lemma ISA_match_um_cd : ISA_match um_cd um_isem.
        Admitted.

        Lemma wf_um_cd : wf um_cd.
        Admitted.

        Lemma ISA_complete_um_cd : ISA_complete um_cd.
        Admitted.

        Lemma UM_consistent_ok_um_cd : UM.consistent_ok user_registers um_cd.
        Admitted.

        Lemma UM_final_match :
          mstate_lift (cd_to_archState vm_cd) = cd_to_archState um_cd.
        Admitted.

      End ActualPhase2.

      Theorem Full_theorem :
        ∃ um_cd,
          cand_lift vm_cd = Some um_cd ∧
            ISA_match um_cd um_isem ∧
            wf um_cd ∧
            ISA_complete um_cd ∧
            UM.consistent_ok user_registers um_cd ∧
            mstate_lift (cd_to_archState vm_cd) = cd_to_archState um_cd.
      pose proof UM_lifted_success as Hum.
      destruct Hum as [um_cd Heq].
      exists um_cd.
      naive_solver
          ## ISA_match_um_cd
          ## wf_um_cd
          ## ISA_complete_um_cd
          ## UM_consistent_ok_um_cd
          ## UM_final_match.
      Qed.

    End FullThm.
  End WithVMCD.
  (* About Full_theorem. *)






  (* TODO figure out how to present system register assumptions *)

  (* Context (trace_erasure_not_failing: *)
  (*           ∀ trc : iTrace (), *)
  (*            cmatch vm_isem trc → *)
  (*            no_system_event trc → *)
  (*            is_Some (trace_erasure trc)). *)

  (* Context (trace_erasure_valid: *)
  (*           ∀ trc trc' : iTrace (), *)
  (*            cmatch vm_isem trc → *)
  (*            trace_erasure trc = Some trc' → *)
  (*            cmatch um_isem trc'). *)

  (* For any memory access in a VM trace, the pa is in the same page as
     translation end. *)
  (* For any VM trace, the pa in translation end match the characteisation function *)


  (* Need Caracterisation function *)

  (* Need to be able to split VM initial state into mutable and immutable(page-table) state *)

End Phase2.
