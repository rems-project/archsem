Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.
Require Import GenModels.ArmInst.
Require Import GenAxiomaticArm.

Import Candidate.

(** This file define the VMSA model from the ESOP 22 paper by Ben Simner et al.
    The reference implementation is at: TODO
*)

Section rel.
  Context {nmth : nat}.
  Context `(cd : Candidate.t NMS nmth).

  Import Candidate.

  Notation outcome := (outcome DepOn.t).
  Notation iMon := (iMon DepOn.t).
  Notation iSem := (iSem DepOn.t).
  Notation iEvent := (iEvent DepOn.t).
  Notation iTrace := (iTrace DepOn.t).

  Notation "'W'" := (W cd).
  Notation "'R'" := (R cd).
  Notation "'A'" := (A cd).
  Notation "'Q'" := (Q cd).
  Notation "'L'" := (L cd).
  Notation "'F'" := (F cd).
  Notation "'C'" := (C cd).
  Notation "'M'" := (W ∪ R).
  Notation "'T'" := (T cd).
  Notation "'T_f'" := (T_f cd).
  Notation "'TLBI'" := (TLBI cd).
  Notation "'MSR'" := (MSR cd).
  Notation "'TE'" := (TE cd).
  Notation "'ERET'" := (ERET cd).
  Notation "'ISB'" := (isb cd).

  Notation "'rmw'" := (rmw cd).
  Notation "'addr'" := (addr cd).
  Notation "'data'" := (data cd).
  Notation "'ctrl'" := (ctrl cd).
  Notation "'loc'" := (same_pa cd).
  Notation "'int'" := (same_thread cd).
  Notation "'iio'" := (iio cd).

  Notation "'instruction_order'" := (instruction_order cd).
  Notation "'overlap_loc'" := (overlap_loc cd).

  Notation "'dmbst'" := (dmbst cd).
  Notation "'dmbsy'" := (dmbsy cd).
  Notation "'dmbld'" := (dmbld cd).
  Notation "'dsb'" := (dsb cd).
  Notation "'dsbsy'" := (dsbsy cd).

  Notation "'id'" := ⦗valid_eids cd⦘.

  Definition valid_eids_rc r := r ∪ id.
  Definition valid_eids_compl a := (valid_eids cd) ∖ a.

  Notation "a ?" := (valid_eids_rc a) (at level 1, format "a ?") : stdpp_scope.
  Notation "'~~' a" := (valid_eids_compl a)
                          (at level 1, format "~~ a") : stdpp_scope.

  (* po orders memory events between instructions *)
  Definition po := ⦗M ∪ F ∪ C⦘⨾instruction_order⨾⦗M ∪ F ∪ C⦘.

  (* other shared relations *)
  Definition po_loc := po ∩ loc.

  (* wco orders tlbi and writes *)
  Definition wco := (coherence cd).
  Definition co := ⦗W⦘⨾wco⨾⦗W⦘.
  Definition coi := co ∩ int.
  Definition coe := co ∖ coi.

  (* rf orders explicit writes and reads *)
  Definition rf := ⦗W⦘⨾(reads_from cd)⨾⦗R⦘.
  Definition rfi := rf ∩ int.
  Definition rfe := rf ∖ rfi.

  (* armv9-interface/translation.cat#L35 *)
  Definition trf := (reads_from cd) ∖ rf.
  Definition trfi := trf ∩ int.
  Definition trfe := trf ∖ trfi.

  (* rf orders explicit reads and writes,
    is unusual because of the handle of initial writes *)
  Definition fr := (loc ∩ (W × R)) ∖ (co ∪ ⦗W⦘ ⨾ rf)⁻¹.
  Definition fri := fr ∩ int.
  Definition fre := fr ∖ fri.

  (* armv9-interface/translation.cat#L46 *)
  (* Definition tfr := ((trf⁻¹⨾co) ∖ id ) ∩ overlap_loc. *)
  (* NOTE: To take initial writes under consideration, we have another
      implementation for tfr *)
  Definition tfr := (overlap_loc ∩ (W × T)) ∖ (co ∪ ⦗W⦘⨾ rf)⁻¹.
  Definition tfri := tfr ∩ int.
  Definition tfre := tfr ∖ tfr.

  #[local] Hint Extern 10 (Decision (?x _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _ _)) => unfold x : typeclass_instances.

  (*** TLBI *)
  (* armv9-interface/tlbi.cat *)

  (**  operation *)
  Definition has_tlb_op_P (P : _ -> Prop) `{forall op, Decision (P op)}
    (event : iEvent) :=
    match event with
    | TlbOp _ op &→ _ => P op
    | _ => False
    end.

  Global Instance has_tlb_op_P_dec P `{forall op, Decision (P op)} event :
    Decision (has_tlb_op_P P event).
  Proof.  apply _. Qed.

  Definition is_tlbi_op  (tlbiop : TLBIOp) (tlbop : SailArmInstTypes.TLBI) :=
    tlbop.(TLBI_rec).(TLBIRecord_op) = tlbiop.

  Definition has_tlbi_op (event : iEvent) (tlbiop : TLBIOp) :=
    has_tlb_op_P (is_tlbi_op tlbiop) event.

  (* armv9-interface/tlbi.cat#L82 *)
  Definition TLBI_ASID :=
    collect_all (λ _ event, has_tlbi_op event TLBIOp_ASID
                            ∨ has_tlbi_op event TLBIOp_VA
                            ∨ has_tlbi_op event TLBIOp_VAA) cd.
  (* armv9-interface/tlbi.cat#L89 *)
  Definition TLBI_S1 :=
    collect_all (λ _ event, has_tlbi_op event TLBIOp_VA
                            ∨ has_tlbi_op event TLBIOp_VMALLS12
                            ∨ has_tlbi_op event TLBIOp_VMALL
                            ∨ has_tlbi_op event TLBIOp_ALL
                            ∨ has_tlbi_op event TLBIOp_ASID) cd.
  (* armv9-interface/tlbi.cat#L98 *)
  Definition TLBI_S2 :=
    collect_all (λ _ event, has_tlbi_op event TLBIOp_IPAS2
                            ∨ has_tlbi_op event TLBIOp_VMALLS12
                            ∨ has_tlbi_op event TLBIOp_VMALL
                            ∨ has_tlbi_op event TLBIOp_ALL
                            ∨ has_tlbi_op event TLBIOp_ASID) cd.
  (* armv9-interface/tlbi.cat#L108 *)
  Definition TLBI_VMID :=
    collect_all (λ _ event, has_tlbi_op event TLBIOp_VA
                            ∨ has_tlbi_op event TLBIOp_VAA
                            ∨ has_tlbi_op event TLBIOp_IPAS2
                            ∨ has_tlbi_op event TLBIOp_VMALLS12
                            ∨ has_tlbi_op event TLBIOp_VMALL
                            ∨ has_tlbi_op event TLBIOp_ASID) cd.
  (* armv9-interface/tlbi.cat#L118 *)
  Definition TLBI_VA :=
    collect_all (λ _ event, has_tlbi_op event TLBIOp_VA) cd.
  (* armv9-interface/tlbi.cat#L121 *)
  Definition TLBI_IPA :=
    collect_all (λ _ event, has_tlbi_op event TLBIOp_IPAS2) cd.

  (** regime *)
  Definition is_tlbi_regime (reg : Regime) (tlbop : SailArmInstTypes.TLBI) :=
    tlbop.(TLBI_rec).(TLBIRecord_regime) = reg.

  Definition has_tlbi_regime (event : iEvent) (reg : Regime) :=
    has_tlb_op_P (is_tlbi_regime reg) event.

  (* armv9-interface/tlbi.cat#L126 *)
  Definition TLBI_EL1 :=
    collect_all (λ _ event, has_tlbi_regime event Regime_EL10) cd.
  (* armv9-interface/tlbi.cat#L129 *)
  Definition TLBI_EL2 :=
    collect_all (λ _ event, has_tlbi_regime event Regime_EL2) cd.

  (** shareability *)
  Definition is_tlbi_shareability (share : Shareability)
    (tlbop : SailArmInstTypes.TLBI) :=
    tlbop.(TLBI_shareability) = share.

  Definition has_tlbi_shareability (event : iEvent) (share : Shareability) :=
    has_tlb_op_P (is_tlbi_shareability share) event.

  (* armv9-interface/tlbi.cat#L135 *)
  Definition TLBI_IS :=
    collect_all (λ _ event, has_tlbi_shareability event Shareability_ISH
                            ∨ has_tlbi_shareability event Shareability_OSH) cd.

  (* armv9-interface/tlbi.cat#L142 *)
  (* This relation is supposed to group [T]s with in the same TTW together,
    which is not definable with the current outcome interface.
    We define it as [same_instruction_instance] for now which is only correct if one
    instruction invokes at most one TTW.
    *)
  Definition same_translation : grel EID.t := same_instruction_instance cd.

  Definition get_vmid (event : iEvent) :=
    match event with
    | TlbOp _ tlbop &→ _ => Some (tlbop.(TLBI_rec).(TLBIRecord_vmid))
    | MemRead _ rreq &→ _ => (rreq.(ReadReq.translation).(TranslationInfo_vmid))
    | _ => None
    end.

  (* symmetry relation for [T] and [TLBI] with same vmid *)
  Definition same_vmid := same_key (λ _ event, get_vmid event) cd.

  Definition get_asid (event : iEvent) :=
    match event with
    | TlbOp _ tlbop &→ _ => Some (tlbop.(TLBI_rec).(TLBIRecord_asid))
    | MemRead _ rreq &→ _ => (rreq.(ReadReq.translation).(TranslationInfo_asid))
    | _ => None
    end.

  (* symmetry relation for [T] and [TLBI] with same asid *)
  Definition same_asid := same_key (λ _ event, get_asid event) cd.

  (* armv9-interface/tlbi.cat#L158 *)
  (* NOTE: the definition diverges from the hacky cat version *)
  Definition tlbi_translate_same_asid : grel EID.t :=
    (TLBI_ASID × T) ∩ same_asid.

  (* armv9-interface/tlbi.cat#L157 *)
  (* NOTE: similar to [tlbi_translatr_same_asid] *)
  Definition tlbi_translate_same_vmid : grel EID.t :=
    (TLBI_VMID × T) ∩ same_vmid.

  Definition page_of_addr (ad: bits 64): bits 36 := bv_extract 12 36 ad.

  (* below are specialised version of [page_overlaps] *)
  (* armv9-interface/tlbi.cat#L170 *)

  Definition get_va_page (event : iEvent) :=
    match event with
    | MemRead _ rreq &→ _ => match (rreq.(ReadReq.va)) with
                                  | Some va => Some (page_of_addr va)
                                  | None => None
                                  end
    | TlbOp _ tlbop &→ _ => Some (page_of_addr (tlbop.(TLBI_rec)
                                                      .(TLBIRecord_address)))
    | _ => None
    end.

  Definition va_page_overlap :=
    same_key (λ _ event, get_va_page event) cd.

  Definition get_ipa_page (event : iEvent) :=
    match event with
    | MemRead _ rreq &→ _ =>
        match (rreq.(ReadReq.translation).(TranslationInfo_s2info)) with
        | Some (ipa, _) => Some (page_of_addr ipa)
        | None => None
        end
    | TlbOp _ tlbop &→ _ => Some (page_of_addr
                                          (tlbop.(TLBI_rec).(TLBIRecord_address)))
    | _ => None
    end.

  Definition ipa_page_overlap :=
    same_key (λ _ event, get_ipa_page event) cd.

  (* armv9-interface/tlbi.cat#L173 *)
  Definition tlbi_translate_same_va_page : grel EID.t :=
    (TLBI_VA × T) ∩ va_page_overlap.

  (* armv9-interface/tlbi.cat#L176 *)
  Definition tlbi_translate_same_ipa_page : grel EID.t :=
    (TLBI_IPA × T) ∩ ipa_page_overlap.

  (*** exceptions *)
  (* armv9-interface/exceptions.cat *)

  (* A Fault is an exception with a FaultRecord *)
  Definition has_fault_P P `{forall f, Decision (P f)} (event : iEvent) :=
    match event with
    | TakeException exn &→ _ => match (exn : Exn).(Exn_fault) with
                                      | Some fault => P fault
                                      | _ => False
                                      end
    | _ => False
    end.

  Global Instance has_fault_P_dec P `{forall f, Decision (P f)} event :
    Decision (has_fault_P P event).
  Proof. apply _. Qed.

  (* armv9-interface/exceptions.cat#L84 *)
  Definition Fault := collect_all (λ _ event, has_fault_P (λ _, True) event) cd.
  (* armv9-interface/exceptions.cat#L94 *)
  Definition Fault_T :=
    collect_all
      (λ _ event,
          has_fault_P
            (λ fault, fault.(FaultRecord_statuscode) = Fault_Translation) event) cd.
  (* armv9-interface/exceptions.cat#L95 *)
  Definition Fault_P :=
    collect_all
      (λ _ event,
          has_fault_P
            (λ fault, fault.(FaultRecord_statuscode) = Fault_Permission) event) cd.
  (* armv9-interface/exceptions.cat#L97 *)
  Definition FaultFromR :=
    collect_all
      (λ _ event,
          has_fault_P (λ fault, fault.(FaultRecord_write) = false) event) cd.
  (* armv9-interface/exceptions.cat#L97 *)
  Definition FaultFromW :=
    collect_all
      (λ _ event,
          has_fault_P (λ fault, fault.(FaultRecord_write) = true) event) cd.
  (* armv9-interface/exceptions.cat#L103 *)
  Definition FaultFromAquireR :=
    collect_all
      (λ _ event,
          has_fault_P
            (λ fault, fault.(FaultRecord_write) = false
                      ∧ fault.(FaultRecord_acctype) = AccType_ORDERED) event) cd.
  (* armv9-interface/exceptions.cat#L106 *)
  Definition FaultFromReleaseW :=
    collect_all
      (λ _ event,
          has_fault_P
            (λ fault, fault.(FaultRecord_write) = true
                      ∧ fault.(FaultRecord_acctype) = AccType_ORDERED) event) cd.

  (*** translation-common *)
  Definition has_translationinfo_P P `{forall ti, Decision (P ti)} (event : iEvent) :=
    match event with
    | MemRead _ rreq &→ _ => P (rreq.(ReadReq.translation))
    | _ => False
    end.

  Definition is_translationinfo_vmid (vmid : bits 16)
    (translationinfo: TranslationInfo) :=
    translationinfo.(TranslationInfo_vmid) = Some vmid.
  Global Instance is_translationinfo_vmid_dec vmid translationinfo :
    Decision (is_translationinfo_vmid vmid translationinfo).
  Proof. apply _. Qed.

  Definition has_translationinfo_vmid (event : iEvent) (vmid : bits 16) :=
    has_translationinfo_P (is_translationinfo_vmid vmid) event.

  Definition is_translationinfo_asid (asid : bits 16)
    (translationinfo: TranslationInfo) :=
    translationinfo.(TranslationInfo_asid) = Some asid.
  Global Instance is_translationinfo_asid_dec asid translationinfo :
    Decision (is_translationinfo_asid asid translationinfo).
  Proof. apply _. Qed.

  Definition has_translationinfo_asid (event : iEvent) (asid : bits 16) :=
    has_translationinfo_P (is_translationinfo_asid asid) event.

  Definition is_translationinfo_stage1 (translationinfo: TranslationInfo) :=
    translationinfo.(TranslationInfo_s2info) = None.

  Definition has_translationinfo_stage1 (event : iEvent) :=
    has_translationinfo_P is_translationinfo_stage1 event.
  Global Instance has_translationinfo_stage1_dec event :
    Decision (has_translationinfo_stage1 event).
  Proof. apply _. Qed.

  (* translation-common.cat#L13 *)
  Definition Stage1 := collect_all
                          (λ _ event, is_translate event
                                      ∧ has_translationinfo_stage1 event) cd.

  Definition is_translationinfo_stage2 (translationinfo: TranslationInfo) :=
    translationinfo.(TranslationInfo_s2info) ≠ None.

  Definition has_translationinfo_stage2 (event : iEvent) :=
    has_translationinfo_P is_translationinfo_stage2 event.
  Global Instance has_translationinfo_stage2_dec event :
    Decision (has_translationinfo_stage2 event).
  Proof. apply _. Qed.

  (* translation-common.cat#L14 *)
  Definition Stage2 := collect_all
                          (λ _ event, is_translate event
                                      ∧ has_translationinfo_stage2 event) cd.
  (* translation-common.cat#L31 *)
  Definition speculative := ctrl ∪ (addr⨾po) ∪ (⦗T⦘⨾instruction_order).
  (* translation-common.cat#L37 *)
  Definition po_pa := (instruction_order ∪ iio) ∩ loc.
  (* translation-common.cat#L42 *)
  Definition ContextChange := MSR ∪ TE ∪ ERET.
  (* translation-common.cat#L46 *)
  Definition CSE := ISB ∪ TE ∪ ERET.

  (* translation-common.cat#L55 *)
  Definition tlb_might_affect :=
    (⦗TLBI_S1 ∩  ~~TLBI_S2 ∩ TLBI_VA ∩ TLBI_ASID⦘⨾
        (tlbi_translate_same_va_page ∩ tlbi_translate_same_asid
          ∩ tlbi_translate_same_vmid)⨾⦗T ∩ Stage1⦘)
      ∪ (⦗TLBI_S1 ∩ ~~TLBI_S2 ∩ TLBI_VA  ∩ TLBI_ASID ∩ ~~TLBI_VMID⦘
            ⨾(tlbi_translate_same_va_page ∩ tlbi_translate_same_asid)⨾⦗T ∩ Stage1⦘)
      ∪ (⦗TLBI_S1 ∩ ~~TLBI_S2 ∩ ~~TLBI_VA ∩ TLBI_ASID ∩ TLBI_VMID⦘
            ⨾(tlbi_translate_same_asid ∩ tlbi_translate_same_vmid)⨾⦗T ∩ Stage1⦘)
      ∪ (⦗TLBI_S1 ∩ ~~TLBI_S2 ∩ ~~TLBI_VA ∩ ~~TLBI_ASID ∩ TLBI_VMID⦘
            ⨾tlbi_translate_same_vmid⨾⦗T ∩ Stage1⦘)
      ∪ (⦗~~TLBI_S1 ∩ TLBI_S2 ∩ TLBI_IPA ∩ ~~TLBI_ASID ∩ TLBI_VMID⦘
            ⨾(tlbi_translate_same_ipa_page ∩ tlbi_translate_same_vmid)⨾⦗T ∩ Stage2⦘)
      ∪ (⦗~~TLBI_S1 ∩ TLBI_S2 ∩ ~~TLBI_IPA ∩ ~~TLBI_ASID ∩ TLBI_VMID⦘⨾
            tlbi_translate_same_vmid⨾⦗T ∩ Stage2⦘)
      ∪ (⦗TLBI_S1 ∩ TLBI_S2 ∩ ~~TLBI_IPA ∩ ~~TLBI_ASID ∩ TLBI_VMID⦘⨾
            tlbi_translate_same_vmid⨾⦗T⦘)
      ∪ (TLBI_S1 ∩ ~~TLBI_IPA ∩ ~~TLBI_ASID ∩ ~~TLBI_VMID) × (T ∩ Stage1)
      ∪ (TLBI_S2 ∩ ~~TLBI_IPA ∩ ~~TLBI_ASID ∩ ~~TLBI_VMID) × (T ∩ Stage2).

  (* translation-common.cat#L67 *)
  Definition tlb_affects :=
    (⦗TLBI_IS⦘⨾tlb_might_affect)
      ∪ (⦗~~TLBI_IS⦘⨾tlb_might_affect) ∩ int.

  (* translation-common.cat#L75 *)
  Definition maybe_TLB_cached :=
    ((⦗T⦘⨾trf⁻¹⨾wco⨾⦗TLBI_S1⦘) ∪
    (* NOTE: The above line exists because of initial writes are not actual events.
        Therefore we need to consider T reading from initial writes, and
      TLBI that are only wco after initial writes separately *)
        ((T ∖ grel_rng trf) × (TLBI_S1 ∩ (grel_dom wco ∖ grel_rng wco)))
    ) ∩ tlb_affects⁻¹.

  (* translation-common.cat#L79 *)
  Definition tob :=
    (⦗T_f⦘⨾tfr) ∪ (speculative⨾trfi).

  (* translation-common.cat#L85 *)
  Definition tlb_barriered :=
    (⦗T⦘⨾tfr⨾wco⨾⦗TLBI⦘) ∩ tlb_affects⁻¹.

  (* translation-common.cat#L88 *)
  Definition obtlbi_translate :=
    (* A S1 translation must read from TLB/memory before the TLBI which
      * invalidates that entry happens *)
    (⦗T ∩ Stage1⦘⨾tlb_barriered⨾⦗TLBI_S1⦘)
      (* if the S2 translation is ordered before some S2 write
        * then the S1 translation has to be ordered before the subsequent
        * S1 invalidate which would force the S2 write to be visible
        *
        * this applies to S2 translations during a S1 walk as well
        * here the Stage2 translation is only complete once the TLBI VA which
        * invalidates previous translation-table-walks have been complete *)
      (* if the S1 translation is from after the TLBI VA
        * then the S2 translation is only ordered after the TLBI IPA
        *)
      ∪ ((⦗T ∩ Stage2⦘⨾tlb_barriered⨾⦗TLBI_S2⦘)
            ∩ (same_translation⨾⦗T ∩ Stage1⦘⨾trf⁻¹⨾wco⁻¹))
      (* if the S1 translation is from before the TLBI VA,
        * then the S2 translation is ordered after the TLBI VA
        *)
      ∪ (((⦗T ∩ Stage2⦘⨾tlb_barriered⨾⦗TLBI_S2⦘)⨾(wco ?)⨾⦗TLBI_S1⦘)
            ∩ (same_translation⨾⦗T ∩ Stage1⦘⨾maybe_TLB_cached)).

  (* translation-common.cat#L110 *)
  Definition obtlbi :=
    obtlbi_translate
      (*
        * a TLBI ensures all instructions that use the old translation
        * and their respective memory events
        * are ordered before the TLBI.
        *)
      ∪ (⦗R ∪ W ∪ Fault⦘⨾iio⁻¹⨾(obtlbi_translate ∖ int)⨾⦗TLBI⦘).

  (* translation-common.cat#L123 *)
  (* context-change ordered-before *)
  (* note that this is under-approximate and future work is needed
    * on exceptions and context-changing operations in general *)
  Definition ctxob :=
    (* no speculating past context-changing operations *)
    (speculative⨾⦗MSR⦘)
      (* context-synchronization orders everything po-after with the
        synchronization point *)
      ∪ (⦗CSE⦘⨾instruction_order)
      (* context-synchronization acts as a barrier for context-changing operations *)
      ∪ (⦗ContextChange⦘⨾po⨾⦗CSE⦘)
      (* context-synchronization-events cannot happen speculatively *)
      ∪ (speculative⨾⦗CSE⦘).

  (* translation-common.cat#L134 *)
  (* ordered-before a translation fault *)
  Definition obfault :=
    data⨾⦗Fault_T ∩ FaultFromW⦘
      ∪ speculative⨾⦗Fault_T ∩ FaultFromW⦘
      ∪ ⦗dmbst⦘⨾po⨾⦗Fault_T ∩ FaultFromW⦘
      ∪ ⦗dmbld⦘⨾po⨾⦗Fault_T ∩ (FaultFromW  ∪ FaultFromR)⦘
      ∪ ⦗A ∪ Q⦘⨾po⨾⦗Fault_T ∩ (FaultFromW  ∪ FaultFromR)⦘
      ∪ ⦗R ∪ W⦘⨾po⨾⦗Fault_T ∩ FaultFromW ∩ FaultFromReleaseW⦘.

  (* translation-common.cat#L150 *)
  (* ETS-ordered-before *)
  (* if FEAT_ETS then if E1 is ordered-before some Fault
    then E1 is ordered-before the translation-table-walk read which generated
    that fault (but not *every* read from the walk, only the one that directly
    led to the translation fault) Additionally, if ETS then TLBIs are guaranteed
    completed after DSBs hence po-later translations must be ordered after the
    TLBI (D5.10.2)
    *)
  Definition obETS :=
    ((obfault⨾⦗Fault_T⦘)⨾iio⁻¹⨾⦗T_f⦘)
      ∪ ((⦗TLBI⦘⨾po⨾⦗dsb⦘⨾instruction_order⨾⦗T⦘) ∩ tlb_affects).

  (* aarch64_mmu_strong_ETS.cat#L7 *)
  Definition obs  := rfe ∪ fr ∪ wco ∪ trfe.

  (* aarch64_mmu_strong_ETS.cat#L14 *)
  Definition dob :=
    addr ∪ data
      ∪ (speculative⨾⦗W⦘)
      ∪ (addr⨾po⨾⦗W⦘)
      ∪ ((addr ∪ data)⨾rfi)
      ∪ ((addr ∪ data)⨾trfi).

  (* aarch64_mmu_strong_ETS.cat#L22 *)
  Definition aob :=
    rmw
      ∪ (⦗grel_rng rmw⦘⨾rfi⨾(⦗A⦘∪⦗Q⦘)).

  (* aarch64_mmu_strong_ETS.cat#L26 *)
  Definition bob :=
    (⦗R⦘⨾po⨾⦗dmbld⦘)
      ∪ (⦗W⦘⨾po⨾⦗dmbst⦘)
      ∪ (⦗dmbst⦘⨾po⨾⦗W⦘)
      ∪ (⦗dmbld⦘⨾po⨾⦗R ∪ W⦘)
      ∪ (⦗L⦘⨾po⨾⦗A⦘)
      ∪ (⦗A ∪ Q⦘⨾po⨾⦗R ∪ W⦘)
      ∪ (⦗R ∪ W⦘⨾po⨾⦗L⦘)
      ∪ (⦗F ∪ C⦘⨾po⨾⦗dsbsy⦘)
      ∪ (⦗dsb⦘⨾po).

  (* aarch64_mmu_strong_ETS.cat#L37 *)
  (* Ordered-before *)
  Definition ob1 := obs ∪ dob ∪ aob ∪ bob  ∪ iio ∪ tob ∪ obtlbi ∪ ctxob
                      ∪ obfault ∪ obETS.
  (* aarch64_mmu_strong_ETS.cat#L38 *)
  Definition ob := ob1⁺.

  Record consistent := {
      (* aarch64_mmu_strong_ETS.cat#L41 *)
      internal : grel_acyclic (po_loc ∪ fr ∪ co ∪ rf);
      (* aarch64_mmu_strong_ETS.cat#L44 *)
      external : grel_irreflexive ob;
      (* aarch64_mmu_strong_ETS.cat#L47 *)
      atomic : (rmw ∩ (fre⨾ coe)) = ∅;
      (* aarch64_mmu_strong_ETS.cat#L50 *)
      translation_internal : (grel_acyclic (po_pa ∪ trfi));
    }.

End rel.

Section wf.
  Context {nmth : nat}.
  Context `(cd : Candidate.t NMS nmth).
  Context `(init_mem : memoryMap).
  Notation "'rf'" := (rf cd).
  Notation "'trf'" := (trf cd).
  Notation "'W'" := (W cd).
  Notation "'R'" := (R cd).
  Notation "'A'" := (A cd).
  Notation "'Q'" := (Q cd).
  Notation "'L'" := (L cd).
  Notation "'T'" := (T cd).
  Notation "'F'" := (F cd).
  Notation "'C'" := (C cd).
  Notation "'wco'" := (wco cd).
  Notation "'ctrl'" := (Candidate.ctrl cd).
  Notation "'po'" := (po cd).

  Record rf_wf' := {
      rf_dom : grel_dom rf ⊆ W;
      rf_rng : grel_rng rf ⊆ R;
      rf_generic :> NMSWF.generic_rf_wf' cd;
    }.

  Record trf_wf' := {
      trf_dom : grel_dom trf ⊆ W;
      trf_rng : grel_rng trf ⊆ T;
      trf_generic :> NMSWF.generic_rf_wf' cd;
    }.

  Record initial_wf' :=
    {
      (* reads from initial memory get correct values *)
      initial_rf : (R ∪ T) ∖ ((grel_rng rf) ∪ (grel_rng trf))
                    = Candidate.collect_all
                        (λ eid event, eid ∈ (R ∪ T) ∖ (grel_rng rf)
                                      ∧ GenArmNMS.is_initial event init_mem) cd;
    }.

  (* armv9-interface/wco.cat *)
  Record wco_wf' :=
    {
      wco_dom : grel_dom wco ⊆ W ∪ C;
      wco_rng : grel_rng wco ⊆ W ∪ C;
      wco_asym : wco ∩ wco⁻¹ = ∅;
      wco_total : wco ∪ wco⁻¹ = (W ∪ C) × (W ∪ C);
      wco_w_to_c : wco ∪ wco⁻¹ ⊆ W × C;
      wco_generic :> NMSWF.generic_co_wf' cd;
    }.

  Global Instance is_cacheop_dec event : Decision (is_cacheop event).
  Proof. unfold is_cacheop. apply _. Qed.

  Record event_wf' :=
    {
      no_cache_op :=
        Candidate.collect_all
          (λ _ event, is_cacheop event) cd = ∅;
    }.

  Record ctrl_wf' := {
      ctrl_po : ctrl ⨾ po ⊆ ctrl;
    }.

  Record wf := {
      rf_wf :> rf_wf';
      wco_wf :> wco_wf';
      initial_wf :> initial_wf';
      ctrl_wf : ctrl_wf';
      event_wf :> event_wf';
    }.

End wf.
