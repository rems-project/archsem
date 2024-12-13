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

Section VMSAArm.
  Import Candidate.
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
  Notation L := (rel_acq_writes pe).
  Notation A := (rel_acq_reads pe).
  Notation Q := (acq_rcpc_reads pe).
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

  (** * Registers

      Although this model supports updating the page tables, it does not yet
      support updating page table registers like the TTBRs. Therefore it only
      support untagged register writes

   *)

  Definition is_illegal_reg_write (regs : gset reg) :=
    is_reg_writeP (λ reg acc _, reg ∉ regs ∨ acc ≠ None).
  #[export] Instance is_illegal_reg_write_dec regs ev :
    Decision (is_illegal_reg_write regs ev).
  Proof. unfold_decide. Defined.

  Definition Illegal_RW := collect_all (λ _, is_illegal_reg_write regs_whitelist) cd.

  Notation "'id'" := ⦗valid_eids cd⦘.

  Definition valid_eids_rc r := r ∪ id.
  Definition valid_eids_compl a := (valid_eids cd) ∖ a.

  Notation "a ?" := (valid_eids_rc a) (at level 1, format "a ?") : stdpp_scope.
  Notation "'~~' a" := (valid_eids_compl a)
                          (at level 1, format "~~ a") : stdpp_scope.

  (** * Explicit memory

      The only kind of read allowed in this model are:
      - Explicit
      - TTW
      - IFetch

      In addition, only explicit write are allowed.

      [coherence] however can also contain cache operations. *)

  (* po orders memory events between instructions *)
  (* Definition po := ⦗M ∪ F ∪ C⦘⨾instruction_order⨾⦗M ∪ F ∪ C⦘. *)

  (* other shared relations *)
  (* Definition po_loc := po ∩ loc. *)

  (* wco orders tlbi and writes *)
  Definition wco := (coherence cd).
  (* Definition co := ⦗W⦘⨾wco⨾⦗W⦘. *)
  (* Definition coi := co ∩ int. *)
  (* Definition coe := co ∖ coi. *)

  (* rf orders explicit writes and reads *)
  (* Definition rf := reads_from cd ⨾⦗R⦘. *)
  (* Definition rfi := rf ∩ int. *)
  (* Definition rfe := rf ∖ rfi. *)

  (* (* armv9-interface/translation.cat#L35 *) *)
  (* Definition trf := reads_from cd ⨾⦗T⦘. *)
  (* Definition trfi := trf ∩ int. *)
  (* Definition trfe := trf ∖ trfi. *)

  (* rf orders explicit reads and writes,
    is unusual because of the handle of initial writes *)
  (* Definition fr := ⦗R⦘⨾ from_reads cd. *)
  (* Definition fri := fr ∩ int. *)
  (* Definition fre := fr ∖ fri. *)

  (* armv9-interface/translation.cat#L46 *)
  (* Definition tfr := ((trf⁻¹⨾co) ∖ id ) ∩ overlap_loc. *)
  (* NOTE: To take initial writes under consideration, we have another
      implementation for tfr *)
  (* Definition tfr := ⦗T⦘⨾ from_reads cd. *)
  (* Definition tfri := tfr ∩ int. *)
  (* Definition tfre := tfr ∖ tfr. *)

  #[local] Hint Extern 10 (Decision (?x _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _ _)) => unfold x : typeclass_instances.

  (*** TLBI *)
  (* armv9-interface/tlbi.cat *)

  Definition is_tlbi_op  (tlbiop : TLBIOp) (tlbop : SailArmInstTypes.TLBI) :=
    tlbop.(TLBI_rec).(TLBIRecord_op) = tlbiop.

  Definition has_tlbi_op (event : iEvent) (tlbiop : TLBIOp) :=
    is_tlbopP (is_tlbi_op tlbiop) event.

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
    is_tlbopP (is_tlbi_regime reg) event.

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
    is_tlbopP (is_tlbi_shareability share) event.

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
    | TlbOp tlbop &→ _ => Some (tlbop.(TLBI_rec).(TLBIRecord_vmid))
    | MemRead _ rreq &→ _ => (rreq.(ReadReq.translation).(TranslationInfo_vmid))
    | _ => None
    end.

  (* symmetry relation for [T] and [TLBI] with same vmid *)
  Definition same_vmid := same_key (λ _ event, get_vmid event) cd.

  Definition get_asid (event : iEvent) :=
    match event with
    | TlbOp tlbop &→ _ => Some (tlbop.(TLBI_rec).(TLBIRecord_asid))
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
    | TlbOp tlbop &→ _ => Some (page_of_addr (tlbop.(TLBI_rec)
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
    | TlbOp tlbop &→ _ => Some (page_of_addr
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

  Section isFault.
    Context (P : FaultRecord → Prop).
    Implicit Type ev : iEvent.

    Definition is_faultP :=
      is_take_exceptionP (λ e, if e.(Exn_fault) is Some f then P f else False).
    Typeclasses Opaque is_faultP.

    Definition is_faultP_spec ev:
      is_faultP ev ↔
        ∃ exn flt, ev = TakeException (Build_Exn exn (Some flt)) &→ () ∧ P flt.
    Proof.
      clear - P ev.
      destruct ev as [[] fret];
        split; cdestruct |- ? #CDestrMatch; destruct fret; sauto lq:on dep:on.
    Qed.

    Context `{Pdec: ∀ c, Decision (P c)}.
    #[global] Instance is_faultP_dec ev: Decision (is_faultP ev).
    Proof using Pdec. unfold is_faultP. solve_decision. Defined.
  End isFault.
  Notation is_fault := (is_faultP (λ _, True)).

  (* armv9-interface/exceptions.cat#L84 *)
  Definition Fault := collect_all (λ _ event, is_fault event) cd.
  (* armv9-interface/exceptions.cat#L94 *)
  Definition Fault_T :=
    collect_all
      (λ _ event,
          is_faultP
            (λ fault, fault.(FaultRecord_statuscode) = Fault_Translation) event) cd.
  (* armv9-interface/exceptions.cat#L95 *)
  Definition Fault_P :=
    collect_all
      (λ _ event,
          is_faultP
            (λ fault, fault.(FaultRecord_statuscode) = Fault_Permission) event) cd.
  (* armv9-interface/exceptions.cat#L97 *)
  Definition FaultFromR :=
    collect_all
      (λ _ event,
          is_faultP (λ fault, fault.(FaultRecord_write) = false) event) cd.
  (* armv9-interface/exceptions.cat#L97 *)
  Definition FaultFromW :=
    collect_all
      (λ _ event,
          is_faultP (λ fault, fault.(FaultRecord_write) = true) event) cd.
  (* armv9-interface/exceptions.cat#L103 *)
  Definition FaultFromAquireR :=
    collect_all
      (λ _ event,
          is_faultP
            (λ fault, fault.(FaultRecord_write) = false
                      ∧ fault.(FaultRecord_acctype) = AccType_ORDERED) event) cd.
  (* armv9-interface/exceptions.cat#L106 *)
  Definition FaultFromReleaseW :=
    collect_all
      (λ _ event,
          is_faultP
            (λ fault, fault.(FaultRecord_write) = true
                      ∧ fault.(FaultRecord_acctype) = AccType_ORDERED) event) cd.

  (*** translation-common *)

  Notation T_f := (T_f cd).

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

  Definition is_translate := is_mem_read_kindP is_ttw.

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
  (* Definition po_pa := (instruction_order ∪ iio) ∩ loc. *)
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
      ∪ ⦗dmb_store cd⦘⨾po⨾⦗Fault_T ∩ FaultFromW⦘
      ∪ ⦗dmb_load cd⦘⨾po⨾⦗Fault_T ∩ (FaultFromW  ∪ FaultFromR)⦘
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
      ∪ ((⦗TLBI⦘⨾po⨾⦗dsbsy cd⦘⨾instruction_order⨾⦗T⦘) ∩ tlb_affects).

  (* WIP new FEAT_ETS2 definition, very tentative *)
  Definition obETS2 :=
    ⦗M⦘⨾po⨾⦗T_f⦘
      ∪ ⦗dsbsy cd⦘⨾instruction_order⨾⦗IF⦘⨾iio⨾⦗T⦘.


  (* aarch64_mmu_strong_ETS.cat#L7 *)
  Definition obs  := rfe ∪ fr ∪ wco ∪ trfe.

  (* aarch64_mmu_strong_ETS.cat#L14 *)
  Definition dob :=
    addr ∪ data
      ∪ (speculative⨾⦗W⦘)
      ∪ ((addr ∪ data)⨾rfi)
      ∪ ((addr ∪ data)⨾trfi).

  (* aarch64_mmu_strong_ETS.cat#L22 *)
  Definition aob :=
    rmw
      ∪ (⦗grel_rng rmw⦘⨾rfi⨾(⦗A⦘∪⦗Q⦘)).

  Definition bob :=
    (⦗R⦘⨾po⨾⦗dmb_load cd⦘)
    ∪ (⦗W⦘⨾po⨾⦗dmb_store cd⦘)
    ∪ (⦗dmb cd⦘⨾po⨾⦗W⦘)
    ∪ (⦗dmb_load cd⦘⨾po⨾⦗R⦘)
    ∪ (⦗L⦘⨾po⨾⦗A⦘)
    ∪ (⦗A ∪ Q⦘⨾po⨾⦗M⦘)
    ∪ (⦗M⦘⨾po⨾⦗L⦘)
    ∪ (⦗dsb cd⦘⨾po⨾⦗MSR ∪ M ∪ F ∪ C ∪ TE ∪ ERET⦘) (* Maybe MSR => RW??*)
    ∪ (⦗ISB⦘⨾ instruction_order).


  (* aarch64_mmu_strong_ETS.cat#L37 *)
  (* Ordered-before *)
  Definition ob1 := obs ∪ dob ∪ aob ∪ bob ∪ iio ∪ tob ∪ obtlbi ∪ ctxob
                      ∪ obfault ∪ obETS.
  (* aarch64_mmu_strong_ETS.cat#L38 *)
  Definition ob := ob1⁺.

  Record consistent := {
      internal :> exp_internal cd;
      reg_internal' :> reg_internal cd;
      translation_internal : trfi ⊆ not_after cd;
      external : grel_irreflexive ob;
      atomic : (rmw ∩ (fre⨾ coe)) = ∅;
      initial_reads : IF ⊆ IR;
      initial_reads_not_delayed : IF ## grel_rng (coherence cd);
      register_write_permitted : Illegal_RW = ∅;
      memory_events_permitted : (mem_events cd) ⊆ M ∪ T ∪ IF;
      is_nms' : is_nms cd;
      no_cacheop : ICDC = ∅;
      co_contains_TBLI_writes:
      ∀ weid ∈ mem_writes cd, ∀ teid ∈ TLBI,
        (weid, teid) ∈ coherence cd ∨ (teid, weid) ∈ coherence cd
    }.

End VMSAArm.
