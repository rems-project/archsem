Require Import Strings.String.

From stdpp Require Import decidable.

Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.
Require Import ISASem.ArmInst.
Require Import ISASem.SailArmInstTypes.
Require Import GenModels.TermModels.
Module ArmTM := TermModels Arm.
Require Import GenModels.CandidateExecutions.
Module ArmCand := CandidateExecutions Arm ArmTM.

Import Arm.
Import ArmTM.
Import ArmCand.

(* NOTE:
 This file defines the VMSA and User Arm axiomatic models. It starts with some
 common definitions (in section common_def), followed by module GenArm which
 contains a candidate cd, an inital memory map init_mem, with preliminary common
 wellformedness conditions. Finally, the two modules VMSA and UM contain the two
 models and their specific wellformedness conditions respectively. There are no
 dependencies between the two models.
 *)

Section common_def.
  Import Candidate.

  #[local] Hint Extern 10 (Decision (?x _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _)) => unfold x : typeclass_instances.
  #[local] Hint Extern 10 (Decision (?x _ _ _)) => unfold x : typeclass_instances.

  (*** barriers *)
  (* armv9-interface/barriers.cat *)
  Implicit Type b : SailArmInstTypes.Barrier.

  Definition is_barrier_P P `{forall b, Decision (P b)} (event : iEvent) :=
    match event with
    | Barrier b &→ _ => P b
    | _ => False
    end.

  Global Instance is_barrier_P_dec P `{forall b, Decision (P b)} event :
    Decision (is_barrier_P P event).
  Proof. apply _. Qed.

  Definition is_isb (barrier : barrier) :=
    match barrier with
    | Barrier_ISB _ => True
    | _ => False
    end.

  Definition isb {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_isb event) cd.

  Definition has_dsb_P P `{forall dxb, Decision (P dxb)} (barrier : barrier) :=
    match barrier with
    | Barrier_DSB dxb => P dxb
    | _ => False
    end.

  Global Instance has_dsb_P_dec P `{forall dxb, Decision (P dxb)} barrier :
    Decision (has_dsb_P P barrier).
  Proof. apply _. Qed.

  Definition is_dsbsy := has_dsb_P
                           (λ dxb,
                              (* DSBISH *)
                              (dxb.(DxB_domain) = MBReqDomain_InnerShareable
                               ∧ dxb.(DxB_types) = MBReqTypes_All)
                              (* DSBSY *)
                              ∨ (dxb.(DxB_domain) = MBReqDomain_FullSystem
                                 ∧ dxb.(DxB_types) = MBReqTypes_All)
                              (* DSBNSH *)
                              ∨ (dxb.(DxB_domain) = MBReqDomain_Nonshareable
                                 ∧ dxb.(DxB_types) = MBReqTypes_All)
                           ).

  Global Instance is_dsbsy_dec dxb : Decision (is_dsbsy dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L112 *)
  Definition dsbsy {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dsbsy event) cd.

  Definition is_dsbst b := is_dsbsy b
                           ∨ (has_dsb_P
                                (λ dxb,
                                   (* DSBST *)
                                   (dxb.(DxB_types) = MBReqTypes_Writes)
                                   (* DSBISHST *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_InnerShareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_Writes)
                                   (* DSBNSHST *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_Nonshareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_Writes)
                                ) b).

  Global Instance is_dsbst_dec dxb : Decision (is_dsbst dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L115 *)
  Definition dsbst {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dsbst event) cd.

  Definition is_dsbld b := is_dsbsy b
                           ∨ (has_dsb_P
                                (λ dxb,
                                   (* DSBLD *)
                                   (dxb.(DxB_types) = MBReqTypes_Reads)
                                   (* DSBISHLD *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_InnerShareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_Reads)
                                   (* DSBNSHLD *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_Nonshareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_Reads)
                                ) b).

  Global Instance is_dsbld_dec dxb : Decision (is_dsbld dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L115 *)
  Definition dsbld {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dsbld event) cd.

  Definition is_dsbnsh := has_dsb_P
                            (λ dxb,
                               (* DSBNSH *)
                               (dxb.(DxB_domain) = MBReqDomain_InnerShareable
                                ∧ dxb.(DxB_types) = MBReqTypes_All)).

  Global Instance is_dsbnsh_dec dxb : Decision (is_dsbnsh dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L121 *)
  Definition dsbnsh {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dsbnsh event) cd.


  Definition has_dmb_P P `{forall dxb, Decision (P dxb)} (barrier : barrier) :=
    match barrier with
    | Barrier_DMB dxb => P dxb
    | _ => False
    end.

  Global Instance has_dmb_P_dec P `{forall dxb, Decision (P dxb)} barrier :
    Decision (has_dmb_P P barrier).
  Proof. apply _. Qed.

  Definition is_dmbsy b := is_dsbsy b
                           ∨ (has_dmb_P
                                (λ dxb,
                                   (* DMBSY *)
                                   (dxb.(DxB_domain) = MBReqDomain_FullSystem
                                    ∧ dxb.(DxB_types) = MBReqTypes_All)
                                   (* DMBISH *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_InnerShareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_All)
                                   (* DMBNSH *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_Nonshareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_All)
                                ) b).

  Global Instance is_dmbsy_dec dxb : Decision (is_dmbsy dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L124 *)
  Definition dmbsy {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dmbsy event) cd.

  Definition is_dmbst b := is_dmbsy b ∨ is_dsbst b
                           ∨ (has_dmb_P
                                (λ dxb,
                                   (* DMBST *)
                                   (dxb.(DxB_domain) = MBReqDomain_FullSystem
                                    ∧ dxb.(DxB_types) = MBReqTypes_Writes)
                                   (* DMBISHST *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_InnerShareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_Writes)
                                   (* DMBNSHST *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_Nonshareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_Writes)
                                ) b).

  Global Instance is_dmbst_dec dxb : Decision (is_dmbst dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L127 *)
  Definition dmbst {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dmbst event) cd.

  Definition is_dmbld b := is_dmbsy b ∨ is_dsbld b
                           ∨ (has_dmb_P
                                (λ dxb,
                                   (* DMBLD *)
                                   (dxb.(DxB_domain) = MBReqDomain_FullSystem
                                    ∧ dxb.(DxB_types) = MBReqTypes_Reads)
                                   (* DMBISHLD *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_InnerShareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_Reads)
                                   (* DMBNSHLD *)
                                   ∨ (dxb.(DxB_domain) = MBReqDomain_Nonshareable
                                      ∧ dxb.(DxB_types) = MBReqTypes_Reads)
                                ) b).

  Global Instance is_dmbld_dec dxb : Decision (is_dmbld dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L130 *)
  Definition dmbld {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dmbld event) cd.

  Definition is_dmb b := is_dmbsy b ∨ is_dmbst b ∨ is_dmbld b.

  Global Instance is_dmb_dec dxb : Decision (is_dmb dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L133 *)
  Definition dmb {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dmb event) cd.

  Definition is_dsb b := is_dsbsy b ∨ is_dsbst b ∨ is_dsbld b.

  Global Instance is_dsb_dec dxb : Decision (is_dsb dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L136 *)
  Definition dsb {n} (cd : Candidate.t n) :=
    collect_all (λ _ event, is_barrier_P is_dsb event) cd.


  Definition is_explicit_access_kind_P P (event : iEvent) : Prop :=
    match event with
    | MemRead _ rreq &→ _ => match rreq.(ReadReq.access_kind) with
                                  | AK_explicit ak => P ak
                                  | _ => False
                                  end
    | MemWrite _ wreq &→ _ => match wreq.(WriteReq.access_kind) with
                                   | AK_explicit ak => P ak
                                   | _ => False
                                   end
    | _ => False
    end.

  Context {nmth : nat}.
  Context `(cd : t nmth).

  (*** interface-common *)

  (* interface-common.cat#L2 *)
  Definition F := barriers cd.

  (* interface-common.cat#L6 *)
  (* explicit writes *)
  Definition W :=
    collect_all (λ _ event, is_mem_write event
                            ∧ is_explicit_access_kind_P (λ _, True) event) cd.

  (* interface-common.cat#L5 *)
  Definition R :=
    collect_all (λ _ event, is_mem_read event
                            ∧ is_explicit_access_kind_P (λ _, True) event) cd.

  (* interface-common.cat#L52 *)
  Definition L :=
    collect_all
      (λ _ event, is_mem_write event
                  ∧ is_explicit_access_kind_P
                      (λ ak, ak.(Explicit_access_kind_strength) = AS_rel_or_acq)
                      event) cd.

  (* interface-common.cat#L46 *)
  Definition A :=
    collect_all
      (λ _ event, is_mem_read event
                  ∧ is_explicit_access_kind_P
                      (λ ak, ak.(Explicit_access_kind_strength) = AS_rel_or_acq)
                      event) cd.

  (* interface-common.cat#L49 *)
  Definition Q :=
    collect_all
      (λ _ event, is_mem_read event
                  ∧ is_explicit_access_kind_P
                      (λ ak, ak.(Explicit_access_kind_strength) = AS_acq_rcpc)
                      event) cd.

  Definition is_tlbi (event : iEvent) :=
    match event with
    | TlbOp _ _ &→ _ => True
    | _ => False
    end.

  Global Instance is_tlbi_dec event : Decision (is_tlbi event).
  Proof. apply _. Qed.

  Definition is_cacheop (event : iEvent) :=
    match event with
    | CacheOp _ _ &→ _ => True
    | _ => False
    end.

  Global Instance is_cacheop_dec event : Decision (is_cacheop event).
  Proof. unfold is_cacheop. apply _. Qed.

  (* interface-common.cat#L65 *)
  Definition C := collect_all (λ _ event, is_tlbi event ∨ is_cacheop event) cd.

  (* interface-common.cat#L68 *)
  Definition TLBI := collect_all (λ _ event, is_tlbi event) cd.

  Definition is_take_exception (event : iEvent) :=
    match event with
    | TakeException _ &→ _ => True
    | _ => False
    end.

  Global Instance is_take_exception_dec event : Decision (is_take_exception event).
  Proof. apply _. Qed.

  (* interface-common.cat#L71 *)
  Definition TE := collect_all (λ _ event, is_take_exception event) cd.

  Definition is_return_exception (event : iEvent) :=
    match event with
    | ReturnException _ &→ _ => True
    | _ => False
    end.

  Global Instance is_return_exception_dec event :
    Decision (is_return_exception event).
  Proof. apply _. Qed.

  (* interface-common.cat#L72 *)
  Definition ERET := collect_all (λ _ event, is_return_exception event) cd.

  (*** regs *)

  (* armv9-interface/regs.cat#L2 *)
  Definition is_msr (event : iEvent) :=
    match event with
    | RegWrite _ (Some _) _ _ &→ _ => True
    | _ => False
  end.
  Global Instance is_msr_dec event : Decision (is_msr event).
  Proof. unfold is_msr. apply _. Qed.

  Definition MSR := collect_all (λ _ event, is_msr event) cd.

  (* translation-table-walk reads *)
  Definition is_translate (event : iEvent) :=
    match event with
    | MemRead _ rreq &→ _ => rreq.(ReadReq.access_kind) = AK_ttw ()
    | _ => False
    end.

  Global Instance is_translate_dec event : Decision (is_translate event).
  Proof. apply _. Qed.

  (* translation-common.cat#L9 *)
  Definition T := collect_all (λ _ event, is_translate event) cd.

  (* A MemRead with ttw and value 0 *)
  Definition is_translation_read_fault (event : iEvent) :=
    match event with
    | MemRead n rreq &→ resp =>
        match rreq.(ReadReq.access_kind), resp with
        | AK_ttw (), inl (val, _) => val = bv_0 _
        | _, _ => False
        end
    | _ => False
    end.

  Global Instance is_translation_fault_dec event :
    Decision (is_translation_read_fault event).
  Proof.
    unfold is_translation_read_fault.
    destruct event as [T call ret].
    destruct call; tc_solve.
  Qed.

  (* translation-common.cat#L10 *)
  Definition T_f := collect_all (λ _ event, is_translation_read_fault event) cd.

  Notation "'lxsx'" := (lxsx cd).
  Notation "'amo'" := (amo cd).
  Notation "'addr'" := (addr cd).
  Notation "'data'" := (data cd).
  Notation "'ctrl'" := (ctrl cd).
  Notation "'loc'" := (loc cd).
  (* all mem events (explicit and translation) *)
  Notation "'writes'" := (mem_writes cd).
  (* all mem events (explicit and translation) *)
  Notation "'reads'" := (mem_reads cd).

  (* will diverge from loc if merging events *)
  Definition overlap_loc := loc.

  Definition rmw := lxsx ∪ amo.

  (* translation-common.cat#L25 *)
  Notation "'iio'" := (iio cd).
  (* instruction_order orders events between instructions *)
  (* translation-common.cat#L26 *)
  Notation "'instruction_order'" := (instruction_order cd).

End common_def.

Module GenArm.
  Import Candidate.
  Section def.
    Context {nmth : nat}.
    Context (cd : Candidate.t nmth).

  Notation "'amo'" := (amo cd).
  Notation "'lxsx'" := (lxsx cd).
  Notation "'iio'" := (iio cd).
  Notation "'loc'" := (loc cd).
  Notation "'addr'" := (addr cd).
  Notation "'data'" := (data cd).
  Notation "'ctrl'" := (ctrl cd).
  Notation "'instruction_order'" := (instruction_order cd).
  Notation "'W'" := (W cd).
  Notation "'R'" := (R cd).

  Global Instance is_explicit_access_kind_dec P `{forall ak, Decision (P ak)} event :
    Decision (is_explicit_access_kind_P P event).
  Proof. unfold is_explicit_access_kind_P. apply _. Qed.

  Definition is_successful (event : iEvent) :=
    match event with
    | MemWrite _ _ &→ wresp =>
        match wresp with (inl (Some true)) | (inl None) => True | _ => False end
    | _ => False
    end.

  Global Instance is_successful_dec event : Decision (is_successful event).
  Proof.
    unfold is_successful.
    destruct event as [T call ret].
    destruct call; apply _.
  Qed.

  Definition Wx :=
    collect_all
      (λ _ event, is_mem_write event ∧ is_successful event
                  ∧ is_explicit_access_kind_P
                      (λ ak, ak.(Explicit_access_kind_variety) = AV_exclusive)
                      event) cd.

  Definition Rx :=
    collect_all
      (λ _ event, is_mem_read event
                  ∧ is_explicit_access_kind_P
                      (λ ak, ak.(Explicit_access_kind_variety) = AV_exclusive)
                      event) cd.

  Export NMSWF.

  Record amo_wf := {
      amo_dom : grel_dom amo ⊆ Rx;
      amo_rng : grel_rng amo ⊆ Wx;
      amo_in_iio : amo ⊆ iio;
      amo_func : grel_functional amo;
      amo_inv_func : grel_functional (amo⁻¹);
      amo_loc : amo ⊆ loc;
    }.

  Record lxsx_wf := {
      lxsx_dom : grel_dom lxsx ⊆ Rx;
      lxsx_rng : grel_rng lxsx ⊆ Wx;
      lxsx_func : grel_functional lxsx;
      lxsx_inv_func : grel_functional (lxsx⁻¹);
      lxsx_loc : lxsx ⊆ loc;
      lxsx_po : lxsx ⊆ instruction_order;
    }.

  Record addr_wf :=
    {
      addr_dom : grel_dom addr ⊆ R;
      addr_rng : grel_rng addr ⊆ R ∪ W;
      addr_in_instruction_order : addr ⊆ instruction_order;
    }.

  Record data_wf :=
    {
      data_dom : grel_dom data ⊆ R;
      data_rng : grel_rng data ⊆ W;
      data_in_instruction_order : data ⊆ instruction_order;
    }.

  Record ctrl_wf :=
    {
      ctrl_dom : grel_dom ctrl ⊆ R;
      ctrl_in_instruction_order : ctrl ⊆ instruction_order;
      ctrl_instruction_order_in_ctrl : ctrl⨾instruction_order ⊆ ctrl;
    }.

  Record wellformed:= {
      amo :> amo_wf;
      lxsx :> lxsx_wf;
      generic_po :> NMSWF.generic_po_wf' cd;
      addr :> addr_wf;
      data :> data_wf;
      ctrl :> ctrl_wf;
    }.

  (* from promising *)
  Definition get_init_val (a : pa) (init_mem : memoryMap) :=
    list_from_func 8
      (fun n => a |> set FullAddress_address (bv_add (Z_to_bv 52 (Z.of_nat n))))
      |> map init_mem |> bv_of_bytes 64.

  Definition is_initial event init_mem :=
    (match Candidate.get_pa event, NMSWF.get_val event with
     | Some pa, Some val => (get_init_val pa init_mem) = val
     | _, _ => False
     end).

  Global Instance is_initial_dec event init_mem :
    Decision (is_initial event init_mem).
  Proof. unfold is_initial. apply _. Qed.

  End def.

  Variable nmth : nat.
  Variable cd : Candidate.t nmth.
  Variable init_mem : memoryMap.

End GenArm.


(*** VMSA *)
Module VMSA.
  (*** aarch64_mmu_strong_ETS *)
  Section def.
    Context {nmth : nat}.
    Context `(cd : Candidate.t nmth).

    Import Candidate.

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
    Notation "'loc'" := (loc cd).
    Notation "'int'" := (int cd).
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
    Definition wco := (generic_co cd).
    Definition co := ⦗W⦘⨾wco⨾⦗W⦘.
    Definition coi := co ∩ int.
    Definition coe := co ∖ coi.

    (* rf orders explicit writes and reads *)
    Definition rf := ⦗W⦘⨾(generic_rf cd)⨾⦗R⦘.
    Definition rfi := rf ∩ int.
    Definition rfe := rf ∖ rfi.

    (* armv9-interface/translation.cat#L35 *)
    Definition trf := (generic_rf cd) ∖ rf.
    Definition trfi := trf ∩ int.
    Definition trfe := trf ∖ trfi.

    (* rf orders explicit reads and writes,
     is unusual because of the handle of initial writes *)
    Definition fr := (loc ∩ (W × R)) ∖ (co? ⨾ rf)⁻¹.
    Definition fri := fr ∩ int.
    Definition fre := fr ∖ fri.

    (* armv9-interface/translation.cat#L46 *)
    (* Definition tfr := ((trf⁻¹⨾co) ∖ id ) ∩ overlap_loc. *)
    (* NOTE: To take initial writes under consideration, we have another
       impelemtation for tfr *)
    Definition tfr := (overlap_loc ∩ (W × T)) ∖ (co?⨾ rf)⁻¹.
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
     We define it as [same_instruction] for now which is only correct if one
     instruction invokes at most one TTW.
     *)
    Definition same_translation : grel EID.t := same_instruction cd.

    Definition get_vmid (event : iEvent) :=
      match event with
      | TlbOp _ tlbop &→ _ => Some (tlbop.(TLBI_rec).(TLBIRecord_vmid))
      | MemRead _ rreq &→ _ => (rreq.(ReadReq.translation).(TranslationInfo_vmid))
      | _ => None
      end.

    (* symmetry relation for [T] and [TLBI] with same vmid *)
    Definition same_vmid := sym_rel_with_same_key cd (λ _ event, get_vmid event).

    Definition get_asid (event : iEvent) :=
      match event with
      | TlbOp _ tlbop &→ _ => Some (tlbop.(TLBI_rec).(TLBIRecord_asid))
      | MemRead _ rreq &→ _ => (rreq.(ReadReq.translation).(TranslationInfo_asid))
      | _ => None
      end.

    (* symmetry relation for [T] and [TLBI] with same asid *)
    Definition same_asid := sym_rel_with_same_key cd (λ _ event, get_asid event).

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
      sym_rel_with_same_key cd (λ _ event, get_va_page event).

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
      sym_rel_with_same_key cd (λ _ event, get_ipa_page event).

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

  End def.

  Section wf.
    Context {nmth : nat}.
    Context `(cd : Candidate.t nmth).
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
                                       ∧ GenArm.is_initial event init_mem) cd;
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

End VMSA.

(*** User *)
Module UM.
  Section def.
    Context {nmth : nat}.
    Context (cd : Candidate.t nmth).
    Import Candidate.

    Notation "'rmw'" := (rmw cd).
    Notation "'addr'" := (addr cd).
    Notation "'data'" := (data cd).
    Notation "'ctrl'" := (ctrl cd).
    Notation "'W'" := (W cd).
    Notation "'R'" := (R cd).
    Notation "'M'" := (W ∪ R).
    Notation "'A'" := (A cd).
    Notation "'Q'" := (Q cd).
    Notation "'L'" := (L cd).
    Notation "'C'" := (C cd).
    Notation "'int'" := (int cd).
    Notation "'loc'" := (loc cd).

    Notation "'iio'" := (iio cd).
    Notation "'instruction_order'" := (instruction_order cd).

    Notation "'dmbst'" := (dmbst cd).
    Notation "'dmbsy'" := (dmbsy cd).
    Notation "'dmbld'" := (dmbld cd).
    Notation "'dsb'" := (dsb cd).
    Notation "'dsbsy'" := (dsbsy cd).
    Notation "'ISB'" := (isb cd).

    (* po orders memory events between instructions *)
    Definition po := ⦗M⦘⨾instruction_order⨾⦗M⦘.

    (* other shared relations *)
    Definition po_loc := po ∩ loc.

    Definition co := ⦗W⦘⨾(generic_co cd)⨾⦗W⦘.
    Definition coi := co ∩ int.
    Definition coe := co ∖ coi.

    (* rf orders explicit writes and reads *)
    Definition rf := ⦗W⦘⨾(generic_rf cd)⨾⦗R⦘.
    Definition rfi := rf ∩ int.
    Definition rfe := rf ∖ rfi.

    Notation "'id'" := ⦗valid_eids cd⦘.

    Definition valid_eids_rc r := r ∪ id.
    Definition valid_eids_compl a := (valid_eids cd) ∖ a.

    Notation "a ?" := (valid_eids_rc a) (at level 1, format "a ?") : stdpp_scope.

    (* rf orders explicit reads and writes,
     is unusual because of the handle of initial writes *)
    Definition fr := (loc ∩ (W × R)) ∖ (co? ⨾ rf)⁻¹.
    Definition fri := fr ∩ int.
    Definition fre := fr ∖ fri.

    Definition obs := rfe ∪ fr ∪ co.

    Definition dob :=
      addr ∪ data
        ∪ (ctrl⨾⦗W⦘)
        (* NOTE: (ctrl | addr;po) ; [ISB]; po; [R] is splitted into two,
         which seems important for one case of the refinement proof *)
        ∪ ((ctrl ∪ (addr⨾po))⨾⦗ISB⦘)
        ∪ (⦗ISB⦘⨾po⨾⦗R⦘)
        ∪ (addr⨾po⨾⦗W⦘)
        ∪ ((addr ∪ data)⨾rfi).

    Definition aob :=
      rmw
        ∪ (⦗grel_rng rmw⦘⨾rfi⨾ (⦗A⦘∪⦗Q⦘)).

    Definition bob :=
      (⦗R⦘⨾po⨾⦗dmbld⦘)
        ∪ (⦗W⦘⨾po⨾⦗dmbst⦘)
        ∪ (⦗dmbst⦘⨾po⨾⦗W⦘)
        ∪ (⦗dmbld⦘⨾po⨾⦗R ∪ W⦘)
        ∪ (⦗L⦘⨾po⨾⦗A⦘)
        ∪ (⦗A ∪ Q⦘⨾po⨾⦗R ∪ W⦘)
        ∪ (⦗R ∪ W⦘⨾po⨾⦗L⦘)
        ∪ (⦗dsb⦘⨾ po).

    (* Ordered-before *)
    Definition ob1 := obs ∪ dob ∪ aob ∪ bob.
    Definition ob := ob1⁺.

    Record consistent := {
        internal : grel_acyclic (po_loc ∪ fr ∪ co ∪ rf);
        external : grel_irreflexive ob;
        atomic : (rmw ∩ (fre⨾ coe)) = ∅;
      }.

  End def.

  Section wf.
    Context {nmth : nat}.
    Context `(cd : Candidate.t nmth).
    Context `(init_mem : memoryMap).
    Notation "'rf'" := (rf cd).
    Notation "'co'" := (co cd).
    Notation "'W'" := (W cd).
    Notation "'R'" := (R cd).
    Notation "'A'" := (A cd).
    Notation "'Q'" := (Q cd).
    Notation "'L'" := (L cd).
    Notation "'ctrl'" := (Candidate.ctrl cd).
    Notation "'po'" := (po cd).

    Record rf_wf' := {
        rf_dom : grel_dom rf ⊆ W;
        rf_rng : grel_rng rf ⊆ R;
        rf_generic :> NMSWF.generic_rf_wf' cd;
      }.

    Record initial_wf' :=
      {
        (* reads from initial memory get correct values *)
        initial_rf : R ∖ (grel_rng rf)
                     = Candidate.collect_all
                         (λ eid event, eid ∈ R ∖ (grel_rng rf)
                                       ∧ GenArm.is_initial event init_mem) cd;
      }.

    Record co_wf' :=
      {
        co_dom : grel_dom co ⊆ W;
        co_rng : grel_rng co ⊆ W;
        co_asym : co ∩ co⁻¹ = ∅;
        co_total : co ∪ co⁻¹ = W × W;
        co_generic :> NMSWF.generic_co_wf' cd;
      }.

    Record ctrl_wf' := {
        ctrl_po : ctrl ⨾ po ⊆ ctrl;
      }.

    Record event_wf' :=
      {
        no_cache_op :=
          Candidate.collect_all
            (λ _ event, is_cacheop event) cd = ∅;
        no_tlbi :=
          Candidate.collect_all
            (λ _ event, is_tlbi event) cd = ∅;
        no_ttw :=
          Candidate.collect_all
            (λ _ event, is_translate event) cd = ∅;
        no_exn :=
          Candidate.collect_all
            (λ _ event, is_take_exception event) cd = ∅;
        no_eret :=
          Candidate.collect_all
            (λ _ event, is_return_exception event) cd = ∅;
        no_msr :=
          Candidate.collect_all
            (λ _ event, is_msr event) cd = ∅;
      }.

    Record wf := {
        rf_wf :> rf_wf';
        co_wf :> co_wf';
        ctrl_wf :> ctrl_wf';
        initial_wf :> initial_wf';
        event_wf :> event_wf';
      }.
  End wf.

End UM.
