Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.
Require Import GenModels.ArmInst.

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

  Definition isb {et n} (cd : Candidate.t et n) :=
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
  Definition dsbsy {et n} (cd : Candidate.t et n) :=
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
  Definition dsbst {et n} (cd : Candidate.t et n) :=
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
  Definition dsbld {et n} (cd : Candidate.t et n) :=
    collect_all (λ _ event, is_barrier_P is_dsbld event) cd.

  Definition is_dsbnsh := has_dsb_P
                            (λ dxb,
                               (* DSBNSH *)
                               (dxb.(DxB_domain) = MBReqDomain_InnerShareable
                                ∧ dxb.(DxB_types) = MBReqTypes_All)).

  Global Instance is_dsbnsh_dec dxb : Decision (is_dsbnsh dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L121 *)
  Definition dsbnsh {et n} (cd : Candidate.t et n) :=
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
  Definition dmbsy {et n} (cd : Candidate.t et n) :=
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
  Definition dmbst {et n} (cd : Candidate.t et n) :=
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
  Definition dmbld {et n} (cd : Candidate.t et n) :=
    collect_all (λ _ event, is_barrier_P is_dmbld event) cd.

  Definition is_dmb b := is_dmbsy b ∨ is_dmbst b ∨ is_dmbld b.

  Global Instance is_dmb_dec dxb : Decision (is_dmb dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L133 *)
  Definition dmb {et n} (cd : Candidate.t et n) :=
    collect_all (λ _ event, is_barrier_P is_dmb event) cd.

  Definition is_dsb b := is_dsbsy b ∨ is_dsbst b ∨ is_dsbld b.

  Global Instance is_dsb_dec dxb : Decision (is_dsb dxb).
  Proof. apply _. Qed.

  (* armv9-interface/barriers.cat#L136 *)
  Definition dsb {et n} (cd : Candidate.t et n) :=
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

  Context {et : exec_type} {nmth : nat}.
  Context `(cd : t et nmth).

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
    | TlbOp _ &→ _ => True
    | _ => False
    end.

  Global Instance is_tlbi_dec event : Decision (is_tlbi event).
  Proof. apply _. Qed.

  Definition is_cacheop (event : iEvent) :=
    match event with
    | CacheOp _ &→ _ => True
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
    | RegWrite _ (Some _) _ &→ _ => True
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
    destruct event as [call ret].
    destruct call; tc_solve.
  Qed.

  (* translation-common.cat#L10 *)
  Definition T_f := collect_all (λ _ event, is_translation_read_fault event) cd.

  Notation "'lxsx'" := (lxsx cd).
  Notation "'amo'" := (atomic_update cd).
  Notation "'addr'" := (addr cd).
  Notation "'data'" := (data cd).
  Notation "'ctrl'" := (ctrl cd).
  Notation "'loc'" := (same_pa cd).
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

Module GenArmNMS.
  Import Candidate.

  Section def.
    Context {nmth : nat}.
    Context (cd : Candidate.t NMS nmth).
  Notation "'amo'" := (atomic_update cd).
  Notation "'lxsx'" := (lxsx cd).
  Notation "'iio'" := (iio cd).
  Notation "'loc'" := (same_pa cd).
  Notation "'addr'" := (addr cd).
  Notation "'data'" := (data cd).
  Notation "'ctrl'" := (ctrl cd).
  Notation "'instruction_order'" := (instruction_order cd).
  Notation "'W'" := (W cd).
  Notation "'R'" := (R cd).

  Global Instance is_explicit_access_kind_dec P `{forall ak, Decision (P ak)} event :
    Decision (is_explicit_access_kind_P P event).
  Proof. unfold is_explicit_access_kind_P. apply _. Qed.

  Definition Wx :=
    collect_all
      (λ _ event, is_mem_write event
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
      full_instruction_order :> NMSWF.full_instruction_order_wf' cd;
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
    (match get_pa event, NMSWF.get_val event with
     | Some pa, Some val => (get_init_val pa init_mem) = val
     | _, _ => False
     end).

  Global Instance is_initial_dec event init_mem :
    Decision (is_initial event init_mem).
  Proof. unfold is_initial. apply _. Qed.

  End def.

End GenArmNMS.
