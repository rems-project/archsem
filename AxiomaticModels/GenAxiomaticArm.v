Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.
Require Import GenModels.ArmInst.

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

Module AxArmNames.
  Import Candidate.
  Section ArmNames.

  Context {et : exec_type} {nmth : nat}.
  Context `(cd : t et nmth).

  Definition F := barriers cd.

  Definition W := explicit_writes cd.
  Definition R := explicit_reads cd.
  Definition Wx := exclusive_writes cd.
  Definition Rx := exclusive_writes cd.
  Definition L := rel_acq_writes cd.
  Definition A := rel_acq_reads cd.
  Definition Q := acq_rcpc_reads cd.
  Definition T := ttw_reads cd.

  (* All cache flushing operations *)
  Definition C := collect_all (λ _ ev, is_tlbop ev ∨ is_cacheop ev) cd.
  Definition TLBI := collect_all (λ _ ev, is_tlbop ev) cd.
  Definition TE := collect_all (λ _ event, is_take_exception event) cd.
  Definition ERET := collect_all (λ _ event, is_return_exception event) cd.

  Definition is_msr := is_reg_writeP (λ _ o _, is_Some o).
  #[export] Typeclasses Transparent is_msr.
  Definition MSR := collect_all (λ _, is_msr) cd.


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
    set_unfold. hauto q:on use:is_mem_readP_spec.
  Qed.

  Definition amo := atomic_update cd.

  Definition rmw := lxsx cd ∪ amo.
  End ArmNames.
End AxArmNames.
