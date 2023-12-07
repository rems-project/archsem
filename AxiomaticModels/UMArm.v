Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.
Require Import GenModels.ArmInst.
Require Import GenAxiomaticArm.

(** This is an implementation of a user-mode Axiomatic model for ARM. It does
    not support mixed-size accesses, but does support dsb barriers, unlike usual
    Arm user mode models. This model has been written to look like the VMSA ESOP
    22 Arm model to simplify the proof. It is not up to date with change added
    the model by Arm after the ESOP 22 Paper by Ben Simner et al.

    This model used the "pa" part of the interface as the main address and does
    not check that that translation makes sense if there is one. However it will
    (TODO) check that translations read from initial memory if they exist, and
    that no writes are made to the address used for translation *)
Import Candidate.
Section rel.
  Context {nmth : nat}.
  Context (cd : Candidate.t NMS nmth).

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
  Notation "'int'" := (same_thread cd).
  Notation "'loc'" := (same_pa cd).

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

  (* rf orders explicit reads and writes,
     is unusual because of the handle of initial writes *)
  Definition fr := (loc ∩ (W × R)) ∖ (co ∪ ⦗W⦘ ⨾ rf)⁻¹.
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

End rel.

Section wf.
  Context {nmth : nat}.
  Context `(cd : Candidate.t NMS nmth).
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
                                     ∧ GenArmNMS.is_initial event init_mem) cd;
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
