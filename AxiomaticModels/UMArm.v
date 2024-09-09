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
Section UMArm.
  Import Candidate.
  Context (regs_whitelist : gset reg).
  Context {nmth : nat}.
  Context (cd : Candidate.t NMS nmth).
  Import AxArmNames.

  (** * Arm standard notations *)
  Notation F := (F cd).
  Notation W := (W cd).
  Notation R := (R cd).
  Notation M := (mem_events cd).
  Notation Wx := (Wx cd).
  Notation Rx := (Rx cd).
  Notation L := (L cd).
  Notation A := (A cd).
  Notation Q := (Q cd).
  Notation T := (T cd).
  Notation C := (C cd).
  Notation TLBI := (TLBI cd).
  Notation TE := (TE cd).
  Notation ERET := (ERET cd).
  Notation MSR := (MSR cd).
  Notation int := (same_thread cd).
  Notation loc := (same_pa cd).
  Notation iio := (iio cd).
  Notation instruction_order := (instruction_order cd).
  Notation rmw := (rmw cd).
  Notation addr := (addr cd).
  Notation data := (data cd).
  Notation ctrl := (ctrl cd).

  Notation ISB := (isb cd).
  Notation IF := (ifetch_reads cd).
  Notation IR := (init_mem_reads cd).

  (** * Registers *)

  Notation RW := (reg_writes cd).
  Notation RR := (reg_reads cd).
  Notation RE := (RW ∪ RR).

  Definition is_illegal_reg_write (regs : gset reg) :=
    is_reg_writeP (λ reg acc _, reg ∉ regs ∨ acc ≠ None).

  Definition Illegal_RW := collect_all (λ _, is_illegal_reg_write regs_whitelist) cd.

  Definition Rpo := ⦗RE⦘⨾instruction_order⨾⦗RE⦘.
  Notation Rloc := (same_reg cd).

  Definition Rpo_loc := Rpo ∩ Rloc.

  Notation rrf := (reg_reads_from cd).

  Notation rfr := (reg_from_reads cd).

  (** * Explicit memory *)

  (* po orders memory events between instructions *)
  Definition po := ⦗M ∪ F⦘⨾instruction_order⨾⦗M ∪ F⦘.

  (* other shared relations *)
  Definition po_loc := po ∩ loc.

  Definition co := ⦗W⦘⨾ coherence cd ⨾⦗W⦘.

  Definition coi := co ∩ int.
  Definition coe := co ∖ coi.

  (* rf orders explicit writes and reads *)
  Definition rf := ⦗W⦘⨾ reads_from cd ⨾⦗R⦘.
  Definition rfi := rf ∩ int.
  Definition rfe := rf ∖ rfi.

  (* rf orders explicit reads and writes,
     is unusual because of the handle of initial writes *)
  Definition fr := ⦗R⦘⨾ from_reads cd ⨾⦗W⦘.
  Definition fri := fr ∩ int.
  Definition fre := fr ∖ fri.

  Definition obs := rfe ∪ fr ∪ co.

  Definition speculative := ctrl ∪ (addr⨾po).

  Definition dob :=
    addr ∪ data
    ∪ (speculative ⨾⦗W⦘)
    ∪ (speculative ⨾⦗ISB⦘)
    ∪ ((addr ∪ data) ⨾ rfi).

  Definition aob :=
    rmw
    ∪ (⦗grel_rng rmw⦘⨾rfi⨾ (⦗A⦘∪⦗Q⦘)).

  Definition bob :=
    (⦗R⦘⨾po⨾⦗dmb_load cd⦘)
    ∪ (⦗W⦘⨾po⨾⦗dmb_store cd⦘)
    ∪ (⦗dmb cd⦘⨾po⨾⦗W⦘)
    ∪ (⦗dmb_load cd⦘⨾po⨾⦗R⦘)
    ∪ (⦗L⦘⨾po⨾⦗A⦘)
    ∪ (⦗A ∪ Q⦘⨾po⨾⦗R ∪ W⦘)
    ∪ (⦗R ∪ W⦘⨾po⨾⦗L⦘)
    ∪ (⦗dsb cd⦘⨾ po)
    ∪ (⦗ISB⦘⨾ instruction_order).

  (* Ordered-before *)
  Definition ob1 := obs ∪ dob ∪ aob ∪ bob.
  Definition ob := ob1⁺.

  (* TODO This does not distinguishes UB conditions from invalid conditions.
     Cache operation are allowed but are effectively no-ops which is find
     because any TTW or IFetch access must read from initial memory.

     Currently only explicit, TTW or IFetch accesses are accepted but this can
     be updated later *)
  Record consistent := {
      internal : grel_acyclic (po_loc ∪ fr ∪ co ∪ rf);
      reg_internal : grel_acyclic (Rpo_loc ∪ rfr ∪ rrf);
      external : grel_irreflexive ob;
      atomic : (rmw ∩ (fre⨾ coe)) = ∅;
      initial_reads : (T ∪ IF) ⊆ IR;
      register_write_permitted : Illegal_RW = ∅;
      memory_events_permitted : (mem_events cd) ⊆ M ∪ T ∪ IF;
      is_nms' : is_nms cd;
      no_exceptions: TE ∪ ERET = ∅
    }.

End UMArm.
