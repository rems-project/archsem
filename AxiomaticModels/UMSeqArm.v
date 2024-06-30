Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.
Require Import GenModels.ArmInst.
Require Import GenAxiomaticArm.

(** This is an implementation of a user-mode sequential Axiomatic model in ARM style.

    This model used the "pa" part of the interface as the main address and does
    not check that that translation makes sense if there is one. However it will
    check that translations and instruction fetchs read from initial memory if
    they exist, and that no writes are made to the address used for translation *)
Import Candidate.
Section rel.
  Context (regs_whitelist : gset reg).
  Notation nmth := 1%nat.
  Context (cd : Candidate.t NMS nmth).

  Notation W := (W cd).
  Notation R := (R cd).
  Notation M := (W ∪ R).
  Notation A := (A cd).
  Notation Q := (Q cd).
  Notation L := (L cd).
  Notation C := (C cd).
  Notation T := (T cd).
  Notation int := (same_thread cd).
  Notation loc := (same_pa cd).
  Notation IR := (init_mem_reads cd).

  Notation iio := (iio cd).
  Notation instruction_order := (instruction_order cd).


  Definition IF := ifetch_reads cd.

  (* Registers *)

  Notation RW := (reg_writes cd).
  Notation RR := (reg_reads cd).
  Notation RE := (RW ∪ RR).

  Definition Rpo := ⦗RE⦘⨾instruction_order⨾⦗RE⦘.
  Notation Rloc := (same_reg cd).

  Definition Rpo_loc := Rpo ∩ Rloc.

  Notation rrf := (reg_reads_from cd).

  Notation rfr := (reg_from_reads cd).

  Definition is_illegal_reg_write (regs : gset reg) :=
    is_reg_writeP (λ reg _ _, reg ∉ regs).

  Definition Illegal_RW := collect_all (λ _, is_illegal_reg_write regs_whitelist) cd.

  (* po orders memory events between instructions *)
  Definition po := ⦗M⦘⨾instruction_order⨾⦗M⦘.

  (* other shared relations *)
  Definition po_loc := po ∩ loc.

  Definition co := ⦗W⦘⨾(coherence cd)⨾⦗W⦘.

  (* rf orders explicit writes and reads *)
  Definition rf := ⦗W⦘⨾(reads_from cd)⨾⦗R⦘.

  Notation id := ⦗valid_eids cd⦘.

  Definition valid_eids_rc r := r ∪ id.
  Definition valid_eids_compl a := (valid_eids cd) ∖ a.

  (* rf orders explicit reads and writes,
     is unusual because of the handle of initial writes *)
  Definition fr := ⦗W⦘⨾(from_reads cd)⨾⦗R⦘.

  Record consistent := {
      coherence : grel_acyclic (po_loc ∪ fr ∪ co ∪ rf);
      initial_reads : (T ∪ IF) ⊆ IR;
      register_coherence : grel_acyclic (Rpo_loc ∪ rfr ∪ rrf);
      register_permitted : Illegal_RW = ∅;
    }.

  Record wf := {
     co_wf : coherence_wf cd;
     rf_wf : reads_from_wf cd;
     rrf_wf : reg_reads_from_wf cd;
  }.

End rel.
