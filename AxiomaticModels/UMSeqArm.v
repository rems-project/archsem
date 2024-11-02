Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.GRel.
Require Import SSCCommon.FMon.
Require Import GenModels.ArmInst.
Require Import GenAxiomaticArm.

(** This is an implementation of a user-mode SC Axiomatic model in ARM style.

    This model used the "pa" part of the interface as the main address and does
    not check that that translation makes sense if there is one. However it will
    check that translations and instruction fetchs read from initial memory if
    they exist, and that no writes are made to the address used for
    translations(more exactly that translation reads never read from non-initial
    writes) *)
Import Candidate.
Section UMSeqArm.
  Context (regs_whitelist : gset reg).
  Context {nmth : nat}.
  Context (cd : Candidate.t NMS nmth).
  Import AxArmNames.

  Notation W := (W cd).
  Notation R := (R cd).
  Notation M := (W ∪ R).
  Notation A := (A cd).
  Notation Q := (Q cd).
  Notation L := (L cd).
  Notation T := (T cd).
  Notation TE := (TE cd).
  Notation ERET := (ERET cd).
  Notation int := (same_thread cd).
  Notation loc := (same_pa cd).
  Notation IR := (init_mem_reads cd).
  Notation rmw := (rmw cd).

  Notation iio := (iio cd).
  Notation instruction_order := (instruction_order cd).

  Notation IF := (ifetch_reads cd).

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
    is_reg_writeP (λ reg acc _, reg ∉ regs ∨ acc ≠ None).
  #[export] Instance is_illegal_reg_write_dec regs ev :
    Decision (is_illegal_reg_write regs ev).
  Proof. unfold_decide. Defined.

  Definition Illegal_RW := collect_all (λ _, is_illegal_reg_write regs_whitelist) cd.

  Definition is_illegal_reg_read (regs : gset reg) :=
    is_reg_writeP (λ reg acc _, acc ≠ None).
  #[export] Instance is_illegal_reg_read_dec regs ev :
    Decision (is_illegal_reg_read regs ev).
  Proof. unfold_decide. Defined.


  Definition Illegal_RR := collect_all (λ _, is_illegal_reg_read regs_whitelist) cd.

  (* po orders memory events between instructions *)
  Definition po := ⦗M⦘⨾instruction_order⨾⦗M⦘.

  (* other shared relations *)
  Definition po_loc := po ∩ loc.

  Definition co := ⦗W⦘⨾(coherence cd)⨾⦗W⦘.

  (* rf orders explicit writes and reads *)
  Definition rf := ⦗W⦘⨾(reads_from cd)⨾⦗R⦘.

  Definition fr := ⦗W⦘⨾(from_reads cd)⨾⦗R⦘.

  (* TODO This does not distinguishes UB conditions from invalid conditions *)
  Record consistent := {
      total : grel_acyclic (full_instruction_order cd ∪ fr ∪ co ∪ rf ∪ rfr ∪ rrf);
      atomic : (rmw ∩ (fr⨾ co)) = ∅;
      initial_reads : (T ∪ IF) ⊆ IR;
      register_write_permitted : Illegal_RW = ∅;
      register_read_permitted : Illegal_RR = ∅;
      memory_events_permitted : (mem_events cd) ⊆ M ∪ T ∪ IF;
      is_nms' : is_nms cd;
      no_exceptions: TE ∪ ERET = ∅
    }.

End UMSeqArm.
