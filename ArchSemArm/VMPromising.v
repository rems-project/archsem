(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
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
From ASCommon Require Import GRel Exec FMon StateT HVec Common.

Require Import ArmInst.

Require UMPromising.
Import (hints) UMPromising.

#[local] Open Scope list.
#[local] Open Scope nat.
#[local] Open Scope stdpp.

(** The goal of this module is to define a Virtual-memory promising model with
    mixed-size support on top of the ArchSem interface.

    Currently this model only supports EL0 and EL1 with a single stage of
    translation. Translation configuration is hard-coded to be VMSA-64 with 4KB
    granule and 48 bits in and out. The model is parametric on the ETS level


    In addition we assume:
    - FEAT_nTLBPA hold.
    - FEAT_BBM: BBM level is 0
*)


(** * Page numbers *)

(** This model hard-codes a 48 bits to 48 bits translation so page numbers are
    the same for physical addresses as for virtual addresses *)
Definition pn := bv 36.
#[export] Typeclasses Transparent pn.

(** Page number of a virtual address *)
Definition va_to_vpn (va : bv 64) : pn := bv_extract 12 36 va.

(** Page-aligned virtual address of a page number. Since a page number does not
    carry the VA range information, it is provided by [upper] *)
Definition vpn_to_va (upper : bool) (vpn : pn) : bv 64 :=
  let varange_bits : bv 16 := if upper then (-1)%bv else 0%bv in
  bv_concat 64 varange_bits (bv_concat 48 vpn (bv_0 12)).

(** Page number of a physical address *)
Definition pa_to_pn (pa : address) : pn := bv_extract 12 36 pa.

(** Page-aligned physical address of a page number. The upper physical address
    bits are always zero in this model *)
Definition pn_to_pa (p : pn) : address :=
  bv_concat 56 (bv_0 8) (bv_concat 48 p (bv_0 12)).


(** * Memory *)

Module TLBI.
  Inductive t :=
  | All (tid : nat)
  | Asid (tid : nat) (asid : bv 16)
  | Va (tid : nat) (asid : bv 16) (upper : bool) (vpn : pn) (last : bool)
  | Vaa (tid : nat) (upper : bool) (vpn : pn) (last : bool).

  #[global] Instance dec : EqDecision t.
  solve_decision.
  Defined.

  Definition tid (tlbi : t) : nat :=
    match tlbi with
    | All tid => tid
    | Asid tid _ => tid
    | Va tid _ _ _ _ => tid
    | Vaa tid _ _ _ => tid
    end.

  Definition asid_opt (tlbi : t) : option (bv 16) :=
    match tlbi with
    | All _ => None
    | Asid _ asid => Some asid
    | Va _ asid _ _ _ => Some asid
    | Vaa _ _ _ _ => None
    end.

  Definition asid (tlbi : t) : bv 16 :=
    default (Z_to_bv 16 0) (asid_opt tlbi).

  Definition vpn_opt (tlbi : t) : option pn :=
    match tlbi with
    | All _ => None
    | Asid _ _ => None
    | Va _ _ _ vpn _ => Some vpn
    | Vaa _ _ vpn _ => Some vpn
    end.

  Definition vpn (tlbi : t) : pn := default 0%bv (vpn_opt tlbi).

  Definition last_opt (tlbi : t) : option bool :=
    match tlbi with
    | All _ => None
    | Asid _ _ => None
    | Va _ _ _ _ last => Some last
    | Vaa _ _ _ last => Some last
    end.

  Definition last (tlbi : t) : bool :=
    default false (last_opt tlbi).

  Definition upper_opt (tlbi : t) : option bool :=
    match tlbi with
    | All _ => None
    | Asid _ _ => None
    | Va _ _ upper _ _ => Some upper
    | Vaa _ upper _ _ => Some upper
    end.
End TLBI.

(** Events in the VMPromising history can be either memory writes or TLBI effects *)
Module Ev.
  Inductive t :=
  | Msg (msg : Msg.t)
  | Tlbi (tlbi : TLBI.t) (recipient : nat).

  #[export] Instance dec : EqDecision t.
  Proof. solve_decision. Defined.

  Definition tid (ev : t) :=
    match ev with
    | Msg msg => Msg.tid msg
    | Tlbi tlbi _ => TLBI.tid tlbi
    end.

  Definition get_msg (ev : t) : option Msg.t :=
    match ev with
    | Msg msg => Some msg
    | _ => None
    end.

  Definition get_tlbi (ev : t) : option TLBI.t :=
    match ev with
    | Tlbi tlbi _ => Some tlbi
    | _ => None
    end.

  Definition get_tlbi_recipient (ev : t) : option nat :=
    match ev with
    | Tlbi _ recipient => Some recipient
    | _ => None
    end.

  (** Checks whether an write event overlaps an address range *)
  Definition overlap (a : address) (sz : N) (ev : t) : Prop :=
    match ev with
    | Msg msg => Msg.overlap a sz msg
    | _ => False
    end.
  #[export] Instance Decision_overlap (a : address) (sz : N) (ev : t) :
      Decision (overlap a sz ev).
  Proof. unfold_decide. Defined.
End Ev.
Export (hints) Ev.

Coercion Ev.Msg : Msg.t >-> Ev.t.

(** A view is just a natural, reused from UM *)
Definition view := UMPromising.view.
#[export] Typeclasses Transparent view.
Bind Scope nat_scope with view.
Global Hint Transparent view : core.
Global Hint Unfold view : core.

Module Memory.
  Import PromMemory.
  Export (hints) PromMemory.

  (** The promising memory: a list of events *)
  Definition t : Type := t Ev.t.
  #[export] Typeclasses Transparent t.


  Definition cut_after : nat → t → t := cut_after.
  Definition cut_before : nat → t → t := cut_before.
  Definition promise : Ev.t → Exec.t t string nat := promise.
  Definition fulfill : Ev.t → list nat → t → option nat := fulfill.
  Definition read_from : address → N → memoryMap → t → _ := read_from Ev.get_msg.
  Definition read_all : address → N → memoryMap → t → _ := read_all Ev.get_msg.
  Definition read_all_btw : address → N → memoryMap → t → _ :=
    read_all_btw Ev.get_msg.
  Definition read_initial : address → N → memoryMap → t → _ :=
    read_initial Ev.get_msg.
  Definition read_byte : address → memoryMap → t → _ :=
    read_byte Ev.get_msg.
  Definition read_word : address → memoryMap → t → _ :=
    read_word Ev.get_msg.
  Definition to_memMap : memoryMap → t → memoryMap := to_memMap Ev.get_msg.
  Definition exclusive : nat → address → N → nat → nat → t → Prop :=
    exclusive Ev.get_msg.
  #[export] Typeclasses Transparent exclusive.

  (** Read all possible PTE between [tmin] and [tmax] included *)
  Definition read_all_pte (addr : address) (init : memoryMap) (mem : t)
      (tmin tmax : nat) : result string (list (bv 64 * nat)) :=
    read_all_btw addr 8 init mem tmin tmax |$> map (λ bytes,
      (bv_of_bytes 64 bytes.*1, max_list_with snd bytes)).

End Memory.
Import (hints) Memory.


Definition EL := (fin 4).
#[export] Typeclasses Transparent EL.
Bind Scope fin_scope with EL.
Definition ELp := (fin 3).
#[export] Typeclasses Transparent ELp.
Bind Scope fin_scope with ELp.

Definition ELp_to_EL : ELp → EL := FS.


(** * Register classification

    Here we classify register based on which category they belong to. Register
    that are not listed here (other than the PC) are unsupported and cannot be
    written to (But can be read if unmodified) *)

(** Strict registers are those have non-relaxed behaviour: every read must read
    the previous write e.g GP register, stack pointers, ... *)
Definition strict_regs : gset reg :=
  list_to_set [
       R0;
       R1;
       R2;
       R3;
       R4;
       R5;
       R6;
       R7;
       R8;
       R9;
       R10;
       R11;
       R12;
       R13;
       R14;
       R15;
       R16;
       R17;
       R18;
       R19;
       R20;
       R21;
       R22;
       R23;
       R24;
       R25;
       R26;
       R27;
       R28;
       R29;
       R30;
       NZCV;
       CurrentEL;
       SPSel;
       DAIF;
       SP_EL0;
       SP_EL1;
       SP_EL2;
       SP_EL3;
       ELR_EL1;
       ELR_EL2;
       ELR_EL3;
      (* These registers are system registers, but they are considered
         strict in the model. *)
       ESR_EL1;
       ESR_EL2;
       ESR_EL3;
       FAR_EL1;
       FAR_EL2;
       FAR_EL3;
       PAR_EL1;
       SPSR_EL1;
       SPSR_EL2;
       SPSR_EL3]@{reg}.

(** Relaxed registers are not guaranteed to read the latest value. *)
Definition relaxed_regs : gset reg :=
  list_to_set [
       TTBR0_EL1;
       TTBR0_EL2;
       TTBR0_EL3;
       TTBR1_EL1;
       TTBR1_EL2;
       VBAR_EL1;
       VBAR_EL2;
       VBAR_EL3;
       VTTBR_EL2]@{reg}.

(** TTBR registers used for BBM violation checking.
    When checking BBM, we iterate over all TTBRs to find matching page tables. *)
Definition ttbrs : gset reg :=
  list_to_set [
    TTBR0_EL1;
    TTBR0_EL2;
    TTBR0_EL3;
    TTBR1_EL1;
    TTBR1_EL2;
    VTTBR_EL2]@{reg}.


(** Determine if input register is an unknown register from the architecture *)
Definition is_reg_unknown (r : reg) : Prop :=
  ¬(r ∈ relaxed_regs ∨ r ∈ strict_regs ∨ r = pc_reg).
Instance Decision_is_reg_unknown (r : reg) : Decision (is_reg_unknown r).
Proof. unfold_decide. Defined.

Equations regval_to_val (r : reg) (v : reg_type r) : option (bv 64) :=
  | R_bitvector_64 _, v => Some v
  | _, _ => None.

Equations val_to_regval (r : reg) (v : bv 64) : option (reg_type r) :=
  | R_bitvector_64 _, v => Some v
  | _, v => None.


(** * Address and PTE helpers *)
(** All type and infastructure to manipulate VAs, PAs and PTEs *)

(** ** Levels *)

(** Since were are doing 4KB-granule 48bit in translation we are going from level 0 to 3 *)
Definition Level := fin 4.
#[export] Typeclasses Transparent Level.

Definition root_lvl : Level := 0%fin.
Definition leaf_lvl : Level := 3%fin.

Definition child_lvl (lvl : Level) : option Level :=
  match lvl in fin n return option Level with
  | 0 => Some 1
  | 1 => Some 2
  | 2 => Some 3
  | _ => None
  end%fin.

Lemma child_lvl_add_one (lvl clvl : Level)
    (CHILD : child_lvl lvl = Some clvl) :
  lvl + 1 = clvl.
Proof.
  unfold child_lvl in CHILD.
  repeat case_split; cdestruct clvl |- ***.
Qed.

Definition parent_lvl (lvl : Level) : option Level :=
  match lvl in fin n return option Level with
  | 1 => Some 0
  | 2 => Some 1
  | 3 => Some 2
  | _ => None
  end%fin.

Lemma parent_lvl_sub_one (lvl plvl : Level)
    (PARENT : parent_lvl lvl = Some plvl) :
  plvl + 1 = lvl.
Proof.
  unfold parent_lvl in PARENT.
  repeat case_split; cdestruct plvl |- ***.
Qed.

(** ** Prefix helpers *)

(** [level_length] is the translation-relevant part of an address for a given
    level, [offset_bits] is the remaining offset bits. More precisely:
    - Level 0: prefix size is 9, offset size is 39 which means a block is 512GB
    - Level 1: prefixsize is 18, offset_bits is 30 which means a block is 1GB
    - Level 2: level_size is 27, offset_bits is 21 which means a block is 2MB
    - Level 3: level_size is 26, offset_bits is 12 which means a page is 4KB *)
Definition prefix_bits (lvl : Level) : N := 9 * (lvl + 1).
Definition offset_bits (lvl : Level) : N := 48 - prefix_bits lvl.

Lemma prefix_bits_36 lvl : (prefix_bits lvl ≤ 36)%N.
Proof. unfold prefix_bits. use (fin_to_N_lt lvl). lia. Qed.

Definition prefix (lvl : Level) := bv (prefix_bits lvl).
#[export] Typeclasses Transparent prefix.
Definition offset (lvl : Level) := bv (offset_bits lvl).
#[export] Typeclasses Transparent offset.

Definition prefix_offset {lvl : Level} (pre : prefix lvl) (off : offset lvl) : bv 48 :=
  bv_concat 48 pre off.
Definition zero_offset (lvl : Level) : offset lvl := bv_0 (offset_bits lvl).

(** ** VA helpers *)

Definition prefix_to_va (lvl : Level) (upper : bool) (p : prefix lvl) : bv 64 :=
  let varange_bits : bv 16 := if upper then (-1)%bv else 0%bv in
  bv_concat 64 varange_bits (prefix_offset p (zero_offset lvl)).

Definition is_upper_va (va : bv 64) : option bool :=
  let top_bits := bv_extract 48 16 va in
  if top_bits =? (-1)%bv then Some true
  else if top_bits =? 0%bv then Some false
  else None.

Definition va_prefix (lvl : Level) (va : bv 64)  : prefix lvl :=
  bv_extract (offset_bits lvl) (prefix_bits lvl) va.

Definition vpn_prefix (lvl : Level) (vpn : pn) : prefix lvl :=
  bv_extract (36 - prefix_bits lvl) (prefix_bits lvl) vpn.

(* Definition match_prefix_at (lvl : Level) (te_va : prefix lvl) (vpn : pn) : Prop := *)
(*   te_va = vpn_level_prefix vpn lvl. *)
(* Instance Decision_match_prefix_at (lvl : Level) (te_va : prefix lvl) (vpn : pn) : *)
(*   Decision (match_prefix_at lvl te_va vpn). *)
(* Proof. unfold_decide. Defined. *)

(** *** VA indexes *)

(** Get the index at a given level for a VA *)
Definition va_level_index (lvl : Level) (va : bv 64) : bv 9 :=
  bv_extract 0 9 (va_prefix lvl va).

(** Get the index at a given level for a VPN (Virtual page number) *)
Definition vpn_level_index (lvl : Level) (vpn : pn) : bv 9 :=
  bv_extract 0 9 (vpn_prefix lvl vpn).

(** ** PA helpers *)

Definition pa_unused_bits : N := addr_size - 48.

(** Get the physical address of an entry in a given table *)
Definition index_table (table : pn) (index : bv 9) : address :=
  bv_concat 56 (bv_0 pa_unused_bits)
    (bv_concat 48 table (bv_concat 12 index (bv_0 3))).

Definition pa_prefix (pa : address) (lvl : Level) : prefix lvl :=
  bv_extract (offset_bits lvl) (prefix_bits lvl) pa.

Definition pa_offset (lvl : Level) (pa : address) : offset lvl :=
  bv_extract 0 (offset_bits lvl) pa.

Definition pa_prefix_offset (lvl : Level) (p : prefix lvl) (off : offset lvl) :
    address :=
  bv_concat 56 (bv_0 pa_unused_bits) (prefix_offset p off).

Definition prefix_to_pa (lvl : Level) (p : prefix lvl) : address :=
  pa_prefix_offset lvl p (zero_offset lvl).

(** ** PTE helpers *)

Definition is_valid (e : bv 64) : Prop :=
  (bv_extract 0 1 e) = 1%bv.
Instance Decision_is_valid (e : bv 64) : Decision (is_valid e).
Proof. unfold_decide. Defined.

(** A PTE is a table descriptor if:
    - It is not at the leaf level (level 3), AND
    - Its bits [0:2] = 11 (table descriptor encoding)
    At leaf level, bits [0:2]=11 indicates a page entry, not a table. *)
Definition is_table (lvl : Level) (e : bv 64) : Prop :=
  lvl ≠ leaf_lvl ∧ (bv_extract 0 2 e) = 3%bv.
Instance Decision_is_table (lvl : Level) (e : bv 64) : Decision (is_table lvl e).
Proof. unfold_decide. Defined.

Definition is_block (e : bv 64) : Prop :=
  (bv_extract 0 2 e) = 1%bv.
Instance Decision_is_block (e : bv 64) : Decision (is_block e).
Proof. unfold_decide. Defined.

Definition is_final (lvl : Level) (e : bv 64) : Prop :=
  if lvl is 3%fin then (bv_extract 0 2 e) = 3%bv
  else lvl ≠ root_lvl ∧ is_block e.
Instance Decision_is_final (lvl : Level) (e : bv 64) : Decision (is_final lvl e).
Proof. unfold_decide. Defined.

Definition has_access_flag (e : bv 64) : Prop :=
  (bv_extract 10 1 e) = 1%bv.
Instance Decision_has_access_flag (e : bv 64) : Decision (has_access_flag e).
Proof. unfold_decide. Defined.

(** Final descriptors require the access flag to produce translations. *)
Definition is_accessible_final (lvl : Level) (e : bv 64) : Prop :=
  is_final lvl e ∧ has_access_flag e.
Instance Decision_is_accessible_final (lvl : Level) (e : bv 64) :
    Decision (is_accessible_final lvl e).
Proof. unfold_decide. Defined.

(** TLB-fillable descriptors are tables or accessible final descriptors. *)
Definition is_tlb_fillable (lvl : Level) (e : bv 64) : Prop :=
  is_table lvl e ∨ is_accessible_final lvl e.
Instance Decision_is_tlb_fillable (lvl : Level) (e : bv 64) :
    Decision (is_tlb_fillable lvl e).
Proof. unfold_decide. Defined.

Definition is_global (lvl : Level) (e : bv 64) : Prop :=
  is_final lvl e ∧ (bv_extract 11 1 e) = 0%bv.
Instance Decision_is_global (lvl : Level) (e : bv 64) : Decision (is_global lvl e).
Proof. unfold_decide. Defined.

(** Extract AttrIndx field (bits 4:2) from a block/page descriptor.
    This indexes into MAIR_ELx to determine memory type and cacheability. *)
Definition attr_idx (e : bv 64) : bv 3 := bv_extract 2 3 e.

(** Extract Shareability field (bits 9:8) from a block/page descriptor.
    00 = Non-shareable, 10 = Outer Shareable, 11 = Inner Shareable *)
Definition shareability (e : bv 64) : bv 2 := bv_extract 8 2 e.

(** Extract non-Global bit (bit 11) from a block/page descriptor.
    nG=0 means global (all ASIDs), nG=1 means non-global (ASID-specific). *)
Definition is_non_global (e : bv 64) : bool := (bv_extract 11 1 e) =? 1%bv.

(** Extract Contiguous bit (bit 52) from a block/page descriptor.
    When set, indicates this entry is part of a contiguous set of entries
    that could be cached as a single TLB entry. *)
Definition is_contiguous (e : bv 64) : bool := (bv_extract 52 1 e) =? 1%bv.

(** Check if a PTE allows write access.
    For table descriptors: check APTable[1] (bit 62) = 0
    For block/page entries: check AP[1] (bit 7) = 0
    AP[1]=0 means EL1 read/write, AP[1]=1 means EL1 read-only. *)
Definition allow_write (lvl : Level) (e : bv 64) : Prop :=
  let ap := if decide (is_table lvl e) then (bv_extract 61 2 e)
            else (bv_extract 6 2 e) in
  (bv_extract 1 1 ap) = 0%bv.
Instance Decision_allow_write (lvl : Level) (e : bv 64) : Decision (allow_write lvl e).
Proof. unfold_decide. Defined.

(** Gives the output prefix of a pte *)
Definition output_prefix (lvl : Level) (pte : bv 64) : prefix lvl :=
  va_prefix lvl pte.

(** If the pte is a table entry (check with is_table), then give the page number
    of the next table *)
Definition next_table (pte : bv 64) : pn := bv_extract 12 36 pte.


(** ** Translation register root helpers *)

(** For the supported EL10 A1=0 configuration, TTBR0_EL1 provides the ASID
    tag even when TTBR1_EL1 provides the page-table root. *)
Definition asid_ttbr_of_root_ttbr (reg_ttbr : reg) : reg :=
  if decide (reg_ttbr = TTBR1_EL1) then TTBR0_EL1 else reg_ttbr.

(** Get the active root TTBR in a certain regime (must be EL10 for now)*)
Definition root_ttbr (regime : Regime) (upper : bool) : result string reg :=
  match regime with
  | Regime_EL10 =>
      if upper then mret (TTBR1_EL1 : reg) else mret (TTBR0_EL1 : reg)
  | _ => mthrow "The model does not support regimes other than EL10"
  end.

(** Give the page number of the root level 0 table from the TTBR value *)
Definition ttbr_root_table (val_ttbr : bv 64) : pn := bv_extract 12 36 val_ttbr.


(** * TLB *)

(** This module implements the TLB definitions that support the model *)
Module TLB.
  (** ** TLB types definitions *)
  (** *** Contexts *)
  Module NDCtxt.
    (** A TLB context consists of a level and this. Given that types of both
        contexts and entries depend on the lvl, We split off non-level context
        information into an independent record. The actual context is a
        dependent pair of a level and context *)
    Record t (lvl : Level) :=
      make {
          upper : bool;
          va : prefix lvl;
          asid : option (bv 16);
        }.
    Arguments make {_} _ _ _.
    Arguments upper {_}.
    Arguments va {_}.
    Arguments asid {_}.

    #[global] Instance eq_dec lvl : EqDecision (t lvl).
    Proof. solve_decision. Defined.

    #[global] Instance eqdep_dec : EqDepDecision t.
    Proof. intros ? ? ? [] []. decide_jmeq. Defined.

    #[export] Instance count lvl : Countable (t lvl).
    Proof.
      eapply (inj_countable'
                (fun ndctxt =>
                   let upper : bv 1 := bool_to_bv 1 ndctxt.(upper) in
                   let va := bv_zero_extend 36 ndctxt.(va) in
                   let asid : bv 17 :=
                     if ndctxt.(asid) is Some asid
                     then bv_concat 17 asid (1%bv : bv 1)
                     else 0%bv
                   in bv_concat 54 (bv_concat 53 asid va) upper)
                (fun x =>
                   let upper : bool := bv_extract 0 1 x =? 1%bv in
                   let va := bv_extract 0 _ (bv_extract 1 36 x) in
                   let asid :=
                     if bv_extract 37 1 x =? 1%bv
                     then Some (bv_extract 38 16 x)
                     else None
                   in make upper va asid
                )).
      abstract (
        intros [upper va asid];
        use (prefix_bits_36 lvl);
        cdestruct |- *** #CDestrMatch #CDestrSplitGoal; bv_solve').
    Defined.
  End NDCtxt.
  Export (hints) NDCtxt.

  (** The full context with both the Level and the rest (upper, va, asid) *)
  Module Ctxt.
    Definition t := {lvl : Level & NDCtxt.t lvl}.
    Definition make (lvl : Level) (upper : bool) (va : prefix lvl)
        (asid : option (bv 16)) : t :=
      existT lvl (NDCtxt.make upper va asid).
    Definition lvl : t → Level := projT1.
    Definition nd (ctxt : t) : NDCtxt.t (lvl ctxt) := projT2 ctxt.
    Definition upper (ctxt : t) : bool := NDCtxt.upper (nd ctxt).
    Definition va (ctxt : t) : prefix (lvl ctxt) := NDCtxt.va (nd ctxt).
    Definition asid (ctxt : t) : option (bv 16) := NDCtxt.asid (nd ctxt).
  End Ctxt.
  #[export] Typeclasses Transparent Ctxt.t.

  (** *** Entries *)
  (** A TLB entry that records everything needed to replay the translation
      function of the ISA model. For now no system register affecting
      translation other than the TTBR is allowed to be modified during
      execution*)
  Module Entry.
    Record t {lvl : Level} :=
      make {
        val_ttbr : bv 64;
        ptes : vec (bv 64) (S lvl);
      }.
    Arguments t : clear implicits.

    #[global] Instance eq_dec lvl : EqDecision (t lvl).
    Proof. solve_decision. Defined.

    #[global] Instance eqdep_dec : EqDepDecision t.
    Proof. intros ? ? ? [] []. decide_jmeq. Defined.

    #[global] Instance count lvl : Countable (t lvl).
    Proof.
      eapply (inj_countable' (fun ent => (val_ttbr ent, ptes ent))
                        (fun x => make lvl x.1 x.2)).
      abstract sauto.
    Defined.

    Definition pte {lvl} (tlbe : t lvl) := Vector.last tlbe.(ptes).

    Definition is_table {lvl} (tlbe : t lvl) := is_table lvl (pte tlbe).
    #[export] Typeclasses Transparent is_table.

    Definition next_table {lvl} (tlbe : t lvl) : pn := next_table (pte tlbe).

    Program Definition append {lvl clvl : Level}
        (tlbe : t lvl)
        (pte : bv 64)
        (CHILD : lvl + 1 = clvl) : @t clvl :=
      make _ tlbe.(val_ttbr) (ctrans _ (tlbe.(ptes) +++ [#pte])).
    Solve All Obligations with lia.

    Variant event :=
      | Load
      | Tlbi (tid : nat).

    (** The list of events that happened to an entry. This should be sorted in
        decreasing order, most recent event first. The invariant should be:
        - If a TLBI then a load happen at the same timestamp, that means the
          TLBI invalidated the entry but it was still reachable in memory so it
          was immediately reloaded.
        - It should not be possible to reach any other group of multiple
          events at the same timestamp.
        - It should not be possible to have multiple consecutive loads
        - You can have an abritrary number of consecutive TLBIs (at their
          respectives timestamp).
        - In the current setup, an entry might not have a load at all if it was
        rolled-back by a CSE
     *)
    Definition events := list (event * nat (* timestamp *)).
    #[export] Typeclasses Transparent events.
  End Entry.
  Export (hints) Entry.

  (** A full entry is a context and an entry together, which can be convenient
      for some manipulations *)
  Module FE.
    Definition t := { ctxt : Ctxt.t & Entry.t (Ctxt.lvl ctxt) }.
    #[export] Typeclasses Transparent t.
    Definition ctxt : t → Ctxt.t := projT1.
    #[export] Typeclasses Transparent ctxt.
    Definition lvl (fe : t) : Level := Ctxt.lvl (ctxt fe).
    #[export] Typeclasses Transparent lvl.
    Definition ndctxt (fe : t) : NDCtxt.t (lvl fe) := fe |> ctxt |> projT2.
    Definition upper (fe : t) : bool := Ctxt.upper (ctxt fe).
    Definition va (fe : t) : prefix (lvl fe) := Ctxt.va (ctxt fe).
    Definition vpn (fe : t) : prefix (lvl fe) := Ctxt.va (ctxt fe).
    Definition asid (fe : t) : option (bv 16) := Ctxt.asid (ctxt fe).
    Definition is_active_asid (asids : list (bv 16)) (fe : t) :=
      if asid fe is Some asid then asid ∈ asids else False.
    #[export] Instance is_active_asid_sec asids fe : Decision (is_active_asid asids fe).
    Proof. unfold_decide. Defined.
    Definition entry (fe : t) : Entry.t (lvl fe) := projT2 fe.
    Definition ttbr (fe : t) : bv 64 := Entry.val_ttbr (entry fe).
    Definition ptes (fe : t) : list (bv 64) := Entry.ptes (entry fe).
    Definition pte (fe : t) : bv 64 := Entry.pte (entry fe).
    Definition is_table (fe : t) : Prop := Entry.is_table (entry fe).
    #[export] Typeclasses Transparent is_table.
    Definition next_table (fe : t) : pn := Entry.next_table (entry fe).

    Definition make_nd (lvl : Level) (nd: NDCtxt.t lvl) (entry : Entry.t lvl) : t :=
      existT (existT lvl nd) entry.

    (** Make a root level TLB entry for the given parameters *)
    Definition make0 (upper : bool) (idx : prefix 0%fin) (asid : bv 16)
        (val_ttbr : bv 64) (pte : bv 64) : t :=
      existT (Ctxt.make 0%fin upper idx (Some asid))
        (Entry.make 0%fin val_ttbr [#pte]).

    (** Extend a full entry with the PTE found at index [idx] of the table it
        points to, giving the corresponding full entry at the next level. Fails
        on leaf level entries, which have no child level. *)
    Definition append (fe : t) (idx : bv 9) (pte : bv 64) : result string t :=
      match inspect $ child_lvl (lvl fe) with
      | Some clvl eq:e =>
          (let CHILD := child_lvl_add_one _ _ e in
          let cva : prefix clvl := bv_concat (prefix_bits clvl) (va fe) idx in
          (* A global entry drops the ASID tag from the context *)
          let casid := if bool_decide (is_global clvl pte) then None
                       else asid fe in
          let cctxt := Ctxt.make clvl (upper fe) cva casid in
          Ok (existT cctxt (Entry.append (entry fe) pte CHILD)) : result string _)
      | None eq:_ => Error "Cannot extend a leaf level TLB entry"
      end.
  End FE.
  Export (hints) FE.

  (** ** The VA-level TLB *)
  (** This is the part of the TLB indexed by VA, currently we assume
      [FEAT_nTLBPA], so there is no PA-indexed TLB, but that might change *)
  Module VATLB.
    (** For every level and context we store a list of entry that each have a
        list of events. Entries should never be removed, invalidation is just do
        by adding a TLBI event to the entry event list *)
    (* TODO: Consider moving to have just a context and using a dmap *)
    Definition T (lvl : Level) :=
      gmap (NDCtxt.t lvl) (list (Entry.t lvl * Entry.events)).
    #[export] Typeclasses Transparent T.
    Definition t := hvec T.

    (** The empty VATLB *)
    Definition init : t := hvec_func (fun lvl => ∅).

    (** Get all entries (and their events) for a context *)
    Definition get (ctxt : Ctxt.t) (vatlb : t) :
        list (Entry.t (Ctxt.lvl ctxt) * Entry.events) :=
      (hget (Ctxt.lvl ctxt) vatlb) !! (Ctxt.nd ctxt) |> default [].

    (** Get all full entries (and their events) for a context. All full entries
        will contain the input context *)
    Definition get_fe (vatlb : t) (ctxt : Ctxt.t) : list (FE.t * Entry.events) :=
      map (λ '(entry, events), (existT ctxt entry, events)) (get ctxt vatlb).

    (** Alter the entry list for a given context. Entries should generally not
        be deleted, but this is not enforced*)
    Definition alter_entries (ctxt : Ctxt.t)
        (f : list (Entry.t (Ctxt.lvl ctxt) * Entry.events) →
             list (Entry.t (Ctxt.lvl ctxt) * Entry.events))
        (vatlb : t) : t :=
      let lvl := Ctxt.lvl ctxt in
      let nd := Ctxt.nd ctxt in
      hset lvl (partial_alter
                  (λ x, if x is Some m then Some (f m) else Some (f []))
                  nd (hget lvl vatlb))
        vatlb.

    (** Get the events of a full entry *)
    #[export] Instance lookup_fe : Lookup FE.t Entry.events t :=
      λ fe tlb, lookup_assoc (FE.entry fe) (get (FE.ctxt fe) tlb) .

    (** Alter the vents of a full entry *)
    #[export] Instance partial_alter_fe : PartialAlter FE.t Entry.events t :=
      λ f fe, alter_entries (FE.ctxt fe) (partial_alter_assoc f (FE.entry fe)).

    (** Check if a full entry is active at the tip of memory (timestamp [length
        mem])*)
    Definition is_active (vatlb : t) (fe : FE.t)  :=
      if vatlb !! fe is Some ((Entry.Load, _)::_) then true else false.

    (** Apply [f] to the events of every entry of the TLB. This traverses the
        whole TLB structure once. *)
    Definition map_fe (f : FE.t → Entry.events → Entry.events) (vatlb : t) : t :=
      hmap (λ lvl,
          imap (M := gmap _) (λ ndctxt,
              map (λ '(entry, events),
                  (entry, f (FE.make_nd lvl ndctxt entry) events))))
        vatlb.

    (** Collect all full entries satisfying a property *)
    Definition collect_fe (P : FE.t → Prop) `{∀ fe, Decision (P fe)} (vatlb : t) :
        list FE.t  :=
      foldl (λ acc lvl,
          map_fold (λ ndctxt entries acc,
              foldl (λ acc '(entry, _),
                  let fe := FE.make_nd lvl ndctxt entry in
                  if bool_decide (P fe) then fe :: acc else acc)
                acc entries)
            acc (hget lvl vatlb))
        [] (enum Level).

    (** List all entries of the TLB, grouped by context: each element pairs
        a context with all of its entries and their events. *)
    Definition entries_by_ctxt (vatlb : t)
        : list { ctxt : Ctxt.t & list (Entry.t (Ctxt.lvl ctxt) * Entry.events) } :=
      foldl (λ acc lvl,
          map_fold (λ ndctxt (entries : list (Entry.t lvl * Entry.events)) acc,
              existT (existT lvl ndctxt : Ctxt.t) entries :: acc)
            acc (hget lvl vatlb))
        [] (enum Level).

  End VATLB.
  Export (hints) VATLB.

  Record t :=
    make {
        vatlb : VATLB.t;

        (** Map from physical page numbers to the list of 8-byte aligned addresses
            that are present in memory. This is immutable during execution. *)
        pte_present : gmap pn (list (bv 9));

        (** Map from physical page numbers to TLB entries that point to them *)
        next_table_cache : gmap pn (list FE.t);

        (** Root contexts active at the end of memory, for new promises *)
        asid_roots : list (bv 16 * bv 64 * bool);

        (** ETS level. Cannot be dynamically changed in this model. ETS1 is
            deprecated by Arm and behaves the same as ETS0 *)
        ets : N;
      }.

  (** Compute the [pte_present] field from the initial memory: for each physical
      page, the list of 8-byte slots of that page (identified by their index in
      the page) whose 8 bytes are all present in [init].  *)
  Definition get_pte_present (init : memoryMap) : gmap pn (list (bv 9)) :=
    (* For each page and each 8-byte slot of that page, count how many of its
       bytes are in [init]. Since each address is visited once, a slot is fully
       present exactly when its count reaches 8 *)
    let counts : gmap pn (gmap (bv 9) N) :=
      map_fold
        (λ pa _ acc,
          (* Physical addresses above 2^48 are not covered by any page number *)
          if bool_decide (bv_extract 48 pa_unused_bits pa = 0%bv) then
            partial_alter
              (λ slots,
                slots |> default ∅
                      |> partial_alter
                           (λ cnt, cnt |> default 0%N |> N.succ |> Some)
                           (bv_extract 3 9 pa)
                      |> Some)
              (pa_to_pn pa) acc
          else acc)
        ∅ init
    in
    omap
      (λ slots,
        let idxs :=
          map_fold
            (λ idx cnt acc, if bool_decide (cnt = 8%N) then idx :: acc else acc)
            [] slots
        in if idxs is [] then None else Some (reverse idxs))
      counts.


  (** ** TLB filling *)

  (** The TLB filling monad *)
  Notation tlb_mon := (stateT t (result string)).
  

  Section TLBFill.
    Context (tid : nat) (imem : memoryMap) (mem : Memory.t).

    (** *** TLB filling for an event *)
    (** TLB filling at a specific time. All function assume that the TLB is
        filled until exactly just before [time]. This means:
        - No events at [time] or after is recorded
        - If an entry is already loaded and the current event at [time] doesn't
          affect it, then it is not explored further *)
    Section TLBFillTime.
      Context (time : nat).

      (** Ensure an entry is in TLB at [time], returns true if it was just
      loaded or re-loaded at [time] *)
      Definition fill_entry (entry : FE.t) : tlb_mon bool :=
        events ← mget ((.!! entry) ∘ vatlb);
        if events is Some l then
          if l is (Entry.Load, _) :: _ then mret false
          else
            msetv ((.!! entry) ∘ vatlb) (Some ((Entry.Load, time) :: l));;
            mret true
        else
          msetv ((.!! entry) ∘ vatlb) (Some [(Entry.Load, time)]);;
          ( if decide (FE.is_table entry) then
              mset next_table_cache (alter_default (entry::.) (FE.next_table entry))
            else mret ());;
          mret true.

      (** Return a list of newly reachable level 0 entries (and add them) from a
          list of register contexts (asid, root, upper) *)
      Definition fill_root (asid_roots : list (bv 16 * bv 64 * bool)) :
          tlb_mon (list FE.t) :=
        for (asid, val_ttbr, upper) in asid_roots do
          let lvl0_pn := ttbr_root_table val_ttbr in
          indexes ← mget ((.!!!lvl0_pn) ∘ pte_present);
          for idx in indexes do
            let pte_addr := index_table lvl0_pn idx in
            if Memory.read_word pte_addr imem mem time is Ok memval then
              if decide (is_table 0%fin memval) then
                let entry := FE.make0 upper idx asid val_ttbr memval in
                loaded ← fill_entry entry;
                if loaded : bool then mret [entry] else mret []
              else mret []
            else
              (* Error for required entries missing are checked by requiring at
                least on entry during translation *)
              mret []
          end |$> List.concat
        end |$> List.concat.

      (** Fill all entry reachable from [entry] one level down. Returns all new
          table entries that need to be explored further. Assumes [entry] is a
          table entry *)
      Definition fill_from_entry (entry : FE.t) : tlb_mon (list FE.t) :=
        guard_or "Fill_from_entry should only take tables" (FE.is_table entry);;
        let next_pn := FE.next_table entry in
        indexes ← mget ((.!!!next_pn) ∘ pte_present);
        clvl ← othrow "Filling from level 3 entry" (child_lvl (FE.lvl entry));
        for idx in indexes do
          let pte_addr := index_table next_pn idx in
          if Memory.read_word pte_addr imem mem time is Ok memval then
            if decide (is_tlb_fillable clvl memval) then
              next_entry ← mlift $ FE.append entry idx memval;
              loaded ← fill_entry next_entry;
              if loaded : bool then
                if decide (is_table clvl memval)
                then mret [next_entry]
                else mret []
              else mret []
            else mret []
          else
            (* Error for required entries missing are checked by requiring at
              least on entry during translation *)
            mret []
        end |$> List.concat.

      (** Take a list of table entries and fill from all of them and returns the
          resulting new next level table entries *)
      Definition fill_from_entries_step (entries : list FE.t) : tlb_mon (list FE.t) :=
        for entry in entries do
          fill_from_entry entry
        end |$> List.concat.

      (** Fill from a list of table entries all the way down. *)
      Definition fill_from_entries (entries : list FE.t) : tlb_mon () :=
        entries ← fill_from_entries_step entries;
        entries ← fill_from_entries_step entries;
        entries ← fill_from_entries_step entries;
        (* All entries should have pushed down as there is only 3 levels to push
          through so this should be terminated, will need to change with stage
          2, or a different configuration *)
        guard_or' "fill_from_entries messed up" (entries = []).

      (** Fill all entries reachable from a list of register contexts (asid,
          root, upper) *)
      Definition fill_full (asid_roots : list (bv 16 * bv 64 * bool)) : tlb_mon () :=
        entries ← fill_root asid_roots;
        fill_from_entries entries.

      (** Get all active table entries pointing to a page table. Active means
          currently in TLB and using an active ASIDs (which means they could be
          reloading new children entries now if that page was modified). *)
      Definition get_relevant_entries (asids : list (bv 16)) (page : pn)
        : tlb_mon (list FE.t) :=
        relevant_entries ← mget ((.!!!page) ∘ next_table_cache);
        vatlb ← mget vatlb;
        relevant_entries
        |> filter (λ fe, VATLB.is_active vatlb fe ∧ FE.is_active_asid asids fe)
        |> mret.

      (** Update the TLB for the write that is present at [time] based on the
          provided context roots (asid, root, upper). This assumes that [write]
          is indeed the event that happened at [time] *)
      Definition fill_write (asid_roots : list (bv 16 * bv 64 * bool))
          (write : Msg.t) : tlb_mon () :=
        let addr := Msg.addr write in
        let page := pa_to_pn addr in
        guard_or "SCA write across pages"
          (page = pa_to_pn (addr_addN addr (N.pred (Msg.size write))));;
        let relevant_asid_roots :=
          filter (λ '(_, val_ttbr, _), ttbr_root_table val_ttbr = page) asid_roots
        in
        lvl0_entries ← fill_root relevant_asid_roots;
        let asids := asid_roots.*1.*1 |> remove_dups in
        relevant_entries ← get_relevant_entries asids page;
        fill_from_entries (lvl0_entries ++ relevant_entries).


      (** Decide if a full entry is affected by an invalidation by asid *)
      Definition affects_asid (asid : bv 16) (fe : FE.t) : Prop :=
        if (FE.asid fe) is Some te_asid then te_asid = asid else False.
      Instance Decision_affects_asid (asid : bv 16) (fe : FE.t) :
        Decision (affects_asid asid fe).
      Proof. unfold_decide. Defined.

      (** Decide if a full entry is affected by an invalidation by va *)
      Definition affects_va (upper : bool) (vpn : pn) (last : bool)
          (fe : FE.t) : Prop :=
        (vpn_prefix (FE.lvl fe) vpn = (FE.va fe))
        ∧ (if last then is_final (FE.lvl fe) (FE.pte fe) else True)
        ∧ (upper = FE.upper fe).
      Instance Decision_affects_va (upper : bool) (vpn : pn) (last : bool)
                                    (fe : FE.t):
        Decision (affects_va upper vpn last fe).
      Proof. unfold_decide. Defined.

      (** Decide if TLBI instruction affects a given full entry *)
      Definition affects (tlbi : TLBI.t) (fe : FE.t): Prop :=
        match tlbi with
        | TLBI.All tid => True
        | TLBI.Va tid asid upper vpn last =>
          affects_asid asid fe ∧ affects_va upper vpn last fe
        | TLBI.Asid tid asid => affects_asid asid fe
        | TLBI.Vaa tid upper vpn last => affects_va upper vpn last fe
        end.
      Instance Decision_affects (tlbi : TLBI.t) (fe : FE.t):
        Decision (affects tlbi fe).
      Proof. unfold_decide. Defined.

      (** Updates the TLB for the TLBI that is present at [time] based on the
          provided context roots (asid, root, upper). This assumes that [tlbi]
          is indeed the event that happened at [time] and that the current
          thread is the recipient. This invalidates all affected entries and
          then reloads the ones that are still reachable (which can lead to
          having TLBi and then a load at the same timestamp for those entries.

          The reloading strategy is different depending on whether this is a
          last-level TLBI or not *)
      Definition fill_tlbi (asid_roots : list (bv 16 * bv 64 * bool))
          (tlbi : TLBI.t) : tlb_mon () :=
        let last := TLBI.last tlbi in
        let tid := TLBI.tid tlbi in
        if last then
          (* For last TLBI invalidation, reloading from top won't work because
          parent entries are not invalidated, but reloading from parent entries
          works directly so it's a different reloading algorithm than from
          non-last TLBIs. This works because all non-last TLBIs invalidate the
          whole chain of entries *)
          let asids := asid_roots.*1.*1 |> remove_dups in
          vatlb' ← mget vatlb;
          entries ← mget (VATLB.collect_fe (affects tlbi) ∘ vatlb);
          parent_entries ← for entry in entries do
            let page := FE.next_table entry in
            mset vatlb (alter ((Entry.Tlbi tid, time)::.) entry);;
            get_relevant_entries asids page
          end |$> List.concat;
          fill_from_entries parent_entries
        else
          let inv_if_affected fe evs :=
            if decide (affects tlbi fe) then
              (Entry.Tlbi tid, time) :: evs
            else evs
          in
          mset vatlb (VATLB.map_fe inv_if_affected);;
          fill_full asid_roots.

      (** Updates the TLB for the event that is present at [time] based on the
          provided context roots (asid, root, upper). This assumes that [ev] is
          indeed the event that happened at [time] *)
      Definition fill_event (asid_roots : list (bv 16 * bv 64 * bool))
          (ev : Ev.t) : tlb_mon () :=
        match ev with
        | Ev.Msg msg => fill_write asid_roots msg
        | Ev.Tlbi tlbi recipient =>
            if decide (tid = recipient) then fill_tlbi asid_roots tlbi else mret ()
        end.
    End TLBFillTime.

    (** *** TLB filling top-level *)
    (** This provides the top-level TLB function. Whenever an TLB-relevant event
        happens, the TLB must be updated with those function.

        In theory given a local event list and a memory history, the TLB value
        should be the same (except maybe for some entries with empty event
        lists). In other words the context functions [fill_cse] and
        [fill_asid_root] should commute with [fill_promise] (as long as the time
        of the first two is before the end of memory). This fact has not been
        proven though. *)

    (** Load the TLB from [tmin] to [tmax] using a constant register context.
        Assumes that the TLB is already loaded up to [tmin] excluded and
        that the size of [mem] is [tmax] *)
    Fixpoint fill_from_btw (asid_roots : list (bv 16 * bv 64 * bool))
        (tmin tmax : nat) (mem : Memory.t) : tlb_mon () :=
      if decide (tmax < tmin) then mret () else
      if tmax is S ntmax then
        if mem is ev :: nmem then
          fill_from_btw asid_roots tmin ntmax nmem;;
          fill_event tmax asid_roots ev
        else mthrow "fill_from_btw: Invalid precondition"
      else mthrow "fill_from_btw: Invalid precondition".

    (** Load the TLB from [time] to the end of memory using a constant
        register context. Assumes that the TLB is already loaded up to
        [time] excluded *)
    Definition fill_from (asid_roots : list (bv 16 * bv 64 * bool))
        (time : nat) : tlb_mon () :=
      fill_from_btw asid_roots time (length mem) mem.

    (** Rolls back to how the TLB was just after processing memory event [time]
     *)
    Definition roll_back (time : nat) : tlb_mon () :=
      mset vatlb (VATLB.map_fe (λ _, filter (λ '(_, evtime), evtime ≤ time))).

    (** Applies the effect of a CSE to the TLB, with the post-CSE values of
        TTBRs *)
    Definition fill_cse (time : nat) (ttbr0 : bv 64) (ttbr1 : option (bv 64)) :
      tlb_mon () :=
      (* We have to roll_back the TLB to before the CSE and then reload with the
         new context. The fact that we are doing a CSE at timestamp [time]
         proves that none of the entry we are rolling back were actually used
         po-before the CSE *)
      roll_back time;;
      let asid := bv_extract 48 16 ttbr0 in
      let asid_roots' :=
        (** If the TTBR1 doesn't exist, we just don't use the upper address
            space. *)
        if ttbr1 is Some ttbr1
        then [(asid, ttbr0, false); (asid, ttbr1, true)]
        else [(asid, ttbr0, false)]
      in
      msetv asid_roots asid_roots';;
      fill_from asid_roots' (S time).

    (** Adds a new root context to the TLB at time [time] (Which means that new
        context is visible after that [time]. This is done by sytem register
        writes *)
    Definition fill_asid_root (asid_root : bv 16 * bv 64 * bool) (time : nat) :
        tlb_mon () :=
      fill_full time [asid_root];;
      fill_from [asid_root] (S time);;
      mset asid_roots (asid_root::.).

    (** Adds a new event at the end of memory. This is called whenever a promise
        is made. *)
    Definition fill_promise (ev : Ev.t) : tlb_mon () :=
      asid_roots ← mget asid_roots;
      fill_event (length mem) asid_roots ev.

  End TLBFill.


  (** ** TLB initialisation *)

  (** Get the ETS value from the initial register map *)
  Definition get_ets (iregs : registerMap) : result string N :=
  mmfr1 ← othrow "ETS is indicated in the ID_AA64MMFR1_EL1 register value" $
    reg_lookup ID_AA64MMFR1_EL1 iregs;
  mmfr1 |> bv_extract 36 4 |> bv_unsigned |> Z.to_N |> mret.

  (** Returns an intial TLB value for an initial state. Assumes Regime_EL10 for
      now, will need to be updated when supporting multiple regimes *)
  Definition init (tid : nat) (imem : memoryMap) (iregs : registerMap) :
      result string t :=
    tcr_val ← othrow "TCR_EL1 is not set" $ reg_lookup TCR_EL1 iregs;
    guard_or "TCR_EL1.A1 = 1 is not supported" (bv_extract 22 1 tcr_val = 0%bv);;
    ttbr0 ← othrow "TTBR0_EL1 not set" $ reg_lookup TTBR0_EL1 iregs;
    let asid := bv_extract 48 16 ttbr0 in
    let asid_roots :=
      (** If the TTBR1 doesn't exist, we just don't use the upper address space,
      in that same way that if a PTE is missing we don't load it. If a upper VA
      is used the model will crash saying there is no entry for that VA *)
      if reg_lookup TTBR1_EL1 iregs is Some ttbr1
      then [(asid, ttbr0, false); (asid, ttbr1, true)]
      else [(asid, ttbr0, false)]
    in
    ets ← get_ets iregs;
    make VATLB.init (get_pte_present imem) ∅ asid_roots ets
    |> fill_full imem [] 0 asid_roots
    |$> fst.


  (** ** TLB lookup *)

  (** A [TLB.Result.t] is a possible result of looking up the TLB for a specific
      context *)
  Module Result.
    Record t :=
      make {
          ttbr : bv 64;
          path : list (bv 64);
          tstart : nat; (* First timestamp that could see this entry without a fault *)
          tend : nat; (* Last timestamp that could see this entry *)
          inv_time : option nat (* If other-thread TLBI, time of the that TLBI *)
        }.
  End Result.

  Section TLBLookup.
    Context (tid : nat) (imem : memoryMap) (mem : Memory.t).
    Context (tlb : TLB.t).
    Context (ifetch : bool) (upper : bool) (vpn : pn).

    (** Get all global ctxts that are relevant for the address being translated,
        There are only leaf global entries, so level 0 is irrelevant. *)
    Definition get_global_Ctxts :=
      map (λ lvl, Ctxt.make lvl upper (vpn_prefix lvl vpn) None)
         [1; 2; 3]%fin.

    (** Get all contexts that are relevant for the given va and [asid] *)
    Definition get_asid_Ctxts (asid : bv 16) :=
      map
        (λ lvl, Ctxt.make lvl upper (vpn_prefix lvl vpn) (Some asid))
        (enum Level).

    (** Get all full entries that come from the list of contexts *)
    Definition get_fes (ctxts : list Ctxt.t) :
        list (FE.t * Entry.events) :=
      ctxts |> map (VATLB.get_fe tlb.(vatlb)) |> List.concat.

    (** Get all TLB result for the given entry parameters and list of events
        that are between [tmin] and [tmax] included. *)
    Fixpoint get_results_from_events (ttbr : bv 64) (path : list (bv 64))
        (events : Entry.events) (tmin tmax : nat) (inv_time : option nat) :=
      if decide (tmax < tmin) then [] else
      match events with
      | [] => []
      | (Entry.Load, tload) :: tl =>
          if decide (tmax < tload) then
            get_results_from_events ttbr path tl tmin tmax inv_time
          else
            if decide (tload < tmin) then
              [Result.make ttbr path tmin tmax inv_time]
            else
              let normal '() :=
                  Result.make ttbr path tload tmax inv_time ::
                    get_results_from_events ttbr path tl tmin tmax inv_time
              in
              if tl is (Entry.Tlbi tidt, ttlbi) :: tl' then
                if decide (tload = ttlbi ∧ (ifetch ∨ tidt = tid)) then
                  (* Merge the current range and the next *)
                  get_results_from_events ttbr path tl' tmin tmax inv_time
                else normal ()
              else normal ()
      | (Entry.Tlbi tidt, ttlbi) :: tl =>
          let inv_time :=
            if decide (ifetch ∨ tidt = tid) then inv_time else Some ttlbi
          in
          let ntmax := min tmax (Nat.pred ttlbi) in
          get_results_from_events ttbr path tl tmin ntmax inv_time
      end.

    (** Get all the TLB result for a full entry between [tmin] and [tmax]
        included. Returns [[]] if [tmax < tmin] *)
    Definition get_result_from_leaf_FE (fe : FE.t)
      (events : Entry.events) (tmin tmax : nat) : list Result.t :=
      if decide (tmax < tmin) then [] else
      get_results_from_events (FE.ttbr fe) (FE.ptes fe) events tmin
        tmax None.

    (** Given the TLB results that correspond to a table entry, compute the TLB
        results obtainable by reading an uncacheable entry starting from the
        input results. Takes the list of [ptes] that could be read for the
        target pte between [tmin] and [tmax]. All those values timestamps should
        be between [tmin] and [tmax] and no other reads should be missing.*)
    Fixpoint get_results_from_events_uncacheable_aux (results : list Result.t)
      (ptes : list (bv 64 * nat)) (tmin tmax : nat) (lvl : Level) :
      list Result.t :=
      if results is result :: nresults then
        (fix aux (ptes : list (bv 64 * nat)) tmax : list Result.t :=
           if ptes is (pte, tpte) :: nptes then
             let rng_max := min result.(Result.tend) tmax in
             if decide (rng_max < tmin) then []
             else
               let rest :=
                 if decide (tpte ≤ result.(Result.tstart)) then
                   get_results_from_events_uncacheable_aux nresults ptes tmin tmax lvl
                 else
                   aux nptes (Nat.pred tpte)
               in
               if decide (is_tlb_fillable lvl pte) then rest
               else
                 let rng_min := max result.(Result.tstart) tpte in
                 let real_min := max rng_min tmin in
                 let nresult :=
                   result |> set Result.path (.++[pte])
                   |> setv Result.tstart real_min
                   |> setv Result.tend rng_max
                        in nresult :: rest
        else []) ptes tmax
      else [].

    (** Get all uncacheable results reachable from a table entry, between [tmin]
        and [tmax] included *)
    Definition get_result_from_table_FE (fe : FE.t)
        (events : Entry.events) (tmin tmax : nat) :
        result string (list Result.t) :=
      if decide (tmax < tmin) then mret [] else
      if child_lvl (FE.lvl fe) is Some lvl then
        let next_table := FE.next_table fe in
        let index := vpn_level_index lvl vpn in
        let next_pte_addr := index_table next_table index in
        ptes ← Memory.read_all_pte next_pte_addr imem mem tmin tmax;
        let presults :=
          get_results_from_events (FE.ttbr fe) (FE.ptes fe) events tmin tmax None
        in
        mret $ get_results_from_events_uncacheable_aux presults ptes tmin tmax lvl
      else mret [].

    (** Get all the [Result.t] that can be obtained from en entry.
        If it is a leaf entry, then it's from that entry,
        while if it is a table entry, it's all the uncacheable entries
        reachable from that table entry *)
    Definition get_result_from_FE (fe : FE.t) (events : Entry.events)
        (tmin_ok tmin_unc tmax : nat) : result string (list Result.t) :=
      if decide $ FE.is_table fe then
        get_result_from_table_FE fe events tmin_unc tmax
      else
        mret $ get_result_from_leaf_FE fe events tmin_ok tmax.

    (** Lookup all entries reachable from TLB or walk-caches. Does not return
        level-0 invalid PTEs as they are not reachable from the TLB *)
    Definition lookup
      (tmin_ok tmin_unc tmax : nat) (asids: list (bv 16 * view)) :
        result string (list Result.t) :=
      global_results ← for (fe, events) in get_fes get_global_Ctxts do
        get_result_from_FE fe events tmin_ok tmin_unc tmax
      end |$> List.concat;
      asid_results ← for (asid, vasid) in asids do
        let tmin_ok := tmin_ok ⊔ vasid in
        let tmin_unc := tmin_unc ⊔ vasid in
        for (fe, events) in get_fes (get_asid_Ctxts asid) do
          get_result_from_FE fe events tmin_ok tmin_unc tmax
        end |$> List.concat
      end |$> List.concat;
      mret (global_results ++ asid_results).

  End TLBLookup.

End TLB.
Export (hints) TLB.

Module VATLB := TLB.VATLB.


(** * The thread state *)

(** ** Local events *)

(** The model works by tracking local event that affect the system register
context such as system register write and CSE in a per-thread event list *)

(** A system register write event *)
Module WSReg.
  Record t :=
    make {
        sreg : reg;
        val : reg_type sreg;
        view : nat
      }.

  Definition to_val_view_if (sr : reg) (wsreg : t) : option (reg_type sr * nat) :=
    if decide (wsreg.(sreg) = sr) is left eq
    then Some $ (ctrans eq wsreg.(val), wsreg.(view))
    else None.

  #[global] Instance eta : Settable _ := settable! make <sreg;val;view>.
End WSReg.

(** The local events that are tracked per-thread *)
Module LEv.
  Inductive t :=
  | Cse (t : nat)
  | Wsreg (wsreg : WSReg.t).

  Definition get_cse (lev : t) : option view :=
    match lev with
    | Cse t => Some t
    | _ => None
    end.

  Definition get_wsreg (lev : t) : option WSReg.t :=
    match lev with
    | Wsreg wsreg => Some wsreg
    | _ => None
    end.
End LEv.
Coercion LEv.Wsreg : WSReg.t >-> LEv.t.

(** Re-using the User mode model databank types *)
Module FwdItem := UMPromising.FwdItem.
Module XclItem := UMPromising.XclItem.

(** ** The thread state definition *)

Module TState.
  Record t :=
    make {
        (* The promises that this thread must fullfil
           Is must be ordered with oldest promises at the bottom of the list *)
        prom_wr : list view;
        prom_tlbi : list view;

        (* registers values and views. System(relaxed) registers are not
           modified in the [regs] field directly, but instead accumulate changes *)
        regs : dmap reg (λ reg, reg_type reg * view)%type;
        levs : list LEv.t;

        (* Per-byte coherence views *)
        coh : gmap address view;
        (* Per-ASID/page-offset translation coherence views. *)
        tcoh : gmap (bv 16 * bv 12)%type view;

        vrd : view; (* The maximum output view of a read  *)
        vwr : view; (* The maximum output view of a write  *)
        vdmbst : view; (* The maximum output view of a dmb st  *)
        vdmb : view; (* The maximum output view of a dmb ld or dmb sy  *)
        vdsb : view; (* The maximum output view of a dsb  *)
        vspec : view; (* The maximum output view of speculative operation. *)
        vcse : view; (* The maximum output view of an Context Synchronization Event *)
        vtlbi_self : view; (* The maximum output view of a TLBI for this thread *)
        vtlbi_other : view; (* The maximum output view of a TLBI broadcasted to other threads *)
        vmsr : view; (* The maximum output view of an MSR *)
        vacq : view; (* The maximum output view of an acquire access *)
        vrel : view; (* The maximum output view of an release access *)

        (* Per-byte forwarding bank *)
        fwdb : gmap address FwdItem.t;

        (* The latest load-exclusive, if its matching store-exclusive has not
           run yet. *)
        xclb : option XclItem.t;

        (* The TLB structure. This is for caching purposes. The TLB can be
           functionally computed from the regitsers (regs + levs) and memory
           state. [None] is when translation is disabled *)
        tlb : option TLB.t;
      }.

  #[global] Instance eta : Settable _ :=
    settable! make <prom_wr; prom_tlbi;regs;levs;coh;tcoh;vrd;vwr;vdmbst;vdmb;vdsb;
                    vspec;vcse;vtlbi_self;vtlbi_other;vmsr;vacq;vrel;fwdb;xclb;
                    tlb>.

  Definition init (tid : nat) (imem : memoryMap) (iregs : registerMap) :=
    sctlr ← othrow "SCTLR_EL1 is not set" $ reg_lookup SCTLR_EL1 iregs;
    tlb ← (if bv_extract 0 1 sctlr =? 1%bv then
            TLB.init tid imem iregs |$> Some else mret None);
    el ← othrow "CurrentEL is not set" $ reg_lookup CurrentEL iregs;
    guard_or "EL 2 and above unsupported" (bv_unsigned el ≤ 1)%Z;;
    (* TODO check other system register values?*)
    mret
    ({|
      prom_wr := [];
      prom_tlbi := [];
      regs := dmap_map (λ _ v, (v, 0%nat)) iregs;
      levs := []; (* latest event at the top of the list *)
      coh := ∅;
      tcoh := ∅;
      vrd := 0;
      vwr := 0;
      vdmbst := 0;
      vdmb := 0;
      vdsb := 0;
      vspec := 0;
      vcse := 0;
      vtlbi_self := 0;
      vtlbi_other := 0;
      vmsr := 0;
      vacq := 0;
      vrel := 0;
      fwdb := ∅;
      xclb := None;
      tlb := tlb;
    |})%nat.

  Definition run_tlb (tlb_upd : stateT TLB.t (result string) ()) (ts : t) :
      result string t :=
    if ts.(tlb) is Some otlb then
      ntlb ← tlb_upd otlb |$> fst;
      mret (setv tlb (Some ntlb) ts)
    else mret ts.

  Definition lev_cur (ts : t) := length ts.(levs).

  Definition filter_wsreg : list LEv.t → list WSReg.t := omap LEv.get_wsreg.

  Definition filter_cse : list LEv.t → list view := omap LEv.get_cse.

  (** Convert a CSE timestamp to the suffix position expected by
      read_sreg_last. Events are stored newest-first in levs, so an event at
      index i corresponds to the suffix of length lev_cur ts - i. *)
  Definition cse_position (ts : t) (cse : view) : nat :=
    match List.find
      (λ '(_, lev), if lev is LEv.Cse t then t =? cse else false)
      (enumerate ts.(levs)) with
    | Some (i, _) => (lev_cur ts - i)%nat
    | None => 0%nat
    end.

  (** Read the last system register write at system register position s *)
  Definition read_sreg_last (ts : t) (sreg : reg) (s : nat) :=
    let newval :=
      ts.(levs)
      |> drop ((lev_cur ts) - s)
      |> filter_wsreg
      |> omap (WSReg.to_val_view_if sreg)
      |> hd_error in
    newval ∪ dmap_lookup sreg ts.(regs).

  (** Read all possible system register values for sreg assuming the optional
      last synchronization timestamp tcse *)
  Definition read_sreg_by_cse (ts : t) (sreg : reg) (tcse : option nat)
    : option (list (reg_type sreg * view))
    :=
    let s := if tcse is Some tcse then cse_position ts tcse else 0%nat in
    sync_val ← read_sreg_last ts sreg s;
    let rest :=
      ts.(levs)
      |> take ((lev_cur ts) - s)
      |> filter_wsreg
      |> omap (WSReg.to_val_view_if sreg)
    in Some $ sync_val :: rest.

  (** Read the most recent system register write (for MRS implementation). *)
  Definition read_sreg_direct (ts : t) (sreg : reg) :=
    read_sreg_last ts sreg (lev_cur ts).

  (** Read possible system register values from the timestamp of the most recent CSE *)
  Definition read_sreg_indirect (ts : t) (sreg : reg) :=
    let max_cse :=
      ts.(levs)
           |> filter_cse
           |> hd_error
    in
    read_sreg_by_cse ts sreg max_cse.

  (** Read system register values at the timestamp t *)
  Definition read_sreg_at (ts : t) (sreg : reg) (t : nat) :
      option (list (reg_type sreg * nat)) :=
    let last_cse :=
      ts.(levs)
           |> filter_cse
           |> filter (λ tcse, tcse < t)
           |> hd_error
    in
    read_sreg_by_cse ts sreg last_cse
      |$> omap (M:=list) (
            λ '(val, view),
              if bool_decide (view ≤ t)
              then Some (val, view)
              else None).

  (** Read uniformly a register of any kind. *)
  Definition read_reg (ts : t) (r : reg) : option (reg_type r * view) :=
    if bool_decide (r ∈ relaxed_regs) then
      read_sreg_direct ts r
    else dmap_lookup r ts.(regs).

  (** Extract a plain register map from the thread state without views. *)
  Definition reg_map (ts : t) : registerMap :=
    dmap_map
      (λ r rv,
        if bool_decide (r ∈ relaxed_regs)
        then from_option fst rv.1 (read_sreg_direct ts r)
        else rv.1)
      ts.(regs).

  (** Extract the PC from the thread state, without rebuilding a full register
      map. This is used to decide if a thread has terminated on every step *)
  Definition pc (ts : t) : option (reg_type pc_reg) :=
    fst <$> dmap_lookup pc_reg ts.(regs).

  Lemma pc_reg_map (ts : t) : pc ts = reg_lookup pc_reg (reg_map ts).
  Proof. unfold pc, reg_map, reg_lookup. by rewrite dmap_lookup_map. Qed.

  (** Sets the value of a register *)
  Definition set_reg (reg : reg) (rv : reg_type reg * view) (ts : t) : option t :=
    if decide (is_Some (dmap_lookup reg ts.(regs))) then
      Some $ set regs (dmap_insert reg rv) ts
    else None.

  (** Add a system register write event to the local event list *)
  Definition add_wsreg (tid : nat) (imem : memoryMap) (mem : Memory.t)
      (sreg : reg) (val : reg_type sreg) (v : view) (ts : t) :
    result string t :=
    let wsreg := WSReg.make sreg val v in
    ts ←
      run_tlb
        ( match sreg return reg_type sreg → stateT TLB.t (result string) () with
          | TTBR0_EL1 =>
              λ val,
              TLB.fill_asid_root tid imem mem (bv_extract 48 16 val, val, false) v
          | TTBR1_EL1 =>
              λ val,
              ttbr0s ←
                othrow "Can't read TTBR0_EL1" $
                  read_sreg_indirect ts TTBR0_EL1;
              for (ttbr0, v0) in ttbr0s do
                let v := v ⊔ v0 in
                TLB.fill_asid_root tid imem mem (bv_extract 48 16 ttbr0, val, true) v
              end;;
              mret ()
          | _ => λ _, mret ()
         end val) ts;
    ts |> set levs ((LEv.Wsreg wsreg)::.) |> mret (M := result string).

  (** Returns the minimum coherence flag for a range of addresses. Returns
      [None] if the range is empty *)
  Definition min_cohs (addrs : list address) (ts : t) : option nat :=
    foldl
      (λ res addr, union_with (λ x y, Some $ min x y) res $ ts.(coh) !! addr)
      None addrs.

  (** Sets the coherence view of a byte address *)
  Definition set_coh (a : address) (v : view) : t → t :=
    set coh (insert a v).

  (** Updates the coherence view of a byte address *)
  Definition update_coh (a : address) (v : view) (ts : t) : t :=
    set_coh a (max v (ts.(coh) !!! a)) ts.

  (** Updates the coherence view for a list of (address, view) pairs. *)
  Definition update_cohs (avs : list (address * view)) (ts : t) : t :=
    foldr (λ '(a, v), update_coh a v) ts avs.

  (** Max coherence view across a range of byte addresses *)
  Definition max_cohs (addrs : list address) (ts : t) : view :=
    foldr max 0%nat (map (λ a, ts.(coh) !!! a) addrs).

  Definition va_page_offsets (va : bv 64) (size : N) : list (bv 12) :=
    map (λ n, bv_extract 0 12 (va `+Z` (Z.of_N n))%bv) (seqN 0 size).

  Definition get_tcoh (asid : bv 16) (page_offset : bv 12) (ts : t) : view :=
    ts.(tcoh) !!! (asid, page_offset).

  Definition update_tcoh (asid : bv 16) (page_offset : bv 12) (v : view) (ts : t) : t :=
    set tcoh
      (partial_alter (λ ov, Some (max v (default 0 ov)))
        (asid, page_offset)) ts.

  Definition update_tcohs (asid : bv 16) (page_offsets : list (bv 12)) (v : view) (ts : t) : t :=
    foldr (λ page_offset, update_tcoh asid page_offset v) ts page_offsets.

  Definition tcohs_before_inv_time (asid : bv 16) (page_offsets : list (bv 12))
      (inv_time : option nat) (ts : t) : Prop :=
    match inv_time with
    | Some inv_t => ∀ page_offset ∈ page_offsets, (get_tcoh asid page_offset ts < inv_t)%nat
    | None => True
    end.
  #[global] Instance Decision_tcohs_before_inv_time asid page_offsets inv_time ts :
    Decision (tcohs_before_inv_time asid page_offsets inv_time ts).
  Proof. unfold_decide. Defined.

  (** Updates the forwarding bank for an address. *)
  Definition set_fwdb (addr : address) (fi : FwdItem.t) : t → t :=
    set fwdb (insert addr fi).

  (** Sets the forwarding bank for every byte address in a write range. The size
      of [data] should be [8 * (length addrs)] *)
  Definition set_fwdbs (addrs : list address) `(data : bv n)
      (time : nat) (vdata : view) (xcl_view : option view) (ts : t) : t :=
    let bytes := data |> bv_to_bytes 8 in
    foldl (λ ts '(a, byte), set_fwdb a (FwdItem.make time vdata byte xcl_view) ts)
      ts (zip addrs bytes).

  (** Set the exclusive bank to the footprint of the latest load exclusive. *)
  Definition set_xclb (time : nat) (addr : address) (size : N)
      (vpost : view) : t → t :=
    setv xclb (Some (XclItem.make time addr size vpost)).

  (** Clears the exclusive bank, to mark a store exclusive *)
  Definition clear_xclb : t → t := setv xclb None.

  (** Updates a view that from the state, by taking the max of new value and
      the current value.

      For example `update rmax vnew t` does t.rmax ← max t.rmax vnew *)
  Definition update (acc : t → view) {_: Setter acc}
             (v : view) : t → t :=
    set acc (max v).

  (** Updates two view in the same way as update. Purely for convenience *)
  Definition update2 (acc1 acc2 : t → view) {_: Setter acc1} {_: Setter acc2}
             (v : view) : t → t :=
    (update acc1 v) ∘ (update acc2 v).

  (** Add a promise to the write promise set *)
  Definition promise_write (v : view) : t → t := set prom_wr (v ::.).

  (** Add a promise to the TLBI promise set *)
  Definition promise_tlbi (v : view) : t → t := set prom_tlbi (v ::.).

  Definition process_event (tid : nat) (imem : memoryMap) (mem : Memory.t)
      (ev : Ev.t) : t → result string t :=
    run_tlb (TLB.fill_promise tid imem mem ev).

  Definition emit_promise (tid : nat) (imem : memoryMap) (mem : Memory.t)
      (ev : Ev.t) (ts : t) : result string t :=
    let ts :=
      if bool_decide (Ev.tid ev = tid) then
        if ev is Ev.Msg _ then promise_write (length mem) ts
        else promise_tlbi (length mem) ts
      else ts in
    process_event tid imem mem ev ts.

  (** Check that all pending promises are after the given view *)
  Definition no_promises_until (v : view) (ts : t) : Prop :=
    ∀ p ∈ ts.(prom_wr) ++ ts.(prom_tlbi), (v < p)%nat.
  #[global] Instance Decision_no_promises_until (v : view) (ts : t) :
    Decision (no_promises_until v ts).
  Proof. unfold_decide. Defined.

  (** Check that all pending write promises are after the given view *)
  Definition no_write_promises_until (v : view) (ts : t) : Prop :=
    ∀ p ∈ ts.(prom_wr),(v < p)%nat.
  #[global] Instance Decision_no_write_promises_until (v : view) (ts : t) :
    Decision (no_write_promises_until v ts).
  Proof. unfold_decide. Defined.

  (** Compute the minimum of all pending promises *)
  Definition min_promise (vmax_t : view) (ts : t) : view :=
    foldr (λ p v, min v p) (vmax_t + 1) (ts.(prom_wr) ++ ts.(prom_tlbi)).

  (** Compute all the timestamps a CSE could happen at, this is inefficient but
      hard to optimize *)
  Definition cse_candidates
      (vpre vmax_t : view) (ts : t) : list view :=
    seq vpre (min_promise vmax_t ts - vpre).

  (** Perform a context synchronization event *)
  Definition cse (imem : memoryMap) (mem : Memory.t) (tid : nat) (v : view)
    (ts : t) : result string t :=
    let ts := ts |> update vcse v |> set levs (LEv.Cse v ::.) in
    ttbr0 ← othrow "Can't read TTBR0_EL1" $ read_sreg_direct ts TTBR0_EL1;
    let ttbr1 := read_sreg_direct ts TTBR1_EL1 |$> fst in
    ts ← run_tlb (TLB.fill_cse tid imem mem v ttbr0.1 ttbr1) ts;
    ts |> update vcse v |> set levs (LEv.Cse v ::.) |> mret.

  Definition tlb_lookup (tid : nat) (imem : memoryMap) (mem : Memory.t) (ts : t)
      (ifetch upper : bool) (vpn : pn) (tmin_ok tmin_unc tmax : nat) :
    result string (list TLB.Result.t) :=
    tlb ← othrow "TLB lookup, but translation disabled by SCTLR_EL1" $ ts.(tlb);
    ttbr0s ← othrow "Can't read TTBR0_EL1" $ read_sreg_indirect ts TTBR0_EL1;
    let asids := ttbr0s |> map (λ '(ttbr0, vttbr0), (bv_extract 48 16 ttbr0, vttbr0)) in
    from_tlb ← TLB.lookup tid imem mem tlb ifetch upper vpn tmin_ok tmin_unc tmax asids;
    (* Still missing invalid lookups from root, those do not go through the TLB *)
    from_lvl0_inv ←
    ( if decide (tmin_unc ≤ tmax) then
        ttbrs ←
          (if upper then
            othrow "Can't read TTBR1_EL1, but using negative addresses" $
              read_sreg_indirect ts TTBR1_EL1 : result string (list (bv 64 * view))
          else mret ttbr0s);
        let lvl0_index := vpn_level_index 0%fin vpn in
        for (ttbr, vttbr) in ttbrs do
          let pte_addr := index_table (ttbr_root_table ttbr) lvl0_index in
          let tmin := tmin_unc ⊔ vttbr in
          ptes ← Memory.read_all_pte pte_addr imem mem tmin tmax;
          ptes
          |> filter (λ '(pte, _), ¬ is_tlb_fillable 0%fin pte)
          (* TODO figure out if top-level invalid entries are concerned by *)
          (*      invalidation times *)
          |> map (λ '(pte, vpte), TLB.Result.make ttbr [pte] (tmin ⊔ vpte) tmax None)
          |> mret
        end |$> List.concat
      else mret []);
    mret (from_tlb ++ from_lvl0_inv).

  Definition ets2 (ts : t) : bool :=
    if ts.(tlb) is Some tlb then bool_decide (2 ≤ tlb.(TLB.ets))%N else false.
  Definition ets3 (ts : t) : bool :=
    if ts.(tlb) is Some tlb then bool_decide (3 ≤ tlb.(TLB.ets))%N else false.
End TState.


(** * Instruction semantics *)

(** ** IIS definition *)

(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  (* Translation Results *)
  Module TransRes.
    Record t :=
      make {
          trans_start : nat;
          trans_end : nat;
          root : option {ttbr : reg & reg_type ttbr};
          remaining : list (bv 64)
        }.

    Definition pop (tres : t): result string (t * bv 64) :=
      if tres.(remaining) is h :: tl then mret (setv remaining tl tres, h)
      else mthrow "Couldn't pop the next PTE: error in translation assumptions".
  End TransRes.

  Record t :=
    make {
        strict : view;
        (* The translations results of the latest translation *)
        trs : option TransRes.t;
        inv_time : option nat;
        rmw_read : option (nat * bool)
      }.

  Definition init : t := make 0 None None None.

  (** Add a new view to the IIS *)
  Definition add (v : view) (iis : t) : t :=
    iis |> set strict (max v).

  Definition set_trs (tres : TransRes.t) :=
    setv trs (Some tres).

  Definition set_inv_time (ti_opt : option nat) :=
    setv inv_time ti_opt.

End IIS.

Definition view_if := UMPromising.view_if.

Section RunOutcome.
  Context (n_threads tid : nat) (imem : memoryMap).
  Notation prom_mon := (Exec.t (PPState.t TState.t Ev.t IIS.t) string).


(** ** Register semantics *)

Definition run_reg_general_read (reg : reg) (racc : reg_acc) :
    Exec.t (TState.t * IIS.t) string (reg_type reg * view) :=
  ts ← mget fst;
  if decide (reg ∈ relaxed_regs) then
    if decide (is_Some racc)
      then othrow
            ("Register " ++ pretty reg ++ " unmapped on direct read")%string
            $ TState.read_sreg_direct ts reg
    else
      valvs ← othrow
              ("Register " ++ pretty reg ++ " unmapped on indirect read")%string
              $ TState.read_sreg_indirect ts reg;
      mchoosel valvs
  else
    othrow
      ("Register " ++ pretty reg ++ " unmapped; cannot read")%string
      $ TState.read_reg ts reg.

Definition run_reg_trans_read (reg : reg) (racc : reg_acc)
      (trs : IIS.TransRes.t) :
    Exec.t TState.t string (reg_type reg * view) :=
  guard_or "Register read during the translation should be implicit"
    (¬ (is_Some racc));;
  root ← othrow "Could not find the translation root: error in translation assumptions"
    (trs.(IIS.TransRes.root));
  if decide (root.T1 = reg) is left eq then
    mret (ctrans eq root.T2, 0%nat)
  else
    ts ← mGet;
    guard_or ("The register should be strict: " ++ pretty reg)%string (reg ∈ strict_regs);;
    othrow
      ("Register " ++ pretty reg ++ " unmapped; cannot read")%string
      $ TState.read_reg ts reg.

(** Run a RegRead outcome.
    Returns the register value based on the type of register and the access type. *)
Definition run_reg_read (reg : reg) (racc : reg_acc) :
    Exec.t (TState.t * IIS.t) string (reg_type reg) :=
  '(val, view) ←
    (* Check if the register is read during the translation *)
    iis ← mget snd;
    if iis.(IIS.trs) is Some trs then
      Exec.liftSt fst $ run_reg_trans_read reg racc trs
    else
      run_reg_general_read reg racc;
  mset snd $ IIS.add view;;
  mret val.

(** Run a RegWrite outcome.
    Updates the thread state using a register value *)
Definition run_reg_write (reg : reg) (racc : reg_acc) (val : reg_type reg) :
    prom_mon () :=
  guard_or
    ("Cannot write to unknown register " ++ pretty reg)%string
    (¬(is_reg_unknown reg));;
  iis ← mget PPState.iis;
  ts ← mget PPState.state;
  mem ← mget PPState.mem;
  let vreg := IIS.strict iis in
  match racc with
  | Some _ =>
      (* Direct system-register writes are MSRs. *)
      let vpre := ts.(TState.vcse) ⊔ ts.(TState.vspec) ⊔ ts.(TState.vdsb) in
      vpost ←
        if decide (reg ∈ relaxed_regs) then
          '(_, view) ← othrow
                        ("Register " ++ pretty reg ++ " unmapped on direct read")%string
                        $ TState.read_sreg_direct ts reg;

          let vpost := vreg ⊔ vpre ⊔ view in
          nts ← mlift $ TState.add_wsreg tid imem mem reg val vpost ts;
          msetv PPState.state nts;;
          mret vpost
        else if decide (reg ∈ strict_regs) then
          let vpost := vreg ⊔ vpre in
          nts ← othrow
                  ("Register " ++ pretty reg ++ " unmapped; cannot write")%string
                  $ TState.set_reg reg (val, vpost) ts;
          msetv PPState.state nts;;
          mret vpost
        else
          mthrow ("Cannot write register " ++ pretty reg ++
                  " with direct system-register access")%string;
      mset PPState.state $ TState.update TState.vmsr vpost;;
      mset PPState.iis $ IIS.add vpost
  | None =>
      if reg =? pc_reg then
        guard_discard (TState.no_promises_until vreg ts);;
        mset PPState.state $ TState.update TState.vspec vreg;;
        ts ← mget PPState.state;
        nts ← othrow
                ("Register " ++ pretty reg ++ " unmapped; cannot write")%string
                $ TState.set_reg reg (val, 0%nat) ts;
        msetv PPState.state nts
      else if decide (reg ∈ strict_regs) then
        nts ← othrow
                ("Register " ++ pretty reg ++ " unmapped; cannot write")%string
                $ TState.set_reg reg (val, vreg) ts;
        msetv PPState.state nts
      else
        mthrow ("Cannot write relaxed register " ++ pretty reg ++
                " without direct system-register access")%string
  end.


(** ** Memory semantics *)

(** Reads an instruction from initial memory.  Returns the [size]-byte
    instruction word as a [bv (8 * size)] formed by concatenating the
    bytes in [addr_range addr size]. Fails if [size] is not 4, or
    if any byte in the range has been overwritten by a later write. *)
Definition read_imem (addr : address) (mem : Memory.t) : Exec.res string (bv 32) :=
  bytes ← mlift $ Memory.read_initial addr 4 imem mem;
  mret (bv_of_bytes 32 bytes).

(** Performs a multi-byte explicit memory read. This involves multiple steps:
    - Computing the minimum view
    - Reading main memory at all interesting timestamps with [Memory.read_all]
    - Applying forwarding ([read_fwd])
    - Do a coherence check
    - Do an translation invalidation check (about [invalidation_time])
    - Update all the views that should be updated
    - If exclusive, set the exclusive bank
    - If atomic RMW, remember this read for the matching write *)
Definition read_mem_explicit (addr : address) (size : N) (macc : mem_acc) :
    prom_mon (bv (8 * size)) :=
  ts ← mget PPState.state;
  vaddr ← mget (IIS.strict ∘ PPState.iis);
  guard_discard (TState.no_promises_until vaddr ts);;
  let addrs := addr_range addr size in
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
              ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
                (* Strong Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vcoh := default 0%nat $ TState.min_cohs addrs ts in
  let vpre := vaddr ⊔ vbob in
  mem ← mget PPState.mem;
  candidates ← mlift $ Memory.read_all addr size imem mem (vpre ⊔ vcoh);
  candidate ← mchoosel candidates;
  let tread := max_list_with snd candidate in
  (* Record every atomic RMW read so the later write can check atomicity and
     apply acquire ordering. *)
  ( if is_atomic_rmw macc
    then msetv (IIS.rmw_read ∘ PPState.iis) (Some (tread, is_rel_acq macc))
    else mret ());;
  (* per-byte (value, view, write-timestamp) after forwarding *)
  let fwd_bytes :=
    map (λ '(addr, (byte, twrite)),
        UMPromising.read_fwd ts.(TState.fwdb) macc tread addr
        |> default (byte, tread, twrite)) $
      zip addrs candidate in

  let bytes := fwd_bytes.*1.*1 in
  let read_views := fwd_bytes.*1.*2 in
  let twrites := fwd_bytes.*2 in
  (* Per-byte coherence: each byte's twrite ≥ that byte's coh view. *)
  guard_discard (∀ '(a,t) ∈ zip addrs twrites, (ts.(TState.coh) !!! a ≤ t)%nat);;
  let res := bv_of_bytes (8 * size) bytes in
  let vreads := foldr max 0%nat read_views in
  let vpost := vpre ⊔ vreads in
  (* Check that the explicit access is done before the translation becomes invalid *)
  inv_time ← mget (IIS.inv_time ∘ PPState.iis);
  guard_discard' (if inv_time is Some inv_t then (vpost < inv_t)%nat else True);;
  mset PPState.state $ TState.update_cohs (zip addrs twrites);;
  mset PPState.state $ TState.update TState.vrd vpost;;
  mset PPState.state $ TState.update TState.vacq (view_if (is_rel_acq macc) vpost);;
  mset PPState.state $ TState.update TState.vspec vaddr;;
  ( if is_exclusive macc
    then mset PPState.state $ TState.set_xclb tread addr size vpost
    else mret ());;
  mset PPState.iis $ IIS.add vpost;;
  mret res.

(** Read a PTE from the TLB entry selected at translation start *)
Definition read_pte : prom_mon (bv 64) :=
  tres_opt ← mget (IIS.trs ∘ PPState.iis);
  tres ← othrow "TTW read before translation start" tres_opt;
  '(ntres, val) ← mlift (IIS.TransRes.pop tres);
  msetv (IIS.trs ∘ PPState.iis) (Some ntres);;
  mret val.

(** Performs a memory write for a thread [tid] at [addr]:

    - First attempt to fulfill an existing promises, or add a new one otherwise
    - Compute the minimum view of the write
    - Discard if the write is not compatible with that view or coherence checks
    - Discard if the write is supposed to be atomic, but other writes intervened
    - Update all the views that should be updated
    - Set the forwarding bank
    - If a new promise was added, return its minimum view, otherwise [None] *)
Definition write_mem (addr : address) (size : N) (macc : mem_acc)
    (data : bv (8 * size)) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string (option view) :=
  let msg := Msg.make tid addr size data in
  let is_release := is_rel_acq macc in
  let addrs := addr_range addr size in
  ts ← mget PPState.state;
  mem ← mget PPState.mem;
  '(time, new_promise) ←
    match Memory.fulfill msg (TState.prom_wr ts) mem with
    | Some time => mret (time, false)
    | None =>
      let ev := Ev.Msg msg in
      time ← Exec.liftSt PPState.mem $ Memory.promise ev;
      nts ← mlift $ TState.process_event tid imem mem ev ts;
      msetv PPState.state nts;;
      mret (time, true)
    end;
  '(read_acquire : bool) ←
    (if is_atomic_rmw macc then
      rmw_read_opt ← mget (IIS.rmw_read ∘ PPState.iis);
      '(tread, read_acquire) ← othrow "RMW write without a read" rmw_read_opt;
      guard_discard' (Memory.exclusive tid addr size tread time mem);;
      msetv (IIS.rmw_read ∘ PPState.iis) None;;
      mret read_acquire
    else mret false);
  let vbob :=
    ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
    ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
    ⊔ view_if is_release (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  vdata ← mget (IIS.strict ∘ PPState.iis);
  let vpre := vdata ⊔ ts.(TState.vspec) ⊔ vbob in
  guard_discard (vpre < time ∧ ∀ a ∈ addrs, ts.(TState.coh) !!! a < time)%nat;;
  (* Check that the explicit access is done before the translation becomes invalid *)
  inv_time ← mget (IIS.inv_time ∘ PPState.iis);
  guard_discard' (if inv_time is Some inv_t then (time < inv_t)%nat else True);;
  mset (TState.prom_wr ∘ PPState.state) $ filter (λ t, t ≠ time);;
  mset PPState.state $ TState.update_cohs (map (., time) addrs);;
  mset PPState.state $ TState.update TState.vwr time;;
  mset PPState.state $ TState.update TState.vrel (view_if is_release time);;
  (* Advance the acquire view to the write timestamp so later operations are ordered after the full RMW. *)
  ( if (is_atomic_rmw macc && is_rel_acq macc && read_acquire)
    then mset PPState.state $ TState.update TState.vacq time
    else mret ());;

  fwd_xcl_view ← if is_exclusive macc then
      match TState.xclb ts with
      | None => mdiscard
      | Some xcl =>
        mset PPState.state $ TState.clear_xclb;;
        if decide (addr = xcl.(XclItem.addr) ∧ size = xcl.(XclItem.size)) then
          guard_discard'
            (Memory.exclusive tid addr size xcl.(XclItem.time) time mem);;
          mret (Some xcl.(XclItem.view))
        else
          (* PA/size mismatch fails the exclusive-monitor check; STXR failure is no-write. *)
          mdiscard
      end
    else mret None;

  mset PPState.state $ TState.set_fwdbs addrs data time vdata fwd_xcl_view;;
  mret (if (new_promise : bool) then Some vpre else None).


(** ** Barrier semantics *)

(** Perform a Context Synchronization Event (CSE).

    CSEs occur at ISB instructions, exception taking, and exception returns.
    They ensure that all prior context-changing operations (MSR writes) are
    observed before subsequent instruction fetch and execution.

    Non-deterministically chooses a view between the current dependencies
    and [vmax_t], then updates [vcse] and adds a CSE marker to the local
    event list. *)
Definition run_cse (vmax_t : view) : prom_mon () :=
  ts ← mget PPState.state;
  mem ← mget PPState.mem;
  iis ← mget PPState.iis;
  let v := ts.(TState.vspec) ⊔ ts.(TState.vcse)
            ⊔ ts.(TState.vdsb) ⊔ ts.(TState.vmsr) in
  let vpre := IIS.strict iis ⊔ v in
  guard_discard (TState.no_promises_until vpre ts);;
  vpost ← mchoosel $ TState.cse_candidates vpre vmax_t ts;
  nts ← mlift $ TState.cse imem mem tid vpost ts;
  msetv PPState.state nts;;
  mset PPState.iis $ IIS.add vpost.

(** Execute a barrier instruction (DMB, DSB, or ISB).

    Barriers enforce ordering between memory accesses by updating view
    state. The specific semantics depend on the barrier type:
    - DMB: Orders loads/stores without waiting for completion.
    - DSB: Stronger ordering, waits for prior operations to complete.
    - ISB: Context synchronization, handled via [run_cse]. *)
Definition run_barrier (barrier : barrier) (vmax_t : view) : prom_mon () :=
  ts ← mget PPState.state;
  match barrier with
  | Barrier_DMB dmb => (* dmb *)
      match dmb.(DxB_types) with
      | MBReqTypes_All (* dmb sy *) =>
          let vpost :=
            ts.(TState.vrd) ⊔ ts.(TState.vwr)
            ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb)
          in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdmb vpost;;
          mset PPState.iis $ IIS.add vpost
      | MBReqTypes_Reads (* dmb ld *) =>
          let vpost := ts.(TState.vrd) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdmb vpost;;
          mset PPState.iis $ IIS.add vpost
      | MBReqTypes_Writes (* dmb st *) =>
          let vpost := ts.(TState.vwr) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdmbst vpost;;
          mset PPState.iis $ IIS.add vpost
      end
  | Barrier_DSB dsb => (* dsb *)
      match dsb.(DxB_types) with
      | MBReqTypes_All (* dsb sy *) =>
          let vtlbi :=
            if decide (dsb.(DxB_domain) = MBReqDomain_Nonshareable)
            then ts.(TState.vtlbi_self)
            else ts.(TState.vtlbi_self) ⊔ ts.(TState.vtlbi_other)
          in
          let vpost :=
            ts.(TState.vrd) ⊔ ts.(TState.vwr)
            ⊔ ts.(TState.vdmb) ⊔ ts.(TState.vdmbst)
            ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) ⊔ vtlbi
          in
          guard_discard (TState.no_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdsb vpost;;
          mset PPState.iis $ IIS.add vpost
      | MBReqTypes_Reads (* dsb ld *) =>
          let vpost := ts.(TState.vrd) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdsb vpost;;
          mset PPState.iis $ IIS.add vpost
      | MBReqTypes_Writes (* dsb st *) =>
          let vpost := ts.(TState.vwr) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdsb vpost;;
          mset PPState.iis $ IIS.add vpost
      end
  | Barrier_ISB () => run_cse vmax_t
  | _ => mthrow "Unsupported barrier"
  end.

(** ** Translation semantics *)

(** Prepare a recipient-specific TLBI visibility event.

    TLBI effects are represented as one [Ev.Tlbi] event per recipient, so
    different threads may observe the same TLBI at different memory times.  This
    helper either fulfills a matching promised event or creates a fresh one, and
    returns its timestamp with a flag indicating whether it was newly created. *)
Definition materialize_tlbi_for_recipient
    (vpre : view) (tlbi : TLBI.t) (recipient : nat) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string (view * bool) :=
  let ev := Ev.Tlbi tlbi recipient in
  ts ← mget PPState.state;
  mem ← mget PPState.mem;
  '(time, new_tlbi_event) ←
    match Memory.fulfill ev (TState.prom_tlbi ts) mem with
    | Some t => mret (t, false)
    | None =>
      time ← Exec.liftSt PPState.mem $ Memory.promise ev;
      nts ← mlift $ TState.process_event tid imem mem ev ts;
      msetv PPState.state nts;;
      mret (time, true)
    end;
  guard_discard (vpre < time)%nat;;
  mset (TState.prom_tlbi ∘ PPState.state) (filter (λ t, t ≠ time));;
  mret (time, new_tlbi_event).

Definition run_tlbi (viio : view) (tlbi : TLBIInfo) : prom_mon (option view) :=
  guard_or
    "TLBIs in other regimes than EL10 are unsupported"
    (tlbi.(TLBIInfo_rec).(TLBIRecord_regime) = Regime_EL10);;
  let asid := tlbi.(TLBIInfo_rec).(TLBIRecord_asid) in
  let va := tlbi.(TLBIInfo_rec).(TLBIRecord_address) in
  let last := tlbi.(TLBIInfo_rec).(TLBIRecord_level) =? TLBILevel_Last in
  let upper := bv_extract 55 1 va =? 1%bv in
  let vpn := va_to_vpn va in
  ts ← mget PPState.state;
  iis ← mget PPState.iis;
  let vpre := ts.(TState.vcse) ⊔ ts.(TState.vdsb) ⊔ ((*iio*) IIS.strict iis)
              ⊔ viio ⊔ ts.(TState.vspec) in
  '(tlbiev : TLBI.t) ←
    match tlbi.(TLBIInfo_rec).(TLBIRecord_op) with
    | TLBIOp_ALL => mret $ TLBI.All tid
    | TLBIOp_VMALL => mret $ TLBI.All tid
    | TLBIOp_ASID => mret $ TLBI.Asid tid asid
    | TLBIOp_VAA => mret $ TLBI.Vaa tid upper vpn last
    | TLBIOp_VA => mret $ TLBI.Va tid asid upper vpn last
    | _ => mthrow "Unsupported kind of TLBI"
    end;
  let recipients :=
    if decide (tlbi.(TLBIInfo_shareability) = Shareability_NSH)
    then [tid]
    else seq 0 n_threads
  in
  '((vself, vother), created_new_tlbi_events) ←
    foldlM (λ '((vself, vother), created_new_tlbi_events) recipient,
      '(time, is_new_tlbi_event) ←
        materialize_tlbi_for_recipient vpre tlbiev recipient;
      let vself := if decide (recipient = tid) then max vself time else vself in
      let vother := if decide (recipient = tid) then vother else max vother time in
      mret ((vself, vother), created_new_tlbi_events || is_new_tlbi_event)
    ) ((0%nat, 0%nat), false) recipients;
  let vpost := vself ⊔ vother in
  mset PPState.state $
    TState.update TState.vtlbi_other vother ∘
    TState.update TState.vtlbi_self vself;;
  mset PPState.iis $ IIS.add vpost;;
  (* [Some vpre] is an aggregate signal to the generic promise runner; the
     recipient-specific events themselves are collected from the memory delta. *)
  mret (if (created_new_tlbi_events : bool) then Some vpre else None).


(** Handle the start of an address translation.

    This is called when the architecture initiates a translation table walk.
    This will lookup the TLB to gather all possible translations

    TODO more comment *)
Definition run_trans_start (trans_start : TranslationStartInfo) : prom_mon () :=
  ts ← mget PPState.state;
  iis ← mget PPState.iis;
  mem ← mget PPState.mem;

  let ifetch :=
    trans_start.(TranslationStartInfo_accdesc).(AccessDescriptor_acctype) =?
    AccessType_IFETCH in
  let ets2 := TState.ets2 ts in
  let vpre_t := ts.(TState.vcse) ⊔ IIS.strict iis ⊔
                 (view_if (ets2 && (negb ifetch)) ts.(TState.vdsb)) in
  let vpre_inv :=
      vpre_t ⊔ view_if ets2 (ts.(TState.vwr) ⊔ ts.(TState.vrd)) in
  let vmax_t := pred (TState.min_promise (length mem) ts) in
  let asid := trans_start.(TranslationStartInfo_asid) in
  let va : bv 64 := trans_start.(TranslationStartInfo_va) in
  let size := Z.to_N trans_start.(TranslationStartInfo_size) in
  let regime := trans_start.(TranslationStartInfo_regime) in
  guard_or "Invalid regime, only EL1&0 supported" (regime = Regime_EL10);;

  trans_res ←
    if is_upper_va va is Some upper then
      reg_ttbr ← mlift $ root_ttbr regime upper;
      let vpn := va_to_vpn va in
      tlb_results ← mlift $ TState.tlb_lookup tid imem mem ts ifetch upper vpn
        vpre_t vpre_inv vmax_t;
      (guard_or ("Can't translate address " ++ pretty va)%string
        (tlb_results ≠ []));;
      tlb_result ← mchoosel tlb_results;
      val_ttbr ← othrow
        "Unexpected TTBR value type"
          (val_to_regval reg_ttbr tlb_result.(TLB.Result.ttbr));
      let root := Some $ existT reg_ttbr val_ttbr in
      mret (
        IIS.TransRes.make
          tlb_result.(TLB.Result.tstart)
          tlb_result.(TLB.Result.tend)
          root
          tlb_result.(TLB.Result.path),
        tlb_result.(TLB.Result.inv_time))
    else
      mret $ (IIS.TransRes.make vpre_t vmax_t None [], None);
  let '(tres, inv_time) := trans_res in
  let page_offsets := TState.va_page_offsets va size in
  guard_discard (TState.tcohs_before_inv_time asid page_offsets inv_time ts);;
  mset PPState.state $
    TState.update_tcohs asid page_offsets tres.(IIS.TransRes.trans_start);;
  mset PPState.iis $ IIS.set_trs tres;;
  mset PPState.iis $ IIS.set_inv_time inv_time.

(** Handle the end of an address translation.

    If the translation succeeded (no fault), clears the translation state.
    If a fault occurred, updates views to reflect the fault timing. With
    ETS3, faults may be discarded if they occur before recent memory
    accesses. *)
Definition run_trans_end (trans_end : trans_end) :
    Exec.t (TState.t * IIS.t) string () :=
  ts ← mget fst;
  iis ← mget snd;
  if iis.(IIS.trs) is Some trs then
    msetv (IIS.trs ∘ snd) None;;

    (* Propagate the effect of translation to follwing effects *)
    let trans_start := trs.(IIS.TransRes.trans_start) in
    mset snd $ IIS.add trans_start;;
    mset fst $ TState.update TState.vspec trans_start;;

    (* If the translation faulted, apply additional translation fault orderings *)
    let fault := trans_end.(AddressDescriptor_fault) in
    if decide (fault.(FaultRecord_statuscode) = Fault_None) then mret ()
    else
      let ets3 := TState.ets3 ts in
      let is_ifetch :=
        fault.(FaultRecord_access).(AccessDescriptor_acctype) =?
        AccessType_IFETCH in
      let trans_time :=
        trans_start ⊔
        view_if (ets3 && (negb is_ifetch))
          (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
      (* With the ETS3, a faulting translation from a cacheable entry still
         needs to respect extra ETS constraint. If that pushes the minimum
         beyong the end of the range, this this translation can't have happened *)
      if trans_time <=? trs.(IIS.TransRes.trans_end) then
        mset snd $ IIS.add trans_time;;

        let is_write := fault.(FaultRecord_access).(AccessDescriptor_write) in
        let vbob := (view_if is_write ts.(TState.vdmbst)) ⊔ ts.(TState.vdmb)
              ⊔ ts.(TState.vdsb) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq) in
        mset snd $ IIS.add vbob
      else mdiscard
  else
    mthrow "Translation ends with an empty translation".

(* TODO: check translation fault using `fault` and handle other cases *)
Definition run_take_exception (fault : exn) (vmax_t : view) : prom_mon () :=
  inv_time ← mget (IIS.inv_time ∘ PPState.iis);
  match inv_time with
  | Some inv_time => run_cse inv_time
  | None => run_cse vmax_t
  end.

(** ** Top-level outcome semantics *)

(** Runs an outcome. *)

  Equations run_outcome (out : outcome) :
      Exec.t (PPState.t TState.t Ev.t IIS.t) string (eff_ret out * option view) :=
  | RegRead reg racc =>
      val ← Exec.liftSt (PPState.state ×× PPState.iis) $ (run_reg_read reg racc);
      mret (val, None)
  | RegWrite reg racc val =>
      run_reg_write reg racc val;;
      mret ((), None)
  | MemRead (MemReq.make macc addr addr_space size 0) =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      if is_ifetch macc then
        size_4 ← guard_or "Ifetch read of size other than 4" (size = 4)%N;
        mem ← mget PPState.mem;
        opcode ← mlift $ read_imem addr mem;
        mret (Ok (ctrans _ opcode, 0%bv), None)
      else if is_explicit macc then
        val ← read_mem_explicit addr size macc;
        mret (Ok (val, 0%bv), None)
      else if is_ttw macc then
        size_8 ← guard_or "TTW read of size other than 8" (size = 8)%N;
        val ← read_pte;
        mret (Ok (ctrans _ val, 0%bv), None)
      else mthrow "Read is not explicit, ifetch, nor translation"
  | MemRead _ => mthrow "Memory read with tags unsupported"
  | MemWriteAddrAnnounce _ =>
      vaddr ← mget (IIS.strict ∘ PPState.iis);
      ts ← mget PPState.state;
      guard_discard (TState.no_write_promises_until vaddr ts);;
      mset PPState.state $ TState.update TState.vspec vaddr;;
      mret ((), None)
  | MemWrite (MemReq.make macc addr addr_space size 0) val _ =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      guard_or "Only explicit writes are supported" (is_explicit macc);;
      vpre_opt ← write_mem addr size macc val;
      mret (Ok (), vpre_opt)
  | MemWrite _ _ _ => mthrow "Memory write with tags unsupported"
  | Barrier barrier =>
      mem ← mget PPState.mem;
      run_barrier barrier (length mem);;
      mret ((), None)
  | TlbOp tlbi =>
      viio ← mget (IIS.strict ∘ PPState.iis);
      vpre_opt ← run_tlbi viio tlbi;
      mret ((), vpre_opt)
  | ReturnException =>
      mem ← mget PPState.mem;
      run_cse (length mem);;
      mret ((), None)
  | TranslationStart trans_start =>
      run_trans_start trans_start;;
      mret ((), None)
  | TranslationEnd trans_end =>
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_trans_end trans_end;;
      mret ((), None)
  | GenericFail s => mthrow ("Instruction failure: " ++ s)%string
  | TakeException fault =>
      mem ← mget PPState.mem;
      run_take_exception fault (length mem);;
      mret ((), None)
  | _ => mthrow "Unsupported outcome".
  Solve Obligations with lia.

  Definition run_outcome' (out : outcome) :
      Exec.t (PPState.t TState.t Ev.t IIS.t) string (eff_ret out) :=
    run_outcome out |$> fst.

End RunOutcome.

(** * BBM Check Implementation *)

(** BBM (Break-Before-Make) violation detection.

    A BBM violation occurs when a page table entry is modified without
    following the proper invalidation sequence (DSB, TLBI, DSB).

    This section implements checking for all seven ARM BBM scenarios
    (ARM DDI0487, D8.14.1):
    - Same-level conflicts (output address, memory type, shareability,
      contiguous bit, global/non-global changes)
    - Cross-level conflicts (Block→Table or Table→Block conversion) *)


Module BBM.
Section BBM.
  Import TLB.
  Context (imem : memoryMap) (mem : Memory.t) (relevant_addrs : list address).

  (** Checks that the memory contents of two pages or blocks are the same at
      [time]. This requires that the set of mapped bytes of both pages/blocks
      are equivalent, otherwise the check throws an error *)
  Definition mem_contents_eq (time : nat) (lvl : Level) (oa1 oa2 : prefix lvl) :
      result string bool :=
    let relevant_offs :=
      omap (λ addr,
          if decide (pa_prefix addr lvl = oa1 ∨ pa_prefix addr lvl = oa2)
          then Some (pa_offset lvl addr)
          else None) relevant_addrs |> remove_dups in
    for offs in relevant_offs do
      let addr1 := pa_prefix_offset lvl oa1 offs in
      let addr2 := pa_prefix_offset lvl oa2 offs in
      byte1 ←@{result string} Memory.read_byte addr1 imem mem time;
      byte2 ← Memory.read_byte addr2 imem mem time;
      mret (byte1 =? byte2)
    end |$> List.forallb id.

  (** Checks that the memory contents of two pages or blocks are the same
      between [tmin] and [tmax]. This requires that the set of mapped bytes of
      both pages/blocks are equivalent, otherwise the check throws an error *)
  Definition mem_contents_eq_btw (tmin tmax : nat) (lvl : Level)
      (oa1 oa2 : prefix lvl) : result string bool :=
    mem_eq ← mem_contents_eq tmin lvl oa1 oa2;
    let not_changed :=
      let size := offset_bits lvl |> bv_modulus |> Z.to_N in
      let pa1 := prefix_to_pa lvl oa1 in
      let pa2 := prefix_to_pa lvl oa2 in
      bool_decide (
          ∀ ev ∈ (Memory.cut_after tmin (Memory.cut_before tmax mem)),
            if Ev.get_msg ev is Some msg
            then ¬ Msg.overlap pa1 size msg ∧ ¬ Msg.overlap pa2 size msg
            else True)
    in mret (mem_eq && not_changed).

  (** Compute all the time intervals (inclusive bounds, most recent first) up to
      [tmax] included during which both entries were active according to their
      event lists. *)
  Fixpoint time_intervals (tend : nat) (evs1 evs2 : Entry.events)
      : list (nat * nat) :=
    match evs1 with
    | [] => []
    | (ev1, t1) :: tl1 =>
        (fix go2 tend evs2 :=
           match evs2 with
           | [] => []
           | (ev2, t2) :: tl2 =>
               let pop1 '() := time_intervals (min tend $ Nat.pred t1) tl1 evs2 in
               let pop2 '() := go2 (min tend $ Nat.pred t2) tl2 in
               match ev1, ev2 with
               | Entry.Load, Entry.Load =>
                   let tstart := max t1 t2 in
                   let rest := if decide (t2 ≤ t1) then pop1 () else pop2 () in
                   if decide (tstart ≤ tend) then (tstart, tend) :: rest
                   else rest
               | Entry.Load, _ => if decide (t2 ≤ t1) then pop1 () else pop2 ()
               | _, _ => if decide (t2 < t1) then pop1 () else pop2 ()
               end
           end) tend evs2
    end.

  (** Computes whether two entries where loaded in TLB at the same time at
      any point before [tmax] included *)
  Definition time_overlaps (tmax : nat) (evs1 evs2 : Entry.events)
    : bool :=
    if time_intervals tmax evs1 evs2 is [] then false else true.

  (** Computes whether two entries in the same context where in conflict before
      [tmax] included *)
  Definition is_bbm_violation (tmax : nat)
    (ctxt : Ctxt.t) (e1 e2 : Entry.t (Ctxt.lvl ctxt))
    (evs1 evs2 : Entry.events) : result string bool :=
    let lvl := Ctxt.lvl ctxt in
    let pte1 := Entry.pte e1 in
    let pte2 := Entry.pte e2 in
    if decide $ is_final lvl pte1 then
      if decide $ is_final lvl pte2 then
        if negb (attr_idx pte1 =? attr_idx pte2) then
          mret (time_overlaps tmax evs1 evs2)
        else if negb (shareability pte1 =? shareability pte2) then
          mret (time_overlaps tmax evs1 evs2)
        else if negb (is_contiguous pte1 =? is_contiguous pte2) then
          mret (time_overlaps tmax evs1 evs2)
        else
        let oa1 := output_prefix lvl pte1 in
        let oa2 := output_prefix lvl pte2 in
        if decide (oa1 ≠ oa2) then
          let intervals := time_intervals tmax evs1 evs2 in
          if intervals is [] then mret false
          else
            if decide $ allow_write lvl pte1 then mret true
            else if decide $ allow_write lvl pte2 then mret true
            else
            for (tmin, tmax) in intervals do
              mem_contents_eq_btw tmin tmax lvl oa1 oa2
            end |$> List.forallb id |$> negb
        else mret false
      else mret true
    else mret $ bool_decide $ is_final lvl pte2.

  (** Return the parent context of [ctxt] at level [lvl] (which should be
      smaller than [Ctxt.lvl ctxt]) *)
  Definition ctxt_parent (ctxt : Ctxt.t) (lvl : Level) (asid : option (bv 16)) :
      Ctxt.t :=
    let va := prefix_to_va (Ctxt.lvl ctxt) (Ctxt.upper ctxt) (Ctxt.va ctxt) in
    Ctxt.make lvl (Ctxt.upper ctxt) (va_prefix lvl va) asid.

  (** Check that [f] holds for all pairs of elements of [l] *)
  Fixpoint for_all_pairs {A} (f : A → A → result string bool) (l : list A)
      : result string bool :=
    match l with
    | [] => mret true
    | x :: tl =>
        b ← (for y in tl do f x y end |$> List.forallb id);
        if (b : bool) then for_all_pairs f tl else mret false
    end.

  (** Check the TLB for BBM violations, returns true if there is one *)
  (** TODO, this misses conflict between ASID block entries and page global entries *)
  Definition check_tlb (tlb : TLB.t) : result string bool :=
    let vatlb := tlb.(vatlb) in
    let tmax := length mem in
    for existT ctxt entries in VATLB.entries_by_ctxt vatlb do
      let lvl := Ctxt.lvl ctxt in
      let asid := Ctxt.asid ctxt in
      if entries is [] then mret false else
      (* All pairs of entries in the same context *)
      no_pair_violation ←@{result string}
        for_all_pairs (λ '(e1, evs1) '(e2, evs2),
            is_bbm_violation tmax ctxt e1 e2 evs1 evs2 |$> negb)
          entries;
      (* Block entries in parent contexts, active at the same time as [evs] *)
      let parent_block (evs : Entry.events) : Prop :=
        ∃ plvl : Level, plvl < lvl ∧
          ∃ '(pe, pevs) ∈ VATLB.get (ctxt_parent ctxt plvl asid) vatlb,
            is_final plvl (Entry.pte pe) ∧ time_overlaps tmax evs pevs = true in
      (* Any entry in the corresponding global context and its parents, active
         at the same time as [evs] *)
      let global_conflict (evs : Entry.events) : Prop :=
        is_Some asid ∧
        ∃ glvl: Level, glvl ≤ lvl ∧
          ∃ '(ge, gevs) ∈ VATLB.get (ctxt_parent ctxt glvl None) vatlb,
            time_overlaps tmax evs gevs = true in
      (* The parent and global checks are only needed for final entries *)
      let final_conflict :=
        bool_decide (∃ '(e, evs) ∈ entries,
            is_final lvl (Entry.pte e) ∧
            (parent_block evs ∨ global_conflict evs)) in
      mret (negb no_pair_violation || final_conflict)
    end |$> List.existsb id.

End BBM.

(** Check if there was a BBM violation during execution *)
Definition check (imem : memoryMap) (mem : Memory.t) (ts : TState.t)
   : result string bool :=
  if ts.(TState.tlb) is Some tlb then
    check_tlb imem mem (elements (dom imem)) tlb
  else mret false.

End BBM.


(** * Implement GenPromising ***)

Import Promising.

(** Avoid exploring duplicate TLBI promise orders.  During one enumeration run,
    we keep TLBI recipients in nondecreasing order, comparing each candidate
    with the last TLBI promise already selected in memory. *)
Definition filter_tlbi_promises
    (n_threads tid : nat) (mem : Memory.t) (candidates : list Ev.t) :
    list Ev.t :=
  let run_recipient :=
    if mem is ev :: _ then Ev.get_tlbi_recipient ev else None in
  filter (λ ev,
    match Ev.get_tlbi_recipient ev with
    | Some recipient =>
      match run_recipient with
      | Some prev_recipient => prev_recipient <=? recipient
      | None => true
      end
    | None => true
    end) candidates.

Definition VMPromising (bbm : bool) : Promising.Model :=
  {|tState := TState.t;
    tState_init := TState.init;
    tState_regs := TState.reg_map;
    tState_pc := TState.pc;
    tState_pc_spec := TState.pc_reg_map;
    tState_nopromises := (λ ts, is_emptyb (TState.prom_wr ts ++ TState.prom_tlbi ts));
    iis := IIS.t;
    iis_init := IIS.init;
    address_space := PAS_NonSecure;
    mEvent := Ev.t;
    mEvent_tid := Ev.tid;
    filter_promises := filter_tlbi_promises;
    handle_outcome := run_outcome;
    emit_promise := TState.emit_promise;
    check_valid_end := λ _ imem ts mem,
      if bbm then
        match BBM.check imem mem ts with
        | Ok true => ["BBM violation detected"]
        | Ok false => []
        | Error err => [err]
        end
      else [];
    memory_snapshot := Memory.to_memMap;
  |}.

Definition VMPromising_nocert (bbm : bool) :=
  Promising_to_Modelnc (VMPromising bbm).

Definition VMPromising_exe (bbm : bool) :=
  Promising_to_Modelc (VMPromising bbm).

Definition VMPromising_pf (bbm : bool) :=
  Promising_to_Modelc_pf (VMPromising bbm).

Definition VMPromising_opmodel (bbm : bool) (isem : iMon ())
    (n : nat) : opModel n := CPState.opmodel isem (VMPromising bbm).

Definition VMPromising_opmodel_pf (bbm : bool) (isem : iMon ())
    (n : nat) : opModel n := CPState.opmodel_pf isem (VMPromising bbm).
