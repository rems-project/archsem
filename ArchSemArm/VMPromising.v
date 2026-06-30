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
From ASCommon Require Import Common GRel Exec FMon StateT HVec.

From ArchSem Require Import GenPromising.
Require Import ArmInst.

Require UMPromising.
Import (hints) UMPromising.

Module Msg := UMPromising.Msg.
Export (hints) Msg.

#[local] Open Scope list.
#[local] Open Scope nat.
#[local] Open Scope stdpp.

(** The goal of this module is to define a Virtual-memory promising model
    with mixed-size support on top of the new interface.

    Memory events use byte-granular addresses. *)

Definition val_to_addr {size : N} (v : bv (8 * size)) : address := bv_extract 0 56 v.

Module TLBI.
  Inductive t :=
  | All (tid : nat)
  | Asid (tid : nat) (asid : bv 16)
  | Va (tid : nat) (asid : bv 16) (va : bv 36) (last : bool) (upper : bool)
  | Vaa (tid : nat) (va : bv 36) (last : bool) (upper : bool).

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

  Definition va_opt (tlbi : t) : option (bv 36) :=
    match tlbi with
    | All _ => None
    | Asid _ _ => None
    | Va _ _ va _ _ => Some va
    | Vaa _ va _ _ => Some va
    end.

  Definition va (tlbi : t) : bv 36 :=
    default (Z_to_bv 36 0) (va_opt tlbi).

  Definition last_opt (tlbi : t) : option bool :=
    match tlbi with
    | All _ => None
    | Asid _ _ => None
    | Va _ _ _ last _ => Some last
    | Vaa _ _ last _ => Some last
    end.

  Definition last (tlbi : t) : bool :=
    default false (last_opt tlbi).

  Definition upper_opt (tlbi : t) : option bool :=
    match tlbi with
    | All _ => None
    | Asid _ _ => None
    | Va _ _ _ _ upper => Some upper
    | Vaa _ _ _ upper => Some upper
    end.
End TLBI.

(** Events in the VMPromising history can be either memory writes or TLBI effects *)
Module Ev.
  Inductive t :=
  | Msg (msg : Msg.t)
  | Tlbi (tlbi : TLBI.t).

  #[global] Instance dec : EqDecision t.
  solve_decision.
  Defined.

  Definition tid (ev : t) :=
    match ev with
    | Msg msg => Msg.tid msg
    | Tlbi tlbi => TLBI.tid tlbi
    end.

  Definition get_msg (ev : t) : option Msg.t :=
    match ev with
    | Msg msg => Some msg
    | _ => None
    end.

  Definition get_tlbi (ev : t) : option TLBI.t :=
    match ev with
    | Tlbi tlbi => Some tlbi
    | _ => None
    end.

  (** Checks whether an write event overlaps an address range *)
  Definition addr_overlap (a : address) (sz : N) (ev : t) : Prop :=
    match ev with
    | Msg msg => (addr_overlap a sz (Msg.addr msg) (Msg.size msg))
    | _ => False
    end.
  #[global] Instance Decision_addr_overlap (a : address) (sz : N) (ev : t) :
      Decision (addr_overlap a sz ev).
  Proof. unfold_decide. Defined.
End Ev.

Coercion Ev.Msg : Msg.t >-> Ev.t.
Coercion Ev.Tlbi : TLBI.t >-> Ev.t.

(** A view is just a natural, reused from UM *)
Definition view := UMPromising.view.
#[export] Typeclasses Transparent view.
Bind Scope nat_scope with view.
Global Hint Transparent view : core.
Global Hint Unfold view : core.

Module Memory.
  Import PromMemory.

  (** The promising memory: a list of events *)
  Definition t : Type := t Ev.t.
  #[export] Typeclasses Transparent t.

  Definition cut_after : nat → t → t := @cut_after Ev.t.
  Definition cut_before : nat → t → t := @cut_before Ev.t.

  (** Reads the last byte written at an address.
      Returns the byte value and the timestamp of the write.
      Timestamp is 0 if reading from initial memory.
      Returns [None] if the address isn't present in initial memory. *)
  Fixpoint read_last (addr : address) (init : memoryMap)
      (mem : t) : option (bv 8 * nat) :=
    match mem with
    | [] => init !! addr |$> (., 0%nat)
    | (Ev.Msg msg) :: mem' =>
        if Msg.read_byte addr msg is Some byte then
          Some (byte, List.length mem)
        else read_last addr init mem'
    | Ev.Tlbi _ :: mem' => read_last addr init mem'
    end.

  (** Reads from initial memory and fails if the memory has been overwritten.

      This is mainly for instruction fetching in this model. *)
  Definition read_initial (addr : address) (init : memoryMap)
      (mem : t) : option (bv 8) :=
    match read_last addr init mem with
    | Some (v, 0%nat) => Some v
    | _ => None
    end.

  (** Reads [size] bytes starting at [addr] from the memory state at
      timestamp [tread]. Returns each byte paired with the timestamp of the
      write it comes from, or [None] if any byte is unmapped. *)
  Definition read_from (addr : address) (size : N) (tread : nat)
      (init : memoryMap) (mem : t) : option (list (bv 8 * nat)) :=
    let snap := cut_before tread mem in
    for a in addr_range addr size do
      read_last a init snap
    end.

  (** Reads a byte at timestamp [time]. *)
  Definition read_byte (addr : address) (init : memoryMap)
      (mem : t) (time : nat) : option (bv 8) :=
    bytes ← read_from addr 1 time init mem;
    List.head (bytes.*1).

  (** Reads an 8-byte memory word at timestamp [time]. *)
  Definition read_word (addr : address) (init : memoryMap)
      (mem : t) (time : nat) : option (bv 64) :=
    bytes ← read_from addr 8 time init mem;
    Some (bv_of_bytes 64 bytes.*1).

  (** Transforms an initial [memoryMap] and a promising memory history back to
      a [memoryMap] *)
  Definition to_memMap (init : memoryMap) (mem : t) : memoryMap :=
    foldr (λ ev mm,
        if Ev.get_msg ev is Some msg
        then mem_insert_bv (Msg.addr msg) (Msg.val msg) mm
        else mm) init mem.

  (** Promises an event and adds it at the end of memory. *)
  Definition promise (ev : Ev.t) : Exec.t t string view :=
    mSet (cons ev);;
    mem ← mGet;
    mret (List.length mem).

  (** Returns the oldest unfulfilled promise timestamp that corresponds to an
      event.

      Choosing the oldest matching promise avoids fulfilling a later duplicate
      before an earlier one, which would make the earlier promise impossible to
      fulfill later. *)
  Definition fulfill (ev : Ev.t) (prom : list view) (mem : t) : option view :=
    prom |> filter (λ t, mem !! t = Some ev)
         |> reverse
         |> head.

 (** Checks that no write overlapping [addr, addr+size) has been made by any
      thread other than [tid] in between [tread] and [twrite] *)
  Definition exclusive (tid : nat) (addr : address) (size : N)
      (tread : nat) (twrite : nat) (mem : t) : Prop :=
    ∀ ev ∈ (cut_after tread (cut_before (twrite - 1)%nat mem)),
      Ev.addr_overlap addr size ev → Ev.tid ev = tid.
  #[global] Instance exclusive_dec tid addr size tread twrite mem :
      Decision (exclusive tid addr size tread twrite mem).
  Proof. unfold exclusive. apply _. Defined.

End Memory.
Import (hints) Memory.

Module FwdItem := UMPromising.FwdItem.

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

(** * The thread state *)

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


(** The thread state *)
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

        vrd : view; (* The maximum output view of a read  *)
        vwr : view; (* The maximum output view of a write  *)
        vdmbst : view; (* The maximum output view of a dmb st  *)
        vdmb : view; (* The maximum output view of a dmb ld or dmb sy  *)
        vdsb : view; (* The maximum output view of a dsb  *)
        vspec : view; (* The maximum output view of speculative operation. *)
        vcse : view; (* The maximum output view of an Context Synchronization Event *)
        vtlbi : view; (* The maximum output view of a TLBI *)
        vmsr : view; (* The maximum output view of an MSR *)
        vacq : view; (* The maximum output view of an acquire access *)
        vrel : view; (* The maximum output view of an release access *)

        (* Per-byte forwarding database *)
        fwdb : gmap address FwdItem.t;

        (* Exclusive database: (load-time, optional VA, physical address, size) *)
        xclb : option (nat * option (bv 64) * address * N);
      }.

  #[global] Instance eta : Settable _ :=
    settable! make <prom_wr; prom_tlbi;regs;levs;coh;vrd;vwr;vdmbst;vdmb;vdsb;
                    vspec;vcse;vtlbi;vmsr;vacq;vrel;fwdb;xclb>.

  (* TODO Check and remove mem as an argument here *)
  Definition init (mem : memoryMap) (iregs : registerMap) :=
    ({|
      prom_wr := [];
      prom_tlbi := [];
      regs := dmap_map (λ _ v, (v, 0%nat)) iregs;
      levs := []; (* latest event at the top of the list *)
      coh := ∅;
      vrd := 0;
      vwr := 0;
      vdmbst := 0;
      vdmb := 0;
      vdsb := 0;
      vspec := 0;
      vcse := 0;
      vtlbi := 0;
      vmsr := 0;
      vacq := 0;
      vrel := 0;
      fwdb := ∅;
      xclb := None;
    |})%nat.

  Definition lev_cur (ts : t) := length ts.(levs).

  Definition filter_wsreg : list LEv.t → list WSReg.t := omap LEv.get_wsreg.

  Definition filter_cse : list LEv.t → list view := omap LEv.get_cse.

  (** Read the last system register write at system register position s *)
  Definition read_sreg_last (ts : t) (sreg : reg) (s : nat) :=
    let newval :=
      ts.(levs)
      |> drop ((lev_cur ts) - s)
      |> filter_wsreg
      |> omap (WSReg.to_val_view_if sreg)
      |> hd_error in
    newval ∪ dmap_lookup sreg ts.(regs).

  (** Read all possible system register values for sreg assuming the last
      synchronization at position sync *)
  Definition read_sreg_by_cse (ts : t) (sreg : reg) (s : nat)
    : option (list (reg_type sreg * view))
    :=
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

  (** Read possible system register values from the position of the most recent CSE *)
  Definition read_sreg_indirect (ts : t) (sreg : reg) :=
    let max_cse :=
      ts.(levs)
           |> filter_cse
           |> hd 0%nat
    in
    read_sreg_by_cse ts sreg max_cse.

  (** Read system register values at the timestamp t *)
  Definition read_sreg_at (ts : t) (sreg : reg) (t : nat) :
      option (list (reg_type sreg * nat)) :=
    let last_cse :=
      ts.(levs)
           |> filter_cse
           |> filter (λ tcse, tcse < t)
           |> hd 0%nat
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
      read_sreg_last ts r (lev_cur ts)
    else dmap_lookup r ts.(regs).

  (** Extract a plain register map from the thread state without views.
      This is used to decide if a thread has terminated, and to observe the
      results of the model *)
  Definition reg_map (ts : t) : registerMap :=
    dmap_map (λ _, fst) ts.(regs).

  (** Sets the value of a register *)
  Definition set_reg (reg : reg) (rv : reg_type reg * view) (ts : t) : option t :=
    if decide (is_Some (dmap_lookup reg ts.(regs))) then
      Some $ set regs (dmap_insert reg rv) ts
    else None.

  (** Add a system register write event to the local event list *)
  Definition add_wsreg (sreg : reg) (val : reg_type sreg) (v : view) : t → t :=
    let lev := LEv.Wsreg (WSReg.make sreg val v) in
    set levs (lev::.).

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

  (** Sets the forwarding database for an address *)
  Definition set_fwdb (addr : address) (fi : FwdItem.t) : t → t :=
    set fwdb (insert addr fi).

  (** Set forwarding entries for all bytes in a range *)
  Definition set_fwdbs (addrs : list address)
      (time : nat) (vdata : view) (xcl : bool) (ts : t) : t :=
    let fi := FwdItem.make time vdata xcl in
    foldr (λ a, set_fwdb a fi) ts addrs.

  (** Set the exclusive database to the footprint of the latest load
      exclusive. *)
  Definition set_xclb (time : nat) (va : option (bv 64))
      (addr : address) (size : N) : t → t :=
    setv xclb (Some (time, va, addr, size)).

  (** Clears the exclusive database, to mark a store exclusive *)
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
  Definition cse_candidates (vpre vmax_t : view) (ts : t) : list view :=
    seq vpre (min_promise vmax_t ts - vpre).

  (** Perform a context synchronization event *)
  Definition cse (v : view) : t → t :=
    (update vcse v) ∘ (set levs (LEv.Cse v ::.)).
End TState.

(*** VA helper ***)

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

(* It is important to be consistent on "level_length" and not write it as 9 *
   lvl + 9, otherwise some term won't type because the equality is only
   propositional *)
Definition level_length (lvl : Level) : N := 9 * (lvl + 1).

Definition prefix (lvl : Level) := bv (level_length lvl).
#[export] Typeclasses Transparent prefix.

Definition va_to_vpn {n : N} (va : bv 64) : bv n :=
  bv_extract 12 n va.

Definition prefix_to_va {n : N} (upper : bool) (p : bv n) : bv 64 :=
  let varange_bits : bv 16 := if upper then (-1)%bv else 0%bv in
  let padding := bv_0 (48 - n) in
  bv_concat 64 varange_bits (bv_concat 48 p padding).

Definition is_upper_va (va : bv 64) : option bool :=
  let top_bits := bv_extract 48 16 va in
  if top_bits =? (-1)%bv then Some true
  else if top_bits =? 0%bv then Some false
  else None.

Definition level_prefix {n : N} (va : bv n) (lvl : Level) : prefix lvl :=
  bv_extract (12 + 9 * (3 - lvl)) (9 * (lvl + 1)) va.

Definition match_prefix_at {n n' : N} (lvl : Level) (va : bv n) (va' : bv n') : Prop :=
  level_prefix va lvl = level_prefix va' lvl.
Instance Decision_match_prefix_at {n n' : N} (lvl : Level) (va : bv n) (va' : bv n') :
  Decision (match_prefix_at lvl va va').
Proof. unfold_decide. Defined.

Definition level_index {n : N} (va : bv n) (lvl : Level) : bv 9 :=
  bv_extract 0 9 (level_prefix va lvl).

Definition index_to_offset (idx : bv 9) : bv 12 :=
  bv_concat 12 idx (bv_0 3).

Definition higher_level {n : N} (va : bv n) : bv (n - 9) :=
  bv_extract 9 (n - 9) va.

Definition next_entry_addr {n : N} (addr : bv n) (index : bv 9) : address :=
  bv_concat 56 (bv_0 8) (bv_concat 48 (bv_extract 12 36 addr) (index_to_offset index)).

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
  if lvl is 3%fin then (bv_extract 0 2 e) = 3%bv else is_block e.
Instance Decision_is_final (lvl : Level) (e : bv 64) : Decision (is_final lvl e).
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

(** The offset size (in bits) for a given translation level.
    Level 0: 12 + 27 = 39 bits  (512GB block)
    Level 1: 12 + 18 = 30 bits  (1GB block)
    Level 2: 12 + 9  = 21 bits  (2MB block)
    Level 3: 12 + 0  = 12 bits  (4KB page) *)
Definition offset_size (lvl : Level) : N := (12 + (3 - lvl) * 9)%N.

(** The output address size (in bits) for a given translation level.
    This is 48 - offset_size, representing the significant address bits. *)
Definition output_addr_size (lvl : Level) : N := 48 - (offset_size lvl).

(** Extract the output address (OA) from a PTE at a given level.
    The OA is the physical address base that the PTE maps to. *)
Definition output_addr (lvl : Level) (e : bv 64) : bv (output_addr_size lvl) :=
  bv_extract (offset_size lvl) (output_addr_size lvl) e.

(** * TLB ***)

Module TLB.
  (** ** TLB types definitions *)
  Module NDCtxt.
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

    #[global] Instance count lvl : Countable (t lvl).
    Proof.
      eapply (inj_countable' (fun ndc => (upper ndc, va ndc, asid ndc))
                        (fun x => make x.1.1 x.1.2 x.2)).
      abstract sauto.
    Defined.
  End NDCtxt.

  Module Ctxt.
    Definition t := {lvl : Level & NDCtxt.t lvl}.
    Definition lvl : t → Level := projT1.
    Definition nd (ctxt : t) : NDCtxt.t (lvl ctxt) := projT2 ctxt.
    Definition upper (ctxt : t) : bool := NDCtxt.upper (nd ctxt).
    Definition va (ctxt : t) : prefix (lvl ctxt) := NDCtxt.va (nd ctxt).
    Definition asid (ctxt : t) : option (bv 16) := NDCtxt.asid (nd ctxt).
  End Ctxt.
  #[export] Typeclasses Transparent Ctxt.t.

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

    Program Definition append {lvl clvl : Level}
        (tlbe : t lvl)
        (pte : bv 64)
        (CHILD : lvl + 1 = clvl) : @t clvl :=
      make _ tlbe.(val_ttbr) (ctrans _ (tlbe.(ptes) +++ [#pte])).
    Solve All Obligations with lia.
  End Entry.
  Export (hints) Entry.

  (* Full Entry *)
  Module FE.
    Definition t := { ctxt : Ctxt.t & Entry.t (Ctxt.lvl ctxt) }.
    Definition ctxt : t → Ctxt.t := projT1.
    Definition lvl (fe : t) : Level := Ctxt.lvl (ctxt fe).
    Definition va (fe : t) : prefix (lvl fe) := Ctxt.va (ctxt fe).
    Definition asid (fe : t) : option (bv 16) := Ctxt.asid (ctxt fe).
    Definition ptes (fe : t) := projT2 fe.
    Definition pte (fe : t) := Entry.pte (projT2 fe).
  End FE.
  #[export] Typeclasses Transparent FE.t.

  Module VATLB.
    Definition T (lvl : Level) := gmap (NDCtxt.t lvl) (gset (Entry.t lvl)).
    #[global] Typeclasses Transparent T.
    Definition t := hvec T.

    Definition init : t := hvec_func (fun lvl => ∅).

    Definition get (ctxt : Ctxt.t) (vatlb : t) :
        gset (Entry.t (Ctxt.lvl ctxt)) :=
      (hget (Ctxt.lvl ctxt) vatlb) !! (Ctxt.nd ctxt) |> default ∅.

    Definition getFE (ctxt : Ctxt.t) (vatlb : t) : gset (FE.t) :=
      get ctxt vatlb
      |> set_map (fun (e : Entry.t (Ctxt.lvl ctxt)) => existT ctxt e).

    Definition singleton (ctxt : Ctxt.t) (entry : Entry.t (Ctxt.lvl ctxt)) : t :=
      hset (Ctxt.lvl ctxt) {[(Ctxt.nd ctxt) := {[ entry ]}]} init.

    #[global] Instance elements : Elements FE.t t :=
      λ vatlb,
        let lists :=
          map (λ lvl : Level,
            map_fold
              (λ ctxt entry_set cur,
                  set_fold (λ ent,
                    let fent := existT (existT lvl ctxt) (ent : Entry.t lvl) in
                    (fent ::.)) cur entry_set)
              [] (hget lvl vatlb))
          (enum Level) in
        List.concat lists.

    Instance filter : Filter FE.t t :=
      λ P P_dec,
        hmap
          (λ lvl,
            iomap
              (λ ctxt entry_set,
                let new_entry_set :=
                  filter
                    (λ ent, P (existT (existT lvl ctxt) (ent : Entry.t lvl)))
                    entry_set
                in
                if decide (new_entry_set = ∅) then None else Some new_entry_set)).

    Definition setFEs (ctxt : Ctxt.t)
        (entries : gset (Entry.t (Ctxt.lvl ctxt))) (vatlb : t) : t :=
      let lvl := Ctxt.lvl ctxt in
      let nd := Ctxt.nd ctxt in
      hset lvl (<[ nd := entries ]> (hget lvl vatlb)) vatlb.

    Definition insert (ctxt : Ctxt.t) (entry : Entry.t (Ctxt.lvl ctxt))
        (vatlb : t) : t :=
      let lvl := Ctxt.lvl ctxt in
      let nd := Ctxt.nd ctxt in
      let lvl_map : T lvl := hget lvl vatlb in
      let entries := (get ctxt vatlb) ∪ {[ entry ]} in
      hset lvl (<[ nd := entries ]> lvl_map) vatlb.

    #[global] Instance empty : Empty t := VATLB.init.
    #[global] Instance union : Union t := fun x y => hmap2 (fun _ => (∪ₘ)) x y.

    (** Domain of VATLB: the set of all contexts that have entries. *)
    #[global] Instance vatlb_dom : Dom t (gset Ctxt.t) :=
      λ vatlb,
        fold_left (λ acc lvl,
          map_fold (λ nd _ cur, {[existT lvl nd]} ∪ cur) acc (hget lvl vatlb)
        ) (enum Level) ∅.

    (** Get all final entries (blocks/pages, not table descriptors). *)
    Definition final_entries (vatlb : t) : list FE.t :=
      List.filter (λ fe, if decide (is_final (FE.lvl fe) (FE.pte fe)) then true else false)
        (elements vatlb).
  End VATLB.
  Export (hints) VATLB.

  Record t :=
    make {
        vatlb : VATLB.t;
      }.

  Definition init := make VATLB.init.

  (** ** TLB filling *)

  Definition is_active_asid (ts : TState.t)
      (asid : option (bv 16))
      (val_ttbrs : list (bv 64)) : Prop :=
    match asid with
    | Some asid =>
      ∃ val_ttbr ∈ val_ttbrs, asid = (bv_extract 48 16 val_ttbr)
    | None => True
    end.
  Instance Decision_is_active_asid (ts : TState.t)
      (asid : option (bv 16))
      (val_ttbrs : list (bv 64)) : Decision (is_active_asid ts asid val_ttbrs).
  Proof. unfold_decide. Defined.

  Definition next_va {clvl : Level}
    (ctxt : Ctxt.t)
    (index : bv 9)
    (CHILD : (Ctxt.lvl ctxt) + 1 = clvl) : prefix clvl :=
    bv_concat (level_length clvl) (Ctxt.va ctxt) index.

  Definition is_upper_ttbr (ttbr : reg) : option bool :=
    if decide
      (ttbr = TTBR0_EL1 ∨
       ttbr = TTBR0_EL2 ∨
       ttbr = TTBR0_EL3) then Some false
    else if decide
      (ttbr = TTBR1_EL1 ∨
       ttbr = TTBR1_EL2) then Some true
    else None.

  (** Seed root-level TLB entries from a list of TTBR values.

      For each TTBR value in [val_ttbrs]:
      - Computes the root page table entry address from the TTBR base and [va] index.
      - Reads the entry from memory at [time].
      - If the entry is a valid table descriptor, creates a TLB entry with
        the ASID extracted from the TTBR value (bits 48-63) and the [upper]
        flag indicating upper/lower VA range.
      - Inserts the entry into the VATLB if not already present.

      The [mem_strict] param decides if non-existing memory triggers an error.

      Returns [(vatlb', changed)] where [changed] is [true] if new entries
      were added. *)
  Definition va_fill_root (vatlb : VATLB.t) (ts : TState.t)
      (init : memoryMap)
      (mem : Memory.t)
      (time : nat)
      (va : prefix root_lvl)
      (upper : bool)
      (val_ttbrs : list (bv 64))
      (mem_strict : bool) : result string (VATLB.t * bool) :=
    foldlM (λ '(vatlb, is_changed) val_ttbr,
      let entry_addr := next_entry_addr val_ttbr va in
      if Memory.read_word entry_addr init mem time is Some memval then
        if decide (is_table root_lvl memval) then
          let asid := bv_extract 48 16 val_ttbr in
          let ndctxt := NDCtxt.make upper va (Some asid) in
          let ctxt := existT root_lvl ndctxt in
          let entry : Entry.t (Ctxt.lvl ctxt) :=
            Entry.make 0%fin val_ttbr [#memval] in
          (* add the entry to vatlb only when it is not in the original vatlb *)
          if decide (entry ∉ (VATLB.get ctxt vatlb)) then
            Ok (VATLB.insert ctxt entry vatlb, true)
          else Ok (vatlb, is_changed)
        else Ok (vatlb, is_changed)
      else
        guard_or
          ("TLB Fill: Failed to read page table memory at " ++
             (pretty entry_addr))%string
          (negb mem_strict);;
        Ok (vatlb, is_changed)
    ) (vatlb, false) val_ttbrs.

  (** Extend a TLB entry one level down by following a table descriptor.

      Given a parent TLB entry [te] at context [ctxt], reads the next-level
      page table entry at the given [index] and creates a child TLB entry.

      The child entry inherits the ASID from the parent unless the new PTE
      has the global (nG) bit clear, in which case the ASID is dropped.

      The [mem_strict] param decides if non-existing memory triggers an error.

      Returns [(vatlb', changed)] where [changed] is [true] if a new entry
      was added. *)
  Definition va_fill_lvl (vatlb : VATLB.t) (ts : TState.t)
      (init : memoryMap)
      (mem : Memory.t)
      (time : nat)
      (ctxt : Ctxt.t)
      (te : Entry.t (Ctxt.lvl ctxt))
      (index : bv 9)
      (mem_strict : bool) : result string (VATLB.t * bool) :=
    let plvl := Ctxt.lvl ctxt in
    if decide (¬is_table plvl (Entry.pte te)) then Ok (vatlb, false)
    else
      let entry_addr := next_entry_addr (Entry.pte te) index in
      if Memory.read_word entry_addr init mem time is Some next_pte then
        if decide (is_valid next_pte) then
          match inspect $ child_lvl (Ctxt.lvl ctxt) with
          | Some clvl eq:e =>
            let va := next_va ctxt index (child_lvl_add_one _ _ e) in
            let asid := if bool_decide (is_global clvl next_pte) then None
                        else Ctxt.asid ctxt in
            let ndctxt := NDCtxt.make (Ctxt.upper ctxt) va asid in
            let ctxt := existT clvl ndctxt in
            let entry := Entry.append te next_pte (child_lvl_add_one _ _ e) in
            (* add the entry to vatlb only when it is not in the original vatlb *)
            if decide (entry ∉ (VATLB.get ctxt vatlb)) then
              Ok (VATLB.insert ctxt entry vatlb, true)
            else Ok (vatlb, false)
          | None eq:_ => mthrow "An intermediate level should have a child level"
          end
        else Ok (vatlb, false)
      else
        guard_or ("TLB Fill: Failed to read next level PTE at " ++ (pretty entry_addr))%string
                 (negb mem_strict);;
        Ok (vatlb, false).

  (** Fill TLB entries for a specific VA at a given translation level.

      At the root level (level 0), seeds entries from TTBR values using
      [va_fill_root]. At deeper levels, extends existing parent entries
      using [va_fill_lvl].

      The [mem_strict] param decides if non-existing memory triggers an error.

      Returns [(tlb', changed)] where [changed] is [true] if new entries
      were added. *)
  Definition va_fill (tlb : t) (ts : TState.t)
      (init : memoryMap)
      (mem : Memory.t)
      (time : nat)
      (lvl : Level)
      (va : bv 64)
      (upper : bool)
      (val_ttbrs : list (bv 64))
      (mem_strict : bool) : result string (t * bool) :=
    '(vatlb_new, is_changed) ←
      match parent_lvl lvl with
      | None =>
        va_fill_root tlb.(vatlb) ts init mem time (level_index va root_lvl)
                     upper val_ttbrs mem_strict
      | Some plvl =>
        let pva := level_prefix va plvl in
        let index := level_index va lvl in
        foldlM (λ prev val_ttbr,
          let asid := bv_extract 48 16 val_ttbr in
          let ndctxt := NDCtxt.make upper pva (Some asid) in
          let ctxt := existT plvl ndctxt in
          (* parent entries should be from the original TLB (in the parent level) *)
          let tes := elements (VATLB.get ctxt tlb.(vatlb)) in
          foldlM (λ '(vatlb_prev, is_changed_prev) te,
            '(vatlb_lvl, is_changed_lvl) ←
              va_fill_lvl vatlb_prev ts init mem time ctxt te index mem_strict;
            mret (vatlb_lvl, is_changed_lvl || is_changed_prev)
          ) prev tes
        ) (tlb.(vatlb), false) val_ttbrs
      end;
    mret $ (TLB.make vatlb_new, is_changed).

  (** Fill TLB entries for a VA through all translation levels 0-3.

      Iterates through each level, calling [va_fill] to progressively build
      the complete translation chain from root to leaf. The [ttbr] register
      determines both the upper/lower VA range and provides the base addresses.

      Returns [(tlb', changed)] where [changed] is [true] if new entries
      were added. *)
  Definition update (tlb : t) (ts : TState.t)
      (init : memoryMap)
      (mem : Memory.t)
      (time : nat)
      (va : bv 64)
      (ttbr : reg) : result string (t * bool) :=
    upper ← othrow "The register is not TTBR" (is_upper_ttbr ttbr);
    sregs ← othrow "TTBR should exist in initial state"
      $ TState.read_sreg_at ts ttbr time;
    val_ttbrs ← othrow "TTBR should be a 64 bit value"
      $ mapM (M:=option) (λ sreg, regval_to_val ttbr sreg.1) sregs;
    foldlM (λ '(tlb_prev, is_changed_prev) lvl,
      '(tlb_new, is_changed) ←
        va_fill tlb_prev ts init mem time lvl va upper val_ttbrs (*strict*)true;
      mret (tlb_new, is_changed || is_changed_prev)
    ) (tlb, false) (enum Level).

  (** ** TLB Traversal for BBM checking *)

  (** Traverse root-level TLB entries for all possible indices.
      Unlike [va_fill_root] which fills for a specific VA, this function
      iterates over all 512 possible root indices to build a complete TLB.

      The [mem_strict] param decides if non-existing memory triggers an error. *)
  Definition traverse_root (vatlb : VATLB.t) (ts : TState.t)
        (init : memoryMap)
        (mem : Memory.t)
        (time : nat)
        (upper : bool)
        (val_ttbrs : list (bv 64))
        (mem_strict : bool) : result string (VATLB.t * bool) :=
    foldlM (λ '(vatlb_prev, is_changed_prev) index,
      '(vatlb_new, is_changed) ←
        va_fill_root vatlb_prev ts init mem time index upper val_ttbrs mem_strict;
      mret (vatlb_new, is_changed || is_changed_prev)
    ) (vatlb, false) (enum (bv 9)).

  (** Traverse one level down from a parent entry for all possible indices.
      Iterates over all 512 indices at the next level to extend the TLB.

      The [mem_strict] param decides if non-existing memory triggers an error. *)
  Definition traverse_lvl (vatlb : VATLB.t) (ts : TState.t)
        (init : memoryMap)
        (mem : Memory.t)
        (time : nat)
        (fe : FE.t)
        (mem_strict : bool) : result string (VATLB.t * bool) :=
    foldlM (λ '(vatlb_prev, is_changed_prev) index,
      '(vatlb_new, is_changed_new) ←
        va_fill_lvl vatlb_prev ts init mem time (FE.ctxt fe) (projT2 fe) index mem_strict;
      mret (vatlb_new, is_changed_new || is_changed_prev)
    ) (vatlb, false) (enum (bv 9)).

  (** Traverse the page table at a specific level and build TLB entries.
      At root level, uses [traverse_root]. At deeper levels, extends all
      existing parent entries using [traverse_lvl].

      The [mem_strict] param decides if non-existing memory triggers an error. *)
  Definition traverse (tlb : t) (ts : TState.t)
      (init : memoryMap)
      (mem : Memory.t)
      (time : nat)
      (lvl : Level)
      (upper : bool)
      (val_ttbrs : list (bv 64))
      (mem_strict : bool) : result string (t * bool) :=
    '(vatlb_new, is_changed) ←
      match parent_lvl lvl with
      | None => traverse_root tlb.(vatlb) ts init mem time upper val_ttbrs mem_strict
      | Some plvl =>
        let fes :=
          omap (λ fe,
            if decide (FE.lvl fe = plvl ∧ is_active_asid ts (FE.asid fe) val_ttbrs)
              then Some fe
              else None) (elements tlb.(vatlb)) in
        foldlM (λ '(vatlb, is_changed_prev) fe,
          '(vatlb_new, is_changed) ← traverse_lvl vatlb ts init mem time fe mem_strict;
          mret (vatlb_new, is_changed || is_changed_prev)
        ) (tlb.(vatlb), false) fes
      end;
    mret $ (TLB.make vatlb_new, is_changed).

  (** Fill TLB entries for all VAs through all translation levels 0-3.
      Unlike [update] which fills for a single VA, this function traverses
      the entire page table to build a complete TLB for BBM checking.

      The [mem_strict] param decides if non-existing memory triggers an error. *)
  Definition update_all (tlb : t) (ts : TState.t)
        (init : memoryMap)
        (mem : Memory.t)
        (time : nat)
        (ttbr : reg)
        (mem_strict : bool) : result string (t * bool) :=
    upper ← othrow "The register is not TTBR" (is_upper_ttbr ttbr);
    sregs ← othrow "TTBR should exist in initial state"
      $ TState.read_sreg_at ts ttbr time;
    val_ttbrs ← othrow "TTBR should be a 64 bit value"
      $ mapM (M:=option) (λ sreg, regval_to_val ttbr sreg.1) sregs;
    foldlM (λ '(tlb_prev, is_changed_prev) lvl,
      '(tlb_new, is_changed) ←
          traverse tlb_prev ts init mem time lvl upper val_ttbrs mem_strict;
      mret (tlb_new, is_changed || is_changed_prev)
    ) (tlb, false) (enum Level).

  (** ** TLB invalidation *)

  (** Decide if a TLB entry is affected by an invalidation by asid at this asid *)
  Definition affects_asid (asid : bv 16)
                          (ctxt : Ctxt.t) : Prop :=
    match (Ctxt.asid ctxt) with
    | Some te_asid => te_asid = asid
    | None => False
    end.
  Instance Decision_affects_asid (asid : bv 16) (ctxt : Ctxt.t) :
    Decision (affects_asid asid ctxt).
  Proof. unfold_decide. Defined.

  (** Decide if a TLB entry is affected by an invalidation by va at this asid *)
  Definition affects_va (va : bv 36) (last : bool) (upper : bool)
                         (ctxt : Ctxt.t)
                         (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
    let '(te_lvl, te_va, te_val) :=
          (Ctxt.lvl ctxt, Ctxt.va ctxt, Entry.pte te) in
    (match_prefix_at te_lvl te_va va)
    ∧ (if last then is_final te_lvl te_val else True)
    ∧ (upper = Ctxt.upper ctxt).
  Instance Decision_affects_va (va : bv 36) (last : bool) (upper : bool)
                                (ctxt : Ctxt.t)
                                (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (affects_va va last upper ctxt te).
  Proof. unfold_decide. Defined.

  (** Decide a TLBI instruction affects a given TLB entry *)
  Definition affects (tlbi : TLBI.t) (ctxt : Ctxt.t)
                     (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
    match tlbi with
    | TLBI.All tid => True
    | TLBI.Va tid asid va last upper =>
      affects_asid asid ctxt ∧ affects_va va last upper ctxt te
    | TLBI.Asid tid asid => affects_asid asid ctxt
    | TLBI.Vaa tid va last upper => affects_va va last upper ctxt te
    end.
  Instance Decision_affects (tlbi : TLBI.t) (ctxt : Ctxt.t)
                     (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (affects tlbi ctxt te).
  Proof. unfold_decide. Defined.

  (** Apply a TLBI instruction to a TLB by removing all affected entries. *)
  Definition tlbi_apply (tlbi : TLBI.t) (tlb : t) : t :=
    set vatlb (filter (λ '(existT ctxt te), ¬ affects tlbi ctxt te)) tlb.

  (** ** TLB Snapshot Functions for Specific VA (Translation) *)

  (** Compute unique TLB snapshots for a specific VA over a time range.

      Iterates from [time_prev + 1] to [time_prev + cnt], updating the TLB
      at each step by:
      - Applying any TLBI events in memory.
      - Calling [update] to fill translation entries for the specific VA.

      Only records snapshots where the TLB actually changed. The result is
      accumulated in [acc] and returned in descending timestamp order. *)
  Fixpoint unique_snapshots_va_between (ts : TState.t) (mem_init : memoryMap)
                       (mem : Memory.t)
                       (tlb_prev : t)
                       (time_prev cnt : nat)
                       (va : bv 64)
                       (ttbr : reg)
                       (acc : list (t * nat)) :
                      result string (list (t * nat)) :=
    match cnt with
    | O => mret acc
    | S ccnt =>
      let time_cur := time_prev + 1 in
      '(tlb, is_changed) ←
        match mem !! time_cur with
        | Some ev =>
            let (tlb_inv, is_changed_by_tlbi) :=
              if ev is Ev.Tlbi tlbi then (tlbi_apply tlbi tlb_prev, true) else (tlb_prev, false)
            in
            '(tlb, is_changed) ← update tlb_inv ts mem_init mem time_cur va ttbr;
            mret (tlb, is_changed || is_changed_by_tlbi)
        | None => mret (init, false)
        end;
      let acc :=
        match is_changed with
        | true => (tlb, time_cur) :: acc
        | false => acc
        end in
      unique_snapshots_va_between
        ts mem_init mem tlb time_cur ccnt va ttbr acc
    end.

  (** Compute all unique TLB snapshots for a specific VA from time 0 to [time].

      Initializes the TLB at time 0, then calls [unique_snapshots_va_between]
      to track changes. Returns snapshots in descending timestamp order,
      including the initial state at time 0.  *)
  Definition unique_snapshots_va_until (ts : TState.t)
                       (mem_init : memoryMap)
                       (mem : Memory.t)
                       (time : nat)
                       (va : bv 64)
                       (ttbr : reg) : result string (list (t * nat)) :=
    '(tlb, _) ← update init ts mem_init mem 0 va ttbr;
    unique_snapshots_va_between ts mem_init mem tlb 0 time va ttbr [(tlb, 0)].

  (** Find snapshots at or after [time].

      If [time] falls between two snapshots, keep the closest earlier TLB state
      as a snapshot at [time]. *)
  Fixpoint snapshots_from (time : nat) (snapshots : list (t * nat))
      : list (t * nat) :=
    match snapshots with
    | [] => []
    | (tlb, t) :: snapshots =>
      if time <? t then (tlb, t) :: snapshots_from time snapshots
      else [(tlb, time)]
    end.

  (** ** TLB Snapshot Functions for All VAs (BBM Checking) *)

  (** Compute unique TLB snapshots over a time range for BBM checking.

      Iterates from [time_prev + 1] to [time_prev + cnt], updating the TLB
      at each step by:
      - Applying any TLBI events in memory.
      - Calling [update_all] to fill translation entries for all VAs.

      Only records snapshots where the TLB actually changed. The result is
      accumulated in [acc] and returned in descending timestamp order. *)
  Fixpoint unique_snapshots_between (ts : TState.t) (mem_init : memoryMap)
                       (mem : Memory.t)
                       (tlb_prev : t)
                       (time_prev cnt : nat)
                       (ttbr : reg)
                       (acc : list (t * nat))
                       (mem_strict : bool) :
                      result string (list (t * nat)) :=
    match cnt with
    | O => mret acc
    | S ccnt =>
      let time_cur := time_prev + 1 in
      '(tlb, is_changed) ←
        match mem !! time_cur with
        | Some ev =>
            let (tlb_inv, is_changed_by_tlbi) :=
              if ev is Ev.Tlbi tlbi
              then (tlbi_apply tlbi tlb_prev, true)
              else (tlb_prev, false)
            in
            '(tlb, is_changed) ←
              update_all tlb_inv ts mem_init mem time_cur ttbr mem_strict;
            mret (tlb, is_changed || is_changed_by_tlbi)
        | None => mret (init, false)
        end;
      let acc :=
        match is_changed with
        | true => (tlb, time_cur) :: acc
        | false => acc
        end in
      unique_snapshots_between ts mem_init mem tlb time_cur ccnt ttbr acc mem_strict
    end.

  (** Compute all unique TLB snapshots from time 0 to [time] for BBM checking.

      Initializes the TLB at time 0, then calls [unique_snapshots_between]
      to track changes. Returns snapshots in descending timestamp order,
      including the initial state at time 0. *)
  Definition unique_snapshots_until (ts : TState.t)
                       (mem_init : memoryMap)
                       (mem : Memory.t)
                       (time : nat)
                       (ttbr : reg)
                       (mem_strict : bool) : result string (list (t * nat)) :=
    '(tlb, _) ← update_all init ts mem_init mem 0 ttbr mem_strict;
    unique_snapshots_between ts mem_init mem tlb 0 time ttbr [(tlb, 0)] mem_strict.

  (** Check if a TLB entry is invalidated by a TLBI from a different thread.

      Returns [True] if the TLBI is from a different thread than [tid] and
      the entry is affected by the invalidation. *)
  Definition is_te_invalidated_by_tlbi
                (tlbi : TLBI.t)
                (tid : nat)
                (ctxt : Ctxt.t)
                (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
      TLBI.tid tlbi <> tid ∧ (affects tlbi ctxt te).
  Instance Decision_is_te_invalidated_by_tlbi (tlbi : TLBI.t) (tid : nat)
                (ctxt : Ctxt.t) (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (is_te_invalidated_by_tlbi tlbi tid ctxt te).
  Proof. unfold_decide. Defined.

  (** Find the first TLBI event in [evs] that invalidates the given entry.

      Scans through timestamped events looking for a TLBI from another thread
      that affects the entry [te] at context [ctxt]. Returns [Some t] with the
      timestamp of the first such TLBI, or [None] if no invalidation is found. *)
  Fixpoint invalidation_time_from_evs (tid : nat)
              (ctxt : Ctxt.t)
              (te : Entry.t (Ctxt.lvl ctxt))
              (evs : list (Ev.t * nat)) : result string (option nat) :=
    match evs with
    | [] => mret None
    | (ev, t) :: tl =>
      match ev with
      | Ev.Tlbi tlbi =>
        if decide (is_te_invalidated_by_tlbi tlbi tid ctxt te) then
          mret (Some t)
        else
          invalidation_time_from_evs tid ctxt te tl
      | _ => invalidation_time_from_evs tid ctxt te tl
      end
    end.

  (** Calculate the earliest future time at which a TLB entry is invalidated.

      Searches memory events after [trans_time] for a TLBI from another thread
      that would invalidate entry [te]. Used to determine the validity window
      of a translation result. *)
  Definition invalidation_time (mem : Memory.t)
                (tid : nat)
                (trans_time : nat)
                (ctxt : Ctxt.t)
                (te : Entry.t (Ctxt.lvl ctxt)) : result string (option nat) :=
    let evs := PromMemory.cut_after_with_timestamps trans_time mem in
    invalidation_time_from_evs tid ctxt te evs.

  Definition get_leaf_ptes_with_inv_time_by_ctxt (mem : Memory.t)
              (tid : nat)
              (tlb : t) (trans_time : nat)
              (lvl : Level)
              (ndctxt : NDCtxt.t lvl) :
            result string (list (bv 64 * list (bv 64) * (option nat))) :=
    let ctxt := existT lvl ndctxt in
    let tes := VATLB.get ctxt tlb.(TLB.vatlb) in
    let tes := if decide (lvl = leaf_lvl) then tes
               else filter (λ te, is_block (TLB.Entry.pte te)) tes in
    for te in (elements tes) do
      ti ← invalidation_time mem tid trans_time ctxt te;
      mret ((Entry.val_ttbr te), (vec_to_list (Entry.ptes te)), ti)
    end.

  (** Get all the TLB entries (including the TTBR value) TTBR value that
      could translate the given VA at the provided level
      and in the provided ASID context.
      Return each TLB entry as a list of descriptors [list val] with
      the invalidation time [nat] *)
  Definition get_leaf_ptes_with_inv_time (mem : Memory.t)
              (tid : nat)
              (tlb : t) (trans_time : nat)
              (lvl : Level)
              (va : bv 64) (asid : bv 16) :
            result string (list (bv 64 * list (bv 64) * (option nat))) :=
    upper ← othrow ("VA is not in the 48 bits range: " ++ (pretty va))%string
                (is_upper_va va);
    let ndctxt_asid := NDCtxt.make upper (level_prefix va lvl) (Some asid) in
    let ndctxt_global := NDCtxt.make upper (level_prefix va lvl) None in
    candidates_asid ←
      get_leaf_ptes_with_inv_time_by_ctxt mem tid tlb trans_time lvl ndctxt_asid;
    candidates_global ←
      get_leaf_ptes_with_inv_time_by_ctxt mem tid tlb trans_time lvl ndctxt_global;
    mret (candidates_asid ++ candidates_global)%list.

  (** Get all the TLB entries and the corresponding TTBR value that
      could translate the given VA in the provided ASID context.
      Return each TLB entry as a list of descriptors [list val] with
      the invalidation time [nat] *)
  Definition lookup (mem : Memory.t)
              (tid : nat)
              (tlb : TLB.t) (trans_time : nat)
              (va : bv 64) (asid : bv 16) :
            result string (list (bv 64 * list (bv 64) * (option nat))) :=
    res1 ← get_leaf_ptes_with_inv_time mem tid tlb trans_time 1%fin va asid;
    res2 ← get_leaf_ptes_with_inv_time mem tid tlb trans_time 2%fin va asid;
    res3 ← get_leaf_ptes_with_inv_time mem tid tlb trans_time leaf_lvl va asid;
    mret (res1 ++ res2 ++ res3).

  (** Get all the TLB entries and the corresponding TTBR value that
      trigger fault from the given VA
      at the provided level and in the provided ASID context.
      Return each TLB entry as a list of descriptors [list val] with
      the invalidation time [option nat] *)
  Definition get_invalid_ptes_with_inv_time_by_lvl_asid (ts : TState.t)
                (init : memoryMap)
                (mem : Memory.t)
                (tid : nat)
                (tlb : t) (trans_time : nat)
                (lvl : Level)
                (va : bv 64)
                (asid : option (bv 16))
                (ttbr : reg) :
        result string (list (bv 64 * list (bv 64) * (option nat))) :=
    if parent_lvl lvl is Some parent_lvl then
      upper ← othrow ("VA is not in the range: " ++ (pretty va))%string
        (is_upper_va va);
      let ndctxt := NDCtxt.make upper (level_prefix va parent_lvl) asid in
      let ctxt := existT parent_lvl ndctxt in
      let tes := VATLB.get ctxt tlb.(TLB.vatlb) in
      let tes := filter (λ te, is_table parent_lvl (TLB.Entry.pte te)) tes in
      invalid_ptes ←
        for te in (elements tes) do
          let entry_addr :=
            next_entry_addr (Entry.pte te) (level_index va lvl) in
          if Memory.read_word entry_addr init mem trans_time is Some memval then
            if decide (is_valid memval) then mret None
            else
              ti ← invalidation_time mem tid trans_time ctxt te;
              let vals := (vec_to_list (Entry.ptes te)) ++ [memval] in
              mret $ Some (Entry.val_ttbr te, vals, ti)
          else
            mthrow "The PTE is missing"
        end;
      mret $ omap id invalid_ptes
    else
      sregs ← othrow "TTBR should exist in initial state"
        $ TState.read_sreg_at ts ttbr trans_time;
      invalid_ptes ←
        for sreg in sregs do
          val_ttbr ← othrow "TTBR should be a 64 bit value"
            $ regval_to_val ttbr sreg.1;
          let entry_addr :=
              next_entry_addr (val_to_addr (size:= 8) val_ttbr) (level_index va lvl) in
          if Memory.read_word entry_addr init mem trans_time is Some memval then
            if decide (is_valid memval) then mret None
            else
              mret $ Some ((val_ttbr : bv 64), [memval], None)
          else mthrow "The root PTE is missing"
        end;
      mret $ omap id invalid_ptes.

  (** Get all the TLB entries and the corresponding TTBR value that
      trigger fault from the given VA
      in the provided ASID context.
      Return each TLB entry as a list of descriptors [list val] with
      the invalidation time [option nat] *)
  Definition get_invalid_ptes_with_inv_time_by_lvl (ts : TState.t)
                (init : memoryMap)
                (mem : Memory.t)
                (tid : nat)
                (tlb : t) (trans_time : nat)
                (lvl : Level)
                (va : bv 64) (asid : bv 16)
                (ttbr : reg) :
      result string (list (bv 64 * list (bv 64) * (option nat))) :=
    candidates_asid ←
      get_invalid_ptes_with_inv_time_by_lvl_asid
        ts init mem tid tlb trans_time lvl va (Some asid) ttbr;
    candidates_global ←
      get_invalid_ptes_with_inv_time_by_lvl_asid
        ts init mem tid tlb trans_time lvl va None ttbr;
    mret (candidates_asid ++ candidates_global).

  Definition get_invalid_ptes_with_inv_time (ts : TState.t) (init : memoryMap)
                       (mem : Memory.t)
                       (tid : nat)
                       (tlb : TLB.t) (time : nat)
                       (va : bv 64) (asid : bv 16)
                       (ttbr : reg) :
    result string (list (bv 64 * list (bv 64) * (option nat))) :=
  fault_ptes ←
    for lvl in enum Level do
      get_invalid_ptes_with_inv_time_by_lvl ts init mem tid tlb time lvl va asid ttbr
    end;
  mret $ List.concat fault_ptes.

  Definition invalidation_time_lt (ti_old ti_new : option nat) : bool :=
    match ti_old, ti_new with
    | Some ti_old, Some ti_new => ti_old <? ti_new
    | None, None => false
    | None, Some _ => false
    | Some _, None => true
    end.

  Definition is_new_entry (val_ttbr : bv 64) (path : list (bv 64))
      (ti_new : option nat)
      (entries : list (bv 64 * list (bv 64) * nat * option nat)) : Prop :=
    ¬ ∃ entry ∈ entries,
      let '(vt, p, _, ti) := entry in
      val_ttbr = vt ∧ path = p ∧ invalidation_time_lt ti ti_new = false.

  Instance Decision_is_new_entry val_ttbr path ti_new entries :
      Decision (is_new_entry val_ttbr path ti_new entries).
  Proof. unfold is_new_entry. apply _. Defined.

  (* Snapshots are sorted in the descending order of [trans_time].
    Thus, we do not have to use [trans_time] to check the interval *)
  Definition get_valid_entries_from_snapshots (snapshots : list (t * nat))
                (mem : Memory.t)
                (tid : nat)
                (va : bv 64) (asid : bv 16) :
              result string (list (bv 64 * list (bv 64) * nat * option nat)) :=
    foldrM (λ '(tlb, trans_time) entries,
      candidates ← TLB.lookup mem tid tlb trans_time va asid;
      let new :=
        omap (λ '(val_ttbr, path, ti_opt),
          if decide (is_new_entry val_ttbr path ti_opt entries) then
            Some (val_ttbr, path, trans_time, ti_opt)
          else None
        ) candidates in
      mret (new ++ entries)
    ) snapshots [].

  Definition get_invalid_entries_from_snapshots (snapshots : list (t * nat))
                (ts : TState.t)
                (init : memoryMap)
                (mem : Memory.t)
                (tid : nat) (is_ets2 : bool)
                (va : bv 64) (asid : bv 16) (ttbr : reg) :
              result string (list (bv 64 * list (bv 64) * nat * option nat)) :=
    foldrM (λ '(tlb, trans_time) entries,
      if decide (is_ets2 ∧ trans_time < ts.(TState.vwr) ⊔ ts.(TState.vrd)) then
        mret entries
      else
        candidates ← TLB.get_invalid_ptes_with_inv_time ts init mem tid tlb trans_time va asid ttbr;
        let new :=
          omap (λ '(val_ttbr, path, ti_opt),
            if decide (is_new_entry val_ttbr path ti_opt entries) then
              Some (val_ttbr, path, trans_time, ti_opt)
            else None
          ) candidates in
        mret (new ++ entries)
    ) snapshots [].
End TLB.
Export (hints) TLB.

Module VATLB := TLB.VATLB.

(** * Instruction semantics *)

(** ** IIS definition *)

(** Check if MMU is enabled by reading SCTLR_EL1.M bit (bit 0). *)
Definition is_mmu_enabled (ts : TState.t) : result string bool :=
  '(sctlr, _) ← othrow "SCTLR_EL1 is not set" $ TState.read_reg ts SCTLR_EL1;
  val ← othrow
    "SCTLR_EL1 should be a 64 bit value"
    (regval_to_val SCTLR_EL1 sctlr);
  Ok ((bv_extract 0 1 val) =? 1%bv).

(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  (* Translation Results *)
  Module TransRes.
    Record t :=
      make {
          va : bv 36;
          time : nat;
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
        (* Virtual address of the current translated memory access, if any. *)
        access_va : option (bv 64);
        (* The translations results of the latest translation *)
        trs : option TransRes.t;
        inv_time : option nat
      }.

  Definition init : t := make 0 None None None.

  (** Add a new view to the IIS *)
  Definition add (v : view) (iis : t) : t :=
    iis |> set strict (max v).

  Definition set_trs (tres : TransRes.t) :=
    setv trs (Some tres).

  Definition set_access_va (va_opt : option (bv 64)) :=
    setv access_va va_opt.

  Definition clear_access_va : t → t := setv access_va None.

  Definition set_inv_time (ti_opt : option nat) :=
    setv inv_time ti_opt.

End IIS.

Definition view_if := UMPromising.view_if.


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
    Exec.t (PPState.t TState.t Ev.t IIS.t) string unit :=
  guard_or
    ("Cannot write to unknown register " ++ pretty reg)%string
    (¬(is_reg_unknown reg));;
  iis ← mget PPState.iis;
  ts ← mget PPState.state;
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
          mset PPState.state $ TState.add_wsreg reg val vpost;;
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
Definition read_imem (addr : address) (init : memoryMap)
    (mem : Memory.t) : Exec.res string (bv 32) :=
  bytes ← othrow "Modified instruction memory" $
    for a in addr_range addr 4 do
      Memory.read_initial a init mem
    end;
  mret (bv_of_bytes 32 bytes).

(** Returns all interesting timestamp when reading range [addr, addr+size) with
    minimum view [vpre]. Those are [vpre] itself and any later timestamp that
    contain an overlapping write event *)
Definition read_candidates (addr : address) (size : N) (vpre : view)
    (mem : Memory.t) : list nat :=
  PromMemory.cut_after_with_timestamps vpre mem
    |> omap (λ '(ev, t),
              match Ev.get_msg ev with
              | Some msg =>
                  if decide (addr_overlap addr size (Msg.addr msg) (Msg.size msg))
                  then Some t else None
              | None => None
              end)
    |> cons vpre.

(** Per-byte forwarding. Forwarding fires when [fwdb !! addr] has an entry [fwd]
    with [fwd.time > tread], which means there is a more recent po-previous
    write that hasn't been propagated yet. In that case we replace the
    byte/view/timestamp with the ones of the forwarded write. The timestamp
    returned (last value) is for coherence checking purposes). Returns [None] if
    no forwarding occurs *)
Definition read_fwd (fwdb : gmap address FwdItem.t) (macc : mem_acc)
    (mem : Memory.t) (tread : nat) (addr : address) :
    Exec.res string (option (bv 8 * view * nat)) :=
  match fwdb !! addr with
  | Some fwd =>
    if (tread <? fwd.(FwdItem.time))%nat then
      ev ← othrow "Failed to retrieve forwarded event" (mem !! fwd.(FwdItem.time));
      msg ← othrow "Forwarded event is not a memory write" (Ev.get_msg ev);
      byte' ← othrow "Failed to read a byte from the message" (Msg.read_byte addr msg);
      mret (Some (byte', FwdItem.read_fwd_view macc fwd, fwd.(FwdItem.time)))
    else mret None
  | None => mret None
  end.

(** Performs a multi-byte explicit memory read. This involves multiple steps:
    - Computing the minimum view
    - Picking an interesting timestamp [tread]with [read_candidates]
    - Reading main memory at [tread] with [Memory.read_from]
    - Applying forwarding ([read_fwd])
    - Do a coherence check
    - Do an translation invalidation check (about [invalidation_time])
    - Update all the views that should be updated
    - If exclusive, set the exclusive database *)
Definition read_mem_explicit (addr : address) (size : N) (macc : mem_acc)
    (init : memoryMap) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string (bv (8 * size)) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  ts ← mget PPState.state;
  vaddr ← mget (IIS.strict ∘ PPState.iis);
  guard_discard (TState.no_promises_until vaddr ts);;
  let addrs := addr_range addr size in
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
              ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
                (* Strong Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  mem ← mget PPState.mem;
  tread ← mchoosel (read_candidates addr size vpre mem);
  raw_bytes ← othrow "Memory read of unmapped bytes" $
    Memory.read_from addr size tread init mem;
  (* per-byte (value, view, write-timestamp) after forwarding *)
  fwd_bytes ← mlift $
    for (addr, (byte, twrite)) in zip addrs raw_bytes do
      read_fwd ts.(TState.fwdb) macc mem tread addr
        |$> default (byte, tread, twrite)
    end;

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
    then
      va ← mget (IIS.access_va ∘ PPState.iis);
      mset PPState.state $ TState.set_xclb tread va addr size
    else mret ());;
  mset PPState.iis $ IIS.add vpost;;
  mret res.

(** Read a PTE from the TLB entry selected at translation start *)
Definition read_pte :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string (bv 64) :=
  tres_opt ← mget (IIS.trs ∘ PPState.iis);
  tres ← othrow "TTW read before translation start" tres_opt;
  viio ← mget (IIS.strict ∘ PPState.iis);
  let vpost := viio ⊔ tres.(IIS.TransRes.time) in
  ts ← mget PPState.state;
  guard_discard (TState.no_promises_until vpost ts);;
  '(ntres, val) ← mlift (IIS.TransRes.pop tres);
  msetv (IIS.trs ∘ PPState.iis) (Some ntres);;
  mset PPState.iis $ IIS.add vpost;;
  mset PPState.state $ TState.update TState.vspec vpost;;
  mret val.

(** Performs a memory write for a thread [tid] at [addr]:

    - First attempt to fulfill an existing promises, or add a new one otherwise
    - Compute the minimum view of the write
    - Discard if the write is not compatible with that view or coherence checks
    - Discard if the write is supposed to be atomic, but other writes intervened
    - Update all the views that should be updated
    - Set the forwarding database
    - If a new promise was added, return its minimum view, otherwise [None] *)
Definition write_mem (tid : nat) (addr : address) (size : N) (macc : mem_acc)
    (data : bv (8 * size)) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string (option view) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  let msg := Msg.make size tid addr data in
  let is_release := is_rel_acq macc in
  let addrs := addr_range addr size in
  ts ← mget PPState.state;
  mem ← mget PPState.mem;
  '(time, new_promise) ←
    match Memory.fulfill msg (TState.prom_wr ts) mem with
    | Some time => mret (time, false)
    | None =>
      time ← Exec.liftSt PPState.mem $ Memory.promise (Ev.Msg msg);
      mret (time, true)
    end;
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

  xcl ← if is_exclusive macc then
      match TState.xclb ts with
      | None => mdiscard
      | Some (tread, rva, raddr, rsize) =>
        mset PPState.state $ TState.clear_xclb;;
        va ← mget (IIS.access_va ∘ PPState.iis);
        if decide (rva = va ∧ addr = raddr ∧ size = rsize) then
          guard_discard' (Memory.exclusive tid addr size tread time mem);;
          mret true
        else
          (* If the store-exclusive footprint does not exactly match the previous
             load-exclusive footprint (including va), it may still succeed as an
             ordinary store, but without exclusive atomicity guarantees. *)
          mret false
      end
    else mret false;

  mset PPState.state $ TState.set_fwdbs addrs time vdata xcl;;
  mset PPState.iis IIS.clear_access_va;;
  mret (if (new_promise : bool) then Some vpre else None).


(** ** Barrier semantics *)

(** Perform a Context Synchronization Event (CSE).

    CSEs occur at ISB instructions, exception taking, and exception returns.
    They ensure that all prior context-changing operations (MSR writes) are
    observed before subsequent instruction fetch and execution.

    Non-deterministically chooses a view between the current dependencies
    and [vmax_t], then updates [vcse] and adds a CSE marker to the local
    event list. *)
Definition run_cse (vmax_t : view) : Exec.t (TState.t * IIS.t) string () :=
  ts ← mget fst;
  iis ← mget snd;
  let v := ts.(TState.vspec) ⊔ ts.(TState.vcse)
            ⊔ ts.(TState.vdsb) ⊔ ts.(TState.vmsr) in
  let vpre := IIS.strict iis ⊔ v in
  guard_discard (TState.no_promises_until vpre ts);;
  vpost ← mchoosel $ TState.cse_candidates vpre vmax_t ts;
  mset fst $ TState.cse vpost;;
  mset snd $ IIS.add vpost.

(** Execute a barrier instruction (DMB, DSB, or ISB).

    Barriers enforce ordering between memory accesses by updating view
    state. The specific semantics depend on the barrier type:
    - DMB: Orders loads/stores without waiting for completion.
    - DSB: Stronger ordering, waits for prior operations to complete.
    - ISB: Context synchronization, handled via [run_cse]. *)
Definition run_barrier (barrier : barrier) (vmax_t : view) :
  Exec.t (TState.t * IIS.t) string () :=
  ts ← mget fst;
  match barrier with
  | Barrier_DMB dmb => (* dmb *)
      match dmb.(DxB_types) with
      | MBReqTypes_All (* dmb sy *) =>
          let vpost :=
            ts.(TState.vrd) ⊔ ts.(TState.vwr)
            ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb)
          in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset fst $ TState.update TState.vdmb vpost;;
          mset snd $ IIS.add vpost
      | MBReqTypes_Reads (* dmb ld *) =>
          let vpost := ts.(TState.vrd) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset fst $ TState.update TState.vdmb vpost;;
          mset snd $ IIS.add vpost
      | MBReqTypes_Writes (* dmb st *) =>
          let vpost := ts.(TState.vwr) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset fst $ TState.update TState.vdmbst vpost;;
          mset snd $ IIS.add vpost
      end
  | Barrier_DSB dsb => (* dsb *)
      guard_or "Non-shareable barrier are not supported"
       (dsb.(DxB_domain) ≠ MBReqDomain_Nonshareable);;
       match dsb.(DxB_types) with
      | MBReqTypes_All (* dsb sy *) =>
          let vpost :=
            ts.(TState.vrd) ⊔ ts.(TState.vwr)
            ⊔ ts.(TState.vdmb) ⊔ ts.(TState.vdmbst)
            ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) ⊔ ts.(TState.vtlbi)
          in
          guard_discard (TState.no_promises_until vpost ts);;
          mset fst $ TState.update TState.vdsb vpost;;
          mset snd $ IIS.add vpost
      | MBReqTypes_Reads (* dsb ld *) =>
          let vpost := ts.(TState.vrd) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset fst $ TState.update TState.vdsb vpost;;
          mset snd $ IIS.add vpost
      | MBReqTypes_Writes (* dsb st *) =>
          let vpost := ts.(TState.vwr) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          guard_discard (TState.no_write_promises_until vpost ts);;
          mset fst $ TState.update TState.vdsb vpost;;
          mset snd $ IIS.add vpost
      end
  | Barrier_ISB () => run_cse vmax_t
  | _ => mthrow "Unsupported barrier"
  end.

(** ** Translation semantics *)

Definition run_tlbi (tid : nat) (viio : view) (tlbi : TLBIInfo) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string (option view) :=
  guard_or
    "Non-shareable TLBIs are not supported"
    (tlbi.(TLBIInfo_shareability) ≠ Shareability_NSH);;
  guard_or
    "TLBIs in other regimes than EL10 are unsupported"
    (tlbi.(TLBIInfo_rec).(TLBIRecord_regime) = Regime_EL10);;
  let asid := tlbi.(TLBIInfo_rec).(TLBIRecord_asid) in
  let va := tlbi.(TLBIInfo_rec).(TLBIRecord_address) in
  let last := tlbi.(TLBIInfo_rec).(TLBIRecord_level) =? TLBILevel_Last in
  let upper := bv_extract 55 1 va =? 1%bv in
  let va_extracted := bv_extract 12 36 va in
  ts ← mget PPState.state;
  iis ← mget PPState.iis;
  let vpre := ts.(TState.vcse) ⊔ ts.(TState.vdsb) ⊔ ((*iio*) IIS.strict iis)
              ⊔ viio ⊔ ts.(TState.vspec) in
  '(tlbiev : TLBI.t) ←
    match tlbi.(TLBIInfo_rec).(TLBIRecord_op) with
    | TLBIOp_ALL => mret $ TLBI.All tid
    | TLBIOp_VMALL => mret $ TLBI.All tid
    | TLBIOp_ASID => mret $ TLBI.Asid tid asid
    | TLBIOp_VAA => mret $ TLBI.Vaa tid va_extracted last upper
    | TLBIOp_VA => mret $ TLBI.Va tid asid va_extracted last upper
    | _ => mthrow "Unsupported kind of TLBI"
    end;
  mem ← mget PPState.mem;
  '(time, new_promise) ←
    match Memory.fulfill tlbiev (TState.prom_tlbi ts) mem with
    | Some t => mret (t, false)
    | None =>
      t ← Exec.liftSt PPState.mem $ Memory.promise tlbiev;
      mret (t, true)
    end;
  guard_discard (vpre < time)%nat;;
  mset (TState.prom_tlbi ∘ PPState.state) (filter (λ t, t ≠ time));;
  mset PPState.state $ TState.update TState.vtlbi time;;
  mset PPState.iis $ IIS.add time;;
  mret (if (new_promise : bool) then Some vpre else None).

Definition va_in_range (va : bv 64) : Prop :=
  let top_bits := bv_extract 48 16 va in
  top_bits = (-1)%bv ∨ top_bits = 0%bv.
Instance Decision_va_in_range (va : bv 64) : Decision (va_in_range va).
Proof. unfold_decide. Defined.

(** Determine the TTBR register for a VA based on the translation regime. *)
Definition ttbr_of_regime (va : bv 64) (regime : Regime) : result string reg :=
  match regime with
  | Regime_EL10 =>
    let varange_bit := bv_extract 48 1 va in
    if varange_bit =? 1%bv
      then Ok (TTBR1_EL1 : reg)
      else Ok (TTBR0_EL1 : reg)
  | _ => Error "This model does not support multiple regimes"
  end.

Definition ets2 (ts : TState.t) : result string bool :=
  '(mmfr1, _) ← othrow
    "ETS is indicated in the ID_AA64MMFR1_EL1 register value"
    (TState.read_reg ts ID_AA64MMFR1_EL1);
  val ← othrow
    "ID_AA64MMFR1_EL1 should be a 64 bit value"
    (regval_to_val ID_AA64MMFR1_EL1 mmfr1);
  let ets_bits := bv_extract 36 4 val in
  mret ((ets_bits =? 2%bv) || (ets_bits =? 3%bv)).

Definition ets3 (ts : TState.t) : result string bool :=
  '(mmfr1, _) ← othrow
    "ETS is indicated in the ID_AA64MMFR1_EL1 register value"
    (TState.read_reg ts ID_AA64MMFR1_EL1);
  val ← othrow
    "ID_AA64MMFR1_EL1 should be a 64 bit value"
    (regval_to_val ID_AA64MMFR1_EL1 mmfr1);
  mret (bv_extract 36 4 val =? 3%bv).

(** Handle the start of an address translation.

    This is called when the architecture initiates a translation table walk.
    Computes all possible translation results by:
    1. Building TLB snapshots for the VA across all timestamps.
    2. Collecting valid translations (successful page table walks).
    3. Collecting invalid translations (faults due to invalid PTEs).

    Non-deterministically selects one translation result and records it
    in the intra-instruction state ([IIS.trs]) for use by subsequent
    translation reads. Also records the invalidation time if the translation
    may be affected by a future TLBI. *)
Definition run_trans_start (trans_start : TranslationStartInfo)
    (tid : nat) (init : memoryMap) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string unit :=
  ts ← mget PPState.state;
  mem ← mget PPState.mem;

  let is_ifetch :=
    trans_start.(TranslationStartInfo_accdesc).(AccessDescriptor_acctype) =?
    AccessType_IFETCH in
  is_ets2 ← mlift (ets2 ts);
  let vpre_t := ts.(TState.vcse) ⊔
                 (view_if (is_ets2 && (negb is_ifetch)) ts.(TState.vdsb)) in
  let vmax_t := length mem in
  (* lookup (successful results or faults) *)
  let asid := trans_start.(TranslationStartInfo_asid) in
  let va : bv 64 := trans_start.(TranslationStartInfo_va) in

  trans_res ←
    if decide (va_in_range va) then
      ttbr ← mlift $ ttbr_of_regime va trans_start.(TranslationStartInfo_regime);
      snapshots ← mlift $ TLB.unique_snapshots_va_until ts init mem vmax_t va ttbr;
      let snapshots := TLB.snapshots_from vpre_t snapshots in
      valid_entries ← mlift $
        TLB.get_valid_entries_from_snapshots snapshots mem tid va asid;
      invalid_entries ← mlift $
        TLB.get_invalid_entries_from_snapshots
          snapshots ts init mem tid is_ets2 va asid ttbr;
      (* update IIS with either a valid translation result or an invalid result *)
      valid_res ←
        for (val_ttbr, path, t, ti) in valid_entries do
          val_ttbr ← othrow
            "TTBR value type does not match with the value from the translation"
            (val_to_regval ttbr val_ttbr);
          let root := (Some (existT ttbr val_ttbr)) in
          let ti := if is_ifetch then None else ti in
          mret $ (IIS.TransRes.make (va_to_vpn va) t root path, ti)
        end;
      invalid_res ←
        for (val_ttbr, path, t, ti) in invalid_entries do
          val_ttbr ← othrow
            "TTBR value type does not match with the value from the translation"
            (val_to_regval ttbr val_ttbr);
          let root := (Some (existT ttbr val_ttbr)) in
          mret $ (IIS.TransRes.make (va_to_vpn va) t root path, ti)
        end;
      mchoosel (valid_res ++ invalid_res)
    else
      mret $ (IIS.TransRes.make (va_to_vpn va) vpre_t None [], None);
  mset PPState.iis $ IIS.set_trs trans_res.1;;
  mset PPState.iis $ IIS.set_inv_time trans_res.2;;
  mset PPState.iis $ IIS.set_access_va (Some va).

(** Compute the pre-view for a translation fault on a read access. *)
Definition read_fault_vpre (is_acq : bool)
  (trans_time : nat) : Exec.t (TState.t * IIS.t) string view :=
  ts ← mget fst;
  iis ← mget snd;
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
              ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
              ⊔ view_if is_acq ts.(TState.vrel) in
  mret $ iis.(IIS.strict) ⊔ vbob ⊔ trans_time ⊔ ts.(TState.vmsr).

(** Compute the pre-view for a translation fault on a write access. *)
Definition write_fault_vpre (is_rel : bool)
  (trans_time : nat) : Exec.t (TState.t * IIS.t) string view :=
  ts ← mget fst;
  iis ← mget snd;
  let vbob := ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
              ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
              ⊔ view_if is_rel (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  mret $ iis.(IIS.strict) ⊔ ts.(TState.vspec) ⊔ vbob ⊔ trans_time ⊔ ts.(TState.vmsr).

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
    let trans_time := trs.(IIS.TransRes.time) in
    let fault := trans_end.(AddressDescriptor_fault) in
    if decide (fault.(FaultRecord_statuscode) = Fault_None) then
      mset snd $ IIS.add trans_time;;
      msetv (IIS.trs ∘ snd) None
    else
      is_ets3 ← mlift (ets3 ts);
      if is_ets3 && (trans_time <? (ts.(TState.vrd) ⊔ ts.(TState.vwr)))
      then mdiscard
      else
        mset snd $ IIS.add trans_time;;
        (* if the fault is from read, add the read view *)
        let is_read := fault.(FaultRecord_access).(AccessDescriptor_read) in
        let is_acq := fault.(FaultRecord_access).(AccessDescriptor_acqsc) in
        read_view ← read_fault_vpre is_acq trans_time;

        mset snd $ IIS.add (view_if is_read read_view);;
        (* if the fault is from write, add the write view *)
        let is_write := fault.(FaultRecord_access).(AccessDescriptor_write) in
        let is_rel := fault.(FaultRecord_access).(AccessDescriptor_relsc) in
        write_view ← write_fault_vpre is_rel trans_time;
        mset snd $ IIS.add (view_if is_write write_view);;
        msetv (IIS.trs ∘ snd) None
  else
    mthrow "Translation ends with an empty translation".

(* TODO: check translation fault using `fault` and handle other cases *)
Definition run_take_exception (fault : exn) (vmax_t : view) :
    Exec.t (TState.t * IIS.t) string () :=
  iis ← mget snd;
  match iis.(IIS.inv_time) with
  | Some inv_time => run_cse inv_time
  | None => run_cse vmax_t
  end.

(** ** Top-level outcome semantics *)

(** Runs an outcome. *)
Section RunOutcome.
  Context (tid : nat) (initmem : memoryMap).

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
        opcode ← mlift $ read_imem addr initmem mem;
        mret (Ok (ctrans _ opcode, 0%bv), None)
      else if is_explicit macc then
        val ← read_mem_explicit addr size macc initmem;
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
      vpre_opt ← write_mem tid addr size macc val;
      mret (Ok (), vpre_opt)
  | MemWrite _ _ _ => mthrow "Memory write with tags unsupported"
  | Barrier barrier =>
      mem ← mget PPState.mem;
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_barrier barrier (length mem);;
      mret ((), None)
  | TlbOp tlbi =>
      viio ← mget (IIS.strict ∘ PPState.iis);
      vpre_opt ← run_tlbi tid viio tlbi;
      mret ((), vpre_opt)
  | ReturnException =>
      mem ← mget PPState.mem;
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_cse (length mem);;
      mret ((), None)
  | TranslationStart trans_start =>
      run_trans_start trans_start tid initmem;;
      mret ((), None)
  | TranslationEnd trans_end =>
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_trans_end trans_end;;
      mret ((), None)
  | GenericFail s => mthrow ("Instruction failure: " ++ s)%string
  | TakeException fault =>
      mem ← mget PPState.mem;
      Exec.liftSt (PPState.state ×× PPState.iis)
        $ run_take_exception fault (length mem);;
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


Section BBM.
  Context (initmem : memoryMap).

  (** Check if a physical address falls within the address range
      covered by a given output address prefix. *)
  Definition is_addr_from_oa {n : N} (addr : address) (oa : bv n) : Prop :=
    bv_extract (56 - n) n addr = oa.
  Instance Decision_is_addr_from_oa {n : N} (addr : address) (oa : bv n) :
    Decision (is_addr_from_oa addr oa).
  Proof. unfold_decide. Defined.

  (** Compare memory contents at two output addresses.
      Checks whether all 8-byte-aligned addresses that fall under either
      output address have the same memory contents. *)
  Definition mem_contents_eq (mem : Memory.t) (init : memoryMap)
                (time : nat)
                (lvl : Level)
                (oa1 oa2 : bv (output_addr_size lvl))
                (relevant_addrs : list address) : Prop :=
    let offset_bits := (56 - output_addr_size lvl)%N in
    let relevant_offs :=
      omap (λ addr,
        if decide (is_addr_from_oa addr oa1 ∨ is_addr_from_oa addr oa2)
          then Some (bv_extract 0 offset_bits addr)
          else None) relevant_addrs in
    ∀ offs ∈ relevant_offs,
      let addr1 := bv_concat 56 oa1 offs in
      let addr2 := bv_concat 56 oa2 offs in
      let byte1 := Memory.read_byte addr1 init mem time in
      let byte2 := Memory.read_byte addr2 init mem time in
      match byte1, byte2 with
      | Some byte1, Some byte2 => byte1 = byte2
      | Some byte1, None => byte1 = 0%bv
      | None, Some byte2 => 0%bv = byte2
      | None, None => True
      end.

  Instance Decision_mem_contents_eq mem init time lvl oa1 oa2
      relevant_addrs :
      Decision (mem_contents_eq mem init time lvl oa1 oa2 relevant_addrs).
  Proof. unfold mem_contents_eq. apply _. Defined.

  (** Check if two translation contexts have overlapping VA ranges. *)
  Definition va_ranges_overlap (c1 c2 : TLB.Ctxt.t) : bool :=
    if decide (TLB.Ctxt.upper c1 ≠ TLB.Ctxt.upper c2) then false
    else if decide (TLB.Ctxt.asid c1 ≠ TLB.Ctxt.asid c2
                    ∧ TLB.Ctxt.asid c1 ≠ None
                    ∧ TLB.Ctxt.asid c2 ≠ None) then false
    else
      let lvl1 := TLB.Ctxt.lvl c1 in
      let lvl2 := TLB.Ctxt.lvl c2 in
      let va1 := TLB.Ctxt.va c1 in
      let va2 := TLB.Ctxt.va c2 in
      if decide (lvl1 ≤ lvl2)%fin then
        let va2_trunc : prefix lvl1 := bv_extract 0 (level_length lvl1) va2 in
        va1 =? va2_trunc
      else
        let va1_trunc : prefix lvl2 := bv_extract 0 (level_length lvl2) va1 in
        va1_trunc =? va2.

  (** Check for BBM violation between two TLB entries. *)
  Definition is_bbm_violation (mem : Memory.t) (init : memoryMap)
                (time : nat)
                (relevant_addrs : list address)
                (fe1 fe2 : TLB.FE.t) : bool :=
    let c1 := TLB.FE.ctxt fe1 in
    let c2 := TLB.FE.ctxt fe2 in
    let lvl1 := TLB.FE.lvl fe1 in
    let lvl2 := TLB.FE.lvl fe2 in
    let pte1 := TLB.FE.pte fe1 in
    let pte2 := TLB.FE.pte fe2 in
    if decide (¬ is_final lvl1 pte1 ∨ ¬ is_final lvl2 pte2) then false
    else if negb (va_ranges_overlap c1 c2) then false
    else
      match decide (lvl1 = lvl2) with
      | left Heq =>
        let oa1 := output_addr lvl1 pte1 in
        let oa2 : bv (output_addr_size lvl1) :=
          ctrans (f_equal output_addr_size (eq_sym Heq)) (output_addr lvl2 pte2) in
        if negb (oa1 =? oa2) then
          if decide (allow_write lvl1 pte1 ∨ allow_write lvl2 pte2) then true
          else bool_decide
            (¬ (mem_contents_eq mem init time lvl1 oa1 oa2 relevant_addrs))
        else if negb (attr_idx pte1 =? attr_idx pte2) then true
        else if negb (shareability pte1 =? shareability pte2) then true
        else if xorb (is_contiguous pte1) (is_contiguous pte2) then true
        else if xorb (is_non_global pte1) (is_non_global pte2) then true
        else false
      | right _ => true
      end.

  (** Check for BBM violations within a single TLB snapshot. *)
  Definition has_bbm_violation (mem : Memory.t)
                (init : memoryMap)
                (tlb : TLB.t)
                (time : nat) : Prop :=
    let relevant_addrs := elements (dom init) in
    let finals := TLB.VATLB.final_entries (TLB.vatlb tlb) in
    ∃ '(fe1, fe2) ∈ list_prod finals finals,
      fe1 ≠ fe2 ∧
      is_bbm_violation mem init time relevant_addrs fe1 fe2 = true.

  Instance Decision_has_bbm_violation mem init tlb time :
      Decision (has_bbm_violation mem init tlb time).
  Proof. unfold has_bbm_violation. apply _. Defined.

  (** Find the TLB snapshot that was active at a given time. *)
  Definition find_latest_snapshot_before (snapshots : list (TLB.t * nat))
      (target : nat) : option (TLB.t * nat) :=
    List.find (λ '(_, t), (t <=? target)%nat) snapshots.

  (** Main BBM violation check. Returns [Ok true] if violation detected. *)
  Definition check_bbm_violation (ts : TState.t)
        (mem : Memory.t) (mem_strict : bool) : result string bool :=
    mmu_enabled ← is_mmu_enabled ts;
    if (mmu_enabled : bool) then
      let max_t := length mem in
      let ttbrs_to_check :=
        filter (λ ttbr, is_Some (dmap_lookup ttbr ts.(TState.regs))) ttbrs in
      let tlbi_times := filter (λ i,
        if mem !! i is Some (Ev.Tlbi _) then true else false
      ) (seq 1 max_t) in
      let times_to_check := max_t :: (map (λ t, t - 1) tlbi_times) in
      foldlM (λ violated ttbr,
        if (violated : bool) then mret true
        else
          snapshots ← TLB.unique_snapshots_until ts initmem mem max_t ttbr mem_strict;
          mret $
            bool_decide
              (∃ target_time ∈ times_to_check,
                match find_latest_snapshot_before snapshots target_time with
                | Some (tlb, _) => has_bbm_violation mem initmem tlb target_time
                | None => False
                end)
      ) false (elements ttbrs_to_check)
    else
      mret false.
End BBM.

Module BBM.
  (** The BBM parameter telling how strict the BBM checker must be *)
  Inductive param :=
  | Off
  | Lax
  | Strict.

  (** Wrapper for check_valid_end that returns list of error strings. *)
  Definition check (p : param) (tid : nat) (initmem : memoryMap) (ts : TState.t)
      (mem : Memory.t) : list string :=
    let aux_check strict :=
      match check_bbm_violation initmem ts mem strict with
      | Ok true => ["BBM violation detected"]
      | Ok false => []
      | Error s => [("BBM checker: " ++ s)%string]
      end
    in
    match p with
    | Off => []
    | Lax => aux_check false
    | Strict => aux_check true
    end.
End BBM.

(** * Implement GenPromising ***)

Import Promising.

Definition emit_promise' (tid : nat) (initmem : memoryMap) (mem : Memory.t) ev :=
  if ev is Ev.Msg _ then TState.promise_write (length mem)
  else TState.promise_tlbi (length mem).

Definition VMPromising (bbm_param : BBM.param) : Promising.Model :=
  {|tState := TState.t;
    tState_init := λ tid, TState.init;
    tState_regs := TState.reg_map;
    tState_nopromises := (λ ts, is_emptyb (TState.prom_wr ts ++ TState.prom_tlbi ts));
    iis := IIS.t;
    iis_init := IIS.init;
    address_space := PAS_NonSecure;
    mEvent := Ev.t;
    mEvent_tid := Ev.tid;
    handle_outcome := run_outcome;
    emit_promise := emit_promise';
    check_valid_end := λ tid initmem ts mem, BBM.check bbm_param tid initmem ts mem;
    memory_snapshot := Memory.to_memMap;
  |}.

Definition VMPromising_nocert (bbm_param : BBM.param) :=
  Promising_to_Modelnc (*certified=*)false (VMPromising bbm_param).

Definition VMPromising_cert (bbm_param : BBM.param) :=
  Promising_to_Modelnc (*certified=*)true (VMPromising bbm_param).

Definition VMPromising_exe (bbm_param : BBM.param) :=
  Promising_to_Modelc (VMPromising bbm_param).

Definition VMPromising_pf (bbm_param : BBM.param) :=
  Promising_to_Modelc_pf (VMPromising bbm_param).
