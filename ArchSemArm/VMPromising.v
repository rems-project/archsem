(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  All files except SailArmInstTypes.v are distributed under the             *)
(*  license below (BSD-2-Clause). The former is distributed                   *)
(*  under a mix of BSD-2-Clause and BSD-3-Clause Clear, as described          *)
(*  in the file header.                                                       *)
(*                                                                            *)
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

#[local] Open Scope list.
#[local] Open Scope nat.
#[local] Open Scope stdpp.

(** The goal of this module is to define an Virtual memory promising model,
    without mixed-size on top of the new interface *)

(** This model only works for 8-bytes aligned locations, as there
    in no support for mixed-sizes yet. Also all location are
    implicitly in the non-secure world.

    So in order to get the physical address you need to append 3 zeros.

    We reuse the location setup from the User-Mode promising model. *)
Module Loc := UMPromising.Loc.

(** Register and memory values (all memory access are 8 bytes aligned *)
Definition val := bv 64.
#[global] Typeclasses Transparent val.

Definition val_to_address (v : val) : address :=
  bv_extract 0 56 v.

(** We also reuse the Msg object from the User-Mode Promising Model. *)
Module Msg := UMPromising.Msg.

Module TLBI.
  Inductive t :=
  | All (tid : nat)
  | Asid (tid : nat) (asid : bv 16)
  | Va (tid : nat) (asid : bv 16) (va : bv 36) (last : bool)
  | Vaa (tid : nat) (va : bv 36) (last : bool).

  #[global] Instance dec : EqDecision t.
  solve_decision.
  Defined.

  Definition tid (tlbi : t) : nat :=
    match tlbi with
    | All tid => tid
    | Asid tid _ => tid
    | Va tid _ _ _ => tid
    | Vaa tid _ _ => tid
    end.

  Definition asid_opt (tlbi : t) : option (bv 16) :=
    match tlbi with
    | All _ => None
    | Asid _ asid => Some asid
    | Va _ asid _ _ => Some asid
    | Vaa _ _ _ => None
    end.

  Definition asid (tlbi : t) : bv 16 :=
    default (Z_to_bv 16 0) (asid_opt tlbi).

  Definition va_opt (tlbi : t) : option (bv 36) :=
    match tlbi with
    | All _ => None
    | Asid _ _ => None
    | Va _ _ va _ => Some va
    | Vaa _ va _ => Some va
    end.

  Definition va (tlbi : t) : bv 36 :=
    default (Z_to_bv 36 0) (va_opt tlbi).

  Definition last_opt (tlbi : t) : option bool :=
    match tlbi with
    | All _ => None
    | Asid _ _ => None
    | Va _ _ _ last => Some last
    | Vaa _ _ last => Some last
    end.

  Definition last (tlbi : t) : bool :=
    default false (last_opt tlbi).
End TLBI.

(** Promising events appearing in the trace *)
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

  Definition is_write_to (loc : Loc.t) (ev : t) :=
    match ev with
    | Msg msg => Msg.loc msg =? loc
    | Tlbi _ => false
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
End Ev.
Coercion Ev.Msg : Msg.t >-> Ev.t.
Coercion Ev.Tlbi : TLBI.t >-> Ev.t.

(** A view is just a natural *)
Definition view := nat.
#[export] Typeclasses Transparent view.
Bind Scope nat_scope with view.
Global Hint Transparent view : core.
Global Hint Unfold view : core.

Module Memory.
  Import PromMemory.

  (** Representation of initial memory, this is representation
      optimized for the internals of this model, so it not a plain
      memoryMap *)
  Definition initial := gmap Loc.t val.
  #[export] Typeclasses Transparent initial.

  (** Convert from a memoryMap to the internal representation: initial *)
  Definition initial_from_memMap (mem : memoryMap) : initial :=
    mem
    |> dom
    |> (set_map (bv_extract 3 53) : _ → gset Loc.t)
    |> set_fold (λ loc map,
        let base := Loc.to_addr loc in
        let lo :=
          for addr in addr_range base 4 do mem !! addr end
          |$> bv_of_bytes 32
        in
        let hi :=
          for addr in addr_range (addr_addN base 4) 4 do mem !! addr end
          |$> bv_of_bytes 32
        in
        let val :=
          match lo, hi with
          | Some lo, Some hi => Some (bv_concat 64 hi lo)
          | Some lo, None => Some (bv_concat 64 (bv_0 32) lo)
          | None, Some hi => Some (bv_concat 64 hi (bv_0 32))
          | None, None => None
          end
        in
        partial_alter (λ _, val) loc map) ∅.


  (** The promising memory: a list of events *)
  Definition t : Type := t Ev.t.
  #[export] Typeclasses Transparent t.

  Definition cut_after : nat -> t -> t := @cut_after Ev.t.
  Definition cut_before : nat -> t -> t := @cut_before Ev.t.

 (** Reads the last write to a location in some memory. Gives the value and the
     timestamp of the write that it read from.
     The timestamp is 0 if reading from initial memory. *)
  Fixpoint read_last (loc : Loc.t) (init : initial) (mem : t) : option (val * nat) :=
    match mem with
    | [] => init !! loc |$> (., 0%nat)
    | (Ev.Msg msg) :: mem' =>
        if Msg.loc msg =? loc then
          Some (Msg.val msg, List.length mem)
        else read_last loc init mem'
    | Ev.Tlbi _ :: mem' => read_last loc init mem'
    end.

  (** Read memory at a given timestamp without any weak memory behaviour *)
  Definition read_at (loc : Loc.t) (init : initial) (mem : t) (time : nat) :=
    read_last loc init (cut_before time mem).

  (** Reads from initial memory and fail if the memory has been overwritten.

      This is mainly for instruction fetching in this model *)
  Definition read_initial (loc : Loc.t) (init : initial) (mem : t) : option val :=
    match read_last loc init mem with
    | Some (v, 0%nat) => Some v
    | _ => None
    end.


  (* (** Reads from initial memory for instruction fetch (only 4 bytes aligned) *)
  (*     and fail if the memory was modified *)
  (*  *) *)
  (* Definition read_ifetch (addr : bv 50) (init : initial) (mem : t) *)
  (*   : option val := *)
  (*   if existsb (fun ev => *)
  (*                 match ev with *)
  (*                 | Ev.Msg msg => Msg.lov msg =? (bv_extract 1 49 addr) *)
  (*                 | _ => false) mem *)
  (*   then None *)
  (*   else Some ( *)
  (*   match read_last loc init mem with *)
  (*   | (v, 0%nat) => Some v *)
  (*   | _ => None *)
  (*   end. *)


  (** Transform a promising initial memory and memory history back to a
      TermModel memoryMap *)
  Definition to_memMap (init : initial) (mem : t) : memoryMap:=
    let final :=
      foldl (λ nmem ev,
          if ev is Ev.Msg msg
          then insert msg.(Msg.loc) msg.(Msg.val) nmem
          else nmem)
        init mem
    in
    map_fold (λ loc (val : bv 64), mem_insert (Loc.to_addr loc) 8 val) ∅ final.

  (** Returns the list of possible reads at a location restricted by a certain
      view. The list is never empty as one can always read from at least the
      initial value. *)
  Definition read (loc : Loc.t) (v : view) (init : initial) (mem : t)
    : option (list (val * view)) :=
    first ← mem |> cut_before v |> read_last loc init;
    let lasts :=
      mem |> cut_after_with_timestamps v
      |> omap
           (λ '(ev, v),
             match ev with
             | Ev.Msg msg =>
                 if Msg.loc msg =? loc
                 then Some (Msg.val msg, v)
                 else None
             | Ev.Tlbi _ => None
             end)
    in
    Some (lasts ++ [first])%list.


  (** Promise a write and add it at the end of memory *)
  Definition promise (ev : Ev.t) : Exec.t t string view :=
    mSet (cons ev);;
    mem ← mGet;
    mret (List.length mem).

  (** Returns a view among a promise set that correspond to an event. The
      oldest matching view is taken. This is because it can be proven that
      taking a more recent view, will make the previous promises unfulfillable
      and thus the corresponding executions would be discarded. TODO prove it.
      *)
  Definition fulfill (ev : Ev.t) (prom : list view) (mem : t) : option view :=
    prom |> filter (λ t, mem !! t = Some ev)
         |> reverse
         |> head.

  (** Check that the write at the provided timestamp is indeed to that location
      and that no write to that location have been made by any other thread *)
  Definition exclusive (loc : Loc.t) (v : view) (mem : t) : bool :=
    match mem !! v with
    | Some (Ev.Msg msg) =>
        if Msg.loc msg =? loc then
          let tid := Msg.tid msg in
          mem |> cut_after v
              |> forallb
              (fun ev => match ev with
                      | Ev.Msg msg =>
                          (Msg.tid msg =? tid)
                          || negb (Msg.loc msg =? loc)
                      | _ => true
                      end)
        else false
    | _ => false
    end.
End Memory.
Import (hints) Memory.

Module FwdItem := UMPromising.FwdItem.


Definition EL := (fin 4).
#[export] Typeclasses Transparent EL.
Bind Scope fin_scope with EL.
Definition ELp := (fin 3).
#[export] Typeclasses Transparent ELp.
Bind Scope fin_scope with ELp.

Definition ELp_to_EL : ELp -> EL := FS.


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
       SP_EL0;
       SP_EL1;
       SP_EL2;
       SP_EL3;
       PSTATE;
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
       PAR_EL1]@{reg}.

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

(** Determine if input register is an unknown register from the architecture *)
Definition is_reg_unknown (r : reg) : Prop :=
  ¬(r ∈ relaxed_regs ∨ r ∈ strict_regs ∨ r = pc_reg).
Instance Decision_is_reg_unknown (r : reg) : Decision (is_reg_unknown r).
Proof. unfold_decide. Defined.

Equations regval_to_val (r : reg) (v : reg_type r) : option val :=
  | R_bitvector_64 _, v => Some v
  | _, v => None.

Equations val_to_regval (r : reg) (v : val) : option (reg_type r) :=
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
        prom : list view;

        (* registers values and views. System(relaxed) registers are not
           modified in the [regs] field directly, but instead accumulate changes *)
        regs : dmap reg (λ reg, reg_type reg * view)%type;
        levs : list LEv.t;

        (* The coherence views *)
        coh : gmap Loc.t view;

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

        (* Forwarding database. The first view is the timestamp of the
           write while the second view is the max view of the dependencies
           of the write. The boolean marks if the store was an exclusive*)
        fwdb : gmap Loc.t FwdItem.t;

        (* Exclusive database. If there was a recent load exclusive but the
           corresponding store exclusive has not yet run, this will contain
           the timestamp and post-view of the load exclusive*)
        xclb : option (nat * view);
      }.

  #[global] Instance eta : Settable _ :=
    settable! make <prom;regs;levs;coh;vrd;vwr;vdmbst;vdmb;vdsb;
                    vspec;vcse;vtlbi;vmsr;vacq;vrel;fwdb;xclb>.

  (* TODO Check and remove mem as an argument here *)
  Definition init (mem : memoryMap) (iregs : registerMap) :=
    ({|
      prom := [];
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

  (** Sets the coherence view of a location *)
  Definition set_coh (loc : Loc.t) (v : view) : t → t :=
    set coh (insert loc v).

  (** Updates the coherence view of a location by taking the max of the new
      view and of the existing value *)
  Definition update_coh (loc : Loc.t) (v : view) (ts : t) : t :=
    set_coh loc (max v (ts.(coh) !!! loc)) ts.

  (** Updates the forwarding database for a location. *)
  Definition set_fwdb (loc : Loc.t) (fi : FwdItem.t) : t → t :=
    set fwdb (insert loc fi).

  (** Set the exclusive database to the timestamp and view of the latest
      load exclusive *)
  Definition set_xclb (vs : view * view) : t → t :=
    set xclb (λ _, Some vs).

  (** Clear the exclusive database, to mark a store exclusive *)
  Definition clear_xclb : t → t :=
    set xclb (λ _, None).

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

  (** Add a promise to the promise set *)
  Definition promise (v : view) : t -> t := set prom (v ::.).

  (** Perform a context synchronization event *)
  Definition cse (v : view) : t -> t :=
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

Definition prefix_to_va {n : N} (p : bv n) : bv 64 :=
  bv_concat 64 (bv_0 16) (bv_concat 48 p (bv_0 (48 - n))).

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

Definition next_entry_loc (loc : Loc.t) (index : bv 9) : Loc.t :=
  bv_concat 53 (bv_extract 9 44 loc) index.

Definition is_valid (e : val) : Prop :=
  (bv_extract 0 1 e) = 1%bv.
Instance Decision_is_valid (e : val) : Decision (is_valid e).
Proof. unfold_decide. Defined.

Definition is_table (e : val) : Prop :=
  (bv_extract 0 2 e) = 3%bv.
Instance Decision_is_table (e : val) : Decision (is_table e).
Proof. unfold_decide. Defined.

Definition is_block (e : val) : Prop :=
  (bv_extract 0 2 e) = 1%bv.
Instance Decision_is_block (e : val) : Decision (is_block e).
Proof. unfold_decide. Defined.

Definition is_final (lvl : Level) (e : val) : Prop :=
  if lvl is 3%fin then (bv_extract 0 2 e) = 3%bv else is_block e.
Instance Decision_is_final (lvl : Level) (e : val) : Decision (is_final lvl e).
Proof. unfold_decide. Defined.

Definition is_global (lvl : Level) (e : val) : Prop :=
  is_final lvl e ∧ (bv_extract 11 1 e) = 0%bv.
Instance Decision_is_global (lvl : Level) (e : val) : Decision (is_global lvl e).
Proof. unfold_decide. Defined.

(** * TLB ***)

Module TLB.
  (** ** TLB types definitions *)
  Module NDCtxt.
    Record t (lvl : Level) :=
      make {
          va : prefix lvl;
          asid : option (bv 16);
        }.
    Arguments make {_} _ _.
    Arguments va {_}.
    Arguments asid {_}.

    #[global] Instance eq_dec lvl : EqDecision (t lvl).
    Proof. solve_decision. Defined.

    #[global] Instance eqdep_dec : EqDepDecision t.
    Proof. intros ? ? ? [] []. decide_jmeq. Defined.

    #[global] Instance count lvl : Countable (t lvl).
    Proof.
      eapply (inj_countable' (fun ndc => (va ndc, asid ndc))
                        (fun x => make x.1 x.2)).
      abstract sauto.
    Defined.
  End NDCtxt.

  Module Ctxt.
    Definition t := {lvl : Level & NDCtxt.t lvl}.
    Definition lvl : t -> Level := projT1.
    Definition nd (ctxt : t) : NDCtxt.t (lvl ctxt) := projT2 ctxt.
    Definition va (ctxt : t) : prefix (lvl ctxt) := NDCtxt.va (nd ctxt).
    Definition asid (ctxt : t) : option (bv 16) := NDCtxt.asid (nd ctxt).
  End Ctxt.
  #[export] Typeclasses Transparent Ctxt.t.

  Module Entry.
    Definition t (lvl : Level) := vec val (S lvl).
    Definition pte {lvl} (tlbe : t lvl) := Vector.last tlbe.

    Program Definition append {lvl clvl : Level}
        (tlbe : t lvl)
        (pte : val)
        (CHILD : lvl + 1 = clvl) : t clvl :=
      ctrans _ (tlbe +++ [#pte]).
    Solve All Obligations with lia.
  End Entry.
  #[export] Typeclasses Transparent Entry.t.

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
      hset (Ctxt.lvl ctxt) {[(Ctxt.nd ctxt) := entries]} vatlb.

    #[global] Instance empty : Empty t := VATLB.init.
    #[global] Instance union : Union t := fun x y => hmap2 (fun _ => (∪ₘ)) x y.
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
      (ttbr : reg) (time : nat) : Prop :=
    match asid with
    | Some asid =>
      if TState.read_sreg_at ts ttbr time is Some sregs
        then ∃ '(regval, view) ∈ sregs,
              if (regval_to_val ttbr regval) is Some v
                then asid = (bv_extract 48 16 v)
                else False
        else False
    | None => True
    end.
  Instance Decision_is_active_asid (ts : TState.t)
      (asid : option (bv 16))
      (ttbr : reg) (time : nat) : Decision (is_active_asid ts asid ttbr time).
  Proof. unfold_decide. Defined.

  Definition next_va {clvl : Level}
    (ctxt : Ctxt.t)
    (index : bv 9)
    (CHILD : (Ctxt.lvl ctxt) + 1 = clvl) : prefix clvl :=
    bv_concat (level_length clvl) (Ctxt.va ctxt) index.


  (** Seed root-level TLB entries from [ttbr].
      - Reads [ttbr] at [time], checks it is 64-bit.
      - Computes root entry address for [va], reads memory.
      - If entry is a table, builds a root context with ASID from TTBR
        and inserts it into VATLB.
      - Otherwise returns empty VATLB. *)
  Definition va_fill_root (ts : TState.t)
      (init : Memory.initial)
      (mem : Memory.t)
      (time : nat)
      (va : prefix root_lvl)
      (ttbr : reg) : result string VATLB.t :=
    sregs ← othrow "TTBR should exist in initial state"
              $ TState.read_sreg_at ts ttbr time;
    vatlbs ←
      for sreg in sregs do
        val_ttbr ← othrow "TTBR should be a 64 bit value"
                    $ regval_to_val ttbr sreg.1;
        let entry_addr := next_entry_addr val_ttbr va in
        let loc := Loc.from_addr_in entry_addr in
        if (Memory.read_at loc init mem time) is Some (memval, _) then
          if decide (is_table memval) then
            let asid := bv_extract 48 16 val_ttbr in
            let ndctxt := NDCtxt.make va (Some asid) in
            Ok $ VATLB.singleton (existT root_lvl ndctxt) [#memval]
          else
            Ok VATLB.init
        else
          Ok VATLB.init
      end;
    Ok (union_list vatlbs).

  (** Extend one level down from a parent table entry [te].
      - Requires [te] ∈ [vatlb] and ASID active for [ttbr].
      - Reads next-level PTE at [index]; if valid and table, build child context
        (ASID dropped if global) and insert into VATLB.
      - Otherwise returns empty. *)
  Definition va_fill_lvl (vatlb : VATLB.t) (ts : TState.t)
      (init : Memory.initial)
      (mem : Memory.t)
      (time : nat)
      (ctxt : Ctxt.t)
      (te : Entry.t (Ctxt.lvl ctxt))
      (index : bv 9)
      (ttbr : reg) : result string VATLB.t :=
    guard_or "ASID is not active"
      $ is_active_asid ts (Ctxt.asid ctxt) ttbr time;;
    guard_or "The translation entry is not in the TLB"
      (te ∈ VATLB.get ctxt vatlb);;

    if decide (¬is_table (Entry.pte te)) then Ok VATLB.init
    else
      let entry_addr := next_entry_addr (Entry.pte te) index in
      let loc := Loc.from_addr_in entry_addr in
      '(next_pte, _) ← othrow "The location of the next level address should be read"
                        $ Memory.read_at loc init mem time;
      if decide (is_valid next_pte) then
        match inspect $ child_lvl (Ctxt.lvl ctxt) with
        | Some clvl eq:e =>
          let va := next_va ctxt index (child_lvl_add_one _ _ e) in
          let asid := if bool_decide (is_global clvl next_pte) then None
                      else Ctxt.asid ctxt in
          let ndctxt := NDCtxt.make va asid in
          let new_te := Entry.append te next_pte (child_lvl_add_one _ _ e) in
          Ok $ VATLB.singleton (existT clvl ndctxt) new_te
        | None eq:_ => mthrow "An intermediate level should have a child level"
        end
      else
        Ok VATLB.init.

  (** Make [tlb] containing entries for [va] at [lvl].
      - At root: call [va_fill_root].
      - At deeper levels: for each parent entry, call [va_fill_lvl].
      - Returns [(tlb, is_changed)]. [is_changed] is true when there are new VATLB entries. *)
  Definition va_fill (tlb : t) (ts : TState.t)
      (init : Memory.initial)
      (mem : Memory.t)
      (time : nat)
      (lvl : Level)
      (va : bv 64)
      (ttbr : reg) : result string (t * bool) :=
    vatlb_new ←
      match parent_lvl lvl with
      | None =>
        va_fill_root ts init mem time (level_index va root_lvl) ttbr
      | Some plvl =>
        let pva := level_prefix va plvl in
        let index := level_index va lvl in
        sregs ← othrow "TTBR should exist in initial state"
                $ TState.read_sreg_at ts ttbr time;
        active_vatlbs ←
          for sreg in sregs do
            val_ttbr ← othrow "TTBR should be a 64 bit value"
                    $ regval_to_val ttbr sreg.1;
            let asid := bv_extract 48 16 val_ttbr in
            let ndctxt := NDCtxt.make pva (Some asid) in
            let ctxt := existT plvl ndctxt in
            vatlbs ←
              for te in elements (VATLB.get ctxt tlb.(vatlb)) do
                va_fill_lvl tlb.(vatlb) ts init mem time ctxt te index ttbr
              end;
            Ok (union_list vatlbs)
          end;
        Ok $ (union_list active_vatlbs)
      end;
    mret $ (TLB.make (vatlb_new ∪ tlb.(vatlb)), negb(vatlb_new =? ∅)).

  (** Fill TLB entries for [va] through all levels 0–3.
      - Sequentially calls [va_fill] at each level.
      - Produces a TLB with the full translation chain if available. *)
  Definition update (tlb : t)
      (ts : TState.t)
      (init : Memory.initial)
      (mem : Memory.t)
      (time : nat)
      (va : bv 64)
      (ttbr : reg) : result string (t * bool) :=
    (* make an incremental update *)
    fold_left (λ prev lvl,
      '(tlb_prev, is_changed_prev) ← prev;
      '(tlb_new, is_changed) ← va_fill tlb_prev ts init mem time lvl va ttbr;
      mret (tlb_new, is_changed || is_changed_prev)
    ) (enum Level) (mret (tlb, false)).

  (** ** TLB invalidation *)

  (** Decide if a TLB entry is affected by an invalidation by asid at this asid *)
  Definition affects_asid (asid : bv 16)
                          (ctxt : Ctxt.t)
                          (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
    match (Ctxt.asid ctxt) with
    | Some te_asid => te_asid = asid
    | None => False
    end.
  Instance Decision_affects_asid (asid : bv 16)
                                 (ctxt : Ctxt.t)
                                 (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (affects_asid asid ctxt te).
  Proof. unfold_decide. Defined.

  (** Decide if a TLB entry is affected by an invalidation by va at this asid *)
  Definition affects_va (va : bv 36) (last : bool)
                         (ctxt : Ctxt.t)
                         (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
    let '(te_lvl, te_va, te_val) :=
          (Ctxt.lvl ctxt, Ctxt.va ctxt, Entry.pte te) in
    (match_prefix_at te_lvl te_va va)
    ∧ (if last then is_final te_lvl te_val else True).
  Instance Decision_affects_va (va : bv 36) (last : bool)
                                (ctxt : Ctxt.t)
                                (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (affects_va va last ctxt te).
  Proof. unfold_decide. Defined.

  (** Decide a TLBI instruction affects a given TLB entry *)
  Definition affects (tlbi : TLBI.t) (ctxt : Ctxt.t)
                     (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
    match tlbi with
    | TLBI.All tid => True
    | TLBI.Va tid asid va last =>
      affects_asid asid ctxt te ∧ affects_va va last ctxt te
    | TLBI.Asid tid asid => affects_asid asid ctxt te
    | TLBI.Vaa tid va last => affects_va va last ctxt te
    end.
  Instance Decision_affects (tlbi : TLBI.t) (ctxt : Ctxt.t)
                     (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (affects tlbi ctxt te).
  Proof. unfold_decide. Defined.

  Definition tlbi_apply (tlbi : TLBI.t) (tlb : t) : t :=
    set vatlb (filter (λ '(existT ctxt te), ¬ affects tlbi ctxt te)) tlb.

  (** Get the TLB states up until the timestamp along with
      a boolean value that shows if it is different from the previous tlb and
      the timestamp used to compute that state. [list (TLB.t * bool * nat)] *)
  Fixpoint snapshots_until_timestamp (ts : TState.t) (mem_init : Memory.initial)
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
            (* always true if tlbi is applied *)
            let tlb_inv :=
              if ev is Ev.Tlbi tlbi then tlbi_apply tlbi tlb_prev else tlb_prev
            in
            update tlb_inv ts mem_init mem time_cur va ttbr
        | None => mret (init, false)
        end;
      let acc :=
        match is_changed with
        | true => (tlb, time_cur) :: acc
        | false => acc
        end in
      snapshots_until_timestamp
        ts mem_init mem tlb time_cur ccnt va ttbr acc
    end.

  (** Get the unique TLB states up until the timestamp along with the timestamp
      used to compute that state. [list (TLB.t * nat)] *)
  Definition unique_snapshots_until_timestamp (ts : TState.t)
                       (mem_init : Memory.initial)
                       (mem : Memory.t)
                       (time : nat)
                       (va : bv 64)
                       (ttbr : reg) : result string (list (t * nat)) :=
    '(tlb, _) ← update init ts mem_init mem 0 va ttbr;
    snapshots_until_timestamp ts mem_init mem tlb 0 time va ttbr [(tlb, 0)].

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

  Fixpoint invalidation_time_from_evs (tid : nat)
              (ctxt : Ctxt.t)
              (te : Entry.t (Ctxt.lvl ctxt))
              (evs : list (Ev.t * nat)) : result string (option nat) :=
    match evs with
    | nil => mret None
    | (ev, t) :: tl =>
      match ev with
      | Ev.Tlbi tlbi =>
        let va := prefix_to_va (Ctxt.va ctxt) in
        if decide (is_te_invalidated_by_tlbi tlbi tid ctxt te) then
          mret (Some t)
        else
          invalidation_time_from_evs tid ctxt te tl
      | _ => invalidation_time_from_evs tid ctxt te tl
      end
    end.

  (** Calculate the earliest future time at which a translation entry is
      effectively invalidated in the TLB due to a TLBI event *)
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
            result string (list (list val * (option nat))) :=
    let ctxt := existT lvl ndctxt in
    let tes := VATLB.get ctxt tlb.(TLB.vatlb) in
    let tes := if decide (lvl = leaf_lvl) then tes
               else filter (λ te, is_block (TLB.Entry.pte te)) tes in
    for te in (elements tes) do
      ti ← invalidation_time mem tid trans_time ctxt te;
      mret ((vec_to_list te), ti)
    end.

  (** Get all the TLB entries that could translate the given VA
      at the provided level and in the provided ASID context.
      Return each TLB entry as a list of descriptors [list val] with
      the invalidation time [nat] *)
  Definition get_leaf_ptes_with_inv_time (mem : Memory.t)
              (tid : nat)
              (tlb : t) (trans_time : nat)
              (lvl : Level)
              (va : bv 64) (asid : bv 16) :
            result string (list (list val * (option nat))) :=
    let ndctxt_asid := NDCtxt.make (level_prefix va lvl) (Some asid) in
    let ndctxt_global := NDCtxt.make (level_prefix va lvl) None in
    candidates_asid ←
      get_leaf_ptes_with_inv_time_by_ctxt mem tid tlb trans_time lvl ndctxt_asid;
    candidates_global ←
      get_leaf_ptes_with_inv_time_by_ctxt mem tid tlb trans_time lvl ndctxt_global;
    mret (candidates_asid ++ candidates_global)%list.

  (** Get all the TLB entries that could translate the given VA
      in the provided ASID context.
      Return each TLB entry as a list of descriptors [list val] with
      the invalidation time [nat] *)
  Definition lookup (mem : Memory.t)
              (tid : nat)
              (tlb : TLB.t) (trans_time : nat)
              (va : bv 64) (asid : bv 16) :
            result string (list (list val * (option nat))) :=
    res1 ← get_leaf_ptes_with_inv_time mem tid tlb trans_time 1%fin va asid;
    res2 ← get_leaf_ptes_with_inv_time mem tid tlb trans_time 2%fin va asid;
    res3 ← get_leaf_ptes_with_inv_time mem tid tlb trans_time leaf_lvl va asid;
    mret (res1 ++ res2 ++ res3).

  (** Get all the TLB entries that trigger fault from the given VA
      at the provided level and in the provided ASID context.
      Return each TLB entry as a list of descriptors [list val] with
      the invalidation time [option nat] *)
  Definition get_invalid_ptes_with_inv_time_by_lvl_asid (ts : TState.t)
                (init : Memory.initial)
                (mem : Memory.t)
                (tid : nat)
                (tlb : t) (trans_time : nat)
                (lvl : Level)
                (va : bv 64)
                (asid : option (bv 16))
                (ttbr : reg) : result string (list (list val * (option nat))) :=
    if parent_lvl lvl is Some parent_lvl then
      let ndctxt := NDCtxt.make (level_prefix va parent_lvl) asid in
      let ctxt := existT parent_lvl ndctxt in
      let tes := VATLB.get ctxt tlb.(TLB.vatlb) in
      let tes := filter (λ te, is_table (TLB.Entry.pte te)) tes in
      invalid_ptes ←
        for te in (elements tes) do
          let entry_addr :=
            next_entry_addr (Entry.pte te) (level_index va lvl) in
          let loc := Loc.from_addr_in entry_addr in
          if (Memory.read_at loc init mem trans_time) is Some (memval, _) then
            if decide (is_valid memval) then mret None
            else
              ti ← invalidation_time mem tid trans_time ctxt te;
              mret $ Some ((vec_to_list te) ++ [memval], ti)
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
              next_entry_addr (val_to_address val_ttbr) (level_index va lvl) in
          let loc := Loc.from_addr_in entry_addr in
          if (Memory.read_at loc init mem trans_time) is Some (memval, _) then
            if decide (is_valid memval) then mret None
            else
              mret $ Some ([memval], None)
          else mthrow "The root PTE is missing"
        end;
      mret $ omap id invalid_ptes.

  (** Get all the TLB entries that trigger fault from the given VA
      in the provided ASID context.
      Return each TLB entry as a list of descriptors [list val] with
      the invalidation time [option nat] *)
  Definition get_invalid_ptes_with_inv_time_by_lvl (ts : TState.t) (init : Memory.initial)
                (mem : Memory.t)
                (tid : nat)
                (tlb : t) (trans_time : nat)
                (lvl : Level)
                (va : bv 64) (asid : bv 16)
                (ttbr : reg) : result string (list (list val * (option nat))) :=
    candidates_asid ←
      get_invalid_ptes_with_inv_time_by_lvl_asid ts init mem tid tlb trans_time lvl va (Some asid) ttbr;
    candidates_global ←
      get_invalid_ptes_with_inv_time_by_lvl_asid ts init mem tid tlb trans_time lvl va None ttbr;
    mret (candidates_asid ++ candidates_global).

  Definition get_invalid_ptes_with_inv_time (ts : TState.t) (init : Memory.initial)
                       (mem : Memory.t)
                       (tid : nat)
                       (tlb : TLB.t) (time : nat)
                       (va : bv 64) (asid : bv 16)
                       (ttbr : reg) :
    result string (list (list val * (option nat))) :=
  fault_ptes ←
    for lvl in enum Level do
      get_invalid_ptes_with_inv_time_by_lvl ts init mem tid tlb time lvl va asid ttbr
    end;
  mret $ List.concat fault_ptes.
End TLB.
Export (hints) TLB.

Module VATLB := TLB.VATLB.

(** * Instruction semantics ***)

(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  (* Translation Results *)
  Module TransRes.
    Record t :=
      make {
          va : bv 36;
          time : nat;
          remaining : list (bv 64); (* NOTE: translation memory read - ptes *)
          invalidation : option nat
        }.

    Definition pop : Exec.t t string (bv 64) :=
      remain ← mget remaining;
      if remain is h :: tl then
        msetv remaining tl;;
        mret h
      else mthrow "Couldn't pop the next PTE: error in translation assumptions".
  End TransRes.

  Record t :=
    make {
        strict : view;
        (* The translations results of the latest translation *)
        trs : option TransRes.t
      }.

  Definition init : t := make 0 None.

  (** Add a new view to the IIS *)
  Definition add (v : view) (iis : t) : t :=
    iis |> set strict (max v).

  Definition set_trs (tres : TransRes.t) :=
    setv trs (Some tres).

End IIS.

Import UMPromising(view_if, read_fwd_view).

(** Performs a memory read at a location with a view and return possible output
    states with the timestamp and value of the read *)
Definition read_mem_explicit (loc : Loc.t) (vaddr : view)
    (invalidation_time : option nat) (macc : mem_acc)
    (init : Memory.initial) :
  Exec.t (TState.t * Memory.t) string (view * val) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  ts ← mget fst;
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
              ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
                (* Strong Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  (* We only read after the coherence point, because without mixed-size, this
     is equivalent to reading at vpre and discarding incoherent options *)
  let vread := vpre ⊔ (TState.coh ts !!! loc) in
  mem ← mget snd;
  reads ← othrow ("Reading from unmapped memory " ++ (pretty loc))%string
            $ Memory.read loc vread init mem;
  '(res, time) ← mchoosel reads;
  let read_view :=
    if (ts.(TState.fwdb) !! loc) is Some fwd then
      if (fwd.(FwdItem.time) =? time) then read_fwd_view macc fwd else time
    else time in
  let vpost := vpre ⊔ read_view in
  let check_vpost :=
    if invalidation_time is Some invalidation_time then
      (vpost <? invalidation_time)%nat
    else true in
  guard_discard (check_vpost);;
  mset fst $ TState.update_coh loc time;;
  mset fst $ TState.update TState.vrd vpost;;
  mset fst $ TState.update TState.vacq (view_if (is_rel_acq macc) vpost);;
  mset fst $ TState.update TState.vspec vaddr;;
  (if is_exclusive macc
  then mset fst $ TState.set_xclb (time, vpost)
  else mret ());;
  mret (vpost, res).

Definition read_pte (vaddr : view) :
    Exec.t (TState.t * IIS.TransRes.t) string (view * val) :=
  tres ← mget snd;
  let vpost := vaddr ⊔ tres.(IIS.TransRes.time) in
  val ← Exec.liftSt snd IIS.TransRes.pop;
  mset fst $ TState.update TState.vspec vpost;;
  mret (vpost, val).

(** Run a RegRead outcome.
    Returns the register value based on the type of register and the access type. *)
Definition run_reg_read (reg : reg) (racc : reg_acc) :
    Exec.t (TState.t * IIS.t) string (reg_type reg) :=
  ts ← mget fst;
  '(val, view) ←
    (if decide (reg ∈ relaxed_regs) then
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
        $ TState.read_reg ts reg);
  mset snd $ IIS.add view;;
  mret val.

(** Run a RegWrite outcome.
    Updates the thread state using a register value *)
Definition run_reg_write (reg : reg) (racc : reg_acc) (val : reg_type reg) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string unit :=
  guard_or
    ("Cannot write to unknown register " ++ pretty reg)%string
    (¬(is_reg_unknown reg));;
  guard_or
    "Non trivial write reg access types unsupported"
    (racc = None);;
  iis ← mget PPState.iis;
  ts ← mget PPState.state;
  let vreg := IIS.strict iis in
  vreg' ←
    (if reg =? pc_reg
      then
        mset PPState.state $ TState.update TState.vspec vreg;;
        mret 0%nat
      else mret vreg);
  if decide (reg ∈ relaxed_regs) then
    '(val, view) ← othrow
                  ("Register " ++ pretty reg ++ " unmapped on direct read")%string
                  $ TState.read_sreg_direct ts reg;
    let vpre := ts.(TState.vcse) ⊔ ts.(TState.vspec) ⊔ ts.(TState.vdsb) ⊔ view in
    let vpost := vreg' ⊔ vpre in
    mset PPState.state $ TState.add_wsreg reg val vpost;;
    mset PPState.state $ TState.update TState.vmsr vpost;;
    mset PPState.iis $ IIS.add vpost
  else
    nts ← othrow
            ("Register " ++ pretty reg ++ " unmapped; cannot write")%string
            $ TState.set_reg reg (val, vreg') ts;
    msetv PPState.state nts.

(** Run a MemRead outcome.
    Returns the new thread state, the vpost of the read and the read value. *)
Definition run_mem_read (addr : address) (macc : mem_acc) (init : Memory.initial) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string val :=
  loc ← othrow "Address not supported" $ Loc.from_addr addr;
  iis ← mget PPState.iis;
  let vaddr := iis.(IIS.strict) in
  if is_explicit macc then
    tres_opt ← mget (IIS.trs ∘ PPState.iis);
    trans_res ← othrow "Explicit access before translation" tres_opt;
    let invalidation := trans_res.(IIS.TransRes.invalidation) in
    '(view, val) ←
      Exec.liftSt (PPState.state ×× PPState.mem)
        $ read_mem_explicit loc vaddr invalidation macc init;
    mset PPState.iis $ IIS.add view;;
    mret val
  else if is_ttw macc then
    ts ← mget PPState.state;
    tres_option ← mget (IIS.trs ∘ PPState.iis);
    tres ← othrow "TTW read before translation start" tres_option;
    '(view, val) ←
      read_pte vaddr (ts, tres)
      |> Exec.lift_res_set_full
          (λ '(ts, tres) ppst,
            ppst
            |> setv PPState.state ts
            |> set PPState.iis (IIS.set_trs tres));
    mset PPState.iis $ IIS.add view;;
    mret val
  else mthrow "Unsupported 8 bytes access".

Definition run_mem_read4  (addr : address) (macc : mem_acc) (init : Memory.initial) :
    Exec.t Memory.t string (bv 32) :=
  if is_ifetch macc then
    let aligned_addr := bv_unset_bit 2 addr in
    let bit2 := bv_get_bit 2 addr in
    loc ← othrow "Address not supported" $ Loc.from_addr aligned_addr;
    mem ← mGet;
    block ← othrow ("Modified instruction memory at " ++ (pretty loc))%string
                            (Memory.read_initial loc init mem);
    mret $ (if bit2 then bv_extract 32 32 else bv_extract 0 32) block
  else mthrow "Non-ifetch 4 bytes access".


(** Performs a memory write for a thread tid at a location loc with view
    vaddr and vdata. Return the new state.

    This may mutate memory if no existing promise can be fullfilled *)
Definition write_mem (tid : nat) (loc : Loc.t) (viio : view)
    (invalidation_time : option nat) (macc : mem_acc)
    (data : val) : Exec.t (TState.t * Memory.t) string (view * option view) :=
  let msg := Msg.make tid loc data in
  let is_release := is_rel_acq macc in
  '(ts, mem) ← mGet;
  '(time, new_promise) ←
    match Memory.fulfill msg (TState.prom ts) mem with
    | Some t => mret (t, false)
    | None =>
      t ← Exec.liftSt snd $ Memory.promise msg;
      mret (t, true)
    end;
  let vbob :=
    ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
    ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
    ⊔ view_if is_release (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  let vpre := ts.(TState.vspec) ⊔ vbob ⊔ viio in
  let check_vpost :=
    if invalidation_time is Some invalidation_time then
      (time <? invalidation_time)%nat
    else true in
  guard_discard check_vpost;;
  guard_discard (vpre ⊔ (TState.coh ts !!! loc) < time)%nat;;
  mset (TState.prom ∘ fst) (filter (λ t, t ≠ time));;
  mset fst $ TState.update_coh loc time;;
  mset fst $ TState.update TState.vwr time;;
  mset fst $ TState.update TState.vrel (view_if is_release time);;
  match new_promise with
  | true => mret (time, Some vpre)
  | false => mret (time, None)
  end.

(** Tries to perform a memory write.

    If the store is not exclusive, the write is always performed and the third
    return value is true.

    If the store is exclusive the write may succeed or fail and the third
    return value indicate the success (true for success, false for error) *)
Definition write_mem_xcl (tid : nat) (loc : Loc.t) (viio : view)
    (invalidation_time : option nat) (macc : mem_acc) (data : val) :
  Exec.t (TState.t * Memory.t) string (option view) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  let xcl := is_exclusive macc in
  if xcl then
    '(time, vpre_opt) ← write_mem tid loc viio invalidation_time macc data;
    '(ts, mem) ← mGet;
    match TState.xclb ts with
    | None => mdiscard
    | Some (xtime, xview) =>
        guard_discard' (Memory.exclusive loc xtime (Memory.cut_after time mem))
    end;;
    mset fst $ TState.set_fwdb loc (FwdItem.make time viio true);;
    mset fst TState.clear_xclb;;
    mret vpre_opt
  else
    '(time, vpre_opt) ← write_mem tid loc viio invalidation_time macc data;
    mset fst $ TState.set_fwdb loc (FwdItem.make time viio false);;
    mret vpre_opt.

Definition run_cse (vmax_t : view) : Exec.t (TState.t * IIS.t) string () :=
  ts ← mget fst;
  iis ← mget snd;
  let v := ts.(TState.vspec) ⊔ ts.(TState.vcse)
            ⊔ ts.(TState.vdsb) ⊔ ts.(TState.vmsr) in
  vpost ← mchoosel $ seq_bounds (IIS.strict iis ⊔ v) vmax_t;
  mset fst $ TState.cse vpost;;
  mset snd $ IIS.add vpost.

(** Perform a barrier, mostly view shuffling *)
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
          mset fst $ TState.update TState.vdmb vpost;;
          mset snd $ IIS.add vpost
      | MBReqTypes_Reads (* dmb ld *) =>
          let vpost := ts.(TState.vrd) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          mset fst $ TState.update TState.vdmb vpost;;
          mset snd $ IIS.add vpost
      | MBReqTypes_Writes (* dmb st *) =>
          let vpost := ts.(TState.vwr) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
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
          mset fst $ TState.update TState.vdsb vpost;;
          mset snd $ IIS.add vpost
      | MBReqTypes_Reads (* dsb ld *) =>
          let vpost := ts.(TState.vrd) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          mset fst $ TState.update TState.vdsb vpost;;
          mset snd $ IIS.add vpost
      | MBReqTypes_Writes (* dsb st *) =>
          let vpost := ts.(TState.vwr) ⊔ ts.(TState.vcse) ⊔ ts.(TState.vdsb) in
          mset fst $ TState.update TState.vdsb vpost;;
          mset snd $ IIS.add vpost
      end
  | Barrier_ISB () => run_cse vmax_t
  | _ => mthrow "Unsupported barrier"
  end.

Definition run_tlbi (tid : nat) (view : nat) (tlbi : TLBIInfo) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string () :=
  guard_or
    "Non-shareable TLBIs are not supported"
    (tlbi.(TLBIInfo_shareability) ≠ Shareability_NSH);;
  guard_or
    "TLBIs in other regimes than EL10 are unsupported"
    (tlbi.(TLBIInfo_rec).(TLBIRecord_regime) = Regime_EL10);;
  let asid := tlbi.(TLBIInfo_rec).(TLBIRecord_asid) in
  let last := tlbi.(TLBIInfo_rec).(TLBIRecord_level) =? TLBILevel_Last in
  let va := bv_extract 12 36 (tlbi.(TLBIInfo_rec).(TLBIRecord_address)) in
  ts ← mget PPState.state;
  iis ← mget PPState.iis;
  let vpre := ts.(TState.vcse) ⊔ ts.(TState.vdsb) ⊔ ((*iio*) IIS.strict iis)
              ⊔ view ⊔ ts.(TState.vspec) in
  '(tlbiev : TLBI.t) ←
    match tlbi.(TLBIInfo_rec).(TLBIRecord_op) with
    | TLBIOp_ALL => mret $ TLBI.All tid
    | TLBIOp_ASID => mret $ TLBI.Asid tid asid
    | TLBIOp_VAA => mret $ TLBI.Vaa tid va last
    | TLBIOp_VA => mret $ TLBI.Va tid asid va last
    | _ => mthrow "Unsupported kind of TLBI"
    end;
  mem ← mget PPState.mem;
  time ← (if Memory.fulfill tlbiev (TState.prom ts) mem is Some t
          then mret t
          else Exec.liftSt PPState.mem $ Memory.promise tlbiev);
  guard_discard (vpre < time)%nat;;
  mset (TState.prom ∘ PPState.state) (filter (λ t, t ≠ time));;
  mset PPState.state $ TState.update TState.vtlbi time;;
  mset PPState.iis $ IIS.add time.

Definition va_in_range (va : bv 64) : Prop :=
  let top_bits := bv_extract 48 16 va in
  top_bits = (-1)%bv ∨ top_bits = 0%bv.
Instance Decision_va_in_range (va : bv 64) : Decision (va_in_range va).
Proof. unfold_decide. Defined.

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
  let mmfr1 : reg := ID_AA64MMFR1_EL1 in
  '(regval, _) ← othrow "ETS is indicated in the ID_AA64MMFR1_EL1 register value" (TState.read_reg ts mmfr1);
  val ← othrow "The register value of ID_AA64MMFR1_EL1 is 64 bit" (regval_to_val mmfr1 regval);
  let ets_bits := bv_extract 36 4 val in
  mret ((ets_bits =? 2%bv) || (ets_bits =? 3%bv)).

Definition ets3 (ts : TState.t) : result string bool :=
  let mmfr1 : reg := ID_AA64MMFR1_EL1 in
  '(regval, _) ← othrow "ETS is indicated in the ID_AA64MMFR1_EL1 register value" (TState.read_reg ts mmfr1);
  val ← othrow "The register value of ID_AA64MMFR1_EL1 is 64 bit" (regval_to_val mmfr1 regval);
  mret (bv_extract 36 4 val =? 3%bv).

Definition new_invalidation_opt (ti_new ti_old : option nat) : bool :=
  match ti_new, ti_old with
  | Some ti_new, Some ti_old => ti_old <? ti_new
  | None, None => false
  | Some _, None => true
  | None, Some _ => true
  end.

Definition is_new_entry (path : list val) (ti_new : option nat)
    (entries : list (list val * nat * option nat)) : bool :=
  forallb
    (λ '(p, t, ti),
      negb(path =? p) || new_invalidation_opt ti_new ti) entries.

(* Snapshots are sorted in the descending order of `trans_time`.
   Thus, we do not have to use `trans_time` to check the interval *)
Definition get_valid_entries_from_snapshots (snapshots : list (TLB.t * nat))
              (mem : Memory.t)
              (tid : nat)
              (va : bv 64) (asid : bv 16) :
            result string (list (list val * nat * option nat)) :=
  fold_right (λ '(tlb, trans_time) entries,
    candidates ← TLB.lookup mem tid tlb trans_time va asid;
    prev ←@{result string} entries;
    let new :=
      omap (λ '(path, ti_opt),
        if decide (is_new_entry path ti_opt prev) then
          Some (path, trans_time, ti_opt)
        else None
      ) candidates in
    mret (new ++ prev)
  ) (mret nil) snapshots.

Definition get_invalid_entries_from_snapshots (snapshots : list (TLB.t * nat))
              (ts : TState.t)
              (init : Memory.initial)
              (mem : Memory.t)
              (tid : nat) (is_ets2 : bool)
              (va : bv 64) (asid : bv 16) (ttbr : reg) :
            result string (list (list val * nat * option nat)) :=
  fold_right (λ '(tlb, trans_time) entries,
    if decide (is_ets2 ∧ trans_time < ts.(TState.vwr) ⊔ ts.(TState.vrd)) then
      entries
    else
      candidates ← TLB.get_invalid_ptes_with_inv_time ts init mem tid tlb trans_time va asid ttbr;
      prev ←@{result string} entries;
      let new :=
        omap (λ '(path, ti_opt),
          if decide (is_new_entry path ti_opt prev) then
            Some (path, trans_time, ti_opt)
          else None
        ) candidates in
      mret (new ++ prev)
  ) (mret nil) snapshots.

Definition run_trans_start (trans_start : TranslationStartInfo)
                           (tid : nat) (init : Memory.initial) :
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
      snapshots ← mlift $ TLB.unique_snapshots_until_timestamp ts init mem vmax_t va ttbr;
      valid_entries ← mlift $ get_valid_entries_from_snapshots snapshots mem tid va asid;
      invalid_entries ← mlift $
        get_invalid_entries_from_snapshots snapshots ts init mem tid is_ets2 va asid ttbr;
      (* update IIS with either a valid translation result or a fault *)
      let valid_trs :=
        map (λ '(path, t, ti),
          IIS.TransRes.make (va_to_vpn va) t path ti) valid_entries in
      let invalid_trs :=
        map (λ '(path, t, ti),
          IIS.TransRes.make (va_to_vpn va) t path ti) invalid_entries in
      mchoosel (valid_trs ++ invalid_trs)
    else
      mret $ IIS.TransRes.make (va_to_vpn va) vpre_t [] None;
  mset PPState.iis $ IIS.set_trs trans_res.

Definition read_fault_vpre (is_acq : bool)
  (trans_time : nat) : Exec.t (TState.t * IIS.t) string view :=
  ts ← mget fst;
  iis ← mget snd;
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
              ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
              ⊔ view_if is_acq ts.(TState.vrel) in
  mret $ iis.(IIS.strict) ⊔ vbob ⊔ trans_time ⊔ ts.(TState.vmsr).

Definition write_fault_vpre (is_rel : bool)
  (trans_time : nat) : Exec.t (TState.t * IIS.t) string view :=
  ts ← mget fst;
  iis ← mget snd;
  let vbob := ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
              ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
              ⊔ view_if is_rel (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  mret $ iis.(IIS.strict) ⊔ ts.(TState.vspec) ⊔ vbob ⊔ trans_time ⊔ ts.(TState.vmsr).

Definition run_trans_end (trans_end : trans_end) :
    Exec.t (TState.t * IIS.t) string () :=
  ts ← mget fst;
  iis ← mget snd;
  if iis.(IIS.trs) is Some trs then
    let trans_time := trs.(IIS.TransRes.time) in
    let fault := trans_end.(AddressDescriptor_fault) in
    if decide (fault.(FaultRecord_statuscode) = Fault_None) then
      mret ()
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
        mset snd $ IIS.add (view_if is_write write_view)
  else
    mthrow "Translation ends with an empty translation".

Definition run_take_exception (fault : exn) (vmax_t : view) :
    Exec.t (TState.t * IIS.t) string () :=
  iis ← mget snd;
  if iis.(IIS.trs) is Some trans_res then
    match trans_res.(IIS.TransRes.invalidation) with
    | Some invalidation => run_cse invalidation
    | None => mret ()
    end
  else
    run_cse vmax_t.

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
  | MemRead (MemReq.make macc addr addr_space 8 0) =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      let initmem := Memory.initial_from_memMap initmem in
      val ← run_mem_read addr macc initmem;
      mret (Ok (val, 0%bv), None)
  | MemRead (MemReq.make macc addr addr_space 4 0) => (* ifetch *)
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      let initmem := Memory.initial_from_memMap initmem in
      opcode ← Exec.liftSt PPState.mem $ run_mem_read4 addr macc initmem;
      mret (Ok (opcode, 0%bv), None)
  | MemRead _ => mthrow "Memory read of size other than 8 or 4, or with tags"
  | MemWriteAddrAnnounce _ =>
      vaddr ← mget (IIS.strict ∘ PPState.iis);
      mset PPState.state $ TState.update TState.vspec vaddr;;
      mret ((), None)
  | MemWrite (MemReq.make macc addr addr_space 8 0) val _ =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      addr ← othrow "Address not supported" $ Loc.from_addr addr;
      viio ← mget (IIS.strict ∘ PPState.iis);
      if is_explicit macc then
        tres_opt ← mget (IIS.trs ∘ PPState.iis);
        trans_res ← othrow "Explicit access before translation" tres_opt;
        let invalidation := trans_res.(IIS.TransRes.invalidation) in
        vpre_opt ← Exec.liftSt (PPState.state ×× PPState.mem) $
                      write_mem_xcl tid addr viio invalidation macc val;
        mret (Ok (), vpre_opt)
      else mthrow "Unsupported non-explicit write"
  | MemWrite _ _ _ => mthrow "Memory write of size other than 8, or with tags"
  | Barrier barrier =>
      mem ← mget PPState.mem;
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_barrier barrier (length mem);;
      mret ((), None)
  | TlbOp tlbi =>
      viio ← mget (IIS.strict ∘ PPState.iis);
      run_tlbi tid viio tlbi;;
      mret ((), None)
  | ReturnException =>
      mem ← mget PPState.mem;
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_cse (length mem);;
      mret ((), None)
  | TranslationStart trans_start =>
      let initmem := Memory.initial_from_memMap initmem in
      run_trans_start trans_start tid initmem;;
      mret ((), None)
  | TranslationEnd trans_end =>
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_trans_end trans_end;;
      mret ((), None)
  | GenericFail s => mthrow ("Instruction failure: " ++ s)%string
  | TakeException fault =>
      mem ← mget PPState.mem;
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_take_exception fault (length mem);;
      mret ((), None)
  | _ => mthrow "Unsupported outcome".

  Definition run_outcome' (out : outcome) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string (eff_ret out) :=
    run_outcome out |$> fst.

End RunOutcome.

Module CProm.
  Record t :=
    make {
      proms : list Ev.t;
    }.
  #[global] Instance eta : Settable _ :=
    settable! make <proms>.

  #[global] Instance empty : Empty t := CProm.make [].

  #[global] Instance union : Union t := λ x y, CProm.make (x.(proms) ++ y.(proms)).

  Definition init : t := make [].

  (** Add the latest ev in the mem to the CProm
      if the corresponding vpre is not bigger than the base *)
  Definition add_if (mem : Memory.t) (vpre : view) (base : view) (cp : t) : t :=
    if decide (vpre ≤ base)%nat then
      match mem with
      | ev :: mem =>
        cp |> set proms (ev ::.)
      | [] => cp
      end
    else cp.

End CProm.

Section ComputeProm.
  Context (tid : nat).
  Context (initmem : memoryMap).
  Context (term : registerMap → bool).

  Definition run_outcome_with_promise
              (base : view)
              (out : outcome) :
        Exec.t (CProm.t * PPState.t TState.t Ev.t IIS.t) string (eff_ret out) :=
    '(res, vpre_opt) ← Exec.liftSt snd $ run_outcome tid initmem out;
    if vpre_opt is Some vpre then
      mem ← mget (PPState.mem ∘ snd);
      mset fst (CProm.add_if mem vpre base);;
      mret res
    else
      mret res.

  Fixpoint runSt_to_termination
                      (isem : iMon ())
                      (fuel : nat)
                      (base : nat)
      : Exec.t (CProm.t * PPState.t TState.t Ev.t IIS.t) string bool :=
    match fuel with
    | 0%nat =>
      ts ← mget (PPState.state ∘ snd);
      mret (term (TState.reg_map ts))
    | S fuel =>
      let handler := run_outcome_with_promise base in
      cinterp handler isem;;
      ts ← mget (PPState.state ∘ snd);
      if term (TState.reg_map ts) then
        mret true
      else
        runSt_to_termination isem fuel base
    end.

  Definition run_to_termination (isem : iMon ())
                                (fuel : nat)
                                (ts : TState.t)
                                (mem : Memory.t)
      : Exec.res string Ev.t :=
    let base := List.length mem in
    let res := Exec.results $ runSt_to_termination isem fuel base (CProm.init, PPState.Make ts mem IIS.init) in
    guard_or ("Could not finish promises within the size of the fuel")%string (∀ r ∈ res, r.2 = true);;
    res.*1.*1
    |> union_list
    |> mchoosel ∘ CProm.proms.

End ComputeProm.

(** * Implement GenPromising ***)

(** A thread is allowed to promise any promises with the correct tid for a
    non-certified promising model *)
Definition allowed_promises_nocert tid (initmem : memoryMap) (ts : TState.t)
  (mem : Memory.t) := {[ ev | (Ev.tid ev) = tid]}.
Arguments allowed_promises_nocert _ _ _ /.

Definition VMPromising_nocert' : PromisingModel :=
  {|tState := TState.t;
    tState_init := λ tid, TState.init;
    tState_regs := TState.reg_map;
    tState_nopromises := is_emptyb ∘ TState.prom;
    iis := IIS.t;
    iis_init := IIS.init;
    address_space := PAS_NonSecure;
    mEvent := Ev.t;
    allowed_promises := allowed_promises_nocert;
    handler := run_outcome';
    emit_promise := λ tid initmem mem msg, TState.promise (length mem);
    memory_snapshot :=
      λ initmem, Memory.to_memMap (Memory.initial_from_memMap initmem);
  |}.

Definition VMPromising_nocert isem :=
  Promising_to_Modelnc isem VMPromising_nocert'.

Definition seq_step (isem : iMon ()) (tid : nat) (initmem : memoryMap)
  : relation (TState.t * Memory.t) :=
  let handler := run_outcome' tid initmem in
  λ '(ts, mem) '(ts', mem'),
    (ts', mem') ∈
    PPState.state ×× PPState.mem
      <$> (Exec.success_state_list $ cinterp handler isem (PPState.Make ts mem IIS.init)).

Definition allowed_promises_cert (isem : iMon ()) tid (initmem : memoryMap)
  (ts : TState.t) (mem : Memory.t) : propset Ev.t :=
  {[ ev |
    let ts := TState.promise (length mem) ts in
    let mem := ev :: mem in
    ∃ ts' mem',
      rtc (seq_step isem tid initmem) (ts, mem) (ts', mem') ∧
        TState.prom ts' = []
  ]}.


Definition VMPromising_cert' (isem : iMon ()) : PromisingModel  :=
  {|tState := TState.t;
    tState_init := λ tid, TState.init;
    tState_regs := TState.reg_map;
    tState_nopromises := is_emptyb ∘ TState.prom;
    iis := IIS.t;
    iis_init := IIS.init;
    address_space := PAS_NonSecure;
    mEvent := Ev.t;
    handler := run_outcome';
    allowed_promises := allowed_promises_cert isem;
    emit_promise := λ tid initmem mem msg, TState.promise (length mem);
    memory_snapshot :=
      λ initmem, Memory.to_memMap (Memory.initial_from_memMap initmem);
  |}.

Program Definition VMPromising_exe' (isem : iMon ())
    : BasicExecutablePM :=
  {|pModel := VMPromising_cert' isem;
    promise_select :=
      λ fuel tid term initmem ts mem,
          run_to_termination tid initmem term isem fuel ts mem
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.


Definition VMPromising_cert_c isem fuel :=
  Promising_to_Modelc isem (VMPromising_exe' isem) fuel.
