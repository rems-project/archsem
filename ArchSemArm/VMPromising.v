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

Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.Exec.
Require Import ASCommon.GRel.
Require Import ASCommon.StateT.
Require Import ASCommon.FMon.
Require Import ASCommon.HVec.
Require Import Coq.Program.Equality.

Require UMPromising.
Import (hints) UMPromising.

Require Import ArchSem.GenPromising.
Require Import ArmInst.

From stdpp Require Import decidable list vector.
From stdpp Require Import pretty.


(* Shadow constructor name from coq-sail with our result type *)
Import ASCommon.CResult.

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
          let val :=
            for addr in addr_range (Loc.to_addr loc) 8 do mem !! addr end
            |$> bv_of_bytes 64
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
    prom |> filter (fun t => Some ev =? mem !! t)
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
      GReg R0;
      GReg R1;
      GReg R2;
      GReg R3;
      GReg R4;
      GReg R5;
      GReg R6;
      GReg R7;
      GReg R8;
      GReg R9;
      GReg R10;
      GReg R11;
      GReg R12;
      GReg R13;
      GReg R14;
      GReg R15;
      GReg R16;
      GReg R17;
      GReg R18;
      GReg R19;
      GReg R20;
      GReg R21;
      GReg R22;
      GReg R23;
      GReg R24;
      GReg R25;
      GReg R26;
      GReg R27;
      GReg R28;
      GReg R29;
      GReg R30;
      GReg SP_EL0;
      GReg SP_EL1;
      GReg SP_EL2;
      GReg SP_EL3;
      GReg PSTATE;
      GReg ELR_EL1;
      GReg ELR_EL2;
      GReg ELR_EL3].

(** Relaxed registers are not guaranteed to read the latest value. *)
Definition relaxed_regs : gset reg :=
  list_to_set [
      GReg ESR_EL1;
      GReg ESR_EL2;
      GReg ESR_EL3;
      GReg FAR_EL1;
      GReg FAR_EL2;
      GReg FAR_EL3;
      GReg PAR_EL1;
      GReg TTBR0_EL1;
      GReg TTBR0_EL2;
      GReg TTBR0_EL3;
      GReg TTBR1_EL1;
      GReg TTBR1_EL2;
      GReg VBAR_EL1;
      GReg VBAR_EL2;
      GReg VBAR_EL3;
      GReg VTTBR_EL2].

(** Determine if input register is an unknown register from the architecture *)
Definition is_reg_unknown (r : reg) : Prop :=
  ¬(r ∈ relaxed_regs ∨ r ∈ strict_regs ∨ r = pc_reg).
Instance Decision_is_reg_unknown (r : reg) : Decision (is_reg_unknown r).
Proof. unfold_decide. Defined.

Equations regval_to_val (r : reg) (v : reg_type r) : option val :=
  regval_to_val (GReg (R_bitvector_64 _)) v := Some v.
  (* regval_to_val _ _ := None. *)

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
        vtlbi : view; (* The maximum output view of an TLBI *)
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
  Definition set_reg (ts : t) (reg : reg) (rv : reg_type reg * view) : option t :=
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
  Definition update_coh (loc : Loc.t) (v : view) : t → t :=
    set coh (alter (max v) loc).

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

    Definition get (ctxt : Ctxt.t) (vatlb : t)
      : gset (Entry.t (Ctxt.lvl ctxt)) :=
      (hget (Ctxt.lvl ctxt) vatlb) !! (Ctxt.nd ctxt) |> default ∅.

    Definition getFE (ctxt : Ctxt.t) (vatlb : t)
      : gset (FE.t) :=
      get ctxt vatlb
      |> set_map (fun (e : Entry.t (Ctxt.lvl ctxt)) => existT ctxt e).

    Definition singleton (ctxt : Ctxt.t) (entry : Entry.t (Ctxt.lvl ctxt)) : t :=
      hset (Ctxt.lvl ctxt) {[(Ctxt.nd ctxt) := {[ entry ]}]} init.

    #[global] Instance empty : Empty t := VATLB.init.
    #[global] Instance union : Union t := fun x y => hmap2 (fun _ => (∪ₘ)) x y.
  End VATLB.

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
    Ok (fold_left union vatlbs VATLB.init).

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
      - Returns [tlb] with added VATLB entries. *)
  Definition va_fill (tlb : t) (ts : TState.t)
      (init : Memory.initial)
      (mem : Memory.t)
      (time : nat)
      (lvl : Level)
      (va : bv 64)
      (ttbr : reg) : result string t :=
    new_vatlb ←
      match parent_lvl lvl with
      | None =>
        vatlb_new ← va_fill_root ts init mem time (level_index va root_lvl) ttbr;
        Ok $ vatlb_new ∪ tlb.(vatlb)
      | Some plvl =>
        sregs ← othrow "TTBR should exist in initial state"
                $ TState.read_sreg_at ts ttbr time;
        active_vatlbs ←
          let pva := level_prefix va plvl in
          let index := level_index va lvl in
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
    Ok (TLB.make (new_vatlb ∪ tlb.(vatlb))).

  (** Fill TLB entries for [va] through all levels 0–3.
      - Sequentially calls [va_fill] at each level.
      - Produces a TLB with the full translation chain if available. *)
  Definition update (tlb : t)
      (ts : TState.t)
      (init : Memory.initial)
      (mem : Memory.t)
      (time : nat)
      (va : bv 64)
      (ttbr : reg) : result string t :=
    tlb0 ← va_fill tlb ts init mem time root_lvl va ttbr;
    tlb1 ← va_fill tlb0 ts init mem time 1%fin va ttbr;
    tlb2 ← va_fill tlb1 ts init mem time 2%fin va ttbr;
    va_fill tlb2 ts init mem time 3%fin va ttbr.

  (** ** TLB invalidation *)

  Definition affects_va (asid : bv 16) (va : bv 36) (last : bool)
                        (ctxt : Ctxt.t)
                        (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
    let '(te_lvl, te_va, te_asid, te_val) :=
          (Ctxt.lvl ctxt, Ctxt.va ctxt, Ctxt.asid ctxt, Entry.pte te) in
    (match_prefix_at te_lvl te_va va)
    ∧ (match te_asid with
        | Some te_asid => asid = te_asid
        | None => True
        end)
    ∧ (if last then is_final te_lvl te_val else False).
  Instance Decision_affects_va (asid : bv 16) (va : bv 36) (last : bool)
                               (ctxt : Ctxt.t)
                               (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (affects_va asid va last ctxt te).
  Proof. unfold_decide. Defined.

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

  Definition affects_vaa (va : bv 36) (last : bool)
                         (ctxt : Ctxt.t)
                         (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
    let '(te_lvl, te_va, te_val) :=
          (Ctxt.lvl ctxt, Ctxt.va ctxt, Entry.pte te) in
    (match_prefix_at te_lvl te_va va)
    ∧ (if last then is_final te_lvl te_val else False).
  Instance Decision_affects_vaa (va : bv 36) (last : bool)
                                (ctxt : Ctxt.t)
                                (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (affects_vaa va last ctxt te).
  Proof. unfold_decide. Defined.

  Definition affects (tlbi : TLBI.t) (ctxt : Ctxt.t)
                     (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
    match tlbi with
    | TLBI.All tid => True
    | TLBI.Va tid asid va last => affects_va asid va last ctxt te
    | TLBI.Asid tid asid => affects_asid asid ctxt te
    | TLBI.Vaa tid va last => affects_vaa va last ctxt te
    end.
  Instance Decision_affects (tlbi : TLBI.t) (ctxt : Ctxt.t)
                     (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (affects tlbi ctxt te).
  Proof. unfold_decide. Defined.

  Definition tlbi_apply_lvl (tlb : t) (ts : TState.t)
                  (init : Memory.initial) (mem : Memory.t)
                  (time : nat)
                  (tlbi : TLBI.t)
                  (lvl : Level)
                  (va : bv 64)
                  (asid : option (bv 16)) : t :=
    let ndctxt := NDCtxt.make (level_prefix va lvl) asid in
    let ctxt := existT lvl ndctxt in
    VATLB.get ctxt tlb.(vatlb)
    |> filter (λ te, ¬(affects tlbi ctxt te))
    |> λ tes,
        TLB.make $ hset (Ctxt.lvl ctxt) {[(Ctxt.nd ctxt) := tes]} tlb.(vatlb).

  Definition tlbi_apply (tlb : t) (ts : TState.t)
                  (init : Memory.initial) (mem : Memory.t)
                  (time : nat)
                  (tlbi : TLBI.t)
                  (va : bv 64)
                  (asid : option (bv 16)) : t :=
    let tlb0 := tlbi_apply_lvl tlb ts init mem time tlbi root_lvl va asid in
    let tlb1 := tlbi_apply_lvl tlb0 ts init mem time tlbi 1%fin va asid in
    let tlb2 := tlbi_apply_lvl tlb1 ts init mem time tlbi 2%fin va asid in
    tlbi_apply_lvl tlb2 ts init mem time tlbi 3%fin va asid.

  (** Get the TLB state at a certain timestamp *)
  Fixpoint at_timestamp (ts : TState.t) (mem_init : Memory.initial) (mem : Memory.t)
                       (time : nat)
                       (va : bv 64)
                       (asid : option (bv 16))
                       (ttbr : reg)
                      {struct time} : result string t :=
    match time with
    | O => update init ts mem_init mem 0 va ttbr
    | S ptime =>
      tlb ← at_timestamp ts mem_init mem ptime va asid ttbr;
      match mem !! time with
      | Some ev =>
        match Ev.get_tlbi ev with
        | Some tlbi => mret $ tlbi_apply tlb ts mem_init mem time tlbi va asid
        | None => update tlb ts mem_init mem time va ttbr
        end
      | None => mret init
      end
    end.

  Definition is_te_invalidated_by_tlbi (tlb : t)
                (tlbi : TLBI.t)
                (tid : nat)
                (ctxt : Ctxt.t)
                (te : Entry.t (Ctxt.lvl ctxt)) : Prop :=
      TLBI.tid tlbi <> tid ∧ te ∉ VATLB.get ctxt tlb.(vatlb).
  Instance Decision_is_te_invalidated_by_tlbi (tlb : t) (tlbi : TLBI.t) (tid : nat)
                (ctxt : Ctxt.t) (te : Entry.t (Ctxt.lvl ctxt)) :
    Decision (is_te_invalidated_by_tlbi tlb tlbi tid ctxt te).
  Proof. unfold_decide. Defined.

  Fixpoint invalidation_time_from_evs (ts : TState.t) (init : Memory.initial)
                                      (mem : Memory.t)
                                      (tid : nat)
                                      (ctxt : Ctxt.t)
                                      (te : Entry.t (Ctxt.lvl ctxt))
                                      (ttbr : reg)
                                      (evs : list (Ev.t * nat)) : result string nat :=
    match evs with
    | nil => mret 0
    | (ev, t) :: tl =>
      match ev with
      | Ev.Tlbi tlbi =>
        let va := Ctxt.va ctxt in
        let asid := Ctxt.asid ctxt in
        tlb ← at_timestamp ts init mem t (prefix_to_va va) asid ttbr;
        if decide (is_te_invalidated_by_tlbi tlb tlbi tid ctxt te) then
          mret t
        else
          invalidation_time_from_evs ts init mem tid ctxt te ttbr tl
      | _ => invalidation_time_from_evs ts init mem tid ctxt te ttbr tl
      end
    end.

  (** Calculate the earliest future time at which a translation entry is effectively invalidated
      in the TLB due to an TLBI event *)
  Definition invalidation_time (ts : TState.t) (init : Memory.initial) (mem : Memory.t)
                               (tid : nat) (time : nat)
                               (ctxt : Ctxt.t)
                               (te : Entry.t (Ctxt.lvl ctxt))
                               (ttbr : reg) : result string nat :=
    let evs := PromMemory.cut_after_with_timestamps time mem in
    invalidation_time_from_evs ts init mem tid ctxt te ttbr evs.
End TLB.

Module VATLB := TLB.VATLB.

(** * Instruction semantics ***)

(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  (* TODO Fixup this type to contain:
     - Translation parameters
     - whether we're in the middle or after the end
     - If after the end: The results: pa + attributes *)
  (* Translation Results *)
  Module TransRes.
    Record t :=
      make {
          va : bv 36;
          time : nat;
          remaining : list (bv 64);
          invalidation : nat
        }.

    #[global] Instance eta : Settable _ :=
      settable! make <va; time; remaining; invalidation>.

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

  #[global] Instance eta : Settable _ :=
    settable! make <strict;trs>.

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
  (invalidation_time : nat) (macc : mem_acc)
  (init : Memory.initial)
  : Exec.t (TState.t * Memory.t) string (view * val) :=
  guard_or "Atomic RMV unsupported" (¬ (is_atomic_rmw macc));;
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
  reads ← othrow "Reading from unmapped memory" $
            Memory.read loc vread init mem;
  '(res, time) ← mchoosel reads;
  let read_view :=
    if (ts.(TState.fwdb) !! loc) is Some fwd then
      if (fwd.(FwdItem.time) =? time) then read_fwd_view macc fwd else time
    else time in
  let vpost := vpre ⊔ read_view in
  guard_discard (vpost ≤ invalidation_time)%nat;;
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
        then othrow "Register unmapped on direct read"
              $ TState.read_sreg_direct ts reg
        else
          valvs ← othrow "Register unmapped on indirect read"
                  $ TState.read_sreg_indirect ts reg;
          mchoosel valvs
    else
      othrow "Register unmapped; cannot read" $ TState.read_reg ts reg);
  mset snd $ IIS.add view;;
  mret val.

(** Run a RegWrite outcome.
    Updates the thread state using a register value *)
Definition run_reg_write (reg : reg) (racc : reg_acc) (val : reg_type reg) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string unit :=
  guard_or
    "Cannot write to unknown register"
    (is_reg_unknown reg);;
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
    '(val, view) ← othrow "Register unmapped on direct read" $
                     TState.read_sreg_direct ts reg;
    let vpre := ts.(TState.vcse) ⊔ ts.(TState.vspec) ⊔ ts.(TState.vdsb) ⊔ view in
    let vpost := vreg' ⊔ vpre in
    mset PPState.state $ TState.add_wsreg reg val vpost;;
    mset PPState.state $ TState.update TState.vmsr vpost;;
    mset PPState.iis $ IIS.add vpost
  else
    nts ← othrow "Register unmapped; cannot write" $
            TState.set_reg ts reg (val, vreg');
    msetv PPState.state nts.

(** Run a MemRead outcome.
    Returns the new thread state, the vpost of the read and the read value. *)
Definition run_mem_read (addr : address) (macc : mem_acc) (init : Memory.initial) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string val :=
  addr ← othrow "Address not supported" $ Loc.from_addr addr;
  iis ← mget PPState.iis;
  let vaddr := iis.(IIS.strict) in
  if is_explicit macc then
    tres_opt ← mget (IIS.trs ∘ PPState.iis);
    trans_res ← othrow "Explicit access before translation" tres_opt;
    let invalidation := trans_res.(IIS.TransRes.invalidation) in
    '(view, val) ←
      Exec.liftSt (PPState.state ×× PPState.mem)
        $ read_mem_explicit addr vaddr invalidation macc init;
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
    block ← othrow "Modified instruction memory"
                            (Memory.read_initial loc init mem);
    mret $ (if bit2 then bv_extract 32 32 else bv_extract 0 32) block
  else mthrow "Non-ifetch 4 bytes access".


(** Performs a memory write for a thread tid at a location loc with view
    vaddr and vdata. Return the new state.

    This may mutate memory if no existing promise can be fullfilled *)
Definition write_mem (tid : nat) (loc : Loc.t) (viio : view) (macc : mem_acc)
    (data : val) : Exec.t (TState.t * Memory.t) string view :=
  let msg := Msg.make tid loc data in
  let is_release := is_rel_acq macc in
  '(ts,mem) ← mGet;
  time ← (if Memory.fulfill msg (TState.prom ts) mem is Some t
         then mret t
         else Exec.liftSt snd $ Memory.promise msg);
  let vbob :=
    ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.vdsb)
    ⊔ ts.(TState.vcse) ⊔ ts.(TState.vacq)
    ⊔ view_if is_release (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  let vpre := ts.(TState.vspec) ⊔ vbob ⊔ viio in
  guard_discard (vpre ⊔ (TState.coh ts !!! loc) < time)%nat;;
  mset (TState.prom ∘ fst) (filter (λ t, t ≠ time));;
  mset fst $ TState.update_coh loc time;;
  mset fst $ TState.update TState.vwr time;;
  mset fst $ TState.update TState.vrel (view_if is_release time);;
  mret time.


(** Tries to perform a memory write.

    If the store is not exclusive, the write is always performed and the third
    return value is true.

    If the store is exclusive the write may succeed or fail and the third
    return value indicate the success (true for success, false for error) *)
Definition write_mem_xcl (tid : nat) (loc : Loc.t) (viio : view)
    (macc : mem_acc) (data : val)
    : Exec.t (TState.t * Memory.t) string () :=
  guard_or "Atomic RMV unsupported" (¬ (is_atomic_rmw macc));;
  let xcl := is_exclusive macc in
  if xcl then
    time ← write_mem tid loc viio macc data;
    '(ts, mem) ← mGet;
    match TState.xclb ts with
    | None => mdiscard
    | Some (xtime, xview) =>
        guard_discard' (Memory.exclusive loc xtime (Memory.cut_after time mem))
    end;;
    mset fst $ TState.set_fwdb loc (FwdItem.make time viio true);;
    mset fst TState.clear_xclb
  else
    time ← write_mem tid loc viio macc data;
    mset fst $ TState.set_fwdb loc (FwdItem.make time viio false).

Definition run_cse : Exec.t (TState.t * IIS.t) string () :=
  mSet
    (λ '(ts, iis),
      let vpost :=
        ts.(TState.vspec) ⊔ ts.(TState.vcse)
        ⊔ ts.(TState.vdsb) ⊔ ts.(TState.vmsr)
      in (TState.cse vpost ts, IIS.add vpost iis)).

(** Perform a barrier, mostly view shuffling *)
Definition run_barrier (barrier : barrier) :
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
  | Barrier_DSB dmb => (* dsb *)
      guard_or "Non-shareable barrier are not supported"
       (dmb.(DxB_domain) = MBReqDomain_Nonshareable);;
       match dmb.(DxB_types) with
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
  | Barrier_ISB () => run_cse
  | _ => mthrow "Unsupported barrier"
  end.

Definition run_tlbi (tid : nat) (view : nat) (tlbi : TLBIInfo) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string () :=
  guard_or
    "Non-shareable TLBIs are not supported"
    (tlbi.(TLBIInfo_shareability) = Shareability_NSH);;
  guard_or
    "TLBIs in other regimes than EL10 are unsupported"
    (tlbi.(TLBIInfo_rec).(TLBIRecord_regime) ≠ Regime_EL10);;
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
  mset (TState.prom ∘ PPState.state) $ delete time;;
  mset PPState.state $ TState.update TState.vtlbi time;;
  mset PPState.iis $ IIS.add time.


(** Runs an outcome. *)
Section RunOutcome.
  Context (tid : nat) (initmem : memoryMap).

  Equations run_outcome (out : outcome) :
      Exec.t (PPState.t TState.t Ev.t IIS.t) string (eff_ret out) :=
  | RegWrite reg racc val =>
      run_reg_write reg racc val
  | RegRead reg racc =>
      Exec.liftSt (PPState.state ×× PPState.iis) $ (run_reg_read reg racc)
  | MemRead (MemReq.make macc addr addr_space 8 0) =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      let initmem := Memory.initial_from_memMap initmem in
      val ← run_mem_read addr macc initmem;
      mret (Ok (val, 0%bv))
  | MemRead (MemReq.make macc addr addr_space 4 0) => (* ifetch *)
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      let initmem := Memory.initial_from_memMap initmem in
      opcode ← Exec.liftSt PPState.mem $ run_mem_read4 addr macc initmem;
      mret (Ok (opcode, 0%bv))
  | MemRead _ => mthrow "Memory read of size other than 8 or 4, or with tags"
  | MemWriteAddrAnnounce _ =>
      vaddr ← mget (IIS.strict ∘ PPState.iis);
      mset PPState.state $ TState.update TState.vspec vaddr
  | MemWrite (MemReq.make macc addr addr_space 8 0) val _ =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      addr ← othrow "Address not supported" $ Loc.from_addr addr;
      viio ← mget (IIS.strict ∘ PPState.iis);
      if is_explicit macc then
        Exec.liftSt (PPState.state ×× PPState.mem) $
            write_mem_xcl tid addr viio macc val;;
        mret (Ok ())
      else mthrow "Unsupported non-explicit write"
  | MemWrite _ _ _ => mthrow "Memory write of size other than 8, or with tags"
  | Barrier barrier =>
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_barrier barrier
  | TlbOp tlbi =>
      viio ← mget (IIS.strict ∘ PPState.iis);
      run_tlbi tid viio tlbi
  | ReturnException =>
      Exec.liftSt (PPState.state ×× PPState.iis) $ run_cse
  | GenericFail s => mthrow ("Instruction failure: " ++ s)%string
  | _ => mthrow "Unsupported outcome".
    (* TODO: translation - split lookup and update *)
End RunOutcome.

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
    handler := run_outcome;
    allowed_promises := allowed_promises_nocert;
    emit_promise := λ tid initmem mem msg, TState.promise (length mem);
    memory_snapshot :=
      λ initmem, Memory.to_memMap (Memory.initial_from_memMap initmem);
  |}.

Definition VMPromising_nocert isem :=
  Promising_to_Modelnc isem VMPromising_nocert'.

Definition seq_step (isem : iMon ()) (tid : nat) (initmem : memoryMap)
  : relation (TState.t * Memory.t) :=
  let handler := run_outcome tid initmem in
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
    handler := run_outcome;
    allowed_promises := allowed_promises_cert isem;
    emit_promise := λ tid initmem mem msg, TState.promise (length mem);
    memory_snapshot :=
      λ initmem, Memory.to_memMap (Memory.initial_from_memMap initmem);
  |}.
