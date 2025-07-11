(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021 Anonymous                                              *)
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
      |> list_filter_map
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
  Definition exclusive (loc : Loc.t) (v : view) (mem : t) : bool:=
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
End WSReg.

Module LEvent.
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
End LEvent.


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
        levs : list LEvent.t;

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

  Definition filter_wsreg (levs : list LEvent.t) : list WSReg.t :=
    levs |> list_filter_map LEvent.get_wsreg.

  Definition filter_cse (levs: list LEvent.t) : list view :=
    levs |> list_filter_map LEvent.get_cse.
    
  (** Read the last system register write at system register position s *)
  Definition read_sreg_last (ts : t) (sreg : reg) (s : nat) :=
    let newval :=
      ts.(levs)
      |> drop ((lev_cur ts) - s)
      |> filter_wsreg
      |> list_filter_map (WSReg.to_val_view_if sreg)
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
      |> list_filter_map (WSReg.to_val_view_if sreg)
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
  Definition read_sreg_at (ts : t) (sreg : reg) (t : nat) :=
    let last_cse :=
      ts.(levs)
           |> filter_cse
           |> filter (λ tcse, tcse < t)
           |> hd 0%nat
    in
    read_sreg_by_cse ts sreg last_cse
      |$> list_filter_map (
            λ valv, 
              if bool_decide (valv.2 ≤ t) 
              then Some valv
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
    (update vcse v) ∘ (set levs (LEvent.Cse v ::.)).
End TState.

(*** VA helper ***)

Definition Level := fin 4.
#[export] Typeclasses Transparent Level.

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

Definition level_index {n : N} (va : bv n) (lvl : Level) : bv 9 :=
  bv_extract 0 9 (level_prefix va lvl).

Definition higher_level {n : N} (va : bv n) : bv (n - 9) :=
  bv_extract 9 (n - 9) va.

Definition next_entry_loc (loc : Loc.t) (index : bv 9) : Loc.t :=
  bv_concat 53 (bv_extract 9 44 loc) index.

(*** TLB ***)

Global Program Instance countable_sigT `{Countable A} (P : A → Type)
    {eqdepP : EqDepDecision P} {eqP: ∀ a, EqDecision (P a)}
    {cntP: ∀ a : A, Countable (P a)} : Countable (sigT P) :=
  (inj_countable
     (λ sig, (projT1 sig, encode (projT2 sig)))
     (λ '(a, b),
       bd ← decode b;
       Some $ existT a bd)
     _).
Next Obligation.
  intros.
  cbn.
  setoid_rewrite decode_encode.
  hauto lq:on.
Defined.

Module TLB.
  (* TODO: pair programming to switch to dmaps. *)

  Module NDCtxt.
    Record t (lvl : Level) :=
      make
        {
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
      sauto.
    Qed.
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
  End Entry.
  #[export] Typeclasses Transparent Entry.t.

  (* Full Entry *)
  Module FE.
    Definition t := { ctxt : Ctxt.t & Entry.t (Ctxt.lvl ctxt) }.
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

    #[global] Instance union : Union t := fun x y => hmap2 (fun _ => (∪ₘ)) x y.
  End VATLB.

  Record t :=
    make {
        vatlb : VATLB.t
      }.

  Definition init := make VATLB.init.

  Definition read_sreg (tlb : t) (ts : TState.t) (time : view) (sreg : reg) :=
    TState.read_sreg_at ts sreg time.



  (* Program Definition va_fill_lvl0 (tlb : t) (ts : TState.t) *)
  (*   (init : Memory.initial) *)
  (*   (mem : Memory.t) (time : nat) : VATLB.t := *)
  (*   tlb.(vatlb) ∪ *)
  (*     fun ctxt => *)
  (*       match ctxt.(Ctxt.lvl) with *)
  (*       | 0%fin => *)
  (*           match ctxt.(Ctxt.asid) return gset (Entry.t ctxt.(Ctxt.lvl)) with *)
  (*           | Some asid => *)
  (*               ( *)
  (*                 let valttbrs := *)
  (*                   (* read_sreg tlb ts time (Reg.TTBR0 0%fin) *) *)
  (*                   (* |> List.filter (fun '(val,v) => bv_extract 48 16 val =? asid) *) *)
  (*                   [] *)
  (*                 in *)
  (*                 valttbr ← valttbrs; *)
  (*                 let root_addr := *)
  (*                   bv_concat 64 (bv_0 16) (bv_extract 0 48 valttbr) in *)
  (*                 root_loc ← Loc.from_va root_addr |> option_list; *)
  (*                 let loc := next_entry_loc root_loc ctxt.(Ctxt.va) in *)
  (*                 let '(val, _) := Memory.read_at loc init mem time in *)
  (*                 [Vector.const val 1] *)
  (*               ) *)
  (*                |> list_to_set *)
  (*           | None => ∅ *)
  (*           end *)
  (*       | _ => ∅ *)
  (*       end. *)





  (** WARNING HACK: Coq is shit so I'm forced to copy paste this function 3
      times, because after 4 hours I didn't find a way to make it type a generic
      version (among various internal crashes and similar errors). *)

  (** Needed to do sensible match case on fin values *)
  Definition fin_case {n : nat} (i : fin (S n)) : option (fin n) :=
    match i with
    | Fin.F1 => None
    | FS n => Some n
    end.

  (* TODO report bug: Function is incompatible with Keyed Unification *)
  #[local] Unset Keyed Unification.

  Fixpoint fin_inj1 {n : nat} (p : fin n) : fin (S n) :=
    match p with
    | Fin.F1 => Fin.F1
    | FS p' => FS (fin_inj1 p')
    end.


  Lemma fin_to_nat_fin_inj1 {n : nat} (p : fin n) : fin_inj1 p =@{nat} p.
    Admitted.

  (* Lemma va_fill_termination {n : nat} (i : fin (S n)) (j : fin n) : *)
  (*   fin_case i = Some j -> (Fin.L 1 j < i)%nat. *)
  (*   inv_fin i. *)

  Set Printing Implicit.
  Set Printing Coercions.

  (* Function va_fill_lvl (tlb : t) (ts : TState.t) *)
  (*   (init : Memory.initial) *)
  (*   (mem : Memory.t) (time : nat) (lvl : Level) {measure fin_to_nat lvl } := *)
  (*   match fin_case lvl return VATLB.t with *)
  (*   | None => VATLB.init *)
  (*   | Some n => *)
  (*       va_fill_lvl tlb ts init mem time (fin_inj1 n) *)
  (*   end *)
  (*   ∪ tlb.(vatlb). *)
  (* Proof. *)
  (*   intros. *)
  (*   inv_fin lvl. *)
  (*   scongruence. *)
  (*   cbn in *. *)
  (*   intros. *)
  (*   inversion teq as []. *)
  (*   destruct H. *)
  (*   rewrite fin_to_nat_fin_inj1. *)
  (*   lia. *)
  (* Qed. *)



  (* Program Fixpoint va_fill_lvl (lvl : Level) {measure (fin_to_nat lvl) } := *)
  (*   fun (tlb : t) (ts : TState.t) *)
  (*   (init : Memory.initial) *)
  (*   (mem : Memory.t) (time : nat) => *)
  (*   match lvl return VATLB.t with *)
  (*   | Fin.F1 => VATLB.init *)
  (*   | FS n => va_fill_lvl (n : Level) tlb ts init mem time *)
  (*   end. *)
  (* Next Obligation. *)
  (*   intros. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (* Admitted. *)

  (* Print va_fill_lvl. *)


  (* Definition va_fill (tlb : t) (ts : TState.t) (init : Memory.initial) *)
  (*   (mem : Memory.t) (time : nat) : VATLB.t. *)
  (* Admitted. *)


  (** Get the TLB state at a certain timestamp *)
  (* Definition get (ts : TState.t) (init : Memory.initial) (mem : Memory.t) *)
  (*               (time : nat) : t. *)
End TLB.

Module VATLB := TLB.VATLB.



(*** Instruction semantics ***)

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
  reads ← Exec.error_none "Reading from unmapped memory" $
            Memory.read loc vread init mem;
  '(res, time) ← mchoosel reads;
  let read_view :=
    if (ts.(TState.fwdb) !! loc) is Some fwd then
      if (fwd.(FwdItem.time) =? time) then read_fwd_view macc fwd else time
    else time in
  let vpost := vpre ⊔ read_view in
  guard_discard (vpost <= invalidation_time)%nat;;
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

(** Run a MemRead outcome.
    Returns the new thread state, the vpost of the read and the read value. *)
Definition run_mem_read (addr : address) (macc : mem_acc) (init : Memory.initial) :
    Exec.t (PPState.t TState.t Ev.t IIS.t) string val :=
  addr ← Exec.error_none "Address not supported" $ Loc.from_addr addr;
  iis ← mget PPState.iis;
  let vaddr := iis.(IIS.strict) in
  if is_explicit macc then
    tres_opt ← mget (IIS.trs ∘ PPState.iis);
    trans_res ← Exec.error_none "Explicit access before translation" tres_opt;
    let invalidation := trans_res.(IIS.TransRes.invalidation) in
    '(view, val) ←
      Exec.liftSt (PPState.state ×× PPState.mem)
        $ read_mem_explicit addr vaddr invalidation macc init;
    mset PPState.iis $ IIS.add view;;
    mret val
  else if is_ttw macc then
    ts ← mget PPState.state;
    tres_option ← mget (IIS.trs ∘ PPState.iis);
    tres ← Exec.error_none "TTW read before translation start" tres_option;
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
    loc ← Exec.error_none "Address not supported" $ Loc.from_addr aligned_addr;
    mem ← mGet;
    block ← Exec.error_none "Modified instruction memory"
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
  mset (TState.prom ∘ fst) $ delete time;;
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
      guard_or
        "Non trivial write reg access types unsupported"
        (bool_decide (racc ≠ None));;
      iis ← mget PPState.iis;
      let vreg := IIS.strict iis in
      vreg' ←
        (if reg =? pc_reg
         then
           mset PPState.state $ TState.update TState.vspec vreg;;
           mret 0%nat
         else mret vreg);
      if decide (reg ∈ relaxed_regs) then
        mthrow "TODO"
      else
        ts ← mget PPState.state;
        nts ← Exec.error_none "Register isn't mapped, can't write" $
                TState.set_reg reg (val, vreg') ts;
        msetv PPState.state nts
  | RegRead reg direct => mthrow "TODO"
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
      addr ← Exec.error_none "Address not supported" $ Loc.from_addr addr;
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
