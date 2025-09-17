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

Require Import Coq.Program.Equality.
From stdpp Require Import decidable.
Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.Exec.
Require Import ASCommon.StateT.
Require Import ASCommon.FMon.

Require Import ArchSem.GenPromising.
Require Import ArmInst.

(** The goal of this module is to define an User-mode promising model,
    without mixed-size on top of the new interface *)

(** This model only works for 8-bytes aligned location, as there
    in no support for mixed-sizes yet. Also all location are
    implicitly in the non-secure world.

    So in order to get the physical address you need to append 3 zeros. *)
Module Loc.
  Definition t := bv 53.
  #[export] Typeclasses Transparent t.
  #[export] Hint Transparent t : bv_unfold_db.

  #[global] Instance dec : EqDecision t.
  Proof. unfold t. solve_decision. Defined.

  (** Convert a location into an ARM physical address *)
  Definition to_addr (loc : t) : address := bv_concat 56 loc (bv_0 3).


  (** Recover a location from an ARM physical address. *)
  Definition from_addr (addr : address) : option t :=
    if bv_extract 0 3 addr =? bv_0 3 then
      Some (bv_extract 3 53 addr)
    else None.

  Lemma to_from_addr (addr : address) (loc : t) :
    from_addr addr = Some loc → to_addr loc = addr.
  Proof.
    unfold from_addr,to_addr in *.
    cdestruct addr,loc |- *** #CDestrMatch.
    bv_solve'.
  Qed.

  Lemma from_to_addr (loc : t) : from_addr (to_addr loc) = Some loc.
    unfold t in *.
    unfold from_addr, to_addr.
    cdestruct |- *** #CDestrMatch; bv_solve'.
  Qed.

  (** Convert a location to a list of covered physical addresses *)
  Definition to_addrs (loc : t) : list address := addr_range (to_addr loc) 8.

  (** Give the location containing a addr *)
  Definition from_addr_in (addr : address) : t := bv_extract 3 53 addr.

  (** Give the index of a addr inside its containing 8-bytes word *)
  Definition addr_index (addr : address) : bv 3 := bv_extract 0 3 addr.

  Lemma from_addr_addr_in addr loc :
    from_addr addr = Some loc → from_addr_in addr = loc.
  Proof. unfold from_addr,from_addr_in. cdestruct |- *** #CDestrMatch. Qed.

  Lemma from_addr_in_to_addrs loc :
    ∀ addr ∈ to_addrs loc, from_addr_in addr = loc.
  Proof.
    unfold from_addr_in, to_addrs, addr_range, addr_addN, to_addr.
    set_unfold.
    cdestruct |- ***.
    unfold t, addr_size in *.
    bv_solve.
  Qed.

  (** Convert a physical address back to a 64 bits "virtual" address *)
  Definition to_va (loc : t) : bv 64 :=
    bv_concat 64 (bv_0 8) $ bv_concat 52 loc (bv_0 3).

  Definition from_va (addr : bv 64) : option t :=
    if bv_extract 0 3 addr =? bv_0 3 then
      Some (bv_extract 3 53 addr)
    else None.

End Loc.
Export (hints) Loc.


(** Register and memory values (all memory access are 8 bytes aligned *)
Definition val := bv 64.
#[export] Typeclasses Transparent val.

(** This is an message in the promising model memory. The location is a physical
    address as virtual memory is ignored by this model *)
Module Msg.
  Record t := make { tid : nat; loc : Loc.t; val : val }.

  #[global] Instance dec : EqDecision t.
  solve_decision.
  Defined.

  #[global] Instance count : Countable t.
  Proof.
    eapply (inj_countable' (fun msg => (tid msg, loc msg, val msg))
                      (fun x => make x.1.1 x.1.2 x.2)).
    abstract sauto.
  Defined.
End Msg.

(* TODO make naming match current latex definition *)

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
  Definition t : Type := t Msg.t.
  #[export] Typeclasses Transparent t.

  Definition cut_after : nat -> t -> t := @cut_after Msg.t.
  Definition cut_before : nat -> t -> t := @cut_before Msg.t.



 (** Reads the last write to a location in some memory. Gives the value and the
     timestamp of the write that it read from.
     The timestamp is 0 if reading from initial memory. *)
  Fixpoint read_last (loc : Loc.t) (init : initial) (mem : t) : option (val * nat) :=
    match mem with
    | [] => init !! loc |$> (., 0%nat)
    | msg :: mem' =>
        if Msg.loc msg =? loc then
          Some (Msg.val msg, List.length mem)
        else read_last loc init mem'
    end.

  (** Reads from initial memory and fail, if the memory has been overwritten
      this will fail.

      This is mainly for instruction fetching in this model *)
  Definition read_initial (loc : Loc.t) (init : initial) (mem : t) : option val :=
    match read_last loc init mem with
    | Some (v, 0%nat) => Some v
    | _ => None
    end.

  (** Transform a promising initial memory and memory history back to a
      TermModel memoryMap *)
  Definition to_memMap (init : initial) (mem : t) : memoryMap:=
    let final :=
      foldl (λ nmem ev, insert ev.(Msg.loc) ev.(Msg.val) nmem) init mem
    in
    map_fold (λ loc (val : bv 64), mem_insert (Loc.to_addr loc) 8 val) ∅ final.

  (** Adds the view number to each message given a view for the last message.
      This is for convenient use with cut_after.

      TODO: it would make sense to make a function that does cut_after
      and this in a single step. *)
  (* Fixpoint with_views_from (v : view) (mem : t) *)
  (*   : list (Msg.t * view) := *)
  (*   match mem with *)
  (*   | [] => [] *)
  (*   | h :: q => (v, h) :: with_views_from (v - 1) q *)
  (*   end. *)

  (** Returns the list of possible reads at a location restricted by a certain
      view. The list is never empty as one can always read from at least the
      initial value. Returns [None] if the address is not mapped in initial
      memory *)
  Definition read (loc : Loc.t) (v : view) (init : initial) (mem : t)
    : option (list (val * view)) :=
    first ← mem |> cut_before v |> read_last loc init;
    let lasts := mem |> cut_after_with_timestamps v
                     |> filter (fun '(msg, v) => Msg.loc msg =? loc)
                     |> map (fun '(msg, v) => (Msg.val msg, v))
    in
    Some (lasts ++ [first])%list.

  (** Promise a write and add it at the end of memory *)
  Definition promise (msg : Msg.t) (mem : t) : view * t :=
    let nmem := msg :: mem in (List.length nmem, nmem).

  (** Returns a view among a promise set that correspond to a message. The
      oldest matching view is taken. This is because it can be proven that
      taking a more recent view, will make the previous promises unfulfillable
      and thus the corresponding executions would be discarded. TODO prove it.
      *)
  Definition fulfill (msg : Msg.t) (prom : list view) (mem : t) : option view :=
    prom |> filter (λ t, mem !! t = Some msg)
         |> reverse
         |> head.

  (** Check that the write at the provided timestamp is indeed to that location
      and that no write to that location have been made by any other thread *)
  Definition exclusive (loc : Loc.t) (v : view) (mem : t) : bool:=
    match mem !! v with
    | None => false
    | Some msg =>
        if Msg.loc msg =? loc then
          let tid := Msg.tid msg in
          mem |> cut_after v
              |> forallb (fun msg => (Msg.tid msg =? tid)
                                  || negb (Msg.loc msg =? loc))
        else false
    end.

End Memory.
Import (hints) Memory.

Module FwdItem.
   Record t :=
    make {
        time : nat;
        view : view;
        xcl : bool
      }.

   Definition init := make 0 0 false.
End FwdItem.

(** The thread state *)
Module TState.
  Record t :=
    make {
        (* The promises that this thread must fullfil
           Is must be ordered with oldest promises at the bottom of the list *)
        prom : list view;

        (* regs values and views *)
        regs : dmap reg (λ reg, reg_type reg * view)%type;

        (* The coherence views *)
        coh : gmap Loc.t view;


        vrd : view; (* The maximum output view of a read  *)
        vwr : view; (* The maximum output view of a write  *)
        vdmbst : view; (* The maximum output view of a dmb st  *)
        vdmb : view; (* The maximum output view of a dmb ld or dmb sy  *)
        vcap : view; (* The maximum output view of control or address dependency  *)
        visb : view; (* The maximum output view of an isb *)
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
    settable! make <prom;regs;coh;vrd;vwr;vdmbst;vdmb;vcap;visb;vacq;vrel;fwdb;xclb>.

  Definition init (mem : memoryMap) (iregs : registerMap) :=
    ({|
      prom := [];
      regs := dmap_map (λ _ v, (v, 0%nat)) iregs;
      coh := ∅;
      vrd := 0;
      vwr := 0;
      vdmbst := 0;
      vdmb := 0;
      vcap := 0;
      visb := 0;
      vacq := 0;
      vrel := 0;
      fwdb := ∅;
      xclb := None
    |})%nat.

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
  Definition set_coh (loc : Loc.t) (v : view) : t -> t :=
    set coh (insert loc v).

  (** Updates the coherence view of a location by taking the max of the new
      view and of the existing value *)
  Definition update_coh (loc : Loc.t) (v : view) (ts : t) : t :=
    set_coh loc (max v (ts.(coh) !!! loc)) ts.

  (** Updates the forwarding database for a location. *)
  Definition set_fwdb (loc : Loc.t) (fi : FwdItem.t) : t -> t :=
    set fwdb (insert loc fi).

  (** Set the exclusive database to the timestamp and view of the latest
      load exclusive *)
  Definition set_xclb (vs : view * view) : t -> t :=
    set xclb (fun _ => Some vs).

  (** Clear the exclusive database, to mark a store exclusive *)
  Definition clear_xclb : t -> t :=
    set xclb (fun _ => None).

  (** Updates a view that from the state, by taking the max of new value and
      the current value.

      For example `update rmax vnew t` does t.rmax <- max t.rmax vnew *)
  Definition update (acc : t -> view) {_: Setter acc}
             (v : view) : t -> t :=
    set acc (max v).

  (** Updates two view in the same way as update. Purely for convenience *)
  Definition update2 (acc1 acc2 : t -> view) {_: Setter acc1} {_: Setter acc2}
             (v : view) : t -> t :=
    (update acc1 v) ∘ (update acc2 v).

  (** Add a promise to the promise set *)
  Definition promise (v : view) : t -> t := set prom (fun p => v :: p).
End TState.

(*** Instruction semantics ***)

Definition view_if (b : bool) (v : view) := if b then v else 0%nat.

(** The view of a read from a forwarded write *)
Definition read_fwd_view (macc : mem_acc) (f : FwdItem.t) :=
  if f.(FwdItem.xcl) && is_rel_acq macc
  then f.(FwdItem.time) else f.(FwdItem.view).

(** Performs a memory read at a location with a view and return possible output
    states with the timestamp and value of the read *)
Definition read_mem (loc : Loc.t) (vaddr : view) (macc : mem_acc)
           (init : Memory.initial) (mem : Memory.t) :
    Exec.t TState.t string (view * val) :=
  guard_or "Atomic RMV unsupported" (¬ (is_atomic_rmw macc));;
  ts ← mGet;
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
                (* SC Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  let vread := vpre ⊔ (ts.(TState.coh) !!! loc) in
  reads ← othrow "Reading from unmapped memory" $
            Memory.read loc vread init mem;
  '(res, time) ← mchoosel reads;
  let read_view :=
    if (ts.(TState.fwdb) !! loc) is Some fwd then
      if (fwd.(FwdItem.time) =? time) then read_fwd_view macc fwd else time
    else time in
  let vpost := vpre ⊔ read_view in
  mSet $ TState.update_coh loc time;;
  mSet $ TState.update TState.vrd vpost;;
  mSet $ TState.update TState.vacq (view_if (is_rel_acq macc) vpost);;
  mSet $ TState.update TState.vcap vaddr;;
  ( if is_exclusive macc
    then mSet $ TState.set_xclb (time, vpost)
    else mret ());;
  mret (vpost, res).

Definition read_mem4 (addr : address) (macc : mem_acc) (init : Memory.initial) :
    Exec.t Memory.t string (bv 32) :=
  if is_ifetch macc then
    let aligned_addr := bv_unset_bit 2 addr in
    let bit2 := bv_get_bit 2 addr in
    loc ← othrow "Address not supported" $ Loc.from_addr aligned_addr;
    mem ← mGet;
    block ← othrow "Modified instruction memory" (Memory.read_initial loc init mem);
    mret $ (if bit2 then bv_extract 32 32 else bv_extract 0 32) block
  else mthrow "Non-ifetch 4 bytes access".

(** Performs a memory write for a thread tid at a location loc with view
    vaddr and vdata. Return the new state.

    This may mutate memory if no existing promise can be fullfilled *)
Definition write_mem (tid : nat) (loc : Loc.t) (vdata : view)
           (macc : mem_acc) (mem : Memory.t)
           (data : val) : Exec.t TState.t string (Memory.t * view * option view):=
  let msg := Msg.make tid loc data in
  let is_release := is_rel_acq macc in
  ts ← mGet;
  let '(time, mem, new_promise) :=
    match Memory.fulfill msg (TState.prom ts) mem with
    | Some t => (t, mem, false)
    | None => (Memory.promise msg mem, true)
    end in
  let vbob :=
    ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
    ⊔ view_if is_release (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  let vpre := vdata ⊔ ts.(TState.vcap) ⊔ vbob in
  guard_discard (vpre ⊔ (ts.(TState.coh) !!! loc) < time)%nat;;
  mset TState.prom (filter (λ t, t ≠ time));;
  mSet $ TState.update_coh loc time;;
  mSet $ TState.update TState.vwr time;;
  mSet $ TState.update TState.vrel (view_if is_release time);;
  mret (mem, time, (if new_promise then Some vpre else None)).


(** Tries to perform a memory write.

    If the store is not exclusive, the write is always performed and the third
    return value is true.

    If the store is exclusive the write may succeed or fail and the third
    return value indicate the success (true for success, false for error) *)
Definition write_mem_xcl (tid : nat) (loc : Loc.t)
           (vdata : view) (macc : mem_acc)
           (mem : Memory.t) (data : val)
  : Exec.t TState.t string (Memory.t * option view) :=
  guard_or "Atomic RMV unsupported" (¬ (is_atomic_rmw macc));;
  let xcl := is_exclusive macc in
  if xcl then
    '(mem, time, vpre_opt) ← write_mem tid loc vdata macc mem data;
    ts ← mGet;
    match TState.xclb ts with
    | None => mdiscard
    | Some (xtime, xview) =>
        guard_discard' (Memory.exclusive loc xtime (Memory.cut_after time mem))
    end;;
    mSet $ TState.set_fwdb loc (FwdItem.make time vdata true);;
    mSet TState.clear_xclb;;
    mret (mem, vpre_opt)
  else
    '(mem, time, vpre_opt) ← write_mem tid loc vdata macc mem data;
    mSet $ TState.set_fwdb loc (FwdItem.make time vdata false);;
    mret (mem, vpre_opt).

(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  Record t :=
    make {
      strict : view;
    }.

  #[global] Instance eta : Settable _ :=
    settable! make <strict>.

  Definition init : t := make 0.

  (** Add a new view to the IIS *)
  Definition add (v : view) (iis : t) : t :=
    iis |> set strict (max v).

End IIS.


(** Runs an outcome in the promising model while doing the correct view tracking
    and computation. This can mutate memory because it will append a write at
    the end of memory the corresponding event was not already promised. *)
Section RunOutcome.
  Context (tid : nat) (initmem : memoryMap).

  Equations run_outcome (out : outcome) :
      Exec.t (PPState.t TState.t Msg.t IIS.t) string (eff_ret out * option view) :=
  | RegWrite reg racc val =>
      guard_or "Non trivial reg access types unsupported" (racc = None);;
      vreg ← mget (IIS.strict ∘ PPState.iis);
      vreg' ←
        (if reg =? pc_reg
         then
           mset PPState.state $ TState.update TState.vcap vreg;;
           mret 0%nat
         else mret vreg);
      ts ← mget PPState.state;
      nts ← othrow "Register isn't mapped, can't write" $
        TState.set_reg reg (val, vreg') ts;
      msetv PPState.state nts;;
      mret ((), None)
  | RegRead reg racc =>
      guard_or "Non trivial reg access types unsupported" (racc = None);;
      ts ← mget PPState.state;
      '(val, view) ← othrow "Register isn't mapped can't read" $
          dmap_lookup reg ts.(TState.regs);
    mset PPState.iis $ IIS.add view;;
    mret (val, None)
  | MemRead (MemReq.make macc addr addr_space 8 0) =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      loc ← othrow "PA not supported" $ Loc.from_addr addr;
      if is_ifetch macc then
        mthrow "TODO ifetch"
      else if is_explicit macc then
        let initmem := Memory.initial_from_memMap initmem in
        vaddr ← mget (IIS.strict ∘ PPState.iis);
        mem ← mget PPState.mem;
        '(view, val) ← Exec.liftSt
          PPState.state (read_mem loc vaddr macc initmem mem);
        mset PPState.iis $ IIS.add view;;
        mret (Ok (val, bv_0 0), None)
      else mthrow "Read is not explicit or ifetch"
  | MemRead (MemReq.make macc addr addr_space 4 0) => (* ifetch *)
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      let initmem := Memory.initial_from_memMap initmem in
      opcode ← Exec.liftSt PPState.mem $ read_mem4 addr macc initmem;
      mret (Ok (opcode, 0%bv), None)
  | MemRead _ => mthrow "Memory read of size other than 8 and 4"
  | MemWriteAddrAnnounce _ =>
      vaddr ← mget (IIS.strict ∘ PPState.iis);
      mset PPState.state $ TState.update TState.vcap vaddr;;
      mret ((), None)
  | MemWrite (MemReq.make macc addr addr_space 8 0) val tags =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      addr ← othrow "PA not supported" $ Loc.from_addr addr;
      if is_explicit macc then
        mem ← mget PPState.mem;
        vdata ← mget (IIS.strict ∘ PPState.iis);
        '(mem, vpre_opt) ← Exec.liftSt PPState.state
                $ write_mem_xcl tid addr vdata macc mem val;
        msetv PPState.mem mem;;
        mret (Ok (), vpre_opt)
      else mthrow "Unsupported non-explicit write"
  | Barrier (Barrier_DMB dmb) => (* dmb *)
      ts ← mget PPState.state;
      match dmb.(DxB_types) with
      | MBReqTypes_All (* dmb sy *) =>
          mset PPState.state $ TState.update TState.vdmb (ts.(TState.vrd) ⊔ ts.(TState.vwr))
      | MBReqTypes_Reads (* dmb ld *) =>
          mset PPState.state $ TState.update TState.vdmb ts.(TState.vrd)
      | MBReqTypes_Writes (* dmb st *) =>
          mset PPState.state $ TState.update TState.vdmbst ts.(TState.vwr)
      end;;
      mret ((), None)
  | Barrier (Barrier_ISB ()) => (* isb *)
      ts ← mget PPState.state;
    mset PPState.state $ TState.update TState.visb (TState.vcap ts);;
    mret ((), None)
  | GenericFail s => mthrow ("Instruction failure: " ++ s)%string
  | _ => mthrow "Unsupported outcome".

  Definition run_outcome' (out : outcome) :
      Exec.t (PPState.t TState.t Msg.t IIS.t) string (eff_ret out) :=
    run_outcome out |$> fst.

End RunOutcome.

Module CProm.
  Record t :=
    make {
      proms : list Msg.t;
    }.
  #[global] Instance eta : Settable _ :=
    settable! make <proms>.

  #[global] Instance empty : Empty t := CProm.make [].

  #[global] Instance union : Union t := λ x y, CProm.make (x.(proms) ++ y.(proms)).

  Definition init : t := make [].

  (** Add the latest msg in the mem to the CProm
      if the corresponding vpre is not bigger than the base *)
  Definition add_if (mem : Memory.t) (vpre : view) (base : view) (cp : t) : t :=
    if decide (vpre ≤ base)%nat then
      match mem with
      | msg :: mem =>
        cp |> set proms (msg ::.)
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
        Exec.t (CProm.t * PPState.t TState.t Msg.t IIS.t) string (eff_ret out) :=
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
      : Exec.t (CProm.t * PPState.t TState.t Msg.t IIS.t) string bool :=
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
      : Exec.res string Msg.t :=
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
  (mem : Memory.t) := {[ msg | msg.(Msg.tid) = tid]}.
Arguments allowed_promises_nocert _ _ _ _ /.

Definition UMPromising_nocert' : PromisingModel :=
  {|tState := TState.t;
    tState_init := λ tid, TState.init;
    tState_regs := TState.reg_map;
    tState_nopromises := is_emptyb ∘ TState.prom;
    iis := IIS.t;
    iis_init := IIS.init;
    address_space := PAS_NonSecure;
    mEvent := Msg.t;
    handler := run_outcome';
    allowed_promises := allowed_promises_nocert;
    emit_promise := λ tid initmem mem msg, TState.promise (length mem);
    memory_snapshot :=
      λ initmem, Memory.to_memMap (Memory.initial_from_memMap initmem);
  |}.

Definition UMPromising_nocert isem :=
  Promising_to_Modelnc isem UMPromising_nocert'.

(* The certified version only works on simple ISA model without internal
     state *)

Definition seq_step (isem : iMon ()) (tid : nat) (initmem : memoryMap)
  : relation (TState.t * Memory.t) :=
  let handler := run_outcome' tid initmem in
  λ '(ts, mem) '(ts', mem'),
    (ts', mem') ∈
      PPState.state ×× PPState.mem
        <$> (Exec.success_state_list $ cinterp handler isem (PPState.Make ts mem IIS.init)).

Definition allowed_promises_cert (isem : iMon ()) tid (initmem : memoryMap)
    (ts : TState.t) (mem : Memory.t) :=
  {[ msg |
     let ts := TState.promise (length mem) ts in
     let mem := msg :: mem in
     ∃ ts' mem',
       rtc (seq_step isem tid initmem) (ts, mem) (ts', mem') ∧
         TState.prom ts' = []
  ]}.

Definition UMPromising_cert' (isem : iMon ()) : PromisingModel :=
  {|tState := TState.t;
    tState_init := λ tid, TState.init;
    tState_regs := TState.reg_map;
    tState_nopromises := is_emptyb ∘ TState.prom;
    iis := IIS.t;
    iis_init := IIS.init;
    address_space := PAS_NonSecure;
    mEvent := Msg.t;
    handler := run_outcome';
    allowed_promises := allowed_promises_cert isem;
    emit_promise := λ tid initmem mem msg, TState.promise (length mem);
    memory_snapshot :=
      λ initmem, Memory.to_memMap (Memory.initial_from_memMap initmem);
  |}.

Definition UMPromising_cert_nc isem :=
  Promising_to_Modelnc isem (UMPromising_cert' isem).

(** Implement the Executable Promising Model *)

Program Definition UMPromising_exe' (isem : iMon ())
    : BasicExecutablePM :=
  {|pModel := UMPromising_cert' isem;
    promise_select :=
      λ fuel tid term initmem ts mem,
          run_to_termination tid initmem term isem fuel ts mem
  |}.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition UMPromising_cert_c isem fuel :=
  Promising_to_Modelc isem (UMPromising_exe' isem) fuel.
