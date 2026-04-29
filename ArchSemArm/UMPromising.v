(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
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
From ASCommon Require Import Common Exec FMon StateT.

From ArchSem Require Import GenPromising.
Require Import ArmInst.

#[local] Open Scope stdpp.

(** The goal of this module is to define an User-mode promising model
    with mixed-size support on top of the new interface *)


(** A message in the promising model memory.  [size] is a field (not a
    parameter) so that [Msg.t] is a plain [Set] and all messages
    can live in one list. *)
Module Msg.
  Record t :=
    make {
        size : N;
        tid : nat;
        addr : address;
        val : bv (8 * size);
      }.

  #[global] Instance eq_dec : EqDecision t.
  Proof. intros [] []. decide_eq. Defined.

  Definition is_addr_in (a : address) (msg : t) : Prop :=
    let base := addr msg in
    (bv_unsigned base ≤ bv_unsigned a)%Z ∧
    (bv_unsigned a < bv_unsigned base + Z.of_N (size msg))%Z.
  #[global] Instance Decision_is_addr_in (a : address) (msg : t) : Decision (is_addr_in a msg).
  Proof. unfold_decide. Defined.

  (** Extracts a byte from a message *)
  Definition read_byte (a : address) (msg : t) : option (bv 8) :=
    if decide (is_addr_in a msg) then
      let offset := Z.to_N (bv_unsigned a - bv_unsigned (addr msg)) in
      Some (bv_get_byte 8 offset (val msg))
    else None.

  (** Checks whether a message overlaps with the address range [l, l+sz) *)
  Definition overlaps_range (a : address) (sz : N) (msg : t) : bool :=
    let msg_end := (bv_unsigned (addr msg) + Z.of_N (size msg))%Z in
    let addr_end := (bv_unsigned a + Z.of_N sz)%Z in
    negb ((msg_end <=? bv_unsigned a)%Z || (addr_end <=? bv_unsigned (addr msg))%Z).
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

  (** The promising memory: a list of events *)
  Definition t : Type := t Msg.t.
  #[export] Typeclasses Transparent t.

  Definition cut_after : nat -> t -> t := @cut_after Msg.t.
  Definition cut_before : nat -> t -> t := @cut_before Msg.t.

  (** Reads the last write covering a byte location. Returns the byte value
      and the timestamp of the write. Timestamp is 0 if reading from initial
      memory. *)
  Fixpoint read_last (addr : address) (init : memoryMap) (mem : t) : option (bv 8 * nat) :=
    match mem with
    | [] => init !! addr |$> (., 0%nat)
    | msg :: mem' =>
      if Msg.read_byte addr msg is Some byte then
        Some (byte, List.length mem)
      else read_last addr init mem'
    end.

  (** Reads from initial memory and fail, if the memory has been overwritten
      this will fail.

      This is mainly for instruction fetching in this model *)
  Definition read_initial (addr : address) (init : memoryMap) (mem : t) : option (bv 8) :=
    match read_last addr init mem with
    | Some (v, 0%nat) => Some v
    | _ => None
    end.

  (** Transforms a promising initial memory and memory history back to a
      TermModel memoryMap *)
  Definition to_memMap (init : memoryMap) (mem : t) : memoryMap :=
    foldr (λ msg mm, mem_insert_bv (Msg.addr msg) (Msg.val msg) mm) init mem.

  (** Promises a write and adds it at the end of memory *)
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

  (** Checks that no write overlapping [addr, addr+size) has been made by any
      thread other than [tid] since view [v].  This is the exclusive-monitor
      interference check: if another thread wrote to any byte in the monitored
      range between the load-exclusive and store-exclusive, the exclusive
      must fail. *)
  Definition exclusive (tid : nat) (addr : address) (size : N)
      (v : view) (mem : t) : bool :=
    mem |> cut_after v
        |> forallb (λ msg, (Msg.tid msg =? tid)
                          || negb (Msg.overlaps_range addr size msg)).

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

  (** The view of a read from a forwarded write *)
  Definition read_fwd_view (macc : mem_acc) (f : t) :=
    if f.(xcl) && is_rel_acq macc then f.(time) else f.(view).
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
        coh : gmap address view;

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
        fwdb : gmap address FwdItem.t;

        (* Exclusive database. If there was a recent load exclusive but the
           corresponding store exclusive has not yet run, this will contain
           the timestamp, post-view, size, and address of the load exclusive *)
        xclb : option (nat * view * N * address);
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

  (** Extracts a plain register map from the thread state without views.
      This is used to decide if a thread has terminated, and to observe the
      results of the model *)
  Definition reg_map (ts : t) : registerMap :=
    dmap_map (λ _, fst) ts.(regs).

  (** Sets the value of a register *)
  Definition set_reg (reg : reg) (rv : reg_type reg * view) (ts : t) : option t :=
    if decide (is_Some (dmap_lookup reg ts.(regs))) then
      Some $ set regs (dmap_insert reg rv) ts
    else None.

  (** Sets the coherence view of an address *)
  Definition set_coh (addr : address) (v : view) : t -> t :=
    set coh (insert addr v).

  (** Updates the coherence view of an address by taking the max of the new
      view and of the existing value *)
  Definition update_coh (addr : address) (v : view) (ts : t) : t :=
    set_coh addr (max v (ts.(coh) !!! addr)) ts.

  (** Max of coherence views over a list of addresses (starting from 0) *)
  Definition max_cohs (addrs : list address) (ts : t) : view :=
    foldr max 0%nat (map (λ l, ts.(coh) !!! l) addrs).

  (** Updates the coherence view for a list of (address, view) pairs. *)
  Definition update_cohs (avs : list (address * view)) (ts : t) : t :=
    foldr (λ '(a, v), update_coh a v) ts avs.

  (** Updates the forwarding database for an address. *)
  Definition set_fwdb (addr : address) (fi : FwdItem.t) : t -> t :=
    set fwdb (insert addr fi).

  (** Sets the same [FwdItem] for every byte address in a write range. *)
  Definition set_fwdbs (addrs : list address)
      (time : nat) (vdata : view) (xcl : bool) (ts : t) : t :=
    let fi := FwdItem.make time vdata xcl in
    foldr (λ a, set_fwdb a fi) ts addrs.

  (** Sets the exclusive database to the timestamp and view of the latest
      load exclusive *)
  Definition set_xclb (vs : view * view * N * address) : t -> t :=
    setv xclb (Some vs).

  (** Clears the exclusive database, to mark a store exclusive *)
  Definition clear_xclb : t -> t := setv xclb None.

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

  (** Adds a promise to the promise set *)
  Definition promise (v : view) : t -> t := set prom (v ::.).
End TState.


(*** Instruction semantics ***)

Definition view_if (b : bool) (v : view) := if b then v else 0%nat.


(** Reads an instruction from initial memory.
    Fails if size is not 4 or any byte has been overwritten. *)
Definition read_imem (addr : address) (size : N)
           (init : memoryMap) (mem : Memory.t) :
    Exec.t TState.t string (bv (8 * size)) :=
  guard_or "Ifetch of size other than 4" (size =? 4)%N;;
  bytes ← othrow "Modified instruction memory" $
    mapM (λ a, Memory.read_initial a init mem) (addr_range addr size);
  mret (bv_of_bytes _ bytes).

(** Reads a single byte from a memory snapshot with forwarding applied.
    If the observed write's timestamp matches [fwdb]'s entry for the byte,
    the read view is [FwdItem.read_fwd_view] (possibly smaller than
    [twrite]); otherwise the read view is just [twrite]. *)
Definition read_fwd (addr : address) (fwdb : gmap address FwdItem.t)
    (macc : mem_acc) (init : memoryMap) (mem : Memory.t) : option (bv 8 * view * nat) :=
  '(val, twrite) ← Memory.read_last addr init mem;
  let read_view :=
    if fwdb !! addr is Some fwd then
      if (fwd.(FwdItem.time) =? twrite)%nat
      then FwdItem.read_fwd_view macc fwd
      else twrite
    else twrite in
  Some (val, read_view, twrite).

(** Performs a multi-byte memory read.  Picks a candidate read-point
    [tread] (either [vread] itself or the timestamp of a write overlapping
    the range after [vread]), then resolves each byte at [tread] via
    [read_fwd]. *)
Definition read_mem (addr : address) (size : N) (vaddr : view) (macc : mem_acc)
           (init : memoryMap) (mem : Memory.t) :
    Exec.t TState.t string (view * bv (8 * size)) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  let addrs := addr_range addr size in
  ts ← mGet;
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
                (* SC Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  let vread := vpre ⊔ TState.max_cohs addrs ts in
  let affecting_ts :=
    mem |> PromMemory.cut_after_with_timestamps vread
        |> omap (λ '(msg, t),
            if Msg.overlaps_range addr size msg then Some t else None) in
  tread ← mchoosel (remove_dups (vread :: affecting_ts));
  let mem_at_read := Memory.cut_before tread mem in
  resolved ← othrow "Reading from unmapped memory" $
    mapM (λ a, read_fwd a ts.(TState.fwdb) macc init mem_at_read) addrs;
  let '(bytes_views, twrites) := List.split resolved in
  let '(bytes, read_views) := List.split bytes_views in
  let res := bv_of_bytes (8 * size) bytes in
  let read_view := foldr max 0%nat read_views in
  let vpost := vpre ⊔ read_view in
  let tmax := foldr max 0%nat twrites in
  mSet $ TState.update_cohs (zip addrs twrites);;
  mSet $ TState.update TState.vrd vpost;;
  mSet $ TState.update TState.vacq (view_if (is_rel_acq macc) vpost);;
  mSet $ TState.update TState.vcap vaddr;;
  ( if is_exclusive macc
    then mSet $ TState.set_xclb (tmax, vpost, size, addr)
    else mret ());;
  mret (vpost, res).

(** Performs a memory write for a thread [tid] at [addr] with view
    [vdata].  May mutate memory if no existing promise can be fulfilled. *)
Definition write_mem (tid : nat) (addr : address) (size : N) (vdata : view)
           (macc : mem_acc) (mem : Memory.t)
           (data : bv (8 * size)) :
          Exec.t TState.t string (Memory.t * view * option view):=
  let msg : Msg.t := Msg.make size tid addr data in
  let is_release := is_rel_acq macc in
  let addrs := addr_range addr size in
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
  guard_discard (vpre ⊔ TState.max_cohs addrs ts < time)%nat;;
  mset TState.prom (filter (λ t, t ≠ time));;
  mSet $ TState.update_cohs (map (., time) addrs);;
  mSet $ TState.update TState.vwr time;;
  mSet $ TState.update TState.vrel (view_if is_release time);;
  mret (mem, time, (if new_promise then Some vpre else None)).


(** Tries to perform a memory write.

    If the store is not exclusive, the write is always performed and the third
    return value is true.

    If the store is exclusive the write may succeed or fail and the third
    return value indicate the success (true for success, false for error) *)
Definition write_mem_xcl (tid : nat) (addr : address) (size : N)
           (vdata : view) (macc : mem_acc)
           (mem : Memory.t) (data : bv (8 * size))
  : Exec.t TState.t string (Memory.t * option view) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  let addrs := addr_range addr size in
  if is_exclusive macc then
    '(mem, time, vpre_opt) ← write_mem tid addr size vdata macc mem data;
    ts ← mGet;
    match TState.xclb ts with
    | None => mdiscard
    | Some (xtime, _, xsize, xaddr) =>
      if decide (addr = xaddr ∧ size = xsize) then
        guard_discard' (Memory.exclusive tid addr xsize xtime
                         (Memory.cut_after time mem));;
        mSet $ TState.set_fwdbs addrs time vdata true
      else
        mSet $ TState.set_fwdbs addrs time vdata false
    end;;
    mSet TState.clear_xclb;;
    mret (mem, vpre_opt)
  else
    '(mem, time, vpre_opt) ← write_mem tid addr size vdata macc mem data;
    mSet $ TState.set_fwdbs addrs time vdata false;;
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
  | MemRead (MemReq.make macc addr addr_space size 0) =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      if is_ifetch macc then
        mem ← mget PPState.mem;
        opcode ← Exec.liftSt PPState.state (read_imem addr size initmem mem);
        mret (Ok (opcode, 0%bv), None)
      else if is_explicit macc then
        vaddr ← mget (IIS.strict ∘ PPState.iis);
        mem ← mget PPState.mem;
        '(view, val) ← Exec.liftSt
          PPState.state (read_mem addr size vaddr macc initmem mem);
        mset PPState.iis $ IIS.add view;;
        mret (Ok (val, 0%bv), None)
      else mthrow "Read is not explicit nor ifetch"
  | MemRead _ => mthrow "Memory read with tags unsupported"
  | MemWriteAddrAnnounce _ =>
      vaddr ← mget (IIS.strict ∘ PPState.iis);
      mset PPState.state $ TState.update TState.vcap vaddr;;
      mret ((), None)
  | MemWrite (MemReq.make macc addr addr_space size 0) val tags =>
      guard_or "Access outside Non-Secure" (addr_space = PAS_NonSecure);;
      if is_explicit macc then
        mem ← mget PPState.mem;
        vdata ← mget (IIS.strict ∘ PPState.iis);
        '(mem, vpre_opt) ← Exec.liftSt PPState.state
                $ write_mem_xcl tid addr size vdata macc mem val;
        msetv PPState.mem mem;;
        mret (Ok (), vpre_opt)
      else mthrow "Unsupported non-explicit write"
  | MemWrite _ _ _ => mthrow "Memory write with tags unsupported"
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


(** * Implement GenPromising ***)

Import Promising.

Definition UMPromising : Promising.Model :=
  {|tState := TState.t;
    tState_init := λ tid, TState.init;
    tState_regs := TState.reg_map;
    tState_nopromises := is_emptyb ∘ TState.prom;
    iis := IIS.t;
    iis_init := IIS.init;
    address_space := PAS_NonSecure;
    mEvent := Msg.t;
    mEvent_tid := Msg.tid;
    handle_outcome := run_outcome;
    emit_promise := λ tid initmem mem msg, TState.promise (length mem);
    check_valid_end := λ _ _ _ _, [];
    memory_snapshot := Memory.to_memMap;
  |}.

Definition UMPromising_nocert :=
  Promising_to_Modelnc (*certified=*)false UMPromising.

Definition UMPromising_cert :=
  Promising_to_Modelnc (*certified=*)true UMPromising.

Definition UMPromising_exe := Promising_to_Modelc UMPromising.

Definition UMPromising_pf := Promising_to_Modelc_pf UMPromising.
