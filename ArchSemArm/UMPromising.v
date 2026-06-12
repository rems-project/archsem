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

  (** Extracts a byte from a message *)
  Definition read_byte (a : address) (msg : t) : option (bv 8) :=
    if decide (addr_in_range (addr msg) (size msg) a) then
      let offset := Z.to_N (bv_unsigned a - bv_unsigned (addr msg)) in
      Some (bv_get_byte 8 offset (val msg))
    else None.
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

  Definition cut_after : nat → t → t := @cut_after Msg.t.
  Definition cut_before : nat → t → t := @cut_before Msg.t.

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

  (** Reads [size] bytes starting at [addr] from the memory state at
      timestamp [tread]. Returns each byte paired with its actual
      write-timestamp [twrite], or [None] if any byte is unmapped. *)
  Definition read_from (addr : address) (size : N) (tread : nat)
      (init : memoryMap) (mem : t) : option (list (bv 8 * nat)) :=
    let snap := cut_before tread mem in
    for a in addr_range addr size do
      read_last a init snap
    end.

  (** Transforms an initial memory map and a promising memory history back
      to a memoryMap *)
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
      (v : view) (mem : t) : Prop :=
    ∀ msg ∈ (cut_after v mem),
      addr_overlap addr size (Msg.addr msg) (Msg.size msg) →
      Msg.tid msg = tid.

  #[global] Instance exclusive_dec tid addr size v mem :
      Decision (exclusive tid addr size v mem).
  Proof. unfold exclusive. apply _. Defined.

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
           the timestamp, address, and size of the load exclusive *)
        xclb : option (nat * address * N);
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
  Definition set_coh (addr : address) (v : view) : t → t :=
    set coh (insert addr v).

  (** Updates the coherence view of an address by taking the max of the new
      view and of the existing value *)
  Definition update_coh (addr : address) (v : view) (ts : t) : t :=
    set_coh addr (max v (ts.(coh) !!! addr)) ts.

  (** Updates the coherence view for a list of (address, view) pairs. *)
  Definition update_cohs (avs : list (address * view)) (ts : t) : t :=
    foldr (λ '(a, v), update_coh a v) ts avs.

  (** Updates the forwarding database for an address. *)
  Definition set_fwdb (addr : address) (fi : FwdItem.t) : t → t :=
    set fwdb (insert addr fi).

  (** Sets the same [FwdItem] for every byte address in a write range. *)
  Definition set_fwdbs (addrs : list address)
      (time : nat) (vdata : view) (xcl : bool) (ts : t) : t :=
    let fi := FwdItem.make time vdata xcl in
    foldr (λ a, set_fwdb a fi) ts addrs.

  (** Sets the exclusive database to the footprint of the latest load
      exclusive. *)
  Definition set_xclb (time : nat) (addr : address) (size : N) : t → t :=
    setv xclb (Some (time, addr, size)).

  (** Clears the exclusive database, to mark a store exclusive *)
  Definition clear_xclb : t → t := setv xclb None.

  (** Updates a view that from the state, by taking the max of new value and
      the current value.

      For example `update rmax vnew t` does t.rmax <- max t.rmax vnew *)
  Definition update (acc : t → view) {_: Setter acc}
             (v : view) : t → t :=
    set acc (max v).

  (** Updates two view in the same way as update. Purely for convenience *)
  Definition update2 (acc1 acc2 : t → view) {_: Setter acc1} {_: Setter acc2}
             (v : view) : t → t :=
    (update acc1 v) ∘ (update acc2 v).

  (** Adds a promise to the promise set *)
  Definition promise (v : view) : t → t := set prom (v ::.).

  Definition no_promises_until (v : view) (ts : t) : Prop :=
    ∀ p ∈ ts.(prom), (v < p)%nat.
  #[global] Instance Decision_no_promises_until (v : view) (ts : t) :
      Decision (no_promises_until v ts).
  Proof. unfold_decide. Defined.
End TState.


(*** Instruction semantics ***)

Definition view_if (b : bool) (v : view) := if b then v else 0%nat.

(** Interesting timestamps are [vpre] itself and any later timestamp whose
    write overlaps [addr, addr+size). *)
Definition read_candidates (addr : address) (size : N) (vpre : view)
    (mem : Memory.t) : list nat :=
  PromMemory.cut_after_with_timestamps vpre mem
    |> omap (λ '(msg, t),
              if decide (addr_overlap addr size (Msg.addr msg) (Msg.size msg))
              then Some t else None)
    |> cons vpre.

(** Reads an instruction from initial memory.  Returns the [size]-byte
    instruction word as a [bv (8 * size)] formed by concatenating the
    bytes in [addr_range addr size]. Fails if [size] is not 4, or
    if any byte in the range has been overwritten by a later write. *)
Definition read_imem (addr : address) (size : N)
           (init : memoryMap) (mem : Memory.t) :
    Exec.t TState.t string (bv (8 * size)) :=
  guard_or "Ifetch of size other than 4" (size =? 4)%N;;
  bytes ← othrow "Modified instruction memory" $
    for a in addr_range addr size do
      Memory.read_initial a init mem
    end;
  mret (bv_of_bytes _ bytes).

(** Per-byte forwarding (paper math [read-fwd]).  Forwarding fires when
    [fwdb !! a] has an entry [fwd] with [fwd.time > tread], replacing
    the byte/view/timestamp. Otherwise, the byte takes view [tread]. *)
Definition apply_fwd (fwdb : gmap address FwdItem.t) (macc : mem_acc)
    (mem : Memory.t) (tread : nat)
    (a : address) (entry : bv 8 * nat) : Exec.res string (bv 8 * view * nat) :=
  let '(byte, twrite) := entry in
  let default := (byte, tread, twrite) in
  match fwdb !! a with
  | Some fwd =>
    if (tread <? fwd.(FwdItem.time))%nat then
      msg ← othrow "Failed to retrieve forwarded message" (mem !! fwd.(FwdItem.time));
      byte' ← othrow "Failed to read a byte from the message" (Msg.read_byte a msg);
      mret (byte', FwdItem.read_fwd_view macc fwd, fwd.(FwdItem.time))
    else mret default
  | None => mret default
  end.

(** Performs a multi-byte memory read. Picks an interesting timestamp
    [tread] from [read_candidates], then applies per-byte forwarding. *)
Definition read_mem (addr : address) (size : N) (vaddr : view) (macc : mem_acc)
           (init : memoryMap) (mem : Memory.t) :
    Exec.t TState.t string (view * bv (8 * size)) :=
  ts ← mGet;
  guard_discard (TState.no_promises_until vaddr ts);;
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  let addrs := addr_range addr size in
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
                (* SC Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  tread ← mchoosel (read_candidates addr size vpre mem);
  raw_bytes ← othrow "Memory read of unmapped bytes" $
    Memory.read_from addr size tread init mem;
  (* per-byte (value, view, write-timestamp) after forwarding *)
  fwd_bytes ← mlift $
    for (a, raw) in zip addrs raw_bytes do
      apply_fwd ts.(TState.fwdb) macc mem tread a raw
    end;

  let bytes := fwd_bytes.*1.*1 in
  let read_views := fwd_bytes.*1.*2 in
  let twrites := fwd_bytes.*2 in
  (* Per-byte coherence: each byte's twrite ≥ that byte's coh view *)
  guard_discard (∀ '(a,t) ∈ zip addrs twrites, (ts.(TState.coh) !!! a ≤ t)%nat);;
  let res := bv_of_bytes (8 * size) bytes in
  let vreads := foldr max 0%nat read_views in
  let vpost := vpre ⊔ vreads in
  mSet $ TState.update_cohs (zip addrs twrites);;
  mSet $ TState.update TState.vrd vpost;;
  mSet $ TState.update TState.vacq (view_if (is_rel_acq macc) vpost);;
  mSet $ TState.update TState.vcap vaddr;;
  ( if is_exclusive macc
    then mSet $ TState.set_xclb tread addr size
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
  guard_discard
    (vpre < time ∧ ∀ a ∈ addrs, ts.(TState.coh) !!! a < time)%nat;;
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
    | Some (xtime, xaddr, xsize) =>
      if decide (addr = xaddr ∧ size = xsize) then
        guard_discard' (Memory.exclusive tid addr xsize xtime
                         (Memory.cut_after time mem));;
        mSet $ TState.set_fwdbs addrs time vdata true
      else
        (* If the store-exclusive footprint does not exactly match the previous
           load-exclusive footprint, it may still succeed as an ordinary store,
           but without exclusive atomicity guarantees. *)
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
           ts ← mget PPState.state;
           guard_discard (TState.no_promises_until vreg ts);;
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
      ts ← mget PPState.state;
      guard_discard (TState.no_promises_until vaddr ts);;
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
          let vpost := ts.(TState.vrd) ⊔ ts.(TState.vwr) in
          guard_discard (TState.no_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdmb vpost
      | MBReqTypes_Reads (* dmb ld *) =>
          let vpost := ts.(TState.vrd) in
          guard_discard (TState.no_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdmb vpost
      | MBReqTypes_Writes (* dmb st *) =>
          let vpost := ts.(TState.vwr) in
          guard_discard (TState.no_promises_until vpost ts);;
          mset PPState.state $ TState.update TState.vdmbst vpost
      end;;
      mret ((), None)
  | Barrier (Barrier_DSB dsb) => (* dsb: in UM, same as dmb (except dsb st order loads) *)
      ts ← mget PPState.state;
      let vpost :=
        match dsb.(DxB_types) with
        | MBReqTypes_All (* dsb sy *) => ts.(TState.vrd) ⊔ ts.(TState.vwr)
        | MBReqTypes_Reads (* dsb ld *) => ts.(TState.vrd)
        | MBReqTypes_Writes (* dsb st *) => ts.(TState.vwr)
        end in
      guard_discard (TState.no_promises_until vpost ts);;
      mset PPState.state $ TState.update TState.vdmb vpost;;
      mret ((), None)
  | Barrier (Barrier_ISB ()) => (* isb *)
      ts ← mget PPState.state;
      let vpost := TState.vcap ts in
      guard_discard (TState.no_promises_until vpost ts);;
      mset PPState.state $ TState.update TState.visb vpost;;
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
