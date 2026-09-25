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

Require Import ArmInst.

#[local] Open Scope stdpp.

(** The goal of this module is to define an User-mode promising model
    with mixed-size support on top of the new interface *)

(* TODO make naming match current latex definition *)

(** A view is just a natural *)
Definition view := nat.
#[export] Typeclasses Transparent view.
Bind Scope nat_scope with view.
Global Hint Transparent view : core.
Global Hint Unfold view : core.

Module Memory.
  Import PromMemory.
  Export (hints) PromMemory.

  (** The promising memory: a list of events *)
  Definition t : Type := t Msg.t.
  #[export] Typeclasses Transparent t.

  Definition promise : Msg.t → Exec.t t string nat := promise.
  Definition fulfill : Msg.t → list nat → t → option nat := fulfill.
  Definition read_from : address → N → memoryMap → t → _ := read_from Some.
  Definition read_all : address → N → memoryMap → t → _ := read_all Some.
  Definition read_initial : address → N → memoryMap → t → _ := read_initial Some.
  Definition to_memMap : memoryMap → t → memoryMap := to_memMap Some.
  Definition exclusive : nat → address → N → nat → nat → t → Prop := exclusive Some.
  #[export] Typeclasses Transparent exclusive.

End Memory.
Import (hints) Memory.

(** A forwarding bank item for a byte, present as soon as this thread wrote that
    byte*)
Module FwdItem.
  Record t :=
    make {
        time : nat; (** The timstamp of the po-lastest write to that byte *)
        view : view; (** When did the write data became available *)
        byte : bv 8; (** The data that was actuall written *)
        xcl_view : option nat (** If relevant, the view of the exclusive read
                                  that matched this write. Implements the new
                                  [[R];rmw;rfi;[A|Q]] rule in [aob]. *)
      }.

  Definition init := make 0 0 0 None.

  (** The view of a read from a forwarded write. If a successful store-exclusive
      is forwarded to an acquire read, include the post-view of its paired
      load-exclusive. Plain reads should only inherit the write-data view. *)
  Definition read_fwd_view (macc : mem_acc) (f : t) :=
    match f.(xcl_view) with
    | Some xv => if is_rel_acq macc then f.(view) ⊔ xv else f.(view)
    | None => f.(view)
    end.
End FwdItem.

(** Data of a load-exclusive: [time] is its external read time and [view] is
    its [vpost]. *)
Module XclItem.
  Record t :=
    make {
        time : nat;
        addr : address;
        size : N;
        view : view
      }.
End XclItem.

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

        (* Forwarding bank. The first view is the timestamp of the
           write while the second view is the max view of the dependencies
           of the write. The optional view records the paired load-exclusive
           post-view for successful store-exclusive forwarding. *)
        fwdb : gmap address FwdItem.t;

        (* The latest unmatched load-exclusive. *)
        xclb : option XclItem.t;
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

  (** Extracts a plain register map from the thread state without views. *)
  Definition reg_map (ts : t) : registerMap :=
    dmap_map (λ _, fst) ts.(regs).

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

  (** Sets the exclusive bank to the footprint of the latest load exclusive. *)
  Definition set_xclb (time : nat) (addr : address) (size : N)
      (vpost : view) : t → t :=
    setv xclb (Some (XclItem.make time addr size vpost)).

  (** Clears the exclusive bank, to mark a store exclusive *)
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

(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  Record t :=
    make {
      strict : view;
      rmw_read : option (nat * bool);
    }.

  #[global] Instance eta : Settable _ :=
    settable! make <strict;rmw_read>.

  Definition init : t := make 0 None.

  (** Add a new view to the IIS *)
  Definition add (v : view) (iis : t) : t :=
    iis |> set strict (max v).

End IIS.


(** * Instruction semantics *)

Definition view_if (b : bool) (v : view) := if b then v else 0%nat.

(** Reads an instruction from initial memory.  Returns the [size]-byte
    instruction word as a [bv (8 * size)] formed by concatenating the
    bytes in [addr_range addr size]. Fails if [size] is not 4, or
    if any byte in the range has been overwritten by a later write. *)
Definition read_ifetch (addr : address) (imem : memoryMap)
    (mem : Memory.t) : Exec.res string (bv 32) :=
  bytes ← mlift $ Memory.read_initial addr 4 imem mem;
  mret (bv_of_bytes 32 bytes).

(** Per-byte forwarding. Forwarding fires when [fwdb !! addr] has an entry [fwd]
    with [fwd.time > tread], which means there is a more recent po-previous
    write that hasn't been propagated yet. In that case we replace the
    byte/view/timestamp with the ones of the forwarded write. The timestamp
    returned (last value) is for coherence checking purposes. Returns [None] if
    no forwarding occurs *)
Definition read_fwd (fwdb : gmap address FwdItem.t) (macc : mem_acc)
    (tread : nat) (addr : address) :
    option (bv 8 * view * nat) :=
  if fwdb !! addr is Some fwd then
    if (tread <? fwd.(FwdItem.time))%nat then
      Some (fwd.(FwdItem.byte), FwdItem.read_fwd_view macc fwd, fwd.(FwdItem.time))
    else None
  else None.

(** Performs a multi-byte memory read. This involves multiple steps:
    - Computing the minimum view
    - Reading main memory at all interesting timestamps with [Memory.read_all]
    - Applying forwarding ([read_fwd])
    - Do a coherence check
    - Update all the views that should be updated
    - If exclusive, set the exclusive bank
    - If atomic RMW, remember this read for the matching write *)
Definition read_mem (addr : address) (size : N) (macc : mem_acc) (imem : memoryMap) :
    Exec.t (PPState.t TState.t Msg.t IIS.t) string (bv (8 * size)) :=
  ts ← mget PPState.state;
  vaddr ← mget (IIS.strict ∘ PPState.iis);
  guard_discard (TState.no_promises_until vaddr ts);;
  let addrs := addr_range addr size in
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
                (* SC Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  mem ← mget PPState.mem;
  candidates ← mlift $ Memory.read_all addr size imem mem vpre;
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
        read_fwd ts.(TState.fwdb) macc tread addr
        |> default (byte, tread, twrite)) $
      zip addrs candidate in

  let bytes := fwd_bytes.*1.*1 in
  let read_views := fwd_bytes.*1.*2 in
  let twrites := fwd_bytes.*2 in
  (* Per-byte coherence: each byte's twrite ≥ that byte's coh view *)
  guard_discard (∀ '(a,t) ∈ zip addrs twrites, (ts.(TState.coh) !!! a ≤ t)%nat);;
  let res := bv_of_bytes (8 * size) bytes in
  let vreads := foldr max 0%nat read_views in
  let vpost := vpre ⊔ vreads in
  mset PPState.state $ TState.update_cohs (zip addrs twrites);;
  mset PPState.state $ TState.update TState.vrd vpost;;
  mset PPState.state $ TState.update TState.vacq (view_if (is_rel_acq macc) vpost);;
  mset PPState.state $ TState.update TState.vcap vaddr;;
  ( if is_exclusive macc
    then mset PPState.state $ TState.set_xclb tread addr size vpost
    else mret ());;
  mset PPState.iis $ IIS.add vpost;;
  mret res.

(** Performs a memory write for a thread [tid] at [addr]:

    - First attempt to fulfill an existing promises, or add a new one otherwise
    - Compute the minimum view of the write
    - Discard if the write is not compatible with that view or coherence checks
    - Discard if the write is supposed to be atomic, but other writes intervened
    - Update all the views that should be updated
    - Set the forwarding bank
    - If a new promise was added, return its minimum view, otherwise [None] *)
Definition write_mem (tid : nat) (addr : address) (size : N) (macc : mem_acc)
    (data : bv (8 * size)) :
    Exec.t (PPState.t TState.t Msg.t IIS.t) string (option view) :=
  let msg := Msg.make tid addr size data in
  let is_release := is_rel_acq macc in
  let addrs := addr_range addr size in
  ts ← mget PPState.state;
  mem ← mget PPState.mem;
  '((time, new_promise) : nat * bool) ←
    match Memory.fulfill msg (TState.prom ts) mem with
    | Some time => mret (time, false)
    | None =>
      time ← Exec.liftSt PPState.mem $ Memory.promise msg;
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
    ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
    ⊔ view_if is_release (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  vdata ← mget (IIS.strict ∘ PPState.iis);
  let vpre := vdata ⊔ ts.(TState.vcap) ⊔ vbob in
  guard_discard (vpre < time ∧ ∀ a ∈ addrs, ts.(TState.coh) !!! a < time)%nat;;
  mset (TState.prom ∘ PPState.state) $ filter (λ t, t ≠ time);;
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
          guard_discard' (Memory.exclusive tid addr size xcl.(XclItem.time) time mem);;
          mret (Some xcl.(XclItem.view))
        else
          (* Address/size mismatch fails the exclusive-monitor check; STXR failure is no-write. *)
          mdiscard
      end
    else mret None;
  mset PPState.state $ TState.set_fwdbs addrs data time vdata fwd_xcl_view;;
  mret (if (new_promise : bool) then Some vpre else None).



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
        size_4 ← guard_or "Ifetch read of size other than 4" (size = 4)%N;
        mem ← mget PPState.mem;
        opcode ← mlift $ read_ifetch addr initmem mem;
        mret (Ok (ctrans _ opcode, 0%bv), None)
      else if is_explicit macc then
        val ← read_mem addr size macc initmem;
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
      guard_or "Only explicit writes are supported" (is_explicit macc);;
      vpre_opt ← write_mem tid addr size macc val;
      mret (Ok (), vpre_opt)
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
  Solve Obligations with lia.

  Definition run_outcome' (out : outcome) :
      Exec.t (PPState.t TState.t Msg.t IIS.t) string (eff_ret out) :=
    run_outcome out |$> fst.

End RunOutcome.


(** * Implement GenPromising ***)

Import Promising.

Definition UMPromising : Promising.Model :=
  {|tState := TState.t;
    tState_init := λ tid mem regs, mret (TState.init mem regs);
    tState_regs := TState.reg_map;
    tState_pc := TState.pc;
    tState_pc_spec := TState.pc_reg_map;
    tState_nopromises := is_emptyb ∘ TState.prom;
    iis := IIS.t;
    iis_init := IIS.init;
    address_space := PAS_NonSecure;
    mEvent := Msg.t;
    mEvent_tid := Msg.tid;
    filter_promises := λ _ _ _ promises, promises;
    handle_outcome := λ _ tid initmem, run_outcome tid initmem;
    emit_promise := λ tid initmem mem msg ts,
      mret $
        if bool_decide (Msg.tid msg = tid) then TState.promise (length mem) ts
        else ts;
    check_valid_end := λ _ _ _ _, [];
    memory_snapshot := Memory.to_memMap;
  |}.

Definition UMPromising_nocert :=
  Promising_to_Modelnc UMPromising.

Definition UMPromising_exe := Promising_to_Modelc UMPromising.

Definition UMPromising_pf := Promising_to_Modelc_pf UMPromising.

Definition UMPromising_opmodel (isem : iMon ()) (n : nat) : opModel n :=
  CPState.opmodel isem UMPromising.

Definition UMPromising_opmodel_pf (isem : iMon ()) (n : nat) : opModel n :=
  CPState.opmodel_pf isem UMPromising.
