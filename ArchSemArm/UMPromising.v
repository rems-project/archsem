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
From Stdlib Require Import Eqdep_dec.

From ArchSem Require Import GenPromising.
Require Import ArmInst.

#[local] Open Scope stdpp.

(** The goal of this module is to define an User-mode promising model
    with mixed-size support on top of the new interface *)


(** A message in the promising model memory.  [size] is a field (not a
    parameter) so that [Ev.t = Msg.t] is a plain [Set] and all messages
    can live in one list. *)
Module Msg.
  Record t :=
    make {
      size : N;
      tid : nat;
      addr : address;
      val : bv (8 * size);
    }.

  (** Warning: this instance does not reduce under [vm_compute] because
      the dependent [val] field requires proof terms that get stuck on
      opaque bitvector lemmas.  Use [Ev.eqb] instead for computation. *)
  #[global] Instance eq_dec : EqDecision t.
  Proof.
    intros [s1 t1 l1 v1] [s2 t2 l2 v2].
    destruct (decide (s1 = s2)) as [<- | Hne];
      [| right; intros H; apply Hne; exact (f_equal size H)].
    destruct (decide (t1 = t2)) as [<- | Hne];
      [| right; intros H; apply Hne; exact (f_equal tid H)].
    destruct (decide (l1 = l2)) as [<- | Hne];
      [| right; intros H; apply Hne; exact (f_equal addr H)].
    destruct (decide (v1 = v2)) as [<- | Hne].
    - left. reflexivity.
    - right. intros H. apply Hne. injection H.
      exact (Eqdep_dec.inj_pair2_eq_dec N (decide_rel (=)) _ s1 v1 v2).
  Defined.
End Msg.

(** Events are just messages — no sigma type wrapper. *)
Module Ev.
  Definition t := Msg.t.
  Definition size : t -> N := Msg.size.
  Definition tid : t -> nat := Msg.tid.
  Definition addr : t -> address := Msg.addr.
  Definition val (ev : t) : bv (8 * size ev) := Msg.val ev.

  #[global] Instance eq_dec : EqDecision t := Msg.eq_dec.

  Definition is_addr_in (l : address) (ev : t) : Prop :=
    let base := addr ev in
    (bv_unsigned base ≤ bv_unsigned l)%Z ∧
    (bv_unsigned l < bv_unsigned base + Z.of_N (size ev))%Z.
  #[global] Instance Decision_is_addr_in (l : address) (ev : t) : Decision (is_addr_in l ev).
  Proof. unfold_decide. Defined.

  (** Boolean equality for use in [vm_compute] paths. *)
  Definition eqb (e1 e2 : t) : bool :=
    (size e1 =? size e2)%N &&
    (tid e1 =? tid e2)%nat &&
    (bv_unsigned (addr e1) =? bv_unsigned (addr e2))%Z &&
    (bv_unsigned (val e1) =? bv_unsigned (val e2))%Z.

End Ev.
#[export] Typeclasses Transparent Ev.t.

(* TODO make naming match current latex definition *)

(** A view is just a natural *)
Definition view := nat.
#[export] Typeclasses Transparent view.
Bind Scope nat_scope with view.
Global Hint Transparent view : core.
Global Hint Unfold view : core.

Module Memory.
  Import PromMemory.

  (** Initial memory is now byte-granular, same as memoryMap *)
  Definition initial := memoryMap.
  #[export] Typeclasses Transparent initial.

  (** Identity conversion: initial memory is already a memoryMap *)
  Definition initial_from_memMap (mem : memoryMap) : initial := mem.

  (** The promising memory: a list of events *)
  Definition t : Type := t Ev.t.
  #[export] Typeclasses Transparent t.

  Definition cut_after : nat -> t -> t := @cut_after Ev.t.
  Definition cut_before : nat -> t -> t := @cut_before Ev.t.

  (** Extract a byte from an event *)
  Definition read_byte (addr : address) (ev : Ev.t) : option (bv 8) :=
    if decide (Ev.is_addr_in addr ev) then
      let offset := Z.to_N (bv_unsigned addr - bv_unsigned (Ev.addr ev)) in
      Some (bv_get_byte 8 offset (Ev.val ev))
    else None.

 (** Reads the last write covering a byte location. Returns the byte value
      and the timestamp of the write. Timestamp is 0 if reading from initial
      memory. *)
  Fixpoint read_last (addr : address) (init : initial) (mem : t)
      : option (bv 8 * nat) :=
    match mem with
    | [] =>
      v ← (init : memoryMap) !! (addr : address);
      Some (v, 0%nat)
    | ev :: mem' =>
        match read_byte addr ev with
        | Some byte => Some (byte, List.length mem)
        | None => read_last addr init mem'
        end
    end.

  (** Reads from initial memory and fail, if the memory has been overwritten
      this will fail.

      This is mainly for instruction fetching in this model *)
  Definition read_initial (addr : address) (init : initial) (mem : t) : option (bv 8) :=
    match read_last addr init mem with
    | Some (v, 0%nat) => Some v
    | _ => None
    end.

  (** Transform a promising initial memory and memory history back to a
      TermModel memoryMap *)
  Definition to_memMap (init : initial) (mem : t) : memoryMap :=
    foldl (λ mm ev, mem_insert_bv (Ev.addr ev) (Ev.val ev) mm) init mem.

  (** Read each byte in a list of locations via read_last.
      Returns None if any byte is unmapped in initial memory and has no
      covering write. *)
  Definition read_bytes_at (addrs : list address) (init : initial) (mem : t) :
      option (list (bv 8 * nat)) :=
    for a in addrs do
      read_last a init mem
    end.

  (** Check whether an event overlaps with the address range [addr, addr+size) *)
  Definition ev_overlaps_range (addr : address) (size : N) (ev : Ev.t) : bool :=
    let ev_end := (bv_unsigned (Ev.addr ev) + Z.of_N (Ev.size ev))%Z in
    let addr_end := (bv_unsigned addr + Z.of_N size)%Z in
    negb ((ev_end <=? bv_unsigned addr)%Z || (addr_end <=? bv_unsigned (Ev.addr ev))%Z).

  (** Returns the list of possible multi-byte reads at a location range
      restricted by a certain view.

      Picks a single timestamp, then reads all bytes from the memory
      snapshot at that time.  The candidate timestamps are [v] itself
      plus every overlapping write after [v].
      Each snapshot is a list of per-byte (value, write_timestamp) pairs.
      Returns None if any byte is not mapped in initial memory. *)
  Definition read_size (addr : address) (size : N) (v : view) (init : initial)
      (mem : t) : option (list (list (bv 8 * nat))) :=
    let addrs := addr_range addr size in
    (* Timestamps of writes after v that overlap with the read range *)
    let overlapping :=
      mem |> cut_after_with_timestamps v
          |> omap (λ '(ev, t),
              if ev_overlaps_range addr size ev then Some t else None)
    in
    (* Candidate timestamps: v plus all overlapping writes, deduplicated *)
    let candidates := remove_dups (v :: overlapping)%list in
    for t in candidates do
      read_bytes_at addrs init (cut_before t mem)
    end.

  (** Promise a write and add it at the end of memory *)
  Definition promise (ev : Ev.t) (mem : t) : view * t :=
    let nmem := ev :: mem in (List.length nmem, nmem).

  (** Returns a view among a promise set that correspond to a message. The
      oldest matching view is taken. This is because it can be proven that
      taking a more recent view, will make the previous promises unfulfillable
      and thus the corresponding executions would be discarded. TODO prove it.
      *)
  Definition fulfill (ev : Ev.t) (prom : list view) (mem : t) : option view :=
    prom |> List.filter (λ t,
              match mem !! t with
              | Some ev' => Ev.eqb ev ev'
              | None => false
              end)
         |> reverse
         |> head.

  (** Check that no write overlapping [addr, addr+size) has been made by any
      thread other than [tid] since view [v].  This is the exclusive-monitor
      interference check: if another thread wrote to any byte in the monitored
      range between the load-exclusive and store-exclusive, the exclusive
      must fail. *)
  Definition exclusive (tid : nat) (addr : address) (size : N)
      (v : view) (mem : t) : bool :=
    mem |> cut_after v
        |> forallb (λ ev, (Ev.tid ev =? tid)
                          || negb (ev_overlaps_range addr size ev)).

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

  (** Sets the coherence view of an address *)
  Definition set_coh (addr : address) (v : view) : t -> t :=
    set coh (insert addr v).

  (** Updates the coherence view of an address by taking the max of the new
      view and of the existing value *)
  Definition update_coh (addr : address) (v : view) (ts : t) : t :=
    set_coh addr (max v (ts.(coh) !!! addr)) ts.

  (** Updates the forwarding database for an address. *)
  Definition set_fwdb (addr : address) (fi : FwdItem.t) : t -> t :=
    set fwdb (insert addr fi).

  (** Set the exclusive database to the timestamp and view of the latest
      load exclusive *)
  Definition set_xclb (vs : view * view * N * address) : t -> t :=
    set xclb (λ _, Some vs).

  (** Clear the exclusive database, to mark a store exclusive *)
  Definition clear_xclb : t -> t :=
    set xclb (λ _, None).

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
  Definition promise (v : view) : t -> t := set prom (v ::.).
End TState.

(*** Instruction semantics ***)

Definition view_if (b : bool) (v : view) := if b then v else 0%nat.

(** The view of a read from a forwarded write *)
Definition read_fwd_view (macc : mem_acc) (f : FwdItem.t) :=
  if f.(FwdItem.xcl) && is_rel_acq macc
  then f.(FwdItem.time) else f.(FwdItem.view).

(** Per-byte forwarding view: if this byte was forwarded from a local
    store (fwdb entry timestamp matches the byte's read timestamp), use
    the forwarding view; otherwise use the write's timestamp directly.
    This supports partial forwarding: some bytes may forward from a local
    store while others are read from memory. *)
Definition byte_fwd_view (macc : mem_acc) (ts : TState.t) (a : address)
    (time_i : nat) : view :=
  match ts.(TState.fwdb) !! a with
  | Some fwd_i =>
      if fwd_i.(FwdItem.time) =? time_i
      then read_fwd_view macc fwd_i
      else time_i
  | None => time_i
  end.

(** Reads a 4-byte instruction from initial memory.
    Fails if any byte has been overwritten (no self-modifying code). *)
Definition read_imem (addr : address)
           (init : Memory.initial) (mem : Memory.t) :
    Exec.t TState.t string (bv 32) :=
  bytes ← othrow "Modified instruction memory" $
    for a in addr_range addr 4 do Memory.read_initial a init mem end;
  mret (bv_of_bytes 32 bytes).

(** Performs a multi-byte memory read.  Picks a single timestamp
    t >= vread, then reads each byte from the most recent write
    covering it at or before t. *)
Definition read_mem (addr : address) (size : N) (vaddr : view) (macc : mem_acc)
           (init : Memory.initial) (mem : Memory.t) :
    Exec.t TState.t string (view * bv (8 * size)) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  let addrs := addr_range addr size in
  ts ← mGet;
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
                (* SC Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  (* Per-byte coherence: vread = vpre ⊔ max(coh[byte] for byte in range) *)
  let vread := fold_right max vpre (map (λ l : address, ts.(TState.coh) !!! l) addrs) in
  (* Non-deterministically choose a snapshot *)
  snapshots ← othrow "Reading from unmapped memory" $
    Memory.read_size addr size vread init mem;
  byte_reads ← mchoosel snapshots;
  let byte_vals := map fst byte_reads in
  let byte_times := map snd byte_reads in
  let res : bv (8 * size) := bv_of_bytes (8 * size) byte_vals in
  let max_time := fold_right max 0%nat byte_times in
  (* Per-byte forwarding: each byte independently checks its fwdb entry.
     Partial forwarding is allowed — forwarded bytes contribute their
     forwarding view, non-forwarded bytes contribute their timestamp. *)
  let read_view :=
    fold_right max 0%nat
      (map (λ '(a, time_i), byte_fwd_view macc ts a time_i)
           (zip addrs byte_times)) in
  let vpost := vpre ⊔ read_view in
  (* Update per-byte coherence *)
  mapM (λ '(a, (_, time_i)), mSet $ TState.update_coh a time_i)
       (zip addrs byte_reads);;
  mSet $ TState.update TState.vrd vpost;;
  mSet $ TState.update TState.vacq (view_if (is_rel_acq macc) vpost);;
  mSet $ TState.update TState.vcap vaddr;;
  ( if is_exclusive macc
    then mSet $ TState.set_xclb (max_time, vpost, size, addr)
    else mret ());;
  mret (vpost, res).

(** Performs a memory write for a thread tid at address addr with view
    vaddr and vdata. Return the new state.

    This may mutate memory if no existing promise can be fullfilled *)
Definition write_mem (tid : nat) (addr : address) (size : N) (vdata : view)
           (macc : mem_acc) (mem : Memory.t)
           (data : bv (8 * size)) :
          Exec.t TState.t string (Memory.t * view * option view):=
  let ev : Ev.t := Msg.make size tid addr data in
  let is_release := is_rel_acq macc in
  let addrs := addr_range addr size in
  ts ← mGet;
  let '(time, mem, new_promise) :=
    match Memory.fulfill ev (TState.prom ts) mem with
    | Some t => (t, mem, false)
    | None => (Memory.promise ev mem, true)
    end in
  let vbob :=
    ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
    ⊔ view_if is_release (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  let vpre := vdata ⊔ ts.(TState.vcap) ⊔ vbob in
  (* Per-byte coherence check *)
  let max_coh := fold_right max 0%nat (map (λ l : address, ts.(TState.coh) !!! l) addrs) in
  guard_discard (vpre ⊔ max_coh < time)%nat;;
  mset TState.prom (filter (λ t, t ≠ time));;
  (* Update per-byte coherence *)
  for a in addrs do mSet $ TState.update_coh a time end;;
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
  let xcl := is_exclusive macc in
  let addrs := addr_range addr size in
  if xcl then
    '(mem, time, vpre_opt) ← write_mem tid addr size vdata macc mem data;
    ts ← mGet;
    match TState.xclb ts with
    | None => mdiscard
    | Some (xtime, xview, xsize, xaddr) =>
        if decide (addr = xaddr ∧ size = xsize) then
          (* Address and size match: enforce exclusive monitor ordering.
             The exclusive check uses the LDXR's size because the ARM
             exclusive monitor tracks the range from the load-exclusive. *)
          guard_discard' (Memory.exclusive tid addr xsize xtime (Memory.cut_after time mem));;
          (* Update per-byte fwdb — exclusive forwarding semantics *)
          for a in addrs do
            mSet $ TState.set_fwdb a (FwdItem.make time vdata true)
          end
        else
          (* Address or size mismatch: STXR may succeed or fail
             non-deterministically. Success carries no ordering guarantee
             (behaves like a plain store).  See ARM ARM B2.12. *)
          b ← mchoosef;
          if (b : bool) then
            (* Update per-byte fwdb — plain store semantics (no xcl ordering) *)
            for a in addrs do
              mSet $ TState.set_fwdb a (FwdItem.make time vdata false)
            end
          else mdiscard
    end;;
    mSet TState.clear_xclb;;
    mret (mem, vpre_opt)
  else
    '(mem, time, vpre_opt) ← write_mem tid addr size vdata macc mem data;
    (* Update per-byte fwdb *)
    for a in addrs do
      mSet $ TState.set_fwdb a (FwdItem.make time vdata false)
    end;;
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
      Exec.t (PPState.t TState.t Ev.t IIS.t) string (eff_ret out * option view) :=
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
      let initmem := Memory.initial_from_memMap initmem in
      if is_ifetch macc then
        match size as s return
          Exec.t _ string (result abort (bv (8 * s) * bv 0) * option view) with
        | 4%N =>
          mem ← mget PPState.mem;
          opcode ← Exec.liftSt
            PPState.state (read_imem addr initmem mem);
          mret (Ok (opcode, 0%bv), None)
        | _ => mthrow "Ifetch of size other than 4"
        end
      else if is_explicit macc then
        vaddr ← mget (IIS.strict ∘ PPState.iis);
        mem ← mget PPState.mem;
        '(view, val) ← Exec.liftSt
          PPState.state (read_mem addr size vaddr macc initmem mem);
        mset PPState.iis $ IIS.add view;;
        mret (Ok (val, bv_0 _), None)
      else mthrow "Read is not explicit or ifetch"
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
      Exec.t (PPState.t TState.t Ev.t IIS.t) string (eff_ret out) :=
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
    mEvent := Ev.t;
    mEvent_eqb := Ev.eqb;
    mEvent_tid := Ev.tid;
    handle_outcome := run_outcome;
    emit_promise := λ tid initmem mem ev, TState.promise (length mem);
    check_valid_end := λ _ _ _ _, [];
    memory_snapshot :=
      λ initmem, Memory.to_memMap (Memory.initial_from_memMap initmem);
  |}.

Definition UMPromising_nocert :=
  Promising_to_Modelnc (*certified=*)false UMPromising.

Definition UMPromising_cert :=
  Promising_to_Modelnc (*certified=*)true UMPromising.

Definition UMPromising_exe := Promising_to_Modelc UMPromising.

Definition UMPromising_pf := Promising_to_Modelc_pf UMPromising.
