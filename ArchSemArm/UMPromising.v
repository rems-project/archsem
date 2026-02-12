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

(** Locations in the mixed-size model are byte-granular physical addresses.
    All locations are implicitly in the non-secure world. *)
Module Loc.
  Definition t := address.
  #[export] Typeclasses Transparent t.
  #[export] Hint Transparent t : bv_unfold_db.

  #[global] Instance dec : EqDecision t.
  Proof. unfold t. solve_decision. Defined.

  #[global] Instance count : Countable t.
  Proof. unfold t. exact (bv_countable_compute _). Defined.

  (** Identity: locations are already addresses *)
  Definition to_addr (loc : t) : address := loc.

  (** Convert a physical address back to a 64 bits "virtual" address *)
  Definition to_va (loc : t) : bv 64 :=
    bv_zero_extend 64 loc.

End Loc.


(** Register and memory values (all memory access are 8 bytes aligned *)
Definition sval (size : N) := bv (8 * size).
#[export] Typeclasses Transparent sval.
Definition val := sval 8.
#[export] Typeclasses Transparent val.

(** This is an message in the promising model memory. The location is a physical
    address as virtual memory is ignored by this model *)
Module Msg.
  Record t (size : N) :=
    make {
      tid : nat;
      loc : Loc.t;
      val : sval size;
    }.

  Arguments make {_} _ _.
  Arguments tid {_}.
  Arguments loc {_}.
  Arguments val {_}.

  #[global] Instance eq_dec size : EqDecision (t size).
  Proof. solve_decision. Defined.

  #[global] Instance count size : Countable (t size).
  Proof.
    apply (inj_countable' (λ msg, (tid msg, loc msg, val msg))
                      (λ x, make x.1.1 x.1.2 x.2)).
    by intros [].
  Defined.
End Msg.

Module Ev.
  Definition t := {size : N & Msg.t size}.
  Definition size : t -> N := projT1.
  Definition msg (ev : t) : Msg.t (size ev) := projT2 ev.
  Definition tid (ev : t) : nat := Msg.tid (msg ev).
  Definition loc (ev : t) : Loc.t := Msg.loc (msg ev).
  Definition val (ev : t) : sval (size ev) := Msg.val (msg ev).

  #[global] Instance eq_dec : EqDecision t.
  Proof.
    intros [s1 m1] [s2 m2].
    destruct (decide (s1 = s2)) as [<- | Hne].
    - destruct (decide (m1 = m2)) as [<- | Hne].
      + left. reflexivity.
      + right. intros H. apply Hne.
        exact (Eqdep_dec.inj_pair2_eq_dec N (decide_rel (=)) _ _ _ _ H).
    - right. intros H. apply Hne. exact (f_equal projT1 H).
  Defined.

  Definition is_loc_in (l : Loc.t) (ev : t) : Prop :=
    let base := loc ev in
    (bv_unsigned base ≤ bv_unsigned l)%Z ∧
    (bv_unsigned l < bv_unsigned base + Z.of_N (size ev))%Z.
  #[global] Instance Decision_is_loc_in (l : Loc.t) (ev : t) : Decision (is_loc_in l ev).
  Proof. unfold_decide. Defined.

  (** Boolean equality for events using only computable integer
      comparisons.  Unlike [eq_dec] this never gets stuck under
      [vm_compute] on opaque bitvector proofs. *)
  Definition eqb (e1 e2 : t) : bool :=
    (size e1 =? size e2)%N &&
    (tid e1 =? tid e2)%nat &&
    (bv_unsigned (loc e1) =? bv_unsigned (loc e2))%Z &&
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

  (** Extract a byte from an event: read-byte(w, loc) = w.val[8(loc-w.loc) : 8(loc-w.loc+1)] *)
  Definition read_byte (loc : Loc.t) (ev : Ev.t) : option (bv 8) :=
    if decide (Ev.is_loc_in loc ev) then
      let offset := Z.to_N (bv_unsigned loc - bv_unsigned (Ev.loc ev)) in
      Some (bv_get_byte 8 offset (Ev.val ev))
    else None.

 (** Reads the last write covering a byte location. Returns the byte value
      and the timestamp of the write. Timestamp is 0 if reading from initial
      memory. *)
  Fixpoint read_last (loc : Loc.t) (init : initial) (mem : t)
      : option (bv 8 * nat) :=
    match mem with
    | [] =>
      v ← (init : memoryMap) !! (loc : address);
      Some (v, 0%nat)
    | ev :: mem' =>
        match read_byte loc ev with
        | Some byte => Some (byte, List.length mem)
        | None => read_last loc init mem'
        end
    end.

  (** Reads from initial memory and fail, if the memory has been overwritten
      this will fail.

      This is mainly for instruction fetching in this model *)
  Definition read_initial (loc : Loc.t) (init : initial) (mem : t)
      : option (bv 8) :=
    match read_last loc init mem with
    | Some (v, 0%nat) => Some v
    | _ => None
    end.

  (** Transform a promising initial memory and memory history back to a
      TermModel memoryMap *)
  Definition to_memMap (init : initial) (mem : t) : memoryMap :=
    foldl (λ mm ev, mem_insert_bv (Ev.loc ev) (Ev.val ev) mm) init mem.

  (** Returns the list of possible reads at a byte location restricted by a
      certain view. The list is never empty as one can always read from at least
      the initial value. Returns [None] if the address is not mapped in initial
      memory *)
  Definition read (loc : Loc.t) (v : view) (init : initial) (mem : t)
    : option (list (bv 8 * view)) :=
    first ← mem |> cut_before v |> read_last loc init;
    let lasts := mem |> cut_after_with_timestamps v
                     |> omap (λ '(ev, v),
                        byte ← read_byte loc ev;
                        Some (byte, v))
    in
    Some (lasts ++ [first])%list.

  (** Read each byte in a list of locations via read_last.
      Returns None if any byte is unmapped in initial memory and has no
      covering write. *)
  Definition read_bytes_at (locs : list Loc.t) (init : initial) (mem : t)
      : option (list (bv 8 * nat)) :=
    for loc_i in locs do read_last loc_i init mem end.

  (** Check whether an event overlaps with the address range [addr, addr+size) *)
  Definition ev_overlaps_range (addr : Loc.t) (size : N) (ev : Ev.t) : bool :=
    let ev_end := (bv_unsigned (Ev.loc ev) + Z.of_N (Ev.size ev))%Z in
    let rd_end := (bv_unsigned addr + Z.of_N size)%Z in
    negb ((ev_end <=? bv_unsigned addr)%Z || (rd_end <=? bv_unsigned (Ev.loc ev))%Z).

  (** Returns the list of possible multi-byte reads at a location range
      restricted by a certain view. Uses observation-time semantics:
      pick a single observation timestamp, read all bytes at that time.
      Each snapshot is a list of per-byte (value, write_timestamp) pairs.
      Returns None if any byte is not mapped in initial memory. *)
  Definition read_size (addr : Loc.t) (size : N) (v : view) (init : initial)
      (mem : t) : option (list (list (bv 8 * nat))) :=
    let locs := addr_range addr size in
    (* Events after v that overlap with the read range *)
    let overlapping_timestamps :=
      mem |> cut_after_with_timestamps v
          |> omap (λ '(ev, t),
               if ev_overlaps_range addr size ev then Some t else None)
    in
    (* All observation times: overlapping timestamps + baseline at v *)
    for obs_t in (overlapping_timestamps ++ [v])%list do
      read_bytes_at locs init (cut_before obs_t mem)
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

  (** Check that the write at the provided timestamp is indeed to that location
      and that no write to that location have been made by any other thread *)
  Definition exclusive (loc : Loc.t) (size : N) (v : view) (mem : t) : bool:=
    match mem !! v with
    | None => false
    | Some ev =>
        if (Ev.loc ev =? loc) && (Ev.size ev =? size) then
          let tid := Ev.tid ev in
          mem |> cut_after v
              |> forallb (λ ev, (Ev.tid ev =? tid)
                                || negb (Ev.loc ev =? loc))
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
        xclb : option (nat * view * N);
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
  Definition set_xclb (vs : view * view * N) : t -> t :=
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

(** Check if all bytes in a range can be forwarded from the same store.
    Returns [Some fwd] if all bytes have fwdb entries with the same timestamp
    that matches their read timestamp, [None] otherwise. *)
Definition check_fwd_all (ts : TState.t) (locs : list Loc.t)
    (byte_times : list nat) : option FwdItem.t :=
  match locs, byte_times with
  | loc0 :: _, _ =>
    match ts.(TState.fwdb) !! loc0 with
    | Some fwd0 =>
      if forallb (λ '(loc_i, time_i),
           match ts.(TState.fwdb) !! loc_i with
           | Some fwd_i => (fwd_i.(FwdItem.time) =? fwd0.(FwdItem.time))
                          && (fwd_i.(FwdItem.time) =? time_i)
           | None => false
           end) (zip locs byte_times)
      then Some fwd0
      else None
    | None => None
    end
  | _, _ => None
  end.

(** Performs a multi-byte memory read using observation-time semantics.
    Picks a single observation timestamp t >= vread, then reads each byte
    from the most recent write covering it at or before t. This prevents
    observing torn (partially applied) writes. *)
Definition read_mem (loc : Loc.t) (size : N) (vaddr : view) (macc : mem_acc)
           (init : Memory.initial) (mem : Memory.t) :
    Exec.t TState.t string (view * sval size) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  ts ← mGet;
  let locs := addr_range loc size in
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
                (* SC Acquire loads are ordered after Release stores *)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  (* Per-byte coherence: vread = vpre ⊔ max(coh[byte] for byte in range) *)
  let vread := fold_right max vpre (map (λ l : Loc.t, ts.(TState.coh) !!! l) locs) in
  (* Non-deterministically choose a snapshot from observation-time semantics *)
  snapshots ← othrow "Reading from unmapped memory" $
    Memory.read_size loc size vread init mem;
  byte_reads ← mchoosel snapshots;
  let byte_vals := map fst byte_reads in
  let byte_times := map snd byte_reads in
  let res : sval size := bv_of_bytes (8 * size) byte_vals in
  let max_time := fold_right max 0%nat byte_times in
  (* Forwarding: check if all bytes can forward from the same store *)
  let read_view :=
    match check_fwd_all ts locs byte_times with
    | Some fwd => read_fwd_view macc fwd
    | None => max_time
    end in
  let vpost := vpre ⊔ read_view in
  (* Update per-byte coherence *)
  mapM (λ '(loc_i, (_, time_i)), mSet $ TState.update_coh loc_i time_i)
       (zip locs byte_reads);;
  mSet $ TState.update TState.vrd vpost;;
  mSet $ TState.update TState.vacq (view_if (is_rel_acq macc) vpost);;
  mSet $ TState.update TState.vcap vaddr;;
  ( if is_exclusive macc
    then mSet $ TState.set_xclb (max_time, vpost, size)
    else mret ());;
  mret (vpost, res).

Definition read_mem4 (addr : address) (macc : mem_acc) (init : Memory.initial) :
    Exec.t Memory.t string (bv 32) :=
  if is_ifetch macc then
    mem ← mGet;
    bytes ← othrow "Modified instruction memory" $
      for loc_i in addr_range addr 4 do Memory.read_initial loc_i init mem end;
    mret (bv_of_bytes 32 bytes : bv 32)
  else mthrow "Non-ifetch 4 bytes access".

(** Performs a memory write for a thread tid at a location loc with view
    vaddr and vdata. Return the new state.

    This may mutate memory if no existing promise can be fullfilled *)
Definition write_mem (tid : nat) (loc : Loc.t) (size : N) (vdata : view)
           (macc : mem_acc) (mem : Memory.t)
           (data : sval size) :
          Exec.t TState.t string (Memory.t * view * option view):=
  let msg : Msg.t size := Msg.make tid loc data in
  let ev : Ev.t := existT size msg in
  let is_release := is_rel_acq macc in
  let locs := addr_range loc size in
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
  let max_coh := fold_right max 0%nat (map (λ l : Loc.t, ts.(TState.coh) !!! l) locs) in
  guard_discard (vpre ⊔ max_coh < time)%nat;;
  mset TState.prom (filter (λ t, t ≠ time));;
  (* Update per-byte coherence *)
  for loc_i in locs do mSet $ TState.update_coh loc_i time end;;
  mSet $ TState.update TState.vwr time;;
  mSet $ TState.update TState.vrel (view_if is_release time);;
  mret (mem, time, (if new_promise then Some vpre else None)).


(** Tries to perform a memory write.

    If the store is not exclusive, the write is always performed and the third
    return value is true.

    If the store is exclusive the write may succeed or fail and the third
    return value indicate the success (true for success, false for error) *)
Definition write_mem_xcl (tid : nat) (loc : Loc.t) (size : N)
           (vdata : view) (macc : mem_acc)
           (mem : Memory.t) (data : sval size)
  : Exec.t TState.t string (Memory.t * option view) :=
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  let xcl := is_exclusive macc in
  let locs := addr_range loc size in
  if xcl then
    '(mem, time, vpre_opt) ← write_mem tid loc size vdata macc mem data;
    ts ← mGet;
    match TState.xclb ts with
    | None => mdiscard
    | Some (xtime, xview, xsize) =>
        guard_discard' (Memory.exclusive loc xsize xtime (Memory.cut_after time mem))
    end;;
    (* Update per-byte fwdb *)
    for loc_i in locs do
      mSet $ TState.set_fwdb loc_i (FwdItem.make time vdata true)
    end;;
    mSet TState.clear_xclb;;
    mret (mem, vpre_opt)
  else
    '(mem, time, vpre_opt) ← write_mem tid loc size vdata macc mem data;
    (* Update per-byte fwdb *)
    for loc_i in locs do
      mSet $ TState.set_fwdb loc_i (FwdItem.make time vdata false)
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
      let loc : Loc.t := addr in
      let initmem := Memory.initial_from_memMap initmem in
      if is_ifetch macc then
        match size as s return
          Exec.t _ string (result abort (bv (8 * s) * bv 0) * option view) with
        | 4%N =>
          opcode ← Exec.liftSt PPState.mem $ read_mem4 addr macc initmem;
          mret (Ok (opcode, 0%bv), None)
        | _ => mthrow "Ifetch of size other than 4"
        end
      else if is_explicit macc then
        vaddr ← mget (IIS.strict ∘ PPState.iis);
        mem ← mget PPState.mem;
        '(view, val) ← Exec.liftSt
          PPState.state (read_mem loc size vaddr macc initmem mem);
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
      let loc : Loc.t := addr in
      if is_explicit macc then
        mem ← mget PPState.mem;
        vdata ← mget (IIS.strict ∘ PPState.iis);
        '(mem, vpre_opt) ← Exec.liftSt PPState.state
                $ write_mem_xcl tid loc size vdata macc mem val;
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

(* Module CProm. *)
(*   Record t := *)
(*     make { *)
(*       proms : list Msg.t; *)
(*     }. *)
(*   #[global] Instance eta : Settable _ := *)
(*     settable! make <proms>. *)

(*   #[global] Instance empty : Empty t := CProm.make []. *)

(*   #[global] Instance union : Union t := λ x y, CProm.make (x.(proms) ++ y.(proms)). *)

(*   Definition init : t := make []. *)

(*   (** Add the latest msg in the mem to the CProm *)
(*       if the corresponding vpre is not bigger than the base *) *)
(*   Definition add_if (mem : Memory.t) (vpre : view) (base : view) (cp : t) : t := *)
(*     if decide (vpre ≤ base)%nat then *)
(*       match mem with *)
(*       | msg :: mem => *)
(*         cp |> set proms (msg ::.) *)
(*       | [] => cp *)
(*       end *)
(*     else cp. *)

(* End CProm. *)

(* Section ComputeProm. *)
(*   Context (tid : nat). *)
(*   Context (initmem : memoryMap). *)
(*   Context (term : registerMap → bool). *)

(*   Definition run_outcome_with_promise *)
(*               (base : view) *)
(*               (out : outcome) : *)
(*         Exec.t (CProm.t * PPState.t TState.t Msg.t IIS.t) string (eff_ret out) := *)
(*     '(res, vpre_opt) ← Exec.liftSt snd $ run_outcome tid initmem out; *)
(*     if vpre_opt is Some vpre then *)
(*       mem ← mget (PPState.mem ∘ snd); *)
(*       mset fst (CProm.add_if mem vpre base);; *)
(*       mret res *)
(*     else *)
(*       mret res. *)

(*   (* Run the thread state until termination, collecting certified promises. *)
(*      Returns true if termination occurs within the given fuel, *)
(*      false otherwise. *) *)
(*   Fixpoint run_to_termination_promise *)
(*                       (isem : iMon ()) *)
(*                       (fuel : nat) *)
(*                       (base : nat) : *)
(*       Exec.t (CProm.t * PPState.t TState.t Msg.t IIS.t) string bool := *)
(*     match fuel with *)
(*     | 0%nat => *)
(*       ts ← mget (PPState.state ∘ snd); *)
(*       mret (term (TState.reg_map ts)) *)
(*     | S fuel => *)
(*       let handler := run_outcome_with_promise base in *)
(*       cinterp handler isem;; *)
(*       ts ← mget (PPState.state ∘ snd); *)
(*       if term (TState.reg_map ts) then *)
(*         mret true *)
(*       else *)
(*         msetv (PPState.iis ∘ snd) IIS.init;; *)
(*         run_to_termination_promise isem fuel base *)
(*     end. *)

(*   Definition run_to_termination (isem : iMon ()) *)
(*                                 (fuel : nat) *)
(*                                 (ts : TState.t) *)
(*                                 (mem : Memory.t) *)
(*       : ExecutablePMResult Msg.t TState.t := *)
(*     let base := List.length mem in *)
(*     let res_proms := Exec.results $ *)
(*       run_to_termination_promise isem fuel base (CProm.init, PPState.Make ts mem IIS.init) in *)
(*     guard_or ("Out of fuel when searching for new promises")%string *)
(*       (∀ r ∈ res_proms, r.2 = true);; *)
(*     let promises := res_proms.*1.*1 |> union_list |> CProm.proms in *)
(*     let tstates := *)
(*       res_proms *)
(*       |> omap (λ '((cp, st), _), *)
(*           if is_emptyb (CProm.proms cp) then Some (PPState.state st) *)
(*           else None) in *)
(*     mret (promises, tstates). *)

(* End ComputeProm. *)

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
