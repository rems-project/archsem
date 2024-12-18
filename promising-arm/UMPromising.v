(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2022                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aahrus Univeristy                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aahrus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, Univeristy of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, Univeristy of Cambridge                                 *)
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
(*  1. Redistributions of source code must retain the above copyright         *)
(*     notice, this list of conditions and the following disclaimer.          *)
(*                                                                            *)
(*  2. Redistributions in binary form must reproduce the above copyright      *)
(*     notice, this list of conditions and the following disclaimer in the    *)
(*     documentation and/or other materials provided with the distribution.   *)
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
Require Import ASCommon.StateT.
Require Import ASCommon.FMon.
Require Import Coq.Program.Equality.

From stdpp Require Import decidable.

Require Import GenModels.ArmInst.
Require Import GenPromising.
Module ArmGP := Gen Arm ArmTM.
Import ArmGP.

(** The goal of this module is to define an User-mode promising model,
    without mixed-size on top of the new interface *)

(** This model only works for 8-bytes aligned location, as there
    in no support for mixed-sizes yet. Also all location are
    implicitly in the non-secure world.

    So in order to get the physical address you need to append 3 zeros. *)
Module Loc.
  Definition t := bv 49.

  #[global] Instance dec : EqDecision t.
  Proof. unfold t. solve_decision. Defined.

  (** Convert a location into an ARM physical address *)
  Definition to_pa (loc : t) : FullAddress :=
    {|FullAddress_paspace := PAS_NonSecure;
      FullAddress_address := bv_concat 52 loc (bv_0 3)
    |}.

  (** Recover a location from an ARM physical address. *)
  Definition from_pa (pa : FullAddress) : option t :=
    match FullAddress_paspace pa with
    | PAS_NonSecure =>
        let bvaddr := FullAddress_address pa in
        if bv_extract 0 3 bvaddr =? bv_0 3 then
          Some (bv_extract 3 49 bvaddr)
        else None
    | _ => None
    end.

  Lemma to_from_pa (pa : FullAddress) (loc : t) :
    from_pa pa = Some loc -> to_pa loc = pa.
  Proof.
    unfold from_pa,to_pa.
    hauto inv:FullAddress b!:on solve:bv_solve' simp+:f_equal.
 Qed.

  Lemma from_to_pa (loc : t) : from_pa (to_pa loc) = Some loc.
    unfold from_pa, to_pa.
    hauto b!:on solve:bv_solve' simp+:f_equal.
  Qed.

  (** Convert a location to a list of covered physical addresses *)
  Definition to_pas (loc : t) : list FullAddress := pa_range (to_pa loc) 8.

  (** Give the location containing a pa *)
  Definition from_pa_in (pa : FullAddress) : option t :=
    match FullAddress_paspace pa with
    | PAS_NonSecure =>
        let bvaddr := FullAddress_address pa in
          Some (bv_extract 3 49 bvaddr)
    | _ => None
    end.

  (** Give the index of a pa inside its containing 8-bytes word *)
  Definition pa_index (pa : FullAddress) : option (bv 3) :=
    match FullAddress_paspace pa with
    | PAS_NonSecure =>
        let bvaddr := FullAddress_address pa in
          Some (bv_extract 0 3 bvaddr)
    | _ => None
    end.

  Lemma from_pa_pa_in pa loc :
    from_pa pa = Some loc -> from_pa_in pa = Some loc.
    Proof. unfold from_pa,from_pa_in. hauto. Qed.

  Lemma from_pa_in_to_pas loc :
    ∀ pa ∈ to_pas loc, from_pa_in pa = Some loc.
  Proof.
    unfold from_pa_in, to_pas, pa_range.
    set_unfold.
    cdestruct |- **.
    cbn.
    f_equal.
    bv_solve.
  Qed.

  (** Convert a physical address back to a 64 bits "virtual" address *)
  Definition to_va (loc : t) : bv 64 :=
    bv_concat 64 (bv_0 8) $ bv_concat 52 loc (bv_0 3).

  Definition from_va (addr : bv 64) : option t :=
    if bv_extract 0 3 addr =? bv_0 3 then
      Some (bv_extract 3 49 addr)
    else None.

End Loc.


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
  Definition initial := Loc.t -> val.

  (** Convert from a memoryMap to the internal representation: initial *)
  Definition initial_from_memMap (mem : memoryMap) : initial :=
    fun loc => Loc.to_pas loc |> map mem |> bv_of_bytes 64.

  (** The promising memory: a list of events *)
  Definition t : Type := t Msg.t.
  #[export] Typeclasses Transparent t.

  Definition cut_after : nat -> t -> t := @cut_after Msg.t.
  Definition cut_before : nat -> t -> t := @cut_before Msg.t.



 (** Reads the last write to a location in some memory. Gives the value and the
     timestamp of the write that it read from.
     The timestamp is 0 if reading from initial memory. *)
  Fixpoint read_last (loc : Loc.t) (init : initial) (mem : t) : (val * nat) :=
    match mem with
    | [] => (init loc, 0%nat)
    | msg :: mem' =>
        if Msg.loc msg =? loc then
          (Msg.val msg, List.length mem)
        else read_last loc init mem'
    end.

  (** Reads from initial memory and fail, if the memory has been overwritten
      this will fail.

      This is mainly for instruction fetching in this model *)
  Definition read_initial (loc : Loc.t) (init : initial) (mem : t) : option val :=
    match read_last loc init mem with
    | (v, 0%nat) => Some v
    | _ => None
    end.


  (** To a snapshot of the memory back to a memoryMap *)
  Definition to_memMap (init : initial) (mem : t) : memoryMap:=
    fun pa =>
      (loc ← Loc.from_pa_in pa;
      let '(v, _) := read_last loc init mem in
      index ← Loc.pa_index pa;
      bv_to_bytes 8 v !! bv_unsigned index)
        |> default (bv_0 8).

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
      initial value. *)
  Definition read (loc : Loc.t) (v : view) (init : initial) (mem : t)
    : list (val * view) :=
    let first := mem |> cut_before v |> read_last loc init in
    let lasts := mem |> cut_after_with_timestamps v
                     |> filter (fun '(msg, v) => Msg.loc msg =? loc)
                     |> map (fun '(msg, v) => (Msg.val msg, v))
    in
    lasts ++ [first].

  (** Promise a write and add it at the end of memory *)
  Definition promise (msg : Msg.t) (mem : t) : view * t :=
    let nmem := msg :: mem in (List.length nmem, nmem).

  (** Returns a view among a promise set that correspond to a message. The
      oldest matching view is taken. This is because it can be proven that
      taking a more recent view, will make the previous promises unfulfillable
      and thus the corresponding executions would be discarded. TODO prove it.
      *)
  Definition fulfill (msg : Msg.t) (prom : list view) (mem : t) : option view :=
    prom |> filter (fun t => Some msg =? mem !! t)
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
        regs : reg -> regval * view;

        (* The coherence views *)
        coh : Loc.t -> view;


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
        fwdb : Loc.t -> FwdItem.t;

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
      regs := fun reg => (iregs reg, 0);
      coh := fun loc => 0;
      vrd := 0;
      vwr := 0;
      vdmbst := 0;
      vdmb := 0;
      vcap := 0;
      visb := 0;
      vacq := 0;
      vrel := 0;
      fwdb := fun loc => FwdItem.init;
      xclb := None
    |})%nat.

  (** Extract a plain register map from the thread state without views.
      This is used to decide if a thread has terminated, and to observe the
      results of the model *)
  Definition reg_map (ts : t) : registerMap :=
    fun reg => (ts.(regs) reg).1.

  (** Sets the value of a register *)
  Definition set_reg (reg : reg) (rv : (reg_type reg) * view) : t -> t
    := set regs (fun_add reg rv).

  (** Sets the coherence view of a location *)
  Definition set_coh (loc : Loc.t) (v : view) : t -> t :=
    set coh (fun_add loc v).

  (** Updates the coherence view of a location by taking the max of the new
      view and of the existing value *)
  Definition update_coh (loc : Loc.t) (v : view) (s : t) : t :=
    set_coh loc (max v (coh s loc)) s.

  (** Updates the forwarding database for a location. *)
  Definition set_fwdb (loc : Loc.t) (fi : FwdItem.t) : t -> t :=
    set fwdb (fun_add loc fi).

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
Definition read_fwd_view (ak : Explicit_access_kind) (f : FwdItem.t) :=
  if f.(FwdItem.xcl) && negb (ak.(Explicit_access_kind_strength) =? AS_normal)
  then f.(FwdItem.time) else f.(FwdItem.view).

(* (** Read memory from a timestamp. *) *)
(* Definition read_from (init: Memory.initial) (mem : Memory.t) (loc : Loc.t) (tr : nat) := *)
(*   Memory.read_last loc init (Memory.cut_before tr mem). *)


(** Performs a memory read at a location with a view and return possible output
    states with the timestamp and value of the read *)
Definition read_mem (loc : Loc.t) (vaddr : view) (ak : Explicit_access_kind)
           (ts : TState.t) (init : Memory.initial) (mem : Memory.t)
  : Exec.t string (TState.t * view * val) :=
  let acs := ak.(Explicit_access_kind_strength) in
  let acv := ak.(Explicit_access_kind_variety) in
  guard_or "Atomic RMV unsupported" (acv = AV_atomic_rmw);;
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
                (* Strong Acquire loads are ordered after Release stores *)
              ⊔ view_if (acs =? AS_rel_or_acq) ts.(TState.vrel) in
  let vpre := vaddr ⊔ vbob in
  let vread := vpre ⊔ (TState.coh ts loc) in
  '(res, time) ← Exec.Results $ Memory.read loc vread init mem;
  let fwd := TState.fwdb ts loc in
  let read_view :=
    if (fwd.(FwdItem.time) =? time) then read_fwd_view ak fwd else time in
  let vpost := vpre ⊔ read_view in
  let ts :=
    ts |> TState.update_coh loc time
       |> TState.update TState.vrd vpost
       |> TState.update TState.vacq (view_if (negb (acs =? AS_normal)) vpost)
       |> TState.update TState.vcap vaddr
       |> (if acv =? AV_exclusive then TState.set_xclb (time, vpost) else id)
  in mret (ts, vpost, res).

(** Performs a memory write for a thread tid at a location loc with view
    vaddr and vdata. Return the new state.

    This may mutate memory if no existing promise can be fullfilled *)
Definition write_mem (tid : nat) (loc : Loc.t) (vdata : view)
           (acs : Access_strength) (ts : TState.t) (mem : Memory.t)
           (data : val) : Exec.t string (TState.t * Memory.t * view):=
  let msg := Msg.make tid loc data in
  let is_release := acs =? AS_rel_or_acq in
  let '(time, mem) :=
    match Memory.fulfill msg (TState.prom ts) mem with
    | Some t => (t, mem)
    | None => Memory.promise msg mem
    end in
  let vbob :=
    ts.(TState.vdmbst) ⊔ ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
    ⊔ view_if is_release (ts.(TState.vrd) ⊔ ts.(TState.vwr)) in
  let vpre := vdata ⊔ ts.(TState.vcap) ⊔ vbob in
  guard_discard (vpre ⊔ (TState.coh ts loc) < time)%nat;;
  let ts :=
    ts |> set TState.prom (delete time)
       |> TState.update_coh loc time
       |> TState.update TState.vwr time
       |> TState.update TState.vrel (view_if is_release time)
  in mret (ts, mem, time).


(** Tries to perform a memory write.

    If the store is not exclusive, the write is always performed and the third
    return value is true.

    If the store is exclusive the write may succeed or fail and the third
    return value indicate the success (true for success, false for error) *)
Definition write_mem_xcl (tid : nat) (loc : Loc.t)
           (vdata : view) (ak : Explicit_access_kind) (ts : TState.t)
           (mem : Memory.t) (data : val)
  : Exec.t string (TState.t * Memory.t):=
  let acs := Explicit_access_kind_strength ak in
  let acv := Explicit_access_kind_variety ak in
  guard_or "Atomic RMV unsupported" (acv = AV_atomic_rmw) ;;
  let xcl := acv =? AV_exclusive in
  if xcl then
    '(ts, mem, time) ← write_mem tid loc vdata acs ts mem data;
    match TState.xclb ts with
    | None => mdiscard
    | Some (xtime, xview) =>
        guard_discard' (Memory.exclusive loc xtime (Memory.cut_after time mem))
    end;;
    (* let ts := TState.set_fwdb loc (FwdItem.make time (vaddr ⊔ vdata) true) ts in *)
    mret (TState.clear_xclb ts, mem)
  else
    '(ts, mem, time) ← write_mem tid loc vdata acs ts mem data;
    let ts := TState.set_fwdb loc (FwdItem.make time vdata false) ts in
    mret (ts, mem).

(** Intra instruction state for propagating views inside an instruction *)
Module IIS.

  Record t := make { strict : view }.

  #[global] Instance eta : Settable _ :=
    settable! make <strict>.

  Definition init : t := make 0.

  (** Add a new view to the IIS *)
  Definition add (v : view) (iis : t) : t :=
    iis |> set strict (max v).

End IIS.

(** Runs an outcome. *)
Definition run_outcome (tid : nat) (initmem : memoryMap) (out : outcome) :
   stateT (TState.t * Memory.t * IIS.t) (Exec.t string) (eff_ret out) := λ '(ts, mem, iis),
  let initmem := Memory.initial_from_memMap initmem in
  match out with
  | RegWrite reg racc val =>
      guard_or "Non trivial reg access types unsupported" (racc ≠ None);;
      let vreg := iis.(IIS.strict) in
      let ts :=
        if decide (reg = pc_reg) then
          ts
          |> TState.update TState.vcap vreg
          |> TState.set_reg reg (val, 0%nat)
        else TState.set_reg reg (val, vreg) ts
      in
      mret (ts, mem, iis, ())
  | RegRead reg racc =>
      guard_or "Non trivial reg access types unsupported" (racc ≠ None);;
      let (val, view) := ts.(TState.regs) reg in
      let iis := IIS.add view iis in
      mret (ts, mem, iis, val)
  | MemRead 8 rr =>
      addr ← Exec.error_none "PA not supported" $ Loc.from_pa rr.(ReadReq.pa);
      let vaddr := iis.(IIS.strict) in
      match rr.(ReadReq.access_kind) with
      | AK_explicit eak =>
          '(ts, view, val) ← read_mem addr vaddr eak ts initmem mem;
          mret (ts, mem, IIS.add view iis, inl (val, None))
      | AK_ifetch () => mthrow "TODO ifetch"
      | _ => mthrow "Only ifetch and explicit accesses supported"
      end
  | MemRead _ _ => mthrow "Memory read of size other than 8"
  | MemWriteAddrAnnounce _ _ _ _ =>
      let vaddr := iis.(IIS.strict) in
      let ts := TState.update TState.vcap vaddr ts in
      mret (ts, mem, iis, ())
  | MemWrite 8 wr =>
      addr ← Exec.error_none "PA not supported" $ Loc.from_pa wr.(WriteReq.pa);
      let data := wr.(WriteReq.value) in
      let vdata := iis.(IIS.strict) in
      match wr.(WriteReq.access_kind) with
      | AK_explicit eak =>
          '(ts, mem) ← write_mem_xcl tid addr vdata eak ts mem data;
          mret (ts, mem, iis, inl true)
      | AK_ifetch () => mthrow "Write of type ifetch ???"
      | AK_ttw () => mthrow "Write of type TTW ???"
      | _ => mthrow "Unsupported non-explicit write"
      end
  | Barrier (Barrier_DMB dmb) => (* dmb *)
      match dmb.(DxB_types) with
      | MBReqTypes_All (* dmb sy *) =>
          let ts :=
            TState.update TState.vdmb (ts.(TState.vrd) ⊔ ts.(TState.vwr)) ts in
          mret (ts, mem, iis, ())
      | MBReqTypes_Reads (* dmb ld *) =>
          let ts := TState.update TState.vdmb ts.(TState.vrd) ts in
          mret (ts, mem, iis, ())
      | MBReqTypes_Writes (* dmb st *) =>
          let ts := TState.update TState.vdmbst ts.(TState.vwr) ts in
          mret (ts, mem, iis, ())
      end
  | Barrier (Barrier_ISB ()) => (* isb *)
      let ts := TState.update TState.visb (TState.vcap ts) ts in
      mret (ts, mem, iis, ())
  | GenericFail s => mthrow ("Instruction failure: " ++ s)%string
  | _ => mthrow "Unsupported outcome"
  end.

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
    mEvent := Msg.t;
    handler := run_outcome;
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
  let handler := run_outcome tid initmem in
  λ tsmem tsmem',
    tsmem' ∈ (cinterp handler isem (tsmem, IIS.init) |$> fst ∘ fst).

Definition allowed_promises_cert (isem : iMon ()) tid (initmem : memoryMap)
    (ts : TState.t) (mem : Memory.t) :=
  {[ msg |
     let ts := TState.promise (length mem) ts in
     let mem := msg :: mem in
     ∃ ts' mem',
       rtc (seq_step isem tid initmem) (ts, mem) (ts', mem') ∧
         TState.prom ts' = []
  ]}.


Definition UMPromising_cert' (isem : iMon ()) : PromisingModel  :=
  {|tState := TState.t;
    tState_init := λ tid, TState.init;
    tState_regs := TState.reg_map;
    tState_nopromises := is_emptyb ∘ TState.prom;
    iis := IIS.t;
    iis_init := IIS.init;
    mEvent := Msg.t;
    handler := run_outcome;
    allowed_promises := allowed_promises_cert isem;
    emit_promise := λ tid initmem mem msg, TState.promise (length mem);
    memory_snapshot :=
      λ initmem, Memory.to_memMap (Memory.initial_from_memMap initmem);
  |}.

(* Definition UMPromising_cert isem := Promising_to_Modelnc UMPromising_cert'. *)
