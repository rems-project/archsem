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

  Lemma read_last_cons_miss addr init mem msg :
    Msg.read_byte addr msg = None →
    read_last addr init (msg :: mem) = read_last addr init mem.
  Proof.
    intro Hmiss.
    cbn.
    rewrite Hmiss.
    reflexivity.
  Qed.

  Lemma read_initial_cons_miss addr init mem msg :
    Msg.read_byte addr msg = None →
    read_initial addr init (msg :: mem) = read_initial addr init mem.
  Proof.
    intro Hmiss.
    unfold read_initial.
    rewrite read_last_cons_miss by exact Hmiss.
    reflexivity.
  Qed.

  Lemma read_initial_cons_overwrite addr init mem msg byte :
    Msg.read_byte addr msg = Some byte →
    read_initial addr init (msg :: mem) = None.
  Proof.
    intro Hread.
    unfold read_initial.
    cbn.
    rewrite Hread.
    reflexivity.
  Qed.

  (** Reads [size] bytes starting at [addr] from the memory state at
      timestamp [tread]. Returns each byte paired with its actual
      write-timestamp [twrite], or [None] if any byte is unmapped. *)
  Definition read_from (addr : address) (size : N) (tread : nat)
      (init : memoryMap) (mem : t) : option (list (bv 8 * nat)) :=
    let snap := cut_before tread mem in
    for a in addr_range addr size do
      read_last a init snap
    end.

  Lemma read_from_cons_old addr size tread init mem msg :
    (tread ≤ length mem)%nat →
    read_from addr size tread init (msg :: mem) =
    read_from addr size tread init mem.
  Proof.
    intro Hle.
    unfold read_from, cut_before.
    rewrite PromMemory.cut_before_cons_old by exact Hle.
    reflexivity.
  Qed.

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

  Lemma fulfill_none_no_match msg prom mem t :
    fulfill msg prom mem = None →
    t ∈ prom →
    mem !! t ≠ Some msg.
  Proof.
    unfold fulfill.
    rewrite list_basics.head_reverse.
    intro Hfulfill.
    apply list_basics.last_None in Hfulfill.
    intros Hprom Hlookup.
    pose proof (list_basics.filter_nil_not_elem_of
      (λ t, mem !! t = Some msg) prom t Hfulfill Hlookup) as Hnot.
    exact (Hnot Hprom).
  Qed.

  Lemma last_cons_all_eq {A} (x : A) (l : list A) :
    (∀ y, y ∈ l → y = x) →
    last (x :: l) = Some x.
  Proof.
    induction l as [|a l IH]; intro Hall.
    - reflexivity.
    - rewrite list_basics.last_cons_cons.
      assert (a = x) by (apply Hall; left; reflexivity).
      subst a.
      apply IH.
      intros y Hy.
      apply Hall.
      right.
      exact Hy.
  Qed.

  Lemma fulfill_after_promise msg prom mem :
    fulfill msg prom mem = None →
    fulfill msg (length (msg :: mem) :: prom) (msg :: mem) =
    Some (length (msg :: mem)).
  Proof.
    intro Hfulfill.
    set (time := length (msg :: mem)).
    assert (Hno_match : ∀ t, t ∈ prom → mem !! t ≠ Some msg).
    { intros t Hprom.
      eapply fulfill_none_no_match; eauto. }
    unfold fulfill.
    rewrite list_basics.head_reverse.
    rewrite list_basics.filter_cons_True.
    - apply last_cons_all_eq.
      intros t Hmatch.
      rewrite list_basics.elem_of_list_filter in Hmatch.
      destruct Hmatch as [Hlookup Hprom].
      apply PromMemory.lookup_cons_inv_same in Hlookup as [Hold_lookup|Htime].
      + exfalso.
        eapply Hno_match; eauto.
      + exact Htime.
    - subst time.
      apply PromMemory.lookup_latest.
  Qed.

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

  Lemma filter_prom_after_promise v ts :
    set prom (filter (λ t, t ≠ v)) (promise v ts) =
    set prom (filter (λ t, t ≠ v)) ts.
  Proof.
    destruct ts.
    unfold promise.
    cbn.
    f_equal.
    destruct (decide (v ≠ v)) as [Hneq|_].
    - exfalso.
      apply Hneq.
      reflexivity.
    - reflexivity.
  Qed.
End TState.


(*** Instruction semantics ***)

Definition view_if (b : bool) (v : view) := if b then v else 0%nat.

(** Addresses that may be fetched as instruction bytes.  The executable
    promising model currently treats instruction memory as immutable; keeping
    that assumption explicit makes it possible to replace it later with an
    instruction-side timestamp/cache model. *)
Definition code_region := address → Prop.

Definition event_misses_code (code : code_region) (msg : Msg.t) : Prop :=
  ∀ a, code a → Msg.read_byte a msg = None.

Definition ifetch_in_code (code : code_region) (addr : address) (size : N) :
    Prop :=
  ∀ a, a ∈ addr_range addr size → code a.

Definition event_misses_ifetch (msg : Msg.t) (addr : address) (size : N) :
    Prop :=
  ∀ a, a ∈ addr_range addr size → Msg.read_byte a msg = None.

Lemma event_misses_code_ifetch code msg addr size :
  event_misses_code code msg →
  ifetch_in_code code addr size →
  event_misses_ifetch msg addr size.
Proof.
  intros Hmiss Hifetch a Ha.
  apply Hmiss.
  apply Hifetch.
  exact Ha.
Qed.

(** Interesting timestamps are [vpre] itself and any later timestamp whose
    write overlaps [addr, addr+size). *)
Definition read_candidates (addr : address) (size : N) (vpre : view)
    (mem : Memory.t) : list nat :=
  PromMemory.cut_after_with_timestamps vpre mem
    |> omap (λ '(msg, t),
              if decide (addr_overlap addr size (Msg.addr msg) (Msg.size msg))
              then Some t else None)
    |> cons vpre.

Lemma read_candidates_cons_old addr size vpre mem msg t :
  (vpre ≤ length mem)%nat →
  t ∈ read_candidates addr size vpre mem →
  t ∈ read_candidates addr size vpre (msg :: mem).
Proof.
  intros Hle Ht.
  unfold read_candidates in Ht |- *.
  rewrite PromMemory.cut_after_with_timestamps_cons_old by exact Hle.
  cbn.
  destruct (decide (addr_overlap addr size (Msg.addr msg) (Msg.size msg)));
    set_solver.
Qed.

Lemma read_candidates_time_le addr size vpre mem t :
  (vpre ≤ length mem)%nat →
  t ∈ read_candidates addr size vpre mem →
  (t ≤ length mem)%nat.
Proof.
  intros Hle Ht.
  unfold read_candidates in Ht.
  apply elem_of_cons in Ht as [->|Ht]; [exact Hle|].
  rewrite elem_of_list_omap in Ht.
  destruct Ht as [[msg t0] [Hin Hsome]].
  destruct (decide (addr_overlap addr size (Msg.addr msg) (Msg.size msg)));
    cbn in Hsome; inversion Hsome; subst t0.
  eapply PromMemory.cut_after_with_timestamps_time_le.
  exact Hin.
Qed.

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

Lemma read_imem_cons_miss addr size init mem msg :
  (∀ a, a ∈ addr_range addr size → Msg.read_byte a msg = None) →
  read_imem addr size init (msg :: mem) = read_imem addr size init mem.
Proof.
  intro Hmiss.
  unfold read_imem.
  assert
    (Hbytes :
       (for a in addr_range addr size do
          Memory.read_initial a init (msg :: mem)
        end) =
       (for a in addr_range addr size do
          Memory.read_initial a init mem
        end)).
  { induction (addr_range addr size) as [|a addrs IH].
    - reflexivity.
    - cbn.
      rewrite Memory.read_initial_cons_miss.
      + rewrite IH.
        * reflexivity.
        * intros a' Ha'.
          apply Hmiss.
          set_solver.
      + apply Hmiss.
        set_solver. }
  rewrite Hbytes.
  reflexivity.
Qed.

Lemma read_imem_cons_misses_code code addr size init mem msg :
  event_misses_code code msg →
  ifetch_in_code code addr size →
  read_imem addr size init (msg :: mem) = read_imem addr size init mem.
Proof.
  intros Hmiss Hifetch.
  apply read_imem_cons_miss.
  eapply event_misses_code_ifetch; eauto.
Qed.

Lemma read_imem_state_irrelevant addr size init mem ts ts' ts_new opcode :
  Exec.elem_of_results (ts', opcode) (read_imem addr size init mem ts) →
  Exec.elem_of_results (ts_new, opcode)
    (read_imem addr size init mem ts_new).
Proof.
  intro Hrun.
  unfold read_imem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_guard [p_size [Hsize Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hsize) as Hsize_prop.
  apply Exec.elem_of_guard_or_inv in Hsize as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_bytes [bytes [Hbytes Hrun]]].
  unfold othrow in Hbytes.
  destruct
    (for a in addr_range addr size do Memory.read_initial a init mem end)
    as [bytes0|] eqn:Hread.
  2: {
    unfold elem_of, Exec.elem_of_results in Hbytes.
    cbn in Hbytes.
    inversion Hbytes.
  }
  apply Exec.elem_of_mret_inv in Hbytes as [-> Hbytes_eq].
  inversion Hbytes_eq; subst bytes0.
  apply Exec.elem_of_mret_inv in Hrun as [-> ->].
  destruct (Exec.elem_of_guard_or
    (St:=TState.t) (E:=string) (P:=(size =? 4)%N) ts_new
    "Ifetch of size other than 4" Hsize_prop) as [p_size' Hsize'].
  eapply Exec.elem_of_bind_intro with
    (e := guard_or "Ifetch of size other than 4" (size =? 4)%N)
    (st' := ts_new) (a := p_size').
  - exact Hsize'.
  - cbn.
    apply Exec.elem_of_mret.
Qed.

Lemma read_imem_preserves_state addr size init mem ts ts' opcode :
  Exec.elem_of_results (ts', opcode) (read_imem addr size init mem ts) →
  ts' = ts.
Proof.
  intro Hrun.
  unfold read_imem in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_guard [p_size [Hsize Hrun]]].
  apply Exec.elem_of_guard_or_inv in Hsize as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_bytes [bytes [Hbytes Hrun]]].
  unfold othrow in Hbytes.
  destruct
    (for a in addr_range addr size do Memory.read_initial a init mem end)
    as [bytes0|] eqn:Hread.
  2: {
    unfold elem_of, Exec.elem_of_results in Hbytes.
    cbn in Hbytes.
    inversion Hbytes.
  }
  apply Exec.elem_of_mret_inv in Hbytes as [-> _].
  apply Exec.elem_of_mret_inv in Hrun as [-> _].
  reflexivity.
Qed.

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

Definition fwdb_times_le (mem : Memory.t) (ts : TState.t) : Prop :=
  ∀ a fwd, ts.(TState.fwdb) !! a = Some fwd →
    (fwd.(FwdItem.time) ≤ length mem)%nat.

Definition read_mem_vpre (vaddr : view) (macc : mem_acc) (ts : TState.t) :
    view :=
  let vbob := ts.(TState.vdmb) ⊔ ts.(TState.visb) ⊔ ts.(TState.vacq)
              ⊔ view_if (is_rel_acq_rcsc macc) ts.(TState.vrel) in
  vaddr ⊔ vbob.

Lemma apply_fwd_cons_old fwdb macc mem tread a raw msg :
  (∀ fwd, fwdb !! a = Some fwd →
    (fwd.(FwdItem.time) ≤ length mem)%nat) →
  apply_fwd fwdb macc (msg :: mem) tread a raw =
  apply_fwd fwdb macc mem tread a raw.
Proof.
  intros Hbound.
  destruct raw as [byte twrite].
  unfold apply_fwd.
  destruct (fwdb !! a) as [fwd|] eqn:Hfwd; [|reflexivity].
  destruct (tread <? FwdItem.time fwd)%nat; [|reflexivity].
  rewrite PromMemory.lookup_cons_old by (apply (Hbound fwd); reflexivity).
  reflexivity.
Qed.

Lemma apply_fwd_list_cons_old fwdb macc mem tread addrs raws msg :
  (∀ a fwd, a ∈ addrs → fwdb !! a = Some fwd →
    (fwd.(FwdItem.time) ≤ length mem)%nat) →
  (for ar in zip addrs raws do
     let '(a, raw) := ar in apply_fwd fwdb macc (msg :: mem) tread a raw
   end) =
  (for ar in zip addrs raws do
     let '(a, raw) := ar in apply_fwd fwdb macc mem tread a raw
   end).
Proof.
  revert raws.
  induction addrs as [|a addrs IH]; intros [|raw raws] Hbound;
    cbn; try reflexivity.
  rewrite apply_fwd_cons_old.
  - rewrite IH.
    + reflexivity.
    + intros a' fwd Ha' Hfwd.
      apply (Hbound a' fwd); [right; exact Ha'|exact Hfwd].
  - intros fwd Hfwd.
    apply (Hbound a fwd); [left; reflexivity|exact Hfwd].
Qed.

(** Performs a multi-byte memory read. Picks an interesting timestamp
    [tread] from [read_candidates], then applies per-byte forwarding. *)
Definition read_mem (addr : address) (size : N) (vaddr : view) (macc : mem_acc)
           (init : memoryMap) (mem : Memory.t) :
    Exec.t TState.t string (view * bv (8 * size)) :=
  ts ← mGet;
  guard_discard (TState.no_promises_until vaddr ts);;
  guard_or "Atomic RMW unsupported" (¬ (is_atomic_rmw macc));;
  let addrs := addr_range addr size in
  let vpre := read_mem_vpre vaddr macc ts in
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

Lemma read_mem_vpre_promise vaddr macc v ts :
  read_mem_vpre vaddr macc (TState.promise v ts) =
  read_mem_vpre vaddr macc ts.
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma fwdb_times_le_promise mem v ts :
  fwdb_times_le mem (TState.promise v ts) ↔ fwdb_times_le mem ts.
Proof.
  destruct ts.
  unfold fwdb_times_le.
  cbn.
  split; auto.
Qed.

Lemma TState_promise_update_coh p loc v ts :
  TState.update_coh loc v (TState.promise p ts) =
  TState.promise p (TState.update_coh loc v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_cohs avs p ts :
  TState.update_cohs avs (TState.promise p ts) =
  TState.promise p (TState.update_cohs avs ts).
Proof.
  unfold TState.update_cohs.
  revert ts.
  induction avs as [|[a v] avs IH]; intro ts; cbn.
  - reflexivity.
  - rewrite IH.
    apply TState_promise_update_coh.
Qed.

Lemma TState_promise_update_vrd p v ts :
  TState.update TState.vrd v (TState.promise p ts) =
  TState.promise p (TState.update TState.vrd v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vacq p v ts :
  TState.update TState.vacq v (TState.promise p ts) =
  TState.promise p (TState.update TState.vacq v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vcap p v ts :
  TState.update TState.vcap v (TState.promise p ts) =
  TState.promise p (TState.update TState.vcap v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vdmb p v ts :
  TState.update TState.vdmb v (TState.promise p ts) =
  TState.promise p (TState.update TState.vdmb v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_vdmbst p v ts :
  TState.update TState.vdmbst v (TState.promise p ts) =
  TState.promise p (TState.update TState.vdmbst v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_update_visb p v ts :
  TState.update TState.visb v (TState.promise p ts) =
  TState.promise p (TState.update TState.visb v ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_promise_set_xclb p tread addr size ts :
  TState.set_xclb tread addr size (TState.promise p ts) =
  TState.promise p (TState.set_xclb tread addr size ts).
Proof.
  destruct ts.
  reflexivity.
Qed.

Lemma TState_set_reg_promise p reg rv ts ts' :
  TState.set_reg reg rv ts = Some ts' →
  TState.set_reg reg rv (TState.promise p ts) =
  Some (TState.promise p ts').
Proof.
  destruct ts as [prom regs coh vrd vwr vdmbst vdmb vcap visb vacq vrel
    fwdb xclb].
  unfold TState.set_reg, TState.promise.
  cbn.
  destruct (decide (is_Some (dmap_lookup reg regs))) as [Hsome|Hnone];
    cbn; intro Hset; inversion Hset; subst; reflexivity.
Qed.

Lemma TState_set_reg_promise_update_vcap p v reg rv ts ts' :
  TState.set_reg reg rv (TState.update TState.vcap v ts) = Some ts' →
  TState.set_reg reg rv
    (TState.update TState.vcap v (TState.promise p ts)) =
  Some (TState.promise p ts').
Proof.
  rewrite TState_promise_update_vcap.
  apply TState_set_reg_promise.
Qed.

Lemma read_mem_promise_state addr size vaddr macc init mem p
    ts ts' res :
  (vaddr < p)%nat →
  Exec.elem_of_results (ts', res) (read_mem addr size vaddr macc init mem ts) →
  Exec.elem_of_results (TState.promise p ts', res)
    (read_mem addr size vaddr macc init mem (TState.promise p ts)).
Proof.
  intros Hfuture Hrun.
  unfold read_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_get [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_guard [p_no_promises [Hno_promises_guard Hrun]]].
  pose proof p_no_promises as Hno_promises.
  apply Exec.elem_of_guard_discard_inv in Hno_promises_guard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_atomic [p_atomic [Hatomic_guard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hatomic_guard)
    as Hatomic.
  apply Exec.elem_of_guard_or_inv in Hatomic_guard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_choose [tread [Hchoose Hrun]]].
  change (Exec.elem_of_results (ts_choose, tread)
    ((mchoosel (read_candidates addr size (read_mem_vpre vaddr macc ts) mem) :
        Exec.t TState.t string nat) ts)) in Hchoose.
  apply Exec.elem_of_mchoosel_inv in Hchoose as [-> Htread].
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_raw [raw_bytes [Hraw Hrun]]].
  unfold othrow in Hraw.
  destruct (Memory.read_from addr size tread init mem) as [raw_bytes0|]
    eqn:Hread.
  2: {
    unfold elem_of, Exec.elem_of_results in Hraw.
    cbn in Hraw.
    inversion Hraw.
  }
  apply Exec.elem_of_mret_inv in Hraw as [Hts_raw Hraw_eq].
  subst ts_raw.
  inversion Hraw_eq; subst raw_bytes0.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_bytes [byte_results [Hbytes Hrun]]].
  apply Exec.elem_of_lift_res_inv in Hbytes as [-> Hbytes].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_coh [pcoh [Hcoh Hrun]]].
  pose proof Hcoh as Hcoh_prop.
  apply Exec.elem_of_guard_discard_inv in Hcoh_prop as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_cohs [[] [Hcohs Hrun]]].
  apply Exec.elem_of_mSet_inv in Hcohs as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_vrd [[] [Hvrd Hrun]]].
  apply Exec.elem_of_mSet_inv in Hvrd as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_vacq [[] [Hvacq Hrun]]].
  apply Exec.elem_of_mSet_inv in Hvacq as ->.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_vcap [[] [Hvcap Hrun]]].
  apply Exec.elem_of_mSet_inv in Hvcap as ->.

  eapply Exec.elem_of_bind_intro with
    (e := (mGet : Exec.t TState.t string TState.t))
    (st' := TState.promise p ts) (a := TState.promise p ts).
  - apply Exec.elem_of_mGet.
  - cbn.
    assert
      (Hno_promises_promise :
         TState.no_promises_until vaddr (TState.promise p ts)).
    { destruct ts as [prom regs coh vrd vwr vdmbst vdmb vcap visb vacq
        vrel fwdb xclb].
      cbn in Hno_promises |- *.
      intros p0 Hin.
      apply elem_of_cons in Hin as [->|Hin].
      - exact Hfuture.
      - apply Hno_promises.
        exact Hin. }
    destruct (Exec.elem_of_guard_discard
      (St:=TState.t) (E:=string)
      (P:=TState.no_promises_until vaddr (TState.promise p ts))
      (TState.promise p ts) Hno_promises_promise) as
      [p_no_promises' Hno_promises_guard'].
    eapply Exec.elem_of_bind_intro with
      (e := guard_discard
              (TState.no_promises_until vaddr (TState.promise p ts)))
      (st' := TState.promise p ts) (a := p_no_promises').
    + exact Hno_promises_guard'.
    + cbn.
      destruct (Exec.elem_of_guard_or
        (St:=TState.t) (E:=string)
        (P:=¬ is_atomic_rmw macc) (TState.promise p ts)
        "Atomic RMW unsupported" Hatomic)
        as [p_atomic' Hatomic_guard'].
      eapply Exec.elem_of_bind_intro with
        (e := guard_or "Atomic RMW unsupported" (¬ is_atomic_rmw macc))
        (st' := TState.promise p ts) (a := p_atomic').
      * exact Hatomic_guard'.
      * cbn.
        rewrite read_mem_vpre_promise.
        eapply Exec.elem_of_bind_intro with
          (st' := TState.promise p ts) (a := tread).
        -- change (Exec.elem_of_results (TState.promise p ts, tread)
             ((mchoosel
                 (read_candidates addr size (read_mem_vpre vaddr macc ts) mem) :
                Exec.t TState.t string nat) (TState.promise p ts))).
           apply Exec.elem_of_mchoosel.
           exact Htread.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (e := othrow "Memory read of unmapped bytes"
                     (Memory.read_from addr size tread init mem))
             (st' := TState.promise p ts) (a := raw_bytes).
           ++ unfold othrow.
              rewrite Hread.
              apply Exec.elem_of_mret.
           ++ cbn.
              eapply Exec.elem_of_bind_intro with
                (e := mlift
                        (for (a, raw) in zip (addr_range addr size) raw_bytes do
                           apply_fwd (TState.fwdb (TState.promise p ts))
                             macc mem tread a raw
                         end))
                (st' := TState.promise p ts) (a := byte_results).
              ** apply Exec.elem_of_lift_res.
                 destruct ts.
                 exact Hbytes.
              ** cbn.
                 assert
                   (Hcoh_prom :
                      ∀ '(a, t) ∈ zip (addr_range addr size) byte_results.*2,
                        (TState.coh (TState.promise p ts) !!! a ≤ t)%nat).
                 { intros [a t] Hin.
                   destruct ts.
                   cbn in pcoh |- *.
                   apply (pcoh (a, t) Hin). }
                 destruct (Exec.elem_of_guard_discard
                   (St:=TState.t) (E:=string)
                   (P:=∀ '(a, t) ∈ zip (addr_range addr size) byte_results.*2,
                        (TState.coh (TState.promise p ts) !!! a ≤ t)%nat)
                   (TState.promise p ts) Hcoh_prom) as [pcoh' Hcoh'].
                 eapply Exec.elem_of_bind_intro with
                   (e := guard_discard
                           (∀ '(a, t) ∈ zip (addr_range addr size) byte_results.*2,
                             (TState.coh (TState.promise p ts) !!! a ≤ t)%nat))
                   (st' := TState.promise p ts) (a := pcoh').
                 ---- exact Hcoh'.
                 ---- cbn.
                 set (vpost :=
                        read_mem_vpre vaddr macc ts ⊔
                        foldr max 0%nat byte_results.*1.*2).
                 eapply Exec.elem_of_bind_intro
                   with
                     (st' :=
                        TState.promise p
                          (TState.update_cohs
                             (zip (addr_range addr size) byte_results.*2) ts))
                     (a := ()).
                 --- rewrite <- TState_promise_update_cohs.
                     apply Exec.elem_of_mSet.
                 --- cbn.
                     eapply Exec.elem_of_bind_intro
                       with
                         (st' :=
                            TState.promise p
                                 (TState.update TState.vrd vpost
                                    (TState.update_cohs
                                    (zip (addr_range addr size) byte_results.*2)
                                    ts)))
                         (a := ()).
                     +++ rewrite <- TState_promise_update_vrd.
                         apply Exec.elem_of_mSet.
                     +++ cbn.
                         eapply Exec.elem_of_bind_intro
                           with
                             (st' :=
                                TState.promise p
                                  (TState.update TState.vacq
                                     (view_if (is_rel_acq macc) vpost)
                                     (TState.update TState.vrd vpost
                                           (TState.update_cohs
                                           (zip (addr_range addr size)
                                              byte_results.*2)
                                           ts))))
                             (a := ()).
                         *** rewrite <- TState_promise_update_vacq.
                             apply Exec.elem_of_mSet.
                         *** cbn.
                             eapply Exec.elem_of_bind_intro
                               with
                                 (st' :=
                                    TState.promise p
                                      (TState.update TState.vcap vaddr
                                         (TState.update TState.vacq
                                            (view_if (is_rel_acq macc) vpost)
                                            (TState.update TState.vrd vpost
                                               (TState.update_cohs
                                                  (zip (addr_range addr size)
                                                     byte_results.*2) ts)))))
                                 (a := ()).
                             ++++ rewrite <- TState_promise_update_vcap.
                                 apply Exec.elem_of_mSet.
                             ++++ cbn.
                                  destruct (is_exclusive macc) eqn:Hexcl.
                                  { cbn in Hrun.
                                    apply Exec.elem_of_bind_elim in Hrun as
                                      [ts_xcl [[] [Hxcl Hret]]].
                                    apply Exec.elem_of_mSet_inv in Hxcl as ->.
                                    apply Exec.elem_of_mret_inv in Hret as
                                      [-> ->].
                                    eapply Exec.elem_of_bind_intro
                                      with
                                        (st' :=
                                           TState.promise p
                                             (TState.set_xclb tread addr size
                                                (TState.update TState.vcap vaddr
                                                   (TState.update TState.vacq
                                                      (view_if
                                                         (is_rel_acq macc)
                                                         vpost)
                                                      (TState.update TState.vrd
                                                         vpost
                                                         (TState.update_cohs
                                                            (zip
                                                             (addr_range addr
                                                                  size)
                                                               byte_results.*2)
                                                            ts))))))
                                        (a := ()).
                                      * rewrite <- TState_promise_set_xclb.
                                        apply Exec.elem_of_mSet.
                                      * cbn.
                                        apply Exec.elem_of_mret. }
                                  { cbn in Hrun.
                                    apply Exec.elem_of_bind_elim in Hrun as
                                      [ts_skip [[] [Hskip Hret]]].
                                    unfold elem_of, Exec.elem_of_results
                                      in Hskip.
                                    cbn in Hskip.
                                    apply elem_of_list_singleton in Hskip.
                                    inversion Hskip; subst ts_skip;
                                      clear Hskip.
                                    unfold elem_of, Exec.elem_of_results
                                      in Hret.
                                    cbn in Hret.
                                    apply elem_of_list_singleton in Hret.
                                    inversion Hret; subst; clear Hret.
                                    eapply Exec.elem_of_bind_intro
                                      with
                                        (st' :=
                                           TState.promise p
                                             (TState.update TState.vcap vaddr
                                                (TState.update TState.vacq
                                                   (view_if (is_rel_acq macc)
                                                      vpost)
                                                   (TState.update TState.vrd
                                                      vpost
                                                      (TState.update_cohs
                                                         (zip
                                                            (addr_range addr
                                                               size)
                                                            byte_results.*2)
                                                         ts)))))
                                        (a := ()).
                                      * apply Exec.elem_of_mret.
                                      * cbn.
                                        apply Exec.elem_of_mret. }
Qed.

Lemma read_mem_cons_old addr size vaddr macc init mem msg ts ts' res :
  (read_mem_vpre vaddr macc ts ≤ length mem)%nat →
  fwdb_times_le mem ts →
  Exec.elem_of_results (ts', res) (read_mem addr size vaddr macc init mem ts) →
  Exec.elem_of_results (ts', res)
    (read_mem addr size vaddr macc init (msg :: mem) ts).
Proof.
  intros Hvpre Hfwdb Hrun.
  unfold read_mem in Hrun |- *.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_get [ts0 [Hget Hrun]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_guard [p_no_promises [Hno_promises_guard Hrun]]].
  pose proof p_no_promises as Hno_promises.
  apply Exec.elem_of_guard_discard_inv in Hno_promises_guard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_atomic [p_atomic [Hatomic_guard Hrun]]].
  pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hatomic_guard)
    as Hatomic.
  apply Exec.elem_of_guard_or_inv in Hatomic_guard as ->.
  cbn in Hrun.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_choose [tread [Hchoose Hrun]]].
  change (Exec.elem_of_results (ts_choose, tread)
    ((mchoosel (read_candidates addr size (read_mem_vpre vaddr macc ts) mem) :
        Exec.t TState.t string nat) ts)) in Hchoose.
  apply Exec.elem_of_mchoosel_inv in Hchoose as [-> Htread].
  pose proof (read_candidates_time_le addr size
    (read_mem_vpre vaddr macc ts) mem tread Hvpre Htread) as Htread_le.
  pose proof (read_candidates_cons_old addr size
    (read_mem_vpre vaddr macc ts) mem msg tread Hvpre Htread)
    as Htread_new.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_raw [raw_bytes [Hraw Hrun]]].
  pose proof (Memory.read_from_cons_old addr size tread init mem msg Htread_le)
    as Hread_from.
  unfold othrow in Hraw.
  destruct (Memory.read_from addr size tread init mem) as [raw_bytes0|]
    eqn:Hread_old.
  2: {
    unfold elem_of, Exec.elem_of_results in Hraw.
    cbn in Hraw.
    inversion Hraw.
  }
  apply Exec.elem_of_mret_inv in Hraw as [Hts_raw Hraw_eq].
  subst ts_raw.
  inversion Hraw_eq; subst raw_bytes0.
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_bytes [byte_results [Hbytes Hrun]]].
  apply Exec.elem_of_lift_res_inv in Hbytes as [-> Hbytes].
  apply Exec.elem_of_bind_elim in Hrun as
    [ts_coh [pcoh [Hcoh Hrun]]].
  pose proof Hcoh as Hcoh_state.
  apply Exec.elem_of_guard_discard_inv in Hcoh_state as ->.

  eapply Exec.elem_of_bind_intro with
    (e := (mGet : Exec.t TState.t string TState.t))
    (st' := ts) (a := ts).
  - apply Exec.elem_of_mGet.
  - cbn.
    destruct (Exec.elem_of_guard_discard
      (St:=TState.t) (E:=string)
      (P:=TState.no_promises_until vaddr ts) ts Hno_promises) as
      [p_no_promises' Hno_promises_guard'].
    eapply Exec.elem_of_bind_intro with
      (e := guard_discard (TState.no_promises_until vaddr ts))
      (st' := ts) (a := p_no_promises').
    + exact Hno_promises_guard'.
    + cbn.
      destruct (Exec.elem_of_guard_or
        (St:=TState.t) (E:=string)
        (P:=¬ is_atomic_rmw macc) ts "Atomic RMW unsupported" Hatomic)
        as [p_atomic' Hatomic_guard'].
      eapply Exec.elem_of_bind_intro with
        (e := guard_or "Atomic RMW unsupported" (¬ is_atomic_rmw macc))
        (st' := ts) (a := p_atomic').
      * exact Hatomic_guard'.
      * cbn.
        eapply Exec.elem_of_bind_intro with (st' := ts) (a := tread).
        -- change (Exec.elem_of_results (ts, tread)
             ((mchoosel
                 (read_candidates addr size (read_mem_vpre vaddr macc ts)
                    (msg :: mem)) : Exec.t TState.t string nat) ts)).
           apply Exec.elem_of_mchoosel.
           exact Htread_new.
        -- cbn.
           eapply Exec.elem_of_bind_intro with
             (e := othrow "Memory read of unmapped bytes"
                     (Memory.read_from addr size tread init (msg :: mem)))
             (st' := ts) (a := raw_bytes).
           ++ unfold othrow.
              rewrite Hread_from.
              apply Exec.elem_of_mret.
           ++ cbn.
              eapply Exec.elem_of_bind_intro with
                (e := mlift
                        (for (a, raw) in zip (addr_range addr size) raw_bytes do
                           apply_fwd (TState.fwdb ts) macc (msg :: mem)
                             tread a raw
                         end))
                (st' := ts) (a := byte_results).
              ** apply Exec.elem_of_lift_res.
                 rewrite apply_fwd_list_cons_old.
                 --- exact Hbytes.
                 --- intros a fwd _ Hfwd.
                     exact (Hfwdb a fwd Hfwd).
              ** cbn.
                 eapply Exec.elem_of_bind_intro with
                   (e := guard_discard
                           (∀ '(a, t) ∈ zip (addr_range addr size) byte_results.*2,
                             (TState.coh ts !!! a ≤ t)%nat))
                   (st' := ts) (a := pcoh).
                 --- exact Hcoh.
                 --- exact Hrun.
Qed.

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

Lemma write_mem_none_preserves_mem tid addr size vdata macc mem data
    ts ts' mem' time :
  Exec.elem_of_results (ts', (mem', time, None))
    (write_mem tid addr size vdata macc mem data ts) →
  mem' = mem.
Proof.
  intro H.
  unfold write_mem in H.
  set (msg := Msg.make size tid addr data) in *.
  apply Exec.elem_of_bind_elim in H as [ts0 [ts_read [Hget H]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  destruct (Memory.fulfill msg (TState.prom ts) mem) as [t|] eqn:Hfulfill;
    cbn in H.
  - repeat (apply Exec.elem_of_bind_elim in H as [? [[] [? H]]]).
    apply Exec.elem_of_mret_inv in H as [_ Heq].
    inversion Heq; subst.
    reflexivity.
  - cbn in H.
    repeat (apply Exec.elem_of_bind_elim in H as [? [[] [? H]]]).
    apply Exec.elem_of_mret_inv in H as [_ Heq].
    inversion Heq.
Qed.

Lemma write_mem_promise_replay_one tid addr size vdata macc mem data
    ts ts' mem' time vpre :
  Exec.elem_of_results (ts', (mem', time, Some vpre))
    (write_mem tid addr size vdata macc mem data ts) →
  let msg := Msg.make size tid addr data in
  mem' = msg :: mem ∧
  time = length mem' ∧
  (vpre < time)%nat ∧
  Exec.elem_of_results (ts', (mem', time, None))
    (write_mem tid addr size vdata macc mem' data
       (TState.promise time ts)).
Proof.
  intro H.
  unfold write_mem in H.
  set (msg := Msg.make size tid addr data) in *.
  apply Exec.elem_of_bind_elim in H as [ts0 [ts_read [Hget H]]].
  apply Exec.elem_of_mGet_inv in Hget as [-> ->].
  destruct (Memory.fulfill msg (TState.prom ts) mem) as [t|]
      eqn:Hfulfill; cbn in H.
  - repeat (apply Exec.elem_of_bind_elim in H as [? [[] [? H]]]).
    apply Exec.elem_of_mret_inv in H as [_ Heq].
    inversion Heq.
  - apply Exec.elem_of_bind_elim in H as [ts_guard [p [Hguard H]]].
    destruct p as [Hvpre Hcoh].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    apply Exec.elem_of_bind_elim in H as [ts_prom [[] [Hprom H]]].
    apply Exec.elem_of_mset_inv in Hprom as ->.
    apply Exec.elem_of_bind_elim in H as [ts_coh [[] [Hcoh_set H]]].
    apply Exec.elem_of_mSet_inv in Hcoh_set as ->.
    apply Exec.elem_of_bind_elim in H as [ts_vwr [[] [Hvwr H]]].
    apply Exec.elem_of_mSet_inv in Hvwr as ->.
    apply Exec.elem_of_bind_elim in H as [ts_vrel [[] [Hvrel H]]].
    apply Exec.elem_of_mSet_inv in Hvrel as ->.
    apply Exec.elem_of_mret_inv in H as [Heq Hret].
    inversion Hret; subst mem' time vpre.
    inversion Heq; subst ts'.
    repeat split; try reflexivity.
    + exact Hvpre.
    + unfold write_mem.
      eapply Exec.elem_of_bind_intro.
      * apply Exec.elem_of_mGet.
      * unfold msg in Hfulfill |- *.
        cbn.
        rewrite Memory.fulfill_after_promise by exact Hfulfill.
        cbn.
        unfold guard_discard.
        destruct (decide _) as [pguard|Hnp].
        -- eapply Exec.elem_of_bind_intro with (a := pguard).
           ++ apply Exec.elem_of_mret.
           ++ eapply Exec.elem_of_bind_intro with
                (st' := set TState.prom
                   (filter (λ t : view, t ≠ S (length mem))) ts)
                (a := ()).
              ** rewrite <- TState.filter_prom_after_promise.
                 apply Exec.elem_of_mset.
              ** eapply Exec.elem_of_bind_intro.
                 --- apply Exec.elem_of_mSet.
                 --- eapply Exec.elem_of_bind_intro.
                     +++ apply Exec.elem_of_mSet.
                     +++ eapply Exec.elem_of_bind_intro.
                         *** apply Exec.elem_of_mSet.
                         *** apply Exec.elem_of_mret.
        -- exfalso.
           apply Hnp.
           unfold TState.promise.
           cbn.
           split.
           ++ exact Hvpre.
           ++ intros a Ha.
              exact (Hcoh a Ha).
Qed.


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

Lemma write_mem_xcl_none_preserves_mem tid addr size vdata macc mem data
    ts ts' mem' :
  Exec.elem_of_results (ts', (mem', None))
    (write_mem_xcl tid addr size vdata macc mem data ts) →
  mem' = mem.
Proof.
  intro H.
  unfold write_mem_xcl in H.
  case_guard as Hatomic.
  - apply Exec.elem_of_bind_elim in H as [tsg [Hat [Hguard H]]].
    apply Exec.elem_of_mret_inv in Hguard as [-> _].
    destruct (is_exclusive macc) eqn:Hxcl.
    + apply Exec.elem_of_bind_elim in H as [ts0 [res [Hwrite H]]].
      destruct res as [[mem0 time] vpre_opt].
      apply Exec.elem_of_bind_elim in H as [ts1 [ts_mid [Hget H]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      destruct (TState.xclb ts0) as [[[xtime xaddr] xsize]|] eqn:Hxclb.
      * destruct (decide (addr = xaddr ∧ size = xsize)) as [Heq|Hneq].
        -- apply Exec.elem_of_bind_elim in H as
             [ts2 [[] [Hguard2 H]]].
           apply Exec.elem_of_bind_elim in H as
             [ts3 [[] [Hfwdb H]]].
           apply Exec.elem_of_mret_inv in H as [_ Hret].
           inversion Hret; subst.
           eapply write_mem_none_preserves_mem; eauto.
        -- apply Exec.elem_of_bind_elim in H as
             [ts2 [[] [Hfwdb H]]].
           apply Exec.elem_of_mret_inv in H as [_ Hret].
           inversion Hret; subst.
           eapply write_mem_none_preserves_mem; eauto.
      * rewrite Exec.mdiscard_eq in H.
        unfold elem_of, Exec.elem_of_results in H.
        cbn in H.
        inversion H.
    + apply Exec.elem_of_bind_elim in H as [ts0 [res [Hwrite H]]].
      destruct res as [[mem0 time] vpre_opt].
      apply Exec.elem_of_bind_elim in H as [ts1 [[] [Hfwdb H]]].
      apply Exec.elem_of_mret_inv in H as [_ Hret].
      inversion Hret; subst.
      eapply write_mem_none_preserves_mem; eauto.
  - unfold elem_of, Exec.elem_of_results in H.
    cbn in H.
    set_solver.
Qed.

Lemma write_mem_xcl_promise_replay_one tid addr size vdata macc mem data
    ts ts' mem' vpre :
  Exec.elem_of_results (ts', (mem', Some vpre))
    (write_mem_xcl tid addr size vdata macc mem data ts) →
  let msg := Msg.make size tid addr data in
  mem' = msg :: mem ∧
  (vpre < length mem')%nat ∧
  Exec.elem_of_results (ts', (mem', None))
    (write_mem_xcl tid addr size vdata macc mem' data
       (TState.promise (length mem') ts)).
Proof.
  intro H.
  unfold write_mem_xcl in H.
  case_guard as Hatomic.
  - apply Exec.elem_of_bind_elim in H as [tsg [Hat [Hguard H]]].
    apply Exec.elem_of_mret_inv in Hguard as [-> _].
    destruct (is_exclusive macc) eqn:Hxcl.
    + apply Exec.elem_of_bind_elim in H as [ts0 [res [Hwrite H]]].
      destruct res as [[mem0 time] vpre_opt].
      apply Exec.elem_of_bind_elim in H as [ts1 [ts_mid [Hget H]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      destruct (TState.xclb ts0) as [[[xtime xaddr] xsize]|] eqn:Hxclb.
      * destruct (decide (addr = xaddr ∧ size = xsize)) as [Heq|Hneq].
        -- apply Exec.elem_of_bind_elim in H as
             [ts2 [[] [Hmatch H]]].
           apply Exec.elem_of_bind_elim in Hmatch as
             [ts_guard [[] [Hguard2 Hfwdb]]].
           pose proof (Exec.elem_of_guard_discard_unit_prop _ _ Hguard2)
             as Hexclusive.
           apply Exec.elem_of_guard_discard_unit_inv in Hguard2 as ->.
           apply Exec.elem_of_mSet_inv in Hfwdb as ->.
           apply Exec.elem_of_bind_elim in H as
             [ts4 [[] [Hclear H]]].
           apply Exec.elem_of_mSet_inv in Hclear as ->.
           apply Exec.elem_of_mret_inv in H as [Heq_final Hret].
           inversion Hret; subst mem' vpre_opt.
           inversion Heq_final; subst ts'.
           pose proof (write_mem_promise_replay_one
             tid addr size vdata macc mem data ts ts0 mem0 time vpre Hwrite)
             as [Hmem0 [Htime [Hvpre Hwrite_replay]]].
           subst mem0 time.
           repeat split; try reflexivity.
           ++ exact Hvpre.
	           ++ unfold write_mem_xcl.
	              case_guard as Hatomic'.
	              ** eapply Exec.elem_of_bind_intro.
	                 --- apply Exec.elem_of_mret.
	                 --- rewrite Hxcl.
	                     eapply Exec.elem_of_bind_intro.
	                     +++ exact Hwrite_replay.
	                     +++ eapply Exec.elem_of_bind_intro.
	                         *** apply Exec.elem_of_mGet.
	                         *** rewrite Hxclb.
	                             destruct (decide (addr = xaddr ∧ size = xsize))
	                               as [_|Hneq'].
	                             ---- eapply Exec.elem_of_bind_intro.
	                                  ++++ eapply Exec.elem_of_bind_intro.
	                                       ***** apply Exec.elem_of_guard_discard_unit.
	                                             exact Hexclusive.
	                                       ***** apply Exec.elem_of_mSet.
	                                  ++++ eapply Exec.elem_of_bind_intro.
	                                       ***** apply Exec.elem_of_mSet.
	                                       ***** apply Exec.elem_of_mret.
	                             ---- exfalso.
	                                  apply Hneq'.
	                                  exact Heq.
              ** contradiction.
        -- apply Exec.elem_of_bind_elim in H as
             [ts2 [[] [Hfwdb H]]].
           apply Exec.elem_of_mSet_inv in Hfwdb as ->.
           apply Exec.elem_of_bind_elim in H as
             [ts3 [[] [Hclear H]]].
           apply Exec.elem_of_mSet_inv in Hclear as ->.
           apply Exec.elem_of_mret_inv in H as [Heq_final Hret].
           inversion Hret; subst mem' vpre_opt.
           inversion Heq_final; subst ts'.
           pose proof (write_mem_promise_replay_one
             tid addr size vdata macc mem data ts ts0 mem0 time vpre Hwrite)
             as [Hmem0 [Htime [Hvpre Hwrite_replay]]].
           subst mem0 time.
           repeat split; try reflexivity.
           ++ exact Hvpre.
	           ++ unfold write_mem_xcl.
	              case_guard as Hatomic'.
	              ** eapply Exec.elem_of_bind_intro.
	                 --- apply Exec.elem_of_mret.
	                 --- rewrite Hxcl.
	                     eapply Exec.elem_of_bind_intro.
	                     +++ exact Hwrite_replay.
	                     +++ eapply Exec.elem_of_bind_intro.
	                         *** apply Exec.elem_of_mGet.
	                         *** rewrite Hxclb.
	                             destruct (decide (addr = xaddr ∧ size = xsize))
	                               as [Heq'|_].
	                             ---- exfalso.
	                                  apply Hneq.
	                                  exact Heq'.
	                             ---- eapply Exec.elem_of_bind_intro.
	                                  ++++ apply Exec.elem_of_mSet.
	                                  ++++ eapply Exec.elem_of_bind_intro.
	                                       ***** apply Exec.elem_of_mSet.
	                                       ***** apply Exec.elem_of_mret.
              ** contradiction.
      * rewrite Exec.mdiscard_eq in H.
        unfold elem_of, Exec.elem_of_results in H.
        cbn in H.
        inversion H.
    + apply Exec.elem_of_bind_elim in H as [ts0 [res [Hwrite H]]].
      destruct res as [[mem0 time] vpre_opt].
      apply Exec.elem_of_bind_elim in H as [ts1 [[] [Hfwdb H]]].
      apply Exec.elem_of_mSet_inv in Hfwdb as ->.
      apply Exec.elem_of_mret_inv in H as [Heq_final Hret].
      inversion Hret; subst mem' vpre_opt.
      inversion Heq_final; subst ts'.
      pose proof (write_mem_promise_replay_one
        tid addr size vdata macc mem data ts ts0 mem0 time vpre Hwrite)
        as [Hmem0 [Htime [Hvpre Hwrite_replay]]].
      subst mem0 time.
      repeat split; try reflexivity.
      * exact Hvpre.
	      * unfold write_mem_xcl.
	        case_guard as Hatomic'.
	        -- eapply Exec.elem_of_bind_intro.
	           ++ apply Exec.elem_of_mret.
	           ++ rewrite Hxcl.
	              eapply Exec.elem_of_bind_intro.
	              ** exact Hwrite_replay.
	              ** eapply Exec.elem_of_bind_intro.
	                 --- apply Exec.elem_of_mSet.
	                 --- apply Exec.elem_of_mret.
        -- contradiction.
  - unfold elem_of, Exec.elem_of_results in H.
    cbn in H.
    set_solver.
Qed.

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

  #[local] Typeclasses Transparent othrow.
  #[local] Instance exec_unfold : Exec.Unfold := {}.

  Ltac inv_run_outcome :=
    repeat match goal with
    | x : unit |- _ => destruct x
    | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
    | H : Some _ = Some _ |- _ => inversion H; subst; clear H
    | H : (_, _) = ?p |- _ => destruct p; inversion H; subst; clear H
    | H : ?p = (_, _) |- _ => destruct p; inversion H; subst; clear H
    | H : Exec.elem_of_results _ ((_ ≫= _) _) |- _ =>
        apply Exec.elem_of_bind_elim in H as [? [? [? H]]]
    | H : Exec.elem_of_results _ ((mget _) _) |- _ =>
        apply Exec.elem_of_mget_inv in H as [-> ->]
    | H : Exec.elem_of_results _ ((mret _) _) |- _ =>
        apply Exec.elem_of_mret_inv in H as [-> ?]
    | H : Exec.elem_of_results _ ((msetv _ _) _) |- _ =>
        unfold msetv in H
    | H : Exec.elem_of_results _ ((mset _ _) _) |- _ =>
        apply Exec.elem_of_mset_inv in H as ->
    | H : Exec.elem_of_results _ ((mSet _) _) |- _ =>
        apply Exec.elem_of_mSet_inv in H as ->
    | H : Exec.elem_of_results _ ((guard_discard _) _) |- _ =>
        apply Exec.elem_of_guard_discard_inv in H as ->
    | H : Exec.elem_of_results _ ((guard_or _ _) _) |- _ =>
        apply Exec.elem_of_guard_or_inv in H as ->
    | H : Exec.elem_of_results _ ((Exec.liftSt _ _) _) |- _ =>
        apply Exec.elem_of_liftSt_inv in H as [? [-> H]]
    | H : Exec.elem_of_results _ ((mthrow _) _) |- _ =>
        unfold elem_of, Exec.elem_of_results in H; cbn in H; inversion H
    | H : context[othrow _ ?opt] |- _ => unfold othrow in H
    | H : context[if ?b then _ else _] |- _ => destruct b eqn:?
    | H : context[match ?x with _ => _ end] |- _ => destruct x eqn:?
    end.

  Ltac solve_ppstate_mem :=
    cbn;
    match goal with
    | |- PPState.mem _ = PPState.mem _ =>
        repeat match goal with
        | st : PPState.t _ _ _ |- _ => destruct st
        end;
        cbn;
        reflexivity
    end.

  Lemma run_outcome_none_preserves_mem out ppst ppst'
      (eret : eff_ret out) :
    Exec.elem_of_results (ppst', (eret, None)) (run_outcome out ppst) →
    PPState.mem ppst' = PPState.mem ppst.
  Proof.
    intro H.
    funelim (run_outcome out ppst).
    all: rewrite <- Heqcall in H.
    all: inv_run_outcome; try solve [solve_ppstate_mem].
    all: cbn; eapply write_mem_xcl_none_preserves_mem; eauto.
  Qed.

  Lemma run_outcome_promise_replay_one out ppst ppst'
      (eret : eff_ret out) vpre :
    Exec.elem_of_results (ppst', (eret, Some vpre)) (run_outcome out ppst) →
    ∃ event,
      PPState.mem ppst' = event :: PPState.mem ppst ∧
      Msg.tid event = tid ∧
      (vpre < length (PPState.mem ppst'))%nat ∧
      Exec.elem_of_results (ppst', (eret, None))
        (run_outcome out
           (PPState.Make
              (TState.promise (length (PPState.mem ppst')) (PPState.state ppst))
              (PPState.mem ppst')
              (PPState.iis ppst))).
  Proof.
    intro H.
    funelim (run_outcome out ppst).
    all: rewrite <- Heqcall in H.
    all: try solve [inv_run_outcome].
    inv_run_outcome.
    pose proof (write_mem_xcl_promise_replay_one
      tid addr size (IIS.strict (PPState.iis out)) macc
      (PPState.mem out) val (PPState.state out) x t vpre H2)
      as [Hmem [Hlt Hreplay]].
    subst t.
    exists (Msg.make size tid addr val).
    repeat split; try reflexivity; [exact Hlt|].
    simp run_outcome.
    cbn.
    rewrite Heqb.
    eapply Exec.elem_of_bind_intro.
    - unfold guard_or.
      destruct (decide (PAS_NonSecure = PAS_NonSecure)) as [Heq|Hneq].
      + apply Exec.elem_of_mret.
      + exfalso; apply Hneq; reflexivity.
    - cbn.
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + cbn.
        eapply Exec.elem_of_bind_intro.
        * apply Exec.elem_of_mget.
        * cbn.
          eapply Exec.elem_of_bind_intro.
          -- apply Exec.elem_of_liftSt.
             exact Hreplay.
          -- cbn.
             eapply Exec.elem_of_bind_intro.
             ++ apply Exec.elem_of_mset.
             ++ cbn.
                destruct out; cbn in *.
                apply Exec.elem_of_mret.
  Qed.

  Lemma run_outcome_no_promise_non_mem_write out :
    (∀ mr (val : bv (8 * mr.(MemReq.size)))
        (tags : bv mr.(MemReq.num_tag)),
      out ≠ MemWrite mr val tags) →
    ∀ ppst ppst' (eret : eff_ret out) vpre,
      Exec.elem_of_results (ppst', (eret, Some vpre))
        (run_outcome out ppst) →
      False.
  Proof.
    intros Hnot ppst ppst' eret vpre H.
    funelim (run_outcome out ppst).
    all: rewrite <- Heqcall in H.
    all: try solve [inv_run_outcome].
    exfalso.
    eapply Hnot.
    reflexivity.
  Qed.

Definition ppstate_read_times_le macc
    (ppst : PPState.t TState.t Msg.t IIS.t) : Prop :=
  (read_mem_vpre (IIS.strict (PPState.iis ppst)) macc
     (PPState.state ppst) ≤ length (PPState.mem ppst))%nat ∧
  fwdb_times_le (PPState.mem ppst) (PPState.state ppst).

Lemma ppstate_read_times_le_promise macc p ppst :
  ppstate_read_times_le macc
    (PPState.Make (TState.promise p (PPState.state ppst))
       (PPState.mem ppst) (PPState.iis ppst)) ↔
  ppstate_read_times_le macc ppst.
Proof.
  destruct ppst as [ts mem iis].
  unfold ppstate_read_times_le.
  cbn.
  rewrite read_mem_vpre_promise.
  rewrite fwdb_times_le_promise.
  reflexivity.
Qed.

  Lemma run_outcome_explicit_read_cons_old addr size macc addr_space
      ppst ppst' msg eret :
    is_ifetch macc = false →
    is_explicit macc = true →
    ppstate_read_times_le macc ppst →
    Exec.elem_of_results (ppst', (eret, None))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0)) ppst) →
    Exec.elem_of_results
      (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
         (PPState.iis ppst'), (eret, None))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
         (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
            (PPState.iis ppst))).
  Proof.
    intros Hnot_ifetch Hexplicit [Hvpre Hfwdb] Hrun.
    simp run_outcome in Hrun |- *.
    rewrite Hnot_ifetch in Hrun |- *.
    rewrite Hexplicit in Hrun |- *.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_guard [p_nss [Hguard Hrun]]].
    pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hnss.
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_vaddr [vaddr [Hvaddr Hrun]]].
    apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_mem [mem [Hmem Hrun]]].
    apply Exec.elem_of_mget_inv in Hmem as [-> ->].
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_read [[view val] [Hread Hrun]]].
    apply Exec.elem_of_liftSt_inv in Hread as [ts_read [-> Hread]].
    pose proof (read_mem_cons_old addr size
      (IIS.strict (PPState.iis ppst)) macc initmem (PPState.mem ppst)
      msg (PPState.state ppst) ts_read (view, val) Hvpre Hfwdb Hread)
      as Hread_new.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_iis [[] [Hiis Hrun]]].
    apply Exec.elem_of_mSet_inv in Hiis as ->.
    apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
    inversion Hret; subst eret.
    inversion Heq; subst ppst'.

    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
      (P:=addr_space = PAS_NonSecure)
      (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
         (PPState.iis ppst) : PPState.t TState.t Msg.t IIS.t)
      "Access outside Non-Secure" Hnss) as [p_nss' Hguard'].
    eapply Exec.elem_of_bind_intro with
      (e := guard_or "Access outside Non-Secure"
              (addr_space = PAS_NonSecure))
      (st' := PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
                 (PPState.iis ppst))
      (a := p_nss').
    - exact Hguard'.
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := (mget (IIS.strict ∘ PPState.iis) :
                 Exec.t (PPState.t TState.t Msg.t IIS.t) string nat))
        (st' := PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
                 (PPState.iis ppst))
        (a := IIS.strict (PPState.iis ppst)).
      + apply (Exec.elem_of_mget (E := string)
          (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
             (PPState.iis ppst)) (IIS.strict ∘ PPState.iis)).
      + cbn.
        eapply Exec.elem_of_bind_intro with
          (e := (mget PPState.mem :
                   Exec.t (PPState.t TState.t Msg.t IIS.t) string Memory.t))
          (st' := PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
                   (PPState.iis ppst))
          (a := msg :: PPState.mem ppst).
        * apply (Exec.elem_of_mget (E := string)
            (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
               (PPState.iis ppst)) PPState.mem).
        * cbn.
          eapply Exec.elem_of_bind_intro with
            (e := Exec.liftSt PPState.state
                    (read_mem addr size (IIS.strict (PPState.iis ppst))
                       macc initmem (msg :: PPState.mem ppst)))
            (st' := setv PPState.state ts_read
                     (PPState.Make (PPState.state ppst)
                        (msg :: PPState.mem ppst) (PPState.iis ppst)))
            (a := (view, val)).
          -- eapply (@Exec.elem_of_liftSt
               (PPState.t TState.t Msg.t IIS.t) TState.t string
               (nat * bv (8 * size))%type
               (PPState.Make (PPState.state ppst)
                  (msg :: PPState.mem ppst) (PPState.iis ppst))
               ts_read (view, val) PPState.state _
               (read_mem addr size (IIS.strict (PPState.iis ppst))
                  macc initmem (msg :: PPState.mem ppst))).
             exact Hread_new.
          -- cbn.
             eapply Exec.elem_of_bind_intro with
               (st' := set PPState.iis (IIS.add view)
                        (setv PPState.state ts_read
                           (PPState.Make (PPState.state ppst)
                              (msg :: PPState.mem ppst)
                              (PPState.iis ppst))))
               (a := ()).
             ++ apply Exec.elem_of_mset.
             ++ cbn.
                apply Exec.elem_of_mret.
  Qed.

  Lemma run_outcome_ifetch_cons_misses_code code addr size macc addr_space
      ppst ppst' msg eret :
    event_misses_code code msg →
    ifetch_in_code code addr size →
    is_ifetch macc = true →
    Exec.elem_of_results (ppst', (eret, None))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0)) ppst) →
    Exec.elem_of_results
      (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
         (PPState.iis ppst'), (eret, None))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
         (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
            (PPState.iis ppst))).
  Proof.
    intros Hmiss Hifetch Hifetch_macc Hrun.
    simp run_outcome in Hrun |- *.
    rewrite Hifetch_macc in Hrun |- *.
    inv_run_outcome.
    destruct (Exec.elem_of_guard_or
      (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
      (P:=PAS_NonSecure = PAS_NonSecure)
      (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
         (PPState.iis ppst) : PPState.t TState.t Msg.t IIS.t)
      "Access outside Non-Secure" eq_refl) as [p_nss Hnss].
    eapply Exec.elem_of_bind_intro with
      (e := guard_or "Access outside Non-Secure"
              (PAS_NonSecure = PAS_NonSecure))
      (st' := PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
                 (PPState.iis ppst))
      (a := p_nss).
    - exact Hnss.
    - cbn.
      eapply Exec.elem_of_bind_intro with
        (e := (mget PPState.mem :
                 Exec.t (PPState.t TState.t Msg.t IIS.t) string Memory.t)).
      + apply Exec.elem_of_mget.
      + cbn.
        change (read_imem addr size initmem (msg :: PPState.mem ppst)) with
          (read_imem addr size initmem
             (PPState.mem
                (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
                   (PPState.iis ppst)))).
        rewrite (read_imem_cons_misses_code code addr size initmem
          (PPState.mem ppst) msg) by eauto.
        eapply Exec.elem_of_bind_intro with
          (e := Exec.liftSt PPState.state
                  (read_imem addr size initmem (PPState.mem ppst))).
        * eapply Exec.elem_of_liftSt.
          eassumption.
        * cbn.
          apply Exec.elem_of_mret.
  Qed.

  Lemma run_outcome_mem_read_cons_old code addr size macc addr_space
      ppst ppst' msg eret :
    (is_ifetch macc = true →
      event_misses_code code msg ∧ ifetch_in_code code addr size) →
    (is_ifetch macc = false →
      is_explicit macc = true →
      ppstate_read_times_le macc ppst) →
    Exec.elem_of_results (ppst', (eret, None))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0)) ppst) →
    Exec.elem_of_results
      (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
         (PPState.iis ppst'), (eret, None))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
         (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
            (PPState.iis ppst))).
  Proof.
    intros Hifetch_assume Hread_bound Hrun.
    destruct (is_ifetch macc) eqn:Hifetch.
    - destruct (Hifetch_assume eq_refl) as [Hmiss Hcode].
      eapply run_outcome_ifetch_cons_misses_code; eauto.
    - destruct (is_explicit macc) eqn:Hexplicit.
	      + eapply run_outcome_explicit_read_cons_old.
	        * exact Hifetch.
	        * exact Hexplicit.
	        * apply Hread_bound; reflexivity.
	        * exact Hrun.
		      + simp run_outcome in Hrun.
		        rewrite Hifetch in Hrun.
		        rewrite Hexplicit in Hrun.
		        inv_run_outcome.
  Qed.

  Lemma run_outcome_mem_read_cons_old_full code addr size macc addr_space
      ppst ppst' msg eret vpre_opt :
    (is_ifetch macc = true →
      event_misses_code code msg ∧ ifetch_in_code code addr size) →
    (is_ifetch macc = false →
      is_explicit macc = true →
      ppstate_read_times_le macc ppst) →
    Exec.elem_of_results (ppst', (eret, vpre_opt))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0)) ppst) →
    Exec.elem_of_results
      (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
         (PPState.iis ppst'), (eret, vpre_opt))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
         (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
            (PPState.iis ppst))).
  Proof.
    intros Hifetch_assume Hread_bound Hrun.
    destruct vpre_opt as [vpre|].
    - simp run_outcome in Hrun.
      destruct (is_ifetch macc) eqn:Hifetch.
      + inv_run_outcome.
      + destruct (is_explicit macc) eqn:Hexplicit; inv_run_outcome.
    - eapply run_outcome_mem_read_cons_old; eauto.
  Qed.

  Lemma run_outcome_mem_read_cons_old_fmap code addr size macc addr_space
      ppst ppst' msg eret :
    (is_ifetch macc = true →
      event_misses_code code msg ∧ ifetch_in_code code addr size) →
    (is_ifetch macc = false →
      is_explicit macc = true →
      ppstate_read_times_le macc ppst) →
    Exec.elem_of_results (ppst', eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst) ppst) →
    Exec.elem_of_results
      (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
         (PPState.iis ppst'), eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst)
         (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
            (PPState.iis ppst))).
  Proof.
    intros Hifetch_assume Hread_bound Hrun.
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
    pose proof
      (run_outcome_mem_read_cons_old_full code addr size macc addr_space
         ppst ppst' msg eret0 vpre_opt Hifetch_assume Hread_bound Hrun)
      as Hrun'.
    unfold elem_of, Exec.elem_of_results in Hrun' |- *.
    unfold fmap, Exec.fmap_inst.
    destruct
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
         (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
            (PPState.iis ppst))) as [rs es].
    cbn in *.
    rewrite elem_of_list_fmap.
    exists
      (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
         (PPState.iis ppst'), (eret0, vpre_opt)).
    split; [reflexivity|exact Hrun'].
  Qed.

  Lemma run_outcome_mem_read_promise_state_full addr size macc addr_space
      ppst ppst' p eret vpre_opt :
    (is_ifetch macc = false →
      is_explicit macc = true →
      (IIS.strict (PPState.iis ppst) < p)%nat) →
    Exec.elem_of_results (ppst', (eret, vpre_opt))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0)) ppst) →
    Exec.elem_of_results
      (PPState.Make (TState.promise p (PPState.state ppst'))
         (PPState.mem ppst') (PPState.iis ppst'), (eret, vpre_opt))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
         (PPState.Make (TState.promise p (PPState.state ppst))
            (PPState.mem ppst) (PPState.iis ppst))).
  Proof.
    intros Hfuture Hrun.
    simp run_outcome in Hrun |- *.
    apply Exec.elem_of_bind_elim in Hrun as
      [pp_guard [p_nss [Hguard Hrun]]].
    pose proof (Exec.elem_of_guard_or_prop _ _ _ _ Hguard) as Hnss.
    apply Exec.elem_of_guard_or_inv in Hguard as ->.
    destruct (is_ifetch macc) eqn:Hifetch.
    - apply Exec.elem_of_bind_elim in Hrun as
        [pp_mem [mem [Hmem Hrun]]].
      apply Exec.elem_of_mget_inv in Hmem as [-> ->].
      apply Exec.elem_of_bind_elim in Hrun as
        [pp_read [opcode [Hread Hrun]]].
      apply Exec.elem_of_liftSt_inv in Hread as [ts_read [-> Hread]].
      pose proof
        (read_imem_preserves_state addr size initmem (PPState.mem ppst)
           (PPState.state ppst) ts_read opcode Hread) as ->.
      apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
      inversion Heq; subst ppst'.
      inversion Hret; subst eret vpre_opt.
      destruct (Exec.elem_of_guard_or
        (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
        (P:=addr_space = PAS_NonSecure)
        (PPState.Make (TState.promise p (PPState.state ppst))
           (PPState.mem ppst) (PPState.iis ppst))
        "Access outside Non-Secure" Hnss) as [p_nss' Hguard'].
      eapply Exec.elem_of_bind_intro
        with
          (e := guard_or "Access outside Non-Secure"
                  (addr_space = PAS_NonSecure))
          (st' := PPState.Make (TState.promise p (PPState.state ppst))
                    (PPState.mem ppst) (PPState.iis ppst))
          (a := p_nss').
      + exact Hguard'.
      + cbn.
        eapply Exec.elem_of_bind_intro with
          (e := (mget PPState.mem :
                   Exec.t (PPState.t TState.t Msg.t IIS.t) string Memory.t))
	          (st' := PPState.Make (TState.promise p (PPState.state ppst))
	                    (PPState.mem ppst) (PPState.iis ppst))
	          (a := PPState.mem ppst).
	        * apply (Exec.elem_of_mget (E:=string)
                    (PPState.Make (TState.promise p (PPState.state ppst))
                       (PPState.mem ppst) (PPState.iis ppst)) PPState.mem).
        * cbn.
          eapply Exec.elem_of_bind_intro with
		            (e := Exec.liftSt PPState.state
		                    (read_imem addr size initmem (PPState.mem ppst)))
		            (st' := PPState.Make
		                     (TState.promise p (PPState.state ppst))
		                     (PPState.mem ppst) (PPState.iis ppst))
	            (a := opcode).
	          -- change
                   (Exec.elem_of_results
	                      (setv PPState.state
                         (TState.promise p (PPState.state ppst))
	                         (PPState.Make
                            (TState.promise p (PPState.state ppst))
                            (PPState.mem ppst) (PPState.iis ppst)),
                       opcode)
                      (Exec.liftSt PPState.state
                         (read_imem addr size initmem (PPState.mem ppst))
                         (PPState.Make
                            (TState.promise p (PPState.state ppst))
                            (PPState.mem ppst) (PPState.iis ppst)))).
             eapply (@Exec.elem_of_liftSt
                   (PPState.t TState.t Msg.t IIS.t) TState.t string
                   (bv (8 * size))
	                   (PPState.Make (TState.promise p (PPState.state ppst))
	                      (PPState.mem ppst) (PPState.iis ppst))
	                   (TState.promise p (PPState.state ppst)) opcode
                   PPState.state _
                   (read_imem addr size initmem (PPState.mem ppst))).
	             eapply read_imem_state_irrelevant.
	             exact Hread.
          -- cbn.
             apply Exec.elem_of_mret.
    - destruct (is_explicit macc) eqn:Hexplicit.
      + apply Exec.elem_of_bind_elim in Hrun as
          [pp_vaddr [vaddr0 [Hvaddr Hrun]]].
        apply Exec.elem_of_mget_inv in Hvaddr as [-> ->].
        apply Exec.elem_of_bind_elim in Hrun as
          [pp_mem [mem [Hmem Hrun]]].
        apply Exec.elem_of_mget_inv in Hmem as [-> ->].
        apply Exec.elem_of_bind_elim in Hrun as
          [pp_read [[view val] [Hread Hrun]]].
        apply Exec.elem_of_liftSt_inv in Hread as [ts_read [-> Hread]].
        pose proof
          (read_mem_promise_state addr size
             (IIS.strict (PPState.iis ppst)) macc initmem
             (PPState.mem ppst) p (PPState.state ppst) ts_read
             (view, val) (Hfuture eq_refl eq_refl) Hread)
          as Hread_promise.
        apply Exec.elem_of_bind_elim in Hrun as
          [pp_iis [[] [Hiis Hrun]]].
        apply Exec.elem_of_mSet_inv in Hiis as ->.
        apply Exec.elem_of_mret_inv in Hrun as [Heq Hret].
        inversion Heq; subst ppst'.
        inversion Hret; subst eret vpre_opt.
        destruct (Exec.elem_of_guard_or
          (St:=PPState.t TState.t Msg.t IIS.t) (E:=string)
          (P:=addr_space = PAS_NonSecure)
          (PPState.Make (TState.promise p (PPState.state ppst))
             (PPState.mem ppst) (PPState.iis ppst))
          "Access outside Non-Secure" Hnss) as [p_nss' Hguard'].
        eapply Exec.elem_of_bind_intro
          with
            (e := guard_or "Access outside Non-Secure"
                    (addr_space = PAS_NonSecure))
            (st' := PPState.Make (TState.promise p (PPState.state ppst))
                      (PPState.mem ppst) (PPState.iis ppst))
            (a := p_nss').
	        * exact Hguard'.
	        * cbn.
	          eapply Exec.elem_of_bind_intro
            with
              (e := (mget (IIS.strict ∘ PPState.iis) :
                       Exec.t (PPState.t TState.t Msg.t IIS.t) string nat))
	              (st' := PPState.Make (TState.promise p (PPState.state ppst))
	                        (PPState.mem ppst) (PPState.iis ppst))
	              (a := IIS.strict (PPState.iis ppst)).
	          -- apply (Exec.elem_of_mget (E:=string)
                   (PPState.Make (TState.promise p (PPState.state ppst))
                      (PPState.mem ppst) (PPState.iis ppst))
                   (IIS.strict ∘ PPState.iis)).
          -- cbn.
             eapply Exec.elem_of_bind_intro
               with
                 (e := (mget PPState.mem :
                          Exec.t (PPState.t TState.t Msg.t IIS.t) string
                            Memory.t))
	                 (st' := PPState.Make
	                          (TState.promise p (PPState.state ppst))
	                          (PPState.mem ppst) (PPState.iis ppst))
	                 (a := PPState.mem ppst).
	             ++ apply (Exec.elem_of_mget (E:=string)
                    (PPState.Make (TState.promise p (PPState.state ppst))
                       (PPState.mem ppst) (PPState.iis ppst)) PPState.mem).
             ++ cbn.
                eapply Exec.elem_of_bind_intro
                  with
                    (e := Exec.liftSt PPState.state
                            (read_mem addr size
                               (IIS.strict (PPState.iis ppst)) macc initmem
                               (PPState.mem ppst)))
	                    (st' := PPState.Make
	                             (TState.promise p ts_read)
	                             (PPState.mem ppst) (PPState.iis ppst))
	                    (a := (view, val)).
	                ** change
                     (Exec.elem_of_results
                        (setv PPState.state (TState.promise p ts_read)
                           (PPState.Make
                              (TState.promise p (PPState.state ppst))
                              (PPState.mem ppst) (PPState.iis ppst)),
                         (view, val))
                        (Exec.liftSt PPState.state
                           (read_mem addr size
                              (IIS.strict (PPState.iis ppst)) macc initmem
                              (PPState.mem ppst))
                           (PPState.Make
                              (TState.promise p (PPState.state ppst))
                              (PPState.mem ppst) (PPState.iis ppst)))).
                   eapply (@Exec.elem_of_liftSt
                     (PPState.t TState.t Msg.t IIS.t) TState.t string
                     (nat * bv (8 * size))%type
                     (PPState.Make (TState.promise p (PPState.state ppst))
                        (PPState.mem ppst) (PPState.iis ppst))
                     (TState.promise p ts_read) (view, val)
                     PPState.state _
                     (read_mem addr size (IIS.strict (PPState.iis ppst))
                        macc initmem (PPState.mem ppst))).
	                   exact Hread_promise.
                ** cbn.
                   eapply Exec.elem_of_bind_intro
                     with
                       (st' := set PPState.iis (IIS.add view)
                                  (PPState.Make (TState.promise p ts_read)
                                     (PPState.mem ppst) (PPState.iis ppst)))
                       (a := ()).
                   --- apply Exec.elem_of_mset.
                   --- cbn.
                       apply Exec.elem_of_mret.
      + unfold elem_of, Exec.elem_of_results in Hrun.
        cbn in Hrun.
        inversion Hrun.
  Qed.

  Lemma run_outcome_mem_read_promise_state_fmap addr size macc addr_space
      ppst ppst' p eret :
    (is_ifetch macc = false →
      is_explicit macc = true →
      (IIS.strict (PPState.iis ppst) < p)%nat) →
    Exec.elem_of_results (ppst', eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst) ppst) →
    Exec.elem_of_results
      (PPState.Make (TState.promise p (PPState.state ppst'))
         (PPState.mem ppst') (PPState.iis ppst'), eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst)
         (PPState.Make (TState.promise p (PPState.state ppst))
            (PPState.mem ppst) (PPState.iis ppst))).
  Proof.
    intros Hfuture Hrun.
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
    pose proof
      (run_outcome_mem_read_promise_state_full addr size macc addr_space
         ppst ppst' p eret0 vpre_opt Hfuture Hrun) as Hrun'.
    unfold elem_of, Exec.elem_of_results in Hrun' |- *.
    unfold fmap, Exec.fmap_inst.
    destruct
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
         (PPState.Make (TState.promise p (PPState.state ppst))
            (PPState.mem ppst) (PPState.iis ppst))) as [rs es].
    cbn in *.
    rewrite elem_of_list_fmap.
    exists
      (PPState.Make (TState.promise p (PPState.state ppst'))
      (PPState.mem ppst') (PPState.iis ppst'), (eret0, vpre_opt)).
    split; [reflexivity|exact Hrun'].
  Qed.

  Lemma run_outcome_mem_read_fmap_preserves_mem addr size macc addr_space
      ppst ppst' eret :
    Exec.elem_of_results (ppst', eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst) ppst) →
    PPState.mem ppst' = PPState.mem ppst.
  Proof.
    intro Hrun.
    apply Exec.elem_of_fmap_inv in Hrun as [[eret0 vpre_opt] [-> Hrun]].
    destruct vpre_opt as [vpre|].
    - simp run_outcome in Hrun.
      destruct (is_ifetch macc) eqn:Hifetch.
      + inv_run_outcome.
      + destruct (is_explicit macc) eqn:Hexplicit; inv_run_outcome.
    - eapply run_outcome_none_preserves_mem.
      exact Hrun.
  Qed.

  Lemma run_outcome_mem_read_promise_cons_old_fmap code addr size
      macc addr_space ppst ppst' msg eret :
    (is_ifetch macc = true →
      event_misses_code code msg ∧ ifetch_in_code code addr size) →
    (is_ifetch macc = false →
      is_explicit macc = true →
      ppstate_read_times_le macc ppst) →
    Exec.elem_of_results (ppst', eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst) ppst) →
    Exec.elem_of_results
      (PPState.Make (TState.promise (length (msg :: PPState.mem ppst'))
         (PPState.state ppst')) (msg :: PPState.mem ppst')
         (PPState.iis ppst'), eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst)
         (PPState.Make (TState.promise (length (msg :: PPState.mem ppst))
            (PPState.state ppst)) (msg :: PPState.mem ppst)
            (PPState.iis ppst))).
  Proof.
    intros Hifetch_assume Hread_bound Hrun.
    pose proof
      (run_outcome_mem_read_fmap_preserves_mem addr size macc addr_space
         ppst ppst' eret Hrun) as Hmem.
    set (p := length (msg :: PPState.mem ppst)).
    assert
      (Hfuture_promise :
         is_ifetch macc = false →
         is_explicit macc = true →
         (IIS.strict (PPState.iis ppst) < p)%nat).
    { intros Hnot_ifetch Hexplicit.
      specialize (Hread_bound Hnot_ifetch Hexplicit) as [Hvpre _].
      assert
        (Hstrict_le_vpre :
           (IIS.strict (PPState.iis ppst) ≤
            read_mem_vpre (IIS.strict (PPState.iis ppst)) macc
              (PPState.state ppst))%nat).
      { unfold read_mem_vpre.
        apply Nat.le_max_l. }
      subst p.
      cbn.
      lia. }
    pose proof
      (run_outcome_mem_read_promise_state_fmap addr size macc addr_space
         ppst ppst' p eret Hfuture_promise Hrun) as Hpromise.
    pose proof
      (run_outcome_mem_read_cons_old_fmap code addr size macc addr_space
         (PPState.Make (TState.promise p (PPState.state ppst))
            (PPState.mem ppst) (PPState.iis ppst))
         (PPState.Make (TState.promise p (PPState.state ppst'))
            (PPState.mem ppst') (PPState.iis ppst'))
         msg eret Hifetch_assume) as Hcons.
    assert
      (Hread_bound_promise :
         is_ifetch macc = false →
         is_explicit macc = true →
         ppstate_read_times_le macc
           (PPState.Make (TState.promise p (PPState.state ppst))
              (PPState.mem ppst) (PPState.iis ppst))).
    { intros Hnot_ifetch Hexplicit.
      apply ppstate_read_times_le_promise.
      apply Hread_bound; assumption. }
    specialize (Hcons Hread_bound_promise Hpromise).
    cbn in Hcons |- *.
    subst p.
    rewrite Hmem in Hcons.
    rewrite Hmem.
    exact Hcons.
  Qed.

  (** Read outcomes are stable under adding a future memory event, provided
      instruction fetches are protected by the immutable-code assumption and
      explicit reads only observe timestamps in the old memory prefix.  Write
      outcomes are handled separately by [run_outcome_promise_replay_one]. *)
  Lemma run_outcome_future_promise_stable code addr size macc addr_space
      ppst ppst' msg eret :
    (is_ifetch macc = true →
      event_misses_code code msg ∧ ifetch_in_code code addr size) →
    (is_ifetch macc = false →
      is_explicit macc = true →
      ppstate_read_times_le macc ppst) →
    Exec.elem_of_results (ppst', (eret, None))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0)) ppst) →
    Exec.elem_of_results
      (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
         (PPState.iis ppst'), (eret, None))
      (run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
         (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
            (PPState.iis ppst))).
  Proof.
    eapply run_outcome_mem_read_cons_old.
  Qed.

  Lemma run_outcome_future_promise_stable_fmap code addr size macc addr_space
      ppst ppst' msg eret :
    (is_ifetch macc = true →
      event_misses_code code msg ∧ ifetch_in_code code addr size) →
    (is_ifetch macc = false →
      is_explicit macc = true →
      ppstate_read_times_le macc ppst) →
    Exec.elem_of_results (ppst', eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst) ppst) →
    Exec.elem_of_results
      (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
         (PPState.iis ppst'), eret)
      ((run_outcome (MemRead (MemReq.make macc addr addr_space size 0))
          |$> fst)
         (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
            (PPState.iis ppst))).
  Proof.
    eapply run_outcome_mem_read_cons_old_fmap.
  Qed.

  Definition outcome_future_promise_stable_fmap
      (code : code_region) (msg : Msg.t) (out : outcome) : Prop :=
    ∀ ppst ppst' (eret : eff_ret out),
      Exec.elem_of_results (ppst', eret) ((run_outcome out |$> fst) ppst) →
      Exec.elem_of_results
        (PPState.Make (PPState.state ppst') (msg :: PPState.mem ppst')
           (PPState.iis ppst'), eret)
        ((run_outcome out |$> fst)
           (PPState.Make (PPState.state ppst) (msg :: PPState.mem ppst)
              (PPState.iis ppst))).

  Fixpoint imon_future_promise_stable_fmap
      (code : code_region) (msg : Msg.t) A (mon : iMon A) : Prop :=
    match mon with
    | Ret _ => True
    | Next call k =>
        match call with
        | inl out =>
            outcome_future_promise_stable_fmap code msg out ∧
            ∀ eret, imon_future_promise_stable_fmap code msg A (k eret)
        | inr _ =>
            ∀ ret, imon_future_promise_stable_fmap code msg A (k ret)
        end
    end.

  Lemma mem_read_outcome_future_promise_stable_fmap code msg addr size
      macc addr_space :
    (is_ifetch macc = true →
      event_misses_code code msg ∧ ifetch_in_code code addr size) →
    (∀ ppst,
      is_ifetch macc = false →
      is_explicit macc = true →
      ppstate_read_times_le macc ppst) →
    outcome_future_promise_stable_fmap code msg
      (MemRead (MemReq.make macc addr addr_space size 0)).
  Proof.
    intros Hifetch_assume Hread_bound ppst ppst' eret Hrun.
    eapply run_outcome_future_promise_stable_fmap.
    - exact Hifetch_assume.
    - intros Hifetch Hexplicit.
      apply Hread_bound; assumption.
    - exact Hrun.
  Qed.

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
