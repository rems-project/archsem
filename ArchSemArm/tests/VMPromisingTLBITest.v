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

From ASCommon Require Import Options Common CResult CList Exec.
From ArchSemArm Require Import ArmInst VMPromising.

Open Scope stdpp.
Open Scope bv.

(** A last-level TLBI must not depend on allocations left empty by rollback.

    Page tables: L0 at 0x0, L1 at 0x1000, L2 at 0x2000 and the last-level
    table at 0x3000, whose slot 0 holds leaf [c] and slot 1 is invalid. The
    level-2 entry [parent] points to the last-level table. While ASID 1 is
    active, write [w1] replaces [c] by [c']; [parent] has ASID 0, so the write
    does not refill it. After switching back to ASID 0, a last-level TLBI for
    slot 1 arrives, then this thread promises [wd], which maps slot 1.

    Promising [wd] before the CSE at time 1 allocates the slot-1 leaf and
    rolls it back to an empty history. Replaying the TLBI must not treat that
    empty allocation as a TLB entry. Otherwise it refills [parent] at time 2
    and loads [c'] one step earlier than when the CSE comes first. *)
Module LastLevelDormant.
  Definition imem : memoryMap :=
    ∅ |> mem_insert 0x0 8 0x1003 |> mem_insert 0x1000 8 0x2003
      |> mem_insert 0x2000 8 0x3003 |> mem_insert 0x3000 8 0x4403
      |> mem_insert 0x3008 8 0.
  Definition ttbr_a : bv 64 := 0.
  Definition ttbr_b : bv 64 := 0x1000000007000.
  Definition regs : registerMap :=
    ∅ |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 ttbr_a
      |> reg_insert ID_AA64MMFR1_EL1 0.

  Definition w1 := Ev.Msg (Msg.make 1 0x3000 8 0x5403).
  Definition tlbi := Ev.Tlbi (TLBI.Vaa 1 false 1 true) 0 0.
  Definition wd := Ev.Msg (Msg.make 0 0x3008 8 0x6403).
  Definition mem := [tlbi; w1].
  Definition mem' := wd :: mem.

  Definition run (step : TLB.t → result string (TLB.t * ())) (cache : TLB.t) :=
    if step cache is Ok (next, _) then next else cache.

  Definition init : TLB.t :=
    match TLB.init 0 imem regs with
    | Ok cache => cache
    | Error _ => TLB.make TLB.VATLB.init ∅ ∅ [] 0
    end.
  Definition old : TLB.t :=
    init |> run (TLB.fill_cse 0 imem [] 0 ttbr_b None)
      |> run (TLB.fill_promise 0 imem [w1] w1)
      |> run (TLB.fill_cse 0 imem [w1] 1 ttbr_a None)
      |> run (TLB.fill_promise 0 imem mem tlbi).

  (** The promise first, then the CSE at time 1. *)
  Definition promise_first : TLB.t :=
    old |> run (TLB.fill_promise 0 imem mem' wd)
      |> run (TLB.fill_cse 0 imem mem' 1 ttbr_a None).
  (** The CSE first, then the promise. *)
  Definition context_first : TLB.t :=
    old |> run (TLB.fill_cse 0 imem mem 1 ttbr_a None)
      |> run (TLB.fill_promise 0 imem mem' wd).

  Definition entry (lvl0 : TLB.FE.t) (path : list (bv 9 * bv 64)) : result string TLB.FE.t :=
    foldl (λ acc '(idx, pte), fe ← acc; TLB.FE.append fe idx pte) (Ok lvl0) path.
  Definition root := TLB.FE.make0 false 0 0 ttbr_a 0x1003.
  Definition history (cache : TLB.t) (path : list (bv 9 * bv 64)) :=
    if entry root path is Ok fe then TLB.vatlb cache !! fe else None.
  Definition parent : list (bv 9 * bv 64) := [(0, 0x2003); (0, 0x3003)].
  Definition c' : list (bv 9 * bv 64) := parent ++ [(0, 0x5403)].
  Definition d : list (bv 9 * bv 64) := parent ++ [(1, 0x6403)].

  Definition ok {A} (r : result string A) : bool := if r is Ok _ then true else false.

  (** Every step of both orders succeeds. *)
  Goal ok (TLB.init 0 imem regs) = true. Proof. vm_compute. reflexivity. Qed.
  Goal ok (TLB.fill_promise 0 imem mem' wd old) = true. Proof. vm_compute. reflexivity. Qed.
  Goal ok (TLB.fill_cse 0 imem mem 1 ttbr_a None old) = true. Proof. vm_compute. reflexivity. Qed.

  Goal history old parent = Some [(TLB.Entry.Load, 0%nat)]. Proof. vm_compute. reflexivity. Qed.
  Goal history old c' = None. Proof. vm_compute. reflexivity. Qed.

  (** Before empty allocations were skipped, [promise_first] loaded [c'] at
      time 2. *)
  Goal history promise_first c' = Some [(TLB.Entry.Load, 3%nat)].
  Proof. vm_compute. reflexivity. Qed.
  Goal history context_first c' = Some [(TLB.Entry.Load, 3%nat)].
  Proof. vm_compute. reflexivity. Qed.
  Goal history promise_first d = Some [(TLB.Entry.Load, 3%nat)].
  Proof. vm_compute. reflexivity. Qed.
  Goal history context_first d = Some [(TLB.Entry.Load, 3%nat)].
  Proof. vm_compute. reflexivity. Qed.
End LastLevelDormant.

(** Merged lookup results must not depend on allocation order.

    TTBR0_EL1 starts at 0, whose level-0 slot is invalid. The root at 0x2000
    maps VA 0 through the table at 0x1000 to a level-1 block. Write [w] stores
    the same table descriptor at address 0, so afterwards both roots map VA 0
    to the same block. Writing TTBR0_EL1 = 0x2000 at view 0 before the write is
    promised allocates the block entry of root 0x2000 first. Promising the
    write first allocates the block entry of root 0 first; the later rollback
    keeps that empty allocation in place and the refill reloads it.

    The two lookups list the same alternatives in opposite orders. Before
    merging kept the smallest walk, the merged results kept the first root:
    0x2000 when the TTBR write came first and 0 when the promise came first. *)
Module MergeOrder.
  Definition imem : memoryMap :=
    ∅ |> mem_insert 0 8 0 |> mem_insert 0x1000 8 1 |> mem_insert 0x2000 8 0x1003.
  Definition regs : registerMap :=
    ∅ |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
      |> reg_insert ID_AA64MMFR1_EL1 0.
  Definition w := Ev.Msg (Msg.make 1 0 8 0x1003).
  Definition root : bv 16 * bv 64 * bool := (0, 0x2000, false).

  Definition run (step : TLB.t → result string (TLB.t * ())) (cache : TLB.t) :=
    if step cache is Ok (next, _) then next else cache.
  Definition ok {A} (r : result string A) : bool := if r is Ok _ then true else false.

  Definition init : TLB.t :=
    match TLB.init 0 imem regs with
    | Ok cache => cache
    | Error _ => TLB.make TLB.VATLB.init ∅ ∅ [] 0
    end.
  (** The TTBR write first, then the promise. *)
  Definition root_first : TLB.t :=
    init |> run (TLB.fill_asid_root 0 imem [] root 0)
      |> run (TLB.fill_promise 0 imem [w] w).
  (** The promise first, then the TTBR write at view 0. *)
  Definition promise_first : TLB.t :=
    init |> run (TLB.fill_promise 0 imem [w] w)
      |> run (TLB.fill_asid_root 0 imem [w] root 0).

  Definition lookup (cache : TLB.t) :=
    Exec.results (TLB.lookup 0 imem [w] cache false false 0 0 0 1 0).

  (** Every step of both orders succeeds. *)
  Goal ok (TLB.init 0 imem regs) = true. Proof. vm_compute. reflexivity. Qed.
  Goal ok (TLB.fill_asid_root 0 imem [] root 0 init) = true. Proof. vm_compute. reflexivity. Qed.
  Goal ok (TLB.fill_promise 0 imem [w] w (run (TLB.fill_asid_root 0 imem [] root 0) init)) = true.
  Proof. vm_compute. reflexivity. Qed.
  Goal ok (TLB.fill_promise 0 imem [w] w init) = true. Proof. vm_compute. reflexivity. Qed.
  Goal ok (TLB.fill_asid_root 0 imem [w] root 0 (run (TLB.fill_promise 0 imem [w] w) init)) = true.
  Proof. vm_compute. reflexivity. Qed.

  (** The alternatives come in opposite orders. *)
  Goal lookup root_first =
    [TLB.Result.make 0x2000 [0x1003; 1] 0 1 None; TLB.Result.make 0 [0x1003; 1] 1 1 None].
  Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.
  Goal lookup promise_first =
    [TLB.Result.make 0 [0x1003; 1] 1 1 None; TLB.Result.make 0x2000 [0x1003; 1] 0 1 None].
  Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.

  (** Both merges keep root 0, the smaller walk, with the earliest start. *)
  Goal TLB.Result.merge (lookup root_first) = [TLB.Result.make 0 [0x1003; 1] 0 1 None].
  Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.
  Goal TLB.Result.merge (lookup promise_first) = [TLB.Result.make 0 [0x1003; 1] 0 1 None].
  Proof. vm_compute. repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal]. Qed.
End MergeOrder.

(** A reload at an own TLBI's timestamp must survive when a previous TLBI
    already invalidated the entry. The old root is inactive during both
    invalidations, then is restored at the own TLBI's time. *)
Module ReloadAfterInvalidation.
  Definition imem : memoryMap :=
    ∅ |> mem_insert 0 8 0x1003 |> mem_insert 0x1000 8 0x401
      |> mem_insert 0x2000 8 0.
  Definition regs : registerMap :=
    ∅ |> reg_insert TCR_EL1 0 |> reg_insert TTBR0_EL1 0
      |> reg_insert ID_AA64MMFR1_EL1 0.
  Definition foreign := Ev.Tlbi (TLBI.All 1) 0 0.
  Definition own := Ev.Tlbi (TLBI.All 0) 0 0.
  Definition cache : result string TLB.t :=
    c ← TLB.init 0 imem regs;
    '(c, _) ← TLB.fill_cse 0 imem [] 0 0x2000 None c;
    '(c, _) ← TLB.fill_promise 0 imem [foreign] foreign c;
    '(c, _) ← TLB.fill_promise 0 imem [own; foreign] own c;
    '(c, _) ← TLB.fill_asid_root 0 imem [own; foreign] (0, 0, false) 2 c;
    mret c.
  Definition history :=
    c ← cache;
    fe ← TLB.FE.append (TLB.FE.make0 false 0 0 0 0x1003) 0 0x401;
    mret (TLB.vatlb c !! fe).
  Definition lookup (ifetch : bool) :=
    c ← cache;
    mret (TLB.lookup 0 imem [own; foreign] c ifetch false 0 2 2 2 0).

  Goal history = Ok (Some [(TLB.Entry.Load, 2%nat); (TLB.Entry.Tlbi 0, 2%nat);
    (TLB.Entry.Tlbi 1, 1%nat); (TLB.Entry.Load, 0%nat)]).
  Proof. vm_compute. reflexivity. Qed.

  (** Both data and instruction lookups retain the newly valid interval. *)
  Goal ∀ ifetch, lookup ifetch = Ok (Exec.make [TLB.Result.make 0 [0x1003; 0x401] 2 2 None] []).
  Proof.
    destruct ifetch; vm_compute;
      repeat first [reflexivity | apply bv_eq; reflexivity | progress f_equal].
  Qed.

  (** A load without an older valid interval must also be retained. *)
  Goal TLB.get_results_from_events 0 false 0 []
    [(TLB.Entry.Load, 1%nat); (TLB.Entry.Tlbi 0, 1%nat)] 0 1 None =
    [TLB.Result.make 0 [] 1 1 None].
  Proof. vm_compute. reflexivity. Qed.

  (** Adjacent valid intervals still coalesce. *)
  Goal TLB.get_results_from_events 0 false 0 []
    [(TLB.Entry.Load, 1%nat); (TLB.Entry.Tlbi 0, 1%nat); (TLB.Entry.Load, 0%nat)] 0 1 None =
    [TLB.Result.make 0 [] 0 1 None].
  Proof. vm_compute. reflexivity. Qed.
End ReloadAfterInvalidation.
