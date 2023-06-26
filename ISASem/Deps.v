Require Import Strings.String.
Require Import stdpp.unstable.bitvector.

(* This is needed because sail cannot export into multiple Coq files *)
Require Import SailArmInstTypes.
Require Import Interface.

Require Import SSCCommon.Common.

Local Open Scope stdpp_scope.
Local Open Scope Z_scope.


Module DepsDefs (IWA : InterfaceWithArch). (* to be imported *)
  Import IWA.

  Module DepOn.
    Record t :=
      make
        {
          (** The list of registers the effect depends on. *)
          regs : list reg;
          (** The list of memory access the effect depends on. The number
              corresponds to the memory reads done by the instruction in the
              order specified by the instruction semantics. The indexing starts
              at 0. *)
          mem_reads : list nat
        }.

    Definition emp := make [] [].
  End DepOn.

  Module Footprint.

    (* This module is still quite experimental and subject to change, possibly
    more frequently than the rest of the interface *)

    Record taints := {
        regs : list reg;
        mem : bool
      }.

    Definition taints2DepOn (tt : taints) (num_read : nat) :=
      DepOn.make tt.(regs) (if tt.(mem) then seq 0 num_read else []).

    Record t := {
        (** Dependencies feeding into the data of writes *)
        writes_data : taints;
        (** Dependencies feeding into the address of memory accesses *)
        memory_address: taints;
        (** Dependencies feeding into a branch address *)
        branch_dep: taints;
        (** List of register read (dependencies for any register write) *)
        register_reads : list reg;
        (** List of written registers that only use register reads *)
        register_writes : list reg;
        (** List of written registers that also use memory reads *)
        register_writes_tainted : list reg;
        (** All register read-write pairs to the following registers are
          ignored for tracking dependencies within an instruction. If
          the first element of the tuple is None then all writes are
          ignored *)
        register_write_ignored : list ((option reg) * reg);
        is_store : bool;
        is_load : bool;
        is_branch : bool;
        is_exclusive : bool;
      }.

    Definition reg_write_dep (fprt : t) (wreg : reg) (num_read : nat) : DepOn.t :=
      let regs :=
        if decide ((None, wreg) ∈ fprt.(register_write_ignored))
        then []
        else filter (fun rreg => (Some rreg, wreg) ∉ fprt.(register_write_ignored))
               fprt.(register_reads)
      in
      let mem :=
        if decide (wreg ∈ fprt.(register_writes_tainted))
        then seq 0 num_read
        else []
      in
      DepOn.make regs mem.


    Definition mem_read_dep (fprt : t) (num_read : nat) : DepOn.t :=
      taints2DepOn fprt.(memory_address) num_read.

    (* addr then data *)
    Definition mem_write_dep (fprt : t) (num_read : nat) : DepOn.t * DepOn.t :=
      (taints2DepOn fprt.(memory_address) num_read,
      taints2DepOn fprt.(writes_data) num_read).

    Definition ctrl_dep (fprt : t) (num_read : nat) : DepOn.t :=
      taints2DepOn fprt.(branch_dep) num_read.

    Definition special_dep (fprt : t) (num_read : nat) : DepOn.t :=
      DepOn.make fprt.(register_reads) [].

  End Footprint.
End DepsDefs.

Module Type InterfaceWithDeps.
  Declare Module IWA : InterfaceWithArch.
  Include IWA.
  Include DepsDefs IWA.
End InterfaceWithDeps.

(** Optional system for dependency computation *)
Module Type ArchDeps (IWD : InterfaceWithDeps).
  Import IWD.

  (** Extra context for footprint analysis *)
  Parameter footprint_context : Type.

  Parameter get_footprint_context :
    forall {deps : Type} {out : Type -> Type}, iMon deps out footprint_context.

  Parameter fault_add_empty_deps : fault unit -> fault DepOn.t.

  Parameter fault_add_deps : Footprint.t -> fault unit -> fault DepOn.t.
End ArchDeps.

Module DepsComp (IWD : InterfaceWithDeps) (AD : ArchDeps IWD).
  Import IWD.
  Import AD.

  Definition footprint_model := bvn -> footprint_context -> Footprint.t.

  Definition add_fine_grained_dependency_fprt_outcome {A : Type}
      (out : outcome unit empOutcome A) (fprt : Footprint.t) (num_read : nat)
      : nat * outcome DepOn.t empOutcome A :=
    match out with
    | RegRead reg direct => (num_read, RegRead reg direct)
    | RegWrite reg direct () val =>
        (num_read,
          RegWrite reg direct (Footprint.reg_write_dep fprt reg num_read) val)
    | MemRead n rr =>
        rr |> ReadReq.setv_deps (Footprint.mem_read_dep fprt num_read)
           |> MemRead n
           |> (S num_read,.)
    | MemWrite n wr =>
        let (addr_dep, data_dep) := Footprint.mem_write_dep fprt num_read in
        wr |> WriteReq.setv_deps addr_dep data_dep
           |> MemWrite n
           |> (num_read,.)
    | InstrAnnounce opcode => (num_read, InstrAnnounce opcode)
    | BranchAnnounce pa () =>
        Footprint.ctrl_dep fprt num_read
        |> BranchAnnounce pa
        |> (num_read,.)
    | Barrier barrier => (num_read, Barrier barrier)
    | CacheOp () cop =>
        (num_read, CacheOp (Footprint.special_dep fprt num_read) cop)
    | TlbOp () tlbop =>
        (num_read, TlbOp (Footprint.special_dep fprt num_read) tlbop)
    | TakeException fault =>
        (num_read, TakeException (fault_add_deps fprt fault))
    | ReturnException pa => (num_read, ReturnException pa)
    | GenericFail msg => (num_read, GenericFail msg)
    | Choose n => (num_read, Choose n)
    | Discard => (num_read, Discard)
    | ExtraOutcome e => match e with end
    end.

  Fixpoint add_fine_grained_dependency_fprt {A : Type}
      (orig : iMon unit empOutcome A) (fprt : Footprint.t) (num_read : nat)
      : iMon DepOn.t empOutcome A :=
    match orig with
    | Ret a => Ret a
    | Next outcome k =>
        let '(num_read, newoutcome) :=
          add_fine_grained_dependency_fprt_outcome outcome fprt num_read
        in
        Next newoutcome (fun x => add_fine_grained_dependency_fprt (k x) fprt num_read)
    end.

  Definition add_empty_dependency_outcome {A : Type}
      (out : outcome unit empOutcome A) (num_read : nat)
      : nat * outcome DepOn.t empOutcome A :=
    match out with
    | RegRead reg direct => (num_read, RegRead reg direct)
    | RegWrite reg direct () val =>
        (num_read,
          RegWrite reg direct DepOn.emp val)
    | MemRead n rr =>
        rr |> ReadReq.setv_deps DepOn.emp
           |> MemRead n
           |> (S num_read,.)
    | MemWrite n wr =>
        wr |> WriteReq.setv_deps DepOn.emp DepOn.emp
           |> MemWrite n
           |> (num_read,.)
    | InstrAnnounce opcode => (num_read, InstrAnnounce opcode)
    | BranchAnnounce pa () => (num_read, BranchAnnounce pa DepOn.emp)
    | Barrier barrier => (num_read, Barrier barrier)
    | CacheOp () cop => (num_read, CacheOp DepOn.emp cop)
    | TlbOp () tlbop => (num_read, TlbOp DepOn.emp tlbop)
    | TakeException fault =>
        (num_read, TakeException (fault_add_empty_deps fault))
    | ReturnException pa => (num_read, ReturnException pa)
    | GenericFail msg => (num_read, GenericFail msg)
    | Choose n => (num_read, Choose n)
    | Discard => (num_read, Discard)
    | ExtraOutcome e => match e with end
    end.

  (** Add fine grained dependencies after the InstrAnnounce depending on a
  footprint model *)
  Fixpoint add_fine_grained_dependency {A : Type} (orig : iMon unit empOutcome A)
      (fmod : footprint_model) (num_read : nat) : iMon DepOn.t empOutcome A :=
    match orig with
    | Ret a => Ret a
    | Next (InstrAnnounce opcode) k =>
        ctxt ← get_footprint_context;
        let fprt := fmod opcode ctxt in
        add_fine_grained_dependency_fprt (k ()) fprt num_read
    | Next outcome k =>
        let '(num_read, newoutcome) :=
          add_empty_dependency_outcome outcome num_read
        in
        Next newoutcome (fun x => add_fine_grained_dependency (k x) fmod num_read)
    end.

End DepsComp.

Module Type InterfaceWithDepsComp.
  Declare Module IWD : InterfaceWithDeps.
  Declare Module AD : ArchDeps IWD.
  Include IWD.
  Include AD.
  Include DepsComp IWD AD.
End InterfaceWithDepsComp.


(* DepOn *)

(* Full Footprint type *)

(* Conversion boilerplate code *)
