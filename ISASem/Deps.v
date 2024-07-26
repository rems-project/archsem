Require Import Strings.String.
Require Import stdpp.bitvector.bitvector.

(* This is needed because sail cannot export into multiple Coq files *)
Require Import SailArmInstTypes.
Require Import Interface.

Require Import SSCCommon.Options.
Require Import SSCCommon.Common.
Require Import SSCCommon.Effects.
Require Import SSCCommon.FMon.
Require Import SSCCommon.StateT.

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

    Global Instance eq_dec : EqDecision t.
    Proof using. solve_decision. Defined.

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
    ∀ {deps : Type}, iMon deps footprint_context.

  Parameter fault_add_empty_deps : fault unit → fault DepOn.t.

  Parameter fault_add_deps : Footprint.t → fault unit → fault DepOn.t.
End ArchDeps.

Module DepsComp (IWD : InterfaceWithDeps) (AD : ArchDeps IWD).
  Import IWD.
  Import AD.

  Definition footprint_model := bvn → footprint_context → Footprint.t.

  Record footprint_state := { num_reads : nat; fprt : option Footprint.t}.


  #[local] Notation ReplEffD call := (ReplEff (call : outcome DepOn.t)).
  Definition add_fine_grained_dependency_fprt_outcome
    (out : outcome unit) (fprt : Footprint.t) (num_read : nat)
    : nat * repl_eff out (outcome DepOn.t) :=
    match out with
    | RegRead reg direct as rr =>
        (num_read, ReplEffD (RegRead reg direct))
    | RegWrite reg direct () val =>
        (num_read,
          ReplEffD (RegWrite reg direct (Footprint.reg_write_dep fprt reg num_read) val))
    | MemRead n rr =>
        let rr := ReadReq.setv_deps (Footprint.mem_read_dep fprt num_read) rr in
        (S num_read, ReplEffD (MemRead n rr))
    | MemWrite n wr =>
        let (addr_dep, data_dep) := Footprint.mem_write_dep fprt num_read in
        let wr := WriteReq.setv_deps addr_dep data_dep wr in
        (num_read, ReplEffD (MemWrite n wr))
    | InstrAnnounce opcode => (num_read, ReplEffD (InstrAnnounce opcode))
    | BranchAnnounce pa () =>
        (num_read, ReplEffD (BranchAnnounce pa (Footprint.ctrl_dep fprt num_read)))
    | Barrier barrier => (num_read, ReplEffD (Barrier barrier))
    | CacheOp () cop =>
        (num_read, ReplEffD (CacheOp (Footprint.special_dep fprt num_read) cop))
    | TlbOp () tlbop =>
        (num_read, ReplEffD (TlbOp (Footprint.special_dep fprt num_read) tlbop))
    | TakeException fault =>
        (num_read, ReplEffD (TakeException (fault_add_deps fprt fault)))
    | ReturnException pa => (num_read, ReplEffD (ReturnException pa))
    | GenericFail msg => (num_read, ReplEffD (GenericFail msg))
    end.

  Definition add_empty_dependency_outcome (out : outcome unit) (num_read : nat)
      : nat * repl_eff out (outcome DepOn.t) :=
    match out with
    | RegRead reg direct => (num_read, ReplEffD (RegRead reg direct))
    | RegWrite reg direct () val =>
        (num_read,
          ReplEffD (RegWrite reg direct DepOn.emp val))
    | MemRead n rr =>
        let rr := ReadReq.setv_deps DepOn.emp rr in
        (S num_read, ReplEffD (MemRead n rr))
    | MemWrite n wr =>
        let wr := WriteReq.setv_deps DepOn.emp DepOn.emp wr in
        (num_read, ReplEffD (MemWrite n wr))
    | InstrAnnounce opcode => (num_read, ReplEffD (InstrAnnounce opcode))
    | BranchAnnounce pa () => (num_read, ReplEffD (BranchAnnounce pa DepOn.emp))
    | Barrier barrier => (num_read, ReplEffD (Barrier barrier))
    | CacheOp () cop => (num_read, ReplEffD (CacheOp DepOn.emp cop))
    | TlbOp () tlbop => (num_read, ReplEffD (TlbOp DepOn.emp tlbop))
    | TakeException fault =>
        (num_read, ReplEffD (TakeException (fault_add_empty_deps fault)))
    | ReturnException pa => (num_read, ReplEffD (ReturnException pa))
    | GenericFail msg => (num_read, ReplEffD (GenericFail msg))
    end.

  Program Definition add_dependency_handler (fmod : footprint_model) :
    fHandler (outcome unit) (stateT (nat * option Footprint.t) (iMon DepOn.t)) :=
    λ out,
      '(num_read, fprt) ← mGet;
      match fprt with
      | Some fprt =>
          let '(num_read, rout) :=
            add_fine_grained_dependency_fprt_outcome out fprt num_read
          in
          msetv fst num_read;;
          mcall_repl rout
      | _ =>
          match out with
          | InstrAnnounce opcode =>
              ctxt ← st_lift get_footprint_context;
              let fprt' : Footprint.t := fmod opcode ctxt in
              msetv snd (Some fprt')
          | out =>
              let '(num_read, rout) :=
                add_empty_dependency_outcome out num_read
              in
              msetv fst num_read;;
              mcall_repl rout
          end
      end.


  (** Add fine grained dependencies after the InstrAnnounce depending on a
      footprint model *)
  Definition add_fine_grained_dependency {A : Type} (prog : iMon unit A)
      (fmod : footprint_model) : iMon DepOn.t A :=
    cinterp (add_dependency_handler fmod) prog (0%nat, None) |$> snd.

End DepsComp.

Module Type InterfaceWithDepsComp.
  Declare Module IWD : InterfaceWithDeps.
  Declare Module AD : ArchDeps IWD.
  Include IWD.
  Include AD.
  Include DepsComp IWD AD.
End InterfaceWithDepsComp.
