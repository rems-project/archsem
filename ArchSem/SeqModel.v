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

Require Import Interface.
Require Import TermModels.


(* Module to be imported *)
Module SequentialModel (IWA : InterfaceWithArch) (Term : TermModelsT IWA)
    (NC : NoCHERI IWA).
  Import IWA.Arch.
  Import IWA.Interface.
  Import Term.

  Section Seq.

    Context (regs_whitelist : option (gset reg)).

    (** A sequential state for bookkeeping reads and writes to registers/memory
        in gmaps, as well as, the initial state *)
    Record seq_state := {
        (** The sequential model is simple enough to use directly a [MState.t]
            as an internal mutable state *)
        sst : archState 1;
        (** [written] records addresses that were written to since the start *)
        written : gset address;
      }.

    (** Sequential state monad *)
    Notation seqmon := (Exec.t seq_state string).

    Definition read_reg_seq_state (reg : reg) (seqst : seq_state) :
        option (reg_type reg) :=
      seqst.(sst).(archState.regs) !!! 0%fin |> dmap_lookup reg.

    Definition write_reg_seq_state (reg : reg) (val : reg_type reg) :
        seq_state → seq_state :=
      set (lookup_total 0%fin ∘ archState.regs ∘ sst)
        (dmap_insert reg val).

    Definition read_byte_seq_state (seqst : seq_state) (addr : address) :
        option (bv 8) :=
      seqst.(sst).(archState.memory) !! addr.

    Definition read_mem_seq_state (n : N) (addr : address) (seqst : seq_state) :
        option (bv (8 * n)) :=
      addr_range addr n
      |$> read_byte_seq_state seqst
      |> list_of_options
      |$> bv_of_bytes (8 * n).

    (** Check if a region of memory was written to or not *)
    Definition mem_was_written (n : N) (addr : address) (seqst : seq_state) : bool :=
      bool_decide (∃ a ∈ addr_range addr n, a ∈ seqst.(written)).

    Definition check_address_space (pas : addr_space) : seqmon unit :=
      init_pas ← mget (archState.address_space ∘ sst);
      guard_or "Wrong address space" (pas = init_pas);;
      mret ().

    Fixpoint write_mem_seq_state (addr : address) (bytes : list (bv 8)) : seqmon unit :=
      if bytes is byte :: bytes
      then
        opt ← mget $ read_mem_seq_state (N.of_nat (length bytes)) addr;
        guard_or "Memory isn't mapped to write" $ is_Some opt;;
        msetv (lookup addr ∘ archState.memory ∘ sst) (Some byte);;
        mset written (.∪{[addr]});;
        write_mem_seq_state (addr `+Z` 1)%bv bytes
      else mret ().

    (** This is the effect handler for the outcome effect in the sequential model *)
    Equations sequential_model_outcome (call : outcome) : seqmon (eff_ret call) :=
      | RegRead reg racc =>
          opt ←  mget (read_reg_seq_state reg);
          othrow ("Register " ++ pretty reg ++ " not found")%string opt
      | RegWrite reg racc val =>
          opt ←  mget (read_reg_seq_state reg);
          guard_or ("Writing register " ++ pretty reg ++ " not in initial state")%string $
            is_Some opt;;
          if regs_whitelist is Some rwl
          then
            if bool_decide (reg ∈ rwl)
            then mSet $ write_reg_seq_state reg val
            else mthrow "Write to illegal register (not in whitelist)"
          else mSet $ write_reg_seq_state reg val
      | MemRead (MemReq.make macc addr addr_space size 0) =>
          check_address_space addr_space;;
          ( if is_ifetch macc || is_ttw macc
            then
              was_written ← mget (mem_was_written size addr);
              guard_or "Ifetch or TTW reading from modified memory" (negb was_written);;
              mret ()
            else mret ());;
          opt ← mget (read_mem_seq_state size addr);
          read ← othrow ("Memory not found at " ++ (pretty addr))%string opt;
          mret (Ok (read, bv_0 _))
      | MemRead _ => mthrow "CHERI tags are unsupported for now"
      | MemWriteAddrAnnounce mr => check_address_space mr.(MemReq.address_space)
      | MemWrite (MemReq.make macc addr addr_space size 0) val _ =>
          guard_or "Non-explicit write" $ is_explicit macc;;
          check_address_space addr_space;;
          write_mem_seq_state addr (val |> bv_to_bytes 8);;
        mret (Ok ())
      | MemWrite _ _ _ => mthrow "CHERI tags are unsupported for now"
      | Barrier _ => mret ()
      | CacheOp _ => mret ()
      | TlbOp _ => mret ()
      | TakeException _ => mthrow "Taking exception is not supported"
      | ReturnException => mret ()
      | TranslationStart _ => mret ()
      | TranslationEnd _ => mret ()
      | GenericFail s => mthrow ("Instruction failure: " ++ s)%string.

    (** Run instructions until a final state has been reached or fuel is depleted *)
    Fixpoint sequential_model_seqmon (fuel : nat) (isem : iMon ()) (term : terminationCondition 1)
      : seqmon {s : archState 1 & archState.is_terminated term s}:=
      if fuel is S fuel
      then
        FMon.cinterp sequential_model_outcome isem;;
        st ← mget sst;
        if decide (archState.is_terminated term st) is left p
        then mret (existT st p)
        else sequential_model_seqmon fuel isem term
      else mthrow "Out of fuel".

    (** Top-level one-threaded sequential model function that takes fuel (guaranteed
        termination) and an instruction monad, and returns a computational set of
        all possible final states. *)
    Definition sequential_modelc (fuel : nat) (isem : iMon ()) : (archModel.c ∅) :=
      λ n,
      match n with
      | 1 => λ term initSt,
        {| sst := initSt; written := ∅ |}
        |> archModel.Res.from_exec (sequential_model_seqmon fuel isem term)
      | _ => λ _ _, mret (archModel.Res.Error "Exptected one thread")
      end.

  End Seq.
End SequentialModel.
