(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
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

Require Import ASCommon.Options.
Require Import ArmInst.
Require Import ASCommon.Common.
Require Import ASCommon.Exec.
Require Import ASCommon.StateT.
Require Import ASCommon.Effects.

Section Seq.

Context (regs_whitelist : option (gset reg)).

(** A sequential state for bookkeeping reads and writes to registers/memory in
    gmaps, as well as, the initial state *)
Record seq_state := {
  initSt : MState.init 1;
  mem : gmap pa (bv 8);
  regs : gmap reg (bv 64);
  itrs : list (iTrace ())
}.

Global Instance eta_seq_state : Settable seq_state :=
  settable! Build_seq_state <initSt;mem;regs;itrs>.

Notation seqmon := (Exec.t seq_state string).

Definition read_reg_seq_state (reg : reg) (seqst : seq_state) : reg_type reg:=
  if (seqst.(regs) !! reg) is Some v
  then regt_of_bv64 v
  else (seqst.(initSt).(MState.regs) !!! 0%fin) reg.

Definition read_byte_seq_state_flag (seqst : seq_state) (pa : pa) : bv 8 * bool :=
  if (seqst.(mem) !! pa) is Some v
  then (v, true)
  else (seqst.(initSt).(MState.memory) pa, false).

Definition read_byte_seq_state (seqst : seq_state) (pa : pa) : bv 8 :=
  fst (read_byte_seq_state_flag seqst pa).

Definition read_mem_seq_state (n : N) (pa : pa) (seqst : seq_state) : bv (8 * n) :=
  pa_range pa n |$> read_byte_seq_state seqst |> bv_of_bytes (8 * n).

Definition read_mem_seq_state_flag (n : N) (pa : pa) (seqst : seq_state)
  : bv (8 * n) * bool :=
  let bf := pa_range pa n |$> read_byte_seq_state_flag seqst in
  let '(bytes, flags) := split bf in
    (bv_of_bytes (8 * n) bytes, existsb id flags).

Fixpoint write_mem_seq_state (pa : pa) (bytes : list (bv 8)) : seqmon unit :=
  if bytes is byte :: bytes
  then
    msetv (lookup pa ∘ mem) (Some byte);;
    write_mem_seq_state (pa_addZ pa 1) bytes
  else mret ().

(** Combines a gmap with a registerMap to a new registerMap that was updated
    with the values from the gmap *)
Definition seq_state_to_init_regs (regs_map : gmap reg (bv 64))
  (regs_vec : vec registerMap 1) : vec registerMap 1 :=
  [# (λ reg, if (regs_map !! reg) is Some v then regt_of_bv64 v else (regs_vec !!! 0%fin) reg)].

(** Combines a gmap with a memoryMap to a new memoryMap that was updated with the
    values from the gmap *)
Definition seq_state_to_init_mem (mem_map : gmap pa (bv 8)) (mem : memoryMap)
  : memoryMap :=
  λ pa, if (mem_map !! pa) is Some v then v else mem pa.

(** Turn a seq_state into an MState.init by updating the initial state with the
    gmaps for registers and memory *)
Definition seq_state_to_init (seqs : seq_state) : MState.init 1 :=
  {| MState.state :=
      {| MState.memory :=
          seq_state_to_init_mem seqs.(mem) seqs.(initSt).(MState.memory);
         MState.regs :=
          seq_state_to_init_regs seqs.(regs) seqs.(initSt).(MState.regs) |};
     MState.termCond := seqs.(initSt).(MState.termCond) |}.

(** This is the effect handler for the outcome effect in the sequential model *)
Definition sequential_model_outcome (call : outcome) : seqmon (eff_ret call) :=
  match call with
  | RegRead reg racc => mget (read_reg_seq_state reg)
  | RegWrite reg racc val =>
    if regs_whitelist is Some rwl
    then if bool_decide (reg ∈ rwl)
      then msetv (lookup reg ∘ regs) (Some (regt_to_bv64 val))
      else mthrow "Write to illegal register"
    else msetv (lookup reg ∘ regs) (Some (regt_to_bv64 val))
  | MemRead n rr =>
    if is_ifetch rr.(ReadReq.access_kind) || is_ttw rr.(ReadReq.access_kind)
    then
      '(read, flag) ← mget (read_mem_seq_state_flag n rr.(ReadReq.pa));
      if (flag : bool)
      then mthrow "iFetch or TTW read from modified memory"
      else mret (inl (read, None))
    else
      read ← mget (read_mem_seq_state n rr.(ReadReq.pa));
      mret (inl (read, None))
  | MemWriteAddrAnnounce _ _ _ _ => mret ()
  | MemWrite n wr =>
    write_mem_seq_state wr.(WriteReq.pa) (wr.(WriteReq.value) |> bv_to_bytes 8);;
    mret (inl true)
  | Barrier _ => mret ()
  | CacheOp _ => mret ()
  | TlbOp _ => mret ()
  | TakeException _ => mthrow "Taking exception is not supported"
  | ReturnException => mret ()
  | TranslationStart _ => mret ()
  | TranslationEnd _ => mret ()
  | GenericFail s => mthrow ("Instruction failure: " ++ s)%string
  end.

Definition sequential_model_outcome_logged : ∀ call : outcome, seqmon (eff_ret call) :=
  (λ ev,
    mset itrs (λ l, (hd FMon.FTNothing l |> set fst (cons ev)) :: tl l);;
    mret ())
  |> FMon.fHandler_logger sequential_model_outcome.

(** Run instructions until a final state has been reached or fuel is depleted *)
Fixpoint sequential_model_seqmon (fuel : nat) (isem : iMon ())
  : seqmon (MState.final 1) :=
  if fuel is S fuel
  then
    mset itrs (cons FMon.FTNothing);;
    FMon.cinterp (sequential_model_outcome) isem;;
    mset itrs (λ l, (List.rev (hd FMon.FTNothing l).1, FMon.FTERet ()) :: tl l);;
    st ← mget seq_state_to_init;
    if MState.finalize st is Some final
    then
      mset itrs (@List.rev _);;
      mret final
    else sequential_model_seqmon fuel isem
  else mthrow "Out of fuel".

(** Top-level one-threaded sequential model function that takes fuel (guaranteed
    termination) and an instruction monad, and returns a computational set of
    all possible final states. *)
Definition sequential_modelc (fuel : nat) (isem : iMon ()) : (Model.c ∅) :=
  λ n,
  match n with
  | 1 => λ initSt : MState.init 1,
           Listset
            (sequential_model_seqmon fuel isem {| initSt := initSt; regs := ∅; mem := ∅; itrs := [] |}
             |> Exec.to_stateful_result_list
             |$> snd
             |$> Model.Res.from_result)
  | _ => λ _, mret (Model.Res.Error "Exptected one thread")
  end.

End Seq.
