(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
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

From ASCommon Require Import Options.
From ASCommon Require Import Common Exec.

Require Import Interface.



(** This module specify general definitions of hardware architecture models for
    finite executions. Models only define behaviours up to a specified
    termination condition at which all relaxed behavior disappear as if it was
    an infinitely strong barrier.

    The definitions here will need to change to accommodate infinite execution
    or any externally observable behaviour (I/O). *)
Module TermModels (IWA : InterfaceWithArch). (* to be imported *)
  Import IWA.Arch.
  Import IWA.Interface.

  (** * Architectural States

      This section defines types to represent architecturally defined state.
      Those states allow to express initial and final states uniformly across
      all kinds of models *)

  (** ** Memory map *)

  (** Assuming bytes of 8 bits, not caring about weird architectures *)
  Definition memoryMap := gmap address (bv 8).
  #[global] Typeclasses Transparent memoryMap.

  (** Lookup a range of memory as a list of bytes.
      Returns [None] if any byte is missing *)
  Definition mem_lookup_bytes (addr : address) (n : N) (mm : memoryMap) :
      option (list (bv 8)) :=
    addr_range addr n |$> (mm !!.) |> list_of_options.

  (** Lookup a range of memory as a [bv] (little-endian).
      Returns [None] if any byte is missing *)
  Definition mem_lookup (addr : address) (n : N) (mm : memoryMap) :
      option (bv (8 * n)) :=
    bv_of_bytes _ <$> (mem_lookup_bytes addr n mm).

  (** Insert a sequence of bytes to memory (even if there were not there before).
      A normal memory write should check if bytes exists before writing them *)
  Fixpoint mem_insert_bytes (addr : address) (bytes : list (bv 8)) (mm : memoryMap) :
      memoryMap :=
    if bytes is byte :: bytes'
    then
      mm
      |> insert addr byte
      |> mem_insert_bytes (addr_addN addr 1) bytes'
    else mm.

  (** Write a bitvector to memory (little-endian). If the size is not a multiple
      of 8, it is zero extended to the next byte boundary*)
  Definition mem_insert_bv (addr : address) {m : N} (val : bv m) : memoryMap → memoryMap :=
    mem_insert_bytes addr (bv_to_bytes 8 val).

  (** Write a bitvector to memory (little-endian). *)
  Definition mem_insert (addr : address) (n : N) (val : bv (8 * n)) : memoryMap → memoryMap :=
    mem_insert_bytes addr (bv_to_bytes 8 val).

  (** Remove all bytes in the range provided from the memory map *)
  Definition mem_delete (addr : address) (n : N) : memoryMap → memoryMap :=
    fold_left (λ mm i, delete (addr_addN addr i) mm) (seqN 0 n).


  (** ** Register map *)
  Definition registerMap := dmap reg reg_type.
  #[global] Typeclasses Transparent registerMap.

  (** Helpers for type inference.
      WARNING: Do not eta-contract, otherwise OCaml extraction fails *)
  Definition reg_lookup (r : reg) : registerMap → option (reg_type r) :=
    dmap_lookup r.
  Definition reg_insert (r : reg) (rv : reg_type r) : registerMap → registerMap :=
    dmap_insert r rv.
  Definition reg_delete (r : reg) : registerMap → registerMap := dmap_delete r.

  (** A termination condition that define when each thread should stop.

      We expect this will be restricted to only being about the PC (RIP on x86)
      soon (maybe also the privilege level) *)
  Definition terminationCondition (n : nat) := fin n → registerMap → bool.

  (** ** Architectural state

  This module define a concept of an architecturally defined state. This is a
  state that is fully defined architecturally and independent of any
  micro-architectural details (and is therefore independent of concrete
  hardware).

  Such a state is an abstraction of a micro architectural state where all the
  caches are fully coherent, including things like TLB and icaches

  Those state should be interpretable by any concurrency models.

  Currently this does not support CHERI tags, even if the interface supports
  them *)
  Module archState. (* namespace *)

    (** An architecture state, [archState n] outside this module.
          [n] is the number of hardware threads*)
    Record t {n : nat} :=
      Make {
          memory : memoryMap;
          address_space : addr_space;
          regs: vec registerMap n;
        }.
    Arguments t : clear implicits.

    Definition is_terminated `(termCond : terminationCondition n) (s : t n) :=
      ∀ tid, termCond tid (s.(regs) !!! tid).

    #[export] Instance is_terminated_dec n term s :
      Decision (@is_terminated n term s).
    Proof. unfold_decide. Defined.

  End archState.
  Export (hints) archState.
  Notation archState := archState.t.

  (** * General terminating architecture model

      This section defines general terminating models which are CPU architecture
      models that are defined by the set of final state reachable from a given
      initial state. Given that there is no fundamental notion of termination,
      they use a provided [terminationCondition] that gives the program point at
      which one must examine final state as if that program point was a strong
      synchronization point. *)
  Module archModel. (* namespace *)

    (** ** Model results *)
    Module Res. (* namespace *)
      Section AMR.
      Context {flag : Type} {n : nat}.
      Context {termCond : terminationCondition n}.

      (** A model result is the output of a model on a given initial state. *)
      Inductive t :=
      | FinalState (s : archState n) (t : archState.is_terminated termCond s)
      (** Flagged behaviours is any kind of behaviour that is not fully
        described but is not a UB error. For example a BBM failure or any other
        constrained unpredictable behaviour for Arm. *)
      | Flagged (f : flag)
      (** An error means Undefined Behaviour (UB), this means that the initial
        state is out of scope for the model. Expected reasons for failures:

        - The model does not support a specific outcome.

        - An instruction issued a "GenericFail" (problem with an ISA model)

        - A fuel-limited executable model did not have enough fuel.

        - The test has an infinite execution (not the fault of the model) *)
      | Error (msg : string).

      Definition from_result
        (res : result string {s & archState.is_terminated termCond s}) : t :=
        match res with
        | Ok fs => FinalState fs.T1 fs.T2
        | CResult.Error msg => Error msg
        end.

      (** ** Sets of model results *)

      (** We are only interested in monadsets, so sets that support fmap, bind,
          mret, ... *)
      Context `{MonadSet E}.


      Definition finalStates (ts : E t) :=
        mset_omap
          (λ x, match x with | FinalState s t => Some (existT s t) | _ => None end) ts.

      Definition flags (ts : E t) :=
        mset_omap
          (λ x, match x with | Flagged fs => Some fs | _ => None end) ts.

      Definition errors (ts : E t) :=
        mset_omap (λ x, match x with | Error us => Some us | _ => None end) ts.

      Definition no_error (ts : E t) := errors ts ⊆ ∅.
      #[global] Typeclasses Transparent no_error.

      (* TODO SetUnfold instances for othrow *)
      #[local] Typeclasses Transparent othrow.

      #[global] Instance set_unfold_elem_of_flagifieds ts fs P:
        SetUnfoldElemOf (Flagged fs) ts P →
        SetUnfoldElemOf fs (flags ts) P.
      Proof using.
        tcclean.
        unfold flags.
        hauto l:on simp+:set_unfold simp+:eexists.
      Qed.
      #[global] Instance set_unfold_elem_of_finalStates ts fs P:
        SetUnfoldElemOf (FinalState fs.T1 fs.T2) ts P →
        SetUnfoldElemOf fs (finalStates ts) P.
      Proof using.
        tcclean.
        unfold finalStates.
        hauto l:on simp+:set_unfold simp+:eexists.
      Qed.
      #[global] Instance set_unfold_elem_of_errors ts msg P:
        SetUnfoldElemOf (Error msg) ts P → SetUnfoldElemOf msg (errors ts) P.
      Proof using.
        tcclean.
        unfold errors.
        hauto l:on simp+:set_unfold simp+:eexists.
      Qed.
      #[global] Typeclasses Opaque finalStates.
      #[global] Typeclasses Opaque flags.
      #[global] Typeclasses Opaque errors.

      (** A model is weaker if it allows more behaviors. This assumes all
          flagified behaviors to be independent of regular final states, later
          this may be expanded with an order on the flagified objects.
          weaker ts ts' ↔ "ts' is weaker than ts" ↔
          "ts' has more behaviours than ts" *)
      Definition weaker (ts ts' : E t) :=
        no_error ts' →
        finalStates ts ⊆ finalStates ts' ∧ flags ts ⊆ flags ts'
        ∧ no_error ts.

      (** A model is wider if it matches exactly the narrow model when the
          narrow model has no error. This means it is the same model except it
          has more coverage
          wider ts ts' ↔ "ts' is a strict extension of ts" ↔<→
          "ts' only adds new behaviours when ts says error"
       *)
      Definition wider (ts ts' : E t) :=
        (no_error ts' →
         finalStates ts ⊆ finalStates ts' ∧ flags ts ⊆ flags ts') ∧
          (no_error ts →
           finalStates ts ≡ finalStates ts' ∧
             flags ts ≡ flags ts' ∧
             no_error ts').

      Lemma wider_weaker (ts ts' : E t) : wider ts ts' → weaker ts' ts.
      Proof using. firstorder. Qed.

      Definition equiv (ts ts' : E t) := weaker ts ts' ∧ weaker ts' ts.

      Lemma equiv_wider (ts ts' : E t) :
        equiv ts ts' ↔ wider ts ts' ∧ (no_error ts' → no_error ts).
      Proof using. firstorder. Qed.

      Lemma equiv_wider' (ts ts' : E t) : equiv ts ts' → wider ts ts'.
      Proof using. firstorder. Qed.

      Lemma equiv_errors (ts ts' : E t) :
        equiv ts ts' → (no_error ts ↔ no_error ts').
      Proof using. firstorder. Qed.

      End AMR.
      Arguments t : clear implicits.

      Definition from_exec {St n term}
          (e : Exec.t St string {s & archState.is_terminated term s}) (st : St) :
          listset (t ∅ n term) :=
        e st |> Exec.to_stateful_result_list |$> snd |$> from_result |> Listset.

    End Res.
    Notation res := Res.t.

    (** ** Models *)
    Section Model.
      Context `{MonadSet E}.
      Context {flag : Type}.

      (** Definition of an architectural model. This is parametric on the set
          type [E] of results, so that this definition supports both executable
          and non-executable models *)
      Definition t : Type :=
        ∀ (n : nat) (term : terminationCondition n),
        archState n → E (res flag n term).

      Definition weaker (m m' : t) : Prop
        := ∀ n term initSt, Res.weaker (m n term initSt) (m' n term initSt).

      Definition wider (m m' : t)
        := ∀ n term initSt, Res.wider (m n term initSt) (m' n term initSt).

      Instance equiv : Equiv t :=
        λ m m', ∀ n term initSt, Res.equiv (m n term initSt) (m' n term initSt).

      Lemma wider_weaker (m m' : t) : wider m m' → weaker m' m.
      Proof using.
        unfold wider, weaker. intros. apply Res.wider_weaker. naive_solver.
      Qed.

      Lemma equiv_weaker (m m' : t) :
        equiv m m' ↔ weaker m m' ∧ weaker m' m.
      Proof using. unfold equiv, weaker, Res.equiv. naive_solver. Qed.

      Lemma equiv_wider (m m' : t) :
        equiv m m' ↔
          wider m m' ∧
          (∀ n term initSt,
             Res.no_error (m' n term initSt) → Res.no_error (m n term initSt)).
      Proof using.
        unfold equiv, wider. setoid_rewrite Res.equiv_wider. naive_solver.
      Qed.
      Lemma equiv_wider' (m m' : t) :
        equiv m m' → wider m m'.
      Proof using. rewrite equiv_wider. naive_solver. Qed.
      Lemma equiv_errors (m m' : t) :
        equiv m m' →
        (∀ n term initSt,
           Res.no_error (m n term initSt) ↔ Res.no_error (m' n term initSt)).
      Proof using.
        unfold equiv. intros. apply Res.equiv_errors. naive_solver.
      Qed.

    End Model.
    Arguments t : clear implicits.

    (** Change the set type of a model *)
    Definition map_set {E E' flag} (f : ∀ {A}, E A → E' A) (m : t E flag)
      : t E' flag := λ n term initSt, f (m n term initSt).

    (** Non computational model *)
    Notation nc := (t propset).

    (** Computational model *)
    Notation c := (t listset).

    Definition to_nc {flag} `{MonadSet E} : t E flag → nc flag :=
      map_set (λ A, set_to_propset).
  End archModel.


End TermModels.

Module Type TermModelsT (IWA : InterfaceWithArch).
  Include TermModels IWA.
End TermModelsT.
