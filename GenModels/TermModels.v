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

Require Import Strings.String.

Require Import ASCommon.Options.
Require Import ASCommon.Common.
Require Import ASCommon.Exec.

Require Import Relations.
Require Import Program.

Open Scope Z_scope.
Open Scope stdpp_scope.

Require Import ISASem.Interface.


(** This module specify general definitions of hardware models over finite
    executions. Models only define behavior up to a specified termination
    condition at which all relaxed behavior disappear as if it was an infinitely
    strong barrier.

    The definitions in this module are highly experimental and will change
    heavily depending on various requirements that are not yet known.
 *)
Module TermModels (IWA : InterfaceWithArch). (* to be imported *)
  Import IWA.Arch.
  Import IWA.Interface.

  (** Assuming bytes of 8 bits, not caring about weird architectures for now *)
  Definition memoryMap := pa → bv 8.
  #[global] Typeclasses Transparent memoryMap.

  (** Read a sequence of bytes from  a [memoryMap]:  *)
  Definition memoryMap_read (mm : memoryMap) (pa : pa) (n : N) : bv (8 * n) :=
    pa_range pa n |$> mm |> bv_of_bytes (8 * n).

  Definition registerMap := ∀ r : reg, reg_type r.
  #[global] Typeclasses Transparent registerMap.

  (** A termination condition that define when each thread should stop.

      For now it only needs a register maps as I expect it will most often just
      be `PC = ...` or `PC >= ...` *)
  Definition terminationCondition (n : nat) := fin n → registerMap → bool.

  (** This module define a concept of simple machine state without any
      micro-architectural details.

      TODO decide among other possible name:
      - SeqState, for sequential state.
      - SimpState, for simple state.
      - SState for one of the above but shorter. *)
  Module MState. (* namespace *)

    Section MS.
    Context {n : nat}. (* thread number *)

    (** A simple machine state for comparing models and defining sequential
        semantics *)
    Record t :=
      Make {
          memory : memoryMap;
          regs: vec registerMap n;
        }.

    (** A initial state for a machine model test. This means that the
        machine must stop at the required termination condition *)
    Record init :=
      MakeI {
          state :> t;
          termCond : terminationCondition n
        }.

    Definition is_terminated (s : init) :=
      ∀ tid, s.(termCond) tid (s.(regs) !!! tid).
    Typeclasses Transparent is_terminated.

    (** A final state for a machine model test. This means that the machine has
        stopped at the required termination condition *)
    Record final :=
      MakeF {
          istate :> init;
          terminated' : bool_decide (is_terminated istate)
        }.

    Definition terminated (f : final) : is_terminated f :=
      bool_decide_unpack (terminated' f).

    Definition finalize (s : init) : option final :=
      match decide (is_terminated s) with
      | left yes => Some $ MakeF s $ bool_decide_pack yes
      | right _ => None
      end.


    Lemma finalize_same (s : init) (f : final) : finalize s = Some f → s = f.
    Proof. unfold finalize. hauto lq:on. Qed.

    Lemma finalize_final (s : final) : finalize s = Some s.
    Proof.
      unfold finalize. destruct s.
      case_decide.
      - repeat f_equal;apply proof_irrel.
      - hauto lqb:on.
    Qed.
    End MS.
    Arguments t : clear implicits.
    Arguments init : clear implicits.
    Arguments final : clear implicits.

  End MState.
  (* Make the coercions available without importing the module *)
  Global Coercion MState.state : MState.init >-> MState.t.
  Global Coercion MState.istate : MState.final >-> MState.init.

  Class SubsetEqEquiv (E : Type) {sse : SubsetEq E} {eq : Equiv E} :=
    subseteq_equiv : forall a b : E, a ≡ b ↔ a ⊆ b ∧ b ⊆ a.

  Global Instance set_subseteq_equiv_instance `{ElemOf A C} :
    SubsetEqEquiv C.
  Proof. intros a b. set_solver. Qed.

  Module Model. (* namespace *)
    Module Res. (* namespace *)
      Section MR.
      Context {unspecified : Type} {n : nat}.
      (* TODO consider replacing this type with:
         result string (MState.final n + unspecified) *)
      Inductive t :=
      | FinalState (finSt : MState.final n)
      (** Unspecified is any kind of behavior that is not fully specified but is
        not a model error. For example a BBM failure. *)
      | Unspecified (unspec : unspecified)
      (** Expected reasons for failures:

        - The model does not support a specific outcome.

        - An instruction issued a "GenericFail" (problem with an ISA model)

        - A fuel-limited executable model did not have enough fuel.

        - The test has an infinite execution (not the fault of the model) *)
      | Error (msg : string).

      Definition from_result (res : result string (MState.final n)) : t :=
        match res with
        | Ok fs => FinalState fs
        | CResult.Error msg => Error msg
        end.

      (** * Sets of model results *)

      (** We are only interested in monadsets, so sets that support fmap, bind,
      ... *)
      Context `{MonadSet E}.

      Definition finalStates (ts : E t) :=
        mset_omap
          (λ x, match x with | FinalState fs => Some fs | _ => None end) ts.

      Definition unspecifieds (ts : E t) :=
        mset_omap
          (λ x, match x with | Unspecified us => Some us | _ => None end) ts.

      Definition errors (ts : E t) :=
        mset_omap (λ x, match x with | Error us => Some us | _ => None end) ts.

      Definition no_error (ts : E t) := errors ts ⊆ ∅.
      #[global] Typeclasses Transparent no_error.

      (* TODO SetUnfold instances for othrow *)
      #[local] Typeclasses Transparent othrow.

      #[global] Instance set_unfold_elem_of_unspecifieds ts us P:
        SetUnfoldElemOf (Unspecified us) ts P →
        SetUnfoldElemOf us (unspecifieds ts) P.
      Proof using. tcclean. unfold unspecifieds. hauto l:on simp+:set_unfold simp+:eexists. Qed.
      #[global] Instance set_unfold_elem_of_finalStates ts fs P:
        SetUnfoldElemOf (FinalState fs) ts P →
        SetUnfoldElemOf fs (finalStates ts) P.
      Proof using. tcclean. unfold finalStates. hauto l:on simp+:set_unfold simp+:eexists. Qed.
      #[global] Instance set_unfold_elem_of_errors ts msg P:
        SetUnfoldElemOf (Error msg) ts P → SetUnfoldElemOf msg (errors ts) P.
      Proof using. tcclean. unfold errors. hauto l:on simp+:set_unfold simp+:eexists. Qed.
      #[global] Typeclasses Opaque finalStates.
      #[global] Typeclasses Opaque unspecifieds.
      #[global] Typeclasses Opaque errors.


      (* The definition of weaker and wider are intended as an experimental
         guide, not as final definitions *)

      (** A model is weaker if it allows more behaviors. This assumes all
          unspecified behaviors to be independent of regular final states, later
          this may be expanded with an order on the unspecified objects.
          weaker ts ts' ↔ "ts' is weaker than ts" ↔
          "ts' has more behaviours than ts" *)
      Definition weaker (ts ts' : E t) :=
        no_error ts' →
        finalStates ts ⊆ finalStates ts' ∧ unspecifieds ts ⊆ unspecifieds ts'
        ∧ no_error ts.

      (** A model is wider if it matches exactly the narrow model when the
          narrow model has no error. This means it is the same model except it
          has more coverage
          wider ts ts' ↔ "ts' is a strict extension of ts" ↔<→
          "ts' only adds new behaviours when ts says error"
       *)
      Definition wider (ts ts' : E t) :=
        (no_error ts' →
         finalStates ts ⊆ finalStates ts' ∧ unspecifieds ts ⊆ unspecifieds ts') ∧
          (no_error ts →
           finalStates ts ≡ finalStates ts' ∧
             unspecifieds ts ≡ unspecifieds ts' ∧
             no_error ts').

      Lemma wider_weaker (ts ts' : E t) : wider ts ts' → weaker ts' ts.
      Proof using. firstorder. Qed.

      (** Both kind of equivalence are the same when there is no error.
          The strong equivalence is too restrictive
       *)
      Definition equiv (ts ts' : E t) := weaker ts ts' ∧ weaker ts' ts.


      Lemma equiv_wider (ts ts' : E t) :
        equiv ts ts' ↔ wider ts ts' ∧ (no_error ts' → no_error ts).
      Proof using. firstorder. Qed.

      Lemma equiv_wider' (ts ts' : E t) : equiv ts ts' → wider ts ts'.
      Proof using. firstorder. Qed.

      Lemma equiv_errors (ts ts' : E t) :
        equiv ts ts' → (no_error ts ↔ no_error ts').
      Proof using. firstorder. Qed.


      End MR.
      Arguments t : clear implicits.

      Definition from_exec {n} (e : Exec.t string (MState.final n)) :
          listset (t ∅ n) :=
        e |> Exec.to_result_list |$> from_result |> Listset.

    End Res.

    Section Model.
      Context `{MonadSet E}.
      Context {unspec : Type}.

      Definition t : Type :=
        ∀ n : nat, MState.init n → E (Res.t unspec n).

      Definition weaker (m m' : t) : Prop
        := ∀ n initSt, Res.weaker (m n initSt) (m' n initSt).

      Definition wider (m m' : t)
        := ∀ n initSt, Res.wider (m n initSt) (m' n initSt).

      Instance equiv : Equiv t :=
        λ m m', ∀ n initSt, Res.equiv (m n initSt) (m' n initSt).

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
          (∀ n initSt, Res.no_error (m' n initSt) → Res.no_error (m n initSt)).
      Proof using.
        unfold equiv, wider. setoid_rewrite Res.equiv_wider. naive_solver.
      Qed.
      Lemma equiv_wider' (m m' : t) :
        equiv m m' → wider m m'.
      Proof using. rewrite equiv_wider. naive_solver. Qed.
      Lemma equiv_errors (m m' : t) :
        equiv m m' →
        (∀ n initSt, Res.no_error (m n initSt) ↔ Res.no_error (m' n initSt)).
      Proof using.
        unfold equiv. intros. apply Res.equiv_errors. naive_solver.
      Qed.

    End Model.
    Arguments t : clear implicits.

    Definition map_set {E E' unspec} (f : ∀ {A}, E A → E' A) (m : t E unspec)
      : t E' unspec := λ n initSt, f (m n initSt).

    (** Non computational model *)
    Notation nc := (t propset).

    (** Computational model *)
    Notation c := (t listset).

    Definition to_nc {unspec} `{MonadSet E} : t E unspec → nc unspec :=
      map_set (λ A, set_to_propset).
  End Model.

End TermModels.

Module Type TermModelsT (IWA : InterfaceWithArch).
  Include TermModels IWA.
End TermModelsT.
