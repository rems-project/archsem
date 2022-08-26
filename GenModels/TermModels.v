
Require SSCCommon.Exec.
Module Exec := SSCCommon.Exec.
Import Exec.Tactics.

Require Import Ensembles.

Require Import Strings.String.

Require Import SSCCommon.Common.

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
Module TermModels (Arch : Arch). (* to be imported *)
  Module IA := Interface Arch.
  Import IA.

  (** Assuming bytes of 8 bits, not caring about weird architectures for now *)
  Definition memoryMap := pa -> bv 8.

  Definition registerMap := reg → reg_type.

  (** A termination condition that define when each thread should stop.

      For now it only needs a register maps as I expect it will most often just
      be `PC = ...` or `PC >= ...` *)
  Definition terminationCondition (n : nat) := fin n -> registerMap -> bool.

  (** This module define a concept of simple machine state without any
      micro-architectural details.

      TODO decide among other possible name:
      - SeqState, for sequential state.
      - SimpState, for simple state.
      - SState for one of the above but shorter. *)
  Module MState. (* namespace *)

    (** A simple machine state for comparing models and defining sequential
        semantics *)
    Record t {n : nat} :=
      Make{
          memory : memoryMap;
          regs: vec registerMap n;
        }.
    Arguments t : clear implicits.

    (** A initial state for a machine model test. This means that the
        machine must stop at the required termination condition *)
    Record init {n : nat} :=
      MakeI {
          state :> t n;
          termCond : terminationCondition n
        }.
    Arguments init : clear implicits.

    (** A final state for a machine model test. This means that the machine has
        stopped at the required termination condition *)
    Record final {n : nat} :=
      MakeF {
          istate :> init n;
          terminated : forall tid : fin n, istate.(termCond) tid $ istate.(regs) !!! tid
        }.
    Arguments final : clear implicits.
  End MState.
  (* Make the coercion available without importing the module *)
  Global Coercion MState.state : MState.init >-> MState.t.
  Global Coercion MState.istate : MState.final >-> MState.init.

  Module ModelResult. (* namespace *)
    Section MR.
      Context {unspecified : Type} {n : nat}.
      Inductive t :=
      | FinalState : MState.final n -> t
      (** Unspecified is any kind of behavior that is not fully specified but is
        not a model error. For example a BBM failure. *)
      | Unspecified : unspecified -> t
      (** Expected reasons for failures:

        - The model does not support a specific outcome.

        - An instruction issued a "GenericFail" (problem with an ISA model)

        - A fuel-limited executable model did not have enough fuel.

        - The test has an infinite execution (not the fault of the model) *)
      | Error : string -> t.

      Context `{OMap E}.
      Context `{Empty (E string)}.
      Context {sse : forall x, SubsetEq (E x)}.

      Definition finalStates (ts : E t) :=
        omap (fun x => match x with | FinalState fs => Some fs | _ => None end) ts.

      Definition unspecifieds  (ts : E t) :=
        omap (fun x => match x with | Unspecified us => Some us | _ => None end) ts.

      Definition errors  (ts : E t) :=
        omap (fun x => match x with | Error us => Some us | _ => None end) ts.

      Definition no_error (ts : E t) := errors ts ⊆ ∅.

      (* The definition of weaker and wider are intended as an experimental
         guide, not as final definitions *)

      (** A model is weaker if it allows more behaviors. This assumes all
          unspecified to be independent, later this may be expanded with an
          order on the unspecified objects.
       *)
      Definition weaker (ts ts' : E t) :=
        no_error ts' ->
        finalStates ts ⊆ finalStates ts' ∧ unspecifieds ts ⊆ unspecifieds ts'.

      (** A model is wider if it matches exactly the narrow model when the
          narrow model has no error. This means it is the same model except it
          has more coverage *)
      Definition wider (ts ts' : E t) :=
        weaker ts ts' /\
          (no_error ts ->
           finalStates ts ≡ₛ finalStates ts' /\
             unspecifieds ts ≡ₛ unspecifieds ts /\
             no_error ts').

      Lemma wider_weaker (ts ts' : E t) : wider ts ts' -> weaker ts ts'.
      Proof. firstorder. Qed.


      (** Both kind of equivalence are the same when there is no error.
          The strong equivalence is too restrictive
       *)
      Definition sEquiv (ts ts' : E t) := wider ts ts' /\ wider ts' ts.

      Definition wEquiv (ts ts' : E t) := weaker ts ts' /\ weaker ts' ts.

      Lemma sEquiv_wEquiv (ts ts' : E t) : sEquiv ts ts' -> wEquiv ts ts'.
      Proof. firstorder. Qed.

    End MR.
    Arguments t : clear implicits.

    Definition from_exec {n} (e : Exec.t string (MState.final n)) : list (t False n) :=
      match e with
      | Exec.Error s => [Error s]
      | Exec.Results l => FinalState <$> l
      end.

  End ModelResult.


  Module Model. (* namespace *)
    Section M.
      Context `{OMap E}.
      Context `{Empty (E string)}.
      Context {sse : forall x, SubsetEq (E x)}.
      Context {unspec : Type}.

      Definition t : Type :=
        forall n : nat, MState.init n -> E (ModelResult.t unspec n).

      Definition weaker (m1 m2 : t) : Prop
        := forall n initSt, ModelResult.weaker (m1 n initSt) (m2 n initSt).

      Definition wider (m1 m2 : t)
        := forall n initSt, ModelResult.wider (m1 n initSt) (m2 n initSt).

      Definition sEquiv (m1 m2 : t)
        := forall n initSt, ModelResult.sEquiv (m1 n initSt) (m2 n initSt).

      Definition wEquiv (m1 m2 : t)
        := forall n initSt, ModelResult.wEquiv (m1 n initSt) (m2 n initSt).

      (** Model identities, this require that any error messages are identical.
        This is thus only useful when comparing two related versions of the same
        model (like a certified and non-certified versions of promising)*)
      Global Instance equiv : Equiv t :=
        fun m1 m2 => forall n initSt, m1 n initSt ≡ₛ m2 n initSt.
    End M.
    Arguments t : clear implicits.

    Definition map {E E' unspec} (f : forall {A}, E A -> E' A) (m : t E unspec)
      : t E' unspec :=
      fun n initSt => m n initSt |> f.

    (** Non computational model *)
    Notation nc := (t Ensemble).

    (** Computational model (TODO: maybe listset instead of list?) *)
    Notation c := (t list).

    Definition c_to_nc {unspec} : c unspec -> nc unspec :=
      map (@Ensemble_from_list).
  End Model.

End TermModels.
