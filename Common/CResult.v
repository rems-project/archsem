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

From stdpp Require Import option.
Require Import Options.
Require Import CBase CDestruct CMonads.

(** The point of this module is to keep the [sum] type symmetric and use this to
    assign a meaning to success and error (and a corresponding monad instance)

    The naming is intended to match Ocaml's result as Haskell uses Either which
    is similar to the regular [sum].
 *)

Section Result.

  (** The error type is first so that [result E] is a monad *)
  Context {E A : Type}.

  Inductive result : Type :=
  | Ok (val : A)
  | Error (err : E).

  Definition get_Ok (r : result) : option A :=
    match r with
    | Ok val => Some val
    | Error err => None
    end.

  Definition get_Error (r : result) : option E :=
    match r with
    | Ok val => None
    | Error err => Some err
    end.

  (** Takes an option but convert [None] into the provided error *)
  Definition res_from_opt (e : E) : option A -> result :=
  from_option Ok (Error e).

  (* For convenience *)
  Definition res_to_opt := get_Ok.

  Definition res_from_suml (s : A + E) : result :=
    match s with
    | inl val => Ok val
    | inr err => Error err
    end.

  Definition res_from_sumr (s : E + A) : result :=
    match s with
    | inr val => Ok val
    | inl err => Error err
    end.

  Definition res_to_suml (r : result) : A + E :=
    match r with
    | Ok val => inl val
    | Error err => inr err
    end.

  Definition res_to_sumr (r : result) : E + A :=
    match r with
    | Ok val => inr val
    | Error err => inl err
    end.

  Lemma res_from_to_suml (s : A + E) : res_to_suml (res_from_suml s) = s.
  Proof using. by destruct s. Qed.

  Lemma res_to_from_suml (r : result) : res_from_suml (res_to_suml r) = r.
  Proof using. by destruct r. Qed.

  Lemma res_from_to_sumr (s : E + A) : res_to_sumr (res_from_sumr s) = s.
  Proof using. by destruct s. Qed.

  Lemma res_to_from_sumr (r : result) : res_from_sumr (res_to_sumr r) = r.
  Proof using. by destruct r. Qed.


  (** [is_Err] and [is_Ret] are doing the same as [is_Some] but for results *)
  Definition is_Error (r : result) := ∃ err, r = Error err.
  #[export] Instance is_Error_Decision (r : result) : Decision (is_Error r).
  Proof.
    refine (match r with | Error _ => left _ | _ => right _ end);
      unfold is_Error;
      naive_solver.
  Defined.

  Definition is_Ok (r : result) := ∃ val, r = Ok val.
  #[export] Instance is_Ok_Decision (r : result) : Decision (is_Ok r).
  Proof.
    refine (match r with | Ok _ => left _ | _ => right _ end);
      unfold is_Ok;
      naive_solver.
  Defined.

  #[export] Instance cdestruct_is_Ok r :
    CDestrSimpl false (is_Ok r) (∃ o, r = Ok o).
  Proof. tcclean. now unfold is_Ok. Qed.

  #[export] Instance obv_true_is_Ok_Ok x : ObvTrue (is_Ok (Ok x)).
  Proof. tcclean. unfold is_Ok. eauto. Qed.

  #[export] Instance obv_false_is_Ok_Error x : ObvFalse (is_Ok (Error x)).
  Proof. tcclean. unfold is_Ok. naive_solver. Qed.

  (** Unpack a result into any monad that supports that error type *)
  Definition unpack_result `{MThrow E M, MRet M} (r : result) : M A :=
    match r with
    | Ok val => mret val
    | Error err => mthrow err
    end.

  #[export] Instance result_eq_dec `{EqDecision E} `{EqDecision A} : EqDecision (result).
  Proof. solve_decision. Defined.

End Result.
Arguments result : clear implicits.

Instance DecisionT_result  `{DecisionT E} `{DecisionT A} : DecisionT (result E A).
Proof. sfirstorder. Qed.

Instance result_inhabited_ok {E} `{Inhabited A} : Inhabited (result E A).
Proof. firstorder. Defined.

Instance result_inhabited_error `{Inhabited E} {A} : Inhabited (result E A).
Proof. firstorder. Defined.

(** * CDestruct interaction *)

Definition cdestruct_result (E A : Type) :
  CDestrCase (result E A) := ltac:(constructor).

(** * Result as monad *)
Section ResultMonad.
  Context {E : Type}.

  #[export] Instance result_ret : MRet (result E) := @Ok E.

  #[export] Instance result_throw : MThrow E (result E) := @Error E.

  #[export] Instance result_bind : MBind (result E) :=
    λ _ _ f r,
      match r with
      | Ok val => f val
      | Error err => Error err
      end.

  #[export] Instance result_join : MJoin (result E) :=
    λ _ r,
      match r with
      | Error err => Error err
      | Ok (Error err) => Error err
      | Ok (Ok a) => Ok a
      end.

  #[export] Instance result_fmap : FMap (result E) :=
    λ _ _  f r,
      match r with
      | Ok val => Ok (f val)
      | Error err => Error err
      end.

  #[export] Instance result_monad : Monad (result E).
  Proof. split; cdestruct |- *** ## cdestruct_result. Qed.

  #[export] Instance result_monad_fmap : MonadFMap (result E).
  Proof. cdestruct |- *** ## cdestruct_result. Qed.

End ResultMonad.

(** * Error map *)

Definition mapE {E E' A} (f : E → E') (r : result E A) : result E' A :=
  match r with
  | Ok val => Ok val
  | Error err => Error (f err)
  end.

