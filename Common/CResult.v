Require Import CBase.
From stdpp Require Import option.

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

  (** Unpack a result into any monad that supports that error type *)
  Definition unpack_result `{MThrow E M, MRet M} (r : result) : M A :=
    match r with
    | Ok val => mret val
    | Error err => mthrow err
    end.

End Result.
Arguments result : clear implicits.


(** * Result as monad *)
Section ResultMonad.
  Context {E : Type}.

  Global Instance result_ret : MRet (result E) := @Ok E.

  Global Instance result_throw : MThrow E (result E) := @Error E.

  Global Instance result_bind : MBind (result E) :=
    λ _ _ f r,
      match r with
      | Ok val => f val
      | Error err => Error err
      end.

  Global Instance result_join : MJoin (result E) :=
    λ _ r,
      match r with
      | Error err => Error err
      | Ok (Error err) => Error err
      | Ok (Ok a) => Ok a
      end.

  Global Instance result_fmap : FMap (result E) :=
    λ _ _  f r,
      match r with
      | Ok val => Ok (f val)
      | Error err => Error err
      end.

End ResultMonad.

(** * Error map *)

Definition mapE {E E' A} (f : E → E') (r : result E A) : result E' A :=
  match r with
  | Ok val => Ok val
  | Error err => Error (f err)
  end.
