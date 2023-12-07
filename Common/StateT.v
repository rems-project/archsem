(** Add a state monad transformer *)

Require Import CBase.
Require Import Options.
Require Import Effects.

Section ST.
  Context {St : Type}.
  Context `{MRet M} `{MBind M} `{MJoin M} `{FMap M}.

  Definition stateT (A : Type):= St → M (St * A).

  Definition st_lift {A : Type} (m : M A) : stateT A := λ s, fmap (s,.) m.

  #[global] Instance st_ret : MRet stateT := λ _ a s, mret (s, a).
  #[global] Instance st_bind : MBind stateT := λ _ _ f ma s,
      '(s', a) ← ma s; f a s'.
  #[global] Instance st_join : MJoin stateT := λ _ mma s, '(s', y) ← mma s; y s'.
  #[global] Instance st_fmap : FMap stateT := λ _ _ f ma s,
      (ma s) |$> (λ '(s, a), (s, f a)).

  #[global] Instance st_call_MState : MCall (MState St) stateT | 10 := λ _ eff,
      match eff with
      | MSet s => λ _, mret (s, ())
      | MGet => λ s, mret (s, s)
      end.

  #[global] Instance st_throw `{MThrow E M}: MThrow E stateT :=
    λ _ x, st_lift (mthrow x).

  (* Specific instances can override this if they want a state modifying effect
  different from MState. *)
  #[global] Instance st_call_inner `{MCall Eff M} : MCall Eff stateT | 100 :=
    λ _ eff, st_lift (mcall eff).

End ST.
Arguments stateT : clear implicits.

(** Move to a state transformer monad over a different monad *)
Definition st_move {St M M' A} (f : M (St * A)%type → M' (St * A)%type)
    (mx : stateT St M A) : stateT St M' A :=
  λ s, f (mx s).

(** The state monad is just the state transformer over the id monad *)
Notation stateM St := (stateT St idM).
