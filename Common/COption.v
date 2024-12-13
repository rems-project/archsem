Require Import CBase CBool CDestruct.
Require Import Options.
From stdpp Require Import base.
From stdpp Require Export option.

(** Unpack an option into a monad by throwing an error for None *)
Definition othrow `{MThrow E M} `{MRet M} {A} (err : E) (v : option A) : M A :=
  match v with
  | None => mthrow err
  | Some x => mret x
  end.

Notation ofail := (othrow ()).

(** * EqSomeUnfold *)

Class EqSomeUnfold {A} (oa : option A) (a : A) (P : Prop) :=
  {eq_some_unfold : oa = Some a ↔ P}.
Global Hint Mode EqSomeUnfold + + - - : typeclass_instances.

Global Instance eq_some_unfold_default {A} (oa : option A) (a : A):
  EqSomeUnfold oa a (oa = Some a) | 1000.
Proof. tcclean. reflexivity. Qed.

Global Instance eq_some_unfold_Some {A} (a b : A):
  EqSomeUnfold (Some a) b (a = b).
Proof. tcclean. naive_solver. Qed.

Global Instance eq_some_unfold_None {A} (a : A):
  EqSomeUnfold None a False.
Proof. tcclean. naive_solver. Qed.

Global Instance eq_some_unfold_mret {A} (a b : A):
  EqSomeUnfold (mret a) b (a = b).
Proof. tcclean. unfold mret. unfold option_ret. naive_solver. Qed.

Global Instance eq_some_unfold_mfail {A} (a b : A):
  EqSomeUnfold mfail b False.
Proof. tcclean. unfold mfail. unfold option_mfail. naive_solver. Qed.

Global Instance eq_some_unfold_fmap {A B} (f : A → B) ma b P:
  (∀ a, EqSomeUnfold ma a (P a)) →
  EqSomeUnfold (f <$> ma) b (∃ a : A, P a ∧ b = f a).
Proof. tcclean. apply fmap_Some. Qed.

Global Instance eq_some_unfold_bind {A B} (f : A → option B) ma b P Q:
  (∀ a, EqSomeUnfold ma a (P a)) →
  (∀ a, EqSomeUnfold (f a) b (Q a)) →
  EqSomeUnfold (ma ≫= f) b (∃ a : A, P a ∧ Q a) | 20.
Proof. tcclean. apply bind_Some. Qed.

Global Instance eq_some_unfold_bind_guard `{Decision P} {A} (oa : option A) a Q:
  EqSomeUnfold oa a Q →
  EqSomeUnfold (guard P;; oa) a (P ∧ Q) | 10.
Proof. tcclean. case_guard; rewrite eq_some_unfold; naive_solver. Qed.


(** * CDestrEqSome *)

(** To enable unfolding of some equality, use this *)
Class CDestrEqSome := cdestr_eq_some {}.

#[export] Instance cdestr_eq_some_dir `{CDestrEqSome} `{EqSomeUnfold T oa a P}
  `{∀ x, Unconvertible (option T) oa (Some x)}
  `{Unconvertible Prop (oa = Some a) P} :
  CDestrSimpl (oa = Some a) P :=
  cdestr_simpl (@eq_some_unfold T oa a P _).

#[export] Instance cdestr_eq_some_rev `{CDestrEqSome} `{EqSomeUnfold T oa a P}
  `{∀ x, Unconvertible (option T) oa (Some x)}
  `{Unconvertible Prop (oa = Some a) P} :
    CDestrSimpl (Some a = oa) P.
Proof. sfirstorder. Qed.

(** * Hint database for options *)
Hint Extern 5 (_ = Some _) => progress (apply eq_some_unfold) : option.
Hint Extern 5 (Some _ = _) => progress (apply eq_some_unfold) : option.

Global Instance incomptible_None_Some {A} (a : option A) (b : A) :
  Incompatible (a = None) (a = Some b).
Proof. tcclean. cdestruct a |- **. Qed.
