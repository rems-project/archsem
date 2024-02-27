(** This file defines an execution monad for operational models.

This monad supports non determinism and errors. Use StateT to add state. *)

Require Import Options.
Require Import Common.
Require Import Effects.


(* TODO: Make it a top level name *)
Module Exec.

(** * Base definitions *)
Record t {E A : Type} := make {
    results: list A;
    errors: list E;
  }.
Arguments t : clear implicits.
Arguments make {_ _}.

(** Decide if a execution has errors *)
Definition has_error `(e : t E A) :=
  match e with
  | make _ [] => False
  | _ => True
  end.
#[global] Instance has_error_dec `(e : t E A): Decision (has_error e).
Proof. destruct e as [? []]; tc_solve. Qed.

(** Create an execution from a set of results, e.g. to convert from pure
    non-determinism to Exec *)
Definition Results {E A C} `{Elements A C} (s : C) : t E A := make (elements s) [].

(** Merge the results of two executions *)
Definition merge {E A} (e1 e2 : t E A) :=
  make (e1.(results) ++ e2.(results)) (e1.(errors) ++ e2.(errors)).
#[global] Typeclasses Opaque merge.
Arguments merge : simpl never.

(** Convert an execution into a list of results *)
Definition to_result_list `(e : t E A) : list (result E A) :=
  map Ok e.(results) ++ map Error e.(errors).

#[global] Instance mret_inst {E} : MRet (t E) := λ _ v, make [v] [].

#[global] Instance mbind_inst {E} : MBind (t E) :=
  λ _ _ f e, foldr merge (make [] e.(errors)) (map f e.(results)).
#[global] Typeclasses Opaque mbind_inst.

#[global] Instance fmap_inst {E} : FMap (t E) :=
  λ _ _ f e, make (map f e.(results)) e.(errors).
#[global] Typeclasses Opaque fmap_inst.

#[global] Instance throw_inst {E} : MThrow E (t E) := λ _ e, make [] [e].

#[global] Instance choose_inst {E} : MChoose (t E) :=
  λ _ '(ChooseFin n), make (enum (fin n)) [].
#[global] Typeclasses Opaque choose_inst.

Lemma mdiscard_eq {E A} : mdiscard =@{t E A} make [] [].
Proof. reflexivity. Qed.

#[global] Instance elem_of_results {E A} : ElemOf A (t E A) :=
  λ x e, x ∈ e.(results).
#[global] Typeclasses Opaque elem_of_results.

#[global] Instance elem_of_result {E A} : ElemOf (result E A) (t E A) :=
  λ x e, match x with
         | Ok v => v ∈ e
         | Error err => err ∈ e.(errors)
         end.
#[global] Typeclasses Opaque elem_of_result.

(** Takes an option but convert None into an error *)
Definition error_none {E A} (e : E) : option A -> t E A :=
  from_option mret (mthrow e).

(** Takes an option but convert None into a discard *)
Definition discard_none {E A} : option A -> t E A :=
  from_option mret mdiscard.

(** Maps the error to another error type. *)
Definition map_error {E E' A} (f : E -> E') (e : t E A) : t E' A :=
  make e.(results) (map f e.(errors)).
(** Merge the results of two executions *)

(** * Unfold typeclass for results *)

Class UnfoldElemOf {A E} (x : A) (e : t E A) (Q : Prop) :=
  {unfold_elem_of : x ∈ e ↔ Q}.
#[global] Hint Mode UnfoldElemOf + + - + - : typeclass_instances.

#[global] Instance unfold_elem_of_default {A E} (x : A) (e : t E A) :
  UnfoldElemOf x e (x ∈ e) | 1000.
Proof. done. Qed.

#[export] Hint Extern 5 (UnfoldElemOf ?x (match ?b with _ => _ end) ?G) =>
  has_option SetUnfoldMatch;
  let H := fresh in
  match G with
  | ?Q => is_evar Q; unshelve eassert (UnfoldElemOf x _ _) as H
  | ?Q ?y => is_evar Q; unshelve eassert (UnfoldElemOf x _ (_ y)) as H
  | ?Q ?x ?y => is_evar Q; unshelve eassert (UnfoldElemOf x _ (_ x y)) as H
  | ?Q ?x ?y ?z => is_evar Q; unshelve eassert (UnfoldElemOf x _ (_ x y z)) as H
  end;
  [.. | apply H];
  [intros; destruct b; shelve | ..];
  destruct b; cbn zeta match : typeclass_instances.

#[global] Instance UnfoldElemOf_proper {A E} :
  Proper (@eq A ==> @eq (t E A) ==> iff ==> iff) UnfoldElemOf.
Proof. solve_proper2_tc. Qed.

(** Enables Exec unfolding in regular set_unfold *)
Class Unfold := unfold {}.

#[global] Instance UnfoldElemOfSetUnfoldElemOf `{UnfoldElemOf E A x e P} `{Unfold} :
  SetUnfoldElemOf x e P.
Proof. tcclean. apply unfold_elem_of. Qed.

(** Enable that option locally. *)
#[local] Existing Instance unfold.

(** ** Actual unfolding lemmas *)

#[global] Instance unfold_elem_of_make {E A} x l l' P:
  SetUnfoldElemOf x l P →
  UnfoldElemOf x (make l l' : t E A) P.
Proof. tcclean. naive_solver. Qed.

#[global] Instance unfold_elem_of_merge {E A} x (e e' : t E A) P Q:
  UnfoldElemOf x e P →
  UnfoldElemOf x e' Q →
  UnfoldElemOf x (merge e e') (P ∨ Q).
Proof. tcclean. unfold merge. destruct e. destruct e'. set_solver. Qed.

#[global] Instance unfold_elem_of_mbind {E A B} (x : B) (e : t E A) (f : A → t E B) P:
  (∀ y, UnfoldElemOf y e (P y)) →
  UnfoldElemOf x (e ≫= f) (∃ y, P y ∧ x ∈ f y) | 20.
Proof.
  tcclean. deintro. intros _. destruct e as [l es]. cbn.
  setoid_rewrite unfold_elem_of.
  induction l; set_solver.
Qed.

#[global] Instance unfold_elem_of_bind_guard `{Decision P} {E A} (e : t E A)
    (err : E) a Q:
  UnfoldElemOf a e Q →
  UnfoldElemOf a (guard_or err P;; e) (P ∧ Q) | 10.
Proof. tcclean. case_guard; set_solver. Qed.

#[global] Instance unfold_elem_of_bind_guard_discard `{Decision P} {E A} (e : t E A) a Q:
  UnfoldElemOf a e Q →
  UnfoldElemOf a (guard_discard P;; e) (P ∧ Q) | 10.
Proof. tcclean. case_guard_discard; set_solver. Qed.

#[global] Instance unfold_elem_of_fmap {E A B} (x : B) (e : t E A) (f : A → B) P:
  (∀ y, UnfoldElemOf y e (P y)) →
  UnfoldElemOf x (f <$> e) (∃ y, P y ∧ x = f y).
Proof. tcclean. destruct e as [l es]. cbn. set_solver. Qed.

#[global] Instance unfold_elem_of_mdiscard {E A} (x : A) :
  UnfoldElemOf x (mdiscard : t E A) False.
Proof. tcclean. unfold mdiscard. set_solver. Qed.


(** * Unfold the [has_error] predicate *)

Class UnfoldHasError `(e : t E A) (Q : Prop) :=
  {unfold_has_error : has_error e ↔ Q }.
#[global] Hint Mode UnfoldHasError + + + - : typeclass_instances.

#[global] Instance unfold_has_error_default `(e : t E A) :
  UnfoldHasError e (has_error e) | 1000.
Proof. done. Qed.

#[global] Instance unfold_has_error_mret {E A} (x : A):
  UnfoldHasError (mret x: t E A) False.
Proof. done. Qed.

#[global] Instance unfold_has_error_mthrow {E A} (err : E):
  UnfoldHasError (mthrow err: t E A) True.
Proof. done. Qed.

#[global] Instance unfold_has_error_mdiscard {E A}:
  UnfoldHasError (mdiscard: t E A) False.
Proof. done. Qed.


#[global] Instance unfold_has_error_merge {E A} (e e' : t E A) P Q:
  UnfoldHasError e P →
  UnfoldHasError e' Q →
  UnfoldHasError (merge e e') (P ∨ Q).
Proof.
  tcclean.
  destruct e as [ ? []]; destruct e' as [? []]; cbn in *; naive_solver.
Qed.

#[global] Instance unfold_has_error_mbind {E A B} (e : t E A) (f : A → t E B) P Q R:
  UnfoldHasError e P →
  (∀ y, UnfoldElemOf y e (Q y)) →
  (∀ y, UnfoldHasError (f y) (R y)) →
  UnfoldHasError (e ≫= f) (P ∨ ∃ y, Q y ∧ R y) | 20.
Proof.
  tcclean.
  clear H.
  clear H1.
  clear H0.
  destruct e as [l e]; cbn.
  setoid_rewrite unfold_elem_of.
  induction l; try rewrite unfold_has_error; set_solver.
Qed.

#[global] Instance unfold_has_error_bind_guard `{Decision P} {E A} (e : t E A)
  (err : E) Q:
  UnfoldHasError e Q →
  UnfoldHasError (guard_or err P;; e) (¬ P ∨ Q) | 10.
Proof. tcclean. case_guard; try rewrite unfold_has_error; naive_solver. Qed.

#[global] Instance unfold_has_error_bind_guard_discard `{Decision P} {E A} (e : t E A) Q:
  UnfoldHasError e Q →
  UnfoldHasError (guard_discard P;; e) (P ∧ Q) | 10.
Proof. tcclean. case_guard_discard; try rewrite unfold_has_error; naive_solver. Qed.

#[global] Instance unfold_has_error_fmap {E A B} (e : t E A) (f : A → B) P:
  UnfoldHasError e P →
  UnfoldHasError (f <$> e) P.
Proof. tcclean. destruct e as [l es]. cbn. set_solver. Qed.

End Exec.
