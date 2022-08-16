(* This file defines an execution monad for the model.

   It is not intended to be Imported as name are not qualified.

   The execution model is Either a named error or a lists of possible outputs.
   This is used to represent non-deterministic but computational execution that
   may fail.

   Getting a Results l, means that all path from the initial state have been
   computed and all the results are in l and none of them are errors.

   Getting an Error e, means that there is one non-deterministic path that
   reaches that error. All other possible outcome are specified.

   In the case of this model, an Error means a behavior not supported by the
   model. In particular, since processor exceptions are not supported, any
   invalid code that would trigger them will make the whole execution return
   an error with hopefully a descriptive message. *)

(* Require Import Common. *)
Require Import SSCCommon.Common.

Require Import Sail.Base.


(********** Tactics **********)

Create HintDb exec discriminated.

(** This module is intended to be imported and provides tactics to be used
    to deal with the exec monad *)
Module Tactics.

  Tactic Notation "exec_simp" "in" "|-*" :=
    rewrite_strat topdown hints exec.

  Tactic Notation "exec_simp" "in" hyp(H) :=
    rewrite_strat topdown hints exec in H.

  Tactic Notation "exec_simp" :=
    progress
      (repeat exec_simp in |-*;
            repeat match goal with
                   | [H : _ |- _ ] => rewrite_strat topdown  (repeat hints exec) in H
                   end).
End Tactics.
Import Tactics.




(********** Definition and utility functions **********)

Inductive t (E A : Type) : Type :=
| Error : E -> t E A
| Results : list A -> t E A.
Arguments Error {_ _} _.
Arguments Results {_ _} _.

(** Means that this execution has no output and may be safely discarded.*)
Notation discard := (Results []).

(** Monadic return *)
Definition ret {E A} (a : A) : t E A := Results [a].

(** Takes an option but convert None into an error *)
Definition error_none {E A} (e : E) : option A -> t E A :=
  from_option ret (Error e).

(** Takes an option but convert None into a discard *)
Definition discard_none {E A} : option A -> t E A :=
  from_option ret discard.

(** Returns an error if the condition is met *)
Definition fail_if {E} (b : bool) (e : E) : t E () :=
  if b then Error e else ret ().

(** Discards the execution if the condition is not met *)
Definition assert {E} (b : bool) : t E () :=
  if b then ret () else discard.

(** Maps the error to another error type. *)
Definition map_error {E E' A} (f : E -> E') (e : t E A) : t E' A :=
  match e with
  | Error err => Error (f err)
  | Results l => Results l
  end.

(** Merge the results of two executions *)
Definition merge {E A} (e1 e2 : t E A) :=
  match e1 with
  | Error e => Error e
  | Results l =>
      match e2 with
      | Error e => Error e
      | Results l' => Results (l ++ l')
      end
  end.


(********** Monad instance **********)

Global Instance mret_inst {E} : MRet (t E) := { mret A := ret }.

Global Instance mbind_inst {E} : MBind (t E) :=
  { mbind _ _ f x :=
    match x with
    | Error e => Error e
    | Results l => foldl merge discard (map f l)
    end
  }.

Global Instance fmap_inst {E} : FMap (t E) :=
  { fmap _ _  f x :=
    match x with
    | Error e => Error e
    | Results l => Results (map f l)
    end }.



(********** Simplification lemmas **********)

Lemma mbind_ret E A B (x : A) (f : A -> t E B) : (ret x ≫= f) = f x.
Proof. hauto lq:on. Qed.
#[global] Hint Rewrite mbind_ret : exec.

Lemma mbind_error (E A B : Type) e (f : A -> t E B) : Error e ≫= f = Error e.
Proof. done. Qed.
#[global] Hint Rewrite mbind_error : exec.

Lemma mbind_discard E A B (f : A -> t E B) : discard ≫= f = discard.
Proof. done. Qed.
#[global] Hint Rewrite mbind_discard : exec.

Lemma merge_error E A s (e : t E A):
  merge (Error s) e = Error s.
Proof. done. Qed.
#[global] Hint Rewrite merge_error : exec.

Lemma foldl_merge_error E A s (l : list (t E A)):
  foldl merge (Error s) l = Error s.
Proof. by induction l. Qed.
#[global] Hint Rewrite foldl_merge_error : exec.

Lemma merge_discard E A (e : t E A) : merge discard e = e.
Proof. by destruct e. Qed.
#[global] Hint Rewrite merge_discard : exec.

Lemma mbind_cons E A B (x : A) (l : list A) (f : A -> t E B):
  Results (x :: l) ≫= f =
    merge (f x) (Results l ≫= f).
  cbn.
  destruct (f x) as [|lx]; [ by exec_simp| clear x].
  - generalize dependent lx.
    induction (map f l) as [| y lt]; hauto use: app_assoc inv:t db:exec,list.
Qed.
#[global] Hint Rewrite mbind_cons : exec.


(********** Predicate on the results **********)

(** Describe an non-error execution *)
Inductive has_results {E A} : t E A -> Prop :=
| HResults l : has_results (Results l).
#[global] Hint Constructors has_results : exec.

(** Describe the fact that an execution is successful and contains the
    specified value *)
Inductive elem_of {E A} : ElemOf A (t E A):=
| ElemOf x l : x ∈ l -> elem_of x (Results l).
#[global] Hint Constructors elem_of : exec.
Global Existing Instance elem_of.


Lemma elem_of_has_results E A (e : t E A) x : x ∈ e -> has_results e.
Proof. sauto lq:on. Qed.
#[global] Hint Resolve elem_of_has_results : exec.




(********** Simplification with the predicates **********)

Lemma has_results_error E A err: has_results (Error err : t E A) <-> False.
Proof. sauto. Qed.
#[global] Hint Rewrite has_results_error : exec.

Lemma elem_of_error E A (err : E) (x : A) : x ∈ (Error err) <-> False.
Proof. sauto. Qed.
#[global] Hint Rewrite elem_of_error : exec.

Lemma elem_of_discard E A (x : A) : x ∈ (discard : t E A) <-> False.
Proof. sauto. Qed.
#[global] Hint Rewrite elem_of_discard: exec.

Lemma has_results_results E A l : has_results (Results l : t E A) <-> True.
Proof. ssimpl. Qed.
#[global] Hint Rewrite has_results_results : exec.

Lemma elem_of_results E A (x : A) l : x ∈ (Results l : t E A) <-> x ∈ l.
Proof. hauto inv:elem_of. Qed.
#[global] Hint Rewrite elem_of_results : exec.

Lemma has_results_merge E A (e e' : t E A) :
  has_results (merge e e') <-> has_results e /\ has_results e'.
Proof. destruct e; destruct e'; hauto inv:has_results db:list,exec. Qed.
#[global] Hint Rewrite has_results_merge : exec.

Lemma elem_of_merge E A (e e' : t E A) x :
  x ∈ (merge e e') <->
    (x ∈ e /\ has_results e') \/ (has_results e /\ x ∈ e').
Proof. destruct e; destruct e'; sauto db:list. Qed.
#[global] Hint Rewrite elem_of_merge : exec.

Lemma elem_of_ret E A (x y :A) : x ∈ (ret y : t E A) <-> x = y.
Proof. sauto. Qed.
#[global] Hint Rewrite elem_of_ret : exec.

Lemma has_results_error_none E A (err : E) opt :
  has_results (error_none err opt) <-> exists x : A, opt = Some x.
Proof. sauto q:on rew:off. Qed.
#[global] Hint Rewrite has_results_error_none : exec.

Lemma elem_of_error_none E A (x : A) (err : E) opt :
  x ∈ (error_none err opt) <-> opt = Some x.
Proof. sauto q:on rew:off. Qed.
#[global] Hint Rewrite elem_of_error_none : exec.

Lemma has_results_map_error E E' A (e : t E A) (f : E -> E') :
  has_results (map_error f e) <-> has_results e.
Proof. sauto q:on rew:off. Qed.
#[global] Hint Rewrite has_results_map_error : exec.

Lemma elem_of_map_error E E' A (x : A) (e : t E A) (f : E -> E') :
  x ∈ (map_error f e) <-> x ∈ e.
Proof. sauto q:on rew:off. Qed.
#[global] Hint Rewrite elem_of_map_error : exec.

Lemma has_results_results_mbind E A B (l : list A) (f : A -> t E B):
  has_results (Results l ≫= f) <-> ∀'z ∈ l, has_results (f z).
Proof.
  unfold_cqual.
  induction l; hauto inv:elem_of_list l:on db:exec.
Qed.


Lemma elem_of_results_mbind E A B (x : B) (l : list A) (f: A -> t E B) :
  x ∈ (Results l ≫= f) <-> (∃'y ∈ l, x ∈ (f y)) /\ ∀'z ∈ l, has_results (f z).
Proof.
  induction l.
  - hauto inv:elem_of_list lq:on db:exec.
  - exec_simp.
    rewrite has_results_results_mbind.
    hauto
      inv:elem_of_list ctrs:elem_of_list lq:on hint:db:exec simp+:unfold_cqual.
Qed.

Lemma has_results_mbind E A B (e : t E A) (f : A -> t E B):
  has_results (e ≫= f) <->
    has_results e /\ ∀'z ∈ e, has_results (f z).
Proof.
  destruct e.
  - hauto inv:has_results.
  - rewrite has_results_results_mbind.
    hauto lq:on db:list simp+:unfold_cqual simp+:exec_simp.
Qed.
#[global] Hint Rewrite has_results_mbind : exec.

Lemma elem_of_mbind E A B (x : B) e (f: A -> t E B) :
  x ∈ (e ≫= f) <-> (∃'y ∈ e, x ∈ (f y)) /\ (∀'z ∈ e, has_results (f z)).
Proof.
  destruct e.
  - hauto inv:elem_of.
  - rewrite elem_of_results_mbind.
    hauto db:list simp+:exec_simp simp+:unfold_cqual.
Qed.
#[global] Hint Rewrite elem_of_mbind : exec.

(* This is an optimisation of the previous rewriting rules *)
Lemma elem_of_error_none_mbind E A B (x : B) (f: A -> t E B) err opt :
  x ∈ (error_none err opt ≫= f) <-> exists y, opt = Some y /\ x ∈ (f y).
Proof. hauto q:on db:exec simp+:unfold_cqual. Qed.
#[global] Hint Rewrite elem_of_error_none_mbind : exec.




(********** Inclusion of execution **********)

(** A execution being included in another means that a success in the
    first implies a success in the second and all elements in the first
    are also in the second *)
Definition Incl {E E' A B} (f : A -> B) (e : t E A) (e' : t E' B) : Prop :=
  (has_results e -> has_results e') /\
    ∀'x ∈ e, (f x) ∈ e'.

Lemma Incl_elem_of E A B (e : t E A) (e' : t E B) x f :
  Incl f e e' -> x ∈ e -> (f x) ∈ e'.
Proof. firstorder. Qed.

Lemma Incl_has_results E A (e e' : t E A) f :
  Incl f e e' -> has_results e -> has_results e'.
Proof. firstorder. Qed.




