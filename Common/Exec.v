(* This file defines an execution monad for the model.

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

Require Import Common.


(*** Tactics ***)

Create HintDb exec discriminated.

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

Module Exec.

(*** Definition and utility functions ***)

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

(** Non-deterministically choose an element in a finite set *)
Definition choose {E} (A : Type) `{Finite A} : t E A := Results (enum A).

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


(*** Monad instance ***)

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



(*** Simplification lemmas ***)

Lemma mbind_ret E A B (x : A) (f : A -> t E B) : (ret x ≫= f) = f x.
Proof. hauto lq:on. Qed.
#[global] Hint Rewrite mbind_ret : exec.
#[global] Hint Rewrite mbind_ret : execc.

Lemma mbind_error (E A B : Type) e (f : A -> t E B) : Error e ≫= f = Error e.
Proof. done. Qed.
#[global] Hint Rewrite mbind_error : exec.
#[global] Hint Rewrite mbind_error : execc.

Lemma mbind_discard E A B (f : A -> t E B) : discard ≫= f = discard.
Proof. done. Qed.
#[global] Hint Rewrite mbind_discard : exec.
#[global] Hint Rewrite mbind_discard : execc.

Lemma merge_error E A s (e : t E A):
  merge (Error s) e = Error s.
Proof. done. Qed.
#[global] Hint Rewrite merge_error : exec.
#[global] Hint Rewrite merge_error : execc.

Lemma foldl_merge_error E A s (l : list (t E A)):
  foldl merge (Error s) l = Error s.
Proof. by induction l. Qed.
#[global] Hint Rewrite foldl_merge_error : exec.
#[global] Hint Rewrite foldl_merge_error : execc.

Lemma merge_discard E A (e : t E A) : merge discard e = e.
Proof. by destruct e. Qed.
#[global] Hint Rewrite merge_discard : exec.
#[global] Hint Rewrite merge_discard : execc.

Lemma merge_discard2 E A (e : t E A) : merge e discard = e.
Proof. destruct e; hauto db:list. Qed.
#[global] Hint Rewrite merge_discard : exec.
#[global] Hint Rewrite merge_discard : execc.

Lemma mbind_cons E A B (x : A) (l : list A) (f : A -> t E B):
  Results (x :: l) ≫= f =
    merge (f x) (Results l ≫= f).
  cbn.
  destruct (f x) as [|lx]; [ by exec_simp| clear x].
  - generalize dependent lx.
    induction (map f l) as [| y lt]; hauto use: app_assoc inv:t db:exec,list.
Qed.
#[global] Hint Rewrite mbind_cons : exec.
#[global] Hint Rewrite mbind_cons : execc.

Opaque mbind_inst.


(*** Predicate on the results ***)

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
#[global] Hint Resolve elem_of_has_results : execc.



(*** Exec unfolding ***)

Class ExecUnfold (P Q : Prop) := { exec_unfold : P ↔ Q }.
Global Arguments exec_unfold _ _ {_} : assert.
Global Hint Mode ExecUnfold + - : typeclass_instances.

Global Instance exec_unfold_default P : ExecUnfold P P | 1000. done. Qed.
Definition exec_unfold_1 `{ExecUnfold P Q} : P → Q := proj1 (exec_unfold P Q).
Definition exec_unfold_2 `{ExecUnfold P Q} : Q → P := proj2 (exec_unfold P Q).

Tactic Notation "exec_unfold" :=
  let rec unfold_hyps :=
    try match goal with
    | H : ?P |- _ =>
       lazymatch type of P with
       | Prop =>
         apply exec_unfold_1 in H; revert H;
         first [unfold_hyps; intros H | intros H; fail 1]
       | _ => fail
       end
    end in
  apply exec_unfold_2; unfold_hyps; csimpl in *.

Tactic Notation "exec_unfold" "in" ident(H) :=
  let P := type of H in
  lazymatch type of P with
  | Prop => apply exec_unfold_1 in H
  | _ => fail "hypothesis" H "is not a proposition"
  end.


Class UnfoldElemOf {A E} (x : A) (e : t E A) (Q : Prop) :=
  {unfold_elem_of : x ∈ e <-> Q}.
Arguments unfold_elem_of {_ _} _ _ _ {_} : assert.
Global Hint Mode UnfoldElemOf + + - + - : typeclass_instances.

Global Instance unfold_elem_of_exec_unfold {A E} (x : A) (e : t E A) Q :
  UnfoldElemOf x e Q → ExecUnfold (x ∈ e) Q.
Proof. sfirstorder. Qed.
Global Instance unfold_elem_of_default {A E} (x : A) (e : t E A) :
  UnfoldElemOf x e (x ∈ e) | 1000.
Proof. done. Qed.

Global Instance unfold_elem_of_let_pair {A B C E} (x : A) (p : B * C) (e : B -> C -> t E A) Q :
  (forall y z, UnfoldElemOf x (e y z) (Q y z)) ->
  UnfoldElemOf x (let '(y, z) := p in e y z) (let '(y, z) := p in Q y z).
Proof. by destruct p. Qed.


Class UnfoldHasResults {A E} (e : t E A) (Q : Prop) :=
  {unfold_has_results : has_results e <-> Q}.
Global Hint Mode UnfoldHasResults + + + - : typeclass_instances.

Global Instance unfold_has_results_exec_unfold {A E} (e : t E A) Q :
  UnfoldHasResults e Q → ExecUnfold (has_results e) Q.
Proof. sfirstorder. Qed.
Global Instance unfold_has_results_default {A E} (e : t E A) :
  UnfoldHasResults e (has_results e) | 1000.
Proof. done. Qed.

Global Instance unfold_has_result_let_pair {A B C E} (p : B * C) (e : B -> C -> t E A) Q :
  (forall y z, UnfoldHasResults (e y z) (Q y z)) ->
  UnfoldHasResults (let '(y, z) := p in e y z) (let '(y, z) := p in Q y z).
Proof. by destruct p. Qed.

Global Instance UnfoldElemOf_proper {A E} :
  Proper (@eq A ==> @eq (t E A) ==> iff ==> iff) UnfoldElemOf.
Proof. solve_proper2_tc. Qed.

Global Instance UnfoldHasResults_proper {A E} :
  Proper (@eq (t E A) ==> iff ==> iff) UnfoldHasResults.
Proof. solve_proper2_tc. Qed.

(** Importing this will make set_unfold also unfold exec values *)
Module SetUnfoldExecUnfold.

  #[export] Instance unfold_has_results_set_unfold {A E} (e : t E A) Q :
  UnfoldHasResults e Q → SetUnfold (has_results e) Q.
  Proof. sfirstorder. Qed.

  #[export] Instance unfold_elem_of_set_unfold_elemOf {A E} (x : A) (e : t E A) Q :
    UnfoldElemOf x e Q → SetUnfoldElemOf x e Q.
  Proof. sfirstorder. Qed.
End SetUnfoldExecUnfold.

Import SetUnfoldExecUnfold.

Lemma exec_unfold_impl P Q P' Q' :
  ExecUnfold P P' → ExecUnfold Q Q' → ExecUnfold (P → Q) (P' → Q').
Proof. constructor. by rewrite (exec_unfold P P'), (exec_unfold Q Q'). Qed.
Lemma exec_unfold_and P Q P' Q' :
  ExecUnfold P P' → ExecUnfold Q Q' → ExecUnfold (P ∧ Q) (P' ∧ Q').
Proof. constructor. by rewrite (exec_unfold P P'), (exec_unfold Q Q'). Qed.
Lemma exec_unfold_or P Q P' Q' :
  ExecUnfold P P' → ExecUnfold Q Q' → ExecUnfold (P ∨ Q) (P' ∨ Q').
Proof. constructor. by rewrite (exec_unfold P P'), (exec_unfold Q Q'). Qed.
Lemma exec_unfold_iff P Q P' Q' :
  ExecUnfold P P' → ExecUnfold Q Q' → ExecUnfold (P ↔ Q) (P' ↔ Q').
Proof. constructor. by rewrite (exec_unfold P P'), (exec_unfold Q Q'). Qed.
Lemma exec_unfold_not P P' : ExecUnfold P P' → ExecUnfold (¬P) (¬P').
Proof. constructor. by rewrite (exec_unfold P P'). Qed.
Lemma exec_unfold_forall {A} (P P' : A → Prop) :
  (∀ x, ExecUnfold (P x) (P' x)) → ExecUnfold (∀ x, P x) (∀ x, P' x).
Proof. constructor. naive_solver. Qed.
Lemma exec_unfold_exist {A} (P P' : A → Prop) :
  (∀ x, ExecUnfold (P x) (P' x)) → ExecUnfold (∃ x, P x) (∃ x, P' x).
Proof. constructor. naive_solver. Qed.

(* Avoid too eager application of the above instances (and thus too eager
unfolding of type class transparent definitions). *)
Global Hint Extern 0 (ExecUnfold (_ → _) _) =>
  class_apply exec_unfold_impl : typeclass_instances.
Global Hint Extern 0 (ExecUnfold (_ ∧ _) _) =>
  class_apply exec_unfold_and : typeclass_instances.
Global Hint Extern 0 (ExecUnfold (_ ∨ _) _) =>
  class_apply exec_unfold_or : typeclass_instances.
Global Hint Extern 0 (ExecUnfold (_ ↔ _) _) =>
  class_apply exec_unfold_iff : typeclass_instances.
Global Hint Extern 0 (ExecUnfold (¬ _) _) =>
  class_apply exec_unfold_not : typeclass_instances.
Global Hint Extern 1 (ExecUnfold (∀ _, _) _) =>
  class_apply exec_unfold_forall : typeclass_instances.
Global Hint Extern 0 (ExecUnfold (∃ _, _) _) =>
  class_apply exec_unfold_exist : typeclass_instances.

(********** Simplification with the predicates **********)

Global Instance unfold_has_results_error E A err :
  UnfoldHasResults (Error err : t E A) False.
Proof. sauto. Qed.

Lemma has_results_error E A err: has_results (Error err : t E A) <-> False.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite has_results_error : exec.

Global Instance unfold_elem_of_error E A x err :
  UnfoldElemOf x (Error err : t E A) False.
Proof. sauto. Qed.

Lemma elem_of_error E A (err : E) (x : A) : x ∈ (Error err) <-> False.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite elem_of_error : exec.

Global Instance unfold_elem_of_discard E A x :
  UnfoldElemOf x (discard : t E A) False.
Proof. sauto. Qed.

Lemma elem_of_discard E A (x : A) : x ∈ (discard : t E A) <-> False.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite elem_of_discard: exec.

Global Instance unfold_has_results_results E A l :
  UnfoldHasResults (Results l : t E A) True.
Proof. sauto. Qed.

Lemma has_results_results E A l : has_results (Results l : t E A).
Proof. by exec_unfold. Qed.
#[global] Hint Resolve has_results_results : exec.
#[global] Hint Rewrite (fun E A l => Prop_for_rewrite $ has_results_results E A l) : exec.

Global Instance unfold_elem_of_results E A x l Q :
  SetUnfoldElemOf x l Q -> UnfoldElemOf x (Results l : t E A) Q.
Proof. sauto lq:on. Qed.

Lemma elem_of_results E A (x : A) l : x ∈ (Results l : t E A) <-> x ∈ l.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite elem_of_results : exec.

Global Instance unfold_has_results_merge E A (e e' : t E A) Q Q' :
  UnfoldHasResults e Q -> UnfoldHasResults e' Q' ->
  UnfoldHasResults (merge e e') (Q /\ Q').
Proof.
  tcclean.
  destruct e; destruct e'; hauto inv:has_results db:list simp+:exec_unfold.
Qed.

Lemma has_results_merge E A (e e' : t E A) :
  has_results (merge e e') <-> has_results e /\ has_results e'.
Proof. by exec_unfold.  Qed.
#[global] Hint Rewrite has_results_merge : exec.

Global Instance unfold_elem_of_merge E A (e e' : t E A) x P P' Q Q' :
  UnfoldHasResults e P -> UnfoldElemOf x e Q ->
  UnfoldHasResults e' P' -> UnfoldElemOf x e' Q' ->
  UnfoldElemOf x (merge e e') (P' /\ Q \/ P /\ Q').
Proof.
  tcclean.
  destruct e; destruct e'; cbn in *; exec_unfold; firstorder.
Qed.

Lemma elem_of_merge E A (e e' : t E A) x :
  x ∈ (merge e e') <->
    (x ∈ e /\ has_results e') \/ (has_results e /\ x ∈ e').
Proof. exec_unfold; firstorder. Qed.
#[global] Hint Rewrite elem_of_merge : exec.

Global Instance unfold_has_result_ret E A (y : A) :
  UnfoldHasResults (ret y : t E A) True.
Proof. sauto. Qed.

Global Instance unfold_elem_of_ret E A (x y : A) :
  UnfoldElemOf x (ret y : t E A) (x = y).
Proof. sauto. Qed.

Lemma elem_of_ret E A (x y :A) : x ∈ (ret y : t E A) <-> x = y.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite elem_of_ret : exec.

Global Instance unfold_has_result_error_none E A (err : E) (opt : option A) :
  UnfoldHasResults (error_none err opt) (is_Some opt).
Proof. sauto lq:on rew:off. Qed.

Lemma has_results_error_none E A (err : E) opt :
  has_results (error_none err opt) <-> exists x : A, opt = Some x.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite has_results_error_none : exec.

Global Instance unfold_elem_error_none E A (err : E) (x : A) (opt : option A) :
  UnfoldElemOf x (error_none err opt) (opt = Some x).
Proof. sauto lq:on rew:off. Qed.

Lemma elem_of_error_none E A (x : A) (err : E) opt :
  x ∈ (error_none err opt) <-> opt = Some x.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite elem_of_error_none : exec.

Global Instance unfold_has_result_map_error E E' A (f : E -> E') (e : t E A) Q :
  UnfoldHasResults e Q -> UnfoldHasResults (map_error f e) Q.
Proof. destruct e; sauto lq:on. Qed.

Lemma has_results_map_error E E' A (e : t E A) (f : E -> E') :
  has_results (map_error f e) <-> has_results e.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite has_results_map_error : exec.

Global Instance unfold_elem_of_map_error E E' A (f : E -> E') (e : t E A) x Q :
  UnfoldElemOf x e Q -> UnfoldElemOf x (map_error f e) Q.
Proof. destruct e; sauto lq:on. Qed.

Lemma elem_of_map_error E E' A (x : A) (e : t E A) (f : E -> E') :
  x ∈ (map_error f e) <-> x ∈ e.
Proof. by exec_unfold. Qed.
#[global] Hint Rewrite elem_of_map_error : exec.

Global Instance unfold_has_result_choose E A `{Finite A} :
  UnfoldHasResults (choose A : t E A) True.
Proof. sfirstorder. Qed.

Lemma has_results_choose E A `{Finite A}:
  has_results (choose A : t E A).
Proof. by exec_unfold. Qed.
#[global] Hint Resolve has_results_choose : exec.
#[global] Hint Rewrite (fun E A `{Finite A} => Prop_for_rewrite (has_results_choose E A)) : exec.

Global Instance unfold_elem_of_choose E A `{Finite A} x :
  UnfoldElemOf x (choose A : t E A) True.
Proof. sauto lq:on. Qed.

Lemma elem_of_choose E A `{Finite A} x:
  x ∈ (choose A : t E A).
Proof. by exec_unfold. Qed.
#[global] Hint Resolve elem_of_choose : exec.
#[global] Hint Rewrite (fun E A `{Finite A} x => Prop_for_rewrite (elem_of_choose E A x)) : exec.


Global Instance unfold_has_result_fail_if E (b : bool) (e : E) :
  UnfoldHasResults (fail_if b e : t E ()) (¬b).
Proof. tcclean. sauto lq:on rew:off. Qed.

Global Instance unfold_elem_of_fail_if E x (b : bool) (e : E) :
  UnfoldElemOf x (fail_if b e : t E ()) (¬b).
Proof. tcclean. sauto lq:on rew:off. Qed.


Global Instance unfold_has_result_assert E (b : bool) (e : E) :
  UnfoldHasResults (assert b : t E ()) True.
Proof. tcclean. sauto lq:on rew:off. Qed.

Global Instance unfold_elem_of_assert E x (b : bool) (e : E) :
  UnfoldElemOf x (assert b : t E ()) b.
Proof. tcclean. sauto lq:on rew:off. Qed.


Lemma has_results_results_mbind E A B (l : list A) (f : A -> t E B):
  has_results (Results l ≫= f) <-> ∀'z ∈ l, has_results (f z).
Proof.
  induction l; hauto simp+:set_unfold l:on db:exec.
Qed.


Lemma has_results_results_mbind' E A B (l : list A) (f : A -> t E B):
  has_results (Results l ≫= f) <-> ∀'z ∈ l, has_results (f z).
Proof.
  induction l; hauto lq:on db:execc simp+:set_unfold.
Qed.

Local Instance unfold_has_results_results_mbind E A B l (f : A -> t E B) P Q:
  (forall z, SetUnfoldElemOf z l (P z)) -> (forall z, UnfoldHasResults (f z) (Q z)) ->
  UnfoldHasResults (Results l ≫= f) (forall z, P z -> Q z).
Proof. tcclean. apply has_results_results_mbind. Qed.

Lemma elem_of_results_mbind E A B (x : B) (l : list A) (f: A -> t E B) :
  x ∈ (Results l ≫= f) <-> (∃'y ∈ l, x ∈ (f y)) /\ ∀'z ∈ l, has_results (f z).
Proof.
  induction l.
  - hauto inv:elem_of_list lq:on db:exec.
  - exec_simp.
    rewrite has_results_results_mbind.
    hauto
      inv:elem_of_list ctrs:elem_of_list lq:on hint:db:exec.
Qed.

Lemma elem_of_results_mbind' E A B (x : B) (l : list A) (f: A -> t E B) :
  x ∈ (Results l ≫= f) <-> (∃'y ∈ l, x ∈ (f y)) /\ ∀'z ∈ l, has_results (f z).
Proof.
  induction l.
  - set_unfold. sfirstorder.
  - autorewrite with execc.
    set_unfold.
    hauto lq:on hint:db:execc.
Qed.



Global Instance unfold_elem_of_results_mbind E A B x l (f : A -> t E B) P Q R:
  (forall z, SetUnfoldElemOf z l (P z)) ->
  (forall z, UnfoldHasResults (f z) (Q z)) ->
  (forall z, UnfoldElemOf x (f z) (R z)) ->
  UnfoldElemOf x (Results l ≫= f) ((exists z, P z /\ R z) /\ forall z, P z -> Q z).
Proof. tcclean. apply elem_of_results_mbind. Qed.



Lemma has_results_mbind E A B (e : t E A) (f : A -> t E B):
  has_results (e ≫= f) <->
    has_results e /\ ∀'z ∈ e, has_results (f z).
Proof.
  destruct e.
  - hauto inv:has_results.
  - rewrite has_results_results_mbind.
    hauto lq:on db:list simp+:exec_simp.
Qed.
#[global] Hint Rewrite has_results_mbind : exec.

Lemma has_results_mbind' E A B (e : t E A) (f : A -> t E B):
  has_results (e ≫= f) <->
    has_results e /\ ∀'z ∈ e, has_results (f z).
Proof.
  destruct e; hauto l:on simp+:exec_unfold db:execc.
Qed.

Global Instance unfold_has_results_mbind E A B e (f : A -> t E B) P Q R:
  UnfoldHasResults e P ->
  (forall z, UnfoldElemOf z e (Q z)) ->
  (forall z, UnfoldHasResults (f z) (R z)) ->
  UnfoldHasResults (e ≫= f) (P /\ forall z, Q z -> R z).
Proof. tcclean. apply has_results_mbind. Qed.

Lemma elem_of_mbind E A B (x : B) e (f: A -> t E B) :
  x ∈ (e ≫= f) <-> (∃'y ∈ e, x ∈ (f y)) /\ (∀'z ∈ e, has_results (f z)).
Proof.
  destruct e.
  - hauto inv:elem_of.
  - rewrite elem_of_results_mbind.
    hauto db:list simp+:exec_simp.
Qed.
#[global] Hint Rewrite elem_of_mbind : exec.

Lemma elem_of_mbind' E A B (x : B) e (f: A -> t E B) :
  x ∈ (e ≫= f) <-> (∃'y ∈ e, x ∈ (f y)) /\ (∀'z ∈ e, has_results (f z)).
Proof.
  destruct e; hauto l:on simp+:exec_unfold db:execc.
Qed.

Global Instance unfold_elem_of_mbind E A B x e (f : A -> t E B) P Q R:
  (forall z, UnfoldElemOf z e (P z)) ->
  (forall z, UnfoldHasResults (f z) (Q z)) ->
  (forall z, UnfoldElemOf x (f z) (R z)) ->
  UnfoldElemOf x (e ≫= f) ((exists z, P z /\ R z) /\ (forall z, P z -> Q z)).
Proof. tcclean.  apply elem_of_mbind. Qed.

(* This is an optimisation of the previous rewriting rules *)
Lemma elem_of_error_none_mbind E A B (x : B) (f: A -> t E B) err opt :
  x ∈ (error_none err opt ≫= f) <-> exists y, opt = Some y /\ x ∈ (f y).
Proof.
  hauto db:execc simp+:exec_unfold. Qed.
#[global] Hint Rewrite elem_of_error_none_mbind : exec.

Global Instance unfold_elem_of_error_none_mbind
    E A B (x : B) (f: A -> t E B) err opt P:
  (forall z, UnfoldElemOf x (f z) (P z)) ->
  UnfoldElemOf x (error_none err opt ≫= f) (exists y, opt = Some y /\ P y).
Proof. tcclean. apply elem_of_error_none_mbind. Qed.

Ltac dest_unit :=
  match goal with
  | u : () |- _ => destruct u
  end.

Global Instance unfold_elem_of_fail_if_mbind
    E B (x : B) (f: () -> t E B) b e P:
  UnfoldElemOf x (f ()) P ->
  UnfoldElemOf x (fail_if b e ≫= f) (¬ b /\ P).
Proof. tcclean. sauto simp+:dest_unit simp+:exec_unfold. Qed.

Global Instance unfold_elem_of_assert_mbind
    E B (x : B) (f: () -> t E B) b P:
  UnfoldElemOf x (f ()) P ->
  UnfoldElemOf x (assert b ≫= f) (b /\ P).
Proof.
  tcclean.
  unfold assert.
  sauto simp+:dest_unit simp+:exec_unfold.
Qed.





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

End Exec.

(* Copy paste of the tactics: delete in Coq 8.15 and import tactics instead *)

Tactic Notation "exec_unfold" :=
  let rec unfold_hyps :=
    try match goal with
    | H : ?P |- _ =>
       lazymatch type of P with
       | Prop =>
         apply Exec.exec_unfold_1 in H; revert H;
         first [unfold_hyps; intros H | intros H; fail 1]
       | _ => fail
       end
    end in
  apply Exec.exec_unfold_2; unfold_hyps; csimpl in *.

Tactic Notation "exec_unfold" "in" ident(H) :=
  let P := type of H in
  lazymatch type of P with
  | Prop => apply Exec.exec_unfold_1 in H; csimpl in H
  | _ => fail "hypothesis" H "is not a proposition"
  end.
