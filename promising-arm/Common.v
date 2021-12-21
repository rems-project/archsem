(** This file contains common definition and automation helpers that are use in
    the rest of this development.

    It contains automation helpers, some patching to get multiple library to
    interact correctly with each other and various utility definitions. *)

From Hammer Require Export Tactics.
From RecordUpdate Require Export RecordSet.
From stdpp Require Export base strings.
Require Export bbv.Word.

Require Import Sail.Base.

Require Import PRelations.


(** Functional pipe notation.

    TODO figure out a correct parsing level. Currently is just below relation so
    that a = b |> f will be parsed as a = (b |> f). *)
Notation "v |> f" := (f v) (at level 69, only parsing, left associativity).



(********** Boolean reflection **********)

(* This is a hack to make CoqHammer boolean reflection use the Is_true coercion
    from stdpp*)

(* Using a plain Require and not Require Import is critical to not import the
   is_true coercion since stdpp already uses the Is_true coercion. *)
From Hammer Require Reflect.

Tactic Notation "breflect" :=
  try rewrite_strat topdown hints brefl.

Tactic Notation "breflect" "in" hyp(H) :=
  try rewrite_strat topdown hints brefl in H.

Tactic Notation "breflect" "in" "*" :=
  breflect;
  repeat match goal with
         | [H : _ |- _ ] => rewrite_strat topdown hints brefl in H
         end.

(* Convert the normal coercion to the is_true one that CoqHammer expects. *)
Lemma true_is_true (b : bool) : b <-> is_true b.
  Proof. sauto lq:on. Qed.
Hint Rewrite -> true_is_true : brefl.
Hint Rewrite <- true_is_true : breif.


(** existsb boolean reflection *)
Lemma existsb_exists' (A : Type) (f : A → bool) (l : list A):
  is_true (existsb f l) ↔ (∃ x : A, In x l ∧ is_true(f x)).
Proof. unfold is_true. apply existsb_exists. Qed.
Hint Rewrite existsb_exists' : brefl.




(********** List automation **********)

(** Automation for list simplifications *)
Tactic Notation "list_simp" "in" "|-*" :=
  rewrite_strat topdown hints list.

Tactic Notation "list_simp" "in" hyp(H) :=
  rewrite_strat topdown hints list in H.

Tactic Notation "list_simp" :=
  progress (try list_simp in |-*;
  repeat match goal with
         | [H : _ |- _ ] => rewrite_strat topdown hints list in H
         end).

Hint Rewrite in_app_iff : list.
Arguments elem_of_list_In : clear implicits.
Hint Rewrite elem_of_list_In : list.
Arguments list_subseteq _ _ _ /.
Hint Rewrite Forall_forall : list.

Global Hint Resolve in_map : list.




(********** Decidable equality **********)

(** Decidable equality notation that use the EqDecision type class from stdpp*)
Notation "x == y" := (bool_decide (x = y)) (at level 70, no associativity).

(** Boolean reflection of decidable equality. *)
Lemma bool_decide_is_true (P : Prop) {dec : Decision P} :
  is_true (bool_decide P) <-> P.
Proof. unfold is_true. apply bool_decide_eq_true. Qed.
Hint Rewrite bool_decide_is_true : brefl.

(* Interface Equality decision for words (from bbv) *)
Global Instance word_eq_dec n : EqDecision (word n).
Proof.
  unfold EqDecision.
  unfold Decision.
  auto using weq.
Defined.

(** Convert automatical a Decidable instance (Coq standard library) to
    a Decision instance (stdpp)

    TODO: Decide (no pun intended) if we actually want to use Decidable or
    Decision in this development. *)
Global Instance Decidable_to_Decision P `{dec : Decidable P} : Decision P.
Proof.
  (* sauto lq:on dep:on works, but since this is a Defined and noq a Qed.
     I went for a manual proof that prooduces a simpler term. *)
  unfold Decision.
  destruct dec as [p Spec].
  destruct p.
  - left.
    apply Spec.
    reflexivity.
  - right.
    intro.
    apply Spec in H.
    inversion H.
Defined.




(********** Utility functions **********)

(** Update a function at a specific value *)
Definition fun_add {A B} {_: EqDecision A} (k : A) (v : B) (f : A -> B) :=
  fun x : A => if k == x then v else f x.


(** A list_remove version that uses the EqDecision typeclass *)
Definition list_remove `{EqDecision A} :=
  List.remove (decide_rel (=@{A})).


(** I couldn't find this in the standard library but there should be something
somewhere. I can't be the first one to need that.*)
Fixpoint list_set {A} (n : nat) (v : A) (l : list A) :=
  match l, n with
  | nil, _ => nil
  | h :: t, 0%nat => v :: t
  | h :: t, S m => h :: (list_set m v t)
  end.
