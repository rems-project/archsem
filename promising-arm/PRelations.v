(* This file define support for relation in the promising model.

   This is required because of various compatibility issues with the library
   used by this development:

   - The notation of Hahn and stdpp are in conflict.
   - stdpp redefine its own concept of reflexive transitive closure which is by
     default incompatible with the version of the standard library.

   The current design choice with those incompatibilities are:
   - Use stdpp notations and implement the correct typeclasses so that they
     are usable for relations.
   - Use the standard library definitions for relations like clos_refl_trans.
   - Redefine Hahn notations that are compatible with stdpp in a relation scope
   - Unfortunately: Import needed lemmas from Hahn one by one.
*)

From Coq.Relations Require Export
     Relation_Definitions
     Relation_Operators
     Operators_Properties.


Require hahn.Hahn.
Module Rel := HahnRelationsBasic.

From stdpp Require Import base sets.
(* stdpp.relations is explicitely ignored because I use the
   standard library + hahn formalism *)

From Hammer Require Import Tactics. (* sauto/hauto/... *)

Declare Scope rels_scope.
Delimit Scope rels_scope with rels.

Global Instance rel_elem_of {A} : ElemOf (A * A) (relation A) :=
  fun '(a, b) R => R a b.

Global Instance rel_empty {A} : Empty (relation A) := fun a b => False.

Global Instance rel_union {A} : Union (relation A) :=
  @Relation_Operators.union A.

Notation "P ⨾ Q" := (Rel.seq P Q) (at level 44, right associativity)
    : rels_scope.
Notation "a ⁺" := (clos_trans a) (at level 1, format "a ⁺") : rels_scope.
Notation "a ^+" := (clos_trans a) (at level 1, only parsing) : rels_scope.
Notation "a ^*" := (clos_refl_trans a) (at level 1, format "a ^*") : rels_scope.
Notation "a ⁻¹" := (transp a) (at level 1, format "a ⁻¹") : rels_scope.
Notation "a ^{-1}" := (transp a) (at level 1, only parsing) : rels_scope.
Notation "a ^?" := (clos_refl a) (at level 1, format "a ^?") : rels_scope.
Notation "⦗ a ⦘" := (Rel.eqv_rel a) (format "⦗ a ⦘") : rels_scope.

Global Hint Unfold inclusion : rels.



Lemma forall_pair_expand A B (P : A * B -> Prop) :
  (forall x : A * B, P x) <-> (forall a :A, forall b : B, P (a, b)).
Proof. hauto lq:on. Qed.


Lemma subseteq_inclusion A (R R' : relation A):
  R ⊆ R' <-> inclusion R R'.
Proof.
  unfold subseteq.
  unfold set_subseteq_instance.
  rewrite forall_pair_expand.
  firstorder.
  Qed.
Hint Rewrite subseteq_inclusion : rels.
