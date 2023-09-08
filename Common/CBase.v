
From stdpp Require Export base.
From stdpp Require Export tactics.
Require Import DecidableClass.
Require Export Relations.
From RecordUpdate Require Export RecordSet.
From Hammer Require Export Tactics.
Require Import ZArith.

#[export] Set Keyed Unification.

(*** Notations ***)


(** Functional pipe notation.

    TODO figure out a correct parsing level. Currently is just below relation so
    that a = b |> f will be parsed as a = (b |> f). *)
Notation "v |> f" := (f v) (at level 69, only parsing, left associativity).

(* FMap notations *)
Notation "v |$> f" := (fmap f v) (at level 69, only parsing, left associativity).
Notation "f <$>@{ M } v" := (@fmap M _ _ _ f v) (at level 61, only parsing, left associativity).
Notation "v |$>@{ M } f" := (@fmap M _ _ _ f v) (at level 69, only parsing, left associativity).


(** Monadic bind with an explicit monad annotation *)
Notation "x ←@{ M } y ; z" := (@mbind M _ _ _ (λ x : _, z) y)
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.
Notation "' x ←@{ M } y ; z" := (@mbind M _ _ _ (λ x : _, z) y)
  (at level 20, x pattern, y at level 100, z at level 200, only parsing) : stdpp_scope.


(*** Utility functions ***)

(** Convenient iff destruction *)
Definition iffLR {A B : Prop} (i : A <-> B) : A -> B := proj1 i.
Definition iffRL {A B : Prop} (i : A <-> B) : B -> A := proj2 i.

(** Convert a true proposition into a rewriting rule of that proposition to true
*)
Definition Prop_for_rewrite {P : Prop} (H : P) : P <-> True.
  firstorder.
Defined.


(*** Constrained quantifiers ***)

Notation "∀' x ∈ b , P" := (∀ x, x ∈ b → P)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∀' x  ∈  b ']' ,  '/' P ']'") : type_scope.

(* The formatting, doesn't work so this is still printed as exists x, x ∈ b ∧ P
   but that's not really a problem *)
Notation "∃' x ∈ b , P" := (∃ x, x ∈ b ∧ P)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∃' x  ∈  b ']' ,  '/' P ']'") : type_scope.


(*** Relations ***)

Arguments clos_refl_trans {_}.


(*** Utility tactics ***)

Ltac block t := change t with (block t) in *.
Ltac unblock := unfold block in *.

(* useful for debugging *)
Ltac deintro :=
  match goal with
  | H : _ |- _ => generalize dependent H
  end.
Ltac deintros := repeat deintro.
Ltac print_full_goal := try(deintros; match goal with |- ?G => idtac G end; fail).

(* run tac on all hypotheses in first-to-last order *)
Ltac forall_hyps tac :=
  lazymatch goal with
  | H : _ |- _ => revert H; try (forall_hyps tac); intro H; try(tac H)
  end.

(** Actual dependent rewrite by calling destruct on the equality.
    The rewrite must be of the form var = exp where var is a plain variable and not
    a complicated expression *)
Tactic Notation "drewrite" "<-" constr(H) :=
  match type of H with
  | _ = _ => destruct H
  end.
Tactic Notation "drewrite" "->" constr(H) := symmetry in H; drewrite <- H.
Tactic Notation "drewrite" constr(H) := drewrite -> H.

(** Typeclass clean to help prove typeclasss lemmas *)
Ltac tcclean_hyp H :=
  lazymatch type of H with
  | forall x y, @?P x y =>
    let tP := type of P in
    let Q := mk_evar tP in
    let Hb := fresh "H" in
    rename H into Hb;
    assert (forall x y, Q x y);
    [intros x y; destruct (Hb x y) as [H]; exact H |];
    simpl in H;
    clear Hb;
    try(repeat (setoid_rewrite <- H || rewrite <- H))
  | forall z, @?P z =>
    let tP := type of P in
    let Q := mk_evar tP in
    let Hb := fresh "H" in
    rename H into Hb;
    assert (forall z, Q z);
    [intro z; destruct (Hb z) as [H]; exact H |];
    simpl in H;
    clear Hb;
    try(repeat (setoid_rewrite <- H || rewrite <- H))
  | TCEq _ _ => rewrite TCEq_eq in H; try (setoid_rewrite H)
  | Unconvertible _ _ _ => clear H
  | TCFastDone _ => apply (@tc_fast_done _) in H
  | _ => destruct H as [H]; try(repeat (setoid_rewrite <- H || rewrite <- H))
  end.

Ltac tcclean :=
  repeat (let H := fresh "H" in intro H; try (tcclean_hyp H));
  constructor.

(*** Integer lattice ***)

(* n ⊔ n' means max and n ⊓ n' means min *)

#[global] Instance join_nat : Join nat := Nat.max.
#[global] Instance meet_nat : Meet nat := Nat.min.
#[global] Instance join_pos : Join positive := Pos.max.
#[global] Instance meet_pos : Meet positive := Pos.min.
#[global] Instance join_N : Join N := N.max.
#[global] Instance meet_N : Meet N := N.min.
#[global] Instance join_Z : Join Z := Z.max.
#[global] Instance meet_Z : Meet Z := Z.min.


(*** Typeclass magic ***)

Require Import Morphisms.
Import Morphisms.ProperNotations.
Require Import Coq.Classes.RelationClasses.
From stdpp Require Import sets.

Opaque Unconvertible.

Global Instance Unconvertible_proper A :
  Proper ((=) ==> (=) ==> (=)) (Unconvertible A).
Proof.
  unfold Proper.
  solve_proper.
Qed.

(* I don't want unfolding typeclasses such as SetUnfold to unfold an mbind ever *)
Global Typeclasses Opaque mbind.

(* A variation of solve_proper that uses setoid_rewrite *)

Ltac solve_proper2_core tac :=
  match goal with
  | |- Proper _ _ => unfold Proper; solve_proper2_core tac
  | |- respectful _ _ _ _ =>
    let H := fresh "h" in
    intros ? ? H; solve_proper2_core tac;
    let t := type of H in
    try rewrite H in *
  | |- _ => tac
  end.

(* For Proper of a typeclass in Prop (the last relation must be iff)
   The tactic passed to core will see a goal of the form
   TC arg1 arg2 ↔ TC arg1' arg2' *)
Ltac solve_proper2_tc :=
  solve_proper2_core ltac:(split; destruct 1; constructor); assumption.

(* For Proper of an unfoldable function *)
Ltac solve_proper2_funcs :=
  solve_proper2_core solve_proper_unfold; reflexivity.

Global Instance SetUnfold_proper :
  Proper (iff ==> iff ==> iff) SetUnfold.
Proof. solve_proper2_tc. Qed.

Global Instance SetUnfoldElemOf_proper `{ElemOf A C}  :
  Proper ((=@{A}) ==> (≡@{C}) ==> iff ==> iff) SetUnfoldElemOf.
Proof. solve_proper2_tc. Qed.


(*** Record management ***)

Definition setv {R T} (proj : R -> T) {_ : Setter proj} ( v: T) : R -> R :=
  set proj (fun _ => v).

(** This allows to use set fst and set snd on pairs *)
Global Instance eta_pair A B : Settable (A * B) :=
  settable! (fun (a : A) (b : B) => (a, b)) <fst;snd>.

Global Instance Setter_compose `{SRT : Setter R T proj}
  `{STT : Setter T T' proj'} :
  Setter (proj' ∘ proj) := fun x => SRT (STT x).

Global Program Instance Setter_compose_wf `{SRT : SetterWf R T proj}
  `{STT : SetterWf T T' proj'} : SetterWf (proj' ∘ proj) :=
  { set_wf := Setter_compose;
    set_get := _;
    set_eq := _ }.
Solve All Obligations with sauto lq:on.

(*** Pair management ***)

Create HintDb pair discriminated.
Lemma exists_pair B C P:
  (∃ x : C * B, P x) ↔ (∃ x y, P (x, y)).
Proof. hauto lq:on. Qed.
#[global] Hint Resolve <- exists_pair : pair.
#[global] Hint Rewrite exists_pair : pair.

Lemma forall_pair B C (P : B * C → Prop):
  (∀ x : B * C, P x) ↔ ∀ x y, P (x, y).
Proof. hauto lq:on. Qed.
#[global] Hint Rewrite forall_pair : pair.

Lemma pair_let_simp A B (z : A * B) P : (let '(x,y) := z in P x y) ↔ P z.1 z.2.
Proof. by destruct z. Qed.
#[global] Hint Rewrite pair_let_simp : pair.
#[global] Hint Rewrite <- surjective_pairing : pair.
Ltac pair_let_clean :=
  setoid_rewrite pair_let_simp; try (setoid_rewrite <- surjective_pairing).
