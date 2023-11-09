
From stdpp Require Export base.
From stdpp Require Export fin.
From stdpp Require Export tactics.
From stdpp Require Import vector.
From stdpp Require Import decidable.
Require Export Relations.
From RecordUpdate Require Export RecordSet.
From Hammer Require Export Tactics.
Require Import ZArith.
Require Import Options.


(** * Notations ***)


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

(** Useful for defining decision procedures *)
Notation dec_if D := (match D with | left _ => left _ | right _ => right _ end).
Notation dec_swap D := (match D with | left _ => right _ | right _ => left _ end).

(** * Utility functions ***)

(** Convenient iff destruction *)
Definition iffLR {A B : Prop} (i : A <-> B) : A -> B := proj1 i.
Definition iffRL {A B : Prop} (i : A <-> B) : B -> A := proj2 i.

(** Convert a true proposition into a rewriting rule of that proposition to true
*)
Definition Prop_for_rewrite {P : Prop} (H : P) : P <-> True.
  firstorder.
Defined.

(** Unpack an exception *)
Definition othrow `{MThrow E M} `{MRet M} {A} (err : E) (v : option A) : M A :=
  match v with
  | None => mthrow err
  | Some x => mret x
  end.

(** This is useful for keeping the equality in a match for dependent typing
    purposes *)
Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.

(** When matching [inspect p] instead of [p], this notation allows to have the
    cases be [| pat_for_p ed: Heq => ...] *)
Notation "x 'eq:' p" := (exist _ x p) (only parsing, at level 20).

Definition mapl {A B C} (f : A → B) (x : A + C) : B + C :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

Definition mapr {A B C} (f : B → C) (x : A + B) : A + C :=
  match x with
  | inl l => inl l
  | inr r => inr (f r)
  end.


(** * Constrained quantifiers ***)

Notation "∀' x ∈ b , P" := (∀ x, x ∈ b → P)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∀' x  ∈  b ']' ,  '/' P ']'") : type_scope.

(* The formatting, doesn't work so this is still printed as exists x, x ∈ b ∧ P
   but that's not really a problem *)
Notation "∃' x ∈ b , P" := (∃ x, x ∈ b ∧ P)
  (at level 200, x binder, right associativity,
  format "'[ ' '[ ' ∃' x  ∈  b ']' ,  '/' P ']'") : type_scope.


(** * Relations ***)

Arguments clos_refl_trans {_}.


(** * Utility tactics ***)

Ltac block t := change t with (block t) in *.
Ltac unblock := unfold block in *.

(* useful for debugging *)
Ltac deintro :=
  match goal with
  | H : _ |- _ => revert H
  end.
Ltac deintros := repeat deintro.
Ltac print_full_goal := try(deintros; match goal with |- ?G => idtac G end; fail).

(* Take an evar and puts it in a pattern shape. Use as (do n pattern_evar) if you have n evars in your goal. This is needed for typeclass-based rewriting tactics *)
(* TODO detect the number of evar automatically *)
Ltac pattern_evar :=
  match goal with | |- context G [?x] => is_evar x; pattern x end.

(* run tac on all hypotheses in first-to-last order *)
Ltac forall_hyps tac :=
  lazymatch goal with
  | H : _ |- _ => revert H; try (forall_hyps tac); intro H; try(tac H)
  end.

Tactic Notation "orewrite" uconstr(p) :=
  opose_core p ltac: (fun p => rewrite p).
Tactic Notation "orewrite" "*" uconstr(p) :=
  opose_specialize_foralls_core p () ltac: (fun p => rewrite p).

Tactic Notation "osrewrite" uconstr(p) :=
  opose_core p ltac: (fun p => setoid_rewrite p).
Tactic Notation "osrewrite" "*" uconstr(p) :=
  opose_specialize_foralls_core p () ltac: (fun p => setoid_rewrite p).

(** Actual dependent rewrite by calling destruct on the equality.
    The rewrite must be of the form var = exp where var is a plain variable and not
    a complicated expression. Use subst if you can, this is last resort *)
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
  (let H := fresh "H" in intro H; tcclean; try(tcclean_hyp H)) || constructor.

(** Convenient notation for deciding a proposition in a proof *)
Tactic Notation "destruct" "decide" constr(P) := destruct (decide P).
Tactic Notation "destruct" "decide" constr(P) "as" simple_intropattern(pat) :=
  destruct (decide P) as pat.

(** Check if x = y. If yes, replace all y by x in the goal *)
Tactic Notation "destruct" "decide" "subst" constr(x) constr (y) :=
  destruct decide (x = y);[subst y |].

Tactic Notation "destruct" "decide" "subst" constr(x) constr (y)
    "as" simple_intropattern(pat) :=
  destruct decide (x = y) as [? | pat]; [subst y |].


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


(** * Typeclass magic ***)

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


(** * Record management ***)

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
  { set_wf := Setter_compose }.
Solve All Obligations with sauto lq:on.

(* SetterWF can only be proven for particular Ms *)
#[global] Instance Setter_alter `{LookupTotal K A M, Alter K A M} k :
  @Setter M A (lookup_total k) := λ f, alter f k.

(** Tactic to prove record equality by proving equality for all fields. If two
    fields are identical (according to the reflexivity tactic), this will not
    create a subgoal for them, so the number of subgoal may vary, don't rely on
    it *)
Ltac record_eq :=
  setoid_rewrite <- mkT_ok;
  lazymatch goal with
    |- mkT ?T ?T_eta _ = mkT ?T' ?T_eta' _ =>
      unify T T'; unify T_eta T_eta';
      cbn [T_eta mkT]
  end; f_equal.

(** * Pair management ***)

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

(** * EmptyT and DecisionT *)

(** Mark a type as empty, useable for guiding typeclass resolution. *)
Class EmptyT (T : Type) := emptyT : (T → False : Prop).
Global Hint Mode EmptyT ! : typeclass_instances.


(** Typeclass for type (and more usefully families of types) that are decidably
    empty or not *)
Class DecisionT (T : Type) := decideT : T + {T → False}.
Global Hint Mode DecisionT ! : typeclass_instances.
Global Arguments decideT _ {_} : simpl never, assert.

Global Instance inabited_decisionT `{Inhabited T} : DecisionT T :=
  inleft inhabitant.
Global Instance emptyT_decisionT `{EmptyT T} : DecisionT T := inright emptyT.

(** Application of DecisionT to fin *)
Global Instance emptyT_fin0 : EmptyT (fin 0).
Proof. inversion 1. Qed.

Global Instance inhabited_finSn n : Inhabited (fin (S n)).
Proof. repeat constructor. Qed.

Global Instance decisionT_fin n : DecisionT (fin n).
Proof. destruct n; apply _. Qed.

Global Instance emptyT_pair1  `{EmptyT A} B : EmptyT (A * B).
Proof. sfirstorder. Qed.

Global Instance emptyT_pair2 A `{EmptyT B} : EmptyT (A * B).
Proof. sfirstorder. Qed.

Global Instance emptyT_sum  `{EmptyT A} `{EmptyT B} : EmptyT (A + B).
Proof. sfirstorder. Qed.

Global Instance DecisionT_pair  `{DecisionT A} `{DecisionT B} : DecisionT (A * B).
Proof. sfirstorder. Qed.

Global Instance DecisionT_sum  `{DecisionT A} `{DecisionT B} : DecisionT (A + B).
Proof. sfirstorder. Qed.
