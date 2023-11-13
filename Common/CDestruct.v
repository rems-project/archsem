Require Import Options.
Require Import CBase.



(** * ObvFalse

This is a typeclass to gather fact that are obviously false. If you have a
theory specific way of deriving false, add it to this typeclass *)
Class ObvFalse (P : Prop) := {obv_false : P → False}.
Global Hint Mode ObvFalse + : typeclass_instances.

Global Instance obv_false_False : ObvFalse False.
Proof. by tcclean. Qed.

Global Hint Extern 10 (ObvFalse _) =>
  let H := fresh "H" in
  constructor; intro H; discriminate H : typeclass_instances.

Global Hint Extern 8 (ObvFalse (¬ _)) =>
  let H := fresh "H" in
  constructor; intro H; contradiction H : typeclass_instances.

(** * CDestruct

[cdestruct] is a custom destruction tactic. The goal is to recursively destruct
[∧], [∃], pairs as well as specified custom types as well as cleaning up
injective equalities (like [Some x = Some y]). [cdestruct] is intended to stay
safe and should never do unsafe (irreversible) operations. Here is an hopefully
exhaustive list of what [cdestruct] does.

- Destruct any type for which [CDestructCase] is implemented ([∧], [∃], [True]
  and pairs by default) - Apply simplification rule given by [CDestructSimpl]
  which include - Simplify equalities according to [Inj] and [Inj2] like [Some x
  = Some y] or [(a, b) = (c, d)] - Solve the goal if any of the introduced
  hypothesis is obviously false ([ObvFalse])

Additionally [cdestruct] can be configured with typeclass options to do more
things. *)

(** ** CDestruct options *)

(** If [CDestrCase] is enabled for a type, then [cdestruct] will destruct
    that type when it sees it *)
Class CDestrCase (T : Type) := {}.

(** [cdestruct] will apply all simplification provided by [CDestrSimpl] *)
Class CDestrSimpl (P Q : Prop) := {cdestruct_simpl : P ↔ Q}.
Global Hint Mode CDestrSimpl + - : typeclass_instances.

(** If [CDestrSubst] is enabled, [cdestruct] will try to apply [subst] on every equalities
it sees. *)
Class CDestrSubst := {}.

(** If [CDestrCbn] is enabled, then [cdestruct] will apply [cbn] on all the
    goals it sees. *)
Class CDestrCbn := {}.

(** If [CDestrMatchT] is enabled for a type, then [cdestruct] will process match
    cases of that type by calling [destruct] on the match discriminee. The value
    will therefore be destructed even if not directly processed by [cdestruct]
    *)
Class CDestrMatchT (T : Type) := {}.

(** [CDestrMatch] is [CDestrMatch T] for all [T] *)
Class CDestrMatch := {}.
Global Instance cdestr_matchT `{CDestrMatch} T : CDestrMatchT T. Qed.

(** [CDestrRecInj] allow [cdestruct] to blow up record equalities of the form [{|
    ... |} = {| ... |}] in a group of field-wise equality. One must specify the
    constructor term for internal reasons (it's hard to guess). The record must
    implement [Settable] *)
Class CDestrRecInj (rec_type : Type) {constr_type : Type}
  (constr : constr_type) := {}.

(* Assumes already blocked goal, H must be valid hyp *)
Ltac cdestruct_core H :=
  assert_succeeds (revert H);
  let cont a :=
      match goal with
      | |- block _ => idtac
      | |- ?G =>
          let x := intro_get_name in
          once cdestruct_core x
      | |- _ => idtac
      end in
  match type of H with
  | ?T =>
      has_option (CDestrCase T);
      case H; clear H;
      cont ()
  | _ =>
      once apply obv_false in H;
      destruct H;
      fail
  | _ =>
      once rewrite cdestruct_simpl in H;
      once cdestruct_core H
  | ?x = ?y =>
      has_option CDestrSubst;
      once first [subst x | subst y];
      cont ()
  | match ?b with _ => _ end =>
      let T := type of b in
      has_option (CDestrMatchT T);
      let Heqn := fresh in
      destruct b eqn:Heqn;
      revert H;
      once cdestruct_core Heqn
  | _ =>
      has_option CDestrCbn;
      progress (cbn in H);
      once cdestruct_core H
  | ?T =>
      cont ();
      try revert H
  end.

(** [cdestruct H] will destroy [H] with the cdestruct engine. It will not touch
    the other hypotheses or the goal (unless through [CDestrSubst] or
    [CDestrMatch]. *)
Tactic Notation "cdestruct" ident(H) :=
  block_goal; cdestruct_core H; intros; unblock_goal.
Tactic Notation "cdestruct" ident(H) "as" simple_intropattern_list(pats) :=
  block_goal; cdestruct_core H; intros pats; unblock_goal.

(** [cdestruct_intro] will introduce the next value and call cdestruct on it.
    It's the [cdestruct] equivalent of [destruct 1]. *)
Tactic Notation "cdestruct_intro" :=
  let H := intro_get_name in cdestruct H.
Tactic Notation "cdestruct_intro" "as" simple_intropattern_list(pats) :=
  let H := intro_get_name in cdestruct H as pats.

(** [cdestruct_intros] will introduce all possible values (like [intros]), but
additionally destroy each of them with the [cdestruct] engine. *)
Tactic Notation "cdestruct_intros" :=
  let H := intro_get_name in cdestruct_core H; intros.
Tactic Notation "cdestruct_intros" "as" simple_intropattern_list(pats) :=
  let H := intro_get_name in cdestruct_core H; intro pats.

(** ** Default Instanciation of the CDestruct typeclasses *)

(** CDestruct destroys [∧], [∃], pairs, [True] and [False] by default. It
    purposefully does NOT destroy [∨] by default. This behavior can be added
    locally with [#[local] Existing Instance cdestruct_or] or with
    [cdestruct use cdestruct_or] *)
Global Instance cdestruct_and A B : CDestrCase (A ∧ B) := ltac:(constructor).
#[global] Instance cdestruct_ex T P : CDestrCase (∃ x : T, P x) := ltac:(constructor).
#[global] Instance cdestruct_pair (A B : Type) : CDestrCase (A * B) :=
  ltac:(constructor).
Global Instance cdestruct_True : CDestrCase True := ltac:(constructor).
Global Instance cdestruct_False : CDestrCase False := ltac:(constructor).
Definition cdestruct_or A B : CDestrCase (A ∨ B) := ltac:(constructor).

(** Injective equalities are simplified by default *)
Global Instance cdestruct_inj `{Inj A B RA RB f} {HP: Proper (RA ==> RB) f} x y :
  CDestrSimpl (RB (f x) (f y)) (RA x y).
Proof. constructor. use (inj f). naive_solver. Qed.

Global Instance cdestruct_inj2 `{Inj2 A B C RA RB RC f}
    {HP : Proper (RA ==> RB ==> RC) f} x1 x2 y1 y2 :
  CDestrSimpl (RC (f x1 x2) (f y1 y2)) (RA x1 y1 ∧ RB x2 y2).
Proof. constructor. use (inj2 f). sfirstorder. Qed.

(** Implementation of [CDestrRecInj], see the typeclass definition for an
    explanation *)
#[global] Hint Extern 30 (CDestrSimpl (?L =@{?T} ?R) ?Q) =>
  let L_head := get_head L in
  let R_head := get_head R in
  has_option (CDestrRecInj T L_head);
  unify L_head R_head;
  constructor;
  rewrite record_eq_unfold;
  cbn;
  reflexivity : typeclass_instances.
