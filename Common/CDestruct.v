Require Import Options.
Require Import CBase.
Require Import Program Equality.


(** * Injectivity

    This is a is done with a bunch of injectivity typeclasses, that can be used
    elsewhere. This enforce that any injection done by [cdestruct] respects
    typeclass opaqueness (unlike the regular [injection]) *)

(** Deduce Inj instance from dependent injection. This might use UIP *)
#[export] Hint Extern 20 (Inj ?A eq ?Constr) =>
  eunify A eq;
  unfold Inj;
  by simplify_dep_elim
  : typeclass_instances.

(** Deduce Inj2 instance from dependent injection. This might use UIP *)
#[export] Hint Extern 20 (Inj2 ?A ?B eq ?Constr) =>
  eunify A eq;
  eunify B eq;
  unfold Inj2;
  by simplify_dep_elim
  : typeclass_instances.

Lemma inj2_iff `{Inj2 A B C RA RB RC f} {HP : Proper (RA ==> RB ==> RC) f}
  x1 x2 y1 y2 :
  RC (f x1 x2) (f y1 y2) ↔ RA x1 y1 ∧ RB x2 y2.
Proof. split; intro; [by apply (inj2 f) | apply HP; naive_solver]. Qed.
Arguments inj2_iff {_ _ _ _ _ _} _ {_ _}.



Class Inj3 {A B C D} (R1 : relation A) (R2 : relation B) (R3 : relation C)
    (S : relation D) (f : A → B → C → D) : Prop := inj3 x1 x2 x3 y1 y2 y3 :
    S (f x1 x2 x3) (f y1 y2 y3) → R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3.
Global Arguments inj3 {_ _ _ _ _ _ _ _} _ {_} _ _ _ _ _ _ _: assert.

Lemma inj3_iff `{Inj3 A B C D R1 R2 R3 RS f}
  {HP : Proper (R1 ==> R2 ==> R3 ==> RS) f} x1 x2 x3 y1 y2 y3 :
  RS (f x1 x2 x3) (f y1 y2 y3) ↔ R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3.
Proof. split; intro; [by apply (inj3 f) | apply HP; naive_solver]. Qed.
Arguments inj3_iff {_ _ _ _ _ _ _ _} _ {_ _}.

(** Deduce Inj3 instance from dependent injection. This might use UIP *)
#[export] Hint Extern 20 (Inj3 ?A ?B ?C eq ?Constr) =>
  eunify A eq;
  eunify B eq;
  eunify C eq;
  unfold Inj3;
  by simplify_dep_elim
  : typeclass_instances.


Class Inj4 {A B C D E} (R1 : relation A) (R2 : relation B) (R3 : relation C)
  (R4 : relation D) (S : relation E) (f : A → B → C → D → E) : Prop :=
  inj4 x1 x2 x3 x4 y1 y2 y3 y4 :
    S (f x1 x2 x3 x4) (f y1 y2 y3 y4) →
    R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3 ∧ R4 x4 y4.
Global Arguments inj4 {_ _ _ _ _ _ _ _ _ _} _ {_} _ _ _ _ _ _ _ _ _: assert.

Lemma inj4_iff `{Inj4 A B C D E R1 R2 R3 R4 RS f}
  {HP : Proper (R1 ==> R2 ==> R3 ==> R4 ==> RS) f} x1 x2 x3 x4 y1 y2 y3 y4 :
  RS (f x1 x2 x3 x4) (f y1 y2 y3 y4) ↔ R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3 ∧ R4 x4 y4.
Proof. split; intro; [by apply (inj4 f) | apply HP; naive_solver]. Qed.
Arguments inj4_iff {_ _ _ _ _ _ _ _ _ _} _ {_ _}.

#[export] Hint Rewrite @inj_iff using tc_solve : inj.
#[export] Hint Rewrite @inj2_iff using tc_solve : inj.
#[export] Hint Rewrite @inj3_iff using tc_solve : inj.
#[export] Hint Rewrite @inj4_iff using tc_solve : inj.

(** Deduce Inj4 instance from dependent injection. This might use UIP *)
#[export] Hint Extern 20 (Inj4 ?A ?B ?C ?D eq ?Constr) =>
  eunify A eq;
  eunify B eq;
  eunify C eq;
  eunify D eq;
  unfold Inj4;
  by simplify_dep_elim
  : typeclass_instances.

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
  and pairs by default)
- Apply simplification rule given by [CDestructSimpl] which include
  - Simplify equalities according to [Inj] and [Inj2] like [Some x = Some y]
    or [(a, b) = (c, d)] - Solve the goal if any of the introduced hypothesis
    is obviously false ([ObvFalse])

Additionally [cdestruct] can be configured with typeclass options to do more
things. *)

(** ** CDestruct options *)

(** If [CDestrCase] is enabled for a type, then [cdestruct] will destruct
    that type when it sees it *)
Class CDestrCase (T : Type) := {}.

(** [cdestruct] will apply all simplification provided by [CDestrSimpl] *)
Class CDestrSimpl (P Q : Prop) := cdestr_simpl {cdestruct_simpl : P ↔ Q}.
Global Hint Mode CDestrSimpl + - : typeclass_instances.
Arguments cdestr_simpl {_ _} .

(** If [CDestrSubst] is enabled, [cdestruct] will try to apply [subst] on every
    equality it sees. *)
Class CDestrSubst := {}.

(** If [CDestrCbn] is enabled, then [cdestruct] will apply [cbn] on all the
    hypotheses it sees. (Including types not in [Prop] *)
Class CDestrCbn := {}.

(** Convenience option to enable the previous 2 options in a single option *)
Class CDestrCbnSubst := {}.
#[global] Instance cdestr_cbnsubst_cbn `{CDestrCbnSubst} : CDestrCbn. Qed.
#[global] Instance cdestr_cbnsubst_subst `{CDestrCbnSubst} : CDestrSubst. Qed.

(** This is used to deal with dependent equality. When having a dependent
    equality implies simpler equalities. [cdestruct] will try to use the simpler
    equality to do substitution and therefore make the dependent equality
    simpler. For example when you have [existT a b = existT c d], one can deduce
    [a = c]. Then if either [a] or [c] is a variable, we can do a substitution
    and simplify the existT equality *)
(* TODO *)
Class CDestrSuperSubst (P : Prop) (T : Type) (a b : T) :=
  mk_cdestr_supersubst { cdestr_supersubst : P → a = b}.

(** If [CDestrMatchT] is enabled for a type, then [cdestruct] will process match
    cases of that type by calling [destruct] on the match discriminee. The value
    will therefore be destructed even if not directly processed by [cdestruct]
    *)
Class CDestrMatchT (T : Type) := {}.

(** [CDestrMatch] is [CDestrMatch T] for all [T] *)
Class CDestrMatch := {}.
Global Instance cdestr_matchT `{CDestrMatch} T : CDestrMatchT T. Qed.

(** [CDestrRecInj] allow [cdestruct] to blow up record equalities of the form
    [{| ... |} = {| ... |}] in a group of field-wise equality. One must specify
    the constructor term for internal reasons (it's hard to guess). The record
    must implement [Settable] *)
Class CDestrRecInj (rec_type : Type) {constr_type : Type}
  (constr : constr_type) := {}.

(* TODO switch to hyp_block hyp management *)

(* Assumes already blocked goal, H must be a valid hyp from which no other hyp
   depends on*)
Ltac cdestruct_core H :=
  (* Check that no other hypothesis depends on H *)
  assert_succeeds (revert H);
  (* Continues running by introducing the next hypothesis, The a is unit
     argument for lazyness *)
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
      (* TODO this is slow, there is way to make it faster.
         It should only run at top level *)
      once rewrite cdestruct_simpl in H;
      once cdestruct_core H
  | ?t = ?t =>
      (clear H || (revert H; refine (simplification_K _ t _ _)));
      cont ()
  | ?x = ?y =>
      has_option CDestrSubst;
      once first [subst x | subst y];
      cont ()
  | ?P =>
      has_option CDestrSubst;
      let H' := fresh in
      pose proof H as H';
      apply cdestr_supersubst in H';
      match type of H' with
      | ?x = ?y => once first [subst x | subst y]
      end;
      once cdestruct_core H
  | _ =>
      has_option CDestrCbn;
      progress (cbn in H);
      once cdestruct_core H
  | context [match ?b with _ => _ end] =>
      let T := type of b in
      has_option (CDestrMatchT T);
      let Heqn := fresh in
      destruct b eqn:Heqn;
      revert H;
      once cdestruct_core Heqn
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

(** CDestruct destroys [∧], [∃], pairs, [True], [False],[unit] and [Empty_set]
    by default. It purposefully does NOT destroy [∨] by default. This behavior
    can be added locally with [#[local] Existing Instance cdestruct_or] or with
    [cdestruct use cdestruct_or] *)
Global Instance cdestruct_and A B : CDestrCase (A ∧ B) := ltac:(constructor).
#[global] Instance cdestruct_ex T P : CDestrCase (∃ x : T, P x) := ltac:(constructor).
#[global] Instance cdestruct_pair (A B : Type) : CDestrCase (A * B) :=
  ltac:(constructor).
Global Instance cdestruct_True : CDestrCase True := ltac:(constructor).
Global Instance cdestruct_False : CDestrCase False := ltac:(constructor).
Definition cdestruct_or A B : CDestrCase (A ∨ B) := ltac:(constructor).
Definition cdestruct_sum A B : CDestrCase (A + B) := ltac:(constructor).
#[global] Instance cdestruct_unit : CDestrCase unit := ltac:(constructor).
#[global] Instance cdestruct_Empty_set : CDestrCase Empty_set := ltac:(constructor).

(** Injective equalities are simplified by default, up to 4 arguments *)
Global Instance cdestruct_inj `{Inj A B RA RB f} {HP: Proper (RA ==> RB) f} x y :
  CDestrSimpl (RB (f x) (f y)) (RA x y).
Proof. constructor. apply (inj_iff f). Qed.

Global Instance cdestruct_inj2 `{Inj2 A B C RA RB RC f}
  `{!Proper (RA ==> RB ==> RC) f} x1 x2 y1 y2 :
  CDestrSimpl (RC (f x1 x2) (f y1 y2)) (RA x1 y1 ∧ RB x2 y2).
Proof. constructor. apply (inj2_iff f). Qed.

Global Instance cdestruct_inj3 `{Inj3 A B C D R1 R2 R3 RS f}
    {HP : Proper (R1 ==> R2 ==> R3 ==> RS) f} x1 x2 x3 y1 y2 y3 :
  CDestrSimpl (RS (f x1 x2 x3) (f y1 y2 y3)) (R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3).
Proof. constructor. apply (inj3_iff f). Qed.

Global Instance cdestruct_inj4 `{Inj4 A B C D E R1 R2 R3 R4 RS f}
    {HP : Proper (R1 ==> R2 ==> R3 ==> R4 ==> RS) f} x1 x2 x3 x4 y1 y2 y3 y4 :
  CDestrSimpl (RS (f x1 x2 x3 x4) (f y1 y2 y3 y4))
    (R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3 ∧ R4 x4 y4).
Proof. constructor. apply (inj4_iff f). Qed.

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

#[global] Instance cdestr_supersubst_sigT (T : Type) (P : T → Type) a b c d :
  CDestrSuperSubst (existT a b =@{sigT P} existT c d) T a c.
Proof. tcclean. by simplify_dep_elim. Qed.

Instance cdestruct_bool_decide_true `{Decision P} :
  CDestrSimpl (bool_decide P = true) P.
Proof. tcclean. apply bool_decide_eq_true. Qed.

Instance cdestruct_bool_decide `{Decision P} :
  CDestrSimpl (bool_decide P) P.
Proof. tcclean. apply bool_decide_spec. Qed.

Instance cdestruct_bool_decide_false `{Decision P} :
  CDestrSimpl (bool_decide P = false) (¬ P).
Proof. tcclean. apply bool_decide_eq_false. Qed.

(** Try to do the axiom-free version first *)
Instance cdestruct_not_not_dec `{Decision P} :
  CDestrSimpl (¬ ¬ P) P | 10.
Proof. tcclean. sfirstorder use:dec_stable. Qed.

Instance cdestruct_not_not P :
  CDestrSimpl (¬ ¬ P) P | 20.
Proof. tcclean. use NNPP. naive_solver. Qed.
