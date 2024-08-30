Require Import Options.
Require Import CBase.
Require Import Program.Equality.


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

Create HintDb inj discriminated.

(** Use f_equal automatically and safely on injective functions *)
Hint Extern 1 (?f ?x = ?f ?y) =>
       has_option (Inj (=) (=) f);
       simple apply (f_equal f) : inj.

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

(** Use f_equal automatically and safely on injective functions *)
Hint Extern 1 (?f _ _ = ?f _ _) =>
       has_option (Inj2 (=) (=) (=) f);
       simple apply (f_equal2 f) : inj.


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

(** Use f_equal automatically and safely on injective functions *)
Hint Extern 1 (?f _ _ _ = ?f _ _ _) =>
       has_option (Inj3 (=) (=) (=) (=) f);
       simple apply (f_equal3 f) : inj.


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

(** Use f_equal automatically and safely on injective functions *)
Hint Extern 1 (?f _ _ _ _ = ?f _ _ _ _) =>
       has_option (Inj3 (=) (=) (=) (=) (=) f);
       simple apply (f_equal4 f) : inj.


(** * ObvFalse

This is a typeclass to gather fact that are obviously false. If you have a
theory specific way of deriving false, add it to this typeclass *)
Class ObvFalse (P : Prop) := {obv_false : P → False}.
Global Hint Mode ObvFalse + : typeclass_instances.

Global Instance obv_false_False : ObvFalse False.
Proof. by tcclean. Qed.

Global Instance obv_false_neq A (x : A) : ObvFalse (x ≠ x).
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

(** If [CDestrMatchNoEq] is enabled for a type, then whenever CDestruct destroy
    the discriminee of a match with it, it does not generate the corresponding
    equality *)
Class CDestrMatchNoEq (T : Type) := {}.


(** [CDestrRecInj] allow [cdestruct] to blow up record equalities of the form
    [{| ... |} = {| ... |}] in a group of field-wise equality. One must specify
    the constructor term for internal reasons (it's hard to guess). The record
    must implement [Settable] *)
Class CDestrRecInj (rec_type : Type) {constr_type : Type}
  (constr : constr_type) := {}.

Ltac2 subst_constr x := let x := get_var_bt x in Std.subst [x].

Ltac2 cdestruct_step () :=
  match! goal with
  | [|- ∀ _ : ?t, _] =>
      let h := intro_get_name () in
      assert_option (CDestrCase $t);
      Std.case false (Control.hyp h, Std.NoBindings);
      clear $h
  | [|- ∀ _, _] =>
      let h := intro_get_name () in
      apply obv_false in $h;
      Std.case false (Control.hyp h, Std.NoBindings)
  | [|- ∀ _, _] =>
      let h := intro_get_name () in
      apply (iffLR cdestruct_simpl) in $h;
      revert $h
  | [|- ?t = ?t → _ ] => intros _
  | [|- ∀ _ : ?t = ?t, _ ] => refine '(simplification_K _ $t _ _)
  | [|- ∀ _ : ?x = ?y, _ ] =>
      assert_option CDestrSubst;
      let h := intro_get_name () in
      first [subst_constr x | subst_constr y]
  | [|- ∀ _ : _, _ ] =>
      let h := intro_get_name () in
      progress (cbn in $h);
      revert $h
  | [|- ∀ _, _ ] =>
      assert_option CDestrSubst;
      let h := intro_get_name () in
      let p := Control.hyp h in
      let e := pose_proof_get constr:(cdestr_supersubst $p) in
      lazy_match! Constr.type (Control.hyp e) with
      | ?x = ?y => first [subst_constr x | subst_constr y]
      end;
      revert $h
  | [|- ∀ _ : ?p, _ ] =>
      lazy_match! p with
      | context [match inspect ?b with _ => _ end] =>
          let t := Constr.type b in
          assert_option (CDestrMatchT $t);
          Std.case false ('(inspect $b), Std.NoBindings);
          let hb := intro_get_name () in
          Std.case false (Control.hyp hb, Std.NoBindings);
          clear $hb
      | context [match ?b with _ => _ end] =>
          let t := Constr.type b in
          assert_option (CDestrMatchT $t);
          match get_var b with
          | Some x => Std.case false (b, Std.NoBindings); clear $x
          | None =>
              if has_option (CDestrMatchNoEq $t)
              then Std.case false (b, Std.NoBindings)
              else
                ltac1:(b |- case_eq b) (Ltac1.of_constr b)
          end
      end
  | [|- ∀ _, _] => intro
  end.

Ltac2 cdestruct_intros0 () := repeat (once (cdestruct_step ())).
Ltac2 Notation cdestruct_intros := cdestruct_intros0 ().

Ltac2 Notation "cdestruct_intros" "as" ip(intropatterns) :=
  revert_generated_hyps cdestruct_intros0; Std.intros false ip.

Ltac2 cdestruct_intro0 () :=
  Control.enter
    (fun () =>
       let h := intro_get_name () in
       block_goal;
       revert $h;
       cdestruct_intros;
       unblock_goal).
Ltac2 Notation cdestruct_intro := cdestruct_intro0 ().

Ltac2 cdestruct0 h :=
  block_goal;
  revert $h;
  cdestruct_intros;
  unblock_goal.
Ltac2 Notation "cdestruct" h(ident) := cdestruct0 h.

Tactic Notation "cdestruct_intros" := ltac2:(cdestruct_intros).
Tactic Notation "cdestruct_intros" "as" simple_intropattern_list(pats) :=
  ltac2:(revert_generated_hyps cdestruct_intros0); intros pats.
Tactic Notation "cdestruct_intro" := ltac2:(cdestruct_intro).
Tactic Notation "cdestruct_intro" "as" simple_intropattern_list(pats) :=
  ltac2:(revert_generated_hyps cdestruct_intro0); intros pats.
Ltac cdestruct0 := ltac2:(h |- cdestruct0 (Option.get (Ltac1.to_ident h))).
Tactic Notation "cdestruct" hyp(h) := cdestruct0 h.
Tactic Notation "cdestruct" hyp(h) "as" simple_intropattern_list(pats) :=
  revert_generated_hyps ltac:(cdestruct0 h); intros pats.


(** ** Default Instanciation of the CDestruct typeclasses *)

(** CDestruct destroys [∧], [∃], pairs, [True], [False],[unit] and [Empty_set]
    by default. It purposefully does NOT destroy [∨] by default. This behavior
    can be added locally with [#[local] Existing Instance cdestruct_or] or with
    [cdestruct use cdestruct_or] *)
Global Instance cdestruct_and A B : CDestrCase (A ∧ B) := ltac:(constructor).
#[global] Instance cdestruct_ex T P : CDestrCase (∃ x : T, P x) := ltac:(constructor).
Definition cdestruct_sigT T (F : T → Type) : CDestrCase (sigT F) := ltac:(constructor).
#[global] Instance cdestruct_pair (A B : Type) : CDestrCase (A * B) :=
  ltac:(constructor).
Global Instance cdestruct_True : CDestrCase True := ltac:(constructor).
Global Instance cdestruct_False : CDestrCase False := ltac:(constructor).
Definition cdestruct_or A B : CDestrCase (A ∨ B) := ltac:(constructor).
Definition cdestruct_sum A B : CDestrCase (A + B) := ltac:(constructor).
#[global] Instance cdestruct_unit : CDestrCase unit := ltac:(constructor).
#[global] Instance cdestruct_Empty_set : CDestrCase Empty_set := ltac:(constructor).

#[global] Instance cdestruct_match_noeq_sig A (P : A → Prop)
  : CDestrMatchNoEq (sig P)  := ltac:(constructor).
#[global] Instance cdestruct_match_noeq_sumbool P Q
  : CDestrMatchNoEq ({P} + {Q})  := ltac:(constructor).

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

(** CTrans simplification *)
#[global] Instance cdestruct_ctrans_inj `{CTransSimpl T F} {n m : T} (e e' : n = m)
  (a b : F n):
  CDestrSimpl (ctrans e a = ctrans e' b) (a = b).
Proof. constructor. by simp ctrans. Qed.

#[global] Instance cdestruct_ctrans_simpl_l `{CTransSimpl T F} {n : T} (e : n = n)
  (a b : F n):
  CDestrSimpl (ctrans e a = b) (a = b).
Proof. constructor. by simp ctrans. Qed.

#[global] Instance cdestruct_ctrans_simpl_r `{CTransSimpl T F} {n : T} (e : n = n)
  (a b : F n):
  CDestrSimpl (a = ctrans e b) (a = b).
Proof. constructor. by simp ctrans. Qed.

Hint Extern 5 (CDestrSuperSubst ?P _ _ _) =>
       let TP := type of P in
       match P with
       | context [@ctrans _ _ _ ?A ?B ?E _] =>
           assert_fails (unify A B);
           constructor;
           intro;
           exact E
       end : typeclass_instances.
(* (* TODO improve to any ctrans in the context, and not just left or right of equality *) *)
(* #[global] Instance cdestr_supersubst_ctrans_l `{CTransSimpl T F} *)
(*   `{Unconvertible T n n} (e : n = n) (a : F n) b : *)
(*   CDestrSuperSubst (ctrans e a = b) T n n. *)
(* Proof. *)
(*   Set Typeclasses Debug. *)
(*   tc_solve. *)
(*   by tcclean. Qed. *)

(* #[global] Instance cdestr_supersubst_ctrans_r `{CTransSimpl T F} *)
(*   `{Unconvertible T n m} (e : n = m) (a : F n) b : *)
(*   CDestrSuperSubst (b = ctrans e a) T n m. *)
(* Proof. by tcclean. Qed. *)

(** JMeq simplification *)
Global Instance cdestruct_JMeq A (x y : A) :
  CDestrSimpl (x =ⱼ y) (x = y).
Proof. constructor. use JMeq_eq. naive_solver. Qed.

Global Instance cdestruct_neg_JMeq A (x y : A) :
  CDestrSimpl (x ≠ⱼ y) (x ≠ y).
Proof. constructor. use JMeq_eq. naive_solver. Qed.


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
