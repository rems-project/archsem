Require Import Options.
Require Import CBase.
Require Import Program.Equality.

(** CDestruct is context cleaner/clarifier.

    It will process a set of hypotheses (both in the context and goal)
    - [cdestruct h,h2]: processes h and h2 and any context hypotheses that
      depend on them
    - [cdestruct |- ??]: Processes the first 2 hypotheses in the goal [A → B → G]
    - [cdestruct |- **]: Processes all the hypotheses in the goal
    - [cdestruct |- ***]: Processes all the hypotheses in the goal and the goal
      itself
    - Combinations like [cdestruct h,h2 |- **] also work.

    On those hypotheses, cdestruct will perform the following:
    - Split all types specified by CDestrCase. By default:
      - pairs, [∧], [∃]
    - cbn
    - discharge if an hypothesis is trivially false:
      - discriminate and contradiction
      - [x ≠ x]
    - Clean up [t = t]
    - If there is an equality with a variable and the variable is part of the
      processed subset, then do the substitution.
    - Apply all rewritings in [CDestrSimpl]
    - If an hypothesis implies an equality that is substituable, (as defined by
      CDestrSuperSubst), then do the substitution. By default:
      - [existsT T x = exists T' x'] if either T or T' is a variable
      - [ctrans e f] anywhere if [e] has a variable on either side
    - If a there is a match of a type (or inspect of a type), and the type is in
      [CDestrMatchT], then destruct the discriminee (and keep the equality if
      not a variable)
*)


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

(** This is used to deal with dependent equality. When having a dependent
    equality implies simpler equalities. [cdestruct] will try to use the simpler
    equality to do substitution and therefore make the dependent equality
    simpler. For example when you have [existT a b = existT c d], one can deduce
    [a = c]. Then if either [a] or [c] is a variable, we can do a substitution
    and simplify the existT equality *)
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
(* TODO not implemented *)
Class CDestrRecInj (rec_type : Type) {constr_type : Type}
  (constr : constr_type) := {}.


(** If the provided constr is a variable, calls subst on it, otherwise
    backtracks *)
Ltac2 subst_constr x := let x := get_var_bt x in Std.subst [x].

(** [subst_clean h x] substitute [x] using equality [h] after reverting all
    hypotheses using [x] *)
Ltac2 subst_clean h x :=
  move $h before $x;
  revert dependent $x;
  intros $x $h;
  subst $x.

(** Decide if [h1] is before [h2] in the current goal *)
Ltac2 hyp_before h1 h2 :=
  Ident.equal h1
    (Control.hyps ()
     |> List.map (fun (h, _, _) => h)
     |> List.find (fun h => Ident.equal h h1 || Ident.equal h h2)).

(** Check if substitution is allowed, which means that the variable to be
    substitued is below HypBlock. *)
Ltac2 can_subst x :=
  match get_hyp_id pat:(hyp_block) with
  | Some hb => hyp_before hb x
  | None => true
  end.

(** Case split on the first context hypothesis *)
Ltac2 case_intro () :=
  let h := intro_get_name () in
  Std.case false (Control.hyp h, Std.NoBindings); clear $h.

(** Core [cdestruct] engine. One single step, see top of module for
    documentation *)
Ltac2 cdestruct_step0 () :=
  let clean_up_eq h x y :=
    match get_var x, get_var y with
    | Some x, Some y =>
        (* If it's a variable equality, subst the lastest variable *)
        if hyp_before x y
        then assert_bt (can_subst y); subst_clean h y
        else assert_bt (can_subst x); subst_clean h x
    | Some x, None => assert_bt (can_subst x); subst_clean h x
    | None, Some y => assert_bt (can_subst y); subst_clean h y
    | None, None => Control.zero Match_failure
    end
  in
  match! goal with
  | [|- ∀ _ : ?t, _] => (* Case splitting *)
      let h := intro_get_name () in
      assert_option (CDestrCase $t);
      Std.case false (Control.hyp h, Std.NoBindings);
      clear $h
  | [|- ∀ _, _] => (* Obviously false *)
      let h := intro_get_name () in
      apply obv_false in $h;
      Std.case false (Control.hyp h, Std.NoBindings)
  | [|- ∀ _, _] => (* Rewriting *)
      let h := intro_get_name () in
      apply (iffLR cdestruct_simpl) in $h;
      revert $h
  | [|- ?t = ?t → _ ] => intros _ (* Reflexive equality cleanup *)
  | [|- ∀ _ : ?t = ?t, _ ] => refine '(simplification_K _ $t _ _)
  | [|- ∀ _ : ?x = ?y, _ ] => (* Substitution *)
      assert_bt (Constr.is_var x || Constr.is_var y);
      let h := intro_get_name () in
      clean_up_eq h x y
  | [|- ∀ _ : _, _ ] => (* Cbn *)
      let h := intro_get_name () in
      progress (cbn in $h);
      revert $h
  | [|- ∀ _, _ ] => (* Supersubst *)
      let h := intro_get_name () in
      let p := Control.hyp h in
      let e := pose_proof_get constr:(cdestr_supersubst $p) in
      cbn in $e;
      lazy_match! Constr.type (Control.hyp e) with
      | ?x = ?y => clean_up_eq e x y
      end;
     try (revert $h)
  | [|- ∀ _ : ?p, _ ] => (* Match splitting *)
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

Ltac2 Notation cdestruct_step := cdestruct_step0 ().
Ltac cdestruct_step := ltac2:(cdestruct_step).

Ltac2 throw_tacticf fmt := Message.Format.kfprintf (fun m => Control.throw (Tactic_failure (Some m))) fmt.
Ltac2 Notation "throw_tacticf" fmt(format) := throw_tacticf fmt.

Ltac2 clear_hyp_block0 () :=
  Control.enter
    (fun () =>
       match get_hyp_id pat:(hyp_block) with
       | Some h => Std.clear [h]
       | None => throw_tacticf "clear_hyp_block: HypBlock not found"
    end).
Ltac2 Notation clear_hyp_block := clear_hyp_block0 ().

(** We need an actually opaque block *)
Definition cblock {A : Type} (a : A) := a.
Opaque cblock.

Ltac2 cblock_goal0 () := lazy_match! goal with [ |- ?t ] => change (cblock $t) end.
Ltac2 Notation cblock_goal := cblock_goal0 ().
Ltac2 uncblock_goal0 () := cbv [cblock].
Ltac2 Notation uncblock_goal := uncblock_goal0 ().

(** Repeat a single cdestruct step *)
Ltac2 Notation cdestruct_steps := repeat (once cdestruct_step).
Ltac cdestruct_steps := ltac2:(cdestruct_steps).

(** Generic cdestruct tactic with pre and post processing *)
Ltac2 cdestruct_gen0 goaltac hyptac cleantac :=
  pose proof HypBlock;
  goaltac ();
  hyptac ();
  cdestruct_steps;
  Control.enter (fun () => cleantac (); uncblock_goal).
Ltac2 Notation cdestruct_gen := cdestruct_gen0.

(** Does intro with a ltac1 pattern (of type Ltac1.t) *)
Ltac2 ltac1_intros pats := ltac1:(pats |- intros pats) pats.

(** Preprocess for the [|- intro pattern] syntax *)
Ltac2 cdest_intro_start ipats :=
  ltac1_intros ipats; cblock_goal; revert until hyp_block.

(** Preprocess for the [|- **] and [|- ***] syntax *)
Ltac2 cdest_intros_start0 () :=
  intros; cblock_goal; revert until hyp_block.
Ltac2 Notation cdest_intros_start := cdest_intros_start0.

(** Preprocesse the list of hypotheses of cdestruct *)
Ltac2 cdest_rev_start l :=
  revert_dependent (ltac1_to_list ltac1_to_ident l).

(** Postprocess the "as ..." part of cdestruct syntax *)
Ltac2 cdest_as_end pats :=
  revert until* hyp_block; ltac1_intros pats.

Tactic Notation "cdestruct" hyp_list_sep(hs, ",") :=
  let f := ltac2:(hs |- cdestruct_gen cblock_goal
                          (cdest_rev_start hs) clear_hyp_block)
  in f hs.
Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "as" simple_intropattern_list(pats) :=
  let f := ltac2:(hs pats |- cdestruct_gen cblock_goal
                               (cdest_rev_start hs) (cdest_as_end pats))
  in f hs pats.

Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" simple_intropattern_list(ipats) :=
  let f := ltac2:(hs ipats |- cdestruct_gen (cdest_intro_start ipats)
                          (cdest_rev_start hs) clear_hyp_block)
  in f hs ipats.
Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" simple_intropattern_list(ipats) "as" simple_intropattern_list(pats) :=
  let f := ltac2:(hs ipats pats |- cdestruct_gen (cdest_intro_start ipats)
                               (cdest_rev_start hs) (cdest_as_end pats))
  in f hs ipats pats.

(* Do we need cdestruct |- * ? *)

Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" "**" :=
  let f := ltac2:(hs |- cdestruct_gen cdest_intros_start
                          (cdest_rev_start hs) clear_hyp_block)
  in f hs.
Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" "**" "as" simple_intropattern_list(pats) :=
  let f := ltac2:(hs pats |- cdestruct_gen cdest_intros_start
                               (cdest_rev_start hs) (cdest_as_end pats))
  in f hs pats.

Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" "***" :=
  let f := ltac2:(hs |- cdestruct_gen ()
                          (cdest_rev_start hs) clear_hyp_block)
  in f hs.
Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" "***" "as" simple_intropattern_list(pats) :=
  let f := ltac2:(hs pats |- cdestruct_gen ()
                               (cdest_rev_start hs) (cdest_as_end pats))
  in f hs pats.



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
Hint Extern 5 (CDestrSimpl ?P _) =>
       match P with
       | context [ctrans] =>
           constructor;
           progress (simp ctrans);
           reflexivity
       end : typeclass_instances.

Hint Extern 5 (CDestrSuperSubst ?P _ _ _) =>
       match P with
       | context [@ctrans _ _ _ ?A ?B ?E _] =>
           assert_fails (unify A B);
           constructor;
           intro;
           exact E
       end : typeclass_instances.

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
