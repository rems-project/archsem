(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  All files except SailArmInstTypes.v are distributed under the             *)
(*  license below (BSD-2-Clause). The former is distributed                   *)
(*  under a mix of BSD-2-Clause and BSD-3-Clause Clear, as described          *)
(*  in the file header.                                                       *)
(*                                                                            *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

Require Import Options.
Require Import CBase.
(* TODO Use Equations for dependent equalities management ? *)
Require Import Program.Equality.

(** CDestruct is context cleaner/clarifier.

    It will process a set of hypotheses (both in the context and goal), as well
    as possibly the goal. The current syntax is:
    - [cdestruct h,h2]: processes [h] and [h2] and any context hypotheses that
      depend on them (i.e. [generalize dependent])
    - [cdestruct |- ??]: Processes the first 2 hypotheses in the goal [A → B → G]
    - [cdestruct |- **]: Processes all the hypotheses in the goal, but not the goal
      For example if goal is [A → G] (and [G] is not a product), then this
      processes only [A]
    - [cdestruct |- ***]: Processes all the hypotheses in the goal and the goal
      itself.
    - Combinations like [cdestruct h,h2 |- **] also work.
    - [cdestruct ... as intro_pattern] can be used to name the generated
      hypotheses. If less names than needed are provided, the corresponding
      hypotheses are left in the goal. [cdestruct ... as] will leave everything
      in the goal.

    The goal of [cdestruct] is to perform a set of user-specified
    simplification/clarification rules without backtracking to bring the goal in
    a cleaner state, or discharge the goal if it is trivial after those
    simplifications.

    [cdestruct] should not introduce evars and tries to not fill any either.
    However it is relatively easy to add hints that would do either and there is
    currently no check for that, but it could break the safeness properties

    On each specified hypotheses, [cdestruct] will perform the following:
    - Split all types specified by [CDestrCase]. By default:
      - pairs, [∧], [∃], [False], [True]
      - If [CDestrSplitGoal] is specified: [∨], [+], ...
    - Simplify with [cbn] (Always on, can't be disabled for now)
    - discharge if an hypothesis is trivially false:
      - discriminate and contradiction
      - [x ≠ x]
    - Clean up [t = t]
    - Apply all rewritings in [CDestrSimpl false], by default:
      - Simplifying obviously false as defined [ObvFalse] into [False], by default:
        - contradicting hypotheses ([contradiction])
        - different constructor equalities ([discriminate])
        - [x ≠ x]
      - Injectivity of constructors (with less that 4 different parameters)
      - Injectivity of record constructor when enabled with [CDestrRecInj]
      - Boolean tautologies: [¬¬P] to [P], and some De Morgan laws
      - equalities with [bool_decide]
      - Simplifying [ctrans] calls when possible.
    - If an hypothesis implies an equality that is substituable, (as defined by
      CDestrSubst), then do the substitution. By default:
      - A plain variable equality [x = expr] or [expr = y]
      - [existsT T x = existsT T' x'] if either T or T' is a variable
      - The same with constructor nesting:
        [existsT (existT T x) y = existT (existT T' x') y'),
        if either T or T' is a variable.
      - Also by default with other constructors than [existT]
      - [ctrans e f] anywhere if [e] has a variable on either side
    - If a there is a match of a type (or [inspect] of a type), and the type is
      in [CDestrMatchT], then destruct the discriminee (and keep the equality if
      not a variable)

    Then on the goal [cdestruct] will perform the following:
    - Split all types specified by [CDestrSplit]. By default:
      - [True]
      - If [CDestrSplitGoal] is specified: [∧], [↔]. ...
    - Discharge if the goal is obviously true ([ObvTrue]). By default:
      - [reflexivity], [assumption], [eassumption].
    - Perform all rewriting given by [CDestrSimpl true] it's possible to have
      different rewriting than in an hypothesis context
    - Try [CDestrGoalSuperSubst] substitution that come from the goal's type,
      mostly things like try substitution on [e] when [ctrans e f] is in the goal.
    - Break match cases in the same way as in the hypotheses.


    In addition we have a few immediate improvement plans:
    - Do not reintroduce the same hypothesis twice
    - This would allow to have some basic system of fact saturation
    - Potentially the substitution system could be replaced by saturating with
      the extracted equality
    - Need to think how to do saturation from the goal without doing the same
      things multiple times (e.g. extract [e] from a goal containing [ctrans e f])

    Longer term we probably also need to improve the simplification system for
    performance, and make typeclass resolution faster/simpler in general.
*)


(** * Injectivity

    This is a is done with a bunch of injectivity typeclasses, that can be used
    elsewhere. This enforce that any injection done by [cdestruct] respects
    typeclass opaqueness (unlike the regular [injection]) *)

(** Deduce Inj instance from dependent injection. *)
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
       has_option (Inj4 (=) (=) (=) (=) (=) f);
       simple apply (f_equal4 f) : inj.


(** * ObvFalse

This typeclass gathers facts that are obviously false. If you have a
theory specific way of deriving false, you can add it to this typeclass.
[cdestruct] will then use this to simplify those fact into [False]
(and discharge the goal if those are in the context) *)
#[local] Set Typeclasses Strict Resolution.
Class ObvFalse (P : Prop) := {obv_false : P → False}.
#[local] Unset Typeclasses Strict Resolution.

Global Instance obv_false_False : ObvFalse False.
Proof. by tcclean. Qed.

Global Instance obv_false_neq A (x : A) : ObvFalse (x ≠ x).
Proof. by tcclean. Qed.

Global Hint Extern 8 (ObvFalse _) =>
  let H := fresh "H" in
  constructor; intro H; (contradiction H || discriminate H) : typeclass_instances.

(** ** Incompatible

This typeclass flags mutually exclusive properties of an object, like
discriminate but for non inductives. If there are n incompatible statements this
setup still requires [n(n-1)/2] Instances. TODO improve that *)
Class Incompatible (P : Prop) (Q : Prop) := {incompatible : P → Q → False}.
#[global] Hint Mode Incompatible + - : typeclass_instances.
#[global] Hint Mode Incompatible - + : typeclass_instances.

#[global] Instance obv_false_incompatible_l `{Incompatible P Q} :
  TCFastDone P → ObvFalse Q.
Proof. deintro. tcclean. naive_solver. Qed.

#[global] Instance obv_false_incompatible_r `{Incompatible P Q} :
  TCFastDone Q → ObvFalse P.
Proof. deintro. tcclean. naive_solver. Qed.

(** * ObvTrue

This typeclass gathers fact that are obviously true, this allows to solve the
goal quickly if possible, try to limit the search time though.
[fast_done] is and example of what it expected to be solved by this typeclass.*)

#[local] Set Typeclasses Strict Resolution.
Class ObvTrue (P : Prop) := {obv_true : P}.
#[local] Unset Typeclasses Strict Resolution.

(* Global Instance obv_false_False : ObvFalse False. *)
(* Proof. by tcclean. Qed. *)

Global Hint Extern 2 (ObvTrue _) =>
         constructor; reflexivity : typeclass_instances.

Global Hint Extern 3 (ObvTrue _) =>
         constructor; assumption : typeclass_instances.

Global Hint Extern 4 (ObvTrue _) =>
         constructor; symmetry; assumption : typeclass_instances.

(** * CDestruct

See the top of the file comment for details about what [cdestruct] does. *)

(** ** CDestruct options *)

(** If [CDestrCase] is enabled for a type, then [cdestruct] will destruct
    that type when it sees it in an hypothesis *)
#[local] Set Typeclasses Strict Resolution.
Class CDestrCase (T : Type) := {}.
#[local] Unset Typeclasses Strict Resolution.

(** If [CDestrSplit] is enabled for a type, then [cdestruct] will split that
    type when it sees it in the goal *)
#[local] Set Typeclasses Strict Resolution.
Class CDestrSplit (T : Type) := {}.
#[local] Unset Typeclasses Strict Resolution.

(** [cdestruct] will apply all simplification provided by [CDestrSimpl]
    If is provided by [CDestrSimpl false] it will be an hypothesis
    simplification, otherwise it will be a goal simplification. *)
Class CDestrSimpl (goal : bool) (P Q : Prop) := cdestr_simpl {cdestruct_simpl : P ↔ Q}.
Global Hint Mode CDestrSimpl + ! - : typeclass_instances.
Arguments cdestr_simpl _ {_ _} _.
Arguments cdestruct_simpl _ _ {_ _}.
(** Useful for [blocked_evar] resolution in [block_all_evars] *)
Ltac get_cdestr_simpl_evars _ :=
  lazymatch goal with
  | |- CDestrSimpl _ ?G _ => G
  end.


(** [CDestrSubst] try to extract a variable substitution from a given
    proposition [P] that cannot be directly simplified. [CDestrSimpl] is tried
    before [CDestrSubst]. The output proposition [Q] must have the form
    [x = expr] or [expr = y] where [x] or [y] respectively is a variable.
    Otherwise the instance found is rejected (and [cdestruct] wastes time).

    One simple case is if [P] itself is [x = expr] with x a variable. However
    more subtle cases are possible such as
    [P = (existT x expr1 = existT expr2 expr3)]

    There is a [Hint Extern] below that tries to find the simple case of that
    pattern generically *)
Class CDestrSubst (P : Prop) (Q : Prop) :=
  cdestr_subst {cdestruct_subst : P → Q}.
Global Hint Mode CDestrSubst ! - : typeclass_instances.
Arguments cdestr_subst {_ _} _.
Arguments cdestruct_subst _ {_ _}.
Ltac get_cdestr_subst_evars _ :=
  lazymatch goal with
  | |- CDestrSubst ?G _ => G
  end.

(** This is the goal version of the previous to extract equalities from the goal
    that could be used for substitution, like [e] in a goal containing
    [ctrans e x] *)
Class CDestrSubstGoal (P : Prop) (Q : Prop) :=
  cdestr_subst_goal {cdestruct_subst_goal : Q}.
Global Hint Mode CDestrSubstGoal ! - : typeclass_instances.
Arguments cdestr_subst_goal {_ _} _.
Arguments cdestruct_subst_goal _ {_ _}.
Ltac get_cdestr_subst_goal_evars _ :=
  lazymatch goal with
  | |- CDestrSubstGoal ?G _ => G
  end.



(** If [CDestrMatchT] is enabled for a type, then [cdestruct] will process match
    cases of that type by calling [destruct] on the match discriminee. The value
    will therefore be destructed even if not directly processed by [cdestruct] *)
#[local] Set Typeclasses Strict Resolution.
Class CDestrMatchT (T : Type) := {}.
#[local] Unset Typeclasses Strict Resolution.

(** [CDestrMatch] is [CDestrMatch T] for all [T] *)
Class CDestrMatch := {}.
Global Instance cdestr_matchT `{CDestrMatch} T : CDestrMatchT T. Qed.

(** If [CDestrMatchNoEq] is enabled for a type, then whenever CDestruct destroy
    the discriminee of a match with that type, it does not generate the
    corresponding equality, this is intended for types like [{P} + {Q}] *)
#[local] Set Typeclasses Strict Resolution.
Class CDestrMatchNoEq (T : Type) := {}.
#[local] Unset Typeclasses Strict Resolution.

(** [CDestrRecInj] allow [cdestruct] to blow up record equalities of the form
    [{| ... |} = {| ... |}] in a group of field-wise equality. One must specify
    the constructor term for internal reasons (it's hard to guess). The record
    must implement [Settable] *)
#[local] Set Typeclasses Strict Resolution.
Class CDestrRecInj (rec_type : Type) {constr_type : Type}
  (constr : constr_type) := {}.
#[local] Unset Typeclasses Strict Resolution.

(** Directed rewriting. Declares that if A = B, then rewriting A to B is a good
    idea, This is not used by default as it is quite fragile, probably best use
    only as a local hint.

    This is really fragile and might be deleted, use with care *)
#[local] Set Typeclasses Strict Resolution.
Class CDestrDRew {T} (A : T) (B : T) := {}.
#[local] Unset Typeclasses Strict Resolution.


(** ** CDestruct helper tactics *)

(** *** Breaking up match cases *)

(** Breaks any match case found in [p] according to the typeclass options *)
Ltac2 break_match_in p :=
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
      if has_option (CDestrMatchNoEq $t)
      then Std.case false (b, Std.NoBindings)
      else
        ltac1:(b |- case_eq b) (Ltac1.of_constr b)
  end.

(** *** Substitution *)

(** If the provided constr is a variable, calls subst on it, otherwise
    backtracks *)
Ltac2 subst_constr x := let x := get_var_bt x in Std.subst [x].

(** [subst_clean h x] substitute [x] using equality [h] after reverting all
    hypotheses using [x], This insured that all hypotheses modified by the
    substitution are back in the goal *)
Ltac2 subst_clean h x :=
  move $h before $x;
  revert dependent $x;
  intros $x $h;
  Std.subst [x].

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

Ltac2 clean_up_eq h x y :=
  match get_var x, get_var y with
  | Some x, Some y =>
      (* If it's a variable equality, subst the lowest context variable *)
      if hyp_before x y
      then (assert_bt (can_subst y); subst_clean h y)
      else (assert_bt (can_subst x); subst_clean h x)
  | Some x, None => assert_bt (can_subst x); subst_clean h x
  | None, Some y => assert_bt (can_subst y); subst_clean h y
  | None, None => Control.zero Match_failure
  end.

(** *** Blocking *)

(** We need an actually opaque block, so we make a new one *)
Definition cblock {A : Type} (a : A) := a.
Opaque cblock.

Ltac2 cblock_goal0 () := lazy_match! goal with [ |- ?t ] => change (cblock $t) end.
Ltac2 Notation cblock_goal := cblock_goal0 ().
Ltac2 uncblock_goal0 () := cbv [cblock].
Ltac2 Notation uncblock_goal := uncblock_goal0 ().

(** [cdestruct_step] can block an hypothesis if need to be simplified, but it is
    used in a dependent manner (e.g. in a transport call). In this case the
    hypotheses would be duplicated and the original is blocked. At the end,
    blocked hypotheses must thus be cleared if they are not longer needed, or
    otherwise unblocked *)
Ltac2 clear_or_uncblock h :=
  clear $h ||ₜ cbv [cblock] in $h.
Ltac2 clear_or_uncblock_hyp () :=
  match! goal with
  | [h : cblock _ |- _] => clear_or_uncblock h
  end.
Ltac2 clear_or_uncblock_hyps () := repeat (clear_or_uncblock_hyp ()).


(** ** CDestruct Step

[cdestruct] works by repeating one single simplification step until it doesn't
work (or doesn't make progress) Therefore there is no transmission of
information between the steps, except what is in the goal and what is in the
context. The general idea being that hypotheses to be processes are in the goal,
and hypotheses already processed are in the context. *)

(** Core [cdestruct] engine: One single step *)
Ltac2 cdestruct_step0 () :=
  match! goal with
  | [|- ∀ _ : ?t, _] => (* Case splitting *)
      assert_option (CDestrCase $t);
      let h := intro_get_name () in
      Std.case false (Control.hyp h, Std.NoBindings);
      clear $h
  (* | [|- ∀ _, _] => (* Obviously false *) *)
  (*     let h := intro_get_name () in *)
  (*     apply obv_false in $h; *)
  (*     Std.case false (Control.hyp h, Std.NoBindings) *)
  | [|- ?t = ?t → _ ] => intros _ (* Reflexive equality cleanup *)
  | [|- ∀ _ : ?t = ?t, _ ] => refine '(simplification_K _ $t _ _)
  | [|- ∀ _ : _, _ ] => (* Cbn *)
      let h := intro_get_name () in
      progress (cbn in $h);
      revert $h
  | [|- ∀ _ : ?p, _] => (* Rewriting *)
      let r := '(@cdestruct_simpl false $p _
                   ltac:(block_all_evars get_cdestr_simpl_evars; tc_solve)) in
      let r := eval cbv[blocked_evar] in $r in
      let h := intro_get_name () in
      orelse
      (fun () => apply (iffLR $r) in $h; revert $h)
      (fun _ =>
         (* If the hypotheses can't be modified (used somewhere else),
            we make a copy and block the original, cdestruct removes all
            blocks at the end (and clears unused block hypotheses)*)
         let h' := pose_proof_get (Control.hyp h) in
         apply (iffLR $r) in $h';
         revert $h';
         change (cblock $p) in $h;
         revert $h)
  | [|- ∀ _ : ?p, _ ] => (* Substitution *)
      let cds := '(@cdestruct_subst $p _
                     ltac:(block_all_evars get_cdestr_subst_evars; tc_solve)) in
      let cds := eval cbv[blocked_evar] in $cds in
      let h := intro_get_name () in
      let prf := Control.hyp h in
      let e := pose_proof_get '($cds $prf) in
      cbn in $e;
      lazy_match! Constr.type (Control.hyp e) with
      | ?x = ?y => clean_up_eq e x y
      end;
      try (revert $h)
  | [|- ∀ _ : ?x = ?y, _ ] => (* Directed rewrite *)
      (* TODO This is bad, it needs to backtrack on previous hypotheses too *)
      assert_option (CDestrDRew $x $y);
      let h := intro_get_name () in
      let t := Control.hyp h in
      progress (setoid_rewrite $t);
      revert $h
  | [|- ∀ _ : ?p, _ ] => (* Match splitting *) break_match_in p

  (* If there is nothing to do, introduce the hypothesis, this commits it as
     being "processed" and we won't go back to it (unless modified) *)
  | [|- ∀ _, _] => intro

  (* If the goal is blocked, we don't do goal clean-up *)
  | [|- cblock _] => () (* stop on block: (cdestruct_step) is wrapped in progress*)

  (* Goal clean-up *)
  | [|- ?t ] => assert_option (CDestrSplit $t); split
  | [|- _] => apply obv_true
  | [|- _] => progress cbn
  | [|- ?p] => (* Goal simplification *)
      let r := '(@cdestruct_simpl true $p _
                   ltac:(block_all_evars get_cdestr_simpl_evars; tc_solve)) in
      let r := eval cbv[blocked_evar] in $r in
      apply (iffRL $r)
  | [|- ?p] => (* Goal substitution *)
      let e :=
        pose_proof_get
          '(@cdestruct_subst_goal $p _
              ltac:(block_all_evars get_cdestr_subst_goal_evars; tc_solve)) in
      unblock_evars;
      cbn in $e;
      lazy_match! Constr.type (Control.hyp e) with
      | ?x = ?y => clean_up_eq e x y
      end
  | [|- ?p] => (* Goal match splitting *) break_match_in p
  end.

Ltac2 Notation cdestruct_step := cdestruct_step0 ().
Ltac cdestruct_step := ltac2:(cdestruct_step).

(** ** CDestruct top-level setup and syntax

The core of cdestruct is just [cdestruct_steps = repeat cdestruct_step],
however we also want to do some pre and post processing, to give a nice UX.

First we delimit the range of hypotheses (and maybe goal) that we need to process:
- We need to revert all hypotheses to process
- We need to block the part of the goal we do not want to process
- We add a marker ([hyp_block]) to mark the set hypotheses we can change,
  anything above should be left untouched
*)

(** Repeat a single cdestruct step *)
Ltac2 Notation cdestruct_steps := repeat (once cdestruct_step).
Ltac cdestruct_steps := ltac2:(cdestruct_steps).

(** *** Preprocessing tactics *)

(** Remove the [hyp_block] or fails otherwise *)
Ltac2 clear_hyp_block0 () :=
  Control.enter
    (fun () =>
       match get_hyp_id pat:(hyp_block) with
       | Some h => Std.clear [h]
       | None => throw_tacticf "clear_hyp_block: HypBlock not found"
    end).
Ltac2 Notation clear_hyp_block := clear_hyp_block0 ().

(** Generic cdestruct tactic with goal, hyp and post (clean) processing *)
Ltac2 cdestruct_gen0 goaltac hyptac cleantac :=
  pose proof HypBlock;
  goaltac ();
  hyptac ();
  cdestruct_steps;
  Control.enter (fun () => cleantac (); uncblock_goal; clear_or_uncblock_hyps ()).
Ltac2 Notation cdestruct_gen := cdestruct_gen0.

(** Does intro with a ltac1 pattern *)
Ltac2 ltac1_intros (pats : Ltac1.t) := ltac1:(pats |- intros pats) pats.

(** Preprocess for the [|- intro_pattern] syntax *)
Ltac2 cdest_intro_start ipats :=
  ltac1_intros ipats; cblock_goal; revert until hyp_block.

(** Preprocess for the [|- **] syntax *)
Ltac2 cdest_intros_start0 () :=
  intros; cblock_goal; revert until hyp_block.
Ltac2 Notation cdest_intros_start := cdest_intros_start0 ().

(** Preprocesse the list of hypotheses of cdestruct *)
Ltac2 cdest_rev_start (l : Ltac1.t) :=
  revert_dependent (ltac1_to_list ltac1_to_ident l).

(** Postprocess the "as ..." part of cdestruct syntax *)
Ltac2 cdest_as_end pats :=
  revert until* hyp_block; ltac1_intros pats.

Tactic Notation "cdestruct" hyp_list_sep(hs, ",") :=
  let f := ltac2:(hs |- cdestruct_gen cblock_goal
                          (cdest_rev_start hs) clear_hyp_block)
  in f hs.
Tactic Notation "cdestruct" hyp_list_sep(hs, ",")
                "as" simple_intropattern_list(pats) :=
  let f := ltac2:(hs pats |- cdestruct_gen cblock_goal
                               (cdest_rev_start hs) (cdest_as_end pats))
  in f hs pats.

Tactic Notation "cdestruct" hyp_list_sep(hs, ",")
                "|-" simple_intropattern_list(ipats) :=
  let f := ltac2:(hs ipats |- cdestruct_gen (cdest_intro_start ipats)
                          (cdest_rev_start hs) clear_hyp_block)
  in f hs ipats.
Tactic Notation "cdestruct" hyp_list_sep(hs, ",")
                "|-" simple_intropattern_list(ipats)
                "as" simple_intropattern_list(pats) :=
  let f := ltac2:(hs ipats pats |- cdestruct_gen (cdest_intro_start ipats)
                               (cdest_rev_start hs) (cdest_as_end pats))
  in f hs ipats pats.

(* Do we need cdestruct |- *, that would do only dependent products ? Probably not *)

Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" "**" :=
  let f := ltac2:(hs |- cdestruct_gen cdest_intros_start
                          (cdest_rev_start hs) clear_hyp_block)
  in f hs.
Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" "**"
                "as" simple_intropattern_list(pats) :=
  let f := ltac2:(hs pats |- cdestruct_gen cdest_intros_start
                               (cdest_rev_start hs) (cdest_as_end pats))
  in f hs pats.

Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" "***" :=
  let f := ltac2:(hs |- cdestruct_gen ()
                          (cdest_rev_start hs) clear_hyp_block)
  in f hs.
Tactic Notation "cdestruct" hyp_list_sep(hs, ",") "|-" "***"
                "as" simple_intropattern_list(pats) :=
  let f := ltac2:(hs pats |- cdestruct_gen ()
                               (cdest_rev_start hs) (cdest_as_end pats))
  in f hs pats.



(** * Default Instanciation of the CDestruct typeclass options *)

(** ** Inductive case splitting *)

(** Enable default rules that can split a goal, like case splitting [∨] or goal
    splitting [∧] *)
Class CDestrSplitGoal := {}.

(** CDestruct destroys [∧], [∃], pairs, [True], [False],[unit] and [Empty_set]
    by default. It purposefully does NOT destroy [∨] and [+] by default. This
    behaviour can be added locally with [CDestrSplitGoal] *)
#[global] Instance cdestruct_and A B : CDestrCase (A ∧ B) := ltac:(constructor).
#[global] Instance cdestruct_ex T P : CDestrCase (∃ x : T, P x) := ltac:(constructor).
#[global] Instance cdestruct_sigT T (F : T → Type) :
  CDestrCase (sigT F) := ltac:(constructor).
#[global] Instance cdestruct_pair (A B : Type) :
  CDestrCase (A * B) := ltac:(constructor).
#[global] Instance cdestruct_True : CDestrCase True := ltac:(constructor).
#[global] Instance cdestruct_False : CDestrCase False := ltac:(constructor).
#[global] Instance cdestruct_or `{CDestrSplitGoal} A B :
  CDestrCase (A ∨ B) := ltac:(constructor).
#[global] Instance cdestruct_sum `{CDestrSplitGoal} A B :
  CDestrCase (A + B) := ltac:(constructor).
#[global] Instance cdestruct_unit : CDestrCase () := ltac:(constructor).
#[global] Instance cdestruct_Empty_set : CDestrCase Empty_set := ltac:(constructor).

(** CDestruct can split goals if enabled by [CDestrSplitGoal] *)
#[global] Instance cdestr_split_and `{CDestrSplitGoal}
  A B : CDestrSplit (A ∧ B) := ltac:(constructor).
#[global] Instance cdestr_split_iff `{CDestrSplitGoal}
  A B : CDestrSplit (A ↔ B) := ltac:(constructor).
#[global] Instance cdestr_split_True : CDestrSplit True := ltac:(constructor).
#[global] Instance cdestr_split_unit : CDestrSplit () := ltac:(constructor).

(** ** Match case splitting *)

(** For some case spliting on match cases, we not want to keep the equalities *)
#[global] Instance cdestruct_match_noeq_sig A (P : A → Prop)
  : CDestrMatchNoEq (sig P)  := ltac:(constructor).
#[global] Instance cdestruct_match_noeq_sumbool P Q
  : CDestrMatchNoEq ({P} + {Q})  := ltac:(constructor).

(** ** ObvFalse simplification *)

(** Obviously False equality are simplified to False

    TODO: with contradiction in ObvFalse this might be weird *)
Global Instance cdestruct_obvFalse b (P : Prop) `{ObvFalse P} :
  CDestrSimpl b (P : Prop) False.
Proof. constructor. by destruct H. Qed.

(** ** Injectivity *)
(** Injective equalities are simplified by default, up to 4 arguments, both in
the hypotheses and the goal *)
Global Instance cdestruct_inj b `{Inj A B RA RB f} {HP: Proper (RA ==> RB) f} x y :
  CDestrSimpl b (RB (f x) (f y)) (RA x y).
Proof. constructor. apply (inj_iff f). Qed.

Global Instance cdestruct_inj2 b `{Inj2 A B C RA RB RC f}
  `{!Proper (RA ==> RB ==> RC) f} x1 x2 y1 y2 :
  CDestrSimpl b (RC (f x1 x2) (f y1 y2)) (RA x1 y1 ∧ RB x2 y2).
Proof. constructor. apply (inj2_iff f). Qed.

Global Instance cdestruct_inj3 b `{Inj3 A B C D R1 R2 R3 RS f}
    {HP : Proper (R1 ==> R2 ==> R3 ==> RS) f} x1 x2 x3 y1 y2 y3 :
  CDestrSimpl b (RS (f x1 x2 x3) (f y1 y2 y3)) (R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3).
Proof. constructor. apply (inj3_iff f). Qed.

Global Instance cdestruct_inj4 b `{Inj4 A B C D E R1 R2 R3 R4 RS f}
    {HP : Proper (R1 ==> R2 ==> R3 ==> R4 ==> RS) f} x1 x2 x3 x4 y1 y2 y3 y4 :
  CDestrSimpl b (RS (f x1 x2 x3 x4) (f y1 y2 y3 y4))
    (R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3 ∧ R4 x4 y4).
Proof. constructor. apply (inj4_iff f). Qed.

(** Implementation of [CDestrRecInj] for record injectivity, see that typeclass
    definition for an explanation *)
#[global] Hint Extern 30 (CDestrSimpl _ (?L =@{?T} ?R) ?Q) =>
  let L_head := get_head L in
  let R_head := get_head R in
  has_option (CDestrRecInj T L_head);
  unify L_head R_head;
  constructor;
  rewrite record_eq_unfold;
  cbn;
  reflexivity : typeclass_instances.

(** ** Substitution *)

#[global] Hint Extern 10 (CDestrSubst (?x = ?y) _) =>
  (first [is_var x | is_var y]; assert_fails (unify x y); econstructor; let H := fresh "H" in intro H; exact H)
  : typeclass_instances.

Ltac cds_by_congruence Ht :=
  constructor;
  let Hs := fresh "H" in
  intro Hs;
  class_apply (@cdestruct_subst Ht);[clear Hs| congruence].


(* TODO make a single Hint Extern *)
#[global] Hint Extern 5 (CDestrSubst (?f ?x = ?f ?y) _) =>
  (assert_fails (unify x y);
   cds_by_congruence (x = y)) : typeclass_instances.

#[global] Hint Extern 4 (CDestrSubst (?f ?x _ = ?f ?y _) _) =>
  (assert_fails (unify x y);
   cds_by_congruence (x = y)) : typeclass_instances.

#[global] Hint Extern 3 (CDestrSubst (?f ?x _ _ = ?f ?y _ _) _) =>
  (assert_fails (unify x y);
   cds_by_congruence (x = y)) : typeclass_instances.

#[global] Hint Extern 2 (CDestrSubst (?f ?x _ _ _ = ?f ?y _ _ _)) =>
  (assert_fails (unify x y);
   cds_by_congruence (x = y)) : typeclass_instances.


(** ** CTrans simplification and substitution *)
Hint Extern 5 (CDestrSimpl _ ?P _) =>
       match P with
       | context [ctrans] =>
           constructor;
           progress (simp ctrans);
           reflexivity
       end : typeclass_instances.

Hint Extern 9 (CDestrSubst ?P _) =>
       match P with
       | context [@ctrans _ _ _ ?A ?B ?E _] =>
           assert_fails (unify A B);
           constructor;
           intros _;
           let t := type of E in
           let t' := eval cbn in t in
           class_apply (@cdestruct_subst t');[ | exact E]
           (* exact E *)
       end : typeclass_instances.

Hint Extern 9 (CDestrSubstGoal ?P _) =>
       match P with
       | context [@ctrans _ _ _ ?A ?B ?E _] =>
           assert_fails (unify A B);
           constructor;
           let t := type of E in
           let t' := eval cbn in t in
             class_apply (@cdestruct_subst t');[ | exact E]
       end : typeclass_instances.

(** ** JMeq simplification *)

Global Instance cdestruct_JMeq b A (x y : A) :
  CDestrSimpl b (x =ⱼ y) (x = y).
Proof. constructor. use JMeq_eq. naive_solver. Qed.

Global Instance cdestruct_neg_JMeq b A (x y : A) :
  CDestrSimpl b (x ≠ⱼ y) (x ≠ y).
Proof. constructor. use JMeq_eq. naive_solver. Qed.

(** ** [bool_decide] simplification *)
Instance cdestruct_bool_decide_true b `{Decision P} :
  CDestrSimpl b (bool_decide P = true) P.
Proof. tcclean. apply bool_decide_eq_true. Qed.

Instance cdestruct_bool_decide b `{Decision P} :
  CDestrSimpl b (bool_decide P) P.
Proof. tcclean. apply bool_decide_spec. Qed.

Instance cdestruct_bool_decide_false b `{Decision P} :
  CDestrSimpl b (bool_decide P = false) (¬ P).
Proof. tcclean. apply bool_decide_eq_false. Qed.

(** ** Logical connectives simplification *)

Instance cdestruct_not_not b P :
  CDestrSimpl b (¬ ¬ P) P.
Proof. tcclean. use NNPP. naive_solver. Qed.

(* Don't introduce an ∨ in a goal, better to have to prove False in a context
with P and Q *)
Instance cdestruct_not_and_or_ctxt P Q :
  CDestrSimpl false (¬ (P ∧ Q)) (¬ P ∨ ¬ Q).
Proof. tcclean. tauto. Qed.

Instance cdestruct_not_and_or_goal P Q :
  CDestrSimpl true (¬ P ∨ ¬ Q) (¬ (P ∧ Q)) | 10.
Proof. tcclean. tauto. Qed.

Instance cdestruct_not_or_l_goal P Q :
  CDestrSimpl true (¬ P ∨ Q) (P → Q) | 20.
Proof. tcclean. tauto. Qed.

Instance cdestruct_not_or_r_goal P Q :
  CDestrSimpl true (P ∨ ¬ Q) (Q → P) | 20.
Proof. tcclean. tauto. Qed.

Instance cdestruct_not_or_and b P Q :
  CDestrSimpl b (¬ (P ∨ Q)) (¬ P ∧ ¬ Q).
Proof. tcclean. naive_solver. Qed.

Instance cdestruct_or_False_l b P :
  CDestrSimpl b (False ∨ P) P.
Proof. tcclean. naive_solver. Qed.

Instance cdestruct_or_False_r b P :
  CDestrSimpl b (P ∨ False) P.
Proof. tcclean. naive_solver. Qed.

Instance cdestruct_and_True_l b P :
  CDestrSimpl b (True ∧ P) P.
Proof. tcclean. naive_solver. Qed.

Instance cdestruct_and_True_r b P :
  CDestrSimpl b (P ∧ True) P.
Proof. tcclean. naive_solver. Qed.
