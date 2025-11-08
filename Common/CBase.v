(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
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

Require Export Equations.Prop.Equations.
From Stdlib Require Export Program.Equality Relations.
From Stdlib Require Import ZArith JMeq.

From Ltac2 Require Export Ltac2.
Export Ltac2.Printf.
Export Ltac2.Bool.BoolNotations.
#[export] Set Default Proof Mode "Classic".

From stdpp Require Export base.
From stdpp Require Export numbers.
From stdpp Require Export fin.
From stdpp Require Export tactics.
From stdpp Require Export list.
From stdpp Require Import vector.
From stdpp Require Import decidable.
From stdpp Require Import sets.

From RecordUpdate Require Export RecordSet.
From Hammer Require Export Tactics.

Require Import Options.


(** * Default Typeclass opaque

  By default we make all constants opaque in typeclass resolution (in
  Options.v). This make typeclass search much faster on average, at the cost of
  requiring more instances or transparency annotations. In general for most type
  definitions, one need either to declare it transparent, or define all the
  required typeclasses on it. Same for decidable predicates as this development
  use stdpp's [Decision] *)

(** Some standard library (or stdpp) type abbreviations need to be
    typeclass-transparent: Add them here *)
#[global] Typeclasses Transparent relation.

(** This is needed to fix the behaviour or setoid rewriting under opaque typeclasses *)
Hint Extern 0 (ProperProxy _ _) =>
       simple apply @eq_proper_proxy || simple apply @reflexive_proper_proxy : typeclass_instances.

(** For the decide_rel instance we want to be more lax that the default. If R is
homogenous, we want to unify x y without typeclass opacity because that's what
the type checker does *)
Hint Extern 3 (@Decision (?R ?x ?y)) => simple apply @decide_rel : typeclass_instances.
Remove Hints decide_rel : typeclass_instances.

(** * Axioms

   We want to work in classical logic with extensional equality.

   Doing this in [Prop] and not [SProp] risks blocking reduction of recursive
   function using a generic [Acc] predicate. But it's fine for function whose
   termination is derived from a measure *)

From Stdlib Require Export FunctionalExtensionality PropExtensionality Classical.

(** Axiomatic proof irrelevance has low priority so that search for proof
    irrelevance try to find axiom-free instances first *)
Instance proof_irrelevance_pi (P : Prop) : ProofIrrel P | 1000 :=
  proof_irrelevance P.

(** ** Make functional extensionality work with rewriting *)

Instance pointwise_eq_ext {A B : Type} `(sb : subrelation B RB eq)
  : subrelation (pointwise_relation A RB) eq.
Proof. intros f g Hfg. apply functional_extensionality. intro x; apply sb, (Hfg x). Qed.

Instance subrel_eq_refl {A : Type} (R : relation A) `{Reflexive A R}
  : subrelation eq R.
Proof. unfold subrelation. naive_solver. Qed.

Instance reflexive_respectful {A B} `{Reflexive C R'}
  : Reflexive (pointwise_relation A (=@{B}) ==> R')%signature.
Proof.
  intros f x y Hpr.
  enough (x = y) as Heq by naive_solver.
  by apply functional_extensionality.
Qed.


(** * Notations ***)

Notation "∅" := Datatypes.Empty_set : type_scope.

(** Heterogenous equality *)
Notation "x =ⱼ y" := (@JMeq _ x _ y) (at level 70, no associativity).
Notation "x ≠ⱼ y" := (¬(x =ⱼ y)) (at level 70, no associativity).

(** Type-annotated list notations *)
Notation "[ ]@{ T }" := (@nil T) (only parsing) : list_scope.
Notation "[ x ]@{ T }" := (@cons T x (@nil T)) (only parsing ): list_scope.
Notation "[ x ; y ; .. ; z ]@{ T }" :=
  (@cons T x (@cons T y .. (@cons T z (@nil T)) ..)) (only parsing ) : list_scope.

(** Monad-annotated fmap notation *)
Notation "f <$>@{ M } v" := (@fmap M _ _ _ f v)
    (at level 61, only parsing, left associativity).

(** Monad annotated bind notations *)
Notation "x ←@{ M } y ; z" := (@mbind M _ _ _ (λ x : _, z) y)
    (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.
Notation "' x ←@{ M } y ; z" := (@mbind M _ _ _ (λ x : _, z) y)
    (at level 20, x pattern, y at level 100, z at level 200, only parsing)
    : stdpp_scope.
Notation "x ;;@{ M } z" := (@mbind M _ _ _ (λ _, z) x)
                       (at level 100, z at level 200, only parsing, right associativity): stdpp_scope.

(** This defines operators [|>] and [|$>] for pipe-style function application
    and fmap *)
Module FunctionPipeNotations := FunctionPipeNotations.

(** Useful for defining decision procedures *)
Notation dec_if D := (match D with | left _ => left _ | right _ => right _ end).
Notation dec_if_and D1 D2 := (match D1 with | left _ => dec_if D2 | right _ => right _ end).
Notation dec_swap D := (match D with | left _ => right _ | right _ => left _ end).

(** Imperative loop in a monad ([M]). If [l] is a [list A] and the body [E] has
    type [M B] (with [x : A] in context), then the whole loop evaluate to a
    value [M (list B)] that yield the list of value of the loop body with monad
    effects applied in the list order (head first). If you want a truly
    imperative loop, use a state monad and have [E] evaluate to [unit], you can
    then ignore the resulting [list unit] e.g. with [;;] *)
Notation "'for' x 'in' l 'do' E 'end'" :=
  (mapM (λ x, E) l)
    (at level 200, x pattern, no associativity).
Notation "'for' @{ M  } x 'in' l 'do' E 'end'" :=
  (@mapM M _ _ _ _ (λ x, E) l)
    (at level 200, x pattern, no associativity, only parsing).

Notation "x .T1" := (projT1 x) (at level 1, left associativity, format "x .T1").
Notation "x .T2" := (projT2 x) (at level 1, left associativity, format "x .T2").

Notation "'is_patP' pat pred" := (λ x, match x with pat => pred | _ => False end) (pat pattern, at level 10).
Notation "'is_pat' pat" := (λ x, match x with pat => True | _ => False end) (pat pattern, at level 10).

(** * Operator typeclasses *)

Class IMap (K : Type) (M : Type → Type) := imap : ∀ {A B}, (K → A → B) → M A → M B.
#[global] Arguments imap {_ _ _ _ _} _ !_ / : assert.
#[export] Instance: Params (@imap) 5 := {}.
#[export] Hint Mode IMap - ! : typeclass_instances.

Class IOMap (K : Type) (M : Type → Type) :=
  iomap : ∀ {A B}, (K → A → option B) → M A → M B.
#[global] Arguments iomap {_ _ _ _ _} _ !_ / : assert.
#[export] Instance: Params (@iomap) 5 := {}.
#[export] Hint Mode IOMap - ! : typeclass_instances.


(** * Utility functions ***)

Arguments bool_decide_pack {_ _} _.
Arguments bool_decide_unpack {_ _} _.

(** Convenient iff destruction *)
Definition iffLR {A B : Prop} (i : A <-> B) : A -> B := proj1 i.
Definition iffRL {A B : Prop} (i : A <-> B) : B -> A := proj2 i.

(** Convert a true proposition into a rewriting rule of that proposition to true
*)
Definition Prop_for_rewrite {P : Prop} (H : P) : P <-> True.
  firstorder.
Defined.

(** This is useful for keeping the equality in a match for dependent typing
    purposes *)
Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.
Arguments inspect : simpl never.

(** When matching [inspect p] instead of [p], this notation allows to have the
    cases be [| pat_for_p eq: Heq => ...] *)
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

Definition is_inl `(x : A + B) : Prop :=
  match x with
  | inl _ => True
  | inr _ => False
  end.
#[global] Instance is_inl_dec `(x : A + B) : Decision (is_inl x).
Proof. destruct x; unfold is_inl; solve_decision. Qed.

Definition is_inr `(x : A + B) : Prop :=
  match x with
  | inl _ => False
  | inr _ => True
  end.
#[global] Instance is_inr_dec `(x : A + B) : Decision (is_inr x).
Proof. destruct x; unfold is_inr; solve_decision. Qed.

Notation guard' P := (guard P;; mret ()).
Notation guard_or' e P := (guard_or e P;; mret ()).

(** * Cartesian product *)

(** Notation for cartesian product on sets and lists. *)
(** × must be left associative because the * of types is left associative.
      Thus if you have sa : set A, sb : set B and sc : set C, then
      sa × sb × sc : set (A * B * C) *)
Infix "×" := cprod (at level 37, left associativity) : stdpp_scope.
Notation "(×)" := cprod (only parsing) : stdpp_scope.
Notation "( x ×.)" := (cprod x) (only parsing) : stdpp_scope.
Notation "(.× x )" := (λ y, cprod y x) (only parsing) : stdpp_scope.


(** * Constrained quantifiers ***)

(* Need this until https://github.com/rocq-prover/rocq/issues/19631 gets
   fixed *)
#[export] Set Warnings "-notation-incompatible-prefix".

#[local] Notation "∀in x ∈ b , P" := (∀ x, x ∈ b → P)
  (at level 10, x binder, only parsing, P at level 200) : type_scope.

Notation "∀ x .. y ∈ b , P" := (∀in x ∈ b, .. (∀in y ∈ b, P) ..)
  (at level 10, x binder, y binder, only parsing, P at level 200) : type_scope.

(* Due to https://github.com/coq/coq/issues/18318, We only reprint constrained
   quantifiers one by one, and not as a group. This allows to specify the proper
   "closed binder" printing specification *)
Notation "∀ x ∈ b , P" := (∀ x, x ∈ b → P)
  (at level 10, x closed binder, only printing,
    format "'[  ' '[  ' ∀  x  ∈  b ']' ,  '/' P ']'") : type_scope.

#[local] Notation "∃in x ∈ b , P" := (∃ x, x ∈ b ∧ P)
  (at level 10, x binder, only parsing, P at level 200) : type_scope.

Notation "∃ x .. y ∈ b , P" := (∃in x ∈ b, .. (∃in y ∈ b, P) ..)
  (at level 10, x binder, y binder, only parsing, P at level 200) : type_scope.

Notation "∃ x ∈ b , P" := (∃ x, x ∈ b ∧ P)
  (at level 10, x closed binder, only printing,
    format "'[  ' '[  ' ∃  x  ∈  b ']' ,  '/' P ']'") : type_scope.


(** * Relations ***)

Arguments clos_refl_trans {_}.

(** * Ltac2 utilities *)

(** Pipe notation for function calls *)
Ltac2 Notation x(self) "|>" f(self) : 4 := f x.

(** Fix up the do notation. The default one doesn't work *)
Ltac2 Notation "do" n(thunk(tactic(0))) t(thunk(self)) := do0 n t.

(** or else notation, same as [||] in Ltac1. Due to parser limitations this is a
    the same level as [;] and also right associative, so [a ; b ||ₜ c] is
    [a ; (b ||ₜ c)] but [a ||ₜ b ; c] is [a ||ₜ (b ; c)]*)
Ltac2 Notation a(thunk(self)) "||ₜ" b(thunk(self)) : 6 :=
  orelse a (fun _ => b ()).

(** Throw a [Tactic_failure] with the provided formated message *)
Ltac2 throw_tacticf fmt :=
  Message.Format.kfprintf (fun m => Control.throw (Tactic_failure (Some m))) fmt.
Ltac2 Notation "throw_tacticf" fmt(format) := throw_tacticf fmt.

(** Backtracks with a [Tactic_failure] with the provided formated message *)
Ltac2 zero_tacticf fmt :=
  Message.Format.kfprintf (fun m => Control.zero (Tactic_failure (Some m))) fmt.
Ltac2 Notation "zero_tacticf" fmt(format) := zero_tacticf fmt.

(** Converts a result into an option, discarding the error payload *)
Ltac2 res_to_opt a :=
  match a with
  | Val v => Some v
  | Err _ => None
  end.

Ltac2 case_opt (f: unit -> 'a) : 'a option :=
  match Control.case f with
  | Val (v, _) => Some v
  | Err _ => None
  end.

(** Get the name of the last hypothesis *)
Ltac2 last_hyp_name () := let (h, _, _) := List.last (Control.hyps ()) in h.
(** Introduce an hypothesis and get the automatically generated name *)
Ltac2 intro_get_name () := intro; last_hyp_name ().

(** If a term is an application, get the head function of that application *)
Ltac2 rec get_head (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h _ => get_head h
  | _ => t
  end.

(** Separate a non-dependent function type like [A → B → C] into ([A; B], C)*)
Ltac2 rec decompose_non_dep_fun_type (t : constr) : constr list * constr :=
  lazy_match! t with
  | ?hd -> ?tl => let (args, res) := decompose_non_dep_fun_type tl in
                  (hd :: args, res)
  | _ => ([], t)
  end.

(** If a constr is a variable, get the variable name, otherwise None *)
Ltac2 get_var (c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var i => Some i
  | _ => None
  end.
Ltac2 get_var_bt (c: constr) := Option.get_bt (get_var c).

(** Create an evar of the required type *)
Ltac2 mk_evar (t : constr) : constr :=
  let res := '(_) in
  Std.unify (Constr.type res) t;
  res.

(** Get an instance of a provided typeclass (evar allowed in output positions)
    Fail (backtracks) if the instance can't be found *)
Ltac2 get_instance (tc : constr) : constr :=
  '(ltac2:(Std.unify (Control.goal ()) tc; typeclasses_eauto)).
(** Same but returns None if instance can't be found *)
Ltac2 get_instance_opt (tc : constr) : constr option :=
  case_opt (fun () => get_instance tc).

(** Used when success has been found *)
Ltac2 Type exn ::= [ Success ].

(** Return true if the tactics succeeds in the context, and [false] otherwise *)
Ltac2 succeeds0 t :=
  match Control.case (fun () => t (); Control.zero Success) with
  | Err Success => true
  | Err _ => false
  | Val _ => Control.throw Assertion_failure
  end.
Ltac2 Notation succeeds := succeeds0.

(** Backtrack if the boolean is not [true] *)
Ltac2 assert_bt b := if b then () else Control.zero Assertion_failure.

(** Ltac2 version of pose_proof *)
Ltac2 pose_proof c := Std.pose None c; Std.clearbody [last_hyp_name()].
Ltac2 Notation "pose" "proof" c(constr) := pose_proof c.
Ltac2 pose_proof_get c :=
  Std.pose None c;
  let n := last_hyp_name () in
  Std.clearbody [n];
  n.

(** Remove the last element of a list and return the reverted version of the rest *)
Ltac2 rec removelast_rev (l : 'a list) :=
  let rec aux (acc : 'a list) (ls : 'a list) :=
    match ls with
    | [] => []
    | [_] => acc
    | x :: (_ :: _ as t) => aux (x :: acc) t
    end
  in aux [] l.

Ltac2 ignore x := x; ().

(** [match_pat p c] decides if term [c] matches pattern [p] *)
Ltac2 match_pat (p : pattern) (c : constr) : bool :=
  succeeds (ignore (Pattern.matches p c)).

(** Finds the highest hypothesis that matches the pattern and revert all
    hypotheses below it *)
Ltac2 revert_until (clr : bool) (p : pattern) :=
  match
    List.fold_left
      (fun o (h, _, c) =>
         match o with
         | [] => if match_pat p c then [h] else []
         | l => h :: l
         end
      ) [] (Control.hyps ())

  with
  | [] => Control.zero Not_found
  | l =>
      Std.revert (removelast_rev l); if clr then Std.clear [List.last l] else ()
  end.
Ltac2 Notation "revert" "until" p(pattern) := revert_until false p.
Ltac2 Notation "revert" "until" "*" p(pattern) := revert_until true p.

(** Get an hypothesis by pattern *)
Ltac2 get_hyp (p : pattern) : (ident * constr option * constr) option :=
  Control.hyps () |> List.find_opt (fun (_, _, c) => match_pat p c).

(** Get an hypothesis name by pattern *)
Ltac2 get_hyp_id (p : pattern) : ident option :=
  get_hyp p |> Option.map (fun (h, _, _) => h).


Ltac2 block_goal0 () := ltac1:(block_goal).
Ltac2 Notation block_goal := block_goal0 ().
Ltac2 unblock_goal0 () := ltac1:(unblock_goal).
Ltac2 Notation unblock_goal := unblock_goal0 ().


(** Ltac2 conversions that throw on error *)
Ltac2 ltac1_to_ident x := Option.get (Ltac1.to_ident x).
Ltac2 ltac1_to_constr x := Option.get (Ltac1.to_constr x).
Ltac2 ltac1_to_list (f : Ltac1.t -> 'a) (t : Ltac1.t) :=
  t |> Ltac1.to_list |> Option.get |> List.map f.

(** Revert dependent is like generalize dependent but only on hypothesis *)
Ltac2 revert_dependent (l : ident list) :=
  List.iter (fun x => ltac1:(x |- generalize dependent x) (Ltac1.of_ident x))
    (List.rev l).
Ltac2 Notation "revert" "dependent" l(list1(ident)) := revert_dependent l.
Tactic Notation "revert" "dependent" ne_ident_list(h) :=
  let f := ltac2:(h |- revert_dependent (ltac1_to_list ltac1_to_ident h)) in f h.


(** ** Ltac2 debug printers *)
(** Ident Ltac2 printer *)
Ltac2 prt_id () := fprintf "@%I".

(** Int Ltac2 printer *)
Ltac2 prt_int () := Message.of_int.

(** String Ltac2 printer *)
Ltac2 prt_str () := Message.of_string.
(** Quoted string Ltac2 printer *)
Ltac2 prt_strq () s :=
  let quote_string := String.make 1 (Char.of_int 34) in
  fprintf "%s%s%s" quote_string s quote_string.

(** Term Ltac2 printer *)
Ltac2 prt_cstr () := Message.of_constr.
(** Preterm Ltac2 printer *)
Ltac2 prt_pret () pt := Message.of_constr (Constr.pretype pt).

(** Bool Ltac2 printer *)
Ltac2 prt_bool () b :=
  if b then Message.of_string "true" else Message.of_string "false".

(** List Ltac2 printer *)
Ltac2 prt_list (printer : unit -> 'a -> message) () (l : 'a list) :=
  let rec aux () l :=
    match l with
    | [] => Message.of_string ""
    | [a] => printer () a
    | hd :: tl => fprintf "%a; %a" printer hd aux tl
    end
  in fprintf "[%a]" aux l.

(** Option Ltac2 printer *)
Ltac2 prt_opt (printer : unit -> 'a -> message) () (o : 'a option) :=
  match o with
  | Some x => fprintf "Some %a" printer x
  | None => fprintf "None"
  end.

(** Pair Ltac2 printer *)
Ltac2 prt_pair (printer1 : unit -> 'a -> message) (printer2 : unit -> 'b -> message)
               () (p : 'a * 'b) :=
  let (a, b) := p in
  fprintf "(%a, %a)" printer1 a printer2 b.

(** Hypothesis Ltac2 printer. The name must exist in the current goal *)
Ltac2 prt_hyp () (x : ident) := fprintf "%I:%t" x (Constr.type (Control.hyp x)).


(** *** Ltac2 inductive type manipulation *)

(** Get the number of constructor of an inductive type. Does [get_head] automatically if needed. *)
Ltac2 rec get_nconstructors(ind_type : constr) : int option :=
  match Constr.Unsafe.kind ind_type with
  | Constr.Unsafe.Ind i _ => Some (Ind.nconstructors (Ind.data i))
  | Constr.Unsafe.App c _ => get_nconstructors c
  | _ => None
  end.

(** Takes an inductive type constructor, possibly partially applied to
    parameters, and return its [n]th constructor, partially applied to the same
    parameter. This will fail if the type constructor is applied to indices
    (non-uniform) parameters *)
Ltac2 rec get_constructor (ind_type : constr) (n : int) : constr option :=
  match Constr.Unsafe.kind ind_type with
  | Constr.Unsafe.Ind i inst =>
      let ctr : constructor := Ind.get_constructor (Ind.data i) n in
      let ctr := Constr.Unsafe.Constructor ctr inst |> Constr.Unsafe.make in
      ctr |> Constr.Unsafe.check |> res_to_opt
  | Constr.Unsafe.App i a =>
      match get_constructor i n with
      | Some c =>
          Constr.Unsafe.App c a
          |> Constr.Unsafe.make
          |> Constr.Unsafe.check
          |> res_to_opt
      | None => None
      end
  | _ => None
  end.


(** *** Ltac2 goal printer

   Allow to print the current goal anywhere *)
Ltac2 print_goal0 () :=
  List.iter (fun (name, body, type) =>
               match body with
               | None => printf "%I: %t" name type
               | Some b => printf "%I: %t := %t" name type b
               end) (Control.hyps ());
  printf "--------------------------------------------------------------";
  printf "%t" (Control.goal ()).
Ltac2 Notation print_goal := print_goal0 ().
Ltac print_goal := ltac2:(print_goal).

(** * Conversion check

This allows to test whether two terms convert without unifying evars. This will
be in Ltac2 standard library in 9.1, but this works in the mean time. *)

#[local] Set Typeclasses Strict Resolution.
Inductive TCConv {A} (x : A) : A → Prop := TCConv_refl : TCConv x x.
Existing Class TCConv.
#[local] Unset Typeclasses Strict Resolution.
Existing Instance TCConv_refl.

Ltac2 conv_check t t' :=
  if (succeeds (assert (TCConv $t $t') by typeclasses_eauto))
  then ()
  else zero_tacticf "%t and %t are not convertible" t t'.

Ltac conv_check t t' :=
  let f := ltac2:(t t' |- conv_check (ltac1_to_constr t) (ltac1_to_constr t')) in
  f t t'.


(** * Tactic options

This development relies a lot on automation. This automation sometime needs to
be configured in what it should or should not do. A typeclass option is an empty
typeclass like [Class Option1 := {}] It can take parameter like [Class Option2
(n : nat) := {}.]. When defining options it nice to provide a default instance
like [Definition option1 : Option1 := ltac:(constructor)]. This allows the user
to enable the option with a plain [Existing Instance].

Options can be used in typeclass resolution by requiring the option typeclass in
specific instances: [Instance myinstance: `{Option1} param1 param2 : MyTypeclass
param 1 param2.] *)

(** To use such an option in a tactic, one can use [has_option opt] which will
    succeed if the option is turned on (aka the typeclass resolution found the
    option), and fail other wise.

    This can be used more generally to check if a typeclass instance exists *)
Ltac has_option opt := assert_succeeds (eassert opt; first tc_solve).

Ltac2 has_option0 c := succeeds (assert $c by ltac1:(tc_solve)).
Ltac2 Notation "has_option" c(constr) := has_option0 c.
Ltac2 Notation "assert_option" c(constr) := assert_bt (has_option0 c).
Ltac use_option opt := assert opt by constructor.


(** To enable an option locally, one can either do it at Section/Module scope
    with: [#[local] Exixting Instance option1.]. Alternatively one can use the
    [#] combinator to add an option for the time of a single tactic. If it's an
    option with universally quantified parameters you need to manually write the
    foralls: [tac # (∀ n, Option2 (S n))] *)
Tactic Notation (at level 4) tactic4(tac) "#" constr(opt) :=
  let Opt := fresh "Opt" in
  assert opt as Opt by (intros; constructor);
  move Opt at top;
  tac;
  clear Opt.

(** Another way to use options or other lemma is the [use] combinator. For
    example [tac use lem] add the lemma/Instance [lem] temporaryly, just while
    [tac] is running. In general, for clarity, prefer [#] for options and [use]
    for other lemmas. *)
Tactic Notation (at level 4) tactic4(tac) "##" constr(p) :=
  let Use := fresh "Use" in
  pose proof p as Use;
  tac;
  clear Use.


(** * Utility tactics ***)

Ltac block t := change t with (block t) in *.
Ltac unblock := unfold block in *.

(** ** Hypothesis management *)

(** Introduces a variable or hypothesis with its default name and returns that
    name *)
Ltac intro_get_name :=
  let _ := match goal with |- _ => intro end in
  match goal with H : _ |- _ => H end.

(** Reverts the last hypothesis *)
Ltac deintro :=
  match goal with
  | H : _ |- _ => revert H
  end.

(** Reverts all hypotheses *)
Ltac deintros := repeat deintro.

(** Reverts all hypotheses, print the goal and then undo everything.
    This is a debugging no-op tactic. *)
Ltac print_full_goal := try(deintros; match goal with |- ?G => idtac G end; fail).

(** Run [tac] on all hypotheses in first-to-last order. Later hypotheses are
    moved into the goal when [tac] is ran*)
Ltac forall_hyps tac :=
  lazymatch goal with
  | H : _ |- _ => revert H; try (forall_hyps tac); intro H; try(tac H)
  end.

Inductive hyp_block := HypBlock.

Ltac hyp_start_block := pose proof HypBlock.
Ltac hyp_revert_until_block :=
  lazymatch goal with
  | H : ?T |- _ => tryif unify T hyp_block then clear H else (revert H;hyp_revert_until_block)
  end.

Ltac revert_generated_hyps tac := hyp_start_block; tac; hyp_revert_until_block.

Ltac2 revert_generated_hyps tac :=
  Control.enter (fun () => pose proof HypBlock; tac (); revert until* hyp_block).

(** Actually simple inversion: Leave the generated equalities in the goal *)
Tactic Notation "sinv" ident(x) :=
  hyp_start_block; simple inversion x; hyp_revert_until_block; intros _.
Tactic Notation "sinv" integer(x) :=
  hyp_start_block; simple inversion x; hyp_revert_until_block; intros _.

(** Funelim that leave new hypotheses in the goal *)
Tactic Notation "sfunelim" uconstr(t) :=
  hyp_start_block; funelim t; hyp_revert_until_block.



(** ** Rewriting *)

(** Takes an evar and puts it in a pattern shape. Use as (do n pattern_evar) if
    you have [n] evars in your goal. This is might be needed for typeclass-based
    rewriting tactics that use "+" and not "!" as Hint Mode *)
(* TODO detect the number of evar automatically *)
Ltac pattern_evar :=
  match goal with | |- context G [?x] => is_evar x; pattern x end.

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

(** ** Typeclass clean

Typeclass clean to help prove typeclasses lemmas.

Call this when the goal is rewriting typeclass (generally with [Unfold] in its
name), with other rewriting typeclasses in the context. This unfold all the
typeclasses, apply the rewrites and leave with the actual rewriting goal to
prove. *)

(** Cleanup a single hypothesis *)
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
  | TCSimpl _ _ => rewrite TCSimpl_eq in H; try (setoid_rewrite H)
  | Unconvertible _ _ _ => clear H
  | TCFastDone _ => apply (@tc_fast_done _) in H
  | _ => destruct H as [H]; try(repeat (setoid_rewrite <- H || rewrite <- H))
  end.

(** Introduce and cleans up all typeclass hypothesis and then cleans up the goal
    typeclass *)
Ltac tcclean :=
  (let H := fresh "H" in intro H; tcclean; try(tcclean_hyp H)) || constructor.

(** ** Destruct decide *)

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

(** ** Evar blocking *)

(** Yet another block like marker for blocking evar, mainly for typeclass resolution *)
Definition blocked_evar {A} (a : A) := a.
#[global] Opaque blocked_evar.

Ltac block_evar t := change t with (blocked_evar t) in *.
Ltac unblock_evars := cbv [blocked_evar] in *.
Ltac2 unblock_evars0 () := cbv [blocked_evar] in *.
Ltac2 Notation unblock_evars := unblock_evars0 ().

(** Take a term as a parameter and blocks one evar from it *)
Ltac block_one_evar t :=
  match t with
  | context [ ?e ] =>
      is_evar e;
      assert_fails (idtac; lazymatch t with context [blocked_evar e] => idtac end);
      block_evar e
  end.
(** Take a tactic looking up the context to find a term  *)
Ltac block_all_evars tac :=
  repeat (let t := tac () in block_one_evar t).


(** * Proof search ***)

(* Useful to tell auto/eauto to call lia could be improved by looking if the
   goal is an equality/inequality on integers*)
Hint Extern 10 => lia : lia.

(** * Typeclass magic ***)

Require Import Morphisms.
Import Morphisms.ProperNotations.
Require Import Stdlib.Classes.RelationClasses.

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


(** * Record management and lenses

We somewhat hack [coq-record-update] to provide a lens-like system with vertical
composition and horizontal merges. We basically have standard way to compose
record fields and more generic getters that can then be used to infer a setter
using coq-record-update mechanisms. *)

Hint Mode Setter + + + : typeclass_instances.
Hint Mode SetterWf + + + : typeclass_instances.

(** Remove the [set_wf] instance because it make the search for a Setter much
    slower in the general case. Just allow to use it if there is a [SetterWf]
    in the immediate (or section) context, like in [Setter_compose_wf] *)
#[export] Remove Hints RecordSet.set_wf : typeclass_instances.
Hint Extern 100 (Setter _) =>
       class_apply (RecordSet.set_wf) ; assumption : typeclass_instances.

(** Set a value without looking at the previous value *)
Definition setv {R T} (proj : R -> T) `{!Setter proj} (v: T) : R -> R :=
  set proj (fun _ => v).

(** This allows to use set fst and set snd on pairs *)
Global Instance eta_pair A B : Settable (A * B) :=
  settable! (@pair A B) <fst;snd>.

(** ** Getter and setter vertical composition *)
Global Instance Setter_compose `{SRT : Setter R T proj}
  `{STT : Setter T T' proj'} :
  Setter (proj' ∘ proj) := fun x => SRT (STT x).

Global Program Instance Setter_compose_wf `{SRT : SetterWf R T proj}
  `{STT : SetterWf T T' proj'} : SetterWf (proj' ∘ proj) :=
  { set_wf := Setter_compose }.
Solve All Obligations with sauto lq:on.

(** ** Getter and setter horizontal merging *)
Definition getter_merge {R T T'} (proj : R → T) (proj' : R → T') : R → T * T' :=
  λ r, (proj r, proj' r).
#[global] Infix "××" := getter_merge (at level 40).

Global Instance Setter_merge `{SRT : Setter R T proj} `{SRT' : Setter R T' proj'}
  : Setter (proj ×× proj') :=
  λ f r,
    let t := proj r in
    let t' := proj' r in
    let (nt, nt') := f (t, t') in
    r |> setv proj nt |> setv proj' nt'.

Class Separated `{SRT : Setter R T proj} `{SRT' : Setter R T' proj'} :=
  separated : ∀ f r, proj' (set proj f r) = proj' r.
Arguments Separated {_ _} _ {_ _} _ {_}.
Hint Mode Separated + + + + + + + : typeclass_instances.
(* This should find most trivial instances automatically *)
Hint Extern 10 (Separated _ _) =>
       unfold Separated; reflexivity : typeclass_instances.

(* We can't make this an instance directly because [class_apply] shelves the
   [SetterWf] instances. Instead we add a [Hint Extern] with
   [unshelve (class_apply _)] instead *)
Definition Setter_merge_wf `{SRT : SetterWf R T proj}
  `{SRT' : SetterWf R T' proj'} `{!Separated proj' proj} :
    SetterWf (proj ×× proj').
  esplit;
    abstract(
        intros;
        unfold set, Setter_merge, getter_merge, setv in *;
        case_match;
        f_equal;
        simplify_eq;
        try rewrite separated;
        by (rewrite set_get || (repeat rewrite RecordSet.set_eq))).
Defined.
Hint Extern 10 (SetterWf (_ ×× _)) =>
       unshelve (class_apply @Setter_merge_wf) : typeclass_instances.


(** ** Constants getter *)

(** Sometimes it is useful to have a fake constant getter to merge with other
getters. It will not be well formed *)
Definition const_getter {R T} (t : T) : R → T := λ r, t.

Global Instance Setter_const {R T} t :
  @Setter R T (const_getter t) := λ f r, r.


(** ** Record equality unfolding *)

(** For a record type A, this typeclass provides an output predicate Q that is a
    conjunction of field_wise equality that is equivalent to the record
    equality. This is automatically derived from a [Settable] instance although
    the user is free to define his own instances *)
Class RecordEqUnfold A (Q : A → A → Prop) := {record_eq_unfold a b : a = b ↔ Q a b}.
#[global] Hint Mode RecordEqUnfold + - : typeclass_instances.

(** Helper for the following [Hint Extern] *)
Lemma __rec_eq_help (A B C : Prop) : (B ∧ A → C) → A → B → C.
Proof. firstorder. Qed.

(** Generate a [RecordEqUnfold] instance from a [Settable] instance *)
#[export] Hint Extern 0 (RecordEqUnfold ?T _) =>
  has_option (Settable T);
  let H := fresh in
  constructor;
  intros ? ?;
    setoid_rewrite <- mkT_ok at 1 2;
  cbn;
  split;
  [intro H;
   injection H;
   repeat
     lazymatch goal with
       |- _ → _ → _ => refine (__rec_eq_help _ _ _ _)
     end;
   clear H;
   intro H;
   exact H|];
  cbn beta;
  intro H;
  destruct_and! H;
  congruence : typeclass_instances.

(** Tactic to prove record equality by proving equality for all fields. The
    number of subgoal is exactly the number of field*)
Ltac record_eq := apply record_eq_unfold; repeat split_and.

(** Take an equality hypothesis [H] of the form [rec = rec'] and destruct it
    into an equlity for each field. The "as" version is use with a conjunction
    pattern: [record_inj H as (Hfield1 & Hfield2 & ...)] *)
Tactic Notation "record_inj" hyp(H) :=
  apply record_eq_unfold in H; destruct_and! H.
Tactic Notation "record_inj" hyp(H) "as" simple_intropattern(pat) :=
  apply record_eq_unfold in H; destruct H as pat.


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
Lemma pair_let_simp_type A B C (z : A * B) (P : A → B → C) : (let '(x,y) := z in P x y) = P z.1 z.2.
Proof. by destruct z. Qed.
#[global] Hint Rewrite pair_let_simp : pair.
#[global] Hint Rewrite pair_let_simp_type : pair.
#[global] Hint Rewrite <- surjective_pairing : pair.
Ltac pair_let_clean :=
  (setoid_rewrite pair_let_simp || setoid_rewrite pair_let_simp_type);
  try (setoid_rewrite <- surjective_pairing).

(** * EmptyT and DecisionT *)

(** Mark a type as empty, useable for guiding typeclass resolution. *)
Class EmptyT (T : Type) := emptyT : (T → False : Prop).
Global Hint Mode EmptyT ! : typeclass_instances.


(** Typeclass for type (and more usefully families of types) that are decidably
    empty or not *)
Class DecisionT (T : Type) := decideT : T + {T → False}.
Global Hint Mode DecisionT ! : typeclass_instances.
Global Arguments decideT _ {_} : simpl never, assert.

(** Trivial instances of Decision T if type is either inhabited or empty *)
Global Instance inhabited_decisionT `{Inhabited T} : DecisionT T :=
  inleft inhabitant.
Global Instance emptyT_decisionT `{EmptyT T} : DecisionT T := inright emptyT.

(** ** Inhabited, EmptyT, and DecisionT, missing base type instances *)

Global Instance emptyT_empty : EmptyT ∅.
Proof. inversion 1. Qed.

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

(** * Identity Monad

This is useful to apply transformers on, or in contexts that really expect a
monad. *)

(** The identity monad. We are not using a regular [id] to help type inference
    and avoid universes constraints *)
Definition idM (T : Type) := T.
(* This is necessary otherwise typeclass search would find monads everywhere. *)
#[global] Typeclasses Opaque idM.

#[global] Instance idM_ret : MRet idM := λ _ x, x.
#[global] Instance idM_bind : MBind idM := λ _ _ f ma, f ma.
#[global] Instance idM_join : MJoin idM := λ _ mma, mma.
#[global] Instance idM_fmap : FMap idM := λ _ _ f ma, f ma.

(** * Computable transport

This allow to computably transport object of type families along an equality on
the indices (e.g. [fin], [vec], [bv]). The equality must be on concrete values
and not on types (e.g. [n = m] and not [fin n = fin m]).

The goal for ctrans is to compute using [vm_compute] and similar tactics even if
the equality proof is entirely opaque. Nevertheless it can safely be extracted
to [Obj.magic]. This is a band aid until we have builtin [cast] from Observable
Type Theory (OTT). *)

(** CTrans is the main typeclass for computable transport. It only contains
computational content and not soundness *)
Class CTrans {T : Type} (F : T → Type) :=
  ctrans : ∀ (x y : T) (eq : x = y) (a : F x), F y.
#[global] Arguments ctrans {_ _ _ _ _} _ _.
#[export] Instance: Params (@ctrans) 3 := {}.
#[export] Hint Mode CTrans ! ! : typeclass_instances.

(** [CTransSimpl] is a companion typeclass that the soundness proof of a
[CTrans] instance *)
Class CTransSimpl `{CTrans T F} :=
  ctrans_simpl : ∀ (x : T) (p : x = x) (a : F x), ctrans p a = a.
#[global] Arguments CTransSimpl {_} _ {_}.
#[export] Hint Mode CTransSimpl ! ! - : typeclass_instances.
#[export] Hint Rewrite @ctrans_simpl using tc_solve : ctrans.

Lemma ctrans_sym `{CTransSimpl T F} {n m : T} (e : n = m) (a : F n) (b : F m):
  a = ctrans (symmetry e) b ↔ ctrans e a = b.
Proof. subst. cbn. by simp ctrans. Qed.
#[export] Hint Rewrite @ctrans_sym using tc_solve : ctrans.

Lemma ctrans_trans `{CTransSimpl T F} {n m p : T}
  (e : n = m) (e' : m = p) (a : F n) :
  a |> ctrans e |> ctrans e' = ctrans (eq_trans e e') a.
Proof. subst. cbn. by simp ctrans. Qed.
#[export] Hint Rewrite @ctrans_trans using tc_solve : ctrans.

Lemma ctrans_inj `{CTransSimpl T F} {n m : T} (e e' : n = m) (a b : F n):
  ctrans e a = ctrans e' b ↔ a = b.
Proof. rewrite <- ctrans_sym. simp ctrans. reflexivity. Qed.
#[export] Hint Rewrite @ctrans_inj using tc_solve : ctrans.


(** ** Computable transport combinators *)

Instance ctrans_prod `{CTrans A F, CTrans A G} :
    CTrans (λ x, F x * G x)%type | 100 :=
  λ a b e '(x, y), (ctrans e x, ctrans e y).

Instance ctrans_prod_simpl `{CTransSimpl A F, CTransSimpl A G} :
  CTransSimpl (λ x, F x * G x)%type | 100.
Proof. intros x p []. cbn. by simp ctrans. Qed.

Instance ctrans_prodl `{CTrans A F} T :
    CTrans (λ x, F x * T)%type | 50 :=
  λ a b e '(x, y), (ctrans e x, y).

Instance ctrans_prodl_simpl `{CTransSimpl A F} T :
  CTransSimpl (λ x, F x * T)%type | 50.
Proof. intros x p []. cbn. by simp ctrans. Qed.

Instance ctrans_prodr `{CTrans A F} T :
    CTrans (λ x, T * F x)%type | 50 :=
  λ a b e '(x, y), (x, ctrans e y).

Instance ctrans_prodr_simpl `{CTransSimpl A F} T :
  CTransSimpl (λ x, T * F x)%type | 50.
Proof. intros x p []. cbn. by simp ctrans. Qed.

Instance ctrans_f_equal `(f : A → B) `{CTrans B F}  :
  CTrans (λ x, F (f x)) := λ a b e x, ctrans (f_equal f e) x.

Instance ctrans_f_equal_simpl `(f : A → B) `{CTransSimpl B F} :
  CTransSimpl (λ x, F (f x)).
Proof. intros x p a. unfold ctrans. unfold ctrans_f_equal. by simp ctrans. Qed.

(** ** Computable transport for [fin] *)

Arguments eq_add_S {_ _} _.

Equations ctrans_fin : CTrans fin :=
ctrans_fin (S x) (S y) _ 0%fin := 0%fin;
ctrans_fin (S x) (S y) H (FS a) := FS (ctrans_fin x y (eq_add_S H) a).
#[export] Existing Instance ctrans_fin.

Lemma ctrans_fin_zero `(H : S x = S y) : ctrans H (0%fin) = 0%fin.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @ctrans_fin_zero : ctrans.

Lemma ctrans_fin_succ `(H : S x = S y) a :
  ctrans H (FS a) = FS (ctrans (eq_add_S H) a).
Proof. unfold ctrans. by simp ctrans_fin. Qed.
#[export] Hint Rewrite @ctrans_fin_succ : ctrans.

#[export] Instance ctrans_fin_simpl : CTransSimpl fin.
Proof.
  intros x p a.
  induction a; simp ctrans; congruence.
Qed.

