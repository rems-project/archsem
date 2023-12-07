(** This file provide support for handling algebraic effects.
    It uses UIP *)

Require Import CBase CBool.
Require Import Options.
From stdpp Require Import base.
From stdpp Require Import fin.
From stdpp Require Import vector.

(** UIP is need for this theory to be usable *)
Require Export Eqdep.
Require Export Program.Equality.

From Equations Require Import Equations.





(** An effected is a function from Type to Type that take the return type of the
    effect and give the type of all calls that could return that return type.

    This is voluntarily NOT universe polymorphic. It should probably be Set →
    Set to be honest. *)
Definition eff := Type → Type.

(** Generic interface for calling an algebraic effect in a monad *)
Class MCall (Eff : eff) (M : Type → Type) := mcall : ∀ {A}, Eff A → M A.
#[global] Arguments mcall {_ _ _ _} _ : assert.
#[global] Instance: Params (@mcall) 4 := {}.
#[global] Hint Mode MCall - ! : typeclass_instances.

(** Call a non returning effect. This is not necessarily a failure, so this
    doesn't automatically implement MThrow *)
Definition mcall_noret `{EmptyT T, MBind M, MCall Eff M} (call : Eff T) {A} :
    M A :=
  x ← mcall call;
  match emptyT x with end.


(** Generic sub-effect judgment, in theory this looks like MCall, but make both
the same causes universes problems. In addition they need a different Hint Mode
*)
Class SubEff (Eff Eff' : eff) := eff_inj : ∀ {A}, Eff A → Eff' A.
#[global] Arguments eff_inj {_ _ _ _} _ : assert.
#[global] Instance: Params (@eff_inj) 4 := {}.
#[global] Hint Mode SubEff ! ! : typeclass_instances.

#[global] Instance SubEff_default Eff : SubEff Eff Eff | 100 := λ _ x, x.

(* TODO, this might need to be a Hint Extern *)
Definition MCall_SubEff {E} `{MCall E' M} `{SubEff E E'} : MCall E M :=
  λ A e, mcall (eff_inj e : E' A).

#[export] Hint Extern 5 (MCall ?E ?M) =>
  tryif (is_evar E) then fail else class_apply MCall_SubEff
  : typeclass_instances.




(** Scope for effect notation *)
Declare Scope effect_scope.
Delimit Scope effect_scope with eff.
Bind Scope effect_scope with eff.
Open Scope effect_scope.

Notation "x .T1" := (projT1 x) (at level 1, left associativity, format "x .T1").
Notation "x .T2" := (projT2 x) (at level 1, left associativity, format "x .T2").

(** For any effect value, either a value to be returned exists, or the effect is
    an exception and can be converted to the associated exception type *)
Module Eff.
  Section Eff.
    Context {Eff : eff}.

    (** * Effect equality *)
    Definition eq {T T'} (call : Eff T) (call' : Eff T') :=
      existT T call = existT T' call'.
    Infix "=ₑ" := eq (at level 70, no associativity) : effect_scope.

    Definition conv_call {T T'} (eq : T = T') (call : Eff T) : Eff T' :=
      eq_rect T Eff call T' eq.

    Definition conv_ret {T T'} (eq : T = T') (ret : T) : T' :=
      eq_rect T (λ x, x) ret T' eq.

    Definition eq_type {T T'} {call : Eff T} {call' : Eff T'} :
      call =ₑ call' → T = T' := @eq_sigT_fst _ _ _ _ _ _.

    Definition eq_call {T} {call call': Eff T} :
      call =ₑ call' → call = call' := inj_pair2 _ _ _ _ _.

    Definition eq_call_rew {T} {call call': Eff T} :
      call =ₑ call' ↔ call = call'.
    Proof using. split; [apply eq_call | naive_solver]. Qed.

    Lemma existT_eq_type {a b : sigT Eff} : a = b → a.T1 = b.T1.
    Proof using. scongruence. Qed.

    Lemma existT_eq_simplify (a : sigT Eff) (c : Eff a.T1) :
      a = existT _ c → a.T2 = c.
    Proof using.
      intro H.
      destruct a.
      by dependent destruction H.
    Qed.


    (** * Effect Decision *)
    Class Decision :=
      decide_eq T T' (c : Eff T) (c' : Eff T') :: base.Decision (c =ₑ c').

    #[global] Instance eff_decision_sigT `{Decision} : EqDecision (sigT Eff).
    Proof using. intros [] []. solve_decision. Defined.

    #[global] Instance eff_decision_eff `{Decision} T : EqDecision (Eff T).
    Proof using.
      refine (λ x y, dec_if (decide (x =ₑ y))).
      - by apply eq_call.
      - naive_solver.
    Defined.


    (** * Effect wellformedness

          An effect is wellformed if we have DecisionT for all type that it
          could ask as return type. In other words if for all effects we can
          decide if has an empty return type or not *)
    Class Wf := wf : ∀ T, Eff T → DecisionT T.


    (** * Exception representation.

        The goal of this typeclass is to represent all effects that cannot be
        returned to as a single exception type
     *)
    Class Exc := {
        exc : Type;
        exc2eff : exc → sigT Eff;
        eff2exc : ∀ {T}, Eff T → option exc;
        exc_wf : ∀ e T call,
          exc2eff e = existT T call ↔ eff2exc call = Some e;
        exc_empty : ∀ T (call : Eff T), is_Some (eff2exc call) ↔ (T → False)
        }.
    Context {E : Exc}.


    Lemma exc_empty_helper `{Inhabited T} P: ¬ P → P ↔ (T → False).
    Proof using. sfirstorder. Qed.

    Lemma exc_no_return T (call : Eff T) : is_Some (eff2exc call) → T → False.
    Proof using. by rewrite exc_empty. Qed.

    #[global] Instance exc2eff_inj : Inj (=) (=) (exc2eff).
    Proof using.
      intros x y H.
      destruct (exc2eff x) eqn:Heqn.
      hfcrush use:exc_wf.
    Qed.

    Definition exc2call (e : exc) := (exc2eff e).T2.

    Lemma exc2call_wf {T} (c : Eff T) e:
      eff2exc c = Some e ↔ c =ₑ exc2call e.
    Proof using.
      unfold exc2call.
      unfold eq.
      rewrite <- sigT_eta.
      sfirstorder use:exc_wf.
    Qed.

    Lemma ret_or_exc_exc2call e : eff2exc (exc2call e) = Some e.
    Proof using.
      unfold exc2call.
      rewrite <- exc_wf.
      rewrite <- sigT_eta.
      reflexivity.
    Qed.

    #[global] Instance eff2exc_type_empty e : EmptyT (Eff.exc2eff e).T1.
    Proof using.
      unfold EmptyT.
      rewrite <- exc_empty.
      eexists.
      by apply ret_or_exc_exc2call.
    Qed.

    Lemma exc_type_empty e : (exc2eff e).T1 → False.
    Proof using.
      intro T.
      destruct (exc2eff e) eqn:He.
      eapply exc_no_return.
      - rewrite exc_wf in He. naive_solver.
      - assumption.
    Qed.


  End Eff.

  Infix "=ₑ" := Eff.eq (at level 70, no associativity) : effect_scope.
  #[global] Hint Mode Exc ! : typeclasses_instances.
  #[global] Arguments Exc : clear implicits.
  #[global] Arguments exc _ {_}.
  #[global] Hint Mode Wf ! : typeclasses_instances.
  #[global] Arguments Wf : clear implicits.
  #[global] Hint Mode Decision ! : typeclass_instances.
  #[global] Arguments Decision : clear implicits.
  #[global] Arguments decide_eq {_ _ _ _} _ _ : simpl never, assert.

  #[global] Hint Rewrite @ret_or_exc_exc2call : eff.

  Ltac Wf_decisionT_apply T :=
    match goal with
    | call : ?Eff T |- _ =>
        let H := fresh "H" in
        enough (Wf Eff) as H; first apply (H T call)
    end.
  #[global] Hint Extern 5 (DecisionT ?T) =>
           Wf_decisionT_apply T : typeclass_instances.

  Tactic Notation "simplify_eff_eq" "in" ident(H) :=
    match type of H with
    | _ = @existT Type ?Eff ?T ?call =>
        is_var T;
        let H' := fresh "H" in
        pose proof (existT_eq_type H) as H'; cbn in H';
        subst T;
        apply (@existT_eq_simplify Eff) in H
    | @existT Type ?Eff ?T ?call = _ =>
        is_var T;
        let H' := fresh "H" in
        pose proof (existT_eq_type H) as H'; cbn in H';
        subst T;
        symmetry in H;
        apply (@existT_eq_simplify Eff) in H;
        symmetry in H
    | @Eff.eq _ ?T _ ?call _ =>
        is_var T;
        let H' := fresh "H" in
        pose proof (Eff.eq_type H) as H';
        subst T;
        apply Eff.eq_call in H
    | @Eff.eq _ _ ?T _ ?call =>
        is_var T;
        let H' := fresh "H" in
        pose proof (Eff.eq_type H) as H';
        subst T;
        apply Eff.eq_call in H
    end.

  Tactic Notation "simplify_eff_eq" :=
    match goal with
    | H : Eff.eq _ _ |- _ => simplify_eff_eq in H
    | H : _ = @existT Type _ _ _ |- _ => simplify_eff_eq in H
    | H : @existT Type _ _ _ = _ |- _ => simplify_eff_eq in H
    end.


  Section Plus.
    Context {Eff : eff}.
    Context {Eff' : eff}.

    Definition plus : eff := λ T, (Eff T + Eff' T)%type.

    #[global] Instance plus_wf `{Wf Eff, Wf Eff'} : Wf plus.
    Proof using. intros T x. destruct x; naive_solver. Qed.

    #[global] Instance plus_dec `{Decision Eff, Decision Eff'} : Decision plus.
    Proof using.
      intros T T' c c'.
      refine (match c, c' with
              | inl a, inl b => dec_if (decide (a =ₑ b))
              | inr a, inr b => dec_if (decide (a =ₑ b))
              | _, _ => right _
              end);
        hauto lq:on simp+:simplify_eff_eq.
    Defined.

    #[global] Program Instance plus_exc `{Exc Eff, Exc Eff'} : Exc plus :=
      { exc := exc Eff + exc Eff';
        exc2eff e := match e return sigT plus with
                     | inl x => existT _ (inl (exc2eff x).T2)
                     | inr x => existT _ (inr (exc2eff x).T2)
                     end;
        eff2exc _ e := match e with
                     | inl x => inl <$> eff2exc x
                     | inr x => inr <$> eff2exc x
                     end
      }.
    Next Obligation.
      repeat case_split;
        (split; intro Heq; [simplify_eff_eq | rewrite fmap_Some in Heq]);
        sauto q:on dep:on use:exc_wf db:eff.
    Qed.
    Next Obligation.
      case_split;
        rewrite fmap_is_Some;
        rewrite exc_empty;
        reflexivity.
    Qed.

    (** Effect injection. Most of the time, the correct version is the left one,
        so it has a higher priority *)
    #[global] Instance subeff_plusl `{SubEff E Eff} : SubEff E plus | 10 :=
      λ _ e, inl (eff_inj e).
    #[global] Instance subeff_plusr `{SubEff E Eff'} : SubEff E plus | 20 :=
      λ _ e, inr (eff_inj e).
  End Plus.
  #[global] Arguments plus : clear implicits.

End Eff.
Export (hints, notations, ltac.notations) Eff.
#[export] Hint Rewrite @Eff.exc2call_wf : eff.
#[export] Hint Rewrite @Eff.ret_or_exc_exc2call : eff.
#[export] Hint Rewrite @Eff.eq_call_rew : eff.

Infix "+ₑ" := Eff.plus (at level 50, left associativity) : effect_scope.
Infix "=ₑ" := Eff.eq (at level 70, no associativity) : effect_scope.


Infix "=ₑ" := Eff.eq (at level 70, no associativity) : effect_scope.
Infix "=ₑ@{ A }" := (@Eff.eq A _)
  (at level 70, only parsing, no associativity) : effect_scope.


Notation "(=ₑ)" := Eff.eq (only parsing) : effect_scope.
Notation "( X =ₑ.)" := (Eff.eq X) (only parsing) : effect_scope.
Notation "(.=ₑ X )" := (λ Y, Y =ₑ X) (only parsing) : effect_scope.
Notation "(≠ₑ)" := (λ X Y, ¬X =ₑ Y) (only parsing) : effect_scope.
Notation "X ≠ₑ Y":= (¬X =ₑ Y) (at level 70, no associativity) : effect_scope.
Notation "( X ≠ₑ.)" := (λ Y, X ≢ Y) (only parsing) : effect_scope.
Notation "(.≠ₑ X )" := (λ Y, Y ≢ X) (only parsing) : effect_scope.

Notation "(=ₑ@{ Eff } )" := (@Eff.eq Eff _ _) (only parsing) : effect_scope.
Notation "(≠ₑ@{ Eff } )" := (λ X Y, ¬X =ₑ@{Eff} Y) (only parsing) : effect_scope.
Notation "X ≠ₑ@{ Eff } Y":= (¬X =ₑ@{ Eff } Y)
  (at level 70, only parsing, no associativity) : effect_scope.

(** * Tactics about effects *)

(** A version of [decide_eq] but for [Eff.eq]. Similarly, it expects the effect
    type (Inductive) to be destroyed before the call *)
Ltac decide_eff_eq :=
  lazymatch goal with
  | |- Decision (?f ?a ?b ?c ?d ?e ?f ?g =ₑ ?f ?a' ?b' ?c' ?d' ?e' ?f' ?g') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      decide_field d d'; [ .. |
      decide_field e e'; [ .. |
      decide_field f f'; [ .. |
      decide_field g g'; [ .. |
      left; reflexivity]]]]]]]
  | |- Decision (?f ?a ?b ?c ?d ?e ?f =ₑ ?f ?a' ?b' ?c' ?d' ?e' ?f') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      decide_field d d'; [ .. |
      decide_field e e'; [ .. |
      decide_field f f'; [ .. |
      left; reflexivity]]]]]]
  | |- Decision (?f ?a ?b ?c ?d ?e =ₑ ?f ?a' ?b' ?c' ?d' ?e') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      decide_field d d'; [ .. |
      decide_field e e'; [ .. |
      left; reflexivity]]]]]
  | |- Decision (?f ?a ?b ?c ?d =ₑ ?f ?a' ?b' ?c' ?d') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      decide_field d d'; [ .. |
      left; reflexivity]]]]
  | |- Decision (?f ?a ?b ?c =ₑ ?f ?a' ?b' ?c') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      decide_field c c'; [ .. |
      left; reflexivity]]]
  | |- Decision (?f ?a ?b =ₑ ?f ?a' ?b') =>
      decide_field a a'; [ .. |
      decide_field b b'; [ .. |
      left; reflexivity]]
  | |- Decision (?f ?a =ₑ ?f ?a') =>
      decide_field a a'; [ .. |
      left; reflexivity]
  | |- Decision (?f =ₑ ?f) => left; reflexivity
  | |- Decision (_ =ₑ _) => right; discriminate
  end.

(** * Generic noreturn type

This is intended to mark explicitly effect that are not returning when defining
custom effects *)

Definition noreturn := False.

#[global] Instance emptyT_noreturn : EmptyT noreturn.
Proof. inversion 1. Qed.

(** * Non determinism effect *)

(** MChoice is the standard non determinism effect, doing a n-wise choice
    n can be 0 in which case this correspond to a no-behavior execution *)
Inductive MChoice : eff := ChooseFin (n : nat) : MChoice (fin n).

#[global] Instance MChoice_EffWf : Eff.Wf MChoice.
Proof. intros T [[]]; tc_solve. Qed.

Equations MChoice_EffDec : Eff.Decision MChoice :=
  MChoice_EffDec _ _ (ChooseFin n) (ChooseFin n') := dec_if (decide (n = n')).
Solve All Obligations with hauto lq:on.
#[global] Existing Instance MChoice_EffDec.

Inductive discard_type := discard_value.

(* Not using unit a exception type to be sure that discard is never confused
   with failing, as mfail is implemented as mthrow unit *)
#[global] Program Instance MChoice_EffExc : Eff.Exc MChoice :=
  { exc := discard_type;
    exc2eff := λ _, existT _ (ChooseFin 0);
    eff2exc := λ T c,
      match c return option discard_type with
      | ChooseFin 0 => Some discard_value
      | _ => None
      end
  }.
Solve All Obligations with sauto.

(** Special case of MCall for MChoice *)
Notation MChoose := (MCall MChoice).
Definition mchoose `{MChoose M} (n : nat) : M (fin n) := mcall (ChooseFin n).
Definition mdiscard `{MCall MChoice M} `{FMap M} {A} : M A :=
  mcall (ChooseFin 0) |$> (λ x, match (x : fin 0) with end).

(** Helper to non-deterministically choose in a list *)
Definition mchoosel `{MChoose M} `{FMap M} {A} (l : list A) : M A :=
  mchoose (length l) |$> ((list_to_vec l) !!!.).


(** * State effect *)
Inductive MState {St : Type} : eff :=
| MSet (val : St) : MState unit
| MGet : MState St.
Arguments MState : clear implicits.

#[global] Instance MState_EffWf `{Inhabited St} : Eff.Wf (MState St).
Proof. intros _ []; tc_solve. Qed.

Equations MState_EffDec `{EqDecision St} : Eff.Decision (MState St) :=
  MState_EffDec _ _ (MSet s) (MSet s') := dec_if (decide (s = s'));
  MState_EffDec _ _ MGet MGet := left _;
  MState_EffDec _ _ _ _ := right _.
Solve All Obligations with hauto lq:on.
#[global] Existing Instance MState_EffDec.

Notation mGet := (mcall MGet).
Definition mget `{MCall (MState St) M, FMap M} {T} (proj : St → T) : M T :=
  mGet |$> proj.

Notation mSetv s := (mcall (MSet s)).
Definition mSet `{MCall (MState St) M, MBind M} (upd : St → St) : M unit :=
  s ← mGet;
  mSetv (upd s).
Definition mset `{MCall (MState St) M, MBind M} {T} (proj : St → T)
  `{Setter St T proj} (upd : T → T) : M unit :=
  mSet (set proj upd).
Definition msetv `{MCall (MState St) M, MBind M} {T} (proj : St → T)
  `{Setter St T proj} (val : T) : M unit :=
  mset proj (λ _, val).
