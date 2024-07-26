(** This file provide support for handling algebraic effects.*)

Require Import CBase CBool CDestruct.
Require Import Options.
From stdpp Require Import base.
From stdpp Require Import fin.
From stdpp Require Import vector.


(** * Base effect definitions *)

(** An effect is a type that has an associated function that gives the return
    type. We fix the universe of all effects because they are fixed anyway by
    monad universe constraints in stdpp, but then it's easier to debug with a
    named universe. *)
Universe e.
Definition eff := Type@{e}.
Bind Scope type_scope with eff.

Set Typeclasses Unique Instances.
(** The effect typeclass, declares a type as an effect and provide [eff_ret],
    the return type function. *)
Class Effect (Eff : eff) := eff_ret : Eff → Type@{e}.
#[export] Hint Mode Effect ! : typeclass_instances.
Unset Typeclasses Unique Instances.


(** Generic interface for calling an algebraic effect in a monad *)
Class MCall (Eff : eff) `{Effect Eff} (M : Type → Type) :=
  mcallM : ∀ call : Eff, M (eff_ret call).
Arguments mcallM {_ _} _ {_} _ : assert.
#[export] Instance: Params (@mcallM) 2 := {}.
#[export] Hint Mode MCall - - ! : typeclass_instances.


(** [MCall'] is a type inference hack to be able to call [mcallM] without
    specifying the monad, otherwise Coq type inference fails to propagate the
    ambient monad type back. Nobody should implement this typeclass directly. *)
Class MCall' (Eff : eff) `{Effect Eff} (MEff : Type) (call : Eff) :=
  mcall : MEff.
Arguments mcall {_ _ _} _ {_}.
#[export] Instance: Params (@mcall) 2 := {}.
#[export] Hint Mode MCall' - - ! ! : typeclass_instances.

Hint Extern 1 (@MCall' ?Eff ?H (?M ?T) ?call) =>
       notypeclasses refine (@mcallM Eff H M _ call): typeclass_instances.

(** Call a non returning effect. This is not necessarily a failure, so this is
    not directly linked to [MThrow] *)
Definition mcall_noret `{MBind M, MCall Eff M} (call : Eff)
   `{EmptyT (eff_ret call)} {A} : M A :=
  x ← mcall call;
  match emptyT x with end.


(** * Sub-Effects and effect conversion *)

(** Transforming an effect into another effect requires giving a conversion for
    the return value the other way. [repl_eff] is a type that packages this *)
Definition repl_eff `{Effect Eff} (call : Eff) Eff' `{Effect Eff'} :=
  {call' : Eff' & eff_ret call' → eff_ret call}.
(** Helper constructor for [repl_eff]. Generally f should be the identity
    function when matching over an event *)
Definition ReplEff' `{Effect Eff, Effect Eff'} {call : Eff} (call' : Eff')
  (f : eff_ret call' → eff_ret call) : repl_eff call Eff' :=
  existT call' f.
Notation ReplEff call := (ReplEff' call (λ x, x)).
Definition mcall_repl `{Effect Eff, Effect Eff', MCall Eff' M, FMap M}
  {call : Eff} (reff : repl_eff call Eff') : M (eff_ret call) :=
  mcall reff.T1 |$> reff.T2.

(** Sub-Effect judgment: This provide a canonical effect injection relation.
    There is no associated proof than this is actually an injection*)
Class SubEff (Eff Eff': eff) `{Effect Eff, Effect Eff'} :=
  sub_eff : ∀ call : Eff, repl_eff call Eff'.
Arguments sub_eff {_ _ _ _ _} _ : assert.
#[export] Instance: Params (@sub_eff) 5 := {}.
#[export] Hint Mode SubEff ! ! ! ! : typeclass_instances.

#[global] Instance SubEff_default Eff `{Effect Eff} : SubEff Eff Eff | 100 :=
  λ call, ReplEff call.

(** When calling an effect in a monad that support a bigger effect, this will
    automatically search of a [SubEff] relation to do the adequate effect
    injection *)
Definition MCall_SubEff Eff Eff'
  `{Effect Eff, MCall Eff' M, !SubEff Eff Eff', FMap M} : MCall Eff M :=
  λ call, mcall_repl (sub_eff call).

#[export] Hint Extern 20 (MCall ?E ?M) =>
  tryif (is_evar E) then fail else class_apply MCall_SubEff
  : typeclass_instances.


(** * Effect typeclasses *)

(** ** Effect wellformedness

An effect is wellformed if we have DecisionT for all type that it could ask as
return type. In other words if for all effects we can decide if has an empty
return type or not *)
Class EffWf `{Effect Eff} := eff_wf : ∀ call : Eff, DecisionT (eff_ret call).
#[global] Arguments EffWf _ {_}.
#[global] Hint Mode EffWf ! ! : typeclasses_instances.
#[export] Existing Instance eff_wf.


(** ** Effect transportability

An effect is computably transportable if all the return value of the effect are
transportable, even using an opaque effect equality. This is just implementing
[CTrans] on [eff_ret] *)
Class EffCTrans `{Effect Eff} := ctrans_eff : CTrans (eff_ret (Eff := Eff)).
#[global] Arguments EffCTrans _ {_}.
#[global] Hint Mode EffCTrans ! ! : typeclasses_instances.
#[export] Existing Instance ctrans_eff.

Class EffCTransSimpl `{EffCTrans Eff} := ctrans_simpl_eff :
    CTransSimpl (eff_ret (Eff := Eff)).
#[global] Arguments EffCTransSimpl _ {_ _}.
#[global] Hint Mode EffCTransSimpl ! ! ! : typeclasses_instances.
#[export] Existing Instance ctrans_simpl_eff.

(** * Effect sums

This allows to combine two effects in a single effect, mainly to instantiate
objects like free monads *)

Section Plus.
  Context Eff `{Effect Eff} Eff' `{Effect Eff'}.
  #[export] Instance Effect_sum : Effect (Eff + Eff') :=
    λ call, match call with
            | inl calll => eff_ret calll
            | inr callr => eff_ret callr
            end.

  #[export] Instance EffWf_sum `{!EffWf Eff} `{!EffWf Eff'}: EffWf (Eff + Eff').
  Proof. intros []; cbn; tc_solve. Defined.

  #[export] Instance EffCTrans_sum `{!EffCTrans Eff} `{!EffCTrans Eff'} :
    EffCTrans (Eff + Eff').
  Proof. intros [] [] eq er; cbn in *.
         all: try abstract discriminate.
         all: eapply ctrans;[|eassumption].
         all: abstract naive_solver.
  Defined.

  #[export] Instance SubEff_suml : SubEff Eff (Eff + Eff') | 100 :=
    λ x, ReplEff (inl x).

  #[export] Instance SubEff_sumr : SubEff Eff' (Eff + Eff') | 100 :=
    λ x, ReplEff (inr x).
End Plus.


(** * Non determinism effect: [MChoice] *)

(** MChoice is the standard non determinism effect.
    [ChooseFin n] is doing a [n]-wise choice.
    [n] can be 0 in which case this correspond to a no-behavior execution *)
Inductive MChoice : eff := ChooseFin (n : nat).
#[export] Instance MChoice_ret : Effect MChoice := λ '(ChooseFin n), fin n.

#[export] Instance MChoice_EffWf : EffWf MChoice.
Proof. intros []. cbn. tc_solve. Defined.

#[export] Instance MChoice_EffCTrans : EffCTrans MChoice.
Proof.
  intros [] [] eq er.
  cbn in *.
  eapply ctrans; [|eassumption].
  abstract (naive_solver).
Defined.

#[export] Instance MChoice_EffCTransSimpl : EffCTransSimpl MChoice.
Proof. intros [] ? ?. cbn. by simp ctrans. Qed.

#[export] Instance MChoice_eq_dec : EqDecision MChoice.
Proof. solve_decision. Defined.

(** ** [MChoice] helper functions *)

(** Special case of MCall for MChoice *)
Notation MChoose := (@MCall MChoice MChoice_ret).
Definition mchoose `{!MChoose M} (n : nat) : M (fin n) := mcall (ChooseFin n).
Definition mdiscard `{MChoose M, FMap M} {A} : M A :=
  mcall (ChooseFin 0) |$> (λ x, match (x : fin 0) with end).

(** Helper to non-deterministically choose in a list *)
Definition mchoosel `{MChoose M, FMap M} {A} (l : list A) : M A :=
  mchoose (length l) |$> ((list_to_vec l) !!!.).

(** Same as [guard] but discard the execution if the proposition is false  *)
Definition guard_discard `{MChoose M, FMap M, MRet M} P `{Decision P} : M P :=
  match decide P with
  | left x => mret x
  | right _ => mdiscard
  end.

Notation guard_discard' P := (guard_discard P;; mret ()).

Tactic Notation "case_guard_discard" "as" ident(Hx) :=
  match goal with
  | H : context C [@guard_discard ?M ?C ?F ?R ?P ?dec] |- _ =>
      change (@guard_discard M C F R P dec) with (
        match @decide P dec with
          left H' => @mret M R P H' | _ => @mdiscard M C F P end) in *;
      destruct_decide (@decide P dec) as Hx

  | |- context C [@guard_discard ?M ?C ?F ?R ?P ?dec] =>
      change (@guard_discard M C F R P dec) with (
        match @decide P dec with
          left H' => @mret M R P H' | _ => @mdiscard M C F P end) in *;
      destruct_decide (@decide P dec) as Hx
  end.
Tactic Notation "case_guard_discard" :=
  let H := fresh in case_guard_discard as H.


(** * State effect: [MState] *)

(** This is the standard state effect with a getter and a setter. The state must
    be in or below the effect universe *)
Inductive MState {St : Type@{e}} : eff :=
| MSet (val : St) : MState
| MGet : MState.
Arguments MState : clear implicits.

#[export] Instance MState_ret St : Effect (MState St) :=
  λ call, match call with
          | MSet _ => unit
          | MGet => St
          end.

#[export] Instance MState_EffWf `{Inhabited St} : EffWf (MState St).
Proof. intros []; cbn; tc_solve. Defined.

#[export] Instance MState_EffCTrans St : EffCTrans (MState St).
Proof.
  intros [] [].
  all: try (abstract discriminate).
  all: cbn in *.
  all: intros; assumption.
Defined.

#[export] Instance MState_EffCTransSimpl St : EffCTransSimpl (MState St).
Proof. by intros [] ? ?. Qed.

#[export] Instance MState_eq_dec `{EqDecision St} : EqDecision (MState St).
Proof. solve_decision. Defined.

(** ** [MState] helper functions

- [mGet] : get the whole state
- [mget field] : get the field [field] of the state
- [mSet upd] : update the state with the function [upd]
- [mSetv val] : update the state with the value [val]
- [mset field upd] : update the state field [field] with the function [upd]
- [msetv field val] : update the state field [field] with the value [val] *)

Notation mGet := (mcall MGet).
Definition mget `{!MCall (MState St) M, FMap M} {T} (proj : St → T) : M T :=
  mGet |$> proj.

Notation mSetv s := (mcall (MSet s)).
Definition mSet `{!MCall (MState St) M, MBind M} (upd : St → St) : M unit :=
  s ← mGet;
  mSetv (upd s).
Definition mset `{!MCall (MState St) M, MBind M} {T} (proj : St → T)
  `{Setter St T proj} (upd : T → T) : M unit :=
  mSet (set proj upd).
Definition msetv `{!MCall (MState St) M, MBind M} {T} (proj : St → T)
  `{Setter St T proj} (val : T) : M unit :=
  mset proj (λ _, val).
