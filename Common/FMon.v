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
Require Import Program.Equality.
Require Import Common.
From stdpp Require Import option.

(* Reexporting Effects. Using FMon implies using Effects *)
Require Export Effects.

(* Needed for setoid rewrite along cequiv that is defined as an Equiv instance *)
#[export] Typeclasses Transparent Equiv.



(** * Free monad

This is a custom implementation of a free monad, which is basically a finite
itree (thus inductive, not coinductive). Therefore, it cannot represent
non-termination. *)

(*** Rationale: it's ok to do that, and later to consider only finite traces because the intended use is for the semantics of single instructions. ***)
                            


Section FMon.
  Context {Eff : eff}.
  Context {ER : Effect Eff}.
  Context {ED : EqDecision Eff}.
  Context {Wf : EffWf Eff}.
  Context {CT : EffCTrans Eff}.
  Context {CTS : EffCTransSimpl Eff}.

  (** This implementation is not very computationally efficient in case of
      repeated binds, but has the advantage of being canonical, e.g. trace
      equivalence is Leibtniz equality (with functional extensionality)*)
  Inductive fMon {A : Type} :=
  | Ret (ret : A)
  | Next (call : Eff) (k : eff_ret call → fMon).
  Arguments fMon : clear implicits.

  #[global] Instance fMon_ret : MRet fMon := @Ret.

  #[global] Instance fMon_bind : MBind fMon :=
    λ _ _, fix bind f ma :=
      match ma with
      | Ret x => f x
      | Next oc k => Next oc (λ x, bind f (k x)) end.

  #[global] Instance fMon_join : MJoin fMon :=
    λ _ mmx, mx ← mmx; mx.

  #[global] Instance fMon_fmap : FMap fMon :=
    λ _ _, fix map f ma :=
      match ma with
      | Ret x => Ret (f x)
      | Next oc k => Next oc (λ x, map f (k x)) end.

  #[global] Instance fMon_call : MCall Eff fMon := λ out, Next out Ret.

  (** * Events *)

  (** A event of an effect type is a combination of an effect call and its
      result *)
  Record fEvent := FEvent {fcall : Eff; fret : eff_ret fcall}.
  Infix "&→" := FEvent (at level 45, no associativity).

  Lemma fEvent_call_eq `{Effect Eff} (call call' : Eff) ret ret' :
    call &→ ret = call' &→ ret' → call = call'.
  Proof. cdestruct call |- ***. Qed.

  Lemma fEvent_ret_JMeq `{Effect Eff} (call call' : Eff) ret ret' :
    call &→ ret = call' &→ ret' → ret =ⱼ ret'.
  Proof. cdestruct call |- ***. Qed.

  Lemma fEvent_eq_spec_JMeq `{Effect Eff} (call call' : Eff) ret ret' :
    call &→ ret = call' &→ ret' ↔ call = call' ∧ ret =ⱼ ret'.
  Proof. cdestruct call |- *** #CDestrSplitGoal. Qed.

  (** Decide if a [call] matches an event [ev] and return the return value with
      the correct type if it matches *)
  Definition event_extract (ev : fEvent) (call : Eff) : option (eff_ret call) :=
    match decide (ev.(fcall) = call) with
    | left e => Some (ctrans e ev.(fret))
    | right _ => None
    end.

  Lemma event_extract_Some ev (call : Eff) ret :
    event_extract ev call = Some ret ↔ ev = (call &→ ret).
  Proof using CTS.
    unfold event_extract.
    destruct ev. cbn in *.
    case_decide.
    - subst. simp ctrans. naive_solver.
    - naive_solver.
  Qed.
  Hint Rewrite @event_extract_Some : fmon.

  Lemma event_extract_None ev (call : Eff) :
    event_extract ev call = None ↔ fcall ev ≠ call.
  Proof using CTS.
    rewrite eq_None_not_Some.
    apply not_iff_compat.
    unfold is_Some.
    setoid_rewrite event_extract_Some.
    destruct ev. naive_solver.
  Qed.
  Hint Rewrite @event_extract_None : fmon.

  (** * Event as transitions

  One can see a free monad (or an itree) as a state transtion system where the
  free monad value itself is the state and events are transitions. *)

  (** [fsteps] describe the result of a list of transitions, labelled by events in
      the list, allowed by the monad.  For a single transition, there is an [fstep] notation that uses that on a singleton list, instead of a separate predicate. 

      [fsteps f evs f']  iff free monad value [f] can do a sequence of transitions, labelled by the events of the list [evs], to  free monad value [f'].

      In the rhs of the body of [FMCons], the monadic value [Next call k] can do a transition with label [call &→ ret], with the same [call] and an arbitrary return value [ret], and then the rest of the events [tl], to reach monadic value [f'], reached by applying the continuation [k] to that return value [ret]. 

 *)
  Inductive fsteps {A : Type} : fMon A → list fEvent → fMon A → Prop :=
  | FMNil f : fsteps f [] f
  | FMCons call k ret tl f' :
    fsteps (k ret) tl f' → fsteps (Next call k) ((call &→ ret) :: tl) f'.
  Notation fstep f ev f' := (fsteps f [ev] f').
  Hint Constructors fsteps : fmon.

  Lemma fsteps_nil {A} (f f' : fMon A) :
    fsteps f [] f' ↔ f = f'.
  Proof. sauto. Qed.
  Hint Rewrite @fsteps_nil : fmon.

  Lemma fsteps_app {A} l l' (f f' : fMon A) :
    fsteps f (l ++ l') f' ↔ ∃ f'', fsteps f l f'' ∧ fsteps f'' l' f'.
  Proof.
    split.
    - generalize dependent f.
      induction l; cbn.
      + sauto lq:on.
      + intros f H. dependent destruction H.
        sauto lq:on.
    - intros (f'' & H & H').
      induction H; hauto.
  Qed.

  Definition fsteps_cons {A} ev tl (f f' : fMon A) :
    fsteps f (ev :: tl) f' ↔ ∃ f'', fstep f ev f'' ∧ fsteps f'' tl f'
  := fsteps_app [ev] tl f f'.
  Lemma fsteps_Next_cons {A} call k ret tl (f : fMon A) :
      fsteps (Next call k) ((call &→ ret) :: tl) f ↔ fsteps (k ret) tl f.
    Proof.
      split; intro H.
      - by dependent destruction H.
      - by constructor.
  Qed.
  Hint Rewrite @fsteps_Next_cons : fmon.

  Lemma fsteps_Ret_cons {A} ret l (f : fMon A) :
    fsteps (Ret ret) l f ↔ l = [] ∧ f = Ret ret.
  Proof.
    split; intro H.
    - by dependent destruction H.
    - hauto ctrs:fsteps.
  Qed.

  (** ** Replay function *)

  (** [freplay] is a computational version of [fsteps]. It takes a free monad
      and a list of events and tries to replay it. It might fail of course *)
  Equations freplay {A} (f : fMon A) (l : list fEvent) : option (fMon A) :=
    freplay f [] := Some f;
    freplay (Next call k) (ev :: tl)  with event_extract ev call := {
      | Some ret => freplay (k ret) tl
      | None => None
      } ;
    freplay _ _ := None.

  Lemma freplay_ind A
    (P : fMon A → list fEvent → option (fMon A) → Prop)
    (Pempty: ∀ f : fMon A, P f [] (Some f))
    (PRetNone: ∀ ret ev tl, P (Ret ret) (ev :: tl) None)
    (Pcallmatch: ∀ call k ret tl o,
       freplay (k ret) tl = o →
       P (k ret) tl o → P (Next call k) (call &→ ret :: tl) o)
    (Pcallnomatch: ∀ call k call' ret' tl ,
       call ≠ call' → P (Next call k) (call' &→ ret' :: tl) None) f l :
    P f l (freplay f l).
    funelim (freplay _ _); sauto db:fmon lq:on.
  Qed.
  Remove Hints FunctionalElimination_freplay : typeclass_instances.
  #[global] Instance FunctionalElimination_freplay' A :
    FunctionalElimination (@freplay A) _ 5 := @freplay_ind A.

  Lemma freplay_Some l {A} (f f' : fMon A) :
    freplay f l = Some f' ↔ fsteps f l f'.
  Proof using CTS. funelim (freplay _ _); sauto db:fmon lq:on dep:on. Qed.

  Lemma freplay_None l {A} (f f' : fMon A) :
    freplay f l = None ↔ ∀ f', ¬ fsteps f l f'.
  Proof using CTS.
    setoid_rewrite <- freplay_Some.
    destruct (freplay _ _); naive_solver.
  Qed.

  (** ** Free monad traces

  The type of finite traces over fMon. These traces are partial and can stop
  anywhere, including having or not an incomplete next event. *)

  (*** Rationale: we define traces as a pair of a list of events and a trace end, rather than defining a new list type with the trace ends in place of Nil, as otherwise we need to redefine all the standard list things. ***) 

  (** *** Trace ends *)

  (** A trace end is either nothing, a return value or an incomplete event i.e a
      call without a return value *)
  Inductive fTraceEnd {A : Type} :=
  | FTERet (a : A)                     (* Terminated            *)
  | FTENothing                         (* PartialClean          *)
  | FTEStop (call : Eff).              (* PartialIncompleteCall *)
  Arguments fTraceEnd : clear implicits.

  #[export] Instance fTraceEnd_eqdec `{EqDecision A} : EqDecision (fTraceEnd A).
  Proof using ED. solve_decision. Defined.

  (** Definition of trance end matching a value of the monad *)
  Definition fmatch_end {A} (f : fMon A) (tre : fTraceEnd A) :=
    match tre with
    | FTENothing => True
    | FTERet r => if f is Ret r' then r = r' else False
    | FTEStop call => if f is Next call' _ then call = call' else False
    end.

  #[export] Instance fmatch_end_dec `{EqDecision A}
    (f : fMon A) tre : Decision (fmatch_end f tre).
  Proof using ED. unfold fmatch_end. tc_solve. Defined.

  Lemma fmatch_end_ret `(r : A) : fmatch_end (Ret r) (FTERet r).
  Proof. done. Qed.
  Hint Resolve fmatch_end_ret : fmon.

  Lemma fmatch_end_stop {A} (call : Eff) k :
    fmatch_end (A := A) (Next call k) (FTEStop call).
  Proof. done. Qed.
  Hint Resolve fmatch_end_stop : fmon.

  (** *** Traces *)

  (** A trace is a list of events and an end. *)
  Definition fTrace A : Type := list fEvent * fTraceEnd A.
                                                                             
  #[global] Typeclasses Transparent fTrace.
  Notation FTRet a := ([], FTERet a).
  Notation FTStop call := ([], FTEStop call).
  Notation FTNothing := ([], FTENothing).

  (** We keep the defintion of a trace matching a monad value as an inductive
  for convenience *)
  Inductive fmatch {A : Type} : fMon A → fTrace A → Prop :=
  | FTMNothing f : fmatch f FTNothing
  | FTMRet a : fmatch (Ret a) (FTRet a)
  | FTMStop call k : fmatch (Next call k) (FTStop call)
  | FTMNext call k ret tl tre :
    fmatch (k ret) (tl, tre) → fmatch (Next call k) ((call &→ ret) :: tl, tre).

  (** Matching a whole trace is the same as running all the transitions and then
      matching the end of the trace *)
  Lemma fmatch_fsteps {A} (f : fMon A) tr :
    fmatch f tr ↔ ∃ f', fsteps f tr.1 f' ∧ fmatch_end f' tr.2.
  Proof.
    split.
    - induction 1; hauto l:on db:fmon.
    - destruct tr. cbn. intros [f' [FS FME]].
      induction FS; sauto.
  Qed.

  (** [fmatch] is decidable which is very important for the rest of this project *)
  Equations fmatch_dec `{EqDecision A}
    (f : fMon A) tr : Decision (fmatch f tr) :=
    fmatch_dec f (l, tre)
      with inspect (freplay f l) := {
      | Some f' eq: _ =>
          dec_if (decide (fmatch_end f' tre))
      | None eq: _ => right _
      }.
  Solve All Obligations with
    intros; cbn in *;
    rewrite fmatch_fsteps;
    setoid_rewrite <- freplay_Some;
    naive_solver.

  Lemma fmatch_next A (call : Eff) (k : eff_ret call → fMon A) (ret : eff_ret call) tl tre:
    fmatch (Next call k) (call &→ ret :: tl, tre)
      ↔ fmatch (k ret) (tl, tre).
  Proof using.
    repeat rewrite fmatch_fsteps.
    by setoid_rewrite fsteps_Next_cons.
  Qed.

  (** *** Full traces *)

    (** TP: deprecated notion **)
  (** Full trace are traces that only stop on a non returning effect *)
  Definition ftfull {A} (ft : fTrace A) :=
    match ft.2 with
    | FTEStop call => eff_ret call → False
    | FTERet _ => True
    | FTENothing => False
    end.
  Lemma ftfull_FTRet {A} (a : A) : ftfull (FTRet a).
  Proof using. naive_solver. Qed.
  Hint Resolve ftfull_FTRet : fmon.
  Lemma ftfull_FTStop {A} (call : Eff) :
    (eff_ret call → False) → ftfull (A := A) (FTStop call).
  Proof using. naive_solver. Qed.
  Hint Resolve ftfull_FTStop : fmon.
  Lemma ftfull_FTStop_spec {A} (call : Eff) :
    ftfull (A := A) (FTStop call) ↔ (eff_ret call → False).
  Proof using. split; [sfirstorder | apply ftfull_FTStop]. Qed.
  Hint Rewrite @ftfull_FTStop_spec : fmon.

  Equations ftfull_dec {A} `{!EffWf Eff} (ft : fTrace A) : Decision (ftfull ft) :=
    ftfull_dec (_, FTEStop call) with decideT (eff_ret call) := {
      | inleft _ => right _
      | inright _ => left _
      };
    ftfull_dec (_, FTENothing) := right _;
    ftfull_dec (_, FTERet) := left _.
  Solve All Obligations with unfold ftfull; sfirstorder.


  (** A full trace always exists for any free monad value *)
  Lemma ftrace_ftfull_exists {A} (m : fMon A) : ∃ t, fmatch m t ∧ ftfull t.
  Proof using Wf.
    setoid_rewrite fmatch_fsteps.
    unfold fTrace. apply exists_pair.
    induction m as [|?? IH].
    - repeat (eexists || split || auto with fmon || cbn).
    - destruct (decideT (eff_ret call)) as [e | ?].
      + specialize (IH e). sauto q:on dep:on db:pair.
      + repeat (eexists || split || auto with fmon || cbn).
  Qed.

  (** Two values of the free monad that generate the same sets of full traces are
      equal *)
  Theorem fmon_eq_via_ftrace_ftfull A m1 m2:
    (∀ trc : fTrace A, ftfull trc → fmatch m1 trc ↔ fmatch m2 trc) → m1 = m2.
  Proof using Wf.
    generalize dependent m2.
    induction m1 as [ret| call k IH]; intros m2 Ht.
    - specialize (Ht ([], FTERet ret)). hauto l:on inv:fmatch db:fmon.
    - destruct m2 as [ret2 | call2 k2].
      + clear IH. specialize (Ht ([], FTERet ret2)).
        hauto l:on inv:fmatch db:fmon.
      + destruct (ftrace_ftfull_exists (Next call k)) as [tr [Htr Hfull]].
        pose proof Htr as Htr2.
        apply Ht in Htr2. 2: done.
        dependent destruction Htr; dependent destruction Htr2;
          cbn in *; first done.
        all: f_equal.
        all: apply functional_extensionality.
        all: intro ret'.
        * done.
        * apply IH.
          intros [tl' tre'].
          specialize Ht with (call &→ ret' :: tl', tre').
          by setoid_rewrite fmatch_next in Ht.
  Qed.

  Corollary fmon_eq_via_ftrace A m1 m2:
    (∀ trc : fTrace A, fmatch m1 trc ↔ fmatch m2 trc) → m1 = m2.
  Proof using Wf. intro. apply fmon_eq_via_ftrace_ftfull. naive_solver. Qed.

  (** ** Free monad effect handling *)

  (** A handler is a function that describes how to interpret all effects of [Eff]
      in a monad [M] *)
  Definition fHandler (M : Type → Type) := ∀ call : Eff, M (eff_ret call).

  (** If the target monad already supports the effect, then there is a trivial
      handler *)
  Definition mcall_fHandler `{MC : !MCall Eff M} : fHandler M := mcallM M.
  #[export] Typeclasses Transparent mcall_fHandler.
  #[global] Arguments mcall_fHandler {_ _} _ /.

  (** Free monad interpret: Interprets a free monad over Eff in an arbitrary monad, using a handler *)
  Fixpoint finterp `{MR: MRet M, MB: MBind M} (handler : fHandler M)
    [A] (mon : fMon A) : M A :=
    match mon with
    | Ret a => (mret a : M A)
    | Next call k => ret ←@{M} handler call; finterp handler (k ret)
    end.

  (** Interpreting inside the free monad itself is the identity *)
  Lemma finterp_mcall A (f : fMon A) : finterp mcall_fHandler f = f.
  Proof using. induction f; hauto l:on use:functional_extensionality.
  Qed.
  Hint Rewrite finterp_mcall : fmon.
End FMon.

Arguments fMon _ {_}.
Arguments fEvent _ {_}.
Arguments fTraceEnd :clear implicits.
Arguments fTrace _ {_}.
Arguments fHandler _ {_}.

Infix "&→" := FEvent (at level 45, no associativity).
Infix "&→@{ Eff }" := (@FEvent Eff _)
                        (at level 45, only parsing, no associativity).

Notation fstep f ev f' := (fsteps f [ev] f').
Notation FTRet a := ([], FTERet a).
Notation FTStop call := ([], FTEStop call).
Notation FTNothing := ([], FTENothing).


(** Helper for the following Hint Extern. The goal is that in case of an fEvent
    equality, where the return values happen to be of the same type, then
    [call &→ ret = call' &→ ret'] can be simplified to
    [call = call' ∧ ret = ret'] *)
Lemma fEvent_eq_helper `{Effect Eff} (call call' : Eff) ret ret' P :
  ret =ⱼ ret' ↔ P →
  call &→ ret = call' &→ ret' ↔ call = call' ∧ P.
Proof. intros <-. apply fEvent_eq_spec_JMeq. Qed.

(** Perform the CDestruct simplification described above *)
#[export]
Hint Extern 2
  (CDestrSimpl _
     (@FEvent ?Eff ?ER ?call ?ret = @FEvent ?Eff ?ER ?call' ?ret') ?Q) =>
       eunify Q (call = call' ∧ ret = ret'); (* we want to unify without typeclass opacity *)
       constructor;
       refine (@fEvent_eq_helper Eff ER call call' ret ret' _ _);
       exact (JMeq_simpl _ ret ret') : typeclass_instances.


(** Create a handler for a sum of effects from handler for each individual
    effects *)
Definition fHandler_plus `{Effect Effl, Effect Effr, MRet M, MBind M}
    (fl : fHandler Effl M) (fr : fHandler Effr M) : fHandler (Effl + Effr) M :=
  λ call, match call with
          | inl l => fl l
          | inr r => fr r
          end.
Infix "+ₕ" := fHandler_plus (at level 50, left associativity).

(** * Choice monad: Non deterministic free monad *)
Notation Nextl e := (Next (inl e)).
Notation Nextr e := (Next (inr e)).

Section CMon.
  Context {Eff : eff}.
  Context {ER : Effect Eff}.
  Context {ED : EqDecision Eff}.
  Context {Wf : EffWf Eff}.
  Context {CT : EffCTrans Eff}.
  Context {CTS : EffCTransSimpl Eff}.

  (** A choice monad is just a free monad with additional choice effects. The
      only difference is the theory around it (equivalence, trace matching, etc.) *)
  Definition cMon := fMon (Eff + MChoice).
  #[export] Typeclasses Transparent cMon.

  (** Interprets the effect in a monad supporting non-determinism *)
  Definition cinterp `{MR: MRet M, MB: MBind M, MCh: MChoose M}
      (f : fHandler Eff M) [A] (c : cMon A) : M A :=
    finterp (f +ₕ mcall_fHandler) c.

  (** ** Matching a choice monad with a trace that does not contain choice
         points *)
  Inductive cmatch {A : Type} : cMon A → fTrace Eff A → Prop :=
  | CTMNothing f : cmatch f FTNothing
  | CTMRet a : cmatch (Ret a) (FTRet a)
  | CTMStop (call : Eff) k : cmatch (Nextl call k) (FTStop call)
  | CTMNext (call : Eff) k ret tl tre :
    cmatch (k ret) (tl, tre) → cmatch (Nextl call k) (call &→ ret :: tl, tre)
  | CTMChoose n i k tr : cmatch (k i) tr →
    cmatch (Nextr (ChooseFin n) k) tr.

  Lemma cmatch_Nextl A (call : Eff) (k : eff_ret call → cMon A)
    (ret : eff_ret call) tl tre:
    cmatch (Nextl call k) (call &→ ret :: tl, tre)
      ↔ cmatch (k ret) (tl, tre).
  Proof using.
    split.
    - intro H. by dependent destruction H.
    - by constructor.
  Qed.

  (** Decide a cmatch: This is a bit dumb, it will try every possible
      non-deterministic choice until one match succeeded or all failed. However
      in practice, if concrete value of cMon avoid doing choice before doing
      very long identical sequences of calls in all branches, this shouldn't be
      that bad. *)
  Equations cmatch_dec `{EqDecision A} (f : cMon A) tr
    : Decision (cmatch f tr) :=
    cmatch_dec _ FTNothing := left _;
    cmatch_dec (Ret r) (FTRet r') := dec_if (decide (r = r'));
    cmatch_dec (Nextl call k) (FTStop call') :=
      dec_if (decide (call = call'));
    cmatch_dec (Nextl call k) (ev :: tl, tre)
      with inspect (event_extract ev call) := {
      | Some ret eq: _ =>
          dec_if (cmatch_dec (k ret) (tl, tre))
      | None eq: _ => right _
      } ;
    cmatch_dec (Nextr (ChooseFin n) k) tr :=
      dec_if (@decide (∃x : fin n, cmatch (k x) tr) (@exists_dec _ _ _ _ (λ x, cmatch_dec (k x) tr)));
    cmatch_dec _ _ := right _.
  Solve All Obligations with
    cbn;
    intros;
    try match goal with | H : ∃ _, _ |- _ => destruct H end;
    try rewrite event_extract_Some in *;
    try rewrite event_extract_None in *;
    subst;
    try (intro H; dependent destruction H);
    try econstructor;
    naive_solver.
  #[export] Existing Instance cmatch_dec.

  (** ** Choice monad equivalence

  A choice monad is not a canonical representation, so there is a non-equality
  equivalence relation *)


  (** Definition of strong equivalence. I haven't found a way to define it in a
      more useable manner. In particular one can't do (yet) an induction on it *)
  Definition cequiv {A} : Equiv (cMon A) :=
    λ c1 c2, ∀ tr, cmatch c1 tr ↔ cmatch c2 tr.

  #[local] Instance local_cequiv_params : Params (@cequiv) 1 := {}.

  #[global] Instance cequiv_sym A : Symmetric (@cequiv A).
  Proof using. unfold Symmetric, cequiv in *. naive_solver. Qed.
  #[global] Instance cequiv_refl A : Reflexive (@cequiv A).
  Proof using. unfold Reflexive, cequiv in *. naive_solver. Qed.
  #[global] Instance cequiv_trans A : Transitive (@cequiv A).
  Proof using. unfold Transitive, cequiv in *. naive_solver. Qed.
  #[global] Instance cequiv_equiv A : Equivalence (@cequiv A).
  Proof using. constructor; tc_solve. Qed.

  #[global] Instance cmatch_cequiv_Proper A :
    Proper (cequiv ==> eq ==> iff) (@cmatch A).
  Proof using.
    intros m1 m2 H ? t ->.
    by unfold cequiv in H.
  Qed.

  Lemma cequiv_Ret A (a : A) : cequiv (Ret a) (Ret a).
  Proof using. reflexivity. Qed.

  Lemma cequiv_Next A call k k':
    pointwise_relation (eff_ret call) cequiv k k' →
    @cequiv A (Next call k) (Next call k').
  Proof using.
    intros H trc.
    unfold pointwise_relation in H.
    destruct call;
      split;
      intro Hc;
      dependent destruction Hc;
      econstructor;
      by rewrite H in *.
  Qed.

  #[global] Instance Next_cequiv_Proper A call:
    Proper (pointwise_relation (eff_ret call) cequiv ==> @cequiv A) (Next call).
  Proof using. intros k k'. apply cequiv_Next. Qed.

  (* TODO: Make a good induction principle for cequiv *)

End CMon.
Arguments cMon _ {_}.

#[global] Instance cequiv_params : Params (@cequiv) 2 := {}.
