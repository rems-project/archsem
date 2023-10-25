Require Import Common.
Require Import Options.
From stdpp Require Import option.

(* Reexporting Effects. Using FMon implies using Effects *)
Require Export Effects.
Open Scope effect_scope.

(* Needed for setoid rewrite along fequiv and cequiv that are defined as an
   Equiv instance *)
#[export] Typeclasses Transparent Equiv.



(** * Free monad

This is a custom implementation of a free monad, which is basically a finite
itree (thus inductive, not coinductive). Therefore, it cannot represent
non-termination. *)

Section FMon.
  Context {Eff : eff}.

  (** This implementation is not very computationally efficient in case of
      repeated binds, but has the advantage of being canonical up to
      functional extensionality *)
  Inductive fMon {A : Type} :=
  | Ret (ret : A)
  | Next {T : Type} (call : Eff T) (k : T → fMon).
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

  #[global] Instance fMon_call : MCall Eff fMon := λ _ out, Next out Ret.

  (** * FMon equivalence

     This would be plain equality with functional extensionality,
     TODO: maybe we should actually require FunExt and remove this *)
  Inductive fequiv {A} : Equiv (fMon A) :=
  | FERet a : fequiv (Ret a) (Ret a)
  | FENext T (call : Eff T) k1 k2 (Hpr : pointwise_relation T fequiv k1 k2):
    fequiv (Next call k1) (Next call k2).

  #[global] Instance fequiv_sym A : Symmetric (@fequiv A).
  Proof using. intros x y H. induction H; constructor; naive_solver. Qed.

  #[global] Instance fequiv_refl A : Reflexive (@fequiv A).
  Proof using. intros x. induction x; constructor; naive_solver. Qed.

  #[global] Instance fequiv_trans A : Transitive (@fequiv A).
  Proof using.
    intros x y z H H'.
    generalize dependent z.
    induction H;
      intros z H';
      dependent destruction H';
      constructor;
      sfirstorder.
  Qed.

  #[global] Instance fequiv_equiv A : Equivalence (@fequiv A).
  Proof using. constructor; apply _. Qed.

  #[global] Instance Next_fequiv_Proper A T (call : Eff T):
    Proper (pointwise_relation T fequiv ==> @fequiv A) (Next call).
  Proof using. hauto l:on. Qed.

  Infix "≡ₑ" := fequiv (at level 70, no associativity).
  Infix "≡ₑ@{ A }" := (@fequiv A _)
                       (at level 70, only parsing, no associativity).

  (** * Events and traces *)

  (** A event of an effect type is a combination of an effect call and its
      result *)
  Record fEvent := FEvent {ftype : Type; fcall : Eff ftype; fret: ftype}.
  Arguments FEvent {_} _ _.

  Infix "&→" := FEvent (at level 45, no associativity).

  (** The type of trace over fMon. Those trace are partial and can stop
      anywhere *)
  Inductive fTrace {A : Type} :=
  | FTNext (ev : fEvent) (ntr : fTrace)
  | FTRet (a : A)
  | FTStop {T} (call : Eff T).
  Arguments fTrace : clear implicits.

  Fixpoint ftlist {A : Type} (ft : fTrace A) :=
    match ft with
    | FTNext ev ntr => ev :: ftlist ntr
    | _ => []
    end.
  Fixpoint ftres {A : Type} (ft : fTrace A) : result (sigT Eff) A:=
    match ft with
    | FTNext ev ntr => ftres ntr
    | FTRet a => Ok a
    | FTStop call => Error (existT _ call)
    end.

  Fixpoint fTrace_list_res {A} (l : list fEvent) (r : result (sigT Eff) A) :=
    match l with
    | [] => match r with
            | Ok a => FTRet a
            | Error (existT T call) => FTStop call
            end
    | ev :: tl => FTNext ev (fTrace_list_res tl r)
    end.

  Lemma fTrace_ftlist_ftres {A} (ft : fTrace A) :
    fTrace_list_res (ftlist ft) (ftres ft) = ft.
  Proof using. induction ft; sfirstorder. Qed.
  Hint Rewrite @fTrace_ftlist_ftres : fmon.

  Lemma ftlist_fTrace_list_res {A} l e :
    ftlist (@fTrace_list_res A l e) = l.
  Proof using. induction l; hauto lq:on. Qed.
  Hint Rewrite @ftlist_fTrace_list_res : fmon.

  Lemma ftres_fTrace_list_res {A} l e :
    ftres (@fTrace_list_res A l e) = e.
  Proof using. induction l; hauto lq:on. Qed.
  Hint Rewrite @ftres_fTrace_list_res : fmon.

  (** * Full traces *)

  (** Full trace are traces that only stop on a non returning effect *)
  Definition ftfull {A} (ft : fTrace A) :=
    ∀ T call, ftres ft = Error (existT T call) → T → False.
  Lemma ftfull_FTRet {A} (a : A) : ftfull (FTRet a).
  Proof using. hfcrush. Qed.
  Hint Resolve ftfull_FTRet : fmon.
  Lemma ftfull_FTNext {A} ev (ntr : fTrace A) :
    ftfull ntr → ftfull (FTNext ev ntr).
  Proof using. hfcrush. Qed.
  Hint Resolve ftfull_FTNext : fmon.
  Lemma ftfull_FTStop {A} T (call : Eff T) :
    (T → False) → ftfull (A := A) (FTStop call).
  Proof using. intros H T' call' H'. by dependent destruction H'. Qed.
  Hint Resolve ftfull_FTStop : fmon.
  Lemma ftfull_FTStop_spec {A} T (call : Eff T) :
    ftfull (A := A) (FTStop call) ↔ (T → False).
  Proof using. split; [sfirstorder | apply ftfull_FTStop]. Qed.
  Hint Rewrite @ftfull_FTStop_spec : fmon.

  Equations ftfull_dec {A} `{Eff.Wf Eff} (ft : fTrace A) : Decision (ftfull ft) :=
    ftfull_dec (FTNext _ tr) := dec_if (ftfull_dec tr);
    ftfull_dec (FTRet _) := left _;
    ftfull_dec (@FTStop T call) with decideT T := {
      | inleft _ => right _
      | inright _ => left _
      }.
  Solve All Obligations with hauto l:on db:fmon.

  (** If the effect type provides an exception type to represent its non
      terminating calls, then we can use that type to represent a trace *)
  Context {Ex : Eff.Exc Eff}.
  Notation exc := (Eff.exc Eff).

  (** If an effect type provide an exception, one can throw that exception
      This is implemented by a Hint Extern later *)
  Definition fmon_throw_exc : MThrow exc fMon :=
    λ _ e, mcall_noret (Eff.exc2eff e).T2.

  Definition ftres_full {A} (ft : fTrace A) : option (result exc A) :=
    match ftres ft with
    | Ok a => Some (Ok a)
    | Error (existT T call) => Eff.eff2exc call |$> Error
    end.

  Lemma ftres_full_ftfull {A} (ft : fTrace A) :
    ftfull ft ↔ is_Some (ftres_full ft).
  Proof using.
    unfold ftfull, ftres_full.
    destruct (ftres ft) as [|[]].
    - hauto l:on.
    - rewrite fmap_is_Some.
      rewrite Eff.exc_empty.
      split.
      + naive_solver.
      + injection 2. sfirstorder.
  Qed.

  Definition fTrace_list_res_full {A} (l : list fEvent) (r : result exc A) :=
    fTrace_list_res l (mapE Eff.exc2eff r).

  Lemma fTrace_ftlist_ftres_full {A} (ft : fTrace A) e:
    ftres_full ft = Some e →
    fTrace_list_res_full (ftlist ft) e = ft.
  Proof using.
    unfold fTrace_list_res_full.
    intro H.
    rewrite <- fTrace_ftlist_ftres.
    f_equal.
    unfold ftres_full, mapE in *.
    repeat case_split;
      try (f_equal; rewrite Eff.exc_wf);
      try (rewrite fmap_Some in * );
      sfirstorder.
  Qed.
  Hint Rewrite @fTrace_ftlist_ftres_full : fmon.

  Lemma ftlist_fTrace_list_res_full {A} l e :
    ftlist (@fTrace_list_res_full A l e) = l.
  Proof using. unfold fTrace_list_res_full. hauto l:on db:fmon. Qed.
  Hint Rewrite @ftlist_fTrace_list_res_full : fmon.

  Lemma ftres_fTrace_list_res_full {A} l e :
    ftres_full (@fTrace_list_res_full A l e) = Some e.
  Proof using.
    unfold fTrace_list_res_full, ftres_full.
    autorewrite with fmon.
    destruct e; cbn in *.
    + done.
    + case_split.
      rewrite Eff.exc_wf in *.
      hauto lq:on.
  Qed.
  Hint Rewrite @ftres_fTrace_list_res_full : fmon.

  Lemma ftfull_fTrace_list_res_full A l e: ftfull (A:=A) (fTrace_list_res_full l e).
  Proof using.
    rewrite ftres_full_ftfull.
    by rewrite ftres_fTrace_list_res_full.
  Qed.
  Hint Resolve ftfull_fTrace_list_res_full : fmon.

  (** * Trace matching *)

  Inductive fmatch {A : Type} : fMon A → fTrace A → Prop :=
  | FTMNext T (call : Eff T) k ret tr :
    fmatch (k ret) tr → fmatch (Next call k) (FTNext (call &→ ret) tr)
  | FTMRet a : fmatch (Ret a) (FTRet a)
  | FTMStop T (call : Eff T) k : fmatch (Next call k) (FTStop call).

  Lemma fmatch_next A T (call : Eff T) (k : T → fMon A) (ret : T) tr:
    fmatch (Next call k) (FTNext (call &→ ret) tr)
      ↔ fmatch (k ret) tr.
  Proof using.
    split; intro H.
    - dependent destruction H. hauto inv:fTrace.
    - sauto lq:on.
  Qed.

  #[global] Instance fmatch_Proper A :
    Proper (@fequiv A ==> eq ==> iff) fmatch.
  Proof using.
    intros m1 m2 H ? t ->.
    generalize dependent t.
    induction H.
    - naive_solver.
    - split;
        intro Hfm;
        dependent destruction Hfm;
        constructor;
        naive_solver.
  Qed.

  Lemma ftrace_exists {A} (m : fMon A) : ∃ t, fmatch m t.
  Proof using. induction m; hauto q:on ctrs:fmatch. Qed.

  Context {Wf : Eff.Wf Eff}.

  Lemma ftrace_ftfull_exists {A} (m : fMon A) : ∃ t, fmatch m t ∧ ftfull t.
  Proof using Wf.
    induction m. { hauto lq:on ctrs:fmatch hint:db:fmon. }
    destruct (decideT T).
    - hauto lq:on ctrs:fmatch.
    - hauto lq:on ctrs:fmatch db:fmon.
  Qed.

  Lemma fequiv_via_ftrace_ftfull A m1 m2:
    (∀ trc : fTrace A, ftfull trc → fmatch m1 trc ↔ fmatch m2 trc) →
    m1 ≡ₑ m2.
  Proof using Wf.
    generalize dependent m2.
    induction m1; intros m2 Ht; destruct m2.
    - hauto ctrs:fmatch inv:fmatch q:on db:fmon.
    - hauto ctrs:fmatch inv:fmatch q:on db:fmon.
    - hauto ctrs:fmatch inv:fmatch q:on db:fmon.
    - destruct (ftrace_ftfull_exists (Next call k)) as [tr [Htr Hfull]].
      pose proof Htr as Htr2.
      apply Ht in Htr2. 2: done.
      dependent destruction Htr;
      dependent destruction Htr2.
      + clear dependent tr.
        constructor.
        intro a.
        apply H.
        intro trc.
        specialize Ht with (FTNext (call &→ a) trc).
        by setoid_rewrite fmatch_next in Ht.
      + constructor. intro. hauto l:on db:fmon.
  Qed.

  (** * Fmon Handling *)

  Definition fHandler (M : Type → Type) := ∀ A, Eff A → M A.

  Definition mcall_fHandler `{MC : MCall Eff M} : fHandler M := @mcall _ _ MC.

  Fixpoint finterp `{MRet M, MBind M} (handler : fHandler M)
    [A] (mon : fMon A) : M A :=
    match mon with
    | Ret a => (mret a : M A)
    | @Next _ T call k => ret ←@{M} handler T call; finterp handler (k ret)
    end.

  #[global] Instance fequiv_finterp A `{MRet M, MBind M} (handler : fHandler M):
    (∀ T, Proper (pointwise_relation T eq ==> eq ==> eq) (@mbind M _ T A)) →
    Proper (@fequiv A ==> eq) (finterp handler (A := A)).
  Proof using.
    intros P m1 m2 He.
    induction He; sfirstorder.
  Qed.

  Lemma finterp_mcall A (f : fMon A) : finterp mcall_fHandler f ≡ₑ f.
  Proof using. induction f; hauto l:on. Qed.



  (** * Decidability for fmatch *)

  Context {ED : Eff.Decision Eff}.

  Definition event_extract (ev : fEvent) {T} (call : Eff T) : option T :=
    match decide (ev.(fcall) =ₑ call) with
    | left e => Some (Eff.conv_ret (Eff.eq_type e) ev.(fret))
    | right _ => None
    end.

  Lemma event_extract_Some ev T (call : Eff T) ret :
    event_extract ev call = Some ret ↔ ev = (call &→ ret).
  Proof using.
    unfold event_extract.
    case_decide.
    - pose proof H as H'.
      simplify_eff_eq in H'.
      setoid_rewrite UIP_refl.
      split.
      + hauto q:on inv:fEvent.
      + intro E.
        destruct ev.
        by dependent destruction E.
    - hauto q:on.
  Qed.

  Lemma event_extract_None ev T (call : Eff T) :
    event_extract ev call = None ↔ fcall ev ≠ₑ call.
  Proof using.
    rewrite eq_None_not_Some.
    apply not_iff_compat.
    unfold is_Some.
    setoid_rewrite event_extract_Some.
    clear Wf Ex. (* Otherwise sauto uses them *)
    sauto.
  Qed.

  Equations fmatch_dec `{EqDecision A}
      (f : fMon A) tr : Decision (fmatch f tr) :=
    fmatch_dec (Next call k) (FTNext ev ft)
      with inspect (event_extract ev call) := {
      | Some ret eq: _ =>
          dec_if (fmatch_dec (k ret) ft)
      | None eq: _ => right _
      } ;
    fmatch_dec (Ret r) (FTRet r') := dec_if (decide (r = r'));
    fmatch_dec (Next call k) (FTStop call') := dec_if (decide (call =ₑ call'));
    fmatch_dec _ _ := right _.
  Solve All Obligations with
    intros; cbn in *;
    try (rewrite event_extract_Some in *;
         subst ev;
         by rewrite <- fmatch_next in * );
    try match goal with | |- ¬ _ => intro H; dependent destruction H end;
    try(rewrite event_extract_None in * );
    hauto db:fmon.
  #[global] Existing Instance fmatch_dec.

End FMon.
Arguments fMon : clear implicits.
Arguments fEvent : clear implicits.
Arguments FEvent {_ _} _ _.
Arguments fTrace : clear implicits.
Arguments fHandler : clear implicits.
#[global] Instance fequiv_params : Params (@fequiv) 2 := {}.
Infix "≡ₑ" := fequiv (at level 70, no associativity).
Infix "≡ₑ@{ A }" := (@fequiv A _)
                      (at level 70, only parsing, no associativity).
Infix "&→" := FEvent (at level 45, no associativity).
Infix "&→@{ Eff }" := (@FEvent (Eff _) _) (at level 45, no associativity).

Definition fHandler_plus {Effl Effr : eff} `{MRet M, MBind M}
    (fl : fHandler Effl M) (fr : fHandler Effr M) : fHandler (Effl +ₑ Effr) M :=
  λ T e, match e with
         | inl l => fl T l
         | inr r => fr T r
         end.
Infix "+ₕ" := fHandler_plus (at level 50, left associativity) : effect_scope.

#[export] Hint Extern 5 (MThrow _ ?M) =>
  let Eff := mk_evar eff in unify M (fMon Eff);
  class_apply (@fmon_throw_exc Eff _) : typeclass_instances.

(** * Choice monad: Non deterministic free monad *)
Section CMon.
  Context {Eff : eff}.

  (** A choice monad is just a free monad with additional choice effects. The
      only difference is the theory around it (equivalence, trace matching, etc.) *)
  Definition cMon := fMon (Eff +ₑ MChoice).
  Notation Nextl e := (Next (inl e)).
  Notation Nextr e := (Next (inr e)).

  Definition cinterp `{MRet M, MBind M, MChoose M} (f : fHandler Eff M) [A]
      (c : cMon A) : M A :=
    finterp (f +ₕ mcall_fHandler) c.

  Definition cmon_throw_exc `{Eff.Exc Eff} : MThrow (Eff.exc Eff) cMon :=
    λ _ e, @mthrow (Eff.exc Eff + discard_type) _ _ _ (inl e).

  (** * CMon matching with a trace *)
  Inductive cmatch {A : Type} : cMon A → fTrace Eff A → Prop :=
  | CTMNext T (call : Eff T) k ret tr :
    cmatch (k ret) tr → cmatch (Nextl call k) (FTNext (call &→ ret) tr)
  | CTMChoose n i k tr : cmatch (k i) tr →
    cmatch (Nextr (ChooseFin n) k) tr
  | CTMRet a : cmatch (Ret a) (FTRet a)
  | CTMStop T (call : Eff T) k : cmatch (Nextl call k) (FTStop call).

  #[local] Instance cmatch_fequiv_Proper A :
    Proper (fequiv ==> eq ==> iff) (@cmatch A).
  Proof using.
    intros m1 m2 H ? t ->.
    generalize dependent t.
    induction H.
    - naive_solver.
    - destruct call as [call | choice];
        split;
        intro Hfm;
        dependent induction Hfm;
        try (intro H'; dependent destruction H');
        econstructor;
        naive_solver.
  Qed.

  Lemma cmatch_Nextl A T (call : Eff T) (k : T → cMon A) (ret : T) tr:
    cmatch (Nextl call k) (FTNext (call &→ ret) tr)
      ↔ cmatch (k ret) tr.
  Proof using.
    split; intro H.
    - dependent destruction H. hauto inv:fTrace.
    - sauto lq:on.
  Qed.

  (** Definition of strong equivalence. I haven't found a way to define it in a
      more useable manner. In particular one can't do an induction on it *)
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
  Proof using. constructor; apply _. Qed.

  #[global] Instance cequiv_fequiv_Proper A :
    Proper (fequiv ==> fequiv ==> iff) (@cequiv A).
  Proof using.
    unfold cequiv.
    intros m1 m2 H m'1 m'2 H'.
    setoid_rewrite H.
    setoid_rewrite H'.
    reflexivity.
  Qed.

  #[global] Instance fequiv_cequiv A : subrelation fequiv (@cequiv A).
  Proof using. by intros x y ->. Qed.

  #[global] Instance cmatch_cequiv_Proper A :
    Proper (cequiv ==> eq ==> iff) (@cmatch A).
  Proof using.
    intros m1 m2 H ? t ->.
    by unfold cequiv in H.
  Qed.

  (** * Some cequiv useability lemma *)
  Lemma cequiv_Ret A (a : A) : cequiv (Ret a) (Ret a).
  Proof using. reflexivity. Qed.

  Lemma cequiv_Next A T call k k':
    pointwise_relation T cequiv k k' → @cequiv A (Next call k) (Next call k').
  Proof using.
    intros H trc.
    destruct call;
      split;
      intro Hc;
      dependent destruction Hc;
      econstructor;
      by rewrite H in *.
  Qed.

  #[global] Instance Next_cequiv_Proper A T call:
    Proper (pointwise_relation T cequiv ==> @cequiv A) (Next call).
  Proof using. intros k k'. apply cequiv_Next. Qed.

  (* TODO: Make a good inversion tactic for cequiv *)

  (** * Decidability for cmatch *)
  Context {ED : Eff.Decision Eff}.

  (** Decide a cmatch: a bit dumb, it will try every possible non-deterministic
      choice until one match succeeded or all failed. However in practice, if
      concrete value of cMon avoid doing choice before doing very long
      identical sequenced of calls in all choice, this shouldn't be that bad. *)
  Equations cmatch_dec `{EqDecision A} (f : cMon A) tr
    : Decision (cmatch f tr) :=
    cmatch_dec (Nextl call k) (FTNext ev ft)
      with inspect (event_extract ev call) := {
      | Some ret eq: _ =>
          dec_if (cmatch_dec (k ret) ft)
      | None eq: _ => right _
      } ;
    cmatch_dec (Ret r) (FTRet r') := dec_if (decide (r = r'));
    cmatch_dec (Nextl call k) (FTStop call') :=
      dec_if (decide (call =ₑ call'));
    cmatch_dec (Nextr (ChooseFin n) k) tr :=
      dec_if (@decide (∃x : fin n, cmatch (k x) tr) _);
    cmatch_dec _ _ := right _.
  Solve Obligations with
    try (intros; cbn in *;
         lazymatch goal with | |- Decision _ => fail | |- _ => idtac end;
         try (rewrite event_extract_Some in *;
              subst ev;
              by rewrite <- cmatch_Nextl in * );
         try match goal with | |- ¬ _ => intro H; dependent destruction H end;
         try(rewrite event_extract_None in * );
         hauto ctrs:cmatch).
  Next Obligation. cbn. intros. apply _. Defined.
  #[global] Existing Instance cmatch_dec.

End CMon.
Arguments cMon : clear implicits.

Notation Nextl e := (Next (inl e)).
Notation Nextr e := (Next (inr e)).

#[global] Instance cequiv_params : Params (@cequiv) 2 := {}.

#[export] Hint Extern 5 (MThrow _ ?M) =>
  let Eff := mk_evar eff in unify M (cMon Eff);
  class_apply (@cmon_throw_exc Eff _) : typeclass_instances.
