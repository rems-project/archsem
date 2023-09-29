(** Add a state monad transformer *)

Require Import CBase.
Require Import Effects.

Module ST.
  Section ST.
    Context {S : Type}.
    Context `{MRet M} `{MBind M} `{MJoin M} `{FMap M}.

    Definition t (A : Type):= S → M (S * A).

    Definition lift {A : Type} (m : M A) : ST.t A := λ s, fmap (s,.) m.

    (** Accessors fora accesing fields of a record like state *)
    Definition get {T} (proj : S → T)  : t T := λ s, mret (s, proj s).
    Definition set {T} (proj : S → T) {st : Setter proj} (f : T → T) : t () :=
      λ s, mret (set proj f s, ()).
    Definition setv {T} (proj : S → T) {st : Setter proj} (f : T) : t () :=
      λ s, mret (setv proj f s, ()).

    (** Accessors for getting the whole state *)
    Definition geta : t S := fun s => mret (s, s).
    Definition seta (f : S → S) : t () := fun s => mret (f s, ()).
    Definition setav (s : S) : t () := fun _ => mret (s, ()).

    Global Instance mret_inst : MRet t :=
      { mret _ a := fun s => mret (s, a) }.
    Global Instance mbind_inst : MBind t :=
      { mbind _ _ f x := fun s => '(s', a) ← x s; f a s'}.
    Global Instance mjoin_inst : MJoin t :=
      { mjoin _ x := fun s => '(s', y) ← x s; y s'}.
    Global Instance fmap_inst : FMap t :=
      { fmap _ _ f x := fun s => fmap (fun '(s, a) => (s, f a)) (x s)}.

    Context `{MThrow E M}.
    Global Instance mthrow_inst : MThrow E t :=
      { mthrow _ x := lift (mthrow x) }.

    (* Specific instance can override this if they want the effect to modify the
    state, but they probably shouldn't *)
    Context `{MCall Eff M}.
    Global Instance mcall_inst : MCall Eff t :=
     { mcall _ eff := lift (mcall eff) }.


  End ST.
  Arguments t : clear implicits.

  Definition move {S M M' A} (f : M (S * A)%type → M'(S * A)%type) (x : t S M A)
      : t S M' A :=
    fun s => f (x s).



End ST.
