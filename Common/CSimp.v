(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
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

(** CSimp is general simplifier, but that only rewrite using equality ([eq]).
    Since we have functional and propositional extensionality, this still allows
    us to go quite far and in particular to rewrite arbitrarily deep under
    binders all kinds. *)

(** * User configuration *)

(** CSimp does not use [Hint Rewrite] as there is no way to access those from a
    custom tactic. Instead it use a typeclass.

    Any user can make an [Hint Extern] instance of the [CSimp] typeclass that
    call [autorewrite] or [rewrite_db] although we would recommend hooking that
    on some pattern (like a specific head constant) to avoid slowing the
    rewriting search too much.

    Similarly a user can add arbitrarily complex simplification procedures
    (simproc) by hooking them up to a [Hint Extern] *)
Class CSimp {T : Type} (x y : T) := csimp_eq : x = y.
Hint Mode CSimp + ! - : typeclass_instances.
Infix "⇒" := CSimp (at level 70).

(** Set to true to enable [csimp] tracing *)
Ltac2 mutable csimp_trace := false.

(** Trace when [csimp_trace] is turned on. Can be used in other related tactics
    if needed *)
Ltac2 csimp_tracef0 fmt :=
  if csimp_trace then Printf.printf fmt
  else Message.Format.ikfprintf (fun _ => ()) (Message.of_string "") fmt.
Ltac2 Notation "csimp_tracef" fmt(format) := csimp_tracef0 fmt.
Ltac2 Notation "csimp_tracef_if" b(tactic(0)) fmt(format) :=
  if csimp_trace then
    if b then Printf.printf fmt
    else Message.Format.ikfprintf (fun _ => ()) (Message.of_string "") fmt
  else Message.Format.ikfprintf (fun _ => ()) (Message.of_string "") fmt.

(** * Tactic internals *)

(** ** Leaf rewriting rule search *)

(** Get the target of a rewriting proof term *)
Ltac2 csimp_get_target (c : constr) :=
  lazy_match! Constr.type c with
  | _ = ?t => t
  | _ ⇒ ?t => t
  end.


(** Search for a single rewriting step on term [c]. If found returns the
    equality proof term as a pre-term and the target (what [c] was rewritten to)
    as typed term *)
Ltac2 csimp_leaf (c : constr) : (preterm * constr) option :=
  match
  Control.case (fun () =>
      let eq := get_instance '($c ⇒ _) in
      (preterm:($eq), csimp_get_target eq)) with
  | Val(e, _) => Some e
  | Err _ => None
  end.

(** ** Helper lemmas *)

Lemma csimp_app_fun_arg {A B : Type} {f g : A → B} {a b : A} :
  f = g → a = b → f a = g b.
Proof. naive_solver. Qed.

Lemma csimp_app_nofun_arg {A B : Type} (f : A → B) {a b : A} :
  a = b → f a = f b.
Proof. naive_solver. Qed.

Lemma csimp_app_fun_noarg {A B : Type} {f g : A → B} (a : A) :
  f = g → f a = g a.
Proof. naive_solver. Qed.

Lemma csimp_imp_lr {P P' Q Q' : Prop} :
  P = P' → Q = Q' → (P → Q) = (P' → Q').
Proof. naive_solver. Qed.

Lemma csimp_imp_l {P P' : Prop} (Q : Prop) :
  P = P' → (P → Q) = (P' → Q).
Proof. naive_solver. Qed.

Lemma csimp_imp_r (P : Prop) {Q Q' : Prop} :
  Q = Q' → (P → Q) = (P → Q').
Proof. naive_solver. Qed.

Lemma csimp_forall {A : Type} {P Q: A → Prop} :
  (∀ x, P x = Q x) → (∀ x, P x) = (∀ x, Q x).
Proof. intro H. setoid_rewrite H. reflexivity. Qed.

Lemma csimp_lambda {A B : Type} {P Q: A → B} :
  (∀ x, P x = Q x) → (λ x, P x) = (λ x, Q x).
Proof. intro H. setoid_rewrite H. reflexivity. Qed.

(** Detect whether an application is dependent. [csimp] will not go rewrite
    under a dependent application *)
Definition is_nondep_app_aux {A B} (f : A → B) : unit := ().
Ltac2 csimp_is_nondep_app (c : constr) :=
  succeeds (let _ := '(is_nondep_app_aux $c) in ()).

(** Apply a lambda binder or a prod ([∀]) binder to a variable by direct
    substitution: The result is already locally beta reduced *)
Ltac2 apply_subst (c: constr) (var : ident) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Lambda _ c =>
      Constr.Unsafe.substnl [Constr.Unsafe.make (Constr.Unsafe.Var var)] 0 c
  | Constr.Unsafe.Prod _ c =>
      Constr.Unsafe.substnl [Constr.Unsafe.make (Constr.Unsafe.Var var)] 0 c
  | _ => throw_tacticf "apply_subst, not on a lambda or prod abstraction"
  end.

(** ** Main tactic body *)

(* TODO:
- Split down and up rewrite typeclasses
- Rewrite under match cases
- Build a constr map and cache results
- Allow more control when calling csimp:
  - Add custom rewriting rules on the fly
  - Only custom rules mode (crewrite?)
  - Allow specific cbn reduction rules (in particular which constant to reduce)
  - Allow specifing complete unfolding of constants
*)
Ltac2 rec csimp_go_down (c : constr) : (preterm * constr) option :=
  csimp_tracef "csimp: Search down in term : %t" c;
  let nc := eval cbn beta iota in $c in
  csimp_tracef_if (Bool.neg (Constr.equal c nc)) "csimp: After cbn: %t" nc;
  match csimp_leaf nc with
  | Some (e, t) =>
      csimp_tracef "csimp: Found down rewrite from %t to %t" nc t;
      match csimp_go_down t with
      | Some (e', t') => Some (preterm:(eq_trans $preterm:e $preterm:e'), t')
      | None => Some (e, t)
      end
  | None =>
      match csimp_go_rec nc with
      | Some (e, t) =>
          csimp_tracef "csimp: Found recursive rewrite from %t to %t" nc t;
          match csimp_go_up t with
          | Some (e', t') => Some (preterm:(eq_trans $preterm:e $preterm:e'), t')
          | None => Some (e, t)
          end
      | None => csimp_go_up nc
      end
  end
with csimp_go_rec (c : constr) : (preterm * constr) option :=
  lazy_match! c with
  | ?f ?a =>
      if csimp_is_nondep_app f then
        match (csimp_go_down f, csimp_go_down a) with
        | Some (ef, f'), Some (ea, a') =>
            Some (preterm:(csimp_app_fun_arg $preterm:ef $preterm:ea), '($f' $a'))
        | Some (ef, f'), None =>
            Some (preterm:(csimp_app_fun_noarg $a $preterm:ef), '($f' $a))
        | None, Some (ea, a') =>
            Some (preterm:(csimp_app_nofun_arg $f $preterm:ea), '($f $a'))
        | None, None => None
        end
      else None
  | ?p → ?q =>
      if Constr.equal (Constr.type p) 'Prop then
        if Constr.equal (Constr.type q) 'Prop then
          match (csimp_go_down p, csimp_go_down q) with
          | Some (ep, p'), Some (eq, q') =>
              Some (preterm:(csimp_imp_lr $preterm:ep $preterm:eq), '($p' → $q'))
          | Some (ep, p'), None =>
              Some (preterm:(csimp_imp_l $q $preterm:ep), '($p' → $q))
          | None, Some (eq, q') =>
              Some (preterm:(csimp_imp_r $p $preterm:eq), '($p → $q'))
          | None, None => None
          end
        else None
      else None
  | ∀ x : ?t, @?f x =>
      let x := Fresh.in_goal @x in
      match
        Control.case
          (fun () =>
            Constr.in_context x t
              (fun () =>
                  let c := apply_subst f x in
                  match csimp_go_down c with
                  | Some (e, _) =>  exact $preterm:e
                  | None => zero_tacticf "Nope"
                  end
          )) with
      | Val (e, _) =>
          let p := '(csimp_forall $e) in
          let t := csimp_get_target p in
          Some (preterm:($p), (eval cbn beta in $t))
      | Err _ => None
      end
  | λ x : ?t, @?f x =>
      let x := Fresh.in_goal @x in
      match
        Control.case
          (fun () =>
            Constr.in_context x t
              (fun () =>
                  let c := apply_subst f x in
                  match csimp_go_down c with
                  | Some (e, _) =>  exact $preterm:e
                  | None => zero_tacticf "Nope"
                  end
          )) with
      | Val (e, _) =>
          let p := '(csimp_lambda $e) in
          let t := csimp_get_target p in
          Some (preterm:($p), (eval cbn beta in $t))
      | Err _ => None
      end
  | _ => None
  end
with csimp_go_up  (c : constr) : (preterm * constr) option :=
  csimp_tracef "csimp: Search up in term : %t" c;
  let nc := eval cbn beta iota in $c in
  csimp_tracef_if (Bool.neg (Constr.equal c nc)) "csimp: After cbn: %t" nc;
  match csimp_leaf nc with
  | Some (e, t) =>
      csimp_tracef "csimp: Found up rewrite from %t to %t" nc t;
      match csimp_go_down t with
      | Some (e', t') => Some (preterm:(eq_trans $preterm:e $preterm:e'), t')
      | None => Some (e, t)
      end
  | None => None
  end.

Lemma csimp_goal_lemma (A B : Prop) : A = B → B → A.
Proof. naive_solver. Qed.

Ltac2 csimp_goal () :=
  Control.enter
    (fun () =>
       let g := Control.goal () in
       match csimp_go_down g with
       | Some (e, t) =>
           apply (csimp_goal_lemma $g $t $preterm:e)
       | None => zero_tacticf "csimp: Nothing to simplify"
       end).

Ltac2 Notation csimp := csimp_goal ().
Tactic Notation "csimp" := ltac2:(csimp).

(** * Default rewriting rules *)


Instance csimp_eq_refl {A} (a : A) : (a = a) ⇒ True.
Proof. by apply propositional_extensionality. Qed.

Instance csimp_csimp_refl {A} (a : A) : (a ⇒ a) ⇒ True.
Proof. unfold CSimp. by csimp. Qed.

Lemma csimp_eta_contract {A B} (f : A → B) : (λ x, f x) ⇒ f.
Proof. done. Qed.
(* Need a more rigid matching, without eta-conversion, otherwise this will loop *)
Hint Extern 2 ((λ x, ?f x) ⇒ _) => apply csimp_eta_contract : typeclass_instances.

Instance csimp_id {A} (a : A) : id a ⇒ a.
Proof. reflexivity. Qed.

(** ** Pair rewriting *)

(** Open this module to rewrite [let '(x, y) := z in P x y] to P z.1 z.2.
    Discrimination tree are not smart with this, so this will be tried at every
    level. *)
Module CSimpPairLet.
  Hint Extern 10 ((let '(_,_) := _ in _) ⇒ _) =>
         apply pair_let_simp_type : typeclass_instances.
End CSimpPairLet.

(** In nearly all situation any exists on a pair can be safely replaces by 2
    exists on the pair component however this could break stuff so I made
    optional *)
Module CSimpPairExists.
  Instance exists_pair_csimp B C P:
    (∃ x : C * B, P x) ⇒ (∃ x y, P (x, y)).
  Proof. apply propositional_extensionality. apply exists_pair. Qed.
End CSimpPairExists.

Instance csimp_fst_pair {A B} (a : A) (b : B) : (a, b).1 ⇒ a.
Proof. done. Qed.

Instance csimp_snd_pair {A B} (a : A) (b : B) : (a, b).2 ⇒ b.
Proof. done. Qed.

Instance csimp_pair_fst_snd {A B} (x : A * B) : (x.1, x.2) ⇒ x.
Proof. by destruct x. Qed.
