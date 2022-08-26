(** Unfortunately this development needs to support two kinds of bitvector.
    The module will attempt to provide smooth interoperability between the two *)

Require Import Lia.
Require Export stdpp.unstable.bitvector.
Require Export stdpp.unstable.bitvector_tactics.
Require Export bbv.Word.
Require Import CBase.
Require Import Coq.Logic.Eqdep. (* <- This assumes UIP *)

From Hammer Require Import Tactics.


(********** Dependent types stuff **********)

Lemma symmetry_symmetry {A} (x y : A) (e : x = y) :
  symmetry (symmetry e) = e.
Proof. sfirstorder. Qed.
#[global] Hint Rewrite @symmetry_symmetry : core.

Section Transport.
  Context {A : Type}.
  Context (P : A -> Type).

  (* I love dependent types /s *)
  Definition transport {x y : A} (e : x = y) (t : P x) : P y :=
    match e with
    | eq_refl => t
    end.

  (* This equivalent to eq_rect_eq which is itself equivalent to UIP *)
  Lemma transport_simpl {x} (e : x = x) (t : P x) :
    transport e t = t.
  Proof.
    unfold transport.
    rewrite (eq_rect_eq A x P t e) at 2. (* <- This is where UIP is used *)
    unfold eq_rect.
    reflexivity.
  Qed.

  Lemma transport_eq_trans {x y z} (e : x = y) (e' : y = z) (t : P x) :
    t |> transport e |> transport e' = t |> transport (eq_trans e e').
  Proof. sfirstorder. Qed.

  Lemma transport_symmetry {x y : A} (e : x = y) (a : P x) (b : P y) :
    a = transport (symmetry e) b <-> transport e a = b.
  Proof. sfirstorder. Qed.

  Lemma transport_eq_dep {x y : A} (a : P x) (b : P y) :
    eq_dep A P x a y b <-> exists e : y = x, a = transport e b.
  Proof.
    split.
    - unfold transport.
      destruct 1.
      exists eq_refl.
      reflexivity.
    - destruct 1 as [e H].
      destruct e.
      unfold transport in H.
      rewrite H.
      constructor.
  Qed.

  Lemma transport_fdep (f : forall A, P A) {x y : A} (e : x = y) :
    f y = transport e (f x).
  Proof. hauto use:transport_simpl. Qed.

End Transport.
Arguments transport_fdep {_ _} _ {_ _}.

Ltac transport_symmetry :=
  lazymatch goal with
  | |- ?a = transport ?P ?e ?b => symmetry; apply transport_symmetry; symmetry
  | |- transport ?P ?e ?a = ?b => apply transport_symmetry
  end.

#[global] Hint Rewrite @transport_simpl : transport.

Lemma transport_func {A B} {P : A -> Type} {x y : A} (e : x = y) (b : B)
  (f : B -> P x)
  : (transport (fun x : A => B -> P x) e f) b = transport P e (f b).
Proof.
  hauto db:transport.
Qed.
#[global] Hint Rewrite @transport_func : transport.



(********** Arithmetic helper stuff **********)

(* Makes lia able to handle euclidean division, which makes bv_solve,
   bv_solve' and bv_word_solve able to handle concat and extract *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* These need to be easily available to create equalities directly in Gallina *)
Arguments N2Nat.id {_}.
Arguments Nat2N.id {_}.

Lemma eq_N_to_nat {n m : N} :
  n = m -> N.to_nat n = N.to_nat m.
Proof. lia. Qed.

Lemma eq_nat_to_N {n m : nat} :
  n = m -> N.of_nat n = N.of_nat m.
Proof. lia. Qed.


(* The arith rewrite database helps simplify arithmetic in bitvector sizes*)
#[global] Hint Rewrite N_nat_Z : arith.
#[global] Hint Rewrite nat_N_Z : arith.
#[global] Hint Rewrite @N2Nat.id : arith.
#[global] Hint Rewrite @Nat2N.id : arith.

(* Reduce concrete arithmetic values to help lia. This is a tactic from stdpp bitvector
   that is redefined so it will also affect development done there*)
Ltac reduce_closed_N ::=
  reduce_closed_N_tac;
  repeat match goal with
    | |- context [Pos.to_nat ?a] => progress reduce_closed (Pos.to_nat a)
    | H: context [Pos.to_nat ?a] |- _ => progress reduce_closed (Pos.to_nat a)
    | |- context [N.to_nat ?a] => progress reduce_closed (N.to_nat a)
    | H: context [N.to_nat ?a] |- _ => progress reduce_closed (N.to_nat a)
    | |- context [N.of_nat ?a] => progress reduce_closed (N.of_nat a)
    | H: context [N.of_nat ?a] |- _ => progress reduce_closed (N.of_nat a)
    | |- context [Z.to_nat ?a] => progress reduce_closed (Z.to_nat a)
    | H: context [Z.to_nat ?a] |- _ => progress reduce_closed (Z.to_nat a)
    | |- context [Z.of_nat ?a] => progress reduce_closed (Z.of_nat a)
    | H: context [Z.of_nat ?a] |- _ => progress reduce_closed (Z.of_nat a)
    | |- context [N.add ?a ?b] => progress reduce_closed (N.add a b)
    | H : context [N.add ?a ?b] |- _ => progress reduce_closed (N.add a b)
    end.

Ltac simplify_arith :=
  reduce_closed_N;
  (try rewrite_strat topdown hints arith);
  repeat match goal with
    | H : _ |- _ => progress rewrite_strat topdown hints arith in H
    end.


(********** Bitvector decision **********)

(* Interface Equality decision for words (from bbv) *)
Global Instance word_eq_dec n : EqDecision (word n).
Proof.
  unfold EqDecision.
  unfold Decision.
  apply weq.
Defined.

(* This is already instanciated for bv *)

(********** word rewrite database **********)

(* The word database simplifies word related expressions *)

#[global] Hint Rewrite @uwordToZ_ZToWord : word.
#[global] Hint Rewrite @ZToWord_uwordToZ : word.

Lemma transport_ZToWord {n m : nat} (e : n = m) (z : Z) :
  transport word e (ZToWord n z) = ZToWord m z.
Proof. scongruence. Qed.
#[global] Hint Rewrite @transport_ZToWord : word.

Lemma transport_uwordToZ (n m : nat) (w : word n) (e : n = m):
  uwordToZ (transport word e w) = uwordToZ w.
Proof. scongruence. Qed.
#[global] Hint Rewrite transport_uwordToZ : word.

(* Do a transport_symmetry only if it enables immediate progress on
   either side of the equality *)
Ltac transport_symmetry_word :=
  transport_symmetry; rewrite_strat subterm hints word.


(********** bv rewrite database **********)

Lemma bv_wrap_bv_unsigned' {n m} (b : bv m) :
  n = m -> bv_wrap n (bv_unsigned b) = bv_unsigned b.
Proof. intro H. rewrite H. apply bv_wrap_bv_unsigned. Qed.
#[global] Hint Rewrite @bv_wrap_bv_unsigned' using lia : bv.

Lemma bv_wrap_uwordToZ {n m} (w : word m) :
  n = N.of_nat m -> bv_wrap n (uwordToZ w) = uwordToZ w.
Proof.
  intro H.
  rewrite bv_wrap_small.
  - reflexivity.
  - use uwordToZ_bound.
    unfold bv_modulus.
    sauto lq:on.
Qed.
#[global] Hint Rewrite @bv_wrap_uwordToZ using lia : bv.

#[global] Hint Rewrite Z_to_bv_small
  using unfold bv_modulus in *; lia : bv.
#[global] Hint Rewrite bv_wrap_small
  using unfold bv_modulus in *; lia : bv.
#[global] Hint Rewrite bv_wrap_bv_wrap using lia : bv.
#[global] Hint Rewrite bv_extract_concat_here using lia : bv.
#[global] Hint Rewrite bv_extract_concat_later using lia : bv.
#[global] Hint Rewrite Z_to_bv_unsigned : bv.
#[global] Hint Rewrite Z_to_bv_bv_unsigned : bv.


Lemma transport_Z_to_bv {n m : N} (e : n = m) (z : Z) :
  transport bv e (Z_to_bv n z) = Z_to_bv m z.
Proof. scongruence. Qed.
#[global] Hint Rewrite @transport_Z_to_bv : bv.
#[global] Hint Rewrite @transport_Z_to_bv : bv_simplify.

Lemma transport_bv_unsigned (n m i l : N) (b : bv n) (e : n = m):
  bv_unsigned (transport bv e b) = bv_unsigned b.
Proof. scongruence. Qed.
#[global] Hint Rewrite transport_bv_unsigned : bv.
#[global] Hint Rewrite transport_bv_unsigned : bv_simplify.

Lemma transport_bv_extract1 (n m i l : N) (b : bv n) (e : n = m):
  bv_extract i l (transport bv e b) = bv_extract i l b.
Proof. scongruence. Qed.
#[global] Hint Rewrite transport_bv_extract1 : bv.
#[global] Hint Rewrite transport_bv_extract1 : bv_simplify.

Lemma transport_bv_extract2 (n i l l' : N) (b : bv n) (e : l = l'):
  transport bv e (bv_extract i l b) = bv_extract i l' b.
Proof. scongruence. Qed.
#[global] Hint Rewrite transport_bv_extract2 : bv.
#[global] Hint Rewrite transport_bv_extract2 : bv_simplify.

Ltac transport_symmetry_bv :=
  transport_symmetry; rewrite_strat subterm hints bv.



(********** bv to word and back conversions **********)

Definition bv_to_word {n} (b : bv n) : word (N.to_nat n) :=
  ZToWord (N.to_nat n) (bv_unsigned b).

Definition word_to_bv {n} (b : word n) : bv (N.of_nat n) :=
  Z_to_bv (N.of_nat n) (uwordToZ b).


Lemma word_to_bv_to_word' {n} (b : word n) :
  b |> word_to_bv |> bv_to_word |> transport word Nat2N.id =  b.
Proof.
  unfold word_to_bv, bv_to_word.
  sauto lq:on db:bv,word use:uwordToZ_bound.
Qed.
#[global] Hint Rewrite @word_to_bv_to_word' : word.

Lemma word_to_bv_to_word {n} (b : word n) :
  b |> word_to_bv |> bv_to_word = transport word (symmetry Nat2N.id) b.
Proof.
  transport_symmetry.
  autorewrite with core word.
  reflexivity.
Qed.
#[global] Hint Rewrite @word_to_bv_to_word : word.

Lemma bv_to_word_to_bv' {n} (b : bv n) :
  b |> bv_to_word |> word_to_bv |> transport bv N2Nat.id = b.
Proof.
  unfold word_to_bv. unfold bv_to_word.
  hauto lq:on db:bv,word,arith use:bv_unsigned_in_range.
Qed.
#[global] Hint Rewrite @bv_to_word_to_bv' : bv.

Lemma bv_to_word_to_bv {n} (b : bv n) :
  b |> bv_to_word |> word_to_bv = transport bv (symmetry N2Nat.id) b.
Proof.
  transport_symmetry.
  autorewrite with core bv.
  reflexivity.
Qed.
#[global] Hint Rewrite @bv_to_word_to_bv : bv.
#[global] Hint Rewrite @bv_to_word_to_bv : bv_simplify.


Lemma transport_word_to_bv (n m : nat) (w : word n) (e : n = m):
  word_to_bv (transport word e w) = transport bv (eq_nat_to_N e) (word_to_bv w).
Proof.
  unfold word_to_bv.
  autorewrite with bv word.
  reflexivity.
Qed.
#[global] Hint Rewrite transport_word_to_bv : bv.


(* Doing `rewrite bv_to_word_to_bv` sometimes fails, if bitvector size are
   too concrete, this tactic perform the rewrite anyway *)
Ltac bv_to_word_to_bv :=
  match goal with
  | |- context C [@word_to_bv ?m (@bv_to_word ?n ?b)] =>
      let H := fresh "H" in
      assert_succeeds (enough (H : m = N.to_nat n);[| reflexivity]);
      let nG := context C [@word_to_bv (N.to_nat n) (@bv_to_word n b)] in
      let G := fresh "G" in
      enough (G : nG);[exact G| rewrite bv_to_word_to_bv]
  | Hyp : context C [@word_to_bv ?m (@bv_to_word ?n ?b)] |- _ =>
      let H := fresh "H" in
      assert_succeeds (enough (H : m = N.to_nat n);[| reflexivity]);
      let nG := context C [@word_to_bv (N.to_nat n) (@bv_to_word n b)] in
      let G := fresh "G" in
      rename Hyp into G;
      assert (Hyp : nG);
      [assumption | clear G; rewrite bv_to_word_to_bv in Hyp]
  end.

(* Doing `rewrite word_to_bv_to_word` sometimes fails, if bitvector size are
   too concrete, this tactic perform the rewrite anyway *)
Ltac word_to_bv_to_word :=
  match goal with
  | |- context C [@bv_to_word ?m (@word_to_bv ?n ?w)] =>
      let H := fresh "H" in
      assert_succeeds (enough (H : m = N.of_nat n);[| reflexivity]);
      let nG := context C [@bv_to_word (N.of_nat n) (@word_to_bv n w)] in
      let G := fresh "G" in
      enough (G : nG);[exact G| rewrite word_to_bv_to_word]
  | Hyp : context C [@bv_to_word ?m (@word_to_bv ?n ?w)] |- _ =>
      let H := fresh "H" in
      assert_succeeds (enough (H : m = N.of_nat n);[| reflexivity]);
      let nG := context C [@bv_to_word (N.of_nat n) (@word_to_bv n w)] in
      let G := fresh "G" in
      rename Hyp into G;
      assert (Hyp : nG);
      [assumption | clear G; rewrite word_to_bv_to_word in Hyp]
  end.

(********** Convert a mixed bv + word goal into a pure bv goal **********)

Lemma word_to_bv_eq {n : nat} (w w' : word n) :
  word_to_bv w = word_to_bv w' <-> w = w'.
Proof.
  split.
  + unfold word_to_bv.
    intro H.
    apply (f_equal bv_unsigned) in H.
    hauto db:bv use:ZToWord_uwordToZ.
  + scongruence.
Qed.

Lemma word_to_bv_neq {n : nat} (w w' : word n) :
  word_to_bv w ≠ word_to_bv w' <-> w ≠ w'.
Proof. rewrite word_to_bv_eq. reflexivity. Qed.


(* Replace the variable w of type by an equivalent variable of type bv *)
Ltac remove_word_var w :=
  let w2 := fresh "w" in
  rename w into w2;
  rewrite <- (word_to_bv_to_word' w2) in *;
  set (w := word_to_bv w2) in *;
  clearbody w;
  clear w2;
  autorewrite with bv word transport in *;
  reduce_closed_N.

(* Replace all context variables of type word by equivalent variables of type
bv *)
Ltac remove_word_vars :=
  repeat (match goal with
          | w : ?T |- _ => eunify T (word _); remove_word_var w end).

(* Replace a word equality by a bitvector equality *)
Ltac remove_word_eq :=
  match goal with
  | |- ?w = ?w' =>
      let t := type of w in
      eunify t (word _);
      apply word_to_bv_eq
  | |- ?w ≠ ?w' =>
      let t := type of w in
      eunify t (word _);
      apply word_to_bv_neq
  | H : ?w = ?w' |- _ =>
      let t := type of w in
      eunify t (word _);
      apply word_to_bv_eq in H
  | H : ?w ≠ ?w' |- _ =>
      let t := type of w in
      eunify t (word _);
      apply word_to_bv_neq in H
  end.

(* Replace a word equality by a bitvector equality *)
Ltac remove_word_eqs :=
  repeat remove_word_eq.

Ltac remove_words :=
  remove_word_vars; remove_word_eqs.


(********** bv_solve improvements **********)


(* Full bitvector simplification for both word and bv, contrary to bv_simplify,
   it does not move the goal to Z. Equalities in bv will stay in bv *)
Ltac bv_word_simp :=
  (* TODO maybe move to rewrite_strat if quantifier rewriting is needed *)
  repeat (autorewrite with bv word transport in *;
          try bv_to_word_to_bv;
          try word_to_bv_to_word).


(* Makes bv_unfold slower but more powerful, we'll see if that is better. *)
Global Hint Constants Transparent : bv_unfold_db.

(* Support transport in bv_simplify, bv_solve *)
Lemma bv_unfold_transport n m s w (e : n = m) (b : bv n) z:
  BvUnfold n s w b z ->
  BvUnfold m s w (transport bv e b) z.
Proof. scongruence. Qed.
Global Hint Resolve bv_unfold_transport | 10 : bv_unfold_db.
Global Hint Extern 20 => apply bv_unfold_transport : bv_unfold_db.

(** Simplify all bitvector equation in Z equations everywhere. Aimed for
    bitblast and bit by bit analysis*)
Ltac bv_simplify' :=
  forall_hyps ltac:(fun H => bv_simplify H); bv_simplify.

(** Simplify all bitvector equation in Z equations everywhere. Aimed for
    lia and arithmetic analysis*)
Ltac bv_simplify_arith' :=
  forall_hyps ltac:(fun H => bv_simplify_arith H); bv_simplify_arith.

(** Improvement of bv_solve that also simplifies the hypothesis *)
Ltac bv_solve' :=
  forall_hyps ltac:(fun H => bv_simplify_arith H); bv_solve.

(** Solve a goal with mixed word and bv reasoning, with lia as backend.
    Therefore it will not support bitwise and, or and xor. *)
Ltac bv_word_solve' := remove_words; bv_word_simp; bv_solve'.

Ltac bv_word_solve :=
  match goal with
  | |- _ =@{?T} _ => (eunify T (bv _) + eunify T (word _))
  | |- _ ≠@{?T} _ => (eunify T (bv _) + eunify T (word _))
  | H : _ =@{?T} _ |- _ => (eunify T (bv _) + eunify T (word _)); exfalso
  | H : _ ≠@{?T} _ |- _ => (eunify T (bv _) + eunify T (word _)); exfalso
  end; bv_word_solve'.



(* TODO improve performance *)
