(******************************************************************************)
(* Syntactic facts for the installed sail-tiny-arm source             *)
(******************************************************************************)

(** This checks the Sail syntax, including translation and decoded instruction
    execution. The abstract iMon counterexample uses an explicit discard; the
    actual Sail source emits no SI.Discard. Outcome handlers can still discard; this theorem does not
    assert that certification always has a result. *)
From ASCommon Require Import Options Common.
From ArchSemArm Require Import ArmInst.
From SailTinyArm Require Import System.

Definition SailOutcomeNoDiscard {eo A} (out : SI.outcome eo A) : Prop :=
  match out with SI.Discard => False | _ => True end.
Fixpoint SailNoDiscard {eo A} (mon : SI.iMon eo A) : Prop :=
  match mon with
  | SI.Ret _ => True
  | SI.Next out k => SailOutcomeNoDiscard out ∧ ∀ r, SailNoDiscard (k r)
  end.
Lemma sail_no_discard_bind {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  SailNoDiscard mon → (∀ a, SailNoDiscard (k a)) →
  SailNoDiscard (SI.iMon_bind mon k).
Proof.
  revert B k. induction mon as [a|T out km IH]; intros B k Hm Hk.
  - apply Hk.
  - cbn in Hm |- *. destruct Hm as [Ho Ht]. split; [exact Ho|].
    intro r. apply IH; [apply Ht|exact Hk].
Qed.
Lemma sail_no_discard_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  SailNoDiscard mon → (∀ e, SailNoDiscard (h e)) →
  SailNoDiscard (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hm Hh.
  - exact I.
  - cbn in Hm |- *. destruct Hm as [Ho Ht].
    destruct out; cbn in Ho |- *; try contradiction;
      try (split; [exact Ho|]; intro r; apply IH; [apply Ht|exact Hh]).
    apply Hh.
Qed.
Lemma sail_no_discard_foreach {E Vars} from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, SailNoDiscard (body z vars)) →
  SailNoDiscard (System_types.Defs.foreach_ZM_up' from to step fuel vars body).
Proof.
  revert from vars. induction fuel as [|fuel IH]; intros from vars Hbody.
  - cbn [System_types.Defs.foreach_ZM_up']. destruct (from <=? to); exact I.
  - cbn [System_types.Defs.foreach_ZM_up']. destruct (from <=? to); [|exact I].
    apply sail_no_discard_bind; [apply Hbody|]. intro v. apply IH, Hbody.
Qed.
Ltac sail_head t :=
  lazymatch t with ?f ?x => sail_head f | _ => t end.
Ltac solve_sail_no_discard :=
  lazymatch goal with
  | |- True => exact I
  | |- SailNoDiscard (SI.Ret _) => exact I
  | |- SailNoDiscard (SI.Next ?out ?k) =>
      split; [cbn [SailOutcomeNoDiscard]; exact I|intro; solve_sail_no_discard]
  | |- SailNoDiscard (SI.iMon_bind _ _) =>
      apply sail_no_discard_bind; [solve_sail_no_discard|intro; solve_sail_no_discard]
  | |- SailNoDiscard (System_types.Defs.bind _ _) =>
      apply sail_no_discard_bind; [solve_sail_no_discard|intro; solve_sail_no_discard]
  | |- SailNoDiscard (System_types.Defs.bind0 _ _) =>
      apply sail_no_discard_bind; [solve_sail_no_discard|intro; solve_sail_no_discard]
  | |- SailNoDiscard (System_types.Defs.try_catch _ _) =>
      apply sail_no_discard_try_catch; [solve_sail_no_discard|intro; solve_sail_no_discard]
  | |- SailNoDiscard (System_types.Defs.foreach_ZM_up' _ _ _ _ _ _) =>
      apply sail_no_discard_foreach; intros; solve_sail_no_discard
  | |- SailNoDiscard (match ?x with _ => _ end) =>
      destruct x; solve_sail_no_discard
  | |- SailNoDiscard ?mon =>
      let hd := sail_head mon in
      let mon' := eval unfold hd in mon in
      let mon'' := eval cbv beta iota zeta in mon' in
      change (SailNoDiscard mon''); solve_sail_no_discard
  end.
Lemma sail_no_discard_translation va size acc :
  SailNoDiscard (System.translate_address va size acc).
Proof. solve_sail_no_discard. Qed.
Lemma sail_no_discard_decode opcode : SailNoDiscard (System.decode opcode).
Proof. solve_sail_no_discard. Qed.
Lemma sail_no_discard_execute instr : SailNoDiscard (System.execute instr).
Proof. solve_sail_no_discard. Qed.
Lemma sail_no_discard_fetch_and_execute :
  SailNoDiscard (System.fetch_and_execute ()).
Proof. solve_sail_no_discard. Qed.

(** A counted update is a MemWrite or TlbOp outcome. A VM TlbOp can emit
    several recipient events; this bound counts outcomes, not those events.
    Address translation and instruction decoding emit neither kind. *)
Definition SailOutcomeNoUpdate {eo A} (out : SI.outcome eo A) : Prop :=
  match out with SI.MemWrite _ _ _ | SI.TlbOp _ => False | _ => True end.
Fixpoint SailNoUpdate {eo A} (mon : SI.iMon eo A) : Prop :=
  match mon with
  | SI.Ret _ => True
  | SI.Next out k => SailOutcomeNoUpdate out ∧ ∀ r, SailNoUpdate (k r)
  end.
Fixpoint SailAtMostOneUpdate {eo A} (mon : SI.iMon eo A) : Prop :=
  match mon with
  | SI.Ret _ => True
  | SI.Next out k =>
      (SailOutcomeNoUpdate out ∧ ∀ r, SailAtMostOneUpdate (k r)) ∨
      (∀ r, SailNoUpdate (k r))
  end.
Lemma sail_no_update_bind {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  SailNoUpdate mon → (∀ a, SailNoUpdate (k a)) →
  SailNoUpdate (SI.iMon_bind mon k).
Proof.
  revert B k. induction mon as [a|T out km IH]; intros B k Hm Hk.
  - apply Hk.
  - cbn in Hm |- *. destruct Hm as [Ho Ht]. split; [exact Ho|].
    intro r. apply IH; [apply Ht|exact Hk].
Qed.
Lemma sail_no_update_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  SailNoUpdate mon → (∀ e, SailNoUpdate (h e)) →
  SailNoUpdate (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hm Hh.
  - exact I.
  - cbn in Hm |- *. destruct Hm as [Ho Ht].
    destruct out; cbn in Ho |- *; try contradiction;
      try (split; [exact Ho|]; intro r; apply IH; [apply Ht|exact Hh]).
    apply Hh.
Qed.
Lemma sail_no_update_foreach {E Vars} from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, SailNoUpdate (body z vars)) →
  SailNoUpdate (System_types.Defs.foreach_ZM_up' from to step fuel vars body).
Proof.
  revert from vars. induction fuel as [|fuel IH]; intros from vars Hbody.
  - cbn [System_types.Defs.foreach_ZM_up']. destruct (from <=? to); exact I.
  - cbn [System_types.Defs.foreach_ZM_up']. destruct (from <=? to); [|exact I].
    apply sail_no_update_bind; [apply Hbody|]. intro v. apply IH, Hbody.
Qed.
Lemma sail_one_update_of_no_update {eo A} (mon : SI.iMon eo A) :
  SailNoUpdate mon → SailAtMostOneUpdate mon.
Proof.
  induction mon as [a|T out k IH]; intro Hm; [exact I|].
  cbn in Hm |- *. destruct Hm as [Ho Ht]. left. split; [exact Ho|].
  intro r. apply IH, Ht.
Qed.
Lemma sail_one_update_bind_left {eo A B} (mon : SI.iMon eo A)
    (k : A → SI.iMon eo B) :
  SailNoUpdate mon → (∀ a, SailAtMostOneUpdate (k a)) →
  SailAtMostOneUpdate (SI.iMon_bind mon k).
Proof.
  revert B k. induction mon as [a|T out km IH]; intros B k Hm Hk.
  - apply Hk.
  - cbn in Hm |- *. destruct Hm as [Ho Ht]. left. split; [exact Ho|].
    intro r. apply IH; [apply Ht|exact Hk].
Qed.
Lemma sail_one_update_bind_right {eo A B} (mon : SI.iMon eo A)
    (k : A → SI.iMon eo B) :
  SailAtMostOneUpdate mon → (∀ a, SailNoUpdate (k a)) →
  SailAtMostOneUpdate (SI.iMon_bind mon k).
Proof.
  revert B k. induction mon as [a|T out km IH]; intros B k Hm Hk.
  - apply sail_one_update_of_no_update, Hk.
  - cbn in Hm |- *. destruct Hm as [[Ho Ht]|Ht].
    + left. split; [exact Ho|]. intro r. apply IH; [apply Ht|exact Hk].
    + right. intro r. apply sail_no_update_bind; [apply Ht|exact Hk].
Qed.
Lemma sail_one_update_try_catch {A E1 E2}
    (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  SailAtMostOneUpdate mon → (∀ e, SailNoUpdate (h e)) →
  SailAtMostOneUpdate (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hm Hh; [exact I|].
  cbn in Hm |- *. destruct out; cbn in Hm |- *;
    try (destruct Hm as [[Ho Ht]|Ht];
      [left; split; [exact Ho|]; intro r; apply IH; [apply Ht|exact Hh]
      |right; intro r; apply sail_no_update_try_catch; [apply Ht|exact Hh]]).
  apply sail_one_update_of_no_update, Hh.
Qed.
Ltac sail_update_head t :=
  lazymatch t with ?f ?x => sail_update_head f | _ => t end.
Create HintDb sail_no_update.
Create HintDb sail_one_update.

Ltac solve_sail_no_update :=
  first [solve [eauto 1 with sail_no_update] |
  lazymatch goal with
  | |- True => exact I
  | |- SailNoUpdate (SI.Ret _) => exact I
  | |- SailNoUpdate (SI.Next ?out ?k) =>
      split; [cbn [SailOutcomeNoUpdate]; exact I|intro; solve_sail_no_update]
  | |- SailNoUpdate (SI.iMon_bind _ _) =>
      apply sail_no_update_bind; [solve_sail_no_update|intro; solve_sail_no_update]
  | |- SailNoUpdate (System_types.Defs.bind _ _) =>
      apply sail_no_update_bind; [solve_sail_no_update|intro; solve_sail_no_update]
  | |- SailNoUpdate (System_types.Defs.bind0 _ _) =>
      apply sail_no_update_bind; [solve_sail_no_update|intro; solve_sail_no_update]
  | |- SailNoUpdate (System_types.Defs.try_catch _ _) =>
      apply sail_no_update_try_catch; [solve_sail_no_update|intro; solve_sail_no_update]
  | |- SailNoUpdate (System_types.Defs.foreach_ZM_up' _ _ _ _ _ _) =>
      apply sail_no_update_foreach; intros; solve_sail_no_update
  | |- SailNoUpdate (match ?x with _ => _ end) =>
      destruct x; solve_sail_no_update
  | |- SailNoUpdate ?mon =>
      let hd := sail_update_head mon in
      let mon' := eval unfold hd in mon in
      let mon'' := eval cbv beta iota zeta in mon' in
      change (SailNoUpdate mon''); solve_sail_no_update
  end].
Ltac solve_sail_one_update :=
  first [solve [eauto 1 with sail_one_update] |
  lazymatch goal with
  | |- SailAtMostOneUpdate (SI.Ret _) => exact I
  | |- SailAtMostOneUpdate (SI.Next ?out ?k) =>
      first [right; intro; solve_sail_no_update |
        left; split; [cbn [SailOutcomeNoUpdate]; exact I|intro; solve_sail_one_update]]
  | |- SailAtMostOneUpdate (SI.iMon_bind _ _) =>
      first [apply sail_one_update_bind_left;
        [solve_sail_no_update|intro; solve_sail_one_update] |
        apply sail_one_update_bind_right;
        [solve_sail_one_update|intro; solve_sail_no_update]]
  | |- SailAtMostOneUpdate (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind; solve_sail_one_update
  | |- SailAtMostOneUpdate (System_types.Defs.bind0 _ _) =>
      unfold System_types.Defs.bind0, System_types.Defs.bind; solve_sail_one_update
  | |- SailAtMostOneUpdate (System_types.Defs.try_catch _ _) =>
      apply sail_one_update_try_catch; [solve_sail_one_update|intro; solve_sail_no_update]
  | |- SailAtMostOneUpdate (match ?x with _ => _ end) =>
      destruct x; solve_sail_one_update
  | |- SailAtMostOneUpdate ?mon =>
      let hd := sail_update_head mon in
      let mon' := eval unfold hd in mon in
      let mon'' := eval cbv beta iota zeta in mon' in
      change (SailAtMostOneUpdate mon''); solve_sail_one_update
  end].
Lemma sail_no_update_translation va size acc :
  SailNoUpdate (System.translate_address va size acc).
Proof. solve_sail_no_update. Qed.
#[local] Hint Resolve sail_no_update_translation : sail_no_update.
Lemma sail_no_update_decode opcode : SailNoUpdate (System.decode opcode).
Proof. solve_sail_no_update. Qed.
#[local] Hint Resolve sail_no_update_decode : sail_no_update.
Lemma sail_one_update_execute instr : SailAtMostOneUpdate (System.execute instr).
Proof. solve_sail_one_update. Qed.
#[local] Hint Resolve sail_one_update_execute : sail_one_update.
Lemma sail_one_update_fetch_and_execute :
  SailAtMostOneUpdate (System.fetch_and_execute ()).
Proof. solve_sail_one_update. Qed.
