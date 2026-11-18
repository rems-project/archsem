(******************************************************************************)
(* Walk-address insensitivity of the Sail translation                        *)
(******************************************************************************)
From ASCommon Require Import Options Common FMon.
From ArchSemArm Require Import ArmInst.
From SailStdpp Require Import ConcurrencyInterfaceBuiltinsV2.
From SailTinyArm Require Import System.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.

(** Instruction monads that cannot observe the table addresses of a
    translation walk.

    [TSafe mon] (on ArchSem instruction monads): at every translation start,
    the rest of the instruction is related to itself by [WSafe] for each TTBR
    that may provide the root. [WSafe rr lvl t1 t2]: [t1] and [t2] reach the
    same translation end with the same continuation when register reads of
    [rr] return arbitrary values to each side and walk reads return
    descriptors related by [rel_at] at the current walk level.

    [STSafe] and [SWSafe] are the same properties on Sail monads, closed
    under the Sail combinators. [sail_tsafe] transports them through
    [iMon_from_Sail]. *)

Module VMWalkSail.

(** * Related descriptors *)

(** The descriptor value Sail reads from the bytes of a walk read *)
Definition conv (v : bv 64) : bv 64 :=
  from_bytes_le 8 (System_types.Defs.bytes_of_bv (n := 8) v).

Definition rel_at (lvl : nat) (v1 v2 : bv 64) : Prop :=
  v1 = v2 ∨
  (decode_desc_type (conv v1) (Z.of_nat lvl) = DescriptorType_Table ∧
   decode_desc_type (conv v2) (Z.of_nat lvl) = DescriptorType_Table ∧
   extract_perms_table (conv v1) = extract_perms_table (conv v2)).

Definition mres_rel (lvl : nat) {a1 b1 a2 b2 : N}
    (r1 : result abort (bv a1 * bv b1)) (r2 : result abort (bv a2 * bv b2)) : Prop :=
  ∃ h1 h2 x1 x2 g1 g2, r1 = Ok (x1, g1) ∧ r2 = Ok (x2, g2) ∧
    bv_unsigned x1 = bv_unsigned h1 ∧ bv_unsigned x2 = bv_unsigned h2 ∧ rel_at lvl h1 h2.

Definition is_ttbr (r : reg) : Prop := r = TTBR0_EL1 ∨ r = TTBR1_EL1.

Definition not_start (out : outcome) : Prop := ∀ s, out ≠ TranslationStart s.

(** * ArchSem instruction monads *)

Inductive TSafe {A : Type} : iMon A → Prop :=
| TSRet a : TSafe (Ret a)
| TSNext (out : outcome) k : not_start out → (∀ r, TSafe (k r)) → TSafe (Next (inl out) k)
| TSChoice (c : MChoice) k : (∀ r, TSafe (k r)) → TSafe (Next (inr c) k)
| TSStart s k : (∀ rr, is_ttbr rr → WSafe rr 0 (k ()) (k ())) →
    TSafe (Next (inl (TranslationStart s)) k)
with WSafe {A : Type} : reg → nat → iMon A → iMon A → Prop :=
| WSRead rr lvl reg racc (k1 k2 : reg_type reg → iMon A) :
    (∀ v1 v2, (reg ≠ rr → v1 = v2) → WSafe rr lvl (k1 v1) (k2 v2)) →
    WSafe rr lvl (Next (inl (RegRead reg racc)) k1) (Next (inl (RegRead reg racc)) k2)
| WSMem rr lvl mr1 mr2 k1 k2 :
    MemReq.access_kind mr2 = MemReq.access_kind mr1 →
    MemReq.address_space mr2 = MemReq.address_space mr1 →
    MemReq.size mr2 = MemReq.size mr1 → MemReq.num_tag mr2 = MemReq.num_tag mr1 →
    is_ifetch (MemReq.access_kind mr1) = false → is_explicit (MemReq.access_kind mr1) = false →
    (∀ r1 r2, mres_rel lvl r1 r2 → WSafe rr (S lvl) (k1 r1) (k2 r2)) →
    WSafe rr lvl (Next (inl (MemRead mr1)) k1) (Next (inl (MemRead mr2)) k2)
| WSEnd rr lvl te k : (∀ r, TSafe (k r)) →
    WSafe rr lvl (Next (inl (TranslationEnd te)) k) (Next (inl (TranslationEnd te)) k)
| WSFail rr lvl s k t : WSafe rr lvl (Next (inl (GenericFail s)) k) t
| WSChoice rr lvl (c : MChoice) k1 k2 : (∀ r, WSafe rr lvl (k1 r) (k2 r)) →
    WSafe rr lvl (Next (inr c) k1) (Next (inr c) k2).

Scheme TSafe_mut := Induction for TSafe Sort Prop
  with WSafe_mut := Induction for WSafe Sort Prop.
Combined Scheme TW_mut from TSafe_mut, WSafe_mut.

Lemma tw_bind {A B} :
  (∀ (m : iMon A), TSafe m → ∀ (f : A → iMon B), (∀ x, TSafe (f x)) → TSafe (m ≫= f)) ∧
  (∀ rr lvl (t1 t2 : iMon A), WSafe rr lvl t1 t2 → ∀ (f : A → iMon B), (∀ x, TSafe (f x)) →
    WSafe rr lvl (t1 ≫= f) (t2 ≫= f)).
Proof.
  apply (TW_mut A (λ m _, ∀ f, _ → _) (λ rr lvl t1 t2 _, ∀ f, _ → _)); intros; cbn.
  all: try (constructor; eauto; fail). all: auto.
Qed.

(** * Sail monads *)

(** * Sail monads *)

Definition snot_start {eo T} (o : SI.outcome eo T) : Prop :=
  match o with SI.TranslationStart _ => False | _ => True end.

Definition smres_rel (lvl : nat) {a1 b1 a2 b2 : N}
    (r1 : (bv a1 * bv b1 + abort)%type) (r2 : (bv a2 * bv b2 + abort)%type) : Prop :=
  ∃ h1 h2 x1 x2 g1 g2, r1 = inl (x1, g1) ∧ r2 = inl (x2, g2) ∧
    bv_unsigned x1 = bv_unsigned h1 ∧ bv_unsigned x2 = bv_unsigned h2 ∧ rel_at lvl h1 h2.

Section Sail.
Context {E : Type}.
Local Notation smon := (SI.iMon (λ _, E)).

(** [VR] relates the values returned at the end of related computations,
    [VE] the exceptions they may throw, with the current walk level. *)
Inductive STSafe {A : Type} : smon A → Prop :=
| STRet a : STSafe (SI.Ret a)
| STNext T (o : SI.outcome (λ _, E) T) k : snot_start o → (∀ r, STSafe (k r)) →
    STSafe (SI.Next o k)
| STStart s k :
    (∀ rr, is_ttbr rr → SWSafe rr 0 (λ _ _ _, False) (λ _ _, False) (k ()) (k ())) →
    STSafe (SI.Next (SI.TranslationStart s) k)
with SWSafe {A : Type} :
    reg → nat → (nat → A → A → Prop) → (nat → E → Prop) → smon A → smon A → Prop :=
| SWRet rr lvl VR VE a1 a2 : VR lvl a1 a2 → SWSafe rr lvl VR VE (SI.Ret a1) (SI.Ret a2)
| SWRead rr lvl VR VE reg racc (k1 k2 : System_types.Arch.reg_type reg → smon A) :
    (∀ v1 v2, (reg ≠ rr → v1 = v2) → SWSafe rr lvl VR VE (k1 v1) (k2 v2)) →
    SWSafe rr lvl VR VE (SI.Next (SI.RegRead reg racc) k1) (SI.Next (SI.RegRead reg racc) k2)
| SWMem rr lvl VR VE mr1 mr2 k1 k2 :
    SI.MemReq.access_kind mr2 = SI.MemReq.access_kind mr1 →
    SI.MemReq.address_space mr2 = SI.MemReq.address_space mr1 →
    SI.MemReq.size mr2 = SI.MemReq.size mr1 → SI.MemReq.num_tag mr2 = SI.MemReq.num_tag mr1 →
    is_ifetch (SI.MemReq.access_kind mr1) = false →
    is_explicit (SI.MemReq.access_kind mr1) = false →
    (∀ r1 r2, smres_rel lvl r1 r2 → SWSafe rr (S lvl) VR VE (k1 r1) (k2 r2)) →
    SWSafe rr lvl VR VE (SI.Next (SI.MemRead mr1) k1) (SI.Next (SI.MemRead mr2) k2)
| SWEnd rr lvl VR VE te k : (∀ r, STSafe (k r)) →
    SWSafe rr lvl VR VE (SI.Next (SI.TranslationEnd te) k) (SI.Next (SI.TranslationEnd te) k)
| SWFail rr lvl VR VE s k t : SWSafe rr lvl VR VE (SI.Next (SI.GenericFail s) k) t
| SWExn rr lvl VR VE T (e : E) (k1 k2 : T → smon A) : VE lvl e →
    SWSafe rr lvl VR VE (SI.Next (SI.ExtraOutcome (A := T) e) k1)
      (SI.Next (SI.ExtraOutcome (A := T) e) k2).

Scheme STSafe_mut := Induction for STSafe Sort Prop
  with SWSafe_mut := Induction for SWSafe Sort Prop.
Combined Scheme STW_mut from STSafe_mut, SWSafe_mut.

Lemma stw_bind {A B} :
  (∀ (m : smon A), STSafe m → ∀ (f : A → smon B), (∀ x, STSafe (f x)) →
    STSafe (SI.iMon_bind m f)) ∧
  (∀ rr lvl VR VE (t1 t2 : smon A), SWSafe rr lvl VR VE t1 t2 →
    ∀ (f : A → smon B) VR', (∀ x, STSafe (f x)) →
    (∀ lvl' a1 a2, VR lvl' a1 a2 → SWSafe rr lvl' VR' VE (f a1) (f a2)) →
    SWSafe rr lvl VR' VE (SI.iMon_bind t1 f) (SI.iMon_bind t2 f)).
Proof.
  apply (STW_mut A (λ m _, ∀ f, _ → _) (λ rr lvl VR VE t1 t2 _, ∀ f VR', _ → _ → _));
    intros; cbn.
  all: try (constructor; eauto; fail). all: auto.
  apply STStart. intros rr Hrr. apply H; [exact Hrr|exact H0|intros ? ? ? []].
Qed.

End Sail.

Lemma stw_try_catch {E1 E2 A} :
  (∀ (m : SI.iMon (λ _, E1) A), STSafe m →
    ∀ (h : E1 → SI.iMon (λ _, E2) A), (∀ e, STSafe (h e)) →
    STSafe (System_types.Defs.try_catch m h)) ∧
  (∀ rr lvl VR VE (t1 t2 : SI.iMon (λ _, E1) A), SWSafe rr lvl VR VE t1 t2 →
    ∀ (h : E1 → SI.iMon (λ _, E2) A) VE', (∀ e, STSafe (h e)) →
    (∀ lvl' e, VE lvl' e → SWSafe rr lvl' VR VE' (h e) (h e)) →
    SWSafe rr lvl VR VE' (System_types.Defs.try_catch t1 h) (System_types.Defs.try_catch t2 h)).
Proof.
  apply (STW_mut A (λ m _, ∀ h, _ → _) (λ rr lvl VR VE t1 t2 _, ∀ h VE', _ → _ → _));
    intros; cbn.
  - constructor.
  - destruct o; cbn in *; try contradiction; try (constructor; [exact I|]; intro; auto); auto.
  - apply STStart. intros rr Hrr. apply H; [exact Hrr|exact H0|intros ? ? []].
  - constructor. assumption.
  - constructor. intros. apply H; auto.
  - constructor; auto.
  - constructor. intros. auto.
  - constructor.
  - auto.
Qed.

Lemma stsafe_foreach {E Vars} from to step n (vars : Vars) (body : Z → Vars → SI.iMon (λ _, E) Vars) :
  (∀ z v, STSafe (body z v)) →
  STSafe (System_types.Defs.foreach_ZM_up' from to step n vars body).
Proof.
  intro Hb. revert from vars. induction n as [|n IH]; intros from vars; cbn.
  all: destruct (from <=? to)%Z; try constructor.
  apply stw_bind; auto.
Qed.

(** * Transport to ArchSem instruction monads *)

Section Transport.
Context (nondet : bool).
Local Notation interp := (IMonFromSail.iMon_from_Sail nondet).

Lemma interp_tsafe {E T} (o : SI.outcome (λ _, E) T) :
  snot_start o → TSafe (IMonFromSail.Sail_outcome_interp nondet o).
Proof.
  intro Hns. destruct o; cbn in *; try contradiction.
  all: repeat first
    [ apply TSRet
    | apply TSChoice; intro
    | apply TSNext; [intros ? [=]|intro]
    | progress cbn
    | match goal with |- context [if ?b then _ else _] => destruct b end
    | match goal with |- context [match ?x with _ => _ end] => destruct x end ].
  all: unfold IMonFromSail.Sail_choose, IMonFromSail.Sail_nochoose; destruct ty.
  all: repeat first
    [ apply TSRet
    | apply TSChoice; intro
    | apply TSNext; [intros ? [=]|intro]
    | progress cbn
    | match goal with |- context [if ?b then _ else _] => destruct b end
    | match goal with |- context [match ?x with _ => _ end] => destruct x end ].
Qed.

Lemma sail_tsafe {E A} :
  (∀ (t : SI.iMon (λ _, E) A), STSafe t → TSafe (interp t)) ∧
  (∀ rr lvl VR VE (t1 t2 : SI.iMon (λ _, E) A), SWSafe rr lvl VR VE t1 t2 →
    (∀ l a1 a2, ¬ VR l a1 a2) → (∀ l e, ¬ VE l e) →
    WSafe rr lvl (interp t1) (interp t2)).
Proof.
  apply (STW_mut A (λ t _, _) (λ rr lvl VR VE t1 t2 _, _ → _ → _)); intros; cbn.
  - constructor.
  - apply tw_bind; [apply interp_tsafe; exact s|exact H].
  - apply TSStart. intros rr Hrr. apply H; [exact Hrr|intros ? ? ? []|intros ? ? []].
  - exfalso. eapply H; eassumption.
  - apply WSRead. intros. apply H; auto.
  - eapply WSMem; cbn; auto.
    intros r1 r2 (h1 & h2 & x1 & x2 & g1 & g2 & -> & -> & Hx1 & Hx2 & Hh). cbn.
    apply H; auto. exists h1, h2, x1, x2, g1, g2. auto.
  - apply WSEnd. intro r. apply H.
  - apply WSFail.
  - exfalso. eapply H0; eassumption.
Qed.
End Transport.

(** * The Sail translation walk *)

Ltac wcbn := cbn -[System_types.Defs.bytes_of_bv from_bytes_le decode_desc_type
  extract_perms_table check_permission get_TTEntryAddress leaf_access_flag_set
  leaf_dirty_bit_set extract_perms_leaf].

Ltac sw_read :=
  match goal with |- SWSafe ?rr ?l _ _ (SI.Next (SI.RegRead ?r ?a) _) _ =>
    apply (SWRead rr l _ _ r a) end.

Ltac sw_mem :=
  match goal with |- SWSafe ?rr ?l _ _ (SI.Next (SI.MemRead ?m1) _) (SI.Next (SI.MemRead ?m2) _) =>
    apply (SWMem rr l _ _ m1 m2) end.


Ltac level_step :=
  let h1 := fresh "h" in let h2 := fresh "h" in
  let Hx1 := fresh "Hx" in let Hx2 := fresh "Hx" in let Hh := fresh "Hh" in
  intros ? ? (h1 & h2 & ? & ? & ? & ? & -> & -> & Hx1 & Hx2 & Hh);
  apply bv_eq in Hx1, Hx2; subst; wcbn;
  change (from_bytes_le (__id 8) (System_types.Defs.bytes_of_bv (n := 8) h1)) with (conv h1);
  change (from_bytes_le (__id 8) (System_types.Defs.bytes_of_bv (n := 8) h2)) with (conv h2);
  let Hd1 := fresh "Hd" in let Hd2 := fresh "Hd" in let Hp := fresh "Hp" in
  destruct Hh as [<-|(Hd1 & Hd2 & Hp)];
  [|cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in Hd1, Hd2; rewrite Hd1, Hd2; rewrite ?Hp].

Ltac sw_go Hrr := repeat first
  [ progress wcbn
  | apply SWFail
  | apply SWRet; reflexivity
  | sw_read; let He := fresh "He" in intros ? ? He;
      rewrite He by (destruct Hrr as [-> | ->]; discriminate)
  | sw_mem; [reflexivity..|level_step]
  | match goal with |- context [System_types.Defs.assert_exp' ?b _] =>
      let b' := eval vm_compute in b in progress change b with b' end
  | match goal with |- context [@System_types.Defs.foreach_ZM_up' ?E ?V ?f ?t ?s ?n _ _] =>
      let f' := eval vm_compute in f in let n' := eval vm_compute in n in
      progress change (@System_types.Defs.foreach_ZM_up' E V f t s n) with
        (@System_types.Defs.foreach_ZM_up' E V f' t s n') end
  | match goal with |- context [match ?x with _ => _ end] => destruct x end ].

(** [pgt_walk] returns the same address descriptor when the TTBR read and the
    walk reads return related values. The TTBR value and the table addresses
    only determine the addresses of the following walk reads. *)
Lemma walk_ws rr va acc :
  is_ttbr rr →
  SWSafe rr 0 (λ _ a1 a2, a1 = a2) (λ _ _, False) (pgt_walk va acc) (pgt_walk va acc).
Proof.
  intro Hrr. unfold pgt_walk, System_types.Defs.catch_early_return, get_translation_base_address.
  wcbn. destruct (get_VARange va); wcbn.
  all: sw_read; intros ? ? _.
  all: sw_go Hrr.
Qed.

Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.

Ltac scbn := cbn -[System_types.Defs.bytes_of_bv from_bytes_le translate_address pgt_walk].

Ltac st_step :=
  first
  [ apply STRet
  | progress intros
  | match goal with |- STSafe (SI.Next ?o ?k) => apply (STNext _ o k); [exact I|intro] end
  | match goal with |- STSafe (SI.iMon_bind _ _) => apply (proj1 stw_bind); [|intro] end
  | match goal with |- STSafe (System_types.Defs.try_catch _ _) =>
      apply (proj1 stw_try_catch); [|intro] end
  | match goal with |- STSafe (System_types.Defs.foreach_ZM_up' _ _ _ _ _ _) =>
      apply stsafe_foreach; intros end
  | progress scbn
  | match goal with |- context [match ?x with _ => _ end] => destruct x end
  | match goal with |- STSafe ?t => let h := head_of t in progress unfold h end ].

Ltac sw_end :=
  match goal with |- SWSafe ?rr ?l ?VR ?VE (SI.Next (SI.TranslationEnd ?te) ?k) _ =>
    apply (SWEnd rr l VR VE te k) end.

Lemma st_translate va sz acc : STSafe (translate_address va sz acc).
Proof.
  unfold translate_address. scbn.
  repeat st_step.
  all: match goal with |- STSafe (SI.Next (SI.TranslationStart ?s) ?k) => apply (STStart s k) end.
  all: intros rr Hrr; scbn.
  all: destruct (va_out_of_range va); scbn.
  all: try (eapply (proj2 stw_bind); [apply walk_ws, Hrr| |]).
  all: try (intros ? ? ? ->; scbn).
  all: try (sw_end; intro).
  all: repeat st_step.
Qed.

(** * The Sail instruction *)

Ltac st_step' := first [apply st_translate | st_step].

Lemma st_program : STSafe (fetch_and_execute tt).
Proof.
  unfold fetch_and_execute. repeat st_step'.
Qed.

(** At each translation start of the Sail instruction, the rest of the
    instruction cannot distinguish walks that differ only in the TTBR value
    and in table addresses. *)
Theorem sail_tiny_arm_sem_tsafe nondet : TSafe (sail_tiny_arm_sem nondet).
Proof. exact (proj1 (sail_tsafe nondet) _ st_program). Qed.

End VMWalkSail.
