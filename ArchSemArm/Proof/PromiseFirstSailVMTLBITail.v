(******************************************************************************)
(* A Sail TLBI outcome is the last effect of its instruction                 *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailSyntax PromiseFirstSailExecution
  PromiseFirstVMExecutionCurrent.
From SailTinyArm Require Import System.

Module VMTLBITail.
Definition no_tlbi_out {eo A} (out : SI.outcome eo A) : Prop :=
  match out with SI.TlbOp _ => False | _ => True end.
Fixpoint no_tlbi {eo A} (mon : SI.iMon eo A) : Prop :=
  match mon with
  | SI.Ret _ => True
  | SI.Next out k => no_tlbi_out out ∧ ∀ r, no_tlbi (k r)
  end.
Lemma no_update_no_tlbi {eo A} (mon : SI.iMon eo A) : SailNoUpdate mon → no_tlbi mon.
Proof.
  induction mon as [a|T out k IH]; intro Hmon; [exact I|].
  cbn [SailNoUpdate no_tlbi] in *. destruct Hmon as [Hout Hk]. split.
  - destruct out; cbn [SailOutcomeNoUpdate no_tlbi_out] in *; tauto.
  - intro r. apply IH, Hk.
Qed.
Lemma no_tlbi_bind {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  no_tlbi mon → (∀ a, no_tlbi (k a)) → no_tlbi (SI.iMon_bind mon k).
Proof.
  revert B k. induction mon as [a|T out km IH]; intros B k Hmon Hk; [apply Hk|].
  cbn [no_tlbi SI.iMon_bind] in *. destruct Hmon as [Hout Hkm]. split; [exact Hout|].
  intro r. apply IH; [apply Hkm|exact Hk].
Qed.
Lemma no_tlbi_try_catch {A E1 E2} (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  no_tlbi mon → (∀ e, no_tlbi (h e)) → no_tlbi (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hmon Hh; [exact I|].
  cbn [no_tlbi] in Hmon. destruct Hmon as [Ho Hk].
  destruct out; cbn [no_tlbi_out] in Ho; try contradiction;
    cbn [System_types.Defs.try_catch no_tlbi no_tlbi_out]; try apply Hh.
  all: split; [exact I|intro r; apply IH; [apply Hk|exact Hh]].
Qed.
Lemma no_tlbi_foreach {E Vars} from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z vars, no_tlbi (body z vars)) →
  no_tlbi (System_types.Defs.foreach_ZM_up' from to step fuel vars body).
Proof.
  revert from vars. induction fuel as [|fuel IH]; intros from vars Hbody.
  - cbn [System_types.Defs.foreach_ZM_up']. destruct (from <=? to); exact I.
  - cbn [System_types.Defs.foreach_ZM_up']. destruct (from <=? to); [|exact I].
    apply no_tlbi_bind; [apply Hbody|]. intro v. apply IH, Hbody.
Qed.

Ltac solve_no_tlbi := first [solve [apply no_update_no_tlbi; solve_sail_no_update] |
  lazymatch goal with
  | |- no_tlbi (SI.Ret _) => exact I
  | |- no_tlbi (SI.Next ?out ?k) =>
      split; [cbn [no_tlbi_out]; exact I|intro; solve_no_tlbi]
  | |- no_tlbi (SI.iMon_bind _ _) => apply no_tlbi_bind; [solve_no_tlbi|intro; solve_no_tlbi]
  | |- no_tlbi (System_types.Defs.bind _ _) => apply no_tlbi_bind; [solve_no_tlbi|intro; solve_no_tlbi]
  | |- no_tlbi (System_types.Defs.bind0 _ _) => apply no_tlbi_bind; [solve_no_tlbi|intro; solve_no_tlbi]
  | |- no_tlbi (System_types.Defs.try_catch _ _) => apply no_tlbi_try_catch; [solve_no_tlbi|intro; solve_no_tlbi]
  | |- no_tlbi (System_types.Defs.foreach_ZM_up' _ _ _ _ _ _) => apply no_tlbi_foreach; intros; solve_no_tlbi
  | |- no_tlbi (match ?x with _ => _ end) => destruct x; solve_no_tlbi
  | |- no_tlbi ?mon =>
      let hd := sail_head mon in let mon' := eval unfold hd in mon in
      let mon'' := eval cbv beta iota zeta in mon' in change (no_tlbi mon''); solve_no_tlbi
  end].

Definition pure {eo A} (mon : SI.iMon eo A) : Prop :=
  match mon with SI.Ret _ => True | SI.Next _ _ => False end.
Fixpoint tail {eo A} (mon : SI.iMon eo A) : Prop :=
  match mon with
  | SI.Ret _ => True
  | SI.Next out k =>
      match out with
      | SI.TlbOp _ => ∀ r, pure (k r)
      | _ => ∀ r, tail (k r)
      end
  end.

Lemma pure_tail {eo A} (mon : SI.iMon eo A) : pure mon → tail mon.
Proof. destruct mon; cbn [pure tail]; tauto. Qed.
Lemma pure_bind {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  pure mon → (∀ a, pure (k a)) → pure (SI.iMon_bind mon k).
Proof. destruct mon; cbn [pure SI.iMon_bind]; intros; [auto|contradiction]. Qed.
Lemma pure_try_catch {A E1 E2} (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) : pure mon → pure (System_types.Defs.try_catch mon h).
Proof. destruct mon; cbn [pure System_types.Defs.try_catch]; intros; [exact I|contradiction]. Qed.

Lemma no_update_tail {eo A} (mon : SI.iMon eo A) : SailNoUpdate mon → tail mon.
Proof.
  induction mon as [a|T out k IH]; intro Hmon; [exact I|].
  cbn [SailNoUpdate] in Hmon. destruct Hmon as [Hout Hk].
  destruct out; cbn [SailOutcomeNoUpdate] in Hout; try contradiction;
    cbn [tail]; intro r; apply IH, Hk.
Qed.
Lemma bind_left {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  no_tlbi mon → (∀ a, tail (k a)) → tail (SI.iMon_bind mon k).
Proof.
  revert B k. induction mon as [a|T out km IH]; intros B k Hmon Hk; [apply Hk|].
  cbn [no_tlbi] in Hmon. destruct Hmon as [Hout Hkm].
  destruct out; cbn [no_tlbi_out] in Hout; try contradiction.
  all: cbn [SI.iMon_bind tail]; intro r; apply IH; [apply Hkm|exact Hk].
Qed.
Lemma bind_right {eo A B} (mon : SI.iMon eo A) (k : A → SI.iMon eo B) :
  tail mon → (∀ a, pure (k a)) → tail (SI.iMon_bind mon k).
Proof.
  revert B k. induction mon as [a|T out km IH]; intros B k Hmon Hk; [apply pure_tail, Hk|].
  destruct out; cbn [tail] in Hmon; cbn [SI.iMon_bind tail]; intro r.
  all: first [apply IH; [apply Hmon|exact Hk]|apply pure_bind; [apply Hmon|exact Hk]].
Qed.
Lemma try_catch {A E1 E2} (mon : System_types.Defs.monad E1 A)
    (h : E1 → System_types.Defs.monad E2 A) :
  tail mon → (∀ e, tail (h e)) → tail (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hmon Hh; [exact I|].
  destruct out; cbn [tail] in Hmon; cbn [System_types.Defs.try_catch tail].
  all: first [apply Hh|intro r; first [apply IH; [apply Hmon|exact Hh]|apply pure_try_catch, Hmon]].
Qed.

Ltac solve_pure := lazymatch goal with
  | |- pure (SI.Ret _) => exact I
  | |- pure (match ?x with _ => _ end) => destruct x; solve_pure
  | |- pure ?mon =>
      let hd := sail_head mon in let mon' := eval unfold hd in mon in
      let mon'' := eval cbv beta iota zeta in mon' in change (pure mon''); solve_pure
  end.
Ltac solve_tail := first [solve [apply no_update_tail; solve_sail_no_update] |
  lazymatch goal with
  | |- tail (SI.Ret _) => exact I
  | |- tail (SI.Next ?out ?k) =>
      cbn [tail]; intro; first [solve_pure|solve_tail]
  | |- tail (SI.iMon_bind _ _) => first
      [apply bind_left; [solve_no_tlbi|intro; solve_tail]
      |apply bind_right; [solve_tail|intro; solve_pure]]
  | |- tail (System_types.Defs.bind _ _) => first
      [apply bind_left; [solve_no_tlbi|intro; solve_tail]
      |apply bind_right; [solve_tail|intro; solve_pure]]
  | |- tail (System_types.Defs.bind0 _ _) => first
      [apply bind_left; [solve_no_tlbi|intro; solve_tail]
      |apply bind_right; [solve_tail|intro; solve_pure]]
  | |- tail (System_types.Defs.try_catch _ _) => apply try_catch; [solve_tail|intro; solve_tail]
  | |- tail (match ?x with _ => _ end) => destruct x; solve_tail
  | |- tail ?mon =>
      let hd := sail_head mon in let mon' := eval unfold hd in mon in
      let mon'' := eval cbv beta iota zeta in mon' in change (tail mon''); solve_tail
  end].

Lemma execute_tlbi op shareability level reg :
  tail (System.execute_TLBInvalidation op shareability level reg).
Proof. solve_tail. Qed.
Lemma execute instr : tail (System.execute instr).
Proof. solve_tail. Qed.
Theorem fetch_and_execute : tail (System.fetch_and_execute ()).
Proof. solve_tail. Qed.
End VMTLBITail.

Module VMTLBITailInterp.
Definition pure {A} (mon : iMon A) : Prop :=
  match mon with Ret _ => True | Next _ _ => False end.
Definition no_tlbi_out (out : outcome + MChoice) : Prop :=
  match out with inl (TlbOp _) => False | _ => True end.
Fixpoint no_tlbi {A} (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next out k => no_tlbi_out out ∧ ∀ r, no_tlbi (k r)
  end.
Fixpoint tail {A} (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next out k =>
      match out with
      | inl (TlbOp _) => ∀ r, pure (k r)
      | _ => ∀ r, tail (k r)
      end
  end.
Lemma pure_tail {A} (mon : iMon A) : pure mon → tail mon.
Proof. destruct mon; cbn [pure tail]; tauto. Qed.
Lemma pure_bind {A B} (mon : iMon A) (k : A → iMon B) :
  pure mon → (∀ a, pure (k a)) → pure (mon ≫= k).
Proof. destruct mon; cbn [pure]; intros; [apply H0|contradiction]. Qed.
Lemma bind_left {A B} (mon : iMon A) (k : A → iMon B) :
  no_tlbi mon → (∀ a, tail (k a)) → tail (mon ≫= k).
Proof.
  revert B k. induction mon as [a|out km IH]; intros B k Hmon Hk; [apply Hk|].
  cbn [no_tlbi] in Hmon. destruct Hmon as [Ho Hkm].
  destruct out as [out|out]; [destruct out|]; cbn [no_tlbi_out] in Ho; try contradiction.
  all: cbn [mbind fMon_bind tail]; intro r; apply IH; [apply Hkm|exact Hk].
Qed.
Lemma bind_right {A B} (mon : iMon A) (k : A → iMon B) :
  tail mon → (∀ a, pure (k a)) → tail (mon ≫= k).
Proof.
  revert B k. induction mon as [a|out km IH]; intros B k Hmon Hk; [apply pure_tail, Hk|].
  destruct out as [out|out]; [destruct out|]; cbn [tail] in Hmon;
    cbn [mbind fMon_bind tail]; intro r.
  all: first [apply IH; [apply Hmon|exact Hk]|apply pure_bind; [apply Hmon|exact Hk]].
Qed.
Lemma outcome_no_tlbi nondet {eo A} (out : SI.outcome eo A) :
  VMTLBITail.no_tlbi_out out → no_tlbi (Sail_outcome_interp nondet out).
Proof.
  destruct out; intro Hout; try contradiction; solve_sail_outcome_shape.
  all: destruct ty; solve_sail_outcome_shape.
Qed.
Lemma outcome_tail nondet {eo A} (out : SI.outcome eo A) :
  tail (Sail_outcome_interp nondet out).
Proof.
  destruct out; solve_sail_outcome_shape.
  all: destruct ty; solve_sail_outcome_shape.
Qed.
Lemma interp_pure nondet {eo A} (mon : SI.iMon eo A) :
  VMTLBITail.pure mon → pure (iMon_from_Sail nondet mon).
Proof. destruct mon; cbn [VMTLBITail.pure]; intros; [exact I|contradiction]. Qed.
Lemma interp_tail nondet {eo A} (mon : SI.iMon eo A) :
  VMTLBITail.tail mon → tail (iMon_from_Sail nondet mon).
Proof.
  induction mon as [a|T out k IH]; intro Hmon; [exact I|].
  cbn [iMon_from_Sail]. destruct out; cbn [VMTLBITail.tail] in Hmon.
  all: first
    [ apply bind_left; [apply outcome_no_tlbi; exact I|intro r; apply IH, Hmon]
    | apply bind_right; [apply outcome_tail|intro r; apply interp_pure, Hmon] ].
Qed.
Theorem sail_tiny_arm_tail nondet : tail (sail_tiny_arm_sem nondet).
Proof. apply interp_tail, VMTLBITail.fetch_and_execute. Qed.

Section Execution.
Context (n tid : nat) (imem : memoryMap).
Local Notation ppState := (PPState.t TState.t Ev.t IIS.t).
Local Notation run := (cinterp (run_outcome' n tid imem)).

Lemma pure_run {A} (mon : iMon A) pp pp' value : pure mon →
  Exec.elem_of_results (pp', value) (run mon pp) → mon = Ret value ∧ pp' = pp.
Proof.
  destruct mon as [ret|out k]; cbn [pure]; intros Hpure Hrun; [|contradiction].
  cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> ->]. auto.
Qed.

(** The final TLBI need only establish the relation that the instruction's
    caller observes. Its intra-instruction state is discarded by [run_tid]. *)
Theorem instruction_sim {A} (mon : iMon A) (R Q : ppState → ppState → Prop) :
  tail mon →
  (∀ a b, R a b → Q a b) →
  (∀ out a b a' value, no_tlbi_out (inl out) → R a b →
    Exec.elem_of_results (a', value) (run_outcome' n tid imem out a) →
    ∃ b', Exec.elem_of_results (b', value) (run_outcome' n tid imem out b) ∧ R a' b') →
  (∀ tlbi a b a' value, R a b →
    Exec.elem_of_results (a', value) (run_outcome' n tid imem (TlbOp tlbi) a) →
    ∃ b', Exec.elem_of_results (b', value) (run_outcome' n tid imem (TlbOp tlbi) b) ∧ Q a' b') →
  ∀ a b a' value, R a b → Exec.elem_of_results (a', value) (run mon a) →
    ∃ b', Exec.elem_of_results (b', value) (run mon b) ∧ Q a' b'.
Proof.
  intros Htail Hdone Hstep Htlbi. revert Htail.
  induction mon as [ret|call k IH]; intros Htail a b a' value Hrel Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> ->].
    exists b. split; [apply Exec.elem_of_mret|apply Hdone, Hrel].
  - destruct call as [out|[choices]]; cbn in Hrun |- *.
    + apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hout Hrun]]].
      destruct out; cbn [tail] in Htail.
      all: first
        [ let Hpure := fresh "Hpure" in
          pose proof (pure_run _ _ _ _ (Htail res) Hrun) as [Hpure ->];
          destruct (Htlbi _ a b mid res Hrel Hout) as [b' [Hb HQ]];
          exists b'; split; [eapply Exec.elem_of_bind_intro; [exact Hb|rewrite Hpure; apply Exec.elem_of_mret]|exact HQ]
        | destruct (Hstep _ a b mid res I Hrel Hout) as [bmid [Hb HR]];
          destruct (IH res (Htail res) mid bmid a' value HR Hrun) as [b' [Hend HQ]];
          exists b'; split; [eapply Exec.elem_of_bind_intro; eassumption|exact HQ] ].
    + cbn [tail] in Htail.
      apply Exec.elem_of_bind_elim in Hrun as [mid [res [Hchoose Hrun]]].
      apply Exec.elem_of_mchoose_inv in Hchoose as ->.
      destruct (IH res (Htail res) a b a' value Hrel Hrun) as [b' [Hb HQ]].
      exists b'. split; [|exact HQ]. eapply Exec.elem_of_bind_intro; [|exact Hb].
      apply Exec.elem_of_mchoose.
Qed.
End Execution.
End VMTLBITailInterp.
