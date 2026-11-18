(******************************************************************************)
(* Positive-sized memory writes from the Sail instruction semantics            *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT.
From ArchSemArm Require Import ArmInst VMPromising.
From SailTinyArm Require Import System.
From ArchSemArm.Proof Require Import PromiseFirstSailSyntax PromiseFirstSailExecution
  PromiseFirstVMExecutionCurrent.
#[local] Open Scope stdpp.

Module VMEventValidity.

Definition sail_outcome_positive {eo A} (out : SI.outcome eo A) : Prop :=
  match out with SI.MemWrite req _ _ => (0 < SI.MemReq.size req)%N | _ => True end.

(** The postcondition records decoder facts needed by instruction execution. *)
Fixpoint sail_positive {eo A} (Q : A → Prop) (mon : SI.iMon eo A) : Prop :=
  match mon with
  | SI.Ret a => Q a
  | SI.Next (SI.ExtraOutcome _) _ => True
  | SI.Next out k => sail_outcome_positive out ∧ ∀ r, sail_positive Q (k r)
  end.

Lemma sail_bind {eo A B} (P : A → Prop) (Q : B → Prop) (mon : SI.iMon eo A) k :
  sail_positive P mon → (∀ a, P a → sail_positive Q (k a)) →
  sail_positive Q (SI.iMon_bind mon k).
Proof.
  induction mon as [a|T out km IH]; intros Hm Hk; cbn in Hm |- *.
  - apply Hk, Hm.
  - destruct out; cbn in Hm |- *; try exact I;
      (destruct Hm as [Ho Ht]; split; [exact Ho|]; intro r; apply IH; auto).
Qed.

Lemma sail_try_catch {A E1 E2} (Q : A → Prop)
    (mon : System_types.Defs.monad E1 A) (h : E1 → System_types.Defs.monad E2 A) :
  sail_positive Q mon → (∀ e, sail_positive Q (h e)) →
  sail_positive Q (System_types.Defs.try_catch mon h).
Proof.
  induction mon as [a|T out k IH]; intros Hm Hh; cbn in Hm |- *.
  - exact Hm.
  - destruct out; cbn in Hm |- *;
      first [apply Hh|destruct Hm as [Ho Ht]; split; [exact Ho|]; intro r; apply IH; auto].
Qed.

Lemma sail_no_update {eo A} (mon : SI.iMon eo A) :
  SailNoUpdate mon → sail_positive (λ _, True) mon.
Proof.
  induction mon as [a|T out k IH]; intro H; [exact I|].
  destruct H as [Ho Ht]. destruct out; cbn in Ho |- *; try exact I; try contradiction;
    (split; [exact I|]; intro r; apply IH, Ht).
Qed.

Definition decoded_size (instr : ast) : Prop :=
  match instr with
  | Store (size, _, _, _, _, _) | AtomicRMW (size, _, _, _, _, _, _) => (0 ≤ size)%Z
  | _ => True
  end.

Ltac solve_decode_size :=
  lazymatch goal with
  | |- True => exact I
  | |- (0 ≤ Operators_mwords.uint ?v)%Z => unfold Operators_mwords.uint; lia
  | |- decoded_size (match ?x with _ => _ end) => destruct x; solve_decode_size
  | |- decoded_size ?i =>
      first [progress cbn [decoded_size]; solve_decode_size|
        let hd := sail_head i in unfold hd; solve_decode_size]
  | |- sail_positive _ (SI.Ret _) => cbn [sail_positive]; solve_decode_size
  | |- sail_positive _ (SI.Next _ _) =>
      split; [cbn [sail_outcome_positive]; exact I|intro; solve_decode_size]
  | |- sail_positive _ (SI.iMon_bind _ _) =>
      apply (sail_bind (λ _, True)); [apply sail_no_update; solve_sail_no_update|];
      intros ? _; solve_decode_size
  | |- sail_positive _ (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind; solve_decode_size
  | |- sail_positive _ (System_types.Defs.bind0 _ _) =>
      unfold System_types.Defs.bind0, System_types.Defs.bind; solve_decode_size
  | |- sail_positive _ (match ?x with _ => _ end) => destruct x; solve_decode_size
  | |- match ?x with _ => _ end => destruct x; solve_decode_size
  | |- sail_positive ?Q ?mon =>
      let hd := sail_head mon in
      let mon' := eval unfold hd in mon in
      let mon'' := eval cbv beta iota zeta in mon' in
      change (sail_positive Q mon''); solve_decode_size
  end.

Lemma decode_size opcode : sail_positive decoded_size (System.decode opcode).
Proof. solve_decode_size. Qed.

Lemma sail_lift {A R E} (Q : A → Prop) (mon : System_types.Defs.monad E A) :
  sail_positive Q mon → sail_positive Q (System_types.Defs.liftR (R := R) mon).
Proof.
  intro H. unfold System_types.Defs.liftR. apply sail_try_catch; [exact H|].
  intro e. exact I.
Qed.

Lemma sail_foreach {E Vars} from to step fuel (vars : Vars)
    (body : Z → Vars → System_types.Defs.monad E Vars) :
  (∀ z v, sail_positive (λ _, True) (body z v)) →
  sail_positive (λ _, True) (System_types.Defs.foreach_ZM_up' from to step fuel vars body).
Proof.
  revert from vars. induction fuel as [|fuel IH]; intros from vars Hb;
    cbn [System_types.Defs.foreach_ZM_up']; destruct (from <=? to)%Z; try exact I.
  apply (sail_bind (λ _, True)); [apply Hb|]. intros v _. apply IH, Hb.
Qed.

Create HintDb vm_sail_positive.
#[local] Hint Extern 1 (sail_positive (λ _, True) (System.translate_address _ _ _)) =>
  apply sail_no_update, sail_no_update_translation : vm_sail_positive.

Ltac solve_sail_positive :=
  first [solve [eauto 2 with vm_sail_positive]|
  lazymatch goal with
  | H : Empty_set |- _ => destruct H
  | |- True => exact I
  | |- sail_positive _ (SI.Ret _) => exact I
  | |- sail_positive _ (SI.Next (SI.ExtraOutcome _) _) => exact I
  | |- sail_positive _ (SI.Next _ _) =>
      split; [cbn [sail_outcome_positive SI.MemReq.size]; first [exact I|lia]|intro; solve_sail_positive]
  | |- sail_positive _ (SI.iMon_bind (System_types.Defs.liftR (System.decode _)) _) =>
      apply (sail_bind decoded_size); [apply sail_lift, decode_size|];
      intros instr Hdecoded; solve_sail_positive
  | |- sail_positive _ (SI.iMon_bind (System.decode _) _) =>
      apply (sail_bind decoded_size); [apply decode_size|];
      intros instr Hdecoded; solve_sail_positive
  | |- sail_positive _ (SI.iMon_bind _ _) =>
      apply (sail_bind (λ _, True)); [solve_sail_positive|intros ? _; solve_sail_positive]
  | |- sail_positive _ (System_types.Defs.bind _ _) =>
      unfold System_types.Defs.bind; solve_sail_positive
  | |- sail_positive _ (System_types.Defs.bind0 _ _) =>
      unfold System_types.Defs.bind0, System_types.Defs.bind; solve_sail_positive
  | |- sail_positive _ (System_types.Defs.try_catch _ _) =>
      apply sail_try_catch; [solve_sail_positive|intro; solve_sail_positive]
  | |- sail_positive _ (System_types.Defs.liftR _) => apply sail_lift; solve_sail_positive
  | |- sail_positive _ (System_types.Defs.foreach_ZM_up' _ _ _ _ _ _) =>
      apply sail_foreach; intros; solve_sail_positive
  | |- sail_positive _ (match ?x with _ => _ end) => destruct x; solve_sail_positive
  | |- sail_positive ?Q ?mon =>
      let hd := sail_head mon in
      let mon' := eval unfold hd in mon in
      let mon'' := eval cbv beta iota zeta in mon' in
      change (sail_positive Q mon''); solve_sail_positive
  end].

Lemma wmem_positive size addr val acc :
  (0 < size)%Z → sail_positive (λ _, True) (System.wMem size addr val acc).
Proof. intro Hsize. solve_sail_positive. Qed.
#[local] Hint Resolve wmem_positive : vm_sail_positive.

Lemma pow2_positive size : (0 ≤ size)%Z → (0 < Values.pow2 size)%Z.
Proof. intro H. unfold Values.pow2, Values.pow. apply Z.pow_pos_nonneg; lia. Qed.

Lemma store_positive size t n offset release s : (0 ≤ size)%Z →
  sail_positive (λ _, True) (System.execute_Store size t n offset release s).
Proof.
  intro Hsize. pose proof (pow2_positive size Hsize) as Hpow.
  solve_sail_positive.
Qed.

Lemma atomic_positive size s t n op acq rel : (0 ≤ size)%Z →
  sail_positive (λ _, True) (System.execute_AtomicRMW size s t n op acq rel).
Proof.
  intro Hsize. pose proof (pow2_positive size Hsize) as Hpow.
  solve_sail_positive.
Qed.
#[local] Hint Resolve store_positive atomic_positive : vm_sail_positive.

Lemma execute_positive instr : decoded_size instr →
  sail_positive (λ _, True) (System.execute instr).
Proof.
  destruct instr;
    repeat match goal with x : (_ * _)%type |- _ => destruct x end;
    cbn [decoded_size System.execute]; intro Hsize; solve_sail_positive.
Qed.
#[local] Hint Resolve execute_positive : vm_sail_positive.

Lemma fetch_execute_positive : sail_positive (λ _, True) (System.fetch_and_execute ()).
Proof. solve_sail_positive. Qed.

Definition outcome_positive (out : outcome) : Prop :=
  match out with MemWrite req _ _ => (0 < MemReq.size req)%N | _ => True end.

Fixpoint positive {A} (mon : iMon A) : Prop :=
  match mon with
  | Ret _ => True
  | Next (inl out) k => outcome_positive out ∧ ∀ r, positive (k r)
  | Next (inr _) k => ∀ r, positive (k r)
  end.

Lemma positive_bind {A B} (mon : iMon A) (k : A → iMon B) :
  positive mon → (∀ a, positive (k a)) → positive (mon ≫= k).
Proof.
  induction mon as [a|[out|ch] km IH]; intros Hm Hk; cbn in Hm |- *.
  - apply Hk.
  - destruct Hm as [Ho Ht]. split; [exact Ho|]. intro r. apply IH; auto.
  - intro r. apply IH; auto.
Qed.

Lemma outcome_interp_positive nondet {eo A} (out : SI.outcome eo A) :
  sail_outcome_positive out → positive (Sail_outcome_interp nondet out).
Proof.
  destruct out; intro Hout; solve_sail_outcome_shape; cbn [positive outcome_positive]; auto.
  all: destruct ty; solve_sail_outcome_shape.
Qed.

Lemma interp_positive nondet {eo A} (Q : A → Prop) (mon : SI.iMon eo A) :
  sail_positive Q mon → positive (iMon_from_Sail nondet mon).
Proof.
  induction mon as [a|T out k IH]; intro Hm; [exact I|].
  destruct out; cbn [sail_positive] in Hm;
    try (lazymatch type of Hm with _ ∧ _ => destruct Hm as [Ho Ht] end;
      cbn [iMon_from_Sail];
      apply positive_bind; [apply outcome_interp_positive, Ho|]; intro r; apply IH, Ht).
  cbn [iMon_from_Sail]. solve_sail_outcome_shape.
Qed.

Theorem sail_tiny_arm_positive nondet : positive (sail_tiny_arm_sem nondet).
Proof. apply (interp_positive nondet (λ _, True)), fetch_execute_positive. Qed.

(** * Events created by successful VM instructions *)
Import VMPromising.
#[local] Typeclasses Transparent Memory.t othrow.
#[local] Instance exec_unfold : Exec.Unfold := {}.

Definition event_positive (ev : Ev.t) : Prop :=
  match ev with Ev.Msg msg => (0 < Msg.size msg)%N | _ => True end.

Definition growth (mem mem' : list Ev.t) : Prop :=
  ∃ extra, mem' = (extra ++ mem)%list ∧ Forall event_positive extra.

Lemma growth_refl mem : growth mem mem.
Proof. exists []. split; [reflexivity|constructor]. Qed.

Lemma growth_cons ev mem : event_positive ev → growth mem (ev :: mem).
Proof. intro H. exists [ev]. split; [reflexivity|constructor; [exact H|constructor]]. Qed.

Lemma growth_trans a b c : growth a b → growth b c → growth a c.
Proof.
  intros [xs [-> Hxs]] [ys [-> Hys]]. exists (ys ++ xs)%list.
  split; [apply app_assoc|apply Forall_app; auto].
Qed.

Lemma write_growth tid imem addr size macc data p p' ret :
  (0 < size)%N → Exec.elem_of_results (p', ret) (write_mem tid imem addr size macc data p) →
  growth (PPState.mem p) (PPState.mem p').
Proof.
  intros Hsize Hrun. apply VMMemoryGrowth.write_mem_growth in Hrun as [->|[pre [-> _]]].
  - apply growth_refl.
  - apply growth_cons, Hsize.
Qed.

Lemma materialize_growth tid imem pre tlbi recipient p p' time created :
  Exec.elem_of_results (p', (time, created))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient p) →
  growth (PPState.mem p) (PPState.mem p').
Proof.
  intro Hrun. apply VMMemoryGrowth.materialize_tlbi_growth in Hrun.
  destruct created; cbn in Hrun.
  - destruct Hrun as [epoch [-> _]]. apply growth_cons. exact I.
  - rewrite Hrun. apply growth_refl.
Qed.

Lemma recipients_growth tid imem pre tlbi recipients acc p p' ret :
  Exec.elem_of_results (p', ret)
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi) acc recipients p) →
  growth (PPState.mem p) (PPState.mem p').
Proof.
  revert acc p p' ret. induction recipients as [|recipient recipients IH]; intros acc p p' ret Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. apply growth_refl.
  - cbn [foldlM] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [mid [a [Hstep Htail]]].
    destruct acc as [[vs vo] cr]. unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time created] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    eapply growth_trans; [eapply materialize_growth; exact Hmat|eapply IH; exact Htail].
Qed.

Lemma tlbi_growth n tid imem viio tlbi p p' ret :
  Exec.elem_of_results (p', ret) (run_tlbi n tid imem viio tlbi p) →
  growth (PPState.mem p) (PPState.mem p').
Proof.
  intro Hrun. unfold run_tlbi in Hrun. VMMemoryGrowth.invert_execution.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply recipients_growth in H end.
  all: repeat match goal with q : PPState.t _ _ _ |- _ => destruct q end; cbn in *; assumption.
Qed.

Lemma outcome_growth n tid imem out p p' ret pre :
  outcome_positive out →
  Exec.elem_of_results (p', (ret, pre)) (run_outcome n tid imem out p) →
  growth (PPState.mem p) (PPState.mem p').
Proof.
  intros Hpositive Hrun.
  assert (Hdec : Decision (IEffectNoUpdate (inl out))) by (destruct out; cbn; typeclasses eauto).
  destruct (decide (IEffectNoUpdate (inl out))) as [Hno|Hno].
  { rewrite (VMSailMemory.outcome_no_update_mem n tid imem out p p' ret pre Hno Hrun).
    apply growth_refl. }
  destruct out; cbn in Hno, Hpositive; try contradiction.
  - match type of Hrun with Exec.elem_of_results _ (run_outcome _ _ _ (MemWrite ?mr _ _) _) =>
      destruct mr as [macc addr pas size [|ntags]] end;
      simp run_outcome in Hrun;
      VMMemoryGrowth.invert_execution.
    eapply write_growth; [exact Hpositive|eassumption].
  - simp run_outcome in Hrun. VMMemoryGrowth.invert_execution.
    eapply tlbi_growth; eassumption.
Qed.

Lemma instruction_growth {A n} (tid : fin n) imem (mon : iMon A) p p' ret :
  positive mon → Exec.elem_of_results (p', ret) (cinterp (run_outcome' n tid imem) mon p) →
  growth (PPState.mem p) (PPState.mem p').
Proof.
  revert p p' ret. induction mon as [a|[out|[choices]] k IH]; intros p p' ret Hp Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> _]. apply growth_refl.
  - destruct Hp as [Ho Hk]. cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hout Htail]]].
    apply Exec.elem_of_fmap_inv in Hout as [[v pre] [-> Hout]].
    eapply growth_trans; [eapply outcome_growth; eassumption|eapply IH; [apply Hk|exact Htail]].
  - cbn in Hrun. apply Exec.elem_of_bind_elim in Hrun as [mid [r [Hchoose Htail]]].
    apply Exec.elem_of_mchoose_inv in Hchoose as ->. eapply IH; [apply Hp|exact Htail].
Qed.

Theorem sail_instruction_growth nondet {n} (tid : fin n) imem p p' :
  Exec.elem_of_results (p', ()) (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet) p) →
  growth (PPState.mem p) (PPState.mem p').
Proof. apply instruction_growth, sail_tiny_arm_positive. Qed.

Corollary sail_fresh_event_positive nondet {n} (tid : fin n) imem p p' evs ev :
  Exec.elem_of_results (p', ()) (cinterp (run_outcome' n tid imem) (sail_tiny_arm_sem nondet) p) →
  PPState.mem p' = (evs ++ ev :: PPState.mem p)%list → event_positive ev.
Proof.
  intros Hrun Hmem. destruct (sail_instruction_growth nondet tid imem p p' Hrun) as [extra [He Hpos]].
  rewrite Hmem in He.
  change (evs ++ [ev] ++ PPState.mem p = extra ++ PPState.mem p)%list in He.
  rewrite app_assoc in He. apply app_inv_tail in He. subst extra.
  apply Forall_app in Hpos as [_ Hpos]. inversion Hpos. assumption.
Qed.

End VMEventValidity.
