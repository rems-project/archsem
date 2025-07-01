From ASCommon Require Import Options.
Require Import ArmSeqModel UMSeqArm.
Require Import ArmInst FromSail.
From ASCommon Require Import Exec FMon Common GRel StateT.

Import CDestrUnfoldElemOf.
#[local] Existing Instance Exec.unfold.

#[local] Typeclasses Transparent pa_eq pa_countable.

#[global] Instance lookup_unfold_length_None {A} (l : list A) :
  LookupUnfold (length l) l None.
Proof. tcclean. induction l; done. Qed.

#[global] Instance lookup_unfold_Nil {A} (n : nat) :
  LookupUnfold n (@nil A) None.
Proof. tcclean. by destruct n. Qed.

#[global] Instance eq_Some_unfold_singleton_list_lookup {A} (x y : A) n :
  EqSomeUnfold ([x] !! n) y (x = y ∧ n = 0).
Proof. tcclean. destruct n; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal. Qed.

#[local] Instance obvTrue_isSome_Some {A} (x : A) :
  ObvTrue (is_Some (Some x)).
Proof. tcclean. by eexists. Qed.

#[local] Instance obvFalse_neg_isSome_Some {A} (x : A) :
  ObvFalse (¬ is_Some (Some x)).
Proof. tcclean. intros H. by eapply H. Qed.

#[local] Instance cdestruct_not_is_Some {A} b (x : option A) :
  CDestrSimpl b (¬ is_Some x) (x = None).
Proof. tcclean. sauto. Qed.

Instance Exec_to_state_result_list_Ok {St E A} st (e : Exec.res (St * E) (St * A)) P:
  (∀ v, SetUnfoldElemOf (st, v) e (P v)) →
  SetUnfoldElemOf (Ok st) (Exec.to_state_result_list e) (∃ v, P v).
Proof.
  tcclean.
  unfold Exec.to_state_result_list.
  set_unfold. autorewrite with pair. naive_solver.
Qed.

Instance Exec_to_state_result_list_Error {St E A} st (e : Exec.res (St * E) (St * A)) P:
  (∀ v, SetUnfoldElemOf (st, v) e.(Exec.errors) (P v)) →
  SetUnfoldElemOf (Error st) (Exec.to_state_result_list e) (∃ v, P v).
Proof.
  tcclean.
  unfold Exec.to_state_result_list.
  set_unfold. autorewrite with pair. naive_solver.
Qed.

Instance Exec_to_state_result_list {St E A} r (e : Exec.res (St * E) (St * A)) P Q:
  (∀ st v, SetUnfoldElemOf (st, v) e (P st v)) →
  (∀ st v, SetUnfoldElemOf (st, v) e.(Exec.errors) (Q st v)) →
  SetUnfoldElemOf r (Exec.to_state_result_list e)
    (match r with
    | Ok st => ∃ v, P st v
    | Error st => ∃ v, Q st v
    end) | 999 .
Proof. tcclean. destruct r; set_solver. Qed.

Lemma finterp_inv_induct `{Effect Eff} {St E A}
  (handler : fHandler Eff (Exec.t St E)) (mon : fMon Eff A)
  (I : result St St → Prop) (initSt : St)
  : I (Ok initSt)
    → (∀ st call, I (Ok st) → ∀ st' ∈ Exec.to_state_result_list $ handler call st, I st')
    → ∀ st' ∈ (Exec.to_state_result_list $ FMon.finterp handler mon initSt), I st'.
Proof.
  intros Hinit Hstep.
  induction mon as [|? ? IH] in initSt, Hinit |- *;
  cdestruct |- *** #CDestrMatch;
  set_solver.
Qed.

Arguments Exec.to_state_result_list : simpl never.

Lemma cinterp_inv_induct `{Effect Eff} {St E A}
  (handler : fHandler Eff (Exec.t St E)) (mon : cMon Eff A)
  (I : result St St → Prop) (initSt : St)
  : I (Ok initSt)
    → (∀ st call, I (Ok st) → ∀ st' ∈ Exec.to_state_result_list $ handler call st, I st')
    → ∀ st' ∈ (Exec.to_state_result_list $ FMon.cinterp handler mon initSt), I st'.
Proof.
  intros Hinit HIpreserve st' Hst'.
  eapply finterp_inv_induct; [eassumption | | eassumption].
  clear initSt Hinit st' Hst'.
  cdestruct |- *** as st eff Hst st' v Hst' #CDestrMatch #CDestrSplitGoal;
  try destruct eff;
  set_solver.
Qed.

(* TODO:
   TP: set_unfold on evars
   TP: MemRead and MemWrite supersubst

   NL: Unfold instances on mcallM of MChoice and Exec.Results.
   NL: Keep up the good work

*)

Fixpoint trace_find_indexed (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
  (itrs : list (iTrace ())) : option (nat * nat * FMon.fEvent outcome) :=
  match itrs with
  | ((itr, trend) :: itrr) =>
    if list_find P itr is Some (ieid, ev)
    then Some (0, ieid, ev)
    else prod_map (prod_map S id) id <$> trace_find_indexed P itrr
  | [] => None
  end.

Fixpoint trace_find (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
  (itrs : list (iTrace ())) : option (FMon.fEvent outcome) :=
  match itrs with
  | ((itr, trend) :: itrr) =>
    if find (λ x, bool_decide (P x)) itr is Some ev
    then Some ev
    else trace_find P itrr
  | [] => None
  end.

Lemma trace_find_app (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
  (l l' : list (iTrace ()))
  : trace_find P (l ++ l') = if trace_find P l is Some ev then Some ev else trace_find P l'.
Proof. induction l; cdestruct |- *** #CDestrMatch. Qed.

Definition trace_rev (itrs : list (iTrace ())) : list (iTrace ()) :=
  rev (map (set fst (@rev (FMon.fEvent outcome))) itrs).
Arguments trace_rev : simpl never.

Fixpoint find_last_aux {A} (P : A → Prop) `{∀ x, Decision (P x)} (acc : option A) (l : list A) : option A :=
  if l is a :: ar
  then find_last_aux P (if decide (P a) then Some a else acc) ar
  else acc.

Definition find_last {A} (P : A → Prop) `{∀ x, Decision (P x)} : list A → option A :=
  find_last_aux P None.
Arguments find_last : simpl never.

Lemma find_app {A} (P : A → bool) `{∀ x, Decision (P x)} (l l' : list A)
  : find P (l ++ l') = if find P l is Some a then Some a else find P l'.
Proof. induction l; cdestruct |- *** #CDestrMatch. Qed.

Lemma find_rev_find_last {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A)
  : find (λ x, bool_decide (P x)) (rev l) = find_last P l.
Proof.
  unfold find_last.
  enough (∀ o, (if find (λ x : A, bool_decide (P x)) (rev l) is Some a then Some a else o) = find_last_aux P o l)
  as <- by cdestruct |- *** #CDestrMatch.
  induction l; first done; cdestruct |- ***.
  rewrite <- IHl.
  rewrite find_app; cdestruct |- *** #CDestrMatch; tc_solve.
Qed.

Lemma find_last_spec {A} (P : A → Prop) `{∀ x, Decision (P x)} l a :
  find_last P l = Some a ↔ P a ∧ ∃ i, l !! i = Some a ∧ ∀ a' i', P a' → l !! i' = Some a' → i' ≤ i.
Proof.
  rewrite <- find_rev_find_last.
  induction l using rev_ind.
  1: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  rewrite rev_app_distr; cbn [rev]; rewrite app_nil_l.
  cdestruct |- *** #CDestrMatch.
  - cdestruct a |- *** #CDestrSplitGoal #CDestrEqOpt.
    + eexists (length l).
      rewrite lookup_app, lookup_unfold, Nat.sub_diag.
      cdestruct |- *** #CDestrSplitGoal.
      enough (¬ i' > length l) by lia.
      intro.
      opose proof (lookup_ge_None_2 (l ++ [x]) i' _).
      1: rewrite length_app; cbn; lia.
      deintros; cdestruct |- ***.
    + ospecialize (H3 x (length l) _ _); try fast_done.
      1: rewrite lookup_app, lookup_unfold, Nat.sub_diag; done.
      pose proof (lookup_lt_Some _ _ _ H2).
      rewrite length_app in *; cbn in *.
      assert (x0 = length l) as -> by lia.
      rewrite lookup_app, lookup_unfold, Nat.sub_diag in *.
      deintros; cdestruct |- ***.
  - setoid_rewrite IHl.
    cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
    + eexists x0.
      rewrite lookup_app.
      cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
      assert (x ≠ a') by naive_solver.
      rewrite lookup_app in *.
      cdestruct H5 #CDestrEqOpt #CDestrMatch.
      by eapply H3.
    + assert (x ≠ a) by naive_solver.
      rewrite lookup_app in *.
      deintros; cdestruct |- *** #CDestrMatch #CDestrEqOpt.
      eexists.
      cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal; eauto.
      eapply H3; eauto.
      rewrite lookup_app.
      cdestruct |- *** #CDestrMatch #CDestrEqOpt.
Qed.

#[local] Instance eq_some_unfold_find_last {A} (P : A → Prop) `{∀ x, Decision (P x)} l a :
  EqSomeUnfold (find_last P l) a
    (P a ∧ ∃ i, l !! i = Some a ∧ ∀ a' i', P a' → l !! i' = Some a' → i' ≤ i).
Proof. tcclean. eapply find_last_spec. Qed.

Fixpoint find_last_indexed_aux {A} (P : nat → A → Prop) `{∀ x n, Decision (P x n)}
    (acc : option (nat * A)) (i : nat) (l : list A) : option (nat * A) :=
  if l is a :: ar
  then find_last_indexed_aux P (if decide (P i a) then Some (i, a) else acc) (S i) ar
  else acc.

Definition find_last_indexed {A} (P : nat → A → Prop) `{∀ x n, Decision (P x n)}
    : list A → option (nat * A) :=
  find_last_indexed_aux P None 0.
Arguments find_last : simpl never.

Lemma find_last_indexed_aux_snoc  {A} (P : nat → A → Prop) `{∀ x n, Decision (P x n)}
    (a : A) (l : list A) o n :
  find_last_indexed_aux P o n (l ++ [a]) =
    if decide (P (n + length l) a)
    then Some (n + length l, a)
    else find_last_indexed_aux P o n l.
Proof.
  revert o n.
  elim l; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
  all: try solve [by rewrite Nat.add_0_r in *].
  all: erewrite ?H0 in *.
  all: cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
  all: rewrite ?Nat.add_succ_r in *.
  all: done.
Qed.

Lemma find_last_indexed_snoc {A} (P : nat → A → Prop) `{∀ x n, Decision (P x n)}
    (a : A) (l : list A) :
  find_last_indexed P (l ++ [a]) =
    if decide (P (length l) a)
    then Some (length l, a)
    else find_last_indexed P l.
Proof. unfold find_last_indexed. by rewrite find_last_indexed_aux_snoc. Qed.

Definition list_find_indexed {A} (P : nat → A → Prop) `{∀ x n, Decision (P x n)}
    (l : list A) : option (nat * A) :=
  (λ '(i, (i', a)), (i, a)) <$> list_find (uncurry P) (imap pair l).

Lemma list_find_indexed_Some {A} (P : nat → A → Prop) `{∀ x n, Decision (P x n)}
	  (l : list A) (i : nat) (x : A) :
  list_find_indexed P l = Some (i, x)
  ↔ l !! i = Some x
    ∧ P i x ∧ ∀ (j : nat) (y : A), l !! j = Some y → j < i → ¬ P j y.
Proof.
  unfold list_find_indexed.
  setoid_rewrite fmap_Some.
  cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
  all: unfold not.
  all: try setoid_rewrite list_find_Some in H0; cdestruct H0 |- *** #CDestrEqOpt.
  all: rewrite ?list_lookup_imap, ?fmap_Some in *; cdestruct i, H0 |- *** #CDestrEqOpt.
  1: unshelve eapply (H4 _ (_,_) _ _ H5).
  2: rewrite list_lookup_imap, fmap_Some in *; naive_solver.
  1: done.
  eexists (i,(i,x)); cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
  rewrite list_find_Some; unfold not; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
  2: eapply H2.
  all: rewrite ?list_lookup_imap, ?fmap_Some in *.
  all: naive_solver.
Qed.

#[local] Instance eq_some_unfold_lookup_snoc_l {A} (l : list A) i y x :
  TCFastDone (l !! i = Some x) →
  EqSomeUnfold ((l ++ [y]) !! i) x True.
Proof.
  tcclean.
  setoid_rewrite lookup_app_l; last by eapply lookup_length in H.
  done.
Qed.

Lemma find_last_indexed_Some {A} (P : nat → A → Prop) `{∀ x n, Decision (P x n)}
	  (l : list A) (i : nat) (x : A) :
  find_last_indexed P l = Some (i, x)
  ↔ l !! i = Some x
    ∧ P i x ∧ ∀ (j : nat) (y : A), l !! j = Some y → j > i → ¬ P j y.
Proof.
  enough (find_last_indexed P l = Some (0 + i, x) ↔
    None = Some (0 + i,x) ∧ (∀ j y, l !! j = Some y → ¬ P (0 + j) y) ∨
    l !! i = Some x ∧ P (0 + i) x ∧
    ∀ (j : nat) (y : A), l !! j = Some y → j > i → ¬ P (0+j) y) by sauto.
  unfold find_last_indexed.
  generalize (@None (nat * A)).
  generalize 0.
  elim l using rev_ind; cdestruct |- ***.
  1: cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
  1: by left.
  rewrite find_last_indexed_aux_snoc.
  cdestruct x |- *** #CDestrMatch.
  - cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
    + assert (i = length l0) as -> by lia.
      right.
      cdestruct x |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
      1: rewrite lookup_app; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      1: by rewrite lookup_unfold in *.
      1: by rewrite Nat.sub_diag.
      rewrite lookup_app in *.
      unfold not.
      deintros; cdestruct |- *** #CDestrMatch.
      1: eapply lookup_length in H1; lia.
      assert (j - length l0 ≠ 0) by lia.
      destruct (j - length l0); by cbn in *.
    + exfalso; eapply H2.
      2: eapply p.
      rewrite lookup_app_r; last lia.
      rewrite Nat.sub_diag; done.
    + eapply H2 in p.
      1: done.
      rewrite lookup_app_r; last lia.
      rewrite Nat.sub_diag; done.
    + enough (¬ i < length l0).
      1: eapply lookup_length in H1; rewrite length_app in *; cbn in *; lia.
      intro.
      eapply H3.
      2: eapply H4.
      2: eauto.
      rewrite lookup_app_r; last lia.
      rewrite Nat.sub_diag; done.
    + enough (¬ i < length l0) as ?%Nat.le_ngt.
      { opose proof (lookup_length _ _ _ _ H1); rewrite length_app in *; cbn in *.
        assert (i = length l0) as -> by lia.
        rewrite lookup_app_r in *; last lia; rewrite Nat.sub_diag in *; naive_solver. }
      intro.
      eapply H3.
      2: exact H4.
      2: eauto.
      rewrite lookup_app_r; last lia.
      rewrite Nat.sub_diag.
      naive_solver.
  - setoid_rewrite H0.
    deintros; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    + left; split; try done.
      cdestruct |- *** #CDestrEqOpt #CDestrMatch.
      rewrite lookup_app in H2.
      cdestruct H2 |- *** #CDestrMatch #CDestrEqOpt.
      1: sauto.
      eapply lookup_ge_None_1 in H2.
      assert (j = length l0) as -> by lia.
      naive_solver.
    + right.
      deintros; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      intro.
      eapply H3.
      2,3: eauto.
      rewrite lookup_app in *; cdestruct H4 |- *** #CDestrMatch.
      eapply lookup_length in H1.
      destruct (j - length l0) eqn: ?; last done.
      eapply lookup_ge_None_1 in H4.
      assert (j = length l0) as -> by lia.
      cbn in *.
      naive_solver.
    + left; split; try done.
      unfold not.
      cdestruct |- *** #CDestrEqOpt #CDestrMatch.
      eapply H1.
      2: exact H3.
      cdestruct H2 |- *** #CDestrEqOpt.
    + right.
      unfold not.
      rewrite lookup_app in H1.
      cdestruct H1 |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      1: eapply H3.
      2: exact H5.
      2: exact H6.
      1: cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      1,2: eapply lookup_ge_None_1 in H1.
      1,2: assert (i = length l0) as -> by lia.
      1: sauto.
      eapply lookup_lt_Some in H6.
      lia.
Qed.

(* Lemma find_rev_find_last_indexed {A} (P : nat → A → Prop) `{∀ x n, Decision (P x n)} (l : list A)
    a i j :
  i < length l → j = length l - S i →
  list_find_indexed P (rev l) = Some (i, a) ↔ find_last_indexed P l = Some (j, a).
Proof.
  intros ? ->.
  setoid_rewrite find_last_indexed_Some.
  setoid_rewrite list_find_indexed_Some.
  destruct (decide (l = nil)) as [->|].
  1: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  all: cdestruct |- *** as Hl%(nth_lookup_Some _ _ a) ?? #CDestrEqOpt #CDestrSplitGoal.
  1-3: rewrite rev_nth, nth_lookup in Hl; try done.
  1-3: unfold default in *; cdestruct Hl |- *** #CDestrMatch.
  1: eapply lookup_ge_None_1 in H1.
  1: destruct l; try done; cbn in *; lia.
  1: eapply n.
  1: rewrite nth_lookup in Hl.
  1: eapply (nth_lookup_Some _ _ a).

  Search nth rev.
  Search lookup nth.
  Search length rev.
  all: assert (i < length l).
  all: try (eapply lookup_lt_Some in Hl; try rewrite rev_length in *; done).
  4: { }
  all: try erewrite rev_nth in Hl.
  all: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  Search nth lookup.
  enough (∀ o, (if find (λ x : A, bool_decide (P x)) (rev l) is Some a then Some a else o) = find_last_aux P o l)
  as <- by cdestruct |- *** #CDestrMatch.
  induction l; first done; cdestruct |- ***.
  rewrite <- IHl.
  rewrite find_app; cdestruct |- *** #CDestrMatch; tc_solve.
Qed. *)

Lemma last_exists {A} (P : A → Prop) `{∀ x, Decision (P x)} l :
  ∀ x ∈ l, P x → is_Some (find_last P l).
Proof.
  rewrite <- find_rev_find_last.
  elim l using rev_ind; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  all: rewrite rev_app_distr; cbn.
  all: cdestruct |- *** #CDestrMatch.
  by eapply H0.
Qed.

Lemma last_exists_indexed {A} (P : nat → A → Prop) `{∀ n x, Decision (P n x)} l :
  ∀ x i, l !! i = Some x → P i x → is_Some (find_last_indexed P l).
Proof.
  elim l using rev_ind.
  all: cdestruct |- *** #CDestrEqOpt.
  rewrite find_last_indexed_snoc.
  rewrite lookup_app in *.
  cdestruct x0, H1 |- *** #CDestrEqOpt #CDestrMatch.
  1: eapply H0; eauto.
  eapply lookup_ge_None_1 in H1.
  assert (i = length l0) as -> by lia.
  done.
Qed.

Definition trace_find_last (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
    (itrs : list (iTrace ())) : option (FMon.fEvent outcome) :=
  if find_last (λ '(itr,_), is_Some (find_last P itr)) itrs is Some itr
  then find_last P itr.1
  else None.

Lemma find_trace_rev_find_trace_last (P : FMon.fEvent outcome → Prop)
    `{∀ x, Decision (P x)} (acc : option (FMon.fEvent outcome))
    (itrs : list (iTrace ())) :
  trace_find P (trace_rev itrs) = trace_find_last P itrs.
Proof.
  induction itrs as [|[]]; cdestruct |- ***.
  unfold trace_find_last, trace_rev.
  rewrite <- ?find_rev_find_last.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt.
  - rewrite <- ?find_rev_find_last.
    rewrite find_app, trace_find_app in *.
    2: tc_solve.
    deintros; cdestruct |- *** #CDestrMatch.
    all: rewrite ?find_rev_find_last in *.
    all: unfold trace_rev, trace_find_last in *.
    all: rewrite ?IHitrs in *.
    all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    1: eexists; deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch; eauto.
    revert H5; enough (∃ ev, find_last P l0 = Some ev) by sfirstorder.
    eexists x.
    cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    eexists.
    cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal; eauto.
  - rewrite find_app, trace_find_app in *.
    2: tc_solve.
    unfold trace_rev, trace_find_last in *.
    rewrite ?IHitrs in *.
    deintros; cdestruct |- *** #CDestrMatch.
    all: rewrite ?find_rev_find_last in *.
    all: sfirstorder.
Qed.

Definition trace_find_last_indexed (P : EID.t → iEvent → Prop) `{∀ eid x, Decision (P eid x)}
    (itrs : list (iTrace ())) : option (EID.t * FMon.fEvent outcome) :=
  if find_last_indexed (λ iid '(itr,_), is_Some (find_last_indexed (λ ieid, P (EID.make 0 iid ieid None)) itr)) itrs is Some (iid, itr)
  then
    (if find_last_indexed (λ ieid, P (EID.make 0 iid ieid None)) itr.1 is (Some (ieid, ev))
    then Some (EID.make 0 iid ieid None, ev)
    else None)
  else None.

Lemma trace_find_cons (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
    (itrs : list (iTrace ())) (x : FMon.fEvent outcome)
  : trace_find P (trace_cons x itrs) =
    if decide (P x)
    then Some x
    else trace_find P itrs.
Proof.
  destruct itrs as [|[]].
  all: cdestruct |- *** #CDestrMatch #CDestrEqOpt.
Qed.

#[global] Instance elem_of_trace : ElemOf (fEvent outcome) (list (iTrace ())) :=
  λ ev itrs, ev ∈ (mjoin (fst <$> itrs)).

#[export] Instance unfold_elem_of_trace_cons ev ev' itrs P :
  SetUnfoldElemOf ev itrs P →
  SetUnfoldElemOf ev (trace_cons ev' itrs) (ev = ev' ∨ P).
Proof.
  tcclean.
  unfold elem_of, elem_of_trace.
  unfold trace_cons.
  destruct itrs as [|[]].
  all: set_solver.
Qed.

Arguments trace_find : simpl never.

Definition trace_snoc (ev : FMon.fEvent outcome) (itrs : list (iTrace ())) : list (iTrace ()) :=
  let '(trs, (last_tr,tr_end)) := unsnoc_total FMon.FTNothing itrs in
  trs ++ [(last_tr ++ [ev],tr_end)].

Definition traces_snoc {nmth} (ev : FMon.fEvent outcome) (thread : Fin.t nmth)
    : vec (list (iTrace ())) nmth → vec (list (iTrace ())) nmth :=
  set (.!!! thread) (trace_snoc ev).

Lemma trace_ind P :
  P []
  → (∀ tr trend, P tr → P (([],trend) :: tr))
  → (∀ tr ev, P tr → P (trace_cons ev tr))
  → ∀ tr, P tr.
Proof.
  intros Hb Hs1 Hs2 tr.
  elim tr; cdestruct |- ***; first done.
  induction l.
  1: now eapply Hs1.
  unfold trace_cons in Hs2.
  specialize (Hs2 ((l, f) :: l0)); cbv [set] in *; cbn in *.
  now eapply Hs2.
Qed.

Lemma trace_rev_ind (P : list (iTrace ()) → Prop) :
  P []
  → (∀ tr trend, P tr → P (tr ++ [([],trend)]))
  → (∀ tr ev, tr ≠ [] → P tr → P (trace_snoc ev tr))
  → ∀ tr, P tr.
Proof.
  intros Hb Hs1 Hs2 tr.
  induction tr using rev_ind; first done.
  destruct x.
  induction l using rev_ind.
  1: now eapply Hs1.
  opose proof (Hs2 (tr ++ [(l, f)]) x _ IHl).
  1: destruct tr; done.
  unfold trace_snoc, unsnoc_total in H.
  now rewrite unsnoc_snoc in H.
Qed.

Lemma trace_snoc_app tr tr' ev :
  tr' ≠ [] →
  trace_snoc ev (tr ++ tr') = tr ++ trace_snoc ev tr'.
Proof.
  revert tr'.
  induction tr using trace_rev_ind; cdestruct |- ***.
  - rewrite <- ?app_assoc; cbn.
    rewrite IHtr; last done.
    f_equal.
    pose proof exists_last H as [? [[] ->]].
    unfold trace_snoc, unsnoc_total.
    rewrite app_comm_cons.
    rewrite ?unsnoc_snoc.
    now rewrite app_comm_cons.
  - pose proof exists_last H0 as [? [[] ->]].
    rewrite app_assoc.
    unfold trace_snoc at 1 4, unsnoc_total.
    rewrite ?unsnoc_snoc.
    now rewrite app_assoc.
Qed.

Lemma trace_snoc_rev_cons itrs ev :
  trace_snoc ev (trace_rev itrs) = trace_rev (trace_cons ev itrs).
Proof.
  pattern itrs.
  eapply trace_ind; cdestruct |- ***.
  - cbv [set]; cbn.
    rewrite trace_snoc_app; last done.
    reflexivity.
  - rewrite trace_snoc_app; last done.
    reflexivity.
Qed.

Lemma enumerate_imap {A} (l : list A) :
  enumerate l = imap pair l.
Proof.
  unfold enumerate.
  change pair with (pair (B := A) ∘ Nat.iter 0 S) at 2.
  generalize 0.
  elim l; cdestruct |- *** #CDestrSplitGoal.
  1: induction n; cdestruct |- ***.
  erewrite H, Combinators.compose_assoc.
  eapply imap_ext.
  cdestruct |- *** #CDestrSplitGoal.
  erewrite <- Nat.iter_swap_gen; eauto.
Qed.

Definition intra_trace_eid_succ tid (tr : list (iTrace ())) : EID.t :=
  let '(trs, (last_tr,tr_end)) := unsnoc_total FMon.FTNothing tr in
  EID.make tid (Nat.pred (length tr)) (length last_tr) None.

Lemma intra_trace_eid_succ_tid tid tr :
  (intra_trace_eid_succ tid tr).(EID.tid) = tid.
Proof. unfold intra_trace_eid_succ. cdestruct |- *** #CDestrMatch. Qed.

Lemma intra_trace_eid_succ_byte tid tr :
  (intra_trace_eid_succ tid tr).(EID.byte) = None.
Proof. unfold intra_trace_eid_succ. cdestruct |- *** #CDestrMatch. Qed.

(* Lemma intra_trace_eid_succ_lookup_None {nmth} (pe : Candidate.pre Candidate.NMS nmth) tid :
  pe !! (intra_trace_eid_succ tid (pe !!! tid)) = None.
Proof.
  unfold intra_trace_eid_succ.
  destruct tr; cbn. *)


(* #[export] Instance set_elem_of_traces_snoc {nmth} init (trs : vec (list (iTrace ())) nmth) ev' thread eid ev P :
  SetUnfoldElemOf (eid, ev) (Candidate.event_list (Candidate.make_pre Candidate.NMS init trs)) P →
  SetUnfoldElemOf (eid, ev)
    (Candidate.event_list (Candidate.make_pre Candidate.NMS init (traces_snoc ev' thread trs)))
    (P ∨ eid = intra_trace_eid_succ thread (trs !!! thread) ∧ ev = ev').
Proof.
  tcclean.
  unfold traces_snoc, trace_snoc, unsnoc_total.
  set_unfold.
  destruct eid.
  unfold lookup, Candidate.lookup_eid_pre.
  cbn.
  cbv [set Setter_valter alter valter].
  unfold Candidate.lookup_iEvent, Candidate.lookup_instruction.
  cbn.
  assert ((trs !!! thread) = [] ∨ (trs !!! thread) ≠ []) as [|] by (destruct (trs !!! thread); naive_solver); cbn.
  - rewrite H0 in *.
    cbn in *.
    destruct (decide (fin_to_nat thread = tid)) as [<-|]; cbn.
    + rewrite <- vec_to_list_lookup, vec_to_list_insert, list_lookup_insert;
      last (rewrite length_vec_to_list; eapply fin_to_nat_lt).
      opose proof (vlookup_lookup trs thread []) as [? _].
      specialize (H1 H0); rewrite <- vec_to_list_lookup in *.
      cdestruct |- *** #CDestrSplitGoal.
      1: destruct iid as [|[|]], ieid as [|[|]]; cbn in *; try discriminate.
      all: assert (byte = None) as -> by admit.
      1: unfold guard in H0; cdestruct H0 #CDestrMatch; naive_solver.
      all: destruct iid as [|[|]]; cbn; try discriminate; try naive_solver.
      all: rewrite ?H1 in *; cbn in *; try discriminate.
    + rewrite <- vec_to_list_lookup, vec_to_list_insert, list_lookup_insert_ne; last done.
      cdestruct |- *** #CDestrSplitGoal; last scongruence.
      all: rewrite <- vec_to_list_lookup in *; hauto lq: on rew: off .
  - cbn in *.
Admitted. *)


Lemma trace_snoc_event_list init tr ev :
  Candidate.event_list (Candidate.make_pre Candidate.NMS init [#trace_snoc ev tr]) =
  Candidate.event_list (Candidate.make_pre Candidate.NMS init [#tr]) ++
  [(intra_trace_eid_succ 0 tr, ev)].
Proof.
  unfold intra_trace_eid_succ.
  assert (tr = [] ∨ tr ≠ []) as [->|] by (destruct tr; naive_solver); first done.
  pose proof exists_last H as [? [[] ->]].
  unfold trace_snoc, unsnoc_total.
  rewrite ?unsnoc_snoc.
  cbn.
  repeat rewrite ?enumerate_imap, ?imap_app, ?bind_app.
  cbn.
  rewrite ?app_nil_r.
  rewrite app_assoc.
  repeat f_equal; last lia.
  rewrite length_app.
  cbn.
  lia.
Qed.

Lemma lookup_vec_nat_cons_S {A n} (h : A) (v : vec A n) x :
  (h ::: v) !! S x = v !! x.
Proof.
  unfold lookup, vec_lookup_nat.
  cdestruct |- *** #CDestrMatch; try lia.
  f_equal.
  eapply Fin.of_nat_ext.
Qed.

Lemma lookup_total_fin_to_nat {A size} (n : fin size) (v : vec A size)  :
  v !! fin_to_nat n = Some (v !!! n).
Proof.
  generalize dependent n.
  dependent induction v.
  all: intros m.
  2: destruct n.
  all: depelim m.
  all: cdestruct |- *** #CDestrMatch.
  1: depelim m.
  rewrite lookup_vec_nat_cons_S.
  sfirstorder.
Qed.

(* #[export] Instance lookup_unfold_traces_snoc {nmth} (init : MState.t nmth) evs (ev : iEvent) thread (eid : EID.t) R :
  LookupUnfold eid (Candidate.make_pre Candidate.NMS init evs) R →
  LookupUnfold eid (Candidate.make_pre Candidate.NMS init (traces_snoc ev thread evs))
    (if eid =? intra_trace_eid_succ (fin_to_nat thread) (evs !!! thread) then Some ev else R).
Proof.
  tcclean.
  clear H R.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt.
  - unfold lookup, Candidate.lookup_eid_pre, Candidate.lookup_iEvent, Candidate.lookup_instruction in H |- *.
    cdestruct eid, H |- *** #CDestrEqOpt.
    eexists.
    cdestruct |- *** #CDestrSplitGoal.
    2: eapply intra_trace_eid_succ_byte.
    rewrite intra_trace_eid_succ_tid.
    unfold traces_snoc, set, Setter_valter, alter, valter.
    rewrite lookup_total_fin_to_nat.
    rewrite vlookup_insert.
    cdestruct |- *** #CDestrEqOpt.
    unfold intra_trace_eid_succ, unsnoc_total.
    destruct (unsnoc (evs !!! thread)) as [[? []]|] eqn: Hunsnoc.
    1: cbn.
Admitted.

#[export] Instance lookup_unfold_trace_snoc {et} (init : MState.t 1) evs (ev : iEvent) (eid : EID.t) R :
  LookupUnfold eid (Candidate.make_pre et init [# evs]) R →
  LookupUnfold eid (Candidate.make_pre et init [# trace_snoc ev evs])
    (if eid =? intra_trace_eid_succ 0 evs then Some ev else R).
Proof.
  tcclean.
  cdestruct eid, H |- *** #CDestrMatch.
Admitted. *)

(* #[export] Instance lookup_unfold_intra_traces_eid_succ_None {nmth et} (init : MState.t nmth) trs (tid : Fin.t nmth) :
  LookupUnfold (intra_trace_eid_succ tid (trs !!! tid)) (Candidate.make_pre et init trs) None.
Admitted. *)

Lemma cd_to_pe_lookup `(cd : Candidate.t et nmth) eid :
  cd !! eid = Candidate.pre_exec cd !! eid.
Proof. reflexivity. Qed.

#[local] Instance lookup_ev_from_iTraces : Lookup EID.t iEvent (list (iTrace ())) :=
  λ eid evs,
  guard (eid.(EID.tid) = 0 ∧ eid.(EID.byte) = None);;
  '(trace, result) ← evs !! eid.(EID.iid);
  trace !! eid.(EID.ieid).

#[local] Instance lookup_unfold_list_singleton {A} (x : A) n :
  LookupUnfold n [x] (if n is 0 then Some x else None).
Proof. tcclean. by destruct n. Qed.

Lemma eq_some_unfold_eid_iTraces_lookup (tr : list (iTrace ())) eid ev P Q :
  (∀ itr, EqSomeUnfold (tr !! eid.(EID.iid)) itr (P itr)) →
  (∀ itr, EqSomeUnfold (itr.1 !! eid.(EID.ieid)) ev (Q itr)) →
  EqSomeUnfold (tr !! eid) ev
    (∃ itr, eid.(EID.tid) = 0 ∧ eid.(EID.byte) = None ∧ P itr ∧ Q itr).
Proof.
  tcclean.
  clear dependent P Q.
  unfold lookup at 1, lookup_ev_from_iTraces.
  cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  all: eexists (_,_).
  all: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
Qed.

Lemma eq_None_lookup_length {A} (l : list A) n :
  EqNoneUnfold (l !! n) (length l ≤ n).
Proof. tcclean. apply lookup_ge_None. Qed.

#[local] Instance eq_some_unfold_lookup_singleton_list {A} (x y : A) n :
  EqSomeUnfold ([x] !! n) y (n = 0 ∧ x = y).
Proof. tcclean. destruct n as [|[]]; naive_solver. Qed.

Lemma eid_full_po_lt_intra_trace_eid_succ eid (tr : list (iTrace ())) :
  is_Some (tr !! eid) →
  EID.full_po_lt eid (intra_trace_eid_succ 0 tr).
Proof.
  cdestruct |- *** as ev itr ??? H_itr H_ev #CDestrEqOpt ##eq_some_unfold_eid_iTraces_lookup.
  destruct (decide (tr = [])) as [->|H_notempty].
  1: destruct eid as [? []]; done.
  pose proof (exists_last H_notempty) as [trstart [[] ->]].
  unfold EID.full_po_lt, EID.po_lt, EID.iio_lt, intra_trace_eid_succ, unsnoc_total.
  rewrite ?unsnoc_snoc, length_app.
  destruct eid; cbn in *.
  replace (Nat.pred (length trstart + 1)) with (length trstart) by lia.
  rewrite lookup_app in *.
  cdestruct itr, H_itr |- *** #CDestrEqOpt #CDestrMatch ##@eq_None_lookup_length.
  2: {
    unfold iTrace, fTrace in *; generalize dependent (length trstart).
    eapply lookup_lt_Some in H_ev.
    right; cdestruct |- *** #CDestrSplitGoal; lia.
  }
  eapply lookup_lt_Some in H1.
  now left.
Qed.

#[local] Instance eid_full_po_lt_Irreflexive :
  Irreflexive EID.full_po_lt.
Proof.
  cdestruct |- *** as [] ?.
  unfold EID.full_po_lt, EID.po_lt, EID.iio_lt in *.
  lia.
Qed.

#[local] Instance eid_full_po_lt_Asymmetric :
  Asymmetric EID.full_po_lt.
Proof.
  cdestruct |- *** as eid1 eid2.
  unfold EID.full_po_lt, EID.po_lt, EID.iio_lt in *.
  cdestruct |- *** #CDestrSplitGoal.
  all: lia.
Qed.

#[local] Instance eid_full_po_lt_Transitive :
  Transitive EID.full_po_lt.
Proof.
  unfold EID.full_po_lt, EID.iio_lt, EID.po_lt in *.
  cdestruct |- *** as [] [] [] ??; deintros; cdestruct |- *** #CDestrSplitGoal.
  all: lia.
Qed.

#[local] Instance cdestruct_Transitive `{Transitive A R} x y z :
  TCFastDone (R x y) → TCFastDone (R y z) →
  CDestrSimpl true (R x z) True.
Proof. tcclean. cdestruct |- *** #CDestrSplitGoal. by eapply H. Qed.

#[local] Instance obvFalse_Irreflexive_same `{Irreflexive A R} (x : A):
  ObvFalse (R x x).
Proof. tcclean. firstorder. Qed.

#[local] Instance obvFalse_Asymmetric_symmetric `{Asymmetric A R} (x y : A):
  Incompatible (R x y) (R y x).
Proof. tcclean. firstorder. Qed.

Lemma trace_find_last_spec (P : iEvent → Prop) `{∀ x, Decision (P x)}
    (tr : list (iTrace ())) ev :
  trace_find_last P tr = Some ev ↔
  ∃ eid, tr !! eid = Some ev ∧
    P ev ∧
    ∀ eid' ev', tr !! eid' = Some ev' → P ev' →
      EID.full_po_lt eid' eid ∨ eid' = eid.
Proof.
  unfold trace_find_last.
  unfold lookup, lookup_ev_from_iTraces.
  cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
  - eexists (EID.make 0 x1 x2 None).
    cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    1: eexists; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    unfold EID.full_po_lt, EID.po_lt, EID.iio_lt; cbn.
    ospecialize (H4 (l0,_) _ _ _); eauto.
    1: eapply last_exists; eauto; by eapply elem_of_list_lookup_2.
    eapply Compare.le_le_S_eq in H4.
    cdestruct H4 #CDestrSplitGoal.
    1: do 2 left; lia.
    rewrite H8, H4 in *.
    ospecialize (H7 ev' (EID.ieid eid') _ _ ); first done.
    1: rewrite H3 in *; hauto l: on.
    eapply Compare.le_le_S_eq in H7.
    cdestruct H7 #CDestrSplitGoal.
    1: lia.
    1: right; destruct eid'; sauto.
  - ospecialize (H5 (EID.make 0 x2 x1 None) x0 _ _ );
    cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    1: eexists; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    opose proof (H10 (l,f) (EID.iid x) _ _); try fast_done.
    1: eapply (last_exists _ _ ev); try fast_done; by eapply elem_of_list_lookup_2.
    destruct x; cbn in *.
    unfold EID.full_po_lt, EID.iio_lt, EID.po_lt in *; cbn in *.
    assert (iid = x2) as <- by (destruct H5; first lia; inversion H5; lia).
    rewrite H9 in *; deintros; cdestruct |- ***.
    opose proof (H8 ev ieid _ _); eauto.
    assert (ieid = x1) as <- by (destruct H5 as [|H5]; first lia; inversion H5; lia).
    rewrite H7 in *; deintros; cdestruct |- ***.
    eexists; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; eauto.
  - revert H6.
    eapply not_eq_None_Some.
    eapply last_exists; first by eapply elem_of_list_lookup_2.
    eapply last_exists; first by eapply elem_of_list_lookup_2.
    done.
Qed.

Lemma trace_find_last_indexed_spec (P : EID.t → iEvent → Prop) `{∀ eid x, Decision (P eid x)}
    (tr : list (iTrace ())) ev eid :
  trace_find_last_indexed P tr = Some (eid, ev) ↔
    tr !! eid = Some ev ∧
    P eid ev ∧
    ∀ eid' ev', tr !! eid' = Some ev' → P eid' ev' →
      EID.full_po_lt eid' eid ∨ eid' = eid.
Proof.
  unfold trace_find_last_indexed.
  unfold lookup, lookup_ev_from_iTraces.
  cdestruct eid |- *** as #CDestrEqOpt #CDestrMatch.
  all: try setoid_rewrite find_last_indexed_Some.
  all: cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; eauto.
  - enough (¬ EID.full_po_lt
      {| EID.tid := 0; EID.iid := n; EID.ieid := n1; EID.byte := None |} eid').
    1: opose proof (EID.full_po_lt_connex eid'
      {| EID.tid := 0; EID.iid := n; EID.ieid := n1; EID.byte := None |} _ _ _) as Heid.
    all: cbn in *; try fast_done.
    1: cdestruct Heid |- *** #CDestrSplitGoal; sauto.
    intro.
    unfold EID.full_po_lt, EID.po_lt, EID.iio_lt in H11; cbn in *.
    destruct eid'; cbn in *.
    cdestruct iid, tid, byte, ieid, H11 #CDestrSplitGoal.
    1: eapply H2; eauto; cbn in *.
    1: eapply last_exists_indexed; eauto; naive_solver.
    eapply H5.
    2: eapply H6.
    1: cdestruct l, tr |- *** #CDestrEqOpt.
    1: done.
  - opose proof (H11 {| EID.tid := 0; EID.iid := n; EID.ieid := n1; EID.byte := None |}
      _ _ _).
    1: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    1: eexists (_, _); cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    1: done.
    cdestruct H12 |- *** #CDestrSplitGoal.
    unfold EID.full_po_lt, EID.po_lt, EID.iio_lt in H12; cbn in *.
    destruct eid; cbn in *.
    cdestruct tid, iid, ieid, byte |- *** #CDestrSplitGoal.
    1,2: exfalso; eapply H2; eauto; cbn in *.
    1,2: eapply last_exists_indexed; eauto.
    cdestruct n, l0, f0 |- *** #CDestrEqOpt.
    exfalso.
    eapply H5.
    all: sauto.
  - opose proof (H11 {| EID.tid := 0; EID.iid := n; EID.ieid := n1; EID.byte := None |}
      _ _ _).
    1: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    1: eexists (_, _); cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    1: done.
    cdestruct n, l, f, eid, H12 |- *** #CDestrSplitGoal #CDestrEqOpt.
    unfold EID.full_po_lt, EID.po_lt, EID.iio_lt in H12; cbn in *.
    destruct eid; cbn in *.
    cdestruct tid, iid, ieid, byte |- *** #CDestrSplitGoal.
    1: exfalso; eapply H2; eauto; cbn in *.
    1: eapply last_exists_indexed; eauto.
    cdestruct n, l0, f0 |- *** #CDestrEqOpt.
    exfalso.
    eapply H5.
    all: sauto.
  - revert H0.
    apply not_eq_None_Some.
    eapply last_exists_indexed; eauto; cbn.
    eapply last_exists_indexed; eauto; cbn.
    destruct eid; sauto.
Qed.

Lemma trace_last_exists `{∀ ev : iEvent, Decision (P ev)} (tr : list (iTrace ())) eid :
  ∀ ev, tr !! eid = Some ev → P ev → is_Some (trace_find_last P tr).
Proof.
  cdestruct |- *** #CDestrEqOpt.
  unfold lookup, lookup_ev_from_iTraces, trace_find_last in *.
  cdestruct H0 |- *** #CDestrMatch #CDestrEqOpt.
  1: eapply last_exists; first by eapply elem_of_list_lookup_2.
  1: done.
  exfalso.
  revert H5.
  eapply not_eq_None_Some.
  eapply last_exists; first by eapply elem_of_list_lookup_2.
  eapply last_exists; first by eapply elem_of_list_lookup_2.
  done.
Qed.

Lemma trace_last_exists_indexed `{∀ eid ev, Decision (P eid ev)} (tr : list (iTrace ())) :
  ∀ eid ev, tr !! eid = Some ev → P eid ev → is_Some (trace_find_last_indexed P tr).
Proof.
  unfold trace_find_last_indexed, lookup, lookup_ev_from_iTraces.
  cdestruct |- *** #CDestrEqOpt #CDestrMatch.
  all: exfalso.
  - eapply find_last_indexed_Some in H5.
    cdestruct H5 #CDestrEqOpt.
  - revert H5.
    apply not_eq_None_Some.
    eapply last_exists_indexed; eauto; cbn.
    eapply last_exists_indexed; eauto; cbn.
    destruct eid; sauto.
Qed.

Lemma trace_last_event P `{∀ ev : iEvent, Decision (P ev)} (tr : list (iTrace ())) eid ev :
  tr !! eid = Some ev → P ev →
  ∃ ev' eid', tr !! eid' = Some ev' ∧ P ev' ∧
    ∀ ev'' eid'', tr !! eid'' = Some ev''→ P ev'' →
      EID.full_po_lt eid'' eid' ∨ eid'' = eid'.
Proof.
  cdestruct |- *** as Htr HPev.
  opose proof (trace_last_exists _ _ _ Htr HPev) as Htrlf.
  destruct Htrlf as [lev Hlev].
  eexists lev.
  eapply trace_find_last_spec in Hlev.
  cdestruct Hlev.
  eexists.
  cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; eauto.
Qed.

Lemma trace_last_event_indexed P `{∀ (ev : iEvent) (eid : EID.t), Decision (P eid ev)}
    (tr : list (iTrace ())) eid ev :
  tr !! eid = Some ev → P eid ev →
  ∃ eid' ev', tr !! eid' = Some ev' ∧ P eid' ev' ∧
    ∀ eid'' ev'', tr !! eid'' = Some ev''→ P eid'' ev'' →
      EID.full_po_lt eid'' eid' ∨ eid'' = eid'.
Proof.
  cdestruct |- *** as Htr HPev.
  opose proof (trace_last_exists_indexed _ _ _ Htr HPev) as Htrlf.
  destruct Htrlf as [[leid lev] Hlev].
  eexists leid, lev.
  eapply trace_find_last_indexed_spec in Hlev.
  cdestruct Hlev |- *** #CDestrEqOpt #CDestrSplitGoal.
  by eapply H2.
Qed.

Notation seqmon := (Exec.t seq_state string).
Notation initss := {| initSt := initSt; regs := ∅; mem := ∅; itrs := [] |}.

Definition seqmon_pe (st : seq_state) : Candidate.pre Candidate.NMS 1 :=
  Candidate.make_pre _ st.(initSt) [# st.(itrs)].

Definition result_same_type_proj {T} (r : result T T) :=
  match r with
  | Ok t => t
  | Error t => t
  end.

#[local] Instance cdestruct_is_some_unit b (o : option ()) P :
  EqSomeUnfold o () P →
  CDestrSimpl b (is_Some o) P.
Proof. tcclean. by cdestruct o, H |- *** #CDestrSplitGoal. Qed.

#[local] Instance cdestruct_is_Some_mret b `(x : A) :
  CDestrSimpl b (is_Some (mret x : option A)) True.
Proof. tcclean. unfold mret, option_ret. done. Qed.

#[local] Instance cdestruct_exists_simpl_andr b `(P : A → Prop) Q Q' :
  CDestrSimpl b Q Q' →
  CDestrSimpl b (∃ x, P x ∧ Q) (∃ x, P x ∧ Q').
Proof. tcclean. cdestruct |- *** #CDestrSplitGoal; eexists; eauto. Qed.

#[local] Instance cdestruct_exists_simpl_andl b `(P : A → Prop) Q Q' :
  CDestrSimpl b Q Q' →
  CDestrSimpl b (∃ x, Q ∧ P x) (∃ x, Q' ∧ P x).
Proof. tcclean. cdestruct |- *** #CDestrSplitGoal; eexists; eauto. Qed.

#[local] Instance cdestruct_exists_and_Truel b `(P : A → Prop) :
  CDestrSimpl b (∃ x, True ∧ P x) (∃ x, P x).
Proof. tcclean. cdestruct |- *** #CDestrSplitGoal; eexists; eauto. Qed.

#[local] Instance cdestruct_exists_and_Truer b `(P : A → Prop) :
  CDestrSimpl b (∃ x, P x ∧ True) (∃ x, P x).
Proof. tcclean. cdestruct |- *** #CDestrSplitGoal; eexists; eauto. Qed.

Lemma is_Some_fold `(o : option A) i :
  o = Some i → is_Some o.
Proof. destruct o; done. Qed.

(* Goal ∀ nmth `(∀ eid event, Decision (P eid event)) ev tid (pe : Candidate.pre Candidate.NMS nmth) L, Candidate.collect_all P (set Candidate.events (traces_snoc ev tid) pe) = L.

intros.
set_unfold.
destruct pe.
cbv [set]; cbn.
setoid_rewrite lookup_unfold.
cdestruct |- *** #CDestrMatch.

#[local] Instance set_unfold_elem_of_collect_all_trace_snoc {nmth} eid `{∀ eid ev, Decision (P eid ev)} (pe : Candidate.pre Candidate.NMS nmth) ev tid Q :
  SetUnfoldElemOf eid (Candidate.collect_all P pe) Q →
  SetUnfoldElemOf eid (Candidate.collect_all P (set Candidate.events (traces_snoc ev tid) pe))
  (Q ∨ P eid ev ∧ eid = intra_trace_eid_succ tid (pe.(Candidate.events) !!! tid)).
Proof.
  tcclean.
Admitted. *)


Definition op_mem_wf (str : result seq_state seq_state) : Prop :=
  match str with
  | Ok st =>
    ∀ pa v,
      st.(mem) !! pa = Some v
    ↔ ∃ ev,
        trace_find
          (is_mem_writeP (λ size wr, pa_in_range wr.(WriteReq.pa) size pa))
          st.(itrs)
        = Some ev
    ∧ ∃ offset,
        ev |> is_mem_writeP
          (λ size wr,
            pa_addN wr.(WriteReq.pa) offset = pa
            ∧ (offset < size)%N
            ∧ bv_get_byte 8 offset wr.(WriteReq.value) = v)
  | Error _ => False
  end.

Lemma length_bv_to_bytes n m (v : bv n) :
  length (bv_to_bytes m v) = N.to_nat (div_round_up n m).
Proof.
  unfold bv_to_bytes.
  rewrite length_bv_to_little_endian.
  2: lia.
  rewrite <- Z_N_nat.
  now rewrite N2Z.id.
Qed.

Lemma div_round_up_divisible n m :
  (n ≠ 0)%N → (div_round_up (n * m) n) = m.
Proof.
  intro.
  unfold div_round_up.
  nia.
Qed.

Lemma pa_not_in_range_write size pa pa' st st' (l : list (bv 8)) :
  ¬ pa_in_range pa size pa'
  → (st', ()) ∈ write_mem_seq_state pa l st
  → length l = N.to_nat size
  → mem st' !! pa' = mem st !! pa'.
Proof.
  setoid_rewrite pa_in_range_spec.
  revert dependent size pa st.
  elim l; cdestruct pa' |- ***.
  erewrite (H (N.pred size) (pa_addZ pa0 1) (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)); eauto.
  3: lia.
  - destruct st; cbn; unfold Setter_finmap.
    assert (pa' ≠ pa0).
    { intros ->.
      eapply H0.
      eexists 0%N.
      rewrite pa_addN_zero.
      cdestruct |- *** #CDestrSplitGoal.
      destruct size; lia. }
    admit.
  - unfold not; cdestruct |- ***.
    cdestruct pa'.
    eapply H0.
    unfold pa_addN; rewrite pa_addZ_assoc.
    eexists (N.succ x); cdestruct |- *** #CDestrSplitGoal.
    1: f_equal; lia.
    lia.
Admitted.

Lemma write_mem_seq_state_snoc l x pa st st' :
  (st', ()) ∈ write_mem_seq_state pa (l ++ [x]) st →
  mem st' !! pa_addN pa (N.of_nat (length l)) = Some x.
Proof.
  revert dependent pa st.
  elim l; cdestruct st' |- ***.
  1: rewrite pa_addN_zero; unfold Setter_finmap.
  (* Set Typeclasses Debug Verbosity 2. *)
  (* 1: rewrite lookup_unfold. *)
  1: admit. (* Thibaut *)
  eapply H in H0.
  rewrite <- H0.
  unfold pa_addN.
  rewrite pa_addZ_assoc.
  do 2 f_equal.
  lia.
Admitted.

Lemma write_mem_seq_state_app pa l st st' x :
  (st', ()) ∈ write_mem_seq_state pa (l ++ [x]) st →
  (st', ()) ∈ write_mem_seq_state pa l (setv ((.!! pa_addN pa (N.of_nat (length l))) ∘ mem) (Some x) st).
Proof.
  revert dependent pa st x.
  elim l; cdestruct st' |- *** #CDestrSplitGoal.
  1: rewrite pa_addN_zero; done.
  eexists _, (); cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  2: eapply H.
  2: eapply H0.
  eexists _, _; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  destruct st; cbv [set setv].
  unfold Setter_compose.
  f_equal; cbn.
  unfold Setter_finmap.
  erewrite partial_alter_commute.
  2: admit.
  unfold pa_addN.
  rewrite pa_addZ_assoc.
  do 3 f_equal.
  lia.
Admitted.

Lemma pa_in_range_write pa pa' size (v: bv (8*size)) st st' :
  (st', ()) ∈ write_mem_seq_state pa (bv_to_bytes 8 v) st →
  pa_in_range pa size pa' →
  ∃ offset, (offset < size)%N ∧ pa' = pa_addN pa offset ∧
    mem st' !! pa' = Some (bv_get_byte 8 offset v).
Proof.
  intros ??%pa_in_range_spec;
  deintros; cdestruct |- *** as pa i size v st st' Hw Hs.
  exists i.
  enough (mem st' !! pa_addN pa i = bv_to_bytes 8 v !! i) as ->
  by (setoid_rewrite bv_to_bytes_bv_get_byte; repeat apply conj; try done; lia).
  assert (length (bv_to_bytes 8 v) = N.to_nat size)
    by (rewrite length_bv_to_bytes, div_round_up_divisible; done).
  revert dependent pa st i.
  generalize dependent (bv_to_bytes 8 v).
  clear v.
  intro; revert size.
  elim l using rev_ind; cdestruct st' |- ***; first lia.
  destruct (decide (i = N.of_nat (length l0))) as [->|]; cbn.
  - unfold lookup at 2, list_lookupN.
    rewrite Nat2N.id, lookup_app.
    cdestruct |- *** #CDestrMatch #CDestrEqOpt; first by rewrite lookup_unfold in *.
    rewrite Nat.sub_diag; cbn.
    by eapply write_mem_seq_state_snoc.
  - unfold lookup at 2, list_lookupN.
    rewrite length_app in *; cbn in *.
    rewrite lookup_app.
    cdestruct |- *** #CDestrMatch #CDestrEqOpt; last rewrite lookup_unfold in *.
    2: opose proof (lookup_lt_is_Some_2 l0 (N.to_nat i) _); first lia; sauto.
    erewrite (H (N.pred size)); try done; try lia.
    eapply write_mem_seq_state_app; eauto.
Qed.

Lemma write_mem_seq_state_same_itrs bytes :
  ∀ st st' pa, (st', ()) ∈ write_mem_seq_state pa bytes st → itrs st' = itrs st.
Proof.
  induction bytes; cdestruct |- ***.
  change (itrs st) with (itrs (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)).
  eapply IHbytes, H.
Qed.

Section Proof.
Context (regs_whitelist : gset reg).

Lemma sequential_model_outcome_same_itrs st st' call r s :
  (st', r) ∈ sequential_model_outcome (Some regs_whitelist) s call st → itrs st' = itrs st.
Proof.
  destruct call;
  cdestruct |- *** #CDestrMatch;
  try naive_solver.
  all: do 2 unfold mthrow, Exec.throw_inst, Exec.res_throw_inst in *; try set_solver.
  eapply write_mem_seq_state_same_itrs.
  eauto.
Qed.

Lemma write_mem_seq_state_same_initSt bytes :
  ∀ st st' pa, (st', ()) ∈ write_mem_seq_state pa bytes st → initSt st' = initSt st.
Proof.
  induction bytes; cdestruct |- ***.
  change (initSt st) with (initSt (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)).
  eapply IHbytes, H.
Qed.

Lemma sequential_model_outcome_same_initSt st st' call r s :
  (st', r) ∈ sequential_model_outcome (Some regs_whitelist) s call st → initSt st' = initSt st.
Proof.
  destruct call;
  cdestruct |- *** #CDestrMatch;
  try naive_solver.
  all: do 2 unfold mthrow, Exec.throw_inst, Exec.res_throw_inst in *; try set_solver.
  eapply write_mem_seq_state_same_initSt.
  eauto.
Qed.

Definition rel_strictly_monotone (rel : grel EID.t) : Prop :=
  ∀ '(x,y) ∈ rel, EID.full_po_lt x y.

Definition rel_monotone (rel : grel EID.t) : Prop :=
  ∀ '(x,y) ∈ rel, x = y ∨ EID.full_po_lt x y.

Lemma rel_montone_union (rel1 rel2 : grel EID.t) :
  rel_strictly_monotone rel1 ∧ rel_strictly_monotone rel2 ↔ rel_strictly_monotone (rel1 ∪ rel2).
Proof.
  unfold rel_strictly_monotone.
  autorewrite with pair.
  cdestruct |- *** #CDestrSplitGoal.
  all: set_solver.
Qed.

Lemma rel_montone_intersection1 (rel1 rel2 : grel EID.t) :
  rel_strictly_monotone rel1 → rel_strictly_monotone (rel1 ∩ rel2).
Proof.
  unfold rel_strictly_monotone.
  autorewrite with pair.
  cdestruct |- *** #CDestrSplitGoal.
  all: set_solver.
Qed.

Lemma rel_montone_intersection2 (rel1 rel2 : grel EID.t) :
  rel_strictly_monotone rel1 → rel_strictly_monotone (rel1 ∩ rel2).
Proof.
  unfold rel_strictly_monotone.
  autorewrite with pair.
  cdestruct |- *** #CDestrSplitGoal.
  all: set_solver.
Qed.

Lemma grel_from_set_montone (eids : gset EID.t) :
  rel_monotone ⦗ eids ⦘.
Proof.
  unfold rel_monotone.
  autorewrite with pair.
  cdestruct |- ***.
  now left.
Qed.

Lemma rel_strictly_monotone_seq1 (rel1 rel2 : grel EID.t) :
  rel_strictly_monotone rel1 ∧ rel_monotone rel2 → rel_strictly_monotone (rel1 ⨾ rel2).
Proof.
  unfold rel_strictly_monotone, rel_monotone.
  autorewrite with pair.
  cdestruct |- *** #CDestrSplitGoal.
  eapply H in H1; eapply H0 in H2.
  cdestruct x0, H2 |- *** #CDestrSplitGoal.
Qed.

Lemma rel_strictly_monotone_seq2 (rel1 rel2 : grel EID.t) :
  rel_monotone rel1 ∧ rel_strictly_monotone rel2 → rel_strictly_monotone (rel1 ⨾ rel2).
Proof.
  unfold rel_strictly_monotone, rel_monotone.
  autorewrite with pair.
  cdestruct |- *** #CDestrSplitGoal.
  eapply H in H1; eapply H0 in H2.
  cdestruct x0, H2 |- *** #CDestrSplitGoal.
Qed.

Lemma rel_monotone_acyclic (rel : grel EID.t) :
  rel_strictly_monotone rel → grel_acyclic rel.
Proof.
  unfold rel_strictly_monotone, grel_acyclic, grel_irreflexive.
  autorewrite with pair.
  change (∀ x y, (x, y) ∈ rel → EID.full_po_lt x y)
    with (∀ x y, grel_to_relation rel x y → EID.full_po_lt x y).
  cdestruct |- *** as Hsubrel x Hcylcic.
  rewrite grel_plus_spec in Hcylcic.
  depelim Hcylcic.
  - specialize (Hsubrel _ _ H).
    unfold EID.full_po_lt, EID.po_lt, EID.iio_lt in *.
    lia.
  - opose proof (rtc_subrel _ _ _ _ Hsubrel _).
    1: eapply rtc_tc.
    1: right; eassumption.
    ospecialize (Hsubrel _ _ _); first eauto.
    clear -H0 Hsubrel.
    dependent induction H0.
    { unfold EID.full_po_lt, EID.po_lt, EID.iio_lt in *. lia. }
    eapply IHrtc.
    unfold EID.full_po_lt, EID.po_lt, EID.iio_lt in *.
    lia.
Qed.

Lemma rel_monotone_difference (rel1 rel2 : grel EID.t) :
  (∀ x y, (x,y) ∈ rel1 → EID.full_po_lt x y ∨ (x,y) ∈ rel2) →
  rel_strictly_monotone (rel1 ∖ rel2).
Proof.
  unfold rel_strictly_monotone.
  cdestruct |- *** as H a b ??.
  ospecialize (H _ _ _); eauto.
  cdestruct H |- *** #CDestrSplitGoal.
Qed.


(* Context (max_size : N) {max_size_upper_limit : (max_size < Z.to_N (bv_modulus 52))%N}.

Definition tr_wf (str : result seq_state seq_state) : Prop :=
  match str with
  | Ok st =>
    (∀ ev ∈ st.(itrs), is_mem_write ev → is_mem_writeP (λ size _, (size < max_size)%N) ev)
  | Error _ => False
  end.

Lemma op_reads st call :
  tr_wf (Ok st) →
  op_mem_wf (Ok st) →
  ∀ st' ∈ Exec.to_state_result_list (sequential_model_outcome_logged (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call st),
  is_Ok st' → tr_wf st' → op_mem_wf st'.
Proof.
  intros Htr H_st.
  cdestruct |- *** as st' r H_st' Hsize pa v.
  (* Case split: Is event a memory write? *)
  destruct (decide (is_mem_write (call &→ r))) as [ismw|].
  2: { (* Not mem write: no changes to mem map and remaining trace is still wf *)
    destruct call.
    all: do 7 deintro.
    all: cdestruct |- *** #CDestrMatch.
    all: rewrite trace_find_cons in *.
    all: now cdestruct |- *** #CDestrMatch.
  }
  (* mem write: memory map at pa is exactly written byte and otherwise unchanged *)
  destruct call; try easy; clear ismw.
  cdestruct st', r, H_st' |- *** as st' ? H_st' Hsize #CDestrMatch.
  rewrite trace_find_cons.
  cdestruct st, H_st |- *** #CDestrMatch.
  2: {
    enough (mem st' !! pa = mem st !! pa) as ->
    by (erewrite write_mem_seq_state_same_itrs in Hsize |- *; eauto).
    eapply pa_not_in_range_write; eauto.
    rewrite length_bv_to_bytes.
    f_equal.
    now eapply div_round_up_divisible.
    }
  apply pa_in_range_spec in p.
  cdestruct p as offset H_pa H_offset.
  assert (mem st' !! pa = Some (bv_get_byte 8 offset (WriteReq.value wr))) as ->
  by (eapply pa_in_range_write; eauto).
  cdestruct |- *** #CDestrSplitGoal.
  - eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
  - cdestruct v, pa |- ***.
    f_equal.
    unfold pa_addN, pa_addZ in H0; cbv in H0.
    destruct wr as [[]].
    cdestruct H0.
    eapply bv_add_Z_inj_l in H0; cdestruct H0 |- *** #CDestrSplitGoal #CDestrMatch; try lia.
    all: admit.
Admitted. *)

(* #[local] Typeclasses Transparent mword Z.to_N Decision RelDecision eq_vec_dec MachineWord.MachineWord.Z_idx. *)

Notation "( f <$>.)" := (fmap f) (only parsing) : stdpp_scope.

Print Instances Countable.
Record partial_cd_state := {
  pa_write_map : gmap pa EID.t;
  reg_write_map : gmap reg EID.t;
  pa_writes_set_map : gmap pa (gset EID.t);
  rf_acc : grel EID.t;
  rrf_acc : grel EID.t;
  co_acc : grel EID.t
}.
Set Printing Implicit.
Check pa_write_map.

#[local] Notation "cd∅" := (Build_partial_cd_state ∅ ∅ ∅ ∅ ∅ ∅).

#[global] Instance eta_partial_cd_state : Settable partial_cd_state :=
  settable! Build_partial_cd_state <pa_write_map;reg_write_map;pa_writes_set_map;rf_acc;rrf_acc;co_acc>.

Definition mem_write_upd_partial_cd_state (pa : pa) (weid : EID.t) (st : partial_cd_state) : partial_cd_state :=
  let oprev_weid_set := st.(pa_writes_set_map) !! pa in
  (if oprev_weid_set is Some prev_weids
  then
    st
    |> set co_acc (fold_left (λ acc prev_weid, {[(prev_weid, weid)]} ∪ acc) (elements prev_weids))
    |> setv (lookup pa ∘ pa_writes_set_map) (Some ({[weid]} ∪ prev_weids))
  else
    st |>
    setv (lookup pa ∘ pa_writes_set_map) (Some ({[weid]})))
  |> setv (lookup pa ∘ pa_write_map) (Some weid).

#[local] Instance elem_of_unfold_cdst_mem_write_co pa weid cdst peids P :
  SetUnfoldElemOf peids cdst.(co_acc) P →
  SetUnfoldElemOf peids (mem_write_upd_partial_cd_state pa weid cdst).(co_acc)
    (if cdst.(pa_writes_set_map) !! pa is Some prev_weids
    then (peids.1 ∈ prev_weids ∧ peids.2 = weid) ∨ P
    else P).
Proof using regs_whitelist.
  tcclean.
  destruct peids as [eid1 eid2].
  unfold mem_write_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
  2,5: naive_solver.
  - enough (eid1 ∈ elements g ∧ eid2 = weid ∨ P) by now set_unfold.
    generalize dependent (elements g).
    intro l; elim l using rev_ind; cdestruct |- ***; first hauto lq: on.
    rewrite fold_left_app in *.
    deintros; cdestruct |- *** #CDestrSplitGoal.
    1: left; cdestruct |- *** #CDestrSplitGoal; hauto lq: on.
    ospecialize (H1 _); first done.
    cdestruct H1 |- *** #CDestrSplitGoal; last by right.
    left; cdestruct |- *** #CDestrSplitGoal; naive_solver.
  - fold_left_inv_pose (λ co_acc prev_weids, (eid1,eid2) ∈ co_acc ∨ eid1 ∈ prev_weids).
    1: right; by cdestruct |- ***.
    1: cdestruct |- *** #CDestrSplitGoal; set_unfold; hauto lq: on.
    cdestruct H3 |- *** #CDestrSplitGoal.
  - fold_left_inv_pose (λ co_acc _, (eid1,eid2) ∈ co_acc).
    1: hauto lq: on.
    1: cdestruct |- *** #CDestrSplitGoal; set_unfold; try hauto lq: on.
    cdestruct H2 |- *** #CDestrSplitGoal.
Qed.

#[local] Instance elem_of_unfold_cdst_mem_write_rf pa weid cdst peids P :
  SetUnfoldElemOf peids cdst.(rf_acc) P →
  SetUnfoldElemOf peids (mem_write_upd_partial_cd_state pa weid cdst).(rf_acc) P.
Proof using regs_whitelist.
  tcclean.
  unfold mem_write_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance elem_of_unfold_cdst_mem_write_rrf pa weid cdst peids P :
  SetUnfoldElemOf peids cdst.(rrf_acc) P →
  SetUnfoldElemOf peids (mem_write_upd_partial_cd_state pa weid cdst).(rrf_acc) P.
Proof using regs_whitelist.
  tcclean.
  unfold mem_write_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance lookup_unfold_cdst_mem_write_pa_write_map cdst pa pa' weid o :
  LookupUnfold pa cdst.(pa_write_map) o →
  LookupUnfold pa (mem_write_upd_partial_cd_state pa' weid cdst).(pa_write_map)
    (if decide (pa = pa') then Some weid else o).
Proof.
  tcclean.
  unfold mem_write_upd_partial_cd_state.
  cdestruct pa, pa' |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
  all: unfold Setter_finmap.
  all: by rewrite lookup_unfold.
Qed.

#[local] Instance lookup_unfold_cdst_mem_write_reg_write_map cdst reg pa weid o :
  LookupUnfold reg cdst.(reg_write_map) o →
  LookupUnfold reg (mem_write_upd_partial_cd_state pa weid cdst).(reg_write_map) o.
Proof.
  tcclean.
  unfold mem_write_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance lookup_unfold_cdst_memw_pa_ws_set_map cdst pa pa' weid o :
  LookupUnfold pa' cdst.(pa_writes_set_map) o →
  LookupUnfold pa' (mem_write_upd_partial_cd_state pa weid cdst).(pa_writes_set_map)
    (if decide (pa' = pa)
    then (if o is Some ws then (Some ({[weid]} ∪ ws)) else Some {[weid]})
    else o).
Proof using regs_whitelist.
  tcclean.
  unfold mem_write_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
  all: unfold Setter_finmap.
  all: rewrite lookup_unfold.
  all: deintros; cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

Lemma eq_some_unfold_memw_upd_pcdst_pa_w_map cdst pa pa' weid weid' P :
  EqSomeUnfold (cdst.(pa_write_map) !! pa) weid P →
  EqSomeUnfold ((mem_write_upd_partial_cd_state pa' weid' cdst).(pa_write_map) !! pa)
    weid (pa = pa' ∧ weid = weid' ∨ pa ≠ pa' ∧ P).
Proof.
  tcclean.
  clear dependent P.
  rewrite lookup_unfold.
  cdestruct pa, pa', weid, weid' |- *** #CDestrMatch #CDestrSplitGoal #CDestrEqOpt.
  all: naive_solver.
Qed.

#[local] Instance eq_some_unfold_memw_upd_pcdst_reg_w_map cdst reg pa weid weid' P :
  EqSomeUnfold (cdst.(reg_write_map) !! reg) weid' P →
  EqSomeUnfold ((mem_write_upd_partial_cd_state pa weid cdst).(reg_write_map) !! reg)
     weid' P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

Lemma eq_some_unfold_cdst_memw_upd_pa_ws_set_map cdst pa pa' weid ws (P : gset EID.t → Prop)  Q :
  (∀ ws, EqSomeUnfold (cdst.(pa_writes_set_map) !! pa') ws (P ws)) →
  EqNoneUnfold (cdst.(pa_writes_set_map) !! pa') Q →
  EqSomeUnfold ((mem_write_upd_partial_cd_state pa weid cdst).(pa_writes_set_map) !! pa')
    ws
    (pa' = pa ∧ ((∃ ws', P ws' ∧ ws = ({[weid]} ∪ ws')) ∨ Q ∧ ws = {[weid]}) ∨
    pa' ≠ pa ∧ ((∃ ws', P ws' ∧ ws = ws') ∨ False)).
Proof using regs_whitelist.
  tcclean.
  clear dependent Q.
  rewrite lookup_unfold.
  deintros; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
  all: try (left+right; split; first done).
  1: best.
  all: fcrush.
Qed.

Lemma eq_none_unfold_cdst_memw_upd_pa_ws_set_map cdst pa pa' weid Q :
  EqNoneUnfold (cdst.(pa_writes_set_map) !! pa') Q →
  EqNoneUnfold ((mem_write_upd_partial_cd_state pa weid cdst).(pa_writes_set_map) !! pa')
    (pa' ≠ pa ∧ Q).
Proof using regs_whitelist.
  tcclean.
  rewrite lookup_unfold.
  cdestruct |- *** #CDestrMatch #CDestrSplitGoal #CDestrEqOpt.
Qed.

Definition mem_read_upd_partial_cd_state (pa : pa) (reid : EID.t) (st : partial_cd_state) : partial_cd_state :=
  let oweid := st.(pa_write_map) !! pa in
  if oweid is Some weid
  then set rf_acc ({[((weid,reid))]} ∪.) st
  else st.

#[local] Instance elem_of_unfold_cdst_mem_read_co pa reid cdst peids P :
  SetUnfoldElemOf peids cdst.(co_acc) P →
  SetUnfoldElemOf peids (mem_read_upd_partial_cd_state pa reid cdst).(co_acc) P.
Proof using regs_whitelist.
  tcclean.
  unfold mem_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance elem_of_unfold_cdst_mem_read_rf pa reid cdst peids P :
  SetUnfoldElemOf peids cdst.(rf_acc) P →
  SetUnfoldElemOf peids (mem_read_upd_partial_cd_state pa reid cdst).(rf_acc)
    (if cdst.(pa_write_map) !! pa is Some weid
    then (peids.1 = weid ∧ peids.2 = reid) ∨ P
    else P).
Proof using regs_whitelist.
  tcclean.
  unfold mem_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
  all: hauto lq: on.
Qed.

#[local] Instance elem_of_unfold_cdst_mem_read_rrf pa reid cdst peids P :
  SetUnfoldElemOf peids cdst.(rrf_acc) P →
  SetUnfoldElemOf peids (mem_read_upd_partial_cd_state pa reid cdst).(rrf_acc) P.
Proof using regs_whitelist.
  tcclean.
  unfold mem_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance lookup_unfold_cdst_mem_read_pa_write_map cdst pa pa' weid o :
  LookupUnfold pa cdst.(pa_write_map) o →
  LookupUnfold pa (mem_read_upd_partial_cd_state pa' weid cdst).(pa_write_map) o.
Proof.
  tcclean.
  unfold mem_read_upd_partial_cd_state.
  cdestruct pa, pa' |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance lookup_unfold_cdst_mem_read_reg_write_map cdst reg pa reid o :
  LookupUnfold reg cdst.(reg_write_map) o →
  LookupUnfold reg (mem_read_upd_partial_cd_state pa reid cdst).(reg_write_map) o.
Proof.
  tcclean.
  unfold mem_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance lookup_unfold_cdst_memr_pa_ws_set_map cdst pa pa' reid o :
  LookupUnfold pa' cdst.(pa_writes_set_map) o →
  LookupUnfold pa' (mem_read_upd_partial_cd_state pa reid cdst).(pa_writes_set_map) o.
Proof.
  tcclean.
  unfold mem_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.


#[local] Instance eq_some_unfold_memr_upd_pcdst_pa_w_map cdst pa pa' weid weid' P :
  EqSomeUnfold (cdst.(pa_write_map) !! pa) weid P →
  EqSomeUnfold ((mem_read_upd_partial_cd_state pa' weid' cdst).(pa_write_map) !! pa)
    weid P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[local] Instance eq_some_unfold_memr_upd_pcdst_reg_w_map cdst reg pa weid weid' P :
  EqSomeUnfold (cdst.(reg_write_map) !! reg) weid' P →
  EqSomeUnfold ((mem_read_upd_partial_cd_state pa weid cdst).(reg_write_map) !! reg)
     weid' P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

Definition reg_write_upd_partial_cd_state (reg : reg) (weid : EID.t) : partial_cd_state → partial_cd_state :=
  setv (lookup reg ∘ reg_write_map) (Some weid).

#[local] Instance elem_of_unfold_cdst_reg_write_co reg weid cdst peids P :
  SetUnfoldElemOf peids cdst.(co_acc) P →
  SetUnfoldElemOf peids (reg_write_upd_partial_cd_state reg weid cdst).(co_acc) P.
Proof using regs_whitelist. by tcclean. Qed.

#[local] Instance elem_of_unfold_cdst_reg_write_rf reg weid cdst peids P :
  SetUnfoldElemOf peids cdst.(rf_acc) P →
  SetUnfoldElemOf peids (reg_write_upd_partial_cd_state reg weid cdst).(rf_acc) P.
Proof using regs_whitelist. by tcclean. Qed.

#[local] Instance elem_of_unfold_cdst_reg_write_rrf reg weid cdst peids P :
  SetUnfoldElemOf peids cdst.(rrf_acc) P →
  SetUnfoldElemOf peids (reg_write_upd_partial_cd_state reg weid cdst).(rrf_acc) P.
Proof using regs_whitelist.
  tcclean.
  unfold reg_write_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance lookup_unfold_cdst_reg_write_pa_write_map cdst pa reg weid o :
  LookupUnfold pa cdst.(pa_write_map) o →
  LookupUnfold pa (reg_write_upd_partial_cd_state reg weid cdst).(pa_write_map) o.
Proof. by tcclean. Qed.

#[local] Instance lookup_unfold_cdst_reg_write_reg_write_map cdst reg reg' weid o :
  LookupUnfold reg cdst.(reg_write_map) o →
  LookupUnfold reg (reg_write_upd_partial_cd_state reg' weid cdst).(reg_write_map)
    (if decide (reg = reg') then Some weid else o).
Proof.
  tcclean.
  unfold reg_write_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
  all: unfold Setter_finmap.
  all: rewrite lookup_unfold.
  all: cdestruct |- *** #CDestrMatch.
Qed.

#[local] Instance eq_some_unfold_regw_upd_pcdst_pa_w_map cdst pa reg weid weid' P :
  EqSomeUnfold (cdst.(pa_write_map) !! pa) weid' P →
  EqSomeUnfold ((reg_write_upd_partial_cd_state reg weid cdst).(pa_write_map) !! pa)
     weid' P.
Proof. tcclean. by rewrite lookup_unfold. Qed.


Lemma eq_some_unfold_regw_upd_pcdst_reg_w_map cdst reg reg' weid weid' P :
  EqSomeUnfold (cdst.(reg_write_map) !! reg) weid P →
  EqSomeUnfold ((reg_write_upd_partial_cd_state reg' weid' cdst).(reg_write_map) !! reg)
    weid (reg = reg' ∧ weid = weid' ∨ reg ≠ reg' ∧ P).
Proof.
  tcclean.
  clear dependent P.
  rewrite lookup_unfold.
  cdestruct reg, reg', weid, weid' |- *** #CDestrMatch #CDestrSplitGoal #CDestrEqOpt.
  all: naive_solver.
Qed.

Definition reg_read_upd_partial_cd_state (reg : reg) (reid : EID.t) (st : partial_cd_state) : partial_cd_state :=
  let oweid := st.(reg_write_map) !! reg in
  if oweid is Some weid
  then set rrf_acc ({[((weid,reid))]} ∪.) st
  else st.

#[local] Instance elem_of_unfold_cdst_reg_read_co reg reid cdst peids P :
  SetUnfoldElemOf peids cdst.(co_acc) P →
  SetUnfoldElemOf peids (reg_read_upd_partial_cd_state reg reid cdst).(co_acc) P.
Proof using regs_whitelist.
  tcclean.
  unfold reg_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch.
Qed.

#[local] Instance elem_of_unfold_cdst_reg_read_rf reg reid cdst peids P :
  SetUnfoldElemOf peids cdst.(rf_acc) P →
  SetUnfoldElemOf peids (reg_read_upd_partial_cd_state reg reid cdst).(rf_acc) P.
Proof using regs_whitelist.
  tcclean.
  unfold reg_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch.
Qed.

#[local] Instance elem_of_unfold_cdst_reg_read_rrf reg reid cdst peids P :
  SetUnfoldElemOf peids cdst.(rrf_acc) P →
  SetUnfoldElemOf peids (reg_read_upd_partial_cd_state reg reid cdst).(rrf_acc)
    (if cdst.(reg_write_map) !! reg is Some weid
    then (peids.1 = weid ∧ peids.2 = reid) ∨ P
    else P).
Proof using regs_whitelist.
  tcclean.
  unfold reg_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
  all: hauto lq: on.
Qed.

#[local] Instance lookup_unfold_cdst_reg_read_pa_write_map cdst pa reg weid o :
  LookupUnfold pa cdst.(pa_write_map) o →
  LookupUnfold pa (reg_read_upd_partial_cd_state reg weid cdst).(pa_write_map) o.
Proof.
  tcclean.
  unfold reg_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch.
Qed.

#[local] Instance lookup_unfold_cdst_reg_read_reg_write_map cdst reg reg' reid o :
  LookupUnfold reg cdst.(reg_write_map) o →
  LookupUnfold reg (reg_read_upd_partial_cd_state reg' reid cdst).(reg_write_map) o.
Proof.
  tcclean.
  unfold reg_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance lookup_unfold_cdst_regr_pa_ws_set_map cdst pa reg reid o :
  LookupUnfold pa cdst.(pa_writes_set_map) o →
  LookupUnfold pa (reg_read_upd_partial_cd_state reg reid cdst).(pa_writes_set_map) o.
Proof.
  tcclean.
  unfold reg_read_upd_partial_cd_state.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance eq_some_unfold_regr_upd_pcdst_pa_w_map cdst pa reg weid weid' P :
  EqSomeUnfold (cdst.(pa_write_map) !! pa) weid' P →
  EqSomeUnfold ((reg_read_upd_partial_cd_state reg weid cdst).(pa_write_map) !! pa)
     weid' P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[local] Instance eq_some_unfold_regr_upd_pcdst_reg_w_map cdst reg reg' weid weid' P :
  EqSomeUnfold (cdst.(reg_write_map) !! reg) weid P →
  EqSomeUnfold ((reg_read_upd_partial_cd_state reg' weid' cdst).(reg_write_map) !! reg)
    weid P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

Definition update_partial_cd_state_for_eid_ev st '(eid, ev) :=
  match ev with
  | MemWrite _ wr &→ _ => mem_write_upd_partial_cd_state wr.(WriteReq.pa) eid st
  | MemRead _ rr &→ _ => mem_read_upd_partial_cd_state rr.(ReadReq.pa) eid st
  | RegWrite reg _ _ &→ _ => reg_write_upd_partial_cd_state reg eid st
  | RegRead reg _ &→ _ => reg_read_upd_partial_cd_state reg eid st
  | _ => st
  end.
Arguments update_partial_cd_state_for_eid_ev : simpl never.
Arguments mem_write_upd_partial_cd_state : simpl never.
Arguments mem_read_upd_partial_cd_state : simpl never.

Definition construct_cd_for_pe (pe : Candidate.pre Candidate.NMS 1) : partial_cd_state → partial_cd_state :=
  fold_left update_partial_cd_state_for_eid_ev (Candidate.event_list pe).

Definition build_pre_exec initSt itrs : Candidate.pre Candidate.NMS 1 :=
  Candidate.make_pre Candidate.NMS initSt [# trace_rev itrs].
Arguments build_pre_exec : simpl never.

Notation "(seq_state_to_pe seq_st )" := (build_pre_exec seq_st.(initSt) seq_st.(itrs)) (seq_st at next level).

Definition partial_cd_state_to_cd (cdst : partial_cd_state) (pe : Candidate.pre Candidate.NMS 1) : Candidate.t Candidate.NMS 1 :=
  Candidate.make _ pe cdst.(rf_acc) cdst.(rrf_acc) cdst.(co_acc) ∅.

(* Definition seq_partial_cd_states_to_partial_cd_state (seqst : seq_state) (cdst : partial_cd_state) : partial_cd_state :=
  (construct_cd_for_pe (seq_state_to_pe seqst) cdst).

Definition seq_partial_cd_states_to_cd (seqst : seq_state) (cdst : partial_cd_state) : Candidate.t Candidate.NMS 1 :=
  let pe := (seq_state_to_pe seqst) in
  partial_cd_state_to_cd (construct_cd_for_pe pe cdst) pe. *)

Notation "(seq_state_to_partial_cd_state seq_st )" :=
  (construct_cd_for_pe (seq_state_to_pe seq_st) cd∅) (seq_st at next level).

Notation "(seq_state_to_cd seq_st )" :=
  (partial_cd_state_to_cd (seq_state_to_partial_cd_state seq_st) (seq_state_to_pe seq_st)) (seq_st at next level).

Lemma seqst_to_pe_equal st st' :
  st.(initSt) = st'.(initSt) → st.(itrs) = st'.(itrs) →
  (seq_state_to_pe st) = (seq_state_to_pe st').
Proof. now intros -> ->. Qed.

Lemma seq_state_step_to_pe_eq seq_st seq_st_succ call ret :
  (seq_st_succ, ret) ∈ sequential_model_outcome (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call seq_st →
  (seq_state_to_pe (set itrs (trace_cons (call &→ ret)) seq_st_succ)) = (seq_state_to_pe (set itrs (trace_cons (call &→ ret)) seq_st)).
Proof.
  cdestruct |- ***.
  erewrite sequential_model_outcome_same_initSt, sequential_model_outcome_same_itrs; eauto.
Qed.

Lemma seq_state_to_pe_trace_cons initSt itrs ev :
  (build_pre_exec initSt (trace_cons ev itrs)) =
  set ((.!!! 0%fin) ∘ Candidate.events) (trace_snoc ev) (build_pre_exec initSt itrs).
Proof.
  unfold build_pre_exec; cbv [set]; cbn; unfold Setter_compose; cbn.
  do 2 f_equal.
  unfold trace_snoc, unsnoc_total.
  destruct itrs; first done.
  now rewrite unsnoc_snoc.
Qed.

Lemma seq_state_to_pe_traces_cons seqst ev :
  (seq_state_to_pe (set itrs (trace_cons ev) seqst)) =
  set Candidate.events (traces_snoc ev 0%fin) (seq_state_to_pe seqst).
Proof.
  unfold build_pre_exec; cbv [set]; cbn.
  do 2 f_equal.
  unfold trace_snoc, unsnoc_total.
  destruct (itrs seqst); first done.
  now rewrite unsnoc_snoc.
Qed.

  (* #[local] Instance lookup_ev_from_iTraces {nmth : nat} : Lookup EID.t iEvent (vec (list (iTrace ())) nmth) :=
  λ eid evs,
  traces ← evs !! eid.(EID.tid);
  '(trace, result) ← traces !! eid.(EID.iid);
  trace !! eid.(EID.ieid). *)

#[local] Instance lookup_unfold_vec_singleton (n : nat) `(v : A) :
  LookupUnfold 0 [#v] (Some v).
Proof.
  tcclean.
  unfold lookup, vec_lookup_nat.
  cdestruct n |- *** #CDestrMatch; lia.
Qed.

Lemma lookup_partial_cd_state_to_cd eid pcdst pe :
  (partial_cd_state_to_cd pcdst pe) !! eid = pe !! eid.
Proof. rewrite cd_to_pe_lookup. by unfold partial_cd_state_to_cd. Qed.

#[local] Instance lookup_unfold_partial_cd_state_to_cd eid pcdst pe o :
  LookupUnfold eid pe o →
  LookupUnfold eid (partial_cd_state_to_cd pcdst pe) o.
Proof. tcclean. apply lookup_partial_cd_state_to_cd. Qed.

#[local] Instance eq_some_unfold_partial_cd_state_to_cd eid pcdst pe ev P :
  EqSomeUnfold (pe !! eid) ev P →
  EqSomeUnfold (partial_cd_state_to_cd pcdst pe !! eid) ev P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[local] Instance eq_none_unfold_partial_cd_state_to_cd eid pcdst pe P :
  EqNoneUnfold (pe !! eid) P →
  EqNoneUnfold (partial_cd_state_to_cd pcdst pe !! eid) P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[local] Instance lookup_unfold_cd_to_pe`(cd : Candidate.t et nmth) eid o :
  LookupUnfold eid cd o →
  LookupUnfold eid (Candidate.pre_exec cd) o.
Proof. tcclean. now rewrite cd_to_pe_lookup. Qed.

#[local] Instance eq_some_unfold_cd_to_pe {et nmth} (cd : Candidate.t et nmth) eid ev P :
  EqSomeUnfold (cd !! eid) ev P →
  EqSomeUnfold (Candidate.pre_exec cd !! eid) ev P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[local] Instance eq_none_unfold_cd_to_pe {et nmth} (cd : Candidate.t et nmth) eid P :
  EqNoneUnfold (cd !! eid) P →
  EqNoneUnfold (Candidate.pre_exec cd !! eid) P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[local] Instance lookup_total_unfold_vec_singleton (n : fin 1) `(x : A) :
  LookupTotalUnfold n [#x] x.
Proof.
  tcclean.
  depelim n.
  1: done.
  depelim n1.
Qed.

Lemma lookup_pe_to_lookup_trace (pe : Candidate.pre Candidate.NMS 1) eid :
  pe !! eid = (pe.(Candidate.events) !!! 0%fin) !! eid.
Proof.
  destruct pe.
  do 2 depelim events.
  cbn [Candidate.events].
  rewrite lookup_total_unfold.
  apply option_eq.
  intro ev.
  destruct eid.
  unfold build_pre_exec, lookup, Candidate.lookup_eid_pre, Candidate.lookup_iEvent,
    Candidate.lookup_instruction, lookup_ev_from_iTraces, build_pre_exec.
    cbn.
  cdestruct tid |- *** #CDestrEqOpt #CDestrSplitGoal; first lia.
  2: eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  1: rewrite lookup_total_unfold in H.
  all: eexists (_,_); cdestruct |- *** #CDestrSplitGoal; eauto.
Qed.

#[local] Instance lookup_unfold_pe_eid (pe : Candidate.pre Candidate.NMS 1) eid o :
  LookupUnfold eid (pe.(Candidate.events) !!! 0%fin) o →
  LookupUnfold eid pe o.
Proof. tcclean. by rewrite lookup_pe_to_lookup_trace. Qed.

Lemma lookup_seq_state_to_cd eid seqst :
  (seq_state_to_cd seqst) !! eid = (trace_rev seqst.(itrs)) !! eid.
Proof. rewrite lookup_unfold. by unfold build_pre_exec. Qed.

#[local] Instance lookup_unfold_seq_state_to_cd (eid : EID.t) seqst o :
  LookupUnfold eid (trace_rev seqst.(itrs)) o →
  LookupUnfold eid (seq_state_to_cd seqst) o.
Proof.
  tcclean.
  by rewrite lookup_seq_state_to_cd.
Qed.

#[local] Instance lookup_seq_state_to_pe eid seq_st o :
  LookupUnfold eid (trace_rev seq_st.(itrs)) o →
  LookupUnfold eid (seq_state_to_pe seq_st) o.
Proof. tcclean. rewrite lookup_unfold. by unfold build_pre_exec. Qed.

#[export] Instance lookup_unfold_intra_trace_eid_succ_None evs :
  LookupUnfold (intra_trace_eid_succ 0 evs) evs None.
Proof.
  tcclean.
  unfold intra_trace_eid_succ, unsnoc_total.
  destruct (decide (evs = [])) as [->|Hevs_not_empty]; cdestruct |- ***.
  destruct (exists_last Hevs_not_empty)as [? [[] ->]].
  rewrite unsnoc_snoc.
  unfold lookup, lookup_ev_from_iTraces.
  cdestruct |- *** #CDestrEqOpt.
  rewrite length_app; cbn.
  rewrite Nat.add_1_r; cbn.
  rewrite lookup_app.
  cdestruct |- *** #CDestrMatch #CDestrEqOpt; rewrite lookup_unfold in *.
  1: done.
  rewrite Nat.sub_diag; cbn.
  by rewrite lookup_unfold.
Qed.

#[local] Instance eq_none_unfold_lookup_intra_trace_eid_succ_None evs :
  EqNoneUnfold (evs !! (intra_trace_eid_succ 0 evs)) True.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[local] Instance eq_some_unfold_lookup_intra_trace_eid_succ_None evs ev :
  EqSomeUnfold (evs !! (intra_trace_eid_succ 0 evs)) ev False.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[export] Instance lookup_unfold_pe_intra_trace_eid_succ_None (init : MState.t 1) evs :
  LookupUnfold (intra_trace_eid_succ 0 evs) (Candidate.make_pre Candidate.NMS init [# evs]) None.
Proof.
  tcclean.
  rewrite lookup_pe_to_lookup_trace.
  cbn.
  by rewrite lookup_unfold.
Qed.

#[local] Instance lookup_total_unfold_events_build_pre_exec (n : fin 1) init itrs :
  LookupTotalUnfold n (Candidate.events (build_pre_exec init itrs)) (trace_rev itrs).
Proof using regs_whitelist.
  depelim n.
  2: sauto q: on.
  tcclean.
  by unfold build_pre_exec.
Qed.

Lemma eq_some_unfold_lookup_eid_trace_snoc itrs eid ev ev' :
  EqSomeUnfold (trace_snoc ev itrs !! eid) ev'
    (if decide (is_Some (itrs !! eid))
    then itrs !! eid = Some ev'
    else eid = intra_trace_eid_succ 0 itrs ∧ ev = ev').
Proof.
  tcclean.
  clear dependent regs_whitelist.
  cdestruct |- *** as #CDestrMatch #CDestrEqOpt.
  - intros ev'' H_itrs.
    destruct (decide (itrs = [])) as [->|Hne].
    1: unfold lookup, lookup_ev_from_iTraces in H_itrs; cdestruct H_itrs #CDestrEqOpt.
    pose proof (exists_last Hne) as [itrstr [[itr] ->]].
    destruct (decide (itr = [])) as [->|Hne'] .
    { rewrite trace_snoc_app; last done.
      unfold lookup, lookup_ev_from_iTraces in *.
      deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: rewrite lookup_app in *.
      all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: eauto. }
    pose proof (exists_last Hne') as [trstr [ev''' ->]].
    rewrite trace_snoc_app; last done.
    cbn.
    destruct eid.
    unfold lookup, lookup_ev_from_iTraces in *.
    deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: rewrite lookup_app in *.
    all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: eauto.
    all: rewrite lookup_app in *.
    all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: rewrite ?lookup_app in *.
    all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: rewrite ?H0; cbn.
    all: eexists (_,_); cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: rewrite ?lookup_app in *.
    all: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    1,3: hauto q: on.
    1: rewrite length_app; cbn; lia.
  - intros H_itrs%eq_None_not_Some.
    opose proof (intra_trace_eid_succ_tid 0 itrs) as H_tid.
    opose proof (intra_trace_eid_succ_byte 0 itrs) as H_byte.
    destruct (decide (itrs = [])) as [->|Hne].
    { destruct eid.
      unfold lookup, lookup_ev_from_iTraces in *.
      deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal. }
    pose proof (exists_last Hne) as [itrstr [[itr] ->]].
    rewrite trace_snoc_app; last done.
    destruct (decide (itr = [])) as [->|Hne'].
    { unfold trace_snoc. cbn.
      destruct eid.
      unfold lookup, lookup_ev_from_iTraces in *.
      split.
      all: cdestruct H_itrs #CDestrSplitGoal #CDestrEqOpt; deintros; cdestruct |- *** #CDestrEqOpt.
      all: rewrite ?lookup_app in *.
      all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrMatch.
      1: unfold intra_trace_eid_succ, unsnoc_total.
      1: rewrite unsnoc_snoc; cbn; cdestruct |- *** #CDestrSplitGoal.
      1: rewrite length_app; cbn; rewrite Nat.add_1_r; cbn.
      1: eapply lookup_ge_None_1 in H; unfold iTrace, fTrace;
        generalize dependent (@Datatypes.length (prod (list (@fEvent outcome outcome_ret)) (fTraceEnd outcome unit))
        itrstr); lia.
      all: rewrite <- ?H0, <- ?H1 in *; try done; cbn in *.
      all: unfold intra_trace_eid_succ, unsnoc_total in *; rewrite unsnoc_snoc, length_app in *.
      all: deintros; cdestruct |- *** #CDestrSplitGoal.
      all: rewrite Nat.add_1_r in *; cbn in *.
      1: by rewrite lookup_unfold in H.
      rewrite Nat.sub_diag in *; cbn in *.
      eexists (_,_); split; eauto. }
      unfold intra_trace_eid_succ, unsnoc_total in *; rewrite unsnoc_snoc, length_app in *.
      unfold lookup, lookup_ev_from_iTraces in *.
      all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      1: destruct eid.
      1: rewrite lookup_app in *.
      1: deintros; cdestruct |- *** #CDestrSplitGoal #CDestrMatch.
      1,2: sfirstorder.
      all: unfold iTrace, fTrace, iEvent in *.
      1: apply lookup_length in H2; eapply lookup_ge_None_1 in H1; cbn in *; lia.
      1: destruct (iid - length itrstr); cbn in *; last done.
      1: cdestruct f, l, H2.
      1: rewrite lookup_app in *.
      1: deintros; cdestruct |- *** #CDestrSplitGoal #CDestrMatch.
      1: apply lookup_length in H3; eapply lookup_ge_None_1 in H2; cbn in *; lia.
      1: rewrite lookup_app in *; deintros; cdestruct |- *** #CDestrMatch #CDestrEqOpt.
      1: rewrite lookup_app in *; deintros; cdestruct |- *** #CDestrMatch #CDestrEqOpt.
      1: rewrite H3 in *; naive_solver.
      rewrite Nat.add_1_r, lookup_app in *; cbn in *; cdestruct H |- *** #CDestrMatch #CDestrEqOpt.
      1: by rewrite lookup_unfold in H.
      rewrite Nat.sub_diag in *; cbn in *.
      all: eexists (_,_); cdestruct |- *** #CDestrSplitGoal.
      rewrite lookup_app.
      cdestruct |- *** #CDestrMatch.
      by rewrite Nat.sub_diag.
Qed.

#[local] Instance eq_some_unfold_lookup_eid_trace_snoc_in_tail itrs eid ev ev' ev'' :
  TCFastDone (itrs !! eid = Some ev') →
  EqSomeUnfold (trace_snoc ev itrs !! eid) ev'' (ev' = ev'').
Proof.
  tcclean.
  cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_snoc #CDestrEqOpt
    #CDestrSplitGoal #CDestrMatch.
Qed.

#[local] Instance eq_some_unfold_lookup_succ_eid_trace_snoc_hd itrs eid ev ev' :
  TCFastDone (eid = intra_trace_eid_succ 0 itrs) →
  EqSomeUnfold (trace_snoc ev itrs !! eid) ev' (ev = ev').
Proof.
  tcclean.
  cdestruct eid |- *** ##eq_some_unfold_lookup_eid_trace_snoc #CDestrEqOpt
    #CDestrSplitGoal #CDestrMatch.
Qed.

#[local] Instance eq_some_unfold_lookup_trace_snoc_not_succ_eid itrs eid ev ev' P :
  TCFastDone (eid ≠ intra_trace_eid_succ 0 itrs) →
  EqSomeUnfold (itrs !! eid) ev P →
  EqSomeUnfold (trace_snoc ev' itrs !! eid) ev P.
Proof.
  tcclean.
  cdestruct eid |- *** ##eq_some_unfold_lookup_eid_trace_snoc #CDestrEqOpt
    #CDestrSplitGoal #CDestrMatch.
Qed.

#[local] Instance eq_some_unfold_lookup_succ_eid_None itrs eid ev :
  TCFastDone (eid = intra_trace_eid_succ 0 itrs) →
  EqSomeUnfold (itrs !! eid) ev False.
Proof.
  tcclean.
  cdestruct eid |- *** ##eq_some_unfold_lookup_eid_trace_snoc #CDestrEqOpt
    #CDestrSplitGoal #CDestrMatch.
Qed.

#[local] Instance eq_None_trace_lookup_rev_snoc itrs eid ev P :
  EqNoneUnfold (itrs !! eid) P →
  EqNoneUnfold (trace_snoc ev itrs !! eid) (P ∧ eid ≠ intra_trace_eid_succ 0 itrs).
Proof.
  clear regs_whitelist.
  tcclean.
  cdestruct eid, ev |- *** as ? _ ? HNone ##eq_some_unfold_lookup_eid_trace_snoc #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
  all: intros.
  2: intros ->.
  1,3: eapply eq_None_ne_Some_2; intros ??.
  all: eapply eq_None_ne_Some_1; eauto.
  all: clear HNone.
  all: deintros; cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_snoc
    #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
Qed.

Lemma eq_some_unfold_lookup_eid_trace_rev_cons itrs eid ev ev' :
  EqSomeUnfold (trace_rev (trace_cons ev itrs) !! eid) ev'
    (if decide (is_Some (trace_rev itrs !! eid))
    then trace_rev itrs !! eid = Some ev'
    else eid = intra_trace_eid_succ 0 (trace_rev itrs) ∧ ev = ev').
Proof.
  tcclean.
  rewrite <- trace_snoc_rev_cons.
  cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_snoc #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance eq_some_unfold_lookup_eid_trace_rev_cons_in_tail itrs eid ev ev' ev'' :
  TCFastDone (trace_rev itrs !! eid = Some ev') →
  EqSomeUnfold (trace_rev (trace_cons ev itrs) !! eid) ev'' (ev' = ev'').
Proof.
  tcclean.
  cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt
    #CDestrSplitGoal #CDestrMatch.
Qed.

#[local] Instance lookup_unfold_trace_cons_eid_succ ev itrs :
  LookupUnfold (intra_trace_eid_succ 0 (trace_rev itrs)) (trace_rev (trace_cons ev itrs))
    (Some ev).
Proof.
  tcclean.
  cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
    #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
Qed.

#[local] Instance eq_some_unfold_lookup_succ_eid_trace_rev_cons_hd itrs eid ev ev' :
  TCFastDone (eid = intra_trace_eid_succ 0 (trace_rev itrs)) →
  EqSomeUnfold (trace_rev (trace_cons ev itrs) !! eid) ev' (ev = ev').
Proof.
  tcclean.
  cdestruct eid |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt
    #CDestrSplitGoal #CDestrMatch.
Qed.

#[local] Instance eq_some_unfold_lookup_trace_rev_cons_not_succ_eid itrs eid ev ev' P :
  TCFastDone (eid ≠ intra_trace_eid_succ 0 (trace_rev itrs)) →
  EqSomeUnfold (trace_rev itrs !! eid) ev P →
  EqSomeUnfold (trace_rev (trace_cons ev' itrs) !! eid) ev P.
Proof.
  tcclean.
  cdestruct eid |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt
    #CDestrSplitGoal #CDestrMatch.
Qed.

#[local] Instance eq_None_trace_lookup_rev_cons itrs eid ev P :
  EqNoneUnfold (trace_rev itrs !! eid) P →
  EqNoneUnfold (trace_rev (trace_cons ev itrs) !! eid) (P ∧ eid ≠ intra_trace_eid_succ 0 (trace_rev itrs)).
Proof.
  tcclean.
  rewrite <- trace_snoc_rev_cons.
  cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
Qed.

#[local] Instance Incompatible_Some_and_None {A} (o : option A) (a : A) :
  Incompatible (o = None) (o = Some a).
Proof. tcclean. cdestruct |- ***. Qed.

#[local] Instance set_unfold_elem_of_collect_all_trace_snoc  `{∀ eid ev, Decision (P eid ev)}
    (pe : Candidate.pre Candidate.NMS 1) ev eid  Q :
  SetUnfoldElemOf eid (Candidate.collect_all P pe) Q →
  SetUnfoldElemOf eid
    (Candidate.collect_all P (set ((.!!! 0%fin) ∘ Candidate.events) (trace_snoc ev) pe))
    (Q ∨ (eid = intra_trace_eid_succ 0 (Candidate.events pe !!! 0%fin) ∧ P eid ev)).
Proof.
  tcclean.
  destruct pe.
  repeat depelim events.
  clear dependent Q.
  set_unfold.
  rewrite lookup_unfold.
  cbn.
  cdestruct eid |- *** ##eq_some_unfold_lookup_eid_trace_snoc #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
  all: rewrite ?lookup_unfold in *; cbn in *.
  - naive_solver.
  - naive_solver.
  - eexists x.
    cdestruct eid |- *** ##eq_some_unfold_lookup_eid_trace_snoc #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    all: naive_solver.
  - eexists ev.
    cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_snoc #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
Qed.

#[local] Instance lookup_unfold_build_pre_exec eid init events o :
  LookupUnfold eid (trace_rev events) o →
  LookupUnfold eid (build_pre_exec init events) o.
Proof. tcclean. unfold build_pre_exec. by rewrite lookup_unfold. Qed.

#[local] Instance eq_some_unfold_build_pre_exec_lookup eid init events ev P :
  EqSomeUnfold (trace_rev events !! eid) ev P →
  EqSomeUnfold (build_pre_exec init events !! eid) ev P.
Proof. tcclean. by rewrite lookup_unfold. Qed.

#[local] Instance eq_none_unfold_build_pre_exec_lookup eid init events P :
  EqNoneUnfold (trace_rev events !! eid) P →
  EqNoneUnfold (build_pre_exec init events !! eid) P.
Proof. tcclean. by rewrite lookup_unfold. Qed.


Definition cd_monotone (cd : Candidate.t Candidate.NMS 1) : Prop :=
  rel_strictly_monotone cd.(Candidate.reads_from)
  ∧ rel_strictly_monotone cd.(Candidate.reg_reads_from)
  ∧ rel_strictly_monotone cd.(Candidate.coherence).

Definition partial_cd_state_monotone (cdst : partial_cd_state) : Prop :=
  rel_strictly_monotone cdst.(rf_acc)
  ∧ rel_strictly_monotone cdst.(rrf_acc)
  ∧ rel_strictly_monotone cdst.(co_acc).

Lemma event_list_monotone {nmth} (pe : Candidate.pre Candidate.NMS nmth) l l' :
  Candidate.event_list pe = l ++ l' →
  ∀ '(eid1, ev1) ∈ l, ∀ '(eid2, ev2) ∈ l', eid1.(EID.tid) = eid2.(EID.tid) →
  EID.full_po_lt eid1 eid2.
Admitted.

Arguments Candidate.event_list : simpl never.

Definition seq_model_outcome_invariant_preserved (I I' : seq_state → Prop) : Prop :=
  ∀ (seq_st : seq_state),
  I seq_st →
  ∀ (call : outcome) ret seq_st_succ,
  (seq_st_succ, ret) ∈ sequential_model_outcome (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call seq_st →
  I' (set itrs (trace_cons (call &→ ret)) seq_st_succ).

Lemma seq_state_to_partial_cd_state_destruct (I : partial_cd_state → Prop) initSt itrs call ret :
  let succ_eid := intra_trace_eid_succ 0 (Candidate.events (build_pre_exec initSt itrs) !!! 0%fin) in
  let pcdst := (construct_cd_for_pe (build_pre_exec initSt itrs) cd∅) in
  (¬ is_mem_event (call &→ ret) → ¬ is_reg_write (call &→ ret) → ¬ is_reg_read (call &→ ret) → I pcdst) →
  (∀ reg racc, call = RegRead reg racc → I (reg_read_upd_partial_cd_state reg succ_eid pcdst)) →
  (∀ reg racc regval, call = RegWrite reg racc regval → I (reg_write_upd_partial_cd_state reg succ_eid pcdst)) →
  (∀ n rr, call = MemRead n rr → I (mem_read_upd_partial_cd_state rr.(ReadReq.pa) succ_eid pcdst)) →
  (∀ n wr, call = MemWrite n wr → I (mem_write_upd_partial_cd_state wr.(WriteReq.pa) succ_eid pcdst)) →
  I (construct_cd_for_pe (build_pre_exec initSt (trace_cons (call &→ ret) itrs)) cd∅).
Proof.
  intro.
  unfold construct_cd_for_pe.
  destruct call.
  all: cdestruct |- ***.
  all: erewrite seq_state_to_pe_trace_cons, trace_snoc_event_list.
  all: rewrite fold_left_app.
  1-13: hauto l: on.
Qed.

Lemma seq_state_to_pe_fold seq_st :
  {| Candidate.init := Candidate.init (seq_state_to_pe seq_st);
    Candidate.events := [#Candidate.events (seq_state_to_pe seq_st) !!! 0%fin] |}
  = (seq_state_to_pe seq_st).
Proof. unfold build_pre_exec. cdestruct |- ***. Qed.

(* #[local] Instance set_unfold_elem_of_co_acc_trace_cons init itrs ev x y P :
  SetUnfoldElemOf (x, y)
    (co_acc (construct_cd_for_pe (build_pre_exec init itrs) cd∅)) P →
  SetUnfoldElemOf (x, y)
    (co_acc (construct_cd_for_pe (build_pre_exec init (trace_cons ev itrs)) cd∅))
    (if decide (y = intra_trace_eid_succ 0 itrs)
    then
      ∃ xev, build_pre_exec init itrs !! x = Some xev ∧
        is_mem_write xev ∧ is_mem_write ev ∧ get_pa xev = get_pa ev
    else P).
Proof.
  tcclean.
  destruct ev as [[] ?].
  all: eapply seq_state_to_partial_cd_state_destruct; try done.
  all: unfold reg_read_upd_partial_cd_state, reg_write_upd_partial_cd_state,
    mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state.
  all: cdestruct y, H |- *** #CDestrMatch.
  all: destruct fcall; try done.
  unfold set in *. *)

Definition seq_st_mem_map_consistentP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  ∀ pa v,
      seq_st.(mem) !! pa = Some v
    ↔ ∃ ev eid offset,
        cd !! eid = Some ev ∧
        is_mem_writeP
          (λ size wr, pa_addN wr.(WriteReq.pa) offset = pa
            ∧ (offset < size)%N
            ∧ bv_get_byte 8 offset wr.(WriteReq.value) = v) ev ∧
        (∀ eid' ev', cd !! eid' = Some ev' →
          is_mem_writeP (λ size wr, pa_in_range wr.(WriteReq.pa) size pa) ev' →
          EID.full_po_lt eid' eid ∨ eid' = eid).

Definition mem_writes_succeedP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  let evs := Candidate.event_list cd in
  ∀ ev ∈ evs.*2, is_mem_write_req ev →
  is_mem_write_reqP (λ _ _ ret, if ret is inl b then b = true else False) ev.

Definition pcdst_mem_map_invP seq_st :=
  let pcdst := (seq_state_to_partial_cd_state seq_st) in
  let cd := (seq_state_to_cd seq_st) in
  ∀ eid pa, pcdst.(pa_write_map) !! pa = Some eid ↔
    ∃ ev, cd !! eid = Some ev ∧ is_mem_write ev ∧ get_pa ev = Some pa
      ∧ (∀ eid' ev', cd !! eid' = Some ev' → is_mem_write ev' →
        get_pa ev' = Some pa →
        eid' = eid ∨ EID.full_po_lt eid' eid).

Definition pcdst_mem_set_map_invP seq_st :=
  let pcdst := (seq_state_to_partial_cd_state seq_st) in
  let cd := (seq_state_to_cd seq_st) in
  ∀ eid pa,
    (if pcdst.(pa_writes_set_map) !! pa is Some prev_weids
    then eid ∈ prev_weids
    else False) ↔
    ∃ ev, cd !! eid = Some ev ∧ is_mem_write ev ∧ get_pa ev = Some pa.

Lemma pcdst_mem_map_inv_seq_state_equal s1 s2 :
  itrs s1 = itrs s2 →
  pcdst_mem_map_invP s1 = pcdst_mem_map_invP s2.
Proof. unfold pcdst_mem_map_invP. by intros ->. Qed.

Lemma seq_state_trace_cons_equal s1 s2 ev :
  itrs s1 = itrs s2 →
  (set itrs (trace_cons ev) s1).(itrs) = (set itrs (trace_cons ev) s2).(itrs).
Proof. destruct s1, s2. cbn. by intros ->. Qed.

Definition cdst_co_acc_invP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  let co := co_acc (seq_state_to_partial_cd_state seq_st) in
  ∀ eid1 eid2, (eid1, eid2) ∈ co ↔
  ∃ ev1 ev2, cd !! eid1 = Some ev1 ∧ cd !! eid2 = Some ev2 ∧
    is_mem_write ev1 ∧ is_mem_write ev2 ∧ get_pa ev1 = get_pa ev2 ∧
    EID.full_po_lt eid1 eid2.

Definition cdst_rf_acc_invP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  let rf := rf_acc (seq_state_to_partial_cd_state seq_st) in
  ∀ eid1 eid2, (eid1, eid2) ∈ rf ↔
  ∃ ev1 ev2, cd !! eid1 = Some ev1 ∧ cd !! eid2 = Some ev2 ∧
    is_mem_write ev1 ∧ is_mem_read ev2 ∧ get_pa ev1 = get_pa ev2 ∧
    (* get_mem_value ev1 = get_mem_value ev2 ∧ *) EID.full_po_lt eid1 eid2 ∧
    ∀ other_eid ev', cd !! other_eid = Some ev' → is_mem_write ev' →
      get_pa ev' = get_pa ev2 →
      EID.full_po_lt other_eid eid1 ∨ other_eid = eid1 ∨ EID.full_po_lt eid2 other_eid.

Definition cdst_mem_reads_invP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  let rf := rf_acc (seq_state_to_partial_cd_state seq_st) in
  ∀ reid rev rpa rvalue rsize, cd !! reid = Some rev →
    is_mem_read rev → get_pa rev = Some rpa → get_mem_value rev = Some rvalue →
    get_size rev = Some rsize →
    (∃ weid, (weid, reid) ∈ rf) ∨
      (¬ ∃ weid, (weid, reid) ∈ rf)
      ∧ bv_to_bvn (memoryMap_read seq_st.(initSt).(MState.memory) rpa rsize) = rvalue.

Definition pcdst_reg_map_invP seq_st :=
  let pcdst := (seq_state_to_partial_cd_state seq_st) in
  let cd := (seq_state_to_cd seq_st) in
  ∀ eid reg, pcdst.(reg_write_map) !! reg = Some eid ↔
  ∃ ev, is_reg_writeP (λ reg' _ _, reg' = reg) ev ∧ cd !! eid = Some ev ∧
    (∀ eid' ev', cd !! eid' = Some ev' →
      is_reg_writeP (λ reg' _ _, reg' = reg) ev' →
      eid' = eid ∨ EID.full_po_lt eid' eid).

Record seq_inv_predicate (seq_st : seq_state) := {
  pcdst := (seq_state_to_partial_cd_state seq_st);
  cd := (seq_state_to_cd seq_st);
  evs := Candidate.event_list cd;
  seq_st_mem_map_consistent : seq_st_mem_map_consistentP seq_st;
  mem_writes_succeed : mem_writes_succeedP seq_st;
  pcdst_mem_map_inv : pcdst_mem_map_invP seq_st;
  pcdst_mem_set_map_inv : pcdst_mem_set_map_invP seq_st;
  pcdst_reg_map_inv : pcdst_reg_map_invP seq_st;
  cdst_co_acc_inv : cdst_co_acc_invP seq_st;
  cdst_rf_acc_inv : cdst_rf_acc_invP seq_st;
  cdst_mem_reads_inv : cdst_mem_reads_invP seq_st;
  cd_from_seq_state_monotone : cd_monotone cd;
  cd_wf : Candidate.wf cd;
  cd_from_seq_state_consistent : consistent regs_whitelist cd
}.

Lemma and_or_dist P Q R :
  P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R).
Proof. naive_solver. Qed.

Lemma exists_or_dist {T} (P Q : T → Prop) :
  (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x).
Proof. naive_solver. Qed.

Lemma intra_trace_eid_succ_components_equal eid tid tr :
  eid.(EID.tid) = tid →
  eid.(EID.iid) = (intra_trace_eid_succ tid tr).(EID.iid) →
  eid.(EID.ieid) = (intra_trace_eid_succ tid tr).(EID.ieid) →
  eid.(EID.byte) = None →
  eid = intra_trace_eid_succ tid tr.
Proof.
  destruct eid, (intra_trace_eid_succ tid tr) eqn: ?.
  unfold intra_trace_eid_succ, unsnoc_total in *.
  destruct (decide (tr = [])) as [->|].
  2: opose proof (exists_last _) as [? [ltr]]; eauto.
  all: cdestruct Heqt |- *** #CDestrSplitGoal.
  all: try scongruence.
  all: subst.
  all: rewrite unsnoc_snoc in *.
  all: destruct ltr.
  all: cdestruct Heqt |- ***.
Qed.

Lemma reg_read_upd_pcdst_pa_w_map_equal reg eid pcdst :
  pa_write_map (reg_read_upd_partial_cd_state reg eid pcdst) = pcdst.(pa_write_map).
Proof. unfold reg_read_upd_partial_cd_state. cdestruct |- *** #CDestrMatch. Qed.

Lemma reg_write_upd_pcdst_pa_w_map_equal reg eid pcdst :
  pa_write_map (reg_write_upd_partial_cd_state reg eid pcdst) = pcdst.(pa_write_map).
Proof. unfold reg_write_upd_partial_cd_state. cdestruct |- *** #CDestrMatch. Qed.

Lemma mem_read_upd_pcdst_pa_w_map_equal pa eid pcdst :
  pa_write_map (mem_read_upd_partial_cd_state pa eid pcdst) = pcdst.(pa_write_map).
Proof. unfold mem_read_upd_partial_cd_state. cdestruct |- *** #CDestrMatch. Qed.

Lemma mem_write_upd_pcdst_pa_w_map_rewrite pa eid pcdst :
  pa_write_map (mem_write_upd_partial_cd_state pa eid pcdst) = setv (.!! pa) (Some eid) pcdst.(pa_write_map).
Proof. unfold mem_write_upd_partial_cd_state. cdestruct |- *** #CDestrMatch. Qed.

Lemma reg_read_upd_pcdst_co_acc_equal reg eid pcdst :
  co_acc (reg_read_upd_partial_cd_state reg eid pcdst) = pcdst.(co_acc).
Proof. unfold reg_read_upd_partial_cd_state. cdestruct |- *** #CDestrMatch. Qed.

Lemma mem_read_upd_pcdst_co_acc_equal reg eid pcdst :
  co_acc (mem_read_upd_partial_cd_state reg eid pcdst) = pcdst.(co_acc).
Proof. unfold mem_read_upd_partial_cd_state. cdestruct |- *** #CDestrMatch. Qed.

Lemma if_distribution_option `(f : A → B) `(o : option C) (g : C → A) a :
  f (if o is Some c then g c else a) = (if o is Some c then f (g c) else f a).
Proof. by destruct o. Qed.

Lemma if_indiscriminate_cases_option {B} `(x : option A) (y z : B) :
  y = z → (if x is Some c then y else z) = y.
Proof. by destruct x. Qed.

#[local] Instance cdestruct_full_po_lt_eid_succ_False b eid eid' itrs ev :
  TCFastDone (eid = intra_trace_eid_succ 0 itrs) →
  TCFastDone (itrs !! eid' = Some ev) →
  CDestrSimpl b (EID.full_po_lt eid eid') False.
Proof.
  tcclean.
  opose proof (eid_full_po_lt_intra_trace_eid_succ _ _ _); eauto.
  cdestruct eid, eid' |- *** #CDestrSplitGoal.
Qed.

#[local] Instance cdestruct_full_po_lt_eid_succ_True b eid eid' itrs ev :
  TCFastDone (eid = intra_trace_eid_succ 0 itrs) →
  TCFastDone (itrs !! eid' = Some ev) →
  CDestrSimpl b (EID.full_po_lt eid' eid) True.
Proof.
  tcclean.
  opose proof (eid_full_po_lt_intra_trace_eid_succ _ _ _); eauto.
  cdestruct eid, eid' |- *** #CDestrSplitGoal.
Qed.

Lemma seq_model_seq_st_mem_map_consistent_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate seq_st_mem_map_consistentP.
Proof.
  unfold seq_model_outcome_invariant_preserved, seq_st_mem_map_consistentP.
  setoid_rewrite lookup_unfold.
  cbn.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ pa v.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  rewrite Hsame_itrs in *.
  eapply seq_st_mem_map_consistent in H_inv.
  specialize (H_inv pa v).
  setoid_rewrite lookup_unfold in H_inv.
  destruct (decide (is_mem_write (call &→ ret))).
  - destruct call; unfold is_mem_writeP in *; try done.
    cdestruct ret, H_seqst_succ.
    destruct (decide (pa_in_range (WriteReq.pa wr) n pa)).
    + opose proof (pa_in_range_write _ _ _ _ _ _ _ _) as [offest (? & ? & ->)]; eauto.
      cdestruct seqst_succ |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrSplitGoal #CDestrMatch #CDestrEqOpt.
      * eexists _, (intra_trace_eid_succ 0 (trace_rev (itrs seqst))), _.
        rewrite lookup_unfold.
        cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
          #CDestrSplitGoal #CDestrEqOpt #CDestrMatch; eauto.
        left.
        by eapply eid_full_po_lt_intra_trace_eid_succ.
      * exfalso.
        ospecialize (H9 (intra_trace_eid_succ 0 (trace_rev (itrs seqst))) _ _ _).
        (* Set Typeclasses Debug Verbosity 2.
        1: cdestruct |- *** #CDestrEqOpt.
        (* TODO: ask Thibaut (search for hd in debug) *)
        *)
        1: rewrite lookup_unfold; done.
        1: cbn; eapply pa_in_range_spec; eauto.
        cdestruct x0, H9 #CDestrSplitGoal #CDestrEqOpt.
      * clear H_inv H8 p.
        cdestruct pa, v.
        admit.
    + erewrite pa_not_in_range_write; eauto.
      2: erewrite length_bv_to_bytes, div_round_up_divisible; done.
      all: setoid_rewrite H_inv.
      all: cdestruct |- *** as size wr' b eid offset Htr H_wb H_otherw #CDestrSplitGoal.
      all: cdestruct Htr, H_wb |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
      3: exfalso; eapply n0, pa_in_range_spec; depelim H4;
        eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      all: eexists _, eid, _.
      all: cdestruct eid, seqst_succ, b |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
      all: try done.
      all: eapply H_otherw.
      all: try done.
      all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
  - destruct call; try done.
    all: cdestruct ret, seqst, seqst_succ, H_seqst_succ #CDestrMatch.
    6: by unfold is_mem_writeP in *.
    all: cbn.
    all: setoid_rewrite H_inv; clear H_inv.
    all: cdestruct |- *** as size wr eid offset Htr ??? H_otherw ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
    all: eexists _, eid, _.
    all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
    all: try done.
    all: eapply H_otherw.
    all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrMatch.
Admitted.

Lemma seq_model_mem_writes_succeed_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate mem_writes_succeedP.
Proof.
  unfold seq_model_outcome_invariant_preserved, mem_writes_succeedP, sequential_model_outcome_logged, fHandler_logger, build_pre_exec.
  cdestruct |- *** as seqst H_inv call seqst_succ ret H_seqst_succ n wr wret eid H_eid.
  rewrite lookup_unfold in *.
  eapply mem_writes_succeed in H_inv.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  rewrite Hsame_itrs in *.
  cbn in *.
  cdestruct H_eid ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch #CDestrEqOpt.
  2: cdestruct call, ret; scongruence.
  ospecialize (H_inv (MemWrite n wr &→ wret) _ _).
  { cdestruct |- ***. eexists (eid, _). cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal. }
  all: naive_solver.
Qed.

Lemma mem_writes_succeedP_cons call ret st :
  mem_writes_succeedP (set itrs (trace_cons (call &→ ret)) st) →
  mem_writes_succeedP st ∧
  match call &→ ret with
  | MemWrite _ _ &→ inl true => True
  | MemWrite _ _ &→ _ => False
  | _ => True
  end.
Proof.
  cdestruct |- *** #CDestrSplitGoal.
  - destruct call.
    all: cdestruct |- *** as ev Hev Hevmem.
    all: ospecialize (H ev _ _); [|hauto l: on|hauto l: on].
    all: cdestruct Hev |- *** as eid Heid #CDestrEqOpt.
    all: eexists (eid,ev); cbn; split; eauto.
    all: cdestruct Heid |- *** #CDestrEqOpt.
    all: rewrite <- trace_snoc_rev_cons in *.
    all: cdestruct Heid |- ***  ##eq_some_unfold_lookup_eid_trace_snoc #CDestrMatch #CDestrEqOpt.
    all: hauto lq: on.
  - destruct call; try done.
    ospecialize (H (MemWrite n wr &→ ret) _ _).
    2,3: hauto l: on.
    cdestruct |- ***.
    eexists (intra_trace_eid_succ 0 (trace_rev st.(itrs)), _).
    cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
Qed.

Lemma seq_model_pcdst_mem_map_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate pcdst_mem_map_invP.
Proof.
  unfold seq_model_outcome_invariant_preserved.
  cdestruct as seq_st H_inv call ret seqst_succ H_seqst_succ.
  pose (Candidate.event_list (seq_state_to_cd seq_st)) as evs.
  opose proof (seq_model_mem_writes_succeed_inv _ _ _ _ _ _) as Hmem_w_succeed; eauto.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  erewrite pcdst_mem_map_inv_seq_state_equal;
  last by eapply seq_state_trace_cons_equal.
  opose proof (pcdst_mem_map_inv _ H_inv) as H_base.
  unfold pcdst_mem_map_invP in *.
  cbn.
  setoid_rewrite lookup_unfold.
  setoid_rewrite lookup_unfold in H_base.
  intros eid pa.
  specialize (H_base eid pa).
  destruct (decide (is_mem_write (call &→ ret))).
  - eapply seq_state_to_partial_cd_state_destruct.
    all: cdestruct call |- *** as.
    1: by unfold is_mem_writeP in *.
    setoid_rewrite lookup_unfold.
    cdestruct pa, eid |- *** #CDestrMatch.
    2: {
      setoid_rewrite H_base.
      cdestruct |- *** as ??? ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      1,2: intros ?.
      all: intros H_latest.
      all: try (exfalso; done).
      all: eexists.
      all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: try (exfalso; done).
      all: try eapply H_latest.
      all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: hauto lq: on rew: off.
    }
    clear H_base.
    cdestruct eid |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    + eexists.
      cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: rewrite lookup_total_unfold in *.
      all: rewrite ?lookup_unfold in *.
      2: naive_solver.
      1: right; by eapply eid_full_po_lt_intra_trace_eid_succ.
    + exfalso.
      ospecialize (H5 (intra_trace_eid_succ 0 (trace_rev (itrs seq_st))) _ _ _ _).
      1: by rewrite lookup_unfold.
      1,2: done.
      cdestruct eid, H5 |- *** #CDestrSplitGoal #CDestrEqOpt.
  - eapply seq_state_to_partial_cd_state_destruct.
    5: unfold is_mem_writeP in *; deintros; by cdestruct |- ***.
    all: cdestruct |- *** #CDestrEqOpt.
    all: try setoid_rewrite lookup_total_unfold.
    all: try rewrite lookup_unfold.
    all: setoid_rewrite H_base; clear H_base.
    all: cdestruct |- *** as ???? H_latest ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
    all: try solve [unfold is_mem_writeP in *; by cdestruct call].
    all: eexists.
    all: cdestruct eid, call, ret |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
    all: try (exfalso; done).
    all: try eapply H_latest.
    all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
Qed.

Lemma seq_model_pcdst_mem_set_map_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate pcdst_mem_set_map_invP.
Proof using regs_whitelist.
  unfold seq_model_outcome_invariant_preserved, pcdst_mem_set_map_invP.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ eid pa
    #CDestrEqOpt.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ _) as ->; eauto.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _ _) as ->; eauto.
  opose proof (pcdst_mem_set_map_inv _ H_inv eid pa) as H_base.
  cdestruct H_base |- *** #CDestrEqOpt.
  setoid_rewrite lookup_unfold.
  setoid_rewrite lookup_unfold in H_base.
  destruct (decide (is_mem_write (call &→ ret))).
  - eapply seq_state_to_partial_cd_state_destruct.
    all: cdestruct call |- ***.
    1: by unfold is_mem_writeP in *.
    rewrite lookup_total_unfold.
    destruct H_base as [H_base1 H_base2].
    cdestruct eid |- *** ##eq_some_unfold_cdst_memw_upd_pa_ws_set_map
      ##eq_none_unfold_cdst_memw_upd_pa_ws_set_map
      ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    all: try (ospecialize (H_base1 _); first done; cdestruct H_base1).
    all: try done.
    all: try solve [left+right; done].
    all: try solve [eexists; cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrSplitGoal #CDestrMatch; naive_solver].
    1: right.
    3: exfalso.
    all: eapply H_base2; eexists; cdestruct |- *** #CDestrSplitGoal;
      unfold is_mem_writeP in *; naive_solver.
  - eapply seq_state_to_partial_cd_state_destruct.
    all: unfold is_mem_writeP in *.
    all: cdestruct call |- *** #CDestrEqOpt.
    5: done.
    all: rewrite ?lookup_total_unfold.
    all: rewrite ?lookup_unfold.
    all: setoid_rewrite H_base.
    all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    all: eexists.
    all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    all: hauto lq: on.
Qed.

Lemma seq_model_co_acc_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate cdst_co_acc_invP.
Proof using regs_whitelist.
  unfold seq_model_outcome_invariant_preserved, cdst_co_acc_invP.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ eid1 eid2.
  setoid_rewrite lookup_unfold.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ _) as ->; eauto.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _ _) as ->; eauto.
  opose proof (cdst_co_acc_inv _ H_inv eid1 eid2) as H_base.
  setoid_rewrite lookup_unfold in H_base.
  destruct (decide (is_mem_write (call &→ ret) ∧
    eid2 = intra_trace_eid_succ 0 (trace_rev (itrs seqst)))) as [|H_call].
  - eapply seq_state_to_partial_cd_state_destruct.
    all: cdestruct call |- *** as.
    1: by unfold is_mem_writeP in *.
    cdestruct eid2 |- *** as size wr _ ???.
    opose proof (pcdst_mem_set_map_inv _ H_inv eid1 (WriteReq.pa wr)) as H_mem_set.
    setoid_rewrite lookup_unfold in H_mem_set.
    set_unfold.
    cdestruct |- *** as H_base #CDestrMatch.
    2: {
      intros H_set_None.
      rewrite H_set_None in H_mem_set.
      setoid_rewrite H_base; clear H_base.
      all: cdestruct eid1 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: exfalso.
      all: eapply H_mem_set.
      all: unshelve eexists.
      all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    }
    setoid_rewrite H_base; clear H_base.
    cdestruct |- *** as ? H_paws ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: rewrite H_paws in *.
    all: setoid_rewrite H_mem_set; clear H_mem_set.
    all: cdestruct |- *** #CDestrSplitGoal.
    all: try left.
    all: deintros; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
    all: eexists; eauto.
    1: eexists.
    all: deintros; cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
  - eapply seq_state_to_partial_cd_state_destruct.
    all: unfold is_mem_writeP in *.
    all: cdestruct call |- *** #CDestrEqOpt.
    5: cdestruct H_call #CDestrSplitGoal; first done.
    all: set_unfold.
    5: cdestruct |- *** #CDestrMatch.
    all: setoid_rewrite H_base.
    all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: try right.
    all: eexists _, _.
    all: cdestruct eid1, eid2 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
Qed.

Lemma seq_model_rf_acc_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate cdst_rf_acc_invP.
Proof using regs_whitelist.
  unfold seq_model_outcome_invariant_preserved, cdst_rf_acc_invP.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ eid1 eid2.
  setoid_rewrite lookup_unfold.
  opose proof (seq_model_pcdst_mem_map_inv _ _ _ _ _ _) as H_mem_map; try done; cbn in H_mem_map.
  unfold pcdst_mem_map_invP in *.
  setoid_rewrite lookup_unfold in H_mem_map.
  cbn in H_mem_map.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ _) as H_same_itrs; eauto.
  setoid_rewrite H_same_itrs in H_mem_map; rewrite H_same_itrs; clear H_same_itrs.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _ _) as ->; eauto.
  opose proof (cdst_rf_acc_inv _ H_inv eid1 eid2) as H_base.
  setoid_rewrite lookup_unfold in H_base.
  destruct (decide (is_mem_read (call &→ ret) ∧
    eid2 = intra_trace_eid_succ 0 (trace_rev (itrs seqst)))) as [|H_call].
  - eapply seq_state_to_partial_cd_state_destruct.
    all: cdestruct call |- *** as.
    1: by unfold is_mem_readP in *.
    cdestruct eid2 |- *** as size wr val ? _ H_step ???.
    set_unfold.
    cdestruct |- *** #CDestrMatch #CDestrEqOpt.
    2: {
      opose proof (pcdst_mem_map_inv _ H_inv).
      cdestruct H_step |- *** #CDestrMatch #CDestrEqOpt.
      setoid_rewrite H_base; clear H_base.
      cdestruct eid1, H1 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: exfalso.
      all: eapply eq_None_not_Some; first eapply H.
      all: eexists.
      all: eapply H0.
      all: setoid_rewrite lookup_unfold.
      all: eexists.
      all: erewrite lookup_partial_cd_state_to_cd; unfold build_pre_exec;
        erewrite lookup_pe_to_lookup_trace; cbn.
      all: cdestruct eid1 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch; eauto.
      all: cdestruct |- ***.
      1: ospecialize (H8 eid' _ _ _ _).
      all: try ospecialize (H8 eid' _ _ _ _).
      all: cdestruct eid1 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: eauto.
    }
    opose proof (pcdst_mem_map_inv _ H_inv) as H_mem_base.
    eapply H_mem_base in H.
    setoid_rewrite lookup_unfold in H.
    setoid_rewrite H_base.
    cdestruct H, eid1 |- *** as ???? H_fullpo ? #CDestrSplitGoal #CDestrEqOpt.
    2: {
      cdestruct |- *** as ?????? H_fullpo2.
      left; split; last done.
      ospecialize (H_fullpo eid1 _ _ _ _);
      last ospecialize (H_fullpo2 t _ _ _ _).
      all: cdestruct eid1 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    }
    all: setoid_rewrite lookup_unfold.
    1: eexists _, _.
    all: deintros; cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: ospecialize (H_fullpo _ _ _ _ _); eauto.
    all: cdestruct |- ***.
    all: cdestruct H_fullpo |- *** #CDestrSplitGoal.
    all: left+(right;left)+(right;right); done.
  - eapply seq_state_to_partial_cd_state_destruct.
    all: cdestruct call |- ***.
    4: cdestruct ret, H_call #CDestrSplitGoal.
    4: by unfold is_mem_readP in *.
    all: set_unfold.
    all: cdestruct |- *** as #CDestrMatch.
    all: setoid_rewrite H_base; clear H_base.
    all: cdestruct eid1, eid2 |- *** as #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: try cdestruct H0, H1 #CDestrMatch.
    all: try intros ??????????? Hl1 Hl2 ?? H_rf_fullpo.
    all: try intros ?????????? Hl1 Hl2 ?? H_rf_fullpo.
    all: try intros ????????? Hl1 Hl2 ?? H_rf_fullpo.
    all: try intros ???????? Hl1 Hl2 ?? H_rf_fullpo.
    all: try right.
    all: eexists _, _.
    all: cdestruct Hl1, Hl2 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: try solve [eapply H_rf_fullpo; eauto; cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch; try done].
    all: try do 2 right.
    all: try (eapply eid_full_po_lt_intra_trace_eid_succ; done).
    all: cdestruct eid1, eid2.
    all: try cdestruct call; unfold is_mem_writeP, is_mem_readP in *; try done.
    all: opose proof (eid_full_po_lt_intra_trace_eid_succ _ _ _); eauto.
    all: deintros; cdestruct |- ***.
Qed.

Lemma seq_model_mem_reads_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate cdst_mem_reads_invP.
Proof.
  unfold seq_model_outcome_invariant_preserved, cdst_co_acc_invP.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ eid ev rpa rval.
  setoid_rewrite lookup_unfold.
  cdestruct ev, rpa, rval |- *** as size rr val b H_tr_lu.
  opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _) as H_rf; eauto; cbn in *.
  opose proof (cdst_rf_acc_inv _ H_inv) as H_rfb.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ _) as H_same_itrs; eauto.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _ _) as ->; eauto.
  rewrite H_same_itrs in *.
  cdestruct H_tr_lu ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrMatch.
  - unfold not.
    opose proof (cdst_mem_reads_inv _ H_inv eid _ _ _ _ _ _ _ _ _) as H_base;
    cdestruct |- *** #CDestrEqOpt.
    cdestruct H_base #CDestrSplitGoal; [left|right].
    + eapply H_rfb in H0; cdestruct H0 #CDestrEqOpt.
      eexists x; rewrite <- H_same_itrs in *; apply H_rf.
      eexists _, _; cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      1: eapply H3; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      all: right; right; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    + cdestruct |- *** #CDestrSplitGoal.
      rewrite <- H_same_itrs in H2.
      eapply H_rf in H2; rewrite <- H_same_itrs in *; cdestruct H, H2 |- *** #CDestrEqOpt
        ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
      eapply H0;
      eexists x.
      rewrite H_same_itrs in *.
      apply H_rfb;
      eexists _, _; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
      eapply H5; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
  - cdestruct val, b, eid, call, ret |- *** #CDestrMatch.
    + admit.
    + unfold read_mem_seq_state, memoryMap_read, read_byte_seq_state, read_byte_seq_state_flag in *.
      admit.
Admitted.

Lemma seq_model_pcdst_reg_map_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st,
      let pcdst := (seq_state_to_partial_cd_state seq_st) in
      let cd := (seq_state_to_cd seq_st) in
      let evs := Candidate.event_list cd in
      pcdst_reg_map_invP seq_st).
Proof.
Admitted.

#[local] Instance Incompatible_eid_lookup_byte_Some (itr : list (iTrace ())) eid ev l :
  Incompatible (itr !! eid = Some ev) (eid.(EID.byte) = Some l).
Proof.
  tcclean.
  unfold lookup, lookup_ev_from_iTraces.
  cdestruct |- *** #CDestrEqOpt.
Qed.

Lemma seq_model_pcdst_montonone :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st, cd_monotone (seq_state_to_cd seq_st)).
Proof using regs_whitelist.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _ H_seqst_succ) as Hsame_init.
  cbn.
  rewrite ?Hsame_init, ?Hsame_itrs in *.
  opose proof (cd_from_seq_state_monotone _ H_inv); destruct H; deintros;
  cdestruct |- ***.
  eapply seq_state_to_partial_cd_state_destruct.
  - cdestruct |- ***; repeat apply conj; set_unfold; done.
  - cdestruct |- ***; repeat apply conj; unfold rel_strictly_monotone in *; set_unfold;
    cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
    1: ospecialize (H (_,_) _); eauto.
    {
      eapply eid_full_po_lt_intra_trace_eid_succ.
      eapply (pcdst_reg_map_inv _ H_inv) in H3.
      cdestruct H3 #CDestrEqOpt.
      eexists; cdestruct t |- *** #CDestrEqOpt.
    }
    1,2: ospecialize (H0 (_,_) _); eauto.
    1: ospecialize (H1 (_,_) _); eauto.
  - cdestruct |- ***; repeat apply conj; set_unfold; done.
  - cdestruct |- ***; repeat apply conj; unfold rel_strictly_monotone in *; set_unfold;
    cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
    {
      eapply eid_full_po_lt_intra_trace_eid_succ.
      apply (pcdst_mem_map_inv _ H_inv) in H3.
      cdestruct H3 #CDestrEqOpt.
      eexists; cdestruct t |- *** #CDestrEqOpt.
    }
    1,2: ospecialize (H (_,_) _); eauto.
    1: ospecialize (H0 (_,_) _); eauto.
    1: ospecialize (H1 (_,_) _); eauto.
  - cdestruct |- ***; repeat apply conj; unfold rel_strictly_monotone in *;
    cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
    1: ospecialize (H (_,_) _); eauto.
    1: ospecialize (H0 (_,_) _); eauto.
    {
      set_unfold.
      eapply eid_full_po_lt_intra_trace_eid_succ.
      opose proof (pcdst_mem_set_map_inv _ H_inv t (WriteReq.pa wr)).
      cdestruct H5 |- *** #CDestrMatch #CDestrEqOpt.
      eapply H5 in H4.
      cdestruct H4 #CDestrEqOpt.
      eexists; cdestruct |- *** #CDestrEqOpt.
    }
    1,2: ospecialize (H1 (_,_) _); eauto.
Qed.

Lemma seq_model_pcdst_consistent :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st, consistent regs_whitelist (seq_state_to_cd seq_st)).
Proof.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ.
  opose proof (seq_model_pcdst_montonone _ H_inv _ _ seqst_succ _) as H_mono;
  first (cdestruct |- ***; eauto).
  cbn in *.
  unfold sequential_model_outcome_logged, fHandler_logger in *.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _ H_seqst_succ) as Hsame_init.
  rewrite Hsame_init, Hsame_itrs in *.
  constructor.
  - eapply rel_monotone_acyclic.
    repeat rewrite <- rel_montone_union.
    unfold cd_monotone in *.
    cdestruct H_mono |- *** #CDestrSplitGoal.
    {
      unfold Candidate.full_instruction_order, Candidate.instruction_order, Candidate.iio, rel_strictly_monotone, EID.full_po_lt, EID.po_lt, EID.iio_lt, Candidate.same_thread, Candidate.same_instruction_instance.
      cdestruct |- *** #CDestrSplitGoal.
      2: lia.
      rewrite ?lookup_unfold in *.
      rewrite ?lookup_unfold in H3.
      cdestruct H3, H4 |- *** #CDestrMatch.
      all: lia.
    }
    {
      assert (Candidate.is_nms ((build_pre_exec (initSt seqst) (trace_cons (call &→ ret) (itrs seqst))))) as Hnms by admit.
      unfold GenAxiomaticArm.AxArmNames.fr.
      eapply rel_strictly_monotone_seq2; split.
      1: eapply grel_from_set_montone.
      unfold Candidate.from_reads.
      eapply rel_monotone_difference.
      cdestruct |- ***.
      unfold Candidate.mem_reads, Candidate.mem_writes in *.
      set_unfold.
      cdestruct H2, H6.
      ospecialize (Hnms (x,y) _); first (set_unfold; cdestruct |- *** #CDestrSplitGoal).
      unfold Candidate.same_footprint, Candidate.same_pa, Candidate.same_size in Hnms.
      set_unfold in Hnms.
      rewrite H2, H6 in *.
      cdestruct x, y, Hnms.
      rewrite lookup_unfold in *.
      rewrite lookup_unfold in H2.
      opose proof (EID.full_po_lt_connex x y) as Hconnex.
      cdestruct x, y, H2, H6 #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      all: ospecialize (Hconnex _ _ _); try solve [by rewrite ?intra_trace_eid_succ_tid, ?intra_trace_eid_succ_byte in *]; try lia.
      all: rewrite ?intra_trace_eid_succ_tid, ?intra_trace_eid_succ_byte.
      all: try solve [unfold lookup, lookup_ev_from_iTraces in *; try destruct x; try destruct y;
        cdestruct H2, H6 #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; cbn; by subst].
      all: cdestruct Hconnex #CDestrSplitGoal; subst.
      1: rewrite H2 in *; hauto lq: on rew: off.
      all: try by left.
      all: rewrite lookup_unfold in * |- ; try done.
      all: right.
      all: opose proof (seq_model_co_acc_inv _ H_inv _ _ _ _ y) as H_co; eauto; cbn in *.
      all: setoid_rewrite lookup_unfold in H_co.
      all: rewrite Hsame_itrs in H_co.
      all: setoid_rewrite H_co.
      {
        opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _) as H_rf; eauto; cbn in *.
        unfold cdst_rf_acc_invP in *.
        setoid_rewrite lookup_unfold in H_rf; cbn in *.
        rewrite ?Hsame_itrs, ?Hsame_init in *.
        (* setoid_rewrite H_rf. *)
        clear (* H_rf *) H_co.
        opose proof (seq_model_mem_reads_inv _ H_inv _ _ _ _ x _ _ _ _ _ _ _ _ _) as H_mem_reads; eauto.
        all: cdestruct H2 |- *** #CDestrEqOpt; rewrite ?Hsame_itrs in *;
          cdestruct |- *** #CDestrEqOpt.
        cbn in *.
        rewrite Hsame_itrs, Hsame_init in *.
        cdestruct H_mem_reads #CDestrSplitGoal.
        {
          eexists; split; eauto.
          destruct (decide (y = x0)) as [->|].
          1: right; cdestruct |- *** #CDestrSplitGoal; eexists; cdestruct |- ***
            ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrSplitGoal.
          eapply H_rf in H8.
          cdestruct H8 #CDestrEqOpt #CDestrMatch.
          left.
          eexists _, _.
          cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
          ospecialize (H12 y _ _ _ _).
          all: cdestruct H12 |- *** #CDestrEqOpt #CDestrSplitGoal.
        }
        {
          exfalso.
          eapply H8.
          setoid_rewrite H_rf.
          opose proof (trace_last_event_indexed
          (λ eid ev1,
            is_mem_write ev1 ∧
            get_pa ev1 = get_pa (MemRead x1 x2 &→ inl (x3, x4)) ∧
            EID.full_po_lt eid x) (trace_rev (trace_cons (call &→ ret) (itrs seqst))) y _ _ _).
          1: cdestruct |- *** #CDestrEqOpt.
          1: cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
          cdestruct H11 #CDestrEqOpt.
          eexists _, _ , _; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
          opose proof (EID.full_po_lt_connex x other_eid _ _ _) as Hconnex.
          1-3: destruct x, other_eid; unfold lookup, lookup_ev_from_iTraces in *;
            deintros; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
          destruct Hconnex as [->|[|]].
          1: deintros; cdestruct |- *** #CDestrEqOpt.
          1: by do 2 right.
          ospecialize (H14 other_eid _ _ _); eauto.
          1: eexists; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt; eauto.
          destruct H14; first by left.
          right; left; done.
        }
      }
    }
    1,2: unfold partial_cd_state_to_cd, GenAxiomaticArm.AxArmNames.co, GenAxiomaticArm.AxArmNames.rf; cbn.
    1: eapply rel_montone_intersection1.
    1: eapply rel_strictly_monotone_seq1; split.
    1: eapply rel_strictly_monotone_seq2; split.
    2: assumption.
    1,2: eapply grel_from_set_montone.
    1: eapply  rel_strictly_monotone_seq1; split.
    1: assumption.
    1: eapply grel_from_set_montone.
    unfold Candidate.reg_from_reads.
    eapply rel_monotone_difference.
    unfold Candidate.reg_reads, Candidate.same_reg, Candidate.reg_writes,
      Candidate.reg_reads_from, Candidate.instruction_order, Candidate.same_thread.
    set_unfold.
    cdestruct |- *** as x y ???????? #CDestrEqOpt.
    opose proof (EID.full_po_lt_connex x y _ _ _) as Hfpolt; try fast_done.
    1,2: destruct x as [???[]], y as [???[]]; deintros; cdestruct |- ***.
    cdestruct x, y, Hfpolt #CDestrSplitGoal #CDestrEqOpt.
    1: by left.
    right.
    1: admit. (* reg from reads *)
  - unfold GenAxiomaticArm.AxArmNames.coe, GenAxiomaticArm.AxArmNames.coi, GenAxiomaticArm.AxArmNames.co.
    set_unfold.
    cdestruct |- ***.
    intros Hsets.
    cdestruct Hsets.
    unfold GenAxiomaticArm.AxArmNames.fre, GenAxiomaticArm.AxArmNames.fri,
      GenAxiomaticArm.AxArmNames.fr in *.
    cdestruct H0 #CDestrSplitGoal.
    eapply H9.
    unfold Candidate.same_thread.
    set_unfold.
    unfold Candidate.explicit_reads, Candidate.explicit_writes,
      Candidate.reads_by_kind, Candidate.writes_by_kind in H0, H1.
    cdestruct H0, H1.
    rewrite lookup_unfold in H0; rewrite lookup_unfold in H10;
      setoid_rewrite lookup_unfold.
    eexists _, _, 0.
    cdestruct |- *** #CDestrSplitGoal; eauto.
    all: destruct t, x; unfold lookup, lookup_ev_from_iTraces in *;
    deintros; cdestruct |- *** #CDestrEqOpt.
  - opose proof (initial_reads _ _ (cd_from_seq_state_consistent _ H_inv)) as H_base.
    opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _) as H_rf; eauto; cbn in *.
    opose proof (cdst_rf_acc_inv _ H_inv) as H_rfb.
    unfold Candidate.ttw_reads, Candidate.ifetch_reads, Candidate.init_mem_reads,
      Candidate.mem_reads, Candidate.reads_by_kind in *.
    set_unfold.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_base.
    rewrite <- Hsame_itrs in *.
    intro.
    destruct (decide (x = intra_trace_eid_succ 0 (trace_rev (itrs seqst_succ)))) as [->|].
    * unfold not.
      cdestruct seqst_succ, call, ret, H_base |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      all: try solve [eexists; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal].
      all: admit. (* bv facts / byte flags -> mem map doesn't include value -> wasn't written to that pa *)
    * unfold not.
      intros Hor.
      ospecialize (H_base x _).
      1: cdestruct Hor #CDestrEqOpt #CDestrSplitGoal; [left|right];
        eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      cdestruct H_base |- *** #CDestrEqOpt #CDestrSplitGoal.
      1: eexists; cdestruct |- ***#CDestrEqOpt #CDestrSplitGoal.
      eapply H0.
      eexists x0.
      rewrite Hsame_itrs.
      eapply H_rfb.
      eapply H_rf in H1;
        cdestruct H1 |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons
          #CDestrMatch.
      rewrite Hsame_itrs in *.
      eexists _, _;  cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eapply H4; cdestruct |- *** #CDestrEqOpt.
  - opose proof (register_write_permitted _ _ (cd_from_seq_state_consistent _ H_inv)) as H_base.
    unfold Illegal_RW in *.
    set_unfold.
    unfold not.
    cdestruct |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
    + eapply (H_base x).
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    + clear H_base.
      destruct call.
      all: unfold is_illegal_reg_write, is_reg_writeP in *; cbn in *; try fast_done.
      cdestruct racc, ret, H, H_seqst_succ #CDestrSplitGoal #CDestrMatch #CDestrEqOpt.
  - opose proof (register_read_permitted _ _ (cd_from_seq_state_consistent _ H_inv)) as H_base.
    unfold Illegal_RR in *.
    set_unfold.
    unfold not.
    cdestruct |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
    + eapply (H_base x).
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    + clear H_base.
      destruct call.
      all: unfold is_illegal_reg_write, is_reg_writeP in *; cbn in *; try fast_done.
      cdestruct racc, ret, H, H_seqst_succ #CDestrSplitGoal #CDestrMatch #CDestrEqOpt.
  - opose proof (memory_events_permitted _ _ (cd_from_seq_state_consistent _ H_inv)) as H_base.
    unfold Candidate.mem_explicit, Candidate.ttw_reads, Candidate.ifetch_reads,
      Candidate.mem_events, Candidate.mem_by_kind, Candidate.reads_by_kind in *.
    set_unfold.
    cdestruct H_base |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrMatch.
    * ospecialize (H_base x _).
      1: eexists; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      cdestruct H_base |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal;
      [left;left|left;right|right]; eexists;
      cdestruct x0 |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
    * clear H_base.
      destruct call; unfold is_mem_event, is_mem_readP, is_mem_writeP in *;
      cdestruct H |- *** #CDestrSplitGoal #CDestrMatch; cdestruct ret #CDestrMatch.
      1,2: cdestruct o.
      1: eapply orb_true_iff in H1; cdestruct H1 |- *** #CDestrSplitGoal; [right|left; right];
        unfold is_mem_read_kindP, is_mem_readP; eexists;
        cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; naive_solver.
      all: left; left.
      all: eexists;
        cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; naive_solver.
  - unfold Candidate.is_nms.
    admit. (* TODO *)
  - opose proof (no_exceptions regs_whitelist _ (cd_from_seq_state_consistent _ H_inv)) as H_base.
    unfold GenAxiomaticArm.AxArmNames.TE, GenAxiomaticArm.AxArmNames.ERET in *.
    set_unfold.
    cdestruct |- *** as eid.
    rewrite lookup_unfold in *.
    specialize (H_base eid).
    unfold not.
    cdestruct H_base |- *** as Hb1 Hb2 #CDestrMatch #CDestrSplitGoal #CDestrEqOpt
      ##eq_some_unfold_lookup_eid_trace_rev_cons; intros.
    all: try solve [eapply Hb1; eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal].
    all: try solve [eapply Hb2; eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal].
    all: cdestruct call, eid.
    destruct call; deintros; cdestruct |- ***.
Admitted.

Lemma bvs_equal_get_byte_equal n (x y : bvn) :
  n ≠ 0%N → bvn_n x = bvn_n y →
  (∀ i, (i * n < bvn_n x)%N →
    bv_get_byte n i x.(bvn_val) = bv_get_byte n i y.(bvn_val)) →
  x = y.
Proof.
  destruct x as [size x], y as [ysize y]; cdestruct ysize, x, y |- *** as x Hn y Hbytes.
  setoid_rewrite <- (@bv_of_bytes_bv_to_bytes n) at 1 2; try fast_done.
  f_equal.
  apply list_eq.
  intros.
  apply option_eq.
  intro b.
  opose proof (@bv_to_bytes_bv_get_byte n (N.of_nat i) size _ b _) as Hg1; first lia.
  opose proof (@bv_to_bytes_bv_get_byte n (N.of_nat i) size _ b _) as Hg2; first lia.
  unfold lookup, list_lookupN in Hg1, Hg2; rewrite Nat2N.id in *.
  setoid_rewrite Hg1; setoid_rewrite Hg2; clear Hg1 Hg2.
  cdestruct |- *** #CDestrSplitGoal.
  all: rewrite Hbytes in *; done.
Qed.

Lemma bv_to_bytes_bv_get_byte2 {n i m} (b : bv m) :
	(0 < n)%N → (i * n < m)%N → bv_to_bytes n b !! i = Some (bv_get_byte n i b).
Proof. intros. eapply bv_to_bytes_bv_get_byte. all: done. Qed.

Lemma bv_to_bytes_bv_of_bytes {m n} (l : list (bv n)) :
  n ≠ 0%N → m = N.of_nat (length l) →
  bv_to_bytes n (bv_of_bytes (n * m) l) = l.
Proof.
  intros ? ->.
  unfold bv_to_bytes, bv_of_bytes.
  rewrite div_round_up_divisible; last done.
  bv_simplify.
  unfold bv_wrap.
  rewrite Z.mod_small.
  2: {
    pose proof (little_endian_to_bv_bound n l).
    unfold bv_modulus.
    rewrite N2Z.inj_mul, nat_N_Z, Z.mul_comm.
    done.
  }
  rewrite bv_to_little_endian_to_bv.
  2: lia.
  done.
Qed.

Lemma Some_inj {A} (x y : A) :
  Some x = Some y ↔ x = y.
Proof. cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal. Qed.

Lemma pa_range_lookup pa size i :
  (i < size)%N →
  pa_range pa size !! i = Some (pa_addN pa i).
Proof.
  intros.
  unfold pa_range.
  setoid_rewrite list_lookup_fmap.
  unfold seqN.
  setoid_rewrite list_lookup_fmap.
  rewrite lookup_seq_lt; last lia.
  cbn.
  do 2 f_equal.
  lia.
Qed.

Lemma seq_model_pcdst_wf :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st, Candidate.wf (seq_state_to_cd seq_st)).
Proof.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _ H_seqst_succ) as Hsame_init.
  constructor.
  - unfold Candidate.has_only_supported_events in *.
    set_unfold.
    apply elem_of_nil_inv.
    unfold not; cdestruct |- *** as tid iid ieid ???%Candidate.iEvent_list_match.
    assert (build_pre_exec (initSt seqst_succ) (trace_cons (call &→ ret) (itrs seqst_succ)) !! EID.make tid iid ieid None = Some i).
    1: unfold lookup, Candidate.lookup_eid_pre; cdestruct H0 |- *** #CDestrEqOpt;
      eexists; cdestruct H0 |- *** #CDestrEqOpt #CDestrSplitGoal.
    clear H0; cdestruct H1 ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrMatch.
    + opose proof (Candidate.has_only_supported_events' _ (cd_wf _ H_inv)) as H_base.
      eapply (filter_nil_not_elem_of _ _ (tid,iid,ieid,i) H_base); first done.
      eapply Candidate.iEvent_list_match.
      unfold lookup, lookup_ev_from_iTraces, Candidate.lookup_iEvent, Candidate.lookup_instruction in *.
      cdestruct H0 |- *** #CDestrEqOpt.
      unfold build_pre_exec in *.
      eexists (_,_).
      cdestruct H0 |- *** #CDestrEqOpt #CDestrSplitGoal; last eauto.
      eexists.
      cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal; last eauto.
      assert (tid < 1) by lia.
      eexists H3; rewrite lookup_total_unfold.
      by f_equal.
    + unfold Candidate.unsupported_event in *.
      destruct i as [[]]; unfold is_mem_read_reqP, is_mem_write_reqP in *; cbn in *;
      try solve [destruct H; fast_done].
      all: deintros; cdestruct |- *** #CDestrMatch; rewrite H0 in *.
      all: sauto.
  - constructor.
    + set_unfold.
      cdestruct |- ***.
      opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _ _ _) as H_rf; eauto; cbn in *.
      eapply H_rf in H; clear H_rf; cdestruct H.
      unfold Candidate.mem_writes; set_unfold.
      rewrite lookup_unfold in H; setoid_rewrite lookup_unfold.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      done.
    + set_unfold.
      cdestruct |- ***.
      opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _ _ _) as H_rf; eauto; cbn in *.
      eapply H_rf in H; clear H_rf; cdestruct H.
      unfold Candidate.mem_reads; set_unfold.
      rewrite lookup_unfold in H0; setoid_rewrite lookup_unfold.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      done.
    + set_unfold.
      unfold grel_functional.
      cdestruct |- ***.
      opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _) as H_rf; eauto; cbn in *.
      eapply H_rf in H; eapply H_rf in H0; clear H_rf; cdestruct H, H0 #CDestrEqOpt.
      ospecialize (H3 z _ _ _ _ ); rewrite ?lookup_unfold; eauto; try done.
      1: sauto.
      ospecialize (H7 y _ _ _ _ ); rewrite ?lookup_unfold; eauto; try done.
      1: sauto.
      cdestruct y, x, H3, H7 #CDestrSplitGoal.
      done.
    + cbn.
      assert (Candidate.is_nms ((build_pre_exec (initSt seqst) (trace_cons (call &→ ret) (itrs seqst))))) as Hnms by admit.
      opose proof (Candidate.rf_valid (Candidate.reads_from_wf' _ (cd_wf _ H_inv))) as H_base.
      unfold Candidate.is_valid_rf.
      cdestruct |- *** as.
      opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _) as H_rf; eauto; cbn in *.
      eapply seq_state_to_partial_cd_state_destruct;
      cdestruct |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal;
      rewrite ?Hsame_init, ?Hsame_itrs in *;
      setoid_rewrite lookup_unfold.
      all: try (ospecialize (H_base (_,_) _); [by eauto|]; unfold cd, Candidate.is_valid_rf in *).
      all: cdestruct H_base #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      all: try solve [do 7 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal; eauto)].
      1: by rewrite intra_trace_eid_succ_byte in *.
      cdestruct seqst_succ, call |- ***.
      eapply (pcdst_mem_map_inv _ H_inv) in H0.
      cdestruct H0 #CDestrEqOpt.
      do 5 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch).
      2: cdestruct ret #CDestrMatch.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      opose proof (seq_st_mem_map_consistent _ H_inv) as H_seqst_mem_map.
      cdestruct ret, seqst_succ, H2 #CDestrMatch.
      1: admit.
      unfold read_mem_seq_state, read_byte_seq_state, read_byte_seq_state_flag in *.
      cdestruct b |- ***.
      destruct x1; cbn in *.
      ospecialize (Hnms (t,intra_trace_eid_succ 0 (trace_rev (itrs seqst))) _).
      {
        unfold Candidate.overlapping, Candidate.is_overlapping, Candidate.mem_events.
        set_unfold.
        setoid_rewrite lookup_unfold.
        cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
        all: eexists; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt #CDestrMatch; try done.
        2,3: unfold is_mem_event, is_mem_readP, is_mem_writeP; naive_solver.
        all: do 3 (eexists; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt #CDestrMatch).
        unfold pa_overlap.
        setoid_rewrite pa_in_range_spec.
        cdestruct pa0.
        left; exists 0%N; rewrite pa_addN_zero; cdestruct |- *** #CDestrSplitGoal.
        enough (x0 ≠ 0)%N by lia.
        admit.
      }
      unfold Candidate.same_footprint, Candidate.same_pa, Candidate.same_size in *.
      set_unfold in Hnms.
      cdestruct pa0, n, Hnms #CDestrEqOpt.
      eapply (bvs_equal_get_byte_equal 8); try done.
      intros.
      eapply Some_inj.
      cbn in *.
      setoid_rewrite <- bv_to_bytes_bv_get_byte2 at 2; try lia.
      rewrite bv_to_bytes_bv_of_bytes; try done.
      2: by rewrite length_fmap, pa_range_length, N2Nat.id.
      setoid_rewrite list_lookup_fmap.
      erewrite fmap_Some_2.
      2: eapply pa_range_lookup; lia.
      ospecialize (H_seqst_mem_map (pa_addN (ReadReq.pa rr) i) (bv_get_byte 8 i value)).
      destruct H_seqst_mem_map as [_ H_seqst_mem_map].
      orewrite H_seqst_mem_map; clear H_seqst_mem_map.
      1: done.
      setoid_rewrite lookup_unfold.
      eexists _, _, _.
      cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal; first apply H0.
      1: unfold is_mem_writeP.
      all: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      1: cbn in *; lia.
      eapply or_comm, H5; cdestruct |- *** #CDestrEqOpt.
      admit. (*NMS*)
    + cbn; rewrite Hsame_init, Hsame_itrs.
      unfold Candidate.init_mem_reads, Candidate.mem_reads, Candidate.is_valid_init_mem_read.
      set_unfold.
      cdestruct |- *** #CDestrEqOpt.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      opose proof (seq_model_mem_reads_inv _ H_inv _ _ _ _ x _ _ _ _ _ _ _ _ _) as Hreads;
        eauto; cbn; rewrite ?Hsame_itrs; cdestruct |- *** #CDestrEqOpt; eauto.
      cdestruct Hreads #CDestrEqOpt #CDestrSplitGoal.
      all: rewrite ?Hsame_itrs, ?Hsame_init in *.
      1: exfalso; eauto.
      cdestruct x3.
      replace ((8 * x1) `div` 8)%N with x1 by lia.
      reflexivity.
  - opose proof (seq_model_co_acc_inv _ H_inv _ _ _ _) as H_co; eauto.
    assert (Candidate.is_nms ((build_pre_exec (initSt seqst) (trace_cons (call &→ ret) (itrs seqst))))) as Hnms by admit.
    constructor.
    + eapply grel_transitive_spec.
      cdestruct |- *** as ??? ?%H_co ?%H_co.
      deintros; cdestruct |- *** #CDestrEqOpt.
      eapply H_co.
      eexists _, _; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    + eapply grel_irreflexive_spec.
      cdestruct |- *** as ?? Hc%H_co -> #CDestrEqOpt; cdestruct Hc #CDestrEqOpt.
    + unfold Candidate.mem_writes.
      cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      rewrite Hsame_itrs, Hsame_init in *.
      ospecialize (Hnms (weid1,weid2) _); eauto.
      1: unfold Candidate.overlapping, Candidate.mem_events; set_unfold;
        cdestruct |- *** #CDestrSplitGoal; try eexists;
        cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt;
        unfold is_mem_event, is_mem_writeP; cbn; naive_solver.
      unfold Candidate.same_footprint, Candidate.same_size, Candidate.same_pa in *; set_unfold;
      cdestruct x2, Hnms #CDestrEqOpt.
      opose proof (EID.full_po_lt_connex weid1 weid2 _ _ _).
      1-3: destruct weid1 as [???[]], weid2 as [???[]]; cbn in *; try fast_done;
        deintros; unfold lookup, lookup_ev_from_iTraces; cdestruct |- *** #CDestrEqOpt.
      cdestruct weid1, weid2, H3 |- *** #CDestrSplitGoal.
      1: by left.
      1: right; left.
      2: right; right.
      all: rewrite <- ?Hsame_itrs.
      all: eapply H_co.
      all: eexists _, _; repeat apply conj; cbn; rewrite ?Hsame_itrs;
      cdestruct |- *** #CDestrEqOpt.
  - constructor.
    all: unfold Candidate.exclusive_reads, Candidate.lxsx.
    all: cdestruct |- ***.
    all: set_unfold.
    all: cdestruct |- ***.
  - admit. (* reg reads wf *)
Admitted.

Theorem op_model_soundness max_mem_acc_size isem fuel initSt:
  Model.Res.weaker
    ((Model.to_nc $ sequential_modelc (Some regs_whitelist) max_mem_acc_size fuel isem) 1 initSt)
    (Ax.to_Modelnc (et := Candidate.NMS) isem (AxUMSeqArm regs_whitelist) 1 initSt).
Proof.
  cdestruct |- *** as Ax_no_err.
  unfold Model.Res.no_error in *.
  split.
  - cdestruct |- *** as axfs H_axfs.
    Transparent propset_bind propset_ret.
    unfold propset_bind in *.
    cdestruct axfs, H_axfs |- *** as [] m H_ofinst H_finst.
    set_unfold.
    exists m.
    destruct m; cbn in *.
    2,3: unfold mfail , set_mfail in *; set_solver.
    split.
    1: done.
    unfold mret, propset_ret in *.
    cdestruct finSt, H_ofinst.
    unfold elem_of, listset_elem_of in H_finst.
    cdestruct H_finst.
    destruct x; cbn in *.
    2: done.
    cdestruct val, H.
    unfold Exec.to_stateful_result_list in *.
    set_unfold.
    cdestruct H0 #CDestrSplitGoal.
    revert dependent s isem.
    elim fuel; cdestruct |- *** #CDestrEqOpt #CDestrMatch.
    1: destruct isem; deintros; cdestruct  |- *** #CDestrEqOpt.
    1: unfold set, MState.finalize in *; cdestruct H1 |- *** #CDestrMatch #CDestrEqOpt.
    1: depelim H1.
    1: eexists (Candidate.make _ (Candidate.make_pre _ _ [# [FTRet ()]]) ∅ ∅ ∅ ∅); cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    2: {
      unfold Candidate.ISA_match; cdestruct |- ***.
      rewrite lookup_total_unfold in *.
      cdestruct l, f, H0.
      constructor.
    }
    1: admit.
    1: unfold Ax.to_ModelResult, Ax.Res.to_ModelResult, AxUMSeqArm, Candidate.cd_to_MState_final,
    MState.finalize, MState.is_terminated, Is_true, seq_state_to_init_regs in *.
    1: deintros; cdestruct |- *** #CDestrMatch.
    1: f_equal.
    1: erewrite Is_true_pi; eauto.
    1: eapply n0.
    1: admit.
    1: eexists (Candidate.make _ (Candidate.make_pre _ _ [# [FTRet ()]]) ∅ ∅ ∅ ∅); cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.

    Search Is_true.
    Print ProofIrrel.
    1: unfold Is_true.
    Set Printing All.
    1: unfold Is_true in *.
    1: specialize (i0 0%fin).
    1: unfold terminated'.
    Search bool_decide_pack.
    1: destruct MState.is_terminated in i0.
    1: destruct terminated'.

      set_unfold.
    2: constructor.


    1: set_unfold.
    1: admit. (* initial state is consistent *)

Abort.

        rewrite ?Hsame_itrs; eauto.

      unfold p
      all: try solve
      intros ->.
      eappl
      1: congruence.

      rewrite Hsame_init, Hsame_itrs in *.
      eapply H_cp in H0
      opose proof
      set_unfold.
     unfold grel_transitive; cbn.
    rewrite <- H2.
    cdestruct x3 |- ***.
    rewrite H2.
    all: rewrite ?Hsame_itrs in *.
    eapply (bvs_equal_get_byte_equal 8); first done; cbn.
    replace ((8 * x1) `div` 8)%N with x1 by lia.
    intros offset ?.
    Search bv_to_bytes.
    enough (Some (bv_get_byte 8 offset x3) =
      Some (bv_get_byte 8 offset (bv_of_bytes (8 * x1)
      (MState.memory (initSt seqst) <$> pa_range (ReadReq.pa x2) x1))))
    by (deintros; cdestruct |- *** #CDestrEqOpt).
    replace (Some (bv_get_byte 8 offset (bv_of_bytes (8 * x1) (MState.memory (initSt seqst) <$> pa_range (ReadReq.pa x2) x1))))
    with ((MState.memory (initSt seqst) <$> pa_range (ReadReq.pa x2) x1) !! offset) by admit.
    Print memoryMap.
    replace ((MState.memory (initSt seqst) <$> pa_range (ReadReq.pa x2) x1) !! offset)
    with (Some((MState.memory (initSt seqst)) (pa_addN (ReadReq.pa x2) offset))).
    with


    1: rewrite lookup_unfold; eauto.
    eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.

     {
        eapply H_seqst_mem_map in H7.
        cdestruct b, H7 #CDestrEqOpt.
        setoid_rewrite lookup_unfold in H10.
        ospecialize (H10 _ _ H0 _); first unfold is_mem_writeP; cbn.
        1: eapply pa_in_range_spec; eexists offset; cdestruct |- *** #CDestrSplitGoal.
        setoid_rewrite lookup_unfold in H4.
        ospecialize (H4 _ _ H7 _ _); first done.
        1: admit. (*NMS*)
        cdestruct x1, t, H10, H4 #CDestrSplitGoal #CDestrEqOpt.
        destruct x4; cbn in *. About bv_get_byte.
        assert (x3 = x0) as -> by admit. (*NMS*)
        f_equal.
        1: admit.
        by depelim H0.
     }
     exfalso.
     revert H7.
     eapply not_eq_None_Some.
     unfold is_Some.
     eexists.
     eapply H_seqst_mem_map.
     setoid_rewrite lookup_unfold.
     eexists _, _, offset; cdestruct |- *** #CDestrSplitGoal.
     1: eapply H0.
     1: unfold is_mem_writeP.
     ospecialize (H_seqst_mem_map (pa_addN (ReadReq.pa rr) offset)).

        assert (offset = x2) as -> by admit.
        enough (value = value0) as -> by reflexivity.
        f_equal.
        Set Printing All.

        f_equal.
        f_equal.
        cdestruct H10

        1: eapply H0.
        assert (WriteReq.pa x4 = ReadReq.pa rr) by admit. (* NMS *)
        assert (x2 = offset) as -> by admit.

      cdestruct |- *** #CDestrEqOpt.
      rewrite lookup_unfold.
      unfold bv_of_bytes.

      enough (bv_to_bytes 8 value = ((λ pa,
      (if mem seqst !! pa is Some v then (v, true) else (MState.memory (initSt seqst) pa, false)).1) <$>
   pa_range (ReadReq.pa rr) n)) by admit.
   ospecialize (H6 pa0).
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal
      2: { }
      1: do 7 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal; eauto).
      cdestruct H0 #CDestrEqOpt #CDestrMatch.
      2: ospecialize (H_base (_,_) _); eauto; unfold cd, Candidate.is_valid_rf in *.
      2: cdestruct H_base #CDestrEqOpt #CDestrMatch.
      2-3: do 8 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal).
      * ospecialize (H_base (_,_) _); eauto; unfold cd, Candidate.is_valid_rf in *.
        cdestruct H_base #CDestrEqOpt #CDestrMatch.
        all: do 8 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal).
      * ospecialize (H_base (_,_) _); eauto; unfold cd, Candidate.is_valid_rf in *.
        cdestruct H_base #CDestrEqOpt #CDestrMatch.
        all: do 8 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal).

        eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      1: eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      1: eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      setoid_rewrite H_rf.
      *

      opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _) as H_rf; eauto; cbn in *.
      eapply H_rf in H; clear H_rf; cdestruct H #CDestrEqOpt.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      cdestruct H0 |- *** #CDestrMatch #CDestrEqOpt #CDestrSplitGoal.
      1: unfold lookup, lookup_ev_from_iTraces in *;
        deintros; cdestruct |- *** #CDestrEqOpt.
      opose proof (seq_st_mem_map_consistent _ H_inv) as H_seqst_mem_map; try done; cbn in H_seqst_mem_map.
      unfold seq_st_mem_map_consistentP in *.

      lookup_ev_from_iTracesm

Admitted. (*

    all: rewrite Exec.unfold_has_error in H_seqst_succ.

    cdestruct |- *** #CDestrMatch.
    1: unfold Candidate.reg_from_reads.
    all: try done.
    all: cdestruct H_mono.
    eapply seq_state_to_partial_cd_state_destruct.
    + cdestruct |- ***.
    rel_monotone_acyclic


      1: unfold EID.full_po_lt, EID.po_lt.
      3: best.
      1: rewrite lookup_total_unfold in *.

      subst.
      repeat split; cdestruct |- ***.

      rewrite if_distribution_option in H0.
    erewrite (if_indiscriminate_cases_option) in H0.

    cdestruct H0 #CDestrMatch.
    * ospecialize (H_inv _ _ _).
      setoid_rewrite lookup_unfold in H_inv.
      setoid_rewrite lookup_unfold.
      cdestruct H_inv |- *** #CDestrMatch.
      all: eexists; repeat split; try eassumption.
      1: naive_solver.
      1: cdestruct |- *** #CDestrMatch; eapply H5; cdestruct |- *** #CDestrMatch.
      all: hauto l: on.
  +
    all: try naive_solver.
    unfold reg_read_upd_partial_cd_state in *. (* TODO write Lemmas *)
    cdestruct H0 #CDestrMatch.
      eexists; repeat split; eauto.
      1: destruct call; hauto lq: on.
      cdestruct |- *** #CDestrMatch.
      1: eapply H8.
      1: cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
      1: eapply H12.
      1: done.
      1: destruct call; cdestruct H11 |- ***; hauto l: on.
      1: destruct call; cdestruct H9 |- ***; hauto l: on.
    exists (MemWrite x0 x1 &→ inl true).
    repeat split.
    3: intros ???.
    3: { rewrite lookup_unfold in H9.
    2: { eapply (H8 eid').
    1: rewrite lookup_unfold.
    eapply H_inv.
    eexists.
    cdestruct |- *** #CDestrSplitGoal;
    eauto 9.
    rewrite lookup_unfold.

    eapply H_inv.
  eapply seq_state_step_to_cd; first eauto.
  unfold seq_state_to_cd.
  intros ??.
  (* erewrite seq_state_step_to_pe_eq, seq_state_to_pe_trace_cons; last eauto. *)
  eapply seq_state_step_to_partial_cd_state; first eauto.
  + unfold pcdst_mem_map_invP in *.
    cdestruct |- ***.
    ospecialize (H_pcdst_mem_map_wf _ _ _); first eauto.
    cdestruct H_pcdst_mem_map_wf.
    exists (MemWrite x0 x1 &→ inl true).
    cdestruct |- *** #CDestrSplitGoal.
    * unfold seq_state_to_cd in H1.
      rewrite ?lookup_unfold in *.
      cdestruct H1 |- *** #CDestrMatch.
      1: opose proof (intra_trace_eid_succ_components_equal _ _ _ _ _ _ _ ); eauto.
      1: subst.
      all: rewrite Hsame_itrs in *.
      1: rewrite lookup_unfold in H4.
      1: scongruence.
      1: done.
      1: admit.
    * rewrite ?lookup_unfold in H3.
      cdestruct H1, H3, H_seq_st_succ |- *** #CDestrMatch.
      2: {
        eapply H2; eauto.
        1: rewrite lookup_unfold, Hsame_itrs in *; cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
        1: eauto.
        hauto l: on.
      }
      opose proof (intra_trace_eid_succ_components_equal _ _ _ _ _ _ _ ); eauto.
      exfalso.

      2: {}




        rewrite H4.
        cdestruct |- *** #CDestrMatch.
        1: assert (eid = (intra_trace_eid_succ 0 (trace_rev (itrs seq_st_succ)))) as -> by admit.
        1: erewrite sequential_model_outcome_same_itrs in H4; last eauto.
        1: rewrite lookup_unfold in H4.
        1: done.
        admit.
      * eapply H2.

        cdestruct H3 #CDestrMatch.
        1: assert (eid' = (intra_trace_eid_succ 0 (trace_rev (itrs seq_st_succ)))) as -> by admit.
        all: eapply H2.




      all: cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
      1: assert (eid = (intra_trace_eid_succ 0 (trace_rev (itrs seq_st_succ)))) as ->.
      { destruct eid; subst. cbn in *. subst. admit. }
      1: admit.
      eapply H_pcdst_mem_map_wf.
    all: cdestruct |- ***.
    all: rewrite lookup_unfold.
    all: cdestruct |- *** #CDestrMatch; last admit.
    1: unfold pcdst_mem_map_invP in *.
    1: eapply H_pcdst_mem_map_wf.
    all: unfold pcdst_mem_map_invP, update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
    mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state in *.
    all: cdestruct H_pcdst_mem_map_wf, H0, H_seq_st_succ #CDestrMatch #CDestrSplitGoal.
    all: cdestruct H, H_seq_st_succ |- *** #CDestrMatch #CDestrSplitGoal.
    all: opose proof (H_pcdst_mem_map_wf eid _ _) as Hbase; eauto.
    all: admit.
    (* 5-15,20-24: cdestruct Hbase; eexists; cdestruct |- *** #CDestrSplitGoal; by eauto.
    all: unfold Setter_finmap in *.
    all: rewrite lookup_unfold in *.
    all: cdestruct H1 |- *** #CDestrMatch.
    all: eauto.
    all: subst.
    Search lookup partial_alter.



    hauto lq: on rew: off.
    + cbn in *.
      setoid_rewrite and_or_dist.
      setoid_rewrite exists_or_dist.
      cdestruct H #CDestrMatch; last naive_solver.
      all: unfold Setter_finmap in *.
      all: rewrite lookup_unfold in H2.
      all: cdestruct H2 #CDestrSplitGoal #CDestrMatch.
      1,4: right; autorewrite with pair; eauto.
      all: left; unshelve eapply H_pcdst_wf; eauto.
    + cbn in *.
      setoid_rewrite and_or_dist.
      setoid_rewrite exists_or_dist.
      unfold Setter_finmap in *.
      rewrite (lookup_unfold (k := reg0)) in H.
      cdestruct H #CDestrSplitGoal #CDestrMatch.
      1,3: left; unshelve eapply H_pcdst_wf; eauto.
      1: right; autorewrite with pair; eauto. *)
  - admit.
  - unfold cd_monotone in *.
    cdestruct Hmono |- *** #CDestrSplitGoal.
    all: eapply seq_state_step_to_partial_cd_state; first eauto.
    all: generalize dependent (seq_state_to_partial_cd_state seq_st).
    all: cdestruct |- ***.
    all: opose proof (event_list_monotone _ evs [(intra_trace_eid_succ 0 (Candidate.events (seq_state_to_pe seq_st) !!! 0%fin), call &→ ret)] (trace_snoc_event_list _ _ _)).
    all: unfold update_partial_cd_state_for_eid_ev in *.
    all: destruct call; cbn in *; try done.
    all: unfold reg_read_upd_partial_cd_state, mem_read_upd_partial_cd_state, mem_write_upd_partial_cd_state.
    all: cdestruct |- *** #CDestrMatch.
    all: unfold rel_strictly_monotone in *.
    all: autorewrite with pair in *.
    all: cdestruct |- *** #CDestrSplitGoal; last set_solver.
    all: set_unfold in H2; cdestruct H2.
    all: unshelve assert (t ∈ evs.*1) as H_ev_in_ev_list by admit.
    all: set_unfold in H_ev_in_ev_list; cdestruct H_ev_in_ev_list as ev Hl.
    all: ospecialize (H2 t _ _ (_,_) _ _);
    [eassumption|now eapply elem_of_list_singleton| |assumption].
    all: rewrite intra_trace_eid_succ_tid.
    all: unfold seq_state_to_pe in Hl;
    unfold lookup, Candidate.lookup_eid_pre, Candidate.lookup_iEvent, Candidate.lookup_instruction, lookup,
    vec_lookup_nat in *.
    all: cdestruct Hl #CDestrMatch.
    all: lia.
  Admitted.
 *)
Lemma seq_model_seq_inv_predicate_preserved :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    seq_inv_predicate.
Proof using fuel
isem regs_whitelist.
  cdestruct |- *** as seqst H_seq_inv call seqst_succ H_succ.
  constructor.
  - eapply seq_model_mem_writes_succeed_inv; done.
  - eapply seq_model_pcdst_mem_map_inv; done.
  - eapply seq_model_pcdst_reg_map_inv; done.
  - eapply seq_model_pcdst_montonone; done.
  - eapply seq_model_pcdst_wf; done.
  - eapply seq_model_pcdst_consistent; done.
Qed.

Lemma seq_model_consistent :
  seq_model_outcome_invariant_preserved seq_inv_predicate.
Proof.
  cdestruct |- *** as seq_st [] call seq_st_succ H_succ_st.
  constructor.
  - now eapply (seq_model_monotone seq_st _ call).
  - now eapply (seq_model_monotone seq_st _ call).
  - now eapply (seq_model_monotone seq_st _ call).
  - now eapply (seq_model_monotone seq_st _ call).
  - assert (pcdst_mem_map_invP seq_st_succ) as Hmem_map_wf
    by now eapply (seq_model_monotone seq_st _ call).
    assert (mem_writes_succeedP seq_st_succ) as Hmem_w_succeed
    by now eapply (seq_model_monotone seq_st _ call).
    unfold pcdst_mem_map_invP, mem_writes_succeedP in Hmem_map_wf, Hmem_w_succeed.
    constructor.

    + admit. (* TODO: only supported events *)
    + unfold sequential_model_outcome_logged, fHandler_logger in *.
    cdestruct seq_st_succ, H_succ_st as seq_st_succ ret H_succ_st.
    unfold cd0, seq_state_to_cd in *.
    erewrite seq_state_step_to_pe_eq, seq_state_to_pe_trace_cons(* trace_snoc_event_list *) in *; last eauto.
    eapply seq_state_step_to_partial_cd_state; first eauto.
    unfold cd0, seq_state_to_cd in *.
    destruct cd_wf0 as [? []].
    constructor.
    * destruct (decide (is_mem_write (call &→ ret))).
      2: {
        unfold seq_state_to_partial_cd_state, update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
        mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state, Candidate.mem_writes, seq_state_to_cd in *;
        destruct call; cbn in *; cdestruct |- *** #CDestrMatch;
        intro eid; cdestruct |- ***.
        all: destruct (seq_state_to_pe seq_st); do 2 depelim events; unfold set, Setter_compose; cbn in *.
        all: rewrite lookup_unfold.
        1-3,5-17: cdestruct |- *** #CDestrMatch;
        [opose proof (rf_from_writes eid _) as Hrfdom;
        [set_unfold; try solve [eexists; eassumption] | try solve [cdestruct Hrfdom as ???; subst; by rewrite lookup_unfold in *]]|
        try solve [set_unfold in rf_from_writes; cdestruct rf_from_writes; cbn in *; hauto lq: on rew: off]].
        opose proof (Hmem_map_wf t rr.(ReadReq.pa) _) as [? (? & ? & ?)].
        all: rewrite H in *.
        1: unfold set; now cbn.
        unfold partial_cd_state_to_cd, set, Setter_compose in H2; cbn in *.
        cdestruct H0 |- *** #CDestrMatch #CDestrSplitGoal; subst.
        { unfold lookup, Candidate.lookup_eid_candidate in H2. cbn in *.
          rewrite lookup_unfold in H2; cdestruct H2 #CDestrMatch. naive_solver. }
        { unfold lookup, Candidate.lookup_eid_candidate in H2. cbn in *.
          rewrite lookup_unfold in H2; cdestruct H2 #CDestrMatch.
          set_unfold in Hmem_w_succeed; cdestruct Hmem_w_succeed.
          destruct x0 as [[] ?] eqn: ?H; try done.
          ospecialize (Hmem_w_succeed x0 _ _).
          { eexists (t,_); cdestruct |- *** #CDestrSplitGoal. unfold set, Setter_compose; cbn.
            rewrite lookup_unfold. cdestruct |- *** #CDestrMatch. }
          1: naive_solver.
          eexists.
          split.
          1: eauto.
          subst.
          cbn in *.
          cdestruct Hmem_w_succeed |- *** #CDestrMatch. }
        { opose proof (rf_from_writes (intra_trace_eid_succ 0 h) _).
          1: set_unfold; eexists; eauto.
          cdestruct H4.
          now rewrite lookup_unfold in *. }
        { opose proof (rf_from_writes eid _).
          1: set_unfold; eexists; eauto.
          cdestruct H5.
          naive_solver. } }
      unfold seq_state_to_partial_cd_state, update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
      mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state, Candidate.mem_writes, seq_state_to_cd in *;
      destruct call; cbn in *; try done.
      intro eid.
      destruct (seq_state_to_pe seq_st); do 2 depelim events; unfold set, Setter_compose; cbn in *.
      cdestruct |- ***.
      rewrite lookup_unfold.
      cdestruct H |- *** #CDestrMatch; subst; eauto.
      all: opose proof (rf_from_writes eid _) as Hrfdom; cdestruct |- ***; eauto.
      all: cdestruct Hrfdom; eexists; cdestruct |- *** #CDestrSplitGoal; done.
    * admit.
    * intros x y z; cdestruct |- ***.
      unfold seq_state_to_partial_cd_state, update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
      mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state, Candidate.mem_writes, seq_state_to_cd in *.
      destruct call; cdestruct H, H0 #CDestrMatch.
      all: try solve [eapply rf_functional; by cdestruct |- ***].
      cdestruct H0, H2 #CDestrSplitGoal; subst.
      1: hauto l: on.
      1,2: opose proof (rf_to_reads _ _) as Hrf_reads; first (cdestruct |- ***; eauto).
      1,2: destruct (seq_state_to_pe seq_st) as [? v]; do 2 depelim v; unfold Candidate.mem_reads in Hrf_reads; cbn in *; cdestruct Hrf_reads.
      1,2: by rewrite lookup_unfold in *.
      1: eapply rf_functional; cbn in *; cdestruct |- ***; eauto.
    * cdestruct |- ***.
      unfold partial_cd_state_to_cd, Candidate.is_valid_rf, seq_state_to_partial_cd_state, update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
      mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state, Candidate.mem_writes, seq_state_to_cd in *.
      destruct call; cbn in *; try done.
      all: cdestruct H, H_succ_st |- *** #CDestrMatch #CDestrSplitGoal.
      all: try (ospecialize (rf_valid (_,_) _); first eassumption; cbn in *; cdestruct rf_valid #CDestrMatch).
      all: assert (EID.byte t0 = None) as Hbyte by admit.
      all: rewrite ?Hbyte in *; try done.
      all: destruct (seq_state_to_pe seq_st); do 2 depelim events; unfold set, Setter_compose; cbn in *.
      all: rewrite ?cd_to_pe_lookup in *; unfold set, Setter_compose in *; cbn in *.
      all: cdestruct |- *** #CDestrSplitGoal.
      all: rewrite ?lookup_unfold.
      all: cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
      all: try solve [opose proof (rf_from_writes _ _) as Hrf_writes; first (cdestruct |- ***; eauto);
      cdestruct Hrf_writes; subst; rewrite ?lookup_unfold in *; done].
      all: try (ospecialize (Hmem_map_wf t (ReadReq.pa rr) _); [solve [cdestruct |- *** #CDestrMatch]|];
      cdestruct Hmem_map_wf |- ***; rewrite ?cd_to_pe_lookup in *;
      cbn in *; rewrite ?lookup_unfold in *; do 2 deintro; cdestruct |- *** #CDestrMatch).
      all: rewrite ?cd_to_pe_lookup in *; unfold set, Setter_compose in *; cbn in *.
      all: eexists; split; eauto.
      all: cdestruct |- ***.
      all: rewrite lookup_unfold; cdestruct |- *** #CDestrMatch.
      all: eexists; split; eauto.
      all: rewrite ?lookup_unfold; cdestruct |- *** #CDestrMatch.
      all: try solve [opose proof (rf_from_writes _ _) as Hrf_writes; first (cdestruct |- ***; eauto);
      cdestruct Hrf_writes; subst; rewrite ?lookup_unfold in *; done].
      all: try solve [opose proof (rf_to_reads _ _) as Hrf_reads; first (cdestruct |- ***; eauto);
      unfold Candidate.mem_reads in Hrf_reads; cdestruct Hrf_reads; subst; rewrite ?lookup_unfold in *; done].
      all: eexists; split; eauto.
      all: cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
      4,6: admit (* TODO :  read has right value *).
      4,5: admit. (* Abort write case *)
      all: eexists; split; eauto.
      all: unfold is_Some.
      all: exists ().
      all: cdestruct |- *** #CDestrMatch #CDestrEqOpt.
      all: eauto 7.
      Unshelve.
      all: cdestruct |- *** #CDestrSplitGoal.
    *
    unfold partial_cd_state_to_cd, Candidate.is_valid_rf, seq_state_to_partial_cd_state, update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
      mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state, Candidate.mem_writes, seq_state_to_cd in *.
      destruct call; unfold Candidate.init_mem_reads in *; cbn in *; cdestruct H_succ_st |- *** #CDestrMatch #CDestrSplitGoal; try done.
      9: admit (* write abort *).
      all: unfold Candidate.is_valid_init_mem_read.
      all: cdestruct |- ***.
      all: destruct (seq_state_to_pe seq_st); do 2 depelim events; unfold set, Setter_compose; cbn in *.
      all: rewrite lookup_unfold.
      all: cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
      all: unfold Candidate.mem_reads in *.
      all: cdestruct H1.
      all: unfold set, Setter_compose in *; cbn in H1.
      all: rewrite ?lookup_unfold in *.
      all: cdestruct H1 #CDestrMatch.
      1: {
      ospecialize (rf_valid_initial reid _).
      - unfold Candidate.mem_reads.
        cdestruct |- *** #CDestrSplitGoal.

      }

      all: try (ospecialize (rf_valid_initial reid _);
      first solve [unfold Candidate.mem_reads in *; cdestruct H1 |- *** #CDestrMatch #CDestrSplitGoal;
      unfold set, Setter_compose in H1; cbn in H1;
      rewrite ?lookup_unfold in *; cdestruct H1 #CDestrMatch #CDestrSplitGoal]).
      all: unfold Candidate.is_valid_init_mem_read in *.
      all: cdestruct rf_valid_initial.
      all: eexists; split; eauto.
      2: { ospecialize (rf_valid_initial reid _). 1: unfold Candidate.mem_reads in *;
      cdestruct H1 |- *** #CDestrMatch #CDestrSplitGoal; unfold set, Setter_compose in H1; cbn in H1; rewrite lookup_unfold in *.
      1: cdestruct H1 |- *** #CDestrMatch #CDestrSplitGoal; eexists; cdestruct |- *** #CDestrSplitGoal;
      eauto; cdestruct |- ***.
      1: cdestruct rf_valid_initial |- ***; eauto.
      1: now unfold is_mem_readP, is_mem_read_reqP. }
      9: admit (* write abort *).
      all: unfold Candidate.init_mem_reads in *.
      all : unfold guard.
      all: rewrite ?lookup_unfold; cdestruct |- *** #CDestrMatch.
      5: { rewrite lookup_unfold in *.  cdestruct H10 |- *** #CDestrMatch. cbv [mthrow] in *. }
      1,2: admit.
      1: autorewrite with pair in *.
      1: ospecialize (rf_valid _ _ H).
      1: cdestruct rf_valid #CDestrMatch; eauto.
      1: exact H2.
      (* all: try solve [opose proof (rf_to_reads _ _) as Hrf_reads; first (cdestruct |- ***; eauto);
      unfold Candidate.mem_reads in Hrf_reads; cdestruct Hrf_reads; subst; rewrite ?lookup_unfold in *; done]. *)
      all: eexists; split; cdestruct |- ***.
      all: rewrite ?cd_to_pe_lookup in *; unfold set, Setter_compose in *; cbn in *; eauto.
      all: repeat (eexists; split; cdestruct |- ***; eauto).
      all: rewrite ?lookup_unfold.
      all: cdestruct |- *** #CDestrMatch.
      all: try solve [opose proof (rf_to_reads _ _) as Hrf_reads; first (cdestruct |- ***; eauto);
      unfold Candidate.mem_reads in Hrf_reads; cdestruct Hrf_reads; subst; rewrite ?lookup_unfold in *; done].
      all: eauto.
      all: try ospecialize (rf_valid (_,_) H); cbn in *; cdestruct rf_valid #CDestrMatch.
      all: eauto.
      1: eapply H2.
      6: { cdestruct H0 #CDestrSplitGoal; subst; try solve [opose proof (rf_from_writes _ _) as Hrf_writes; first (cdestruct |- ***; eauto);
      cdestruct Hrf_writes; subst; rewrite ?lookup_unfold in *; done]. admit. (* maps only contain smaller eids *) }
      8: { cdestruct H0 #CDestrSplitGoal; subst; try solve [opose proof (rf_from_writes _ _) as Hrf_writes; first (cdestruct |- ***; eauto);
      cdestruct Hrf_writes; subst; rewrite ?lookup_unfold in *; done]. }
      all: try eapply option_mbind_is_Some_elim.
      1: opose proof (rf_from_writes _ _) as Hrf_writes; first (cdestruct |- ***; eauto);
      cdestruct Hrf_writes; subst; rewrite ?lookup_unfold in *.
      1: eexists; split; eauto.
      1: cdestruct |- ***.
      1: opose proof (rf_to_reads _ _) as Hrf_reads; first (cdestruct |- ***; eauto);
      unfold Candidate.mem_reads in Hrf_reads; subst; cdestruct Hrf_reads |- ***; rewrite ?lookup_unfold in *.
      1: eapply option_mbind_is_Some_elim.
      1: eexists; split; eauto; cdestruct |- ***.
      1: ospecialize (rf_valid (_,_) H0).
      1:  eapply option_mbind_is_Some_intro in rf_valid.
      all: try done.
      all: eexists.
      all: try setoid_rewrite lookup_unfold.
      all: eexists.
      Set Printing All.



        cbn.  ; naive_solver.
        unfold is_mem_writeP, is_mem_write_reqP in *. eexists; split; eauto. naive_solver. }

      1,2: destruct (Hmem_map_wf _ _ H) as (? & ? & ? & ?).
      1: unfold cd0 in *; subst.
      1: unfold seq_state_to_cd in *.
      ; first admit;
      unfold evs0 in *; cdestruct H3; subst; rewrite lookup_unfold in *.
      1: easy.
      1: eexists; split; eauto.

      1-16: set_unfold in rf_from_writes; cdestruct rf_from_writes; cbn in *; hauto lq: on rew: off.
      1: cdestruct H0 #CDestrSplitGoal.
1: opose proof (rf_from_writes eid _) as Hrfdom;
[set_unfold; try solve [eexists; eassumption] | try solve [cdestruct Hrfdom as ???; subst; by rewrite lookup_unfold in *]].
      1: best.
      1: cbn in *.
      1: eapply rf_from_writes.
      1: split.
      1: setoid_rewrite lookup_unfold_traces_snoc.
      1: rewrite lookup_unfold.
      Set Typeclasses Debug Verbosity 2.
      1: cbv [set].
      1: unfold lookup, Candidate.lookup_eid_pre.
      1: unfold Setter_compose, Setter_valter, alter, valter.
      1: rewrite lookup_unfold.


      1: unfold lookup, Candidate.lookup_eid_pre.
      1: rewrite lookup_unfold.
      1: try set_solver.

     intros eid Heiddom.
     cdestruct eid, Heiddom |- ***.

  - constructor.
    * assert (seq_model_monotone (seq_state_to_cd seq_st_succ)) as (? & ? & ?)
      by now eapply (seq_model_monotone seq_st _ call).
      unfold cd_monotone, seq_state_to_cd in *.
      apply rel_monotone_acyclic.
      rewrite <- ?rel_montone_union.
      unfold GenAxiomaticArm.AxArmNames.fr, GenAxiomaticArm.AxArmNames.co, GenAxiomaticArm.AxArmNames.rf.
      cdestruct |- *** #CDestrSplitGoal.
      2: eapply rel_strictly_monotone_seq2; split.
      4: eapply rel_montone_intersection1, rel_strictly_monotone_seq1; split.
      4: eapply rel_strictly_monotone_seq2; split.
      7: eapply rel_strictly_monotone_seq1; split.
      2,4,6,8: eapply grel_from_set_montone.
      all: try assumption.
      2: unfold Candidate.from_reads.
      all: unfold Candidate.overlapping.

      all: unfold Candidate.explicit_writes, Candidate.writes_by_kind.
      2: {
        unfold rel_strictly_monotone.
        cdestruct |- ***.
        assert (t ≠ t0)
        by (intros ->; unfold Candidate.mem_reads, Candidate.mem_writes in *;
            cdestruct H2, H6; naive_solver).
        enough (¬ EID.full_po_lt t0 t)
        by (opose proof (EID.full_po_lt_connex t t0 _ _ _) as [|[|]]; [admit|admit|admit| | |];
        hauto lq: on).
        intro.
        apply H7.
       }
      Print grel_seq.

      all: try naive_solver.
      all: unfold seq_state_to_cd in *.
      all: admit.

    unfold grel_acyclic.



      1: set_unfold.
      1: set_unfold.
      cdestruct H2.
      eapply (H2 _ _ _ _ _ _).
      eapply H2.


      opose proof (event_list_monotone _ evs0).
      2: { autorewrite with pair in *. set_solver. }

      2: best.
      set_unfold.

    unfold construct_cd_for_pe.
      rewrite seq_state_to_pe_trace_cons.
      erewrite seq_state_to_pe_eq.
      2: eapply sequential_model_outcome_same_initSt; eauto.
      2: eapply sequential_model_outcome_same_itrs; eauto.
      2,3:
  destruct seq_inv_predicate.



Definition construct_cd_fold_inv_step (l : list (EID.t * (fEvent outcome)))
    (I : partial_cd_state
        → list (EID.t * (fEvent outcome)) → list (EID.t * (fEvent outcome))
        → Prop)
    : Prop :=
  (∀ (cdst : partial_cd_state) (x : EID.t * (fEvent outcome)) (unproc proc : list (EID.t * (fEvent outcome))),
      x ∈ l → x ∉ proc → x ∉ unproc → l = rev proc ++ x :: unproc
      → I cdst (x :: unproc) proc → I (update_partial_cd_state_for_eid_ev cdst x) unproc (x :: proc)).


Lemma op_model_cd_ind_step seqst cdst call (P : partial_cd_state → Prop) :
  P (seq_partial_cd_states_to_partial_cd_state seqst cdst) →
  ∀ rseqst' ∈ Exec.to_state_result_list (sequential_model_outcome_logged regs_whitelist (Z.to_N (bv_modulus 52)) call seqst),
  ∀ seqst', rseqst' = Ok seqst' →
  construct_cd_fold_inv_step (Candidate.event_list (seq_state_to_pe seqst')) (λ cdst unproc proc, P cdst) →
  P (seq_partial_cd_states_to_partial_cd_state seqst' cdst).
Proof.
  cdestruct |- *** as HP seqst' r Hseqst' Hfold.
  unfold sequential_model_outcome_logged, fHandler_logger, construct_cd_fold_inv_step in *.
  cdestruct seqst', Hseqst' |- ***.
  unfold seq_partial_cd_states_to_partial_cd_state, construct_cd_for_pe in *.
  opose proof (seq_state_to_pe_eq (set itrs (trace_cons (call &→ r)) x) (set itrs (trace_cons (call &→ r)) seqst) _ _); cbn.
  1: eapply sequential_model_outcome_same_initSt; eauto.
  1: f_equal; eapply sequential_model_outcome_same_itrs; eauto.
  rewrite H0 in *.
  rewrite seq_state_to_pe_trace_cons in *.
  unfold seq_state_to_pe in *.
  cbv [set] in *; cbn in *.
  unfold Setter_compose in *; cbn in *.
  rewrite trace_snoc_event_list in *.
  rewrite fold_left_app.
  (* unfold intra_trace_eid_succ.
  destruct unsnoc_total as [? []] eqn: ?H. *)
  cbn in *.
  eapply (Hfold _ _ [] (rev (Candidate.event_list {| Candidate.init := initSt seqst; Candidate.events := [#trace_rev (itrs seqst)] |}))).
  1,3: set_solver.
  1: admit.
  1: by erewrite rev_involutive.
  eapply HP.
Admitted.

Lemma construct_cd_fold_eids_montone (pe : Candidate.pre Candidate.NMS 1) :
  construct_cd_fold_inv_step (Candidate.event_list pe)
    (λ cdst unproc proc, ∀ '(eid1, ev1) ∈ proc, ∀ '(eid2, ev2) ∈ unproc, EID.full_po_lt eid1 eid2).
Proof.
  unfold construct_cd_fold_inv_step.
  cdestruct |- *** as ???????? Hel IH ?? [|] ???.
  - replace (rev proc ++ (t, f) :: unproc) with ((rev proc ++ [(t, f)]) ++ unproc) in Hel.
    2: rewrite <- app_assoc; naive_solver.
    opose proof (event_list_monotone _ _ _ Hel (t0, f0) _ (t1,f1) _).
    1,2: set_solver.
    eapply H3.
    admit.
  - opose proof (event_list_monotone _ _ _ Hel (t0, f0) _ (t1,f1) _).
    1,2: set_solver.
    eapply H3.
    admit.
Admitted.

Definition mem_reg_maps_wf cdst (unproc proc : list (EID.t * (fEvent outcome))) : Prop :=
  ∀ pa reg eid,
  cdst.(pa_write_map) !! pa = Some eid ∨ cdst.(reg_write_map) !! reg = Some eid
  → eid ∈ proc.*1.

Lemma construct_cd_fold_maps_wf (pe : Candidate.pre Candidate.NMS 1) :
  construct_cd_fold_inv_step (Candidate.event_list pe) mem_reg_maps_wf.
Proof.
  unfold construct_cd_fold_inv_step, mem_reg_maps_wf.
  cdestruct |- *** as cdst eid [] ?????? Heid ?? eid' Heid'.
  set_unfold in Heid.
  destruct fcall; unfold update_partial_cd_state_for_eid_ev in Heid';
  unfold reg_read_upd_partial_cd_state, reg_write_upd_partial_cd_state, mem_read_upd_partial_cd_state, mem_write_upd_partial_cd_state in *;
  try solve [right; eapply Heid; by cdestruct Heid' #CDestrMatch].
  - destruct (decide (reg1 = reg0)) as [->|].
    1: left; admit.
    right.
    eapply Heid.
    admit.
  - destruct fret; cdestruct Heid' #CDestrMatch.
    1,2: left; admit.
    right.
    eapply Heid.
    eauto.
Admitted.

Lemma construct_cd_fold_inv_step_strengthening l I1 I2 :
  construct_cd_fold_inv_step l I1 →
  construct_cd_fold_inv_step l (λ cdst unproc proc, I1 cdst unproc proc ∧ I2 cdst unproc proc) →
  construct_cd_fold_inv_step l I2.
Proof.
  unfold construct_cd_fold_inv_step.
  cdestruct |- *** as HI1 HI12 ??????????.
  eapply HI12.
  1,2,3,4: assumption.
  split; last easy.
  eapply HI1.
  try naive_solver.


Lemma op_model_cd_monotone seqst call :
  cd_monotone (seq_partial_cd_states_to_cd seqst cd∅) →
  ∀ seqst' ∈ Exec.to_state_result_list (sequential_model_outcome_logged regs_whitelist (Z.to_N (bv_modulus 52)) call seqst),
  is_Ok seqst' → cd_monotone (seq_partial_cd_states_to_cd (result_same_type_proj seqst') cd∅).
Proof.
  cdestruct |- *** as Hmono seqst' r Hseqst'.
  unfold seq_partial_cd_states_to_cd.
  enough (cd_monotone
  (partial_cd_state_to_cd (construct_cd_for_pe (seq_state_to_pe seqst') cd∅) (seq_state_to_pe seqst')) ∧ mem_reg_maps_wf )
  pattern (construct_cd_for_pe (seq_state_to_pe seqst') cd∅).
  enoug
  pose proof op_model_cd_ind_step.
  unfold seq_partial_cd_states_to_partial_cd_state in H.
  eapply H.
  1: eapply Hmono.
  2: eauto.
  1: instantiate (1 := call).
  1: set_solver.
  enough
  (construct_cd_fold_inv_step (Candidate.event_list (seq_state_to_pe seqst'))
    (λ (cdst : partial_cd_state) (unproc proc : list (EID.t * fEvent outcome)),
      cd_monotone (partial_cd_state_to_cd cdst (seq_state_to_pe seqst')) ∧
      mem_reg_maps_wf cdst unproc proc)).
  {
    unfold construct_cd_fold_inv_step, mem_reg_maps_wf in *.
    cdestruct H0 |- ***.
    eapply H0.
    4: eassumption.
    1,2,3: set_solver.
    split; first assumption.
    revert H4.

    opose proof construct_cd_fold_maps_wf.
    5: intros; eapply H6.
    5: split; first assumption; intros; eapply construct_cd_fold_maps_wf.

    7: { }

  }

  1,2,3: set_solver.
  1: unfold partial_cd_state_to_cd in *. 1: naive_solver.
  unfold construct_cd_fold_inv_step.
  cdestruct |- *** as cdst eid [] ???????.
  unfold cd_monotone in H4 |- *.
  eapply construct_cd_fold_inv_step.
  unfold sequential_model_outcome_logged, fHandler_logger in *.
  cdestruct seqst', Hseqst' |- ***.
  unfold seq_partial_cd_states_to_cd, construct_cd_for_pe in *.
  repeat orewrite (seq_state_to_pe_eq _ (set itrs (trace_cons (call &→ r)) seqst)); cbn.
  2: eapply sequential_model_outcome_same_initSt; eauto.
  2: f_equal; eapply sequential_model_outcome_same_itrs; eauto.
  rewrite seq_state_to_pe_trace_cons.
  unfold seq_state_to_pe in *.
  cbv [set]; cbn.
  unfold Setter_compose; cbn.
  rewrite trace_snoc_event_list.
  rewrite fold_left_app.
  destruct unsnoc_total as [? []] eqn: ?H.
  cbn.
  generalize dependent (trace_rev (itrs seqst)).
  intros.
  fold_left_inv_complete_ND_pose
    (λ (cdst : partial_cd_state) (unpro pro : list (EID.t * (fEvent outcome))),
      ∀ 'memeid ∈ cdst.(pa_write_map),
      ∀ 'regeid ∈ cdst.(reg_write_map),
      let hdeid := (hd (EID.make 0 0 0 None) (fst <$> pro)) in
      (memeid = hdeid ∨ EID.full_po_lt memeid hdeid) ∧ (regeid = hdeid ∨ EID.full_po_lt regeid hdeid)).
  all: cdestruct |- ***.
  1: admit.
  1:{
    rewrite cons_middle in *.
    epose proof (event_list_monotone _ _ _ H2 (_,_) _ (_,_)).
    2: admit.
    1: cbn; right; eauto.
  }
  cbn in *.
  .
  fold_left_inv_complete_pose (λ (cdst : partial_cd_state) (unpro pro : list (EID.t * (fEvent outcome))), True). (λ cdst unpro pro, ∀ '(eid1,ev1) ∈ pro, ∀ '(eid2,ev2) ∈ unpro, EID.full_po_lt eid1 eid2).

  unfold iEvent.
  generalize dependent (fold_left update_partial_cd_state_for_eid_ev
  (Candidate.event_list (et := Candidate.NMS) {| Candidate.init := initSt seqst; Candidate.events := [#l1] |}) cdst).
  intros.
  cbn.
  destruct call; unfold update_partial_cd_state_for_eid_ev at 1; cbn; cdestruct |- ***.
  - unfold reg_read_upd_partial_cd_state.
    cdestruct |- *** #CDestrMatch.
  unfold cd_monotone in *.
  Search (_ ++ [_] ++ _).
  cdestruct Hmono |- ***.
  fold_left_inv_pose (λ cdst (evs : list (EID.t * fEvent outcome)), partial_cd_state_monotone cdst) as H_inv.
  3: { cdestruct H_inv |- ***. }
  - unfold cd_monotone, seq_partial_cd_states_to_cd in H.
    unfold
  }

  cdestruct H_inv |- ***.
  1: unfold cd_monotone, partial_cd_state_monotone, construct_cd_for_pe in *; cdestruct H |- ***.
  1:

  1,2: admit.

  unfold partial_cd_state_to_cd.
  pattern ((fold_left update_partial_cd_state_for_eid_ev (Candidate.event_list (seq_state_to_pe x)) cdst)).

  eapply fold_left_inv.
  intros.
  destruct call;
  cdestruct |- ***. *)

Lemma op_model_to_cd seqst cdst call :
  op_mem_wf (Ok seqst) →
  let rwl := if regs_whitelist is Some rwl then rwl else ∅ in
  consistent rwl (seq_partial_cd_states_to_cd seqst cdst) →
  ∀ seqst' ∈ Exec.to_state_result_list (sequential_model_outcome_logged regs_whitelist (Z.to_N (bv_modulus 52)) call seqst),
  is_Ok seqst' → consistent rwl (seq_partial_cd_states_to_cd (result_same_type_proj seqst') cdst).
Proof.
  cdestruct |- *** as ?? seqst' r Hseqst'.
  unfold sequential_model_outcome_logged, fHandler_logger in *.
  cdestruct seqst', Hseqst' |- ***.
  unfold seq_partial_cd_states_to_cd, construct_cd_for_pe in *.
  repeat orewrite (seq_state_to_pe_eq _ (set itrs (trace_cons (call &→ r)) seqst)); cbn.
  2: eapply sequential_model_outcome_same_initSt; eauto.
  2: f_equal; eapply sequential_model_outcome_same_itrs; eauto.
  rewrite seq_state_to_pe_trace_cons.
  unfold seq_state_to_pe in *.
  cbv [set]; cbn -[Candidate.event_list].
  unfold Setter_compose; cbn -[Candidate.event_list].
  rewrite trace_snoc_event_list.
  rewrite fold_left_app.
  destruct unsnoc_total as [? []] eqn: ?H.
  cbn [fold_left].
  constructor.
  destruct call; cbn -[Candidate.event_list] in *.
unfold update_partial_cd_state_for_eid_ev.
  cdestruct |- ***.
  rewrite trace_snoc_event_list.

  Set Printing Implicit.
  pattern (fold_left update_partial_cd_state_for_eid_ev
  (Candidate.event_list (et := Candidate.NMS)
     {|
       Candidate.init := initSt seqst;
       Candidate.events := [#trace_snoc (call &→ r) (trace_rev (itrs seqst))]
     |}) cdst).

  eapply fold_left_inv.
  constructor.
  - destruct H as [? _ _ _ _ _ _ _].

  unfold partial_cd_state_to_cd in *.
  unfold Setter_compose; cbn -[Candidate.event_list].
  unfold seq_state_to_pe in *.
  cbn -[Candidate.event_list] in *.

  pattern (@fold_left partial_cd_state _ update_partial_cd_state_for_eid_ev
  (@Candidate.iEvent_list Candidate.NMS 1
     (seq_state_to_pe
        (@set seq_state (list (iTrace ())) itrs
           (λ (f : list (iTrace ()) → list (iTrace ())) (x0 : seq_state),
              {| initSt := initSt x0; mem := mem x0; regs := regs x0; itrs := f (itrs x0) |}) (trace_cons (call &→ r)) x))) cdst).
  unfold seq_state_to_pe. cbn.
  eapply fold_left_inv_complete_list.
  Set Printing Implicit.
  partial_cd_state_to_cd.

  constructor.



End Proof.
