From ASCommon Require Import Options.
Require Import ArmSeqModel UMSeqArm.
Require Import ArmInst.
From ASCommon Require Import Exec FMon Common GRel StateT.
From ArchSem Require Import FromSail.

#[local] Typeclasses Transparent Decision RelDecision eq_vec_dec Decidable_eq_mword
MachineWord.MachineWord.eq_dec
    decide decide_rel.
(* Temporary *)

Import CDestrUnfoldElemOf.
#[local] Existing Instance Exec.unfold.

#[local] Typeclasses Transparent pa_eq pa_countable.

Definition max_mem_acc_size : Z := bv_modulus 52.

Lemma pa_addZ_max_mem_acc_size_neq pa z :
  (0 < z < max_mem_acc_size)%Z →
  pa_addZ pa z ≠ pa.
Proof.
  unfold SA.pa, mword, pa_addZ, max_mem_acc_size in *; cbn in *.
  intros.
  bv_simplify'.
  unfold bv_wrap.
  destruct pa.
  unfold definitions.bv_unsigned, BvWf in *.
  eapply andb_True in bv_is_wf.
  destruct bv_is_wf as [?%Is_true_eq_true%Reflect.Z_leb_le ?%Is_true_eq_true%Reflect.Z_ltb_lt].
  assert (0 < z < bv_modulus 56)%Z by (unfold bv_modulus in *; lia); clear H.
  assert ((bv_unsigned + z < bv_modulus 56)%Z ∨ (bv_modulus 56 ≤ bv_unsigned + z)%Z) as [|] by lia.
  { setoid_rewrite Z.mod_small at 1 2; try lia. }
  assert ((bv_unsigned + z)%Z = ((bv_unsigned + z - bv_modulus 56) + 1 * bv_modulus 56)%Z) as -> by lia.
  rewrite Z_mod_plus_full.
  setoid_rewrite Z.mod_small at 1 2; lia.
Qed.

Lemma pa_addZ_lt_max_mem_acc_size_inj pa x y :
  (0 ≤ x < max_mem_acc_size)%Z → (0 ≤ y < max_mem_acc_size)%Z →
  pa_addZ pa x = pa_addZ pa y ↔ x = y.
Proof.
  cdestruct |- *** #CDestrSplitGoal.
  - unfold SA.pa, mword, pa_addZ, max_mem_acc_size in *; cbn in *.
    assert (x < bv_modulus 56)%Z by (unfold bv_modulus in *; lia); clear H0;
    assert (y < bv_modulus 56)%Z by (unfold bv_modulus in *; lia); clear H2.
    bv_simplify'.
    destruct pa.
    unfold bv_wrap in *.
    unfold definitions.bv_unsigned, BvWf in *.
    eapply andb_True in bv_is_wf.
    destruct bv_is_wf as [?%Is_true_eq_true%Reflect.Z_leb_le ?%Is_true_eq_true%Reflect.Z_ltb_lt].
    assert (∀ x, (bv_unsigned + x)%Z = ((bv_unsigned + x - bv_modulus 56) + 1 * bv_modulus 56)%Z) by lia.
    assert ((bv_unsigned + x < bv_modulus 56)%Z ∨ (bv_modulus 56 ≤ bv_unsigned + x)%Z) as [|] by lia;
    assert ((bv_unsigned + y < bv_modulus 56)%Z ∨ (bv_modulus 56 ≤ bv_unsigned + y)%Z) as [|] by lia.
    { setoid_rewrite Z.mod_small in H3 at 1 2; try lia. }
    {
      setoid_rewrite Z.mod_small in H3 at 1; try lia.
      setoid_rewrite H6 in H3 at 2.
      rewrite Z_mod_plus_full, Z.mod_small in *.
      all: lia.
    }
        {
      setoid_rewrite Z.mod_small in H3 at 2; try lia.
      setoid_rewrite H6 in H3 at 1.
      rewrite Z_mod_plus_full, Z.mod_small in *.
      all: lia.
    }
    {
      setoid_rewrite H6 in H3 at 1 2; try lia.
      rewrite ?Z_mod_plus_full, ?Z.mod_small in *.
      all: lia.
    }
  - opose proof (f_equal_pa_addN pa (Z.to_N x) (Z.to_N y) _).
    1: lia.
    unfold pa_addN in *.
    do 2 erewrite Z2N.id in *; try lia.
    done.
Qed.

Lemma pa_addZ_exists_offset pa1 pa2 x y :
  (0 ≤ x)%Z → (0 ≤ y)%Z →
  pa_addZ pa1 x = pa_addZ pa2 y →
  ∃ o, (0 ≤ o)%Z ∧ (pa_addZ pa1 o = pa2 ∧ (o ≤ x)%Z ∨ pa_addZ pa2 o = pa1 ∧ (o ≤ y)%Z).
Proof.
  cdestruct |- ***.
  destruct (Ztrichotomy (x `mod` bv_modulus 56)%Z (y `mod` bv_modulus 56)%Z) as [|[|]].
  2: {
    eexists 0%Z.
    setoid_rewrite pa_addN_zero.
    cdestruct |- *** #CDestrSplitGoal; try done; left; split; last done.
    unfold SA.pa, mword, pa_addZ, max_mem_acc_size in *; cbn in *.
    bv_simplify'.
    destruct pa1, pa2.
    unfold bv_wrap, definitions.bv_unsigned, BvWf in *.
    eapply andb_True in bv_is_wf, bv_is_wf0.
    destruct bv_is_wf as [?%Is_true_eq_true%Reflect.Z_leb_le ?%Is_true_eq_true%Reflect.Z_ltb_lt].
    destruct bv_is_wf0 as [?%Is_true_eq_true%Reflect.Z_leb_le ?%Is_true_eq_true%Reflect.Z_ltb_lt].
    f_equal.
    setoid_rewrite <- Z.add_mod_idemp_r in H1 at 1 2.
    2,3: lia.
    rewrite H2 in *.
    clear dependent x.
    assert (0%Z ≤ (y `mod` bv_modulus 56)%Z < bv_modulus 56)%Z by lia.
    generalize dependent (y `mod` bv_modulus 56)%Z; clear dependent y.
    cdestruct |- ***.
    assert (∀ x, (bv_unsigned + x)%Z = ((bv_unsigned + x - bv_modulus 56) + 1 * bv_modulus 56)%Z) by lia.
    assert (∀ x, (bv_unsigned0 + x)%Z = ((bv_unsigned0 + x - bv_modulus 56) + 1 * bv_modulus 56)%Z) by lia.
    assert ((bv_unsigned + z < bv_modulus 56)%Z ∨ (bv_modulus 56 ≤ bv_unsigned + z)%Z) as [|] by lia;
    assert ((bv_unsigned0 + z < bv_modulus 56)%Z ∨ (bv_modulus 56 ≤ bv_unsigned0 + z)%Z) as [|] by lia.
    - setoid_rewrite Z.mod_small in H1; lia.
    - setoid_rewrite Z.mod_small in H1 at 1; try lia;
      setoid_rewrite H7 in H1;
      rewrite ?Z_mod_plus_full, ?Z.mod_small in *; try lia.
    - setoid_rewrite Z.mod_small in H1 at 2; try lia.
      setoid_rewrite H2 in H1.
      rewrite ?Z_mod_plus_full, ?Z.mod_small in *; try lia.
    - setoid_rewrite H2 in H1; setoid_rewrite H7 in H1.
      rewrite ?Z_mod_plus_full, ?Z.mod_small in *; try lia.
  }
  1: exists ((y - x) `mod` bv_modulus 56)%Z.
  2: exists ((x - y) `mod` bv_modulus 56)%Z.
  all: unfold SA.pa, mword, pa_addZ, max_mem_acc_size in *; cbn in *.
  all: split.
  all: assert (0 ≤ x `mod` bv_modulus 56 < bv_modulus 56)%Z by (unfold bv_modulus in *; lia).
  all: assert (0 ≤ y `mod` bv_modulus 56 < bv_modulus 56)%Z by (unfold bv_modulus in *; lia).
  all: rewrite Zminus_mod in *.
  1,3: lia.
  1: right.
  2: left.
  all: split.
  2,4: unfold bv_modulus in *; lia.
  all: bv_simplify'.
  all: destruct pa1, pa2.
  all: unfold bv_wrap, definitions.bv_unsigned, BvWf in *.
  all: setoid_rewrite <- Zplus_mod_idemp_r in H1.
  all: generalize dependent (x `mod` bv_modulus 56)%Z;
    generalize dependent (y `mod` bv_modulus 56)%Z.
  all: clear dependent x y.
  all: cdestruct |- *** as y ?? x ???? #CDestrSplitGoal.
  all: setoid_rewrite Zplus_mod_idemp_r.
  all: eapply andb_True in bv_is_wf, bv_is_wf0.
  all: destruct bv_is_wf as [?%Is_true_eq_true%Reflect.Z_leb_le ?%Is_true_eq_true%Reflect.Z_ltb_lt].
  all: destruct bv_is_wf0 as [?%Is_true_eq_true%Reflect.Z_leb_le ?%Is_true_eq_true%Reflect.Z_ltb_lt].
  all: assert (∀ x, (bv_unsigned + x)%Z = ((bv_unsigned + x - bv_modulus 56) + 1 * bv_modulus 56)%Z) by lia.
  all: assert (∀ x, (bv_unsigned0 + x)%Z = ((bv_unsigned0 + x - bv_modulus 56) + 1 * bv_modulus 56)%Z) by lia.
  all: assert ((bv_unsigned + x < bv_modulus 56)%Z ∨ (bv_modulus 56 ≤ bv_unsigned + x)%Z) as [|] by lia;
    assert ((bv_unsigned0 + y < bv_modulus 56)%Z ∨ (bv_modulus 56 ≤ bv_unsigned0 + y)%Z) as [|] by lia.
  all: try solve [rewrite ?Z.mod_small in *; try lia].
  all: try solve [rewrite H10, ?Z_mod_plus_full, ?Z.mod_small in H1; try lia;
        rewrite H10, ?Z_mod_plus_full, ?Z.mod_small; try lia].
  all: try solve [rewrite H9, ?Z_mod_plus_full, ?Z.mod_small in H1; try lia;
        rewrite H9, ?Z_mod_plus_full, ?Z.mod_small; try lia].
  all: rewrite H9, H10, ?Z_mod_plus_full, ?Z.mod_small in H1; try lia.
  all: apply Z.sub_cancel_r in H1.
  all: f_equal.
  all: lia.
Qed.

Opaque max_mem_acc_size.

(** Get the size out of a memory call *)
Definition outcome_get_size (call : outcome) : option N :=
  match call with
  | MemRead n _ => Some n
  | MemWriteAddrAnnounce n _ _ _ => Some n
  | MemWrite n _ => Some n
  | _ => None
  end.

Definition legal_memory_acc (call : outcome) : Prop :=
  if outcome_get_size call is Some size
  then (0 < size < Z.to_N max_mem_acc_size)%N
  else True.

Definition legal_memory_acc_ev (ev : iEvent) : Prop :=
  if get_size ev is Some size
  then (0 < size < Z.to_N max_mem_acc_size)%N
  else True.

Lemma legal_memory_acc_legal_memory_acc_ev ev :
  legal_memory_acc_ev ev ↔ legal_memory_acc ev.(fcall).
Proof. destruct ev; cdestruct |- *** #CDestrSplitGoal. Qed.

Inductive fMon_call_inv {A} `{Effect Eff} (P : Eff → Prop) : fMon Eff A → Prop :=
  | finvPRet : ∀ a, fMon_call_inv P (Ret a)
  | finvPNext : ∀ (call : Eff) k,
    P call →
    (∀ (ret : eff_ret call), fMon_call_inv P (k ret)) →
    fMon_call_inv P (Next call k).

Inductive cMon_call_inv {A} `{Effect Eff} (P : Eff → Prop) : cMon Eff A → Prop :=
  | cinvPRet : ∀ a, cMon_call_inv P (Ret a)
  | cinvPNextEff : ∀ (call : Eff) k,
    P call →
    (∀ (ret : eff_ret (inl call)), cMon_call_inv P (k ret)) →
    cMon_call_inv P (Next (inl call) k)
  | cinvnmsNextChoice : ∀ (c : MChoice) k,
    (∀ (ret : eff_ret (inr c)), cMon_call_inv P (k ret)) →
    cMon_call_inv P (Next (inr c) k).

Lemma cMon_to_fMon_call_inv {A} `{Effect Eff} (P : Eff → Prop) (c : cMon Eff A) :
  cMon_call_inv P c ↔ fMon_call_inv (λ s, if s is inl eff then P eff else True) c.
Proof.
  induction c.
  1: cdestruct |- *** as Ho #CDestrSplitGoal; depelim Ho; constructor.
  cdestruct |- *** as Ho #CDestrSplitGoal.
  2: destruct call.
  all: depelim Ho.
  all: constructor; try fast_done.
  all: cdestruct |- ***.
  all: by eapply H0.
Qed.

Definition isem_mem_acc_legal_length : iMon () → Prop :=
  cMon_call_inv legal_memory_acc.

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

Lemma finterp_all_states_inv_induct `{Effect Eff} {St E A}
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

Lemma finterp_inv_induct `{Effect Eff} {St E A}
    (handler : fHandler Eff (Exec.t St E)) (mon : fMon Eff A)
    (I : St → Prop) (Ieff : Eff → Prop) (initSt : St) :
  fMon_call_inv Ieff mon →
  I initSt →
  (∀ st call, I st → Ieff call → ∀ st' ret, (st',ret) ∈ handler call st → I st') →
  ∀ st' ret, (st',ret) ∈ FMon.finterp handler mon initSt → I st'.
Proof.
  intros Hmon Hinit Hstep.
  induction mon as [|? ? IH] in Hmon, initSt, Hinit |- *;
  cdestruct |- *** #CDestrMatch.
  set_unfold.
  depelim Hmon.
  eapply IH.
  2: eapply Hstep.
  all: eauto.
Qed.

Lemma finterp_inv_induct_backwards `{Effect Eff} {St E A}
    (handler : fHandler Eff (Exec.t St E)) (mon : fMon Eff A)
    (I : St → Prop) (Ieff : Eff → Prop) (initSt : St) :
  fMon_call_inv Ieff mon →
  (∀ st st' call ret, I st' → Ieff call → (st',ret) ∈ handler call st → I st) →
  ∀ st' ret, I st' → (st',ret) ∈ FMon.finterp handler mon initSt → I initSt.
Proof.
  intros Hmon H_step.
  induction mon as [|? ? IH] in Hmon, initSt |- *;
  cdestruct |- *** #CDestrMatch.
  set_unfold.
  depelim Hmon.
  eapply H_step.
  2,3: eauto.
  eapply IH; eauto.
Qed.

Arguments Exec.to_state_result_list : simpl never.

Lemma cinterp_all_states_inv_induct `{Effect Eff} {St E A}
  (handler : fHandler Eff (Exec.t St E)) (mon : cMon Eff A)
  (I : result St St → Prop) (Ieff : Eff → Prop) (initSt : St) : I (Ok initSt)
    → (∀ st call, I (Ok st) → ∀ st' ∈ Exec.to_state_result_list $ handler call st, I st')
    → ∀ st' ∈ (Exec.to_state_result_list $ FMon.cinterp handler mon initSt), I st'.
Proof.
  intros Hinit HIpreserve st' Hst'.
  eapply finterp_all_states_inv_induct; [eassumption | | eassumption].
  clear initSt Hinit st' Hst'.
  cdestruct |- *** as st eff Hst st' v Hst' #CDestrMatch #CDestrSplitGoal;
  try destruct eff;
  set_solver.
Qed.

Lemma cinterp_inv_induct `{Effect Eff} {St E A}
    (handler : fHandler Eff (Exec.t St E)) (mon : cMon Eff A)
    (I : St → Prop) (Ieff : Eff → Prop) (initSt : St) :
  cMon_call_inv Ieff mon →
  I initSt →
  (∀ st call, I st → Ieff call → ∀ st' ret, (st',ret) ∈ handler call st → I st') →
  ∀ st' ret, (st',ret) ∈ FMon.cinterp handler mon initSt → I st'.
Proof.
  intros Hmon Hinit HIpreserve st' ret Hst'.
  eapply finterp_inv_induct; [ | eassumption| | eassumption].
  1: eapply cMon_to_fMon_call_inv in Hmon.
  1: exact Hmon.
  clear initSt Hinit st' Hst'.
  cdestruct |- *** as st eff Hst st' v Hst' #CDestrMatch #CDestrSplitGoal;
  try destruct eff.
  eapply (HIpreserve _ eff); eauto.
Qed.

Lemma cinterp_inv_induct_backwards `{Effect Eff} {St E A}
    (handler : fHandler Eff (Exec.t St E)) (mon : cMon Eff A)
    (I : St → Prop) (Ieff : Eff → Prop) (initSt : St) :
  cMon_call_inv Ieff mon →
  (∀ st st' call ret, I st' → Ieff call → (st',ret) ∈ handler call st → I st) →
  ∀ st' ret, I st' → (st',ret) ∈ FMon.cinterp handler mon initSt → I initSt.
Proof.
  intros Hmon HIpreserve final_st ret Hfinalst H_exec.
  eapply finterp_inv_induct_backwards.
  1: by eapply cMon_to_fMon_call_inv in Hmon.
  2,3: eauto.
  clear -HIpreserve.
  cdestruct |- *** as st eff Hst st' v Hst' #CDestrMatch #CDestrSplitGoal;
  try destruct eff.
  eapply (HIpreserve _ eff); eauto.
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
    enough (pa' ≠ pa0)
    by (rewrite lookup_unfold; done).
    intros ->.
    eapply H0.
    eexists 0%N.
    rewrite pa_addN_zero.
    cdestruct |- *** #CDestrSplitGoal.
    destruct size; lia.
  - unfold not; cdestruct |- ***.
    cdestruct pa'.
    eapply H0.
    unfold pa_addN; rewrite pa_addZ_assoc.
    eexists (N.succ x); cdestruct |- *** #CDestrSplitGoal.
    1: f_equal; lia.
    lia.
Qed.

Lemma write_mem_seq_state_snoc l x pa st st' :
  (st', ()) ∈ write_mem_seq_state pa (l ++ [x]) st →
  mem st' !! pa_addN pa (N.of_nat (length l)) = Some x.
Proof.
  revert dependent pa st.
  elim l; cdestruct st' |- ***.
  1: rewrite pa_addN_zero; unfold Setter_finmap.
  1: by rewrite lookup_unfold.
  eapply H in H0.
  rewrite <- H0.
  unfold pa_addN.
  rewrite pa_addZ_assoc.
  do 2 f_equal.
  lia.
Qed.

Lemma write_mem_seq_state_app pa l st st' x :
  (Z.of_nat (S (length l)) < max_mem_acc_size)%Z →
  (st', ()) ∈ write_mem_seq_state pa (l ++ [x]) st →
  (st', ()) ∈ write_mem_seq_state pa l (setv ((.!! pa_addN pa (N.of_nat (length l))) ∘ mem) (Some x) st).
Proof.
  revert dependent pa st x.
  elim l; cdestruct st' |- *** #CDestrSplitGoal.
  1: rewrite pa_addN_zero; done.
  eexists _, (); cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  2: eapply H.
  2: lia.
  2: eapply H1.
  eexists _, _; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  destruct st; cbv [set setv].
  unfold Setter_compose.
  f_equal; cbn.
  unfold Setter_finmap, pa_addN.
  rewrite pa_addZ_assoc.
  erewrite partial_alter_commute.
  2: eapply pa_addZ_max_mem_acc_size_neq; lia.
  do 3 f_equal.
  lia.
Qed.

Lemma pa_in_range_write pa pa' size (v: bv (8*size)) st st' :
  (size < Z.to_N max_mem_acc_size)%N →
  (st', ()) ∈ write_mem_seq_state pa (bv_to_bytes 8 v) st →
  pa_in_range pa size pa' →
  ∃ offset, (offset < size)%N ∧ pa' = pa_addN pa offset ∧
    mem st' !! pa' = Some (bv_get_byte 8 offset v).
Proof.
  intros ???%pa_in_range_spec;
  deintros; cdestruct |- *** as pa i size v st st' Hsize Hw Hs.
  exists i.
  enough (mem st' !! pa_addN pa i = bv_to_bytes 8 v !! i) as ->
  by (setoid_rewrite bv_to_bytes_bv_get_byte; repeat apply conj; try done; lia).
  assert (length (bv_to_bytes 8 v) = N.to_nat size)
    by (rewrite length_bv_to_bytes, div_round_up_divisible; done).
  revert dependent pa st i.
  generalize dependent (bv_to_bytes 8 v).
  clear v.
  intro; revert dependent size.
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
    lia.
Qed.

Lemma write_mem_seq_state_same_itrs bytes :
  ∀ st st' pa, (st', ()) ∈ write_mem_seq_state pa bytes st → itrs st' = itrs st.
Proof.
  induction bytes; cdestruct |- ***.
  change (itrs st) with (itrs (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)).
  eapply IHbytes, H.
Qed.

Lemma write_mem_seq_state_regs_unchanged bytes :
  ∀ st st' pa, (st', ()) ∈ write_mem_seq_state pa bytes st → st'.(regs) = st.(regs).
Proof.
  induction bytes; cdestruct |- ***.
  change (regs st) with (regs (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)).
  eapply IHbytes, H.
Qed.

Section Proof.
Context (regs_whitelist : gset reg).

Lemma sequential_model_outcome_same_itrs st st' call r :
  (st', r) ∈ sequential_model_outcome (Some regs_whitelist) call st → itrs st' = itrs st.
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

Lemma sequential_model_outcome_same_initSt st st' call r :
  (st', r) ∈ sequential_model_outcome (Some regs_whitelist) call st → initSt st' = initSt st.
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
  (seq_st_succ, ret) ∈ sequential_model_outcome (Some regs_whitelist) call seq_st →
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

Definition seq_state_is_nms (st : seq_state) : Prop :=
  Candidate.is_nms (seq_state_to_pe st).

Definition cd_monotone (cd : Candidate.t Candidate.NMS 1) : Prop :=
  rel_strictly_monotone cd.(Candidate.reads_from)
  ∧ rel_strictly_monotone cd.(Candidate.reg_reads_from)
  ∧ rel_strictly_monotone cd.(Candidate.coherence).

Definition partial_cd_state_monotone (cdst : partial_cd_state) : Prop :=
  rel_strictly_monotone cdst.(rf_acc)
  ∧ rel_strictly_monotone cdst.(rrf_acc)
  ∧ rel_strictly_monotone cdst.(co_acc).

Arguments Candidate.event_list : simpl never.

Definition seq_model_outcome_invariant_preserved (I I' : seq_state → Prop) : Prop :=
  ∀ (seq_st : seq_state),
  I seq_st →
  ∀ (call : outcome) ret seq_st_succ,
  (seq_st_succ, ret) ∈ sequential_model_outcome (Some regs_whitelist) call seq_st →
  I' (set itrs (trace_cons (call &→ ret)) seq_st_succ).

  Definition seq_model_outcome_invariant_preserved_mem_assumptions (I I' : seq_state → Prop) : Prop :=
  ∀ (seq_st : seq_state),
  I seq_st →
  ∀ (call : outcome),
  legal_memory_acc call →
  ∀ ret seq_st_succ,
  seq_state_is_nms (set itrs (trace_cons (call &→ ret)) seq_st_succ) →
  (seq_st_succ, ret) ∈ sequential_model_outcome (Some regs_whitelist) call seq_st →
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

Definition seq_st_reg_map_consistentP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  ∀ (reg : Arch.reg) v,
      seq_st.(regs) !! reg = Some v
    ↔ ∃ ev eid T rv,
        cd !! eid = Some ev ∧
        is_reg_write ev ∧ get_reg ev = Some reg ∧
        get_reg_val ev = Some (existT T rv) ∧ regt_to_bv64 rv = v ∧
        (∀ eid' ev', cd !! eid' = Some ev' →
          is_reg_write ev' → get_reg ev' = Some reg →
          EID.full_po_lt eid' eid ∨ eid' = eid).

Definition seq_st_mem_map_is_SomeP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  ∀ pa,
    (∃ ev eid offset,
    cd !! eid = Some ev ∧
        is_mem_writeP
          (λ size wr, pa_addN wr.(WriteReq.pa) offset = pa ∧ (offset < size)%N) ev) →
    is_Some (seq_st.(mem) !! pa).

Definition mem_writes_succeedP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  let evs := Candidate.event_list cd in
  ∀ ev ∈ evs.*2, is_mem_write_req ev →
  is_mem_write_reqP (λ _ _ ret, if ret is inl b then b = true else False) ev.

Definition pcdst_mem_acc_legalP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  ∀ eid ev, cd !! eid = Some ev → legal_memory_acc_ev ev.

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
    EID.full_po_lt eid1 eid2 ∧
    ∀ other_eid ev', cd !! other_eid = Some ev' → is_mem_write ev' →
      get_pa ev' = get_pa ev2 →
      EID.full_po_lt other_eid eid1 ∨ other_eid = eid1 ∨ EID.full_po_lt eid2 other_eid.

Definition cdst_rrf_acc_invP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  let rrf := rrf_acc (seq_state_to_partial_cd_state seq_st) in
  ∀ eid1 eid2, (eid1, eid2) ∈ rrf ↔
  ∃ ev1 ev2, cd !! eid1 = Some ev1 ∧ cd !! eid2 = Some ev2 ∧
    is_reg_write ev1 ∧ is_reg_read ev2 ∧ get_reg ev1 = get_reg ev2 ∧
    EID.full_po_lt eid1 eid2 ∧
    ∀ other_eid ev', cd !! other_eid = Some ev' → is_reg_write ev' →
      get_reg ev' = get_reg ev2 →
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

Definition cdst_reg_reads_invP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  let rrf := rrf_acc (seq_state_to_partial_cd_state seq_st) in
  ∀ reid rev rreg rval, cd !! reid = Some rev →
    is_reg_read rev → get_reg rev = Some rreg → get_reg_val rev = Some (existT rreg rval) →
    (∃ weid, (weid, reid) ∈ rrf) ∨
      (¬ ∃ weid, (weid, reid) ∈ rrf)
      ∧ ((MState.regs seq_st.(initSt)) !!! 0%fin) rreg = rval.

Definition pcdst_reg_map_invP seq_st :=
  let pcdst := (seq_state_to_partial_cd_state seq_st) in
  let cd := (seq_state_to_cd seq_st) in
  ∀ eid reg, pcdst.(reg_write_map) !! reg = Some eid ↔
  ∃ ev, is_reg_writeP (λ reg' _ _, reg' = reg) ev ∧ cd !! eid = Some ev ∧
    (∀ eid' ev', cd !! eid' = Some ev' →
      is_reg_writeP (λ reg' _ _, reg' = reg) ev' →
      eid' = eid ∨ EID.full_po_lt eid' eid).

Definition seq_st_reg_map_is_SomeP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  ∀ reg,
    (∃ ev eid,
    cd !! eid = Some ev ∧ is_reg_write ev ∧ get_reg ev = Some reg) →
    is_Some (seq_st.(regs) !! reg).

Record seq_inv_predicate (seq_st : seq_state) := {
  pcdst := (seq_state_to_partial_cd_state seq_st);
  cd := (seq_state_to_cd seq_st);
  evs := Candidate.event_list cd;
  seq_st_mem_map_consistent : seq_st_mem_map_consistentP seq_st;
  seq_st_mem_map_is_Some : seq_st_mem_map_is_SomeP seq_st;
  seq_st_reg_map_consistent : seq_st_reg_map_consistentP seq_st;
  seq_st_reg_map_is_Some : seq_st_reg_map_is_SomeP seq_st;
  mem_writes_succeed : mem_writes_succeedP seq_st;
  pcdst_mem_acc_legal : pcdst_mem_acc_legalP seq_st;
  pcdst_mem_map_inv : pcdst_mem_map_invP seq_st;
  pcdst_mem_set_map_inv : pcdst_mem_set_map_invP seq_st;
  pcdst_reg_map_inv : pcdst_reg_map_invP seq_st;
  cdst_co_acc_inv : cdst_co_acc_invP seq_st;
  cdst_rf_acc_inv : cdst_rf_acc_invP seq_st;
  cdst_rrf_acc_inv : cdst_rrf_acc_invP seq_st;
  cdst_mem_reads_inv : cdst_mem_reads_invP seq_st;
  cdst_reg_reads_inv : cdst_reg_reads_invP seq_st;
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
  seq_model_outcome_invariant_preserved_mem_assumptions seq_inv_predicate seq_st_mem_map_consistentP.
Proof.
  unfold seq_model_outcome_invariant_preserved_mem_assumptions, seq_st_mem_map_consistentP.
  setoid_rewrite lookup_unfold.
  cbn.
  cdestruct |- *** as seqst H_inv call H_legalmem ret seqst_succ Hnms H_seqst_succ pa v.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
  rewrite Hsame_itrs in *.
  eapply seq_st_mem_map_consistent in H_inv.
  specialize (H_inv pa v).
  setoid_rewrite lookup_unfold in H_inv.
  destruct (decide (is_mem_write (call &→ ret))).
  - destruct call; unfold is_mem_writeP in *; try done.
    cdestruct ret, H_seqst_succ, H_legalmem.
    destruct (decide (pa_in_range (WriteReq.pa wr) n pa)).
    + opose proof (pa_in_range_write _ _ _ _ _ _ _ _ _) as [offset (? & ? & ->)]; eauto.
      cdestruct seqst_succ |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrSplitGoal #CDestrMatch #CDestrEqOpt.
      * eexists _, (intra_trace_eid_succ 0 (trace_rev (itrs seqst))), _.
        rewrite lookup_unfold.
        cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
          #CDestrSplitGoal #CDestrEqOpt #CDestrMatch; eauto.
        left.
        by eapply eid_full_po_lt_intra_trace_eid_succ.
      * exfalso.
        ospecialize (H10 (intra_trace_eid_succ 0 (trace_rev (itrs seqst))) _ _ _).
        1: rewrite lookup_unfold; done.
        1: cbn; eapply pa_in_range_spec; eauto.
        cdestruct x0 #CDestrSplitGoal #CDestrEqOpt.
      * cdestruct pa, v.
        f_equal.
        eapply pa_addZ_lt_max_mem_acc_size_inj in H6.
        all: try lia.
    + erewrite pa_not_in_range_write; eauto.
      2: erewrite length_bv_to_bytes, div_round_up_divisible; done.
      all: setoid_rewrite H_inv.
      all: cdestruct |- *** as size wr' b eid offset Htr H_wb H_otherw #CDestrSplitGoal.
      all: cdestruct Htr, H_wb |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
      3: exfalso; eapply n0, pa_in_range_spec; depelim H5;
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
Qed.

Lemma seq_model_seq_st_mem_map_is_Some_inv :
  seq_model_outcome_invariant_preserved_mem_assumptions seq_inv_predicate seq_st_mem_map_is_SomeP.
Proof.
  unfold seq_model_outcome_invariant_preserved_mem_assumptions, seq_st_mem_map_is_SomeP.
  setoid_rewrite lookup_unfold.
  cbn.
  cdestruct |- *** as seqst H_inv call H_legalmem ret seqst_succ Hnms
    H_seqst_succ size wr offset eid Hl Hsize
    #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
    cdestruct eid, Hl #CDestrMatch #CDestrEqOpt.
  - destruct call.
    all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrMatch.
    6: edestruct (decide (pa_in_range (WriteReq.pa wr0) n (pa_addN (WriteReq.pa wr) offset)))
        as [?%pa_in_range_write|?%pa_not_in_range_write]; eauto.
    6: cdestruct p |- *** #CDestrEqOpt; eauto.
    7: rewrite length_bv_to_bytes, div_round_up_divisible; try done.
    6: rewrite n0, Hsame_itrs in *.
    all: eapply (seq_st_mem_map_is_Some _ H_inv).
    all: setoid_rewrite lookup_unfold.
    all: unfold is_mem_writeP.
    all: eexists _, _, _.
    all: do 2 (cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt; eauto).
  - cdestruct call, ret |- ***.
    opose proof (pa_in_range_write (WriteReq.pa wr) (pa_addN (WriteReq.pa wr) offset) size _ _ _ _ _ _); eauto.
    1: eapply pa_in_range_spec; eauto.
    by cdestruct offset.
Qed.

Lemma seq_model_seq_st_reg_map_consistent_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate seq_st_reg_map_consistentP.
Proof.
  unfold seq_model_outcome_invariant_preserved, seq_st_reg_map_consistentP.
  setoid_rewrite lookup_unfold.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ reg v #CDestrEqOpt.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
  rewrite Hsame_itrs in *.
  eapply seq_st_reg_map_consistent in H_inv.
  specialize (H_inv reg v).
  destruct (decide (is_reg_write (call &→ ret))).
  - destruct call; try (unfold is_reg_writeP; done).
    cdestruct ret, seqst_succ |- *** #CDestrEqOpt.
    unfold Setter_finmap.
    setoid_rewrite lookup_unfold.
    cdestruct reg |- *** #CDestrMatch.
    + cdestruct |- *** #CDestrSplitGoal.
      * eexists _, (intra_trace_eid_succ 0 (trace_rev seqst.(itrs))), _, _.
        cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
        opose proof (EID.full_po_lt_connex (intra_trace_eid_succ 0 (trace_rev seqst.(itrs))) eid' _ _ _) as Hconnex.
        all: rewrite ?intra_trace_eid_succ_byte, ?intra_trace_eid_succ_tid.
        1-3: unfold lookup, lookup_ev_from_iTraces in *; cdestruct eid' |- *** #CDestrEqOpt.
        cdestruct eid', Hconnex |- *** #CDestrSplitGoal ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrMatch.
        all: try solve [left+right; cdestruct |- *** #CDestrEqOpt].
      * ospecialize (H3 (intra_trace_eid_succ 0 (trace_rev seqst.(itrs))) _ _ _ _);
          cdestruct |- *** #CDestrEqOpt.
        cdestruct x0, H3, v, H1 |- *** #CDestrSplitGoal #CDestrEqOpt.
        2: { naive_solver. }
        opose proof (EID.full_po_lt_connex (intra_trace_eid_succ 0 (trace_rev seqst.(itrs))) x0 _ _ _) as Hconnex.
        all: rewrite ?intra_trace_eid_succ_byte, ?intra_trace_eid_succ_tid.
        1-3: unfold lookup, lookup_ev_from_iTraces in *; cdestruct x0 |- *** #CDestrEqOpt.
        cdestruct x0, Hconnex |- *** #CDestrSplitGoal ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrMatch.
    + setoid_rewrite H_inv.
      cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch
        ##eq_some_unfold_lookup_eid_trace_rev_cons.
      1,2: eexists _, x0, _, _;
      cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      1,2: eapply H4; cdestruct eid' |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch
        ##eq_some_unfold_lookup_eid_trace_rev_cons.
      1: scongruence.
      1: done.
  - assert (seqst_succ.(regs) = seqst.(regs)) as Hregs.
    { destruct call; deintros; cdestruct |- *** #CDestrEqOpt #CDestrMatch.
      1: by unfold is_reg_writeP in *.
      eapply write_mem_seq_state_regs_unchanged; eauto. }
    rewrite Hregs.
    setoid_rewrite H_inv.
    cdestruct call |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch
        ##eq_some_unfold_lookup_eid_trace_rev_cons.
      1,2: eexists _, x0, _, _;
      cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      1,2: eapply H1; cdestruct eid' |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch
        ##eq_some_unfold_lookup_eid_trace_rev_cons.
      1,2: unfold is_reg_writeP in *; deintros; cdestruct |- ***; done.
Qed.

Lemma seq_model_seq_st_reg_map_is_Some_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate seq_st_reg_map_is_SomeP.
Proof.
  unfold seq_model_outcome_invariant_preserved, seq_st_reg_map_is_SomeP.
  setoid_rewrite lookup_unfold.
  cdestruct |- *** as seqst H_inv call ret seqst_succ
    H_seqst_succ reg racc eid val
    #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
    cdestruct eid |- *** #CDestrMatch #CDestrEqOpt.
  - destruct call.
    all: deintros; cdestruct |- *** #CDestrEqOpt #CDestrMatch.
    2: unfold Setter_finmap; rewrite lookup_unfold; cdestruct |- *** #CDestrMatch.
    6: erewrite write_mem_seq_state_regs_unchanged in *; eauto.
    all: eapply (seq_st_reg_map_is_Some _ H_inv).
    all: setoid_rewrite lookup_unfold.
    all: unfold is_reg_writeP.
    all: eexists _, _.
    all: do 2 (cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt; eauto).
    1: rewrite Hsame_itrs in *; eauto.
    all: hauto l: on.
  - cdestruct call, ret, seqst_succ |- ***.
    unfold Setter_finmap.
    by rewrite lookup_unfold.
Qed.

Lemma seq_model_mem_writes_succeed_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate mem_writes_succeedP.
Proof.
  unfold seq_model_outcome_invariant_preserved, mem_writes_succeedP, sequential_model_outcome_logged, fHandler_logger, build_pre_exec.
  cdestruct |- *** as seqst H_inv call seqst_succ ret H_seqst_succ n wr wret eid H_eid.
  rewrite lookup_unfold in *.
  eapply mem_writes_succeed in H_inv.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
  rewrite Hsame_itrs in *.
  cbn in *.
  cdestruct H_eid ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch #CDestrEqOpt.
  2: cdestruct call, ret; scongruence.
  ospecialize (H_inv (MemWrite n wr &→ wret) _ _).
  { cdestruct |- ***. eexists (eid, _). cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal. }
  all: naive_solver.
Qed.

Lemma seq_model_mem_accesses_legal_inv :
  seq_model_outcome_invariant_preserved_mem_assumptions seq_inv_predicate pcdst_mem_acc_legalP.
Proof.
  unfold seq_model_outcome_invariant_preserved_mem_assumptions, pcdst_mem_acc_legalP.
  cdestruct |- *** as seqst H_inv call H_legalmem ret seqst_succ Hnms
    H_seqst_succ eid ev Htr #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons
    #CDestrMatch.
  eapply (pcdst_mem_acc_legal _ H_inv eid).
  cdestruct |- *** #CDestrEqOpt.
  by rewrite (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) in *.
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
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
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
      ospecialize (H4 (intra_trace_eid_succ 0 (trace_rev (itrs seq_st))) _ _ _ _).
      1: by rewrite lookup_unfold.
      1,2: done.
      cdestruct eid, H4 |- *** #CDestrSplitGoal #CDestrEqOpt.
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
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _) as ->; eauto.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _) as ->; eauto.
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
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _) as ->; eauto.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _) as ->; eauto.
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
    cdestruct |- *** as #CDestrMatch.
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
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _) as H_same_itrs; eauto.
  setoid_rewrite H_same_itrs in H_mem_map; rewrite H_same_itrs; clear H_same_itrs.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _) as ->; eauto.
  opose proof (cdst_rf_acc_inv _ H_inv eid1 eid2) as H_base.
  setoid_rewrite lookup_unfold in H_base.
  destruct (decide (is_mem_read (call &→ ret) ∧
    eid2 = intra_trace_eid_succ 0 (trace_rev (itrs seqst)))) as [|H_call].
  - eapply seq_state_to_partial_cd_state_destruct.
    all: cdestruct call |- *** as.
    1: by unfold is_mem_readP in *.
    cdestruct eid2 |- *** as size wr val ? H_step ???.
    set_unfold.
    cdestruct |- *** #CDestrMatch #CDestrEqOpt.
    2: {
      opose proof (pcdst_mem_map_inv _ H_inv).
      cdestruct H_step |- *** #CDestrMatch #CDestrEqOpt.
      setoid_rewrite H_base; clear H_base.
      cdestruct eid1, H0 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
      all: exfalso.
      all: eapply eq_None_not_Some; first eapply H.
      all: eexists.
      all: eapply H1.
      all: setoid_rewrite lookup_unfold.
      all: eexists.
      all: erewrite lookup_partial_cd_state_to_cd; unfold build_pre_exec;
        erewrite lookup_pe_to_lookup_trace; cbn.
      all: cdestruct eid1 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrEqOpt #CDestrSplitGoal #CDestrMatch; eauto.
      all: cdestruct |- ***.
      1: ospecialize (H7 eid' _ _ _ _).
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

Lemma pa_range_lookupN pa size i :
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

Lemma pa_range_lookupNat pa size i :
  i < N.to_nat size →
  pa_range pa size !! i = Some (pa_addN pa (N.of_nat i)).
Proof.
  intros.
  opose proof (pa_range_lookupN pa size (N.of_nat i) _); first lia.
  unfold lookup, list_lookupN in H0.
  by rewrite Nat2N.id in H0.
Qed.

Lemma Some_inj {A} (x y : A) :
  Some x = Some y ↔ x = y.
Proof. cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal. Qed.

Lemma bvns_equal_get_byte_equal n (x y : bvn) :
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

Lemma bvs_equal_get_byte_equal size n (x y : bv size) :
  n ≠ 0%N → (∀ i, (i * n < size)%N →
    bv_get_byte n i x = bv_get_byte n i y) →
  x = y.
Proof.
  intros.
  enough (bv_to_bvn x = bv_to_bvn y) by naive_solver.
  eapply bvns_equal_get_byte_equal; eauto.
Qed.

Lemma bv_to_bytes_bv_get_byte2 {n i m} (b : bv m) :
	(0 < n)%N → (i * n < m)%N → bv_to_bytes n b !! i = Some (bv_get_byte n i b).
Proof. intros. eapply bv_to_bytes_bv_get_byte. all: done. Qed.

Lemma bv_to_bytes_bv_get_byte3 {n i m} (b : bv m) byte :
  (0 < n)%N → (i * n < m)%N → bv_get_byte n i b = byte →
  bv_to_bytes n b !! i = Some byte.
Proof. intros. by eapply bv_to_bytes_bv_get_byte. Qed.

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

Lemma read_mem_seq_state_flag_false_get_byte size pa st v :
  read_mem_seq_state_flag size pa st = (v, false) →
  ∀ (offset : N), (offset < size)%N →
  st.(initSt).(MState.memory) (pa_addN pa offset) = bv_get_byte 8 offset v ∧
  st.(mem) !! pa_addN pa offset = None.
Proof.
  intros.
  unfold read_mem_seq_state_flag in *.
  assert
    (∀ p ∈ (read_byte_seq_state_flag st <$> pa_range pa size), p.2 = false).
  {
    cdestruct |- ***.
    destruct b0; try fast_done.
    exfalso.
    assert (In (b,true) (read_byte_seq_state_flag st <$> pa_range pa size)) as ?%in_split_r%elem_of_list_In
      by (eapply elem_of_list_In; set_solver).
    cbn in *.
    setoid_rewrite surjective_pairing in H at 2; cdestruct H as ?.
    eapply not_false_iff_true, existsb_exists.
    eexists true; cdestruct |- *** #CDestrSplitGoal.
    by eapply elem_of_list_In.
  }
  split.
  2:{
    eapply eq_None_not_Some.
    intros [].
    ospecialize (H1 (x, true) _).
    2: { scongruence. }
    unfold read_byte_seq_state_flag.
    set_unfold; eexists (pa_addN pa offset); cdestruct |- *** #CDestrSplitGoal #CDestrMatch #CDestrEqOpt.
    eapply (elem_of_list_lookup_2 _ (N.to_nat offset)).
    rewrite pa_range_lookupNat; first do 2 f_equal; lia.
  }
  assert ((read_byte_seq_state_flag st <$> pa_range pa size) =
    (λ pa, (MState.memory (initSt st) pa, false)) <$> pa_range pa size).
  {
    eapply list_eq.
    setoid_rewrite list_lookup_fmap.
    intros.
    destruct (decide (i < N.to_nat size)).
    2: erewrite <- (pa_range_length pa _) in n; orewrite lookup_ge_None_2; by try lia.
    erewrite <- (pa_range_length pa _) in l.
    apply lookup_lt_is_Some_2 in l.
    cdestruct l |- *** as ?? #CDestrEqOpt.
    rewrite H2.
    cbn.
    f_equal.
    unfold read_byte_seq_state_flag.
    cdestruct |- *** #CDestrMatch.
    ospecialize (H1 (b, true) _).
    2: { scongruence. }
    set_unfold.
    eapply elem_of_list_lookup_2 in H2.
    unfold read_byte_seq_state_flag.
    eexists; cdestruct |- ***; hauto lq: on.
  }
  setoid_rewrite surjective_pairing in H at 2; cdestruct v, H as ?.
  eapply eq_sym, bv_to_bytes_bv_get_byte.
  1: lia.
  rewrite bv_to_bytes_bv_of_bytes.
  3: rewrite split_length_l, length_fmap, pa_range_length.
  2,3: lia.
  rewrite H2.
  unfold lookup, list_lookupN.
  odestruct (nth_lookup_or_length _ _ (bv_0 8)) as [->|].
  2: rewrite split_length_l, length_fmap, pa_range_length in *; lia.
  f_equal.
  change (bv_0 8) with (bv_0 8,false).1.
  assert (∀ B (y : B) {A} (x z : A), (x,y).1 = z → x = z) by done.
  eapply (H3 bool (nth (N.to_nat offset) ?[y].2 (bv_0 8,false).2)).
  erewrite <- split_nth.
  rewrite nth_lookup, list_lookup_fmap, pa_range_lookupNat, N2Nat.id.
  2: lia.
  done.
Qed.

Instance decide_exists_in_gset `{EqDecision A, Countable A} (P : A → Prop) `{∀ a, Decision (P a)} (s : gset A) :
  Decision (∃ a, P a ∧ a ∈ s).
  destruct (filter P (elements s)) eqn: ?.
  - right.
    unfold not; cdestruct |- ***.
    eapply (filter_nil_not_elem_of P _ x Heql); eauto.
    set_solver.
  - left.
    exists a.
    enough (P a ∧ a ∈ (elements s)) by set_solver.
    eapply (elem_of_list_filter P).
    rewrite Heql.
    set_solver.
Qed.

Lemma seq_model_mem_reads_inv :
  seq_model_outcome_invariant_preserved_mem_assumptions seq_inv_predicate cdst_mem_reads_invP.
Proof.
  unfold seq_model_outcome_invariant_preserved, cdst_co_acc_invP.
  cdestruct |- *** as seqst H_inv call H_legalmem ret seqst_succ Hnms H_seqst_succ eid ev rpa rval.
  setoid_rewrite lookup_unfold.
  cdestruct ev, rpa, rval |- *** as size rr val b H_tr_lu.
  opose proof (seq_model_rf_acc_inv _ H_inv _ _ _ _) as H_rf; eauto; cbn in *.
  opose proof (cdst_rf_acc_inv _ H_inv) as H_rfb.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _) as H_same_itrs; eauto.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _) as H_same_init; eauto.
  rewrite H_same_init, H_same_itrs in *.
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
  - cdestruct val, b, eid, call, ret |- *** #CDestrMatch #CDestrEqOpt.
    + opose proof (read_mem_seq_state_flag_false_get_byte _ _ _ _ _); eauto.
      right.
      unfold not.
      cdestruct |- *** #CDestrSplitGoal.
      * rewrite <- H_same_itrs in *.
        eapply H_rf in H6.
        cdestruct H6 |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
        opose proof (seq_st_mem_map_consistent _ H_inv (ReadReq.pa rr)).
        ospecialize (H5 0%N _); first lia.
        destruct H5.
        revert H10; eapply not_eq_None_Some.
        rewrite pa_addN_zero.
        eapply (seq_st_mem_map_is_Some _ H_inv).
        setoid_rewrite lookup_unfold.
        rewrite H_same_itrs in *.
        eexists _, _, 0%N.
        cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal; eauto.
        unfold is_mem_writeP; cdestruct |- *** #CDestrSplitGoal.
        1: by rewrite pa_addN_zero.
        ospecialize (Hnms (x, (intra_trace_eid_succ 0 (trace_rev seqst.(itrs)))) _).
        2: {
          unfold Candidate.same_footprint, Candidate.same_size in *.
          set_unfold in Hnms.
          rewrite <- H_same_itrs in *.
          cdestruct x1, size, Hnms |- *** #CDestrEqOpt.
        }
        unfold Candidate.overlapping, Candidate.is_overlapping,
          Candidate.mem_events, is_mem_event, is_mem_writeP, is_mem_readP.
        set_unfold.
        cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
        all: rewrite <- H_same_itrs in *.
        all: do 4 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch).
        1,2: unfold lookup, lookup_ev_from_iTraces in *; deintros; cdestruct |- *** #CDestrEqOpt.
        1: by erewrite intra_trace_eid_succ_byte in *.
        all: unfold pa_overlap.
        all: rewrite H7.
        right; eapply pa_in_range_spec; exists 0%N.
        rewrite pa_addN_zero; cdestruct |- *** #CDestrSplitGoal.
      * unfold memoryMap_read.
        eapply (bvs_equal_get_byte_equal _ 8); try done.
        cdestruct |- ***.
        eapply Some_inj.
        erewrite <- bv_to_bytes_bv_get_byte2; try done.
        rewrite bv_to_bytes_bv_of_bytes; try done.
        2: by rewrite length_fmap, pa_range_length, N2Nat.id.
        unfold lookup, list_lookupN.
        rewrite list_lookup_fmap.
        setoid_rewrite pa_range_lookupN.
        2: lia.
        cbn.
        f_equal.
        eapply H5.
        lia.
    + destruct
        (decide ((∃ peids,
          peids.2 = intra_trace_eid_succ 0 (trace_rev (itrs seqst)) ∧
          peids ∈ rf_acc (construct_cd_for_pe
            (build_pre_exec (initSt seqst)
              (trace_cons
                (MemRead size rr &→ inl (read_mem_seq_state size (ReadReq.pa rr) seqst, None))
                (itrs seqst))) cd∅)))).
      all: autorewrite with pair in *; cbn in *.
      1: left; naive_solver.
      right.
      split.
      1: naive_solver.
      unfold memoryMap_read, read_mem_seq_state.
      eapply bvn_eq.
      split; first done.
      unfold definitions.bvn_unsigned.
      cbn.
      do 2 f_equal.
      apply list_eq.
      intros.
      setoid_rewrite list_lookup_fmap.
      destruct (decide (i < N.to_nat size)).
      2: apply option_eq;
        cdestruct |- *** as ??%lookup_lt_Some #CDestrEqOpt #CDestrSplitGoal;
        by rewrite pa_range_length in *.
      setoid_rewrite pa_range_lookupNat; try fast_done.
      cbn.
      f_equal.
      unfold read_byte_seq_state, read_byte_seq_state_flag.
      cdestruct |- *** #CDestrMatch.
      exfalso.
      eapply (seq_model_seq_st_mem_map_consistent_inv _ H_inv) in H5.
      3: unfold seq_state_is_nms in *; cbn in *; by rewrite H_same_itrs, H_same_init in *.
      2: done.
      2: {
        cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal;
        first scongruence.
        eexists _, _.
        cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; eauto.
        hauto l: on.
      }
      cdestruct H5 |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
      eapply n.
      eexists x0, _.
      cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; eauto.
      rewrite <- H_same_init, <- H_same_itrs.
      eapply H_rf.
      setoid_rewrite lookup_unfold.
      cbn.
      eexists _, _.
      deintros; cdestruct |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch #CDestrSplitGoal.
      {
        ospecialize (Hnms (x0,(intra_trace_eid_succ 0 (trace_rev seqst.(itrs)))) _).
        2: unfold Candidate.same_footprint, Candidate.same_pa in *; set_unfold in Hnms;
          cdestruct Hnms |- *** #CDestrEqOpt.
        unfold Candidate.overlapping, Candidate.is_overlapping,
        Candidate.mem_events, is_mem_event, is_mem_readP, is_mem_writeP.
        set_unfold.
        all: do 5 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch).
        1,2: unfold lookup, lookup_ev_from_iTraces in *; deintros; cdestruct |- *** #CDestrEqOpt.
        1: by erewrite intra_trace_eid_succ_byte in *.
        unfold pa_addN, pa_overlap in *.
        apply pa_addZ_exists_offset in H6; try lia.
        setoid_rewrite pa_in_range_spec.
        cdestruct H6 |- *** #CDestrSplitGoal.
        all: unfold pa_addN.
        all: rewrite <- H10; setoid_rewrite pa_addZ_assoc.
        all: left+right; eexists (Z.to_N _); cdestruct x |- *** #CDestrSplitGoal;
          rewrite ?Z2N.id; eauto; lia.
      }
      apply or_assoc.
      left.
      eapply H9.
      all: unfold is_mem_writeP.
      all: cdestruct |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch #CDestrSplitGoal.
      eapply pa_in_range_spec.
      eexists (N.of_nat i).
      split.
      1: by f_equal.
      enough (x = size)%N by lia.
      ospecialize (Hnms (other_eid, intra_trace_eid_succ 0 (trace_rev seqst.(itrs))) _).
      2: unfold Candidate.same_footprint, Candidate.same_size in *;
        by cdestruct Hnms #CDestrEqOpt.
      unfold Candidate.overlapping, Candidate.is_overlapping,
        Candidate.mem_events, is_mem_event, is_mem_readP, is_mem_writeP.
      set_unfold.
      all: do 5 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch).
      1,2: unfold lookup, lookup_ev_from_iTraces in *; deintros; cdestruct |- *** #CDestrEqOpt.
      1: by erewrite intra_trace_eid_succ_byte in *.
      unfold pa_overlap.
      rewrite H8.
      apply pa_addZ_exists_offset in H6; try lia.
      setoid_rewrite pa_in_range_spec.
      cdestruct H6 |- *** #CDestrSplitGoal.
      all: unfold pa_addN.
      all: left+right; eexists 0%N; cdestruct x |- *** #CDestrSplitGoal;
        rewrite ?pa_addZ_zero; eauto; lia.
Qed.

Lemma seq_model_pcdst_reg_map_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate pcdst_reg_map_invP.
Proof.
  unfold seq_model_outcome_invariant_preserved, pcdst_reg_map_invP.
  setoid_rewrite lookup_unfold.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ
    eid reg.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as ->.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ H_seqst_succ) as ->.
  destruct (decide (is_reg_write (call &→ ret) ∧ eid = intra_trace_eid_succ 0 (trace_rev (itrs seqst)))) as [Hc|Hc].
  - eapply seq_state_to_partial_cd_state_destruct.
    all: unfold is_mem_event, is_mem_writeP, is_mem_readP, is_reg_writeP, is_reg_readP.
    all: cdestruct eid, call, ret, Hc |- *** #CDestrEqOpt #CDestrSplitGoal.
    all: try done.
    2: unfold Setter_finmap.
    2: by rewrite lookup_unfold, lookup_total_unfold.
    eexists.
    unfold is_reg_writeP.
    cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt; eauto.
    2: {
      opose proof (EID.full_po_lt_connex eid' (intra_trace_eid_succ 0 (trace_rev (itrs seqst))) _ _ _).
      1: rewrite intra_trace_eid_succ_tid.
      3: eapply intra_trace_eid_succ_byte.
      1-2: deintros; unfold lookup, lookup_ev_from_iTraces; cdestruct |- *** #CDestrEqOpt.
      apply or_assoc in H4; destruct H4.
      1: assumption.
      cdestruct eid', H2, H4 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrMatch. }
    unfold Setter_finmap in H1.
    rewrite lookup_unfold in H1.
    cdestruct H1 |- *** #CDestrMatch.
    eapply (pcdst_reg_map_inv _ H_inv) in H2.
    cdestruct H2 |- *** #CDestrEqOpt.
  - eapply seq_state_to_partial_cd_state_destruct.
    all: unfold is_mem_event, is_mem_writeP, is_mem_readP, is_reg_writeP, is_reg_readP in *.
    all: destruct call.
    all: cdestruct |- ***.
    all: try done.
    all: unfold reg_read_upd_partial_cd_state, mem_read_upd_partial_cd_state,
      mem_write_upd_partial_cd_state.
    10: unfold Setter_finmap; setoid_rewrite lookup_unfold.
    all: cdestruct |- *** #CDestrMatch.
    11: {
      cdestruct eid |- *** #CDestrSplitGoal; try done.
      ospecialize (H3 (intra_trace_eid_succ 0 (trace_rev (itrs seqst))) _ _ _);
      cdestruct eid, H3 |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal. }
    all: setoid_rewrite (pcdst_reg_map_inv _ H_inv _ _).
    all: cdestruct eid, ret, Hc, H_seqst_succ |- *** as
      ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: try done.
    all: try intros ??????????? H_eid_order.
    all: try intros ?????????? H_eid_order.
    all: try intros ????????? H_eid_order.
    all: try intros ???????? H_eid_order.
    all: try intros ??????? H_eid_order.
    all: try intros ?????? H_eid_order.
    all: eexists _.
    all: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    all: eauto.
    all: eapply H_eid_order.
    all: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: eauto.
    all: destruct ev' as [[]].
    all: try done.
    all: cdestruct eid' ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrEqOpt #CDestrMatch.
    all: scongruence.
Qed.

Lemma seq_model_rrf_acc_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate cdst_rrf_acc_invP.
Proof.
  unfold seq_model_outcome_invariant_preserved, cdst_rrf_acc_invP.
  setoid_rewrite lookup_unfold.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ eid1 eid2.
  opose proof (cdst_rrf_acc_inv _ H_inv) as H_base.
  opose proof (pcdst_reg_map_inv _ H_inv) as H_reg_map; eauto.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _) as H_same_itrs; eauto.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _) as H_same_init; eauto.
  destruct (decide (is_reg_read (call &→ ret) ∧ eid2 = intra_trace_eid_succ 0 (trace_rev (itrs seqst)))) as [Hc|Hc].
  - eapply seq_state_to_partial_cd_state_destruct.
    all: cdestruct call, ret, eid1, eid2 |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch.
    all: try (unfold is_mem_readP, is_mem_writeP, is_reg_writeP, is_reg_readP in *; done).
    all: rewrite ?H_same_itrs, ?H_same_init in *.
    1,2: eapply H_reg_map in H0; cdestruct H0 |- *** #CDestrEqOpt.
    1: eexists _, _; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    1: apply or_assoc; left; eapply or_comm, H2.
    1: cdestruct H3 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch; eauto.
    1: sauto.
    1,2: eapply H_base in H1; cdestruct H1 |- *** #CDestrEqOpt.
    { left; rewrite lookup_total_unfold; split; last done.
      eapply H_reg_map in H4;
      cdestruct H1, H0, H4 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch; eauto.
      ospecialize (H3 t _ _ _ _); cdestruct |- *** #CDestrEqOpt; first sauto.
      ospecialize (H5 eid1 _ _ _); cdestruct |- *** #CDestrEqOpt; eauto; first sauto.
      cdestruct H3, H5 |- *** #CDestrSplitGoal. }
    exfalso.
    revert H4.
    eapply not_eq_None_Some.
    eexists eid1.
    eapply H_reg_map.
    eexists.
    setoid_rewrite lookup_unfold.
    cdestruct H0, H1 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrSplitGoal #CDestrMatch; eauto; first sauto.
    ospecialize (H3 eid' _ _ _ _); cdestruct |- *** #CDestrEqOpt; first sauto.
    cdestruct H3 |- *** #CDestrSplitGoal; left+right; done.
  - eapply seq_state_to_partial_cd_state_destruct.
    all: unfold reg_read_upd_partial_cd_state, mem_read_upd_partial_cd_state,
      mem_write_upd_partial_cd_state.
    all: cdestruct call, ret, eid1, eid2, Hc |- *** #CDestrMatch.
    all: rewrite ?H_same_itrs, ?H_same_init in *.
    all: set_unfold.
    all: ospecialize (H_base _ _); setoid_rewrite H_base.
    all: cdestruct Hc |- *** as #CDestrSplitGoal #CDestrEqOpt.
    all: try intros ????????? H_eid_order.
    all: try intros ???????? H_eid_order.
    all: try solve [unfold is_reg_readP in *; done].
    all: try right.
    all: try setoid_rewrite lookup_unfold.
    all: eexists _, _.
    all: split; last split;
    cdestruct eid1, eid2 |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrMatch.
    all: repeat apply conj.
    all: try (unfold is_reg_writeP, is_reg_readP in *; done).
    2,4: depelim H5; unfold is_reg_writeP, is_reg_readP in *; done.
    all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrMatch.
    all: try solve [left+(right;left)+(right;right); cdestruct |- *** ].
    all: eapply H_eid_order.
    all: cdestruct |- *** ##eq_some_unfold_lookup_eid_trace_rev_cons
      #CDestrEqOpt #CDestrMatch.
Qed.

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
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ H_seqst_succ) as Hsame_init.
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
  seq_model_outcome_invariant_preserved_mem_assumptions seq_inv_predicate
    (λ seq_st, consistent regs_whitelist (seq_state_to_cd seq_st)).
Proof.
  cdestruct |- *** as seqst H_inv call H_legalmem ret seqst_succ Hnms H_seqst_succ.
  opose proof (seq_model_pcdst_montonone _ H_inv _ _ seqst_succ _) as H_mono;
  first (cdestruct |- ***; eauto).
  cbn in *.
  unfold sequential_model_outcome_logged, fHandler_logger in *.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ H_seqst_succ) as Hsame_init.
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
      unfold GenAxiomaticArm.AxArmNames.fr.
      eapply rel_strictly_monotone_seq2; split.
      1: eapply grel_from_set_montone.
      unfold Candidate.from_reads.
      eapply rel_monotone_difference.
      cdestruct |- ***.
      unfold Candidate.mem_reads, Candidate.mem_writes in *.
      set_unfold.
      cdestruct H2, H6.
      opose proof (Hnms (x,y) _) as Hnmsxy; first (set_unfold; rewrite ?Hsame_init, ?Hsame_itrs;
        cdestruct |- *** #CDestrSplitGoal).
      unfold Candidate.same_footprint, Candidate.same_pa, Candidate.same_size in Hnmsxy.
      set_unfold in Hnmsxy; cbn in *; rewrite ?Hsame_init, ?Hsame_itrs in *.
      rewrite H2, H6 in *.
      cdestruct x, y, Hnmsxy.
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
        clear H_co.
        opose proof (seq_model_mem_reads_inv _ H_inv _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _) as H_mem_reads; eauto.
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
    clear H H1.
    unfold Candidate.reg_from_reads.
    eapply rel_monotone_difference.
    unfold Candidate.reg_reads, Candidate.same_reg, Candidate.reg_writes,
      Candidate.reg_reads_from, Candidate.full_instruction_order,
      Candidate.iio, Candidate.instruction_order, Candidate.same_thread.
    set_unfold.
    cdestruct |- *** as x y ???????? #CDestrEqOpt.
    opose proof (EID.full_po_lt_connex x y _ _ _) as Hfpolt; try fast_done.
    1,2: destruct x as [???[]], y as [???[]]; deintros; cdestruct |- ***.
    cdestruct x, y, Hfpolt #CDestrSplitGoal #CDestrEqOpt.
    1: by left.
    right.
    destruct (decide (∃ peids,
      peids.2 = x ∧
      peids ∈ rrf_acc (construct_cd_for_pe
        (build_pre_exec (initSt seqst)(trace_cons (call &→ ret) (itrs seqst))) cd∅))) as [Hrrf|Hrrf];
    autorewrite with pair in *.
    {
      cdestruct Hrrf as z Hrrf.
      eexists z; split; last done.
      rewrite <- Hsame_init, <- ?Hsame_itrs in Hrrf.
      eapply (seq_model_rrf_acc_inv _ H_inv _ _ _) in Hrrf; eauto.
      cdestruct Hrrf #CDestrEqOpt.
      rewrite Hsame_init, ?Hsame_itrs in *.
      destruct (decide (y = z)); [right; split|left]; try fast_done.
      1: eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      assert (EID.full_po_lt y z) as [|]
      by (ospecialize (H7 y _ _ _ _); cdestruct x, z, H7 |- *** #CDestrEqOpt #CDestrSplitGoal; sauto).
      1: left.
      2: right.
      all: unfold EID.po_lt, EID.iio_lt in *.
      all: split; first lia.
      1: eexists _, _, _; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
      1: unfold lookup, lookup_ev_from_iTraces in *; cdestruct z, y |- *** #CDestrEqOpt.
      unfold Candidate.same_instruction_instance.
      set_unfold.
      eexists _, _, (_, _); cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
      all: hauto l: on.
    }
    {
      exfalso.
      eapply Hrrf.
      rewrite <- ?Hsame_init, <- ?Hsame_itrs.
      setoid_rewrite (seq_model_rrf_acc_inv _ H_inv _ _ _ _ _); eauto.
      setoid_rewrite lookup_unfold.
      opose proof (trace_last_event_indexed
        (λ eid ev, is_reg_write ev ∧ get_reg ev = Some x2 ∧ EID.full_po_lt eid x)
         _ _ _ H1 _) as Hrfw.
      1: cdestruct |- *** #CDestrSplitGoal.
      cdestruct Hrfw |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists x0, _.
      rewrite ?Hsame_init, ?Hsame_itrs in *.
      cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists _, _.
      cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      apply or_assoc.
      destruct (decide (EID.full_po_lt x other_eid)); first by right.
      left.
      eapply H6.
      all: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      assert (other_eid ≠ x) by (intros ->; sauto).
      opose proof (EID.full_po_lt_connex other_eid x _ _ _).
      1-3: unfold lookup, lookup_ev_from_iTraces in *; deintros; cdestruct |- *** #CDestrEqOpt.
      1: cdestruct H9 |- *** #CDestrSplitGoal.
    }
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
      opose proof (seq_st_mem_map_is_Some _ H_inv); eauto.
      cdestruct seqst_succ, call, ret, H_base |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal.
      all: try solve [eexists; cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal].
      2,4: unfold orb, Is_true in *; cdestruct H3, H5 |- #CDestrMatch; hauto l: on.
      all: opose proof (read_mem_seq_state_flag_false_get_byte _ _ _ _ _ 0%N _); eauto.
      all: cdestruct H7 as ?.
      all: eapply not_eq_None_Some.
      all: rewrite pa_addN_zero.
      all: eapply H_rf in H6; cdestruct H6 #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
      all: opose proof (Hnms (x2,intra_trace_eid_succ 0 (trace_rev seqst.(itrs))) _).
      1,3: unfold Candidate.overlapping, Candidate.is_overlapping,
        Candidate.mem_events, is_mem_event, is_mem_readP, is_mem_writeP.
      1,2: set_unfold.
      1,2: do 5 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch).
      1-4: unfold lookup, lookup_ev_from_iTraces in *; deintros; cdestruct |- *** #CDestrEqOpt.
      1,3: by erewrite intra_trace_eid_succ_byte in *.
      1,2: unfold pa_overlap.
      1,2: rewrite H11.
      1,2: right.
      1,2: apply pa_in_range_spec.
      1,2: exists 0%N; rewrite pa_addN_zero; split; done.
      all: eexists _.
      all: eapply (seq_st_mem_map_consistent _ H_inv (ReadReq.pa x0) (bv_get_byte 8 0 x5.(WriteReq.value))).
      all: setoid_rewrite lookup_unfold.
      all: eexists _, _, 0%N.
      all: unfold is_mem_writeP.
      all: cdestruct |- *** #CDestrSplitGoal# CDestrEqOpt; eauto.
      all: cdestruct |- *** #CDestrSplitGoal# CDestrEqOpt.
      all: try rewrite pa_addN_zero.
      all: try done.
      1,3: unfold Candidate.same_footprint, Candidate.same_size in *.
      1,2: set_unfold; cdestruct x2 |- *** #CDestrEqOpt.
      1,2: scongruence.
      all: ospecialize (H9 eid' _ _ _ _ ).
      all: unfold is_mem_writeP.
      all: cdestruct b |- *** #CDestrEqOpt #CDestrMatch.
      2,4: cdestruct H9 |- *** #CDestrSplitGoal.
      all: try (left+right; done).
      all: ospecialize (Hnms (eid', intra_trace_eid_succ 0 (trace_rev seqst.(itrs))) _).
      2,4: unfold Candidate.same_footprint, Candidate.same_pa in *; set_unfold;
        by cdestruct Hnms #CDestrEqOpt.
      all: unfold Candidate.overlapping, Candidate.is_overlapping,
        Candidate.mem_events, is_mem_event, is_mem_readP, is_mem_writeP.
      all: set_unfold.
      all: do 5 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch).
      1,3: by erewrite intra_trace_eid_succ_byte in *.
      all: unfold pa_overlap.
      all: naive_solver.
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
      1: eapply orb_true_iff in H0; cdestruct H0 |- *** #CDestrSplitGoal; [right|left; right];
        unfold is_mem_read_kindP, is_mem_readP; eexists;
        cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; naive_solver.
      all: left; left.
      all: eexists;
        cdestruct |- *** #CDestrEqOpt #CDestrMatch #CDestrSplitGoal; naive_solver.
  - unfold seq_state_is_nms in *; cbn in *.
    by rewrite Hsame_init, Hsame_itrs in *.
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
Qed.

Lemma seq_model_reg_reads_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate cdst_reg_reads_invP.
Proof.
  unfold seq_model_outcome_invariant_preserved, cdst_reg_reads_invP.
  setoid_rewrite lookup_unfold.
  cdestruct |- *** as seqst H_inv call ret seqst_succ H_seqst_succ
    eid reg racc rval #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons.
  opose proof (seq_model_rrf_acc_inv _ H_inv _ _ _ _) as Hrrf; eauto.
  opose proof (cdst_rrf_acc_inv _ H_inv) as Hrrfb.
  opose proof (seq_st_reg_map_consistent _ H_inv) as H_reg_map; eauto.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _) as H_same_itrs; eauto.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ _) as H_same_init; eauto.
  rewrite H_same_itrs, H_same_init.
  cdestruct eid |- *** #CDestrMatch #CDestrEqOpt.
  - opose proof (cdst_reg_reads_inv _ H_inv eid _ _ _ _ _ _ _);
    cdestruct eid |- *** #CDestrEqOpt.
    cdestruct reg |- *** #CDestrSplitGoal #CDestrEqOpt.
    + eapply Hrrfb in H0; cdestruct H0 |- *** #CDestrEqOpt.
      left.
      rewrite <- H_same_itrs, <- H_same_init in *.
      eexists x; eapply Hrrf.
      eexists _, _; cdestruct x, eid |- *** #CDestrEqOpt #CDestrSplitGoal
        ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
      1: eapply H2; cdestruct other_eid |- *** #CDestrEqOpt #CDestrSplitGoal.
      all: right; right; cdestruct |- *** #CDestrEqOpt.
    + right.
      unfold not; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eapply H0; eexists x.
      eapply Hrrfb.
      rewrite <- H_same_itrs, <- H_same_init in *.
      eapply Hrrf in H1.
      cdestruct H1 |- *** #CDestrEqOpt #CDestrSplitGoal
        ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
      eexists _, _; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eapply H3; cdestruct |- *** #CDestrEqOpt.
  - cdestruct call, ret, racc, seqst_succ, rval |- *** #CDestrEqOpt.
    destruct (decide ((∃ peids, peids.2 = intra_trace_eid_succ 0 (trace_rev (itrs seqst)) ∧
      peids ∈ rrf_acc (construct_cd_for_pe (build_pre_exec (initSt seqst)
      (trace_cons (RegRead reg None &→ read_reg_seq_state reg seqst) (itrs seqst))) cd∅)))) as [Hrrfe|Hrrfne].
    + cdestruct Hrrfe |- *** #CDestrEqOpt.
      left.
      hauto lq: on.
    + right; unfold not.
      cdestruct Hrrfne |- *** #CDestrEqOpt #CDestrSplitGoal.
      1: apply Hrrfne; eexists; hauto l: on.
      unfold read_reg_seq_state.
      cdestruct |- *** #CDestrMatch.
      exfalso.
      eapply Hrrfne; clear Hrrfne.
      eapply (H_reg_map reg) in H.
      cdestruct H |- *** #CDestrEqOpt.
      eexists (x0,_); cdestruct |- *** #CDestrSplitGoal.
      eapply Hrrf; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
      eexists _, _; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
      apply or_assoc.
      left.
      cdestruct H2 #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons #CDestrMatch.
      eapply H1; cdestruct |- *** #CDestrEqOpt.
Qed.

Lemma seq_model_pcdst_wf :
  seq_model_outcome_invariant_preserved_mem_assumptions seq_inv_predicate
    (λ seq_st, Candidate.wf (seq_state_to_cd seq_st)).
Proof.
  cdestruct |- *** as seqst H_inv call H_legalmem ret seqst_succ Hnms H_seqst_succ.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ H_seqst_succ) as Hsame_itrs.
  opose proof (sequential_model_outcome_same_initSt _ _ _ _ H_seqst_succ) as Hsame_init.
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
      assert (x0 ≠ 0%N)
      by (opose proof (pcdst_mem_acc_legal _ H_inv t _ _); cdestruct x0 |- *** #CDestrEqOpt; lia).
      opose proof (Hnms (t,intra_trace_eid_succ 0 (trace_rev (itrs seqst))) _).
      {
        unfold Candidate.overlapping, Candidate.is_overlapping, Candidate.mem_events.
        set_unfold.
        setoid_rewrite lookup_unfold.
        rewrite ?Hsame_itrs, ?Hsame_init in *.
        cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
        all: eexists; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt #CDestrMatch; try done.
        2,3: unfold is_mem_event, is_mem_readP, is_mem_writeP; naive_solver.
        do 3 (eexists; cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt #CDestrMatch).
        unfold pa_overlap.
        setoid_rewrite pa_in_range_spec.
        cdestruct n, x0 #CDestrSplitGoal #CDestrMatch #CDestrEqOpt.
        all: left+right; exists 0%N; rewrite pa_addN_zero;
          cdestruct |- *** #CDestrSplitGoal; lia.
      }
      unfold Candidate.same_footprint, Candidate.same_pa, Candidate.same_size in *.
      set_unfold.
      cdestruct ret, seqst_succ, H2 #CDestrMatch #CDestrEqOpt.
      {
        eapply eq_sym, read_mem_seq_state_flag_false_get_byte in H4; eauto.
        exfalso; cdestruct H4 as ?.
        eapply not_eq_None_Some.
        eapply (seq_st_mem_map_is_Some _ H_inv).
        eexists _, t, 0%N.
        unfold is_mem_writeP.
        cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
        2: lia.
        by rewrite ?pa_addN_zero in *.
      }
      unfold read_mem_seq_state, read_byte_seq_state, read_byte_seq_state_flag in *.
      cdestruct b |- ***.
      destruct x1; cbn in *.
      cdestruct pa0, n #CDestrEqOpt.
      eapply (bvns_equal_get_byte_equal 8); try done.
      intros.
      eapply Some_inj.
      cbn in *.
      setoid_rewrite <- bv_to_bytes_bv_get_byte2 at 2; try lia.
      rewrite bv_to_bytes_bv_of_bytes; try done.
      2: by rewrite length_fmap, pa_range_length, N2Nat.id.
      setoid_rewrite list_lookup_fmap.
      erewrite fmap_Some_2.
      2: eapply pa_range_lookupN; lia.
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
      eapply or_comm, H6; cdestruct |- *** #CDestrEqOpt.
      ospecialize (Hnms (eid',intra_trace_eid_succ 0 (trace_rev (itrs seqst))) _).
      { unfold Candidate.overlapping, Candidate.is_overlapping,
        Candidate.mem_events; set_unfold; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
        all: eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
        2,3: sauto.
        do 3 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal #CDestrMatch).
        unfold pa_overlap.
        setoid_rewrite pa_in_range_spec; setoid_rewrite pa_in_range_spec in H10.
        unfold pa_addN in *.
        cdestruct H10.
        eapply pa_addZ_exists_offset in H10; try lia.
        cdestruct H10 #CDestrSplitGoal.
        1: left.
        2: right.
        all: eexists (Z.to_N ?[?z]).
        all: erewrite Z2N.id; eauto.
        all: cdestruct |- *** #CDestrSplitGoal; lia.
      }
      unfold Candidate.same_footprint, Candidate.same_pa, Candidate.same_size in *.
      set_unfold.
      cdestruct Hnms |- *** #CDestrEqOpt.
    + cbn; rewrite Hsame_init, Hsame_itrs.
      unfold Candidate.init_mem_reads, Candidate.mem_reads, Candidate.is_valid_init_mem_read.
      set_unfold.
      cdestruct |- *** #CDestrEqOpt.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
      opose proof (seq_model_mem_reads_inv _ H_inv _ _ _ _ _ _ x _ _ _ _ _ _ _ _ _) as Hreads;
        eauto; cbn; rewrite ?Hsame_itrs; cdestruct |- *** #CDestrEqOpt; eauto.
      cdestruct Hreads #CDestrEqOpt #CDestrSplitGoal.
      all: rewrite ?Hsame_itrs, ?Hsame_init in *.
      1: exfalso; eauto.
      cdestruct x3.
      replace ((8 * x1) `div` 8)%N with x1 by lia.
      reflexivity.
  - opose proof (seq_model_co_acc_inv _ H_inv _ _ _ _) as H_co; eauto.
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
      ospecialize (Hnms (weid1,weid2) _); eauto;
      cbn in *; rewrite ?Hsame_itrs, ?Hsame_init in *.
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
  - opose proof (seq_model_rrf_acc_inv _ H_inv _ _ _ _) as Hrrf; eauto.
    opose proof (cdst_rrf_acc_inv _ H_inv) as Hrrfb.
    constructor; cbn.
    all: unfold Candidate.initial_reg_reads, Candidate.possible_initial_reg_reads,
      Candidate.reg_writes, Candidate.reg_reads, Candidate.same_reg_val, grel_functional.
    all: set_unfold; cdestruct |- ***.
    all: try (eapply Hrrf in H; cdestruct H |- *** #CDestrEqOpt).
    all: try (eapply Hrrf in H0; cdestruct H0 |- *** #CDestrEqOpt).
    all: try solve [eexists; cdestruct H |- *** #CDestrEqOpt #CDestrSplitGoal].
    + ospecialize (H3 x1 _ _ _ _); unfold is_reg_writeP; cdestruct |- *** #CDestrEqOpt.
      ospecialize (H5 x0 _ _ _ _); unfold is_reg_writeP; cdestruct |- *** #CDestrEqOpt.
      cdestruct x0, x1 |- *** #CDestrSplitGoal.
    + eexists _, _, (_, _); cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
      1: unfold lookup, lookup_ev_from_iTraces in *; cdestruct t0, t |- *** #CDestrEqOpt.
      opose proof (seq_model_pcdst_reg_map_inv _ H_inv _ _ _ _) as H_reg_w_map; eauto.
      opose proof (seq_st_reg_map_consistent _ H_inv) as H_reg_map; eauto.
      opose proof (seq_model_reg_reads_inv _ H_inv _ _ _ _) as H_reg_reads; eauto.
      cdestruct t, t0 |- *** #CDestrEqOpt ##eq_some_unfold_lookup_eid_trace_rev_cons
        #CDestrMatch.
      * rewrite Hsame_itrs in *.
        opose proof (Candidate.rrf_same_reg_val (Candidate.reg_reads_from_wf' _ (cd_wf _ H_inv)) (t, t0) _) as H_base.
        {
          eapply Hrrfb.
          eexists _, _.
          cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
          eapply H2.
          all: cdestruct |- *** #CDestrSplitGoal #CDestrEqOpt.
        }
        unfold Candidate.same_reg_val in *.
        set_unfold in H_base.
        cdestruct H_base |- *** #CDestrEqOpt.
      * rewrite Hsame_itrs in *.
        cdestruct x3, x5, call, ret |- *** #CDestrEqOpt.
        unfold read_reg_seq_state.
        cdestruct |- *** #CDestrMatch.
        { eapply H_reg_map in H3.
          cdestruct b, H3 |- *** #CDestrEqOpt.
          enough (x9 = x3) by admit.
          ospecialize (H2 x0 _ _ _ _);
          last ospecialize (H4 t _ _ _ _).
          all: cdestruct |- *** #CDestrEqOpt.
          cdestruct t, x0 |- *** #CDestrEqOpt #CDestrSplitGoal. }
        exfalso.
        revert H3.
        eapply not_eq_None_Some.
        eapply (seq_st_reg_map_is_Some _ H_inv).
        eexists _, t.
        cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
    + unfold Candidate.is_valid_init_reg_read, is_reg_readP.
      eexists _; cdestruct H |- *** #CDestrSplitGoal #CDestrEqOpt #CDestrMatch.
      1: generalize (nat_to_fin x0); intros fin1; depelim fin1; last depelim fin1.
      1: unfold build_pre_exec; cbn.
      2: destruct (EID.tid x) eqn:?.
      3: unfold lookup, lookup_ev_from_iTraces in *; cdestruct x |- *** #CDestrEqOpt;
        scongruence.
      2: unfold build_pre_exec, lookup, vec_lookup_nat in *; cbn in *;
        destruct seqst_succ as [[[]]] in *;
        deintros; cdestruct |- *** #CDestrMatch #CDestrEqOpt.
      opose proof (seq_model_reg_reads_inv _ H_inv _ _ _ _ x _ _ _ _ _ _ _) as H_reg_reads; eauto.
      1: cdestruct |- *** #CDestrEqOpt.
      1-3: sauto.
      cdestruct H_reg_reads |- *** #CDestrSplitGoal.
      1: exfalso; apply H0.
      1: eauto.
Admitted.

Lemma seq_model_seq_inv_predicate_preserved :
  seq_model_outcome_invariant_preserved_mem_assumptions seq_inv_predicate
    seq_inv_predicate.
Proof using regs_whitelist.
  cdestruct |- *** as seqst H_seq_inv call H_legalmem ret seqst_succ Hnms H_succ.
  constructor.
  - by eapply seq_model_seq_st_mem_map_consistent_inv.
  - by eapply seq_model_seq_st_mem_map_is_Some_inv.
  - by eapply seq_model_seq_st_reg_map_consistent_inv.
  - by eapply seq_model_seq_st_reg_map_is_Some_inv.
  - by eapply seq_model_mem_writes_succeed_inv.
  - by eapply seq_model_mem_accesses_legal_inv.
  - by eapply seq_model_pcdst_mem_map_inv.
  - by eapply seq_model_pcdst_mem_set_map_inv.
  - by eapply seq_model_pcdst_reg_map_inv; done.
  - by eapply seq_model_co_acc_inv.
  - by eapply seq_model_rf_acc_inv.
  - by eapply seq_model_rrf_acc_inv.
  - by eapply seq_model_mem_reads_inv.
  - by eapply seq_model_reg_reads_inv.
  - by eapply seq_model_pcdst_montonone.
  - by eapply seq_model_pcdst_wf.
  - by eapply seq_model_pcdst_consistent.
Qed.

#[local] Instance lookup_unfold_change_trace_end trs x trend P :
  LookupUnfold x (trace_rev trs) P →
  LookupUnfold x (trace_rev (((hd FTNothing trs).1, trend) :: tail trs)) P.
Proof.
  tcclean.
  unfold lookup, lookup_ev_from_iTraces, guard, trace_rev.
  destruct x, trs; first destruct iid;
  cdestruct |- *** #CDestrEqOpt #CDestrMatch.
  rewrite ?lookup_app.
  cdestruct |- *** #CDestrEqOpt #CDestrMatch.
  rewrite ?lookup_unfold.
  cdestruct |- *** #CDestrEqOpt #CDestrMatch.
Qed.

#[local] Instance lookup_unfold_cons_empty_trace trs x P :
  LookupUnfold x (trace_rev trs) P →
  LookupUnfold x (trace_rev (FTNothing :: trs)) P.
Proof.
  tcclean.
  unfold lookup, lookup_ev_from_iTraces, guard, trace_rev.
  destruct x, trs; first destruct iid;
  cdestruct |- *** #CDestrEqOpt #CDestrMatch.
  rewrite ?lookup_app.
  cdestruct |- *** #CDestrEqOpt #CDestrMatch.
  rewrite ?lookup_unfold.
  cdestruct |- *** #CDestrEqOpt #CDestrMatch.
Qed.

#[local] Instance set_unfold_elem_of_collect_all_change_trace_end x
    `{∀ eid ev, Decision (P eid ev)} Q init trs trend :
  SetUnfoldElemOf x (Candidate.collect_all P (build_pre_exec init trs)) Q →
  SetUnfoldElemOf x (Candidate.collect_all P
    (build_pre_exec init (((hd FTNothing trs).1, trend) :: tail trs))) Q.
Proof. tcclean. set_unfold. by setoid_rewrite lookup_unfold. Qed.

(* #[local] Instance lookup_unfold
LookupUnfold eid (trace_rev itrs st) P →
LookupUnfold eid
(trace_rev (itrs (set itrs (λ l : list (iTrace ()), ((hd FTNothing l).1, FTERet ()) :: tail l) st))) P *)

Lemma iEvent_list_unchanged_by_trace_end initSt itrs:
  Candidate.iEvent_list (build_pre_exec initSt (((hd FTNothing itrs).1, FTERet ()) :: tail itrs)) =
  Candidate.iEvent_list (build_pre_exec initSt itrs).
Proof using regs_whitelist.
  apply list_eq; intro.
  unfold Candidate.iEvent_list, Candidate.instruction_list,
    build_pre_exec in *.
  setoid_rewrite enumerate_imap.
  cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  setoid_rewrite enumerate_imap.
  destruct itrs as [|[]];
  first (deintros; cdestruct |- *** #CDestrEqOpt).
  unfold trace_rev in *.
  cbn in *; cbv [set] in *.
  rewrite ?imap_app, ?bind_app in *.
  reflexivity.
Qed.

Lemma iEvent_list_unchanged_by_cons_empty_trace initSt itrs:
  Candidate.iEvent_list (build_pre_exec initSt (FTNothing :: itrs)) =
  Candidate.iEvent_list (build_pre_exec initSt itrs).
Proof using regs_whitelist.
  apply list_eq; intro.
  unfold Candidate.iEvent_list, Candidate.instruction_list,
    build_pre_exec in *.
  setoid_rewrite enumerate_imap.
  cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  setoid_rewrite enumerate_imap.
  destruct itrs as [|[]];
  first (deintros; cdestruct |- *** #CDestrEqOpt).
  unfold trace_rev in *.
  cbn in *; cbv [set] in *.
  rewrite ?imap_app, ?bind_app, ?app_nil_r in *.
  reflexivity.
Qed.

Lemma event_list_unchanged_by_trace_end initSt itrs:
  Candidate.event_list (build_pre_exec initSt (((hd FTNothing itrs).1, FTERet ()) :: tail itrs)) =
  Candidate.event_list (build_pre_exec initSt itrs).
Proof using regs_whitelist.
  unfold Candidate.event_list.
  by rewrite iEvent_list_unchanged_by_trace_end.
Qed.

Lemma event_list_unchanged_by_cons_empty_trace initSt itrs:
  Candidate.event_list (build_pre_exec initSt (FTNothing :: itrs)) =
  Candidate.event_list (build_pre_exec initSt itrs).
Proof using regs_whitelist.
  unfold Candidate.event_list.
  by rewrite iEvent_list_unchanged_by_cons_empty_trace.
Qed.

Lemma construct_cd_for_pe_unchanged_by_trace_end initSt itrs :
  (construct_cd_for_pe (build_pre_exec initSt (((hd FTNothing itrs).1, FTERet ()) :: tail itrs)) cd∅) =
  (construct_cd_for_pe (build_pre_exec initSt itrs) cd∅).
Proof using regs_whitelist.
  unfold construct_cd_for_pe.
  f_equal.
  apply list_eq.
  intros.
  apply option_eq.
  cdestruct |- *** as ?? H #CDestrSplitGoal.
  1: by rewrite event_list_unchanged_by_trace_end in H.
  by rewrite event_list_unchanged_by_trace_end.
Qed.

Lemma construct_cd_for_pe_unchanged_by_cons_empty_trace initSt itrs :
  (construct_cd_for_pe (build_pre_exec initSt (FTNothing :: itrs)) cd∅) =
  (construct_cd_for_pe (build_pre_exec initSt itrs) cd∅).
Proof using regs_whitelist.
  unfold construct_cd_for_pe.
  f_equal.
  apply list_eq.
  intros.
  apply option_eq.
  cdestruct |- *** as ?? H #CDestrSplitGoal.
  1: by rewrite event_list_unchanged_by_cons_empty_trace in H.
  by rewrite event_list_unchanged_by_cons_empty_trace.
Qed.

Lemma collect_all_equal_events {et nmth} `{∀ eid ev, Decision (P eid ev)} (pe pe' : Candidate.pre et nmth) :
  Candidate.event_list pe = Candidate.event_list pe' →
  Candidate.collect_all P pe = Candidate.collect_all P pe'.
Proof. unfold Candidate.collect_all. by intros ->. Qed.

Lemma same_key_equal_events {et nmth} `{EqDecision K, Countable K}
    (k : EID.t → iEvent → option K) (pe pe' : Candidate.pre et nmth) :
  Candidate.event_list pe = Candidate.event_list pe' →
  (Candidate.same_key k pe) = (Candidate.same_key k pe').
Proof. unfold Candidate.same_key, Candidate.gather_by_key. by intros ->. Qed.

Lemma is_overlapping_equal_events {et nmth} (pe pe' : Candidate.pre et nmth) :
  Candidate.event_list pe = Candidate.event_list pe' →
  ∀ eid1 eid2, Candidate.is_overlapping pe eid1 eid2 ↔ Candidate.is_overlapping pe' eid1 eid2.
Proof.
  unfold Candidate.is_overlapping.
  cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  all: eapply Candidate.event_list_match in H0, H2.
  1,2: rewrite H in H0, H2.
  3,4: rewrite <- H in H0, H2.
  all: eapply Candidate.event_list_match in H0, H2.
  all: do 4 (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal).
  all: unfold pa_overlap.
  all: naive_solver.
Qed.

Lemma set_filter_iff `{FinSet A C} (P1 P2 : A → Prop)
      `{∀ a, Decision (P1 a)} `{∀ a, Decision (P2 a)} (s : C) :
    (∀ a, P1 a ↔ P2 a) →
    filter P1 s = filter P2 s.
Proof.
  intros.
  unfold filter, set_filter.
  erewrite list_filter_iff.
  1: reflexivity.
  assumption.
Qed.

Lemma is_overlapping_equal_events_filter_predicate {et nmth}
    (pe pe' : Candidate.pre et nmth) :
  Candidate.event_list pe = Candidate.event_list pe' →
  ∀ peids, (λ '(eid1,eid2), Candidate.is_overlapping pe eid1 eid2) peids ↔ (λ '(eid1,eid2), Candidate.is_overlapping pe' eid1 eid2) peids.
Proof. autorewrite with pair. apply is_overlapping_equal_events. Qed.

Lemma seq_state_is_nms_trace_end st :
  seq_state_is_nms
    (set itrs (λ tr, ((hd FTNothing tr).1, FTERet ()) :: tail tr) st) →
  seq_state_is_nms st.
Proof using regs_whitelist.
  unfold seq_state_is_nms, Candidate.is_nms,
    Candidate.same_footprint, Candidate.same_pa, Candidate.same_size,
    Candidate.overlapping, Candidate.mem_events.
  cbn.
  intros H.
  all: setoid_rewrite (collect_all_equal_events _ _ (event_list_unchanged_by_trace_end _ _)) in H.
  all: setoid_rewrite (same_key_equal_events _ _ _ (event_list_unchanged_by_trace_end _ _)) in H.
  all: setoid_rewrite (set_filter_iff _ _ _ (is_overlapping_equal_events_filter_predicate _ _ (event_list_unchanged_by_trace_end (initSt st) (itrs st)))) in H.
  done.
Qed.

Lemma seq_state_is_nms_cons_empty_trace st :
  seq_state_is_nms (set itrs (cons FTNothing) st) →
  seq_state_is_nms st.
Proof using regs_whitelist.
  unfold seq_state_is_nms, Candidate.is_nms,
    Candidate.same_footprint, Candidate.same_pa, Candidate.same_size,
    Candidate.overlapping, Candidate.mem_events.
  cbn.
  intros H.
  all: setoid_rewrite (collect_all_equal_events _ _ (event_list_unchanged_by_cons_empty_trace _ _)) in H.
  all: setoid_rewrite (same_key_equal_events _ _ _ (event_list_unchanged_by_cons_empty_trace _ _)) in H.
  all: setoid_rewrite (set_filter_iff _ _ _ (is_overlapping_equal_events_filter_predicate _ _ (event_list_unchanged_by_cons_empty_trace (initSt st) (itrs st)))) in H.
  done.
Qed.

Lemma seq_inv_predicate_preserved_change_trace_end st :
  seq_inv_predicate st →
  seq_inv_predicate (set itrs (λ l : list (iTrace ()), ((hd FTNothing l).1, FTERet ()) :: tail l) st).
Proof using regs_whitelist.
  intros H_inv.
  constructor.
  - apply seq_st_mem_map_consistent in H_inv.
    unfold seq_st_mem_map_consistentP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply seq_st_mem_map_is_Some in H_inv.
    unfold seq_st_mem_map_is_SomeP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply seq_st_reg_map_consistent in H_inv.
    unfold seq_st_reg_map_consistentP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply seq_st_reg_map_is_Some in H_inv.
    unfold seq_st_reg_map_is_SomeP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply mem_writes_succeed in H_inv.
    unfold mem_writes_succeedP in *.
    cbn.
    set_unfold.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply pcdst_mem_acc_legal in H_inv.
    unfold pcdst_mem_acc_legalP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply pcdst_mem_map_inv in H_inv.
    unfold pcdst_mem_map_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    apply H_inv.
  - apply pcdst_mem_set_map_inv in H_inv.
    unfold pcdst_mem_set_map_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    apply H_inv.
  - apply pcdst_reg_map_inv in H_inv.
    unfold pcdst_reg_map_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    apply H_inv.
  - apply cdst_co_acc_inv in H_inv.
    unfold cdst_co_acc_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    apply H_inv.
  - apply cdst_rf_acc_inv in H_inv.
    unfold cdst_rf_acc_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    apply H_inv.
  - apply cdst_rrf_acc_inv in H_inv.
    unfold cdst_rrf_acc_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    apply H_inv.
  - apply cdst_mem_reads_inv in H_inv.
    unfold cdst_mem_reads_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    apply H_inv.
  - apply cdst_reg_reads_inv in H_inv.
    unfold cdst_reg_reads_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    apply H_inv.
  - opose proof (cd_from_seq_state_monotone st H_inv).
    unfold cd_monotone in *.
    cbn in *.
    rewrite construct_cd_for_pe_unchanged_by_trace_end.
    done.
  - opose proof (cd_wf _ H_inv).
    unfold cd in H.
    destruct H as [? [] [] [] []].
    constructor.
    2-5: constructor.
    all: unfold Candidate.has_only_supported_events, Candidate.initial_reg_reads,
      Candidate.is_valid_init_reg_read, Candidate.is_valid_init_mem_read,
      GenAxiomaticArm.AxArmNames.rmw, GenAxiomaticArm.AxArmNames.fre,
      GenAxiomaticArm.AxArmNames.coe, GenAxiomaticArm.AxArmNames.coi,
      Candidate.init_mem_reads, Candidate.is_nms, Candidate.is_valid_rf,
      Candidate.atomic_update, GenAxiomaticArm.AxArmNames.fri,
      GenAxiomaticArm.AxArmNames.fr, Candidate.writes_by_kind,
      Candidate.full_instruction_order, GenAxiomaticArm.AxArmNames.co,
      GenAxiomaticArm.AxArmNames.rf, Candidate.reg_from_reads,
      Candidate.explicit_reads, Candidate.reads_by_kind, Candidate.from_reads,
      Candidate.reg_reads, Candidate.instruction_order, Candidate.same_thread,
      Candidate.overlapping, Candidate.same_reg, Candidate.same_pa,
      Candidate.same_size, Candidate.reg_writes, Candidate.full_instruction_order,
      Candidate.instruction_order, Candidate.iio, Candidate.same_instruction_instance,
      Candidate.mem_events, Candidate.explicit_writes, Candidate.mem_writes,
      Candidate.mem_reads, Candidate.writes_by_kind,
      Candidate.same_footprint in *; cbn in *.
    all: try setoid_rewrite construct_cd_for_pe_unchanged_by_trace_end.
    all: try setoid_rewrite (collect_all_equal_events _ _ (event_list_unchanged_by_trace_end _ _)).
    all: try setoid_rewrite (same_key_equal_events _ _ _ (event_list_unchanged_by_trace_end _ _)).
    all: try setoid_rewrite iEvent_list_unchanged_by_trace_end.
    all: try setoid_rewrite (set_filter_iff _ _ _ (is_overlapping_equal_events_filter_predicate _ _ (event_list_unchanged_by_trace_end (initSt st) (itrs st)))).
    all: try setoid_rewrite (is_overlapping_equal_events _ _ (event_list_unchanged_by_trace_end (initSt st) (itrs st))).
    all: try assumption.
    1: intros [a b] Hrw; ospecialize (rf_valid (a, b) _).
    1: by setoid_rewrite construct_cd_for_pe_unchanged_by_trace_end in Hrw.
    2: intros reid Hrw; ospecialize (rf_valid_initial reid _); eauto.
    all: cdestruct rf_valid, rf_valid_initial |- *** #CDestrEqOpt.
    all: eexists; cdestruct |- *** #CDestrEqOpt.
    all: setoid_rewrite lookup_unfold.
    all: repeat (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal).
  - opose proof (cd_from_seq_state_consistent _ H_inv).
    unfold cd in *.
    setoid_rewrite construct_cd_for_pe_unchanged_by_trace_end.
    destruct H.
    constructor.
    all: unfold GenAxiomaticArm.AxArmNames.rmw, GenAxiomaticArm.AxArmNames.fre,
      GenAxiomaticArm.AxArmNames.coe, GenAxiomaticArm.AxArmNames.coi,
      Candidate.init_mem_reads, Candidate.is_nms,
      Candidate.atomic_update, GenAxiomaticArm.AxArmNames.fri,
      GenAxiomaticArm.AxArmNames.fr, Candidate.writes_by_kind,
      Candidate.full_instruction_order, GenAxiomaticArm.AxArmNames.co,
      GenAxiomaticArm.AxArmNames.rf, Candidate.reg_from_reads,
      Candidate.explicit_reads, Candidate.reads_by_kind, Candidate.from_reads,
      Candidate.reg_reads, Candidate.instruction_order, Candidate.same_thread,
      Candidate.overlapping, Candidate.same_reg, Candidate.same_pa,
      Candidate.same_size, Candidate.reg_writes, Candidate.full_instruction_order,
      Candidate.instruction_order, Candidate.iio, Candidate.same_instruction_instance,
      Candidate.mem_events, Candidate.explicit_writes, Candidate.mem_writes,
      Candidate.mem_reads, Candidate.writes_by_kind,
      Candidate.same_footprint in *; cbn in *.
    all: try setoid_rewrite (collect_all_equal_events _ _ (event_list_unchanged_by_trace_end _ _)).
    all: try setoid_rewrite (same_key_equal_events _ _ _ (event_list_unchanged_by_trace_end _ _)).
    all: try setoid_rewrite (set_filter_iff _ _ _ (is_overlapping_equal_events_filter_predicate _ _ (event_list_unchanged_by_trace_end (initSt st) (itrs st)))).
    all: try assumption.
Qed.

Lemma seq_inv_predicate_preserved_cons_empty_trace st :
  seq_inv_predicate st →
  seq_inv_predicate (set itrs (cons FTNothing) st).
Proof using regs_whitelist.
  intros H_inv.
  constructor.
  - apply seq_st_mem_map_consistent in H_inv.
    unfold seq_st_mem_map_consistentP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply seq_st_mem_map_is_Some in H_inv.
    unfold seq_st_mem_map_is_SomeP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply seq_st_reg_map_consistent in H_inv.
    unfold seq_st_reg_map_consistentP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply seq_st_reg_map_is_Some in H_inv.
    unfold seq_st_reg_map_is_SomeP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply mem_writes_succeed in H_inv.
    unfold mem_writes_succeedP in *.
    cbn.
    set_unfold.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply pcdst_mem_acc_legal in H_inv.
    unfold pcdst_mem_acc_legalP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    apply H_inv.
  - apply pcdst_mem_map_inv in H_inv.
    unfold pcdst_mem_map_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    apply H_inv.
  - apply pcdst_mem_set_map_inv in H_inv.
    unfold pcdst_mem_set_map_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    apply H_inv.
  - apply pcdst_reg_map_inv in H_inv.
    unfold pcdst_reg_map_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    apply H_inv.
  - apply cdst_co_acc_inv in H_inv.
    unfold cdst_co_acc_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    apply H_inv.
  - apply cdst_rf_acc_inv in H_inv.
    unfold cdst_rf_acc_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    apply H_inv.
  - apply cdst_rrf_acc_inv in H_inv.
    unfold cdst_rrf_acc_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    apply H_inv.
  - apply cdst_mem_reads_inv in H_inv.
    unfold cdst_mem_reads_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    apply H_inv.
  - apply cdst_reg_reads_inv in H_inv.
    unfold cdst_reg_reads_invP in *.
    cbn.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_inv.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    apply H_inv.
  - opose proof (cd_from_seq_state_monotone st H_inv).
    unfold cd_monotone in *.
    cbn in *.
    rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    done.
  - opose proof (cd_wf _ H_inv).
    unfold cd in H.
    destruct H as [? [] [] [] []].
    constructor.
    2-5: constructor.
    all: unfold Candidate.has_only_supported_events, Candidate.initial_reg_reads,
      Candidate.is_valid_init_reg_read, Candidate.is_valid_init_mem_read,
      GenAxiomaticArm.AxArmNames.rmw, GenAxiomaticArm.AxArmNames.fre,
      GenAxiomaticArm.AxArmNames.coe, GenAxiomaticArm.AxArmNames.coi,
      Candidate.init_mem_reads, Candidate.is_nms, Candidate.is_valid_rf,
      Candidate.atomic_update, GenAxiomaticArm.AxArmNames.fri,
      GenAxiomaticArm.AxArmNames.fr, Candidate.writes_by_kind,
      Candidate.full_instruction_order, GenAxiomaticArm.AxArmNames.co,
      GenAxiomaticArm.AxArmNames.rf, Candidate.reg_from_reads,
      Candidate.explicit_reads, Candidate.reads_by_kind, Candidate.from_reads,
      Candidate.reg_reads, Candidate.instruction_order, Candidate.same_thread,
      Candidate.overlapping, Candidate.same_reg, Candidate.same_pa,
      Candidate.same_size, Candidate.reg_writes, Candidate.full_instruction_order,
      Candidate.instruction_order, Candidate.iio, Candidate.same_instruction_instance,
      Candidate.mem_events, Candidate.explicit_writes, Candidate.mem_writes,
      Candidate.mem_reads, Candidate.writes_by_kind,
      Candidate.same_footprint in *; cbn in *.
    all: try setoid_rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    all: try setoid_rewrite (collect_all_equal_events _ _ (event_list_unchanged_by_cons_empty_trace _ _)).
    all: try setoid_rewrite (same_key_equal_events _ _ _ (event_list_unchanged_by_cons_empty_trace _ _)).
    all: try setoid_rewrite iEvent_list_unchanged_by_cons_empty_trace.
    all: try setoid_rewrite (set_filter_iff _ _ _ (is_overlapping_equal_events_filter_predicate _ _ (event_list_unchanged_by_cons_empty_trace (initSt st) (itrs st)))).
    all: try setoid_rewrite (is_overlapping_equal_events _ _ (event_list_unchanged_by_cons_empty_trace (initSt st) (itrs st))).
    all: try assumption.
    1: intros [a b] Hrw; ospecialize (rf_valid (a, b) _).
    1: by rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace in Hrw.
    2: intros reid Hrw; ospecialize (rf_valid_initial reid _); eauto.
    all: cdestruct rf_valid, rf_valid_initial |- *** #CDestrEqOpt.
    all: eexists; cdestruct |- *** #CDestrEqOpt.
    all: setoid_rewrite lookup_unfold.
    all: repeat (eexists; cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal).
  - opose proof (cd_from_seq_state_consistent _ H_inv).
    unfold cd in *.
    setoid_rewrite construct_cd_for_pe_unchanged_by_cons_empty_trace.
    destruct H.
    constructor.
    all: unfold GenAxiomaticArm.AxArmNames.rmw, GenAxiomaticArm.AxArmNames.fre,
      GenAxiomaticArm.AxArmNames.coe, GenAxiomaticArm.AxArmNames.coi,
      Candidate.init_mem_reads, Candidate.is_nms,
      Candidate.atomic_update, GenAxiomaticArm.AxArmNames.fri,
      GenAxiomaticArm.AxArmNames.fr, Candidate.writes_by_kind,
      Candidate.full_instruction_order, GenAxiomaticArm.AxArmNames.co,
      GenAxiomaticArm.AxArmNames.rf, Candidate.reg_from_reads,
      Candidate.explicit_reads, Candidate.reads_by_kind, Candidate.from_reads,
      Candidate.reg_reads, Candidate.instruction_order, Candidate.same_thread,
      Candidate.overlapping, Candidate.same_reg, Candidate.same_pa,
      Candidate.same_size, Candidate.reg_writes, Candidate.full_instruction_order,
      Candidate.instruction_order, Candidate.iio, Candidate.same_instruction_instance,
      Candidate.mem_events, Candidate.explicit_writes, Candidate.mem_writes,
      Candidate.mem_reads, Candidate.writes_by_kind,
      Candidate.same_footprint in *; cbn in *.
    all: try setoid_rewrite (collect_all_equal_events _ _ (event_list_unchanged_by_cons_empty_trace _ _)).
    all: try setoid_rewrite (same_key_equal_events _ _ _ (event_list_unchanged_by_cons_empty_trace _ _)).
    all: try setoid_rewrite (set_filter_iff _ _ _ (is_overlapping_equal_events_filter_predicate _ _ (event_list_unchanged_by_cons_empty_trace (initSt st) (itrs st)))).
    all: try assumption.
Qed.

#[local] Instance eq_some_unfold_trace_rev_empty eid x :
  EqSomeUnfold (trace_rev [] !! eid) x False.
Proof. tcclean. destruct eid as [[] ? ? []]; cbv. all: naive_solver. Qed.

Lemma empty_seq_state_fulfills_seq_inv_predicate initSt :
  seq_inv_predicate {| initSt := initSt; mem := ∅; regs := ∅; itrs := [] |}.
Proof.
  constructor; cbn.
  all: try (intro; deintro).
  all: unfold cd_monotone, rel_strictly_monotone.
  all: cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  all: constructor.
  2-5: constructor.
  all: try (intro; deintro).
  all: cdestruct |- ***.
  1: set_solver.
  setoid_rewrite grel_plus_spec.
  unfold grel_to_relation in *.
  intros [H|H].
  all: set_unfold.
  all: cdestruct H |- *** #CDestrSplitGoal.
Qed.

Lemma trace_tail_preserves_nms init itrs ev :
  Candidate.is_nms (build_pre_exec init (trace_cons ev itrs)) →
  Candidate.is_nms (build_pre_exec init itrs).
Proof.
  unfold Candidate.is_nms.
  set_unfold.
  cdestruct |- *** as H_succ eid1 eid2 H_init_overlapping H_eid1_mem H_eid2_mem.
  ospecialize (H_succ (eid1, eid2) _).
  2: {
    unfold Candidate.same_footprint, Candidate.same_pa, Candidate.same_size,
      Candidate.mem_events in *.
    set_unfold.
    cdestruct eid1, eid2 |- *** #CDestrEqOpt #CDestrSplitGoal.
    all: eexists _, _, _.
    all: cdestruct eid1, eid2 |- *** #CDestrEqOpt #CDestrSplitGoal.
  }
  clear H_succ.
  unfold Candidate.mem_events, Candidate.is_overlapping in *.
  set_unfold.
  cdestruct eid1, eid2 |- *** #CDestrEqOpt #CDestrSplitGoal.
  all: unfold is_mem_event, is_mem_writeP, is_mem_readP in *.
  all: do 4 (eexists; cdestruct eid1, eid2 |- *** #CDestrEqOpt #CDestrSplitGoal).
  all: unfold pa_overlap.
  all: left+right; assumption.
Qed.

Lemma seqmodel_successor_nms_implies_start_nms fuel isem final_st start_st fs :
  seq_state_is_nms final_st →
  (final_st, fs) ∈ sequential_model_seqmon (Some regs_whitelist) fuel isem start_st →
  seq_state_is_nms start_st.
Proof.
  intro final_nms.
  revert dependent start_st.
  elim fuel; clear fuel; cdestruct final_nms |- *** as #CDestrMatch #CDestrEqOpt.
  1: intros succ_nms.
  2: intros final_nms.
  all: intros fuel IH start_st succ_st H_succ_exec.
  1: intros ->.
  all: intros H_finalize.
  2: intros H_final_exec.
  all: cycle 1.
  1: opose proof (IH _ H_final_exec) as succ_nms.
  all: eapply seq_state_is_nms_trace_end in succ_nms.
  1: clear dependent final_st.
  all: eapply seq_state_is_nms_cons_empty_trace.
  all: eapply (cinterp_inv_induct_backwards _ isem seq_state_is_nms (λ _, True));
  first (clear -isem; induction isem as [|[|]]; constructor; sfirstorder).
  3,6: eauto.
  all: eauto.
  all: clear.
  all: unfold sequential_model_outcome_logged, fHandler_logger, seq_state_is_nms in *.
  all: cdestruct |- ***.
  all: opose proof (sequential_model_outcome_same_itrs _ _ _ _ _) as H_itrs; eauto.
  all: opose proof (sequential_model_outcome_same_initSt _ _ _ _ _) as H_init; eauto.
  all: rewrite ?H_itrs, ?H_init in *; clear H_itrs H_init.
  all: eapply trace_tail_preserves_nms.
  all: eassumption.
Qed.

Lemma op_model_exists_consistent_cd fuel isem initSt :
  isem_mem_acc_legal_length isem →
  ∀ st fs, seq_state_is_nms st →
    (st, fs) ∈
      sequential_model_seqmon (Some regs_whitelist) fuel isem
      {| initSt := initSt; regs := ∅; mem := ∅; itrs := [] |} → (* less critical but would be nice:  *)
    ∃ cd, cd.(Candidate.pre_exec) = (seq_state_to_pe st) ∧ (* let cd := instead of the exists *)
      consistent regs_whitelist cd ∧ Candidate.wf cd. (* ISA_match *)
Proof.
  intros Hmemlength ?? Hnms Hexec.
  enough (seq_inv_predicate st) as Hinv.
  1: exists (seq_state_to_cd st); by destruct Hinv.
  pose proof (empty_seq_state_fulfills_seq_inv_predicate initSt).
  generalize dependent {| initSt := initSt; mem := ∅; regs := ∅; itrs := [] |}.
  revert dependent isem st.
  elim fuel; clear fuel; cdestruct |- *** as fuel IH isem Hmemlength #CDestrMatch.
  1: intros one_inst_seqst init_seqst H_inst_cinterp one_inst_seqst_nms H_finalize
    H_inv_init.
  2: intros final_seqst final_seqst_nms init_seqst one_inst_seqst H_inst_cinterp
    H_finalize H_rest_exec H_inv_init.
  1: apply seq_inv_predicate_preserved_change_trace_end.
  all: cycle 1.
  1: eapply IH; eauto.
  1: apply seq_inv_predicate_preserved_change_trace_end.
  1: opose proof (seqmodel_successor_nms_implies_start_nms _ _ _ _ _ _ _)
    as one_inst_seqst_nms; eauto.
  1: clear dependent final_seqst.
  all: apply seq_state_is_nms_trace_end in one_inst_seqst_nms.
  all: revert one_inst_seqst_nms; pattern one_inst_seqst.
  all: eapply cinterp_inv_induct; last eauto.
  all: eauto.
  1,3: intros; by apply seq_inv_predicate_preserved_cons_empty_trace.
  all: clear.
  all: unfold sequential_model_outcome_logged, fHandler_logger.
  all: cdestruct |- *** as start_st call H_base H_call_legal succ_st ret H_exec
    H_succ_nms.
  all: eapply seq_model_seq_inv_predicate_preserved; eauto.
  all: eapply H_base.
  all: opose proof (sequential_model_outcome_same_itrs _ _ _ _ _) as H_itrs; eauto.
  all: opose proof (sequential_model_outcome_same_initSt _ _ _ _ _) as H_init; eauto.
  all: unfold seq_state_is_nms in *; cbn in *.
  all: rewrite ?H_itrs, ?H_init in *; clear H_itrs H_init.
  all: eapply trace_tail_preserves_nms.
  all: done.
Qed.

End Proof.
