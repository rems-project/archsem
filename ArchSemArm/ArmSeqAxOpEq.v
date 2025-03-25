Require Import ArmSeqModel UMSeqArm.
Require Import ArmInst.
From ASCommon Require Import Exec FMon Common Options GRel StateT.

Import CDestrUnfoldElemOf.
#[local] Existing Instance Exec.unfold.

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

Fixpoint find_last_aux {A} (P : A → Prop) `{∀ x, Decision (P x)} (acc : option A) (l : list A) : option A :=
  if l is a :: ar
  then find_last_aux P (if decide (P a) then Some a else acc) ar
  else acc.

Definition find_last {A} (P : A → Prop) `{∀ x, Decision (P x)} : list A → option A :=
  find_last_aux P None.

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

Fixpoint trace_find_last_aux (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
  (acc : option (FMon.fEvent outcome)) (itrs : list (iTrace ())) : option (FMon.fEvent outcome) :=
  match itrs with
  | ((itr, trend) :: itrr) =>
    trace_find_last_aux P (if find_last P itr is Some ev then Some ev else acc) itrr
  | [] => acc
  end.

Definition trace_find_last (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
  : list (iTrace ()) → option (FMon.fEvent outcome) :=
  trace_find_last_aux P None.

Lemma find_trace_rev_find_trace_list (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
  (acc : option (FMon.fEvent outcome)) (itrs : list (iTrace ()))
  : trace_find P (trace_rev itrs) = trace_find_last P itrs.
Proof.
  unfold trace_find_last.
  enough (∀ o, (if trace_find P (trace_rev itrs) is Some ev then Some ev else o)
                = trace_find_last_aux P o itrs)
  as <- by cdestruct |- *** #CDestrMatch.
  unfold trace_rev.
  induction itrs as [|[]]; cdestruct |- ***.
  rewrite trace_find_app.
  cbn.
  rewrite <- find_rev_find_last.
  setoid_rewrite <- IHitrs.
  cdestruct |- *** #CDestrMatch.
Qed.

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

Section Proof.
Context (regs_whitelist : option (gset reg)) (fuel : nat) (isem : iMon ()).

Notation seqmon := (Exec.t seq_state string).
Notation initss := {| initSt := initSt; regs := ∅; mem := ∅; itrs := [] |}.

Definition seqmon_pe (st : seq_state) : Candidate.pre Candidate.NMS 1 :=
  Candidate.make_pre _ st.(initSt) [# st.(itrs)].

Definition result_same_type_proj {T} (r : result T T) :=
  match r with
  | Ok t => t
  | Error t => t
  end.

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
Admitted.

Lemma pa_offset_in_range_write pa pa' offset size (v: bv (8*size)) st st' :
  (st', ()) ∈ write_mem_seq_state pa (bv_to_bytes 8 v) st
  → pa_addN pa offset = pa'
  → (offset < size)%N
  → mem st' !! pa' = Some (bv_get_byte 8 offset v).
Proof.
  remember (bv_to_bytes 8 v); deintro.
  induction l; cdestruct |- ***.
  - epose proof length_bv_to_bytes (8 * size) 8 v.
    enough (size = 0)%N by lia.
    rewrite <- Heql in *.
    cbn in *.
    unfold div_round_up in *.
    lia.
  - destruct offset.
    + rewrite pa_addN_zero in H0; subst.
      epose proof length_bv_to_bytes (8 * size) 8 v.
      rewrite div_round_up_divisible in *; last done.
      epose proof pa_not_in_range_write.
Admitted.


Lemma write_mem_seq_state_itrs bytes :
  ∀ st st' pa, (st', ()) ∈ write_mem_seq_state pa bytes st → itrs st' = itrs st.
Proof.
  induction bytes; cdestruct |- ***.
  change (itrs st) with (itrs (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)).
  eapply IHbytes, H.
Qed.

Lemma sequential_model_outcome_itrs st st' call r s :
  (st', r) ∈ sequential_model_outcome regs_whitelist s call st → itrs st' = itrs st.
Proof.
  destruct call;
  cdestruct |- *** #CDestrMatch;
  try naive_solver.
  all: unfold mthrow, Exec.throw_inst in *; try set_solver.
  eapply write_mem_seq_state_itrs.
  eauto.
Qed.

Lemma write_mem_seq_state_initSt bytes :
  ∀ st st' pa, (st', ()) ∈ write_mem_seq_state pa bytes st → initSt st' = initSt st.
Proof.
  induction bytes; cdestruct |- ***.
  change (initSt st) with (initSt (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)).
  eapply IHbytes, H.
Qed.

Lemma sequential_model_outcome_initSt st st' call r s :
  (st', r) ∈ sequential_model_outcome regs_whitelist s call st → initSt st' = initSt st.
Proof.
  destruct call;
  cdestruct |- *** #CDestrMatch;
  try naive_solver.
  all: unfold mthrow, Exec.throw_inst in *; try set_solver.
  eapply write_mem_seq_state_initSt.
  eauto.
Qed.

Context (max_size : N) {max_size_upper_limit : (max_size < Z.to_N (bv_modulus 52))%N}.

Definition tr_wf (str : result seq_state seq_state) : Prop :=
  match str with
  | Ok st =>
    (∀ ev ∈ st.(itrs), is_mem_write ev → is_mem_writeP (λ size _, (size < max_size)%N) ev)
  | Error _ => False
  end.

Lemma op_reads st call :
  tr_wf (Ok st) →
  op_mem_wf (Ok st) →
  ∀ st' ∈ Exec.to_state_result_list (sequential_model_outcome_logged regs_whitelist (Z.to_N (bv_modulus 52)) call st),
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
    by (erewrite write_mem_seq_state_itrs in Hsize |- *; eauto).
    eapply pa_not_in_range_write; eauto.
    rewrite length_bv_to_bytes.
    f_equal.
    now eapply div_round_up_divisible.
    }
  apply pa_in_range_spec in p.
  cdestruct p as offset H_pa H_offset.
  assert (mem st' !! pa = Some (bv_get_byte 8 offset (WriteReq.value wr))) as ->
  by (eapply pa_offset_in_range_write; eauto).
  cdestruct |- *** #CDestrSplitGoal.
  - eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
  - cdestruct v, pa |- ***.
    f_equal.
    unfold pa_addN, pa_addZ in H0; cbv in H0.
    destruct wr as [[]].
    cdestruct H0.
    eapply bv_add_Z_inj_l in H0; cdestruct H0 |- *** #CDestrSplitGoal #CDestrMatch; lia.
Admitted.

Context {et : Candidate.exec_type}.

Notation "( f <$>.)" := (fmap f) (only parsing) : stdpp_scope.

Record cd_state := {
  pa_write_map : gmap pa EID.t;
  reg_write_map : gmap reg EID.t;
  rf_acc : grel EID.t;
  rrf_acc : grel EID.t;
  co_acc : grel EID.t
}.

#[global] Instance eta_cd_state : Settable cd_state :=
  settable! Build_cd_state <pa_write_map;reg_write_map;rf_acc;rrf_acc;co_acc>.

Definition mem_write_upd_cd_state (pa : pa) (weid : EID.t) (st : cd_state) : cd_state :=
  let oprev_weid := st.(pa_write_map) !! pa in
  (if oprev_weid is Some prev_weid
  then set co_acc ({[((prev_weid,weid))]} ∪.) st
  else st)
  |> setv (lookup pa ∘ pa_write_map) (Some weid).

Definition mem_read_upd_cd_state (pa : pa) (reid : EID.t) (st : cd_state) : cd_state :=
  let oweid := st.(pa_write_map) !! pa in
  if oweid is Some weid
  then set rf_acc ({[((weid,reid))]} ∪.) st
  else st.

Definition reg_write_upd_cd_state (reg : reg) (weid : EID.t) : cd_state → cd_state :=
  setv (lookup reg ∘ reg_write_map) (Some weid).

Definition reg_read_upd_cd_state (reg : reg) (reid : EID.t) (st : cd_state) : cd_state :=
  let oweid := st.(reg_write_map) !! reg in
  if oweid is Some weid
  then set rrf_acc ({[((weid,reid))]} ∪.) st
  else st.

Definition construct_cd_for_pe_fold_aux st '(eid, ev) :=
  match ev with
  | MemWrite _ wr &→ inl _ => mem_write_upd_cd_state wr.(WriteReq.pa) eid st
  | MemRead _ rr &→ _ => mem_read_upd_cd_state rr.(ReadReq.pa) eid st
  | RegWrite reg _ _ &→ _ => reg_write_upd_cd_state reg eid st
  | RegRead reg _ &→ _ => reg_read_upd_cd_state reg eid st
  | _ => st
  end.
Arguments construct_cd_for_pe_fold_aux : simpl never.

Definition construct_cd_for_pe (pe : Candidate.pre Candidate.NMS 1) : cd_state → cd_state :=
  fold_left construct_cd_for_pe_fold_aux (Candidate.event_list pe).

Definition seq_state_to_pe (st : seq_state) : Candidate.pre Candidate.NMS 1 :=
  Candidate.make_pre Candidate.NMS st.(initSt) [# rev st.(itrs)].
Arguments seq_state_to_pe : simpl never.

Definition cd_state_to_cd (cdst : cd_state) (pe : Candidate.pre Candidate.NMS 1) : Candidate.t Candidate.NMS 1 :=
  Candidate.make _ pe cdst.(rf_acc) cdst.(rrf_acc) cdst.(co_acc) ∅.

Definition seq_cd_states_to_cd (seqst : seq_state) (cdst : cd_state) : Candidate.t Candidate.NMS 1 :=
  let pe := (seq_state_to_pe seqst) in
  cd_state_to_cd (construct_cd_for_pe pe cdst) pe.

Lemma seq_state_to_pe_eq st st' :
  st.(initSt) = st'.(initSt) → st.(itrs) = st'.(itrs) →
  seq_state_to_pe st = seq_state_to_pe st'.
Proof. unfold seq_state_to_pe. now intros -> ->. Qed.

Lemma op_model_to_cd seqst cdst call :
  let rwl := if regs_whitelist is Some rwl then rwl else ∅ in
  consistent rwl (seq_cd_states_to_cd seqst cdst) →
  ∀ seqst' ∈ Exec.to_state_result_list (sequential_model_outcome_logged regs_whitelist (Z.to_N (bv_modulus 52)) call seqst),
  is_Ok seqst' → consistent rwl (seq_cd_states_to_cd (result_same_type_proj seqst') cdst).
Proof.
  cdestruct |- *** as ? seqst' r Hseqst'.
  unfold sequential_model_outcome_logged, fHandler_logger in *.
  cdestruct seqst', Hseqst' |- ***.
  unfold seq_cd_states_to_cd, construct_cd_for_pe in *.
  repeat orewrite (seq_state_to_pe_eq _ (set itrs (trace_cons (call &→ r)) seqst)); cbn.
  2: eapply sequential_model_outcome_initSt; eauto.
  2: f_equal; eapply sequential_model_outcome_itrs; eauto.
  destruct seqst.
  cbv [set]; cbn.
  unfold trace_cons.
  unfold seq_state_to_pe in *.
  cbn -[Candidate.event_list] in *.

  pattern (@fold_left cd_state _ construct_cd_for_pe_fold_aux
  (@Candidate.iEvent_list Candidate.NMS 1
     (seq_state_to_pe
        (@set seq_state (list (iTrace ())) itrs
           (λ (f : list (iTrace ()) → list (iTrace ())) (x0 : seq_state),
              {| initSt := initSt x0; mem := mem x0; regs := regs x0; itrs := f (itrs x0) |}) (trace_cons (call &→ r)) x))) cdst).
  unfold seq_state_to_pe. cbn.
  eapply fold_left_inv_complete_list.
  Set Printing Implicit.
  cd_state_to_cd.

  constructor.

Theorem op_model_soundness max_mem_acc_size ax initSt:
  Model.Res.weaker
    ((Model.to_nc $ sequential_modelc regs_whitelist max_mem_acc_size fuel isem) 1 initSt)
    (Ax.to_Modelnc (et := Candidate.NMS) isem ax 1 initSt).
Proof.
  cdestruct |- *** as Ax_no_err.
  split.
  - cdestruct |- *** as axfs H_axfs.
    Transparent propset_bind propset_ret.
    unfold propset_bind in *.
    cdestruct axfs, H_axfs |- *** as [] m H_ofinst H_finst.
    exists m.
    destruct m; cbn in *.
    2,3: unfold mfail , set_mfail in *; set_solver.
    split.
    1: done.
    unfold mret, propset_ret in *.
    cdestruct finSt, H_ofinst.
    unfold elem_of, listset_elem_of in H_finst.
    cdestruct H_finst.
    destruct r; cbn in *.
    2: done.
Abort.

End Proof.
