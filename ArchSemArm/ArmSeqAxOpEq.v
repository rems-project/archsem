From ASCommon Require Import Options.
Require Import ArmSeqModel UMSeqArm.
Require Import ArmInst.
From ASCommon Require Import Exec FMon Common GRel StateT.

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

Definition trace_snoc (ev : FMon.fEvent outcome) (itrs : list (iTrace ())) : list (iTrace ()) :=
  let '(trs, (last_tr,tr_end)) := unsnoc_total FMon.FTNothing itrs in
  trs ++ [(last_tr ++ [ev],tr_end)].

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
Search last.
Lemma enumerate_imap {A} (l : list A) :
  enumerate l = imap pair l.
Admitted.

Definition intra_trace_eid_succ (tr : list (iTrace ())) : EID.t :=
  let '(trs, (last_tr,tr_end)) := unsnoc_total FMon.FTNothing tr in
  EID.make 0 (Nat.pred (length tr)) (length last_tr) None.

Lemma trace_snoc_event_list init tr ev :
  Candidate.event_list (Candidate.make_pre Candidate.NMS init [#trace_snoc ev tr]) =
  Candidate.event_list (Candidate.make_pre Candidate.NMS init [#tr]) ++
  [(intra_trace_eid_succ tr, ev)].
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

Section Proof.
Context (regs_whitelist : gset reg) (fuel : nat) (isem : iMon ()).

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

Lemma write_mem_seq_state_same_itrs bytes :
  ∀ st st' pa, (st', ()) ∈ write_mem_seq_state pa bytes st → itrs st' = itrs st.
Proof.
  induction bytes; cdestruct |- ***.
  change (itrs st) with (itrs (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)).
  eapply IHbytes, H.
Qed.

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
  by (eapply pa_offset_in_range_write; eauto).
  cdestruct |- *** #CDestrSplitGoal.
  - eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
  - cdestruct v, pa |- ***.
    f_equal.
    unfold pa_addN, pa_addZ in H0; cbv in H0.
    destruct wr as [[]].
    cdestruct H0.
    eapply bv_add_Z_inj_l in H0; cdestruct H0 |- *** #CDestrSplitGoal #CDestrMatch; try lia.
    all: admit.
Admitted.

Notation "( f <$>.)" := (fmap f) (only parsing) : stdpp_scope.

Record partial_cd_state := {
  pa_write_map : gmap pa EID.t;
  reg_write_map : gmap reg EID.t;
  rf_acc : grel EID.t;
  rrf_acc : grel EID.t;
  co_acc : grel EID.t
}.

#[local] Notation "cd∅" := (Build_partial_cd_state ∅ ∅ ∅ ∅ ∅).

#[global] Instance eta_partial_cd_state : Settable partial_cd_state :=
  settable! Build_partial_cd_state <pa_write_map;reg_write_map;rf_acc;rrf_acc;co_acc>.

Definition mem_write_upd_partial_cd_state (pa : pa) (weid : EID.t) (st : partial_cd_state) : partial_cd_state :=
  let oprev_weid := st.(pa_write_map) !! pa in
  (if oprev_weid is Some prev_weid
  then set co_acc ({[((prev_weid,weid))]} ∪.) st
  else st)
  |> setv (lookup pa ∘ pa_write_map) (Some weid).

Definition mem_read_upd_partial_cd_state (pa : pa) (reid : EID.t) (st : partial_cd_state) : partial_cd_state :=
  let oweid := st.(pa_write_map) !! pa in
  if oweid is Some weid
  then set rf_acc ({[((weid,reid))]} ∪.) st
  else st.

Definition reg_write_upd_partial_cd_state (reg : reg) (weid : EID.t) : partial_cd_state → partial_cd_state :=
  setv (lookup reg ∘ reg_write_map) (Some weid).

Definition reg_read_upd_partial_cd_state (reg : reg) (reid : EID.t) (st : partial_cd_state) : partial_cd_state :=
  let oweid := st.(reg_write_map) !! reg in
  if oweid is Some weid
  then set rrf_acc ({[((weid,reid))]} ∪.) st
  else st.

Definition update_partial_cd_state_for_eid_ev st '(eid, ev) :=
  match ev with
  | MemWrite _ wr &→ inl _ => mem_write_upd_partial_cd_state wr.(WriteReq.pa) eid st
  | MemRead _ rr &→ _ => mem_read_upd_partial_cd_state rr.(ReadReq.pa) eid st
  | RegWrite reg _ _ &→ _ => reg_write_upd_partial_cd_state reg eid st
  | RegRead reg _ &→ _ => reg_read_upd_partial_cd_state reg eid st
  | _ => st
  end.
Arguments update_partial_cd_state_for_eid_ev : simpl never.

Definition construct_cd_for_pe (pe : Candidate.pre Candidate.NMS 1) : partial_cd_state → partial_cd_state :=
  fold_left update_partial_cd_state_for_eid_ev (Candidate.event_list pe).

Definition seq_state_to_pe (st : seq_state) : Candidate.pre Candidate.NMS 1 :=
  Candidate.make_pre Candidate.NMS st.(initSt) [# trace_rev st.(itrs)].
Arguments seq_state_to_pe : simpl never.

Definition partial_cd_state_to_cd (cdst : partial_cd_state) (pe : Candidate.pre Candidate.NMS 1) : Candidate.t Candidate.NMS 1 :=
  Candidate.make _ pe cdst.(rf_acc) cdst.(rrf_acc) cdst.(co_acc) ∅.

Definition seq_partial_cd_states_to_partial_cd_state (seqst : seq_state) (cdst : partial_cd_state) : partial_cd_state :=
  (construct_cd_for_pe (seq_state_to_pe seqst) cdst).

Definition seq_partial_cd_states_to_cd (seqst : seq_state) (cdst : partial_cd_state) : Candidate.t Candidate.NMS 1 :=
  let pe := (seq_state_to_pe seqst) in
  partial_cd_state_to_cd (construct_cd_for_pe pe cdst) pe.

Definition seq_state_to_partial_cd_state (seq_st : seq_state) : partial_cd_state :=
  construct_cd_for_pe (seq_state_to_pe seq_st) cd∅.

Definition seq_state_to_cd (seq_st : seq_state) : Candidate.t Candidate.NMS 1 :=
  partial_cd_state_to_cd (seq_state_to_partial_cd_state seq_st) (seq_state_to_pe seq_st).

Lemma seq_state_to_pe_eq st st' :
  st.(initSt) = st'.(initSt) → st.(itrs) = st'.(itrs) →
  seq_state_to_pe st = seq_state_to_pe st'.
Proof. unfold seq_state_to_pe. now intros -> ->. Qed.

Lemma seq_state_step_to_pe_eq seq_st seq_st_succ call ret :
  (seq_st_succ, ret) ∈ sequential_model_outcome (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call seq_st →
  seq_state_to_pe (set itrs (trace_cons (call &→ ret)) seq_st_succ) = seq_state_to_pe (set itrs (trace_cons (call &→ ret)) seq_st).
Proof.
  cdestruct |- ***.
  eapply seq_state_to_pe_eq.
  all: cbn in *.
  1: eapply sequential_model_outcome_same_initSt; eauto.
  1: f_equal; eapply sequential_model_outcome_same_itrs; eauto.
Qed.

Lemma seq_state_to_pe_trace_cons seqst ev :
  seq_state_to_pe (set itrs (trace_cons ev) seqst) =
  set ((.!!! 0%fin) ∘ Candidate.events) (trace_snoc ev) (seq_state_to_pe seqst).
Proof.
  unfold seq_state_to_pe; cbv [set]; cbn; unfold Setter_compose; cbn.
  do 2 f_equal.
  unfold trace_snoc, unsnoc_total.
  destruct (itrs seqst); first done.
  now rewrite unsnoc_snoc.
Qed.

Definition rel_monotone (rel : grel EID.t) : Prop :=
  ∀ '(x,y) ∈ rel, EID.full_po_lt x y.

Definition cd_monotone (cd : Candidate.t Candidate.NMS 1) : Prop :=
  rel_monotone cd.(Candidate.reads_from)
  ∧ rel_monotone cd.(Candidate.reg_reads_from)
  ∧ rel_monotone cd.(Candidate.coherence).

Definition partial_cd_state_monotone (cdst : partial_cd_state) : Prop :=
  rel_monotone cdst.(rf_acc)
  ∧ rel_monotone cdst.(rrf_acc)
  ∧ rel_monotone cdst.(co_acc).

Lemma event_list_monotone {nmth} (pe : Candidate.pre Candidate.NMS nmth) l l' :
  Candidate.event_list pe = l ++ l' →
  ∀ '(eid1, ev1) ∈ l, ∀ '(eid2, ev2) ∈ l', eid1.(EID.tid) = eid2.(EID.tid) →
  EID.full_po_lt eid1 eid2.
Admitted.

Arguments Candidate.event_list : simpl never.

Definition seq_model_state_handler_invariant_statement (I : seq_state → Prop) : Prop :=
  ∀ (seq_st : seq_state) (call : outcome),
  I seq_st →
  ∀ seq_st_succ,
  Ok seq_st_succ ∈ Exec.to_state_result_list (sequential_model_outcome_logged (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call seq_st) →
  I seq_st_succ.

Lemma seq_state_step_to_partial_cd_state I seq_st seq_st_succ call ret :
  (seq_st_succ, ret) ∈ sequential_model_outcome (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call seq_st →
  I (update_partial_cd_state_for_eid_ev (seq_state_to_partial_cd_state seq_st)
      (intra_trace_eid_succ (Candidate.events (seq_state_to_pe seq_st) !!! 0%fin), call &→ ret)) →
  I (seq_state_to_partial_cd_state (set itrs (trace_cons (call &→ ret)) seq_st_succ)).
Proof.
  unfold seq_state_to_partial_cd_state, construct_cd_for_pe.
  cdestruct |- ***.
  erewrite seq_state_to_pe_trace_cons, seq_state_to_pe_eq, trace_snoc_event_list.
  2: eapply sequential_model_outcome_same_initSt; eauto.
  2: eapply sequential_model_outcome_same_itrs; eauto.
  rewrite fold_left_app.
  eapply X.
Qed.

Record seq_inv_predicate (seq_st : seq_state) := {
  partial_cd_state_from_seq_state_maps_eids_wf :
    let pcdst := seq_state_to_partial_cd_state seq_st in
    let evs := Candidate.event_list $ seq_state_to_pe seq_st in
    ∀ eid pa reg, pcdst.(pa_write_map) !! pa = Some eid ∨ pcdst.(reg_write_map) !! reg = Some eid
    → eid ∈ fst <$> evs;
  cd_from_seq_state_monotone : cd_monotone (seq_state_to_cd seq_st);
  cd_from_seq_state_consistent : consistent regs_whitelist (seq_state_to_cd seq_st)
}.

Lemma seq_model_consistent :
  seq_model_state_handler_invariant_statement seq_inv_predicate.
Proof.
  unfold seq_model_state_handler_invariant_statement, sequential_model_outcome_logged, fHandler_logger.
  cdestruct |- *** as seq_st call [] seq_st_succ ret H_seq_st_succ.
  constructor; unfold seq_state_to_cd.
  - erewrite seq_state_step_to_pe_eq, seq_state_to_pe_trace_cons, trace_snoc_event_list; last eauto.
    eapply seq_state_step_to_partial_cd_state; first eauto.
    cdestruct |- ***.
    autorewrite with pair.
    eexists eid.
    destruct call;
    unfold update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
    mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state in *;
    cdestruct H |- *** #CDestrMatch #CDestrSplitGoal;
    eexists;
    cdestruct |- *** #CDestrSplitGoal.
    all: destruct (decide (eid = intra_trace_eid_succ (Candidate.events (seq_state_to_pe seq_st) !!! 0%fin))) as [->|];
    [right; eauto|left].
    all: set_unfold in partial_cd_state_from_seq_state_maps_eids_wf0.
    all: cdestruct partial_cd_state_from_seq_state_maps_eids_wf0.
    all: odestruct (partial_cd_state_from_seq_state_maps_eids_wf0 _ _ _ _).
    1: right;eauto.
    1: cdestruct x, H1.
    1: admit.
    1: best.
    1: eapply partial_cd_state_from_seq_state_maps_eids_wf0.

  .
    unfold seq_state_to_partial_cd_state in H.

  unfold cd_monotone in *.
    cdestruct cd_from_seq_state_monotone0 |- *** #CDestrSplitGoal.
    + eapply seq_state_step_to_partial_cd_state; first eauto.
      generalize dependent (seq_state_to_partial_cd_state seq_st).
      cdestruct |- ***.
     unfold seq_state_to_partial_cd_state in *.
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
