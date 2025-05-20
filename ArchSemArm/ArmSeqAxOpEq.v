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

Lemma find_trace_rev_find_trace_last (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
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
Search last.
Lemma enumerate_imap {A} (l : list A) :
  enumerate l = imap pair l.
Admitted.

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

#[export] Instance lookup_unfold_traces_snoc {et nmth} (init : MState.t nmth) evs (ev : iEvent) thread (eid : EID.t) R :
  LookupUnfold eid (Candidate.make_pre et init evs) R →
  LookupUnfold eid (Candidate.make_pre et init (traces_snoc ev thread evs))
    (if eid =? intra_trace_eid_succ (fin_to_nat thread) (evs !!! thread) then Some ev else R).
Proof.
  tcclean.
  cdestruct |- *** #CDestrMatch.
  - rewrite H0 in *.
    unfold lookup, Candidate.lookup_eid_pre, Candidate.lookup_iEvent, Candidate.lookup_instruction in H |- *.
    rewrite intra_trace_eid_succ_tid in *.
    cbn in *.
    unfold traces_snoc, set, Setter_valter, alter, valter.
    destruct (evs !!! thread) eqn:Hvl; cbn in *;
    pose proof Hvl as Hl; eapply vlookup_lookup in Hl;
    rewrite ?Hvl, ?Hl.
Admitted.

#[export] Instance lookup_unfold_trace_snoc {et} (init : MState.t 1) evs (ev : iEvent) (eid : EID.t) R :
  LookupUnfold eid (Candidate.make_pre et init [# evs]) R →
  LookupUnfold eid (Candidate.make_pre et init [# trace_snoc ev evs])
    (if eid =? intra_trace_eid_succ 0 evs then Some ev else R).
Proof.
  tcclean.
  cdestruct eid, H |- *** #CDestrMatch.
Admitted.

#[export] Instance lookup_unfold_intra_traces_eid_succ_None {nmth et} (init : MState.t nmth) trs (tid : Fin.t nmth) :
  LookupUnfold (intra_trace_eid_succ tid (trs !!! tid)) (Candidate.make_pre et init trs) None.
Admitted.

Lemma cd_to_pe_lookup `(cd : Candidate.t et nmth) eid :
  cd !! eid = Candidate.pre_exec cd !! eid.
Proof. reflexivity. Qed.

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

Lemma collect_all_trace_snoc_subset {nmth}  `{∀ eid ev, Decision (P eid ev)}
    (pe : Candidate.pre Candidate.NMS nmth) ev tid :
  Candidate.collect_all P pe ⊆
  Candidate.collect_all P (set Candidate.events (traces_snoc ev tid) pe).
Proof.
  set_unfold.
  cdestruct |- *** as x ? H_lookup HP.
  unfold set.
  rewrite lookup_unfold.
  cdestruct |- *** as Hx #CDestrMatch.
  2: eexists; eauto.
  subst.
  destruct pe; cbn in *.
  now rewrite lookup_unfold in H_lookup.
Qed.

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
  admit. (* TODO : Transitive full_po_lt *)
Admitted.
Lemma rel_strictly_monotone_seq2 (rel1 rel2 : grel EID.t) :
  rel_monotone rel1 ∧ rel_strictly_monotone rel2 → rel_strictly_monotone (rel1 ⨾ rel2).
Proof.
  unfold rel_strictly_monotone, rel_monotone.
  autorewrite with pair.
  cdestruct |- *** #CDestrSplitGoal.
  admit. (* TODO : Transitive full_po_lt *)
Admitted.

Lemma rel_montone_acyclic (rel : grel EID.t) :
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
Admitted. *)

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
  | MemWrite _ wr &→ _ => mem_write_upd_partial_cd_state wr.(WriteReq.pa) eid st
  | MemRead _ rr &→ _ => mem_read_upd_partial_cd_state rr.(ReadReq.pa) eid st
  | RegWrite reg _ _ &→ _ => reg_write_upd_partial_cd_state reg eid st
  | RegRead reg _ &→ _ => reg_read_upd_partial_cd_state reg eid st
  | _ => st
  end.
Arguments update_partial_cd_state_for_eid_ev : simpl never.
Arguments mem_write_upd_partial_cd_state : simpl never.


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

Lemma seq_state_to_pe_trace_cons seqst ev :
  (seq_state_to_pe (set itrs (trace_cons ev) seqst)) =
  set ((.!!! 0%fin) ∘ Candidate.events) (trace_snoc ev) (seq_state_to_pe seqst).
Proof.
  unfold build_pre_exec; cbv [set]; cbn; unfold Setter_compose; cbn.
  do 2 f_equal.
  unfold trace_snoc, unsnoc_total.
  destruct (itrs seqst); first done.
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

#[local] Instance lookup_ev_from_iTraces : Lookup EID.t iEvent (list (iTrace ())) :=
  λ eid evs,
  '(trace, result) ← evs !! eid.(EID.iid);
  trace !! eid.(EID.ieid).

  (* #[local] Instance lookup_ev_from_iTraces {nmth : nat} : Lookup EID.t iEvent (vec (list (iTrace ())) nmth) :=
  λ eid evs,
  traces ← evs !! eid.(EID.tid);
  '(trace, result) ← traces !! eid.(EID.iid);
  trace !! eid.(EID.ieid). *)

#[local] Instance lookup_unfold_vec_singleton (n : nat) `(v : A) :
  LookupUnfold n [#v] (if decide (n = 0) then Some v else None).
Proof.
  tcclean.
  unfold lookup, vec_lookup_nat.
  cdestruct n |- *** #CDestrMatch; lia.
Qed.

#[local] Instance lookup_unfold_seq_state_to_cd (eid : EID.t) seqst o :
  LookupUnfold eid (trace_rev seqst.(itrs)) o →
  LookupUnfold eid (seq_state_to_cd seqst) (if decide (eid.(EID.tid) = 0 ∧ eid.(EID.byte) = None) then o else None).
Proof.
  tcclean.
  destruct eid; subst.
  rewrite cd_to_pe_lookup.
  unfold lookup, Candidate.lookup_eid_pre, Candidate.lookup_iEvent,
    Candidate.lookup_instruction, partial_cd_state_to_cd,
    lookup_ev_from_iTraces, build_pre_exec in *.
  cdestruct tid, byte |- *** #CDestrMatch.
  all: rewrite lookup_unfold.
  all: cdestruct |- *** #CDestrMatch.
  all: destruct (trace_rev (itrs seqst) !! iid) as [[l ?]|].
  all: cdestruct |- ***.
  all: destruct (l !! ieid); cdestruct |- *** #CDestrEqOpt #CDestrSplitGoal.
  set_unfold.
  intros ->.
  naive_solver.
Qed.

#[global] Instance lookup_unfold_length_None {A} (l : list A) :
  LookupUnfold (length l) l None.
Proof. tcclean. induction l; done. Qed.

#[global] Instance lookup_unfold_Nil `(l : list A) n :
  LookupUnfold n [] None.
Proof. tcclean. done. Qed.

#[local] Instance lookup_unfold_partial_cd_state_to_cd eid pcdst pe o :
  LookupUnfold eid pe o →
  LookupUnfold eid (partial_cd_state_to_cd pcdst pe) o.
Proof. tcclean. rewrite cd_to_pe_lookup. now unfold partial_cd_state_to_cd. Qed.

#[local] Instance lookup_seq_state_to_pe eid seq_st o :
  LookupUnfold eid (trace_rev seq_st.(itrs)) o →
  LookupUnfold eid (seq_state_to_pe seq_st)
  (if decide (eid.(EID.tid) = 0 ∧ eid.(EID.byte) = None) then o else None).
Proof.
  tcclean.
  unfold build_pre_exec.
  unfold lookup, Candidate.lookup_eid_pre, lookup_ev_from_iTraces, Candidate.lookup_iEvent, Candidate.lookup_instruction.
  cdestruct o, eid, seq_st, H |- *** #CDestrMatch #CDestrSplitGoal #CDestrEqOpt.
  all: rewrite lookup_unfold.
  all: cdestruct |- *** #CDestrMatch.
  all: destruct (trace_rev (itrs seq_st) !! EID.iid eid) as [[]|].
  all: cdestruct |- ***.
  all: destruct (l !! EID.ieid eid).
  all: cdestruct |- *** #CDestrEqOpt.
  all: sauto lq: on.
Qed.

(* #[global] Instance cdestruct_nat_sub_daig_0 b x P :
  CDestrSimpl b (P (x - x)) (P 0).
Proof. tcclean. by rewrite Nat.sub_diag. Qed. *)

(* Goal ∀ `(l : list A), l !! (length l) = None.
Set Typeclasses Debug Verbosity 2.
intros. rewrite lookup_unfold. *)

#[local] Instance lookup_unfold_trace_rev_cons (eid : EID.t) ev seqst o :
  LookupUnfold eid (trace_rev seqst.(itrs)) o →
  LookupUnfold eid (trace_rev (set itrs (trace_cons ev) seqst).(itrs))
    (let succ_eid := intra_trace_eid_succ 0 (trace_rev seqst.(itrs)) in
      if decide (eid.(EID.iid) = succ_eid.(EID.iid) ∧ eid.(EID.ieid) = succ_eid.(EID.ieid))
    then Some ev
    else
      (if decide (eid.(EID.iid) < succ_eid.(EID.iid)
        ∨ eid.(EID.iid) = succ_eid.(EID.iid) ∧ eid.(EID.ieid) < succ_eid.(EID.ieid))
      then o
      else None)).
Proof.
  tcclean.
  unfold trace_rev, lookup, lookup_ev_from_iTraces, trace_cons in *.
  destruct eid as [?[][]?], seqst, itrs; cbn;
  cdestruct H |- *** as #CDestrMatch #CDestrSplitGoal.
  all: rename itrs into it.
  all: destruct (rev (map (set fst (rev (A:=fEvent outcome))) it)) as [|??] eqn: ?.
  all: destruct i eqn: ?.
  all: cdestruct |- ***.
  all: rewrite ?lookup_app.
  all: cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
  all: destruct (rev l) eqn: ?.
  all: cbn in *.
  all: try scongruence.
  all: unfold intra_trace_eid_succ, unsnoc_total in *.
  all: rewrite ?app_comm_cons, ?unsnoc_snoc in *.
  all: cbn in *.
  all: rewrite ?length_app in *.
  all: cbn in *.
  all: try solve [destruct (length l); lia].
  all: try eapply eq_add_S in H1.
  all: subst.
  (* 1: opose proof (lookup_unfold_length_None l0) as [].
  1: erewrite lookup_unfold in H0. *)
  (* 1: rewrite lookup_unfold in H0. *)

(*   all: inversion H1; subst.
  all: rewrite ?lookup_unfold in *.
  1: unshelve erewrite lookup_unfold in *; try eapply lookup_unfold_length_None; done.
  all: cdestruct |- ***.
  all: rewrite ?Nat.sub_diag in *.
  all: cdestruct |- ***.
  all: try eapply lookup_ge_None in H1.
  1: assert (n - length l0 >= 1) by admit; admit.
  1: admit.
  1: admit.
  1,2: try assert (n - length l = 0) as -> by admit; cbn; admit.
  all: destruct (Init.Nat.sub n (@Datatypes.length (iTrace unit) l)) eqn: ?; cbn.
  all: try lia.
  all: try done.
  all: destruct (rev l0); cbn in *. *)
Admitted.

#[export] Instance lookup_unfold_intra_trace_eid_succ_None evs :
  LookupUnfold (intra_trace_eid_succ 0 evs) evs None.
Proof.
  tcclean.
  unfold intra_trace_eid_succ.
  destruct (decide (evs = [])) as [->|Hevs_not_empty]; cdestruct |- ***.
  destruct (exists_last Hevs_not_empty)as [? [[] ->]].
  unfold unsnoc_total.
  rewrite unsnoc_snoc.
  unfold lookup, lookup_ev_from_iTraces.
  cdestruct |- ***.
  rewrite length_app; cbn.
  replace (Nat.pred (length x + 1)) with (length x) by lia.
  rewrite lookup_app.
  cdestruct |- *** as #CDestrMatch; rewrite lookup_unfold.
  1: scongruence.
  intros.
  rewrite Nat.sub_diag; cbn.
  by rewrite lookup_unfold.
Qed.

#[export] Instance lookup_unfold_pe_intra_trace_eid_succ_None {et} (init : MState.t 1) evs :
  LookupUnfold (intra_trace_eid_succ 0 evs) (Candidate.make_pre et init [# evs]) None.
Proof.
  tcclean.
  unfold intra_trace_eid_succ.
  destruct (decide (evs = [])) as [->|Hevs_not_empty]; cdestruct |- ***.
  destruct (exists_last Hevs_not_empty)as [? [[] ->]].
  unfold unsnoc_total.
  rewrite unsnoc_snoc.
  unfold lookup, Candidate.lookup_eid_pre, Candidate.lookup_iEvent, Candidate.lookup_instruction;
  cdestruct |- ***; unfold lookup at 3, vec_lookup_nat; cdestruct |- *** #CDestrMatch.
  rewrite length_app; cbn.
  replace (Nat.pred (length x + 1)) with (length x) by lia.
  rewrite lookup_app.
  cdestruct |- *** as #CDestrMatch; first (intros ???%lookup_length; lia).
  intros.
  rewrite Nat.sub_diag; cbn.
  destruct (l !! length l) eqn: Hl; cdestruct |- ***.
  pose proof (lookup_length _ _ _ _ Hl).
  unfold iEvent in *; lia.
Qed.

#[local] Instance lookup_unfold_cd_to_pe `(cd : Candidate.t et nmth) eid o :
  LookupUnfold eid cd o →
  LookupUnfold eid (Candidate.pre_exec cd) o.
Proof. tcclean. now rewrite cd_to_pe_lookup. Qed.

#[local] Instance lookup_total_unfold_vec_singleton (n : fin 1) `(x : A) :
  LookupTotalUnfold n [#x] x.
Proof.
  tcclean.
  depelim n.
  1: done.
  depelim n1.
Qed.

#[local] Instance lookup_total_unfold_events_build_pre_exec (n : fin 1) init itrs :
  LookupTotalUnfold n (Candidate.events (build_pre_exec init itrs)) (trace_rev itrs).
Proof.
  depelim n.
  2: sauto q: on.
  tcclean.
  by unfold build_pre_exec.
Qed.


#[local] Instance lookup_unfold_build_pre_exec_trace_cons_tail initSt itrs eid ev o :
  LookupUnfold eid (build_pre_exec initSt itrs) o →
  LookupUnfold eid (build_pre_exec initSt (trace_cons ev itrs))
    (if decide (is_Some o)
    then o
    else
      if decide (eid = intra_trace_eid_succ 0 (trace_rev itrs))
      then Some ev
      else None).
Proof.
  tcclean.
  unfold build_pre_exec, lookup, Candidate.lookup_eid_pre, Candidate.lookup_iEvent, Candidate.lookup_instruction, trace_cons in *.
  destruct eid.
  cdestruct H |- *** #CDestrEqOpt.
(*   assert (tid = 0) as -> by lia.
  rewrite lookup_total_unfold in H.
  rewrite ?lookup_unfold.
  cdestruct |- *** #CDestrMatch.
  rewrite H; cbn.
  rewrite H0; cbn.
  destruct itrs.
  (* destruct (decide (itrs = [])) as [->|Hitrs]. *)
  1: cbn in *; rewrite lookup_unfold in *; destruct iid; done.
  (* opose proof (exists_last Hitrs) as [l' [? ->]]. *)
  cbn in *.
  rewrite ?lookup_app in *.
  cdestruct H |- *** #CDestrMatch.
  1: by rewrite H0.
  opose proof (lookup_lt_is_Some_1 _ _ _).
  1: eexists; eapply H2.
  cbn in *.
  eapply Nat.lt_1_r in H3.
  rewrite H3 in *.
  destruct i.
  unfold set in *.
  cdestruct l0, l, H0, H, H2, H3 |- ***.
  by rewrite lookup_app, H0. *)
Admitted.

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
  ∀ (call : outcome) seq_st_succ,
  Ok seq_st_succ ∈ Exec.to_state_result_list (sequential_model_outcome_logged (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call seq_st) →
  I' seq_st_succ.

Lemma seq_state_to_partial_cd_state_destruct (I : partial_cd_state → Prop) seq_st call ret :
  let succ_eid := intra_trace_eid_succ 0 (Candidate.events (seq_state_to_pe seq_st) !!! 0%fin) in
  let pcdst := (seq_state_to_partial_cd_state seq_st) in
  (¬ is_mem_event (call &→ ret) → ¬ is_reg_write (call &→ ret) → ¬ is_reg_read (call &→ ret) → I pcdst) →
  (∀ reg racc, call = RegRead reg racc → I (reg_read_upd_partial_cd_state reg succ_eid pcdst)) →
  (∀ reg racc regval, call = RegWrite reg racc regval → I (reg_write_upd_partial_cd_state reg succ_eid pcdst)) →
  (∀ n rr, call = MemRead n rr → I (mem_read_upd_partial_cd_state rr.(ReadReq.pa) succ_eid pcdst)) →
  (∀ n wr, call = MemWrite n wr → I (mem_write_upd_partial_cd_state wr.(WriteReq.pa) succ_eid pcdst)) →
  I (seq_state_to_partial_cd_state (set itrs (trace_cons (call &→ ret)) seq_st)).
Proof.
  intro.
  unfold construct_cd_for_pe.
  destruct call.
  all: cdestruct |- ***.
  all: erewrite seq_state_to_pe_trace_cons, trace_snoc_event_list.
  all: rewrite fold_left_app.
  all: hauto lq: on.
Qed.

Lemma seq_state_to_pe_fold seq_st :
  {| Candidate.init := Candidate.init (seq_state_to_pe seq_st);
    Candidate.events := [#Candidate.events (seq_state_to_pe seq_st) !!! 0%fin] |}
  = (seq_state_to_pe seq_st).
Proof. unfold build_pre_exec. cdestruct |- ***. Qed.

Definition mem_writes_succeedP seq_st :=
  let cd := (seq_state_to_cd seq_st) in
  let evs := Candidate.event_list cd in
  ∀ ev ∈ evs.*2, is_mem_write_req ev →
  is_mem_write_reqP (λ _ _ ret, if ret is inl b then b = true else False) ev.

Definition partial_cd_state_mem_map_invP seq_st :=
  let pcdst := (seq_state_to_partial_cd_state seq_st) in
  let cd := (seq_state_to_cd seq_st) in
  ∀ eid pa, pcdst.(pa_write_map) !! pa = Some eid →
    ∃ ev, is_mem_writeP (λ _ wr, wr.(WriteReq.pa) = pa) ev ∧ cd !! eid = Some ev
      ∧ (∀ eid' ev', cd !! eid' = Some ev' →
         is_mem_writeP (λ _ wr, wr.(WriteReq.pa) = pa) ev' →
         eid' = eid ∨
         EID.full_po_lt eid' eid).

Lemma partial_cd_state_mem_map_inv_seq_state_equal s1 s2 :
  itrs s1 = itrs s2 →
  partial_cd_state_mem_map_invP s1 = partial_cd_state_mem_map_invP s2.
Proof. unfold partial_cd_state_mem_map_invP. by intros ->. Qed.

Lemma seq_state_trace_cons_equal s1 s2 ev :
  itrs s1 = itrs s2 →
  (set itrs (trace_cons ev) s1).(itrs) = (set itrs (trace_cons ev) s2).(itrs).
Proof. destruct s1, s2. cbn. by intros ->. Qed.

Definition partial_cd_state_reg_map_invP seq_st :=
  let pcdst := (seq_state_to_partial_cd_state seq_st) in
  let cd := (seq_state_to_cd seq_st) in
  ∀ eid reg, pcdst.(reg_write_map) !! reg = Some eid →
  ∃ ev, is_reg_writeP (λ reg' _ _, reg' = reg) ev ∧ cd !! eid = Some ev ∧
    (∀ eid' ev', cd !! eid' = Some ev' →
      is_reg_writeP (λ reg' _ _, reg' = reg) ev' →
      eid' = eid ∨ EID.full_po_lt eid' eid).

Record seq_inv_predicate (seq_st : seq_state) := {
  pcdst := (seq_state_to_partial_cd_state seq_st);
  cd := (seq_state_to_cd seq_st);
  evs := Candidate.event_list cd;
  mem_writes_succeed : mem_writes_succeedP seq_st;
  partial_cd_state_mem_map_inv : partial_cd_state_mem_map_invP seq_st;
  partial_cd_state_reg_map_inv : partial_cd_state_reg_map_invP seq_st;
  cd_from_seq_state_monotone : cd_monotone cd;
  cd_wf : Candidate.wf cd;
  cd_from_seq_state_consistent : consistent regs_whitelist cd
}.

#[local] Typeclasses Transparent mword Z.to_N Decision RelDecision Decidable_eq_mword eq_vec_dec MachineWord.MachineWord.Z_idx.

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

Lemma if_distribution_option `(f : A → B) `(o : option C) (g : C → A) a :
  f (if o is Some c then g c else a) = (if o is Some c then f (g c) else f a).
Proof. by destruct o. Qed.

Lemma if_indiscriminate_cases_option {B} `(x : option A) (y z : B) :
  y = z → (if x is Some c then y else z) = y.
Proof. by destruct x. Qed.

Lemma seq_model_mem_writes_succeed_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate mem_writes_succeedP.
Proof.
  unfold seq_model_outcome_invariant_preserved, mem_writes_succeedP, sequential_model_outcome_logged, fHandler_logger.
  cdestruct |- *** as seqst H_inv call seqst_succ ret H_seqst_succ n wr wret eid H_eid.
  rewrite lookup_unfold in *.
  eapply mem_writes_succeed in H_inv.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  rewrite Hsame_itrs in *.
  cdestruct H_eid #CDestrMatch.
  2,3: cdestruct call, ret, H_eid; scongruence.
  - ospecialize (H_inv (MemWrite n wr &→ wret) _ _).
    1:{ set_unfold. eexists (eid, _); split; eauto. rewrite lookup_unfold.
        cdestruct |- *** #CDestrMatch #CDestrSplitGoal. }
    1: hauto l: on.
    1: scongruence.
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
    all: cdestruct Hev |- *** as eid Heid.
    all: eexists (eid,ev); cbn; split; eauto.
    all: rewrite lookup_unfold in Heid.
    all: rewrite lookup_unfold.
    all: cdestruct Heid |- *** #CDestrMatch #CDestrEqOpt.
    all: hfcrush.
  - destruct call; try done.
    ospecialize (H (MemWrite n wr &→ ret) _ _).
    2,3: hauto l: on.
    cdestruct |- ***.
    eexists (intra_trace_eid_succ 0 (trace_rev st.(itrs)), _).
    split; eauto; cbn.
    rewrite lookup_unfold.
    cdestruct |- *** #CDestrMatch.
Qed.

Lemma seq_model_pcdst_mem_map_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st,
      let pcdst := (seq_state_to_partial_cd_state seq_st) in
      let cd := (seq_state_to_cd seq_st) in
      let evs := Candidate.event_list cd in
      partial_cd_state_mem_map_invP seq_st
      (* ∧ partial_cd_state_reg_map_invP seq_st
      ∧ cd_monotone cd *)).
Proof.
  unfold seq_model_outcome_invariant_preserved.
  cdestruct as seq_st H_inv call seqst_succ H_seqst_succ.
  pose (Candidate.event_list (seq_state_to_cd seq_st)) as evs.
  opose proof (seq_model_mem_writes_succeed_inv _ _ _ _ _) as Hmem_w_succeed; eauto.
  unfold sequential_model_outcome_logged, fHandler_logger in *.
  cdestruct seqst_succ, H_seqst_succ as seqst_succ ret H_seqst_succ Hmem_w_succeed.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  erewrite partial_cd_state_mem_map_inv_seq_state_equal;
  last by eapply seq_state_trace_cons_equal.
  opose proof (partial_cd_state_mem_map_inv _ H_inv) as H_base.
  unfold partial_cd_state_mem_map_invP.
  eapply seq_state_to_partial_cd_state_destruct.
  all: cdestruct |- ***.
  + ospecialize (H_base eid pa0 _); first eauto.
    rewrite lookup_unfold.
    setoid_rewrite lookup_unfold.
    setoid_rewrite lookup_unfold in H_base.
    cdestruct H_base |- *** #CDestrMatch.
    * eexists; repeat split.
      2: eapply H7.
      1: done.
      cdestruct |- *** #CDestrMatch.
      1: eapply H8.
      1: cdestruct |- *** #CDestrMatch #CDestrSplitGoal; eauto.
      1: done.
      1: destruct call; cdestruct H12 #CDestrMatch; hauto l: on.
      1: destruct call; cdestruct H10 #CDestrMatch; hauto l: on.
    * eexists; repeat split; eauto.
      1: destruct call; hauto lq: on.
      cdestruct |- *** #CDestrMatch.
      1: eapply H8.
      1: cdestruct |- *** #CDestrMatch #CDestrSplitGoal.
      1: eapply H12.
      1: done.
      1: destruct call; cdestruct H11 |- ***; hauto l: on.
      1: destruct call; cdestruct H9 |- ***; hauto l: on.
    * hauto lq: on rew: off.
  + rewrite lookup_unfold.
    ospecialize (H_base _ _ _).
    1: by rewrite reg_read_upd_pcdst_pa_w_map_equal in *.
    setoid_rewrite lookup_unfold in H_base.
    setoid_rewrite lookup_unfold.
    cdestruct H_base |- *** #CDestrMatch.
    2,3: hauto l: on.
    eexists; repeat split.
    2: hauto lq: on.
    1: naive_solver.
    1: cdestruct |- *** #CDestrMatch; eapply H5; cdestruct |- *** #CDestrMatch.
    all: hauto l: on.
  + rewrite lookup_unfold.
    ospecialize (H_base _ _ _); first eassumption.
    setoid_rewrite lookup_unfold in H_base.
    setoid_rewrite lookup_unfold.
    cdestruct H_base |- *** #CDestrMatch.
    2,3: hauto l: on.
    eexists; repeat split.
    2: hauto lq: on.
    1: naive_solver.
    1: cdestruct |- *** #CDestrMatch; eapply H5; cdestruct |- *** #CDestrMatch.
    all: hauto l: on.
  + rewrite lookup_unfold.
    ospecialize (H_base _ _ _).
    1: by rewrite mem_read_upd_pcdst_pa_w_map_equal in *.
    setoid_rewrite lookup_unfold in H_base.
    setoid_rewrite lookup_unfold.
    cdestruct H_base |- *** #CDestrMatch.
    2,3: hauto l: on.
    eexists; repeat split.
    2: hauto lq: on.
    1: naive_solver.
    1: cdestruct |- *** #CDestrMatch; eapply H5; cdestruct |- *** #CDestrMatch.
    all: hauto l: on.
  + rewrite mem_write_upd_pcdst_pa_w_map_rewrite in *.
    unfold setv, set, Setter_finmap in H0.
    rewrite lookup_unfold in H0.
    cdestruct H0 #CDestrMatch.
    * unfold iEvent.
      exists (call &→ ret).
      eapply mem_writes_succeedP_cons in Hmem_w_succeed.
      subst.
      cdestruct Hmem_w_succeed |- *** #CDestrSplitGoal #CDestrMatch.
      1: rewrite lookup_unfold.
      1: cdestruct |- *** #CDestrMatch.
      all: rewrite lookup_total_unfold in *.
      all: try done.
      1: by rewrite lookup_unfold in H3.
      rewrite lookup_unfold in *.
      cdestruct H1 #CDestrMatch.
      1: admit. (* Lemmas about EID.lt *)
      1,2: naive_solver.
    * ospecialize (H_base _ _ _); eauto.
      rewrite lookup_unfold.
      rewrite lookup_unfold in H_base.
      unfold mem_write_upd_partial_cd_state, setv, set, Setter_compose, Setter_finmap.
      setoid_rewrite lookup_unfold.
      cdestruct H_base |- *** #CDestrMatch.
      2: subst; by rewrite lookup_unfold in *.
      2: hauto lq: on rew: off.
      eexists; cdestruct |- *** #CDestrSplitGoal; eauto; first naive_solver.
      cdestruct H8 #CDestrMatch #CDestrSplitGoal.
      1:{
        eapply H6.
        1: rewrite lookup_unfold.
        all: by cdestruct |- *** #CDestrMatch #CDestrSplitGoal; eauto. }
      1: {
        destruct wr, x3, x1; cbn in *.
        subst.
        cdestruct H11.
        by inversion H. }
      1,2: subst.
      1,2: by rewrite ?intra_trace_eid_succ_tid, ?intra_trace_eid_succ_byte in *.
Admitted.

Lemma seq_model_pcdst_reg_map_inv :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st,
      let pcdst := (seq_state_to_partial_cd_state seq_st) in
      let cd := (seq_state_to_cd seq_st) in
      let evs := Candidate.event_list cd in
      partial_cd_state_reg_map_invP seq_st).
Proof.
Admitted.

Lemma seq_model_pcdst_montonone :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st,
      let pcdst := (seq_state_to_partial_cd_state seq_st) in
      let cd := (seq_state_to_cd seq_st) in
      let evs := Candidate.event_list cd in
      cd_monotone cd).
Proof.
  unfold seq_model_outcome_invariant_preserved.
  cdestruct |- *** as seqst H_inv call seqst_succ ret H_seqst_succ.
  unfold sequential_model_outcome_logged, fHandler_logger in *.
  cdestruct seqst_succ, H_seqst_succ as seqst_succ H_seqst_succ.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
  eapply seq_state_to_partial_cd_state_destruct.
Admitted.

Lemma seq_model_pcdst_consistent :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st,
      let pcdst := (seq_state_to_partial_cd_state seq_st) in
      let cd := (seq_state_to_cd seq_st) in
      let evs := Candidate.event_list cd in
      consistent regs_whitelist cd).
Proof.
  unfold seq_model_outcome_invariant_preserved.
  cdestruct |- *** as seqst H_inv call seqst_succ ret H_seqst_succ.
  opose proof (seq_model_pcdst_montonone _ H_inv call seqst_succ _);
  first (cdestruct |- ***; eauto).
  cbn in *.
  unfold sequential_model_outcome_logged, fHandler_logger in *.
  cdestruct seqst_succ, H_seqst_succ as seqst_succ H_seqst_succ H_mono.
  opose proof (sequential_model_outcome_same_itrs _ _ _ _ _ H_seqst_succ) as Hsame_itrs.
    opose proof (sequential_model_outcome_same_initSt _ _ _ _ _ H_seqst_succ) as Hsame_init.
  constructor.
  - eapply rel_montone_acyclic.
    repeat rewrite <- rel_montone_union.
    unfold cd_monotone in *.
    cdestruct H_mono |- *** #CDestrSplitGoal.
    1: admit. (* full instruction order monotone *)
    1: admit. (* from reads montone *)
    1,2: unfold partial_cd_state_to_cd, GenAxiomaticArm.AxArmNames.co, GenAxiomaticArm.AxArmNames.rf; cbn.
    1: eapply rel_montone_intersection1.
    1: eapply rel_strictly_monotone_seq1; split.
    1: eapply rel_strictly_monotone_seq2; split.
    2: assumption.
    1,2: eapply grel_from_set_montone.
    1: eapply  rel_strictly_monotone_seq1; split.
    1: assumption.
    1: eapply grel_from_set_montone.
    1: admit. (* reg from reads *)
  - unfold GenAxiomaticArm.AxArmNames.coe, GenAxiomaticArm.AxArmNames.coi, GenAxiomaticArm.AxArmNames.co.
    admit.
  - admit. (* TODO *)
  - unfold Illegal_RW.
    admit. (* TODO *)
  - unfold Illegal_RR.
    admit. (* TODO *)
  - unfold Candidate.mem_explicit.
    admit. (* TODO *)
  - unfold Candidate.is_nms.
    admit. (* TODO *)
  - opose proof (no_exceptions regs_whitelist _ (cd_from_seq_state_consistent _ H_inv)).
    unfold GenAxiomaticArm.AxArmNames.TE, GenAxiomaticArm.AxArmNames.ERET in *.
    set_unfold.
    cdestruct |- *** as eid.
    rewrite Hsame_itrs, lookup_unfold, Hsame_init.
    specialize (H eid).
    cdestruct H |- *** #CDestrMatch #CDestrSplitGoal.
    all: cdestruct |- *** as exi.
    all: cdestruct exi.
    all: destruct call; try done.
    1: set_unfold.
    1: set_unfold in H_seqst_succ.
    1: done.
    unfold mret, Exec.mret_inst, mret, Exec.res_mret_inst in H_seqst_succ.
    cbn in *.
    cdestruct H_seqst_succ.
    admit. (* TODO: Should not be supported I guess *)
Admitted.

Lemma seq_model_pcdst_wf :
  seq_model_outcome_invariant_preserved seq_inv_predicate
    (λ seq_st,
      let pcdst := (seq_state_to_partial_cd_state seq_st) in
      let cd := (seq_state_to_cd seq_st) in
      let evs := Candidate.event_list cd in
      Candidate.wf cd).
    all: cbn in *.
Admitted.

    all: rewrite Exec.unfold_has_error in H_seqst_succ.

    cdestruct |- *** #CDestrMatch.
    1: unfold Candidate.reg_from_reads.
    all: try done.
    all: cdestruct H_mono.
    eapply seq_state_to_partial_cd_state_destruct.
    + cdestruct |- ***.
    rel_montone_acyclic


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
  + unfold partial_cd_state_mem_map_invP in *.
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
    1: unfold partial_cd_state_mem_map_invP in *.
    1: eapply H_pcdst_mem_map_wf.
    all: unfold partial_cd_state_mem_map_invP, update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
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

Lemma seq_model_consistent :
  seq_model_outcome_invariant_preserved seq_inv_predicate.
Proof.
  cdestruct |- *** as seq_st [] call seq_st_succ H_succ_st.
  constructor.
  - now eapply (seq_model_monotone seq_st _ call).
  - now eapply (seq_model_monotone seq_st _ call).
  - now eapply (seq_model_monotone seq_st _ call).
  - now eapply (seq_model_monotone seq_st _ call).
  - assert (partial_cd_state_mem_map_invP seq_st_succ) as Hmem_map_wf
    by now eapply (seq_model_monotone seq_st _ call).
    assert (mem_writes_succeedP seq_st_succ) as Hmem_w_succeed
    by now eapply (seq_model_monotone seq_st _ call).
    unfold partial_cd_state_mem_map_invP, mem_writes_succeedP in Hmem_map_wf, Hmem_w_succeed.
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
      apply rel_montone_acyclic.
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
