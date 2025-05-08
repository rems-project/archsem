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

#[export] Instance lookup_unfold_intra_trace_eid_succ_None {et} (init : MState.t 1) evs :
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

Lemma option_mbind_is_Some {A B} (o : option A) (f : A → option B) :
  is_Some (x ←@{option} o; f x) ↔ ∃ i, o = Some i ∧ is_Some (f i).
Proof.
  destruct o eqn: Ho; cdestruct o, f, Ho |- *** #CDestrSplitGoal.
  all: by eexists.
Qed.

#[local] Instance cdestruct_bind_is_Some_goal {A B} b o (f : A → option B) :
  CDestrSimpl b (is_Some (x ←@{option} o; f x)) (∃ i, o = Some i ∧ is_Some (f i)).
Proof. tcclean. eapply option_mbind_is_Some. Qed.

#[local] Instance cdestruct_guard'_True b x `(Decision P) :
  CDestrSimpl b (guard' P = Some x) P.
Proof.
  tcclean.
  unfold guard', guard.
  cdestruct |- *** #CDestrMatch #CDestrSplitGoal; try done.
  now destruct x.
Qed.

#[local] Instance cdestruct_elem_of_mthrow {St E A} (x : St * A) (err : E) st :
  CDestrSimpl false (x ∈ (mthrow err : Exec.t St E A) st) False.
Proof.
  tcclean.
  unfold mthrow, Exec.throw_inst, mthrow, Exec.res_throw_inst.
  set_solver.
Qed.

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

Lemma seq_state_to_pe_traces_cons seqst ev :
  seq_state_to_pe (set itrs (trace_cons ev) seqst) =
  set Candidate.events (traces_snoc ev 0%fin) (seq_state_to_pe seqst).
Proof.
  unfold seq_state_to_pe; cbv [set]; cbn.
  do 2 f_equal.
  unfold trace_snoc, unsnoc_total.
  destruct (itrs seqst); first done.
  now rewrite unsnoc_snoc.
Qed.

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

Definition seq_model_outcome_invariant_preserved (I : seq_state → Prop) : Prop :=
  ∀ (seq_st : seq_state),
  I seq_st →
  ∀ (call : outcome) seq_st_succ,
  Ok seq_st_succ ∈ Exec.to_state_result_list (sequential_model_outcome_logged (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call seq_st) →
  I seq_st_succ.

Lemma seq_state_step_to_partial_cd_state I seq_st seq_st_succ call ret :
  (seq_st_succ, ret) ∈ sequential_model_outcome (Some regs_whitelist) (Z.to_N (bv_modulus 52)) call seq_st →
  I (update_partial_cd_state_for_eid_ev (seq_state_to_partial_cd_state seq_st)
      (intra_trace_eid_succ 0 (Candidate.events (seq_state_to_pe seq_st) !!! 0%fin), call &→ ret)) →
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

Definition mem_writes_succeedP seq_st :=
  let cd := seq_state_to_cd seq_st in
  let evs := Candidate.event_list cd in
  ∀ ev ∈ evs.*2, is_mem_write_req ev →
  is_mem_write_reqP (λ _ _ ret, if ret is inl b then b = true else False) ev.

Definition partial_cd_state_eids_mem_map_in_traceP seq_st :=
  let pcdst := seq_state_to_partial_cd_state seq_st in
  let cd := seq_state_to_cd seq_st in
  ∀ eid pa, pcdst.(pa_write_map) !! pa = Some eid →
    ∃ ev, is_mem_writeP (λ _ wr, wr.(WriteReq.pa) = pa) ev ∧ cd !! eid = Some ev
      ∧ (∀ eid' ev', cd !! eid' = Some ev' →
         is_mem_writeP (λ _ wr, wr.(WriteReq.pa) = pa) ev' →
         EID.full_po_lt eid' eid).

Definition partial_cd_state_eids_reg_map_in_traceP seq_st :=
  let pcdst := seq_state_to_partial_cd_state seq_st in
  let cd := seq_state_to_cd seq_st in
  ∀ eid reg, pcdst.(reg_write_map) !! reg = Some eid → ∃ ev, is_reg_writeP (λ reg' _ _, reg' = reg) ev ∧ cd !! eid = Some ev ∧ (∀ eid' ev', cd !! eid' = Some ev' → is_reg_writeP (λ reg' _ _, reg' = reg) ev' → EID.full_po_lt eid' eid).

Record seq_inv_predicate (seq_st : seq_state) := {
  pcdst := seq_state_to_partial_cd_state seq_st;
  cd := seq_state_to_cd seq_st;
  evs := Candidate.event_list cd;
  mem_writes_succeed : mem_writes_succeedP seq_st;
  partial_cd_state_eids_mem_map_in_trace : partial_cd_state_eids_mem_map_in_traceP seq_st;
  partial_cd_state_eids_reg_map_in_trace : partial_cd_state_eids_reg_map_in_traceP seq_st;
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

Lemma seq_model_monotone :
  seq_model_outcome_invariant_preserved
    (λ seq_st,
      let pcdst := seq_state_to_partial_cd_state seq_st in
      let cd := seq_state_to_cd seq_st in
      let evs := Candidate.event_list cd in
      mem_writes_succeedP seq_st
      ∧ partial_cd_state_eids_mem_map_in_traceP seq_st
      ∧ partial_cd_state_eids_reg_map_in_traceP seq_st
      ∧ cd_monotone $ seq_state_to_cd seq_st).
Proof.
  unfold seq_model_outcome_invariant_preserved, sequential_model_outcome_logged, fHandler_logger.
  cdestruct |- *** as seq_st H_mem_w_succeed H_pcdst_mem_map_wf H_pcdst_reg_map_wf Hmono call seq_st_succ ret H_seq_st_succ.
  pose (Candidate.event_list (seq_state_to_cd seq_st)) as evs.
  do 3 try split.
  - admit.
  - unfold partial_cd_state_eids_mem_map_in_traceP.
    (* erewrite seq_state_step_to_pe_eq, seq_state_to_pe_trace_cons; last eauto. *)
    eapply seq_state_step_to_partial_cd_state; first eauto.
    cdestruct |- ***.
    destruct (decide (is_mem_write (call &→ ret)));
    destruct call; try done.
    all: set_unfold in H_pcdst_mem_map_wf;
    cdestruct H_pcdst_mem_map_wf;
    unfold update_partial_cd_state_for_eid_ev, reg_write_upd_partial_cd_state, reg_read_upd_partial_cd_state,
    mem_write_upd_partial_cd_state, mem_read_upd_partial_cd_state in *.
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
  - assert (partial_cd_state_eids_mem_map_in_traceP seq_st_succ) as Hmem_map_wf
    by now eapply (seq_model_monotone seq_st _ call).
    assert (mem_writes_succeedP seq_st_succ) as Hmem_w_succeed
    by now eapply (seq_model_monotone seq_st _ call).
    unfold partial_cd_state_eids_mem_map_in_traceP, mem_writes_succeedP in Hmem_map_wf, Hmem_w_succeed.
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
(*       5: {
        ospecialize (Hmem_map_wf t (ReadReq.pa rr) _).
        1: cdestruct |- *** #CDestrMatch.
        cdestruct Hmem_map_wf #CDestrMatch.
        rewrite ?cd_to_pe_lookup in *; setoid_rewrite cd_to_pe_lookup in H11;
        cbn in *.
        unfold lookup in *.
       } *)
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
      all: cdestruct |- *** #CDestrMatch.
      5,6,7,8,9: admit. (* Abort write *)
      all: eexists; split; eauto.
      all: cdestruct |- *** #CDestrMatch.
      4: admit (* TODO *).
      all: eexists; split; eauto.
      all: cdestruct |- *** #CDestrMatch.
      all: eexists; split; eauto.
      all: cdestruct |- *** #CDestrMatch.

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
