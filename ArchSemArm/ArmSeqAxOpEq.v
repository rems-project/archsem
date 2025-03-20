Require Import ArmSeqModel UMSeqArm.
Require Import ArmInst.
From ASCommon Require Import Exec FMon Common Options.

Import CDestrUnfoldElemOf.

Lemma finterp_inv_induct `{Effect Eff} {St E A}
    (handler : fHandler Eff (Exec.t St E)) (mon : fMon Eff A)
    (P : result St St → Prop) (st : St)
  : P (Ok st)
  → (∀ st call, P (Ok st) → ∀ st' ∈ Exec.to_state_result_list $ handler call st, P st')
  → ∀ st' ∈ (Exec.to_state_result_list $ FMon.finterp handler mon st), P st'.
Proof.
  induction mon as [|? ? IH] in st |- *; cdestruct |- *** as Hbase Hstep st' Hst'.
  unfold Exec.to_state_result_list in *.
  set_unfold.
  cdestruct Hst' |- *** #CDestrSplitGoal; subst.
  - eapply IH.
    2: cdestruct |- *** #CDestrSplitGoal; eapply Hstep; eauto;
       solve[ltac:(left + right); eexists (_,_); eauto].
    2: left; eexists (_,_); eauto.
    eapply Hstep.
    2: left; eexists (_,_); cbn; split; eauto.
    done.
  - eapply Hstep.
    2: right; eexists (_,_); cbn; split; eauto.
    easy.
  - eapply IH.
    2: cdestruct |- *** #CDestrSplitGoal; eapply Hstep; eauto;
       solve[ltac:(left + right); eexists (_,_); eauto].
    2: right; eexists (_,_); eauto.
    eapply Hstep.
    2: left; eexists (_,_); cbn; split; eauto.
    done.
Qed.

Lemma cinterp_inv_induct `{Effect Eff} {St E A}
    (handler : fHandler Eff (Exec.t St E)) (mon : cMon Eff A)
    (P : result St St → Prop) (st : St)
  : P (Ok st)
  → (∀ st call, P (Ok st) → ∀ st' ∈ Exec.to_state_result_list $ (handler +ₕ mcall_fHandler) call st, P st')
  → ∀ st' ∈ (Exec.to_state_result_list $ FMon.cinterp handler mon st), P st'.
Proof. cdestruct |- ***. eapply finterp_inv_induct; done. Qed.

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
Arguments trace_find : simpl never.

Lemma trace_find_cons (P : FMon.fEvent outcome → Prop) `{∀ x, Decision (P x)}
    (itrs : list (iTrace ())) (x : FMon.fEvent outcome)
  : trace_find P (set fst (cons x) (hd FTNothing itrs) :: tail itrs) =
    if decide (P x)
    then Some x
    else trace_find P itrs.
Proof.
  destruct itrs; unfold trace_find at 1; cbn;
  case_bool_decide; case_decide; cdestruct |- ***; try easy.
  now destruct i.
Qed.

Print Coercions.
Context (regs_whitelist : option (gset reg)) (fuel : nat) (isem : iMon ()).

Notation seqmon := (Exec.t seq_state string).
Notation initss := {| initSt := initSt; regs := ∅; mem := ∅; itrs := [] |}.

Definition seqmon_pe (st : seq_state) : Candidate.pre Candidate.NMS 1 :=
  Candidate.make_pre _ st.(initSt) [# st.(itrs)].

Definition op_mem_wf (str : result seq_state seq_state) : Prop :=
  match str with
  | Ok st =>
    ∀ pa v,
      st.(mem) !! pa = Some v
    ↔ ∃ ev,
        trace_find
          (is_mem_writeP (λ size wr, pa_in_range wr.(WriteReq.pa) (Z.to_N (Z.min (Z.of_N size) (bv_modulus 52))) pa))
          st.(itrs)
        = Some ev
    ∧ ∃ offset, (0 ≤ Z.of_N offset < bv_modulus 52)%Z ∧
        ev |> is_mem_writeP
          (λ size wr,
            pa_addN wr.(WriteReq.pa) offset = pa
            ∧ (offset < size)%N
            ∧ bv_get_byte 8 offset wr.(WriteReq.value) = v)
  | Error _ => False
  end.

#[local] Existing Instance Exec.unfold.

Definition result_same_type_proj {T} (r : result T T) :=
  match r with
  | Ok t => t
  | Error t => t
  end.

Lemma length_bv_to_bytes n m (v : bv n) :
  length (bv_to_bytes m v) = N.to_nat (div_round_up n m).
Proof.
  unfold bv_to_bytes.
  rewrite bv_to_little_endian_length.
  2: lia.
  rewrite <- Z_N_nat.
  now rewrite N2Z.id.
Qed.

Lemma div_round_up_divisible n m :
  (n ≠ 0)%N → (div_round_up (n * m) n) = m.
Proof.
  intro.
  unfold div_round_up.
  rewrite N.mul_comm.
  rewrite N.div_add_l; last done.
  rewrite N.div_small; lia.
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


Lemma write_mem_seq_state_itrs bytes  :
  ∀ st st' pa, (st', ()) ∈ write_mem_seq_state pa bytes st → itrs st' = itrs st.
Proof.
  induction bytes; cdestruct |- ***.
  change (itrs st) with (itrs (set (lookup pa0 ∘ mem) (λ _ : option (bv 8), Some a) st)).
  eapply IHbytes, H.
Qed.

Lemma op_reads st :
  op_mem_wf (Ok st) →
  ∀ str ∈ (Exec.to_state_result_list $ FMon.cinterp (sequential_model_outcome_logged regs_whitelist) isem st),
  (λ str, is_Ok str → op_mem_wf str) str.
Proof.
  intro.
  eapply cinterp_inv_induct; first easy; clear.
  cdestruct |- *** as st call H_st st' H_st' pa.
  unfold Exec.to_state_result_list in *.
  cdestruct H_st' as r H_st' v #CDestrSplitGoal.
  destruct call as [|[]]; cbn in *.
  2:{
    cbn in *.
    assert (st' = st) as ->
    by (unfold Exec.Results in *; set_unfold; now cdestruct H_st').
    eapply H_st;
    cdestruct |- ***.
  }
  destruct (decide (is_mem_write (o &→ r))).
  2: {
    destruct o.
    all: do 8 deintro.
    all: cdestruct |- *** #CDestrMatch.
    all: rewrite trace_find_cons.
    all: cdestruct |- *** #CDestrMatch.
    all: try easy.
    all: eapply H_st.
    all: cdestruct |- ***.
  }
  destruct o; try easy.
  do 9 deintro.
  cdestruct |- *** #CDestrMatch.
  rewrite trace_find_cons.
  inversion H0.
  do 11 deintro;
  cdestruct |- *** as ?? st' pa H_st' ?? #CDestrMatch.
  2: {
    assert (mem st' !! pa = mem st !! pa) as ->.
    {
      eapply pa_not_in_range_write; eauto.
      rewrite length_bv_to_bytes.
      f_equal.
      admit.
    }
    erewrite write_mem_seq_state_itrs; last eauto.
    eapply H_st.
    cdestruct |- ***.
    }
  apply pa_in_range_spec in p.
  cdestruct p as offset H_pa H_offset.
  enough (mem st' !! pa = Some (bv_get_byte 8 offset (WriteReq.value wr))) as ->.
  {
    cdestruct |- *** #CDestrSplitGoal.
    - eexists; cdestruct |- *** #CDestrSplitGoal; eauto.
      eexists offset.
      cdestruct |- *** #CDestrSplitGoal; lia.
    - inversion H1; subst.
      deintro; cdestruct |- ***.
      f_equal; last naive_solver.
      subst.
      destruct x1, pa0; cbn in *.
      unfold pa_addN, pa_addZ in H2; cbv in H2.
      cdestruct H2.
      eapply bv_add_Z_inj_l in H2.
      1: deintro.
      all: cdestruct |- *** #CDestrMatch; lia.
  }
  assert (offset < n)%N by lia.
  eapply pa_offset_in_range_write; eauto.
Admitted.
