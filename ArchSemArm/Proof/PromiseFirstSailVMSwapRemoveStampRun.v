(******************************************************************************)
(* Unconditional exclusion of a removed timestamp                            *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstSailVMViews PromiseFirstSailVMSwapRemoveTimes
  PromiseFirstSailVMSwapRemoveThread PromiseFirstSailVMSwapRemoveMemory.
From ArchSemArm.Proof Require Import PromiseFirstSailVMSwapRemoveStamps
  PromiseFirstSailVMSwapRemoveViews PromiseFirstVMExecutionCurrent.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapRemoveStampMemory.
Import VMPromising VMSwapRemoveStamps.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

Definition ok p (pp : PPState.t TState.t Ev.t IIS.t) := ts_ok p (PPState.state pp) ∧ iis_ok p (PPState.iis pp).

Lemma mapped_times p {A C} (f : A * (bv 8 * nat) → C * nat * nat) addrs candidate :
  (∀ x, x.2.2 ≠ p → (f x).2 ≠ p) → Forall (λ byte, byte.2 ≠ p) candidate →
  Forall (λ t, t ≠ p) (map f (zip addrs candidate)).*2.
Proof.
  intros Hf Hcand. apply (VMViews.zip_Forall_snd _ addrs) in Hcand.
  induction Hcand as [|x l Hx Hl IH]; cbn; constructor; [apply Hf, Hx|exact IH].
Qed.

#[local] Hint Rewrite VMViews.strict_set_rmw_read VMViews.strict_set_trs
  VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_iis_field VMViews.mem_set_iis_field VMViews.iis_set_iis_field : pp_stamps.
Ltac simpl_pp := unfold ok, setv in *; autorewrite with pp_stamps in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.
Ltac solve_fields :=
  first [assumption
    | apply update_vrd; solve_fields | apply update_vacq; solve_fields | apply update_vspec; solve_fields
    | apply update_cohs; [lia|assumption|solve_fields]
    | apply set_xclb; [assumption|solve_fields]
    | apply iis_add; solve_fields
    | apply iis_rmw; [intros ? ? H; injection H as <- <-; assumption|solve_fields]].

Lemma read_mem_explicit_ok imem l r tlbi rc epoch addr size macc pp pp' value :
  PPState.mem pp = l ++ Ev.Tlbi tlbi rc epoch :: r → ok (S (length r)) pp →
  Exec.elem_of_results (pp', value) (read_mem_explicit imem addr size macc pp) → ok (S (length r)) pp'.
Proof.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold read_mem_explicit in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: destruct Hok as [Hts Hiis]; VMViews.facts Hts; VMViews.facts Hiis.
  all: match goal with H : Memory.read_all _ _ _ _ _ = Ok _, Hin : ?candidate ∈ _ |- _ =>
    pose proof (VMSwapRemoveTimes.read_all_avoids _ _ _ _ _ _ _ _ _ _ H _ Hin) as Hcand end.
  all: pose proof (VMSwapRemoveTimes.max_list_avoids (S (length r)) snd _ ltac:(lia) Hcand) as Htread.
  all: match goal with |- context[map ?f (zip ?addrs ?candidate)] =>
    assert (Htimes : Forall (λ time, time ≠ S (length r)) (map f (zip addrs candidate)).*2) by
      (apply mapped_times; [|exact Hcand]; intros [a [byte twrite]] Hbyte; cbn in Hbyte |- *;
       match goal with |- context[default _ ?o] => destruct o eqn:Hfwd end; cbn;
       [eapply read_fwd_time; [exact ok_fwdb0|exact Hfwd]|exact Hbyte]) end.
  all: apply (VMViews.zip_Forall_snd _ (addr_range addr size)) in Htimes.
  all: split; solve_fields.
Qed.

Lemma read_mem_explicit_both imem l r tlbi rc epoch addr size macc pp pp' value :
  PPState.mem pp = l ++ Ev.Tlbi tlbi rc epoch :: r →
  VMSwapRemoveThread.ok (S (length r)) pp → ok (S (length r)) pp →
  Exec.elem_of_results (pp', value) (read_mem_explicit imem addr size macc pp) →
  VMSwapRemoveThread.ok (S (length r)) pp' ∧ ok (S (length r)) pp'.
Proof.
  intros Hmem Hviews Hstamps Hrun. split.
  - eapply VMSwapRemoveMemory.read_mem_explicit_ok; eassumption.
  - eapply read_mem_explicit_ok; eassumption.
Qed.
End VMSwapRemoveStampMemory.

Module VMSwapRemoveStampEvents.
Import VMPromising VMSwapRemoveStamps VMSwapRemoveStampMemory.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState
  Promising.iis Memory.t view UMPromising.view.

#[local] Hint Rewrite VMViews.strict_set_rmw_read VMViews.strict_set_trs
  VMViews.state_set_state VMViews.mem_set_state VMViews.iis_set_state
  VMViews.state_set_iis VMViews.mem_set_iis VMViews.iis_set_iis
  VMViews.state_set_state_field VMViews.mem_set_state_field VMViews.iis_set_state_field
  VMViews.state_set_iis_field VMViews.mem_set_iis_field VMViews.iis_set_iis_field
  VMViews.state_set_mem VMViews.mem_set_mem VMViews.iis_set_mem : pp_stamp_write.
Ltac simpl_pp := unfold ok, setv in *; autorewrite with pp_stamp_write in *;
  cbn [PPState.state PPState.mem PPState.iis fst snd] in *.

Ltac solve_time := first [assumption|cbn [length]; rewrite ?length_app; cbn; lia].
Ltac solve_times := first [assumption|apply list.Forall_fmap; apply list.Forall_forall; intros ? ?; cbn; solve_time].
Ltac solve_fields :=
  first [assumption
    | apply update_vwr; solve_fields | apply update_vrel; solve_fields | apply update_vacq; solve_fields
    | apply update_vtlbi_self; solve_fields | apply update_vtlbi_other; solve_fields
    | apply update_cohs; [lia|solve_times|solve_fields]
    | apply filter_prom_wr; solve_fields
    | apply filter_prom_tlbi; solve_fields
    | apply set_fwdbs; [solve_time|solve_fields]
    | apply clear_xclb; solve_fields
    | apply iis_add; solve_fields
    | apply iis_rmw; [intros; discriminate|solve_fields]
    | match goal with
      | |- ts_ok ?p (TState.make _ _ (TState.regs ?X) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
        let HX := fresh in assert (HX : ts_ok p X) by solve_fields;
        destruct HX; constructor; cbn; try assumption;
        apply VMSwapRemoveViews.Forall_filter; assumption
      end].

Lemma write_mem_ok tid imem l r tlbi rc epoch addr size macc data pp pp' value :
  PPState.mem pp = l ++ Ev.Tlbi tlbi rc epoch :: r → ok (S (length r)) pp →
  Exec.elem_of_results (pp', value) (write_mem tid imem addr size macc data pp) → ok (S (length r)) pp'.
Proof.
  destruct pp as [ts mem iis]. cbn. intros -> Hok Hrun. unfold write_mem in Hrun.
  VMViews.invert; subst; simpl_pp.
  all: destruct Hok as [Hts Hiis].
  all: try match goal with H : Memory.fulfill _ _ _ = Some ?time |- _ =>
    assert (Htime : time ≠ S (length r)) by
      (eapply VMSwapRemoveTimes.fulfill_avoids; [exact (ok_prom_wr _ _ Hts)|exact H]) end.
  all: try match goal with H : TState.process_event _ _ _ _ _ = Ok ?after |- _ =>
    assert (Hafter : ts_ok (S (length r)) after) by (eapply process_event; [exact Hts|exact H]) end.
  all: split; solve_fields.
Qed.

Lemma materialize_ok p tid imem pre tlbi recipient pp pp' time created :
  p ≤ length (PPState.mem pp) → ok p pp →
  Exec.elem_of_results (pp', (time, created))
    (materialize_tlbi_for_recipient tid imem pre tlbi recipient pp) →
  ok p pp' ∧ time ≠ p ∧ p ≤ length (PPState.mem pp').
Proof.
  destruct pp as [ts mem iis]. cbn. intros Hbound [Hts Hiis] Hrun.
  unfold materialize_tlbi_for_recipient in Hrun. VMViews.invert; subst; simpl_pp.
  all: try match goal with H : Memory.fulfill _ _ _ = Some ?time |- _ =>
    assert (Htime : time ≠ p) by
      (eapply VMSwapRemoveTimes.fulfill_avoids; [exact (ok_prom_tlbi _ _ Hts)|exact H]) end.
  all: try match goal with H : TState.process_event _ _ _ _ _ = Ok ?after |- _ =>
    assert (Hafter : ts_ok p after) by (eapply process_event; [exact Hts|exact H]) end.
  all: split; [split; solve_fields|split; solve_time].
Qed.

Lemma recipients_ok p tid imem pre tlbi recipients vself0 vother0 created0
    pp pp' vself vother created :
  p ≤ length (PPState.mem pp) → ok p pp → vself0 ≠ p → vother0 ≠ p →
  Exec.elem_of_results (pp', ((vself, vother), created))
    (foldlM (VMMemoryGrowth.tlbi_recipient_step tid imem pre tlbi)
      ((vself0, vother0), created0) recipients pp) →
  ok p pp' ∧ vself ≠ p ∧ vother ≠ p ∧ p ≤ length (PPState.mem pp').
Proof.
  revert vself0 vother0 created0 pp.
  induction recipients as [|recipient recipients IH]; intros vself0 vother0 created0 pp Hb Hok Hself Hother Hrun.
  - cbn in Hrun. apply Exec.elem_of_mret_inv in Hrun as [-> Heq].
    injection Heq as -> -> ->. auto.
  - cbn [foldlM] in Hrun.
    apply Exec.elem_of_bind_elim in Hrun as [mid [[[vself1 vother1] created1] [Hstep Htail]]].
    unfold VMMemoryGrowth.tlbi_recipient_step in Hstep.
    apply Exec.elem_of_bind_elim in Hstep as [mat [[time is_new] [Hmat Hret]]].
    apply Exec.elem_of_mret_inv in Hret as [-> Heq]. injection Heq as Hv1 Hv2 Hc1.
    apply (materialize_ok p) in Hmat as (Hmid & Htime & Hbound); [|exact Hb|exact Hok].
    eapply IH; [exact Hbound|exact Hmid| | |exact Htail]; subst; repeat case_decide; lia.
Qed.

Lemma run_tlbi_ok p n tid imem viio tlbi pp pp' value : 0 < p → p ≤ length (PPState.mem pp) → ok p pp →
  Exec.elem_of_results (pp', value) (run_tlbi n tid imem viio tlbi pp) → ok p pp'.
Proof.
  destruct pp as [ts mem iis]. intros Hp Hb Hok Hrun. unfold run_tlbi in Hrun. VMViews.invert; subst.
  all: match goal with H : Exec.elem_of_results _ (foldlM _ _ _ _) |- _ =>
    apply (recipients_ok p) in H as (Hmid & Hself & Hother & Hbound); [|exact Hb|exact Hok|lia|lia] end.
  all: destruct Hmid as [Hts Hiis]; simpl_pp; unfold compose; split; solve_fields.
Qed.
End VMSwapRemoveStampEvents.
