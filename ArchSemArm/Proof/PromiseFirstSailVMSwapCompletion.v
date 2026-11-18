(******************************************************************************)
(* Adjacent TLBI exchange along continuations with a validated final result    *)
(******************************************************************************)
From ASCommon Require Import Options Common Exec FMon StateT HVec.
From ArchSemArm Require Import ArmInst VMPromising.
From ArchSemArm.Proof Require Import PromiseFirstCurrent PromiseFirstVMExecutionCurrent
  PromiseFirstSailCurrent PromiseFirstSailVMNormalization.
#[local] Open Scope stdpp.
#[local] Open Scope nat_scope.
#[local] Open Scope list_scope.

Module VMSwapCompletion.
Import VMPromising VMNormalization.
#[local] Typeclasses Transparent VMPromising Promising.mEvent Promising.tState Promising.iis Memory.t.

Section Simulation.
Context (bbm nondet : bool) {n : nat} (term : terminationCondition n)
  (initMs : archState n) (code : code_region).
Local Notation prom := (VMPromising bbm).
Local Notation state := (PState.t TState.t Ev.t n).
Local Notation Mixed := (Mixed bbm nondet term).
Local Notation RawStep := (RawStep bbm nondet term).
Local Notation RawTrace := (RawTrace bbm nondet term).
Local Notation FinalResult := (FinalResult bbm term).

Definition completes (st : state) := ∃ final fs, rtc Mixed st final ∧ FinalResult final fs.

Lemma step_completes st next : Mixed st next → completes next → completes st.
Proof.
  intros Hstep [final [fs [Hrest Hfinal]]]. exists final, fs. split; [|exact Hfinal].
  eapply rtc_l; eassumption.
Qed.
Lemma raw_trace_completes st evs next : RawTrace st evs next → completes next → completes st.
Proof.
  intro Htrace. induction Htrace as [|evs mid fin ev _ IH Hstep]; intro Hfin; [exact Hfin|].
  apply IH. eapply step_completes; [right; exists ev; exact Hstep|exact Hfin].
Qed.

(** A successful final result is the observable used by [VMTLBISwapReplay].
    Local replay is therefore needed only when the source continuation can
    still produce such a result. In particular, a DSB that strands an older
    TLBI promise does not impose a handler-simulation obligation. *)
Definition simulation : Prop :=
  ∃ R : state → state → Prop,
    (∀ init evs s a b e1 e2,
      VMSailNoSelfModifying bbm nondet term initMs code →
      PState.from_archState prom initMs = Ok init →
      RawTrace init evs s → RawStep e1 s a → RawStep e2 a b →
      Ev.out_of_order e1 e2 = true → completes b →
      ∃ a' b', RawStep e2 s a' ∧ RawStep e1 a' b' ∧ R b b') ∧
    (∀ x x' ev y, R x x' → RawStep ev x y → completes y →
      ∃ y', RawStep ev x' y' ∧ R y y') ∧
    (∀ x x' y, R x x' → Mixed x y → completes y →
      ∃ y', Mixed x' y' ∧ R y y') ∧
    (∀ x x', R x x' → length (PState.events x') = length (PState.events x)) ∧
    (∀ x x' fs, R x x' → FinalResult x fs → FinalResult x' fs).

Theorem replay : simulation → VMTLBISwapReplay bbm nondet term initMs code.
Proof.
  intros (R & Hstart & Hraw & Hmixed & Hlen & Hres)
    init l1 l2 e1 e2 b final fs Hsafe Hinit Htr Hord Hrest Hfin.
  assert (Hcompleteb : completes b) by (exists final, fs; auto).
  destruct (raw_trace_split bbm nondet term _ l1 _ _ Htr) as [c [Hc Hl1]].
  apply (raw_trace_cons_inv bbm nondet term) in Hc as [a [Ha Hac]].
  apply (raw_trace_cons_inv bbm nondet term) in Ha as [s [Hs Hsa]].
  destruct (Hstart init l2 s a c e1 e2 Hsafe Hinit Hs Hsa Hac Hord
    (raw_trace_completes _ _ _ Hl1 Hcompleteb)) as [a' [c' [Hsa' [Hac' HR]]]].
  assert (Hl1' : ∃ b', RawTrace c' l1 b' ∧ R b b').
  { clear -Hraw Hl1 HR Hcompleteb. revert Hcompleteb.
    induction Hl1 as [|evs mid y ev _ IH Hstep]; intro Hcy.
    - exists c'. split; [constructor|exact HR].
    - assert (Hcm : completes mid) by (eapply step_completes; [right; exists ev; exact Hstep|exact Hcy]).
      destruct (IH Hcm) as [m' [Hm' HRm]].
      destruct (Hraw mid m' ev y HRm Hstep Hcy) as [y' [Hy' HRy]].
      exists y'. split; [econstructor; eassumption|exact HRy]. }
  destruct Hl1' as [b' [Hb' HRb]].
  assert (Hcont : ∃ final', rtc Mixed b' final' ∧ R final final').
  { clear -Hmixed Hrest HRb Hfin. revert b' HRb.
    induction Hrest as [x|x y z Hxy Hyz IH]; intros x' HR.
    - exists x'. split; [apply rtc_refl|exact HR].
    - assert (Hcy : completes y) by (exists z, fs; auto).
      destruct (Hmixed x x' y HR Hxy Hcy) as [y' [Hy' HRy]].
      destruct (IH Hfin y' HRy) as [z' [Hz' HRz]].
      exists z'. split; [eapply rtc_l; eassumption|exact HRz]. }
  destruct Hcont as [final' [Hfinal' HRf]].
  exists b', final'. split.
  - eapply raw_trace_app; [|exact Hb'].
    econstructor; [econstructor; eassumption|exact Hac'].
  - split; [exact Hfinal'|]. split; [eapply Hres; eassumption|]. apply Hlen, HRf.
Qed.
End Simulation.
End VMSwapCompletion.
