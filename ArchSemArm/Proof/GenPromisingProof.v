(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

From ASCommon Require Import Options.
From ASCommon Require Import Common Exec FMon StateT.

From ArchSem Require Import GenPromising.
From ArchSemArm Require Import ArmInst.

#[local] Open Scope list.
#[local] Open Scope nat.
#[local] Open Scope stdpp.

Module PromMemoryFacts.
Section PM.

  Context {ev : Type}.

  Lemma attach_timestamps_time_le (event : ev) (mem : PromMemory.t ev) ts :
    (event, ts) ∈ PromMemory.attach_timestamps mem →
    (ts ≤ length mem)%nat.
  Proof.
    induction mem as [|event0 mem IH]; cbn.
    - set_solver.
    - intro Hin.
      apply elem_of_cons in Hin as [Heq|Hin].
      + inversion Heq.
        lia.
      + specialize (IH Hin).
        lia.
  Qed.

  Lemma cut_after_with_timestamps_time_le
      (event : ev) (mem : PromMemory.t ev) v ts :
    (event, ts) ∈ PromMemory.cut_after_with_timestamps v mem →
    (ts ≤ length mem)%nat.
  Proof.
    unfold PromMemory.cut_after_with_timestamps.
    intro Hin.
    apply elem_of_take in Hin as [i [Hlookup _]].
    eapply attach_timestamps_time_le.
    eapply elem_of_list_lookup_2.
    exact Hlookup.
  Qed.

  Lemma lookup_latest (event : ev) (mem : PromMemory.t ev) :
    ((event :: mem : PromMemory.t ev) !! length (event :: mem)) = Some event.
  Proof.
    unfold lookup, PromMemory.lookup_inst.
    cbn [length].
    destruct (S (length mem) =? 0)%nat eqn:Hzero.
    - apply Nat.eqb_eq in Hzero.
      lia.
    - clear Hzero.
      replace (S (length mem) <=? length (event :: mem))%nat with true
        by (symmetry; apply Nat.leb_le; cbn; lia).
      replace (length (event :: mem) - S (length mem))%nat with 0%nat
        by (cbn; lia).
      reflexivity.
  Qed.

  Lemma lookup_cons_inv_same (event : ev) (mem : PromMemory.t ev) ts :
    ((event :: mem : PromMemory.t ev) !! ts) = Some event →
    mem !! ts = Some event ∨ ts = length (event :: mem).
  Proof.
    destruct ts as [|ts].
    - unfold lookup, PromMemory.lookup_inst.
      cbn.
      discriminate.
    - unfold lookup, PromMemory.lookup_inst.
      cbn [length].
      replace (S ts =? 0)%nat with false by reflexivity.
      destruct (S ts <=? S (length mem))%nat eqn:Hnew.
      + apply Nat.leb_le in Hnew.
        destruct (S ts <=? length mem)%nat eqn:Hold.
        * intro H.
          left.
          apply Nat.leb_le in Hold.
          replace (S (length mem) - S ts)%nat with
            (S (length mem - S ts))%nat in H by lia.
          rewrite nth_error_cons_succ in H.
          replace (S ts =? 0)%nat with false by reflexivity.
          replace (S ts <=? length mem)%nat with true
            by (symmetry; apply Nat.leb_le; lia).
          exact H.
        * intro H.
          right.
          apply Nat.leb_gt in Hold.
          cbn.
          lia.
      + discriminate.
  Qed.

  Lemma lookup_cons_old (event : ev) (mem : PromMemory.t ev) ts :
    (ts ≤ length mem)%nat →
    ((event :: mem : PromMemory.t ev) !! ts) = mem !! ts.
  Proof.
    intro Hle.
    destruct ts as [|ts].
    - reflexivity.
    - unfold lookup, PromMemory.lookup_inst.
      cbn [length].
      replace (S ts =? 0)%nat with false by reflexivity.
      destruct (S ts <=? length mem)%nat eqn:Hold.
      + replace (S ts <=? S (length mem))%nat with true.
        * replace (S (length mem) - S ts)%nat with
            (S (length mem - S ts))%nat by lia.
          rewrite nth_error_cons_succ.
          reflexivity.
        * symmetry.
          apply Nat.leb_le.
          lia.
      + apply Nat.leb_gt in Hold.
        replace (S ts <=? S (length mem))%nat with false.
        * reflexivity.
        * symmetry.
          apply Nat.leb_gt.
          lia.
  Qed.

  Lemma cut_before_cons_old (event : ev) (mem : PromMemory.t ev) ts :
    (ts ≤ length mem)%nat →
    PromMemory.cut_before ts (event :: mem) = PromMemory.cut_before ts mem.
  Proof.
    intro Hle.
    unfold PromMemory.cut_before.
    cbn [length].
    replace (S (length mem) - ts)%nat with
      (S (length mem - ts))%nat by lia.
    cbn.
    reflexivity.
  Qed.

  Lemma cut_after_with_timestamps_cons_old
      (event : ev) (mem : PromMemory.t ev) ts :
    (ts ≤ length mem)%nat →
    PromMemory.cut_after_with_timestamps ts (event :: mem) =
      (event, length (event :: mem)) ::
        PromMemory.cut_after_with_timestamps ts mem.
  Proof.
    intro Hle.
    unfold PromMemory.cut_after_with_timestamps.
    cbn [PromMemory.attach_timestamps length].
    replace (S (length mem) - ts)%nat with
      (S (length mem - ts))%nat by lia.
    reflexivity.
  Qed.

End PM.
End PromMemoryFacts.

Module PromisingProof.
  Import Promising.

  Definition promise_ppstate_event (prom : Model) (tid : nat) initmem
      (event : prom.(mEvent))
      (ppst : PPState.t prom.(tState) prom.(mEvent) prom.(iis)) :
      PPState.t prom.(tState) prom.(mEvent) prom.(iis) :=
    let mem := event :: PPState.mem ppst in
    PPState.Make
      (prom.(emit_promise) tid initmem mem event (PPState.state ppst))
      mem
      (PPState.iis ppst).

  Fixpoint promise_ppstate_events (prom : Model) (tid : nat) initmem
      (events : list prom.(mEvent))
      (ppst : PPState.t prom.(tState) prom.(mEvent) prom.(iis)) :
      PPState.t prom.(tState) prom.(mEvent) prom.(iis) :=
    match events with
    | [] => ppst
    | event :: events =>
        promise_ppstate_event prom tid initmem event
          (promise_ppstate_events prom tid initmem events ppst)
    end.

  Record Replayable (prom : Model) : Prop := {
      replay_none_preserves_mem :
        ∀ {n} (tid : fin n) initmem out
          (ppst ppst' : PPState.t prom.(tState) prom.(mEvent) prom.(iis))
          (eret : eff_ret out),
          Exec.elem_of_results (ppst', (eret, None))
            (prom.(handle_outcome) n tid initmem out ppst) →
          PPState.mem ppst' = PPState.mem ppst;
      replay_promise_replay :
        ∀ {n} (tid : fin n) initmem out
          (ppst ppst' : PPState.t prom.(tState) prom.(mEvent) prom.(iis))
          (eret : eff_ret out) vpre,
          Exec.elem_of_results (ppst', (eret, Some vpre))
            (prom.(handle_outcome) n tid initmem out ppst) →
          ∃ events,
            events ≠ [] ∧
            PPState.mem ppst' = events ++ PPState.mem ppst ∧
            (∀ event, event ∈ events → prom.(mEvent_tid) event = tid) ∧
            (vpre ≤ length (PPState.mem ppst))%nat ∧
            Exec.elem_of_results (ppst', (eret, None))
              (prom.(handle_outcome) n tid initmem out
                 (promise_ppstate_events prom tid initmem events ppst))
    }.

  Definition replay_promise_replay_one (prom : Model)
      (Hreplay : Replayable prom)
      n (tid : fin n) initmem out
      (ppst ppst' : PPState.t prom.(tState) prom.(mEvent) prom.(iis))
      (eret : eff_ret out) vpre :
      Exec.elem_of_results (ppst', (eret, Some vpre))
        (prom.(handle_outcome) n tid initmem out ppst) →
      ∃ events,
        events ≠ [] ∧
        PPState.mem ppst' = events ++ PPState.mem ppst ∧
        (∀ event, event ∈ events → prom.(mEvent_tid) event = tid) ∧
        (vpre ≤ length (PPState.mem ppst))%nat ∧
        Exec.elem_of_results (ppst', (eret, None))
          (prom.(handle_outcome) n tid initmem out
             (promise_ppstate_events prom tid initmem events ppst)) :=
    replay_promise_replay prom Hreplay tid initmem out ppst ppst' eret vpre.

  Definition replay_none_preserves_mem_explicit (prom : Model)
      (Hreplay : Replayable prom)
      n (tid : fin n) initmem out
      (ppst ppst' : PPState.t prom.(tState) prom.(mEvent) prom.(iis))
      (eret : eff_ret out) :
      Exec.elem_of_results (ppst', (eret, None))
        (prom.(handle_outcome) n tid initmem out ppst) →
      PPState.mem ppst' = PPState.mem ppst :=
    replay_none_preserves_mem prom Hreplay tid initmem out ppst ppst' eret.
End PromisingProof.

Module CPStateProof.
  Import Promising.
  Import CPState.

  Definition filter_promises_mono_property (prom : Model) : Prop :=
    ∀ n tid (mem : PromMemory.t prom.(mEvent))
      (xs ys : list prom.(mEvent)) ev,
      (∀ ev, ev ∈ xs → ev ∈ ys) →
      ev ∈ prom.(filter_promises) n tid mem xs →
      ev ∈ prom.(filter_promises) n tid mem ys.

  Lemma exec_elem_of_bind_error_intro {St E A B}
      st st' st'' a err
      (e : Exec.t St E A) (k : A → Exec.t St E B) :
    Exec.elem_of_results (st', a) (e st) →
    (st'', err) ∈ Exec.errors (k a st') →
    (st'', err) ∈ Exec.errors ((e ≫= k) st).
  Proof.
    unfold elem_of, Exec.elem_of_results.
    unfold mbind, Exec.mbind_inst,
      Exec.res_mbind_inst, Exec.merge.
    destruct (e st) as [rs es].
    cbn.
    revert st' a st'' err.
    induction rs as [|[st0 a0] rs IH];
      intros st' a st'' err Hres Herr.
    - inversion Hres.
    - cbn in Hres |- *.
      apply elem_of_cons in Hres as [Heq|Hres].
      + inversion Heq; subst.
        apply elem_of_app.
        left.
        exact Herr.
      + apply elem_of_app.
        right.
        eapply IH; eauto.
  Qed.

  Section ProofProperties.
  Context (isem : iMon ()).
  Context (prom : Model).
  Context {n : nat}.
  Local Notation tState := (tState prom).
  Local Notation mEvent := (mEvent prom).
  Local Notation t := (CPState.t tState mEvent n).

  Definition cons_event_state (event : mEvent) (st : t) : t :=
    set events (event ::.) st.

  Definition cons_event_ppstate (event : mEvent)
      (ppst : PPState.t tState mEvent prom.(iis)) :
      PPState.t tState mEvent prom.(iis) :=
    set PPState.mem (event ::.) ppst.

  Definition promise_ppstate (tid : fin n) initmem (event : mEvent)
      (ppst : PPState.t tState mEvent prom.(iis)) :
      PPState.t tState mEvent prom.(iis) :=
    let mem := event :: PPState.mem ppst in
    PPState.Make
      (prom.(emit_promise) tid initmem mem event (PPState.state ppst))
      mem
      (PPState.iis ppst).

  Definition handle_outcome_no_promise (tid : fin n) initmem
      (out : outcome) : Prop :=
    ∀ ppst ppst' (eret : eff_ret out) vpre,
      Exec.elem_of_results (ppst', (eret, Some vpre))
        (prom.(handle_outcome) n tid initmem out ppst) →
      False.

  Definition handle_outcome_cons_event_stable (tid : fin n) initmem
      (event : mEvent) (out : outcome) : Prop :=
    ∀ ppst ppst' (eret : eff_ret out),
      Exec.elem_of_results (ppst', eret)
        ((prom.(handle_outcome) n tid initmem out |$> fst) ppst) →
      Exec.elem_of_results
        (cons_event_ppstate event ppst', eret)
        ((prom.(handle_outcome) n tid initmem out |$> fst)
           (cons_event_ppstate event ppst)).

  Definition handle_outcome_promise_ppstate_stable (tid : fin n) initmem
      (event : mEvent) (out : outcome) : Prop :=
    ∀ ppst ppst' (eret : eff_ret out),
      Exec.elem_of_results (ppst', eret)
        ((prom.(handle_outcome) n tid initmem out |$> fst) ppst) →
      Exec.elem_of_results
        (promise_ppstate tid initmem event ppst', eret)
        ((prom.(handle_outcome) n tid initmem out |$> fst)
           (promise_ppstate tid initmem event ppst)).

  Fixpoint cmon_handle_outcome_cons_event_stable
      (tid : fin n) initmem (event : mEvent) A (mon : iMon A) : Prop :=
    match mon with
    | Ret _ => True
    | Next call k =>
        match call with
        | inl out =>
            handle_outcome_cons_event_stable tid initmem event out ∧
            ∀ eret,
              cmon_handle_outcome_cons_event_stable
                tid initmem event A (k eret)
        | inr _ =>
            ∀ ret,
              cmon_handle_outcome_cons_event_stable
                tid initmem event A (k ret)
        end
    end.

  Fixpoint cmon_handle_outcome_promise_ppstate_stable
      (tid : fin n) initmem (event : mEvent) A (mon : iMon A) : Prop :=
    match mon with
    | Ret _ => True
    | Next call k =>
        match call with
        | inl out =>
            handle_outcome_promise_ppstate_stable tid initmem event out ∧
            ∀ eret,
              cmon_handle_outcome_promise_ppstate_stable
                tid initmem event A (k eret)
        | inr _ =>
            ∀ ret,
              cmon_handle_outcome_promise_ppstate_stable
                tid initmem event A (k ret)
        end
    end.

  Fixpoint cmon_no_promise (tid : fin n) initmem A
      (mon : iMon A) : Prop :=
    match mon with
    | Ret _ => True
    | Next call k =>
        match call with
        | inl out =>
            handle_outcome_no_promise tid initmem out ∧
            ∀ eret, cmon_no_promise tid initmem A (k eret)
        | inr _ =>
            ∀ ret, cmon_no_promise tid initmem A (k ret)
        end
    end.

  Fixpoint cmon_at_most_one_promise (tid : fin n) initmem A
      (mon : iMon A) : Prop :=
    match mon with
    | Ret _ => True
    | Next call k =>
        match call with
        | inl out =>
            (handle_outcome_no_promise tid initmem out ∧
             ∀ eret, cmon_at_most_one_promise tid initmem A (k eret)) ∨
            (∀ eret, cmon_no_promise tid initmem A (k eret))
        | inr _ =>
            ∀ ret, cmon_at_most_one_promise tid initmem A (k ret)
        end
    end.

  Fixpoint cmon_at_most_one_promise_prefix_stable
      (tid : fin n) initmem (event : mEvent) A (mon : iMon A) : Prop :=
    match mon with
    | Ret _ => True
    | Next call k =>
        match call with
        | inl out =>
            (handle_outcome_no_promise tid initmem out ∧
             handle_outcome_promise_ppstate_stable tid initmem event out ∧
             ∀ eret,
               cmon_at_most_one_promise_prefix_stable
                 tid initmem event A (k eret)) ∨
            (∀ eret, cmon_no_promise tid initmem A (k eret))
        | inr _ =>
            ∀ ret,
              cmon_at_most_one_promise_prefix_stable
                tid initmem event A (k ret)
        end
    end.

  Definition run_tid_noop_property : Prop :=
    ∀ (st st' : t) (tid : fin n),
      Exec.elem_of_results (st', ()) (run_tid isem prom tid st) →
      st' = st.

  Definition run_tid_no_promise_property : Prop :=
    ∀ (st : t) (tid : fin n),
      cmon_no_promise tid (initmem st) () isem.

  Definition run_tid_at_most_one_promise_property : Prop :=
    ∀ (st : t) (tid : fin n),
      cmon_at_most_one_promise tid (initmem st) () isem.

  Definition run_tid_at_most_one_promise_prefix_stable_property : Prop :=
    ∀ (st : t) (tid : fin n) (event : mEvent),
      cmon_at_most_one_promise_prefix_stable
        tid (initmem st) event () isem.

  Definition run_tid_no_new_events_property
      (term : terminationCondition n) : Prop :=
    let _term := term in
    ∀ (st st' : t) (tid : fin n),
      Exec.elem_of_results (st', ()) (run_tid isem prom tid st) →
      events st' = events st.

  Definition run_tid_same_thread_promise_stable_property : Prop :=
    ∀ (st : t) (tid : fin n) (event : mEvent),
      cmon_handle_outcome_promise_ppstate_stable
        tid (initmem st) event () isem.
  End ProofProperties.

  Lemma cmon_no_promise_at_most_one
      (prom : Model) {n A}
      (tid : fin n) initmem (mon : iMon A) :
    cmon_no_promise prom tid initmem A mon →
    cmon_at_most_one_promise prom tid initmem A mon.
  Proof.
    induction mon as [a|call kmon IH]; cbn.
    - intro Hno.
      exact I.
    - destruct call as [out|choice].
      + intros [Hout Htail].
        left.
        split.
        * exact Hout.
        * intro eret.
          apply IH.
          apply Htail.
      + intros Htail ret.
        apply IH.
        apply Htail.
  Qed.

  Lemma cmon_no_promise_prefix_stable
      (prom : Model) {n A}
      (tid : fin n) initmem event (mon : iMon A) :
    cmon_no_promise prom tid initmem A mon →
    cmon_at_most_one_promise_prefix_stable
      prom tid initmem event A mon.
  Proof.
    induction mon as [a|call kmon IH]; cbn.
    - intro Hno.
      exact I.
    - destruct call as [out|choice].
      + intros [Hout Htail].
        right.
        exact Htail.
      + intros Htail ret.
        apply IH.
        apply Htail.
  Qed.

  Lemma cmon_no_promise_bind
      (prom : Model) {n A B}
      (tid : fin n) initmem (mon : iMon A) (k : A → iMon B) :
    cmon_no_promise prom tid initmem A mon →
    (∀ ret, cmon_no_promise prom tid initmem B (k ret)) →
    cmon_no_promise prom tid initmem B (mon ≫= k).
  Proof.
    revert k.
    induction mon as [a|call kmon IH]; intros k Hmon Hk; cbn in *.
    - apply Hk.
    - destruct call as [out|choice].
      + destruct Hmon as [Hout Htail].
        split.
        * exact Hout.
        * intro eret.
          apply IH.
          -- apply Htail.
          -- exact Hk.
      + intro ret.
        apply IH.
        * apply Hmon.
        * exact Hk.
  Qed.

  Lemma cmon_at_most_one_promise_bind_no_left
      (prom : Model) {n A B}
      (tid : fin n) initmem (mon : iMon A) (k : A → iMon B) :
    cmon_no_promise prom tid initmem A mon →
    (∀ ret, cmon_at_most_one_promise prom tid initmem B (k ret)) →
    cmon_at_most_one_promise prom tid initmem B (mon ≫= k).
  Proof.
    revert k.
    induction mon as [a|call kmon IH]; intros k Hmon Hk; cbn in *.
    - apply Hk.
    - destruct call as [out|choice].
      + destruct Hmon as [Hout Htail].
        left.
        split.
        * exact Hout.
        * intro eret.
          apply IH.
          -- apply Htail.
          -- exact Hk.
      + intro ret.
        apply IH.
        * apply Hmon.
        * exact Hk.
  Qed.

  Lemma cmon_at_most_one_promise_bind_no_right
      (prom : Model) {n A B}
      (tid : fin n) initmem (mon : iMon A) (k : A → iMon B) :
    cmon_at_most_one_promise prom tid initmem A mon →
    (∀ ret, cmon_no_promise prom tid initmem B (k ret)) →
    cmon_at_most_one_promise prom tid initmem B (mon ≫= k).
  Proof.
    revert k.
    induction mon as [a|call kmon IH]; intros k Hmon Hk; cbn in *.
    - eapply (cmon_no_promise_at_most_one prom).
      apply Hk.
    - destruct call as [out|choice].
      + destruct Hmon as [[Hout Htail]|Htail].
        * left.
          split.
          -- exact Hout.
          -- intro eret.
             apply IH.
             ++ apply Htail.
             ++ exact Hk.
        * right.
          intro eret.
          eapply (cmon_no_promise_bind prom).
          -- apply Htail.
          -- exact Hk.
      + intro ret.
        apply IH.
        * apply Hmon.
        * exact Hk.
  Qed.

  Lemma cmon_at_most_one_promise_prefix_stable_bind_no_left
      (prom : Model) {n A B}
      (tid : fin n) initmem event (mon : iMon A) (k : A → iMon B) :
    cmon_no_promise prom tid initmem A mon →
    cmon_handle_outcome_promise_ppstate_stable
      prom tid initmem event A mon →
    (∀ ret,
      cmon_at_most_one_promise_prefix_stable
        prom tid initmem event B (k ret)) →
    cmon_at_most_one_promise_prefix_stable
      prom tid initmem event B (mon ≫= k).
  Proof.
    revert k.
    induction mon as [a|call kmon IH]; intros k Hno Hstable Hk; cbn in *.
    - apply Hk.
    - destruct call as [out|choice].
      + destruct Hno as [Hout_no Hno_tail].
        destruct Hstable as [Hout_stable Hstable_tail].
        left.
        repeat split.
        * exact Hout_no.
        * exact Hout_stable.
        * intro eret.
          apply IH.
          -- apply Hno_tail.
          -- apply Hstable_tail.
          -- exact Hk.
      + intro ret.
        apply IH.
        * apply Hno.
        * apply Hstable.
        * exact Hk.
  Qed.

  Lemma cmon_at_most_one_promise_prefix_stable_bind_no_right
      (prom : Model) {n A B}
      (tid : fin n) initmem event (mon : iMon A) (k : A → iMon B) :
    cmon_at_most_one_promise_prefix_stable
      prom tid initmem event A mon →
    (∀ ret, cmon_no_promise prom tid initmem B (k ret)) →
    cmon_at_most_one_promise_prefix_stable
      prom tid initmem event B (mon ≫= k).
  Proof.
    revert k.
    induction mon as [a|call kmon IH]; intros k Hstable Hk; cbn in *.
    - eapply (cmon_no_promise_prefix_stable prom).
      apply Hk.
    - destruct call as [out|choice].
      + destruct Hstable as [[Hout_no [Hout_stable Htail]]|Htail].
        * left.
          repeat split.
          -- exact Hout_no.
          -- exact Hout_stable.
          -- intro eret.
             apply IH.
             ++ apply Htail.
             ++ exact Hk.
        * right.
          intro eret.
          eapply (cmon_no_promise_bind prom).
          -- apply Htail.
          -- exact Hk.
      + intro ret.
        apply IH.
        * apply Hstable.
        * exact Hk.
  Qed.

  Lemma run_tid_noop_ret (isem : iMon ()) (prom : Model) {n} :
    isem = Ret tt →
    run_tid_noop_property isem prom (n:=n).
  Proof.
    intros -> st st' tid Hrun.
    unfold run_tid in Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Hlift]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    apply Exec.elem_of_liftSt_inv in Hlift as [ppst' [-> Hret]].
    apply Exec.elem_of_mret_inv in Hret as [-> _].
    destruct st.
    unfold setv, PState_PPState_set, PState_PPState, tstate.
    cbn.
    autorewrite with vec.
    change (Setter_valter tid (λ _ : tState prom, tstates0 !!! tid)
              tstates0) with
      (alter (λ _ : tState prom, tstates0 !!! tid) tid tstates0).
    rewrite valter_eq by reflexivity.
    reflexivity.
  Qed.

  Lemma run_tid_no_promise_ret (prom : Model) {n} :
    run_tid_no_promise_property (Ret tt) prom (n:=n).
  Proof.
    intros st tid.
    exact I.
  Qed.

  Lemma run_tid_same_thread_promise_stable_ret
      (prom : Model) {n} :
    run_tid_same_thread_promise_stable_property (Ret tt) prom (n:=n).
  Proof.
    intros st tid event.
    exact I.
  Qed.

  Section TermProperties.
  Context (prom : Model).
  Context {n : nat}.
  Context (term : terminationCondition n).
  Local Notation tState := (tState prom).
  Local Notation mEvent := (mEvent prom).
  Local Notation iis := (iis prom).
  Local Notation t := (CPState.t tState mEvent n).

  Definition promise_preserves_terminated_tid_property : Prop :=
    ∀ (st : t) (tid : fin n) (event : mEvent),
      terminated_tid prom term (promise_tid prom tid event st) tid =
      terminated_tid prom term st tid.

  Definition promise_preserves_any_terminated_tid_property : Prop :=
    ∀ (st : t) (tid_p tid : fin n) (event : mEvent),
      terminated_tid prom term (promise_tid prom tid_p event st) tid =
      terminated_tid prom term st tid.
  End TermProperties.

  Section TailProperties.
  Context (isem : iMon ()).
  Context (prom : Model).
  Context {n : nat}.
  Context (term : terminationCondition n).
  Local Notation tState := (tState prom).
  Local Notation mEvent := (mEvent prom).
  Local Notation iis := (iis prom).
  Local Notation t := (CPState.t tState mEvent n).
  Local Notation final := (CPState.final prom term).

  Definition run_tid_pf_tail_lift_property : Prop :=
    ∀ fuel (st st' st_fin : t) (f : final) (tid : fin n),
      Exec.elem_of_results (st', ()) (run_tid isem prom tid st) →
      Exec.elem_of_results (st_fin, f)
        (run_promise_first isem prom term fuel st') →
      Exec.elem_of_results (st_fin, f)
        (run_promise_first isem prom term (S fuel) st).

  Definition run_tid_pf_tail_lift_exists_property : Prop :=
    run_tid_pf_tail_lift_property.

  Definition run_tid_pf_tail_same_thread_promise_stable_property : Prop :=
    let _term := term in
    run_tid_same_thread_promise_stable_property isem prom (n:=n).

  Definition run_tid_pf_tail_event_shape_core_property : Prop :=
    let _term := term in
    run_tid_noop_property isem prom (n:=n) ∨
    run_tid_at_most_one_promise_property isem prom (n:=n).

  Definition run_tid_pf_tail_event_shape_property : Prop :=
    let _term := term in
    run_tid_pf_tail_event_shape_core_property.

  Definition run_tid_pf_tail_event_shape_replay_property : Prop :=
    let _term := term in
    run_tid_pf_tail_event_shape_property.

  Definition replay_none_preserves_mem_property : Prop :=
    ∀ n0 (tid : fin n0) initmem out
      (ppst ppst' : PPState.t tState mEvent iis)
      (eret : eff_ret out),
      Exec.elem_of_results (ppst', (eret, None))
        (prom.(handle_outcome) n0 tid initmem out ppst) →
      PPState.mem ppst' = PPState.mem ppst.

  Definition replay_promise_replay_property : Prop :=
    ∀ n0 (tid : fin n0) initmem out
      (ppst ppst' : PPState.t tState mEvent iis)
      (eret : eff_ret out) vpre,
      Exec.elem_of_results (ppst', (eret, Some vpre))
        (prom.(handle_outcome) n0 tid initmem out ppst) →
      ∃ events,
        events ≠ [] ∧
        PPState.mem ppst' = events ++ PPState.mem ppst ∧
        (∀ event, event ∈ events → prom.(mEvent_tid) event = tid) ∧
        (vpre ≤ length (PPState.mem ppst))%nat ∧
        Exec.elem_of_results (ppst', (eret, None))
          (prom.(handle_outcome) n0 tid initmem out
             (PromisingProof.promise_ppstate_events
                prom tid initmem events ppst)).

  Lemma run_tid_pf_tail_lift_exists_from_tail_lift :
    run_tid_pf_tail_lift_property →
    run_tid_pf_tail_lift_exists_property.
  Proof.
    intro Hlift.
    exact Hlift.
  Qed.

  Lemma run_tid_pf_tail_event_shape_from_noop :
    run_tid_noop_property isem prom (n:=n) →
    run_tid_pf_tail_event_shape_property.
  Proof.
    intro Hnoop.
    left.
    exact Hnoop.
  Qed.

  Lemma run_tid_pf_tail_event_shape_core_from_noop :
    run_tid_noop_property isem prom (n:=n) →
    run_tid_pf_tail_event_shape_core_property.
  Proof.
    intro Hnoop.
    left.
    exact Hnoop.
  Qed.

  Lemma run_tid_pf_tail_event_shape_core_from_at_most_one_promise :
    replay_none_preserves_mem_property →
    replay_promise_replay_property →
    run_tid_at_most_one_promise_property isem prom (n:=n) →
    run_tid_pf_tail_event_shape_core_property.
  Proof.
    intros _ _ Hat_most.
    right.
    exact Hat_most.
  Qed.

  Lemma run_tid_pf_tail_event_shape_replay_from_at_most_one_prefix :
    replay_none_preserves_mem_property →
    replay_promise_replay_property →
    run_tid_at_most_one_promise_property isem prom (n:=n) →
    run_tid_at_most_one_promise_prefix_stable_property isem prom (n:=n) →
    promise_preserves_any_terminated_tid_property prom term →
    run_tid_pf_tail_event_shape_replay_property.
  Proof.
    intros _ _ Hat_most _ _.
    right.
    exact Hat_most.
  Qed.

  Lemma run_tid_pf_tail_event_shape_replay_from_noop :
    run_tid_noop_property isem prom (n:=n) →
    run_tid_pf_tail_event_shape_replay_property.
  Proof.
    intro Hnoop.
    left.
    exact Hnoop.
  Qed.

  Lemma run_tid_no_new_events_from_noop :
    run_tid_noop_property isem prom (n:=n) →
    run_tid_no_new_events_property isem prom term.
  Proof.
    intros Hnoop st st' tid Hrun.
    rewrite (Hnoop st st' tid Hrun).
    reflexivity.
  Qed.

  Lemma run_tid_pf_tail_same_thread_promise_stable_from_same_thread :
    run_tid_same_thread_promise_stable_property isem prom (n:=n) →
    run_tid_pf_tail_same_thread_promise_stable_property.
  Proof.
    intro Hsame.
    exact Hsame.
  Qed.

  Lemma run_tid_pf_tail_same_thread_promise_stable_ret :
    isem = Ret tt →
    run_tid_pf_tail_same_thread_promise_stable_property.
  Proof.
    intro Hret.
    unfold run_tid_pf_tail_same_thread_promise_stable_property.
    rewrite Hret.
    apply (run_tid_same_thread_promise_stable_ret prom).
  Qed.

  Lemma run_tid_pf_tail_event_shape_from_core :
    run_tid_same_thread_promise_stable_property isem prom (n:=n) →
    promise_preserves_any_terminated_tid_property prom term →
    run_tid_pf_tail_event_shape_core_property →
    run_tid_pf_tail_event_shape_property.
  Proof.
    intros _ _ Hshape.
    exact Hshape.
  Qed.

  Lemma run_tid_pf_tail_event_shape_replay_from_event_shape :
    replay_none_preserves_mem_property →
    replay_promise_replay_property →
    run_tid_pf_tail_event_shape_property →
    run_tid_pf_tail_event_shape_replay_property.
  Proof.
    intros _ _ Hshape.
    exact Hshape.
  Qed.

  Lemma run_tid_pf_tail_lift_exists_from_event_shape :
    replay_none_preserves_mem_property →
    replay_promise_replay_property →
    run_tid_pf_tail_lift_exists_property →
    run_tid_pf_tail_event_shape_property →
    run_tid_pf_tail_lift_exists_property.
  Proof.
    intros _ _ Hlift _.
    exact Hlift.
  Qed.

  Lemma run_tid_pf_tail_lift_exists_from_event_shape_replay :
    replay_none_preserves_mem_property →
    replay_promise_replay_property →
    run_tid_pf_tail_lift_exists_property →
    run_tid_pf_tail_event_shape_replay_property →
    run_tid_pf_tail_lift_exists_property.
  Proof.
    intros _ _ Hlift _.
    exact Hlift.
  Qed.

  Lemma run_tid_pf_tail_lift_exists_from_event_shape_tail_lift :
    replay_none_preserves_mem_property →
    replay_promise_replay_property →
    run_tid_same_thread_promise_stable_property isem prom (n:=n) →
    promise_preserves_terminated_tid_property prom term →
    run_tid_pf_tail_lift_exists_property →
    run_tid_pf_tail_event_shape_property →
    run_tid_pf_tail_lift_exists_property.
  Proof.
    intros _ _ _ _ Hlift _.
    exact Hlift.
  Qed.

  Lemma run_tid_pf_tail_lift_exists_from_event_shape_core_tail_lift :
    replay_none_preserves_mem_property →
    replay_promise_replay_property →
    run_tid_same_thread_promise_stable_property isem prom (n:=n) →
    promise_preserves_any_terminated_tid_property prom term →
    run_tid_pf_tail_lift_exists_property →
    run_tid_pf_tail_event_shape_core_property →
    run_tid_pf_tail_lift_exists_property.
  Proof.
    intros _ _ _ _ Hlift _.
    exact Hlift.
  Qed.

  Record PromiseFirstTailCompatible : Prop := {
      promise_first_tail_replayable : PromisingProof.Replayable prom;
      promise_first_tail_lift : run_tid_pf_tail_lift_property;
    }.

  Record PromiseFirstCompatible : Prop := {
      promise_first_compatible_tail : PromiseFirstTailCompatible;
    }.

  Lemma promise_first_compatible_from_tail :
    PromiseFirstTailCompatible →
    PromiseFirstCompatible.
  Proof.
    intro Htail.
    constructor.
    exact Htail.
  Qed.
  End TailProperties.

  Section RunBridgeBasics.
  Context (isem : iMon ()).
  Context (prom : Model).
  Context {n : nat}.
  Context (term : terminationCondition n).
  Local Notation tState := (tState prom).
  Local Notation mEvent := (mEvent prom).
  Local Notation iis := (iis prom).
  Local Notation t := (CPState.t tState mEvent n).
  Local Existing Instance mEvent_eq_dec.

  Lemma promise_select_tid_inv fuel st (tid : fin n) ev :
    Exec.elem_of_results ev (promise_select_tid isem prom term fuel st tid) →
    match enumerate_results isem prom term tid (initmem st) fuel
            (tstate tid st) (events st) with
    | {| promises := promises0 |} => ev ∈ promises0
    end.
  Proof.
    unfold promise_select_tid.
    destruct (enumerate_results isem prom term tid (initmem st) fuel
                (tstate tid st) (events st))
      as [promises0 final_states0 errors0 out_of_fuel0] eqn:Hen.
    destruct out_of_fuel0.
    - intro Hin.
      apply Exec.elem_of_res_bind_elim in Hin
        as [b [_ Hbranch]].
      destruct b.
      + unfold mthrow, Exec.res_throw_inst in Hbranch.
        cbn in Hbranch.
        inversion Hbranch.
      + apply Exec.elem_of_res_mchoosel_inv in Hbranch.
        exact Hbranch.
    - intro Hin.
      apply Exec.elem_of_res_mchoosel_inv in Hin.
      exact Hin.
  Qed.

  Lemma promise_select_tid_intro fuel st (tid : fin n) ev :
    match enumerate_results isem prom term tid (initmem st) fuel
            (tstate tid st) (events st) with
    | {| promises := promises0 |} => ev ∈ promises0
    end →
    Exec.elem_of_results ev (promise_select_tid isem prom term fuel st tid).
  Proof.
    unfold promise_select_tid.
    destruct (enumerate_results isem prom term tid (initmem st) fuel
                (tstate tid st) (events st))
      as [promises0 final_states0 errors0 out_of_fuel0] eqn:Hen.
    intro Hev.
    destruct out_of_fuel0.
    - eapply Exec.elem_of_res_bind_intro with (a := false).
      + change
          (Exec.elem_of_results false
             (mchoosef bool : Exec.res string bool)).
        unfold mchoosef.
        apply Exec.elem_of_res_mchoosel.
        set_solver.
      + apply Exec.elem_of_res_mchoosel.
        exact Hev.
    - apply Exec.elem_of_res_mchoosel.
      exact Hev.
  Qed.

  Definition promise_source_lists
      (res :
        Exec.res
          ((list mEvent * PPState.t tState mEvent iis) * string)
          ((list mEvent * PPState.t tState mEvent iis) * bool)) :
      list (list mEvent) :=
    res |> Exec.results |>
      omap (λ '((new_proms, _), is_done),
          if (is_done : bool) then Some new_proms else None).

  Lemma promise_source_lists_intro res ev proms ppst :
    Exec.elem_of_results ((proms, ppst), true) res →
    ev ∈ proms →
    ev ∈ concat (promise_source_lists res).
  Proof.
    intros Hres Hev.
    unfold promise_source_lists.
    apply elem_of_list_In.
    apply in_concat.
    exists proms.
    split.
    - apply elem_of_list_In.
      apply elem_of_list_omap.
      exists ((proms, ppst), true).
      split; [exact Hres|reflexivity].
    - apply elem_of_list_In.
      exact Hev.
  Qed.

  Lemma run_to_termination_true_result_fuel_step
      (tid0 : fin n) init_memory fuel base
      proms ppst proms' ppst' :
    Exec.elem_of_results ((proms', ppst'), true)
      (run_to_termination isem prom term tid0 init_memory
         fuel base (proms, ppst)) →
    Exec.elem_of_results ((proms', ppst'), true)
      (run_to_termination isem prom term tid0 init_memory
         (S fuel) base (proms, ppst)).
  Proof.
    revert proms ppst proms' ppst'.
    induction fuel as [|fuel IH];
      intros proms ppst proms' ppst' Hrun; cbn in Hrun |- *.
    - apply Exec.elem_of_bind_elim in Hrun
        as [pair_get [ts [Hget Hafter_get]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      cbn in Hafter_get.
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + destruct (term tid0 (tState_regs prom (PPState.state ppst)))
          eqn:Hterm.
        * rewrite Hterm.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get as [Heq_state].
          inversion Heq_state; subst ppst' proms'.
          apply Exec.elem_of_mret.
        * rewrite Hterm.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get.
    - apply Exec.elem_of_bind_elim in Hrun
        as [pair_get [ts [Hget Hafter_get]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      cbn in Hafter_get.
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + destruct (term tid0 (tState_regs prom (PPState.state ppst)))
          eqn:Hterm0.
        * rewrite Hterm0.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get as [Heq_state].
          inversion Heq_state; subst ppst' proms'.
          apply Exec.elem_of_mret.
        * rewrite Hterm0.
          apply Exec.elem_of_bind_elim in Hafter_get
            as [pair_step [u [Hstep Htail]]].
          destruct u.
          destruct pair_step as [proms_step pp_step].
          eapply Exec.elem_of_bind_intro.
          -- exact Hstep.
          -- apply Exec.elem_of_bind_elim in Htail
               as [pair_get1 [ts1 [Hget1 Hafter_get1]]].
             apply Exec.elem_of_mget_inv in Hget1 as [-> ->].
             cbn in Hafter_get1.
             eapply Exec.elem_of_bind_intro.
             ++ apply Exec.elem_of_mget.
             ++ destruct
                  (term tid0 (tState_regs prom (PPState.state pp_step)))
                  eqn:Hterm1.
                ** rewrite Hterm1.
                   unfold elem_of, Exec.elem_of_results in Hafter_get1.
                   cbn in Hafter_get1.
                   apply elem_of_list_singleton in Hafter_get1.
                   inversion Hafter_get1 as [Heq_state].
                   inversion Heq_state; subst ppst' proms'.
                   apply Exec.elem_of_mret.
                ** rewrite Hterm1.
                   apply Exec.elem_of_bind_elim in Hafter_get1
                     as [pair_reset [u [Hreset Hrec]]].
                   destruct u.
                   apply Exec.elem_of_mset_inv in Hreset as ->.
                   eapply Exec.elem_of_bind_intro.
                   --- apply Exec.elem_of_mset.
                   --- eapply IH.
                       exact Hrec.
  Qed.

  Lemma run_to_termination_true_result_fuel_mono
      (tid0 : fin n) init_memory fuel fuel' base
      proms ppst proms' ppst' :
    (fuel ≤ fuel')%nat →
    Exec.elem_of_results ((proms', ppst'), true)
      (run_to_termination isem prom term tid0 init_memory
         fuel base (proms, ppst)) →
    Exec.elem_of_results ((proms', ppst'), true)
      (run_to_termination isem prom term tid0 init_memory
         fuel' base (proms, ppst)).
  Proof.
    intros Hle Hrun.
    induction Hle as [|fuel' Hle IH].
    - exact Hrun.
    - apply run_to_termination_true_result_fuel_step.
      exact IH.
  Qed.

  Lemma run_to_termination_promise_event_fuel_step
      (tid0 : fin n) init_memory fuel base
      (st0 : list mEvent * PPState.t tState mEvent iis) ev :
    ev ∈ concat (promise_source_lists
      (run_to_termination isem prom term tid0 init_memory
         fuel base st0)) →
    ev ∈ concat (promise_source_lists
      (run_to_termination isem prom term tid0 init_memory
         (S fuel) base st0)).
  Proof.
    intro Hin.
    unfold promise_source_lists in Hin.
    apply elem_of_list_In in Hin.
    apply in_concat in Hin as [proms [Hproms Hev]].
    apply elem_of_list_In in Hproms.
    apply elem_of_list_omap in Hproms
      as [[[proms0 ppst0] is_done] [Hres Hsource]].
    destruct is_done; cbn in Hsource; [|discriminate].
    inversion Hsource; subst proms0.
    destruct st0 as [proms_init ppst_init].
    eapply promise_source_lists_intro.
    - eapply run_to_termination_true_result_fuel_step.
      exact Hres.
    - apply elem_of_list_In.
      exact Hev.
  Qed.

  Lemma enumerate_results_promises_mono
      (Hfilter_mono : filter_promises_mono_property prom)
      (tid0 : fin n) init_memory fuel fuel' ts mem ev :
    (fuel ≤ fuel')%nat →
    ev ∈ promises prom
      (enumerate_results isem prom term tid0 init_memory fuel ts mem) →
    ev ∈ promises prom
      (enumerate_results isem prom term tid0 init_memory fuel' ts mem).
  Proof.
    intros Hle.
    induction Hle as [|fuel' Hle IH]; intro Hin.
    - exact Hin.
    - apply IH in Hin.
      clear IH Hle.
      unfold enumerate_results in Hin |- *.
      cbn [promises].
      set (st0 := ([], PPState.Make ts mem (iis_init prom))).
      set (old_res :=
        run_to_termination isem prom term tid0 init_memory fuel'
          (length mem) st0).
      set (new_res :=
        run_to_termination isem prom term tid0 init_memory (S fuel')
          (length mem) st0).
      set (old_lists := promise_source_lists old_res).
      set (new_lists := promise_source_lists new_res).
      set (old_raw := remove_dups (concat old_lists)) in *.
      set (new_raw := remove_dups (concat new_lists)).
      change (ev ∈ prom.(filter_promises) n tid0 mem new_raw).
      change (ev ∈ prom.(filter_promises) n tid0 mem old_raw) in Hin.
      eapply (Hfilter_mono n tid0 mem old_raw new_raw ev).
      2: exact Hin.
      intros ev0 Hev0.
      subst old_raw new_raw.
      rewrite elem_of_remove_dups in Hev0.
      rewrite elem_of_remove_dups.
      subst old_lists new_lists old_res new_res st0.
      eapply run_to_termination_promise_event_fuel_step.
      exact Hev0.
  Qed.

  Lemma enumerate_results_final_states_mono
      (tid0 : fin n) init_memory fuel fuel' ts mem ts' :
    (fuel ≤ fuel')%nat →
    ts' ∈ match enumerate_results isem prom term tid0 init_memory fuel ts mem with
          | {| final_states := final_states0 |} => final_states0
          end →
    ts' ∈ match enumerate_results isem prom term tid0 init_memory fuel' ts mem with
          | {| final_states := final_states0 |} => final_states0
          end.
  Proof.
    intros Hle Hin.
    unfold enumerate_results in Hin |- *.
    cbn [final_states] in Hin |- *.
    set (old_res :=
      run_to_termination isem prom term tid0 init_memory fuel
        (length mem) ([], PPState.Make ts mem (iis_init prom))) in *.
    set (new_res :=
      run_to_termination isem prom term tid0 init_memory fuel'
        (length mem) ([], PPState.Make ts mem (iis_init prom))).
    apply elem_of_list_omap in Hin
      as [[[new_proms ppst] is_done] [Hres Hstate]].
    destruct is_done; cbn in Hstate; [|discriminate].
    destruct new_proms as [|ev new_proms]; cbn in Hstate; [|discriminate].
    destruct (decide (PPState.mem ppst = mem)) as [Hmem|Hmem].
    2: discriminate.
    inversion Hstate; subst ts'.
    apply elem_of_list_omap.
    exists (([], ppst), true).
    split.
    - subst old_res new_res.
      eapply run_to_termination_true_result_fuel_mono.
      + exact Hle.
      + exact Hres.
    - cbn.
      destruct (decide (PPState.mem ppst = mem)) as [_|Hne].
      + reflexivity.
      + contradiction.
  Qed.

  Lemma promise_select_tid_fuel_mono
      (Hfilter_mono : filter_promises_mono_property prom)
      fuel fuel' st (tid0 : fin n) ev :
    (fuel ≤ fuel')%nat →
    Exec.elem_of_results ev
      (promise_select_tid isem prom term fuel st tid0) →
    Exec.elem_of_results ev
      (promise_select_tid isem prom term fuel' st tid0).
  Proof.
    intros Hle Hev.
    apply promise_select_tid_inv in Hev.
    apply promise_select_tid_intro.
    eapply enumerate_results_promises_mono; eauto.
  Qed.

  Lemma cpromise_tid_inv fuel st st' (tid : fin n) :
    Exec.elem_of_results (st', ()) (cpromise_tid isem prom term fuel tid st) →
    ∃ ev,
      Exec.elem_of_results ev (promise_select_tid isem prom term fuel st tid) ∧
      st' = promise_tid prom tid ev st.
  Proof.
    unfold cpromise_tid.
    intro Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Htail]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    apply Exec.elem_of_bind_elim in Htail
      as [st_ev [ev [Hev Hset]]].
    apply Exec.elem_of_lift_res_inv in Hev as [-> Hev].
    apply Exec.elem_of_mSetv_inv in Hset as ->.
    exists ev.
    split; [exact Hev|reflexivity].
  Qed.

  Lemma run_step_inv fuel st st' :
    Exec.elem_of_results (st', ()) (run_step isem prom term fuel st) →
    (∃ tid ev,
      terminated_tid prom term st tid = false ∧
      Exec.elem_of_results ev
        (promise_select_tid isem prom term fuel st tid) ∧
      st' = promise_tid prom tid ev st) ∨
    (∃ tid,
      terminated_tid prom term st tid = false ∧
      Exec.elem_of_results (st', ()) (run_tid isem prom tid st)).
  Proof.
    unfold run_step.
    intro Hstep.
    apply Exec.elem_of_bind_elim in Hstep
      as [st_step_get [st_read [Hget_step Hafter_step_get]]].
    apply Exec.elem_of_mGet_inv in Hget_step as [-> ->].
    apply Exec.elem_of_bind_elim in Hafter_step_get
      as [st_tid [tid [Hchoose_tid Hafter_tid]]].
    apply Exec.elem_of_mchoose_inv in Hchoose_tid as ->.
    destruct (terminated_tid prom term st tid) eqn:Hterm_tid.
    { unfold elem_of, Exec.elem_of_results in Hafter_tid.
      cbn in Hafter_tid.
      inversion Hafter_tid. }
    apply Exec.elem_of_bind_elim in Hafter_tid
      as [st_choice [promise [Hchoose_promise Hafter_promise]]].
    change
      (Exec.elem_of_results (st_choice, promise)
         ((mchoosel (enum bool) : Exec.t t string bool) st))
    in Hchoose_promise.
    apply Exec.elem_of_mchoosel_inv in Hchoose_promise
      as [-> _].
    destruct promise.
    - apply cpromise_tid_inv in Hafter_promise
        as [ev [Hev ->]].
      left.
      exists tid, ev.
      repeat split; auto.
    - right.
      exists tid.
      split; [exact Hterm_tid|exact Hafter_promise].
  Qed.

  Lemma run_step_promise_intro fuel st (tid : fin n) ev :
    terminated_tid prom term st tid = false →
    Exec.elem_of_results ev
      (promise_select_tid isem prom term fuel st tid) →
    Exec.elem_of_results
      (promise_tid prom tid ev st, ()) (run_step isem prom term fuel st).
  Proof.
    intros Hterm_tid Hev.
    unfold run_step.
    eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
    - apply Exec.elem_of_mGet.
    - eapply Exec.elem_of_bind_intro with (st' := st) (a := tid).
      + apply Exec.elem_of_mchoose.
      + rewrite Hterm_tid.
        eapply Exec.elem_of_bind_intro with (st' := st) (a := true).
        * change
            (Exec.elem_of_results (st, true)
               ((mchoosel (enum bool) : Exec.t t string bool) st)).
          apply Exec.elem_of_mchoosel.
          set_solver.
        * unfold cpromise_tid.
          eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
          -- apply Exec.elem_of_mGet.
          -- eapply Exec.elem_of_bind_intro with (st' := st) (a := ev).
             ++ apply Exec.elem_of_lift_res.
                exact Hev.
             ++ apply Exec.elem_of_mSetv.
  Qed.

  Lemma run_step_tid_intro fuel st st' (tid : fin n) :
    terminated_tid prom term st tid = false →
    Exec.elem_of_results (st', ()) (run_tid isem prom tid st) →
    Exec.elem_of_results (st', ()) (run_step isem prom term fuel st).
  Proof.
    intros Hterm_tid Hrun_tid.
    unfold run_step.
    eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
    - apply Exec.elem_of_mGet.
    - eapply Exec.elem_of_bind_intro with (st' := st) (a := tid).
      + apply Exec.elem_of_mchoose.
      + rewrite Hterm_tid.
        eapply Exec.elem_of_bind_intro with (st' := st) (a := false).
        * change
            (Exec.elem_of_results (st, false)
               ((mchoosel (enum bool) : Exec.t t string bool) st)).
          apply Exec.elem_of_mchoosel.
          set_solver.
        * exact Hrun_tid.
  Qed.

  Lemma terminated_not_from_tid_false st (tid : fin n) :
    terminated_tid prom term st tid = false →
    ¬ terminated prom term st.
  Proof.
    intros Htid Hterm.
    unfold terminated in Hterm.
    apply bool_unfold in Hterm.
    specialize (Hterm tid).
    cbn in Hterm.
    rewrite Htid in Hterm.
    exact Hterm.
  Qed.

  Lemma validate_final_inv_at (st_check st st' : t) :
    Exec.elem_of_results (st', ()) (validate_final prom st_check st) →
    st' = st ∧
    nopromises prom st_check = true ∧
    check_valid_end prom st_check = [].
  Proof.
    unfold validate_final.
    intro Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_guard [Hnoprom [Hguard Hafter]]].
    apply Exec.elem_of_guard_discard_inv in Hguard as ->.
    destruct (check_valid_end prom st_check) as [|err errs] eqn:Herrs.
    - apply Exec.elem_of_mret_inv in Hafter as [-> _].
      split; [reflexivity|].
      split.
      + apply true_eq_true.
        exact Hnoprom.
      + reflexivity.
    - apply Exec.elem_of_bind_elim in Hafter
        as [st_err [err' [Herr Hthrow]]].
      unfold mthrow, Exec.throw_inst in Hthrow.
      cbn in Hthrow.
      inversion Hthrow.
  Qed.

  Lemma validate_final_inv (st st' : t) :
    Exec.elem_of_results (st', ()) (validate_final prom st st) →
    st' = st ∧ nopromises prom st = true ∧ check_valid_end prom st = [].
  Proof.
    apply validate_final_inv_at.
  Qed.

  Lemma run_current_final fuel (st : t) :
    nopromises prom st = true →
    check_valid_end prom st = [] →
    ∀ Hterm : terminated prom term st,
      Exec.elem_of_results (st, make_final prom term st Hterm)
        (run isem prom term fuel st).
  Proof.
    intros Hnoprom Hcheck Hterm.
    assert (Hnoprom_true : nopromises prom st).
    {
      apply true_eq_true.
      exact Hnoprom.
    }
    destruct fuel; cbn.
    - eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
      + apply Exec.elem_of_mGet.
      + destruct (decide
          (forallb (terminated_tid prom term st) (fin_enum n)))
          as [Hterm'|Hnot].
        * eapply Exec.elem_of_bind_intro with (a := tt).
          -- unfold validate_final.
             destruct (Exec.elem_of_guard_discard
               (St:=t) (E:=string) st Hnoprom_true)
               as [noprom_proof Hguard].
             eapply Exec.elem_of_bind_intro with (a := noprom_proof).
             ++ exact Hguard.
             ++ rewrite Hcheck.
                apply Exec.elem_of_mret.
          -- replace (make_final prom term st Hterm')
              with (make_final prom term st Hterm).
             ++ apply Exec.elem_of_mret.
             ++ unfold make_final.
                f_equal.
                apply proof_irrelevance.
        * exfalso.
          apply Hnot.
          exact Hterm.
    - eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
      + apply Exec.elem_of_mGet.
      + destruct (decide
          (forallb (terminated_tid prom term st) (fin_enum n)))
          as [Hterm'|Hnot].
        * eapply Exec.elem_of_bind_intro with (a := tt).
          -- unfold validate_final.
             destruct (Exec.elem_of_guard_discard
               (St:=t) (E:=string) st Hnoprom_true)
               as [noprom_proof Hguard].
             eapply Exec.elem_of_bind_intro with (a := noprom_proof).
             ++ exact Hguard.
             ++ rewrite Hcheck.
                apply Exec.elem_of_mret.
          -- replace (make_final prom term st Hterm')
              with (make_final prom term st Hterm).
             ++ apply Exec.elem_of_mret.
             ++ unfold make_final.
                f_equal.
                apply proof_irrelevance.
        * exfalso.
          apply Hnot.
          exact Hterm.
  Qed.

  Lemma run_step_run_intro fuel st st_step st_fin f :
    ¬ terminated prom term st →
    Exec.elem_of_results (st_step, ()) (run_step isem prom term (S fuel) st) →
    Exec.elem_of_results (st_fin, f) (run isem prom term fuel st_step) →
    Exec.elem_of_results (st_fin, f) (run isem prom term (S fuel) st).
  Proof.
    intros Hnot_term Hstep Htail.
    cbn.
    eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
    - apply Exec.elem_of_mGet.
    - destruct (decide (forallb (terminated_tid prom term st) (fin_enum n)))
        as [Hterm|Hnot].
      + exfalso.
        apply Hnot_term.
        exact Hterm.
      + eapply Exec.elem_of_bind_intro.
        * exact Hstep.
        * exact Htail.
  Qed.

  Lemma enumerate_results_terminated_final_state_zero
      (tid : fin n) initmem ts mem :
    term tid (prom.(tState_regs) ts) = true →
    ts ∈ match enumerate_results isem prom term tid initmem 0 ts mem with
         | {| final_states := final_states0 |} => final_states0
         end.
  Proof.
    intro Hterm.
    unfold enumerate_results.
    set (ppst := PPState.Make ts mem (iis_init prom)).
    set (res :=
      run_to_termination isem prom term tid initmem 0
        (length mem) ([], ppst)).
    assert (Hrun : Exec.elem_of_results (([], ppst), true) res).
    {
      subst res ppst.
      cbn.
      eapply Exec.elem_of_bind_intro.
      - apply Exec.elem_of_mget.
      - cbn.
        rewrite Hterm.
        apply Exec.elem_of_mret.
    }
    cbn.
    apply elem_of_list_omap.
    exists (([], ppst), true).
    split.
    - exact Hrun.
    - subst ppst.
      cbn.
      destruct (decide (mem = mem)) as [_|Hne].
      + reflexivity.
      + exfalso.
        apply Hne.
        reflexivity.
  Qed.

  Lemma run_to_termination_terminated_initial
      (tid : fin n) initmem fuel base
      (ppst : PPState.t tState mEvent iis) :
    term tid (prom.(tState_regs) (PPState.state ppst)) = true →
    Exec.elem_of_results (([], ppst), true)
      (run_to_termination isem prom term tid initmem fuel base ([], ppst)).
  Proof.
    intro Hterm.
    destruct fuel; cbn.
    - eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + rewrite Hterm.
        apply Exec.elem_of_mret.
    - eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + rewrite Hterm.
        apply Exec.elem_of_mret.
  Qed.

  Lemma enumerate_results_terminated_final_state
      (tid : fin n) initmem fuel ts mem :
    term tid (prom.(tState_regs) ts) = true →
    ts ∈ match enumerate_results isem prom term tid initmem fuel ts mem with
         | {| final_states := final_states0 |} => final_states0
         end.
  Proof.
    intro Hterm.
    unfold enumerate_results.
    set (ppst := PPState.Make ts mem (iis_init prom)).
    set (res :=
      run_to_termination isem prom term tid initmem fuel
        (length mem) ([], ppst)).
    assert (Hrun : Exec.elem_of_results (([], ppst), true) res).
    {
      subst res ppst.
      apply run_to_termination_terminated_initial.
      exact Hterm.
    }
    cbn.
    apply elem_of_list_omap.
    exists (([], ppst), true).
    split.
    - exact Hrun.
    - subst ppst.
      cbn.
      destruct (decide (mem = mem)) as [_|Hne].
      + reflexivity.
      + exfalso.
        apply Hne.
        reflexivity.
  Qed.

  Lemma run_promise_first_current_final_one (st : t) :
    nopromises prom st = true →
    check_valid_end prom st = [] →
    ∀ Hterm : terminated prom term st,
      Exec.elem_of_results (st, make_final prom term st Hterm)
        (run_promise_first isem prom term 1 st).
  Proof.
    destruct st as [tstates0 initmem0 events0].
    intros Hnoprom Hcheck Hterm.
    cbn in Hnoprom, Hterm |- *.
    apply true_eq_true in Hnoprom.
    set (st0 := {| tstates := tstates0;
                   initmem := initmem0;
                   events := events0 |}).
    eapply Exec.elem_of_bind_intro with (st' := st0) (a := st0).
    - apply Exec.elem_of_mGet.
    - subst st0.
      eapply Exec.elem_of_bind_intro
        with (st' := {| tstates := tstates0;
                        initmem := initmem0;
                        events := events0 |}) (a := 1%nat).
      + change
          (Exec.elem_of_results
             ({| tstates := tstates0; initmem := initmem0; events := events0 |},
              1%nat)
             ((mchoosel (seq 0 4) :
                 Exec.t (PState.t tState mEvent n) string nat)
                {| tstates := tstates0;
                   initmem := initmem0;
                   events := events0 |})).
        apply Exec.elem_of_mchoosel.
        cbn.
        set_solver.
      + eapply Exec.elem_of_bind_intro
          with (st' := {| tstates := tstates0;
                         initmem := initmem0;
                         events := events0 |}) (a := tstates0).
        * apply Exec.elem_of_mchoosel.
          apply cprodn_spec.
          intro idx.
          autorewrite with vec.
          apply enumerate_results_terminated_final_state_zero.
          pose proof Hterm as Hterm_all.
          unfold terminated, terminated_tid in Hterm_all.
          cbn in Hterm_all.
          apply bool_unfold in Hterm_all.
          specialize (Hterm_all idx).
          cbn in Hterm_all.
          apply true_eq_true.
          apply Hterm_all.
          apply Exec.elem_of_fin_enum.
        * destruct (Exec.elem_of_guard_discard
              (St:=PState.t tState mEvent n) (E:=string)
              {| tstates := tstates0;
                 initmem := initmem0;
                 events := events0 |} Hterm) as [term_proof Hterm_guard].
          eapply Exec.elem_of_bind_intro with (a := term_proof).
          -- exact Hterm_guard.
          -- eapply Exec.elem_of_bind_intro with (a := tt).
             ++ unfold validate_final.
                destruct (Exec.elem_of_guard_discard
                  (St:=PState.t tState mEvent n) (E:=string)
                  {| tstates := tstates0;
                     initmem := initmem0;
                     events := events0 |} Hnoprom)
                  as [noprom_proof Hnoprom_guard].
                eapply Exec.elem_of_bind_intro with (a := noprom_proof).
                ** exact Hnoprom_guard.
                ** cbn [initmem events].
                   rewrite Hcheck.
                   apply Exec.elem_of_mret.
             ++ replace (make_final prom term
                  {| tstates := tstates0;
                     initmem := initmem0;
                     events := events0 |} term_proof)
                  with
                  (make_final prom term
                     {| tstates := tstates0;
                        initmem := initmem0;
                        events := events0 |} Hterm).
                ** apply Exec.elem_of_mret.
                ** unfold make_final.
                   f_equal.
                   apply proof_irrelevance.
  Qed.

  Lemma run_promise_first_current_final fuel (st : t) :
    nopromises prom st = true →
    check_valid_end prom st = [] →
    ∀ Hterm : terminated prom term st,
      Exec.elem_of_results (st, make_final prom term st Hterm)
        (run_promise_first isem prom term (S fuel) st).
  Proof.
    destruct st as [tstates0 initmem0 events0].
    intros Hnoprom Hcheck Hterm.
    cbn in Hnoprom, Hterm |- *.
    apply true_eq_true in Hnoprom.
    set (st0 := {| tstates := tstates0;
                   initmem := initmem0;
                   events := events0 |}).
    eapply Exec.elem_of_bind_intro with (st' := st0) (a := st0).
    - apply Exec.elem_of_mGet.
    - subst st0.
      eapply Exec.elem_of_bind_intro
        with (st' := {| tstates := tstates0;
                        initmem := initmem0;
                        events := events0 |}) (a := 1%nat).
      + change
          (Exec.elem_of_results
             ({| tstates := tstates0; initmem := initmem0; events := events0 |},
              1%nat)
             ((mchoosel (seq 0 4) :
                 Exec.t (PState.t tState mEvent n) string nat)
                {| tstates := tstates0;
                   initmem := initmem0;
                   events := events0 |})).
        apply Exec.elem_of_mchoosel.
        cbn.
        set_solver.
      + eapply Exec.elem_of_bind_intro
          with (st' := {| tstates := tstates0;
                         initmem := initmem0;
                         events := events0 |}) (a := tstates0).
        * apply Exec.elem_of_mchoosel.
          apply cprodn_spec.
          intro idx.
          autorewrite with vec.
          apply enumerate_results_terminated_final_state.
          pose proof Hterm as Hterm_all.
          unfold terminated, terminated_tid in Hterm_all.
          cbn in Hterm_all.
          apply bool_unfold in Hterm_all.
          specialize (Hterm_all idx).
          cbn in Hterm_all.
          apply true_eq_true.
          apply Hterm_all.
          apply Exec.elem_of_fin_enum.
        * destruct (Exec.elem_of_guard_discard
              (St:=PState.t tState mEvent n) (E:=string)
              {| tstates := tstates0;
                 initmem := initmem0;
                 events := events0 |} Hterm) as [term_proof Hterm_guard].
          eapply Exec.elem_of_bind_intro with (a := term_proof).
          -- exact Hterm_guard.
          -- eapply Exec.elem_of_bind_intro with (a := tt).
             ++ unfold validate_final.
                destruct (Exec.elem_of_guard_discard
                  (St:=PState.t tState mEvent n) (E:=string)
                  {| tstates := tstates0;
                     initmem := initmem0;
                     events := events0 |} Hnoprom)
                  as [noprom_proof Hnoprom_guard].
                eapply Exec.elem_of_bind_intro with (a := noprom_proof).
                ** exact Hnoprom_guard.
                ** cbn [initmem events].
                   rewrite Hcheck.
                   apply Exec.elem_of_mret.
             ++ replace (make_final prom term
                  {| tstates := tstates0;
                     initmem := initmem0;
                     events := events0 |} term_proof)
                  with
                  (make_final prom term
                     {| tstates := tstates0;
                        initmem := initmem0;
                        events := events0 |} Hterm).
                ** apply Exec.elem_of_mret.
                ** unfold make_final.
                   f_equal.
                   apply proof_irrelevance.
  Qed.

  Lemma validate_final_ret_to_pf_one st st_fin f
      (Hterm : terminated prom term st) :
    Exec.elem_of_results (st_fin, f)
      ((validate_final prom st;; mret (make_final prom term st Hterm)) st) →
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term 1 st).
  Proof.
    intro Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_valid [u [Hvalid Hret]]].
    destruct u.
    apply validate_final_inv in Hvalid
      as [-> [Hnoprom Hcheck]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    apply run_promise_first_current_final_one; eauto.
  Qed.

  Lemma run_final_zero_to_pf st st_fin f :
    Exec.elem_of_results (st_fin, f) (run isem prom term 0 st) →
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term 1 st).
  Proof.
    intro Hrun.
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Hafter_get]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    destruct (decide
      (forallb (terminated_tid prom term st) (fin_enum n)))
      as [Hterm|Hnot] in Hafter_get.
    - eapply validate_final_ret_to_pf_one with (Hterm:=Hterm).
      exact Hafter_get.
    - unfold mthrow, Exec.throw_inst in Hafter_get.
      cbn in Hafter_get.
      inversion Hafter_get.
  Qed.

  Lemma run_promise_first_promise_selected fuel st st' f (tid : fin n) ev :
    terminated_tid prom term st tid = false →
    Exec.elem_of_results ev
      (promise_select_tid isem prom term fuel st tid) →
    Exec.elem_of_results (st', f)
      (run_promise_first isem prom term fuel
         (promise_tid prom tid ev st)) →
    Exec.elem_of_results (st', f)
      (run_promise_first isem prom term (S fuel) st).
  Proof.
    intros Hterm_tid Hev Htail.
    cbn.
    eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
    - apply Exec.elem_of_mGet.
    - eapply Exec.elem_of_bind_intro with (st' := st) (a := 0%nat).
      + change
          (Exec.elem_of_results (st, 0%nat)
             ((mchoosel (seq 0 4) : Exec.t t string nat) st)).
        apply Exec.elem_of_mchoosel.
        cbn.
        set_solver.
      + eapply Exec.elem_of_bind_intro with (st' := st) (a := tid).
        * change
            (Exec.elem_of_results (st, tid)
               ((mchoosef (fin n) : Exec.t t string (fin n)) st)).
          unfold mchoosef.
          apply Exec.elem_of_mchoosel.
          apply Exec.elem_of_fin_enum.
        * rewrite Hterm_tid.
          eapply Exec.elem_of_bind_intro with (st' := st) (a := ev).
          -- apply Exec.elem_of_lift_res.
             exact Hev.
          -- eapply Exec.elem_of_bind_intro
               with (st' := promise_tid prom tid ev st) (a := tt).
             ++ apply Exec.elem_of_mSet.
             ++ exact Htail.
  Qed.

  Lemma run_promise_first_final_fuel_step_mono
      (Hfilter_mono : filter_promises_mono_property prom)
      fuel st st_fin f :
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term fuel st) →
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term (S fuel) st).
  Proof.
    revert st st_fin f.
    induction fuel as [|fuel IH]; intros st st_fin f Hpf.
    - cbn in Hpf.
      unfold mthrow, Exec.throw_inst in Hpf.
      cbn in Hpf.
      inversion Hpf.
    - cbn in Hpf.
      apply Exec.elem_of_bind_elim in Hpf
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      apply Exec.elem_of_bind_elim in Hafter_get
        as [st_opt [opt [Hopt Hbranch]]].
      change
        (Exec.elem_of_results (st_opt, opt)
           ((mchoosel (seq 0 4) : Exec.t t string nat) st)) in Hopt.
      apply Exec.elem_of_mchoosel_inv in Hopt as [-> Hopt_in].
      destruct opt as [|[|[|opt]]]; cbn in Hbranch.
      + apply Exec.elem_of_bind_elim in Hbranch
          as [st_tid [tid [Htid Hafter_tid]]].
        unfold mchoosef in Htid.
        apply Exec.elem_of_mchoosel_inv in Htid as [-> _].
        destruct (terminated_tid prom term st tid) eqn:Hterm_tid.
        * unfold mdiscard, mchoose, Exec.choose_inst,
            fmap, Exec.fmap_inst, Exec.res_fmap_inst in Hafter_tid.
          cbn in Hafter_tid.
          inversion Hafter_tid.
        * apply Exec.elem_of_bind_elim in Hafter_tid
            as [st_ev [ev [Hev Hafter_ev]]].
          apply Exec.elem_of_lift_res_inv in Hev as [-> Hev].
          apply Exec.elem_of_bind_elim in Hafter_ev
            as [st_set [u [Hset Htail]]].
          destruct u.
          apply Exec.elem_of_mSet_inv in Hset as ->.
          eapply run_promise_first_promise_selected.
          -- exact Hterm_tid.
          -- eapply promise_select_tid_fuel_mono.
             ++ exact Hfilter_mono.
             ++ apply Nat.le_succ_diag_r.
             ++ exact Hev.
          -- apply IH.
             exact Htail.
      + apply Exec.elem_of_bind_elim in Hbranch
          as [st_targets [target [Htarget Hafter_target]]].
        apply Exec.elem_of_mchoosel_inv in Htarget
          as [-> Htarget_in].
        set (st_target := Make target (initmem st) (events st)) in *.
        apply Exec.elem_of_bind_elim in Hafter_target
          as [st_guard [Hterm [Hguard Hafter_guard]]].
        apply Exec.elem_of_guard_discard_inv in Hguard as ->.
        apply Exec.elem_of_bind_elim in Hafter_guard
          as [st_valid [u [Hvalid Hret]]].
        destruct u.
        apply Exec.elem_of_mret_inv in Hret as [-> ->].
        cbn.
        eapply Exec.elem_of_bind_intro with (st' := st) (a := st).
        * apply Exec.elem_of_mGet.
        * eapply Exec.elem_of_bind_intro with (st' := st) (a := 1%nat).
          -- change
              (Exec.elem_of_results (st, 1%nat)
                 ((mchoosel (seq 0 4) : Exec.t t string nat) st)).
             apply Exec.elem_of_mchoosel.
             cbn.
             set_solver.
          -- eapply Exec.elem_of_bind_intro with (st' := st) (a := target).
             ++ apply Exec.elem_of_mchoosel.
                apply cprodn_spec.
                intro idx.
                rewrite cprodn_spec in Htarget_in.
                specialize (Htarget_in idx).
                autorewrite with vec in Htarget_in |- *.
                eapply enumerate_results_final_states_mono.
                ** apply Nat.le_succ_diag_r.
                ** exact Htarget_in.
             ++ destruct (Exec.elem_of_guard_discard
                   (St:=t) (E:=string) st Hterm)
                   as [term_proof Hterm_guard].
                eapply Exec.elem_of_bind_intro with (a := term_proof).
                ** exact Hterm_guard.
                ** eapply Exec.elem_of_bind_intro with (a := tt).
                   --- exact Hvalid.
                   --- replace (make_final prom term st_target term_proof)
                         with (make_final prom term st_target Hterm).
                       +++ apply Exec.elem_of_mret.
                       +++ unfold make_final.
                           f_equal.
                           apply proof_irrelevance.
      + apply Exec.elem_of_bind_elim in Hbranch
          as [st_err [err [Herr Hthrow]]].
        unfold mthrow, Exec.throw_inst in Hthrow.
        cbn in Hthrow.
        inversion Hthrow.
      + destruct
          (bool_decide
            (∃ x ∈ map (out_of_fuel prom)
                  (vmap
                     (λ '(tid, ts),
                        enumerate_results isem prom term tid (initmem st)
                          fuel ts (events st)) (venumerate (tstates st))),
              (x : bool))).
        * unfold mthrow, Exec.throw_inst in Hbranch.
          cbn in Hbranch.
          inversion Hbranch.
        * unfold mdiscard, mchoose, Exec.choose_inst,
            fmap, Exec.fmap_inst, Exec.res_fmap_inst in Hbranch.
          cbn in Hbranch.
          inversion Hbranch.
  Qed.

  Lemma run_tid_pf_tail_lift_from_noop :
    filter_promises_mono_property prom →
    run_tid_noop_property isem prom (n:=n) →
    run_tid_pf_tail_lift_property isem prom term.
  Proof.
    intros Hfilter_mono Hnoop fuel st st' st_fin f tid Hrun Hpf.
    rewrite <- (Hnoop st st' tid Hrun).
    eapply run_promise_first_final_fuel_step_mono; eauto.
  Qed.

  Lemma validate_final_ret_to_pf fuel_pf st st_fin f
      (Hterm : terminated prom term st) :
    (1 ≤ fuel_pf)%nat →
    Exec.elem_of_results (st_fin, f)
      ((validate_final prom st;; mret (make_final prom term st Hterm)) st) →
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term fuel_pf st).
  Proof.
    intros Hfuel Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_valid [u [Hvalid Hret]]].
    destruct u.
    apply validate_final_inv in Hvalid
      as [-> [Hnoprom Hcheck]].
    apply Exec.elem_of_mret_inv in Hret as [-> ->].
    destruct fuel_pf as [|fuel_pf].
    - inversion Hfuel.
    - apply run_promise_first_current_final; eauto.
  Qed.

  Lemma elem_of_seq_0_S_mono fuel fuel' x :
    (fuel ≤ fuel')%nat →
    x ∈ seq 0 (S fuel) →
    x ∈ seq 0 (S fuel').
  Proof.
    intros Hle Hin.
    apply elem_of_seq in Hin.
    apply elem_of_seq.
    lia.
  Qed.

  Lemma run_step_mono fuel fuel' st st' :
    filter_promises_mono_property prom →
    (fuel ≤ fuel')%nat →
    Exec.elem_of_results (st', ()) (run_step isem prom term fuel st) →
    Exec.elem_of_results (st', ()) (run_step isem prom term fuel' st).
  Proof.
    intros Hfilter_mono Hle Hstep.
    pose proof (run_step_inv fuel st st' Hstep) as Hinv.
    destruct Hinv
      as [[tid [ev [Hterm_tid [Hev ->]]]]
         |[tid [Hterm_tid Hrun_tid]]].
    - eapply run_step_promise_intro.
      + exact Hterm_tid.
      + eapply promise_select_tid_fuel_mono; eauto.
    - eapply run_step_tid_intro; eauto.
  Qed.

  Lemma run_final_zero_to_pf_with_run_tid_pf_tail_lift
      fuel_pf st st_fin f :
    (1 ≤ fuel_pf)%nat →
    Exec.elem_of_results (st_fin, f) (run isem prom term 0 st) →
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term fuel_pf st).
  Proof.
    intros Hfuel Hrun.
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Hafter_get]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    destruct (decide
      (forallb (terminated_tid prom term st) (fin_enum n)))
      as [Hterm|Hnot]
      in Hafter_get.
    - eapply validate_final_ret_to_pf with (Hterm:=Hterm).
      + exact Hfuel.
      + exact Hafter_get.
    - unfold mthrow, Exec.throw_inst in Hafter_get.
      cbn in Hafter_get.
      inversion Hafter_get.
  Qed.

  Lemma run_final_succ_to_pf_with_run_tid_pf_tail_lift
      fuel fuel_pf st st_fin f :
    filter_promises_mono_property prom →
    (∀ fuel_pf st st_fin f,
      filter_promises_mono_property prom →
      run_tid_pf_tail_lift_property isem prom term →
      (S fuel ≤ fuel_pf)%nat →
      Exec.elem_of_results (st_fin, f) (run isem prom term fuel st) →
      Exec.elem_of_results (st_fin, f)
        (run_promise_first isem prom term fuel_pf st)) →
    run_tid_pf_tail_lift_property isem prom term →
    (S (S fuel) ≤ fuel_pf)%nat →
    Exec.elem_of_results (st_fin, f) (run isem prom term (S fuel) st) →
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term fuel_pf st).
  Proof.
    intros Hfilter_mono IH Hlift Hfuel Hrun.
    cbn in Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Hafter_get]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    destruct (decide
      (forallb (terminated_tid prom term st) (fin_enum n)))
      as [Hterm|Hnot]
      in Hafter_get.
    - eapply validate_final_ret_to_pf with (Hterm:=Hterm).
      + eapply Nat.le_trans.
        * apply le_n_S.
          apply Nat.le_0_l.
        * exact Hfuel.
      + exact Hafter_get.
    - apply Exec.elem_of_bind_elim in Hafter_get
        as [st_step [u [Hstep Htail]]].
      destruct u.
      pose proof (run_step_inv (S fuel) st st_step Hstep)
        as Hstep_cases.
      destruct Hstep_cases
        as [[tid [ev [Hterm_tid [Hev_select ->]]]]
           |[tid [_ Hrun_tid]]].
      + destruct fuel_pf as [|fuel_pf].
        * inversion Hfuel.
        * eapply run_promise_first_promise_selected.
          -- exact Hterm_tid.
          -- eapply (@promise_select_tid_fuel_mono
               Hfilter_mono (S fuel) fuel_pf st tid ev).
             ++ lia.
             ++ exact Hev_select.
          -- eapply IH.
             ++ exact Hfilter_mono.
             ++ exact Hlift.
             ++ lia.
             ++ exact Htail.
      + destruct fuel_pf as [|fuel_pf].
        * inversion Hfuel.
        * eapply Hlift.
          -- exact Hrun_tid.
          -- eapply IH.
             ++ exact Hfilter_mono.
             ++ exact Hlift.
             ++ lia.
             ++ exact Htail.
  Qed.

  Lemma run_final_to_pf_with_run_tid_pf_tail_lift
      fuel fuel_pf st st_fin f :
    filter_promises_mono_property prom →
    run_tid_pf_tail_lift_property isem prom term →
    (S fuel ≤ fuel_pf)%nat →
    Exec.elem_of_results (st_fin, f) (run isem prom term fuel st) →
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term fuel_pf st).
  Proof.
    revert fuel_pf st st_fin f.
    induction fuel as [|fuel IH];
      intros fuel_pf st st_fin f Hfilter_mono Hlift Hfuel Hrun.
    - eapply run_final_zero_to_pf_with_run_tid_pf_tail_lift.
      + exact Hfuel.
      + exact Hrun.
    - eapply run_final_succ_to_pf_with_run_tid_pf_tail_lift.
      + exact Hfilter_mono.
      + exact IH.
      + exact Hlift.
      + exact Hfuel.
      + exact Hrun.
  Qed.

  Lemma run_final_to_pf_exists_with_run_tid_pf_tail_lift
      fuel st st_fin f :
    filter_promises_mono_property prom →
    run_tid_pf_tail_lift_exists_property isem prom term →
    Exec.elem_of_results (st_fin, f) (run isem prom term fuel st) →
    ∃ fuel_pf,
      Exec.elem_of_results (st_fin, f)
        (run_promise_first isem prom term fuel_pf st).
  Proof.
    intros Hfilter_mono Hlift Hrun.
    exists (S fuel).
    eapply run_final_to_pf_with_run_tid_pf_tail_lift.
    - exact Hfilter_mono.
    - exact Hlift.
    - apply Nat.le_refl.
    - exact Hrun.
  Qed.
  End RunBridgeBasics.

  Section RunTidStability.
  Context (isem : iMon ()).
  Context (prom : Model).
  Context {n : nat}.
  Context (term : terminationCondition n).
  Local Notation tState := (tState prom).
  Local Notation mEvent := (mEvent prom).
  Local Notation iis := (iis prom).
  Local Notation t := (CPState.t tState mEvent n).
  Local Existing Instance PState_PPState_set.

  Lemma PState_PPState_cons_event_state
      (tid : fin n) (event : mEvent) (st : t) :
    PState_PPState prom tid (cons_event_state prom event st) =
    cons_event_ppstate prom event (PState_PPState prom tid st).
  Proof.
    destruct st.
    reflexivity.
  Qed.

  Lemma initmem_cons_event_state (event : mEvent) (st : t) :
    initmem (cons_event_state prom event st) = initmem st.
  Proof.
    destruct st.
    reflexivity.
  Qed.

  Lemma setv_PState_PPState_cons_event_state
      (tid : fin n) (event : mEvent) (st : t) ppst :
    setv (PState_PPState prom tid)
      (cons_event_ppstate prom event ppst)
      (cons_event_state prom event st) =
    cons_event_state prom event
      (setv (PState_PPState prom tid) ppst st).
  Proof.
    destruct st, ppst.
    reflexivity.
  Qed.

  Lemma PState_PPState_promise_tid
      (tid : fin n) init_memory (event : mEvent) (st : t) :
    init_memory = initmem st →
    PState_PPState prom tid (promise_tid prom tid event st) =
    promise_ppstate prom tid init_memory event (PState_PPState prom tid st).
  Proof.
    intro Hinit.
    subst init_memory.
    destruct st.
    unfold promise_tid, promise_ppstate, PState_PPState, tstate.
    cbn.
    rewrite vlookup_alter.
    reflexivity.
  Qed.

  Lemma initmem_promise_tid (tid : fin n) (event : mEvent) (st : t) :
    initmem (promise_tid prom tid event st) = initmem st.
  Proof.
    destruct st.
    unfold promise_tid.
    cbn.
    reflexivity.
  Qed.

  Lemma Setter_valter_same_index_overwrite {A} (tid : fin n)
      (v : vec A n) (f g : A → A) (x : A) :
    Setter_valter tid f (Setter_valter tid (λ _ : A, x) v) =
    Setter_valter tid (λ _ : A, f x) (Setter_valter tid g v).
  Proof.
    apply vec_eq.
    intro idx.
    destruct (decide (idx = tid)) as [->|Hne].
    - autorewrite with vec.
      reflexivity.
    - rewrite !vlookup_insert_ne by congruence.
      reflexivity.
  Qed.

  Lemma Setter_valter_id {A} (tid : fin n) (v : vec A n) :
    Setter_valter tid (λ x : A, x) v = v.
  Proof.
    apply vec_eq.
    intro idx.
    destruct (decide (idx = tid)) as [->|Hne].
    - autorewrite with vec.
      reflexivity.
    - rewrite vlookup_insert_ne by congruence.
      reflexivity.
  Qed.

  Lemma setv_PState_PPState_promise_tid
      (tid : fin n) init_memory (event : mEvent) (st : t) ppst :
    init_memory = initmem st →
    setv (PState_PPState prom tid)
      (promise_ppstate prom tid init_memory event ppst)
      (promise_tid prom tid event st) =
    promise_tid prom tid event (setv (PState_PPState prom tid) ppst st).
  Proof.
    intro Hinit.
    subst init_memory.
    destruct st, ppst.
    unfold promise_tid, promise_ppstate, PState_PPState, tstate.
    unfold setv, PState_PPState_set.
    cbn.
    autorewrite with vec.
    rewrite (Setter_valter_same_index_overwrite
      tid tstates0
      (emit_promise prom tid initmem0 (event :: mem) event)
      (emit_promise prom tid initmem0 (event :: events0) event)
      state).
    reflexivity.
  Qed.

  Lemma cinterp_cons_event_stable {A} (tid : fin n) initmem
      (event : mEvent) (mon : iMon A)
      (ppst ppst' : PPState.t tState mEvent iis) (ret : A) :
    cmon_handle_outcome_cons_event_stable
      prom tid initmem event A mon →
    Exec.elem_of_results (ppst', ret)
      (cinterp
         (λ out, prom.(handle_outcome) n tid initmem out |$> fst)
         mon ppst) →
    Exec.elem_of_results
      (cons_event_ppstate prom event ppst', ret)
      (cinterp
         (λ out, prom.(handle_outcome) n tid initmem out |$> fst)
         mon (cons_event_ppstate prom event ppst)).
  Proof.
    revert ppst ppst' ret.
    induction mon as [ret0|call k IH]; intros ppst ppst' ret
      Hstable Hrun; cbn in Hstable, Hrun |- *.
    - apply Exec.elem_of_mret_inv in Hrun as [-> ->].
      apply Exec.elem_of_mret.
    - destruct call as [out|choice].
      + destruct Hstable as [Hout Htail].
        apply Exec.elem_of_bind_elim in Hrun
          as [pp_mid [eret [Hout_run Htail_run]]].
        eapply Exec.elem_of_bind_intro.
        * apply Hout.
          exact Hout_run.
        * eapply IH.
          -- apply Htail.
          -- exact Htail_run.
      + destruct choice as [choices].
        apply Exec.elem_of_bind_elim in Hrun
          as [pp_choose [choice_ret [Hchoose Htail_run]]].
        apply Exec.elem_of_mchoose_inv in Hchoose as ->.
        eapply Exec.elem_of_bind_intro.
        * apply Exec.elem_of_mchoose.
        * eapply IH.
          -- apply Hstable.
          -- exact Htail_run.
  Qed.

  Lemma cinterp_promise_ppstate_stable {A} (tid : fin n) initmem
      (event : mEvent) (mon : iMon A)
      (ppst ppst' : PPState.t tState mEvent iis) (ret : A) :
    cmon_handle_outcome_promise_ppstate_stable
      prom tid initmem event A mon →
    Exec.elem_of_results (ppst', ret)
      (cinterp
         (λ out, prom.(handle_outcome) n tid initmem out |$> fst)
         mon ppst) →
    Exec.elem_of_results
      (promise_ppstate prom tid initmem event ppst', ret)
      (cinterp
         (λ out, prom.(handle_outcome) n tid initmem out |$> fst)
         mon (promise_ppstate prom tid initmem event ppst)).
  Proof.
    revert ppst ppst' ret.
    induction mon as [ret0|call k IH]; intros ppst ppst' ret
      Hstable Hrun; cbn in Hstable, Hrun |- *.
    - apply Exec.elem_of_mret_inv in Hrun as [-> ->].
      apply Exec.elem_of_mret.
    - destruct call as [out|choice].
      + destruct Hstable as [Hout Htail].
        apply Exec.elem_of_bind_elim in Hrun
          as [pp_mid [eret [Hout_run Htail_run]]].
        eapply Exec.elem_of_bind_intro.
        * apply Hout.
          exact Hout_run.
        * eapply IH.
          -- apply Htail.
          -- exact Htail_run.
      + destruct choice as [choices].
        apply Exec.elem_of_bind_elim in Hrun
          as [pp_choose [choice_ret [Hchoose Htail_run]]].
        apply Exec.elem_of_mchoose_inv in Hchoose as ->.
        eapply Exec.elem_of_bind_intro.
        * apply Exec.elem_of_mchoose.
        * eapply IH.
          -- apply Hstable.
          -- exact Htail_run.
  Qed.

  Lemma run_tid_cons_event_stable_mon (tid : fin n) init_memory
      (event : mEvent) (st st' : t) :
    init_memory = initmem st →
    cmon_handle_outcome_cons_event_stable
      prom tid init_memory event () isem →
    Exec.elem_of_results (st', ()) (run_tid isem prom tid st) →
    Exec.elem_of_results
      (cons_event_state prom event st', ())
      (run_tid isem prom tid (cons_event_state prom event st)).
  Proof.
    intros Hinit Hstable Hrun.
    subst init_memory.
    unfold run_tid in Hrun |- *.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Hlift]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    apply Exec.elem_of_liftSt_inv in Hlift
      as [ppst' [-> Hcinterp]].
    rewrite <- (setv_PState_PPState_cons_event_state tid event st ppst').
    eapply Exec.elem_of_bind_intro.
    - apply Exec.elem_of_mGet.
    - rewrite initmem_cons_event_state.
      eapply Exec.elem_of_liftSt.
      rewrite PState_PPState_cons_event_state.
      eapply cinterp_cons_event_stable.
      + exact Hstable.
      + exact Hcinterp.
  Qed.

  Lemma run_tid_promise_same_stable_mon (tid : fin n) init_memory
      (event : mEvent) (st st' : t) :
    init_memory = initmem st →
    cmon_handle_outcome_promise_ppstate_stable
      prom tid init_memory event () isem →
    Exec.elem_of_results (st', ()) (run_tid isem prom tid st) →
    Exec.elem_of_results
      (promise_tid prom tid event st', ())
      (run_tid isem prom tid (promise_tid prom tid event st)).
  Proof.
    intros Hinit Hstable Hrun.
    subst init_memory.
    unfold run_tid in Hrun |- *.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Hlift]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    apply Exec.elem_of_liftSt_inv in Hlift
      as [ppst' [-> Hcinterp]].
    rewrite <-
      (setv_PState_PPState_promise_tid tid (initmem st) event st ppst'
         eq_refl).
    eapply Exec.elem_of_bind_intro.
    - apply Exec.elem_of_mGet.
    - rewrite initmem_promise_tid.
      eapply Exec.elem_of_liftSt.
      rewrite (PState_PPState_promise_tid tid (initmem st) event st eq_refl).
      eapply cinterp_promise_ppstate_stable.
      + exact Hstable.
      + exact Hcinterp.
  Qed.

  Lemma setv_PPState_iis_cons_event_ppstate
      (tid : fin n) (initmem : memoryMap) (event : mEvent) iisv
      (ppst : PPState.t tState mEvent iis) :
    setv PPState.iis iisv
      (cons_event_ppstate prom event ppst) =
    cons_event_ppstate prom event (setv PPState.iis iisv ppst).
  Proof.
    destruct ppst.
    reflexivity.
  Qed.

  Lemma setv_PPState_iis_promise_ppstate
      (tid : fin n) (initmem : memoryMap) (event : mEvent) iisv
      (ppst : PPState.t tState mEvent iis) :
    setv PPState.iis iisv
      (promise_ppstate prom tid initmem event ppst) =
    promise_ppstate prom tid initmem event
      (setv PPState.iis iisv ppst).
  Proof.
    destruct ppst.
    reflexivity.
  Qed.

  Fixpoint run_to_termination_plain (tid : fin n) initmem (fuel : nat) :
      Exec.t (PPState.t tState mEvent iis) string bool :=
    match fuel with
    | 0%nat =>
        ts ← mget PPState.state;
        mret (term tid (prom.(tState_regs) ts))
    | S fuel =>
        ts ← mget PPState.state;
        if term tid (prom.(tState_regs) ts) then
          mret true
        else
          let handler out :=
            prom.(handle_outcome) n tid initmem out |$> fst in
          cinterp handler isem;;
          ts ← mget PPState.state;
          if term tid (prom.(tState_regs) ts) then
            mret true
          else
            msetv PPState.iis prom.(iis_init);;
            run_to_termination_plain tid initmem fuel
    end.

  Lemma run_to_termination_plain_cons_event_stable_mon
      (tid : fin n) initmem event fuel ppst ppst' b :
    cmon_handle_outcome_cons_event_stable
      prom tid initmem event () isem →
    Exec.elem_of_results (ppst', b)
      (run_to_termination_plain tid initmem fuel ppst) →
    Exec.elem_of_results
      (cons_event_ppstate prom event ppst', b)
      (run_to_termination_plain tid initmem fuel
         (cons_event_ppstate prom event ppst)).
  Proof.
    revert ppst ppst' b.
    induction fuel as [|fuel IH]; intros ppst ppst' b Hstable Hrun;
      cbn in Hrun |- *.
    - apply Exec.elem_of_bind_elim in Hrun
        as [pp_get [ts [Hget Hafter_get]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + change (PPState.state (cons_event_ppstate prom event ppst))
          with (PPState.state ppst).
        destruct (term tid (tState_regs prom (PPState.state ppst)))
          eqn:Hterm.
        * apply Exec.elem_of_mret_inv in Hafter_get as [-> ->].
          apply Exec.elem_of_mret.
        * apply Exec.elem_of_mret_inv in Hafter_get as [-> ->].
          apply Exec.elem_of_mret.
    - apply Exec.elem_of_bind_elim in Hrun
        as [pp_get0 [ts0 [Hget0 Hafter_get0]]].
      apply Exec.elem_of_mget_inv in Hget0 as [-> ->].
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + change (PPState.state (cons_event_ppstate prom event ppst))
          with (PPState.state ppst).
        destruct (term tid (tState_regs prom (PPState.state ppst)))
          eqn:Hterm0.
        * apply Exec.elem_of_mret_inv in Hafter_get0 as [-> ->].
          apply Exec.elem_of_mret.
        * apply Exec.elem_of_bind_elim in Hafter_get0
            as [pp_step [u [Hstep Htail]]].
          destruct u.
          eapply Exec.elem_of_bind_intro.
          -- eapply cinterp_cons_event_stable.
             ++ exact Hstable.
             ++ exact Hstep.
          -- apply Exec.elem_of_bind_elim in Htail
               as [pp_get [ts [Hget Hafter_get]]].
             apply Exec.elem_of_mget_inv in Hget as [-> ->].
             eapply Exec.elem_of_bind_intro.
             ++ apply Exec.elem_of_mget.
             ++ change
                  (PPState.state (cons_event_ppstate prom event pp_step))
                  with (PPState.state pp_step).
                destruct
                  (term tid (tState_regs prom (PPState.state pp_step)))
                  eqn:Hterm.
                ** apply Exec.elem_of_mret_inv in Hafter_get
                     as [-> ->].
                   apply Exec.elem_of_mret.
                ** apply Exec.elem_of_bind_elim in Hafter_get
                     as [pp_reset [u [Hreset Hrec]]].
                   destruct u.
                   unfold msetv in Hreset.
                   apply Exec.elem_of_mset_inv in Hreset as ->.
                   eapply Exec.elem_of_bind_intro.
                   --- unfold msetv.
                       apply Exec.elem_of_mset.
                   --- change
                        (set PPState.iis (λ _ : iis, iis_init prom)
                           (cons_event_ppstate prom event pp_step))
                        with
                        (setv PPState.iis (iis_init prom)
                           (cons_event_ppstate prom event pp_step)).
                       rewrite
                         (setv_PPState_iis_cons_event_ppstate
                            tid initmem event).
                       apply IH.
                       +++ exact Hstable.
                       +++ exact Hrec.
  Qed.

  Lemma run_to_termination_plain_promise_ppstate_stable_mon
      (tid : fin n) initmem event fuel ppst ppst' b :
    (∀ ppst0,
      prom.(tState_regs)
        (PPState.state
           (promise_ppstate prom tid initmem event ppst0)) =
      prom.(tState_regs) (PPState.state ppst0)) →
    cmon_handle_outcome_promise_ppstate_stable
      prom tid initmem event () isem →
    Exec.elem_of_results (ppst', b)
      (run_to_termination_plain tid initmem fuel ppst) →
    Exec.elem_of_results
      (promise_ppstate prom tid initmem event ppst', b)
      (run_to_termination_plain tid initmem fuel
         (promise_ppstate prom tid initmem event ppst)).
  Proof.
    revert ppst ppst' b.
    induction fuel as [|fuel IH]; intros ppst ppst' b Hregs Hstable Hrun;
      cbn in Hrun |- *.
    - apply Exec.elem_of_bind_elim in Hrun
        as [pp_get [ts [Hget Hafter_get]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + rewrite Hregs.
        destruct (term tid (tState_regs prom (PPState.state ppst)))
          eqn:Hterm.
        * apply Exec.elem_of_mret_inv in Hafter_get as [-> ->].
          apply Exec.elem_of_mret.
        * apply Exec.elem_of_mret_inv in Hafter_get as [-> ->].
          apply Exec.elem_of_mret.
    - apply Exec.elem_of_bind_elim in Hrun
        as [pp_get0 [ts0 [Hget0 Hafter_get0]]].
      apply Exec.elem_of_mget_inv in Hget0 as [-> ->].
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + rewrite Hregs.
        destruct (term tid (tState_regs prom (PPState.state ppst)))
          eqn:Hterm0.
        * apply Exec.elem_of_mret_inv in Hafter_get0 as [-> ->].
          apply Exec.elem_of_mret.
        * apply Exec.elem_of_bind_elim in Hafter_get0
            as [pp_step [u [Hstep Htail]]].
          destruct u.
          eapply Exec.elem_of_bind_intro.
          -- eapply cinterp_promise_ppstate_stable.
             ++ exact Hstable.
             ++ exact Hstep.
          -- apply Exec.elem_of_bind_elim in Htail
               as [pp_get [ts [Hget Hafter_get]]].
             apply Exec.elem_of_mget_inv in Hget as [-> ->].
             eapply Exec.elem_of_bind_intro.
             ++ apply Exec.elem_of_mget.
             ++ rewrite Hregs.
                destruct
                  (term tid (tState_regs prom (PPState.state pp_step)))
                  eqn:Hterm.
                ** apply Exec.elem_of_mret_inv in Hafter_get
                     as [-> ->].
                   apply Exec.elem_of_mret.
                ** apply Exec.elem_of_bind_elim in Hafter_get
                     as [pp_reset [u [Hreset Hrec]]].
                   destruct u.
                   unfold msetv in Hreset.
                   apply Exec.elem_of_mset_inv in Hreset as ->.
                   eapply Exec.elem_of_bind_intro.
                   --- unfold msetv.
                       apply Exec.elem_of_mset.
                   --- change
                        (set PPState.iis (λ _ : iis, iis_init prom)
                           (promise_ppstate prom tid initmem event pp_step))
                        with
                        (setv PPState.iis (iis_init prom)
                           (promise_ppstate prom tid initmem event pp_step)).
                       rewrite
                         (setv_PPState_iis_promise_ppstate
                            tid initmem event).
                       apply IH.
                       +++ exact Hregs.
                       +++ exact Hstable.
                       +++ exact Hrec.
  Qed.

  End RunTidStability.

  Section RunPfToDirect.
  Context (isem : iMon ()).
  Context (prom : Model).
  Context {n : nat}.
  Context (term : terminationCondition n).
  Local Notation tState := (tState prom).
  Local Notation mEvent := (mEvent prom).
  Local Notation iis := (iis prom).
  Local Notation t := (CPState.t tState mEvent n).
  Local Notation final := (CPState.final prom term).
  Local Existing Instance PState_PPState_set.

  Fixpoint run_tid_until (tid : fin n) (fuel : nat) :
      Exec.t t string bool :=
    st ← mGet;
    if terminated_tid prom term st tid then
      mret true
    else
      match fuel with
      | 0%nat => mret false
      | S fuel =>
          run_tid isem prom tid;;
          run_tid_until tid fuel
      end.

  Definition set_PState_PPState (tid : fin n)
      (ppst : PPState.t tState mEvent iis) (st : t) : t :=
    st
    |> setv (tstate tid) ppst.(PPState.state)
    |> setv events ppst.(PPState.mem).

  Lemma set_PState_PPState_initmem tid ppst st :
    initmem (set_PState_PPState tid ppst st) = initmem st.
  Proof.
    destruct st, ppst.
    reflexivity.
  Qed.

  Lemma set_PState_PPState_get tid st :
    set_PState_PPState tid (PState_PPState prom tid st) st = st.
  Proof.
    destruct st.
    unfold set_PState_PPState, PState_PPState, tstate.
    cbn.
    autorewrite with vec.
    change (Setter_valter tid (λ _ : tState, tstates0 !!! tid)
              tstates0) with
      (alter (λ _ : tState, tstates0 !!! tid) tid tstates0).
    rewrite valter_eq by reflexivity.
    reflexivity.
  Qed.

  Lemma tstate_set_PState_PPState tid ppst st :
    tstate tid (set_PState_PPState tid ppst st) = PPState.state ppst.
  Proof.
    destruct st, ppst.
    unfold set_PState_PPState, tstate.
    cbn.
    autorewrite with vec.
    reflexivity.
  Qed.

  Lemma tstate_set_PState_PPState_ne tid tid_other ppst st :
    tid_other ≠ tid →
    tstate tid_other (set_PState_PPState tid ppst st) =
      tstate tid_other st.
  Proof.
    intro Hne.
    destruct st, ppst.
    unfold set_PState_PPState, tstate.
    cbn.
    rewrite vlookup_insert_ne by congruence.
    reflexivity.
  Qed.

  Lemma events_set_PState_PPState tid ppst st :
    events (set_PState_PPState tid ppst st) = PPState.mem ppst.
  Proof.
    destruct st, ppst.
    reflexivity.
  Qed.

  Lemma set_PState_PPState_overwrite tid ppst' ppst st :
    set_PState_PPState tid ppst' (set_PState_PPState tid ppst st) =
    set_PState_PPState tid ppst' st.
  Proof.
    destruct st as [tstates0 initmem0 events0].
    destruct ppst as [state0 mem0 iis0].
    destruct ppst' as [state1 mem1 iis1].
    unfold set_PState_PPState, setv, tstate.
    cbn.
    autorewrite with vec.
    rewrite (Setter_valter_same_index_overwrite
      tid tstates0 (λ _ : tState, state1) (λ x : tState, x) state0).
    rewrite (Setter_valter_id tid tstates0).
    reflexivity.
  Qed.

  Lemma PState_PPState_set_PState_PPState_iis_init tid ppst st :
    PState_PPState prom tid (set_PState_PPState tid ppst st) =
    setv PPState.iis prom.(iis_init) ppst.
  Proof.
    destruct st, ppst.
    unfold set_PState_PPState, PState_PPState, tstate.
    cbn.
    autorewrite with vec.
    reflexivity.
  Qed.

  Lemma run_tid_from_plain_step (tid : fin n) init_memory st ppst :
    init_memory = initmem st →
    Exec.elem_of_results (ppst, tt)
      (cinterp
         (λ out, prom.(handle_outcome) n tid init_memory out |$> fst)
         isem (PState_PPState prom tid st)) →
    Exec.elem_of_results
      (set_PState_PPState tid ppst st, tt) (run_tid isem prom tid st).
  Proof.
    intros Hinit Hstep.
    unfold run_tid.
    eapply Exec.elem_of_bind_intro.
    - apply Exec.elem_of_mGet.
    - subst init_memory.
      unfold Exec.liftSt, Exec.liftSt_full, Exec.map_state.
      unfold elem_of, Exec.elem_of_results in *.
      destruct
        (cinterp
           (λ out : outcome,
              prom.(handle_outcome) n tid (initmem st) out |$> fst)
           isem (PState_PPState prom tid st))
        as [rs es] eqn:Hcinterp.
      cbn in Hstep |- *.
      rewrite elem_of_list_fmap.
      exists (ppst, tt).
      split.
      + cbn.
        f_equal.
      + exact Hstep.
  Qed.

  Lemma terminated_tid_PState_PPState tid st :
    terminated_tid prom term st tid =
    term tid (prom.(tState_regs)
      (PPState.state (PState_PPState prom tid st))).
  Proof.
    reflexivity.
  Qed.

  Lemma terminated_tid_set_PState_PPState tid ppst st :
    terminated_tid prom term (set_PState_PPState tid ppst st) tid =
    term tid (prom.(tState_regs) (PPState.state ppst)).
  Proof.
    destruct st, ppst.
    unfold set_PState_PPState, terminated_tid, tstate.
    cbn.
    autorewrite with vec.
    reflexivity.
  Qed.

  Lemma run_tid_until_terminated_initial tid fuel st :
    terminated_tid prom term st tid = true →
    Exec.elem_of_results (st, true) (run_tid_until tid fuel st).
  Proof.
    destruct fuel; cbn; intro Hterm;
      eapply Exec.elem_of_bind_intro.
    - apply Exec.elem_of_mGet.
    - rewrite Hterm.
      apply Exec.elem_of_mret.
    - apply Exec.elem_of_mGet.
    - rewrite Hterm.
      apply Exec.elem_of_mret.
  Qed.

  Lemma run_tid_until_true_mono tid fuel st st' :
    Exec.elem_of_results (st', true) (run_tid_until tid fuel st) →
    Exec.elem_of_results (st', true) (run_tid_until tid (S fuel) st).
  Proof.
    revert st st'.
    induction fuel as [|fuel IH]; intros st st' Hrun;
      cbn in Hrun |- *.
    - apply Exec.elem_of_bind_elim in Hrun
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mGet.
      + destruct (terminated_tid prom term st tid) eqn:Hterm.
        * change (Exec.elem_of_results (st', true)
            ((mret true : Exec.t t string bool) st))
            in Hafter_get.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get; subst st'.
          apply Exec.elem_of_mret.
        * change (Exec.elem_of_results (st', true)
            ((mret false : Exec.t t string bool) st))
            in Hafter_get.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get.
    - apply Exec.elem_of_bind_elim in Hrun
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mGet.
      + destruct (terminated_tid prom term st tid) eqn:Hterm.
        * change (Exec.elem_of_results (st', true)
            ((mret true : Exec.t t string bool) st))
            in Hafter_get.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get; subst st'.
          apply Exec.elem_of_mret.
        * change (Exec.elem_of_results (st', true)
            ((run_tid isem prom tid;; run_tid_until tid fuel) st))
            in Hafter_get.
          apply Exec.elem_of_bind_elim in Hafter_get
            as [st_step [u [Hstep Htail]]].
          destruct u.
          eapply Exec.elem_of_bind_intro.
          -- exact Hstep.
          -- apply IH.
             exact Htail.
  Qed.

  Lemma run_to_termination_plain_to_run_tid_until tid init_memory fuel st
      ppst' :
    init_memory = initmem st →
    Exec.elem_of_results (ppst', true)
      (run_to_termination_plain isem prom term tid init_memory fuel
         (PState_PPState prom tid st)) →
    Exec.elem_of_results
      (set_PState_PPState tid ppst' st, true)
      (run_tid_until tid fuel st).
  Proof.
    intro Hinit.
    revert st ppst' Hinit.
    induction fuel as [|fuel IH]; intros st ppst' Hinit Hplain;
      cbn in Hplain |- *.
    - apply Exec.elem_of_bind_elim in Hplain
        as [pp_get [ts [Hget Hafter_get]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mGet.
      + rewrite terminated_tid_PState_PPState.
        destruct (term tid
          (tState_regs prom
            (PPState.state (PState_PPState prom tid st)))) eqn:Hterm.
        * change (Exec.elem_of_results (ppst', true)
            ((mret true :
                Exec.t (PPState.t tState mEvent iis) string bool)
               (PState_PPState prom tid st))) in Hafter_get.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get; subst ppst'.
          rewrite set_PState_PPState_get.
          apply Exec.elem_of_mret.
        * change (Exec.elem_of_results (ppst', true)
            ((mret false :
                Exec.t (PPState.t tState mEvent iis) string bool)
               (PState_PPState prom tid st))) in Hafter_get.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get.
    - apply Exec.elem_of_bind_elim in Hplain
        as [pp_get [ts [Hget Hafter_get]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mGet.
      + rewrite terminated_tid_PState_PPState.
        destruct (term tid
          (tState_regs prom
            (PPState.state (PState_PPState prom tid st)))) eqn:Hterm0.
        * change (Exec.elem_of_results (ppst', true)
             ((mret true :
                 Exec.t (PPState.t tState mEvent iis) string bool)
                (PState_PPState prom tid st))) in Hafter_get.
          unfold elem_of, Exec.elem_of_results in Hafter_get.
          cbn in Hafter_get.
          apply elem_of_list_singleton in Hafter_get.
          inversion Hafter_get; subst ppst'.
          rewrite set_PState_PPState_get.
          apply Exec.elem_of_mret.
        * apply Exec.elem_of_bind_elim in Hafter_get
             as [pp_step [u [Hstep Htail]]].
          destruct u.
          eapply Exec.elem_of_bind_intro
            with (st' := set_PState_PPState tid pp_step st)
                 (a := tt).
          -- eapply run_tid_from_plain_step.
             ++ exact Hinit.
             ++ exact Hstep.
          -- apply Exec.elem_of_bind_elim in Htail
               as [pp_get1 [ts1 [Hget1 Hafter_get1]]].
             apply Exec.elem_of_mget_inv in Hget1 as [-> ->].
             cbn in Hafter_get1.
             destruct
               (term tid (tState_regs prom (PPState.state pp_step)))
               eqn:Hterm1.
             ++ change (Exec.elem_of_results (ppst', true)
                  ((mret true :
                      Exec.t (PPState.t tState mEvent iis) string bool)
                     pp_step)) in Hafter_get1.
                unfold elem_of, Exec.elem_of_results in Hafter_get1.
                cbn in Hafter_get1.
                apply elem_of_list_singleton in Hafter_get1.
                inversion Hafter_get1; subst ppst'.
                apply run_tid_until_terminated_initial.
                rewrite terminated_tid_set_PState_PPState.
                exact Hterm1.
             ++ apply Exec.elem_of_bind_elim in Hafter_get1
                  as [pp_reset [u [Hreset Hrec]]].
                destruct u.
                unfold msetv in Hreset.
                apply Exec.elem_of_mset_inv in Hreset as ->.
                rewrite <-
                  (set_PState_PPState_overwrite tid ppst' pp_step st).
                eapply IH.
                ** rewrite set_PState_PPState_initmem.
                   exact Hinit.
                ** rewrite
                     (PState_PPState_set_PState_PPState_iis_init
                        tid pp_step st).
                   exact Hrec.
  Qed.

  Lemma run_outcome_with_promise_forget (tid : fin n) init_memory base out
      proms ppst proms' ppst' (eret : eff_ret out) :
    Exec.elem_of_results ((proms', ppst'), eret)
      (run_outcome_with_promise prom tid init_memory base out (proms, ppst)) →
    Exec.elem_of_results (ppst', eret)
      ((prom.(handle_outcome) n tid init_memory out |$> fst) ppst).
  Proof.
    unfold run_outcome_with_promise.
    intro Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [pair_mid [[res vpre_opt] [Hhandle Htail]]].
    apply Exec.elem_of_liftSt_inv in Hhandle
      as [pp_mid [Hpair_mid Hhandle]].
    subst pair_mid.
    cbn in Hhandle.
    destruct vpre_opt as [vpre|].
    - destruct (decide (vpre ≤ base)%nat).
      + apply Exec.elem_of_bind_elim in Htail
          as [pair_get [mem [Hget Hafter_get]]].
        apply Exec.elem_of_mget_inv in Hget as [-> ->].
        apply Exec.elem_of_bind_elim in Hafter_get
          as [pair_set [u [Hset Hret]]].
        destruct u.
        apply Exec.elem_of_mset_inv in Hset as ->.
        apply Exec.elem_of_mret_inv in Hret as [Heq_state ->].
        inversion Heq_state; subst ppst'.
        eapply (Exec.elem_of_fmap_intro ppst pp_mid (res, Some vpre)
          (prom.(handle_outcome) n tid init_memory out) fst).
        exact Hhandle.
      + apply Exec.elem_of_mret_inv in Htail as [Heq_state ->].
        inversion Heq_state; subst ppst'.
        eapply (Exec.elem_of_fmap_intro ppst pp_mid (res, Some vpre)
          (prom.(handle_outcome) n tid init_memory out) fst).
        exact Hhandle.
    - apply Exec.elem_of_mret_inv in Htail as [Heq_state ->].
      inversion Heq_state; subst ppst'.
      eapply (Exec.elem_of_fmap_intro ppst pp_mid (res, None)
        (prom.(handle_outcome) n tid init_memory out) fst).
      exact Hhandle.
  Qed.

  Lemma cinterp_run_outcome_with_promise_forget
      (tid : fin n) init_memory {A} base
      (mon : iMon A) proms ppst proms' ppst' ret :
    Exec.elem_of_results ((proms', ppst'), ret)
      (cinterp (run_outcome_with_promise prom tid init_memory base)
         mon (proms, ppst)) →
    Exec.elem_of_results (ppst', ret)
      (cinterp
         (λ out, prom.(handle_outcome) n tid init_memory out |$> fst)
         mon ppst).
  Proof.
    revert proms ppst proms' ppst' ret.
    induction mon as [ret0|call k IH];
      intros proms ppst proms' ppst' ret Hrun; cbn in Hrun |- *.
    - apply Exec.elem_of_mret_inv in Hrun as [Heq_state ->].
      inversion Heq_state; subst ppst'.
      apply Exec.elem_of_mret.
    - destruct call as [out|choice].
      + apply Exec.elem_of_bind_elim in Hrun
          as [pair_mid [eret [Hout Htail]]].
        destruct pair_mid as [proms_mid pp_mid].
        eapply Exec.elem_of_bind_intro.
        * eapply run_outcome_with_promise_forget.
          exact Hout.
        * eapply IH.
          exact Htail.
      + destruct choice as [choices].
        apply Exec.elem_of_bind_elim in Hrun
          as [pair_choose [choice_ret [Hchoose Htail]]].
        apply Exec.elem_of_mchoose_inv in Hchoose as ->.
        eapply Exec.elem_of_bind_intro.
        * apply Exec.elem_of_mchoose.
        * eapply IH.
          exact Htail.
  Qed.

  Lemma run_to_termination_forget (tid : fin n) init_memory fuel base
      proms ppst proms' ppst' b :
    Exec.elem_of_results ((proms', ppst'), b)
      (run_to_termination isem prom term tid init_memory fuel base
         (proms, ppst)) →
    Exec.elem_of_results (ppst', b)
      (run_to_termination_plain isem prom term tid init_memory fuel ppst).
  Proof.
    revert proms ppst proms' ppst' b.
    induction fuel as [|fuel IH];
      intros proms ppst proms' ppst' b Hrun; cbn in Hrun |- *.
    - apply Exec.elem_of_bind_elim in Hrun
        as [pair_get [ts [Hget Hafter_get]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      cbn in Hafter_get.
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + destruct (term tid (tState_regs prom (PPState.state ppst)))
          eqn:Hterm.
        * apply Exec.elem_of_mret_inv in Hafter_get
            as [Heq_state ->].
          inversion Heq_state; subst ppst'.
          apply Exec.elem_of_mret.
        * apply Exec.elem_of_mret_inv in Hafter_get
            as [Heq_state ->].
          inversion Heq_state; subst ppst'.
          apply Exec.elem_of_mret.
    - apply Exec.elem_of_bind_elim in Hrun
        as [pair_get [ts [Hget Hafter_get]]].
      apply Exec.elem_of_mget_inv in Hget as [-> ->].
      cbn in Hafter_get.
      eapply Exec.elem_of_bind_intro.
      + apply Exec.elem_of_mget.
      + destruct (term tid (tState_regs prom (PPState.state ppst)))
           eqn:Hterm0.
        * apply Exec.elem_of_mret_inv in Hafter_get
             as [Heq_state ->].
          inversion Heq_state; subst ppst'.
          apply Exec.elem_of_mret.
        * apply Exec.elem_of_bind_elim in Hafter_get
             as [pair_step [u [Hstep Htail]]].
          destruct u.
          destruct pair_step as [proms_step pp_step].
          eapply Exec.elem_of_bind_intro.
          -- eapply cinterp_run_outcome_with_promise_forget.
             exact Hstep.
          -- apply Exec.elem_of_bind_elim in Htail
               as [pair_get1 [ts1 [Hget1 Hafter_get1]]].
             apply Exec.elem_of_mget_inv in Hget1 as [-> ->].
             cbn in Hafter_get1.
             eapply Exec.elem_of_bind_intro.
             ++ apply Exec.elem_of_mget.
             ++ destruct
                  (term tid (tState_regs prom (PPState.state pp_step)))
                  eqn:Hterm1.
                ** apply Exec.elem_of_mret_inv in Hafter_get1
                     as [Heq_state ->].
                   inversion Heq_state; subst ppst'.
                   apply Exec.elem_of_mret.
                ** apply Exec.elem_of_bind_elim in Hafter_get1
                     as [pair_reset [u [Hreset Hrec]]].
                   destruct u.
                   apply Exec.elem_of_mset_inv in Hreset as ->.
                   eapply Exec.elem_of_bind_intro.
                   --- apply Exec.elem_of_mset.
                   --- eapply IH.
                       exact Hrec.
  Qed.

  Lemma enumerate_results_final_state_plain
      (tid : fin n) init_memory fuel ts mem ts' :
    ts' ∈ match enumerate_results isem prom term tid init_memory fuel ts mem with
          | {| final_states := final_states0 |} => final_states0
          end →
    ∃ ppst',
      PPState.state ppst' = ts' ∧
      PPState.mem ppst' = mem ∧
      Exec.elem_of_results (ppst', true)
        (run_to_termination_plain isem prom term tid init_memory fuel
           (PPState.Make ts mem prom.(iis_init))).
  Proof.
    intro Hin.
    unfold enumerate_results in Hin.
    set (ppst := PPState.Make ts mem (iis_init prom)) in *.
    set (res :=
      run_to_termination isem prom term tid init_memory fuel
        (length mem) ([], ppst)) in *.
    cbn in Hin.
    apply elem_of_list_omap in Hin
      as [[[new_proms ppst'] done] [Hsuccess Hstate]].
    destruct done; cbn in Hstate; [|discriminate].
    destruct new_proms as [|ev new_proms]; cbn in Hstate; [|discriminate].
    destruct (decide (PPState.mem ppst' = mem)) as [Hmem|Hmem].
    2: discriminate.
    inversion Hstate; subst ts'.
    exists ppst'.
    repeat split; try reflexivity.
    - exact Hmem.
    - subst res ppst.
      eapply run_to_termination_forget.
      exact Hsuccess.
  Qed.

  Lemma enumerate_results_final_state_run_tid_until
      (tid : fin n) init_memory fuel st ts mem ts' :
    init_memory = initmem st →
    ts = tstate tid st →
    mem = events st →
    ts' ∈ match enumerate_results isem prom term tid init_memory fuel ts mem with
          | {| final_states := final_states0 |} => final_states0
          end →
    ∃ st' b,
      tstate tid st' = ts' ∧
      events st' = events st ∧
      Exec.elem_of_results (st', b)
        (run_tid_until tid fuel st).
  Proof.
    intros Hinit Hts Hmem Hfinal.
    destruct
      (enumerate_results_final_state_plain
         tid init_memory fuel ts mem ts' Hfinal)
      as [ppst' [Hstate [Hmem_pp Hplain]]].
    exists (set_PState_PPState tid ppst' st), true.
    repeat split.
    - rewrite tstate_set_PState_PPState.
      exact Hstate.
    - rewrite events_set_PState_PPState.
      subst mem.
      exact Hmem_pp.
    - eapply run_to_termination_plain_to_run_tid_until.
      + exact Hinit.
      + subst ts mem.
        exact Hplain.
  Qed.

  Lemma run_tid_initmem (tid : fin n) st st' :
    Exec.elem_of_results (st', ()) (run_tid isem prom tid st) →
    initmem st' = initmem st.
  Proof.
    unfold run_tid.
    intro Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Hlift]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    apply Exec.elem_of_liftSt_inv in Hlift as [ppst' [-> _]].
    destruct st, ppst'.
    reflexivity.
  Qed.

  Lemma run_tid_other_tstate (tid tid_other : fin n) st st' :
    tid_other ≠ tid →
    Exec.elem_of_results (st', ()) (run_tid isem prom tid st) →
    tstate tid_other st' = tstate tid_other st.
  Proof.
    intros Hne Hrun.
    unfold run_tid in Hrun.
    apply Exec.elem_of_bind_elim in Hrun
      as [st_get [st_read [Hget Hlift]]].
    apply Exec.elem_of_mGet_inv in Hget as [-> ->].
    apply Exec.elem_of_liftSt_inv in Hlift as [ppst' [-> _]].
    apply tstate_set_PState_PPState_ne.
    exact Hne.
  Qed.

  Lemma run_tid_until_initmem (tid : fin n) fuel st st' b :
    Exec.elem_of_results (st', b) (run_tid_until tid fuel st) →
    initmem st' = initmem st.
  Proof.
    revert st st' b.
    induction fuel as [|fuel IH]; intros st st' b Hrun; cbn in Hrun.
    - apply Exec.elem_of_bind_elim in Hrun
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      destruct (terminated_tid prom term st tid);
        apply Exec.elem_of_mret_inv in Hafter_get as [-> _];
        reflexivity.
    - apply Exec.elem_of_bind_elim in Hrun
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      destruct (terminated_tid prom term st tid).
      + apply Exec.elem_of_mret_inv in Hafter_get as [-> _].
        reflexivity.
      + apply Exec.elem_of_bind_elim in Hafter_get
          as [st_step [u [Hrun_tid Htail]]].
        destruct u.
        rewrite (IH st_step st' b Htail).
        eapply run_tid_initmem.
        exact Hrun_tid.
  Qed.

  Lemma PState_eq_from_fields
      (target : vec tState n) init_memory
      (mem : PromMemory.t mEvent) st :
    initmem st = init_memory →
    events st = mem →
    (∀ tid : fin n, tstate tid st = target !!! tid) →
    st = {|tstates := target; initmem := init_memory; events := mem|}.
  Proof.
    destruct st as [tstates0 initmem0 events0].
    cbn.
    intros -> -> Htstates.
    f_equal.
    apply vec_eq.
    intro tid.
    specialize (Htstates tid).
    exact Htstates.
  Qed.

  Lemma run_tid_until_other_tstate
      (tid tid_other : fin n) fuel st st' b :
    tid_other ≠ tid →
    Exec.elem_of_results (st', b) (run_tid_until tid fuel st) →
    tstate tid_other st' = tstate tid_other st.
  Proof.
    revert st st' b.
    induction fuel as [|fuel IH]; intros st st' b Hne Hrun;
      cbn in Hrun.
    - apply Exec.elem_of_bind_elim in Hrun
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      destruct (terminated_tid prom term st tid);
        apply Exec.elem_of_mret_inv in Hafter_get as [-> _];
        reflexivity.
    - apply Exec.elem_of_bind_elim in Hrun
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      destruct (terminated_tid prom term st tid).
      + apply Exec.elem_of_mret_inv in Hafter_get as [-> _].
        reflexivity.
      + apply Exec.elem_of_bind_elim in Hafter_get
          as [st_step [u [Hrun_tid Htail]]].
        destruct u.
        rewrite (IH st_step st' b Hne Htail).
        eapply run_tid_other_tstate.
        * exact Hne.
        * exact Hrun_tid.
  Qed.

  Lemma run_tid_until_run_cont (tid : fin n) fuel st st' b st_fin f :
    Exec.elem_of_results (st', b) (run_tid_until tid fuel st) →
    (∀ min,
      ∃ fuel_direct,
        (min ≤ fuel_direct)%nat ∧
        Exec.elem_of_results (st_fin, f)
          (run isem prom term fuel_direct st')) →
    ∀ min,
      ∃ fuel_direct,
        (min ≤ fuel_direct)%nat ∧
        Exec.elem_of_results (st_fin, f)
          (run isem prom term fuel_direct st).
  Proof.
    revert st st' b.
    induction fuel as [|fuel IH]; intros st st' b Huntil Hcont min.
    - cbn in Huntil.
      apply Exec.elem_of_bind_elim in Huntil
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      destruct (terminated_tid prom term st tid);
        apply Exec.elem_of_mret_inv in Hafter_get as [-> ->];
        apply Hcont.
    - cbn in Huntil.
      apply Exec.elem_of_bind_elim in Huntil
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      destruct (terminated_tid prom term st tid) eqn:Hterm_tid.
      + apply Exec.elem_of_mret_inv in Hafter_get as [-> ->].
        apply Hcont.
      + apply Exec.elem_of_bind_elim in Hafter_get
          as [st_step [u [Hrun_tid Htail]]].
        destruct u.
        destruct (IH st_step st' b Htail Hcont min)
          as [fuel_tail [Hmin Hrun_tail]].
        exists (S fuel_tail).
        split; [lia|].
        eapply run_step_run_intro.
        * eapply terminated_not_from_tid_false.
          exact Hterm_tid.
        * eapply run_step_tid_intro.
          -- exact Hterm_tid.
          -- exact Hrun_tid.
        * exact Hrun_tail.
  Qed.

  Lemma run_final_states_list_cont fuel init_memory mem
      (orig target : vec tState n) tids st st_fin f :
    NoDup tids →
    initmem st = init_memory →
    events st = mem →
    (∀ tid : fin n, tid ∈ tids → tstate tid st = orig !!! tid) →
    (∀ tid : fin n, tid ∉ tids → tstate tid st = target !!! tid) →
    (∀ tid : fin n,
      target !!! tid ∈
        match enumerate_results isem prom term tid init_memory fuel
                (orig !!! tid) mem with
        | {| final_states := final_states0 |} => final_states0
        end) →
    (∀ st_done,
      initmem st_done = init_memory →
      events st_done = mem →
      (∀ tid : fin n, tstate tid st_done = target !!! tid) →
      ∀ min,
        ∃ fuel_direct,
          (min ≤ fuel_direct)%nat ∧
          Exec.elem_of_results (st_fin, f)
            (run isem prom term fuel_direct st_done)) →
    ∀ min,
      ∃ fuel_direct,
        (min ≤ fuel_direct)%nat ∧
        Exec.elem_of_results (st_fin, f)
          (run isem prom term fuel_direct st).
  Proof.
    revert st.
    induction tids as [|tid tids IH];
      intros st Hnodup Hinit Hevents Horig Hdone Hfinal Hcont min.
    - apply Hcont.
      + exact Hinit.
      + exact Hevents.
      + intros tid.
        apply Hdone.
        set_solver.
    - rewrite NoDup_cons in Hnodup.
      destruct Hnodup as [Hnotin Hnodup_tail].
      destruct
        (enumerate_results_final_state_run_tid_until
           tid init_memory fuel st (orig !!! tid) mem (target !!! tid))
        as [st1 [b [Htid_state [Hevents1 Hrun_until]]]].
      + symmetry.
        exact Hinit.
      + symmetry.
        apply Horig.
        set_solver.
      + symmetry.
        exact Hevents.
      + apply Hfinal.
      + eapply run_tid_until_run_cont.
        * exact Hrun_until.
        * intros min_tail.
          eapply IH.
          -- exact Hnodup_tail.
          -- transitivity (initmem st).
             ++ eapply run_tid_until_initmem.
                exact Hrun_until.
             ++ exact Hinit.
          -- rewrite Hevents1.
             exact Hevents.
          -- intros tid_other Hin_tail.
             assert (Hne : tid_other ≠ tid).
             {
               intro Heq.
               subst tid_other.
               contradiction.
             }
             rewrite
               (run_tid_until_other_tstate
                  tid tid_other fuel st st1 b Hne Hrun_until).
             apply Horig.
             set_solver.
          -- intros tid_other Hnot_tail.
             destruct (decide (tid_other = tid)) as [->|Hne].
             ++ exact Htid_state.
             ++ rewrite
                  (run_tid_until_other_tstate
                     tid tid_other fuel st st1 b Hne Hrun_until).
                apply Hdone.
                set_solver.
          -- exact Hfinal.
          -- exact Hcont.
  Qed.

  Lemma run_promise_first_final_to_run_exists fuel st st_fin f :
    filter_promises_mono_property prom →
    Exec.elem_of_results (st_fin, f)
      (run_promise_first isem prom term fuel st) →
    ∀ min,
      ∃ fuel_direct st_direct,
        (min ≤ fuel_direct)%nat ∧
        Exec.elem_of_results (st_direct, f)
          (run isem prom term fuel_direct st).
  Proof.
    revert st st_fin f.
    induction fuel as [|fuel IH];
      intros st st_fin f Hfilter_mono Hpf min.
    - cbn in Hpf.
      unfold mthrow, Exec.throw_inst in Hpf.
      cbn in Hpf.
      inversion Hpf.
    - cbn in Hpf.
      apply Exec.elem_of_bind_elim in Hpf
        as [st_get [st_read [Hget Hafter_get]]].
      apply Exec.elem_of_mGet_inv in Hget as [-> ->].
      apply Exec.elem_of_bind_elim in Hafter_get
        as [st_opt [opt [Hopt Hbranch]]].
      change
        (Exec.elem_of_results (st_opt, opt)
           ((mchoosel (seq 0 4) : Exec.t t string nat) st)) in Hopt.
      apply Exec.elem_of_mchoosel_inv in Hopt as [-> Hopt_in].
      destruct opt as [|[|[|opt]]]; cbn in Hbranch.
      + apply Exec.elem_of_bind_elim in Hbranch
          as [st_tid [tid [Htid Hafter_tid]]].
        unfold mchoosef in Htid.
        apply Exec.elem_of_mchoosel_inv in Htid as [-> _].
        destruct (terminated_tid prom term st tid) eqn:Hterm_tid.
        * unfold mdiscard, mchoose, Exec.choose_inst,
            fmap, Exec.fmap_inst, Exec.res_fmap_inst in Hafter_tid.
          cbn in Hafter_tid.
          inversion Hafter_tid.
        * apply Exec.elem_of_bind_elim in Hafter_tid
            as [st_ev [ev [Hev Hafter_ev]]].
          apply Exec.elem_of_lift_res_inv in Hev as [-> Hev].
          apply Exec.elem_of_bind_elim in Hafter_ev
            as [st_set [u [Hset Htail]]].
          destruct u.
          apply Exec.elem_of_mSet_inv in Hset as ->.
          destruct (IH _ _ _ Hfilter_mono Htail (Nat.max min fuel))
            as [fuel_tail [st_direct [Hmin_tail Hrun_tail]]].
          exists (S fuel_tail), st_direct.
          split; [lia|].
          eapply run_step_run_intro.
          -- eapply terminated_not_from_tid_false.
             exact Hterm_tid.
          -- eapply (@run_step_promise_intro
               isem prom n term (S fuel_tail) st tid ev).
             ++ exact Hterm_tid.
             ++ eapply (@promise_select_tid_fuel_mono
                  isem prom n term Hfilter_mono
                  fuel (S fuel_tail) st tid ev).
                ** lia.
                ** exact Hev.
          -- exact Hrun_tail.
      + apply Exec.elem_of_bind_elim in Hbranch
          as [st_targets [target [Htarget Hafter_target]]].
        apply Exec.elem_of_mchoosel_inv in Htarget
          as [-> Htarget_in].
        set (st_target := Make target (initmem st) (events st)) in *.
        apply Exec.elem_of_bind_elim in Hafter_target
          as [st_guard [Hterm [Hguard Hafter_guard]]].
        apply Exec.elem_of_guard_discard_inv in Hguard as ->.
        apply Exec.elem_of_bind_elim in Hafter_guard
          as [st_valid [u [Hvalid Hret]]].
        destruct u.
        apply validate_final_inv_at in Hvalid as [-> [Hnoprom Hcheck]].
        apply Exec.elem_of_mret_inv in Hret as [-> ->].
        assert (Hdirect :
          ∀ min0,
            ∃ fuel_direct,
              (min0 ≤ fuel_direct)%nat ∧
              Exec.elem_of_results
                (st_target, make_final prom term st_target Hterm)
                (run isem prom term fuel_direct st)).
        {
          eapply run_final_states_list_cont
            with (fuel:=fuel) (init_memory:=initmem st) (mem:=events st)
                 (orig:=tstates st) (target:=target)
                 (tids:=fin_enum n).
          - apply Exec.NoDup_fin_enum.
          - reflexivity.
          - reflexivity.
          - intros tid _.
            reflexivity.
          - intros tid Hnotin.
            exfalso.
            apply Hnotin.
            apply Exec.elem_of_fin_enum.
          - intros tid.
            rewrite cprodn_spec in Htarget_in.
            specialize (Htarget_in tid).
            autorewrite with vec in Htarget_in.
            exact Htarget_in.
          - intros st_done Hinit_done Hevents_done Htstates_done min_done.
            assert (Hst_done : st_done = st_target).
            {
              subst st_target.
              eapply PState_eq_from_fields.
              + exact Hinit_done.
              + exact Hevents_done.
              + exact Htstates_done.
            }
            subst st_done.
            exists min_done.
            split; [lia|].
            eapply run_current_final.
            + exact Hnoprom.
            + exact Hcheck.
        }
        destruct (Hdirect min) as [fuel_direct [Hmin_direct Hrun_direct]].
        exists fuel_direct, st_target.
        split; [exact Hmin_direct|exact Hrun_direct].
      + apply Exec.elem_of_bind_elim in Hbranch
          as [st_err [err [Herr Hthrow]]].
        unfold mthrow, Exec.throw_inst in Hthrow.
        cbn in Hthrow.
        inversion Hthrow.
      + destruct
          (bool_decide
            (∃ x ∈ map (out_of_fuel prom)
                  (vmap
                     (λ '(tid, ts),
                        enumerate_results isem prom term tid (initmem st)
                          fuel ts (events st)) (venumerate (tstates st))),
              (x : bool))).
        * unfold mthrow, Exec.throw_inst in Hbranch.
          cbn in Hbranch.
          inversion Hbranch.
        * unfold mdiscard, mchoose, Exec.choose_inst,
            fmap, Exec.fmap_inst, Exec.res_fmap_inst in Hbranch.
          cbn in Hbranch.
          inversion Hbranch.
  Qed.

  End RunPfToDirect.
End CPStateProof.

Lemma Promising_to_Modelc_from_exec_final_inv {St : Type} {n : nat}
    {term : terminationCondition n}
    (e : Exec.t St string {s & archState.is_terminated term s})
    st fs pt :
  archModel.Res.FinalState fs pt ∈ archModel.Res.from_exec e st →
  ∃ st' fsig,
    Exec.elem_of_results (st', fsig) (e st) ∧
    projT1 fsig = fs.
Proof.
  unfold archModel.Res.from_exec.
  unfold elem_of, listset_elem_of.
  cbn.
  intro Hin.
  rewrite elem_of_list_fmap in Hin.
  destruct Hin as [res [Hres Hin]].
  destruct res as [fsig|err].
  - rewrite elem_of_list_fmap in Hin.
    destruct Hin as [[st' res] [Hres_snd Hin]].
    cbn in Hres_snd.
    subst res.
    unfold Exec.to_stateful_result_list in Hin.
    destruct (e st) as [rs es] eqn:Heq.
    cbn in Hin.
    apply elem_of_app in Hin as [Hin|Hin].
    + rewrite elem_of_list_fmap in Hin.
      destruct Hin as [[st0 fsig0] [Heq_pair Hin]].
      inversion Heq_pair; subst st0 fsig0.
      exists st', fsig.
      split.
      * unfold elem_of, Exec.elem_of_results.
        exact Hin.
      * destruct fsig as [fs0 pt0].
        cbn in Hres |- *.
        inversion Hres.
        reflexivity.
    + rewrite elem_of_list_fmap in Hin.
      destruct Hin as [[st_err err0] [Heq_pair _]].
      inversion Heq_pair.
  - cbn in Hres.
    inversion Hres.
Qed.

Lemma Promising_to_Modelc_from_exec_final_intro {St : Type} {n : nat}
    {term : terminationCondition n}
    (e : Exec.t St string {s & archState.is_terminated term s})
    st st' fs pt :
  Exec.elem_of_results
    (st', existT (P:=archState.is_terminated term) fs pt) (e st) →
  archModel.Res.FinalState fs pt ∈ archModel.Res.from_exec e st.
Proof.
  unfold archModel.Res.from_exec.
  unfold elem_of, listset_elem_of.
  cbn.
  intro Hrun.
  rewrite elem_of_list_fmap.
  exists (Ok (existT (P:=archState.is_terminated term) fs pt)).
  split; [reflexivity|].
  rewrite elem_of_list_fmap.
  exists (st', Ok (existT (P:=archState.is_terminated term) fs pt)).
  split; [reflexivity|].
  unfold Exec.to_stateful_result_list.
  destruct (e st) as [rs es] eqn:Heq.
  cbn.
  apply elem_of_app.
  left.
  rewrite elem_of_list_fmap.
  exists (st', existT (P:=archState.is_terminated term) fs pt).
  split; [reflexivity|].
  unfold elem_of, Exec.elem_of_results in Hrun.
  exact Hrun.
Qed.

Lemma Promising_to_Modelc_final_to_pf_with_run_tid_pf_tail_lift
    (prom : Promising.Model) (isem : iMon ()) fuel fuel_pf
    {n} (term : terminationCondition n) initMs fs pt :
  CPStateProof.filter_promises_mono_property prom →
  CPStateProof.run_tid_pf_tail_lift_property isem prom term →
  (S fuel ≤ fuel_pf)%nat →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc prom isem fuel n term initMs →
  ∃ pt_pf,
    archModel.Res.FinalState fs pt_pf ∈
      Promising_to_Modelc_pf prom isem fuel_pf n term initMs.
Proof.
  intros Hfilter_mono Hlift Hfuel Hdirect.
  unfold Promising_to_Modelc, Promising_to_Modelc_pf in *.
  set (initPs := PState.from_archState prom initMs) in *.
  apply Promising_to_Modelc_from_exec_final_inv in Hdirect
    as [st_fin [fsig [Hrun_map Hfs]]].
  apply Exec.elem_of_fmap_inv in Hrun_map
    as [f [Hfsig Hrun]].
  subst fsig.
  pose proof
    (CPStateProof.run_final_to_pf_with_run_tid_pf_tail_lift
       isem prom term fuel fuel_pf initPs st_fin f
       Hfilter_mono Hlift Hfuel Hrun) as Hpf.
  destruct (CPState.to_final_archState f)
    as [fs_pf pt_pf] eqn:Hto.
  cbn in Hfs.
  subst fs_pf.
  exists pt_pf.
  eapply Promising_to_Modelc_from_exec_final_intro.
  rewrite <- Hto.
  apply Exec.elem_of_fmap_intro.
  exact Hpf.
Qed.

Lemma Promising_to_Modelc_pf_final_to_direct_exists
    (prom : Promising.Model) (isem : iMon ()) fuel_pf
    {n} (term : terminationCondition n) initMs fs pt :
  CPStateProof.filter_promises_mono_property prom →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc_pf prom isem fuel_pf n term initMs →
  ∀ min,
    ∃ fuel_direct pt_direct,
      (min ≤ fuel_direct)%nat ∧
      archModel.Res.FinalState fs pt_direct ∈
        Promising_to_Modelc prom isem fuel_direct n term initMs.
Proof.
  intros Hfilter_mono Hpf min.
  unfold Promising_to_Modelc, Promising_to_Modelc_pf in *.
  set (initPs := PState.from_archState prom initMs) in *.
  apply Promising_to_Modelc_from_exec_final_inv in Hpf
    as [st_pf [fsig [Hrun_map Hfs]]].
  apply Exec.elem_of_fmap_inv in Hrun_map
    as [f [Hfsig Hrun_pf]].
  subst fsig.
  destruct
    (CPStateProof.run_promise_first_final_to_run_exists
       isem prom term fuel_pf initPs st_pf f
       Hfilter_mono Hrun_pf min)
    as [fuel_direct [st_direct [Hmin Hrun_direct]]].
  destruct (CPState.to_final_archState f)
    as [fs_direct pt_direct] eqn:Hto.
  cbn in Hfs.
  subst fs_direct.
  exists fuel_direct, pt_direct.
  split; [exact Hmin|].
  eapply Promising_to_Modelc_from_exec_final_intro.
  rewrite <- Hto.
  apply Exec.elem_of_fmap_intro.
  exact Hrun_direct.
Qed.

Lemma Promising_to_Modelc_final_to_pf_exists_with_run_tid_pf_tail_lift
    (prom : Promising.Model) (isem : iMon ()) fuel
    {n} (term : terminationCondition n) initMs fs pt :
  CPStateProof.filter_promises_mono_property prom →
  CPStateProof.run_tid_pf_tail_lift_exists_property isem prom term →
  archModel.Res.FinalState fs pt ∈
    Promising_to_Modelc prom isem fuel n term initMs →
  ∃ fuel_pf pt_pf,
    archModel.Res.FinalState fs pt_pf ∈
      Promising_to_Modelc_pf prom isem fuel_pf n term initMs.
Proof.
  intros Hfilter_mono Hlift Hdirect.
  destruct
    (Promising_to_Modelc_final_to_pf_with_run_tid_pf_tail_lift
       prom isem fuel (S fuel) term initMs fs pt
       Hfilter_mono Hlift (Nat.le_refl _) Hdirect)
    as [pt_pf Hpf].
  exists (S fuel), pt_pf.
  exact Hpf.
Qed.

Lemma Promising_to_Modelc_pf_final_equiv_with_run_tid_pf_tail_lift
    (prom : Promising.Model) (isem : iMon ()) fuel fuel_pf
    {n} (term : terminationCondition n) initMs fs pt :
  CPStateProof.filter_promises_mono_property prom →
  CPStateProof.run_tid_pf_tail_lift_property isem prom term →
  (S fuel ≤ fuel_pf)%nat →
  (archModel.Res.FinalState fs pt ∈
     Promising_to_Modelc prom isem fuel n term initMs →
   ∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       Promising_to_Modelc_pf prom isem fuel_pf n term initMs) ∧
  (archModel.Res.FinalState fs pt ∈
     Promising_to_Modelc_pf prom isem fuel_pf n term initMs →
   ∃ fuel_direct pt_direct,
     (fuel ≤ fuel_direct)%nat ∧
     archModel.Res.FinalState fs pt_direct ∈
       Promising_to_Modelc prom isem fuel_direct n term initMs).
Proof.
  intros Hfilter_mono Hlift Hfuel.
  split.
  - intro Hdirect.
    eapply Promising_to_Modelc_final_to_pf_with_run_tid_pf_tail_lift;
      eauto.
  - intro Hpf.
    eapply Promising_to_Modelc_pf_final_to_direct_exists.
    + exact Hfilter_mono.
    + exact Hpf.
Qed.

Lemma Promising_to_Modelc_pf_final_state_equiv_with_run_tid_pf_tail_lift
    (prom : Promising.Model) (isem : iMon ()) fuel fuel_pf
    {n} (term : terminationCondition n) initMs fs :
  CPStateProof.filter_promises_mono_property prom →
  CPStateProof.run_tid_pf_tail_lift_property isem prom term →
  (S fuel ≤ fuel_pf)%nat →
  ((∃ pt,
     archModel.Res.FinalState fs pt ∈
       Promising_to_Modelc prom isem fuel n term initMs) →
   ∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       Promising_to_Modelc_pf prom isem fuel_pf n term initMs) ∧
  ((∃ pt_pf,
     archModel.Res.FinalState fs pt_pf ∈
       Promising_to_Modelc_pf prom isem fuel_pf n term initMs) →
   ∃ fuel_direct pt_direct,
     (fuel ≤ fuel_direct)%nat ∧
     archModel.Res.FinalState fs pt_direct ∈
       Promising_to_Modelc prom isem fuel_direct n term initMs).
Proof.
  intros Hfilter_mono Hlift Hfuel.
  split.
  - intros [pt Hdirect].
    eapply Promising_to_Modelc_final_to_pf_with_run_tid_pf_tail_lift;
      eauto.
  - intros [pt_pf Hpf].
    eapply Promising_to_Modelc_pf_final_to_direct_exists.
    + exact Hfilter_mono.
    + exact Hpf.
Qed.

Lemma Promising_to_Modelc_pf_final_state_equiv_unbounded_with_run_tid_pf_tail_lift
    (prom : Promising.Model) (isem : iMon ())
    {n} (term : terminationCondition n) initMs fs :
  CPStateProof.filter_promises_mono_property prom →
  CPStateProof.run_tid_pf_tail_lift_property isem prom term →
  (∃ fuel pt,
     archModel.Res.FinalState fs pt ∈
       Promising_to_Modelc prom isem fuel n term initMs) ↔
  (∃ fuel pt,
     archModel.Res.FinalState fs pt ∈
       Promising_to_Modelc_pf prom isem fuel n term initMs).
Proof.
  intros Hfilter_mono Hlift.
  split.
  - intros [fuel [pt Hdirect]].
    destruct
      (Promising_to_Modelc_final_to_pf_exists_with_run_tid_pf_tail_lift
         prom isem fuel term initMs fs pt Hfilter_mono Hlift Hdirect)
      as [fuel_pf [pt_pf Hpf]].
    exists fuel_pf, pt_pf.
    exact Hpf.
  - intros [fuel_pf [pt_pf Hpf]].
    destruct
      (Promising_to_Modelc_pf_final_to_direct_exists
         prom isem fuel_pf term initMs fs pt_pf
         Hfilter_mono Hpf 0)
      as [fuel_direct [pt_direct [_ Hdirect]]].
    exists fuel_direct, pt_direct.
    exact Hdirect.
Qed.

Lemma Promising_to_Modelc_pf_final_state_equiv_unbounded_with_run_tid_pf_tail_lift_exists
    (prom : Promising.Model) (isem : iMon ())
    {n} (term : terminationCondition n) initMs fs :
  CPStateProof.filter_promises_mono_property prom →
  CPStateProof.run_tid_pf_tail_lift_exists_property isem prom term →
  (∃ fuel pt,
     archModel.Res.FinalState fs pt ∈
       Promising_to_Modelc prom isem fuel n term initMs) ↔
  (∃ fuel pt,
     archModel.Res.FinalState fs pt ∈
       Promising_to_Modelc_pf prom isem fuel n term initMs).
Proof.
  apply Promising_to_Modelc_pf_final_state_equiv_unbounded_with_run_tid_pf_tail_lift.
Qed.

Lemma Promising_to_Modelc_pf_final_state_equiv_unbounded_from_event_shape_replay
    (prom : Promising.Model) (isem : iMon ())
    {n} (term : terminationCondition n) initMs fs :
  PromisingProof.Replayable prom →
  CPStateProof.filter_promises_mono_property prom →
  CPStateProof.run_tid_pf_tail_lift_exists_property isem prom term →
  CPStateProof.run_tid_pf_tail_event_shape_replay_property isem prom term →
  (∃ fuel pt,
     archModel.Res.FinalState fs pt ∈
       Promising_to_Modelc prom isem fuel n term initMs) ↔
  (∃ fuel pt,
     archModel.Res.FinalState fs pt ∈
      Promising_to_Modelc_pf prom isem fuel n term initMs).
Proof.
  intros _ Hfilter_mono Hlift _.
  eapply
    Promising_to_Modelc_pf_final_state_equiv_unbounded_with_run_tid_pf_tail_lift_exists.
  - exact Hfilter_mono.
  - exact Hlift.
Qed.
