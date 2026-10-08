(*
 * SPDX-FileCopyrightText: Copyright (c) 2026 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 * SPDX-License-Identifier: Apache-2.0
 *
 * LSE fence-redundancy, proved against ArchSem's REAL Arm axiomatic model.
 * ---------------------------------------------------------------------------
 * This is the "blessable" form of the argument: instead of defining the ob
 * fragment ourselves, it proves the theorems against ArchSem's actual
 * user-mode Arm model (rems-project/archsem, ArchSemArm/UMArm.v) -- its real
 * [obs]/[dob]/[aob]/[bob]/[ob] Definitions.
 *
 * ArchSem's UMArm.v tracks the ESOP'22 model, which LACKS one bob clause that
 * the current Arm model has:
 *     herd aarch64hwreqs.cat:135
 *       [range([Exp&R&A]; amo; [Exp&W&L])]; po; [Exp&M | ...]
 * This clause -- "an acquire-release LSE atomic acts as a full barrier" -- has
 * been in bob since 2018 (Luc Maranget, herd a6c15616, po;([A];amo;[L]);po) and
 * was strengthened to this forward-edge form in 2022 (Alglave, PR #322 636b7163);
 * it post-dates the Jan-2018 Pulte et al. model AxSL formalises and is absent
 * from the ESOP'22 model UMArm tracks (both lack it).
 * We add exactly this clause to [UMArm.bob] (and, to keep the UM/VMSA
 * equivalence proof, to [VMSA22Arm.bob]; see the accompanying patch), bringing
 * the model up to the current cat, and then prove:
 *
 *   - LSE (acquire-release AMO -- an "-al" mnemonic: swpal / casal / ldaddal /
 *     ldclral / ldsetal / ldeoral; a plain swp or acquire-only swpa is NOT
 *     covered, since clause 135 needs [A];amo;[L]): the leading and trailing DMB
 *     fences add no ob edge the AMO does not already add -- redundant.  The lemma
 *     is over an abstract acquire-release AMO, so it is one proof for all six
 *     -al forms (OCaml's runtime uses the first three, OxCaml all six).
 *   - LL/SC (ldaxr/stlxr): the store-exclusive release write is NOT in
 *     range([A];amo;[L]) (it is lxsx, not amo), so clause 135 cannot fire for
 *     it and the trailing fence is load-bearing.
 *
 * Trust: ArchSem's model + Rocq's kernel, plus that the one added [bob] clause
 * equals herd aarch64hwreqs.cat:135 (a one-line, auditable delta).  No axioms.
 *
 * Build: needs the ArchSem libraries; apply archsem-lse-full-barrier.patch, drop
 * this file into archsem/ArchSemArm/ and `dune build` (NOT checked by ../../run.sh,
 * which runs plain coqc on the self-contained ../ob_subsumption.v).  See the
 * README.md in this directory for step-by-step reproduction.
 *)

From ASCommon Require Import Options.
From ASCommon Require Import Common GRel.
Require Import ArmInst.
Require Import GenAxiomaticArm.
Require Import UMArm.

(* ArchSem's dune sets a restrictive [Default Proof Using]; keep all section
   variables so these small proofs need no explicit [Proof using] clauses. *)
Set Default Proof Using "All".

Section ObArchSem.
  Import Candidate.
  Import AxArmNames.
  Context {nmth : nat}.
  Context (cd : Candidate.t NMS nmth).

  (* Same notations as UMArm.v for the tags/relations we use. *)
  Notation pe   := (pre_exec cd).
  Notation M    := (mem_explicit pe).
  Notation A    := (rel_acq_rcsc_reads pe).
  Notation Q    := (rel_acq_rcpc_reads pe).
  Notation L    := (rel_acq_rcsc_writes pe).
  Notation po   := (po cd).
  Notation amo  := (atomic_update cd).

  (* ----- membership builder for a "[s1]; po; [s2]" clause ----- *)
  Lemma seq_po_set (s1 s2 : gset EID.t) (x y : EID.t) :
    x ∈ s1 -> (x, y) ∈ po -> y ∈ s2 -> (x, y) ∈ (⦗s1⦘ ⨾ po ⨾ ⦗s2⦘).
  Proof.
    intros Hs1 Hpo Hs2.
    apply grel_seq_spec. exists y. split.
    - apply grel_seq_spec. exists x. split.
      + apply grel_from_set_spec. split; [exact Hs1 | reflexivity].
      + exact Hpo.
    - apply grel_from_set_spec. split; [exact Hs2 | reflexivity].
  Qed.

  (* bob membership implies ob membership. *)
  Lemma bob_in_ob (x y : EID.t) :
    (x, y) ∈ UMArm.bob cd -> (x, y) ∈ UMArm.ob cd.
  Proof.
    intro H. unfold UMArm.ob. apply grel_plus_once.
    unfold UMArm.ob1. set_solver.
  Qed.

  (* =================== the three current-cat clauses, as theorems =================== *)

  (* clause 135 (the one we added to UMArm.bob):
     the acquire-release AMO write orders any po-later access. *)
  Lemma clause135_ob (w m : EID.t) :
    w ∈ grel_rng (⦗A⦘ ⨾ amo ⨾ ⦗L⦘) -> (w, m) ∈ po -> m ∈ M ->
    (w, m) ∈ UMArm.ob cd.
  Proof.
    intros Hw Hpo Hm. apply bob_in_ob. unfold UMArm.bob.
    assert (Hseq : (w, m) ∈ (⦗grel_rng (⦗A⦘ ⨾ amo ⨾ ⦗L⦘)⦘ ⨾ po ⨾ ⦗M⦘))
      by (apply seq_po_set; assumption).
    set_solver.
  Qed.

  (* clause 137 (real UMArm.bob line 184):  [A|Q]; po; [M]. *)
  Lemma clause137_ob (a m : EID.t) :
    a ∈ A -> (a, m) ∈ po -> m ∈ M -> (a, m) ∈ UMArm.ob cd.
  Proof.
    intros Ha Hpo Hm. apply bob_in_ob. unfold UMArm.bob.
    assert (Hseq : (a, m) ∈ (⦗A ∪ Q⦘ ⨾ po ⨾ ⦗M⦘))
      by (apply seq_po_set; [ set_solver | assumption | assumption ]).
    set_solver.
  Qed.

  (* clause 138 (real UMArm.bob line 185):  [M]; po; [L]. *)
  Lemma clause138_ob (e l : EID.t) :
    e ∈ M -> (e, l) ∈ po -> l ∈ L -> (e, l) ∈ UMArm.ob cd.
  Proof.
    intros He Hpo Hl. apply bob_in_ob. unfold UMArm.bob.
    assert (Hseq : (e, l) ∈ (⦗M⦘ ⨾ po ⨾ ⦗L⦘))
      by (apply seq_po_set; assumption).
    set_solver.
  Qed.

  (* =================== LSE: leading/trailing DMB fences are redundant =================== *)
  Section LSE.
    Variables Ra Wl : EID.t.
    Hypothesis Ra_A      : Ra ∈ A.
    Hypothesis Wl_L      : Wl ∈ L.
    Hypothesis Ra_amo_Wl : (Ra, Wl) ∈ amo.

    (* the amo write is in range([A];amo;[L]), so clause 135 can fire on it. *)
    Lemma Wl_amo_write : Wl ∈ grel_rng (⦗A⦘ ⨾ amo ⨾ ⦗L⦘).
    Proof.
      apply (elem_of_map_2 snd (⦗A⦘ ⨾ amo ⨾ ⦗L⦘) (Ra, Wl)).
      apply grel_seq_spec. exists Wl. split.
      - apply grel_seq_spec. exists Ra. split.
        + apply grel_from_set_spec. split; [exact Ra_A | reflexivity].
        + exact Ra_amo_Wl.
      - apply grel_from_set_spec. split; [exact Wl_L | reflexivity].
    Qed.

    Variables e_pre e_post : EID.t.
    Hypothesis e_pre_M      : e_pre ∈ M.
    Hypothesis e_post_M     : e_post ∈ M.
    Hypothesis po_e_pre_Wl  : (e_pre, Wl) ∈ po.
    Hypothesis po_Ra_e_post : (Ra, e_post) ∈ po.
    Hypothesis po_Wl_e_post : (Wl, e_post) ∈ po.

    (* trailing DMB edges: *)
    Theorem trailing_Ra_epost : (Ra, e_post) ∈ UMArm.ob cd.   (* clause 137 *)
    Proof. apply clause137_ob; assumption. Qed.

    Theorem trailing_Wl_epost : (Wl, e_post) ∈ UMArm.ob cd.   (* clause 135 *)
    Proof. apply clause135_ob; [ apply Wl_amo_write | exact po_Wl_e_post | exact e_post_M ]. Qed.

    Theorem trailing_epre_epost : (e_pre, e_post) ∈ UMArm.ob cd.  (* 138 then 135 *)
    Proof.
      apply grel_plus_trans with (y := Wl).
      - apply clause138_ob; [ exact e_pre_M | exact po_e_pre_Wl | exact Wl_L ].
      - apply clause135_ob; [ apply Wl_amo_write | exact po_Wl_e_post | exact e_post_M ].
    Qed.

    (* leading DMB edges, for a po-earlier read r: *)
    Variable r : EID.t.
    Hypothesis r_M     : r ∈ M.
    Hypothesis po_r_Wl : (r, Wl) ∈ po.

    Theorem leading_r_Wl : (r, Wl) ∈ UMArm.ob cd.   (* clause 138 *)
    Proof. apply clause138_ob; [ exact r_M | exact po_r_Wl | exact Wl_L ]. Qed.

    Theorem leading_r_epost : (r, e_post) ∈ UMArm.ob cd.
    Proof.
      apply grel_plus_trans with (y := Wl).
      - apply leading_r_Wl.
      - apply clause135_ob; [ apply Wl_amo_write | exact po_Wl_e_post | exact e_post_M ].
    Qed.
  End LSE.

  (* ============ LL/SC: clause 135 cannot fire, trailing fence load-bearing ============ *)
  Section LLSC.
    Variable Wl : EID.t.
    Hypothesis Wl_not_amo_tgt : forall x, (x, Wl) ∉ amo.

    Theorem llsc_not_amo_release_write : Wl ∉ grel_rng (⦗A⦘ ⨾ amo ⨾ ⦗L⦘).
    Proof.
      intro H.
      apply elem_of_map_1 in H as [[a w] [Heq Hin]]. cbn in Heq. subst w.
      apply grel_seq_spec in Hin as [z [Hin Hz]].
      apply grel_from_set_spec in Hz as [_ Hz]. subst z.
      apply grel_seq_spec in Hin as [w [_ Hamo]].
      exact (Wl_not_amo_tgt w Hamo).
    Qed.

    Corollary llsc_no_clause135_edge (m : EID.t) :
      ~ (Wl, m) ∈ (⦗grel_rng (⦗A⦘ ⨾ amo ⨾ ⦗L⦘)⦘ ⨾ po ⨾ ⦗M⦘).
    Proof.
      intro Hbob.
      apply grel_seq_spec in Hbob as [z [Hin _]].
      apply grel_seq_spec in Hin as [w [Hw _]].
      apply grel_from_set_spec in Hw as [Hw Heq]. subst w.
      exact (llsc_not_amo_release_write Hw).
    Qed.
  End LLSC.

End ObArchSem.

(* Everything is derived from ArchSem's model + the one added bob clause
   (= herd aarch64hwreqs.cat:135); the checks below must report "Closed under
   the global context" (no axioms, no Admitted). *)
Print Assumptions trailing_epre_epost.
Print Assumptions leading_r_epost.
Print Assumptions llsc_not_amo_release_write.
