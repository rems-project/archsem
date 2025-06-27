(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Zonguyan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  All files except SailArmInstTypes.v are distributed under the             *)
(*  license below (BSD-2-Clause). The former is distributed                   *)
(*  under a mix of BSD-2-Clause and BSD-3-Clause Clear, as described          *)
(*  in the file header.                                                       *)
(*                                                                            *)
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

Require Import Strings.String.
Require Import stdpp.bitvector.bitvector.
Require Import stdpp.strings.
Require Import stdpp.base.
Require Import stdpp.countable.
Require Import stdpp.vector.
Require Import ASCommon.Options.
Require Import SailStdpp.Base.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Export SailRiscVInstTypes.
Require Import Coq.Reals.Rbase.
From RecordUpdate Require Import RecordSet.
From ASCommon Require Import Common Effects CDestruct.
From ArchSem Require Import Interface TermModels CandidateExecutions GenPromising.


From Equations Require Import Equations.


Require Import stdpp.decidable.
Require Import stdpp.list.

#[global] Open Scope stdpp.

#[global] Typeclasses Transparent bits.

(* TODO This will go away very soon so it's fine if it's copy-pasted from ArchSemArm/ArmInst.v *)
Unset Elimination Schemes.
Inductive regval :=
  | Regval_unknown
  | Regval_vector (l : list regval)
  | Regval_list (l : list regval)
  | Regval_option (opt : option regval)
  | Regval_bool (b : bool)
  | Regval_int (z : Z)
  | Regval_string (s : string)
  | Regval_bitvector {n} (b : bv n)
  | Regval_struct (fields : list (string * regval)).
Set Elimination Schemes.


Section regval_rect_gen. (* Most boring code ever *)
  Variable T : regval → Type.
  Variable Tl : list regval → Type.
  Hypothesis T_nil : Tl [].
  Hypothesis T_cons : ∀ {t l}, T t → Tl l → Tl (t :: l).
  Hypothesis T_unknown : T Regval_unknown.
  Hypothesis T_vector : ∀ {l}, Tl l → T (Regval_vector l).
  Hypothesis T_list : ∀ {l}, Tl l → T (Regval_list l).
  Hypothesis T_None : T (Regval_option None).
  Hypothesis T_Some : ∀ {rv}, T rv → T (Regval_option (Some rv)).
  Hypothesis T_bool : ∀ b, T (Regval_bool b).
  Hypothesis T_int : ∀ z, T (Regval_int z).
  Hypothesis T_string : ∀ s, T (Regval_string s).
  Hypothesis T_bitvector : ∀ {n}, ∀ b : bv n, T (Regval_bitvector b).
  Hypothesis T_struct : ∀ {fields}, Tl fields.*2 → T (Regval_struct fields).

  Fixpoint regval_rect_gen (rv : regval) : T rv :=
    let fix go_list (l : list regval) : Tl l :=
        match l with
        | [] => T_nil
        | t :: l => T_cons (regval_rect_gen t) (go_list l)
        end
    in
    let fix go_list' (l : list (string * regval)) : Tl l.*2 :=
        match l with
        | [] => T_nil
        | (s, t) :: l => T_cons (regval_rect_gen t) (go_list' l)
        end
    in
    match rv with
    | Regval_unknown => T_unknown
    | Regval_vector l => T_vector (go_list l)
    | Regval_list l => T_list (go_list l)
    | Regval_option None => T_None
    | Regval_option (Some o) => T_Some (regval_rect_gen o)
    | Regval_bool b => T_bool b
    | Regval_int z => T_int z
    | Regval_string s => T_string s
    | Regval_bitvector b => T_bitvector b
    | Regval_struct l => T_struct (go_list' l)
    end.
End regval_rect_gen.

Section regval_rect.
  Variable T : regval → Type.
  Let Tl (l : list regval) := ∀ x, InT x l → T x.
  Lemma T_nil : Tl [].
  Proof using. sauto lq:on. Defined.
  Lemma T_cons : ∀ t l, T t → Tl l → Tl (t :: l).
  Proof using. sauto lq:on. Defined.
  Hypothesis T_unknown : T Regval_unknown.
  Hypothesis T_vector : ∀ l, Tl l → T (Regval_vector l).
  Hypothesis T_list : ∀ l, Tl l → T (Regval_list l).
  Hypothesis T_None : T (Regval_option None).
  Hypothesis T_Some : ∀ rv, T rv → T (Regval_option (Some rv)).
  Hypothesis T_bool : ∀ b, T (Regval_bool b).
  Hypothesis T_int : ∀ z, T (Regval_int z).
  Hypothesis T_string : ∀ s, T (Regval_string s).
  Hypothesis T_bitvector : ∀ n, ∀ b : bv n, T (Regval_bitvector b).
  Hypothesis T_struct : ∀ fields, Tl fields.*2 → T (Regval_struct fields).

  Definition regval_rect : ∀ rv, T rv :=
    regval_rect_gen T Tl
                    T_nil
                    T_cons
                    T_unknown
                    T_vector
                    T_list
                    T_None
                    T_Some
                    T_bool
                    T_int
                    T_string
                    T_bitvector
                    T_struct.
End regval_rect.
Definition regval_rec := regval_rect.

Section regval_ind.
  Variable P : regval → Prop.
  Let Pl (l : list regval) := ∀ x ∈ l, P x.
  Lemma P_nil : Pl []. Proof using. sauto lq:on. Qed.
  Lemma P_cons : ∀ t l, P t → Pl l → Pl (t :: l).
  Proof using. induction l; sauto lq:on. Qed.
  Hypothesis P_unknown : P (Regval_unknown).
  Hypothesis P_vector : ∀ l, Pl l -> P (Regval_vector l).
  Hypothesis P_list : ∀ l, Pl l -> P (Regval_list l).
  Hypothesis P_None : P (Regval_option None).
  Hypothesis P_Some : ∀ rv, P rv → P (Regval_option (Some rv)).
  Hypothesis P_bool : ∀ b, P (Regval_bool b).
  Hypothesis P_int : ∀ z, P (Regval_int z).
  Hypothesis P_string : ∀ s, P (Regval_string s).
  Hypothesis P_bitvector : ∀ n, ∀ b : bv n, P (Regval_bitvector b).
  Hypothesis P_struct : ∀ fields, Pl fields.*2 → P (Regval_struct fields).

  Definition regval_ind : ∀ rv, P rv :=
    regval_rect_gen P Pl
                    P_nil
                    P_cons
                    P_unknown
                    P_vector
                    P_list
                    P_None
                    P_Some
                    P_bool
                    P_int
                    P_string
                    P_bitvector
                    P_struct.
End regval_ind.

(* Can't be bothered to do regval_sind *)

#[global] Instance regval_eq_dec : EqDecision regval.
Proof. intro x; induction x; intro y; destruct y; typeclasses eauto with eqdec.
Defined.

#[derive(eliminator=no)]
Equations regval_to_gen_tree : regval → gen_tree (Z + string) :=
  regval_to_gen_tree Regval_unknown := GenNode 0 [];
  regval_to_gen_tree (Regval_vector v) := GenNode 1 (map regval_to_gen_tree v);
  regval_to_gen_tree (Regval_list l) := GenNode 2 (map regval_to_gen_tree l);
  regval_to_gen_tree (Regval_option None) := GenNode 3 [];
  regval_to_gen_tree (Regval_option (Some rv)) := GenNode 3 [regval_to_gen_tree rv];
  regval_to_gen_tree (Regval_bool true) := (GenNode 4 []);
  regval_to_gen_tree (Regval_bool false) := (GenNode 5 []);
  regval_to_gen_tree (Regval_int z) := (GenLeaf (inl z));
  regval_to_gen_tree (Regval_string s) := (GenLeaf (inr s));
  regval_to_gen_tree (@Regval_bitvector n bv) :=
    GenNode 6 [GenLeaf (inl (Z.of_N n)); GenLeaf (inl (bv_unsigned bv))];
  regval_to_gen_tree (Regval_struct l) :=
    GenNode 7 (map (λ '(s, rv), GenNode 8 [GenLeaf (inr s); regval_to_gen_tree rv]) l).

#[derive(eliminator=no)]
Equations regval_of_gen_tree : gen_tree (Z + string) → option regval := {
    regval_of_gen_tree (GenNode 0 []) := Some (Regval_unknown);
    regval_of_gen_tree (GenNode 1 l) :=
      for x in l do regval_of_gen_tree x end |$> Regval_vector;
    regval_of_gen_tree (GenNode 2 l) :=
      for x in l do regval_of_gen_tree x end |$> Regval_list;
    regval_of_gen_tree (GenNode 3 []) := Some (Regval_option None);
    regval_of_gen_tree (GenNode 3 [t]) :=
      regval_of_gen_tree t |$> Some |$> Regval_option;
    regval_of_gen_tree (GenNode 4 []) := Some (Regval_bool true);
    regval_of_gen_tree (GenNode 5 []) := Some (Regval_bool false);
    regval_of_gen_tree (GenLeaf (inl z)) := Some (Regval_int z);
    regval_of_gen_tree (GenLeaf (inr s)) := Some (Regval_string s);
    regval_of_gen_tree (GenNode 6 [GenLeaf (inl n); GenLeaf (inl v)]) :=
        Some (Regval_bitvector (Z_to_bv (Z.to_N n) v));
    regval_of_gen_tree (GenNode 7 l) :=
      for x in l do regval_field_of_gen_tree x end |$> Regval_struct;
    regval_of_gen_tree _ := None
  }
where regval_field_of_gen_tree : gen_tree (Z + string) → option (string * regval) := {
    regval_field_of_gen_tree (GenNode 8 [GenLeaf (inr st); t]) :=
    regval_of_gen_tree t |$> (st,.);
    regval_field_of_gen_tree a := None
  }.

Lemma regval_to_gen_tree_inj rv :
  regval_of_gen_tree (regval_to_gen_tree rv) = Some rv.
  induction rv.
  (* Bool encoding are defined separately for true and false *)
  all: try match goal with b : bool |- _ => destruct b end.
  all: simp regval_to_gen_tree regval_of_gen_tree.
  all: try hauto lq:on use:N2Z.id,Z_to_bv_bv_unsigned.
  (* Only list constructors remains *)
  all: apply fmap_Some_2.
  all: apply mapM_Some_2.
  all: apply Forall2_map_l.
  all: apply Forall2_diag.
  all: try assumption.
  (* Only struct case remains *)
  cdestruct |- **.
  apply fmap_Some_2.
  set_unfold.
  sfirstorder.
Qed.

#[global] Instance regval_countable : Countable regval :=
  inj_countable regval_to_gen_tree regval_of_gen_tree regval_to_gen_tree_inj.

#[global] Instance regval_inhabited : Inhabited regval :=
  populate Regval_unknown.

Definition regval_bv (n : N) (rv : regval) : option (bv n) :=
  match rv with
  | @Regval_bitvector z b =>
      match decide (z = n) with
      | left e => Some (ctrans e b)
      | right _ => None
      end
  | _ => None
  end.

Module RiscV.

  Module Arch <: Arch.
    Definition reg := string.
    #[export] Typeclasses Transparent reg.
    Definition reg_eq : EqDecision reg := _.
    Definition reg_countable : Countable reg := _.

    Definition reg_type (_ : reg) := regval.
    #[export] Typeclasses Transparent reg_type.

    Definition reg_type_eq (r : reg) : EqDecision (reg_type r) := _.
    Definition reg_type_countable (r : reg) : Countable (reg_type r) := _.
    Definition reg_type_inhabited (r : reg) : Inhabited (reg_type r) := _.
    Definition ctrans_reg_type : CTrans reg_type := λ _ _ _ x, x.
    #[export] Existing Instance ctrans_reg_type.
    Definition ctrans_reg_type_simpl : CTransSimpl reg_type := λ _ _ _, eq_refl.
    #[export] Existing Instance ctrans_reg_type_simpl.
    Definition reg_type_eq_dep_dec : EqDepDecision reg_type.
    Proof. unfold EqDepDecision. intros. rewrite JMeq_simpl. tc_solve. Defined.
    #[export] Existing Instance reg_type_eq_dep_dec.

    (** None means default access (strict or relaxed is up to the concurrency model).
        Some s, means access with a MSR/MRS with name "s" *)
    Definition reg_acc := unit.
    #[export] Typeclasses Transparent reg_acc.
    Definition reg_acc_eq : EqDecision reg_acc := _.
    #[export] Typeclasses Transparent reg_acc_eq.

    Definition pc_reg := "_PC".

    Definition CHERI := false.
    Definition cap_size_log := 0%N. (* dummy value *)

    Definition addr_size := 64%N.
    #[export] Typeclasses Transparent addr_size.
    Definition addr_space := ()%type.
    #[export] Typeclasses Transparent addr_space.
    Definition addr_space_eq : EqDecision addr_space := _.
    #[export] Typeclasses Transparent addr_space_eq.
    Definition addr_space_countable : Countable addr_space := _.
    #[export] Typeclasses Transparent addr_space_countable.


    Definition mem_acc := Access_kind RISCV_strong_access.
    #[export] Typeclasses Transparent mem_acc.
    Definition mem_acc_eq : EqDecision mem_acc := _.
    (* Current sail-riscv mismaps RCpc accesses to AV_rel_or_acq, and
       the then use AK_arch for RCsc accesses, so we fix that here *)
    Definition is_explicit (acc : mem_acc) :=
      match acc with
      | AK_explicit _ => true
      | AK_arch _ => true
      | _ => false
      end.
    Definition is_ifetch (acc : mem_acc) :=
      if acc is AK_ifetch _ then true else false.
    Definition is_ttw (acc : mem_acc) :=
      if acc is AK_ttw _ then true else false.
    Definition is_relaxed (acc : mem_acc) :=
      if acc is AK_explicit eak then
        eak.(Explicit_access_kind_strength) =? AS_normal else false.
    Definition is_rel_acq_rcsc (acc : mem_acc) :=
      if acc is AK_arch _ then true else false.
    Definition is_rel_acq_rcpc (acc : mem_acc) :=
      if acc is AK_explicit eak then
        eak.(Explicit_access_kind_strength) =? AS_rel_or_acq else false.
    Definition is_standalone (acc : mem_acc) :=
      match acc with
      | AK_explicit eak => eak.(Explicit_access_kind_variety) =? AV_plain
      | AK_arch rsa => rsa.(RISCV_strong_access_variety) =? AV_plain
      | _ => false
      end.
    Definition is_exclusive (acc : mem_acc) :=
      match acc with
      | AK_explicit eak => eak.(Explicit_access_kind_variety) =? AV_exclusive
      | AK_arch rsa => rsa.(RISCV_strong_access_variety) =? AV_exclusive
      | _ => false
      end.
    Definition is_atomic_rmw (acc : mem_acc) :=
      match acc with
      | AK_explicit eak => eak.(Explicit_access_kind_variety) =? AV_atomic_rmw
      | AK_arch rsa => rsa.(RISCV_strong_access_variety) =? AV_atomic_rmw
      | _ => false
      end.

    Definition abort := unit.

    Definition barrier := barrier_kind.
    #[export] Typeclasses Transparent barrier.
    Definition barrier_eq : EqDecision barrier_kind := _.
    Definition cache_op := ∅%type.
    #[export] Typeclasses Transparent cache_op.
    Definition cache_op_eq : EqDecision cache_op := _.
    Definition tlbi := ∅%type.
    #[export] Typeclasses Transparent tlbi.
    Definition tlbi_eq : EqDecision tlbi := _.
    Definition exn := ∅%type.
    #[export] Typeclasses Transparent exn.
    Definition exn_eq : EqDecision exn := _.
    Definition trans_start := ∅%type.
    #[export] Typeclasses Transparent trans_start.
    Definition trans_start_eq : EqDecision trans_start := _.
    Definition trans_end := ∅%type.
    #[export] Typeclasses Transparent trans_end.
    Definition trans_end_eq : EqDecision trans_end := _.
  End Arch.
  Module Interface := Interface Arch.
  (* Module IWA <: InterfaceWithArch. *)
  (*   Module Arch := Arch. *)
  (*   Module Interface := Interface. *)
  (* End IWA. *)
End RiscV.

Module NoCHERI.
  Definition no_cheri : ¬ RiscV.Arch.CHERI := ltac:(naive_solver).
End NoCHERI.

Bind Scope string_scope with RiscV.Arch.reg.

Module RiscVTM := TermModels RiscV.
Module RiscVCand := CandidateExecutions RiscV RiscVTM NoCHERI.
Module RiscVGenPro := GenPromising RiscV RiscVTM.

Export RiscV.Arch.
Export RiscV.Interface.
Export RiscVTM.
Export RiscVCand.
Export RiscVGenPro.
