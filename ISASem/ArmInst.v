Require Import Strings.String.
Require Import stdpp.unstable.bitvector.
Require Import stdpp.strings.
Require Import stdpp.base.
Require Import stdpp.countable.
Require Import stdpp.vector.
Require Import SSCCommon.Options.
Require Import Interface.
Require Import Deps.
Require Import SailStdpp.Base.
Require Export SailArmInstTypes.
Require Import Coq.Reals.Rbase.
From RecordUpdate Require Import RecordSet.
From SSCCommon Require Import CBase COption CList CBitvector Effects CDestruct.


From Equations Require Import Equations.


Require Import stdpp.decidable.
Require Import stdpp.list.

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
  Let Pl (l : list regval) := ∀'x ∈ l, P x.
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
  cdestruct_intros.
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
      | left e => Some (bv_conv e b)
      | right _ => None
      end
  | _ => None
  end.

#[global] Instance FullAddress_eta : Settable _ :=
  settable! Build_FullAddress <FullAddress_paspace; FullAddress_address>.

#[global] Instance PASpace_eq_dec : EqDecision PASpace.
Proof. solve_decision. Qed.
#[global] Instance FullAddress_eq_dec : EqDecision FullAddress.
Proof. solve_decision. Qed.

Definition PASpace_to_nat (pa : PASpace) : nat :=
  match pa with
  | PAS_NonSecure => 0
  | PAS_Secure => 1
  | PAS_Root => 2
  | PAS_Realm => 3
  end.

Definition PASpace_from_nat (pa : nat) :=
  match pa with
  | 0%nat => Some PAS_NonSecure
  | 1%nat => Some PAS_Secure
  | 2%nat => Some PAS_Root
  | 3%nat => Some PAS_Realm
  | _ => None
  end.

Lemma PASpace_from_nat_to_nat (pa : PASpace) :
  PASpace_from_nat (PASpace_to_nat pa) = Some pa.
Proof. by destruct pa. Qed.

#[global] Instance PASpace_countable : Countable PASpace.
Proof.
  apply (inj_countable PASpace_to_nat PASpace_from_nat PASpace_from_nat_to_nat).
Defined.

#[global] Instance FullAddress_countable : Countable FullAddress.
Proof.
  eapply (inj_countable (fun fa => (FullAddress_paspace fa, FullAddress_address fa))
                        (fun x => Some (Build_FullAddress x.1 x.2))).
  intro x. by destruct x.
Defined.

#[global] Instance arm_acc_type_eq_dec : EqDecision arm_acc_type.
Proof. solve_decision. Defined.

#[global] Instance MemAttrHints_eq_dec : EqDecision MemAttrHints.
Proof. solve_decision. Defined.

#[global] Instance MemoryAttributes_eq_dec : EqDecision MemoryAttributes.
Proof. solve_decision. Defined.

#[global] Instance S1TTWParams_eq_dec : EqDecision S1TTWParams.
Proof. solve_decision. Defined.

#[global] Instance S2TTWParams_eq_dec : EqDecision S2TTWParams.
Proof. solve_decision. Defined.

#[global] Instance ArithFact_eq_dec P : EqDecision (ArithFact P).
Proof. left. apply ArithFact_irrelevant. Defined.

#[global] Instance TranslationInfo_eq_dec : EqDecision TranslationInfo.
Proof. solve_decision. Defined.

#[global] Instance DxB_eq_dec : EqDecision DxB.
Proof. solve_decision. Defined.

#[global] Instance Barrier_eq_dec : EqDecision Barrier.
Proof. solve_decision. Defined.

#[global] Instance CacheRecord_eq_dec : EqDecision CacheRecord.
Proof. solve_decision. Defined.

#[global] Instance TLBIRecord_eq_dec : EqDecision TLBIRecord.
Proof. solve_decision. Defined.

#[global] Instance TLBI_eq_dec : EqDecision TLBI.
Proof. solve_decision. Defined.

#[global] Instance ExceptionRecord_eq_dec : EqDecision ExceptionRecord.
Proof. solve_decision. Defined.

#[global] Instance GPCFRecord_eq_dec : EqDecision GPCFRecord.
Proof. solve_decision. Defined.

#[global] Instance FaultRecord_eq_dec : EqDecision FaultRecord.
Proof. solve_decision. Defined.

#[global] Instance Exn_eq_dec : EqDecision Exn.
Proof. solve_decision. Defined.

Module Arm.

  Module Arch <: Arch.
    (* TODO: This should be an enum not a string *)
    Definition reg := string.
    Definition reg_eq : EqDecision reg := _.
    Definition reg_countable : Countable reg := _.
    Definition reg_type := regval.
    Definition reg_type_eq : EqDecision reg_type := _.
    Definition reg_type_countable : Countable reg_type := _.
    Definition reg_type_inhabited : Inhabited reg_type := _.

    (** None means default access (strict or relaxed is up to the concurrency model).
        Some s, means access with a MSR/MRS with name "s" *)
    Definition reg_acc := option string.
    Definition reg_acc_eq : EqDecision reg_acc := _.

    Definition va_size := 64%N.
    Definition pa := FullAddress.
    Definition pa_eq : EqDecision pa := _.
    Definition pa_countable : Countable pa := _.
    Definition pa_addZ pa z :=
      set FullAddress_address (λ addr, addr `+Z` z)%bv pa.
    Lemma pa_addZ_assoc pa z z' :
      pa_addZ (pa_addZ pa z) z' = pa_addZ pa (z + z')%Z.
    Proof. record_eq; cbn; [reflexivity | bv_solve]. Qed.
    Lemma pa_addZ_zero pa : pa_addZ pa 0 = pa.
    Proof. record_eq; cbn; [reflexivity | bv_solve]. Qed.

    Definition arch_ak := arm_acc_type.
    Definition arch_ak_eq : EqDecision arm_acc_type := _.
    Definition translation := TranslationInfo.
    Definition translation_eq : EqDecision TranslationInfo := _.
    Definition abort := PhysMemRetStatus.

    Definition barrier := Barrier.
    Definition barrier_eq : EqDecision Barrier := _.
    Definition cache_op := CacheRecord.
    Definition cache_op_eq : EqDecision CacheRecord := _.
    Definition tlb_op := TLBI.
    Definition tlb_op_eq : EqDecision TLBI := _.

    (* TODO fixup dependencies in exception type *)
    Definition fault (deps : Type) := Exn.
    Definition fault_eq :
      ∀ deps, EqDecision deps → EqDecision (fault deps) := _.
  End Arch.
  Include Arch.

  Module Interface := Interface Arch.
  Include Interface.
  Module IWA <: InterfaceWithArch.
    Module Arch := Arch.
    Include Arch.
    Include Interface.
  End IWA.
  Module DepsDefs := DepsDefs IWA.
  Include DepsDefs.
  Module IWD <: InterfaceWithDeps.
    Module IWA := IWA.
    Include IWA.
    Include DepsDefs.
  End IWD.
  Module ArchDeps <: ArchDeps IWD.
    Import IWD.
    Definition footprint_context := unit.
    Definition get_footprint_context {deps : Type}
      : iMon deps () := mret ().
    Definition fault_add_empty_deps := @id Exn.
    Definition fault_add_deps (_ : Footprint.t) := @id Exn.
  End ArchDeps.
  Module AD := ArchDeps.
  Include ArchDeps.
  Module DepsComp := DepsComp IWD ArchDeps.
  Include DepsComp.
  Module IWDC <: InterfaceWithDepsComp.
    Module IWD := IWD.
    Module AD := ArchDeps.
    Include IWD.
    Include ArchDeps.
    Include DepsComp.
  End IWDC.
End Arm.

Bind Scope string_scope with Arm.reg.

Export Arm.
