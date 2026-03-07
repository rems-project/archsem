(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
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

From Stdlib Require Import ZArith.
From Stdlib Require Import Extraction.

Require Import Options.
Require Import Common HVec Exec.


(** * Base defaults *)

From Stdlib Require Import ExtrOcamlBasic.


(** * Bools *)

Extract Inlined Constant Decision => "bool".
Extract Inlined Constant Bool.eqb => "(=)".
Extraction Inline decide.
Extraction Inline decide_rel.

(** * Integers

All integers types go to Zarith *)

(* From Stdlib Require Import ExtrOcamlZBigInt. *)
(* From Stdlib Require Import ExtrOcamlNatBigInt. *)

Extract Inductive positive => "ZO.t"
  ["(fun x -> ZO.((x lsl 1) lor one))"
   "(fun x -> ZO.(x lsl 1))"
   "ZO.one"]
  "ZO.(fun f2p1 f2p f1 p ->
     if p == one then f1 ()
     else if is_odd p then f2p1 (p asr 1) else f2p (p asr 1))".

Extract Inductive Z => "ZO.t" ["ZO.zero" "" "ZO.neg"]
  "ZO.(fun f0 fp fn z -> match sign z with 0 -> f0 () | 1 -> fp z | _ -> fn (neg z))".

Extract Inductive N => "ZO.t" ["ZO.zero" ""]
  "ZO.(fun f0 fp n -> match sign n with 0 -> f0 () | _ -> fp n)".

Extract Inductive nat => "ZO.t" ["ZO.zero" "ZO.succ"]
  "ZO.(fun f0 fS n -> match sign n with 0 -> f0 () | _ -> fS (pred n))".

Extract Inlined Constant BinPos.Pos.succ => "ZO.succ".
Extract Inlined Constant PosDef.Pos.succ => "ZO.succ".
Extract Inlined Constant N.succ => "ZO.succ".
Extract Inlined Constant Z.succ => "ZO.succ".

Extract Inlined Constant Pos.pred => "ZO.pred_pos".
Extract Inlined Constant N.pred => "ZO.pred_nat".
Extract Inlined Constant Z.pred => "ZO.pred".
Extract Inlined Constant Init.Nat.pred => "ZO.pred_nat".
Extract Inlined Constant PeanoNat.Nat.pred => "ZO.pred_nat".

Extract Inlined Constant BinPos.Pos.add => "ZO.add".
Extract Inlined Constant PosDef.Pos.add => "ZO.add".
Extract Inlined Constant BinNat.N.add => "ZO.add".
Extract Inlined Constant BinNatDef.N.add => "ZO.add".
Extract Inlined Constant Z.add => "ZO.add".
Extract Inlined Constant Init.Nat.add => "ZO.add".
Extract Inlined Constant PeanoNat.Nat.add => "ZO.add".

Extract Inlined Constant Z.opp => "ZO.neg".

Extract Inlined Constant BinPos.Pos.sub => "ZO.sub_pos".
Extract Inlined Constant PosDef.Pos.sub => "ZO.sub_pos".
Extract Inlined Constant BinNat.N.sub => "ZO.sub_nat".
Extract Inlined Constant NatDef.N.sub => "ZO.sub_nat".
Extract Inlined Constant Z.sub => "ZO.sub".
Extract Inlined Constant Init.Nat.sub => "ZO.sub_nat".
Extract Inlined Constant PeanoNat.Nat.sub => "ZO.sub_nat".

Extract Inlined Constant BinPos.Pos.mul => "ZO.mul".
Extract Inlined Constant PosDef.Pos.mul => "ZO.mul".
Extract Inlined Constant BinNat.N.mul => "ZO.mul".
Extract Inlined Constant BinNatDef.N.mul => "ZO.mul".
Extract Inlined Constant Z.mul => "ZO.mul".
Extract Inlined Constant Init.Nat.mul => "ZO.mul".
Extract Inlined Constant PeanoNat.Nat.mul => "ZO.mul".

Extract Inlined Constant BinPos.Pos.min => "ZO.min".
Extract Inlined Constant BinNat.N.min => "ZO.min".
Extract Inlined Constant BinNatDef.N.min => "ZO.min".
Extract Inlined Constant Z.min => "ZO.min".
Extract Inlined Constant Init.Nat.min => "ZO.min".
Extract Inlined Constant PeanoNat.Nat.min => "ZO.min".

Extract Inlined Constant BinPos.Pos.max => "ZO.max".
Extract Inlined Constant BinNat.N.max => "ZO.max".
Extract Inlined Constant BinNatDef.N.max => "ZO.max".
Extract Inlined Constant Z.max => "ZO.max".
Extract Inlined Constant Init.Nat.max => "ZO.max".
Extract Inlined Constant PeanoNat.Nat.max => "ZO.max".

Extract Inlined Constant BinPos.Pos.compare => "ZO.compare_rocq".
Extract Inlined Constant PosDef.Pos.compare => "ZO.compare_rocq".
Extract Inlined Constant BinPos.Pos.compare_cont => "ZO.compare_rocq".
Extract Inlined Constant PosDef.Pos.compare_cont => "ZO.compare_rocq".
Extract Inlined Constant BinNat.N.compare => "ZO.compare_rocq".
Extract Inlined Constant NatDef.N.compare => "ZO.compare_rocq".
Extract Inlined Constant Z.compare => "ZO.compare_rocq".
Extract Inlined Constant PeanoNat.Nat.compare => "ZO.compare_rocq".
Extract Inlined Constant Init.Nat.compare => "ZO.compare_rocq".

Extract Inlined Constant Pos.eqb => "ZO.equal".
Extract Inlined Constant PosDef.Pos.eqb => "ZO.equal".
Extract Inlined Constant BinPos.Pos.eq_dec => "ZO.equal".
Extract Inlined Constant Pos.eq_dec => "ZO.equal".
Extract Inlined Constant N.eqb => "ZO.equal".
Extract Inlined Constant N.eq_dec => "ZO.equal".
Extract Inlined Constant BinNat.N.eq_dec => "ZO.equal".
Extract Inlined Constant Z.eqb => "ZO.equal".
Extract Inlined Constant Z.eq_dec => "ZO.equal".
Extract Inlined Constant BinInt.Z.eq_dec => "ZO.equal".
Extract Inlined Constant PeanoNat.Nat.eq_dec => "ZO.equal".
Extract Inlined Constant numbers.Nat.eq_dec => "ZO.equal".
Extract Inlined Constant PeanoNat.Nat.eqb => "ZO.equal".
Extract Inlined Constant Init.Nat.eqb => "ZO.equal".
Extract Inlined Constant EqNat.eq_nat_decide => "ZO.equal".

Extract Inlined Constant PeanoNat.Nat.leb => "ZO.leq".
Extract Inlined Constant Init.Nat.leb => "ZO.leq".
Extract Inlined Constant PeanoNat.Nat.ltb => "ZO.lt".
Extract Inlined Constant Init.Nat.ltb => "ZO.lt".
Extract Inlined Constant Z.leb => "ZO.leq".
Extract Inlined Constant Z.ltb => "ZO.lt".
Extract Inlined Constant Z.le_dec => "ZO.leq".
Extract Inlined Constant Z.lt_dec => "ZO.lt".
Extract Inlined Constant N.le_dec => "ZO.leq".
Extract Inlined Constant N.lt_dec => "ZO.lt".
Extract Inlined Constant numbers.Nat.le_dec => "ZO.leq".
Extract Inlined Constant numbers.Nat.lt_dec => "ZO.lt".
Extract Inlined Constant CArith.le_dec => "ZO.leq".
Extract Inlined Constant CArith.lt_dec => "ZO.lt".

Extract Inlined Constant PeanoNat.Nat.pow => "ZO.powZ".
Extract Inlined Constant Z.pow_pos => "ZO.powZ".
Extract Inlined Constant Z.pow => "ZO.powZ".

Extract Inlined Constant Z.of_N => "Fun.id".
Extract Inlined Constant Z.of_nat => "Fun.id".
Extract Inlined Constant Z.to_N => "ZO.to_nat".
Extract Inlined Constant Z.to_nat => "ZO.to_nat".

Extract Inlined Constant Z.abs => "ZO.abs".
Extract Inlined Constant Z.abs_nat => "ZO.abs".
Extract Inlined Constant Z.abs_N => "ZO.abs".
Extract Inlined Constant Z.sgn => "ZO.signZ".

Extract Inlined Constant N.div => "ZO.ediv_z".
Extract Inlined Constant N.modulo => "ZO.erem_z".
Extract Inlined Constant N.div_eucl => "ZO.ediv_rem_z".

Extract Inlined Constant Z.div => "ZO.ediv_z".
Extract Inlined Constant Z.modulo => "ZO.erem_z".
Extract Inlined Constant Z.div_eucl => "ZO.ediv_rem_z".

Extract Inlined Constant N.shiftl => "ZO.shiftl".
Extract Inlined Constant Z.shiftl => "ZO.shiftl".
Extract Inlined Constant N.shiftr => "ZO.shiftr".
Extract Inlined Constant Z.shiftr => "ZO.shiftr".
Extract Inlined Constant PeanoNat.Nat.div2 => "ZO.shiftr".
Extract Inlined Constant Init.Nat.div2 => "ZO.shiftr".

(** * Strings *)

From Stdlib Require Import ExtrOcamlNativeString.
Extraction Blacklist String.

From Stdlib Require BinaryString.

Extract Inlined Constant BinaryString.Raw.to_N => "Utils.bin_str_to_N".
Extract Inlined Constant HexString.Raw.to_N => "Utils.hex_str_to_N".
Extract Inlined Constant HexString.of_Z => "Utils.hex_str_of_Z".

(** * Lists *)

Extract Inlined Constant map => "Stdlib.List.map".
Extract Inlined Constant length => "Utils.lengthZ".

Extraction Blacklist List.

(** * Finite numbers *)

Extract Inductive fin => "ZO.t"
  [ "ZO.zero" "ZO.succ" ]
  "Support.fin_case".

Extraction Implicit Fin.F1 [n].
Extraction Implicit Fin.FS [n].

Extraction Implicit fin_dec [n].
Extract Constant fin_dec => "ZO.equal".

Extraction Implicit fin_to_nat [n].
Extract Inlined Constant fin_to_nat => "Fun.id".

Extract Inlined Constant fin0_magic => "Support.fin0_magic".

(** * Vector

Extracted as lists for now *)

Extract Inductive vec => list [ "[]" "( :: )" ].
Extraction Implicit vnil [A].
Extraction Implicit vcons [A n].
Extraction Implicit vmap [A B n].
Extract Inlined Constant vmap => "List.map".
Extract Inlined Constant list_to_vec  => "(fun x -> x)".

Extraction Implicit Vector.last [A n].
Extract Inlined Constant Vector.last => "Support.list_last".
Extraction Implicit Vector.append [A n p].
Extract Inlined Constant Vector.append => "List.append".

Extraction Implicit vector_lookup_total [A m].
Extract Inlined Constant vector_lookup_total => "Support.list_get".

Extraction Implicit vinsert [A n].
Extract Inlined Constant vinsert => "Support.list_set".

Extraction Implicit vec_to_list [A n].
Extract Inlined Constant vec_to_list => "(fun x -> x)".

Extraction Implicit cprodn [A n].
Extraction Implicit vmapM [A B n].

Extraction Implicit vec_dec [A n].
Extract Inlined Constant vec_dec => "List.equal".

(* In theory by marking the correct arguments implicit, this could also just be
   List.equal, but I (TP) couldn't make it work *)
Extract Inlined Constant vec_eqdep_dec => "Support.vec_eqdep_dec".

(** * HVec *)
Extraction Implicit hget [n].
Extraction Implicit hset [n].

(** * Result *)

(* Extract Inductive result => result [ "Ok" "Error"]. *)

(** * CTrans

Extract transport to identity function *)


Extract Inlined Constant ctrans => "(fun x -> x)".
Extraction Implicit ctrans [CTrans x y].
