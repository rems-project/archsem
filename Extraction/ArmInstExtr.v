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

Require Import ASCommon.CExtraction.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.
From ArchSemRiscV Require Import RiscVInst.
From ArchSemX86 Require Import X86Inst OperationalX86TSO.

Unset Extraction SafeImplicits.

Extract Inductive ArchSem.Interface.reg_gen_val =>
  "RegValGen.t"
  ["RegValGen.Number" "RegValGen.String" "RegValGen.Array" "RegValGen.Struct"].


(** * Coq-sail *)

Extraction Implicit SailStdpp.TypeCasts.cast_positive [p q].
Extract Inlined Constant SailStdpp.TypeCasts.cast_positive => "Fun.id".

Extraction Implicit SailStdpp.TypeCasts.cast_N [m n].
Extract Inlined Constant SailStdpp.TypeCasts.cast_N => "Fun.id".

Extraction Implicit SailStdpp.TypeCasts.cast_Z [m n].
Extract Inlined Constant SailStdpp.TypeCasts.cast_Z => "Fun.id".

Extract Inductive SailStdpp.Values.result => "result" [ "Ok" "Error" ].

(** * sail-riscv *)

(** [instruction] has too many constructors for an OCaml variant, see
    [riscVInstruction.ml] *)
Extract Inductive Riscv.rv64d_types.instruction => "RiscVInstruction.t"
  ["(RiscVInstruction.mk 0)"
   "(RiscVInstruction.mk 1)"
   "(RiscVInstruction.mk 2)"
   "(RiscVInstruction.mk 3)"
   "(RiscVInstruction.mk 4)"
   "(RiscVInstruction.mk 5)"
   "(RiscVInstruction.mk 6)"
   "(RiscVInstruction.mk 7)"
   "(RiscVInstruction.mk 8)"
   "(RiscVInstruction.mk 9)"
   "(RiscVInstruction.mk 10)"
   "(RiscVInstruction.mk 11)"
   "(RiscVInstruction.mk 12)"
   "(RiscVInstruction.mk 13)"
   "(RiscVInstruction.mk 14)"
   "(RiscVInstruction.mk 15)"
   "(RiscVInstruction.mk 16)"
   "(RiscVInstruction.mk 17)"
   "(RiscVInstruction.mk 18)"
   "(RiscVInstruction.mk 19)"
   "(RiscVInstruction.mk 20)"
   "(RiscVInstruction.mk 21)"
   "(RiscVInstruction.mk 22)"
   "(RiscVInstruction.mk 23)"
   "(RiscVInstruction.mk 24)"
   "(RiscVInstruction.mk 25)"
   "(RiscVInstruction.mk 26)"
   "(RiscVInstruction.mk 27)"
   "(RiscVInstruction.mk 28)"
   "(RiscVInstruction.mk 29)"
   "(RiscVInstruction.mk 30)"
   "(RiscVInstruction.mk 31)"
   "(RiscVInstruction.mk 32)"
   "(RiscVInstruction.mk 33)"
   "(RiscVInstruction.mk 34)"
   "(RiscVInstruction.mk 35)"
   "(RiscVInstruction.mk 36)"
   "(RiscVInstruction.mk 37)"
   "(RiscVInstruction.mk 38)"
   "(RiscVInstruction.mk 39)"
   "(RiscVInstruction.mk 40)"
   "(RiscVInstruction.mk 41)"
   "(RiscVInstruction.mk 42)"
   "(RiscVInstruction.mk 43)"
   "(RiscVInstruction.mk 44)"
   "(RiscVInstruction.mk 45)"
   "(RiscVInstruction.mk 46)"
   "(RiscVInstruction.mk 47)"
   "(RiscVInstruction.mk 48)"
   "(RiscVInstruction.mk 49)"
   "(RiscVInstruction.mk 50)"
   "(RiscVInstruction.mk 51)"
   "(RiscVInstruction.mk 52)"
   "(RiscVInstruction.mk 53)"
   "(RiscVInstruction.mk 54)"
   "(RiscVInstruction.mk 55)"
   "(RiscVInstruction.mk 56)"
   "(RiscVInstruction.mk 57)"
   "(RiscVInstruction.mk 58)"
   "(RiscVInstruction.mk 59)"
   "(RiscVInstruction.mk 60)"
   "(RiscVInstruction.mk 61)"
   "(RiscVInstruction.mk 62)"
   "(RiscVInstruction.mk 63)"
   "(RiscVInstruction.mk 64)"
   "(RiscVInstruction.mk 65)"
   "(RiscVInstruction.mk 66)"
   "(RiscVInstruction.mk 67)"
   "(RiscVInstruction.mk 68)"
   "(RiscVInstruction.mk 69)"
   "(RiscVInstruction.mk 70)"
   "(RiscVInstruction.mk 71)"
   "(RiscVInstruction.mk 72)"
   "(RiscVInstruction.mk 73)"
   "(RiscVInstruction.mk 74)"
   "(RiscVInstruction.mk 75)"
   "(RiscVInstruction.mk 76)"
   "(RiscVInstruction.mk 77)"
   "(RiscVInstruction.mk 78)"
   "(RiscVInstruction.mk 79)"
   "(RiscVInstruction.mk 80)"
   "(RiscVInstruction.mk 81)"
   "(RiscVInstruction.mk 82)"
   "(RiscVInstruction.mk 83)"
   "(RiscVInstruction.mk 84)"
   "(RiscVInstruction.mk 85)"
   "(RiscVInstruction.mk 86)"
   "(RiscVInstruction.mk 87)"
   "(RiscVInstruction.mk 88)"
   "(RiscVInstruction.mk 89)"
   "(RiscVInstruction.mk 90)"
   "(RiscVInstruction.mk 91)"
   "(RiscVInstruction.mk 92)"
   "(RiscVInstruction.mk 93)"
   "(RiscVInstruction.mk 94)"
   "(RiscVInstruction.mk 95)"
   "(RiscVInstruction.mk 96)"
   "(RiscVInstruction.mk 97)"
   "(RiscVInstruction.mk 98)"
   "(RiscVInstruction.mk 99)"
   "(RiscVInstruction.mk 100)"
   "(RiscVInstruction.mk 101)"
   "(RiscVInstruction.mk 102)"
   "(RiscVInstruction.mk 103)"
   "(RiscVInstruction.mk 104)"
   "(RiscVInstruction.mk 105)"
   "(RiscVInstruction.mk 106)"
   "(RiscVInstruction.mk 107)"
   "(RiscVInstruction.mk 108)"
   "(RiscVInstruction.mk 109)"
   "(RiscVInstruction.mk 110)"
   "(RiscVInstruction.mk 111)"
   "(RiscVInstruction.mk 112)"
   "(RiscVInstruction.mk 113)"
   "(RiscVInstruction.mk 114)"
   "(RiscVInstruction.mk 115)"
   "(RiscVInstruction.mk 116)"
   "(RiscVInstruction.mk 117)"
   "(RiscVInstruction.mk 118)"
   "(RiscVInstruction.mk 119)"
   "(RiscVInstruction.mk 120)"
   "(RiscVInstruction.mk 121)"
   "(RiscVInstruction.mk 122)"
   "(RiscVInstruction.mk 123)"
   "(RiscVInstruction.mk 124)"
   "(RiscVInstruction.mk 125)"
   "(RiscVInstruction.mk 126)"
   "(RiscVInstruction.mk 127)"
   "(RiscVInstruction.mk 128)"
   "(RiscVInstruction.mk 129)"
   "(RiscVInstruction.mk 130)"
   "(RiscVInstruction.mk 131)"
   "(RiscVInstruction.mk 132)"
   "(RiscVInstruction.mk 133)"
   "(RiscVInstruction.mk 134)"
   "(RiscVInstruction.mk 135)"
   "(RiscVInstruction.mk 136)"
   "(RiscVInstruction.mk 137)"
   "(RiscVInstruction.mk 138)"
   "(RiscVInstruction.mk 139)"
   "(RiscVInstruction.mk 140)"
   "(RiscVInstruction.mk 141)"
   "(RiscVInstruction.mk 142)"
   "(RiscVInstruction.mk 143)"
   "(RiscVInstruction.mk 144)"
   "(RiscVInstruction.mk 145)"
   "(RiscVInstruction.mk 146)"
   "(RiscVInstruction.mk 147)"
   "(RiscVInstruction.mk 148)"
   "(RiscVInstruction.mk 149)"
   "(RiscVInstruction.mk 150)"
   "(RiscVInstruction.mk 151)"
   "(RiscVInstruction.mk 152)"
   "(RiscVInstruction.mk 153)"
   "(RiscVInstruction.mk 154)"
   "(RiscVInstruction.mk 155)"
   "(RiscVInstruction.mk 156)"
   "(RiscVInstruction.mk 157)"
   "(RiscVInstruction.mk 158)"
   "(RiscVInstruction.mk 159)"
   "(RiscVInstruction.mk 160)"
   "(RiscVInstruction.mk 161)"
   "(RiscVInstruction.mk 162)"
   "(RiscVInstruction.mk 163)"
   "(RiscVInstruction.mk 164)"
   "(RiscVInstruction.mk 165)"
   "(RiscVInstruction.mk 166)"
   "(RiscVInstruction.mk 167)"
   "(RiscVInstruction.mk 168)"
   "(RiscVInstruction.mk 169)"
   "(RiscVInstruction.mk 170)"
   "(RiscVInstruction.mk 171)"
   "(RiscVInstruction.mk 172)"
   "(RiscVInstruction.mk 173)"
   "(RiscVInstruction.mk 174)"
   "(RiscVInstruction.mk 175)"
   "(RiscVInstruction.mk 176)"
   "(RiscVInstruction.mk 177)"
   "(RiscVInstruction.mk 178)"
   "(RiscVInstruction.mk 179)"
   "(RiscVInstruction.mk 180)"
   "(RiscVInstruction.mk 181)"
   "(RiscVInstruction.mk 182)"
   "(RiscVInstruction.mk 183)"
   "(RiscVInstruction.mk 184)"
   "(RiscVInstruction.mk 185)"
   "(RiscVInstruction.mk 186)"
   "(RiscVInstruction.mk 187)"
   "(RiscVInstruction.mk 188)"
   "(RiscVInstruction.mk 189)"
   "(RiscVInstruction.mk 190)"
   "(RiscVInstruction.mk 191)"
   "(RiscVInstruction.mk 192)"
   "(RiscVInstruction.mk 193)"
   "(RiscVInstruction.mk 194)"
   "(RiscVInstruction.mk 195)"
   "(RiscVInstruction.mk 196)"
   "(RiscVInstruction.mk 197)"
   "(RiscVInstruction.mk 198)"
   "(RiscVInstruction.mk 199)"
   "(RiscVInstruction.mk 200)"
   "(RiscVInstruction.mk 201)"
   "(RiscVInstruction.mk 202)"
   "(RiscVInstruction.mk 203)"
   "(RiscVInstruction.mk 204)"
   "(RiscVInstruction.mk 205)"
   "(RiscVInstruction.mk 206)"
   "(RiscVInstruction.mk 207)"
   "(RiscVInstruction.mk 208)"
   "(RiscVInstruction.mk 209)"
   "(RiscVInstruction.mk 210)"
   "(RiscVInstruction.mk 211)"
   "(RiscVInstruction.mk 212)"
   "(RiscVInstruction.mk 213)"
   "(RiscVInstruction.mk 214)"
   "(RiscVInstruction.mk 215)"
   "(RiscVInstruction.mk 216)"
   "(RiscVInstruction.mk 217)"
   "(RiscVInstruction.mk 218)"
   "(RiscVInstruction.mk 219)"
   "(RiscVInstruction.mk 220)"
   "(RiscVInstruction.mk 221)"
   "(RiscVInstruction.mk 222)"
   "(RiscVInstruction.mk 223)"
   "(RiscVInstruction.mk 224)"
   "(RiscVInstruction.mk 225)"
   "(RiscVInstruction.mk 226)"
   "(RiscVInstruction.mk 227)"
   "(RiscVInstruction.mk 228)"
   "(RiscVInstruction.mk 229)"
   "(RiscVInstruction.mk 230)"
   "(RiscVInstruction.mk 231)"
   "(RiscVInstruction.mk 232)"
   "(RiscVInstruction.mk 233)"
   "(RiscVInstruction.mk 234)"
   "(RiscVInstruction.mk 235)"
   "(RiscVInstruction.mk 236)"
   "(RiscVInstruction.mk 237)"
   "(RiscVInstruction.mk 238)"
   "(RiscVInstruction.mk 239)"
   "(RiscVInstruction.mk 240)"
   "(RiscVInstruction.mk 241)"
   "(RiscVInstruction.mk 242)"
   "(RiscVInstruction.mk 243)"
   "(RiscVInstruction.mk 244)"
   "(RiscVInstruction.mk 245)"
   "(RiscVInstruction.mk 246)"
   "(RiscVInstruction.mk 247)"
   "(RiscVInstruction.mk 248)"
   "(RiscVInstruction.mk 249)"
   "(RiscVInstruction.mk 250)"
   "(RiscVInstruction.mk 251)"
   "(RiscVInstruction.mk 252)"
   "(RiscVInstruction.mk 253)"
   "(RiscVInstruction.mk 254)"
   "(RiscVInstruction.mk 255)"
   "(RiscVInstruction.mk 256)"
   "(RiscVInstruction.mk 257)"
   "(RiscVInstruction.mk 258)"
   "(RiscVInstruction.mk 259)"
   "(RiscVInstruction.mk 260)"
   "(RiscVInstruction.mk 261)"
   "(RiscVInstruction.mk 262)"
   "(RiscVInstruction.mk 263)"
   "(RiscVInstruction.mk 264)"
   "(RiscVInstruction.mk 265)"
   "(RiscVInstruction.mk 266)"
   "(RiscVInstruction.mk 267)"
   "(RiscVInstruction.mk 268)"
   "(RiscVInstruction.mk 269)"
   "(RiscVInstruction.mk 270)"
   "(RiscVInstruction.mk 271)"
   "(RiscVInstruction.mk 272)"
   "(RiscVInstruction.mk 273)"
   "(RiscVInstruction.mk 274)"
   "(RiscVInstruction.mk 275)"
   "(RiscVInstruction.mk 276)"
   "(RiscVInstruction.mk 277)"
   "(RiscVInstruction.mk 278)"
   "(RiscVInstruction.mk 279)"
   "(RiscVInstruction.mk 280)"
   "(RiscVInstruction.mk 281)"
   "(RiscVInstruction.mk 282)"
   "(RiscVInstruction.mk 283)"
   "(RiscVInstruction.mk 284)"
   "(RiscVInstruction.mk 285)"
   "(RiscVInstruction.mk 286)"
   "(RiscVInstruction.mk 287)"
   "(RiscVInstruction.mk 288)"
   "(RiscVInstruction.mk 289)"
   "(RiscVInstruction.mk 290)"
   "(RiscVInstruction.mk 291)"
   "(RiscVInstruction.mk 292)"
   "(RiscVInstruction.mk 293)"
   "(RiscVInstruction.mk 294)"
   "(RiscVInstruction.mk 295)"
   "(RiscVInstruction.mk 296)"
   "(RiscVInstruction.mk 297)"
   "(RiscVInstruction.mk 298)"
   "(RiscVInstruction.mk 299)"
   "(RiscVInstruction.mk 300)"
   "(RiscVInstruction.mk 301)"
   "(RiscVInstruction.mk 302)"
   "(RiscVInstruction.mk 303)"
   "(RiscVInstruction.mk 304)"
   "(RiscVInstruction.mk 305)"
   "(RiscVInstruction.mk 306)"
   "(RiscVInstruction.mk 307)"
   "(RiscVInstruction.mk 308)"
   "(RiscVInstruction.mk 309)"
   "(RiscVInstruction.mk 310)"
   "(RiscVInstruction.mk 311)"
   "(RiscVInstruction.mk 312)"
   "(RiscVInstruction.mk 313)"
   "(RiscVInstruction.mk 314)"
   "(RiscVInstruction.mk 315)"
   "(RiscVInstruction.mk 316)"
   "(RiscVInstruction.mk 317)"
   "(RiscVInstruction.mk 318)"
   "(RiscVInstruction.mk 319)"
   "(RiscVInstruction.mk 320)"
   "(RiscVInstruction.mk 321)"
   "(RiscVInstruction.mk 322)"
   "(RiscVInstruction.mk 323)"
   "(RiscVInstruction.mk 324)"
   "(RiscVInstruction.mk 325)"
   "(RiscVInstruction.mk 326)"
   "(RiscVInstruction.mk 327)"
   "(RiscVInstruction.mk 328)"
   "(RiscVInstruction.mk 329)"
   "(RiscVInstruction.mk 330)"
   "(RiscVInstruction.mk 331)"
   "(RiscVInstruction.mk 332)"
   "(RiscVInstruction.mk 333)"
   "(RiscVInstruction.mk 334)"
   "(RiscVInstruction.mk 335)"
   "(RiscVInstruction.mk 336)"
   "(RiscVInstruction.mk 337)"
   "(RiscVInstruction.mk 338)"
   "(RiscVInstruction.mk 339)"
   "(RiscVInstruction.mk 340)"
   "(RiscVInstruction.mk 341)"
   "(RiscVInstruction.mk 342)"
   "(RiscVInstruction.mk 343)"
   "(RiscVInstruction.mk 344)"
   "(RiscVInstruction.mk 345)"
   "(RiscVInstruction.mk 346)"
   "(RiscVInstruction.mk 347)"
   "(RiscVInstruction.mk 348)"
   "(RiscVInstruction.mk 349)"
   "(RiscVInstruction.mk 350)"
   "(RiscVInstruction.mk 351)"
   "(RiscVInstruction.mk 352)"
   "(RiscVInstruction.mk 353)"
   "(RiscVInstruction.mk 354)"
   "(RiscVInstruction.mk 355)"
   "(RiscVInstruction.mk 356)"
   "(RiscVInstruction.mk 357)"
   "(RiscVInstruction.mk 358)"
   "(RiscVInstruction.mk 359)"
   "(RiscVInstruction.mk 360)"]
  "RiscVInstruction.match_".

(** sail-riscv leaves some functions as axioms (floating-point operations, LR/SC
    reservation tracking, randomness, terminal output). By default extraction
    turns each into a top-level [failwith], which raises as soon as the module
    is loaded and so breaks every user of the library, not just RISC-V. Make
    them fail only when actually called instead. *)
Extract Constant Riscv.rv64d.get_16_random_bits =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.get_16_random_bits)"")".
Extract Constant Riscv.rv64d.riscv_f16Add =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Add)"")".
Extract Constant Riscv.rv64d.riscv_f16Sub =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Sub)"")".
Extract Constant Riscv.rv64d.riscv_f16Mul =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Mul)"")".
Extract Constant Riscv.rv64d.riscv_f16Div =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Div)"")".
Extract Constant Riscv.rv64d.riscv_f32Add =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Add)"")".
Extract Constant Riscv.rv64d.riscv_f32Sub =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Sub)"")".
Extract Constant Riscv.rv64d.riscv_f32Mul =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Mul)"")".
Extract Constant Riscv.rv64d.riscv_f32Div =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Div)"")".
Extract Constant Riscv.rv64d.riscv_f64Add =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Add)"")".
Extract Constant Riscv.rv64d.riscv_f64Sub =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Sub)"")".
Extract Constant Riscv.rv64d.riscv_f64Mul =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Mul)"")".
Extract Constant Riscv.rv64d.riscv_f64Div =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Div)"")".
Extract Constant Riscv.rv64d.riscv_f16MulAdd =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16MulAdd)"")".
Extract Constant Riscv.rv64d.riscv_f32MulAdd =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32MulAdd)"")".
Extract Constant Riscv.rv64d.riscv_f64MulAdd =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64MulAdd)"")".
Extract Constant Riscv.rv64d.riscv_f16Sqrt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Sqrt)"")".
Extract Constant Riscv.rv64d.riscv_f32Sqrt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Sqrt)"")".
Extract Constant Riscv.rv64d.riscv_f64Sqrt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Sqrt)"")".
Extract Constant Riscv.rv64d.riscv_f16ToI32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16ToI32)"")".
Extract Constant Riscv.rv64d.riscv_f16ToUi32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16ToUi32)"")".
Extract Constant Riscv.rv64d.riscv_i32ToF16 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_i32ToF16)"")".
Extract Constant Riscv.rv64d.riscv_ui32ToF16 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_ui32ToF16)"")".
Extract Constant Riscv.rv64d.riscv_f16ToI64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16ToI64)"")".
Extract Constant Riscv.rv64d.riscv_f16ToUi64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16ToUi64)"")".
Extract Constant Riscv.rv64d.riscv_i64ToF16 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_i64ToF16)"")".
Extract Constant Riscv.rv64d.riscv_ui64ToF16 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_ui64ToF16)"")".
Extract Constant Riscv.rv64d.riscv_f32ToI32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32ToI32)"")".
Extract Constant Riscv.rv64d.riscv_f32ToUi32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32ToUi32)"")".
Extract Constant Riscv.rv64d.riscv_i32ToF32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_i32ToF32)"")".
Extract Constant Riscv.rv64d.riscv_ui32ToF32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_ui32ToF32)"")".
Extract Constant Riscv.rv64d.riscv_f32ToI64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32ToI64)"")".
Extract Constant Riscv.rv64d.riscv_f32ToUi64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32ToUi64)"")".
Extract Constant Riscv.rv64d.riscv_i64ToF32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_i64ToF32)"")".
Extract Constant Riscv.rv64d.riscv_ui64ToF32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_ui64ToF32)"")".
Extract Constant Riscv.rv64d.riscv_f64ToI32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64ToI32)"")".
Extract Constant Riscv.rv64d.riscv_f64ToUi32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64ToUi32)"")".
Extract Constant Riscv.rv64d.riscv_i32ToF64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_i32ToF64)"")".
Extract Constant Riscv.rv64d.riscv_ui32ToF64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_ui32ToF64)"")".
Extract Constant Riscv.rv64d.riscv_f64ToI64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64ToI64)"")".
Extract Constant Riscv.rv64d.riscv_f64ToUi64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64ToUi64)"")".
Extract Constant Riscv.rv64d.riscv_i64ToF64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_i64ToF64)"")".
Extract Constant Riscv.rv64d.riscv_ui64ToF64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_ui64ToF64)"")".
Extract Constant Riscv.rv64d.riscv_f16ToF32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16ToF32)"")".
Extract Constant Riscv.rv64d.riscv_f16ToF64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16ToF64)"")".
Extract Constant Riscv.rv64d.riscv_f32ToF64 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32ToF64)"")".
Extract Constant Riscv.rv64d.riscv_f32ToF16 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32ToF16)"")".
Extract Constant Riscv.rv64d.riscv_f64ToF16 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64ToF16)"")".
Extract Constant Riscv.rv64d.riscv_f64ToF32 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64ToF32)"")".
Extract Constant Riscv.rv64d.riscv_f32ToBF16 =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32ToBF16)"")".
Extract Constant Riscv.rv64d.riscv_f16Lt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Lt)"")".
Extract Constant Riscv.rv64d.riscv_f16Lt_quiet =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Lt_quiet)"")".
Extract Constant Riscv.rv64d.riscv_f16Le =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Le)"")".
Extract Constant Riscv.rv64d.riscv_f16Le_quiet =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Le_quiet)"")".
Extract Constant Riscv.rv64d.riscv_f16Eq =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16Eq)"")".
Extract Constant Riscv.rv64d.riscv_f32Lt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Lt)"")".
Extract Constant Riscv.rv64d.riscv_f32Lt_quiet =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Lt_quiet)"")".
Extract Constant Riscv.rv64d.riscv_f32Le =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Le)"")".
Extract Constant Riscv.rv64d.riscv_f32Le_quiet =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Le_quiet)"")".
Extract Constant Riscv.rv64d.riscv_f32Eq =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32Eq)"")".
Extract Constant Riscv.rv64d.riscv_f64Lt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Lt)"")".
Extract Constant Riscv.rv64d.riscv_f64Lt_quiet =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Lt_quiet)"")".
Extract Constant Riscv.rv64d.riscv_f64Le =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Le)"")".
Extract Constant Riscv.rv64d.riscv_f64Le_quiet =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Le_quiet)"")".
Extract Constant Riscv.rv64d.riscv_f64Eq =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64Eq)"")".
Extract Constant Riscv.rv64d.riscv_f16roundToInt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f16roundToInt)"")".
Extract Constant Riscv.rv64d.riscv_f32roundToInt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f32roundToInt)"")".
Extract Constant Riscv.rv64d.riscv_f64roundToInt =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.riscv_f64roundToInt)"")".
Extract Constant Riscv.rv64d.load_reservation =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.load_reservation)"")".
Extract Constant Riscv.rv64d.match_reservation =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.match_reservation)"")".
Extract Constant Riscv.rv64d.cancel_reservation =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.cancel_reservation)"")".
Extract Constant Riscv.rv64d.valid_reservation =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.valid_reservation)"")".
Extract Constant Riscv.rv64d.plat_term_write =>
  "(fun _ -> failwith ""AXIOM TO BE REALIZED (Riscv.rv64d.plat_term_write)"")".

(** * Actual extraction *)
(* DO NOT run this file in your editor. This will extract in the correct folder
   when dune does the extraction *)
Set Extraction Output Directory ".".

#[warnings="-extraction-remaining-implicit,-extraction-reserved-identifier"]
Separate Extraction
  Arm sail_tiny_arm_sem UMPromising_opmodel_pf VMPromising_opmodel_pf
  RiscVInst.RiscV sail_riscv_sem
  X86Inst.X86 sail_tiny_x86_sem x86_tso_opmodel x86_tso_opmodel_eager.
