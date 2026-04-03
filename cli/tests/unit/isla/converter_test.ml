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

(** Unit tests for Isla.Converter. *)

open Litmus
open OUnit2
module Arm = Archsem.Arm
module ArmRunner = Runner.Make (Arm)
module X86 = Archsem.X86
module X86Runner = Runner.Make (X86)
module RegValGen = Archsem.RegValGen

let convert_file path =
  Otoml.Parser.from_file path |> Isla.Ir.of_toml |> Isla.Normalize.apply
  |> Isla.Converter.to_testrepr

let tests =
  "Isla.Converter"
  >::: [ ("cross-format: ARM MP litmus vs archsem same result"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let from_isla = convert_file "../../arm/um/MP.litmus.toml" in
         let from_archsem = Test_utils.parse_file "../arm/um/MP.archsem.toml" in
         let model = Arm.(umProm_model tiny_isa) in
         let (r1, _) = ArmRunner.run_testrepr model from_isla in
         let (r2, _) = ArmRunner.run_testrepr model from_archsem in
         assert_equal ~msg:"litmus and archsem should produce same result" r1 r2
         );
         ("e2e: ARM EOR seq"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let t = convert_file "../../arm/seq/EOR.litmus.toml" in
         let (result, _msgs) =
           ArmRunner.run_testrepr Arm.(seq_model tiny_isa) t
         in
         assert_equal Runner.Expected result
         );
         ("e2e: ARM MP ump"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let t = convert_file "../../arm/um/MP.litmus.toml" in
         let (result, _msgs) =
           ArmRunner.run_testrepr Arm.(umProm_model tiny_isa) t
         in
         assert_equal Runner.Expected result
         )
       ]

let () = run_test_tt_main tests
