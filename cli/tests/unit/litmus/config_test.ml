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

(** Unit tests for Config. *)

open OUnit2
open Litmus

let default_config_tests =
  "default config"
  >::: [ ("finds default Arm config path"
         >:: fun _ ->
         let path = Config.default_path_for_arch Arch_id.Arm in
         assert_bool "expected an Arm config path" (Option.is_some path)
         );
         ("finds default X86 config path"
         >:: fun _ ->
         let path = Config.default_path_for_arch Arch_id.X86 in
         assert_bool "expected an X86 config path" (Option.is_some path)
         );
         ("AArch64 resolves to Arm config path"
         >:: fun _ ->
         let path = Config.default_path_for_arch (Arch_id.of_string "AArch64") in
         assert_bool "expected an Arm config path for AArch64"
           (Option.is_some path)
         );
         ("unknown architecture is rejected"
         >:: fun _ ->
         assert_raises (Failure "unknown architecture: RISCV") (fun () ->
           ignore (Arch_id.of_string "RISCV")
         )
         );
         ("loads built-in Arm config"
         >:: fun _ ->
         Test_utils.setup_arm ();
         assert_equal 1000 (Config.get_fuel ())
         );
         ("loads built-in X86 config"
         >:: fun _ ->
         Test_utils.setup_x86 ();
         assert_equal 1000 (Config.get_fuel ())
         )
       ]

let () = run_test_tt_main ("litmus_config" >::: [default_config_tests])
