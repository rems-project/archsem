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

(** Unit tests for Isla.Symbols. *)

open OUnit2

let tests =
  "Isla.Symbols"
  >::: [ ("empty table resolves nothing"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         assert_equal None (Isla.Symbols.resolve_opt s0 "x")
         );
         ("alloc_data returns address"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         let addr = Isla.Symbols.resolve_or_alloc s0 "x" in
         assert_equal 0x500 addr
         );
         ("resolve after alloc"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         Isla.Symbols.alloc_sym s0 "x";
         assert_equal 0x500 (Isla.Symbols.resolve s0 "x")
         );
         ("first alloc unchanged after second"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         let a1 = Isla.Symbols.resolve_or_alloc s0 "x" in
         Isla.Symbols.alloc_sym s0 "y";
         assert_equal a1 (Isla.Symbols.resolve s0 "x")
         );
         ("duplicate alloc returns same address"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         let a1 = Isla.Symbols.resolve_or_alloc s0 "x" in
         let a2 = Isla.Symbols.resolve_or_alloc s0 "x" in
         assert_equal a1 a2
         )
       ]

let () = run_test_tt_main tests
