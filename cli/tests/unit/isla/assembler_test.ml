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

(** Unit tests for Isla.Assembler. *)

open OUnit2

let tests =
  "Isla.Assembler"
  >::: [ ("assemble ARM: 4 bytes"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let result = Isla.Assembler.assemble "MOV W1, #42" in
         assert_equal 4 (Bytes.length result)
         );
         ("assemble ARM: MOV W1,#42 bytes"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let result = Isla.Assembler.assemble "MOV W1, #42" in
         assert_equal (Bytes.of_string "\x41\x05\x80\x52") result
         );
         ("assemble ARM: branch with label resolves"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let result = Isla.Assembler.assemble "\tCBNZ W0,LC00\nLC00:\n\tISB" in
         assert_equal (Bytes.of_string "\x20\x00\x00\x35\xdf\x3f\x03\xd5") result
         );
         ("assemble ARM: 2 instructions bytes"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let result = Isla.Assembler.assemble "MOV X0, #1\nSTR X0, [X1]" in
         assert_equal (Bytes.of_string "\x20\x00\x80\xd2\x20\x00\x00\xf9") result
         );
         ("assemble X86: nop"
         >:: fun _ ->
         Test_utils.setup_x86 ();
         let result = Isla.Assembler.assemble "nop" in
         assert_equal (Bytes.of_string "\x90") result
         );
         ("assemble X86: xorq bytes"
         >:: fun _ ->
         Test_utils.setup_x86 ();
         let result = Isla.Assembler.assemble "xorq %rcx, %rax" in
         assert_equal (Bytes.of_string "\x48\x31\xc8") result
         );
         ("assemble X86: 2 instructions"
         >:: fun _ ->
         Test_utils.setup_x86 ();
         let result = Isla.Assembler.assemble "nop\nretq" in
         assert_equal (Bytes.of_string "\x90\xc3") result
         )
       ]

let () = run_test_tt_main tests
