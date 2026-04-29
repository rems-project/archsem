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

(** Unit tests for Isla.Assembler. *)

open OUnit2

let arm_cases =
  [ ("MOV W1,#42", "MOV W1, #42", "\x41\x05\x80\x52");
    ( "branch with label resolves",
      "\tCBNZ W0,LC00\nLC00:\n\tISB",
      "\x20\x00\x00\x35\xdf\x3f\x03\xd5"
    );
    ( "2 instructions",
      "MOV X0, #1\nSTR X0, [X1]",
      "\x20\x00\x80\xd2\x20\x00\x00\xf9"
    )
  ]

let x86_cases =
  [ ("nop", "nop", "\x90");
    ("xorq", "xorq %rcx, %rax", "\x48\x31\xc8");
    ("2 instructions", "nop\nretq", "\x90\xc3")
  ]

let cases ~name ~setup xs =
  name
  >::: List.map
         (fun (label, input, expected) ->
            label
            >:: fun _ ->
            setup ();
            assert_equal (Bytes.of_string expected) (Isla.Assembler.assemble input)
          )
         xs

let () =
  run_test_tt_main
    ("Isla.Assembler"
    >::: [ cases ~name:"ARM" ~setup:Test_utils.setup_arm arm_cases;
           cases ~name:"X86" ~setup:Test_utils.setup_x86 x86_cases
         ]
    )
