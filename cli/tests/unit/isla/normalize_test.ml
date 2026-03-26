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

(** Unit tests for Isla.Normalize. *)

open OUnit2
open Isla.Assertion

let sample_ir arch : Isla.Ir.t =
  { arch;
    name = "Normalize";
    threads =
      [ { tid = 0;
          code = "MOV W1,#1";
          init = [("X0", Isla.Ir.Sym "x"); ("W2", Isla.Ir.Int (Z.of_int 3))]
        }
      ];
    symbolic = ["x"];
    locations = [("x", Isla.Ir.Int Z.zero)];
    expect = Isla.Ir.Sat;
    assertion =
      And
        ( Atom (CmpCst (Reg (0, "X1"), Eq, Z.one)),
          Or
            ( Atom (CmpLoc (Reg (0, "X3"), Eq, Mem "x")),
              And
                ( Atom (CmpCst (Reg (0, "W2"), Ne, Z.zero)),
                  Atom (CmpLoc (Reg (0, "W4"), Eq, Reg (1, "X5")))
                )
            )
        )
  }

let tests =
  "Isla.Normalize"
  >::: [ ("AArch64 init and assertion regs normalized"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let normalized = Isla.Normalize.apply (sample_ir Litmus.Arch_id.Arm) in
         let expected : Isla.Ir.t =
           { (sample_ir Litmus.Arch_id.Arm) with
             threads =
               [ { tid = 0;
                   code = "MOV W1,#1";
                   init =
                     [("R0", Isla.Ir.Sym "x"); ("R2", Isla.Ir.Int (Z.of_int 3))]
                 }
               ];
             assertion =
               And
                 ( Atom (CmpCst (Reg (0, "R1"), Eq, Z.one)),
                   Or
                     ( Atom (CmpLoc (Reg (0, "R3"), Eq, Mem "x")),
                       And
                         ( Atom (CmpCst (Reg (0, "R2"), Ne, Z.zero)),
                           Atom (CmpLoc (Reg (0, "R4"), Eq, Reg (1, "R5")))
                         )
                     )
                 )
           }
         in
         assert_equal expected normalized
         )
       ]

let () = run_test_tt_main tests
