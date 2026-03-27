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

(** Unit tests for Isla.Input. *)

open OUnit2
open Isla.Assertion

let simple_toml =
  Otoml.Parser.from_string
    {|
arch = "AArch64"
name = "MP"
symbolic = ["x", "y"]

[locations]
"x" = "0"
"y" = "0"

[thread.0]
init = { X0 = "x" }
code = """
  MOV W1,#1
  STR W1,[X0]
"""

[thread.1]
init = { X1 = "y", X2 = "x" }
code = """
  LDR W0,[X2]
  STR W0,[X1]
"""

[final]
expect = "sat"
assertion = "1:X0 = 1 & *y = 1"
|}

let t = Isla.Ir.of_toml simple_toml

let expected : Isla.Ir.t =
  { arch = Litmus.Arch_id.Arm;
    name = "MP";
    threads =
      [ { tid = 0;
          code = "MOV W1,#1\n  STR W1,[X0]";
          init = [("X0", Isla.Ir.Sym "x")]
        };
        { tid = 1;
          code = "LDR W0,[X2]\n  STR W0,[X1]";
          init = [("X1", Isla.Ir.Sym "y"); ("X2", Isla.Ir.Sym "x")]
        }
      ];
    symbolic = ["x"; "y"];
    locations = [("x", Isla.Ir.Int Z.zero); ("y", Isla.Ir.Int Z.zero)];
    expect = Isla.Ir.Sat;
    assertion =
      And
        ( Atom (CmpCst (Reg (1, "X0"), Eq, Z.one)),
          Atom (CmpCst (Mem "y", Eq, Z.one))
        )
  }

let tests = "Isla.Ir" >::: [("parse" >:: fun _ -> assert_equal expected t)]

let () = run_test_tt_main tests
