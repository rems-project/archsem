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

(** Unit tests for Isla.Assertion. *)

open OUnit2
open Isla.Assertion

let n = Z.of_int

let assertion_of path = (Isla.Ir.of_toml (Otoml.Parser.from_file path)).assertion

let tests =
  "Isla.Assertion"
  >::: [ ("ARM MP: register conjunction"
         >:: fun _ ->
         assert_equal
           (And
              ( Atom (CmpCst (Reg (1, "X0"), Eq, Z.one)),
                Atom (CmpCst (Reg (1, "X2"), Eq, Z.zero))
              )
           )
           (assertion_of "../../arm/um/MP.litmus.toml")
         );
         ("ARM EOR: hex value"
         >:: fun _ ->
         assert_equal
           (Atom (CmpCst (Reg (0, "X0"), Eq, n 0x110)))
           (assertion_of "../../arm/seq/EOR.litmus.toml")
         );
         ("X86 R_PO_MFENCE: memory + register"
         >:: fun _ ->
         assert_equal
           (And
              ( Atom (CmpCst (Mem "y", Eq, n 2)),
                Atom (CmpCst (Reg (1, "RAX"), Eq, Z.zero))
              )
           )
           (assertion_of "../../x86/um/R_PO_MFENCE.litmus.toml")
         );
         ("X86 IRIW: 4-way conjunction"
         >:: fun _ ->
         let rec count_atoms = function
           | And (l, r) -> count_atoms l + count_atoms r
           | Atom _ -> 1
           | _ -> 0
         in
         assert_equal 4
           (count_atoms (assertion_of "../../x86/um/IRIW.litmus.toml"))
         );
         ("register eq symbol (inline)"
         >:: fun _ ->
         assert_equal
           (Atom (CmpLoc (Reg (0, "X0"), Eq, Mem "x")))
           (Isla.Ir.parse_assertion_expr "0:X0 = x")
         );
         ("negation (inline)"
         >:: fun _ ->
         assert_equal
           (Not (Atom (CmpCst (Reg (1, "X0"), Eq, Z.one))))
           (Isla.Ir.parse_assertion_expr "~(1:X0 = 1)")
         );
         ("false (inline)"
         >:: fun _ -> assert_equal False (Isla.Ir.parse_assertion_expr "false")
         )
       ]

let () = run_test_tt_main tests
