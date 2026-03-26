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

let parse_string s =
  let toml =
    Otoml.Parser.from_string
      (Printf.sprintf
         {|
arch = "AArch64"

[thread.0]
code = "NOP"

[final]
assertion = %S
|} s
      )
  in
  (Isla.Ir.of_toml toml).assertion

let assert_parses_as source expected = assert_equal expected (parse_string source)

let tests =
  "Isla.Assertion"
  >::: [ ("parse register eq"
         >:: fun _ ->
         assert_parses_as "1:X0 = 1" (Atom (CmpCst (Reg (1, "X0"), Eq, Z.one)))
         );
         ("parse conjunction"
         >:: fun _ ->
         assert_parses_as "1:X0 = 1 & 2:X0 = 0"
           (And
              ( Atom (CmpCst (Reg (1, "X0"), Eq, Z.one)),
                Atom (CmpCst (Reg (2, "X0"), Eq, Z.zero))
              )
           )
         );
         ("parse false" >:: fun _ -> assert_parses_as "false" False);
         ("parse memory"
         >:: fun _ -> assert_parses_as "*x = 2" (Atom (CmpCst (Mem "x", Eq, n 2)))
         );
         ("parse negation"
         >:: fun _ ->
         assert_parses_as "~(1:X0 = 1)"
           (Not (Atom (CmpCst (Reg (1, "X0"), Eq, Z.one))))
         );
         ("parse hex values"
         >:: fun _ ->
         assert_parses_as "0:X0 = 0x2a" (Atom (CmpCst (Reg (0, "X0"), Eq, n 42)))
         );
         ("parse register equals symbol"
         >:: fun _ ->
         assert_parses_as "0:X0 = x" (Atom (CmpLoc (Reg (0, "X0"), Eq, Mem "x")))
         )
       ]

let () = run_test_tt_main tests
