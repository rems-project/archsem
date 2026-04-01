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

(** Unit tests for Isla.Ir — verify IR parsing from existing test files. *)

open OUnit2
open Isla.Assertion

let find_init reg (thread : Isla.Ir.thread) = List.assoc reg thread.init

let arm_mp = Isla.Ir.of_toml (Otoml.Parser.from_file "../../arm/um/MP.litmus.toml")

let tests =
  "Isla.Ir"
  >::: [ ("ARM MP: arch, name, expect"
         >:: fun _ ->
         let t = arm_mp in
         assert_equal Litmus.Arch_id.Arm t.arch;
         assert_equal "MP" t.name;
         assert_equal Isla.Ir.Sat t.expect
         );
         ("ARM MP: symbolic"
         >:: fun _ ->
         let t = arm_mp in
         assert_equal ["x"; "y"] t.symbolic
         );
         ("ARM MP: thread0 init registers"
         >:: fun _ ->
         let t = arm_mp in
         let t0 = List.nth t.threads 0 in
         assert_equal 0 t0.tid;
         assert_equal (Isla.Ir.Int (Z.of_int 1)) (find_init "X0" t0);
         assert_equal (Isla.Ir.Sym "x") (find_init "X1" t0);
         assert_equal (Isla.Ir.Int (Z.of_int 1)) (find_init "X2" t0);
         assert_equal (Isla.Ir.Sym "y") (find_init "X3" t0)
         );
         ("ARM MP: thread1 init registers"
         >:: fun _ ->
         let t = arm_mp in
         let t1 = List.nth t.threads 1 in
         assert_equal 1 t1.tid;
         assert_equal (Isla.Ir.Sym "y") (find_init "X1" t1);
         assert_equal (Isla.Ir.Sym "x") (find_init "X3" t1)
         );
         ("ARM MP: thread code"
         >:: fun _ ->
         assert_equal "STR X0,[X1]\n\tSTR X2,[X3]"
           (List.nth arm_mp.threads 0).code;
         assert_equal "LDR X0,[X1]\n\tLDR X2,[X3]"
           (List.nth arm_mp.threads 1).code
         );
         ("ARM MP: assertion = 1:X0 = 1 & 1:X2 = 0"
         >:: fun _ ->
         match arm_mp.assertion with
         | And
             ( Atom (CmpCst (Reg (1, "X0"), Eq, v1)),
               Atom (CmpCst (Reg (1, "X2"), Eq, v2))
             ) ->
             assert_equal Z.one v1; assert_equal Z.zero v2
         | _ -> assert_failure "expected 1:X0 = 1 & 1:X2 = 0"
         )
       ]

let () = run_test_tt_main tests
