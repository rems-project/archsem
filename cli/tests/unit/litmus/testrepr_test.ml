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

(** Unit tests for litmus test parsing, test representations, and execution. *)

open OUnit2
open Litmus
open Testrepr
open Test_utils
module Arm = Archsem.Arm
module ArmRunner = Runner.Make (Arm)

let i v = Archsem.RegValGen.Number (Z.of_int v)

let find_reg name regs = List.assoc name regs

let find_code (t : Testrepr.t) =
  List.filter (fun (b : memory_block) -> b.kind = Code) t.memory

let find_data (t : Testrepr.t) =
  List.filter (fun (b : memory_block) -> b.kind = Data) t.memory

(** {1 Parsed Test Fixtures} *)

let mp = parse_file "../arm/um/MP.archsem.toml"

(** {1 Parser Coverage} *)

let parse_tests =
  "parse"
  >::: [ ("MP: two threads with different PCs"
         >:: fun _ ->
         assert_equal "Arm" mp.arch;
         assert_equal "MP" mp.name;
         assert_equal (i 0x500) (find_reg "_PC" (List.nth mp.registers 0));
         assert_equal (i 0x600) (find_reg "_PC" (List.nth mp.registers 1))
         );
         ("MP: code blocks addresses and bytes"
         >:: fun _ ->
         let code = find_code mp in
         let by_addr =
           List.sort
             (fun (a : memory_block) (b : memory_block) -> compare a.addr b.addr)
             code
         in
         let t0 = List.nth by_addr 0 in
         let t1 = List.nth by_addr 1 in
         assert_equal 0x500 t0.addr;
         assert_equal 4 t0.step;
         (* STR X0,[X1]; STR X2,[X3] *)
         assert_equal (Bytes.of_string "\x22\x68\x20\xf8\x85\x68\x23\xf8") t0.data;
         assert_equal 0x600 t1.addr;
         assert_equal 4 t1.step;
         (* LDR X0,[X1]; LDR X2,[X3] *)
         assert_equal (Bytes.of_string "\x85\x68\x63\xf8\x22\x68\x60\xf8") t1.data
         );
         ("MP: data blocks parsed"
         >:: fun _ ->
         let data = find_data mp in
         List.iter
           (fun (b : memory_block) ->
              assert_equal 8 b.step;
              assert_equal 8 (Bytes.length b.data)
            )
           data
         );
         ("MP: term_cond for both threads"
         >:: fun _ ->
         assert_equal (i 0x508) (find_reg "_PC" (List.nth mp.term_cond 0));
         assert_equal (i 0x608) (find_reg "_PC" (List.nth mp.term_cond 1))
         );
         ("MP: multiple outcome formats all parsed"
         >:: fun _ ->
         (* MP.archsem.toml has 4 outcomes in different TOML formats *)
         assert_bool "has multiple finals" (List.length mp.finals >= 4)
         )
       ]

(** {1 ArchState Conversion And Execution} *)

let execution_tests =
  "execution"
  >::: [ ("MP Expected with ump model"
         >:: fun _ ->
         setup_arm ();
         let (result, _msgs) =
           ArmRunner.run_testrepr Arm.(umProm_model tiny_isa) mp
         in
         assert_equal Runner.Expected result
         )
       ]

let () = run_test_tt_main ("litmus_testrepr" >::: [parse_tests; execution_tests])
