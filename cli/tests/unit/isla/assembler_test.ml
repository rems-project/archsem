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
open Isla.Assembler

let make_input ?(symbols = []) sections : assembly_input = {sections; symbols}

let section ?(fixed_addr = None) name code : section = {name; code; fixed_addr}

let sym name size : data_symbol = {name; init_bytes = Bytes.make size '\x00'}

let find_section name (result : assembly_result) =
  List.find (fun (s : linked_section) -> s.name = name) result.sections

let test_assemble_single_thread _ =
  Test_utils.setup_arm ();
  let input =
    make_input ~symbols:[sym "x" 8] [section "thread0" "\tMOV W1, #42\n"]
  in
  let result = assemble input in
  let x_addr = resolve_symbol result "x" in
  assert_bool "x address > 0" (x_addr > 0);
  let thread0 = find_section "thread0" result in
  assert_equal ~printer:string_of_int 4 (Bytes.length thread0.data)

let test_assemble_multiple_threads _ =
  Test_utils.setup_arm ();
  let input =
    make_input
      [ section "thread0" "\tMOV W1, #1\n";
        section "thread1" "\tMOV W2, #2\n\tMOV W3, #3\n"
      ]
  in
  let result = assemble input in
  let t0 = find_section "thread0" result in
  let t1 = find_section "thread1" result in
  assert_equal ~printer:string_of_int ~msg:"thread0 size" 4 (Bytes.length t0.data);
  assert_equal ~printer:string_of_int ~msg:"thread1 size" 8 (Bytes.length t1.data);
  assert_bool "different addresses" (t0.addr <> t1.addr)

let test_assemble_multiple_symbols _ =
  Test_utils.setup_arm ();
  let input =
    make_input ~symbols:[sym "x" 8; sym "y" 8] [section "thread0" "\tNOP\n"]
  in
  let result = assemble input in
  let x_addr = resolve_symbol result "x" in
  let y_addr = resolve_symbol result "y" in
  assert_bool "different addresses" (x_addr <> y_addr)

let test_assemble_no_symbols _ =
  Test_utils.setup_arm ();
  let input = make_input [section "thread0" "\tNOP\n"] in
  let result = assemble input in
  assert_equal ~msg:"0 data" 0 (List.length result.data);
  let t0 = find_section "thread0" result in
  assert_equal ~printer:string_of_int ~msg:"NOP = 4 bytes" 4 (Bytes.length t0.data)

let test_assemble_fixed_addr _ =
  Test_utils.setup_arm ();
  let input =
    make_input
      [ section ~fixed_addr:(Some 0x10000) "handler0" "\tRET\n";
        section "thread0" "\tMOV W1, #1\n"
      ]
  in
  let result = assemble input in
  let handler = find_section "handler0" result in
  assert_equal ~printer:string_of_int ~msg:"handler0 addr" 0x10000 handler.addr;
  assert_equal ~printer:string_of_int ~msg:"handler0 size" 4
    (Bytes.length handler.data)

let test_resolve_unknown_raises _ =
  Test_utils.setup_arm ();
  let input = make_input [section "thread0" "\tNOP\n"] in
  let result = assemble input in
  assert_raises (Failure "assembler: symbol \"nonexistent\" not found") (fun () ->
    resolve_symbol result "nonexistent"
  )

let tests =
  "Isla.Assembler"
  >::: [ "single thread + symbol" >:: test_assemble_single_thread;
         "multiple threads" >:: test_assemble_multiple_threads;
         "multiple symbols" >:: test_assemble_multiple_symbols;
         "no symbols" >:: test_assemble_no_symbols;
         "fixed-addr section" >:: test_assemble_fixed_addr;
         "resolve unknown raises" >:: test_resolve_unknown_raises
       ]

let () = run_test_tt_main tests
