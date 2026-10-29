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

(** Unit tests for Isla.Term printing. *)

open OUnit2

let parse s = Isla.Ir.parse_term (Litmus.Toml.TomlString s)

(** Each case is an input term and how it is printed *)
let print_cases =
  [ ("small constant", "5", "5");
    ("hex constant", "0x1234", "0x1234");
    ("negative constant", "-0x20", "-0x20");
    ("symbol", "x", "x");
    ("symbol with colon", "x:", "x");
    ("nullary function", "f()", "f()");
    ("function", "bvor(x, 0x10)", "bvor(x, 0x10)");
    ("keyword function", "mkdesc3(oa=y, af = 1)", "mkdesc3(oa = y, af = 1)");
    ("function of compound terms", "f(a + b, c | d)", "f(a + b, c | d)");
    ("negation", "-x", "-x");
    ("negation of sum", "-(a + b)", "-(a + b)");
    ("double negation", "-(-x)", "-(-x)");
    ("bit slice", "x[15..8]", "x[15..8]");
    ("single bit", "x[3]", "x[3]");
    ("single bit range", "x[3..3]", "x[3]");
    ("chained bit slices", "(x[15..8])[3]", "(x[15..8])[3]");
    ("bit slice of sum", "(a + b)[7..0]", "(a + b)[7..0]");
    ("bit slice of negation", "(-x)[7..0]", "(-x)[7..0]");
    ("negation of bit slice", "-(x[7..0])", "-(x[7..0])");
    ("bit slice of negative constant", "(-5)[3..0]", "(-5)[3..0]");
    ("left associative sum", "a + b + c", "a + b + c");
    ("right nested sum", "a + (b + c)", "a + (b + c)");
    ("right nested difference", "a - (b - c)", "a - (b - c)");
    ("redundant parentheses", "((a) + (b))", "a + b");
    ("sum of negations", "-a + -b", "-a + -b");
    ("difference of negative constant", "a - -5", "a - -5");
    ("sum of bit slices", "a[3..0] + b[3]", "a[3..0] + b[3]");
    ("or of and", "a | b & c", "a | b & c");
    ("and of or", "(a | b) & c", "(a | b) & c");
    ("and of sum", "(a + b) & c", "a + b & c");
    ("sum of and", "a + (b & c)", "a + (b & c)")
  ]

let print_tests =
  "print"
  >::: List.map
         (fun (label, input, expected) ->
            label
            >:: fun _ ->
            assert_equal ~printer:Fun.id expected
              (Isla.Term.to_string (parse input))
          )
         print_cases

let round_trip_tests =
  "round-trip"
  >::: List.map
         (fun (label, input, _) ->
            label
            >:: fun _ ->
            let term = parse input in
            assert_equal ~printer:Isla.Term.to_string term
              (parse (Isla.Term.to_string term))
          )
         print_cases

let () = run_test_tt_main ("Isla.Term" >::: [print_tests; round_trip_tests])
