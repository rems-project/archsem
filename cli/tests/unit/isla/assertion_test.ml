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

(** Unit tests for Isla.Assertion. *)

open OUnit2
open Isla.Assertion

let n = Z.of_int

let parse = Isla.Ir.parse_assertion_expr

let parse_cases =
  [ ("int constant", "0:X0 = 1", Atom (CmpCst (Reg (0, "X0"), Eq, Z.one)));
    ("hex constant", "0:X0 = 0x2a", Atom (CmpCst (Reg (0, "X0"), Eq, n 42)));
    ("memory location", "*x = 2", Atom (CmpCst (Mem "x", Eq, n 2)));
    ( "symbol on rhs (CmpLoc)",
      "0:X0 = x",
      Atom (CmpLoc (Reg (0, "X0"), Eq, Mem "x"))
    );
    ("negation", "~(1:X0 = 1)", Not (Atom (CmpCst (Reg (1, "X0"), Eq, Z.one))));
    ( "conjunction",
      "1:X0 = 1 & 2:X0 = 0",
      And
        ( Atom (CmpCst (Reg (1, "X0"), Eq, Z.one)),
          Atom (CmpCst (Reg (2, "X0"), Eq, Z.zero))
        )
    );
    ("false", "false", False)
  ]

(* Atoms used to build expected DNF results. *)
let a = CmpCst (Reg (0, "X0"), Eq, Z.zero)

let b = CmpCst (Reg (0, "X0"), Eq, Z.one)

let c = CmpCst (Reg (1, "X0"), Eq, Z.zero)

let d = CmpCst (Reg (1, "X0"), Eq, Z.one)

let na = CmpCst (Reg (0, "X0"), Ne, Z.zero)

let nb = CmpCst (Reg (0, "X0"), Ne, Z.one)

let dnf_cases =
  [ ("atom", Atom a, [[a]]);
    ("true is one empty clause", True, [[]]);
    ("false is no clauses", False, []);
    (* ~(A & B) = ~A | ~B — exercises Not, And, op-flip *)
    ("De Morgan over And", Not (And (Atom a, Atom b)), [[na]; [nb]]);
    (* (A | B) & (C | D) — cartesian product distribution *)
    ( "And-of-Or distributes",
      And (Or (Atom a, Atom b), Or (Atom c, Atom d)),
      [[a; c]; [a; d]; [b; c]; [b; d]]
    );
    ("double negation cancels", Not (Not (Atom a)), [[a]])
  ]

let cases ~name ~run xs =
  name
  >::: List.map
         (fun (label, input, expected) ->
            label >:: fun _ -> assert_equal expected (run input)
          )
         xs

let () =
  run_test_tt_main
    ("Isla.Assertion"
    >::: [ cases ~name:"parse" ~run:parse parse_cases;
           cases ~name:"to_dnf" ~run:to_dnf dnf_cases
         ]
    )
