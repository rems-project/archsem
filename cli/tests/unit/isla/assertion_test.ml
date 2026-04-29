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
open Isla.Term

let n = Z.of_int

let reg tid r = Reg (tid, r)

let mem s = Mem s

let sym s = Sym s

let cst v = Const v

let parse = Isla.Ir.parse_assertion_expr

let parse_cases =
  [ ("int constant", "0:X0 = 1", Atom (CmpTerm (reg 0 "X0", Eq, cst Z.one)));
    ("hex constant", "0:X0 = 0x2a", Atom (CmpTerm (reg 0 "X0", Eq, cst (n 42))));
    ("memory location", "*x = 2", Atom (CmpTerm (mem "x", Eq, cst (n 2))));
    ("symbol on rhs", "0:X0 = x", Atom (CmpTerm (reg 0 "X0", Eq, sym "x")));
    ("register on rhs", "0:X0 = 2:X2", Atom (CmpLoc (reg 0 "X0", Eq, reg 2 "X2")));
    ("memory on rhs", "0:X0 = *x", Atom (CmpLoc (reg 0 "X0", Eq, mem "x")));
    ("negation", "~(1:X0 = 1)", Not (Atom (CmpTerm (reg 1 "X0", Eq, cst Z.one))));
    ( "conjunction",
      "1:X0 = 1 & 2:X0 = 0",
      And
        ( Atom (CmpTerm (reg 1 "X0", Eq, cst Z.one)),
          Atom (CmpTerm (reg 2 "X0", Eq, cst Z.zero))
        )
    );
    ("false", "false", False)
  ]

let parse_error_cases =
  [("register dereference", "*0:X0 = 4"); ("symbol lhs", "x = 1")]

(* Atoms used to build expected DNF results. *)
let a = CmpTerm (reg 0 "X0", Eq, cst Z.zero)

let b = CmpTerm (reg 0 "X0", Eq, cst Z.one)

let c = CmpTerm (reg 1 "X0", Eq, cst Z.zero)

let d = CmpTerm (reg 1 "X0", Eq, cst Z.one)

let na = CmpTerm (reg 0 "X0", Ne, cst Z.zero)

let nb = CmpTerm (reg 0 "X0", Ne, cst Z.one)

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

let error_cases ~name ~run xs =
  name
  >::: List.map
         (fun (label, input) ->
            label
            >:: fun _ ->
            match run input with
            | exception Litmus.Toml.Path_error _ -> ()
            | _ -> assert_failure ("expected parse error for: " ^ input)
          )
         xs

let () =
  run_test_tt_main
    ("Isla.Assertion"
    >::: [ cases ~name:"parse" ~run:parse parse_cases;
           error_cases ~name:"parse-errors" ~run:parse parse_error_cases;
           cases ~name:"to_dnf" ~run:to_dnf dnf_cases
         ]
    )
