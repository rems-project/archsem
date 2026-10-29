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
open Litmus.Assertion
open Isla.Term

let n = Z.of_int

let reg tid r = Base (Reg (tid, r))

let mem s = Base (Mem s)

let mem_addr addr = Base (MemAddr addr)

let sym s = Sym s

let cst v = Const v

let fn name args = Fn (name, args)

let kwfn name args = KwFn (name, args)

let extract v hi lo = Extract (v, n hi, n lo)

let parse = Isla.Ir.parse_assertion_expr

let parse_cases =
  [ ("int constant", "0:X0 = 1", Atom (CmpCst (reg 0 "X0", cst Z.one)));
    ("hex constant", "0:X0 = 0x2a", Atom (CmpCst (reg 0 "X0", cst (n 42))));
    ("memory location", "*x = 2", Atom (CmpCst (mem "x", cst (n 2))));
    ("symbol on rhs", "0:X0 = x", Atom (CmpCst (reg 0 "X0", sym "x")));
    ("register on rhs", "0:X0 = 2:X2", Atom (CmpLoc (reg 0 "X0", reg 2 "X2")));
    ("memory on rhs", "0:X0 = *x", Atom (CmpLoc (reg 0 "X0", mem "x")));
    ( "function on rhs",
      "0:X0 = bvor(0x28, 0x2)",
      Atom (CmpCst (reg 0 "X0", fn "bvor" [cst (n 0x28); cst (n 0x2)]))
    );
    ( "PTE address location",
      "*pte3(x, page_table_base) = mkdesc3(oa=y)",
      Atom
        (CmpCst
           ( mem_addr (fn "pte3" [sym "x"; sym "page_table_base"]),
             kwfn "mkdesc3" [("oa", sym "y")]
           )
        )
    );
    ("negation", "~(1:X0 = 1)", Not (Atom (CmpCst (reg 1 "X0", cst Z.one))));
    ( "conjunction",
      "1:X0 = 1 & 2:X0 = 0",
      And
        [ Atom (CmpCst (reg 1 "X0", cst Z.one));
          Atom (CmpCst (reg 2 "X0", cst Z.zero))
        ]
    );
    ("false", "false", False);
    ( "bit slice",
      "0:X0 = x[15..8]",
      Atom (CmpCst (reg 0 "X0", extract (sym "x") 15 8))
    );
    ( "single bit",
      "0:X0 = x[3]",
      Atom (CmpCst (reg 0 "X0", extract (sym "x") 3 3))
    );
    ( "bit slice binds tighter than +",
      "0:X0 = a + b[3..0]",
      Atom (CmpCst (reg 0 "X0", Binary (sym "a", Add, extract (sym "b") 3 0)))
    );
    ( "bit slice of function call",
      "0:X0 = f(a)[7..0]",
      Atom (CmpCst (reg 0 "X0", extract (fn "f" [sym "a"]) 7 0))
    );
    ( "register slice location",
      "0:R0[15..8] = 1",
      Atom (CmpCst (Slice (Reg (0, "R0"), n 15, n 8), cst Z.one))
    );
    ( "register bit location",
      "0:R0[3] = 1",
      Atom (CmpCst (Slice (Reg (0, "R0"), n 3, n 3), cst Z.one))
    );
    ( "memory slice location",
      "(*x)[15..8] = 1",
      Atom (CmpCst (Slice (Mem "x", n 15, n 8), cst Z.one))
    );
    ( "slice location on rhs",
      "0:X0 = 1:X1[3..0]",
      Atom (CmpLoc (reg 0 "X0", Slice (Reg (1, "X1"), n 3, n 0)))
    );
    ( "memory slice location on rhs",
      "0:X0 = (*x)[7..0]",
      Atom (CmpLoc (reg 0 "X0", Slice (Mem "x", n 7, n 0)))
    )
  ]

let parse_error_cases =
  [ ("register dereference", "*0:X0 = 4");
    ("symbol lhs", "x = 1");
    ("empty bit slice", "0:X0 = x[]");
    ("missing low bit index", "0:X0 = x[1..]");
    ("symbolic bit index", "0:X0 = x[a..0]");
    ("unparenthesized chained bit slices", "0:X0 = x[15..8][3]");
    ("unparenthesized negated bit slice", "0:X0 = -x[7..0]");
    ("unparenthesized memory slice location", "*x[7..0] = 1");
    ("parenthesized register location", "(0:R0)[3] = 1");
    ("chained register slices", "0:R0[15..8][3] = 1")
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
           error_cases ~name:"parse-errors" ~run:parse parse_error_cases
         ]
    )
