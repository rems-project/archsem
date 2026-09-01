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

open OUnit2

let parse_binding input =
  let lexbuf = Lexing.from_string input in
  Isla.Parser.binding Isla.Lexer.token lexbuf

let eval_binding input =
  Isla.Term.eval
    ~lookup_addr:(fun name -> failwith ("unexpected symbol: " ^ name))
    (parse_binding input)

let test_ttbr_helper _ =
  assert_equal
    (Z.of_string "0x0002000000300000")
    (eval_binding "ttbr(asid=0x2, base=0x300000)");
  assert_equal
    (Z.of_string "0x0001000000280000")
    (eval_binding "ttbr(vmid=0x1, base=0x280000)")

let test_ttbr_helper_validation _ =
  assert_raises (Failure "function: ttbr: expected exactly one of asid or vmid")
    (fun () -> eval_binding "ttbr(base=0x280000)" |> ignore
  );
  assert_raises (Failure "function: ttbr: argument asid does not fit in 16 bits")
    (fun () -> eval_binding "ttbr(asid=0x10000, base=0x280000)" |> ignore
  );
  assert_raises (Failure "function: ttbr: argument base must be 4KB aligned")
    (fun () -> eval_binding "ttbr(vmid=1, base=0x280001)" |> ignore
  )

let tests =
  "Isla.Page_table_fns"
  >::: [ "evaluate ttbr helper" >:: test_ttbr_helper;
         "validate ttbr helper" >:: test_ttbr_helper_validation
       ]

let () = run_test_tt_main tests
