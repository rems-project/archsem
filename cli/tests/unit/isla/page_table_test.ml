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

(** Unit tests for page-table setup parsing and evaluation. *)

open OUnit2
module Ast = Isla.Page_table_ast
module Builder = Isla.Page_table_builder
module Desc = Isla.Page_table_desc
module Fns = Isla.Page_table_fns

let z = Z.of_int

let parse input =
  let lexbuf = Lexing.from_string input in
  Isla.Parser.page_table_setup Isla.Lexer.token lexbuf

let parse_cases =
  [ ( "invalid at level",
      "x |-> invalid at level 2;",
      [ Ast.Mapping
          {va_name = "x"; target = Ast.Invalid; attrs = []; level = Some 2}
      ]
    );
    ( "table at level",
      "x |-> table(0x283000) at level 2;",
      [ Ast.Mapping
          { va_name = "x";
            target = Ast.Table (z 0x283000);
            attrs = [];
            level = Some 2
          }
      ]
    )
  ]

let build stmts =
  Builder.build ~arch:Litmus.Arch_id.Arm ~allocator:(Isla.Allocator.make ())
    ~symbolic_vas:[("x", 0x800000)]
    ~code_pages:[] stmts

let pte2_desc layout =
  let pte =
    Fns.pte_addr "test" layout.Builder.table_entries ~base:layout.Builder.root
      ~va:0x800000 ~level:2
  in
  List.assoc_opt pte layout.Builder.table_entries

let builder_cases =
  [ ( "invalid at level",
      fun _ ->
        let layout =
          build
            [ Ast.Mapping
                {va_name = "x"; target = Ast.Invalid; attrs = []; level = Some 2}
            ]
        in
        assert_equal None (pte2_desc layout)
    );
    ( "table at level",
      fun _ ->
        let layout =
          build
            [ Ast.Mapping
                { va_name = "x";
                  target = Ast.Table (z 0x283000);
                  attrs = [];
                  level = Some 2
                }
            ]
        in
        assert_equal
          ~printer:(function
            | None -> "None" | Some desc -> Printf.sprintf "Some 0x%Lx" desc
            )
          (Some (Desc.table_descriptor 0x283000))
          (pte2_desc layout)
    )
  ]

let () =
  run_test_tt_main
    ("Isla.Page_table"
    >::: [ "parse"
           >::: List.map
                  (fun (label, input, expected) ->
                     label >:: fun _ -> assert_equal expected (parse input)
                   )
                  parse_cases;
           "builder"
           >::: List.map (fun (label, test) -> label >:: test) builder_cases
         ]
    )
