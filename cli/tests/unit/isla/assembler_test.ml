(** Unit tests for Isla.Assembler. *)

open OUnit2

let tests =
  "Isla.Assembler"
  >::: [ ("assemble: 4 bytes"
         >:: fun _ ->
         Test_utils.setup ();
         let result = Isla.Assembler.assemble "MOV W1, #42" in
         assert_equal 4 (Bytes.length result)
         );
         ("assemble: MOV W1,#42 bytes"
         >:: fun _ ->
         Test_utils.setup ();
         let result = Isla.Assembler.assemble "MOV W1, #42" in
         assert_equal (Bytes.of_string "\x41\x05\x80\x52") result
         );
         ("assemble: branch with label resolves"
         >:: fun _ ->
         Test_utils.setup ();
         let result = Isla.Assembler.assemble "\tCBNZ W0,LC00\nLC00:\n\tISB" in
         assert_equal (Bytes.of_string "\x20\x00\x00\x35\xdf\x3f\x03\xd5") result
         );
         ("assemble: 2 instructions bytes"
         >:: fun _ ->
         Test_utils.setup ();
         let result = Isla.Assembler.assemble "MOV X0, #1\nSTR X0, [X1]" in
         assert_equal (Bytes.of_string "\x20\x00\x80\xd2\x20\x00\x00\xf9") result
         )
       ]

let () = run_test_tt_main tests
