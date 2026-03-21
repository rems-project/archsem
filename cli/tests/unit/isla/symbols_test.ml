(** Unit tests for Isla.Symbols. *)

open OUnit2

let tests =
  "Isla.Symbols"
  >::: [ ("empty table resolves nothing"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         assert_equal None (Isla.Symbols.resolve_opt s0 "x")
         );
         ("alloc_data returns address"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         let addr = Isla.Symbols.resolve_or_alloc s0 "x" in
         assert_equal 0x500 addr
         );
         ("resolve after alloc"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         Isla.Symbols.alloc_sym s0 "x";
         assert_equal 0x500 (Isla.Symbols.resolve s0 "x")
         );
         ("first alloc unchanged after second"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         let a1 = Isla.Symbols.resolve_or_alloc s0 "x" in
         Isla.Symbols.alloc_sym s0 "y";
         assert_equal a1 (Isla.Symbols.resolve s0 "x")
         );
         ("duplicate alloc returns same address"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let s0 = Isla.Symbols.empty () in
         let a1 = Isla.Symbols.resolve_or_alloc s0 "x" in
         let a2 = Isla.Symbols.resolve_or_alloc s0 "x" in
         assert_equal a1 a2
         )
       ]

let () = run_test_tt_main tests
