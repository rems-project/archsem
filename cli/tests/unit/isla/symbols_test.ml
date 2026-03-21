(** Unit tests for Isla.Symbols. *)

open OUnit2


let tests =
  "Isla.Symbols" >::: [
    "empty table resolves nothing" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      assert_equal None (Isla.Symbols.resolve_opt s0 "x"));
    "alloc_data returns address" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      let addr = Isla.Symbols.resolve_or_alloc s0 "x" in
      assert_equal 0x500 addr);
    "resolve after alloc" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      Isla.Symbols.alloc_sym s0 "x";
      assert_equal 0x500 (Isla.Symbols.resolve s0 "x"));
    "first alloc unchanged after second" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      let a1 = Isla.Symbols.resolve_or_alloc s0 "x" in
      Isla.Symbols.alloc_sym s0 "y";
      assert_equal a1 (Isla.Symbols.resolve s0 "x"));
    "duplicate alloc returns same address" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      let a1 = Isla.Symbols.resolve_or_alloc s0 "x" in
      let a2 = Isla.Symbols.resolve_or_alloc s0 "x" in
      assert_equal a1 a2);
    "alloc skips reserved range" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      ignore (Isla.Symbols.reserve s0 0x500 4);
      let addr = Isla.Symbols.resolve_or_alloc s0 "x" in
      assert_equal 0x1500 addr);
    "alloc skips multiple reserved ranges" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      ignore (Isla.Symbols.reserve s0 0x500 4);
      ignore (Isla.Symbols.reserve s0 0x1500 4);
      let addr = Isla.Symbols.resolve_or_alloc s0 "x" in
      assert_equal 0x2500 addr);
    "alloc skips reserved then continues normally" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      ignore (Isla.Symbols.reserve s0 0x500 4);
      let a1 = Isla.Symbols.resolve_or_alloc s0 "x" in
      let a2 = Isla.Symbols.resolve_or_alloc s0 "y" in
      assert_equal 0x1500 a1;
      assert_equal 0x2500 a2);
    "reserved range overlapping middle of page skips it" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      ignore (Isla.Symbols.reserve s0 0x1000 0x100);
      let addr = Isla.Symbols.resolve_or_alloc s0 "x" in
      assert_equal 0x1500 addr);
    "alloc_table returns 4KB-aligned address and reserves it" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      let s, addr = Isla.Symbols.alloc_table s0 "L0" in
      assert_equal 0x1000 addr;
      let _, addr2 = Isla.Symbols.alloc_data s "x" in
      assert_equal 0x2000 addr2);
    "alloc_table deduplicates" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      let s, a1 = Isla.Symbols.alloc_table s0 "L0" in
      let _, a2 = Isla.Symbols.alloc_table s "L0" in
      assert_equal a1 a2);
    "alloc_table skips reserved ranges" >:: (fun _ ->
      Test_utils.setup ();
      let s0 = Isla.Symbols.empty () in
      let s = Isla.Symbols.reserve s0 0x1000 4096 in
      let _, addr = Isla.Symbols.alloc_table s "L0" in
      assert_equal 0x2000 addr);
  ]

let () = run_test_tt_main tests
