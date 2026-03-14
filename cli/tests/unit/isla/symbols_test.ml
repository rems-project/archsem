(** Unit tests for Isla.Symbols. *)

open OUnit2

let s0 = Isla.Symbols.empty

let tests =
  "Isla.Symbols" >::: [
    "empty table resolves nothing" >:: (fun _ ->
      Test_utils.setup_arm ();
      assert_equal None (Isla.Symbols.resolve_opt s0 "x"));
    "alloc_data returns address" >:: (fun _ ->
      Test_utils.setup_arm ();
      let _, addr = Isla.Symbols.alloc_data s0 "x" in
      assert_equal 0x500 addr);
    "resolve after alloc" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s1, _ = Isla.Symbols.alloc_data s0 "x" in
      assert_equal 0x500 (Isla.Symbols.resolve s1 "x"));
    "first alloc unchanged after second" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s1, a1 = Isla.Symbols.alloc_data s0 "x" in
      let s2, _ = Isla.Symbols.alloc_data s1 "y" in
      assert_equal a1 (Isla.Symbols.resolve s2 "x"));
    "duplicate alloc returns same address" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s1, a1 = Isla.Symbols.alloc_data s0 "x" in
      let _, a2 = Isla.Symbols.alloc_data s1 "x" in
      assert_equal a1 a2);
    "state unchanged on duplicate" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s1, _ = Isla.Symbols.alloc_data s0 "x" in
      let s2, _ = Isla.Symbols.alloc_data s1 "x" in
      assert_equal s1.next_addr s2.next_addr);
    "code alloc returns base" >:: (fun _ ->
      Test_utils.setup_arm ();
      let _, addr = Isla.Symbols.alloc_code s0 16 in
      assert_equal 0x500 addr);
    "shared pointer advances by page" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s1, _ = Isla.Symbols.alloc_code s0 16 in
      assert_equal (Some 0x1500) s1.next_addr);
    "three allocs are contiguous pages" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s1, _ = Isla.Symbols.alloc_data s0 "a" in
      let s1, _ = Isla.Symbols.alloc_data s1 "b" in
      let s1, _ = Isla.Symbols.alloc_data s1 "c" in
      assert_equal (Some 0x3500) s1.next_addr);
    "data and code share the same page allocator" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s1, data_addr = Isla.Symbols.alloc_data s0 "x" in
      let _, code_addr = Isla.Symbols.alloc_code s1 16 in
      assert_equal 0x500 data_addr;
      assert_equal 0x1500 code_addr);
    "alloc skips reserved range" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s = Isla.Symbols.reserve s0 0x500 4 in
      let _, addr = Isla.Symbols.alloc_data s "x" in
      assert_equal 0x1500 addr);
    "alloc skips multiple reserved ranges" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s = Isla.Symbols.reserve s0 0x500 4 in
      let s = Isla.Symbols.reserve s 0x1500 4 in
      let _, addr = Isla.Symbols.alloc_data s "x" in
      assert_equal 0x2500 addr);
    "alloc skips reserved then continues normally" >:: (fun _ ->
      Test_utils.setup_arm ();
      let s = Isla.Symbols.reserve s0 0x500 4 in
      let s, a1 = Isla.Symbols.alloc_data s "x" in
      let _, a2 = Isla.Symbols.alloc_data s "y" in
      assert_equal 0x1500 a1;
      assert_equal 0x2500 a2);
    "reserved range overlapping middle of page skips it" >:: (fun _ ->
      Test_utils.setup_arm ();
      (* reserve range that overlaps with the first page [0x500, 0x1500) *)
      let s = Isla.Symbols.reserve s0 0x1000 0x100 in
      let _, addr = Isla.Symbols.alloc_data s "x" in
      assert_equal 0x1500 addr);
  ]

let () = run_test_tt_main tests
