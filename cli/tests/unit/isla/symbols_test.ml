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
      let s = Isla.Symbols.empty () in
      Isla.Symbols.reserve s 0x500 4;
      let addr = Isla.Symbols.resolve_or_alloc s "x" in
      assert_equal 0x1500 addr);
    "alloc skips multiple reserved ranges" >:: (fun _ ->
      Test_utils.setup ();
      let s = Isla.Symbols.empty () in
      Isla.Symbols.reserve s 0x500 4;
      Isla.Symbols.reserve s 0x1500 4;
      let addr = Isla.Symbols.resolve_or_alloc s "x" in
      assert_equal 0x2500 addr);
    "alloc skips reserved then continues normally" >:: (fun _ ->
      Test_utils.setup ();
      let s = Isla.Symbols.empty () in
      Isla.Symbols.reserve s 0x500 4;
      let a1 = Isla.Symbols.resolve_or_alloc s "x" in
      let a2 = Isla.Symbols.resolve_or_alloc s "y" in
      assert_equal 0x1500 a1;
      assert_equal 0x2500 a2);
    "reserved range overlapping middle of page skips it" >:: (fun _ ->
      Test_utils.setup ();
      let s = Isla.Symbols.empty () in
      (* reserve range that overlaps with the first page [0x500, 0x1500) *)
      Isla.Symbols.reserve s 0x1000 0x100;
      let addr = Isla.Symbols.resolve_or_alloc s "x" in
      assert_equal 0x1500 addr);
  ]

let () = run_test_tt_main tests
