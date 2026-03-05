(** Unit tests for Isla.Symbols. *)

open OUnit2

let s0 = Isla.Symbols.empty

let tests = "Isla.Symbols" >::: [
  "empty table resolves nothing" >:: (fun _ ->
    assert_equal None (Isla.Symbols.resolve s0 "x"));
  "alloc_data returns address" >:: (fun _ ->
    let _, addr = Isla.Symbols.alloc_data s0 "x" in
    assert_bool "" (Z.equal addr (Z.of_int 0x500)));
  "resolve after alloc" >:: (fun _ ->
    let s1, _ = Isla.Symbols.alloc_data s0 "x" in
    assert_equal (Some (Z.of_int 0x500)) (Isla.Symbols.resolve s1 "x"));
  "second alloc is page-aligned" >:: (fun _ ->
    let s1, _ = Isla.Symbols.alloc_data s0 "x" in
    let _, a2 = Isla.Symbols.alloc_data s1 "y" in
    assert_bool "" (Z.equal a2 (Z.of_int 0x1500)));
  "first alloc unchanged after second" >:: (fun _ ->
    let s1, a1 = Isla.Symbols.alloc_data s0 "x" in
    let s2, _ = Isla.Symbols.alloc_data s1 "y" in
    assert_equal (Some a1) (Isla.Symbols.resolve s2 "x"));
  "duplicate alloc returns same address" >:: (fun _ ->
    let s1, a1 = Isla.Symbols.alloc_data s0 "x" in
    let _, a2 = Isla.Symbols.alloc_data s1 "x" in
    assert_bool "" (Z.equal a1 a2));
  "state unchanged on duplicate" >:: (fun _ ->
    let s1, _ = Isla.Symbols.alloc_data s0 "x" in
    let s2, _ = Isla.Symbols.alloc_data s1 "x" in
    assert_bool "" (Z.equal s1.next_data s2.next_data));
  "code alloc returns base" >:: (fun _ ->
    let _, addr = Isla.Symbols.alloc_code s0 16 in
    assert_bool "" (Z.equal addr (Z.of_int 0x20000)));
  "code pointer advances by page" >:: (fun _ ->
    let s1, _ = Isla.Symbols.alloc_code s0 16 in
    assert_bool "" (Z.equal s1.next_code (Z.of_int 0x21000)));
  "three allocs are contiguous pages" >:: (fun _ ->
    let s1, _ = Isla.Symbols.alloc_data s0 "a" in
    let s1, _ = Isla.Symbols.alloc_data s1 "b" in
    let s1, _ = Isla.Symbols.alloc_data s1 "c" in
    assert_bool "" (Z.equal s1.next_data (Z.of_int 0x3500)));
]

let () = run_test_tt_main tests
