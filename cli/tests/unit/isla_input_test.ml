(** Unit tests for Isla.Input. *)

open OUnit2

let simple_toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "MP"
symbolic = ["x", "y"]

[locations]
"x" = "0"
"y" = "0"

[thread.0]
init = { X0 = "x" }
code = """
  MOV W1,#1
  STR W1,[X0]
"""

[thread.1]
init = { X1 = "y", X2 = "x" }
code = """
  LDR W0,[X2]
  STR W0,[X1]
"""

[final]
expect = "sat"
assertion = "1:X0 = 1 & *y = 1"
|}

let t = Isla.Input.parse simple_toml

let no_loc_toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "Simple"
symbolic = ["x"]
[thread.0]
init = { X0 = "x" }
code = "MOV W1,#1"
[final]
assertion = "0:X1 = 1"
|}

let t2 = Isla.Input.parse no_loc_toml

let tests = "Isla.Input" >::: [
  "arch" >:: (fun _ -> assert_equal "AArch64" t.arch);
  "name" >:: (fun _ -> assert_equal "MP" t.name);
  "2 threads" >:: (fun _ -> assert_equal 2 (List.length t.threads));
  "thread 0 tid" >:: (fun _ -> assert_equal 0 (List.nth t.threads 0).tid);
  "thread 1 tid" >:: (fun _ -> assert_equal 1 (List.nth t.threads 1).tid);
  "thread 0 has code" >:: (fun _ ->
    assert_bool "" ((List.nth t.threads 0).code <> ""));
  "thread 0 init X0" >:: (fun _ ->
    assert_equal "x" (List.assoc "X0" (List.nth t.threads 0).init));
  "thread 1 init X1" >:: (fun _ ->
    assert_equal "y" (List.assoc "X1" (List.nth t.threads 1).init));
  "symbolic" >:: (fun _ -> assert_equal ["x"; "y"] t.symbolic);
  "locations x" >:: (fun _ -> assert_equal "0" (List.assoc "x" t.locations));
  "expect" >:: (fun _ -> assert_equal "sat" t.expect);
  "assertion" >:: (fun _ ->
    assert_equal "1:X0 = 1 & *y = 1" t.assertion);
  "no locations" >:: (fun _ -> assert_equal [] t2.locations);
  "default expect" >:: (fun _ -> assert_equal "sat" t2.expect);
]

let () = run_test_tt_main tests
