(** Unit tests for Config. *)

open OUnit2
open Litmus

(** {1 empty} *)

let empty_tests = "empty" >::: [
  "get_int default on empty" >:: (fun _ ->
    assert_equal 1000
      (Config.get_int ["execution"; "fuel"] 1000 Config.empty));
  "get_string_opt None on empty" >:: (fun _ ->
    assert_equal None
      (Config.get_string_opt ["model"; "bbm"] Config.empty));
  "get_string default on empty" >:: (fun _ ->
    assert_equal "off"
      (Config.get_string ["model"; "bbm"] "off" Config.empty));
]

(** {1 get_int} *)

let cfg = Otoml.Parser.from_string
  "[execution]\nfuel = 500\n[model]\nbbm = \"lax\"\n"

let get_int_tests = "get_int" >::: [
  "reads int from section" >:: (fun _ ->
    assert_equal 500
      (Config.get_int ["execution"; "fuel"] 1000 cfg));
  "returns default for missing key" >:: (fun _ ->
    assert_equal 60
      (Config.get_int ["execution"; "timeout"] 60 cfg));
]

(** {1 get_string_opt / get_string} *)

let get_string_tests = "get_string" >::: [
  "reads string from section" >:: (fun _ ->
    assert_equal (Some "lax")
      (Config.get_string_opt ["model"; "bbm"] cfg));
  "None for missing key" >:: (fun _ ->
    assert_equal None
      (Config.get_string_opt ["model"; "other"] cfg));
  "get_string with default" >:: (fun _ ->
    assert_equal "default"
      (Config.get_string ["model"; "other"] "default" cfg));
  "get_string reads value" >:: (fun _ ->
    assert_equal "lax"
      (Config.get_string ["model"; "bbm"] "off" cfg));
]

let () = run_test_tt_main ("litmus_config" >::: [
  empty_tests;
  get_int_tests;
  get_string_tests;
])
