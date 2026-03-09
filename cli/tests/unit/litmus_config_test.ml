(** Unit tests for Config. *)

open OUnit2
open Litmus
let default_config_tests = "default config" >::: [
  "finds default Arm config path" >:: (fun _ ->
    let path = Config.default_path_for_arch Arch_id.Arm in
    assert_bool "expected an Arm config path" (Option.is_some path));
  "loads built-in Arm config" >:: (fun _ ->
    let _ = Config.of_arch Arch_id.Arm in
    assert_equal 1000 (Config.get_fuel ()));
]

let () = run_test_tt_main ("litmus_config" >::: [
  default_config_tests;
])
