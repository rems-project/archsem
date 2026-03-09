(** Unit tests for Config. *)

open OUnit2
open Litmus

let default_config_tests = "default config" >::: [
  "finds default Arm config path" >:: (fun _ ->
    let path = Config.default_path_for_arch Arch_id.Arm in
    assert_bool "expected an Arm config path" (Option.is_some path));
  "AArch64 resolves to Arm config path" >:: (fun _ ->
    let path = Config.default_path_for_arch (Arch_id.of_string "AArch64") in
    assert_bool "expected an Arm config path for AArch64" (Option.is_some path));
  "loads built-in Arm config" >:: (fun _ ->
    Test_utils.setup_arm ();
    assert_equal 4 (Config.get_instruction_step ()));
  "finds default X86 config path" >:: (fun _ ->
    let path = Config.default_path_for_arch Arch_id.X86 in
    assert_bool "expected an X86 config path" (Option.is_some path));
  "loads built-in X86 config" >:: (fun _ ->
    Test_utils.setup_x86 ();
    assert_equal 1 (Config.get_instruction_step ()));
]

let () = run_test_tt_main ("litmus_config" >::: [
  default_config_tests;
])
