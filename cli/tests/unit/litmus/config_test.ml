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
  "RISCV alias is rejected" >:: (fun _ ->
    assert_raises
      (Error.Cli_error (Parser, "unknown architecture: RISCV"))
      (fun () -> ignore (Arch_id.of_string "RISCV")));
  "loads built-in Arm config" >:: (fun _ ->
    let _ = Config.of_arch (Arch_id.of_string "AArch64") in
    assert_equal 1000 (Config.get_fuel ()));
]

let () = run_test_tt_main ("litmus_config" >::: [
  default_config_tests;
])
