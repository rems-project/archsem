(** Unit tests for the runner's error classification.

    Verifies that the nested try-with in {!Runner.run_litmus_test}
    correctly separates parse-phase errors ([SetupError]) from
    model-phase crashes ([ModelError]). *)

open OUnit2
open Litmus

module Arm = Archsem.Arm
module ArmRunner = Runner.Make (Arm)

(** A path that exists so [Sys.file_exists] passes.
    The parse function is injected, so the content is never read. *)
let dummy_path = "/dev/null"

let tests = "runner error classification" >::: [
  "parse phase error returns SetupError" >:: (fun _ ->
    Test_utils.setup ();
    let parse _filename = Error.raise_error Config "simulated config error" in
    let model = Arm.(seq_model tiny_isa) in
    let result = ArmRunner.run_litmus_test ~parse model dummy_path in
    assert_equal ~printer:Runner.string_of_result Runner.SetupError result);

  "file not found returns SetupError" >:: (fun _ ->
    Test_utils.setup ();
    let parse _f = failwith "should not be called" in
    let model = Arm.(seq_model tiny_isa) in
    let result = ArmRunner.run_litmus_test ~parse model "/nonexistent/file.toml" in
    assert_equal ~printer:Runner.string_of_result Runner.SetupError result);

  "model crash returns ModelError" >:: (fun _ ->
    Test_utils.setup ();
    let parse _filename : Testrepr.t = {
      arch = "Arm"; name = "crash-test";
      registers = [[]]; memory = [];
      term_cond = [[]]; finals = [];
    } in
    let model _fuel _term _init = failwith "simulated model crash" in
    let result = ArmRunner.run_litmus_test ~parse model dummy_path in
    assert_equal ~printer:Runner.string_of_result Runner.ModelError result);
]

let () = run_test_tt_main tests
