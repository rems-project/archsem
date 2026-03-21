(** Round-trip tests for Litmus_printer. *)

open OUnit2
open Litmus
open Test_utils

let round_trip rel_path =
  let original = parse_file rel_path in
  let printed = Printer.to_string original in
  let reparsed =
    Parser.parse_to_testrepr (Otoml.Parser.from_string printed)
  in
  original = reparsed

let round_trip_tests =
  Test_utils.setup_arm ();
  let tests = collect_archsem_files () in
  "round-trip" >::: List.map (fun (name, path) ->
    name >:: (fun _ -> assert_bool "" (round_trip path))
  ) tests

let () = run_test_tt_main ("litmus_printer" >::: [
  round_trip_tests;
])
