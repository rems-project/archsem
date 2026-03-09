(** Unit tests for litmus test parsing, test representations, and execution. *)

open OUnit2
open Litmus
open Testrepr
open Test_utils

module Arm = Archsem.Arm
module ArmAS = ToArchState.Make (Arm)
module ArmRunner = Runner.Make (Arm)

(** {1 Parsed Test Fixtures} *)

let eor = parse_file "../seq/EOR.archsem.toml"
let mp = parse_file "../ump/MP.archsem.toml"

let bad_step_toml =
  Otoml.Parser.from_string
    {|
arch = "Arm"
name = "bad-step"

[[registers]]
_PC = 0x500
SCTLR_EL1 = 0x0
PSTATE = { "EL" = 0b00, "SP" = 0b0 }

[[memory]]
addr = 0x500
kind = "code"
step = 0
data = 0xd503201f

[[termCond]]
_PC = 0x504

[[outcome]]
observable.0._PC = 0x504
|}

let size_only_toml =
  Otoml.Parser.from_string
    {|
arch = "Arm"
name = "size-only"

[[registers]]
_PC = 0x500
SCTLR_EL1 = 0x0
PSTATE = { "EL" = 0b00, "SP" = 0b0 }

[[memory]]
addr = 0x500
kind = "code"
size = 4
data = 0xd503201f

[[termCond]]
_PC = 0x504

[[outcome]]
observable.0._PC = 0x504
|}

let bad_memory_toml = Otoml.Parser.from_string {|
arch = "Arm"
name = "bad-memory"

memory = [1]

[[registers]]
_PC = 0x500

[[termCond]]
_PC = 0x500

[[outcome]]
observable.0._PC = 0x500
|}

(** {1 Parser Coverage} *)

let expected_eor = {
  arch = "Arm";
  name = "EOR";
  registers = [[
    "_PC", i 0x500;
    "R0", i 0x0;
    "R1", i 0x11;
    "R2", i 0x101;
    "SCTLR_EL1", i 0x0;
    "PSTATE", Archsem.RegValGen.Struct [("EL", i 0); ("SP", i 0)];
  ]];
  memory = [{
    addr = 0x500;
    step = 4;
    data = Bytes.of_string "\x20\x00\x02\xca";
    sym = None;
    kind = Code;
  }];
  term_cond = [[
    "_PC", i 0x504;
  ]];
  finals = [
    Observable ([0, ["_PC", ReqEq (i 0x504); "R0", ReqEq (i 0x110)]], []);
  ];
}

let expected_mp = {
  arch = "Arm";
  name = "MP";
  registers = [
    [
      "_PC", i 0x500;
      "R0", i 0x1000;
      "R1", i 0x100;
      "R2", i 0x2a;
      "R3", i 0x1000;
      "R4", i 0x200;
      "R5", i 0x1;
      "SCTLR_EL1", i 0x0;
      "PSTATE", Archsem.RegValGen.Struct [("EL", i 0); ("SP", i 0)];
    ];
    [
      "_PC", i 0x600;
      "R0", i 0x1000;
      "R1", i 0x100;
      "R2", i 0x0;
      "R3", i 0x1000;
      "R4", i 0x200;
      "R5", i 0x0;
      "SCTLR_EL1", i 0x0;
      "PSTATE", Archsem.RegValGen.Struct [("EL", i 0); ("SP", i 0)];
    ];
  ];
  memory = [
    {
      addr = 0x500;
      step = 4;
      data = Bytes.of_string "\x22\x68\x20\xf8\x85\x68\x23\xf8";
      sym = None;
      kind = Code;
    };
    {
      addr = 0x600;
      step = 4;
      data = Bytes.of_string "\x85\x68\x63\xf8\x22\x68\x60\xf8";
      sym = None;
      kind = Code;
    };
    {
      addr = 0x1100;
      step = 8;
      data = Bytes.of_string "\x00\x00\x00\x00\x00\x00\x00\x00";
      sym = None;
      kind = Data;
    };
    {
      addr = 0x1200;
      step = 8;
      data = Bytes.of_string "\x00\x00\x00\x00\x00\x00\x00\x00";
      sym = None;
      kind = Data;
    };
  ];
  term_cond = [
    ["_PC", i 0x508];
    ["_PC", i 0x608];
  ];
  finals = [
    Observable ([1, ["R5", ReqEq (i 0x0); "R2", ReqEq (i 0x2a)]], []);
    Observable ([1, ["R5", ReqEq (i 0x0); "R2", ReqEq (i 0x0)]], []);
    Observable ([1, ["R5", ReqEq (i 0x1); "R2", ReqEq (i 0x0)]], []);
    Observable ([1, ["R5", ReqEq (i 0x1); "R2", ReqEq (i 0x2a)]], []);
  ];
}

let assert_parses_as_expected parsed expected =
  assert_bool "" (parsed = expected)

let assert_parse_failure exn toml =
  assert_raises exn (fun () -> Parser.parse_to_testrepr toml)

let parse_correct_file_test =
  let parse_ok name parsed expected =
    name >:: (fun _ -> assert_parses_as_expected parsed expected)
  in
  "parse_correct_file"
  >::: [
         parse_ok "EOR parses as expected" eor expected_eor;
         parse_ok "MP parses as expected" mp expected_mp;
       ]

let parse_bad_file_test =
  let parse_fails name exn toml =
    name >:: (fun _ -> assert_parse_failure exn toml)
  in
  "parse_bad_file"
  >::: [
         parse_fails "non-positive memory step fails"
           (Failure "Memory block step must be positive") bad_step_toml;
         parse_fails "size-only memory blocks fail"
           (Otoml.Key_error "Failed to retrieve a value at step: field step not found")
           size_only_toml;
         parse_fails "malformed memory blocks fail"
           (Otoml.Type_error "Unexpected TOML value type at key memory: value is integer, not a table")
           bad_memory_toml;
       ]

(** {1 ArchState Conversion And Execution} *)

let archstate_runner_tests = "testrepr_to_archstate / run_testrepr" >::: [
  "EOR Expected with seq model" >:: (fun _ ->
    let result, _msgs = ArmRunner.run_testrepr Arm.(seq_model tiny_isa) eor in
    assert_equal Runner.Expected result);
]

let () = run_test_tt_main ("litmus_testrepr" >::: [
  parse_correct_file_test;
  parse_bad_file_test;
  archstate_runner_tests;
])
