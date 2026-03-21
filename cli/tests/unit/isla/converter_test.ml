(** Unit tests for Isla.Converter. *)

open Litmus
open OUnit2

module Arm = Archsem.Arm
module ArmRunner = Runner.Make (Arm)

module RegValGen = Archsem.RegValGen

let convert toml =
  toml |> Isla.Ir.of_toml |> Isla.Normalize.apply |> Isla.Converter.to_testrepr

let n i = RegValGen.Number (Z.of_int i)
let pc_reg = Isla.Converter.pc_reg Litmus.Arch_id.Arm

let expected_regs ~pc overrides =
  let has name = List.exists (fun (k, _) -> k = name) overrides in
  let defaults =
    List.filter_map
      (fun (name, value) -> if has name then None else Some (name, value))
      (Isla.Converter.register_defaults ())
  in
  (pc_reg, n pc) :: overrides @ defaults

let data_block ~addr ~sym =
  {
    Testrepr.addr;
    step = 8;
    data = Bytes.make 8 '\x00';
    sym = Some sym;
    kind = Testrepr.Data;
  }

let simple_toml =
  Otoml.Parser.from_string
    {|
arch = "AArch64"
name = "SimpleStore"
symbolic = ["x"]

[thread.0]
init = { X0 = "x" }
code = """
MOV X1, #42
STR X1, [X0]
"""

[final]
expect = "sat"
assertion = "true"
|}

let mp_toml =
  Otoml.Parser.from_string
    {|
arch = "AArch64"
name = "MP"
symbolic = ["x", "y"]

[locations]
"x" = "0"
"y" = "0"

[thread.0]
init = { X0 = "x" }
code = """
MOV X1, #1
STR X1, [X0]
"""

[thread.1]
init = { X0 = "x" }
code = """
LDR X1, [X0]
"""

[final]
expect = "sat"
assertion = "*x = 1 & 1:X1 = 1"
|}

let tests =
  "Isla.Converter" >::: [
    "SimpleStore" >:: (fun _ ->
      Test_utils.setup ();
      let enc = Isla.Assembler.assemble "MOV X1, #42\nSTR X1, [X0]" in
      let expected =
        {
          Testrepr.arch = "Arm";
          name = "SimpleStore";
          registers = [expected_regs ~pc:0x1500 [("R0", n 0x500)]];
          memory =
            [
              { addr = 0x1500; step = 4; data = enc;
                sym = None; kind = Code };
              data_block ~addr:0x500 ~sym:"x";
            ];
          term_cond = [[(pc_reg, n 0x1508)]];
          finals = [];
        }
      in
      assert_equal expected (convert simple_toml));
    "MP" >:: (fun _ ->
      Test_utils.setup ();
      let enc0 = Isla.Assembler.assemble "MOV X1, #1\nSTR X1, [X0]" in
      let enc1 = Isla.Assembler.assemble "LDR X1, [X0]" in
      let expected =
        {
          Testrepr.arch = "Arm";
          name = "MP";
          registers =
            [
              expected_regs ~pc:0x2500 [("R0", n 0x500)];
              expected_regs ~pc:0x3500 [("R0", n 0x500)];
            ];
          memory =
            [
              { addr = 0x2500; step = 4; data = enc0;
                sym = None; kind = Code };
              { addr = 0x3500; step = 4; data = enc1;
                sym = None; kind = Code };
              data_block ~addr:0x500 ~sym:"x";
              data_block ~addr:0x1500 ~sym:"y";
            ];
          term_cond =
            [[(pc_reg, n 0x2508)]; [(pc_reg, n 0x3504)]];
          finals =
            [
              Testrepr.Observable
                ( [(1, [("R1", Testrepr.ReqEq (RegValGen.Number Z.one))])],
                  [{ sym = "x"; addr = 0x500; size = 8;
                    req = Testrepr.MemEq Z.one }] );
            ];
        }
      in
      assert_equal expected (convert mp_toml));
    "section: assembled at explicit address" >:: (fun _ ->
      Test_utils.setup ();
      let toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "WithSection"
symbolic = ["x"]

[thread.0]
init = { X0 = "x" }
code = "NOP"

[section.handler]
address = "0x1400"
code = "MOV X2, #1"
|} in
      let repr = convert toml in
      let sec_block =
        List.find (fun (b : Testrepr.memory_block) -> b.addr = 0x1400) repr.memory
      in
      assert_equal Testrepr.Code sec_block.kind;
      assert_equal 4 (Bytes.length sec_block.data));
    "e2e: SimpleStore seq" >:: (fun _ ->
      Test_utils.setup ();
      let result, _msgs =
        ArmRunner.run_testrepr Arm.(seq_model tiny_isa) (convert simple_toml)
      in
      assert_equal Runner.Expected result);
    "e2e: MP ump" >:: (fun _ ->
      Test_utils.setup ();
      let result, _msgs =
        ArmRunner.run_testrepr Arm.(umProm_model tiny_isa) (convert mp_toml)
      in
      assert_equal Runner.Expected result);
  ]

let () =
  Test_utils.setup ();
  run_test_tt_main tests
