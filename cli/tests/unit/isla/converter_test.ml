(** Unit tests for Isla.Converter. *)

open Litmus
open OUnit2
module Arm = Archsem.Arm
module ArmRunner = Runner.Make (Arm)
module X86 = Archsem.X86
module X86Runner = Runner.Make (X86)
module RegValGen = Archsem.RegValGen

let convert toml =
  toml |> Isla.Ir.of_toml |> Isla.Normalize.apply |> Isla.Converter.to_testrepr

let n i = RegValGen.Number (Z.of_int i)

let expected_regs ~arch ~pc overrides =
  let pc_reg = Isla.Converter.pc_reg arch in
  let has name = List.exists (fun (k, _) -> k = name) overrides in
  let defaults =
    List.filter_map
      (fun (name, value) -> if has name then None else Some (name, value))
      (Isla.Converter.register_defaults ())
  in
  ((pc_reg, n pc) :: overrides) @ defaults

let data_block ~addr ~sym =
  { Testrepr.addr;
    step = 8;
    data = Bytes.make 8 '\x00';
    sym = Some sym;
    kind = Testrepr.Data
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

let x86_toml =
  Otoml.Parser.from_string
    {|
arch = "x86"
name = "X86Xor"

[thread.0]
init = { RAX = "0x11", RCX = "0x101", RFLAGS = "0x3000" }
code = """
xorq %rcx, %rax
"""

[final]
expect = "sat"
assertion = "0:RAX = 0x110"
|}

let tests =
  "Isla.Converter"
  >::: [ ("SimpleStore"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let arm = Litmus.Arch_id.Arm in
         let pc_reg = Isla.Converter.pc_reg arm in
         let enc = Isla.Assembler.assemble "MOV X1, #42\nSTR X1, [X0]" in
         let expected =
           { Testrepr.arch = "Arm";
             name = "SimpleStore";
             registers = [expected_regs ~arch:arm ~pc:0x1500 [("R0", n 0x500)]];
             memory =
               [ {addr = 0x1500; step = 4; data = enc; sym = None; kind = Code};
                 data_block ~addr:0x500 ~sym:"x"
               ];
             term_cond = [[(pc_reg, n 0x1508)]];
             finals = []
           }
         in
         assert_equal expected (convert simple_toml)
         );
         ("MP"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let arm = Litmus.Arch_id.Arm in
         let pc_reg = Isla.Converter.pc_reg arm in
         let enc0 = Isla.Assembler.assemble "MOV X1, #1\nSTR X1, [X0]" in
         let enc1 = Isla.Assembler.assemble "LDR X1, [X0]" in
         let expected =
           { Testrepr.arch = "Arm";
             name = "MP";
             registers =
               [ expected_regs ~arch:arm ~pc:0x2500 [("R0", n 0x500)];
                 expected_regs ~arch:arm ~pc:0x3500 [("R0", n 0x500)]
               ];
             memory =
               [ {addr = 0x2500; step = 4; data = enc0; sym = None; kind = Code};
                 {addr = 0x3500; step = 4; data = enc1; sym = None; kind = Code};
                 data_block ~addr:0x500 ~sym:"x";
                 data_block ~addr:0x1500 ~sym:"y"
               ];
             term_cond = [[(pc_reg, n 0x2508)]; [(pc_reg, n 0x3504)]];
             finals =
               [ Testrepr.Observable
                   ( [(1, [("R1", Testrepr.ReqEq (RegValGen.Number Z.one))])],
                     [ { sym = "x";
                         addr = 0x500;
                         size = 8;
                         req = Testrepr.MemEq Z.one
                       }
                     ]
                   )
               ]
           }
         in
         assert_equal expected (convert mp_toml)
         );
         ("X86Xor"
         >:: fun _ ->
         Test_utils.setup_x86 ();
         let x86 = Litmus.Arch_id.X86 in
         let pc_reg = Isla.Converter.pc_reg x86 in
         let enc = Isla.Assembler.assemble "xorq %rcx, %rax" in
         let expected =
           { Testrepr.arch = "X86";
             name = "X86Xor";
             registers =
               [ expected_regs ~arch:x86 ~pc:0x500
                   [ ("RAX", RegValGen.Number (Z.of_string "0x11"));
                     ("RCX", RegValGen.Number (Z.of_string "0x101"));
                     ("RFLAGS", RegValGen.Number (Z.of_string "0x3000"))
                   ]
               ];
             memory =
               [{addr = 0x500; step = 1; data = enc; sym = None; kind = Code}];
             term_cond = [[(pc_reg, n (0x500 + Bytes.length enc))]];
             finals =
               [ Testrepr.Observable
                   ( [ ( 0,
                         [ ( "RAX",
                             Testrepr.ReqEq
                               (RegValGen.Number (Z.of_string "0x110"))
                           )
                         ]
                       )
                     ],
                     []
                   )
               ]
           }
         in
         assert_equal expected (convert x86_toml)
         );
         ("e2e: SimpleStore seq"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let (result, _msgs) =
           ArmRunner.run_testrepr Arm.(seq_model tiny_isa) (convert simple_toml)
         in
         assert_equal Runner.Expected result
         );
         ("e2e: MP ump"
         >:: fun _ ->
         Test_utils.setup_arm ();
         let (result, _msgs) =
           ArmRunner.run_testrepr Arm.(umProm_model tiny_isa) (convert mp_toml)
         in
         assert_equal Runner.Expected result
         )
       ]

let () = run_test_tt_main tests
