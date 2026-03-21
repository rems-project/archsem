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
      let enc, _ = Isla.Assembler.assemble "MOV X1, #42\nSTR X1, [X0]" in
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
      let enc0, _ = Isla.Assembler.assemble "MOV X1, #1\nSTR X1, [X0]" in
      let enc1, _ = Isla.Assembler.assemble "LDR X1, [X0]" in
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
    "page table setup produces PageTable blocks" >:: (fun _ ->
      Test_utils.setup ();
      let toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "WithPGT"
symbolic = ["x"]

page_table_setup = """
physical pa;
x |-> pa with default;
*pa = 0;
"""

[thread.0]
init = { X0 = "x" }
code = "NOP"

[final]
expect = "sat"
assertion = "true"
|} in
      let repr = convert toml in
      let pgt_blocks = List.filter
        (fun (b : Testrepr.memory_block) -> b.kind = Testrepr.PageTable)
        repr.memory in
      assert_bool "has page table blocks" (List.length pgt_blocks > 0);
      List.iter (fun (b : Testrepr.memory_block) ->
        assert_equal 8 (Bytes.length b.data)
          ~msg:"each page table entry is 8 bytes")
        pgt_blocks);
    "pte3 and mkdesc3 in reset resolved by converter" >:: (fun _ ->
      Test_utils.setup ();
      let toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "PteResetTest"
symbolic = ["x"]

page_table_setup = """
physical pa_x;
x |-> pa_x with default;
"""

[thread.0]
code = "NOP"

[thread.0.reset]
X0 = "pte3(x, page_table_base)"
X1 = "mkdesc3(oa=pa_x)"
X2 = "bvxor(extz(0x400, 64), mkdesc3(oa=pa_x))"

[final]
expect = "sat"
assertion = "true"
|} in
      let repr = convert toml in
      let regs = List.hd repr.registers in
      let find_reg name =
        List.assoc_opt name regs |> Option.map (function
          | RegValGen.Number z -> Z.to_int z
          | _ -> failwith "expected Number") in
      let pte_addr = Option.get (find_reg "R0") in
      assert_bool "PTE addr is 8-byte aligned" (pte_addr mod 8 = 0);
      let desc = Option.get (find_reg "R1") in
      assert_equal 0x3 (desc land 0x3) ~msg:"mkdesc3 produces valid descriptor";
      let xored = Option.get (find_reg "R2") in
      assert_equal (desc lxor 0x400) xored ~msg:"bvxor toggles AF bit");
    "mkdesc3 in assertion resolved by converter" >:: (fun _ ->
      Test_utils.setup ();
      let toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "MkdescAssertionTest"
symbolic = ["x"]

page_table_setup = """
physical pa_x;
x |-> pa_x with default;
"""

[thread.0]
code = "NOP"

[final]
expect = "sat"
assertion = "0:X0 = mkdesc3(oa=pa_x)"
|} in
      let repr = convert toml in
      assert_equal 1 (List.length repr.finals)
        ~msg:"one final condition";
      match List.hd repr.finals with
      | Observable ([(0, [(_, ReqEq (Number z))])], []) ->
        let desc = Z.to_int z in
        assert_equal 0x3 (desc land 0x3)
          ~msg:"mkdesc3 in assertion produces valid descriptor"
      | _ -> assert_failure "unexpected final condition shape");
    "TTBR0_EL1 auto-injected when page tables present" >:: (fun _ ->
      Test_utils.setup ();
      let toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "TTBR0Test"
symbolic = ["x"]

page_table_setup = """
physical pa;
x |-> pa;
"""

[thread.0]
code = "NOP"

[final]
expect = "sat"
assertion = "true"
|} in
      let repr = convert toml in
      let regs = List.hd repr.registers in
      let ttbr0 = List.assoc_opt "TTBR0_EL1" regs in
      assert_bool "TTBR0_EL1 present" (ttbr0 <> None);
      (match ttbr0 with
       | Some (Number z) ->
         let addr = Z.to_int z in
         assert_bool "4KB aligned" (addr mod 4096 = 0)
       | _ -> assert_failure "TTBR0_EL1 should be a Number"));
    "TTBR0_EL1 not injected without page tables" >:: (fun _ ->
      Test_utils.setup ();
      let repr = convert simple_toml in
      let regs = List.hd repr.registers in
      let ttbr0 = List.assoc_opt "TTBR0_EL1" regs in
      assert_equal None ttbr0 ~msg:"no TTBR0_EL1 without page tables");
  ]

let () =
  run_test_tt_main tests
