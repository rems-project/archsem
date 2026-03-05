(** Unit tests for Isla.Converter. *)

open Archsem
open Litmus
open OUnit2

let aarch64_command = "llvm-mc -triple=aarch64 --assemble --show-encoding"

let has_llvm_mc =
  try
    let ic = Unix.open_process_in
      "llvm-mc -triple=aarch64 --version 2>/dev/null" in
    let _ = try input_line ic with End_of_file -> "" in
    Unix.close_process_in ic = Unix.WEXITED 0
  with _ -> false

let set_assembler_config () =
  Config.set (Otoml.Parser.from_string
    (Printf.sprintf "[assembler]\ncommand = %S\n\n[arch]\ndefault_mem_size = 8\n" aarch64_command))

let simple_toml = Otoml.Parser.from_string {|
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

let mp_toml = Otoml.Parser.from_string {|
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

let tests = "Isla.Converter" >::: [
  "arch is AArch64" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    assert_equal "AArch64" spec.arch);
  "name" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    assert_equal "SimpleStore" spec.name);
  "1 thread" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    assert_equal 1 (List.length spec.registers));
  "1 term_cond" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    assert_equal 1 (List.length spec.term_cond));
  "has code memory" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    assert_bool "" (List.exists (fun (b : Spec.memory_block) ->
      b.kind = Some Spec.Code) spec.memory));
  "has data memory" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    assert_bool "" (List.exists (fun (b : Spec.memory_block) ->
      b.kind = Some Spec.Data) spec.memory));
  "data memory has name" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    assert_bool "" (List.exists (fun (b : Spec.memory_block) ->
      b.name = Some "x") spec.memory));
  "R0 in registers" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    let regs = List.hd spec.registers in
    assert_bool "" (List.exists (fun (r, _) -> r = Reg.r 0) regs));
  "_PC in registers" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    let regs = List.hd spec.registers in
    assert_bool "" (List.exists (fun (r, _) -> r = Reg.pc) regs));
  "SCTLR_EL1 in registers" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    let regs = List.hd spec.registers in
    assert_bool "" (List.exists (fun (r, _) -> r = Reg.sctlr 1) regs));
  "PSTATE in registers" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    let regs = List.hd spec.registers in
    assert_bool "" (List.exists (fun (r, _) -> r = Reg.pstate) regs));
  "no outcomes for 'true' assertion" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    assert_equal [] spec.finals);
  "round-trip SimpleStore" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    let toml_str = Printer.to_string spec in
    let reparsed = Parser.parse_to_spec (Otoml.Parser.from_string toml_str) in
    assert_bool "" (Spec.equal spec reparsed));
  "MP: 2 threads" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    assert_equal 2 (List.length spec.registers));
  "MP: 2 term_conds" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    assert_equal 2 (List.length spec.term_cond));
  "MP: 1 outcome" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    assert_equal 1 (List.length spec.finals));
  "MP: outcome is Observable" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    assert_bool "" (match List.hd spec.finals with
      | Spec.Observable _ -> true | _ -> false));
  "MP: outcome has mem_cond" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    assert_bool "" (match List.hd spec.finals with
      | Spec.Observable (_, mcs) -> List.length mcs = 1
      | _ -> false));
  "MP: mem_cond sym is x" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    assert_bool "" (match List.hd spec.finals with
      | Spec.Observable (_, [mc]) -> mc.sym = "x"
      | _ -> false));
  "MP: data memory for x" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    assert_bool "" (List.exists (fun (b : Spec.memory_block) ->
      b.name = Some "x" && b.kind = Some Spec.Data) spec.memory));
  "MP: data memory for y" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    assert_bool "" (List.exists (fun (b : Spec.memory_block) ->
      b.name = Some "y" && b.kind = Some Spec.Data) spec.memory));
  "round-trip MP" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    let toml_str = Printer.to_string spec in
    let reparsed = Parser.parse_to_spec (Otoml.Parser.from_string toml_str) in
    assert_bool "" (Spec.equal spec reparsed));
  "config: assembler passthrough" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let config = Otoml.Parser.from_string
      (Printf.sprintf "[assembler]\ncommand = %S\n\n[arch]\ndefault_mem_size = 8\n" aarch64_command) in
    Config.set config;
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    set_assembler_config ();
    assert_equal "AArch64" spec.arch);
  "R0 resolved to address" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    let regs = List.hd spec.registers in
    assert_bool "" (match List.assoc_opt (Reg.r 0) regs with
      | Some (RegVal.Number z) -> Z.geq z (Z.of_int 0x500)
      | _ -> false));
  "e2e: SimpleStore seq Expected" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse simple_toml) in
    let result, _msgs = Runner.run_spec "seq" spec in
    assert_equal Runner.Expected result);
  "e2e: MP ump Expected" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let spec = Isla.Converter.to_spec (Isla.Input.parse mp_toml) in
    let result, _msgs = Runner.run_spec "ump" spec in
    assert_equal Runner.Expected result);
]

let () =
  set_assembler_config ();
  run_test_tt_main tests
