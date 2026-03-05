(** Unit tests for Isla.Assembler. *)

open OUnit2

let command = "llvm-mc -triple=aarch64 --assemble --show-encoding"

let has_llvm_mc =
  try
    let ic = Unix.open_process_in
      "llvm-mc -triple=aarch64 --version 2>/dev/null" in
    let _ = try input_line ic with End_of_file -> "" in
    Unix.close_process_in ic = Unix.WEXITED 0
  with _ -> false

let tests = "Isla.Assembler" >::: [
  "le_bytes_to_word: 4 bytes" >:: (fun _ ->
    assert_equal 0x52800541
      (Isla.Assembler.le_bytes_to_word [0x41; 0x05; 0x80; 0x52]));
  "le_bytes_to_word: 3 bytes" >:: (fun _ ->
    assert_equal 0xc18948
      (Isla.Assembler.le_bytes_to_word [0x48; 0x89; 0xc1]));
  "parse_encoding_line: AArch64" >:: (fun _ ->
    assert_equal (Some [0x41; 0x05; 0x80; 0xd2])
      (Isla.Assembler.parse_encoding_line
        "\tmov\tx1, #42\t\t// encoding: [0x41,0x05,0x80,0xd2]"));
  "parse_encoding_line: x86" >:: (fun _ ->
    assert_equal (Some [0x48; 0x89; 0xc1])
      (Isla.Assembler.parse_encoding_line
        "\tmovq\t%rax, %rcx\t\t# encoding: [0x48,0x89,0xc1]"));
  "parse_encoding_line: no encoding" >:: (fun _ ->
    assert_equal None
      (Isla.Assembler.parse_encoding_line "\t.text"));
  "parse_encodings: 2 instructions" >:: (fun _ ->
    let output =
      "\t.text\n\
       \tmov\tx1, #42\t\t// encoding: [0x41,0x05,0x80,0xd2]\n\
       \tstr\tx1, [x0]\t\t// encoding: [0x01,0x00,0x00,0xf9]\n" in
    let pairs = Isla.Assembler.parse_encodings output in
    assert_equal 2 (List.length pairs));
  "parse_encodings: correct words" >:: (fun _ ->
    let output =
      "\tmov\tx1, #42\t\t// encoding: [0x41,0x05,0x80,0xd2]\n" in
    let pairs = Isla.Assembler.parse_encodings output in
    assert_equal [(0xd2800541, 4)] pairs);
  "encode: 1 instruction" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let result = Isla.Assembler.encode ~command "MOV W1, #42" in
    assert_equal 1 (List.length result.bytes));
  "encode: width 4" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let result = Isla.Assembler.encode ~command "MOV W1, #42" in
    assert_equal [4] result.widths);
  "encode: MOV W1,#42 = 0x52800541" >:: (fun _ ->
    skip_if (not has_llvm_mc) "llvm-mc not available";
    let result = Isla.Assembler.encode ~command "MOV W1, #42" in
    assert_equal 0x52800541 (List.hd result.bytes));
]

let () = run_test_tt_main tests
