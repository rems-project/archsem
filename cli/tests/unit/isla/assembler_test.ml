(** Unit tests for Isla.Assembler. *)

open OUnit2

let tests =
  "Isla.Assembler" >::: [
    "assemble ARM: 4 bytes" >:: (fun _ ->
      Test_utils.setup_arm ();
      let result = Isla.Assembler.assemble "MOV W1, #42" in
      assert_equal 4 (Bytes.length result));
    "assemble ARM: MOV W1,#42 bytes" >:: (fun _ ->
      Test_utils.setup_arm ();
      let result = Isla.Assembler.assemble "MOV W1, #42" in
      assert_equal (Bytes.of_string "\x41\x05\x80\x52") result);
    "assemble ARM: branch with label resolves" >:: (fun _ ->
      Test_utils.setup_arm ();
      let result = Isla.Assembler.assemble "\tCBNZ W0,LC00\nLC00:\n\tISB" in
      assert_equal
        (Bytes.of_string "\x20\x00\x00\x35\xdf\x3f\x03\xd5")
        result);
    "assemble ARM: 2 instructions bytes" >:: (fun _ ->
      Test_utils.setup_arm ();
      let result = Isla.Assembler.assemble "MOV X0, #1\nSTR X0, [X1]" in
      assert_equal
        (Bytes.of_string "\x20\x00\x80\xd2\x20\x00\x00\xf9")
        result);
    "assemble X86: nop" >:: (fun _ ->
      Test_utils.setup_x86 ();
      let result = Isla.Assembler.assemble "nop" in
      assert_equal (Bytes.of_string "\x90") result);
    "assemble X86: xorq bytes" >:: (fun _ ->
      Test_utils.setup_x86 ();
      let result = Isla.Assembler.assemble "xorq %rcx, %rax" in
      assert_equal (Bytes.of_string "\x48\x31\xc8") result);
    "assemble X86: 2 instructions" >:: (fun _ ->
      Test_utils.setup_x86 ();
      let result = Isla.Assembler.assemble "nop\nretq" in
      assert_equal (Bytes.of_string "\x90\xc3") result);
  ]

let () = run_test_tt_main tests
