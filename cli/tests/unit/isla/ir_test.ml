(** Unit tests for Isla.Input. *)

open OUnit2
open Isla.Assertion
open Isla.Term

let simple_toml =
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
  MOV W1,#1
  STR W1,[X0]
"""

[thread.1]
init = { X1 = "y", X2 = "x" }
code = """
  LDR W0,[X2]
  STR W0,[X1]
"""

[final]
expect = "sat"
assertion = "1:X0 = 1 & *y = 1"
|}


let t = Isla.Ir.of_toml simple_toml

let expected : Isla.Ir.t =
  {
    arch = Litmus.Arch_id.Arm;
    name = "MP";
    threads =
      [
        { tid = 0;
          code = "MOV W1,#1\n  STR W1,[X0]";
          init = [ ("X0", LocVal (Mem "x")) ];
        };
        { tid = 1;
          code = "LDR W0,[X2]\n  STR W0,[X1]";
          init = [ ("X1", LocVal (Mem "y")); ("X2", LocVal (Mem "x")) ];
        };
      ];
    symbolic = [ "x"; "y" ];
    locations = [ ("x", Const Z.zero); ("y", Const Z.zero) ];
    page_table_setup = [];
    expect = Isla.Ir.Sat;
    assertion =
      And
        (Atom (Cmp (LocVal (Reg (1, "X0")), Eq, Const Z.one)),
         Atom (Cmp (Deref (Mem "y"), Eq, Const Z.one)));
  }

let reset_toml =
  Otoml.Parser.from_string
    {|
arch = "AArch64"
name = "ResetTest"

[thread.0]
code = "NOP"
init = { X0 = 10 }

[thread.0.reset]
X0 = "bvand(0xFF, 0x0F)"
X1 = "extz(42, 64)"
|}

let tests =
  "Isla.Ir" >::: [
    "parse" >:: (fun _ -> assert_equal expected t);
    "reset: expressions evaluated and merged" >:: (fun _ ->
      let ir = Isla.Ir.of_toml reset_toml in
      let thread = List.hd ir.threads in
      assert_equal
        ~msg:"X0 from init takes precedence over reset"
        (Some (Const (Z.of_int 10)))
        (List.assoc_opt "X0" thread.init);
      assert_equal
        ~msg:"X1 from reset with extz evaluated"
        (Some (Const (Z.of_int 42)))
        (List.assoc_opt "X1" thread.init));
    "reset: label parsed as Label loc" >:: (fun _ ->
      let toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "LabelTest"
[thread.0]
code = "NOP"
[thread.0.reset]
ELR_EL1 = "L0:"
|} in
      let ir = Isla.Ir.of_toml toml in
      let thread = List.hd ir.threads in
      assert_equal
        ~msg:"ELR_EL1 parsed as Label"
        (Some (LocVal (Label "L0")))
        (List.assoc_opt "ELR_EL1" thread.init));
    "reset: __isla metadata ignored" >:: (fun _ ->
      let toml = Otoml.Parser.from_string {|
arch = "AArch64"
name = "MetaTest"
[thread.0]
code = "NOP"
[thread.0.reset]
X0 = 42
"__isla_monomorphize_writes" = "true"
|} in
      let ir = Isla.Ir.of_toml toml in
      let thread = List.hd ir.threads in
      assert_equal
        ~msg:"X0 present"
        (Some (Const (Z.of_int 42)))
        (List.assoc_opt "X0" thread.init);
      assert_equal
        ~msg:"__isla key filtered out"
        None
        (List.assoc_opt "__isla_monomorphize_writes" thread.init));
  ]

let () = run_test_tt_main tests
