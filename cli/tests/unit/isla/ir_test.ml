(** Unit tests for Isla.Input. *)

open OUnit2
open Isla.Assertion

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

[section.el1_handler]
address = "0x1400"
code = """
  MOV X2, #1
  ERET
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
          init = [ ("X0", Isla.Ir.Sym "x") ];
        };
        { tid = 1;
          code = "LDR W0,[X2]\n  STR W0,[X1]";
          init = [ ("X1", Isla.Ir.Sym "y"); ("X2", Isla.Ir.Sym "x") ];
        };
      ];
    sections =
      [{ sec_name = "el1_handler"; address = 0x1400; code = "MOV X2, #1\n  ERET" }];
    symbolic = [ "x"; "y" ];
    locations = [ ("x", Isla.Ir.Int Z.zero); ("y", Isla.Ir.Int Z.zero) ];
    expect = Isla.Ir.Sat;
    assertion =
      And
        (Atom (CmpCst (Reg (1, "X0"), Eq, Z.one)),
         Atom (CmpCst (Mem "y", Eq, Z.one)));
  }

let tests =
  "Isla.Ir" >::: [
    "parse" >:: (fun _ -> assert_equal expected t);
  ]

let () = run_test_tt_main tests
