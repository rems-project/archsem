(** Unit tests for Isla.Assertion. *)

open OUnit2
open Isla.Assertion
open Isla.Value_expr

let n = Z.of_int

let parse_string s =
  let toml =
    Otoml.Parser.from_string
      (Printf.sprintf
         {|
arch = "AArch64"

[thread.0]
code = "NOP"

[final]
assertion = %S
|}
         s)
  in
  (Isla.Ir.of_toml toml).assertion

let assert_parses_as source expected =
  assert_equal expected (parse_string source)

let tests =
  "Isla.Assertion" >::: [
    "parse register eq" >:: (fun _ ->
      assert_parses_as
        "1:X0 = 1"
        (Atom (Cmp (LocVal (Reg (1, "X0")), Eq, Const Z.one))));
    "parse conjunction" >:: (fun _ ->
      assert_parses_as
        "1:X0 = 1 & 2:X0 = 0"
        (And
           (Atom (Cmp (LocVal (Reg (1, "X0")), Eq, Const Z.one)),
            Atom (Cmp (LocVal (Reg (2, "X0")), Eq, Const Z.zero)))));
    "parse false" >:: (fun _ ->
      assert_parses_as "false" False);
    "parse memory" >:: (fun _ ->
      assert_parses_as
        "*x = 2"
        (Atom (Cmp (LocVal (Mem "x"), Eq, Const (n 2)))));
    "parse negation" >:: (fun _ ->
      assert_parses_as
        "~(1:X0 = 1)"
        (Not (Atom (Cmp (LocVal (Reg (1, "X0")), Eq, Const Z.one)))));
    "parse hex values" >:: (fun _ ->
      assert_parses_as
        "0:X0 = 0x2a"
        (Atom (Cmp (LocVal (Reg (0, "X0")), Eq, Const (n 42)))));
    "parse register equals symbol" >:: (fun _ ->
      assert_parses_as
        "0:X0 = x"
        (Atom (Cmp (LocVal (Reg (0, "X0")), Eq, LocVal (Mem "x")))));
    "parse bvand" >:: (fun _ ->
      assert_parses_as
        "0:X0 = bvand(0xFF, 0x0F)"
        (Atom (Cmp (LocVal (Reg (0, "X0")), Eq,
                    Fn ("bvand", [Const (n 0xFF); Const (n 0x0F)])))));
    "parse nested fn" >:: (fun _ ->
      assert_parses_as
        "0:X0 = extz(bvxor(0x1, 0x3), 64)"
        (Atom (Cmp (LocVal (Reg (0, "X0")), Eq,
                    Fn ("extz", [Fn ("bvxor", [Const Z.one; Const (n 3)]);
                                 Const (n 64)])))));
    "parse page" >:: (fun _ ->
      assert_parses_as
        "0:X0 = page(0x12000)"
        (Atom (Cmp (LocVal (Reg (0, "X0")), Eq,
                    Fn ("page", [Const (n 0x12000)])))));
    "eval bvand" >:: (fun _ ->
      assert_equal (n 0x0F)
        (Isla.Value_expr.eval (Fn ("bvand", [Const (n 0xFF); Const (n 0x0F)]))));
    "eval bvor" >:: (fun _ ->
      assert_equal (n 0xFF)
        (Isla.Value_expr.eval (Fn ("bvor", [Const (n 0xF0); Const (n 0x0F)]))));
    "eval bvxor" >:: (fun _ ->
      assert_equal (n 0xF0)
        (Isla.Value_expr.eval (Fn ("bvxor", [Const (n 0xFF); Const (n 0x0F)]))));
    "eval bvshl" >:: (fun _ ->
      assert_equal (n 0x80)
        (Isla.Value_expr.eval (Fn ("bvshl", [Const Z.one; Const (n 7)]))));
    "eval bvlshr" >:: (fun _ ->
      assert_equal (n 0x7F)
        (Isla.Value_expr.eval (Fn ("bvlshr", [Const (n 0xFF); Const Z.one]))));
    "eval page" >:: (fun _ ->
      assert_equal (n 0x12)
        (Isla.Value_expr.eval (Fn ("page", [Const (n 0x12345)]))));
    "eval extz" >:: (fun _ ->
      assert_equal (n 42)
        (Isla.Value_expr.eval (Fn ("extz", [Const (n 42); Const (n 64)]))));
    "eval nested" >:: (fun _ ->
      assert_equal (n 2)
        (Isla.Value_expr.eval
           (Fn ("bvxor", [Const (n 1); Const (n 3)]))));
  ]

let () = run_test_tt_main tests
