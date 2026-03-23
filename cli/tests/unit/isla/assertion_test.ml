(** Unit tests for Isla.Assertion. *)

open OUnit2
open Isla.Assertion

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
|} s
      )
  in
  (Isla.Ir.of_toml toml).assertion

let assert_parses_as source expected = assert_equal expected (parse_string source)

let tests =
  "Isla.Assertion"
  >::: [ ("parse register eq"
         >:: fun _ ->
         assert_parses_as "1:X0 = 1" (Atom (CmpCst (Reg (1, "X0"), Eq, Z.one)))
         );
         ("parse conjunction"
         >:: fun _ ->
         assert_parses_as "1:X0 = 1 & 2:X0 = 0"
           (And
              ( Atom (CmpCst (Reg (1, "X0"), Eq, Z.one)),
                Atom (CmpCst (Reg (2, "X0"), Eq, Z.zero))
              )
           )
         );
         ("parse false" >:: fun _ -> assert_parses_as "false" False);
         ("parse memory"
         >:: fun _ -> assert_parses_as "*x = 2" (Atom (CmpCst (Mem "x", Eq, n 2)))
         );
         ("parse negation"
         >:: fun _ ->
         assert_parses_as "~(1:X0 = 1)"
           (Not (Atom (CmpCst (Reg (1, "X0"), Eq, Z.one))))
         );
         ("parse hex values"
         >:: fun _ ->
         assert_parses_as "0:X0 = 0x2a" (Atom (CmpCst (Reg (0, "X0"), Eq, n 42)))
         );
         ("parse register equals symbol"
         >:: fun _ ->
         assert_parses_as "0:X0 = x" (Atom (CmpLoc (Reg (0, "X0"), Eq, Mem "x")))
         )
       ]

let () = run_test_tt_main tests
