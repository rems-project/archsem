(** Unit tests for Isla.Normalize. *)

open OUnit2
open Isla.Assertion
open Isla.Term

let sample_ir arch : Isla.Ir.t =
  {
    arch;
    name = "Normalize";
    threads =
      [
        {
          tid = 0;
          code = "MOV W1,#1";
          init = [ ("X0", LocVal (Mem "x")); ("W2", Const (Z.of_int 3)) ];
        };
      ];
    symbolic = [ "x" ];
    locations = [ ("x", Const Z.zero) ];
    page_table_setup = [];
    expect = Isla.Ir.Sat;
    assertion =
      And
        (Atom (Cmp (LocVal (Reg (0, "X1")), Eq, Const Z.one)),
         Or
           (Atom (Cmp (LocVal (Reg (0, "X3")), Eq, LocVal (Mem "x"))),
            And
              (Atom (Cmp (LocVal (Reg (0, "W2")), Ne, Const Z.zero)),
               Atom (Cmp (LocVal (Reg (0, "W4")), Eq, LocVal (Reg (1, "X5")))))));
  }

let tests =
  "Isla.Normalize" >::: [
    "AArch64 init and assertion regs normalized" >:: (fun _ ->
      Test_utils.setup ();
      let normalized = Isla.Normalize.apply (sample_ir Litmus.Arch_id.Arm) in
      let expected : Isla.Ir.t =
        {
          (sample_ir Litmus.Arch_id.Arm) with
          threads =
            [
              {
                tid = 0;
                code = "MOV W1,#1";
                init = [ ("R0", LocVal (Mem "x")); ("R2", Const (Z.of_int 3)) ];
              };
            ];
          assertion =
            And
              (Atom (Cmp (LocVal (Reg (0, "R1")), Eq, Const Z.one)),
               Or
                 (Atom (Cmp (LocVal (Reg (0, "R3")), Eq, LocVal (Mem "x"))),
                  And
                    (Atom (Cmp (LocVal (Reg (0, "R2")), Ne, Const Z.zero)),
                     Atom (Cmp (LocVal (Reg (0, "R4")), Eq, LocVal (Reg (1, "R5")))))));
        }
      in
      assert_equal expected normalized);
  ]

let () = run_test_tt_main tests
