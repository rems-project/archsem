(** Unit tests for Isla.Normalize. *)

open OUnit2
open Isla.Assertion

let sample_ir arch : Isla.Ir.t =
  {
    arch;
    name = "Normalize";
    threads =
      [
        {
          tid = 0;
          code = "MOV W1,#1";
          init = [ ("X0", Isla.Ir.Sym "x"); ("W2", Isla.Ir.Int (Z.of_int 3)) ];
        };
      ];
    symbolic = [ "x" ];
    locations = [ ("x", Isla.Ir.Int Z.zero) ];
    expect = Isla.Ir.Sat;
    assertion =
      And
        (Atom (CmpCst (Reg (0, "X1"), Eq, Z.one)),
         Or
           (Atom (CmpLoc (Reg (0, "X3"), Eq, Mem "x")),
            And
              (Atom (CmpCst (Reg (0, "W2"), Ne, Z.zero)),
               Atom (CmpLoc (Reg (0, "W4"), Eq, Reg (1, "X5"))))));
  }

let tests =
  "Isla.Normalize" >::: [
    "AArch64 init and assertion regs normalized" >:: (fun _ ->
      Test_utils.setup_arm ();
      let normalized = Isla.Normalize.apply (sample_ir Litmus.Arch_id.Arm) in
      let expected : Isla.Ir.t =
        {
          (sample_ir Litmus.Arch_id.Arm) with
          threads =
            [
              {
                tid = 0;
                code = "MOV W1,#1";
                init = [ ("R0", Isla.Ir.Sym "x"); ("R2", Isla.Ir.Int (Z.of_int 3)) ];
              };
            ];
          assertion =
            And
              (Atom (CmpCst (Reg (0, "R1"), Eq, Z.one)),
               Or
                 (Atom (CmpLoc (Reg (0, "R3"), Eq, Mem "x")),
                  And
                    (Atom (CmpCst (Reg (0, "R2"), Ne, Z.zero)),
                     Atom (CmpLoc (Reg (0, "R4"), Eq, Reg (1, "R5"))))));
        }
      in
      assert_equal expected normalized);
  ]

let () = run_test_tt_main tests
