(** Unit tests for Pgt_parser. *)

open OUnit2
open Isla.Pgtable

let parse s =
  let lexbuf = Lexing.from_string s in
  Isla.Pgtable_parser.program Isla.Pgtable_lexer.token lexbuf

let tests =
  "Pgt_parser" >::: [
    "address declarations" >:: (fun _ ->
      assert_equal
        [AddrDecl { kind = Physical; names = ["pa1"; "pa2"]; alignment = None }]
        (parse "physical pa1 pa2;");
      assert_equal
        [AddrDecl { kind = Virtual; names = ["x"]; alignment = None }]
        (parse "virtual x;");
      assert_equal
        [AddrDecl { kind = Intermediate; names = ["ipa1"]; alignment = None }]
        (parse "intermediate ipa1;");
      assert_equal
        [AddrDecl { kind = Physical; names = ["pa"]; alignment = Some 4096 }]
        (parse "aligned 4096 physical pa;"));

    "mappings with modifiers" >:: (fun _ ->
      (* basic *)
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa"; modifiers = no_mod }]
        (parse "x |-> pa;");
      (* with default/code/attrs *)
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa";
                   modifiers = { no_mod with with_spec = [WsDefault] } }]
        (parse "x |-> pa with default;");
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa";
                   modifiers = { no_mod with with_spec = [WsCode] } }]
        (parse "x |-> pa with code;");
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa";
                   modifiers = { no_mod with with_spec =
                     [WsAttrs [("AP", Isla.Term.Const Z.zero)]] } }]
        (parse "x |-> pa with [AP = 0x00];");
      (* combined with_spec items *)
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa";
                   modifiers = { no_mod with with_spec =
                     [WsAttrs [("AP", Isla.Term.Const Z.one)]; WsDefault] } }]
        (parse "x |-> pa with [AP = 0b01] and default;");
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa";
                   modifiers = { no_mod with with_spec =
                     [WsAttrs [("AP", Isla.Term.Const Z.zero)];
                           WsAttrs [("S2AP", Isla.Term.Const (Z.of_int 3))]] } }]
        (parse "x |-> pa with [AP = 0x00] and [S2AP = 0b11];");
      (* at level, as walk, all combined *)
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa";
                   modifiers = { no_mod with level = Some 2 } }]
        (parse "x |-> pa at level 2;");
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa";
                   modifiers = { no_mod with walk_name = Some "mywalk" } }]
        (parse "x |-> pa as mywalk;");
      assert_equal
        [Mapping { va = SrcName "x"; pa = PA "pa";
                   modifiers = { with_spec = [WsDefault];
                                 level = Some 3; walk_name = Some "w" } }]
        (parse "x |-> pa with default at level 3 as w;");
      (* invalid target *)
      assert_equal
        [Mapping { va = SrcName "x"; pa = Invalid; modifiers = no_mod }]
        (parse "x |-> invalid;"));

    "optional mappings" >:: (fun _ ->
      assert_equal
        [OptMapping { va = SrcName "x"; pa = Invalid; modifiers = no_mod }]
        (parse "x ?-> invalid;");
      assert_equal
        [OptMapping { va = SrcName "x"; pa = PA "pa";
                      modifiers = { no_mod with level = Some 3 } }]
        (parse "x ?-> pa at level 3;"));

    "identity mappings" >:: (fun _ ->
      assert_equal
        [Identity { target = IdName "x"; with_spec = [WsDefault] }]
        (parse "identity x;");
      assert_equal
        [Identity { target = IdName "x"; with_spec = [WsCode] }]
        (parse "identity x with code;");
      assert_equal
        [Identity { target = IdAddr 0x1000; with_spec = [WsCode] }]
        (parse "identity 0x1000 with code;");
      assert_equal
        [Identity { target = IdAddr 0x2000; with_spec = [WsDefault] }]
        (parse "identity 0x2000;");
      (match parse "identity pa_to_ipa(0x1000) with code;" with
       | [Identity { target = IdFn ("pa_to_ipa", [Isla.Term.Const _]);
                     with_spec = [WsCode] }] -> ()
       | _ -> assert_failure "fn identity"));

    "mem init and value exprs" >:: (fun _ ->
      assert_equal
        [MemInit { addr = "pa"; value = Isla.Term.Const (Z.of_int 42) }]
        (parse "*pa = 42;");
      assert_equal
        [MemInit { addr = "pa"; value = Isla.Term.Const (Z.of_int 0xFF) }]
        (parse "*pa = 0xFF;");
      assert_equal
        [MemInit { addr = "pa"; value = Isla.Term.Fn ("bvand",
           [Const (Z.of_int 0xFF); Const (Z.of_int 0x0F)]) }]
        (parse "*pa = bvand(0xFF, 0x0F);"));

    "table blocks and refs" >:: (fun _ ->
      assert_equal
        [TableBlock { stage = S1; name = "mytable"; base = 0x200000;
                      body = [Mapping { va = SrcName "x"; pa = PA "pa";
                                        modifiers = no_mod }] }]
        (parse "s1table mytable 0x200000 { x |-> pa; }");
      assert_equal
        [TableBlock { stage = S2; name = "s2tbl"; base = 0x240000;
                      body = [Mapping { va = SrcName "x"; pa = PA "pa";
                                        modifiers = { no_mod with level = Some 3 } }] }]
        (parse "s2table s2tbl 0x240000 { x |-> pa at level 3; }");
      assert_equal
        [TableRef { stage = S1; name = "mytable" }]
        (parse "s1table mytable;");
      (* nested *)
      (match parse {|s2table s2 0x240000 {
                       s1table s1 0x280000 { x |-> pa at level 3; } }|} with
       | [TableBlock { stage = S2; body = [TableBlock { stage = S1; _ }]; _ }] -> ()
       | _ -> assert_failure "nested tables"));

    "option and assert stmts" >:: (fun _ ->
      assert_equal [Option { name = "f"; value = false }] (parse "option f = false;");
      assert_equal [Option { name = "t"; value = true }] (parse "option t = true;");
      assert_equal
        [Assert { lhs = AVar "pa1"; op = CmpEq; rhs = AVar "ipa1" }]
        (parse "assert pa1 == ipa1;");
      assert_equal
        [Assert { lhs = ASlice ("x", 48, 21); op = CmpNeq;
                  rhs = ASlice ("y", 48, 21) }]
        (parse "assert x[48..21] != y[48..21];");
      (match parse "assert x[48..12] == add_bits_int(y[48..12], 1);" with
       | [Assert { lhs = ASlice ("x", 48, 12); op = CmpEq;
                   rhs = AFn ("add_bits_int", [ASlice ("y", 48, 12); _]) }] -> ()
       | _ -> assert_failure "assert fn"));

    "function call sources" >:: (fun _ ->
      (match parse "pa_to_ipa(table3(walkx)) ?-> invalid;" with
       | [OptMapping { va = SrcExpr (Isla.Term.Fn ("pa_to_ipa", _));
                       pa = Invalid; _ }] -> ()
       | _ -> assert_failure "fn source");
      (match parse "identity pa_to_va(0x1000) with code;" with
       | [Identity { target = IdFn ("pa_to_va", [Isla.Term.Const _]); _ }] -> ()
       | _ -> assert_failure "identity fn"));

    "empty and multi-stmt" >:: (fun _ ->
      assert_equal [] (parse "");
      assert_equal 4 (List.length
        (parse "physical pa; virtual x; x |-> pa; *pa = 0;")));

    "full isla-style program" >:: (fun _ ->
      let stmts = parse {|
        option default_tables = false;
        physical pa1;
        intermediate ipa1;
        s2table vm_s2 0x240000 {
          ipa1 |-> pa1 at level 3;
          ipa1 ?-> invalid at level 3;
          s1table vm_s1 0x280000 {
            x |-> ipa1 at level 3;
            x ?-> invalid at level 3;
          }
        }
        s1table hyp 0x200000 {
          identity 0x1000 with code;
          s2table vm_s2;
          s1table vm_s1;
        }
        *pa1 = 1;
      |} in
      assert_equal 6 (List.length stmts));
  ]

let () = run_test_tt_main tests
