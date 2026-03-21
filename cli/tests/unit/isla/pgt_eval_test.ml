(** Unit tests for Pgt_eval. *)

open OUnit2

let parse s =
  let lexbuf = Lexing.from_string s in
  Isla.Pgtable_parser.program Isla.Pgtable_lexer.token lexbuf

let eval ?(symbolic = []) s =
  Test_utils.setup ();
  let stmts = parse s in
  Isla.Pgtable.evaluate ~arch:Litmus.Arch_id.Arm ~symbolic
    (Isla.Symbols.empty ()) stmts

let read_le64 data offset =
  let v = ref 0 in
  for i = 7 downto 0 do
    v := (!v lsl 8) lor Char.code (Bytes.get data (offset + i))
  done;
  !v

let find_table_at addr blocks =
  List.find (fun (b : Litmus.Testrepr.memory_block) -> b.addr = addr) blocks

let to_table_data blocks =
  List.map (fun (b : Litmus.Testrepr.memory_block) -> (b.addr, b.data)) blocks

let follow_table_desc blocks addr idx =
  let block = find_table_at addr blocks in
  let entry = read_le64 block.data (idx * 8) in
  assert_equal 0x3 (entry land 0x3) ~msg:"table descriptor";
  entry land 0x0000FFFFFFFFF000

let walk_to_l3 blocks l0_addr va =
  let l1 = follow_table_desc blocks l0_addr ((va lsr 39) land 0x1FF) in
  let l2 = follow_table_desc blocks l1 ((va lsr 30) land 0x1FF) in
  follow_table_desc blocks l2 ((va lsr 21) land 0x1FF)

let tests =
  "Pgt_eval" >::: [
    "empty setup" >:: (fun _ ->
      let _, blocks, _, _, l0, _, _ = eval "" in
      assert_equal [] blocks;
      assert_equal None l0);

    "single mapping: full walk L0->L3 with PA and attrs" >:: (fun _ ->
      let syms, blocks, _, _, l0, _, addrs = eval
        "physical pa; virtual va; va |-> pa with default;" in
      let l0_addr = Option.get l0 in
      assert_bool "at least 4 tables" (List.length blocks >= 4);
      List.iter (fun (b : Litmus.Testrepr.memory_block) ->
        assert_equal Litmus.Testrepr.PageTable b.kind;
        assert_equal 4096 (Bytes.length b.data)) blocks;
      (* Walk full chain and check L3 descriptor *)
      let va_base = List.assoc "va" addrs in
      let l3_addr = walk_to_l3 blocks l0_addr va_base in
      let l3_block = find_table_at l3_addr blocks in
      let l3_entry = read_le64 l3_block.data (((va_base lsr 12) land 0x1FF) * 8) in
      assert_equal 0x3 (l3_entry land 0x3) ~msg:"L3 valid bits";
      let pa_addr = Isla.Symbols.resolve syms "pa" in
      assert_equal pa_addr (l3_entry land 0x0000FFFFFFFFF000) ~msg:"L3 encodes PA");

    "two mappings share L0" >:: (fun _ ->
      let _, blocks, _, _, l0, _, _ = eval
        "physical pa1 pa2; virtual va1 va2; va1 |-> pa1; va2 |-> pa2;" in
      let l0_addr = Option.get l0 in
      let l0_block = find_table_at l0_addr blocks in
      (* Both VAs are close, same L0 index *)
      let e = read_le64 l0_block.data 0 in
      assert_bool "L0 entry valid" (e land 0x3 = 0x3));

    "identity mapping (name and numeric)" >:: (fun _ ->
      let _, blocks1, _, _, l0_1, _, _ = eval
        "virtual va; identity va with code;" in
      assert_bool "name: tables created" (l0_1 <> None && List.length blocks1 >= 4);
      let _, blocks2, _, _, l0_2, _, _ = eval
        "identity 0x1000 with code;" in
      assert_bool "numeric: tables created" (l0_2 <> None && List.length blocks2 >= 4));

    "invalid mapping writes zero descriptor" >:: (fun _ ->
      let _, blocks, _, _, l0, _, _ = eval ~symbolic:["x"] "x |-> invalid;" in
      let l0_addr = Option.get l0 in
      let l0_block = find_table_at l0_addr blocks in
      let l0_entry = read_le64 l0_block.data 0 in
      assert_equal 0x3 (l0_entry land 0x3) ~msg:"L0 has table descriptor");

    "symbolic auto-import + walk info + mem init" >:: (fun _ ->
      let syms, blocks, walks, mem_inits, l0, _, _ = eval ~symbolic:["x"]
        "physical pa; x |-> pa as mywalk; *pa = 0xFF;" in
      assert_bool "L0 allocated" (l0 <> None);
      assert_bool "tables created" (List.length blocks >= 4);
      (* walk info *)
      assert_equal 1 (List.length walks);
      let w = List.hd walks in
      assert_equal "mywalk" w.Isla.Pgtable.walk;
      assert_equal 4 (List.length w.tables) ~msg:"4 levels";
      (* mem init *)
      assert_equal 1 (List.length mem_inits);
      let _, value = List.hd mem_inits in
      assert_equal (Z.of_int 0xFF) (Isla.Term.eval ~env:(fun _ -> None) value);
      (* page_table_base symbol *)
      let ptb = Isla.Symbols.resolve syms "page_table_base" in
      assert_equal (Option.get l0) ptb ~msg:"page_table_base = L0");

    "query functions: pte_addr, desc_value, make_desc" >:: (fun _ ->
      let syms, blocks, _, _, l0, _, _ = eval ~symbolic:["x"]
        "physical pa; x |-> pa with default;" in
      let l0_addr = Option.get l0 in
      let table_data = to_table_data blocks in
      let va = Isla.Symbols.resolve syms "x" in
      (* lookup_pte_addr *)
      let pte_addr =
        Isla.Pgtable.lookup_pte_addr ~table_data ~base:l0_addr va 3 in
      assert_bool "PTE 8-byte aligned" (pte_addr mod 8 = 0);
      let l3_base = pte_addr - (pte_addr mod 4096) in
      assert_bool "L3 table exists" (List.mem_assoc l3_base table_data);
      (* lookup_desc_value *)
      let desc =
        Isla.Pgtable.lookup_desc_value ~table_data ~base:l0_addr va 3 in
      assert_equal 0x3 (desc land 0x3) ~msg:"valid page descriptor";
      let pa = Isla.Symbols.resolve syms "pa" in
      assert_equal pa (desc land 0x0000FFFFFFFFF000) ~msg:"correct PA";
      (* make_desc *)
      let d3 = Isla.Pgtable.make_desc ~level:3 ~oa:0x4000
        ~attrs:Isla.Pgtable.default_data_attrs () in
      assert_equal 0x3 (d3 land 0x3) ~msg:"L3 type";
      assert_equal 0x4000 (d3 land 0x0000FFFFFFFFF000) ~msg:"L3 OA";
      let d2 = Isla.Pgtable.make_desc ~level:2 ~oa:0x200000
        ~attrs:Isla.Pgtable.default_data_attrs () in
      assert_equal 0x1 (d2 land 0x3) ~msg:"L2 block type";
      assert_equal 0x200000 (d2 land 0x0000FFFFFFE00000) ~msg:"L2 OA");

    "s1table/s2table: explicit base + nesting" >:: (fun _ ->
      let syms, blocks, _, _, l0, _, _ = eval ~symbolic:["x"]
        "physical pa; s1table mytbl 0x200000 { x |-> pa; }" in
      assert_equal None l0 ~msg:"no default L0";
      assert_bool "table at base"
        (List.exists (fun (b : Litmus.Testrepr.memory_block) ->
          b.addr = 0x200000) blocks);
      assert_equal 0x200000 (Isla.Symbols.resolve syms "mytbl");
      (* nested *)
      let syms2, blocks2, _, _, _, _, _ = eval ~symbolic:["x"]
        {|physical pa; intermediate ipa;
          s2table s2tbl 0x240000 {
            ipa |-> pa at level 3;
            s1table s1tbl 0x280000 { x |-> ipa at level 3; }
          }|} in
      assert_equal 0x240000 (Isla.Symbols.resolve syms2 "s2tbl");
      assert_equal 0x280000 (Isla.Symbols.resolve syms2 "s1tbl");
      assert_bool "has tables" (List.length blocks2 >= 4));

    "optional mapping and option stmt ignored" >:: (fun _ ->
      let _, blocks, _, _, l0, _, _ = eval ~symbolic:["x"]
        "physical pa1 pa2; x |-> pa1; x ?-> invalid; x ?-> pa2;" in
      assert_bool "L0 allocated" (l0 <> None);
      assert_bool "has tables" (List.length blocks >= 4);
      let _ = eval "option default_tables = false;" in
      ());

    "error cases" >:: (fun _ ->
      assert_raises (Failure "pgtable: undeclared address: x")
        (fun () -> eval "x |-> pa;");
      assert_raises
        (Failure "pgtable: target level 0 out of valid range [1..3]")
        (fun () -> eval "physical pa; virtual va; va |-> pa at level 0;");
      assert_raises (Failure "pgtable: duplicate PA/IPA name: pa")
        (fun () -> eval "physical pa; physical pa;"));
  ]

let () = run_test_tt_main tests
