(** Unit tests for Litmus_spec, Litmus_parser, and Litmus_runner. *)

open OUnit2
open Archsem
open Litmus
open Spec
open Utils

(** {1 Helpers} *)

let eor = parse_file "seq/EOR.toml"
let mp = parse_file "ump/MP.toml"

(** {1 RegVal.gen equality} *)

let gen_equality_tests = "RegVal.gen equality" >::: [
  "same integers" >:: (fun _ ->
    assert_bool "" (i 42 = i 42));
  "same strings" >:: (fun _ ->
    assert_bool "" (RegVal.String "hello" = RegVal.String "hello"));
  "empty structs" >:: (fun _ ->
    assert_bool "" (RegVal.Struct [] = RegVal.Struct []));
  "same structs" >:: (fun _ ->
    assert_bool "" (RegVal.Struct [("a", i 1)] = RegVal.Struct [("a", i 1)]));
  "nested structs" >:: (fun _ ->
    assert_bool ""
      (RegVal.Struct [("x", RegVal.Struct [("y", i 1)])] =
       RegVal.Struct [("x", RegVal.Struct [("y", i 1)])]));
  "same arrays" >:: (fun _ ->
    assert_bool "" (RegVal.Array [i 0; i 1] = RegVal.Array [i 0; i 1]));
  "different integers" >:: (fun _ ->
    assert_bool "" (not (i 0 = i 1)));
  "different strings" >:: (fun _ ->
    assert_bool "" (not (RegVal.String "a" = RegVal.String "b")));
  "Int vs String" >:: (fun _ ->
    assert_bool "" (not (i 0 = RegVal.String "0")));
  "Int vs Struct" >:: (fun _ ->
    assert_bool "" (not (i 0 = RegVal.Struct [])));
  "Array vs Struct" >:: (fun _ ->
    assert_bool "" (not (RegVal.Array [i 0] = RegVal.Struct [("0", i 0)])));
  "different struct keys" >:: (fun _ ->
    assert_bool "" (not (RegVal.Struct [("a", i 1)] = RegVal.Struct [("b", i 1)])));
  "different struct lengths" >:: (fun _ ->
    assert_bool ""
      (not (RegVal.Struct [("a", i 1)] = RegVal.Struct [("a", i 1); ("b", i 0)])));
  "different array elements" >:: (fun _ ->
    assert_bool "" (not (RegVal.Array [i 0] = RegVal.Array [i 1])));
  "different array lengths" >:: (fun _ ->
    assert_bool "" (not (RegVal.Array [i 0] = RegVal.Array [i 0; i 1])));
]

(** {1 reg_requirement_equal} *)

let rr_eq = reg_requirement_equal

let reg_requirement_tests = "reg_requirement_equal" >::: [
  "same ReqEq" >:: (fun _ ->
    assert_bool "" (rr_eq (ReqEq (i 1)) (ReqEq (i 1))));
  "different ReqEq" >:: (fun _ ->
    assert_bool "" (not (rr_eq (ReqEq (i 0)) (ReqEq (i 1)))));
  "same ReqNe" >:: (fun _ ->
    assert_bool "" (rr_eq (ReqNe (i 1)) (ReqNe (i 1))));
  "ReqEq vs ReqNe" >:: (fun _ ->
    assert_bool "" (not (rr_eq (ReqEq (i 1)) (ReqNe (i 1)))));
]

(** {1 memory_block_equal} *)

let mb = {
  base = Z.of_int 0x100; size = 8; step = 8;
  data = Bytes.of_string "\x2a\x00\x00\x00\x00\x00\x00\x00";
  name = None; kind = None;
}

let memory_block_tests = "memory_block_equal" >::: [
  "same blocks" >:: (fun _ ->
    assert_bool "" (memory_block_equal mb mb));
  "different base" >:: (fun _ ->
    assert_bool "" (not (memory_block_equal mb { mb with base = Z.of_int 0x200 })));
  "different size" >:: (fun _ ->
    assert_bool "" (not (memory_block_equal mb { mb with size = 4 })));
  "different step" >:: (fun _ ->
    assert_bool "" (not (memory_block_equal mb { mb with step = 4 })));
  "different data" >:: (fun _ ->
    assert_bool "" (not (memory_block_equal mb { mb with data = Bytes.make 8 '\x63' })));
  "different data len" >:: (fun _ ->
    assert_bool "" (not (memory_block_equal mb { mb with data = Bytes.make 4 '\x2a' })));
  "different name" >:: (fun _ ->
    assert_bool "" (not (memory_block_equal mb { mb with name = Some "x" })));
  "different kind" >:: (fun _ ->
    assert_bool "" (not (memory_block_equal mb { mb with kind = Some Data })));
]

(** {1 thread_cond_equal / final_cond_equal} *)

let tc : thread_cond = (0, [(reg "R0", ReqEq (i 1))])

let thread_cond_tests = "thread_cond_equal" >::: [
  "same" >:: (fun _ ->
    assert_bool "" (thread_cond_equal tc tc));
  "different tid" >:: (fun _ ->
    assert_bool "" (not (thread_cond_equal tc (1, snd tc))));
  "different reg" >:: (fun _ ->
    assert_bool "" (not (thread_cond_equal tc (0, [(reg "R1", ReqEq (i 1))]))));
  "different val" >:: (fun _ ->
    assert_bool "" (not (thread_cond_equal tc (0, [(reg "R0", ReqEq (i 0))]))));
]

let obs : final_cond = Observable ([tc], [])

let final_cond_tests = "final_cond_equal" >::: [
  "same Observable" >:: (fun _ ->
    assert_bool "" (final_cond_equal obs obs));
  "Obs vs Unobs" >:: (fun _ ->
    assert_bool "" (not (final_cond_equal obs (Unobservable ([tc], [])))));
  "different threads" >:: (fun _ ->
    assert_bool "" (not (final_cond_equal obs (Observable ([(1, snd tc)], [])))));
]

(** {1 equal (full test)} *)

let t : Spec.t = {
  arch = "Arm"; name = "Test";
  registers = [[(reg "R0", i 0)]];
  memory = [{
    base = Z.of_int 0x500; size = 4; step = 4;
    data = Bytes.of_string "\xca\x00\x00\x00";
    name = None; kind = None;
  }];
  term_cond = [[(Reg.pc, i 0x504)]];
  finals = [Observable ([(0, [(reg "R0", ReqEq (i 0x110))])], [])];
}

let equal_tests = "equal" >::: [
  "same test" >:: (fun _ ->
    assert_bool "" (equal t t));
  "different name" >:: (fun _ ->
    assert_bool "" (not (equal t { t with name = "Other" })));
  "different arch" >:: (fun _ ->
    assert_bool "" (not (equal t { t with arch = "RISC-V" })));
  "different regs" >:: (fun _ ->
    assert_bool "" (not (equal t { t with registers = [[(reg "R1", i 0)]] })));
  "different finals" >:: (fun _ ->
    assert_bool "" (not (equal t { t with finals = [] })));
  "reflexivity (EOR)" >:: (fun _ ->
    assert_bool "" (equal eor eor));
  "reflexivity (MP)" >:: (fun _ ->
    assert_bool "" (equal mp mp));
]

(** {1 toml_to_gen} *)

let tv = Parser.toml_to_gen

let toml_to_gen_tests = "toml_to_gen" >::: [
  "integer" >:: (fun _ ->
    assert_equal (i 42) (tv (Otoml.TomlInteger 42)));
  "string" >:: (fun _ ->
    assert_equal (RegVal.String "hi") (tv (Otoml.TomlString "hi")));
  "inline table" >:: (fun _ ->
    assert_equal
      (RegVal.Struct [("EL", i 0)])
      (tv (Otoml.TomlInlineTable [("EL", Otoml.TomlInteger 0)])));
  "array" >:: (fun _ ->
    assert_equal
      (RegVal.Array [i 1; i 2])
      (tv (Otoml.TomlArray [Otoml.TomlInteger 1; Otoml.TomlInteger 2])));
]

(** {1 parse_to_spec} *)

let parse_tests = "parse_to_spec" >::: [
  "EOR arch" >:: (fun _ ->
    assert_equal "Arm" eor.arch);
  "EOR name" >:: (fun _ ->
    assert_equal "EOR" eor.name);
  "EOR 1 thread" >:: (fun _ ->
    assert_equal 1 (List.length eor.registers));
  "EOR 1 memory block" >:: (fun _ ->
    assert_equal 1 (List.length eor.memory));
  "EOR 1 term_cond" >:: (fun _ ->
    assert_equal 1 (List.length eor.term_cond));
  "EOR 1 outcome" >:: (fun _ ->
    assert_equal 1 (List.length eor.finals));
  "EOR has R0" >:: (fun _ ->
    assert_bool "" (List.mem_assoc (reg "R0") (List.hd eor.registers)));
  "EOR mem base 0x500" >:: (fun _ ->
    assert_bool "" (Z.equal (List.hd eor.memory).base (Z.of_int 0x500)));
  "MP 2 threads" >:: (fun _ ->
    assert_equal 2 (List.length mp.registers));
  "MP 2 term_conds" >:: (fun _ ->
    assert_equal 2 (List.length mp.term_cond));
  "MP 4 finals" >:: (fun _ ->
    assert_equal 4 (List.length mp.finals));
]

(** {1 spec_to_archstate / run_spec} *)

let archstate_runner_tests = "spec_to_archstate / run_spec" >::: [
  "EOR converts to ArchState" >:: (fun _ ->
    ignore (Archstate.spec_to_archstate eor));
  "MP converts to ArchState" >:: (fun _ ->
    ignore (Archstate.spec_to_archstate mp));
  "EOR Expected with seq model" >:: (fun _ ->
    let result, _msgs = Runner.run_spec "seq" eor in
    assert_equal Runner.Expected result);
]

let () = run_test_tt_main ("litmus_spec" >::: [
  gen_equality_tests;
  reg_requirement_tests;
  memory_block_tests;
  thread_cond_tests;
  final_cond_tests;
  equal_tests;
  toml_to_gen_tests;
  parse_tests;
  archstate_runner_tests;
])
