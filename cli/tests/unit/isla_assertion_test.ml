(** Unit tests for Isla.Assertion. *)

open Archsem
open Litmus
open OUnit2

let syms = fst (Isla.Symbols.alloc_data Isla.Symbols.empty "x")

let tests = "Isla.Assertion" >::: [
  "parse register eq" >:: (fun _ ->
    ignore (Isla.Assertion.parse_string "1:X0 = 1"));
  "parse conjunction" >:: (fun _ ->
    ignore (Isla.Assertion.parse_string "1:X0 = 1 & 2:X0 = 0"));
  "parse memory" >:: (fun _ ->
    ignore (Isla.Assertion.parse_string "*x = 2"));
  "parse negation" >:: (fun _ ->
    ignore (Isla.Assertion.parse_string "~(1:X0 = 1)"));
  "parse hex values" >:: (fun _ ->
    ignore (Isla.Assertion.parse_string "0:X0 = 0x2a"));
  "sat + simple -> 1 Observable" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "1:X0 = 1" in
    assert_equal 1 (List.length conds);
    assert_bool "" (match List.hd conds with Spec.Observable _ -> true | _ -> false));
  "sat + conjunction -> 1 Observable with 2 threads" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "1:X0 = 1 & 2:X0 = 0" in
    assert_equal 1 (List.length conds);
    assert_bool "" (match List.hd conds with
      | Spec.Observable (tcs, _) -> List.length tcs = 2
      | _ -> false));
  "sat + negation -> Unobservable" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "~(1:X0 = 1)" in
    assert_equal 1 (List.length conds);
    assert_bool "" (match List.hd conds with Spec.Unobservable _ -> true | _ -> false));
  "unsat -> Unobservable" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"unsat" ~syms "1:X0 = 1" in
    assert_equal 1 (List.length conds);
    assert_bool "" (match List.hd conds with Spec.Unobservable _ -> true | _ -> false));
  "disjunction -> 2 Observables" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "1:X0 = 1 | 2:X0 = 0" in
    assert_equal 2 (List.length conds));
  "mem assertion in Observable mem_cond" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "*x = 2 & 1:X0 = 1" in
    assert_bool "" (match conds with
      | [Spec.Observable (_, mcs)] -> List.length mcs = 1
      | _ -> false));
  "mem-only assertion -> Observable with empty regs" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "*x = 2" in
    assert_bool "" (match conds with
      | [Spec.Observable (tcs, mcs)] -> tcs = [] && List.length mcs = 1
      | _ -> false));
  "trivial assertion -> empty" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "true" in
    assert_equal [] conds);
  "X5 normalized to R5" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "0:X5 = 1" in
    assert_bool "" (match conds with
      | [Spec.Observable ([(0, [(r, _)])], _)] -> r = Reg.r 5
      | _ -> false));
  "W3 normalized to R3" >:: (fun _ ->
    let conds = Isla.Assertion.to_final_conds ~expect:"sat" ~syms "0:W3 = 0" in
    assert_bool "" (match conds with
      | [Spec.Observable ([(0, [(r, _)])], _)] -> r = Reg.r 3
      | _ -> false));
]

let () =
  Litmus.Config.set (Otoml.Parser.from_string "[arch]\ndefault_mem_size = 8\n");
  run_test_tt_main tests
