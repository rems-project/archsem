open Archsem
(* open Archsem.Semantics - REMOVED: Unbound module *)

(* Helper function to print a register value properly *)
let string_of_gen = function
  | RegVal.Number z -> Printf.sprintf "0x%s" (Z.format "%x" z)
  | RegVal.String s -> Format.sprintf "\"%s\"" s
  | RegVal.Struct fields ->
    let fields_str = List.map (fun (k, v) ->
      let v_str = match v with
        | RegVal.Number z -> Printf.sprintf "0x%s" (Z.format "%x" z)
        | RegVal.String s -> Format.sprintf "\"%s\"" s
        | _ -> "?"
      in
      Printf.sprintf "%s = %s" k v_str
    ) fields in
    Printf.sprintf "{ %s }" (String.concat ", " fields_str)
  | _ -> "?"

(* Checks if a final state matches a single outcome (all thread conditions must match) *)
let check_outcome (fs : ArchState.t) (outcome : Litmus_parser.cond) : bool =
  List.for_all (fun (tid, expected_regs) ->
    let actual_regs = ArchState.reg tid fs in
    List.for_all (fun (reg, req) ->
      match RegMap.get_opt reg actual_regs with
      | Some actual_val ->
        let actual_gen = RegVal.to_gen actual_val in
        (match req with
        | Litmus_parser.Eq expected_val -> actual_gen = expected_val
        | Litmus_parser.Neq expected_val -> actual_gen <> expected_val)
      | None -> false
    ) expected_regs
  ) outcome

let print_forbidden_violation (i : int) (arch_state : ArchState.t)
    (forbidden_outcome : Litmus_parser.cond) =
  Printf.printf "FORBIDDEN OUTCOME OBSERVED: Execution %d matched a forbidden outcome!\n" (i + 1);
  List.iter (fun (tid, expected_regs) ->
    Printf.printf "  Thread %d:\n" tid;
    let actual_regs = ArchState.reg tid arch_state in
    List.iter (fun (reg, req) ->
      let actual_opt = RegMap.get_opt reg actual_regs |> Option.map RegVal.to_gen in
      let actual_str = match actual_opt with Some g -> string_of_gen g | None -> "N/A" in
      let (op_str, expected_val) = match req with
        | Litmus_parser.Eq v -> ("eq", v)
        | Litmus_parser.Neq v -> ("ne", v)
      in
      let expected_str = string_of_gen expected_val in
      Printf.printf "    %s: actual=%s, forbidden=%s (%s)\n"
        (Reg.to_string reg) actual_str expected_str op_str
    ) expected_regs
  ) forbidden_outcome

(** Runs model executions and checks coverage (allowed) and forbidden constraints.
    Returns true if all allowed outcomes are covered and no forbidden outcomes are observed. *)
let run_executions model (arch_state : ArchState.t) (_num_threads : int) (fuel : int)
    (termCond : termCond)
    (outcomes : Litmus_parser.outcome list) : bool =
  Printf.printf "Running test with fuel %d...\n%!" fuel;
  let results = model fuel termCond arch_state in

  let allowed_outcomes = List.filter_map
    (function Litmus_parser.Allowed c -> Some c | _ -> None) outcomes in
  let forbidden_outcomes = List.filter_map
    (function Litmus_parser.Forbidden c -> Some c | _ -> None) outcomes in

  (* Process all results to identify matches and print errors if needed *)
  let analyzed_results = List.mapi (fun i res ->
    match res with
    | ArchModel.Res.FinalState fs ->
      (* For analyzed results, we essentially check if it matches ANY constraint.
          But validation logic is separate below. *)
      (i, Some fs)
    | ArchModel.Res.Error e ->
      Printf.printf "  Error: %s\n" e;
      (i, None)
    | ArchModel.Res.Flagged _ ->
      Printf.printf "  Flagged\n";
      (i, None)
  ) results in

  (* Collect valid final states for coverage checking *)
  let valid_final_states =
    List.filter_map (function ArchModel.Res.FinalState fs -> Some fs | _ -> None) results
  in

  (* Coverage (allowed): For ALL allowed checks, there must exist SOME execution
     that matches it. This verifies the model can exhibit all expected behaviors. *)
  let passed_coverage =
    List.for_all (fun expected ->
      let matched = List.exists (fun fs -> check_outcome fs expected) valid_final_states in
      if not matched && valid_final_states <> [] then (
        Printf.printf "COVERAGE FAIL: No execution matched expected outcome:\n";
        List.iter (fun (tid, regs) ->
          Printf.printf "  Thread %d: %s\n" tid
            (String.concat ", " (List.map (fun (reg, req) ->
              let (op, v) = match req with Litmus_parser.Eq v -> ("=", v) | Litmus_parser.Neq v -> ("!=", v) in
              Printf.sprintf "%s%s%s" (Reg.to_string reg) op (string_of_gen v)
            ) regs))
        ) expected;
        (* Show what we actually got *)
        if List.length valid_final_states <= 25 then (
          Printf.printf "  Actual executions (%d total):\n" (List.length valid_final_states);
          List.iteri (fun i fs ->
            Printf.printf "    Execution %d:\n" (i+1);
            List.iter (fun (tid, regs) ->
              let actual_regs = ArchState.reg tid fs in
              List.iter (fun (reg, _) ->
                let actual_opt = RegMap.get_opt reg actual_regs |> Option.map RegVal.to_gen in
                let actual_str = match actual_opt with Some g -> string_of_gen g | None -> "N/A" in
                Printf.printf "      %d:%s = %s\n" tid (Reg.to_string reg) actual_str
              ) regs
            ) expected
          ) valid_final_states
        ) else
          Printf.printf "  Got %d executions, none matching\n" (List.length valid_final_states)
      );
      matched
    ) allowed_outcomes
  in

  (* Forbidden (unsat): NO execution should match ANY forbidden outcome.
     If any execution matches a forbidden outcome, the test fails. *)
  let passed_forbidden =
    if forbidden_outcomes = [] then true
    else
      List.for_all (fun (i, fs_opt) ->
        match fs_opt with
        | Some fs ->
          (* Check if this execution matches ANY forbidden outcome *)
          let violation = List.find_opt (fun c -> check_outcome fs c) forbidden_outcomes in
          (match violation with
           | Some forbidden_cond ->
               print_forbidden_violation i fs forbidden_cond;
               false (* This execution matched a forbidden outcome - FAIL *)
           | None -> true) (* This execution didn't match any forbidden outcome - OK *)
        | None -> true (* Errors don't count against forbidden check *)
      ) analyzed_results
  in

  (* Report if no valid executions at all *)
  if valid_final_states = [] && allowed_outcomes <> [] then
    Printf.printf "NO VALID EXECUTIONS: All %d executions failed with errors\n" (List.length results);

  passed_coverage && passed_forbidden

(** Main entry point: parses a TOML litmus test file and runs it with the given model.
    Returns true if the test passes (coverage + safety checks). *)
let run_litmus_test model filename =
  if not (Sys.file_exists filename) then (
    Printf.eprintf "File not found: %s\n" filename;
    false
  ) else
    try
    let toml = Otoml.Parser.from_file filename in
    let fuel = Otoml.find_opt toml Litmus_parser.get_int ["fuel"]
               |> Option.value ~default:1000 in

    (* Parse Architecture State *)
    let reg_maps = Litmus_parser.parse_registers toml in
    let mem_map = Litmus_parser.parse_memory toml in
    let arch_state = ArchState.make reg_maps mem_map in

    let num_threads = List.length reg_maps in
    let termConds = Litmus_parser.parse_termCond num_threads toml in
    let outcome = Litmus_parser.parse_outcomes toml in

    Printf.printf "\nSuccessfully parsed %s\n" filename;
    let passed = run_executions model arch_state num_threads fuel termConds outcome in
    if passed then Printf.printf "\nRESULT: PASS\n"
    else Printf.printf "\nRESULT: FAIL\n";
    passed

  with
  | Otoml.Parse_error (pos, msg) ->
      let loc = match pos with Some (l, c) -> Printf.sprintf "%d:%d" l c | None -> "unknown" in
      Printf.eprintf "TOML Parse Error at %s: %s\n" loc msg;
      false
  | Failure msg ->
      Printf.eprintf "Error in %s: %s\n" filename msg;
      false
  | exn ->
      Printf.eprintf "Unexpected error in %s: %s\n" filename (Printexc.to_string exn);
      false
