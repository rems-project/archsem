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

let get_reg_val_number = function
  | RegVal.Number z -> z
  | _ -> Z.zero

let print_failed_outcome (i : int) (arch_state : ArchState.t)
    (enforced_outcomes : Litmus_parser.cond list) =
  Printf.printf "SAFETY VIOLATION: Execution %d does not match any enforced outcome\n" (i + 1);

  (* For each enforced outcome, show how well this execution matched it *)
  List.iteri (fun oi outcome ->
    Printf.printf "  vs Enforced outcome #%d:\n" (oi + 1);
    List.iter (fun (tid, expected_regs) ->
      Printf.printf "    Thread %d:\n" tid;
      let actual_regs = ArchState.reg tid arch_state in
      List.iter (fun (reg, req) ->
        let actual_opt = RegMap.get_opt reg actual_regs |> Option.map RegVal.to_gen in
        let actual_str = match actual_opt with Some g -> string_of_gen g | None -> "N/A" in
        let (op_str, expected_val) = match req with
          | Litmus_parser.Eq v -> ("eq", v)
          | Litmus_parser.Neq v -> ("ne", v)
        in
        let expected_str = string_of_gen expected_val in
        let matches = match actual_opt, req with
          | Some actual, Litmus_parser.Eq expected -> actual = expected
          | Some actual, Litmus_parser.Neq expected -> actual <> expected
          | None, _ -> false
        in
        let mark = if matches then "✓" else "✗" in
        Printf.printf "      %s: actual=%s, expected=%s (%s) %s\n"
          (Reg.to_string reg) actual_str expected_str op_str mark
      ) expected_regs
    ) outcome
  ) enforced_outcomes

let run_executions model (arch_state : ArchState.t) (_num_threads : int) (fuel : int)
    (termCond : termCond)
    (outcomes : Litmus_parser.outcome list) : bool =
  Printf.printf "Running test with fuel %d...\n%!" fuel;
  let results = model fuel termCond arch_state in

  let allowed_outcomes = List.filter_map
    (function Litmus_parser.Allowed c -> Some c | _ -> None) outcomes in
  let enforced_outcomes = List.filter_map
    (function Litmus_parser.Enforced c -> Some c | _ -> None) outcomes in

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
      List.exists (fun fs -> check_outcome fs expected) valid_final_states
    ) allowed_outcomes
  in

  (* Safety (enforced): For ALL executions, each must match AT LEAST ONE of the enforced
     outcomes. No execution may produce a result outside the enforced set. *)
  let passed_safety =
    if enforced_outcomes = [] then true
    else
      List.for_all (fun (i, fs_opt) ->
        match fs_opt with
        | Some fs ->
          let is_match = List.exists (fun c -> check_outcome fs c) enforced_outcomes in
          if not is_match then print_failed_outcome i fs enforced_outcomes;
          is_match
        | None -> false (* Errors/Flagged fail the test *)
      ) analyzed_results
  in

  passed_coverage && passed_safety

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
