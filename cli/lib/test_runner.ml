open Archsem

let string_of_gen = function
  | RegVal.Number n -> "0x" ^ Z.format "%x" n
  | RegVal.String s -> "\"" ^ s ^ "\""
  | RegVal.Array _ -> "<array>"
  | RegVal.Struct _ -> "<struct>"

(* Returns a list of (register, expected, actual) for mismatches *)
let check_thread (regs : RegMap.t) (checks : (Reg.t * RegVal.gen) list) : (Reg.t * RegVal.gen * RegVal.gen option) list =
  List.filter_map (fun (reg_check, expected_val) ->
    let actual_rv_opt = RegMap.get_opt reg_check regs in
    let actual_gen_opt = Option.map RegVal.to_gen actual_rv_opt in
    let matches =
      match (actual_gen_opt, expected_val) with
      | (Some (RegVal.Number n1), RegVal.Number n2) -> Z.equal n1 n2
      | (Some (RegVal.String s1), RegVal.String s2) -> String.equal s1 s2
      | (Some (RegVal.Struct s1), RegVal.Struct s2) -> s1 = s2
      | _ -> false
    in
    if matches then None else Some (reg_check, expected_val, actual_gen_opt)
  ) checks

(* Returns a list of (tid, mismatches) *)
let check_outcome (arch_state : ArchState.t) (outcome_checks : (int * (Reg.t * RegVal.gen) list) list) =
  List.map (fun (tid, checks) ->
    if tid < List.length (ArchState.regs arch_state) then
       (tid, check_thread (ArchState.reg tid arch_state) checks)
    else
      failwith "Invalid thread ID"
  ) outcome_checks
  |> List.filter (fun (_, mismatches) -> mismatches <> [])

let get_checked_keys (expected_checks : (int * (Reg.t * RegVal.gen) list) list list) =
  let keys = List.flatten expected_checks in
  List.fold_left (fun acc (tid, checks) ->
    List.fold_left (fun acc (reg, _) -> (tid, reg) :: acc) acc checks
  ) [] keys
  |> List.sort_uniq compare

let print_failed_outcome (outcome_idx : int) (num_threads : int) (arch_state : ArchState.t)
    (checked_keys : (int * Reg.t) list) =
  Printf.printf "Outcome %d:\n" outcome_idx;
  for tid = 0 to num_threads - 1 do
    let regs = ArchState.reg tid arch_state in
    try
      let pc_val = RegMap.getZ Reg.pc regs in
      Printf.printf "  Thread %d PC: 0x%s\n" tid (Z.format "%x" pc_val)
    with _ -> ()
  done;

  Printf.printf "  [INFO] Does not match expected results\n";
  List.iter (fun (tid, reg) ->
    let regs = ArchState.reg tid arch_state in
    let val_opt = RegMap.get_opt reg regs |> Option.map RegVal.to_gen in
    Printf.printf "    Actual value Thread %d %s: %s\n"
      tid (Reg.to_string reg) (match val_opt with Some g -> string_of_gen g | None -> "N/A")
  ) checked_keys

let run_test model (arch_state : ArchState.t) (num_threads : int) (fuel : int)
    (termCond : termCond)
    (expected_checks : (int * (Reg.t * RegVal.gen) list) list list) =
  Printf.printf "Running test with fuel %d...\n" fuel;
  let results = model fuel termCond arch_state in

  let checked_keys = get_checked_keys expected_checks in
  let results = List.mapi (fun i res ->
    match res with
    | ArchModel.Res.FinalState fs ->
        (* Check Expected: At least one expected block must match *)
        let all_mismatches = List.map (fun checks -> check_outcome fs checks) expected_checks in
        let matches = List.exists (fun m -> m = []) all_mismatches in
        if expected_checks = [] || matches then (
          true
        ) else (
          print_failed_outcome i num_threads fs checked_keys;
          false
        )
    | ArchModel.Res.Error e ->
        Printf.printf "  Error: %s\n" e;
        false
    | ArchModel.Res.Flagged _ ->
        Printf.printf "  Flagged\n";
        false
  ) results in

  let all_passed = List.for_all (fun x -> x) results in
  if all_passed then Printf.printf "\nRESULT: PASS\n" else Printf.printf "\nRESULT: FAIL\n";
  all_passed


(* Main function that process a file and run the test*)
let process_file model filename : bool =
  try
    let fuel = 1000 in
    let toml = Otoml.Parser.from_file filename in

    let reg_maps = Toml_parser.parse_registers toml in
    let mem_map = Toml_parser.parse_memory toml in
    let arch_state = ArchState.make reg_maps mem_map in

    let num_threads = List.length reg_maps in
    let termConds = Toml_parser.parse_termCond num_threads toml in
    let expected_checks = Toml_parser.parse_expected toml in

    Printf.printf "\nSuccessfully parsed %s\n" filename;

    run_test model arch_state num_threads fuel termConds expected_checks

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
