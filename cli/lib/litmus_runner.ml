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

let get_checked_keys (expected_checks : (int * (Reg.t * RegVal.gen) list) list list) =
  List.concat (List.map (fun checks ->
    List.concat (List.map (fun (tid, regs) ->
      List.map (fun (reg, _) -> (tid, reg)) regs
    ) checks)
  ) expected_checks)
  |> List.sort_uniq compare

(* Checks if a given final state matches ONE of the expected outcomes *)
let check_outcome (fs : ArchState.t) (checks : (int * (Reg.t * RegVal.gen) list) list) =
  List.filter (fun (tid, expected_regs) ->
      let actual_regs = ArchState.reg tid fs in
      List.exists (fun (reg, expected_val) ->
        match RegMap.get_opt reg actual_regs with
        | Some actual_val ->
             let actual_gen = RegVal.to_gen actual_val in
             if actual_gen <> expected_val then (
                 (* Printf.printf "Mismatch Thread %d Register %s: expected %s, got %s\n"
                    tid (Reg.to_string reg) (string_of_gen expected_val) (string_of_gen actual_gen); *)
                 true
             ) else false
        | None -> true
      ) expected_regs
  ) checks

let get_reg_val_number = function
  | RegVal.Number z -> z
  | _ -> Z.zero

let print_failed_outcome (i : int) (num_threads : int) (arch_state : ArchState.t) (checked_keys : (int * Reg.t) list) =
  Printf.printf "Result %d:\n" (i + 1);
  for tid = 0 to num_threads - 1 do
     let pc_val =
       match RegMap.get_opt Reg.pc (ArchState.reg tid arch_state) with
       | Some v -> get_reg_val_number (RegVal.to_gen v)
       | None -> Z.zero
     in
     Printf.printf "  Thread %d PC: 0x%s\n" tid (Z.format "%x" pc_val);
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
    (expected_checks : (int * (Reg.t * RegVal.gen) list) list list)
    (outcome : string) =
  Printf.printf "Running test with fuel %d...\n" fuel;
  let results = model fuel termCond arch_state in

  let checked_keys = get_checked_keys expected_checks in

  let check_fs fs =
      let all_mismatches = List.map (fun checks -> check_outcome fs checks) expected_checks in
      expected_checks = [] || List.exists (fun m -> m = []) all_mismatches
  in

  (* Process all results to identify matches and print errors if needed *)
  let analyzed_results = List.mapi (fun i res ->
    match res with
    | ArchModel.Res.FinalState fs ->
        let is_match = check_fs fs in
        (i, Some fs, is_match)
    | ArchModel.Res.Error e ->
        Printf.printf "  Error: %s\n" e;
        (i, None, false)
    | ArchModel.Res.Flagged _ ->
        Printf.printf "  Flagged\n";
        (i, None, false)
  ) results in

  (* Collect valid final states for coverage checking *)
  let valid_final_states =
    List.filter_map (function ArchModel.Res.FinalState fs -> Some fs | _ -> None) results
  in

  let passed =
    match outcome with
    | "allowed" ->
        (* Coverage: The model must produce all allowed results found in the expected set *)
        List.for_all (fun expected ->
            List.exists (fun fs -> check_outcome fs expected = []) valid_final_states
        ) expected_checks
    | "enforced" ->
        (* Safety: All model outcomes must be one of the enforced outcomes *)
        List.for_all (fun (i, fs_opt, is_match) ->
           match fs_opt with
           | Some fs ->
               if not is_match then print_failed_outcome i num_threads fs checked_keys;
               is_match
           | None -> false (* Errors/Flagged fail the test *)
        ) analyzed_results
    | _ ->
        Printf.printf "Unknown outcome type: %s (expected 'allowed' or 'enforced')\n" outcome;
        false
  in

  if passed then Printf.printf "\nRESULT: PASS\n" else Printf.printf "\nRESULT: FAIL\n";
  passed

let process_file model filename =
  if not (Sys.file_exists filename) then (
    Printf.eprintf "File not found: %s\n" filename;
    false
  ) else
    try
    let toml = Otoml.Parser.from_file filename in
    let fuel = match Otoml.find_opt toml (function Otoml.TomlInteger i -> i | _ -> 1000) ["fuel"] with
      | Some f -> f
      | None -> 1000
    in

    (* Parse Architecture State *)
    let reg_maps = Litmus_parser.parse_registers toml in
    let mem_map = Litmus_parser.parse_memory toml in
    let arch_state = ArchState.make reg_maps mem_map in

    let num_threads = List.length reg_maps in
    let termConds = Litmus_parser.parse_termCond num_threads toml in
    let outcome, expected_checks = Litmus_parser.parse_outcomes toml in

    Printf.printf "\nSuccessfully parsed %s\n" filename;

    run_test model arch_state num_threads fuel termConds expected_checks outcome

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
