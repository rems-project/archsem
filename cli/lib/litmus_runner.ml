(** Litmus test runner.

    Executes a model on parsed litmus tests and validates outcomes:
    - Observable: Interesting relaxed behavior the test wants to capture
    - Unobservable: Relaxed behavior the test does not expect to occur *)

open Archsem

(** {1 Result Types} *)

type test_result =
  | Expected     (** Outcome matched test expectations *)
  | Unexpected   (** Outcome did not match test expectations *)
  | ModelError   (** Model produced errors during execution *)
  | ParseError   (** Parser or configuration error *)

(** {1 ANSI Colors} *)

let c_reset = "\027[0m"
let c_bold = "\027[1m"
let c_red = "\027[31m"
let c_green = "\027[32m"
let c_yellow = "\027[33m"
let c_cyan = "\027[36m"

(** {1 Helpers} *)

let rec string_of_gen = function
  | RegVal.Number z -> Printf.sprintf "0x%s" (Z.format "%x" z)
  | RegVal.String s -> Printf.sprintf "\"%s\"" s
  | RegVal.Array vs -> Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_gen vs))
  | RegVal.Struct fields ->
    Printf.sprintf "{ %s }" (String.concat ", "
      (List.map (fun (k, v) -> Printf.sprintf "%s = %s" k (string_of_gen v)) fields))

let req_to_string (reg, req) =
  let op, v = match req with
    | Litmus_parser.Eq v -> ("=", v)
    | Litmus_parser.Neq v -> ("!=", v)
  in
  Printf.sprintf "%s%s%s" (Reg.to_string reg) op (string_of_gen v)

(** {1 Outcome Checking} *)

let check_outcome (fs : ArchState.t) (cond : Litmus_parser.cond) : bool =
  List.for_all (fun (tid, reqs) ->
    let regs = ArchState.reg tid fs in
    List.for_all (fun (reg, req) ->
      match RegMap.get_opt reg regs with
      | None -> false
      | Some rv ->
        let actual = RegVal.to_gen rv in
        (match req with
         | Litmus_parser.Eq exp -> actual = exp
         | Litmus_parser.Neq exp -> actual <> exp)
    ) reqs
  ) cond

(** {1 Test Execution} *)

let run_executions model_name model (init : ArchState.t) (fuel : int) (term : termCond)
    (outcomes : Litmus_parser.outcome list) : test_result =
  Printf.printf "Running with %s%s%s%s, fuel=%d...\n%!"
    c_bold c_cyan model_name c_reset fuel;
  let results = model fuel term init in

  let observable = List.filter_map
    (function Litmus_parser.Observable c -> Some c | _ -> None) outcomes in
  let unobservable = List.filter_map
    (function Litmus_parser.Unobservable c -> Some c | _ -> None) outcomes in

  let errors = List.filter_map (function
    | ArchModel.Res.Error e -> Some e
    | _ -> None) results in
  let final_states = List.filter_map (function
    | ArchModel.Res.FinalState fs -> Some fs
    | _ -> None) results in

  List.iter (fun e -> Printf.printf "  %s[Model] Error%s: %s\n" c_red c_reset e) errors;
  if List.exists (function ArchModel.Res.Flagged _ -> true | _ -> false) results then
    Printf.printf "  Flagged\n";

  (* Observable: interesting relaxed behaviors the test wants to capture *)
  let observable_ok = List.for_all (fun cond ->
    let matched = List.exists (fun fs -> check_outcome fs cond) final_states in
    if not matched && final_states <> [] then
      Printf.printf "%sOBSERVABLE NOT FOUND%s: %s\n" c_red c_reset
        (List.map (fun (tid, reqs) ->
          Printf.sprintf "%d:{%s}" tid (String.concat "," (List.map req_to_string reqs))
        ) cond |> String.concat " ");
    matched
  ) observable in

  (* Unobservable: relaxed behaviors the test does not expect to occur *)
  let unobservable_ok = List.for_all Fun.id (List.mapi (fun i fs ->
    match List.find_opt (fun c -> check_outcome fs c) unobservable with
    | Some cond ->
      Printf.printf "%sUNOBSERVABLE FOUND%s in execution %d: %s\n" c_red c_reset (i+1)
        (List.map (fun (tid, reqs) ->
          Printf.sprintf "%d:{%s}" tid (String.concat "," (List.map req_to_string reqs))
        ) cond |> String.concat " ");
      false
    | None -> true
  ) final_states) in

  if final_states = [] && observable <> [] then
    Printf.printf "%sNO VALID EXECUTIONS%s: All %d failed\n" c_red c_reset (List.length results);

  if errors <> [] then ModelError
  else if observable_ok && unobservable_ok then Expected
  else Unexpected

(** {1 Entry Point} *)

let result_to_string = function
  | Expected -> c_green ^ "EXPECTED" ^ c_reset
  | Unexpected -> c_yellow ^ "UNEXPECTED" ^ c_reset
  | ModelError -> c_red ^ "MODEL ERROR" ^ c_reset
  | ParseError -> c_red ^ "PARSE ERROR" ^ c_reset

let run_litmus_test model_name model filename =
  if not (Sys.file_exists filename) then
    (Printf.eprintf "File not found: %s\n" filename; ParseError)
  else try
    let toml = Otoml.Parser.from_file filename in
    let fuel = Otoml.find_opt toml Litmus_parser.get_int ["fuel"] |> Option.value ~default:1000 in
    let regs = Litmus_parser.parse_registers toml in
    let mem = Litmus_parser.parse_memory toml in
    let init = ArchState.make regs mem in
    let term = Litmus_parser.parse_termCond (List.length regs) toml in
    let outcomes = Litmus_parser.parse_outcomes toml in

    Printf.printf "\nParsed %s\n" filename;
    let result = run_executions model_name model init fuel term outcomes in
    Printf.printf "RESULT: %s\n\n" (result_to_string result);
    result
  with
  | Otoml.Parse_error (pos, msg) ->
    Printf.eprintf "[Parser] error at %s: %s\n"
      (Option.fold ~none:"?" ~some:(fun (l,c) -> Printf.sprintf "%d:%d" l c) pos) msg; ParseError
  | Failure msg -> Printf.eprintf "%s\n" msg; ParseError
  | exn -> Printf.eprintf "[Unexpected] %s\n" (Printexc.to_string exn); ParseError
