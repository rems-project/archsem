(** Litmus test runner.

    Executes a model on parsed litmus tests and validates outcomes:
    - Observable: Interesting relaxed behavior the test wants to capture
    - Unobservable: Relaxed behavior the test does not expect to occur *)

open Archsem

(** {1 Types} *)

type test_result =
  | Expected
  | Unexpected
  | ModelError
  | NoBehaviour
  | ParseError

(** {1 Display Helpers} *)

let rec string_of_regval_gen = function
  | RegVal.Number z -> Printf.sprintf "0x%s" (Z.format "%x" z)
  | RegVal.String s -> Printf.sprintf "\"%s\"" s
  | RegVal.Array vs ->
    Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_regval_gen vs))
  | RegVal.Struct fields ->
    Printf.sprintf "{ %s }" (String.concat ", "
      (List.map (fun (k, v) -> Printf.sprintf "%s = %s" k (string_of_regval_gen v)) fields))

let req_to_string (reg, req) =
  let op, v = match req with
    | Spec.ReqEq v -> ("=", v)
    | Spec.ReqNe v -> ("!=", v)
  in
  Printf.sprintf "%s%s%s" (Reg.to_string reg) op (string_of_regval_gen v)

let cond_to_string cond =
  List.map (fun (tid, reqs) ->
    Printf.sprintf "%d:{%s}" tid (String.concat "," (List.map req_to_string reqs))
  ) cond |> String.concat " "

(** {1 Outcome Checking} *)

let check_outcome (fs : ArchState.t) (cond : Spec.thread_cond list) : bool =
  List.for_all (fun (tid, reqs) ->
    let regs = ArchState.reg tid fs in
    List.for_all (fun (reg, req) ->
      match RegMap.get_opt reg regs with
      | None ->
        failwith ("[[outcome]] register not found in final state: " ^ Reg.to_string reg)
      | Some rv ->
        let actual = RegVal.to_gen rv in
        (match req with
         | Spec.ReqEq exp -> actual = exp
         | Spec.ReqNe exp -> actual <> exp)
    ) reqs
  ) cond

(** {1 Test Execution} *)

let run_executions model init fuel term finals =
  let msgs = ref [] in
  let msg s = msgs := s :: !msgs in
  let results = model fuel term init in

  let observable = List.filter_map
    (function Spec.Observable c -> Some c | _ -> None) finals in
  let unobservable = List.filter_map
    (function Spec.Unobservable c -> Some c | _ -> None) finals in

  let errors = List.filter_map (function
    | ArchModel.Res.Error e -> Some e
    | _ -> None) results in
  let final_states = List.filter_map (function
    | ArchModel.Res.FinalState fs -> Some fs
    | _ -> None) results in
  let flags = List.filter_map (function
    | ArchModel.Res.Flagged x -> Some x
    | _ -> None) results in

  List.iter (fun e ->
    msg (Printf.sprintf "%s[Error]%s %s" Terminal.red Terminal.reset e)) errors;
  if flags <> [] then msg "Flagged";

  let observable_ok = List.for_all (fun cond ->
    let matched = List.exists (fun fs -> check_outcome fs cond) final_states in
    if not matched && final_states <> [] then
      msg (Printf.sprintf "%sObservable not found%s: %s"
        Terminal.red Terminal.reset (cond_to_string cond));
    matched
  ) observable in

  let unobservable_ok = List.for_all Fun.id (List.mapi (fun i fs ->
    match List.find_opt (fun c -> check_outcome fs c) unobservable with
    | Some cond ->
      msg (Printf.sprintf "%sUnobservable found%s in execution %d: %s"
        Terminal.red Terminal.reset (i+1) (cond_to_string cond));
      false
    | None -> true
  ) final_states) in

  let result =
    if results = [] then NoBehaviour
    else if errors <> [] then ModelError
    else if observable_ok && unobservable_ok then Expected
    else Unexpected
  in
  (result, List.rev !msgs)

(** {1 Entry Point} *)

let result_to_string = function
  | Expected -> Terminal.green ^ "EXPECTED" ^ Terminal.reset
  | Unexpected -> Terminal.yellow ^ "UNEXPECTED" ^ Terminal.reset
  | ModelError -> Terminal.red ^ "MODEL ERROR" ^ Terminal.reset
  | NoBehaviour -> Terminal.red ^ "NO BEHAVIOUR" ^ Terminal.reset
  | ParseError -> Terminal.red ^ "PARSE ERROR" ^ Terminal.reset

let default_fuel = 1000

let run_spec model (test : Spec.t) =
  let init, term, finals = Archstate.spec_to_archstate test in
  run_executions model init default_fuel term finals

let run_litmus_test model filename =
  let name = Filename.basename filename in
  if not (Sys.file_exists filename) then (
    Printf.printf "  %s✗%s %s  %sfile not found%s\n"
      Terminal.red Terminal.reset name Terminal.red Terminal.reset;
    ParseError
  ) else try
    let toml = Otoml.Parser.from_file filename in
    let test = Parser.parse_to_spec toml in
    let result, msgs = run_spec model test in
    let icon, color = match result with
      | Expected -> Terminal.check, Terminal.green
      | Unexpected -> Terminal.cross, Terminal.yellow
      | _ -> Terminal.cross, Terminal.red
    in
    Printf.printf "  %s%s%s %s\n" color icon Terminal.reset name;
    List.iter (fun m -> Printf.printf "    %s\n" m) msgs;
    result
  with
  | Otoml.Parse_error (pos, msg) ->
    Printf.printf "  %s✗%s %s  %sparse error at %s: %s%s\n" Terminal.red Terminal.reset name
      Terminal.red (Option.fold ~none:"?" ~some:(fun (l,c) -> Printf.sprintf "%d:%d" l c) pos)
      msg Terminal.reset;
    ParseError
  | Failure msg ->
    Printf.printf "  %s✗%s %s  %s%s%s\n"
      Terminal.red Terminal.reset name Terminal.red msg Terminal.reset;
    ParseError
  | exn ->
    Printf.printf "  %s✗%s %s  %s%s%s\n" Terminal.red Terminal.reset name
      Terminal.red (Printexc.to_string exn) Terminal.reset;
    ParseError
