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

(** {1 Shared Helpers} *)

let rec string_of_gen = function
  | Litmus_parser.Number z -> Printf.sprintf "0x%s" (Z.format "%x" z)
  | Litmus_parser.String s -> Printf.sprintf "\"%s\"" s
  | Litmus_parser.Array vs -> Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_gen vs))
  | Litmus_parser.Struct fields ->
    Printf.sprintf "{ %s }" (String.concat ", "
      (List.map (fun (k, v) -> Printf.sprintf "%s = %s" k (string_of_gen v)) fields))

let req_to_string (name, req) =
  let op, v = match req with
    | Litmus_parser.Eq v -> ("=", v)
    | Litmus_parser.Neq v -> ("!=", v)
  in
  Printf.sprintf "%s%s%s" name op (string_of_gen v)

let cond_to_string cond =
  List.map (fun (tid, reqs) ->
    Printf.sprintf "%d:{%s}" tid (String.concat "," (List.map req_to_string reqs))
  ) cond |> String.concat " "

let result_to_string = function
  | Expected -> Ansi.green ^ "expected" ^ Ansi.reset
  | Unexpected -> Ansi.yellow ^ "unexpected" ^ Ansi.reset
  | ModelError -> Ansi.red ^ "model error" ^ Ansi.reset
  | ParseError -> Ansi.red ^ "parse error" ^ Ansi.reset

(** Check observable/unobservable outcomes against a list of final states.
    [check_one] maps a final state and condition to a bool. *)
let check_outcomes ~check_one final_states (outcomes : Litmus_parser.outcome list) =
  let observable = List.filter_map
    (function Litmus_parser.Observable c -> Some c | _ -> None) outcomes in
  let unobservable = List.filter_map
    (function Litmus_parser.Unobservable c -> Some c | _ -> None) outcomes in

  let observable_ok = List.for_all (fun cond ->
    let matched = List.exists (fun fs -> check_one fs cond) final_states in
    if not matched && final_states <> [] then
      Printf.printf "    %sObservable not found%s: %s\n"
        Ansi.yellow Ansi.reset (cond_to_string cond);
    matched
  ) observable in

  let unobservable_ok = List.for_all Fun.id (List.mapi (fun i fs ->
    match List.find_opt (fun c -> check_one fs c) unobservable with
    | Some cond ->
      Printf.printf "    %sUnobservable found%s (exec %d): %s\n"
        Ansi.yellow Ansi.reset (i+1) (cond_to_string cond);
      false
    | None -> true
  ) final_states) in

  (observable_ok, unobservable_ok, observable)

(** Build memory from parsed blocks using an inserti function. *)
let build_mem inserti empty (blocks : Litmus_parser.mem_block list) =
  List.fold_left (fun mm { Litmus_parser.base; size; step; data } ->
    match data with
    | `Single v -> inserti base size v mm
    | `Array vs ->
      let n = List.length vs in
      let step = Option.value step ~default:(if n > 0 then size / n else 0) in
      List.fold_left (fun (addr, mm) v ->
        (addr + step, inserti addr step v mm)
      ) (base, mm) vs |> snd
  ) empty blocks

(** Generic build_term_cond parametrized over register types. *)
let generic_build_term_cond
    (type r rv rm)
    ~(resolve_reg : string -> r option)
    ~(get_opt : r -> rm -> rv option)
    ~(to_gen : rv -> Litmus_parser.gen)
    (test : Litmus_parser.parsed_test) : (rm -> bool) list =
  List.map (fun reqs rm ->
    List.for_all (fun (name, req) ->
      match resolve_reg name with
      | None -> false
      | Some reg ->
        match get_opt reg rm, req with
        | Some rv, Litmus_parser.Eq exp -> to_gen rv = exp
        | Some rv, Litmus_parser.Neq exp -> to_gen rv <> exp
        | None, _ -> false
    ) reqs
  ) test.term_conds

(** Generic check_outcome parametrized over register and state types. *)
let generic_check_outcome
    (type r rv rm s)
    ~(resolve_reg : string -> r option)
    ~(get_opt : r -> rm -> rv option)
    ~(to_gen : rv -> Litmus_parser.gen)
    ~(state_reg : int -> s -> rm)
    (fs : s) (cond : Litmus_parser.cond) : bool =
  List.for_all (fun (tid, reqs) ->
    let regs = state_reg tid fs in
    List.for_all (fun (name, req) ->
      match resolve_reg name with
      | None -> false
      | Some reg ->
        match get_opt reg regs with
        | None -> false
        | Some rv ->
          let actual = to_gen rv in
          (match req with
           | Litmus_parser.Eq exp -> actual = exp
           | Litmus_parser.Neq exp -> actual <> exp)
    ) reqs
  ) cond

(** {1 Tiny Model} *)

module Tiny = struct
  (** Map unified register names to armv9_types names.
      TOML uses "PC"; armv9_types expects "_PC".
      Some registers like TTBR0_EL1 are "_TTBR0_EL1" in armv9_types (128-bit). *)
  let resolve_reg name =
    if name = "PSTATE" then Some RegTiny.pstate
    else if name = "PC" then Some RegTiny.pc
    else match RegTiny.of_string name with
    | Some _ as r -> r
    | None -> RegTiny.of_string ("_" ^ name)

  (** Default PSTATE: EL=0, SP=0, all flags zero *)
  let default_pstate =
    Litmus_parser.Struct [("EL", Number Z.zero); ("SP", Number Z.zero)]

  let build_state (test : Litmus_parser.parsed_test) =
    let regs = List.map (fun thread ->
      let has_pstate = List.exists (fun (name, _) -> name = "PSTATE") thread in
      let thread = if has_pstate then thread
        else thread @ [("PSTATE", default_pstate)] in
      List.fold_left (fun rm (name, value) ->
        match resolve_reg name with
        | None -> rm
        | Some reg ->
          match RegValTiny.of_gen reg value with
          | Ok rv -> RegMapTiny.insert rv rm
          | Error msg -> failwith (Printf.sprintf "Register %s: %s" name msg)
      ) RegMapTiny.empty thread
    ) test.threads in
    let mem = build_mem MemMapTiny.inserti MemMapTiny.empty test.memory in
    (ArchStateTiny.make regs mem, regs)

  let build_term_cond = generic_build_term_cond
    ~resolve_reg ~get_opt:RegMapTiny.get_opt ~to_gen:RegValTiny.to_gen

  let check_outcome = generic_check_outcome
    ~resolve_reg ~get_opt:RegMapTiny.get_opt ~to_gen:RegValTiny.to_gen
    ~state_reg:ArchStateTiny.reg

  let run_executions model init fuel term outcomes =
    let results = model fuel term init in
    let errors = List.filter_map (function
      | ArchModelTiny.Res.Error e -> Some e | _ -> None) results in
    let final_states = List.filter_map (function
      | ArchModelTiny.Res.FinalState fs -> Some fs | _ -> None) results in

    List.iter (fun e ->
      Printf.printf "    %s[Model]%s %s\n" Ansi.red Ansi.reset e
    ) errors;

    let (observable_ok, unobservable_ok, observable) =
      check_outcomes ~check_one:check_outcome final_states outcomes in

    if final_states = [] && observable <> [] then
      Printf.printf "    %sNo valid executions%s (all %d errored)\n"
        Ansi.red Ansi.reset (List.length results);

    if errors <> [] then ModelError
    else if observable_ok && unobservable_ok then Expected
    else Unexpected
end

(** {1 Full Model} *)

module Full = struct
  let resolve_reg name =
    if name = "PSTATE" then Some Reg.pstate
    else if name = "_PC" then Some Reg.pc
    else match Reg.of_string name with
    | Some _ as r -> r
    | None -> Reg.of_string ("_" ^ name)

  (** Build a full PSTATE value from a struct with partial fields.
      All 30 fields default to 0. *)
  let build_pstate_from_struct fields =
    let get_field name default =
      match List.assoc_opt name fields with
      | Some (Litmus_parser.Number z) -> z
      | _ -> default
    in
    let zero = Z.zero in
    let f name = (name, Litmus_parser.Number (get_field name zero)) in
    Litmus_parser.Struct [
      f "N"; f "Z"; f "C"; f "V"; f "D"; f "A"; f "I"; f "F";
      f "EXLOCK"; f "PAN"; f "UAO"; f "DIT"; f "TCO"; f "PM";
      f "PPEND"; f "BTYPE"; f "ZA"; f "SM"; f "ALLINT"; f "SS";
      f "IL"; f "EL"; f "nRW"; f "SP"; f "Q"; f "GE"; f "SSBS";
      f "IT"; f "J"; f "T"; f "E"; f "M";
    ]

  let build_state (test : Litmus_parser.parsed_test) =
    let regs = List.map (fun thread ->
      let rm = RegMap.with_all_defaults () in
      List.fold_left (fun rm (name, value) ->
        match resolve_reg name with
        | None -> rm
        | Some reg ->
          (* Special handling for PSTATE: expand with default fields *)
          let value = if name = "PSTATE" then
            match value with
            | Litmus_parser.Struct fields -> build_pstate_from_struct fields
            | v -> v
          else value in
          let rm = (match RegVal.of_gen reg value with
            | Ok rv -> RegMap.insert rv rm
            | Error msg -> failwith (Printf.sprintf "Register %s: %s" name msg))
          in
          (* If setting PC, also set _PC (sail-arm reads _PC for instruction fetch) *)
          if reg = Reg.pc then (
            match RegVal.of_gen Reg.internal_pc value with
            | Ok rv -> RegMap.insert rv rm
            | Error msg -> failwith (Printf.sprintf "_PC: %s" msg)
          ) else rm
      ) rm thread
    ) test.threads in
    let mem = build_mem MemMap.inserti MemMap.empty test.memory in
    (ArchState.make regs mem, regs)

  let build_term_cond = generic_build_term_cond
    ~resolve_reg ~get_opt:RegMap.get_opt ~to_gen:RegVal.to_gen

  let check_outcome = generic_check_outcome
    ~resolve_reg ~get_opt:RegMap.get_opt ~to_gen:RegVal.to_gen
    ~state_reg:ArchState.reg

  let run_executions model init fuel term outcomes =
    let results = model fuel term init in
    let errors = List.filter_map (function
      | ArchModel.Res.Error e -> Some e | _ -> None) results in
    let final_states = List.filter_map (function
      | ArchModel.Res.FinalState fs -> Some fs | _ -> None) results in

    (* Error-tolerant: only print errors when no successful states *)
    if final_states = [] then
      List.iter (fun e ->
        Printf.printf "    %s[Model]%s %s\n" Ansi.red Ansi.reset e
      ) errors
    else if errors <> [] then
      Printf.printf "    %s[Model]%s %d error branches (expected nondeterminism)\n"
        Ansi.dim Ansi.reset (List.length errors);

    let (observable_ok, unobservable_ok, observable) =
      check_outcomes ~check_one:check_outcome final_states outcomes in

    if final_states = [] && errors <> [] then (
      Printf.printf "    %sNo valid executions%s (all %d errored)\n"
        Ansi.red Ansi.reset (List.length results);
      ModelError)
    else if final_states = [] && observable <> [] then (
      Printf.printf "    %sNo valid executions%s (no results)\n"
        Ansi.red Ansi.reset;
      ModelError)
    else if observable_ok && unobservable_ok then Expected
    else Unexpected
end

(** {1 Entry Points} *)

let run_test ~model_name ~parse_and_run filename =
  if not (Sys.file_exists filename) then (
    Printf.printf "  %s->%s %sfile not found%s\n"
      Ansi.dim Ansi.reset Ansi.red Ansi.reset;
    ParseError
  ) else try
    let test = Litmus_parser.parse_file filename in
    Printf.printf "  %sRunning with model %s and fuel %d...%s\n%!"
      Ansi.dim model_name test.fuel Ansi.reset;
    let (result, num_threads) = parse_and_run test in
    Printf.printf "  %s->%s %s %s(%d threads)%s\n"
      Ansi.dim Ansi.reset (result_to_string result)
      Ansi.dim num_threads Ansi.reset;
    result
  with
  | Otoml.Parse_error (pos, msg) ->
    Printf.printf "  %s->%s %s[Parser]%s %s at %s\n"
      Ansi.dim Ansi.reset Ansi.red Ansi.reset msg
      (Option.fold ~none:"?" ~some:(fun (l,c) -> Printf.sprintf "%d:%d" l c) pos);
    ParseError
  | Failure msg ->
    Printf.printf "  %s->%s %s[Config]%s %s\n"
      Ansi.dim Ansi.reset Ansi.red Ansi.reset msg;
    ParseError
  | exn ->
    Printf.printf "  %s->%s %s[Error]%s %s\n"
      Ansi.dim Ansi.reset Ansi.red Ansi.reset (Printexc.to_string exn);
    ParseError

let run_litmus_test_tiny ~model_name model filename =
  run_test ~model_name ~parse_and_run:(fun test ->
    let (init, regs) = Tiny.build_state test in
    let term = Tiny.build_term_cond test in
    let result = Tiny.run_executions model init test.fuel term test.outcomes in
    (result, List.length regs)
  ) filename

let run_litmus_test_full ~model_name model filename =
  run_test ~model_name ~parse_and_run:(fun test ->
    let (init, regs) = Full.build_state test in
    let term = Full.build_term_cond test in
    let result = Full.run_executions model init test.fuel term test.outcomes in
    (result, List.length regs)
  ) filename
