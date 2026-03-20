(** Litmus test runner. *)

(** {1 Types} *)

type test_result =
  | Expected  (** Outcome matched test expectations *)
  | Unexpected  (** Outcome did not match test expectations *)
  | ModelError  (** Model produced errors during execution *)
  | NoBehaviour  (** Model produces no behaviours (model bug) *)
  | SetupError  (** Pre-execution error: parsing, config, conversion, assembly *)

(** {1 Display Helpers} *)
let rec string_of_regval_gen : Archsem.RegValGen.t -> string = function
  | Number z -> Printf.sprintf "0x%s" (Z.format "%x" z)
  | String s -> Printf.sprintf "\"%s\"" s
  | Array vs ->
      Printf.sprintf "[%s]" (String.concat ", " (List.map string_of_regval_gen vs))
  | Struct fields ->
      Printf.sprintf "{ %s }"
        (String.concat ", "
           (List.map
              (fun (k, v) -> Printf.sprintf "%s = %s" k (string_of_regval_gen v))
              fields
           )
        )

let req_to_string (reg, req) =
  let (op, v) =
    match req with Testrepr.ReqEq v -> ("=", v) | Testrepr.ReqNe v -> ("!=", v)
  in
  Printf.sprintf "%s%s%s" reg op (string_of_regval_gen v)

let cond_to_string cond =
  List.map
    (fun (tid, reqs) ->
       Printf.sprintf "%d:{%s}" tid
         (String.concat "," (List.map req_to_string reqs))
     )
    cond
  |> String.concat " "

let mem_cond_to_string mem_reqs =
  List.map
    (fun (mc : Testrepr.mem_cond) ->
       let (op, value) =
         match mc.req with
         | Testrepr.MemEq value -> ("=", value)
         | Testrepr.MemNe value -> ("!=", value)
       in
       Printf.sprintf "*0x%x[%d]%s0x%s" mc.addr mc.size op (Z.format "%x" value)
     )
    mem_reqs
  |> String.concat " "

let string_of_result = function
  | Expected -> "EXPECTED"
  | Unexpected -> "UNEXPECTED"
  | ModelError -> "MODEL ERROR"
  | NoBehaviour -> "NO BEHAVIOUR"
  | SetupError -> "SETUP ERROR"

let styled_result r =
  let color =
    match r with
    | Expected -> Terminal.green
    | Unexpected -> Terminal.yellow
    | _ -> Terminal.red
  in
  color ^ string_of_result r ^ Terminal.reset

module Make (Arch : Archsem.Arch) = struct
  open Arch
  module AS = ToArchState.Make (Arch)

  let check_outcome (fs : ArchState.t) (cond : Testrepr.thread_cond list) : bool =
    List.for_all
      (fun (tid, reqs) ->
         let regs = ArchState.reg tid fs in
         List.for_all
           (fun (name, req) ->
              let reg = Reg.of_string name in
              match RegMap.get_opt reg regs with
              | None ->
                  Error.raise_error_ctx Runner ~ctx:("outcome." ^ name)
                    "register not found in final state"
              | Some rv -> (
                match req with
                | Testrepr.ReqEq exp -> rv = RegVal.of_gen reg exp
                | Testrepr.ReqNe exp -> rv = RegVal.of_gen reg exp
              )
            )
           reqs
       )
      cond

  let check_mem_outcome (fs : ArchState.t) (mem_conds : Testrepr.mem_cond list) :
    bool
    =
    let mem = ArchState.mem fs in
    List.for_all
      (fun (mc : Testrepr.mem_cond) ->
         match MemMap.lookup_opt mc.addr mc.size mem with
         | None ->
             Error.raise_error_ctx Runner
               ~ctx:(Printf.sprintf "outcome.*0x%x" mc.addr)
               "memory not found at address"
         | Some actual -> (
           match mc.req with
           | Testrepr.MemEq expected -> Z.equal actual expected
           | Testrepr.MemNe expected -> not (Z.equal actual expected)
         )
       )
      mem_conds

  let run_executions model init fuel term finals =
    let msgs = ref [] in
    let msg s = msgs := s :: !msgs in
    let results = model fuel term init in

    let observable =
      List.filter_map
        (function Testrepr.Observable (c, mc) -> Some (c, mc) | _ -> None)
        finals
    in
    let unobservable =
      List.filter_map
        (function Testrepr.Unobservable (c, mc) -> Some (c, mc) | _ -> None)
        finals
    in

    let errors =
      List.filter_map
        (function ArchModel.Res.Error e -> Some e | _ -> None)
        results
    in
    let final_states =
      List.filter_map
        (function ArchModel.Res.FinalState fs -> Some fs | _ -> None)
        results
    in
    let flags =
      List.filter_map
        (function ArchModel.Res.Flagged x -> Some x | _ -> None)
        results
    in

    List.iter
      (fun e ->
         msg (Printf.sprintf "%s[Error]%s %s" Terminal.red Terminal.reset e)
       )
      errors;
    if flags <> [] then msg "Flagged";

    let observable_ok =
      List.for_all
        (fun (cond, mem_cond) ->
           let matched =
             List.exists
               (fun fs -> check_outcome fs cond && check_mem_outcome fs mem_cond)
               final_states
           in
           if (not matched) && final_states <> [] then
             msg
               (Printf.sprintf "%sObservable not found%s: %s %s" Terminal.red
                  Terminal.reset (cond_to_string cond)
                  (mem_cond_to_string mem_cond)
               );
           matched
         )
        observable
    in

    let unobservable_ok =
      List.for_all Fun.id
        (List.mapi
           (fun i fs ->
              match
                List.find_opt
                  (fun (cond, mem_cond) ->
                     check_outcome fs cond && check_mem_outcome fs mem_cond
                   )
                  unobservable
              with
              | Some (cond, mem_cond) ->
                  msg
                    (Printf.sprintf
                       "%sUnobservable found%s in execution %d: %s %s"
                       Terminal.red Terminal.reset (i + 1) (cond_to_string cond)
                       (mem_cond_to_string mem_cond)
                    );
                  false
              | None -> true
            )
           final_states
        )
    in

    let result =
      if results = [] then NoBehaviour
      else if errors <> [] then ModelError
      else if observable_ok && unobservable_ok then Expected
      else Unexpected
    in
    (result, List.rev !msgs)

  let run_testrepr model (test : Testrepr.t) =
    let fuel = Config.get_fuel () in
    let (init, term) = AS.testrepr_to_archstate test in
    run_executions model init fuel term test.finals

  let print_error name origin msg =
    Printf.printf "  %s%s%s %s  %s[%s] %s%s\n" Terminal.red Terminal.cross
      Terminal.reset name Terminal.red origin msg Terminal.reset

  let run_litmus_test ~parse model filename =
    let name = Filename.basename filename in
    if not (Sys.file_exists filename) then (
      print_error name "config" "file not found";
      SetupError
    )
    else
      try
        let test = parse filename in
        (* Inner try: exceptions here are model crashes, not parse errors *)
        try
          let (result, msgs) = run_testrepr model test in
          let (icon, color) =
            match result with
            | Expected -> (Terminal.check, Terminal.green)
            | Unexpected -> (Terminal.cross, Terminal.yellow)
            | _ -> (Terminal.cross, Terminal.red)
          in
          Printf.printf "  %s%s%s %s\n" color icon Terminal.reset name;
          List.iter (fun m -> Printf.printf "    %s\n" m) msgs;
          result
        with
        | Error.Cli_error (origin, msg) ->
            print_error name (Error.string_of_origin origin) msg;
            ModelError
        | exn ->
            print_error name "model" (Printexc.to_string exn);
            ModelError
      with
      | Error.Cli_error (origin, msg) ->
          print_error name (Error.string_of_origin origin) msg;
          SetupError
      | Otoml.Parse_error (pos, msg) ->
          let pos_str =
            Option.fold ~none:"?"
              ~some:(fun (l, c) -> Printf.sprintf "%d:%d" l c)
              pos
          in
          print_error name "parser"
            (Printf.sprintf "parse error at %s: %s" pos_str msg);
          SetupError
      | Failure msg ->
          print_error name "setup" msg;
          SetupError
      | exn ->
          print_error name "setup" (Printexc.to_string exn);
          SetupError
end
