(** Litmus test runner CLI.

    Usage: main <model> <path> [--isla] [--usermode]

    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    Flags:
      --isla     Input is isla format (converts to archsem before running)
      --usermode Use usermode conversion (no page tables, for UM tests) *)

open Archsem
open Archsem_test
open Litmus_runner

let get_model = function
  | "seq" -> seq_model
  | "ump" -> umProm_model
  | "vmp" -> fun fuel term initState -> vmProm_model fuel term initState
  | s -> failwith ("Unknown model: " ^ s ^ ". Use: seq, ump, vmp")

let get_toml_files dir =
  if Sys.file_exists dir && Sys.is_directory dir then
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun f ->
         String.length f > 5 &&
         String.sub f (String.length f - 5) 5 = ".toml")
    |> List.sort String.compare
    |> List.map (Filename.concat dir)
  else []

(** Recursively get all .toml files from a directory *)
let rec get_toml_files_recursive dir =
  if not (Sys.file_exists dir && Sys.is_directory dir) then []
  else
    let entries = Sys.readdir dir |> Array.to_list in
    let files = List.filter (fun f ->
      let path = Filename.concat dir f in
      Sys.file_exists path && not (Sys.is_directory path) &&
      String.length f > 5 && String.sub f (String.length f - 5) 5 = ".toml"
    ) entries in
    let subdirs = List.filter (fun f ->
      let path = Filename.concat dir f in
      Sys.is_directory path && f <> "." && f <> ".." && f <> "@all"
    ) entries in
    let local_files = List.map (fun f -> Filename.concat dir f) files in
    let subdir_files = List.concat_map (fun d ->
      get_toml_files_recursive (Filename.concat dir d)
    ) subdirs in
    local_files @ subdir_files


(** Convert an isla test to archsem format, return temp file path *)
let convert_isla_test ~usermode isla_file =
  let temp_file = Filename.temp_file "archsem_" ".toml" in
  let oc = open_out temp_file in
  (try
    Isla_converter.Symbols.reset ();
    Isla_converter.Allocator.reset ();
    Isla_converter.Converter.process_toml ~usermode isla_file oc;
    close_out oc;
    Some temp_file
  with e ->
    close_out oc;
    Sys.remove temp_file;
    Printf.eprintf "  %s[Convert]%s %s: %s\n"
      Terminal.red Terminal.reset (Filename.basename isla_file) (Printexc.to_string e);
    None)

(** Parse command line arguments *)
let parse_args () =
  let usage = Printf.sprintf
    "Usage: %s <model: seq|ump|vmp> <path> [--isla] [--usermode]" Sys.argv.(0) in
  let model_name = ref "" in
  let path = ref "" in
  let isla_mode = ref false in
  let usermode = ref false in
  let args = Array.to_list Sys.argv |> List.tl in
  let rec parse = function
    | [] -> ()
    | "--isla" :: rest -> isla_mode := true; parse rest
    | "--usermode" :: rest -> usermode := true; parse rest
    | arg :: rest ->
        if !model_name = "" then model_name := arg
        else if !path = "" then path := arg
        else failwith usage;
        parse rest
  in
  parse args;
  if !model_name = "" || !path = "" then failwith usage;
  (!model_name, !path, !isla_mode, !usermode)

let () =
  let (model_name, path, isla_mode, usermode) =
    try parse_args ()
    with Failure msg -> Printf.eprintf "%s\n" msg; exit 1
  in
  let model = get_model model_name in

  (* Get test files *)
  let files, _temp_files =
    if isla_mode then (
      (* Isla mode: find all .toml files recursively and convert *)
      let isla_files =
        if Sys.is_directory path then get_toml_files_recursive path
        else [path]
      in
      Printf.printf "%sConverting %d isla tests...%s\n%!"
        Terminal.dim (List.length isla_files) Terminal.reset;
      let converted = List.filter_map (fun f ->
        match convert_isla_test ~usermode f with
        | Some temp -> Some (temp, temp)
        | None -> None
      ) isla_files in
      let files = List.map fst converted in
      let temps = List.map snd converted in
      (files, temps)
    ) else (
      (* Archsem mode: scan path directly *)
      let files =
        if Sys.is_directory path then get_toml_files path
        else [path]
      in
      (files, [])
    )
  in

  if files = [] then (
    Printf.eprintf "No test files found for model %s in %s\n" model_name path;
    exit 1
  );

  Terminal.print_header model_name (List.length files);

  let results = List.map (fun file ->
    let result = run_litmus_test model file in
    (file, result)
  ) files in

  let count pred = List.length (List.filter (fun (_, r) -> pred r) results) in
  let num_expected = count (fun r -> r = Expected) in
  let num_unexpected = count (fun r -> r = Unexpected) in
  let num_model_error = count (fun r -> r = ModelError) in
  let num_no_behaviour = count (fun r -> r = NoBehaviour) in
  let num_parse_error = count (fun r -> r = ParseError) in
  let total = List.length results in

  let failures = List.filter (fun (_, r) -> r <> Expected) results
    |> List.map (fun (f, r) -> (Filename.basename f, result_to_string r)) in

  Terminal.print_summary ~model_name ~total
    ~expected:num_expected ~unexpected:num_unexpected
    ~model_error:num_model_error ~parse_error:num_parse_error
    ~no_behaviour:num_no_behaviour ~failures;

  if num_expected <> total then exit 1
