(** Litmus test runner CLI.

    Usage: litmus_runner <model> <path ...>
    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    Each path can be a directory (scanned for .toml files) or a .toml file. *)

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

let () =
  if Array.length Sys.argv < 3 then (
    Printf.eprintf "Usage: %s <model: seq|ump|vmp> <path ...>\n" Sys.argv.(0);
    exit 1
  );
  let model_name = Sys.argv.(1) in
  let model = get_model model_name in
  let paths = Array.to_list (Array.sub Sys.argv 2 (Array.length Sys.argv - 2)) in

  let files = List.concat_map (fun path ->
    if Sys.is_directory path then get_toml_files path
    else [path]
  ) paths in

  if files = [] then (
    Printf.eprintf "No test files found for model %s in %s\n" model_name (String.concat ", " paths);
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
