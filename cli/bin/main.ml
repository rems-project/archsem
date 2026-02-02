(** Litmus test runner CLI.

    Usage: litmus_runner <model> <test_dir>

    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    Runs all .toml files from the appropriate subdirectories of test_dir. *)

open Archsem

let get_model = function
  | "seq" -> seq_model
  | "ump" -> umProm_model
  | "vmp" -> vmProm_model
  | s -> failwith ("Unknown model: " ^ s ^ ". Use: seq, ump, vmp")

(** Get all .toml files from a directory *)
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

(** Get test directories for a model.
    Each model runs all tests from weaker models plus its own:
    - seq: seq only
    - ump: seq + ump
    - vmp: seq + ump + vmp *)
let get_test_dirs model_name base_dir =
  let dirs = match model_name with
    | "seq" -> ["seq"]
    | "ump" -> ["seq"; "ump"]
    | "vmp" -> ["seq"; "ump"; "vmp"]
    | _ -> []
  in
  List.map (Filename.concat base_dir) dirs

(** Get test files for a model from a base directory *)
let get_test_files model_name base_dir =
  get_test_dirs model_name base_dir
  |> List.concat_map get_toml_files

let () =
  if Array.length Sys.argv < 3 then (
    Printf.eprintf "Usage: %s <model: seq|ump|vmp> <file.toml|directory>\n" Sys.argv.(0);
    exit 1
  );
  let model_name = Sys.argv.(1) in
  let model = get_model model_name in
  let path = Sys.argv.(2) in

  let files =
    if Sys.is_directory path then get_test_files model_name path
    else [path]
  in

  if files = [] then (
    Printf.eprintf "No test files found for model %s in %s\n" model_name path;
    exit 1
  );

  let results = List.map (fun file ->
    let result = Archsem_test.Litmus_runner.run_litmus_test model_name model file in
    (file, result)
  ) files in

  (* Summary *)
  let open Archsem_test.Litmus_runner in
  let num_expected = List.filter (fun (_, r) -> r = Expected) results |> List.length in
  let num_unexpected = List.filter (fun (_, r) -> r = Unexpected) results |> List.length in
  let num_model_error = List.filter (fun (_, r) -> r = ModelError) results |> List.length in
  let num_parse_error = List.filter (fun (_, r) -> r = ParseError) results |> List.length in
  let total = List.length results in
  Printf.printf "\n========================================\n";
  Printf.printf "Results: %d/%d tests expected\n" num_expected total;

  if num_unexpected > 0 then (
    Printf.printf "Unexpected:\n";
    List.iter (fun (f, r) -> if r = Unexpected then Printf.printf "  - %s\n" f) results
  );
  if num_model_error > 0 then (
    Printf.printf "Model errors:\n";
    List.iter (fun (f, r) -> if r = ModelError then Printf.printf "  - %s\n" f) results
  );
  if num_parse_error > 0 then (
    Printf.printf "Parse errors:\n";
    List.iter (fun (f, r) -> if r = ParseError then Printf.printf "  - %s\n" f) results
  );
  if num_expected < total then exit 1
