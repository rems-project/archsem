(** Litmus test runner CLI.

    Usage: litmus_runner <model> <test_dir>

    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    Runs all .toml files from the appropriate subdirectories of test_dir. *)

open Archsem
open Archsem_test

let get_model = function
  | "seq" -> seq_model
  | "ump" -> umProm_model
  | "vmp" -> vmProm_model
  | s -> failwith ("Unknown model: " ^ s ^ ". Use: seq, ump, vmp")

let model_full_name = function
  | "seq" -> "Sequential"
  | "ump" -> "UM Promising"
  | "vmp" -> "VM Promising"
  | s -> s

(** Get all .toml files from a directory, returning (dir_name, file_path) pairs *)
let get_toml_files dir =
  let dir_name = Filename.basename dir in
  if Sys.file_exists dir && Sys.is_directory dir then
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun f ->
         String.length f > 5 &&
         String.sub f (String.length f - 5) 5 = ".toml")
    |> List.sort String.compare
    |> List.map (fun f -> (dir_name, Filename.concat dir f))
  else []

(** Get test directories for a model *)
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
    else [("", path)]
  in

  if files = [] then (
    Printf.eprintf "No test files found for model %s in %s\n" model_name path;
    exit 1
  );

  let total = List.length files in
  Printf.printf "%s%s=== %s Model (%d tests) ===%s\n\n"
    Ansi.bold Ansi.cyan (model_full_name model_name) total Ansi.reset;

  let results = List.mapi (fun i (dir, file) ->
    Printf.printf "%s[%d/%d]%s %s\n%!"
      Ansi.dim (i + 1) total Ansi.reset (Filename.basename file);
    let result = Litmus_runner.run_litmus_test ~model_name model file in
    (dir, file, result)
  ) files in

  (* Group results by directory *)
  let dirs = List.sort_uniq String.compare (List.map (fun (d, _, _) -> d) results) in
  let by_dir dir = List.filter (fun (d, _, _) -> d = dir) results in

  (* Summary *)
  let open Litmus_runner in
  let count_expected lst = List.filter (fun (_, _, r) -> r = Expected) lst |> List.length in
  let count_unexpected lst = List.filter (fun (_, _, r) -> r = Unexpected) lst |> List.length in
  let count_errors lst = List.filter (fun (_, _, r) -> r = ModelError || r = ParseError) lst |> List.length in

  let num_expected = count_expected results in
  let num_unexpected = count_unexpected results in
  let num_errors = count_errors results in

  Printf.printf "\n%s========================================%s\n" Ansi.bold Ansi.reset;
  Printf.printf "%s%s Model Summary%s\n" Ansi.bold (model_full_name model_name) Ansi.reset;
  Printf.printf "----------------------------------------\n";

  (* Per-directory breakdown *)
  List.iter (fun dir ->
    let dir_results = by_dir dir in
    let dir_total = List.length dir_results in
    let dir_expected = count_expected dir_results in
    let dir_unexpected = count_unexpected dir_results in
    let dir_errors = count_errors dir_results in
    let symbol, color =
      if dir_expected = dir_total then (Ansi.check, Ansi.green)
      else if dir_errors > 0 then (Ansi.cross, Ansi.red)
      else (Ansi.dot, Ansi.yellow)
    in
    Printf.printf "  %s%s%s %s/%s  %d/%d"
      color symbol Ansi.reset dir Ansi.reset dir_expected dir_total;
    if dir_unexpected > 0 then
      Printf.printf " %s(%d unexpected)%s" Ansi.yellow dir_unexpected Ansi.reset;
    if dir_errors > 0 then
      Printf.printf " %s(%d errors)%s" Ansi.red dir_errors Ansi.reset;
    Printf.printf "\n"
  ) dirs;

  (* List issues *)
  if num_unexpected > 0 || num_errors > 0 then (
    Printf.printf "----------------------------------------\n";
    List.iter (fun (_, f, r) ->
      match r with
      | Unexpected ->
        Printf.printf "  %s%s%s %s\n" Ansi.yellow Ansi.dot Ansi.reset (Filename.basename f)
      | ModelError | ParseError ->
        Printf.printf "  %s%s%s %s\n" Ansi.red Ansi.cross Ansi.reset (Filename.basename f)
      | Expected -> ()
    ) results
  );

  Printf.printf "----------------------------------------\n";
  let symbol, status_color =
    if num_expected = total then (Ansi.check, Ansi.green)
    else (Ansi.cross, Ansi.red)
  in
  Printf.printf "  %s%s%s %s%d/%d tests expected%s\n"
    status_color symbol Ansi.reset status_color num_expected total Ansi.reset;
  Printf.printf "%s========================================%s\n" Ansi.bold Ansi.reset;

  if num_expected < total then exit 1
