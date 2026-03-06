(** Litmus test runner CLI.

    Usage: litmus_runner <model> <path ...>
    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    Each path can be a directory (scanned for .toml files) or a .toml file. *)

open Litmus
open Runner

(** {1 Running litmus tests} *)

let get_toml_files dir =
  if Sys.file_exists dir && Sys.is_directory dir then
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".toml")
    |> List.sort String.compare
    |> List.map (Filename.concat dir)
  else []

let get_all_tests paths =
  let files = List.concat_map (fun path ->
    if Sys.is_directory path then get_toml_files path
    else [path]
  ) paths in
  if files = [] then (
    Printf.eprintf "No test files found in %s\n" (String.concat ", " paths);
    exit 1
  );
  files

let run_tests model_name files =
  Terminal.print_header model_name (List.length files);

  let results = List.map (fun file ->
    let result = run_litmus_test model_name file in
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

(** {1 CLI } *)

open Cmdliner
open Cmdliner.Term.Syntax

(** Common arguments *)

let test_path_term =
  let doc = "The tests to run. Can be either single files or directories \
             containing test files" in
  Arg.(non_empty & pos_all file [] & info [] ~doc ~docv:"TESTS")

let config_term =
  let doc = "Path to a TOML configuration file" in
  Arg.(required & opt (some file) None & info ["config"; "c"] ~doc ~docv:"FILE")

(** Set the global config from the CLI --config flag. *)
let init_config path =
  Config.set (Config.of_file path)

(** Model subcommands *)

let model_cmd model_name ~doc =
  let run =
    let+ paths = test_path_term
    and+ config = config_term in
    init_config config;
    let files = get_all_tests paths in
    run_tests model_name files
  in
  Cmd.v (Cmd.info model_name ~doc) run

let cmd_seq = model_cmd "seq" ~doc:"Run sequential model"
let cmd_ump = model_cmd "ump" ~doc:"Run user-mode promising model"
let cmd_vmp = model_cmd "vmp" ~doc:"Run virtual-memory promising model"

(** The main archsem command *)
let cmd =
  let info =
    let doc = "ArchSem model runner" in
    Cmd.(info "archsem" ~doc)
  in
  Cmd.group info [cmd_seq; cmd_ump; cmd_vmp]

let () = exit (Cmd.eval cmd)
