(** Litmus test runner CLI.

    Usage: litmus_runner <model> <path ...>
    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    Each path can be a directory (scanned for .toml files) or a .toml file. *)

open Archsem
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

let run_tests model_name model files =
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

(** {1 CLI } *)

open Cmdliner
open Cmdliner.Term.Syntax

(** Common positional argument for list of tests*)
let test_path_term =
  let doc = "The tests to run. Can be either single files or directories \
             containing test files" in
  Arg.(non_empty & pos_all file [] & info [] ~doc ~docv:"TESTS")

(** The sequential model command *)
let cmd_seq =
  let run =
    let+ paths = test_path_term in
    let files = get_all_tests paths in
    run_tests "seq" seq_model files
  in
  let info =
    let doc = "Run sequential model" in
    Cmd.(info "seq" ~doc)
  in
  Cmd.v info run

(** The user-mode promising command *)
let cmd_ump =
  let run =
    let+ paths = test_path_term in
    let files = get_all_tests paths in
    run_tests "ump" umProm_model files
  in
  let info =
    let doc = "Run user-mode promising model" in
    Cmd.(info "ump" ~doc)
  in
  Cmd.v info run

(** The virtual-memory promising command *)
let cmd_vmp =
  let bbm_mode =
    let off_info =
      let doc = "Turn BBM checking off" in
      Arg.(info ["bbm-off"] ~doc)
    in
    let lax_info =
      let doc = "Make BBM checking lax: if a page table entries is missing, it \
                 just ignores it" in
      Arg.(info ["bbm-lax"] ~doc)
    in
    let strict_info =
      let doc = "Make BBM checking strict: if a page table entries is missing, \
                 the model catches fire" in
      Arg.(info ["bbm-strict"] ~doc)
    in
    Arg.(value &
         vflag BBM.Off (* ← default is Off for now *)
           [(BBM.Off, off_info); (BBM.Lax, lax_info); (BBM.Strict, strict_info)])
  in
  let run =
    let+ paths = test_path_term
    and+ bbm_param = bbm_mode in
    let files = get_all_tests paths in
    run_tests "vmp" (vmProm_model ~bbm_param) files
  in
  let info =
    let doc =
      "Run virtual-memory promising model. Only one --bbm-* option can be active \
       at the same time, the default is --bbm-off" in
    Cmd.(info "vmp" ~doc)
  in
  Cmd.v info run

(** The main archsem command *)
let cmd =
  let info =
    let doc = "ArchSem model runner" in
    Cmd.(info "archsem" ~doc)
  in
  Cmd.group info [cmd_seq; cmd_ump; cmd_vmp]

let () = exit (Cmd.eval cmd)
