(** Litmus test runner CLI.

    Usage: archsem <model> [--format archsem|isla] <path ...>
    Models: seq (sequential), ump (UM Promising), vmp (VM Promising), x86_tso (X86 TSO)

    Each path can be a directory (scanned for .toml files) or a .toml file. *)

open Archsem
open Litmus
open Runner

module ArmRunner = Runner.Make (Arm)
module X86Runner = Runner.Make (X86)

(** {1 Running litmus tests} *)

type format =
  | Archsem
  | Isla

let parse_testfile fmt filename =
  assert (Filename.extension filename = ".toml");
  let fmt = match fmt with
    | Some fmt -> fmt
    | None ->
      let name = Filename.remove_extension filename in
      let ext = Filename.extension name in
      match ext with
      | ".litmus" -> Isla
      | ".archsem" -> Archsem
      | _ -> failwith "Could not guess test format from filename. Only \
                       .archsem.toml and .litmus.toml are supported"
  in
  let toml = Otoml.Parser.from_file filename in
  match fmt with
  | Archsem -> Parser.parse_to_testrepr toml
  | Isla ->
      toml
      |> Isla.Ir.of_toml
      |> Isla.Normalize.apply
      |> Isla.Converter.to_testrepr

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

let run_tests model_name run_test files =
  Terminal.print_header model_name (List.length files);

  let results = List.map (fun file ->
    let result = run_test file in
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

let config_term =
  let doc = "Path to a TOML configuration file. Guessed from the first test in \
             the list if not specified" in
  Arg.(value & opt (some file) None & info ["config"; "c"] ~doc ~docv:"FILE")

let path_and_conf_term =
  let+ paths = test_path_term
  and+ conf = config_term in
  let files = get_all_tests paths in
  let conf =
    match conf with
    | Some conf -> conf
    | None ->
      let file = List.hd files in
      let arch = Arch_id.guess_from_test file in
      match Config.default_path_for_arch arch with
      | Some conf -> conf
      | None ->
        Printf.ksprintf failwith
          "Unable to find %s.toml automatically" (Arch_id.to_string arch)
  in
  Config.load conf;
  files

let format_term =
  let doc = "Input format: $(b,archsem) or $(b,isla). If not specified, it is \
             guessed from extension .litmus.toml or .archsem.toml" in
  let format_enum = Arg.enum ["archsem", Archsem; "isla", Isla] in
  Arg.(value & opt (some format_enum) None & info ["format"; "f"] ~doc ~docv:"FMT")

(** The sequential model command *)
let cmd_seq =
  let run =
    let+ files = path_and_conf_term
    and+ fmt = format_term in
    let parse = parse_testfile fmt in
    assert (Config.get_arch () = Arch_id.Arm);
    run_tests "seq" (ArmRunner.run_litmus_test ~parse Arm.(seq_model tiny_isa)) files
  in
  let info =
    let doc = "Run sequential model" in
    Cmd.(info "seq" ~doc)
  in
  Cmd.v info run

(** The user-mode promising command *)
let cmd_ump =
  let run =
    let+ files = path_and_conf_term
    and+ fmt = format_term in
    let parse = parse_testfile fmt in
    assert (Config.get_arch () = Arch_id.Arm);
    run_tests "ump" (ArmRunner.run_litmus_test ~parse Arm.(umProm_model tiny_isa)) files
  in
  let info =
    let doc = "Run user-mode promising model" in
    Cmd.(info "ump" ~doc)
  in
  Cmd.v info run

let bbm_of_config () =
  match Otoml.find_opt (Config.get ()) (Otoml.get_string) ["vmp"; "bbm"] with
  | Some "lax" -> Arm.BBM.Lax
  | Some "strict" -> Arm.BBM.Strict
  | Some "off" -> Arm.BBM.Off
  | Some s ->
    Printf.ksprintf failwith
      "Config key vmp.bbm contains %s which is not off, lax or strict" s
  | _ ->
    failwith
      "Config key vmp.bbm is unspecified in config, please specify on CLI with --bbm"

(** The virtual-memory promising command *)
let cmd_vmp =
  let open Arm in
  let bbm_mode =
    let doc = "Break-before-make mode: off, lax, or strict" in
    let values =
      [("off", Arm.BBM.Off); ("lax", Arm.BBM.Lax); ("strict", Arm.BBM.Strict)]
    in
    let+ bbm =
      Arg.(value & opt (some (enum values)) None & info ["bbm"] ~doc ~docv:"MODE")
    in match bbm with
    | Some bbm -> bbm
    | None -> bbm_of_config()
  in
  let run =
    let+ files = path_and_conf_term
    and+ bbm_param = bbm_mode
    and+ fmt = format_term in
    let parse = parse_testfile fmt in
    assert (Config.get_arch () = Arch_id.Arm);
    run_tests "vmp" (ArmRunner.run_litmus_test ~parse (vmProm_model ~bbm_param tiny_isa)) files
  in
  let info =
    let doc =
      "Run virtual-memory promising model. Only one --bbm-* option can be active \
       at the same time, the default is --bbm-off" in
    Cmd.(info "vmp" ~doc)
  in
  Cmd.v info run

let cmd_x86_tso =
  let run =
    let+ files = path_and_conf_term
    and+ fmt = format_term in
    let parse = parse_testfile fmt in
    assert (Config.get_arch () = Arch_id.X86);
    run_tests "x86_tso" (X86Runner.run_litmus_test ~parse X86.(tso_model tiny_isa)) files
  in
  let info =
    let doc = "Run sequential model" in
    Cmd.(info "x86_tso" ~doc)
  in
  Cmd.v info run

(** The main archsem command *)

let cmd =
  let info =
    let doc = "ArchSem model runner" in
    Cmd.(info "archsem" ~doc)
  in
  Cmd.group info [cmd_seq; cmd_ump; cmd_vmp; cmd_x86_tso]

let () = exit (Cmd.eval cmd)
