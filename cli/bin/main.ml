open Archsem
open Archsem_test
open Litmus_runner
open Cmdliner

let get_model = function
  | "seq" -> seq_model
  | "ump" -> umProm_model
  | "vmp" -> fun fuel term initState -> vmProm_model fuel term initState
  | s -> failwith ("Unknown model: " ^ s ^ ". Use: seq, ump, vmp")

(** {1 File Discovery} *)

let has_toml_extension f =
  String.length f > 5 && String.sub f (String.length f - 5) 5 = ".toml"

let get_toml_files dir =
  if Sys.file_exists dir && Sys.is_directory dir then
    Sys.readdir dir
    |> Array.to_list
    |> List.filter has_toml_extension
    |> List.sort String.compare
    |> List.map (Filename.concat dir)
  else []

let rec get_toml_files_recursive dir =
  if not (Sys.file_exists dir && Sys.is_directory dir) then []
  else
    let entries = Sys.readdir dir |> Array.to_list in
    let is_file f =
      let path = Filename.concat dir f in
      Sys.file_exists path && not (Sys.is_directory path) && has_toml_extension f
    in
    let is_subdir f =
      let path = Filename.concat dir f in
      Sys.is_directory path && f <> "." && f <> ".." && f <> "@all"
    in
    let files = List.filter is_file entries in
    let subdirs = List.filter is_subdir entries in
    let local_files = List.map (fun f -> Filename.concat dir f) files in
    let subdir_files = List.concat_map (fun d ->
      get_toml_files_recursive (Filename.concat dir d)
    ) subdirs in
    local_files @ subdir_files


(** {1 Isla Conversion} *)

let convert_isla_test ~usermode isla_file =
  let base = Filename.basename isla_file in
  let name = Filename.remove_extension base in
  let temp_dir = Filename.get_temp_dir_name () in
  let temp_file = Filename.concat temp_dir ("archsem_" ^ name ^ ".toml") in
  let oc = open_out temp_file in
  try
    Isla_converter.Symbols.reset ();
    Isla_converter.Allocator.reset ();
    Isla_converter.Converter.process_toml ~usermode isla_file oc;
    close_out oc;
    Some temp_file
  with e ->
    close_out oc;
    (try Sys.remove temp_file with _ -> ());
    Printf.eprintf "  %s[Convert]%s %s: %s\n"
      Terminal.red Terminal.reset (Filename.basename isla_file) (Printexc.to_string e);
    None

let convert_isla_files ~usermode isla_files =
  Printf.printf "%sConverting %d isla tests...%s\n%!"
    Terminal.dim (List.length isla_files) Terminal.reset;
  let temps = List.filter_map (convert_isla_test ~usermode) isla_files in
  (temps, temps)

(** {1 Argument Parsing} *)

type args = {
  model_name: string;
  path: string;
  isla_mode: bool;
  usermode: bool;
  assembler: string option;
}

let model_name_t =
  let doc = "Memory model to use. Must be one of $(b,seq), $(b,ump), or $(b,vmp)." in
  Arg.(required & pos 0 (some (enum ["seq", "seq"; "ump", "ump"; "vmp", "vmp"])) None
       & info [] ~docv:"MODEL" ~doc)

let path_t =
  let doc = "Path to test file or directory." in
  Arg.(required & pos 1 (some string) None & info [] ~docv:"PATH" ~doc)

let isla_mode_t =
  let doc = "Input is isla format (converts to archsem before running)." in
  Arg.(value & flag & info ["isla"] ~doc)

let usermode_t =
  let doc = "Use usermode conversion (no page tables, for UM tests)." in
  Arg.(value & flag & info ["usermode"] ~doc)

let assembler_t =
  let doc = "Assembler backend. $(b,llvm) for llvm-mc (default), $(b,gnu) for \
             aarch64-linux-gnu-as, or a custom prefix (e.g. $(b,llvm-18), \
             $(b,aarch64-none-elf))." in
  Arg.(value & opt (some string) None & info ["assembler"] ~docv:"BACKEND" ~doc)

let parse_assembler s =
  match String.lowercase_ascii s with
  | "llvm" -> Isla_converter.Assembler.LLVM "llvm"
  | "gnu" -> Isla_converter.Assembler.GNU "aarch64-linux-gnu"
  | prefix when String.contains prefix '-' ->
      Isla_converter.Assembler.GNU prefix
  | prefix ->
      Isla_converter.Assembler.LLVM prefix

let args_t =
  let make model_name path isla_mode usermode assembler =
    { model_name; path; isla_mode; usermode; assembler }
  in
  Term.(const make $ model_name_t $ path_t $ isla_mode_t $ usermode_t $ assembler_t)

(** {1 Test Execution} *)

let collect_test_files args =
  if args.isla_mode then
    let isla_files =
      if Sys.is_directory args.path then get_toml_files_recursive args.path
      else [args.path]
    in
    convert_isla_files ~usermode:args.usermode isla_files
  else
    let files =
      if Sys.is_directory args.path then get_toml_files args.path
      else [args.path]
    in
    (files, [])

(** {1 Entry Point} *)

let run args =
  Option.iter (fun s -> Isla_converter.Assembler.set_backend (parse_assembler s)) args.assembler;
  let model = get_model args.model_name in

  let files, temp_files = collect_test_files args in

  if files = [] then begin
    Printf.eprintf "No test files found for model %s in %s\n" args.model_name args.path;
    exit 1
  end else begin
    Terminal.print_header args.model_name (List.length files);

    let results = List.map (fun file ->
      let result = run_litmus_test ~model_name:args.model_name model file in
      (file, result)) files in

    List.iter Sys.remove temp_files;

    let count pred = List.length (List.filter (fun (_, r) -> pred r) results) in
    let num_expected = count (fun r -> r = Expected) in
    let num_unexpected = count (fun r -> r = Unexpected) in
    let num_model_error = count (fun r -> r = ModelError) in
    let num_no_behaviour = count (fun r -> r = NoBehaviour) in
    let num_parse_error = count (fun r -> r = ParseError) in
    let total = List.length results in

    let failures = List.filter (fun (_, r) -> r <> Expected) results
      |> List.map (fun (f, r) -> (Filename.basename f, result_to_string r)) in

    Terminal.print_summary ~model_name:args.model_name ~total
      ~expected:num_expected ~unexpected:num_unexpected
      ~model_error:num_model_error ~parse_error:num_parse_error
      ~no_behaviour:num_no_behaviour ~failures;

    if num_expected <> total then exit 1
  end

let cmd =
  let doc = "Run litmus tests against memory models." in
  let info = Cmd.info "archsem" ~doc in
  Cmd.v info Term.(const run $ args_t)

let () = exit (Cmd.eval cmd)
