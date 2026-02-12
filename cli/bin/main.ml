open Archsem
open Archsem_test
open Cmdliner

(** {1 Model Selection} *)

let mem_param_of_string = function
  | "off" -> Archsem.Off
  | "laxbbm" -> Archsem.LaxBBM
  | "strict" -> Archsem.Strict
  | "strictbbm" -> Archsem.StrictBBM
  | s -> failwith ("Unknown mem_param: " ^ s ^ ". Use: off, laxbbm, strict, strictbbm")

let get_model mem_param = function
  | "seq" -> seq_model
  | "ump" -> umProm_model
  | "vmp" -> vmProm_model mem_param
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
    |> List.map (fun f -> Filename.concat dir f)
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
      Ansi.red Ansi.reset (Filename.basename isla_file) (Printexc.to_string e);
    None

let convert_isla_files ~usermode isla_files =
  Printf.printf "%sConverting %d isla tests...%s\n%!"
    Ansi.dim (List.length isla_files) Ansi.reset;
  let temps = List.filter_map (convert_isla_test ~usermode) isla_files in
  (temps, temps)

(** {1 Argument Parsing} *)

type args = {
  model_name: string;
  mem_param: string;
  path: string;
  isla_mode: bool;
  usermode: bool;
}

let model_name_t =
  let doc = "Memory model to use. Must be one of $(b,seq), $(b,ump), or $(b,vmp)." in
  Arg.(required & pos 0 (some (enum ["seq", "seq"; "ump", "ump"; "vmp", "vmp"])) None
       & info [] ~docv:"MODEL" ~doc)

let path_t =
  let doc = "Path to test file or directory." in
  Arg.(required & pos 1 (some string) None & info [] ~docv:"PATH" ~doc)

let mem_param_t =
  let doc = "Memory parameter for vmp model. One of $(b,off), $(b,laxbbm), $(b,strict), $(b,strictbbm)." in
  Arg.(value & opt string "off" & info ["mem-param"] ~docv:"PARAM" ~doc)

let isla_mode_t =
  let doc = "Input is isla format (converts to archsem before running)." in
  Arg.(value & flag & info ["isla"] ~doc)

let usermode_t =
  let doc = "Use usermode conversion (no page tables, for UM tests)." in
  Arg.(value & flag & info ["usermode"] ~doc)

let args_t =
  let make model_name mem_param path isla_mode usermode =
    { model_name; mem_param; path; isla_mode; usermode }
  in
  Term.(const make $ model_name_t $ mem_param_t $ path_t $ isla_mode_t $ usermode_t)

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
  let mem_param = mem_param_of_string args.mem_param in
  let model = get_model mem_param args.model_name in

  let files, temp_files = collect_test_files args in

  if files = [] then begin
    Printf.eprintf "No test files found for model %s in %s\n" args.model_name args.path;
    exit 1
  end else begin
    let open Litmus_runner in

    Printf.printf "\n%s%s%s%s  %d test(s)\n\n"
      Ansi.bold Ansi.cyan args.model_name Ansi.reset (List.length files);

    let results = List.map (fun file ->
      let result = run_litmus_test ~model_name:args.model_name model file in
      (file, result)
    ) files in

    List.iter Sys.remove temp_files;

    (* Summary *)
    let count pred = List.length (List.filter (fun (_, r) -> pred r) results) in
    let num_expected = count (fun r -> r = Expected) in
    let num_unexpected = count (fun r -> r = Unexpected) in
    let num_model_error = count (fun r -> r = ModelError) in
    let num_parse_error = count (fun r -> r = ParseError) in
    let total = List.length results in
    let all_pass = num_expected = total in

    let repeat n s = String.concat "" (List.init n (fun _ -> s)) in

    Printf.printf "\n%s──────────────────────────────────────────%s\n" Ansi.dim Ansi.reset;

    let status_color = if all_pass then Ansi.green else Ansi.red in
    Printf.printf "  %s%sSUMMARY%s  %s · %d tests\n"
      Ansi.bold status_color Ansi.reset args.model_name total;

    let bar_w = 34 in
    let filled = if total > 0 then num_expected * bar_w / total else 0 in
    let empty = bar_w - filled in
    let pct = if total > 0 then num_expected * 100 / total else 0 in
    Printf.printf "  %s%s%s%s%s %d%%%s\n"
      status_color (repeat filled "█") Ansi.dim (repeat empty "░") status_color pct Ansi.reset;

    Printf.printf "%s──────────────────────────────────────────%s\n" Ansi.dim Ansi.reset;

    Printf.printf "  %s✓%s Expected     %s%d%s\n"
      Ansi.green Ansi.reset Ansi.green num_expected Ansi.reset;
    if num_unexpected > 0 then
      Printf.printf "  %s✗%s Unexpected   %s%d%s\n"
        Ansi.yellow Ansi.reset Ansi.yellow num_unexpected Ansi.reset;
    if num_model_error > 0 then
      Printf.printf "  %s✗%s Model Error  %s%d%s\n"
        Ansi.red Ansi.reset Ansi.red num_model_error Ansi.reset;
    if num_parse_error > 0 then
      Printf.printf "  %s✗%s Parse Error  %s%d%s\n"
        Ansi.red Ansi.reset Ansi.red num_parse_error Ansi.reset;

    let failures = List.filter (fun (_, r) -> r <> Expected) results in
    if failures <> [] then begin
      Printf.printf "%s──────────────────────────────────────────%s\n" Ansi.dim Ansi.reset;
      Printf.printf "  %s%sFailed:%s\n" Ansi.bold Ansi.red Ansi.reset;
      List.iter (fun (f, r) ->
        Printf.printf "    %s  %s\n" (Filename.basename f) (result_to_string r)
      ) failures
    end;

    Printf.printf "%s──────────────────────────────────────────%s\n\n" Ansi.dim Ansi.reset;
    if not all_pass then exit 1
  end

let cmd =
  let doc = "Run litmus tests against memory models" in
  let info = Cmd.info "litmus_runner" ~doc in
  Cmd.v info Term.(const run $ args_t)

let () = exit (Cmd.eval cmd)
