(** Litmus test runner CLI.

    Usage: main <model> <path> [--isla] [--usermode]

    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    Flags:
      --isla     Input is isla format (converts to archsem before running)
      --usermode Use usermode conversion (no page tables, for UM tests) *)

open Archsem
open Archsem_test

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
    |> List.map (fun f -> Filename.concat dir f)
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
      Ansi.red Ansi.reset (Filename.basename isla_file) (Printexc.to_string e);
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
  let files, temp_files =
    if isla_mode then (
      (* Isla mode: find all .toml files recursively and convert *)
      let isla_files =
        if Sys.is_directory path then get_toml_files_recursive path
        else [path]
      in
      Printf.printf "%sConverting %d isla tests...%s\n%!"
        Ansi.dim (List.length isla_files) Ansi.reset;
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

  let open Litmus_runner in

  Printf.printf "\n%s%s%s%s  %d test(s)\n\n"
    Ansi.bold Ansi.cyan model_name Ansi.reset (List.length files);

  let results = List.map (fun file ->
    let result = run_litmus_test model file in
    (file, result)
  ) files in

  (* Clean up temp files *)
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
    Ansi.bold status_color Ansi.reset model_name total;

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
