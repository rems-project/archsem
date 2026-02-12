(** Litmus test runner CLI.

    Usage: litmus_runner <model> <path ...>
    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    Each path can be a directory (scanned for .toml files) or a .toml file. *)

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

  let open Litmus_runner in

  Printf.printf "\n%s%s%s%s  %d test(s)\n\n"
    Ansi.bold Ansi.cyan model_name Ansi.reset (List.length files);

  let results = List.map (fun file ->
    let result = run_litmus_test model file in
    (file, result)
  ) files in

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
