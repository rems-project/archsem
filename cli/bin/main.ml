(** Litmus test runner CLI.

    Usage: litmus_runner <model> <file_or_dir>

    Models: seq (sequential), ump (UM Promising), vmp (VM Promising)

    If a directory is given, runs all .toml files matching the model prefix. *)

open Archsem

let get_model = function
  | "seq" -> seq_model
  | "ump" -> umProm_model
  | "vmp" -> vmProm_model
  | s -> failwith ("Unknown model: " ^ s ^ ". Use: seq, ump, vmp")

(** Get test files for a model from a directory *)
let get_test_files model_name dir =
  let prefix = match model_name with
    | "seq" -> "EOR"  (* Sequential tests start with EOR *)
    | "ump" -> "MP"   (* UM Promising tests start with MP *)
    | "vmp" -> "VMP"  (* VM Promising tests start with VMP *)
    | _ -> ""
  in
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun f ->
       String.length f > 5 &&
       String.sub f (String.length f - 5) 5 = ".toml" &&
       (prefix = "" || String.length f >= String.length prefix &&
        String.sub f 0 (String.length prefix) = prefix))
  |> List.sort String.compare
  |> List.map (Filename.concat dir)

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
    let passed = Archsem_test.Litmus_runner.run_litmus_test model file in
    (file, passed)
  ) files in

  (* Summary *)
  let passed = List.filter snd results |> List.length in
  let total = List.length results in
  Printf.printf "\n========================================\n";
  Printf.printf "Results: %d/%d tests passed\n" passed total;

  if passed < total then (
    Printf.printf "Failed tests:\n";
    List.iter (fun (f, p) -> if not p then Printf.printf "  - %s\n" f) results;
    exit 1
  )
