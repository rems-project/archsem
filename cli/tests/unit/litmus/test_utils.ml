(** Shared test helpers for unit tests. *)

open Litmus

(** {1 Test File Helpers} *)

let test_root = Filename.concat (Filename.dirname Sys.argv.(0)) ".."
let test_dirs = ["../seq"; "../ump"; "../vmp"]

let i n = Archsem.RegValGen.Number (Z.of_int n)

let setup () =
  Config.set (Config.of_arch Arch_id.Arm)

let parse_file path =
  Parser.parse_to_testrepr
    (Otoml.Parser.from_file (Filename.concat test_root path))

let collect_archsem_files () =
  let suffix = ".archsem.toml" in
  List.concat_map
    (fun sub ->
      let dir = Filename.concat test_root sub in
      if Sys.file_exists dir then
        Sys.readdir dir |> Array.to_list
        |> List.filter (fun f -> Filename.check_suffix f suffix)
        |> List.sort String.compare
        |> List.map (fun f ->
             (Filename.chop_suffix f suffix, Filename.concat sub f))
      else [])
    test_dirs
