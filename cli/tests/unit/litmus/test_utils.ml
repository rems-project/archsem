(** Shared test helpers for unit tests. *)

open Litmus

(** {1 Test File Helpers} *)

let test_root = Filename.concat (Filename.dirname Sys.argv.(0)) ".."
let test_dirs = ["seq"; "ump"; "vmp"]

let i n = Archsem.RegValGen.Number (Z.of_int n)

let setup_arm () = Litmus.Config.set (Config.of_arch Arch_id.Arm)
let setup_x86 () = Litmus.Config.set (Config.of_arch Arch_id.X86)


let parse_file path =
  Parser.parse_to_testrepr
    (Otoml.Parser.from_file (Filename.concat test_root path))

let collect_toml_files () =
  List.concat_map
    (fun sub ->
      let dir = Filename.concat test_root sub in
      if Sys.file_exists dir then
        Sys.readdir dir |> Array.to_list
        |> List.filter (fun f -> Filename.check_suffix f ".toml")
        |> List.sort String.compare
        |> List.map (fun f ->
             (Filename.chop_suffix f ".toml", Filename.concat sub f))
      else [])
    test_dirs
