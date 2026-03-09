(** Shared test helpers for unit tests. *)

open Litmus

(** {1 Test File Helpers} *)

let test_root = Filename.concat (Filename.dirname Sys.argv.(0)) ".."
let test_dirs = ["seq"; "ump"; "vmp"]

let i n = Archsem.RegValGen.Number (Z.of_int n)

let parse_file path =
  Parser.parse_to_testrepr
    (Otoml.Parser.from_file (Filename.concat test_root path))
