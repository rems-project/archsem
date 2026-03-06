(** Global configuration from CLI flags.

    A thin wrapper around Otoml.t. Each consumer queries the
    section and keys it needs. No per-test config. *)

type t = Otoml.t

let empty = Otoml.TomlTable []

let rec find_from dir relpath =
  let candidate = Filename.concat dir relpath in
  if Sys.file_exists candidate then Some candidate
  else
    let parent = Filename.dirname dir in
    if parent = dir then None else find_from parent relpath

let first_some = List.find_map Fun.id

let default_path_for_arch arch =
  let file = Arch_id.to_string arch ^ ".toml" in
  let relpath = Filename.concat "config" file in
  let exec_dir = Filename.dirname Sys.argv.(0) in
  first_some [find_from (Sys.getcwd ()) relpath; find_from exec_dir relpath]

let of_arch arch =
  match default_path_for_arch arch with
  | Some path -> Otoml.Parser.from_file path
  | None ->
      failwith ("config: no default config for arch " ^ Arch_id.to_string arch)

(** {1 Global config} *)

let global : t ref = ref empty

let set config = global := config

let load file = global := Otoml.Parser.from_file file

let get () = !global

(** {1 Common fields} *)
let get_arch () = Otoml.find !global Arch_id.of_toml ["arch"]

let get_fuel () =
  Otoml.find_or ~default:1000 !global Otoml.get_integer ["execution"; "fuel"]
