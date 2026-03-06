(** Global configuration from CLI flags.

    A thin wrapper around Otoml.t. Each consumer queries the
    section and keys it needs. No per-test config. *)

type t = Otoml.t

let empty = Otoml.TomlTable []

let get_int keys default t =
  match Otoml.find_opt t (fun x -> x) keys with
  | Some (Otoml.TomlInteger i) -> i
  | _ -> default

let get_string_opt keys t =
  match Otoml.find_opt t (fun x -> x) keys with
  | Some (Otoml.TomlString s) -> Some s
  | _ -> None

let get_string keys default t =
  match get_string_opt keys t with
  | Some s -> s
  | None -> default

let of_config_section toml =
  match Otoml.find_opt toml (fun x -> x) ["config"] with
  | Some section -> section
  | None -> empty

let of_file path = Otoml.Parser.from_file path

(** {1 Global config} *)

let global : t ref = ref empty

let set config = global := config

let get () = !global
