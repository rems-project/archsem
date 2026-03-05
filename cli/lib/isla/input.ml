(** Parse isla-format TOML into an intermediate representation.

    Handles UM-style tests: threads with init registers and assembly code,
    symbolic variables, locations, and final assertions. *)

type thread = {
  tid : int;
  code : string;
  init : (string * string) list;
}

type t = {
  arch : string;
  name : string;
  threads : thread list;
  symbolic : string list;
  locations : (string * string) list;
  expect : string;
  assertion : string;
}

let get_string_opt toml keys =
  match Otoml.find_opt toml (fun x -> x) keys with
  | Some (Otoml.TomlString s) -> Some s
  | _ -> None

let get_string toml keys default =
  match get_string_opt toml keys with
  | Some s -> s
  | None -> default

let parse_threads toml =
  match Otoml.find_opt toml (fun x -> x) ["thread"] with
  | Some (Otoml.TomlTable pairs) ->
    pairs |> List.filter_map (fun (tid_str, v) ->
      match int_of_string_opt tid_str, v with
      | Some tid, Otoml.TomlTable kvs ->
        let code = match List.assoc_opt "code" kvs with
          | Some (Otoml.TomlString s) -> String.trim s
          | _ -> ""
        in
        let init = match List.assoc_opt "init" kvs with
          | Some (Otoml.TomlTable regs | Otoml.TomlInlineTable regs) ->
            List.map (fun (k, v) -> match v with
              | Otoml.TomlString s -> (k, s)
              | Otoml.TomlInteger i -> (k, string_of_int i)
              | _ -> (k, "0")
            ) regs
          | _ -> []
        in
        Some { tid; code; init }
      | _ -> None
    ) |> List.sort (fun a b -> compare a.tid b.tid)
  | _ -> []

let parse_symbolic toml =
  match Otoml.find_opt toml (fun x -> x) ["symbolic"] with
  | Some (Otoml.TomlArray items) ->
    List.filter_map (function Otoml.TomlString s -> Some s | _ -> None) items
  | _ -> []

let parse_locations toml =
  match Otoml.find_opt toml (fun x -> x) ["locations"] with
  | Some (Otoml.TomlTable pairs) ->
    List.map (fun (k, v) -> match v with
      | Otoml.TomlString s -> (k, s)
      | Otoml.TomlInteger i -> (k, string_of_int i)
      | _ -> (k, "0")
    ) pairs
  | _ -> []

let parse toml = {
  arch = get_string toml ["arch"] "AArch64";
  name = get_string toml ["name"] "unknown";
  threads = parse_threads toml;
  symbolic = parse_symbolic toml;
  locations = parse_locations toml;
  expect = (match Otoml.find_opt toml (fun x -> x) ["final"] with
    | Some final_toml -> get_string final_toml ["expect"] "sat"
    | None -> "sat");
  assertion = (match Otoml.find_opt toml (fun x -> x) ["final"] with
    | Some final_toml -> get_string final_toml ["assertion"] "true"
    | None -> "true");
}
