(** Architecture management *)

type t =
  | Arm

let of_string_opt = function
  | "Arm" | "AArch64" | "arm" | "aarch64" -> Some Arm
  | _ -> None

let of_string arch =
  match of_string_opt arch with
  | Some arch -> arch
  | None -> Error.raise_error Parser "unknown architecture: %s" arch

let to_string = function
  | Arm -> "Arm"

let of_toml toml = toml |> Otoml.get_string |> of_string

let to_toml arch = arch |> to_string |> Otoml.string

let guess_from_test filename =
  try
    let toml = Otoml.Parser.from_file filename in
    Otoml.find toml of_toml ["arch"]
  with exn ->
    Error.raise_error Parser
    "failed to guess architecture in %s with error: %s" filename (Printexc.to_string exn)
