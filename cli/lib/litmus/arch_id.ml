(** Architecture management *)

type t =
  | Arm
  | X86

let of_string_opt = function
  | "Arm" | "AArch64" | "arm" | "aarch64" -> Some Arm
  | "X86" | "x86" | "X86_64" | "x86_64" -> Some X86
  | _ -> None

let of_string arch =
  match of_string_opt arch with
  | Some arch -> arch
  | None -> failwith ("unknown architecture: " ^ arch)

let to_string = function Arm -> "Arm" | X86 -> "X86"

let of_toml toml = toml |> Otoml.get_string |> of_string

let to_toml arch = arch |> to_string |> Otoml.string

let guess_from_test filename =
  try
    let toml = Otoml.Parser.from_file filename in
    Otoml.find toml of_toml ["arch"]
  with exn ->
    Printf.ksprintf failwith "Failed to guess architecture in %s with error : %s"
      filename (Printexc.to_string exn)
