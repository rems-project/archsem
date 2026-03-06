type t =
  | Number of Z.t
  | String of string
  | Array of t list
  | Struct of (string * t) list
