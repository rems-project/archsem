
type gen =
  | Number of Z.t
  | String of string
  | Array of gen list
  | Struct of (string * gen) list
