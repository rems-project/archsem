(* cli/lib/convert_litmus/ast.ml *)

type expr =
  | EInt of Z.t
  | EVar of string
  | ECall of string * (string * expr) list (* Named args support: (name, expr) tuple. Name is "" if positional *)
  | ESlice of expr * int * int

type target_expr =
  | TPA of string
  | TTable of string
  | TTableAddr of Z.t
  | TRaw of Z.t
  | TInvalid

type constr =
  | Eq of expr * expr
  | Neq of expr * expr

type stmt =
  | Decl of string * string list
  | OptionDef of string * string
  | TableDef of { name: string; addr: string; body: stmt list }
  | Mapping of { va: string; target: target_expr; variant: bool; level: int option; alias: string option }
  | Identity of string * bool (** Hex string or ID, bool is_code *)
  | MemInit of string * string
  | Assert of constr
