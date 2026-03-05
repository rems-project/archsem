(** AST for isla assertion expressions. *)

type atom =
  | RegEq of int * string * Z.t
  | RegNe of int * string * Z.t
  | MemEq of string * Z.t
  | MemNe of string * Z.t

type expr =
  | Atom of atom
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | True
