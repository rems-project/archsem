type loc =
  | Reg of int * string
  | Mem of string

type op = Eq | Ne

type atom =
  | CmpCst of loc * op * Z.t
  | CmpLoc of loc * op * loc

type expr =
  | Atom of atom
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | True
  | False

val negate_atom : atom -> atom
val to_dnf : expr -> atom list list
val of_dnf : atom list list -> expr
