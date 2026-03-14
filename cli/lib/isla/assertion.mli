type op = Eq | Ne

type atom = Cmp of Value_expr.t * op * Value_expr.t

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
