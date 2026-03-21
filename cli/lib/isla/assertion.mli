type op = Eq | Ne

type atom = Cmp of Term.t * op * Term.t

type expr =
  | Atom of atom
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | True
  | False
(** Boolean expression for a final assertion *)

val to_dnf : expr -> atom list list
(** Convert expression to Disjunctive Normal Form *)
