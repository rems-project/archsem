type loc =
  | Reg of int * string
  | Mem of string
  (** A location to get data from. [Mem] mean the data at that location in memory *)

type op =
  | Eq
  | Ne

type atom =
  | CmpCst of loc * op * Z.t
  | CmpLoc of loc * op * loc

type expr =
  | Atom of atom
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | True
  | False  (** Boolean expression for a final assertion *)

(** Convert expression to Disjunctive Normal Form *)
val to_dnf : expr -> atom list list
