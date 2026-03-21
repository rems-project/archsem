(** Bitvector terms: AST and constant evaluator. *)

type loc =
  | Reg of int * string
  | Mem of string
  | Label of string

type t =
  | Const of Z.t
  | LocVal of loc
  | Deref of loc
  | Fn of string * t list
  | KwFn of string * (string * t) list

val string_of_loc : loc -> string

(** Evaluate a [t] to a concrete integer.
    [~env] maps [LocVal] leaves to integers; returns [None] for unbound locations. *)
val eval : ?td:Function.table_data -> env:(loc -> Z.t option) -> t -> Z.t

(** Evaluate a positional function call. Delegates to {!Function.eval_fn}. *)
val eval_fn : ?td:Function.table_data -> string -> Z.t list -> Z.t
