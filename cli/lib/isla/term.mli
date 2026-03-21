(** Bitvector terms: AST and constant evaluator. *)

type loc =
  | Reg of int * string
  | Mem of string

type t =
  | Const of Z.t
  | LocVal of loc
  | Deref of loc
  | Fn of string * t list
  | KwFn of string * (string * t) list

(** Evaluate a [t] to a concrete integer.
    [~env] maps [LocVal] leaves to integers; returns [None] for unbound locations. *)
val eval : env:(loc -> Z.t option) -> t -> Z.t

(** Evaluate a positional function call. Delegates to {!Function.eval_fn}. *)
val eval_fn : string -> Z.t list -> Z.t
