(** Bitvector value expressions: AST and constant evaluator. *)

type loc =
  | Reg of int * string
  | Mem of string

type t =
  | Const of Z.t
  | LocVal of loc
  | Fn of string * t list
  | KwFn of string * (string * t) list

(** Evaluate a [t] containing only [Const] leaves.
    Raises [Failure] if the expression contains [LocVal]. *)
val eval : t -> Z.t
