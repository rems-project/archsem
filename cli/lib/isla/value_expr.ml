(** Bitvector value expressions: AST and constant evaluator. *)

type loc =
  | Reg of int * string
  | Mem of string

type t =
  | Const of Z.t
  | LocVal of loc
  | Fn of string * t list
  | KwFn of string * (string * t) list

let eval_fn name args =
  match name, args with
  | "bvand", [a; b] -> Z.logand a b
  | "bvor", [a; b] -> Z.logor a b
  | "bvxor", [a; b] -> Z.logxor a b
  | "bvshl", [a; b] -> Z.shift_left a (Z.to_int b)
  | "bvlshr", [a; b] -> Z.shift_right a (Z.to_int b)
  | "page", [a] ->
    (* Extract bits [48:12] — the page frame number. *)
    Z.logand (Z.shift_right a 12) (Z.sub (Z.shift_left Z.one 36) Z.one)
  | "extz", [bits; _len] ->
    (* Zero-extend: identity for non-negative Z values. *)
    bits
  | "exts", [bits; len] ->
    (* Sign-extend from current bit-length to [len] bits. *)
    let src_bits = Z.numbits bits in
    let len = Z.to_int len in
    if src_bits = 0 || src_bits >= len then bits
    else if Z.testbit bits (src_bits - 1) then
      let mask = Z.sub (Z.shift_left Z.one len) (Z.shift_left Z.one src_bits) in
      Z.logor bits mask
    else bits
  | _ ->
    let arity = List.length args in
    failwith
      (Printf.sprintf "value_expr: unknown function %s/%d" name arity)

let rec eval = function
  | Const z -> z
  | LocVal (Reg (tid, reg)) ->
    failwith
      (Printf.sprintf
         "value_expr: cannot evaluate register reference %d:%s as constant"
         tid reg)
  | LocVal (Mem sym) ->
    failwith
      (Printf.sprintf
         "value_expr: cannot evaluate symbol reference %s as constant" sym)
  | Fn (name, args) ->
    let evaluated = List.map eval args in
    eval_fn name evaluated
  | KwFn (name, _) ->
    failwith
      (Printf.sprintf
         "value_expr: keyword function %s requires symbolic context" name)
