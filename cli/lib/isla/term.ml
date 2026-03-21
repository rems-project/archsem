(** Bitvector terms: AST and evaluator. *)

type loc =
  | Reg of int * string
  | Mem of string

type t =
  | Const of Z.t
  | LocVal of loc
  | Deref of loc
  | Fn of string * t list
  | KwFn of string * (string * t) list

let eval_fn = Function.eval_fn

let string_of_loc = function
  | Reg (tid, reg) -> Printf.sprintf "%d:%s" tid reg
  | Mem sym -> sym

let rec eval ?(td=[]) ~env = function
  | Const z -> z
  | LocVal loc ->
    (match env loc with
     | Some z -> z
     | None -> failwith (Printf.sprintf "term: unbound %s" (string_of_loc loc)))
  | Deref loc ->
    failwith (Printf.sprintf "term: cannot evaluate deref *%s statically" (string_of_loc loc))
  | Fn (name, args) ->
    let evaluated = List.map (eval ~td ~env) args in
    Function.eval_fn ~td name evaluated
  | KwFn (name, kwargs) ->
    let evaluated = List.map (fun (k, v) -> (k, eval ~td ~env v)) kwargs in
    Function.eval_kwfn ~td name evaluated
