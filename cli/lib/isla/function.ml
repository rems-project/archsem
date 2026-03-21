(** Functions for isla term evaluation.

    Each function is registered with its parameter names (for keyword
    argument alignment) and an evaluation function on positional args. *)

type fn_spec = {
  params : string list;
  eval : Z.t list -> Z.t;
}

(** Built-in pure functions *)

let arity_error name n =
  failwith (Printf.sprintf "function %s: expected %d args" name n)

let bv_functions : (string * fn_spec) list = [
  "bvand", {
    params = ["a"; "b"];
    eval = (function [a; b] -> Z.logand a b | _ -> arity_error "bvand" 2);
  };
  "bvor", {
    params = ["a"; "b"];
    eval = (function [a; b] -> Z.logor a b | _ -> arity_error "bvor" 2);
  };
  "bvxor", {
    params = ["a"; "b"];
    eval = (function [a; b] -> Z.logxor a b | _ -> arity_error "bvxor" 2);
  };
  "bvshl", {
    params = ["a"; "b"];
    eval = (function [a; b] -> Z.shift_left a (Z.to_int b)
            | _ -> arity_error "bvshl" 2);
  };
  "bvlshr", {
    params = ["a"; "b"];
    eval = (function [a; b] -> Z.shift_right a (Z.to_int b)
            | _ -> arity_error "bvlshr" 2);
  };
  "extz", {
    params = ["bits"; "len"];
    eval = (function [bits; _len] -> bits
            | _ -> arity_error "extz" 2);
  };
  "exts", {
    params = ["bits"; "len"];
    eval = (function [bits; len] ->
              let src_bits = Z.numbits bits in
              let len = Z.to_int len in
              if src_bits = 0 || src_bits >= len then bits
              else if Z.testbit bits (src_bits - 1) then
                let mask = Z.sub (Z.shift_left Z.one len)
                    (Z.shift_left Z.one src_bits) in
                Z.logor bits mask
              else bits
            | _ -> arity_error "exts" 2);
  };
]

let pgt_functions : (string * fn_spec) list = [
  "page", {
    params = ["a"];
    eval = (function [a] ->
              Z.logand (Z.shift_right a 12) (Z.sub (Z.shift_left Z.one 36) Z.one)
            | _ -> arity_error "page" 1);
  };
]

let functions : (string * fn_spec) list = bv_functions @ pgt_functions

let find name = List.assoc_opt name functions

let eval_fn name args =
  match find name with
  | Some spec -> spec.eval args
  | None ->
    failwith (Printf.sprintf "function: unknown %s/%d" name (List.length args))

let align_kwargs name kwargs =
  match find name with
  | Some spec ->
    List.map (fun param ->
      match List.assoc_opt param kwargs with
      | Some v -> v
      | None ->
        failwith (Printf.sprintf "function %s: missing argument %s" name param))
    spec.params
  | None ->
    failwith (Printf.sprintf "function: unknown keyword function %s" name)

let eval_kwfn name kwargs =
  let args = align_kwargs name kwargs in
  eval_fn name args
