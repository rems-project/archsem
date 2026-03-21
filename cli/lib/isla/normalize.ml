(** Normalize architecture-specific register aliases in the IR. *)

open Assertion
open Term

let register_renames () =
  Otoml.find_or ~default:[] (Litmus.Config.get ()) (Otoml.get_table_values Otoml.get_string)
    ["isla"; "register_renames"]

let normalize_reg reg =
  match List.assoc_opt reg (register_renames ()) with
  | Some renamed -> renamed
  | None -> reg

let normalize_loc = function
  | Reg (tid, reg) -> Reg (tid, normalize_reg reg)
  | Mem _ as loc -> loc
  | Label _ as loc -> loc

let rec normalize_term = function
  | Const _ as c -> c
  | LocVal loc -> LocVal (normalize_loc loc)
  | Deref loc -> Deref (normalize_loc loc)
  | Fn (name, args) -> Fn (name, List.map normalize_term args)
  | KwFn (name, kw) -> KwFn (name, List.map (fun (k, v) -> (k, normalize_term v)) kw)

let normalize_atom (Cmp (lhs, op, rhs)) =
  Cmp (normalize_term lhs, op, normalize_term rhs)

let rec normalize_expr = function
  | Atom atom -> Atom (normalize_atom atom)
  | And (lhs, rhs) -> And (normalize_expr lhs, normalize_expr rhs)
  | Or (lhs, rhs) -> Or (normalize_expr lhs, normalize_expr rhs)
  | Not expr -> Not (normalize_expr expr)
  | True -> True
  | False -> False

let normalize_thread (thread : Ir.thread) =
  {
    thread with
    init = List.map (fun (reg, value) -> (normalize_reg reg, value)) thread.init;
  }

let apply (ir : Ir.t) : Ir.t =
  {
    ir with
    threads = List.map normalize_thread ir.threads;
    assertion = normalize_expr ir.assertion;
  }
