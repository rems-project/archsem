(** Normalize architecture-specific register aliases in the IR. *)

open Assertion

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

let normalize_atom = function
  | CmpCst (loc, op, value) -> CmpCst (normalize_loc loc, op, value)
  | CmpLoc (lhs, op, rhs) -> CmpLoc (normalize_loc lhs, op, normalize_loc rhs)

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
