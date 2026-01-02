open Ast

(* --- Symbol Management --- *)
type symbol_map = (string, Z.t) Hashtbl.t
let symbols : symbol_map = Hashtbl.create 16         (* Physical Addresses *)
let virt_symbols : symbol_map = Hashtbl.create 16    (* Virtual Addresses *)

let next_free_addr = ref (Z.of_int 0x10000)
let allocation_step = Z.of_int 0x10000

let get_symbol_addr name =
  match Hashtbl.find_opt symbols name with
  | Some addr -> addr
  | None ->
      let addr = !next_free_addr in
      next_free_addr := Z.add addr allocation_step;
      Hashtbl.add symbols name addr;
      Printf.eprintf "[Info] Allocated PA symbol '%s' at 0x%s\n" name (Z.format "%x" addr);
      addr

(* --- Virtual Address Generation --- *)
let next_va = ref (Z.of_string "0x4000000000")
(* Mapping: Name -> (VA, Optional PA Name) *)
let va_mappings = ref ([] : (string * Z.t * string option) list)

(* Constraint Management *)
let assertion_constraints = ref ([] : constr list)

let record_constraint c =
  assertion_constraints := c :: !assertion_constraints

(* Helper to evaluate expression for constraint checking *)
let rec eval_expr_for_constraint symbols_map e =
  match e with
  | EInt i -> Some i
  | EVar v -> Hashtbl.find_opt symbols_map v
  | ESlice(sub, hi, lo) ->
      (match eval_expr_for_constraint symbols_map sub with
       | Some v ->
           let mask = Z.sub (Z.shift_left Z.one (hi - lo + 1)) Z.one in
           Some (Z.logand (Z.shift_right v lo) mask)
       | None -> None)
  | ECall("add_bits_int", [( _, sub); (_, EInt delta)]) ->
        (match eval_expr_for_constraint symbols_map sub with
         | Some v -> Some (Z.add v delta)
         | None -> None)
  | _ -> None

let get_virt_symbol name =
  match Hashtbl.find_opt virt_symbols name with
  | Some addr -> addr
  | None ->
      let va = !next_va in

      (* Check constraints against allocated symbols *)
      let rec check_constraints curr_va =
         Hashtbl.add virt_symbols name curr_va; (* Temp add *)
         let violation = List.exists (fun c ->
            match c with
            | Eq(e1, e2) ->
                 (match (eval_expr_for_constraint virt_symbols e1, eval_expr_for_constraint virt_symbols e2) with
                  | (Some v1, Some v2) -> not (Z.equal v1 v2)
                  | _ -> false)
            | Neq(e1, e2) ->
                 (match (eval_expr_for_constraint virt_symbols e1, eval_expr_for_constraint virt_symbols e2) with
                  | (Some v1, Some v2) -> Z.equal v1 v2
                  | _ -> false)
         ) !assertion_constraints in
         Hashtbl.remove virt_symbols name;

         if violation then (
             Printf.eprintf "[Info] Constraint conflict for %s at 0x%s, skipping...\n" name (Z.format "%x" curr_va);
             check_constraints (Z.add curr_va (Z.of_int 0x100000))
         ) else curr_va
      in

      let final_va = check_constraints va in
      next_va := Z.add final_va (Z.of_int 0x1000);
      Hashtbl.add virt_symbols name final_va;
      (* Store temporarily without PA mapping, can be updated later *)
      if not (List.exists (fun (n,_,_) -> n=name) !va_mappings) then
        va_mappings := (name, final_va, None) :: !va_mappings;
      Printf.eprintf "[Info] Allocated VA symbol '%s' at 0x%s\n" name (Z.format "%x" final_va);
      final_va

let update_va_mapping_pa name pa_name =
  va_mappings := List.map (fun (n, va, pa_opt) ->
     if n = name then (n, va, Some pa_name) else (n, va, pa_opt)
  ) !va_mappings
