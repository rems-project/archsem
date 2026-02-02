(** Symbol table for isla-to-archsem conversion.

    Allocates page-aligned physical and virtual addresses for named symbols,
    tracks VA-to-PA mappings for page table generation, and manages symbolic
    constraints between addresses. *)

open Ast

type symbol_map = (string, Z.t) Hashtbl.t

let symbols : symbol_map = Hashtbl.create 16
let virt_symbols : symbol_map = Hashtbl.create 16
let l2_tables : symbol_map = Hashtbl.create 16
let l3_tables : symbol_map = Hashtbl.create 16
let next_free_addr = ref Constants.initial_pa

(* Set during initialization to register allocated regions with the Allocator *)
let allocator_add_region : (Z.t -> Z.t -> unit) ref = ref (fun _ _ -> ())

(* Retrieve or allocate a page-aligned PA for the given symbol name. *)
let get_symbol_addr name =
  match Hashtbl.find_opt symbols name with
  | Some addr -> addr
  | None ->
      let addr = !next_free_addr in
      next_free_addr := Z.add addr Constants.page_size_z;
      !allocator_add_region addr Constants.page_size_z;
      Hashtbl.add symbols name addr;
      addr

let next_code_va = ref Constants.initial_code_va
let next_data_va = ref Constants.initial_data_va

(* (name, concrete VA, optional backing PA symbol name) *)
let va_mappings = ref ([] : (string * Z.t * string option) list)

let assertion_constraints = ref ([] : constr list)

(* Called from Assert node processing to record symbolic constraints between
   virtual addresses. get_virt_symbol skips candidate VAs that violate these. *)
let record_constraint c =
  assertion_constraints := c :: !assertion_constraints

let reset () =
  Hashtbl.clear symbols;
  Hashtbl.clear virt_symbols;
  Hashtbl.clear l2_tables;
  Hashtbl.clear l3_tables;
  next_free_addr := Constants.initial_pa;
  next_code_va := Constants.initial_code_va;
  next_data_va := Constants.initial_data_va;
  va_mappings := [];
  assertion_constraints := []

(* Try to evaluate an expression to a concrete Z.t using the given symbol map. *)
let rec resolve_expr symbols_map e =
  match e with
  | EInt i -> Some i
  | EVar v -> Hashtbl.find_opt symbols_map v
  | ESlice(sub, hi, lo) ->
    (match resolve_expr symbols_map sub with
     | Some v ->
        let mask = Z.sub (Z.shift_left Z.one (hi - lo + 1)) Z.one in
        Some (Z.logand (Z.shift_right v lo) mask)
     | None -> None)
  | ECall("add_bits_int", [( _, sub); (_, EInt delta)]) ->
    (match resolve_expr symbols_map sub with
     | Some v -> Some (Z.add v delta)
     | None -> None)
  | _ -> None

(* Allocates from code VA (is_code=true) or data VA range, skipping addresses
   that violate recorded constraints. *)
let get_virt_symbol ?(is_code=false) name =
  match Hashtbl.find_opt virt_symbols name with
  | Some addr -> addr
  | None ->
    let next_ptr = if is_code then next_code_va else next_data_va in
    let va = !next_ptr in

    (* Temporarily insert name -> curr_va into virt_symbols so that
       resolve_expr can evaluate constraints involving this symbol,
       then remove it. Skip forward by constraint_skip on violation. *)
    let rec check_constraints curr_va =
      Hashtbl.add virt_symbols name curr_va;
      let violation = List.exists (fun c ->
        match c with
        | Eq(e1, e2) ->
          (match (resolve_expr virt_symbols e1, resolve_expr virt_symbols e2) with
            | (Some v1, Some v2) -> not (Z.equal v1 v2)
            | _ -> false)
        | Neq(e1, e2) ->
          (match (resolve_expr virt_symbols e1, resolve_expr virt_symbols e2) with
            | (Some v1, Some v2) -> Z.equal v1 v2
            | _ -> false)
      ) !assertion_constraints in
      Hashtbl.remove virt_symbols name;

      if violation then
        check_constraints (Z.add curr_va Constants.constraint_skip)
      else curr_va
    in

    let final_va = check_constraints va in
    (* Commit: advance the bump pointer and record the VA mapping *)
    next_ptr := Z.add final_va Constants.page_size_z;
    Hashtbl.add virt_symbols name final_va;
    if not (List.exists (fun (n,_,_) -> n=name) !va_mappings) then
      va_mappings := (name, final_va, None) :: !va_mappings;
    final_va

let update_va_mapping_pa name pa_name =
  va_mappings := List.map (fun (n, va, pa_opt) ->
    if n = name then (n, va, Some pa_name) else (n, va, pa_opt)
  ) !va_mappings

let get_pa_for_va name =
  match List.find_opt (fun (n, _, _) -> n = name) !va_mappings with
  | Some (_, _, Some pa_name) -> get_symbol_addr pa_name
  | _ -> get_symbol_addr name
