(** Symbol table for isla-to-archsem conversion.

    This module manages symbolic names for physical and virtual addresses
    during the conversion of isla litmus tests to archsem TOML format.

    Key responsibilities:
    - Allocate unique physical addresses (PA) for named memory locations
    - Allocate unique virtual addresses (VA) for symbolic variables
    - Track VA-to-PA mappings for page table generation
    - Manage symbolic constraints (equality/inequality) between addresses
    - Track L2/L3 table addresses for PTE calculation

    Memory layout:
    - PA allocation starts at 0x2000 (reserving 0x0000-0x1FFF)
    - Code VA starts at 0x40000000 (1GB)
    - Data VA starts at 0x8000000000 (32GB)
    - Each symbol gets a 4KB-aligned page for independent PTE manipulation *)

open Ast

(** Constants for memory layout *)
let page_size = Z.of_int 0x1000          (* 4KB page *)
let page_size_int = 4096
let initial_pa = Z.of_int 0x2000         (* Start PA allocation after reserved region *)
let initial_code_va = Z.of_string "0x40000000"   (* 1GB - code VA base *)
let initial_data_va = Z.of_string "0x8000000000" (* 32GB - data VA base *)
let constraint_skip = Z.of_int 0x100000  (* Skip 1MB on constraint conflict *)

type symbol_map = (string, Z.t) Hashtbl.t

(* [symbols] maps physical address symbol names to their allocated concrete integer addresses. *)
let symbols : symbol_map = Hashtbl.create 16

(* [virt_symbols] maps virtual address symbol names to their allocated concrete integer addresses. *)
let virt_symbols : symbol_map = Hashtbl.create 16

(* [l2_tables] maps VA symbol names to the L2 table address where their PTE lives. *)
let l2_tables : symbol_map = Hashtbl.create 16

(* [l3_tables] maps VA symbol names to the L3 table address where their PTE lives. *)
let l3_tables : symbol_map = Hashtbl.create 16

(* [next_free_addr] tracks the next available physical address for allocation. *)
let next_free_addr = ref initial_pa

(* Forward declaration for Allocator - will be set during initialization *)
let allocator_add_region : (Z.t -> Z.t -> unit) ref = ref (fun _ _ -> ())

(* [get_symbol_addr name] retrieves or allocates a page-aligned physical address for [name]. *)
let get_symbol_addr name =
  match Hashtbl.find_opt symbols name with
  | Some addr -> addr
  | None ->
      let addr = !next_free_addr in
      next_free_addr := Z.add addr page_size;
      !allocator_add_region addr (Z.of_int page_size_int);
      Hashtbl.add symbols name addr;
      addr

(* [get_code_addr name] allocates a page-aligned physical address for code. *)
let get_code_addr name =
  match Hashtbl.find_opt symbols name with
  | Some addr -> addr
  | None ->
      let addr = !next_free_addr in
      next_free_addr := Z.add addr page_size;
      !allocator_add_region addr (Z.of_int page_size_int);
      Hashtbl.add symbols name addr;
      addr

(** Virtual Address Generation *)

(* [next_code_va] tracks the next available virtual address for CODE allocation. *)
let next_code_va = ref initial_code_va

(* [next_data_va] tracks the next available virtual address for DATA allocation. *)
let next_data_va = ref initial_data_va

(* [va_mappings] maintains a list of all virtual allocations.
   Each entry is (Symbol Name, Concrete VA, Optional Associated PA Symbol Name). *)
let va_mappings = ref ([] : (string * Z.t * string option) list)

(** Constraint Management *)

(* [assertion_constraints] stores symbolic constraints collected during ISLA processing. *)
let assertion_constraints = ref ([] : constr list)

let record_constraint c =
  assertion_constraints := c :: !assertion_constraints

(* [reset ()] clears all internal state. *)
let reset () =
  Hashtbl.clear symbols;
  Hashtbl.clear virt_symbols;
  Hashtbl.clear l2_tables;
  Hashtbl.clear l3_tables;
  next_free_addr := initial_pa;
  next_code_va := initial_code_va;
  next_data_va := initial_data_va;
  va_mappings := [];
  assertion_constraints := []

(* [resolve_expr symbols_map e] attempts to resolve an expression [e]
   to a concrete integer using the current symbol mappings. *)
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

(* [get_virt_symbol ?is_code name] retrieves or allocates a concrete virtual address for [name].
   - is_code=true: allocates from code VA range (0x40000000+)
   - is_code=false: allocates from data VA range (0x8000000000+)
   Verifies that the chosen address satisfies all recorded constraints. *)
let get_virt_symbol ?(is_code=false) name =
  match Hashtbl.find_opt virt_symbols name with
  | Some addr -> addr
  | None ->
      let next_ptr = if is_code then next_code_va else next_data_va in
      let va = !next_ptr in

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
           check_constraints (Z.add curr_va constraint_skip)
         else curr_va
      in

      let final_va = check_constraints va in
      next_ptr := Z.add final_va page_size;
      Hashtbl.add virt_symbols name final_va;
      if not (List.exists (fun (n,_,_) -> n=name) !va_mappings) then
        va_mappings := (name, final_va, None) :: !va_mappings;
      final_va

(* [update_va_mapping_pa name pa_name] associates an existing virtual symbol [name]
   with a backing physical symbol [pa_name]. *)
let update_va_mapping_pa name pa_name =
  va_mappings := List.map (fun (n, va, pa_opt) ->
    if n = name then (n, va, Some pa_name) else (n, va, pa_opt)
  ) !va_mappings

(* [get_pa_for_va name] retrieves the PA symbol that a VA symbol maps to. *)
let get_pa_for_va name =
  match List.find_opt (fun (n, _, _) -> n = name) !va_mappings with
  | Some (_, _, Some pa_name) -> get_symbol_addr pa_name
  | _ -> get_symbol_addr name
