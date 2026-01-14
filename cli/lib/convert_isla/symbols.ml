open Ast

(** Symbol Management *)

type symbol_map = (string, Z.t) Hashtbl.t
(* [symbols] maps physical address symbol names to their allocated concrete integer addresses. *)
let symbols : symbol_map = Hashtbl.create 16

(* [virt_symbols] maps virtual address symbol names to their allocated concrete integer addresses. *)
let virt_symbols : symbol_map = Hashtbl.create 16

(* [l3_tables] maps VA symbol names to the L3 table address where their PTE lives.
   This is used by pte3() to compute the correct PTE address. *)
let l3_tables : symbol_map = Hashtbl.create 16

(* [next_free_addr] tracks the next available physical address for allocation.
   It starts at 0x2000 to reserve 0x1000-0x1FFF for identity-mapped code in tests. *)
let next_free_addr = ref (Z.of_int 0x2000)

(* [allocation_step] defines the bump allocation size for new physical regions (4KB). *)
let allocation_step = Z.of_int 0x1000

(* Page-packing support: multiple small symbols can share a 4KB page *)
let current_data_page = ref Z.zero  (* Current page for data symbols, Z.zero = none allocated yet *)
let current_data_offset = ref 0      (* Byte offset within current page *)
let page_symbols : (string, string list) Hashtbl.t = Hashtbl.create 16  (* page_base_hex -> symbol list *)

(* Forward declaration for Allocator - will be set during initialization *)
let allocator_add_region : (Z.t -> Z.t -> unit) ref = ref (fun _ _ -> ())

(* [get_symbol_addr name] retrieves the concrete physical address for [name].
   Each data symbol gets its own 4KB-aligned page to ensure independent L3 PTEs.
   This is required for PTE-manipulation tests (like CoTT) where each variable
   needs to be independently addressable via its own page table entry. *)
let get_symbol_addr ?(size=8) name =
  let _ = size in  (* Size parameter kept for API compatibility *)
  match Hashtbl.find_opt symbols name with
  | Some addr -> addr
  | None ->
      (* Allocate a fresh 4KB-aligned page for each data symbol *)
      let addr = !next_free_addr in
      next_free_addr := Z.add addr (Z.of_int 0x1000);
      !allocator_add_region addr (Z.of_int 4096);
      Hashtbl.add symbols name addr;
      Printf.eprintf "[Info] Allocated PA symbol '%s' at 0x%s (page-aligned)\n"
        name (Z.format "%x" addr);
      addr

(* [get_code_addr name size] allocates a page-aligned physical address for code.
   Code is NOT packed with data to avoid "Instruction memory modified" errors
   when PTE updates hit the same page as code. *)
let get_code_addr name size =
  match Hashtbl.find_opt symbols name with
  | Some addr -> addr
  | None ->
      (* Allocate a fresh 4KB-aligned page for each code region *)
      let addr = !next_free_addr in
      next_free_addr := Z.add addr (Z.of_int 0x1000);  (* Bump by full page *)
      !allocator_add_region addr (Z.of_int 4096);
      Hashtbl.add symbols name addr;
      Printf.eprintf "[Info] Allocated code PA '%s' at 0x%s (page-aligned, size=%d)\n"
        name (Z.format "%x" addr) size;
      addr

(** Virtual Address Generation *)
(* [next_code_va] tracks the next available virtual address for CODE allocation.
   Starts at 0x40000000 (1GB) to use L0[0] in the page table (bit 39 clear).
   This is clearly distinct from PA ranges (0x2000-0xd000). *)
let next_code_va = ref (Z.of_string "0x40000000")

(* [next_data_va] tracks the next available virtual address for DATA allocation.
   Starts at 0x8000000000 to use L0[1] in the page table (bit 39 set).
   Data VAs are higher than code VAs for clarity.
   This separates code and data at the L0 level for proper permission isolation. *)
let next_data_va = ref (Z.of_string "0x8000000000")

(* Legacy alias for compatibility *)
let next_va = next_code_va

(* [va_mappings] maintains a list of all virtual allocations for final reporting/checking.
   Each entry is (Symbol Name, Concrete VA, Optional Associated PA Symbol Name). *)
let va_mappings = ref ([] : (string * Z.t * string option) list)

(** Constraint Management *)
(* [assertion_constraints] stores symbolic constraints collected during ISLA processing.
   These are used to validate virtual address allocations against known constraints
   (e.g., page alignment or specific relation to other addrs). *)
let assertion_constraints = ref ([] : constr list)

(* [record_constraint c] adds a new constraint to the global list for later verification. *)
let record_constraint c =
  assertion_constraints := c :: !assertion_constraints

(* [reset ()] clears all internal state, allowing the module to be reused cleanly. *)
let reset () =
  Hashtbl.clear symbols;
  Hashtbl.clear virt_symbols;
  Hashtbl.clear l3_tables;
  Hashtbl.clear page_symbols;
  next_free_addr := Z.of_int 0x2000;
  current_data_page := Z.zero;  (* No page allocated yet *)
  current_data_offset := 0;
  next_code_va := Z.of_string "0x40000000";
  next_data_va := Z.of_string "0x8000000000";
  va_mappings := [];
  assertion_constraints := []

(* [eval_expr_for_constraint symbols_map e] attempts to reduce an ISLA expression [e]
   to a concrete integer using the current symbol mappings in [symbols_map].
   Returns [Some v] if fully resolvable, [None] otherwise. *)
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

(* [get_virt_symbol ?is_code name] retrieves or allocates a concrete virtual address for [name].
   - is_code=true: allocates from 0x8000000000+ range (L0[1], executable)
   - is_code=false: allocates from 0x1000+ range (L0[0], data)
   Critically, it verifies that the chosen address satisfies all recorded constraints
   (like equality/inequality checks) by speculatively assigning and checking [assertion_constraints].
   If a conflict is found, it skips to a new region until a valid address is found. *)
let get_virt_symbol ?(is_code=false) name =
  match Hashtbl.find_opt virt_symbols name with
  | Some addr -> addr
  | None ->
      let next_ptr = if is_code then next_code_va else next_data_va in
      let va = !next_ptr in

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
      next_ptr := Z.add final_va (Z.of_int 0x1000);
      Hashtbl.add virt_symbols name final_va;
      (* Store temporarily without PA mapping, can be updated later *)
      if not (List.exists (fun (n,_,_) -> n=name) !va_mappings) then
        va_mappings := (name, final_va, None) :: !va_mappings;
      Printf.eprintf "[Info] Allocated VA symbol '%s' at 0x%s\n" name (Z.format "%x" final_va);
      final_va

(* [update_va_mapping_pa name pa_name] associates an existing virtual symbol [name]
   with a backing physical symbol [pa_name] in the [va_mappings] list.
   This is used when we discover that a VA maps to a specific PA region. *)
let update_va_mapping_pa name pa_name =
  va_mappings := List.map (fun (n, va, pa_opt) ->
    if n = name then (n, va, Some pa_name) else (n, va, pa_opt)
  ) !va_mappings

(* [get_pa_for_va name] retrieves the PA symbol that a VA symbol maps to.
   Returns the PA address if found, otherwise allocates a new PA. *)
let get_pa_for_va name =
  match List.find_opt (fun (n, _, _) -> n = name) !va_mappings with
  | Some (_, _, Some pa_name) -> get_symbol_addr pa_name
  | _ -> get_symbol_addr name  (* Fall back to creating PA if no mapping *)
