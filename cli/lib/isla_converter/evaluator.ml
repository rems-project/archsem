(** Expression evaluator for isla-to-archsem conversion.

    This module evaluates symbolic expressions from the isla DSL to concrete
    integer values. It handles:
    - Variable resolution (VA and PA symbols)
    - Page descriptor construction (desc3, mkdescN)
    - PTE address calculation (pteN, tableN)
    - Bitvector operations (bvor, bvand, bvadd, etc.)
    - Bit slicing and extraction

    Works with [Symbols] module for address resolution. *)

open Ast

(** Page offset shift (bits [11:0] = 12 bits) *)
let page_shift = 12

(** Get table base for PTE calculation at a given level *)
let get_table_for_level level va_expr =
  match level, va_expr with
  | 2, EVar sym ->
    (match Hashtbl.find_opt Symbols.l2_tables sym with
     | Some addr -> addr
     | None -> Symbols.get_symbol_addr "page_table_base")
  | 3, EVar sym ->
    (match Hashtbl.find_opt Symbols.l3_tables sym with
     | Some addr -> addr
     | None -> Symbols.get_symbol_addr "page_table_base")
  | _, _ -> Symbols.get_symbol_addr "page_table_base"

(** [parse_expr s] parses a string representation of an ISLA expression into an AST. *)
let parse_expr s =
  let lexbuf = Lexing.from_string s in
  try Parser.main_expr Lexer.read lexbuf
  with _ -> failwith ("Failed to parse expression: " ^ s)

(** [eval e] evaluates a symbolic expression [e] to a concrete integer address or value.
    It resolves symbols using [Symbols.get_symbol_addr] and performs arithmetic/bitwise operations. *)
let rec eval e =
  match e with
  | EInt i -> i
  | EVar v ->
    (* Check VA symbols first (e.g., x, y in register values are VAs) then fall back to PA *)
    (match Hashtbl.find_opt Symbols.virt_symbols v with
     | Some va -> va
     | None -> Symbols.get_symbol_addr v)
  | ESlice(sub, hi, lo) ->
    let v = eval sub in
    let mask = Z.sub (Z.shift_left Z.one (hi - lo + 1)) Z.one in
    Z.logand (Z.shift_right v lo) mask
  | ECall("extz", args) -> snd(List.nth args 0) |> eval
  (* [desc3] constructs a Level 3 page descriptor (0x60000000000743 = RW, non-executable)
     For VA symbols, we need to resolve to the PA they map to *)
  | ECall("desc3", args) ->
    let pa_expr = snd(List.nth args 0) in
    let pa = match pa_expr with
      | EVar v -> Symbols.get_pa_for_va v  (* Resolve VA->PA mapping *)
      | _ -> eval pa_expr
    in
    Z.logor pa Constants.leaf_page_desc
  (* [mkdescN] constructs a Level N page descriptor with output address and optional attributes.
     mkdesc3(oa=addr) creates a leaf page descriptor; mkdesc2(table=addr) creates a table descriptor *)
  | ECall(name, args) when String.length name >= 6 && String.sub name 0 6 = "mkdesc" ->
    let level = int_of_string (String.sub name 6 1) in
    (* Check for table descriptor (next-level pointer) vs page descriptor (leaf) *)
    let is_table = List.exists (fun (k, _) -> k = "table") args in
    if is_table || level < 3 then
      (* Table descriptor: just set valid+table bits (0x3) *)
      let addr = try List.assoc "table" args |> eval
                 with Not_found -> snd(List.nth args 0) |> eval in
      Z.logor addr Constants.table_descriptor_bits
    else
      (* Page descriptor: use full descriptor format with OA directly (no VA->PA resolution) *)
      let oa = try List.assoc "oa" args |> eval
               with Not_found -> snd(List.nth args 0) |> eval in
      Z.logor oa Constants.leaf_page_desc
  (* [pteN/tableN] calculates the Physical Address of a Page Table Entry at a given level.
     If explicit table argument provided (not page_table_base), use it directly.
     Otherwise, for pte2/pte3, use tracked L2/L3 table addresses from install_mapping. *)
  | ECall(name, args) when
      (String.length name = 4 && String.sub name 0 3 = "pte") ||
      (String.length name = 6 && String.sub name 0 5 = "table") ->
    let level = int_of_string (String.sub name (String.length name - 1) 1) in
    let shift = Constants.shift_for_level level in
    let va_expr = snd (List.nth args 0) in
    let va = eval va_expr in
    let explicit_table =
      if List.length args > 1 then
        match snd (List.nth args 1) with
        | EVar "page_table_base" -> None
        | _ -> Some (eval(snd(List.nth args 1)))
      else None
    in
    let table = match explicit_table with
      | Some addr -> addr
      | None -> get_table_for_level level va_expr
    in
    let idx = Z.to_int (Z.logand (Z.shift_right va shift) Constants.pte_index_mask) in
    Z.add table (Z.of_int (idx * Constants.pte_size))
  (* Bitvector operations handling (add, sub, logical ops, shifts) *)
  | ECall(op, args) when String.length op >= 2 && String.sub op 0 2 = "bv" ->
    let v1 = eval (snd (List.nth args 0)) in
    let v2 = eval (snd (List.nth args 1)) in
    (match op with
     | "bvor"   -> Z.logor v1 v2
     | "bvand"  -> Z.logand v1 v2
     | "bvxor"  -> Z.logxor v1 v2
     | "bvadd"  -> Z.add v1 v2
     | "bvsub"  -> Z.sub v1 v2
     | "bvlshr" -> Z.shift_right v1 (Z.to_int v2)
     | "bvshl"  -> Z.shift_left v1 (Z.to_int v2)
     | _ -> failwith ("Unknown bitvector operation: " ^ op))

  | ECall("page", args) ->
    Z.logand (eval(snd(List.nth args 0))) Constants.page_mask
  | ECall("offset", args) ->
    let va_arg = try List.assoc "va" args with _ -> snd(List.nth args 1) in
    let va = eval va_arg in
    let idx = Z.to_int (Z.logand (Z.shift_right va page_shift) Constants.pte_index_mask) in
    Z.of_int (idx * Constants.pte_size)
  | ECall("ttbr", args) ->
    let base_arg = try List.assoc "base" args with _ -> snd(List.nth args 1) in
    eval base_arg
  | ECall("add_bits_int", [( _, sub); (_, EInt delta)]) -> Z.add (eval sub) delta
  | ECall _ -> Z.zero
