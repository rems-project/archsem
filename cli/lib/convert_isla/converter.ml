open Ast

(* --- Logic & Evaluation --- *)
type update = { addr: Z.t; data: Z.t; comment: string }
let pt_updates = ref ([] : update list)
let has_code_identity = ref false

let rec process_dsl stmts root_table =
  (* Pass 1: Collect constraints and declarations *)
  List.iter (fun stmt ->
    match stmt with
    | Decl("virtual", ns) -> List.iter (fun n -> ignore(Symbols.get_virt_symbol n)) ns
    | Decl(_,ns) -> List.iter(fun n -> ignore(Symbols.get_symbol_addr n)) ns
    | Assert(c) -> Symbols.record_constraint c
    | Identity(_, is_code) -> if is_code then has_code_identity := true
    | _ -> ()
  ) stmts;

  (* Pass 2: Process mappings and definitions *)
  List.iter (fun stmt ->
    match stmt with
    | Identity(a, _) -> install_mapping !root_table 0 (Z.of_string a) (TPA a) None None
    | TableDef{name;addr;body} -> let t=Z.of_string addr in Hashtbl.add Symbols.symbols name t; process_dsl body (ref t)
    | Mapping{va;target;level;variant=_;alias} ->
        let va_val = if String.contains va '(' then
             Evaluator.eval (Evaluator.parse_string va)
          else Symbols.get_virt_symbol va
        in
        (* Track Mapping for header if simple symbols *)
        (match target with TPA(pa) -> Symbols.update_va_mapping_pa va pa | _ -> ());

        install_mapping !root_table 0 va_val target level alias
    | MemInit(pa,v) -> pt_updates := {addr=Symbols.get_symbol_addr pa; data=Z.of_string v; comment="Initial Data"} :: !pt_updates
    | _ -> ()
  ) stmts
and install_mapping table_base level va target force_level alias_opt =
  let shift = match level with 0->39|1->30|2->21|3->12|_->0 in
  let idx = Z.to_int (Z.logand (Z.shift_right va shift) (Z.of_int 0x1FF)) in
  let entry_addr = Z.add table_base (Z.of_int (idx*8)) in
  let is_leaf = (level=3) || (match force_level with Some l->l=level|None->false) in
  if is_leaf then
    let desc = match target with
      | TInvalid->Z.zero
      | TPA p->Z.logor (Symbols.get_symbol_addr p) (Z.of_int 0x403)
      | TTable p_name -> Z.logor (Symbols.get_symbol_addr p_name) (Z.of_int 3)
      | TTableAddr addr -> Z.logor addr (Z.of_int 3)
      | TRaw v -> v
    in
    let c = Printf.sprintf "Level %d Entry for VA 0x%s" level (Z.format "%x" va) in
    pt_updates := {addr=entry_addr; data=desc; comment=c} :: !pt_updates;
    (match alias_opt with Some a -> Hashtbl.add Symbols.symbols a entry_addr | None -> ())
  else
    (* Reuse table if exists *)
    let key = (Z.to_string table_base)^"_"^(string_of_int idx) in
    let next = match Hashtbl.find_opt Symbols.symbols key with Some a->a | None ->
       let n = Allocator.alloc (Z.of_int 4096) (Z.of_int 4096) in Hashtbl.add Symbols.symbols key n;
       let c = Printf.sprintf "Level %d Table Pointer for VA 0x%s" level (Z.format "%x" va) in
       pt_updates := {addr=entry_addr; data=Z.logor n (Z.of_int 3); comment=c} :: !pt_updates; n
    in install_mapping next (level+1) va target force_level alias_opt

(* --- Main Process --- *)

type thread_data = {
  tid: string;
  pa: Z.t;
  size: Z.t;
  asm: int list;
  reset: (string * Otoml.t) list;
}

let process_toml filename out_channel =
  let toml = Otoml.Parser.from_file filename in

  (* 1. Pre-parsing needed only if NO page table setup provided (Legacy mode)
     Moved logic below *)

  (* 2. Scan Threads - Allocate PAs, store data *)
  let threads_data = ref [] in
  (match Otoml.find_opt toml (fun x->x) ["thread"] with Some (Otoml.TomlTable threads) ->
     List.iter (fun (tid, val_toml) ->
       let code_base = Symbols.get_symbol_addr ("code_"^tid) in
       match val_toml with Otoml.TomlTable k ->
         (match List.assoc_opt "code" k with Some (Otoml.TomlString asm) ->
             let instrs = Assembler.encode_assembly asm in
             let size = Z.of_int (List.length instrs * 4) in
             let reset = match List.assoc_opt "reset" k with Some(Otoml.TomlTable regs) -> regs | _ -> [] in
             threads_data := {tid; pa=code_base; size; asm=instrs; reset} :: !threads_data
          | _ -> ())
       | _ -> ()
     ) threads | _ -> ());

  (* Sort threads by TID - e.g. thread.0, thread.1 *)
  threads_data := List.sort (fun a b -> String.compare a.tid b.tid) !threads_data;

  let root_table = ref Z.zero in

  (* 3. Parse and Analyze Page Table Setup *)
  let pt_stmts =
    match Otoml.find_opt toml (fun x -> x) ["page_table_setup"] with
    | Some (Otoml.TomlString s) ->
       let lexbuf = Lexing.from_string s in
       begin try Parser.main_dsl Lexer.read lexbuf
       with Parser.Error ->
           let pos = Lexing.lexeme_start_p lexbuf in
           failwith (Printf.sprintf "Syntax error at line %d, char %d. Token: %s"
             pos.pos_lnum (pos.pos_cnum - pos.pos_bol) (Lexing.lexeme lexbuf))
       end
    | Some _ | None -> []
  in

  (* LEGACY PRE-SCAN: Only if NO custom PT setup is used *)
  if pt_stmts = [] then (
    (try match Otoml.find toml (fun x->x) ["symbolic"] with Otoml.TomlArray l->List.iter (function Otoml.TomlString s->ignore(Symbols.get_symbol_addr s)|_->()) l |_->() with _->())
  );

  has_code_identity := false; (* Reset global state *)
  List.iter (function Identity(_, true) -> has_code_identity := true | _ -> ()) pt_stmts;

  (* 4. Determine Code Virtual Addresses *)
  let thread_vas = List.map (fun t ->
    let va = if !has_code_identity then t.pa else Symbols.get_virt_symbol ("code_"^t.tid) in
    (t.tid, va)
  ) !threads_data in

  (* 5. Process DSL *)
  if pt_stmts <> [] then (
     root_table := Allocator.alloc (Z.of_int 4096) (Z.of_int 4096);
     Printf.eprintf "Root: 0x%s\n" (Z.format "%x" !root_table);
     process_dsl pt_stmts root_table;

     (* 6. Map Code Regions *)
     List.iter2 (fun t (_, va) ->
        let start_page = Z.logand va (Z.of_string "0xFFFFFFFFFFFFF000") in
        let end_page = Z.logand (Z.sub (Z.add va t.size) Z.one) (Z.of_string "0xFFFFFFFFFFFFF000") in

        let rec map_pages curr_va curr_pa =
           if Z.gt curr_va end_page then () else (
             install_mapping !root_table 0 curr_va (TRaw(Z.logor curr_pa (Z.of_int 0x403))) None None;
             map_pages (Z.add curr_va (Z.of_int 4096)) (Z.add curr_pa (Z.of_int 4096))
           )
        in
        map_pages start_page (Z.logand t.pa (Z.of_string "0xFFFFFFFFFFFFF000"))
     ) !threads_data thread_vas
  );

  (* 7. Output Emission *)
  let arch = match Otoml.find_opt toml (fun x->x) ["arch"] with Some (Otoml.TomlString s) -> s | _ -> "AArch64" in
  let name = match Otoml.find_opt toml (fun x->x) ["name"] with Some (Otoml.TomlString s) -> s | _ -> "converted" in
  Printf.fprintf out_channel "arch = \"%s\"\nname = \"%s\"\n" arch name;
  if !Symbols.va_mappings <> [] then (
    Printf.fprintf out_channel "# Symbolic Variable Mapping:\n";
    List.iter (fun (n, addr, pa_opt) ->
       (* Resolve the PA name to an actual address if exists *)
       let pa_str = match pa_opt with
         | Some p_name ->
             (match Hashtbl.find_opt Symbols.symbols p_name with
              | Some p_addr -> Printf.sprintf " (mapped to PA %s=0x%s)" p_name (Z.format "%x" p_addr)
              | None -> Printf.sprintf " (mapped to PA %s=UNKNOWN)" p_name)
         | None -> ""
       in
       Printf.fprintf out_channel "# %s = 0x%s%s\n" n (Z.format "%x" addr) pa_str
    ) (List.rev !Symbols.va_mappings)
  );
  Printf.fprintf out_channel "\n";

  (* Emit PT updates - SORTED: Initial Data first, then Page Tables *)
  let initial_data, page_tables = List.partition (fun u -> u.comment = "Initial Data") !pt_updates in

  let sort_and_emit updates =
      let sorted = List.sort (fun a b -> Z.compare a.addr b.addr) updates in
      List.iter (fun u -> Printf.fprintf out_channel "[[memory]] # %s\nbase = 0x%s\nsize = 8\ndata = 0x%s\n\n" u.comment (Z.format "%x" u.addr) (Z.format "%x" u.data)) sorted
  in

  sort_and_emit initial_data;
  sort_and_emit page_tables;

  (* Emit Code Memory and Registers *)
  List.iter2 (fun t (_, va) ->
     Printf.fprintf out_channel "[[memory]] # Code %s (PA=0x%s)\nbase = 0x%s\nsize = 4\ndata = %s\n\n"
        t.tid (Z.format "%x" t.pa) (Z.format "%x" t.pa)
        ("[" ^ (String.concat ", " (List.map (Printf.sprintf "0x%x") t.asm)) ^ "]");

     (* Registers *)
     let parsed_reg_names = ref [] in
     let parsed_regs = List.map (fun (r,v) -> parsed_reg_names := r::!parsed_reg_names;
        let vs = match v with Otoml.TomlString s -> "0x"^(Z.format "%x" (Evaluator.eval(Evaluator.parse_string s))) | Otoml.TomlInteger i -> string_of_int i | _ -> "0x0" in
        Printf.sprintf "%s = %s" r vs) t.reset in
     let default_regs = let rec range i acc = if i>30 then acc else let rn="R"^(string_of_int i) in
        if List.mem rn !parsed_reg_names then range(i+1) acc else range(i+1) ((Printf.sprintf "%s = 0x0" rn)::acc) in range 0 [] in
     Printf.fprintf out_channel "[[registers]] # %s\n_PC = 0x%s\n%s\n\n" t.tid (Z.format "%x" va) (String.concat "\n" (parsed_regs@default_regs))
  ) !threads_data thread_vas;

  (* Emit TermCond *)
  List.iter2 (fun t (_, va) ->
     let end_pc = Z.add va t.size in
     Printf.fprintf out_channel "[[termCond]] # %s\n_PC = 0x%s\n\n" t.tid (Z.format "%x" end_pc)
  ) !threads_data thread_vas;

  (* Emit Final Assertions *)
  match Otoml.find_opt toml (fun x->x) ["final"] with Some (Otoml.TomlTable t) ->
     (match List.assoc_opt "assertion" t with Some (Otoml.TomlString s) ->
        let s = Str.global_replace (Str.regexp " ") "" s in
        (* Split by | *)
        let alternatives =
           if String.contains s '|' then
             Str.split (Str.regexp "|") s
           else [s]
        in
        List.iter (fun alt ->
           let asserts = String.split_on_char '&' alt in
           Printf.fprintf out_channel "[[expected]]\n";
           let grouped_asserts = Hashtbl.create 5 in
           List.iter (fun assertion ->
              let parts = String.split_on_char '=' assertion in
              match parts with
              | [lhs; rhs] ->
                 (match String.split_on_char ':' lhs with
                  | [tid_s; reg_s] ->
                      let reg_s = Str.global_replace (Str.regexp "^X") "R" (String.trim reg_s) in
                      let existing = try Hashtbl.find grouped_asserts tid_s with Not_found -> [] in
                      Hashtbl.replace grouped_asserts tid_s ((reg_s, rhs)::existing)
                  | _ -> ())
              | _ -> ()
           ) asserts;
           Hashtbl.iter (fun tid regs ->
              Printf.fprintf out_channel "[expected.%s]\n" tid;
              List.iter (fun (r,v) -> Printf.fprintf out_channel "%s = %s\n" r v) (List.rev regs)
           ) grouped_asserts;
           Printf.fprintf out_channel "\n";
        ) alternatives
      | _ -> ()) | _ -> ()
