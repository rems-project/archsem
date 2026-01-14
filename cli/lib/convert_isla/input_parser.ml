(** Thread code and register configuration *)
type thread_info = {
  tid: string;
  code_pa: Z.t;
  code_size: Z.t;
  instructions: int list;
  reset_regs: (string * Otoml.t) list;
}

(** Exception handler section *)
type section_info = {
  sec_name: string;
  sec_addr: Z.t;
  sec_size: Z.t;
  sec_instructions: int list;
}

(** Parse page_table_setup from TOML *)
let parse_pt_setup toml =
  match Otoml.find_opt toml (fun x -> x) ["page_table_setup"] with
  | Some (Otoml.TomlString s) ->
      let lexbuf = Lexing.from_string s in
      begin try Parser.main_dsl Lexer.read lexbuf with Parser.Error ->
        let pos = Lexing.lexeme_start_p lexbuf in
        failwith (Printf.sprintf "Syntax error at line %d, char %d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol))
      end
  | _ -> []

(** Parse thread definitions from TOML *)
let parse_threads toml arch identity_code_addrs =
  let threads = ref [] in
  let identity_idx = ref 0 in
  (match Otoml.find_opt toml (fun x -> x) ["thread"] with
   | Some (Otoml.TomlTable thread_list) ->
       List.iter (fun (tid, val_toml) ->
         match val_toml with
         | Otoml.TomlTable k ->
             (match List.assoc_opt "code" k with
              | Some (Otoml.TomlString asm) ->
                  let instructions = Assembler.encode_assembly ~arch asm in
                  let code_size = Z.of_int (List.length instructions * 4) in
                  (* Allocate code PA: use identity address if provided, else page-aligned *)
                  let code_pa =
                    if !identity_idx < List.length identity_code_addrs then (
                      let base = List.nth identity_code_addrs !identity_idx in
                      incr identity_idx;
                      (* Offset thread code past exception vector table (0x800)
                         and by page size (0x1000) per thread to avoid overlap *)
                      let thread_idx = int_of_string tid in
                      Z.add base (Z.of_int (0x800 + 0x1000 * thread_idx))
                    ) else Symbols.get_code_addr ("code_" ^ tid) (Z.to_int code_size)
                  in
                  (* Support both 'reset' (pgtable tests) and 'init' (usermode tests) *)
                  let reset_regs = match List.assoc_opt "reset" k with
                    | Some (Otoml.TomlTable regs) -> regs
                    | Some (Otoml.TomlInlineTable regs) -> regs
                    | _ -> match List.assoc_opt "init" k with
                      | Some (Otoml.TomlTable regs) -> regs
                      | Some (Otoml.TomlInlineTable regs) -> regs
                      | _ -> []
                  in
                  threads := { tid; code_pa; code_size; instructions; reset_regs } :: !threads
              | _ -> ())
         | _ -> ()
       ) thread_list
   | _ -> ());
  List.sort (fun a b -> String.compare a.tid b.tid) !threads

(** Parse section definitions from TOML *)
let parse_sections toml arch =
  let sections = ref [] in
  (match Otoml.find_opt toml (fun x -> x) ["section"] with
   | Some (Otoml.TomlTable section_list) ->
       List.iter (fun (name, val_toml) ->
         match val_toml with
         | Otoml.TomlTable k ->
             (match List.assoc_opt "address" k, List.assoc_opt "code" k with
              | Some (Otoml.TomlString addr_s), Some (Otoml.TomlString asm) ->
                  let addr = Z.of_string addr_s in
                  let instructions = Assembler.encode_assembly ~arch asm in
                  let size = Z.of_int (List.length instructions * 4) in
                  sections := { sec_name = name; sec_addr = addr; sec_size = size; sec_instructions = instructions } :: !sections
              | _ -> ())
         | _ -> ()
       ) section_list
   | _ -> ());
  !sections
