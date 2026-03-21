(** Functions for isla term evaluation.

    Each function is registered with its parameter names (for keyword
    argument alignment) and an evaluation function on positional args.

    Functions that need page table context receive it via [table_data].
    Pure functions ignore it. *)

type table_data = (int * Bytes.t) list

type fn_spec = {
  params : string list;
  eval : table_data -> Z.t list -> Z.t;
}

(** {1 Pure functions} *)

let arity_error name n =
  failwith (Printf.sprintf "function %s: expected %d args" name n)

let bv_functions : (string * fn_spec) list = [
  "bvand", {
    params = ["a"; "b"];
    eval = (fun _ -> function [a; b] -> Z.logand a b | _ -> arity_error "bvand" 2);
  };
  "bvor", {
    params = ["a"; "b"];
    eval = (fun _ -> function [a; b] -> Z.logor a b | _ -> arity_error "bvor" 2);
  };
  "bvxor", {
    params = ["a"; "b"];
    eval = (fun _ -> function [a; b] -> Z.logxor a b | _ -> arity_error "bvxor" 2);
  };
  "bvshl", {
    params = ["a"; "b"];
    eval = (fun _ -> function
      | [a; b] -> Z.shift_left a (Z.to_int b) | _ -> arity_error "bvshl" 2);
  };
  "bvlshr", {
    params = ["a"; "b"];
    eval = (fun _ -> function
      | [a; b] -> Z.shift_right a (Z.to_int b) | _ -> arity_error "bvlshr" 2);
  };
  "extz", {
    params = ["bits"; "len"];
    eval = (fun _ -> function [bits; _len] -> bits | _ -> arity_error "extz" 2);
  };
  "exts", {
    params = ["bits"; "len"];
    eval = (fun _ -> function
      | [bits; len] ->
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

(** {1 Page table helpers} *)

let entry_size = 8

let level_shift = function
  | 0 -> 39 | 1 -> 30 | 2 -> 21 | 3 -> 12
  | n -> failwith (Printf.sprintf "function: invalid page table level %d" n)

let va_index va level = (va lsr level_shift level) land 0x1FF

let read_entry data idx =
  let offset = idx * entry_size in
  let v = ref 0 in
  for i = 7 downto 0 do
    v := (!v lsl 8) lor Char.code (Bytes.get data (offset + i))
  done;
  !v

let lookup_pte_addr ~table_data ~base va level =
  let rec walk addr lvl =
    if lvl = level then
      addr + va_index va level * entry_size
    else
      let tbl = List.assoc addr table_data in
      let idx = va_index va lvl in
      let desc = read_entry tbl idx in
      if desc land 0x3 <> 0x3 then
        failwith (Printf.sprintf
          "function: no table descriptor at level %d for VA 0x%x" lvl va);
      let next = desc land 0x0000FFFFFFFFF000 in
      walk next (lvl + 1)
  in
  walk base 0

let lookup_desc_value ~table_data ~base va level =
  let rec walk addr lvl =
    let tbl = List.assoc addr table_data in
    let idx = va_index va lvl in
    if lvl = level then
      read_entry tbl idx
    else
      let desc = read_entry tbl idx in
      if desc land 0x3 <> 0x3 then
        failwith (Printf.sprintf
          "function: no table descriptor at level %d for VA 0x%x" lvl va);
      let next = desc land 0x0000FFFFFFFFF000 in
      walk next (lvl + 1)
  in
  walk base 0

let table_descriptor next_table_pa =
  (next_table_pa land 0x0000FFFFFFFFF000) lor 0x3

let default_data_attrs = 0x440

let page_descriptor pa attrs =
  (pa land 0x0000FFFFFFFFF000) lor attrs lor 0x3

let block_descriptor pa level attrs =
  let shift = level_shift level in
  let mask = (-1) lsl shift in
  (pa land mask land 0x0000FFFFFFFFFFFF) lor attrs lor 0x1

let make_desc ~level ~oa ~attrs =
  if level = 3 then page_descriptor oa attrs
  else block_descriptor oa level attrs

(** {1 Page table query functions} *)

let pgt_fn_for_level prefix level ~mk_eval =
  let name = Printf.sprintf "%s%d" prefix level in
  (name, { params = ["va"; "base"]; eval = mk_eval name level })

let pgt_functions : (string * fn_spec) list =
  let levels = [0; 1; 2; 3] in
  [ "page", {
      params = ["a"];
      eval = (fun _ -> function
        | [a] -> Z.logand (Z.shift_right a 12) (Z.sub (Z.shift_left Z.one 36) Z.one)
        | _ -> arity_error "page" 1);
    }
  ]
  @ List.map (pgt_fn_for_level "pte" ~mk_eval:(fun name level ->
      fun td -> function
        | [va; base] ->
          Z.of_int (lookup_pte_addr ~table_data:td
            ~base:(Z.to_int base) (Z.to_int va) level)
        | _ -> arity_error name 2))
    levels
  @ List.map (pgt_fn_for_level "desc" ~mk_eval:(fun name level ->
      fun td -> function
        | [va; base] ->
          Z.of_int (lookup_desc_value ~table_data:td
            ~base:(Z.to_int base) (Z.to_int va) level)
        | _ -> arity_error name 2))
    levels
  @ List.concat_map (fun level ->
      let name = Printf.sprintf "mkdesc%d" level in
      [ name, {
          params = ["oa"];
          eval = (fun _ -> function
            | [oa] ->
              Z.of_int (make_desc ~level ~oa:(Z.to_int oa) ~attrs:default_data_attrs)
            | _ -> arity_error name 1);
        };
        name ^ "_table", {
          params = ["table"];
          eval = (fun _ -> function
            | [table_addr] -> Z.of_int (table_descriptor (Z.to_int table_addr))
            | _ -> arity_error (name ^ "_table") 1);
        };
      ])
    levels

(** {1 Lookup and evaluation} *)

let functions : (string * fn_spec) list = bv_functions @ pgt_functions

let find name = List.assoc_opt name functions

let eval_fn ?(td=[]) name args =
  match find name with
  | Some spec -> spec.eval td args
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

let eval_kwfn ?(td=[]) name kwargs =
  let args = align_kwargs name kwargs in
  eval_fn ~td name args
