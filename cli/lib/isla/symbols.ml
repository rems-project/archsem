(** Immutable symbol table with bump allocation. *)

type t = {
  mutable next_addr : int;
  mutable table : (string * int) list;
  mutable reserved : (int * int) list;  (** (addr, size) pairs for reserved ranges *)
}

let resolve_opt t name = List.assoc_opt name t.table
let resolve t name =
  match List.assoc_opt name t.table with
  | Some sym -> sym
  | None -> failwith ("Unknown symbol: " ^ name)

let page_bits () =
  let bits =
    Otoml.find (Litmus.Config.get ()) Otoml.get_integer ["isla"; "page_bits"] in
  if bits < 0 then failwith "config: [isla] page_bits must be non-negative";
  bits

let page_size () = 1 lsl page_bits ()

let base_addr () =
  Otoml.find_or ~default:0x500 (Litmus.Config.get ()) Otoml.get_integer
    ["isla"; "symbols"; "base_address"]

let empty () = {
  next_addr = base_addr ();
  table = [];
  reserved = [];
}

let overlaps addr size (r_addr, r_size) =
  addr < r_addr + r_size && r_addr < addr + size

let reserve t addr size =
  t.reserved <- (addr, size) :: t.reserved

let alloc_page t =
  let page_size = page_size () in
  let rec find_free addr =
    if List.exists (overlaps addr page_size) t.reserved then
      find_free (addr + page_size)
    else
      addr
  in
  let addr = find_free t.next_addr in
  t.next_addr <- addr + page_size;
  addr

let alloc_sym t name =
  match resolve_opt t name with
  | Some _ -> ()
  | None ->
    let addr = alloc_page t in
    t.table <- (name, addr) :: t.table;
    ()

let resolve_or_alloc t name =
  match resolve_opt t name with
  | Some addr -> addr
  | None ->
    let addr = alloc_page t in
    t.table <- (name, addr) :: t.table;
    addr

