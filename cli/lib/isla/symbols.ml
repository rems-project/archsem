(** Immutable symbol table with bump allocation. *)

type t = {
  next_addr : int option;
  table : (string * int) list;
  reserved : (int * int) list;  (** (addr, size) pairs for reserved ranges *)
}

let page_bits () =
  let bits =
    Otoml.find (Litmus.Config.get ()) Otoml.get_integer ["isla"; "page_bits"] in
  if bits < 0 then failwith "config: [isla] page_bits must be non-negative";
  bits

let page_size () = 1 lsl page_bits ()

let base_addr () =
  Otoml.find_or ~default:0x500 (Litmus.Config.get ()) Otoml.get_integer
    ["isla"; "symbols"; "base_address"]

let empty = {
  next_addr = None;
  table = [];
  reserved = [];
}

let overlaps addr size (r_addr, r_size) =
  addr < r_addr + r_size && r_addr < addr + size

let reserve t addr size =
  { t with reserved = (addr, size) :: t.reserved }

let alloc_page t =
  let page_size = page_size () in
  let rec find_free addr =
    if List.exists (overlaps addr page_size) t.reserved then
      find_free (addr + page_size)
    else
      addr
  in
  let addr = find_free (Option.value t.next_addr ~default:(base_addr ())) in
  ({ t with next_addr = Some (addr + page_size) }, addr)

let alloc_data t name =
  match List.assoc_opt name t.table with
  | Some addr -> (t, addr)
  | None ->
    let t, addr = alloc_page t in
    let t = {
      t with
      table = (name, addr) :: t.table;
    } in
    (t, addr)

let alloc_code t size =
  let page_size = page_size () in
  assert (size < page_size);
  alloc_page t

let resolve_opt t name = List.assoc_opt name t.table
let resolve t name =
  match List.assoc_opt name t.table with
  | Some sym -> sym
  | None -> failwith ("Unknown symbol: " ^ name)
