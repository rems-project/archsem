(** Immutable symbol table with bump allocation.

    Each allocation returns a new state. Data symbols get page-aligned
    addresses from the data region. Code regions get addresses from the
    code region. *)

type t = {
  next_data : Z.t;
  next_code : Z.t;
  table : (string * Z.t) list;
}

let page_size = 0x1000

let empty = {
  next_data = Z.of_int 0x500;
  next_code = Z.of_int 0x20000;
  table = [];
}

let alloc_data t name =
  match List.assoc_opt name t.table with
  | Some addr -> (t, addr)
  | None ->
    let addr = t.next_data in
    let t = { t with
      next_data = Z.add t.next_data (Z.of_int page_size);
      table = (name, addr) :: t.table;
    } in
    (t, addr)

let alloc_code t size =
  let addr = t.next_code in
  let aligned = Z.add addr (Z.of_int ((size + page_size - 1) / page_size * page_size)) in
  let t = { t with next_code = aligned } in
  (t, addr)

let resolve t name = List.assoc_opt name t.table
