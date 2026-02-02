(** Physical address region allocator.

    Tracks allocated regions and provides aligned PA allocation with no
    overlaps. Works together with [Symbols] which manages the free PA pointer. *)

(* (start, end) inclusive on both sides *)
type interval = Z.t * Z.t

let used_regions = ref ([] : interval list)

let add_region start size =
  let end_a = Z.sub (Z.add start size) Z.one in
  used_regions := (start, end_a) :: !used_regions

let is_free start size =
  let end_a = Z.sub (Z.add start size) Z.one in
  not (List.exists (fun (s, e) -> (Z.lt start e) && (Z.gt end_a s)) !used_regions)

(* Find a free aligned region starting from [Symbols.next_free_addr],
   mark it as used, advance the free pointer, and return the address.
   Unlike [Symbols.get_symbol_addr], this does not call
   [allocator_add_region] — the caller is responsible for registration. *)
let alloc size alignment =
  let rec try_find base =
    let rem = Z.rem base alignment in
    let aligned =
      if Z.equal rem Z.zero then base else Z.add base (Z.sub alignment rem) in
    if is_free aligned size then (
      add_region aligned size;
      aligned
    ) else try_find (Z.add base Constants.page_size_z)
  in
  let res = try_find !Symbols.next_free_addr in
  Symbols.next_free_addr := Z.add res size;
  res

let reset () =
  used_regions := []
