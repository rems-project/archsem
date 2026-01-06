type interval = Z.t * Z.t

let used_regions = ref ([] : interval list)

(* [add_region start size] marks the memory range [start, start + size - 1]
   as allocated by adding it to the internal list of used regions. *)
let add_region start size =
  let end_a = Z.sub (Z.add start size) Z.one in
  used_regions := (start, end_a) :: !used_regions

(* [is_free start size] returns true if the memory range [start, start + size - 1]
   does not overlap with any previously allocated regions. *)
let is_free start size =
  let end_a = Z.sub (Z.add start size) Z.one in
  not (List.exists (fun (s, e) -> (Z.lt start e) && (Z.gt end_a s)) !used_regions)

(* [alloc size alignment] finds a free memory region of [size] bytes aligned to [alignment].
   It starts searching from [!Symbols.next_free_addr], marks the found region as used,
   updates [Symbols.next_free_addr], and returns the starting address. *)
let alloc size alignment =
  let rec try_find base =
    let rem = Z.rem base alignment in
    let aligned =
      if Z.equal rem Z.zero then base else Z.add base (Z.sub alignment rem) in
    if is_free aligned size then (
      add_region aligned size;
      aligned
    ) else try_find (Z.add base (Z.of_int 0x1000))
  in
  let res = try_find !Symbols.next_free_addr in
  Symbols.next_free_addr := Z.add res size;
  res
