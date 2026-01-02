type interval = Z.t * Z.t
let used_regions = ref ([] : interval list)
let add_region start size =
  let end_a = Z.sub (Z.add start size) Z.one in
  used_regions := (start, end_a) :: !used_regions

let is_free start size =
  let end_a = Z.sub (Z.add start size) Z.one in
  not (List.exists (fun (s, e) -> (Z.lt start e) && (Z.gt end_a s)) !used_regions)

let alloc size alignment =
  let rec try_find base =
    let rem = Z.rem base alignment in
    let aligned = if Z.equal rem Z.zero then base else Z.add base (Z.sub alignment rem) in
    if is_free aligned size then (
      add_region aligned size;
      aligned
    ) else try_find (Z.add base (Z.of_int 0x1000))
  in
  let res = try_find !Symbols.next_free_addr in
  Symbols.next_free_addr := Z.add res size;
  res
