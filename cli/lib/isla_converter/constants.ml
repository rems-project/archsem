(** Shared constants for AArch64 page tables and memory layout.

    4KB granule, 4-level page tables (L0-L3), 48-bit VA. *)

(** Page size *)
let page_size = 4096
let page_size_z = Z.of_int page_size

(** Page table entry size (8 bytes = 64 bits) *)
let pte_size = 8

(** PTE index: 9 bits = 512 entries per table *)
let pte_index_bits = 9
let pte_index_mask = Z.of_int 0x1FF

(** VA shifts per level: L0=[47:39], L1=[38:30], L2=[29:21], L3=[20:12] *)
let level0_shift = 39

let shift_for_level level =
  level0_shift - (pte_index_bits * level)

(** Masks *)
let page_mask = Z.of_string "0xFFFFFFFFFFFFF000"

(** Descriptor bits *)
let table_descriptor_bits = Z.of_int 3  (* valid + table *)
let leaf_page_desc = Z.of_string "0x60000000000743"  (* RW, non-executable *)
let code_descriptor = Z.of_int 0x6C3  (* RO, executable *)
let data_descriptor = leaf_page_desc

(** Memory layout *)
let initial_pa = Z.of_int 0x50000
let initial_code_va = Z.of_string "0x40000000"
let initial_data_va = Z.of_string "0x8000000000"
let constraint_skip = Z.of_int 0x100000

(** Code layout *)
let instruction_size = 4  (* AArch64: 32-bit instructions *)
let exception_vector_offset = 0x800  (* Offset before thread code for exception vectors *)
let thread_code_base = Z.of_int 0x10000  (* Base PA for thread code pool *)
