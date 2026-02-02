(** Shared types for isla-to-archsem conversion. *)

(** Thread with encoded instructions and allocated address *)
type thread_info = {
  tid: string;
  code_pa: Z.t;
  code_size: Z.t;
  instructions: int list;
  reset_regs: (string * Otoml.t) list;
}

(** Section with encoded instructions *)
type section_info = {
  sec_name: string;
  sec_addr: Z.t;
  sec_size: Z.t;
  sec_instructions: int list;
}
