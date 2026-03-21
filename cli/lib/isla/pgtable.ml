(** Page table setup DSL: types and parser.

    Defines the abstract syntax for AArch64 page table setup DSL statements.
    The parser ({!Pgtable_parser}) produces values of type {!stmt}. *)

(** {1 Abstract syntax} *)

type addr_kind = Physical | Virtual | Intermediate

type addr_decl = {
  kind : addr_kind;
  names : string list;
  alignment : int option;
}

type attr_group = (string * Term.t) list

type with_spec_item =
  | WsDefault
  | WsCode
  | WsAttrs of attr_group

type with_spec = with_spec_item list

type mapping_mod = {
  with_spec : with_spec;
  level : int option;
  walk_name : string option;
}

let no_mod = { with_spec = [WsDefault]; level = None; walk_name = None }

type mapping_source =
  | SrcName of string
  | SrcExpr of Term.t  (** function call, e.g. [pa_to_ipa(table3(walkx))] *)

type mapping_target =
  | PA of string      (** named physical address *)
  | Invalid           (** invalid descriptor — triggers translation fault *)

type identity_target =
  | IdName of string  (** declared address name *)
  | IdAddr of int     (** literal address, e.g. [identity 0x1000] *)
  | IdFn of string * Term.t list  (** function call, e.g. [identity pa_to_ipa(0x1000)] *)

type table_stage = S1 | S2

type cmp_op = CmpEq | CmpNeq

type assert_expr =
  | AVar of string
  | ASlice of string * int * int   (** name[hi..lo] *)
  | AFn of string * assert_expr list

type stmt =
  | AddrDecl of addr_decl
  | Mapping of { va : mapping_source; pa : mapping_target; modifiers : mapping_mod }
  | OptMapping of { va : mapping_source; pa : mapping_target; modifiers : mapping_mod }
  | Identity of { target : identity_target; with_spec : with_spec }
  | MemInit of { addr : string; value : Term.t }
  | TableBlock of { stage : table_stage; name : string;
                    base : int; body : stmt list }
  | TableRef of { stage : table_stage; name : string }
  | Option of { name : string; value : bool }
  | Assert of { lhs : assert_expr; op : cmp_op; rhs : assert_expr }
