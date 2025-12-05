(** Symbolic expressions (Integers, Variables, Calls, Slices) *)
type expr =
  | EInt of Z.t
  | EVar of string
  | ECall of string * (string * expr) list
  | ESlice of expr * int * int

(** Page table entry target (Physical Address, Table, or Invalid) *)
type target_expr =
  | TPA of string         (** Named Physical Address *)
  | TTable of string      (** Named Page Table *)
  | TTableAddr of Z.t     (** Concrete Address *)
  | TRaw of Z.t           (** Raw Value *)
  | TInvalid              (** Invalid/Fault *)

(** Allocation constraints (Equality, Inequality) *)
type constr =
  | Eq of expr * expr
  | Neq of expr * expr

(** Top-level statements (Definitions, Mappings, Initializations) *)
type stmt =
  | Decl of string * string list  (** Define symbols *)
  | OptionDef of string * string  (** Global options *)
  | TableDef of {
      name: string;
      addr: string;
      body: stmt list
    } (** Define Page Table *)
  | Mapping of {
      va: string;
      target: target_expr;
      variant: bool;
      level: int option;
      alias: string option
    } (** Map VA to Target *)
  | Identity of string * bool   (** Identity Map *)
  | MemInit of string * string  (** Initialize Memory *)
  | Assert of constr            (** Enforce Constraint *)
