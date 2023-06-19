Require Import Strings.String.
Require Import stdpp.unstable.bitvector.

(* This is needed because sail cannot export into multiple Coq files *)
Require Import SailArmInstTypes.
Require Import Interface.

Local Open Scope stdpp_scope.
Local Open Scope Z_scope.


Module Deps (Arch : Arch) (IA : InterfaceT Arch). (* to be imported *)
  Import Arch.
  Import IA.

  Module DepOn.
    Record t :=
      make
        {
          (** The list of registers the effect depends on. *)
          regs : list reg;
          (** The list of memory access the effect depends on. The number
              corresponds to the memory reads done by the instruction in the
              order specified by the instruction semantics. The indexing starts
              at 0. *)
          mem_reads : list N
        }.
  End DepOn.

End Deps.

Module Type DepsT (A : Arch) (IA : InterfaceT A).
  Include Deps A IA.
End DepsT.

(* DepOn *)

(* Full Footprint type *)

(* Conversion boilerplate code *)
