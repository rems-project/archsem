(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Zongyuan Liu, Aarhus University                                       *)
(*      Nils Lauermann, University of Cambridge                               *)
(*      Jean Pichon-Pharabod, University of Cambridge, Aarhus University      *)
(*      Brian Campbell, University of Edinburgh                               *)
(*      Alasdair Armstrong, University of Cambridge                           *)
(*      Ben Simner, University of Cambridge                                   *)
(*      Peter Sewell, University of Cambridge                                 *)
(*                                                                            *)
(*  Redistribution and use in source and binary forms, with or without        *)
(*  modification, are permitted provided that the following conditions        *)
(*  are met:                                                                  *)
(*                                                                            *)
(*   1. Redistributions of source code must retain the above copyright        *)
(*      notice, this list of conditions and the following disclaimer.         *)
(*                                                                            *)
(*   2. Redistributions in binary form must reproduce the above copyright     *)
(*      notice, this list of conditions and the following disclaimer in the   *)
(*      documentation and/or other materials provided with the distribution.  *)
(*                                                                            *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS       *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT         *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS         *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE            *)
(*  COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,      *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,      *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS     *)
(*  OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND    *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR     *)
(*  TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE    *)
(*  USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.  *)
(*                                                                            *)
(******************************************************************************)

(** Abstract archsem test representation.

    Uses plain OCaml types (string for register names, RegValGen.t for values)
    to remain architecture-neutral.  Conversion to arch-specific Coq types
    happens in ToArchState.Make(Arch). *)

(** {1 Memory Types} *)

type memory_kind =
  | Code
  | Data
  | PageTable

let memory_kind_of_string = function
  | "code" -> Code
  | "pagetable" -> PageTable
  | _ -> Data

let string_of_memory_kind = function
  | Code -> "code"
  | Data -> "data"
  | PageTable -> "pagetable"

type memory_block =
  { addr : int;
    step : int;
    data : Bytes.t;
    sym : string option;
    kind : memory_kind
  }

(** {1 Outcome Types} *)

type reg_requirement =
  | ReqEq of Archsem.RegValGen.t
  | ReqNe of Archsem.RegValGen.t

type mem_requirement =
  | MemEq of Z.t
  | MemNe of Z.t

type thread_cond = int * (string * reg_requirement) list

type mem_cond =
  { sym : string;
    addr : int;
    size : int;
    req : mem_requirement
  }

type final_cond =
  | Observable of thread_cond list * mem_cond list
  | Unobservable of thread_cond list * mem_cond list

(** {1 Test} *)

type t =
  { arch : string;
    name : string;
    registers : (string * Archsem.RegValGen.t) list list;
    memory : memory_block list;
    term_cond : (string * Archsem.RegValGen.t) list list;
    finals : final_cond list
  }

(** {1 Helper functions} *)

let block_size (mb : memory_block) : int = Bytes.length mb.data

let mem_by_sym (sym : string) =
  List.find (fun (mb : memory_block) -> mb.sym = Some sym)

(* Convert memory address to corresponding symbol. Returns "?" if symbol is None. *)
let mem_addr_to_symbol (addr : int) (mem_blocks : memory_block list) : string =
  let mem_block =
    List.find (fun (mb : memory_block) -> mb.addr = addr) mem_blocks
  in
  match mem_block.sym with Some symbol -> symbol | None -> "?"
