(******************************************************************************)
(*                                ArchSem                                     *)
(*                                                                            *)
(*  Copyright (c) 2021                                                        *)
(*      Thibaut Pérami, University of Cambridge                               *)
(*      Yeji Han, Seoul National University                                   *)
(*      Shreeka Lohani, University of Cambridge                               *)
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

(** Build and query concrete AArch64 page-table layouts.

    This module owns PA allocation, descriptor construction, and layout
    interpretation for page-table setup. *)

type va = int

type pa = int

type descriptor = int64

type data_value = Z.t

type layout =
  { root : pa;
    (* Base VA of the 2MB window that maps the page-table pool. *)
    va_base : va;
    table_entries : (pa * descriptor) list;
    (* Mapping from PA-side symbols to concrete PAs: pa_x -> PA. *)
    symbols_pa : (string * pa) list;
    (* PA-side data symbols, excluding generated root aliases. *)
    phys_symbols_pa : (string * pa) list;
    (* [*pa = value] initialisers resolved to concrete PAs. *)
    data_inits : (pa * data_value) list
  }

exception Error of string

(** Build a concrete page-table layout from parsed setup. *)
val build :
   arch:Litmus.Arch_id.t ->
  allocator:Allocator.t ->
  (* Maps VA-side symbol names to concrete VAs for explicit mappings *)
  symbolic_vas:(string * va) list ->
  (* Lists built-in thread code pages that should get identity mappings *)
  code_pages:va list ->
  (* Parsed [page_table_setup] statement list *)
  Page_table_ast.stmt list ->
  layout

(** Translate [va] through a layout, returning [None] when no mapping exists.
    Raises [Error msg] when a present descriptor is invalid. *)
val translate_va_to_pa : layout -> va -> pa option
