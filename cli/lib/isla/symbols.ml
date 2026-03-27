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

(** Immutable symbol table with bump allocation. *)

type t =
  { mutable next_addr : int;
    mutable table : (string * int) list
  }

let resolve_opt t name = List.assoc_opt name t.table

let resolve t name =
  match List.assoc_opt name t.table with
  | Some sym -> sym
  | None -> failwith ("Unknown symbol: " ^ name)

let page_bits () =
  let bits =
    Otoml.find (Litmus.Config.get ()) Otoml.get_integer ["isla"; "page_bits"]
  in
  if bits < 0 then failwith "config: [isla] page_bits must be non-negative";
  bits

let page_size () = 1 lsl page_bits ()

let base_addr () =
  Otoml.find_or ~default:0x500 (Litmus.Config.get ()) Otoml.get_integer
    ["isla"; "symbols"; "base_address"]

let empty () = {next_addr = base_addr (); table = []}

let alloc_page t =
  let page_size = page_size () in
  let addr = t.next_addr in
  t.next_addr <- addr + page_size;
  addr

let alloc_sym t name =
  match resolve_opt t name with
  | Some _ -> ()
  | None ->
      let addr = alloc_page t in
      t.table <- (name, addr) :: t.table;
      ()

let resolve_or_alloc t name =
  match resolve_opt t name with
  | Some addr -> addr
  | None ->
      let addr = alloc_page t in
      t.table <- (name, addr) :: t.table;
      addr
