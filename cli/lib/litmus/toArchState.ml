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

(** Convert a Testrepr.t into the Rocq types (ArchState.t, MemMap.t, etc.).

    Parameterized by architecture via the Make functor. *)

module Make (Arch : Archsem.Arch) = struct
  open Arch

  let insert_memory_block mm (block : Testrepr.memory_block) =
    MemMap.insertb block.addr block.data mm

  let regmap_of_gen_list reg_list =
    List.fold_left
      (fun rm (name, gen) -> RegMap.insert (RegVal.of_string_gen name gen) rm)
      RegMap.empty reg_list

  let regmaps_of_testrepr registers = List.map regmap_of_gen_list registers

  let memory_of_testrepr memory =
    List.fold_left insert_memory_block MemMap.empty memory

  let term_cond_of_gen_list reqs =
    let parsed =
      List.map (fun (name, gen) -> RegVal.of_string_gen name gen) reqs
    in
    fun rm ->
      List.for_all
        (fun rv ->
           let reg = RegVal.reg rv in
           match RegMap.get_opt reg rm with
           | Some actual -> rv = actual
           | None ->
               failwith
                 ("[[termCond]] register not found in thread state: "
                ^ Reg.to_string reg
                 )
         )
        parsed

  let term_conds_of_testrepr term_cond = List.map term_cond_of_gen_list term_cond

  let validate_thread_count regs term =
    let num_threads = List.length regs in
    if List.length term <> num_threads then
      failwith
        (Printf.sprintf
           "[[termCond]] count (%d) must match [[registers]] thread count (%d)"
           (List.length term) num_threads
        )

  (** Convert Testrepr.t into ArchState.t and termination conditions. *)
  let testrepr_to_archstate (test : Testrepr.t) =
    let regs = regmaps_of_testrepr test.registers in
    let mem = memory_of_testrepr test.memory in
    let init = ArchState.make regs mem in
    let term = term_conds_of_testrepr test.term_cond in
    validate_thread_count regs term;
    (init, term)
end
