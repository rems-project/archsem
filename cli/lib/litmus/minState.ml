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

(** Convert an ArchState.t into a (reg_state list * mem_state list), and related functions
*)

type reg_state =
  { tid : int;
    regname : string;
    value : int
  }

type mem_state =
  { sym : string;
    addr : int;
    size : int;
    value : int
  }

module Make (Arch : Archsem.Arch) = struct
  open Arch

  (* Convert a collection of register conditions (each having a thread id and a register name)
  into a list of thread-regname pairs *)
  let get_thread_regname_pairs (reg_cond : Testrepr.thread_cond list) :
    (int * string) list
    =
    List.concat_map
      (fun (thread, reg_pair) ->
         List.map (fun (name, _) -> (thread, name)) reg_pair
       )
      reg_cond

  (* Compare the memory symbol of 2 memory conditions *)
  let compare_mem_sym
        (mem_cond_1 : Testrepr.mem_cond)
        (mem_cond_2 : Testrepr.mem_cond)
    =
    String.compare mem_cond_1.sym mem_cond_2.sym

  (* From the test conditions, get a list of all unique thread-register pairs, 
    and a list of all unique memory symbols *)
  let get_unique_conds_ignoring_value
        (conds : (Testrepr.thread_cond list * Testrepr.mem_cond list) list) :
    (int * string) list * Testrepr.mem_cond list
    =
    let (reg_conds, mem_conds) = List.split conds in
    let all_reg_conds = get_thread_regname_pairs (List.flatten reg_conds) in
    ( List.sort_uniq compare all_reg_conds,
      List.sort_uniq compare_mem_sym (List.flatten mem_conds)
    )

  (* From a final state, extract the registers (and values) that the register conditions check *)
  let minimise_reg_state (reg_conds : (int * string) list) (state : ArchState.t) :
    reg_state list
    =
    List.map
      (fun (tid, regname) ->
         let regs = ArchState.reg tid state in
         let value = RegMap.geti (Reg.of_string regname) regs in
         {tid; regname; value}
       )
      reg_conds

  (* From a final state, extract the memory locations (and values) that the memory conditions check *)
  let minimise_mem_state (mem_conds : Testrepr.mem_cond list) (state : ArchState.t)
    : mem_state list
    =
    let mem = ArchState.mem state in
    List.map
      (fun (mc : Testrepr.mem_cond) ->
         let value = MemMap.lookupi mc.addr mc.size mem in
         {sym = mc.sym; addr = mc.addr; size = mc.size; value}
       )
      mem_conds

  (* For a list of final states, for each final state, 
    extract the registers and memory locations that the conditions check
    (with the final values of these locations) *)
  let minimise_states
        ((reg_conds, mem_conds) : (int * string) list * Testrepr.mem_cond list)
        (states : ArchState.t list) : (reg_state list * mem_state list) list
    =
    List.map
      (fun state ->
         (minimise_reg_state reg_conds state, minimise_mem_state mem_conds state)
       )
      states

  (* Find all the registers and memory locations that the conditions check,
    extract only those locations from each final state, and deduplicate them *)
  let get_unique_minimised_states
        (conds : (Testrepr.thread_cond list * Testrepr.mem_cond list) list)
        (final_states : ArchState.t list) : (reg_state list * mem_state list) list
    =
    let unique_cond = get_unique_conds_ignoring_value conds in
    let minimised_fs = minimise_states unique_cond final_states in
    List.sort_uniq compare minimised_fs
end
