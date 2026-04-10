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

(** Helper functions for checking final states *)

module Make (Arch : Archsem.Arch) = struct
  open Arch

  (* Check if a final state satisfies cond (register conditions) *)
  let check_outcome (fs : ArchState.t) (cond : Testrepr.thread_cond list) : bool =
    List.for_all
      (fun (tid, reqs) ->
         let regs = ArchState.reg tid fs in
         List.for_all
           (fun (name, req) ->
              let reg = Reg.of_string name in
              match RegMap.get_opt reg regs with
              | None ->
                  failwith
                    ("[[outcome]] register not found in final state: " ^ name)
              | Some rv -> (
                match req with
                | Testrepr.ReqEq exp -> rv = RegVal.of_gen reg exp
                | Testrepr.ReqNe exp -> rv = RegVal.of_gen reg exp
              )
            )
           reqs
       )
      cond

  (* Check if a final state satisfies mem_conds *)
  let check_mem_outcome (fs : ArchState.t) (mem_conds : Testrepr.mem_cond list) :
    bool
    =
    let mem = ArchState.mem fs in
    List.for_all
      (fun (mc : Testrepr.mem_cond) ->
         match MemMap.lookup_opt mc.addr mc.size mem with
         | None ->
             failwith
               (Printf.sprintf "[[outcome]] memory not found at 0x%x" mc.addr)
         | Some actual -> (
           match mc.req with
           | Testrepr.MemEq expected -> Z.equal actual expected
           | Testrepr.MemNe expected -> not (Z.equal actual expected)
         )
       )
      mem_conds
end
