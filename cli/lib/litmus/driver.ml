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

(** Drive an operational model from OCaml.

    This is the OCaml counterpart of [TermModels.opModel.run] in
    [ArchSem/TermModels.v]: instead of letting Rocq run the model, the
    transition tree is explored here, which gives OCaml access to every
    individual step. *)

module Make (A : Archsem.Arch) (M : A.OpModel.S) = struct
  (** Explore the model exhaustively and return all the final states, as well as
      the errors of the branches that failed or ran out of fuel.

      The exploration uses an explicit stack instead of the native one, so that
      all the calls to [M.step] happen at the same native stack depth, which
      merges the exploration paths when profiling. *)
  let model ?(config = M.default_config) isem fuel term initSt =
    let m = M.make config isem ~nth:(A.ArchState.num_thread initSt) in
    (* [finals] and [errors] are accumulated in reverse order *)
    let rec loop finals errors = function
      | [] -> (finals, errors)
      | (_, 0) :: rest -> loop finals ("Out of fuel" :: errors) rest
      | (st, fuel) :: rest ->
          let {A.OpModel.next; finals = fs; errors = errs} =
            M.step m term initSt ~fuel st
          in
          let finals = List.fold_left (fun acc (_, f) -> f :: acc) finals fs in
          let errors = List.fold_left (fun acc (_, e) -> e :: acc) errors errs in
          let rest =
            List.fold_left (fun acc st -> (st, fuel - 1) :: acc) rest next
          in
          loop finals errors rest
    in
    let (finals, errors) = loop [] [] [(M.init m term initSt, fuel)] in
    List.rev_map (fun fs -> A.ArchModel.Res.FinalState fs) finals
    @ List.rev_map (fun e -> A.ArchModel.Res.Error e) errors
end
