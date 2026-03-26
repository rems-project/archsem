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

module RegValGen = RegValGen
module Utils = Utils

module type Arch = Arch.Arch

type empty = Utils.empty

module Arm = struct
  module Required = struct
    module Arch = ArmInst.Arch
    include ArmInst.Arm

    let default_address_space = System_types.PAS_NonSecure
  end

  include ArchBuild.Build (Required)

  let tiny_isa = ArmInst.sail_tiny_arm_sem true

  let termCond_to_coq (term : termCond) tid rm =
    let tc = List.nth term (Z.to_int tid) in
    tc rm

  let umProm_model isem fuel term initState =
    UMPromising.coq_UMPromising_pf isem (Z.of_int fuel)
      (ArchState.num_thread initState |> Z.of_int)
      (termCond_to_coq term) initState
    |> Obj.magic

  module BBM = VMPromising.BBM

  let vmProm_model ?(bbm_param = BBM.Off) isem fuel term initState =
    VMPromising.coq_VMPromising_pf bbm_param isem (Z.of_int fuel)
      (ArchState.num_thread initState |> Z.of_int)
      (termCond_to_coq term) initState
    |> Obj.magic
end

module X86 = struct
  module Required = struct
    module Arch = X86Inst.Arch
    include X86Inst.X86

    let default_address_space = ()
  end

  include ArchBuild.Build (Required)

  let tiny_isa = X86Inst.sail_tiny_x86_sem true

  let termCond_to_coq (term : termCond) tid rm =
    let tc = List.nth term (Z.to_int tid) in
    tc rm

  let op_model ?(allow_eager = true) isem fuel term initState =
    OperationalX86TSO.x86_operational_modelc (Z.of_int fuel) isem allow_eager
      (ArchState.num_thread initState |> Z.of_int)
      (termCond_to_coq term) initState
    |> Obj.magic
end
