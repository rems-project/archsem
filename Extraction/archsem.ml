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

  module UMProm = OpModel.Of_coq (struct
      type config = unit

      let default_config = ()

      let opmodel () isem ~nth =
        UMPromising.coq_UMPromising_opmodel_pf isem (Z.of_int nth)
    end)

  module VMProm = OpModel.Of_coq (struct
      type config = bool

      let default_config = false

      let opmodel bbm isem ~nth =
        VMPromising.coq_VMPromising_opmodel_pf bbm isem (Z.of_int nth)
    end)
end

module X86 = struct
  module Required = struct
    module Arch = X86Inst.Arch
    include X86Inst.X86

    let default_address_space = ()
  end

  include ArchBuild.Build (Required)

  let tiny_isa = X86Inst.sail_tiny_x86_sem true

  module Tso = OpModel.Of_coq (struct
      (** Whether eager transitions are allowed *)
      type config = bool

      let default_config = true

      let opmodel allow_eager isem ~nth =
        let nth = Z.of_int nth in
        if allow_eager then OperationalX86TSO.x86_tso_opmodel_eager nth isem
        else OperationalX86TSO.x86_tso_opmodel nth isem
    end)
end
