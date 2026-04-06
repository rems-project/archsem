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

(** Bitvector functions: bvand, bvor, bvxor, bvshl, bvlshr, extz, exts. *)

let functions : (string * Fn_registry.fn_spec) list =
  [ ( "bvand",
      { params = ["a"; "b"];
        eval =
          (fun _ -> function
             | [a; b] -> Z.logand a b | _ -> Fn_registry.arity_error "bvand" 2
             )
      }
    );
    ( "bvor",
      { params = ["a"; "b"];
        eval =
          (fun _ -> function
             | [a; b] -> Z.logor a b | _ -> Fn_registry.arity_error "bvor" 2
             )
      }
    );
    ( "bvxor",
      { params = ["a"; "b"];
        eval =
          (fun _ -> function
             | [a; b] -> Z.logxor a b | _ -> Fn_registry.arity_error "bvxor" 2
             )
      }
    );
    ( "bvshl",
      { params = ["a"; "b"];
        eval =
          (fun _ -> function
             | [a; b] -> Z.shift_left a (Z.to_int b)
             | _ -> Fn_registry.arity_error "bvshl" 2
             )
      }
    );
    ( "bvlshr",
      { params = ["a"; "b"];
        eval =
          (fun _ -> function
             | [a; b] -> Z.shift_right a (Z.to_int b)
             | _ -> Fn_registry.arity_error "bvlshr" 2
             )
      }
    );
    ( "extz",
      { params = ["bits"; "len"];
        eval =
          (fun _ -> function
             | [bits; _len] -> bits | _ -> Fn_registry.arity_error "extz" 2
             )
      }
    );
    ( "exts",
      { params = ["bits"; "len"];
        eval =
          (fun _ -> function
             | [bits; len] -> Z.signed_extract bits 0 (Z.to_int len)
             | _ -> Fn_registry.arity_error "exts" 2
             )
      }
    )
  ]
