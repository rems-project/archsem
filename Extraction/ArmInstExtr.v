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

Require Import ASCommon.CExtraction.
From ArchSemArm Require Import ArmInst UMPromising VMPromising.

Unset Extraction SafeImplicits.

Extract Inductive ArchSem.Interface.reg_gen_val =>
  "Reggenval.gen"
  ["Reggenval.Number" "Reggenval.String" "Reggenval.Array" "Reggenval.Struct"].

(** Debug trace functions for translation debugging.
    Uses a global flag in Support module to control output.
    Each returns its first argument to prevent extraction optimization. *)

(* Trace memory/view state before translation *)
Extract Constant VMPromising.debug_trace_trans_state =>
  "(fun vmax_t vpre_t va ->
     (if !Support.debug_trace_enabled then
       Printf.eprintf ""[DEBUG:State] VA=0x%Lx mem_len=%d vpre=%d\n%!""
         (Z.to_int64 va) (Z.to_int vmax_t) (Z.to_int vpre_t));
     vmax_t)".

(* Trace snapshot filtering *)
Extract Constant VMPromising.debug_trace_snapshot_filter =>
  "(fun before after va ->
     (if !Support.debug_trace_enabled then
       Printf.eprintf ""[DEBUG:Filter] VA=0x%Lx snapshots: %d -> %d (after vpre filter)\n%!""
         (Z.to_int64 va) (Z.to_int before) (Z.to_int after));
     before)".

(* Trace snapshot/entry counts *)
Extract Constant VMPromising.debug_trace_translation =>
  "(fun num_snapshots num_valid num_invalid va ->
     (if !Support.debug_trace_enabled then
       Printf.eprintf ""[DEBUG:Trans] VA=0x%Lx snapshots=%d valid=%d invalid=%d\n%!""
         (Z.to_int64 va) (Z.to_int num_snapshots) (Z.to_int num_valid) (Z.to_int num_invalid));
     num_snapshots)".

(* Trace chosen translation result *)
Extract Constant VMPromising.debug_trace_trans_choice =>
  "(fun is_valid trans_time inv_time_opt va ->
     (if !Support.debug_trace_enabled then
       let inv_str = match inv_time_opt with
         | Some t -> Printf.sprintf ""inv_time=%d"" (Z.to_int t)
         | None -> ""inv_time=none""
       in
       Printf.eprintf ""[DEBUG:Choice] VA=0x%Lx %s trans_time=%d %s\n%!""
         (Z.to_int64 va)
         (if Z.to_int is_valid = 1 then ""VALID"" else ""INVALID"")
         (Z.to_int trans_time) inv_str);
     is_valid)".

(* Trace individual valid entry: trans_time (returned), trans_time, inv_time_opt, va *)
Extract Constant VMPromising.debug_trace_valid_entry =>
  "(fun _ret trans_time inv_time_opt va ->
     (if !Support.debug_trace_enabled then
       let inv_str = match inv_time_opt with
         | Some t -> Printf.sprintf ""inv=%d"" (Z.to_int t)
         | None -> ""inv=none""
       in
       Printf.eprintf ""  [ValidEntry] VA=0x%Lx time=%d %s\n%!""
         (Z.to_int64 va) (Z.to_int trans_time) inv_str);
     _ret)".

(* Trace individual invalid entry: trans_time (returned), trans_time, inv_time_opt, va *)
Extract Constant VMPromising.debug_trace_invalid_entry =>
  "(fun _ret trans_time inv_time_opt va ->
     (if !Support.debug_trace_enabled then
       let inv_str = match inv_time_opt with
         | Some t -> Printf.sprintf ""inv=%d"" (Z.to_int t)
         | None -> ""inv=none""
       in
       Printf.eprintf ""  [InvalidEntry] VA=0x%Lx time=%d %s\n%!""
         (Z.to_int64 va) (Z.to_int trans_time) inv_str);
     _ret)".

(* DO NOT run this file in your editor. This will extract in the correct folder
   when dune does the extraction *)
Set Extraction Output Directory ".".

(* Definition umProm_cert_c := UMPromising_cert_c. *)

#[warnings="-extraction-remaining-implicit,-extraction-reserved-identifier"]
Separate Extraction Arm sail_tiny_arm_sem
  sequential_modelc UMPromising_cert_c VMPromising_cert_c
  UMPromising_cert_c_pf VMPromising_cert_c_pf.
