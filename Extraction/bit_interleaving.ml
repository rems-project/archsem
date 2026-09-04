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

(** Bit interleaving library for encoding pair of integers *)

(** I don't care about 32 bits systems *)
let () = assert (Sys.int_size = 63)

(** Spread the low 32 bits of [x]: bit i of the input becomes bit 2*i of the
    result (odd-indexed result bits are 0). The high 32 bits of [x] do
    not appear in the output.*)
let spread (x : int) : int =
  let x = x land 0x00000000FFFFFFFF in
  let x = x lor (x lsl 16) land 0x0000FFFF0000FFFF in
  let x = x lor (x lsl 8) land 0x00FF00FF00FF00FF in
  let x = x lor (x lsl 4) land 0x0F0F0F0F0F0F0F0F in
  let x = x lor (x lsl 2) land 0x3333333333333333 in
  let x = x lor (x lsl 1) land 0x5555555555555555 in
  x

(** Spread the low 16 bits of [x]: bit i of the input becomes bit 2*i of the
    result (odd-indexed result bits are 0). The high 48 bits of [x] do
    not appear in the output.*)
let spread32 (x : int) : int =
  let x = x land 0x0000FFFF in
  let x = x lor (x lsl 8) land 0x00FF00FF in
  let x = x lor (x lsl 4) land 0x0F0F0F0F in
  let x = x lor (x lsl 2) land 0x33333333 in
  let x = x lor (x lsl 1) land 0x55555555 in
  x

(** Inverse of [spread]: gather bits 0,2,4,...,62 of [x] into the low
    32 bits of the result. *)
let compress (x : int) : int =
  let x = x land 0x5555555555555555 in
  let x = x lor (x lsr 1) land 0x3333333333333333 in
  let x = x lor (x lsr 2) land 0x0F0F0F0F0F0F0F0F in
  let x = x lor (x lsr 4) land 0x00FF00FF00FF00FF in
  let x = x lor (x lsr 8) land 0x0000FFFF0000FFFF in
  let x = x lor (x lsr 16) land 0x00000000FFFFFFFF in
  x

(** Inverse of [spread32]: gather bits 0,2,4,...,30 of [x] into the low
    16 bits of the result. *)
let compress32 (x : int) : int =
  let x = x land 0x55555555 in
  let x = x lor (x lsr 1) land 0x33333333 in
  let x = x lor (x lsr 2) land 0x0F0F0F0F in
  let x = x lor (x lsr 4) land 0x00FF00FF in
  let x = x lor (x lsr 8) land 0x0000FFFF in
  x

(** Fast path for small integers *)
module Fast = struct
  (* p, q assumed to have Z.numbits <= 31 *)
  let encode (p : Z.t) (q : Z.t) : Z.t =
    let p = Z.to_int p and q = Z.to_int q in
    let r = spread p lor (spread q lsl 1) in
    Z.of_int r

  (* c assumed to have Z.numbits <= 62 *)
  let decode (c : Z.t) : Z.t * Z.t =
    let c = Z.to_int c in
    (Z.of_int (compress c), Z.of_int (compress (c lsr 1)))
end

(** Slow path for large integers *)
module Generic = struct
  let encode (p : Z.t) (q : Z.t) : Z.t =
    let bp = Z.to_bits p and bq = Z.to_bits q in
    assert (String.length bp mod 8 == 0 && String.length bq mod 8 == 0);
    let get_uint16_le s i =
      if i >= String.length s then 0 else String.get_uint16_le s i
    in
    let nwords = max (String.length bp) (String.length bq) / 2 in
    let buf = Bytes.create (nwords * 4) in
    for i = 0 to nwords - 1 do
      let wp = get_uint16_le bp (2 * i) and wq = get_uint16_le bq (2 * i) in
      let r = spread32 wp lor (spread32 wq lsl 1) in
      Bytes.set_int32_le buf (4 * i) (Int32.of_int r)
    done;
    Z.of_bits (Bytes.unsafe_to_string buf)

  let decode (code : Z.t) : Z.t * Z.t =
    let bc = Z.to_bits code in
    assert (String.length bc mod 8 == 0);
    let nwords = String.length bc / 4 in
    let p = Bytes.create (nwords * 2) and q = Bytes.create (nwords * 2) in
    for i = 0 to nwords - 1 do
      let w = String.get_int32_le bc (4 * i) |> Int32.to_int in
      Bytes.set_uint16_le p (2 * i) (compress32 w);
      Bytes.set_uint16_le q (2 * i) (compress32 (w lsr 1))
    done;
    (Z.of_bits (Bytes.unsafe_to_string p), Z.of_bits (Bytes.unsafe_to_string q))
end

(** Encode two number into one, assuming they are non-negative *)
let encode (p : Z.t) (q : Z.t) : Z.t =
  if Z.numbits p <= 31 && Z.numbits q <= 31 then Fast.encode p q
  else Generic.encode p q

(** The opposite of [encode], assumes the input is non-negative *)
let decode (c : Z.t) : Z.t * Z.t =
  if Z.numbits c <= 62 then Fast.decode c else Generic.decode c
