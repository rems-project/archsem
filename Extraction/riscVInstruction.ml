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

(** OCaml representation of sail-riscv's [rv64d_types.instruction].

    That inductive has 361 non-constant constructors, more than OCaml allows in
    a single variant type (246), so it cannot be extracted as a normal variant.
    Instead it is extracted (see [ArmInstExtr.v]) to a pair of the constructor
    index (in declaration order) and its untyped argument. The [Obj] casts are
    sound because Rocq extraction only ever builds values through [mk] with the
    right index and only destructs them through [match_].

    This file is generated from the constructor list: if the sail-riscv version
    changes the instruction type, it needs to be regenerated together with the
    [Extract Inductive] directive in [ArmInstExtr.v]. *)

type t = int * Obj.t

let mk (tag : int) (x : 'a) : t = (tag, Obj.repr x)

let match_
      f0
      f1
      f2
      f3
      f4
      f5
      f6
      f7
      f8
      f9
      f10
      f11
      f12
      f13
      f14
      f15
      f16
      f17
      f18
      f19
      f20
      f21
      f22
      f23
      f24
      f25
      f26
      f27
      f28
      f29
      f30
      f31
      f32
      f33
      f34
      f35
      f36
      f37
      f38
      f39
      f40
      f41
      f42
      f43
      f44
      f45
      f46
      f47
      f48
      f49
      f50
      f51
      f52
      f53
      f54
      f55
      f56
      f57
      f58
      f59
      f60
      f61
      f62
      f63
      f64
      f65
      f66
      f67
      f68
      f69
      f70
      f71
      f72
      f73
      f74
      f75
      f76
      f77
      f78
      f79
      f80
      f81
      f82
      f83
      f84
      f85
      f86
      f87
      f88
      f89
      f90
      f91
      f92
      f93
      f94
      f95
      f96
      f97
      f98
      f99
      f100
      f101
      f102
      f103
      f104
      f105
      f106
      f107
      f108
      f109
      f110
      f111
      f112
      f113
      f114
      f115
      f116
      f117
      f118
      f119
      f120
      f121
      f122
      f123
      f124
      f125
      f126
      f127
      f128
      f129
      f130
      f131
      f132
      f133
      f134
      f135
      f136
      f137
      f138
      f139
      f140
      f141
      f142
      f143
      f144
      f145
      f146
      f147
      f148
      f149
      f150
      f151
      f152
      f153
      f154
      f155
      f156
      f157
      f158
      f159
      f160
      f161
      f162
      f163
      f164
      f165
      f166
      f167
      f168
      f169
      f170
      f171
      f172
      f173
      f174
      f175
      f176
      f177
      f178
      f179
      f180
      f181
      f182
      f183
      f184
      f185
      f186
      f187
      f188
      f189
      f190
      f191
      f192
      f193
      f194
      f195
      f196
      f197
      f198
      f199
      f200
      f201
      f202
      f203
      f204
      f205
      f206
      f207
      f208
      f209
      f210
      f211
      f212
      f213
      f214
      f215
      f216
      f217
      f218
      f219
      f220
      f221
      f222
      f223
      f224
      f225
      f226
      f227
      f228
      f229
      f230
      f231
      f232
      f233
      f234
      f235
      f236
      f237
      f238
      f239
      f240
      f241
      f242
      f243
      f244
      f245
      f246
      f247
      f248
      f249
      f250
      f251
      f252
      f253
      f254
      f255
      f256
      f257
      f258
      f259
      f260
      f261
      f262
      f263
      f264
      f265
      f266
      f267
      f268
      f269
      f270
      f271
      f272
      f273
      f274
      f275
      f276
      f277
      f278
      f279
      f280
      f281
      f282
      f283
      f284
      f285
      f286
      f287
      f288
      f289
      f290
      f291
      f292
      f293
      f294
      f295
      f296
      f297
      f298
      f299
      f300
      f301
      f302
      f303
      f304
      f305
      f306
      f307
      f308
      f309
      f310
      f311
      f312
      f313
      f314
      f315
      f316
      f317
      f318
      f319
      f320
      f321
      f322
      f323
      f324
      f325
      f326
      f327
      f328
      f329
      f330
      f331
      f332
      f333
      f334
      f335
      f336
      f337
      f338
      f339
      f340
      f341
      f342
      f343
      f344
      f345
      f346
      f347
      f348
      f349
      f350
      f351
      f352
      f353
      f354
      f355
      f356
      f357
      f358
      f359
      f360
      ((tag, x) : t)
  =
  match tag with
  | 0 -> f0 (Obj.obj x) (* ILLEGAL *)
  | 1 -> f1 (Obj.obj x) (* C_ILLEGAL *)
  | 2 -> f2 (Obj.obj x) (* ZICBOP *)
  | 3 -> f3 (Obj.obj x) (* NTL *)
  | 4 -> f4 (Obj.obj x) (* C_NTL *)
  | 5 -> f5 (Obj.obj x) (* PAUSE *)
  | 6 -> f6 (Obj.obj x) (* LPAD *)
  | 7 -> f7 (Obj.obj x) (* UTYPE *)
  | 8 -> f8 (Obj.obj x) (* JAL *)
  | 9 -> f9 (Obj.obj x) (* JALR *)
  | 10 -> f10 (Obj.obj x) (* BTYPE *)
  | 11 -> f11 (Obj.obj x) (* ITYPE *)
  | 12 -> f12 (Obj.obj x) (* SHIFTIOP *)
  | 13 -> f13 (Obj.obj x) (* RTYPE *)
  | 14 -> f14 (Obj.obj x) (* LOAD *)
  | 15 -> f15 (Obj.obj x) (* STORE *)
  | 16 -> f16 (Obj.obj x) (* ADDIW *)
  | 17 -> f17 (Obj.obj x) (* RTYPEW *)
  | 18 -> f18 (Obj.obj x) (* SHIFTIWOP *)
  | 19 -> f19 (Obj.obj x) (* FENCE_TSO *)
  | 20 -> f20 (Obj.obj x) (* FENCE *)
  | 21 -> f21 (Obj.obj x) (* ECALL *)
  | 22 -> f22 (Obj.obj x) (* MRET *)
  | 23 -> f23 (Obj.obj x) (* SRET *)
  | 24 -> f24 (Obj.obj x) (* EBREAK *)
  | 25 -> f25 (Obj.obj x) (* WFI *)
  | 26 -> f26 (Obj.obj x) (* SFENCE_VMA *)
  | 27 -> f27 (Obj.obj x) (* AMO *)
  | 28 -> f28 (Obj.obj x) (* LOADRES *)
  | 29 -> f29 (Obj.obj x) (* STORECON *)
  | 30 -> f30 (Obj.obj x) (* MUL *)
  | 31 -> f31 (Obj.obj x) (* DIV *)
  | 32 -> f32 (Obj.obj x) (* REM *)
  | 33 -> f33 (Obj.obj x) (* MULW *)
  | 34 -> f34 (Obj.obj x) (* DIVW *)
  | 35 -> f35 (Obj.obj x) (* REMW *)
  | 36 -> f36 (Obj.obj x) (* SLLIUW *)
  | 37 -> f37 (Obj.obj x) (* ZBA_RTYPEUW *)
  | 38 -> f38 (Obj.obj x) (* ZBA_RTYPE *)
  | 39 -> f39 (Obj.obj x) (* RORIW *)
  | 40 -> f40 (Obj.obj x) (* RORI *)
  | 41 -> f41 (Obj.obj x) (* ZBB_RTYPEW *)
  | 42 -> f42 (Obj.obj x) (* ZBB_RTYPE *)
  | 43 -> f43 (Obj.obj x) (* ZBB_EXTOP *)
  | 44 -> f44 (Obj.obj x) (* REV8 *)
  | 45 -> f45 (Obj.obj x) (* ORCB *)
  | 46 -> f46 (Obj.obj x) (* CPOP *)
  | 47 -> f47 (Obj.obj x) (* CPOPW *)
  | 48 -> f48 (Obj.obj x) (* CLZ *)
  | 49 -> f49 (Obj.obj x) (* CLZW *)
  | 50 -> f50 (Obj.obj x) (* CTZ *)
  | 51 -> f51 (Obj.obj x) (* CTZW *)
  | 52 -> f52 (Obj.obj x) (* CLMUL *)
  | 53 -> f53 (Obj.obj x) (* CLMULH *)
  | 54 -> f54 (Obj.obj x) (* CLMULR *)
  | 55 -> f55 (Obj.obj x) (* ZBS_IOP *)
  | 56 -> f56 (Obj.obj x) (* ZBS_RTYPE *)
  | 57 -> f57 (Obj.obj x) (* C_NOP *)
  | 58 -> f58 (Obj.obj x) (* C_ADDI4SPN *)
  | 59 -> f59 (Obj.obj x) (* C_LW *)
  | 60 -> f60 (Obj.obj x) (* C_LD *)
  | 61 -> f61 (Obj.obj x) (* C_SW *)
  | 62 -> f62 (Obj.obj x) (* C_SD *)
  | 63 -> f63 (Obj.obj x) (* C_ADDI *)
  | 64 -> f64 (Obj.obj x) (* C_JAL *)
  | 65 -> f65 (Obj.obj x) (* C_ADDIW *)
  | 66 -> f66 (Obj.obj x) (* C_LI *)
  | 67 -> f67 (Obj.obj x) (* C_ADDI16SP *)
  | 68 -> f68 (Obj.obj x) (* C_LUI *)
  | 69 -> f69 (Obj.obj x) (* C_SRLI *)
  | 70 -> f70 (Obj.obj x) (* C_SRAI *)
  | 71 -> f71 (Obj.obj x) (* C_ANDI *)
  | 72 -> f72 (Obj.obj x) (* C_SUB *)
  | 73 -> f73 (Obj.obj x) (* C_XOR *)
  | 74 -> f74 (Obj.obj x) (* C_OR *)
  | 75 -> f75 (Obj.obj x) (* C_AND *)
  | 76 -> f76 (Obj.obj x) (* C_SUBW *)
  | 77 -> f77 (Obj.obj x) (* C_ADDW *)
  | 78 -> f78 (Obj.obj x) (* C_J *)
  | 79 -> f79 (Obj.obj x) (* C_BEQZ *)
  | 80 -> f80 (Obj.obj x) (* C_BNEZ *)
  | 81 -> f81 (Obj.obj x) (* C_SLLI *)
  | 82 -> f82 (Obj.obj x) (* C_LWSP *)
  | 83 -> f83 (Obj.obj x) (* C_LDSP *)
  | 84 -> f84 (Obj.obj x) (* C_SWSP *)
  | 85 -> f85 (Obj.obj x) (* C_SDSP *)
  | 86 -> f86 (Obj.obj x) (* C_JR *)
  | 87 -> f87 (Obj.obj x) (* C_JALR *)
  | 88 -> f88 (Obj.obj x) (* C_MV *)
  | 89 -> f89 (Obj.obj x) (* C_EBREAK *)
  | 90 -> f90 (Obj.obj x) (* C_ADD *)
  | 91 -> f91 (Obj.obj x) (* C_LBU *)
  | 92 -> f92 (Obj.obj x) (* C_LHU *)
  | 93 -> f93 (Obj.obj x) (* C_LH *)
  | 94 -> f94 (Obj.obj x) (* C_SB *)
  | 95 -> f95 (Obj.obj x) (* C_SH *)
  | 96 -> f96 (Obj.obj x) (* C_ZEXT_B *)
  | 97 -> f97 (Obj.obj x) (* C_SEXT_B *)
  | 98 -> f98 (Obj.obj x) (* C_ZEXT_H *)
  | 99 -> f99 (Obj.obj x) (* C_SEXT_H *)
  | 100 -> f100 (Obj.obj x) (* C_ZEXT_W *)
  | 101 -> f101 (Obj.obj x) (* C_NOT *)
  | 102 -> f102 (Obj.obj x) (* C_MUL *)
  | 103 -> f103 (Obj.obj x) (* HLVTYPE *)
  | 104 -> f104 (Obj.obj x) (* HSV *)
  | 105 -> f105 (Obj.obj x) (* HFENCE_VVMA *)
  | 106 -> f106 (Obj.obj x) (* HFENCE_GVMA *)
  | 107 -> f107 (Obj.obj x) (* LOAD_FP *)
  | 108 -> f108 (Obj.obj x) (* STORE_FP *)
  | 109 -> f109 (Obj.obj x) (* F_MADD_TYPE_S *)
  | 110 -> f110 (Obj.obj x) (* F_BIN_RM_TYPE_S *)
  | 111 -> f111 (Obj.obj x) (* F_UN_RM_FF_TYPE_S *)
  | 112 -> f112 (Obj.obj x) (* F_UN_RM_FX_TYPE_S *)
  | 113 -> f113 (Obj.obj x) (* F_UN_RM_XF_TYPE_S *)
  | 114 -> f114 (Obj.obj x) (* F_BIN_TYPE_F_S *)
  | 115 -> f115 (Obj.obj x) (* F_BIN_TYPE_X_S *)
  | 116 -> f116 (Obj.obj x) (* F_UN_TYPE_F_S *)
  | 117 -> f117 (Obj.obj x) (* F_UN_TYPE_X_S *)
  | 118 -> f118 (Obj.obj x) (* C_FLWSP *)
  | 119 -> f119 (Obj.obj x) (* C_FSWSP *)
  | 120 -> f120 (Obj.obj x) (* C_FLW *)
  | 121 -> f121 (Obj.obj x) (* C_FSW *)
  | 122 -> f122 (Obj.obj x) (* F_MADD_TYPE_D *)
  | 123 -> f123 (Obj.obj x) (* F_BIN_RM_TYPE_D *)
  | 124 -> f124 (Obj.obj x) (* F_UN_RM_FF_TYPE_D *)
  | 125 -> f125 (Obj.obj x) (* F_UN_RM_XF_TYPE_D *)
  | 126 -> f126 (Obj.obj x) (* F_UN_RM_FX_TYPE_D *)
  | 127 -> f127 (Obj.obj x) (* F_BIN_F_TYPE_D *)
  | 128 -> f128 (Obj.obj x) (* F_BIN_X_TYPE_D *)
  | 129 -> f129 (Obj.obj x) (* F_UN_X_TYPE_D *)
  | 130 -> f130 (Obj.obj x) (* F_UN_F_TYPE_D *)
  | 131 -> f131 (Obj.obj x) (* C_FLDSP *)
  | 132 -> f132 (Obj.obj x) (* C_FSDSP *)
  | 133 -> f133 (Obj.obj x) (* C_FLD *)
  | 134 -> f134 (Obj.obj x) (* C_FSD *)
  | 135 -> f135 (Obj.obj x) (* F_BIN_RM_TYPE_H *)
  | 136 -> f136 (Obj.obj x) (* F_MADD_TYPE_H *)
  | 137 -> f137 (Obj.obj x) (* F_BIN_F_TYPE_H *)
  | 138 -> f138 (Obj.obj x) (* F_BIN_X_TYPE_H *)
  | 139 -> f139 (Obj.obj x) (* F_UN_RM_FF_TYPE_H *)
  | 140 -> f140 (Obj.obj x) (* F_UN_RM_FX_TYPE_H *)
  | 141 -> f141 (Obj.obj x) (* F_UN_RM_XF_TYPE_H *)
  | 142 -> f142 (Obj.obj x) (* F_UN_F_TYPE_H *)
  | 143 -> f143 (Obj.obj x) (* F_UN_X_TYPE_H *)
  | 144 -> f144 (Obj.obj x) (* FLI_H *)
  | 145 -> f145 (Obj.obj x) (* FLI_S *)
  | 146 -> f146 (Obj.obj x) (* FLI_D *)
  | 147 -> f147 (Obj.obj x) (* FMINM_H *)
  | 148 -> f148 (Obj.obj x) (* FMAXM_H *)
  | 149 -> f149 (Obj.obj x) (* FMINM_S *)
  | 150 -> f150 (Obj.obj x) (* FMAXM_S *)
  | 151 -> f151 (Obj.obj x) (* FMINM_D *)
  | 152 -> f152 (Obj.obj x) (* FMAXM_D *)
  | 153 -> f153 (Obj.obj x) (* FROUND_H *)
  | 154 -> f154 (Obj.obj x) (* FROUNDNX_H *)
  | 155 -> f155 (Obj.obj x) (* FROUND_S *)
  | 156 -> f156 (Obj.obj x) (* FROUNDNX_S *)
  | 157 -> f157 (Obj.obj x) (* FROUND_D *)
  | 158 -> f158 (Obj.obj x) (* FROUNDNX_D *)
  | 159 -> f159 (Obj.obj x) (* FMVH_X_D *)
  | 160 -> f160 (Obj.obj x) (* FMVP_D_X *)
  | 161 -> f161 (Obj.obj x) (* FLEQ_H *)
  | 162 -> f162 (Obj.obj x) (* FLTQ_H *)
  | 163 -> f163 (Obj.obj x) (* FLEQ_S *)
  | 164 -> f164 (Obj.obj x) (* FLTQ_S *)
  | 165 -> f165 (Obj.obj x) (* FLEQ_D *)
  | 166 -> f166 (Obj.obj x) (* FLTQ_D *)
  | 167 -> f167 (Obj.obj x) (* FCVTMOD_W_D *)
  | 168 -> f168 (Obj.obj x) (* VSETVLI *)
  | 169 -> f169 (Obj.obj x) (* VSETVL *)
  | 170 -> f170 (Obj.obj x) (* VSETIVLI *)
  | 171 -> f171 (Obj.obj x) (* VVTYPE *)
  | 172 -> f172 (Obj.obj x) (* NVSTYPE *)
  | 173 -> f173 (Obj.obj x) (* NVTYPE *)
  | 174 -> f174 (Obj.obj x) (* MASKTYPEV *)
  | 175 -> f175 (Obj.obj x) (* MOVETYPEV *)
  | 176 -> f176 (Obj.obj x) (* VXTYPE *)
  | 177 -> f177 (Obj.obj x) (* NXSTYPE *)
  | 178 -> f178 (Obj.obj x) (* NXTYPE *)
  | 179 -> f179 (Obj.obj x) (* VXSG *)
  | 180 -> f180 (Obj.obj x) (* MASKTYPEX *)
  | 181 -> f181 (Obj.obj x) (* MOVETYPEX *)
  | 182 -> f182 (Obj.obj x) (* VITYPE *)
  | 183 -> f183 (Obj.obj x) (* NISTYPE *)
  | 184 -> f184 (Obj.obj x) (* NITYPE *)
  | 185 -> f185 (Obj.obj x) (* VISG *)
  | 186 -> f186 (Obj.obj x) (* MASKTYPEI *)
  | 187 -> f187 (Obj.obj x) (* MOVETYPEI *)
  | 188 -> f188 (Obj.obj x) (* VMVRTYPE *)
  | 189 -> f189 (Obj.obj x) (* MVVTYPE *)
  | 190 -> f190 (Obj.obj x) (* MVVMATYPE *)
  | 191 -> f191 (Obj.obj x) (* WVVTYPE *)
  | 192 -> f192 (Obj.obj x) (* WVTYPE *)
  | 193 -> f193 (Obj.obj x) (* WMVVTYPE *)
  | 194 -> f194 (Obj.obj x) (* VEXTTYPE *)
  | 195 -> f195 (Obj.obj x) (* VMVXS *)
  | 196 -> f196 (Obj.obj x) (* MVVCOMPRESS *)
  | 197 -> f197 (Obj.obj x) (* MVXTYPE *)
  | 198 -> f198 (Obj.obj x) (* MVXMATYPE *)
  | 199 -> f199 (Obj.obj x) (* WVXTYPE *)
  | 200 -> f200 (Obj.obj x) (* WXTYPE *)
  | 201 -> f201 (Obj.obj x) (* WMVXTYPE *)
  | 202 -> f202 (Obj.obj x) (* VMVSX *)
  | 203 -> f203 (Obj.obj x) (* FVVTYPE *)
  | 204 -> f204 (Obj.obj x) (* FVVMATYPE *)
  | 205 -> f205 (Obj.obj x) (* FWVVTYPE *)
  | 206 -> f206 (Obj.obj x) (* FWVVMATYPE *)
  | 207 -> f207 (Obj.obj x) (* FWVTYPE *)
  | 208 -> f208 (Obj.obj x) (* VFUNARY0 *)
  | 209 -> f209 (Obj.obj x) (* VFWUNARY0 *)
  | 210 -> f210 (Obj.obj x) (* VFNUNARY0 *)
  | 211 -> f211 (Obj.obj x) (* VFUNARY1 *)
  | 212 -> f212 (Obj.obj x) (* VFMVFS *)
  | 213 -> f213 (Obj.obj x) (* FVFTYPE *)
  | 214 -> f214 (Obj.obj x) (* FVFMATYPE *)
  | 215 -> f215 (Obj.obj x) (* FWVFTYPE *)
  | 216 -> f216 (Obj.obj x) (* FWVFMATYPE *)
  | 217 -> f217 (Obj.obj x) (* FWFTYPE *)
  | 218 -> f218 (Obj.obj x) (* VFMERGE *)
  | 219 -> f219 (Obj.obj x) (* VFMV *)
  | 220 -> f220 (Obj.obj x) (* VFMVSF *)
  | 221 -> f221 (Obj.obj x) (* VLSEGTYPE *)
  | 222 -> f222 (Obj.obj x) (* VLSEGFFTYPE *)
  | 223 -> f223 (Obj.obj x) (* VSSEGTYPE *)
  | 224 -> f224 (Obj.obj x) (* VLSSEGTYPE *)
  | 225 -> f225 (Obj.obj x) (* VSSSEGTYPE *)
  | 226 -> f226 (Obj.obj x) (* VLXSEGTYPE *)
  | 227 -> f227 (Obj.obj x) (* VSXSEGTYPE *)
  | 228 -> f228 (Obj.obj x) (* VLRETYPE *)
  | 229 -> f229 (Obj.obj x) (* VSRETYPE *)
  | 230 -> f230 (Obj.obj x) (* VMTYPE *)
  | 231 -> f231 (Obj.obj x) (* MMTYPE *)
  | 232 -> f232 (Obj.obj x) (* VCPOP_M *)
  | 233 -> f233 (Obj.obj x) (* VFIRST_M *)
  | 234 -> f234 (Obj.obj x) (* VMSBF_M *)
  | 235 -> f235 (Obj.obj x) (* VMSIF_M *)
  | 236 -> f236 (Obj.obj x) (* VMSOF_M *)
  | 237 -> f237 (Obj.obj x) (* VIOTA_M *)
  | 238 -> f238 (Obj.obj x) (* VID_V *)
  | 239 -> f239 (Obj.obj x) (* VVMTYPE *)
  | 240 -> f240 (Obj.obj x) (* VVMCTYPE *)
  | 241 -> f241 (Obj.obj x) (* VVMSTYPE *)
  | 242 -> f242 (Obj.obj x) (* VVCMPTYPE *)
  | 243 -> f243 (Obj.obj x) (* VXMTYPE *)
  | 244 -> f244 (Obj.obj x) (* VXMCTYPE *)
  | 245 -> f245 (Obj.obj x) (* VXMSTYPE *)
  | 246 -> f246 (Obj.obj x) (* VXCMPTYPE *)
  | 247 -> f247 (Obj.obj x) (* VIMTYPE *)
  | 248 -> f248 (Obj.obj x) (* VIMCTYPE *)
  | 249 -> f249 (Obj.obj x) (* VIMSTYPE *)
  | 250 -> f250 (Obj.obj x) (* VICMPTYPE *)
  | 251 -> f251 (Obj.obj x) (* FVVMTYPE *)
  | 252 -> f252 (Obj.obj x) (* FVFMTYPE *)
  | 253 -> f253 (Obj.obj x) (* RIVVTYPE *)
  | 254 -> f254 (Obj.obj x) (* RMVVTYPE *)
  | 255 -> f255 (Obj.obj x) (* RFVVTYPE *)
  | 256 -> f256 (Obj.obj x) (* RFWVVTYPE *)
  | 257 -> f257 (Obj.obj x) (* SHA256SIG0 *)
  | 258 -> f258 (Obj.obj x) (* SHA256SIG1 *)
  | 259 -> f259 (Obj.obj x) (* SHA256SUM0 *)
  | 260 -> f260 (Obj.obj x) (* SHA256SUM1 *)
  | 261 -> f261 (Obj.obj x) (* AES32ESMI *)
  | 262 -> f262 (Obj.obj x) (* AES32ESI *)
  | 263 -> f263 (Obj.obj x) (* AES32DSMI *)
  | 264 -> f264 (Obj.obj x) (* AES32DSI *)
  | 265 -> f265 (Obj.obj x) (* SHA512SIG0L *)
  | 266 -> f266 (Obj.obj x) (* SHA512SIG0H *)
  | 267 -> f267 (Obj.obj x) (* SHA512SIG1L *)
  | 268 -> f268 (Obj.obj x) (* SHA512SIG1H *)
  | 269 -> f269 (Obj.obj x) (* SHA512SUM0R *)
  | 270 -> f270 (Obj.obj x) (* SHA512SUM1R *)
  | 271 -> f271 (Obj.obj x) (* AES64KS1I *)
  | 272 -> f272 (Obj.obj x) (* AES64KS2 *)
  | 273 -> f273 (Obj.obj x) (* AES64IM *)
  | 274 -> f274 (Obj.obj x) (* AES64ESM *)
  | 275 -> f275 (Obj.obj x) (* AES64ES *)
  | 276 -> f276 (Obj.obj x) (* AES64DSM *)
  | 277 -> f277 (Obj.obj x) (* AES64DS *)
  | 278 -> f278 (Obj.obj x) (* SHA512SIG0 *)
  | 279 -> f279 (Obj.obj x) (* SHA512SIG1 *)
  | 280 -> f280 (Obj.obj x) (* SHA512SUM0 *)
  | 281 -> f281 (Obj.obj x) (* SHA512SUM1 *)
  | 282 -> f282 (Obj.obj x) (* SM3P0 *)
  | 283 -> f283 (Obj.obj x) (* SM3P1 *)
  | 284 -> f284 (Obj.obj x) (* SM4ED *)
  | 285 -> f285 (Obj.obj x) (* SM4KS *)
  | 286 -> f286 (Obj.obj x) (* ZBKB_RTYPE *)
  | 287 -> f287 (Obj.obj x) (* ZBKB_PACKW *)
  | 288 -> f288 (Obj.obj x) (* ZIP *)
  | 289 -> f289 (Obj.obj x) (* UNZIP *)
  | 290 -> f290 (Obj.obj x) (* BREV8 *)
  | 291 -> f291 (Obj.obj x) (* XPERM8 *)
  | 292 -> f292 (Obj.obj x) (* XPERM4 *)
  | 293 -> f293 (Obj.obj x) (* VANDN_VV *)
  | 294 -> f294 (Obj.obj x) (* VANDN_VX *)
  | 295 -> f295 (Obj.obj x) (* VBREV_V *)
  | 296 -> f296 (Obj.obj x) (* VBREV8_V *)
  | 297 -> f297 (Obj.obj x) (* VREV8_V *)
  | 298 -> f298 (Obj.obj x) (* VCLZ_V *)
  | 299 -> f299 (Obj.obj x) (* VCTZ_V *)
  | 300 -> f300 (Obj.obj x) (* VCPOP_V *)
  | 301 -> f301 (Obj.obj x) (* VROL_VV *)
  | 302 -> f302 (Obj.obj x) (* VROL_VX *)
  | 303 -> f303 (Obj.obj x) (* VROR_VV *)
  | 304 -> f304 (Obj.obj x) (* VROR_VX *)
  | 305 -> f305 (Obj.obj x) (* VROR_VI *)
  | 306 -> f306 (Obj.obj x) (* VWSLL_VV *)
  | 307 -> f307 (Obj.obj x) (* VWSLL_VX *)
  | 308 -> f308 (Obj.obj x) (* VWSLL_VI *)
  | 309 -> f309 (Obj.obj x) (* VCLMUL_VV *)
  | 310 -> f310 (Obj.obj x) (* VCLMUL_VX *)
  | 311 -> f311 (Obj.obj x) (* VCLMULH_VV *)
  | 312 -> f312 (Obj.obj x) (* VCLMULH_VX *)
  | 313 -> f313 (Obj.obj x) (* VGHSH_VV *)
  | 314 -> f314 (Obj.obj x) (* VGMUL_VV *)
  | 315 -> f315 (Obj.obj x) (* VAESDF *)
  | 316 -> f316 (Obj.obj x) (* VAESDM *)
  | 317 -> f317 (Obj.obj x) (* VAESEF *)
  | 318 -> f318 (Obj.obj x) (* VAESEM *)
  | 319 -> f319 (Obj.obj x) (* VAESKF1_VI *)
  | 320 -> f320 (Obj.obj x) (* VAESKF2_VI *)
  | 321 -> f321 (Obj.obj x) (* VAESZ_VS *)
  | 322 -> f322 (Obj.obj x) (* VSM4K_VI *)
  | 323 -> f323 (Obj.obj x) (* ZVKSM4RTYPE *)
  | 324 -> f324 (Obj.obj x) (* VSHA2MS_VV *)
  | 325 -> f325 (Obj.obj x) (* ZVKSHA2TYPE *)
  | 326 -> f326 (Obj.obj x) (* VSM3ME_VV *)
  | 327 -> f327 (Obj.obj x) (* VSM3C_VI *)
  | 328 -> f328 (Obj.obj x) (* ZVABD_VV *)
  | 329 -> f329 (Obj.obj x) (* ZVABD_VX *)
  | 330 -> f330 (Obj.obj x) (* ZVWABDA_VV *)
  | 331 -> f331 (Obj.obj x) (* ZVWABDA_VX *)
  | 332 -> f332 (Obj.obj x) (* CSRReg *)
  | 333 -> f333 (Obj.obj x) (* CSRImm *)
  | 334 -> f334 (Obj.obj x) (* SINVAL_VMA *)
  | 335 -> f335 (Obj.obj x) (* SFENCE_W_INVAL *)
  | 336 -> f336 (Obj.obj x) (* SFENCE_INVAL_IR *)
  | 337 -> f337 (Obj.obj x) (* HINVAL_VVMA *)
  | 338 -> f338 (Obj.obj x) (* HINVAL_GVMA *)
  | 339 -> f339 (Obj.obj x) (* WRS *)
  | 340 -> f340 (Obj.obj x) (* SSPUSH *)
  | 341 -> f341 (Obj.obj x) (* C_SSPUSH *)
  | 342 -> f342 (Obj.obj x) (* SSPOPCHK *)
  | 343 -> f343 (Obj.obj x) (* C_SSPOPCHK *)
  | 344 -> f344 (Obj.obj x) (* SSRDP *)
  | 345 -> f345 (Obj.obj x) (* SSAMOSWAP *)
  | 346 -> f346 (Obj.obj x) (* ZICOND_RTYPE *)
  | 347 -> f347 (Obj.obj x) (* ZICBOM *)
  | 348 -> f348 (Obj.obj x) (* BITYPE *)
  | 349 -> f349 (Obj.obj x) (* ZICBOZ *)
  | 350 -> f350 (Obj.obj x) (* FENCEI *)
  | 351 -> f351 (Obj.obj x) (* ZILX_LOAD *)
  | 352 -> f352 (Obj.obj x) (* FCVT_BF16_S *)
  | 353 -> f353 (Obj.obj x) (* FCVT_S_BF16 *)
  | 354 -> f354 (Obj.obj x) (* VFNCVTBF16_F_F_W *)
  | 355 -> f355 (Obj.obj x) (* VFWCVTBF16_F_F_V *)
  | 356 -> f356 (Obj.obj x) (* VFWMACCBF16_VV *)
  | 357 -> f357 (Obj.obj x) (* VFWMACCBF16_VF *)
  | 358 -> f358 (Obj.obj x) (* ZIMOP_MOP_R *)
  | 359 -> f359 (Obj.obj x) (* ZIMOP_MOP_RR *)
  | 360 -> f360 (Obj.obj x) (* ZCMOP *)
  | _ -> invalid_arg "RiscVInstruction.match_: invalid tag"
