(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
needs "common/aes.ml";;

(* References:
   Intel 64 and IA-32 Architectures Software Developer's Manual Volume 1:
     Basic Architecture, page 311-316
   Intel 64 and IA-32 Architectures Software Developer's Manual Volume 2:
     Instruction Set Reference, A-Z, 2A 3-63
   White Paper: Intel Advanced Encryption Standard (AES) New Instructions Set *)

let aesenc = new_definition
 `aesenc (state:(128)word) (roundkey:(128)word) : (128)word =
   let state = aes_shift_rows state in
   let state = aes_sub_bytes joined_GF2 state in
   let state = aes_mix_columns state in
   (word_xor state roundkey)`;;

let aesenclast = new_definition
 `aesenclast (state:(128)word) (roundkey:(128)word) : (128)word =
   let state = aes_shift_rows state in
   let state = aes_sub_bytes joined_GF2 state in
   (word_xor state roundkey)`;;

let aesdec = new_definition
 `aesdec (state:(128)word) (roundkey:(128)word) : (128)word =
   let state = aes_inv_shift_rows state in
   let state = aes_sub_bytes joined_GF2_inv state in
   let state = aes_inv_mix_columns state in
   (word_xor state roundkey)`;;

let aesdeclast = new_definition
 `aesdeclast (state:(128)word) (roundkey:(128)word) : (128)word =
   let state = aes_inv_shift_rows state in
   let state = aes_sub_bytes joined_GF2_inv state in
   (word_xor state roundkey)`;;

let aeskeygenassist = new_definition
  `aeskeygenassist (x:(128)word) (imm8:(8)word) : (128)word =
    let x3 = (word_subword:(128 word)->(num#num)->(32 word)) x (96,32) in
    let x1 = (word_subword:(128 word)->(num#num)->(32 word)) x (32,32) in
    let rcon = (word_zx:(8 word)->(32 word)) imm8 in
    let dest0 = aes_subword x1 in
    let dest1 = word_xor (aes_rotword (aes_subword x1)) rcon in
    let dest2 = aes_subword x3 in
    let dest3 = word_xor (aes_rotword (aes_subword x3)) rcon in
    ((word_join:(32 word)->(96 word)->(128 word)) dest3
     ((word_join:(32 word)->(64 word)->(96 word)) dest2
      ((word_join:(32 word)->(32 word)->(64 word)) dest1 dest0)))`;;

(************************************************)
(** CONVERSIONS                                **)
(************************************************)

let AESENC_HELPER_CONV =
  REWRITE_CONV [aesenc] THENC
  AES_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  AES_MIX_COLUMNS_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESENCLAST_HELPER_CONV =
  REWRITE_CONV [aesenclast] THENC
  AES_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESDEC_HELPER_CONV =
  REWRITE_CONV [aesdec] THENC
  AES_INV_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  AES_INV_MIX_COLUMNS_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESDECLAST_HELPER_CONV =
  REWRITE_CONV [aesdeclast] THENC
  AES_INV_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESKEYGENASSIST_HELPER_CONV =
  REWRITE_CONV [aeskeygenassist] THENC
  AES_SUBWORD_CONV THENC
  AES_ROTWORD_CONV THENC
  TOP_DEPTH_CONV let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESENC_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aesenc",_),
         Comb(Const("word",_),state)),
         Comb(Const("word",_),roundkey))
    when is_numeral state && is_numeral roundkey -> AESENC_HELPER_CONV tm
    | _ -> failwith "AESENC_REDUCE_CONV: inapplicable";;
let AESENCLAST_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aesenclast",_),
         Comb(Const("word",_),state)),
         Comb(Const("word",_),roundkey))
    when is_numeral state && is_numeral roundkey -> AESENCLAST_HELPER_CONV tm
    | _ -> failwith "AESENCLAST_REDUCE_CONV: inapplicable";;
let AESDEC_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aesdec",_),
         Comb(Const("word",_),state)),
         Comb(Const("word",_),roundkey))
    when is_numeral state && is_numeral roundkey -> AESDEC_HELPER_CONV tm
    | _ -> failwith "AESDEC_REDUCE_CONV: inapplicable";;
let AESDECLAST_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aesdeclast",_),
         Comb(Const("word",_),state)),
         Comb(Const("word",_),roundkey))
    when is_numeral state && is_numeral roundkey -> AESDECLAST_HELPER_CONV tm
    | _ -> failwith "AESDECLAST_REDUCE_CONV: inapplicable";;
let AESKEYGENASSIST_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aeskeygenassist",_),
         Comb(Const("word",_),x)),
         Comb(Const("word",_),imm8))
    when is_numeral x && is_numeral imm8 -> AESKEYGENASSIST_HELPER_CONV tm
    | _ -> failwith "AESKEYGENASSIST_HELPER_CONV: inapplicable";;

(************************************************)
(** TESTS                                      **)
(************************************************)
(* From White Paper:
  Intel Advanced Encryption Standard (AES) New Instructions Set
  https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf
  Fig 11. AESENC Example to Fig 14 AESDECLAST Example *)

prove(`aesenc (word 0x7b5b54657374566563746f725d53475d)
              (word 0x48692853686179295b477565726f6e5d) =
       word 0xa8311c2f9fdba3c58b104b58ded7e595`,
       CONV_TAC(LAND_CONV AESENC_REDUCE_CONV) THEN REFL_TAC);;

prove(`aesenclast (word 0x7b5b54657374566563746f725d53475d)
                  (word 0x48692853686179295b477565726f6e5d) =
       word 0xc7fb881e938c5964177ec42553fdc611`,
       CONV_TAC(LAND_CONV AESENCLAST_REDUCE_CONV) THEN REFL_TAC);;

prove(`aesdec (word 0x7b5b54657374566563746f725d53475d)
              (word 0x48692853686179295b477565726f6e5d) =
       word 0x138ac342faea2787b58eb95eb730392a`,
       CONV_TAC(LAND_CONV AESDEC_REDUCE_CONV) THEN REFL_TAC);;

prove(`aesdeclast (word 0x7b5b54657374566563746f725d53475d)
                  (word 0x48692853686179295b477565726f6e5d) =
       word 0xc5a391ef6b317f95d410637b72a593d0`,
       CONV_TAC(LAND_CONV AESDECLAST_REDUCE_CONV) THEN REFL_TAC);;

prove(`aeskeygenassist (word 0x3c4fcf098815f7aba6d2ae2816157e2b)
                       (word 0x1) =
       word 0x01eb848beb848a013424b5e524b5e434`,
       CONV_TAC(LAND_CONV AESKEYGENASSIST_REDUCE_CONV) THEN REFL_TAC);;
