(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Load basic background needed for the x86 bignum proofs.                   *)
(* ========================================================================= *)

loads "update_database.ml";;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Some background theory from the standard libraries.                       *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/bitsize.ml";;
needs "Library/pocklington.ml";;
needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
loadt "Library/records.ml";;

(* ------------------------------------------------------------------------- *)
(* common ARM-x86 proof infrastructure.                                      *)
(* ------------------------------------------------------------------------- *)

loadt "common/overlap.ml";;
loadt "common/for_hollight.ml";;
loadt "common/words2.ml";;
loadt "common/misc.ml";;
loadt "common/components.ml";;
loadt "common/alignment.ml";;
loadt "common/relational.ml";;
loadt "common/interval.ml";;
loadt "common/elf.ml";;
loadt "common/safety.ml";;
loadt "common/execution.ml";;

(* ------------------------------------------------------------------------- *)
(* Additional Cryptographic AES intrinsics                                   *)
(* ------------------------------------------------------------------------- *)

loadt "x86/proofs/aes.ml";;
extra_word_CONV := [AESENC_REDUCE_CONV;
                    AESENCLAST_REDUCE_CONV;
                    AESDEC_REDUCE_CONV;
                    AESDECLAST_REDUCE_CONV;
                    AESKEYGENASSIST_REDUCE_CONV]
                    @ (!extra_word_CONV);;

(* ------------------------------------------------------------------------- *)
(* The main x86_64 model.                                                    *)
(* ------------------------------------------------------------------------- *)

loadt "x86/proofs/instruction.ml";;
loadt "x86/proofs/decode.ml";;
loadt "x86/proofs/x86.ml";;
(* Reduce reads of YMMx_SSE into reads of YMMx by default *)
extra_word_CONV := [GEN_REWRITE_CONV I READ_YMM_SSE_EQUIV] @ !extra_word_CONV;;

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "common/bignum.ml";;
