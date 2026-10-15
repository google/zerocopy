(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Common predicates and lemmas for loading code into memory.                *)
(*                                                                           *)
(* This file is loaded after a backend defines its state and memory          *)
(* component. The address width is inferred from that component.             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Generic byte-list code loading.                                           *)
(* ------------------------------------------------------------------------- *)

(* Read exactly `LENGTH l` consecutive bytes at the backend native word
   address `pc`. Offset arithmetic in the lemmas below therefore wraps at the
   backend address width; this predicate does not embed addresses in int64. *)
let bytes_loaded = new_definition
 `bytes_loaded s pc l <=>
     read (memory :> bytelist(pc,LENGTH l)) s = l`;;

let bytes_loaded_nil = prove
 (`bytes_loaded s pc []`,
  REWRITE_TAC[bytes_loaded; READ_COMPONENT_COMPOSE;
              LENGTH; bytelist_clauses]);;

let bytes_loaded_append = prove
 (`bytes_loaded s pc (APPEND l1 l2) <=>
   bytes_loaded s pc l1 /\
   bytes_loaded s (word_add pc (word (LENGTH l1))) l2`,
  REWRITE_TAC[bytes_loaded; READ_COMPONENT_COMPOSE;
              read_bytelist_append]);;

let bytes_loaded_unique = METIS [bytes_loaded]
 `!s pc l1 l2.
    bytes_loaded s pc l1 ==> bytes_loaded s pc l2 ==>
    LENGTH l1 = LENGTH l2 ==> l1 = l2`;;

let bytes_loaded_update = METIS [bytes_loaded]
 `!l n. LENGTH l = n ==> !s pc. bytes_loaded s pc l ==>
  !s'. read(memory :> bytelist(pc,n)) s' =
       read(memory :> bytelist(pc,n)) s ==>
       bytes_loaded s' pc l`;;

let bytes_loaded_of_append3 = prove
 (`!l l1 l2 l3. l = APPEND l1 (APPEND l2 l3) ==>
   !s pc. bytes_loaded s (word pc) l ==>
          bytes_loaded s (word (pc + LENGTH l1)) l2`,
  REWRITE_TAC[WORD_ADD] THEN METIS_TAC[bytes_loaded_append]);;

let BYTES_LOADED_BUTLAST = prove
 (`!s pc l. bytes_loaded s pc l ==> bytes_loaded s pc (BUTLAST l)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `l:byte list = []` THEN ASM_REWRITE_TAC[BUTLAST] THEN
  FIRST_X_ASSUM(fun th ->
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  SIMP_TAC[bytes_loaded_append]);;

let BYTES_LOADED_SUB_LIST = prove
 (`!s pc l m n.
        bytes_loaded s pc l
        ==> bytes_loaded s (word_add pc (word m)) (SUB_LIST(m,n) l)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `m + n:num`] SUB_LIST_TOPSPLIT) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[bytes_loaded_append] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[SUB_LIST_SPLIT; ADD_CLAUSES; bytes_loaded_append] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LE_CASES; SUB_LIST_TRIVIAL; bytes_loaded_nil]);;

let BYTES_LOADED_TRIM_LIST = prove
 (`!s pc l m n.
        bytes_loaded s pc l
        ==> bytes_loaded s (word_add pc (word m)) (TRIM_LIST(m,n) l)`,
  REWRITE_TAC[BYTES_LOADED_SUB_LIST; TRIM_LIST]);;

(* ------------------------------------------------------------------------- *)
(* Four-byte-aligned code loading for fixed-width instruction sets.          *)
(* ------------------------------------------------------------------------- *)

(* Code is loaded at a native-width address whose unsigned value is divisible
   by four. The non-GEN lemmas below use a type shape that guarantees at least
   two address bits, avoiding a repeated width premise for ordinary 32- and
   64-bit backends. *)
let aligned_bytes_loaded = new_definition
 `aligned_bytes_loaded s pc l <=>
  4 divides val pc /\ bytes_loaded s pc l`;;

let DIVIDES_4_VAL_WORD_GEN = prove
 (`2 <= dimindex(:N) ==>
   (4 divides val(word pc:N word) <=> 4 divides pc)`,
  REWRITE_TAC[ARITH_RULE `4 = 2 EXP 2`] THEN
  MESON_TAC[DIVIDES_VAL_WORD]);;

let DIVIDES_4_VAL_WORD_ADD_GEN = prove
 (`2 <= dimindex(:N) ==>
   !pc n. 4 divides val(pc:N word) ==> 4 divides n ==>
          4 divides val(word_add pc (word n))`,
  DISCH_TAC THEN REWRITE_TAC[FORALL_WORD; GSYM WORD_ADD] THEN
  ASM_SIMP_TAC[DIVIDES_4_VAL_WORD_GEN] THEN
  MESON_TAC[DIVIDES_ADD]);;

let DIMINDEX_TYBIT0_GE_2 = prove
 (`2 <= dimindex(:(N tybit0))`,
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN
  MP_TAC(ISPEC `UNIV:N->bool` DIMINDEX_GE_1) THEN ARITH_TAC);;

let DIVIDES_4_VAL_WORD =
  MATCH_MP DIVIDES_4_VAL_WORD_GEN DIMINDEX_TYBIT0_GE_2;;

let DIVIDES_4_VAL_WORD_ADD =
  MATCH_MP DIVIDES_4_VAL_WORD_ADD_GEN DIMINDEX_TYBIT0_GE_2;;

let aligned_bytes_loaded_word = prove
 (`aligned_bytes_loaded s (word pc) l <=>
   4 divides pc /\ bytes_loaded s (word pc) l`,
  REWRITE_TAC[aligned_bytes_loaded; DIVIDES_4_VAL_WORD]);;

let aligned_bytes_loaded_aligned = prove
 (`!s pc l. aligned_bytes_loaded s pc l ==> aligned 4 pc`,
  REWRITE_TAC[aligned_bytes_loaded; aligned;
              ARITH_RULE `4 = 2 EXP 2`] THEN
  MESON_TAC[DIMINDEX_TYBIT0_GE_2; DIVIDES_EXP_LE_IMP]);;

let aligned_bytes_loaded_append_left = prove
 (`aligned_bytes_loaded s pc (APPEND l1 l2) ==>
   aligned_bytes_loaded s pc l1`,
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded_append] THEN
  METIS_TAC[]);;

let aligned_bytes_loaded_append = prove
 (`4 divides LENGTH l1 ==>
   (aligned_bytes_loaded s pc (APPEND l1 l2) <=>
    aligned_bytes_loaded s pc l1 /\
    aligned_bytes_loaded s (word_add pc (word (LENGTH l1))) l2)`,
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded_append] THEN
  MESON_TAC[DIVIDES_4_VAL_WORD_ADD]);;

let aligned_bytes_loaded_append_alt = prove
 (`aligned_bytes_loaded s pc (APPEND l1 l2) <=>
   aligned_bytes_loaded s pc l1 /\
   bytes_loaded s (word_add pc (word (LENGTH l1))) l2`,
  REWRITE_TAC[aligned_bytes_loaded; bytes_loaded_append; CONJ_ASSOC]);;

let aligned_bytes_loaded_unique =
  METIS [aligned_bytes_loaded; bytes_loaded_unique]
  `!s pc l1 l2.
   aligned_bytes_loaded s pc l1 ==> aligned_bytes_loaded s pc l2 ==>
   LENGTH l1 = LENGTH l2 ==> l1 = l2`;;

let aligned_bytes_loaded_update =
  METIS [aligned_bytes_loaded; bytes_loaded_update]
 `!l n. LENGTH l = n ==> !s pc. aligned_bytes_loaded s pc l ==>
  !s'. read(memory :> bytelist(pc,n)) s' =
       read(memory :> bytelist(pc,n)) s ==>
       aligned_bytes_loaded s' pc l`;;

let aligned_bytes_loaded_of_append3 = prove
 (`!l l1 l2 l3. l = APPEND l1 (APPEND l2 l3) ==>
   4 divides LENGTH l1 ==>
   !s pc. aligned_bytes_loaded s (word pc) l ==>
          aligned_bytes_loaded s (word (pc + LENGTH l1)) l2`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_ADD] THEN
  METIS_TAC[aligned_bytes_loaded_append;
            aligned_bytes_loaded_append_left]);;

let aligned_bytes_loaded_sub_list = prove
 (`!s pc l m n.
      aligned_bytes_loaded s pc l /\ 4 divides m
      ==> aligned_bytes_loaded s (word_add pc (word m))
            (SUB_LIST(m,n) l)`,
  REWRITE_TAC[aligned_bytes_loaded] THEN
  MESON_TAC[BYTES_LOADED_SUB_LIST; DIVIDES_4_VAL_WORD_ADD]);;

let aligned_bytes_loaded_sub_list_zero = prove
 (`!s pc l n.
        aligned_bytes_loaded s pc l
        ==> aligned_bytes_loaded s pc (SUB_LIST(0,n) l)`,
  REWRITE_TAC[aligned_bytes_loaded] THEN
  MESON_TAC[BYTES_LOADED_SUB_LIST;
            WORD_RULE `word_add x (word 0) = x`]);;

let ALIGNED_BYTES_LOADED_SUB_LIST =
  CONJ aligned_bytes_loaded_sub_list
       aligned_bytes_loaded_sub_list_zero;;

let ALIGNED_BYTES_LOADED_TRIM_LIST = prove
 (`!s pc l m n.
      aligned_bytes_loaded s pc l /\ 4 divides m
      ==> aligned_bytes_loaded s (word_add pc (word m))
            (TRIM_LIST(m,n) l)`,
  REWRITE_TAC[TRIM_LIST] THEN
  MATCH_ACCEPT_TAC aligned_bytes_loaded_sub_list);;
