(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generic wordlist support. The memory-specific definitions use the backend *)
(* "memory" component and are loaded after the backend state is defined.     *)
(* ========================================================================= *)

(* The first sections provide pure list/number arithmetic. Later sections:
   - decompose byte-range equalities into word-list elements;
   - change the chunk size of named memory reads;
   - relate fixed-length word lists to backend byte memory; and
   - expose concrete word-list elements as individual memory reads.

   None of these interfaces depends on the mathematical bignum layer. *)

(* ------------------------------------------------------------------------- *)
(* Mapping little-endian word list to/from natural number (general size).    *)
(* ------------------------------------------------------------------------- *)

let num_of_wordlist = define
 `num_of_wordlist ([]:(N word) list) = 0 /\
  num_of_wordlist (CONS (h:N word) t) =
     val h + 2 EXP dimindex(:N) * num_of_wordlist t`;;

let wordlist_of_num = define
 `(wordlist_of_num 0 n :(N word)list = []) /\
  (wordlist_of_num (SUC k) n =
     CONS (word(n MOD 2 EXP dimindex(:N)):N word)
          (wordlist_of_num k (n DIV 2 EXP dimindex(:N))))`;;

let NUM_OF_WORDLIST_SING = prove
 (`!h:N word. num_of_wordlist [h] = val h`,
  REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_APPEND = prove
 (`!lis1 lis2:(N word)list.
        num_of_wordlist(APPEND lis1 lis2) =
        num_of_wordlist lis1 +
        2 EXP (dimindex(:N) * LENGTH lis1) * num_of_wordlist lis2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; num_of_wordlist] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_LENGTH = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; EXP_ADD; ARITH] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o lhand o snd) THEN
  MATCH_MP_TAC(ARITH_RULE
   `n * (x + 1) <= y ==> h < n ==> h + n * x < y`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list n.
        LENGTH l <= n ==> num_of_wordlist l < 2 EXP (dimindex(:N) * n)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(l:(N word)list))` THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH; LE_EXP; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_GEN = prove
 (`!l:((N word)list) n.
        dimindex(:N) * LENGTH l <= n ==> num_of_wordlist l < 2 EXP n`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand NUM_OF_WORDLIST_BOUND_LENGTH o
    lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_DIV = prove
 (`!(w:N word) ws.
        num_of_wordlist (CONS w ws) DIV 2 EXP dimindex(:N) =
        num_of_wordlist ws`,
  SIMP_TAC[num_of_wordlist; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_MOD = prove
 (`!(w:N word) ws.
        num_of_wordlist (CONS w ws) MOD 2 EXP dimindex(:N) = val w`,
  REWRITE_TAC[num_of_wordlist; MOD_MULT_ADD] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let NUM_OF_WORDLIST_ZAP = prove
 (`!l:(N word)list.
        2 EXP dimindex(:N) * num_of_wordlist l =
        num_of_wordlist(CONS (word 0) l)`,
  REWRITE_TAC[num_of_wordlist; VAL_WORD_0; ADD_CLAUSES]);;

let LENGTH_WORDLIST_OF_NUM = prove
 (`!k n. LENGTH(wordlist_of_num k n:(N word)list) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[wordlist_of_num; LENGTH]);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; num_of_wordlist; ARITH; EXP; MULT_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN DISCH_TAC THEN
  REWRITE_TAC[EXP_ADD] THEN  MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
  REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let WORDLIST_OF_NUM_OF_WORDLIST = prove
 (`!l:(N word)list. wordlist_of_num (LENGTH l) (num_of_wordlist l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_wordlist; wordlist_of_num; LENGTH] THEN FIRST_X_ASSUM
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  SIMP_TAC[CONS_11; MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; WORD_VAL_GALOIS;
           EXP_EQ_0; MOD_MOD_REFL; MOD_EQ_SELF] THEN
  SIMP_TAC[VAL_BOUND; DIV_LT; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_OF_NUM_0 = prove
 (`!k. num_of_wordlist(wordlist_of_num k 0:(N word)list) = 0`,
  INDUCT_TAC THEN SIMP_TAC[num_of_wordlist; wordlist_of_num] THEN
  ASM_REWRITE_TAC[VAL_WORD_0; DIV_0; MOD_0; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_OF_NUM = prove
 (`!k n. num_of_wordlist(wordlist_of_num k n:(N word)list) =
         n MOD 2 EXP (dimindex(:N) * k)`,
  INDUCT_TAC THEN REWRITE_TAC[num_of_wordlist] THENL
   [REWRITE_TAC[wordlist_of_num; num_of_wordlist; EXP; MOD_1; MULT_CLAUSES];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[wordlist_of_num; num_of_wordlist] THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE `n * SUC k = n + n * k`; MOD_MULT_MOD] THEN
  REWRITE_TAC[VAL_WORD; MOD_MOD_REFL] THEN ARITH_TAC);;

let WORDLIST_OF_NUM_MOD = prove
 (`!k n. wordlist_of_num k (n MOD 2 EXP (dimindex(:N) * k)):(N word)list =
         wordlist_of_num k n`,
  REPEAT GEN_TAC THEN REWRITE_TAC [GSYM NUM_OF_WORDLIST_OF_NUM] THEN
  REWRITE_TAC [REWRITE_RULE [LENGTH_WORDLIST_OF_NUM]
    (SPEC `wordlist_of_num k n:(N word)list` WORDLIST_OF_NUM_OF_WORDLIST)]);;

let NUM_OF_WORDLIST_OF_NUM_EQ_SELF = prove
 (`!k n. n < 2 EXP (dimindex(:N) * k)
         ==> num_of_wordlist(wordlist_of_num k n:(N word)list) = n`,
  SIMP_TAC[NUM_OF_WORDLIST_OF_NUM; MOD_LT]);;

let NUM_OF_WORDLIST_LT = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) < num_of_wordlist(CONS n0 n1) <=>
        num_of_wordlist m1 < num_of_wordlist n1 \/
        num_of_wordlist m1 = num_of_wordlist n1 /\ val m0 < val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LT THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_LE = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) <= num_of_wordlist(CONS n0 n1) <=>
        num_of_wordlist m1 < num_of_wordlist n1 \/
        num_of_wordlist m1 = num_of_wordlist n1 /\ val m0 <= val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LE THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_EQ = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) = num_of_wordlist(CONS n0 n1) <=>
        m0 = n0 /\ num_of_wordlist m1 = num_of_wordlist n1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_SUB_LIST_0 = prove
 (`!(l:(N word)list) n.
        num_of_wordlist(SUB_LIST(0,n) l) =
        num_of_wordlist l MOD 2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[EXP_ADD] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
    REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`; MOD_LT_EQ] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    MATCH_MP_TAC(NUMBER_RULE
     `(t == t') (mod d)
      ==> (h + e * t == h + e * t') (mod (e * d))`) THEN
    REWRITE_TAC[CONG_RMOD; CONG_REFL]]);;

let NUM_OF_WORDLIST_SUB_LIST = prove
 (`!(l:(N word)list) m n.
        num_of_wordlist (SUB_LIST(m,n) l) =
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; GSYM(CONJUNCT2 num_of_wordlist);
              EXP; DIV_1; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `n:num` THEN
  SIMP_TAC[EXP_ADD; GSYM DIV_DIV; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_EL = prove
 (`!(l:(N word)list) n.
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * n)) MOD
        2 EXP (dimindex(:N)) =
        if n < LENGTH l then val(EL n l) else 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`l:(N word)list`; `n:num`; `1`]
   NUM_OF_WORDLIST_SUB_LIST) THEN
  REWRITE_TAC[SUB_LIST_1; MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SING; num_of_wordlist]);;

let EL_NUM_OF_WORDLIST = prove
 (`!(l:(N word)list) n.
        n < LENGTH l
        ==> EL n l = word(num_of_wordlist l DIV 2 EXP (dimindex(:N) * n))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`l:(N word)list`; `n:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[WORD_VAL_GALOIS]);;

let LISTS_NUM_OF_WORDLIST_EQ = prove
 (`!l1 l2:(N word)list.
        l1 = l2 <=>
        LENGTH l1 = LENGTH l2 /\
        num_of_wordlist l1 = num_of_wordlist l2`,
  MESON_TAC[WORDLIST_OF_NUM_OF_WORDLIST]);;

(* ------------------------------------------------------------------------- *)
(* Relating byte ranges to explicit word lists.                              *)
(*                                                                           *)
(* BYTES_EQ_NUM_OF_WORDLIST_EXPAND exposes the first word and advances the   *)
(* address by its byte width. BYTES_EQ_NUM_OF_WORDLIST_APPEND instead splits *)
(* at a list boundary. BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV repeatedly uses  *)
(* the first theorem until the list is exhausted. For example, it turns      *)
(*                                                                           *)
(*   read (m :> bytes(a,12)) s = num_of_wordlist [x0;x1;x2]                  *)
(*                                                                           *)
(* for 32-bit words into three wbytes equalities at a, a + 4, and a + 8.     *)
(* Proofs commonly apply the conversion to the left side of an implication   *)
(* before rewriting wbytes to the corresponding named byte view.             *)
(* ------------------------------------------------------------------------- *)

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND = prove
 (`!m (a:A word) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word) t.
    dimindex(:N) <= len
    ==> (read (m :> bytes(a,len)) s = num_of_wordlist (CONS h t) <=>
         read (m :> wbytes a) s = h /\
         read (m :> bytes(word_add a (word(dimindex(:N))),len-dimindex(:N))) s=
         num_of_wordlist t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_TYBIT0] THEN
  REWRITE_TAC[ARITH_RULE `2 * 2 * 2 * n = 8 * n`] THEN
  REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `d:num <= l ==> l = d + (l - d)`)) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; ADD_SUB2] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * 2 * n = 8 * n`]);;

let BYTES_EQ_NUM_OF_WORDLIST_APPEND = prove
 (`!m (a:A word) (s:S) lis1 (lis2:(N word)list) len1 len2.
        dimindex(:N) * LENGTH lis1 = 8 * len1
        ==>  (read (m :> bytes(a,len1+len2)) s =
              num_of_wordlist(APPEND lis1 lis2) <=>
              read (m :> bytes(a,len1)) s = num_of_wordlist lis1 /\
              read (m :> bytes(word_add a (word len1),len2)) s =
              num_of_wordlist lis2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN ASM_REWRITE_TAC[LE_REFL]);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV =
  let pth = prove
   (`!m (a:A word) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word).
        dimindex(:N) = len
        ==> (read (m :> bytes(a,len)) s = num_of_wordlist [h] <=>
             read (m :> wbytes a) s = h)`,
    SIMP_TAC[BYTES_EQ_NUM_OF_WORDLIST_EXPAND; LE_REFL] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; SUB_REFL; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[num_of_wordlist]) in
  let frule = PART_MATCH (lhand o rand) pth
  and brule = PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_EXPAND in
  let baseconv tm =
    let ith = frule tm in
    let sth = (LAND_CONV DIMINDEX_CONV THENC NUM_EQ_CONV)
              (lhand(concl ith)) in
    MP ith (EQT_ELIM sth) in
  let rec conv tm =
    try baseconv tm with Failure _ ->
    let ith = brule tm in
    let dth = DIMINDEX_CONV(lhand(lhand(concl ith))) in
    let ith' = SUBS[dth] ith in
    let ath = MP ith' (EQT_ELIM(NUM_LE_CONV(lhand(concl ith')))) in
    let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV
               (RAND_CONV
                 (BINOP2_CONV (TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                              NUM_SUB_CONV))))))) ath in
    CONV_RULE(RAND_CONV(RAND_CONV conv)) bth in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Changing the chunk size of named memory reads.                            *)
(*                                                                           *)
(* `READ_MEMORY_MERGE_CONV n` expands a wide read through `n` word-join      *)
(* levels; callers use the resulting equality to combine narrower read       *)
(* facts. `READ_MEMORY_FULLMERGE_CONV` expands every available level.         *)
(* `READ_MEMORY_SPLIT_CONV n` turns an equality for a wide read into          *)
(* equalities for its low and high subwords through `n` levels. All three     *)
(* retain the address word type inferred from the memory component.          *)
(*                                                                           *)
(* For example, READ_MEMORY_MERGE_CONV 2 applied to a bytes128 read produces  *)
(* a nested word_join of four bytes32 reads. READ_MEMORY_SPLIT_CONV 2 applied *)
(* to `read (memory :> bytes128 a) s = x` produces four equalities between    *)
(* those bytes32 reads and the corresponding 32-bit subwords of x. This is   *)
(* typically used before vector simulation and reversed on its results.       *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let READ_MEMORY_FULLMERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv tm =
    (baseconv THENC BINOP_CONV(TRY_CONV conv)) tm in
  conv;;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Reading a general word list from memory. The definition reads             *)
(* CEILING(dimindex(:N) * n / 8) bytes and truncates the resulting number to  *)
(* `n` words. If the requested bit count is not byte-aligned, unused high     *)
(* bits of the final byte are discarded. Lemmas equating the list value to   *)
(* the complete memory read therefore require an exact byte-size premise.    *)
(* ------------------------------------------------------------------------- *)

(* WORDLIST_FROM_MEMORY_GEN rewrites through any sufficiently large byte read;
   NUM_OF_WORDLIST_FROM_MEMORY_GEN recovers the complete read when the bit and
   byte sizes agree exactly. WORDLIST_FROM_MEMORY_EQ_ALT turns a list equality
   into a length condition and a numeric memory equality, which is often more
   convenient before symbolic execution.

   The unsuffixed convenience theorems constrain the element width to a
   multiple of eight through three tybit0 constructors and discharge the
   associated byte-size premises. *)

let wordlist_from_memory = define
 `wordlist_from_memory(a,n) s:(N word)list =
    wordlist_of_num n
     (read (memory :> bytes(a,(dimindex(:N) * n + 7) DIV 8)) s)`;;

let WORDLIST_FROM_MEMORY_GEN = prove
 (`!n m a s.
        dimindex(:N) * n <= 8 * m
        ==> wordlist_from_memory(a,n) s:(N word)list =
            wordlist_of_num n (read(memory :> bytes(a,m)) s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wordlist_from_memory] THEN
  ONCE_REWRITE_TAC[GSYM WORDLIST_OF_NUM_MOD] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(dimindex (:N) * n + 7) DIV 8 = MIN m ((dimindex (:N) * n + 7) DIV 8)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN ARITH_TAC);;

let WORDLIST_FROM_MEMORY = prove
 (`!a n s. wordlist_from_memory(a,n) s:((((N tybit0)tybit0)tybit0)word)list =
           wordlist_of_num n (read(memory :> bytes(a,dimindex(:N) * n)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wordlist_from_memory] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN REPLICATE_TAC 4 AP_TERM_TAC THEN
  ARITH_TAC);;

let LENGTH_WORDLIST_FROM_MEMORY = prove
 (`!a n s. LENGTH(wordlist_from_memory(a,n) s:(N word)list) = n`,
  REWRITE_TAC[wordlist_from_memory; LENGTH_WORDLIST_OF_NUM]);;

let NUM_OF_WORDLIST_FROM_MEMORY_GEN = prove
 (`!n m a s.
        dimindex(:N) * n = 8 * m
        ==> num_of_wordlist(wordlist_from_memory(a,n) s:(N word)list) =
            read(memory :> bytes(a,m)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wordlist_from_memory] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(8 * m + 7) DIV 8 = m`] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_OF_NUM_EQ_SELF THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let NUM_OF_WORDLIST_FROM_MEMORY = prove
 (`!a n s.
        num_of_wordlist
         (wordlist_from_memory(a,n) s:((((N tybit0)tybit0)tybit0)word)list) =
        read(memory :> bytes(a,dimindex(:N) * n)) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NUM_OF_WORDLIST_FROM_MEMORY_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_FROM_MEMORY_BYTE = prove
 (`!a n s. num_of_wordlist (wordlist_from_memory (a,n) s:byte list) =
           read (memory :> bytes (a,n)) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NUM_OF_WORDLIST_FROM_MEMORY_GEN THEN
  REWRITE_TAC[DIMINDEX_8]);;

let WORDLIST_FROM_MEMORY_EQ_ALT = prove
 (`!addr len size l s.
        dimindex(:N) * len = 8 * size
        ==> (wordlist_from_memory(addr,len) s:(N word)list = l <=>
             LENGTH l = len /\
             read (memory :> bytes(addr,size)) s = num_of_wordlist l)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH(l:(N word)list) = len` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[LENGTH_WORDLIST_FROM_MEMORY]] THEN
  EQ_TAC THENL [ASM_MESON_TAC[NUM_OF_WORDLIST_FROM_MEMORY_GEN]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `wordlist_of_num len:num->(N word)list`) THEN
  MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THENL [ALL_TAC; ASM_MESON_TAC[WORDLIST_OF_NUM_OF_WORDLIST]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORDLIST_FROM_MEMORY_GEN THEN
  ASM_REWRITE_TAC[LE_REFL]);;

let WORDLIST_FROM_MEMORY_CLAUSES = prove
 (`(!a s. wordlist_from_memory(a,0) s:(N word)list = []) /\
   (!a n s.
     wordlist_from_memory(a,SUC n) s :((((N tybit0)tybit0)tybit0)word)list =
     APPEND (wordlist_from_memory(a,n) s)
            [read (memory :> wbytes(word_add a (word(dimindex(:N) * n)))) s])`,
  CONJ_TAC THENL
   [REWRITE_TAC[wordlist_from_memory; MULT_CLAUSES; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[wordlist_of_num];
    REPEAT GEN_TAC] THEN
  REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_APPEND; LENGTH; ADD_CLAUSES;
              NUM_OF_WORDLIST_FROM_MEMORY; wordlist_of_num;
              NUM_OF_WORDLIST_APPEND; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; NUM_OF_WORDLIST_SING] THEN
  REWRITE_TAC[ARITH_RULE `x * SUC y = x * y + x`; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[VAL_READ_WBYTES; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; ARITH_RULE `2 * 2 * 2 * x = 8 * x`] THEN
  REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`]);;

let EL_WORDLIST_FROM_MEMORY = prove
 (`!a n i s.
      i < n
      ==> EL i
           (wordlist_from_memory(a,n) s:
             ((((N tybit0)tybit0)tybit0)word)list) =
          read
           (memory :>
            wbytes(word_add a (word(dimindex(:N) * i)))) s`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[CONJUNCT2 WORDLIST_FROM_MEMORY_CLAUSES] THEN
    ASM_CASES_TAC `i:num < n` THENL
     [ASM_SIMP_TAC[EL_APPEND; LENGTH_WORDLIST_FROM_MEMORY];
      SUBGOAL_THEN `i:num = n` SUBST1_TAC THENL
       [ASM_ARITH_TAC;
        REWRITE_TAC[EL_APPEND; LENGTH_WORDLIST_FROM_MEMORY; LT_REFL;
                    SUB_REFL; EL; HD]]]]);;

(* This conversion expands a wordlist_from_memory term whose list length is a
   numeral. It selects the named byte view from the list element width and
   normalizes the successive address offsets. Schematically,

     WORDLIST_FROM_MEMORY_CONV
       `wordlist_from_memory(a,3) s:int32 list`

   produces a theorem with right-hand side

     [read (memory :> bytes32 a) s;
      read (memory :> bytes32 (word_add a (word 4))) s;
      read (memory :> bytes32 (word_add a (word 8))) s]

   Proofs normally use CONV_TAC, or CONV_RULE to expand an assumption. The
   memory component determines the address type; int32 is the element type. *)
let WORDLIST_FROM_MEMORY_CONV =
  let pthc = prove
   (`l:((((N tybit0)tybit0)tybit0)word)list = APPEND l [] /\
     APPEND (wordlist_from_memory(a,0) s) l = l /\
     APPEND (wordlist_from_memory(a,SUC n) s) l =
     APPEND (wordlist_from_memory(a,n) s)
     (CONS (read(memory :> wbytes(word_add a (word(dimindex(:N) * n)))) s) l)`,
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES] THEN
    REWRITE_TAC[APPEND_NIL; APPEND; GSYM APPEND_ASSOC]) in
  let pths = CONJUNCTS pthc
  and avars = sort (<) (frees(concl pthc))
  and timfn = type_match (type_of(lhand(lhand(concl pthc))))
  and prule =
       (PURE_REWRITE_RULE o map GSYM)
       [BYTES8_WBYTES; BYTES16_WBYTES; BYTES32_WBYTES; BYTES64_WBYTES;
        BYTES128_WBYTES; BYTES256_WBYTES] in
  fun tm ->
    match tm with
      Comb(Comb(Const("wordlist_from_memory",_),
                Comb(Comb(Const(",",_),_),n)),_) when is_numeral n ->
      let tyin = timfn (type_of tm) [] in
      let [a_tm;l_tm;n_tm;s_tm] = map (inst tyin) avars
      and [pth_init;pth_base;pth_step] =
        map (CONV_RULE(ONCE_DEPTH_CONV DIMINDEX_CONV) o INST_TYPE tyin) pths in
      let rule_base = GEN_REWRITE_RULE RAND_CONV [pth_base]
      and rule_step =
        CONV_RULE(RAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV num_CONV)) THENC
                  GEN_REWRITE_CONV I [pth_step] THENC
                  RAND_CONV(LAND_CONV(LAND_CONV (funpow 2 RAND_CONV
                    (funpow 2 RAND_CONV NUM_MULT_CONV THENC
                     TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                     GEN_REWRITE_CONV TRY_CONV
                      [WORD_ADD_0])))))) in
      let rec conv th =
        try rule_base th with Failure _ ->
        let th' = rule_step th in conv th' in
      prule(conv (INST [tm,l_tm] pth_init))
    | _ -> failwith "WORDLIST_FROM_MEMORY_CONV";;

(* ------------------------------------------------------------------------- *)
(* Pairing adjacent low/high words preserves num_of_wordlist. The generic    *)
(* memory theorem requires the total bit count to be divisible by four, so   *)
(* the two list representations read exactly the same number of bytes. The   *)
(* type-constrained convenience theorem discharges that premise.              *)
(* ------------------------------------------------------------------------- *)

let pair_wordlist = define
 `(!hi (lo:N word) rest.
     pair_wordlist (CONS lo (CONS hi rest)) =
     CONS (word_join hi lo:((N)tybit0)word) (pair_wordlist rest)) /\
  (!w. pair_wordlist [w] = [word_join (word 0:N word) w]) /\
  pair_wordlist [] = []`;;

let LENGTH_PAIR_WORDLIST = prove
 (`!l:(N word)list. LENGTH(pair_wordlist l) = (LENGTH l + 1) DIV 2`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[ARITH_RULE `n < SUC(SUC n)`] THEN ARITH_TAC);;

let NUM_OF_PAIR_WORDLIST = prove
 (`!l:(N word)list. num_of_wordlist (pair_wordlist l) = num_of_wordlist l`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  MAP_EVERY X_GEN_TAC [`lo:N word`; `med:(N word)list`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`med:(N word)list`,`med:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN_SIMPLE; DIMINDEX_TYBIT0;
           VAL_WORD_0; GSYM MULT_2; LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  REWRITE_TAC[MULT_2; EXP_ADD] THEN ARITH_TAC);;

let WORDLIST_FROM_MEMORY_PAIR_GEN = prove
 (`!a n s. 4 divides (dimindex(:N) * n)
           ==> wordlist_from_memory(a,n) s =
               pair_wordlist(wordlist_from_memory(a,2*n) s:(N word)list)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  ASM_REWRITE_TAC[LENGTH_PAIR_WORDLIST; LENGTH_WORDLIST_FROM_MEMORY] THEN
  REWRITE_TAC[NUM_OF_PAIR_WORDLIST] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:num` o REWRITE_RULE[divides]) THEN
  TRANS_TAC EQ_TRANS `read(memory :> bytes(a,m)) s` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_FROM_MEMORY_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN POP_ASSUM MP_TAC THEN CONV_TAC NUM_RING);;

let WORDLIST_FROM_MEMORY_PAIR = prove
 (`!a n s. wordlist_from_memory(a,n) s =
           pair_wordlist
             (wordlist_from_memory(a,2*n) s:(((N tybit0)tybit0)word)list)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORDLIST_FROM_MEMORY_PAIR_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * n = n * 4`] THEN
  NUMBER_TAC);;
