(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*               General analysis of memory overlap.                         *)
(*                                                                           *)
(* Considering pairs of regions (addr,len) and defining when they overlap,   *)
(* or one is contained in the other, taking into account that the address    *)
(* wraps modulo n. Note that the case of ignoring this wrapping is still     *)
(* included in this setting simply by setting n = 0 since congruence mod 0   *)
(* is just equality (and in HOL Light m MOD 0 = m for uniformity with this). *)
(* Note that (cf NONOVERLAPPING_MODULO_0) being nonoverlapping mod n implies *)
(* being nonoverlapping in the simple sense.                                 *)
(* ========================================================================= *)

needs "Library/pocklington.ml";; (* To avoid regenerating congruence trivia *)
needs "Library/words.ml";;       (* Just for the two "WORDSWISE" theorems   *)

(* ------------------------------------------------------------------------- *)
(* Definitions of overlapping and containment modulo n.                      *)
(* ------------------------------------------------------------------------- *)

let nonoverlapping_modulo = new_definition
 `nonoverlapping_modulo n (addr1,len1) (addr2,len2) <=>
        ~(?i:num j:num.
                i < len1 /\ j < len2 /\
                (addr1 + i == addr2 + j) (mod n))`;;

let contained_modulo = new_definition
 `contained_modulo n (addr1,len1) (addr2,len2) <=>
        !i:num. i < len1
                ==> ?j. j < len2 /\ (addr1 + i == addr2 + j) (mod n)`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties and interrelations.                                      *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_MODULO_SETWISE = prove
 (`!addr1 addr2 len1 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) <=>
        DISJOINT (IMAGE (\i. (addr1 + i) MOD n) {i | i < len1})
                 (IMAGE (\i. (addr2 + i) MOD n) {i | i < len2})`,
  REWRITE_TAC[nonoverlapping_modulo; CONG] THEN SET_TAC[]);;

let CONTAINED_MODULO_SETWISE = prove
 (`!addr1 addr2 len1 len2.
        contained_modulo n (addr1,len1) (addr2,len2) <=>
        (IMAGE (\i. (addr1 + i) MOD n) {i | i < len1}) SUBSET
        (IMAGE (\i. (addr2 + i) MOD n) {i | i < len2})`,
  REWRITE_TAC[contained_modulo; CONG] THEN SET_TAC[]);;

let NONOVERLAPPING_MODULO_WORDWISE = prove
 (`!(addr1:N word) addr2 len1 len2.
           nonoverlapping_modulo (2 EXP dimindex(:N))
                                 (val addr1,len1) (val addr2,len2) <=>
           DISJOINT (IMAGE (\i. word_add addr1 (word i)) {i | i < len1})
                    (IMAGE (\i. word_add addr2 (word i)) {i | i < len2})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_MODULO_SETWISE] THEN
  MATCH_MP_TAC(SET_RULE
   `(?h. (!x. g1(x) = h(f1 x)) /\
         (!x. g2(x) = h(f2 x)) /\
         (!x y. h x = h y ==> x = y))
    ==> (DISJOINT (IMAGE g1 s) (IMAGE g2 t) <=>
         DISJOINT (IMAGE f1 s) (IMAGE f2 t))`) THEN
  EXISTS_TAC `val:N word->num` THEN
  REWRITE_TAC[WORD_MOD_SIZE; WORD_ADD; WORD_VAL] THEN
  REWRITE_TAC[VAL_EQ; VAL_WORD_ADD; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let CONTAINED_MODULO_WORDWISE = prove
 (`!(addr1:N word) addr2 len1 len2.
           contained_modulo (2 EXP dimindex(:N))
                            (val addr1,len1) (val addr2,len2) <=>
           IMAGE (\i. word_add addr1 (word i)) {i | i < len1} SUBSET
           IMAGE (\i. word_add addr2 (word i)) {i | i < len2}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTAINED_MODULO_SETWISE] THEN
  MATCH_MP_TAC(SET_RULE
   `(?h. (!x. g1(x) = h(f1 x)) /\
         (!x. g2(x) = h(f2 x)) /\
         (!x y. h x = h y ==> x = y))
    ==> (IMAGE g1 s SUBSET IMAGE g2 t <=>
         IMAGE f1 s SUBSET IMAGE f2 t)`) THEN
  EXISTS_TAC `val:N word->num` THEN
  REWRITE_TAC[WORD_MOD_SIZE; WORD_ADD; WORD_VAL] THEN
  REWRITE_TAC[VAL_EQ; VAL_WORD_ADD; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let NONOVERLAPPING_MODULO_TRIVIAL = prove
 (`!n addr1 addr2 len1 len2.
        len1 = 0 \/ len2 = 0
        ==> nonoverlapping_modulo n (addr1,len1) (addr2,len2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[nonoverlapping_modulo; LT]);;

let CONTAINED_MODULO_TRIVIAL = prove
 (`!n addr1 addr2 len2.
        contained_modulo n (addr1,0) (addr2,len2)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[contained_modulo; CONJUNCT1 LT]);;

let CONTAINED_MODULO_EMPTY = prove
 (`!n addr1 addr2 len1.
        contained_modulo n (addr1,len) (addr2,0) <=> len = 0`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[contained_modulo; LT] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN ARITH_TAC);;

let NONOVERLAPPING_MODULO_REFL = prove
 (`!n addr len1 len2.
    nonoverlapping_modulo n (addr,len1) (addr,len2) <=> len1 = 0 \/ len2 = 0`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[NONOVERLAPPING_MODULO_TRIVIAL] THEN
  REWRITE_TAC[nonoverlapping_modulo; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`0`; `0`]) THEN
  REWRITE_TAC[CONG_REFL] THEN ARITH_TAC);;

let CONTAINED_MODULO_REFL = prove
 (`!n addr len1 len2.
        contained_modulo n (addr,len1) (addr,len2) <=>
        len1 <= len2 \/ 0 < n /\ n <= len2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[contained_modulo; NUMBER_RULE
   `(a + m:num == a + n) (mod p) <=> (m == n) (mod p)`] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[LE_1; LT_REFL] THENL
   [REWRITE_TAC[CONG_MOD_0] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[UNWIND_THM1] THEN EQ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `len1 - 1`) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n:num <= len2` THEN ASM_REWRITE_TAC[] THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXISTS_TAC `i MOD n` THEN
    REWRITE_TAC[CONG_RMOD; CONG_REFL] THEN
    TRANS_TAC LTE_TRANS `n:num` THEN ASM_REWRITE_TAC[MOD_LT_EQ];
    ALL_TAC] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[CONG_REFL; LTE_TRANS]] THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  DISCH_THEN(MP_TAC o SPEC `len2:num`) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[CONG] THEN MATCH_MP_TAC(MESON[LT_REFL]
   `j MOD n = j /\ i MOD n = i /\ i < j ==> ~(j MOD n = i MOD n)`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN
  ASM_ARITH_TAC);;

let NONOVERLAPPING_MODULO_SYM = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) <=>
        nonoverlapping_modulo n (addr2,len2) (addr1,len1)`,
  REWRITE_TAC[nonoverlapping_modulo] THEN MESON_TAC[CONG_SYM]);;

let CONTAINED_MODULO_TRANS = prove
 (`!n addr1 len1 addr2 len2 addr3 len3.
        contained_modulo n (addr1,len1) (addr2,len2) /\
        contained_modulo n (addr2,len2) (addr3,len3)
        ==> contained_modulo n (addr1,len1) (addr3,len3)`,
  REWRITE_TAC[CONTAINED_MODULO_SETWISE; SUBSET_TRANS]);;

let NONOVERLAPPING_MODULO_SUBREGIONS = prove
 (`!n addr1 len1 addr2 len2 addr1' len1' addr2' len2'.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) /\
        contained_modulo n (addr1',len1') (addr1,len1) /\
        contained_modulo n (addr2',len2') (addr2,len2)
        ==> nonoverlapping_modulo n (addr1',len1') (addr2',len2')`,
  REWRITE_TAC[CONTAINED_MODULO_SETWISE; NONOVERLAPPING_MODULO_SETWISE] THEN
  SET_TAC[]);;

let NONOVERLAPPING_MODULO_LMOD = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1 MOD n,len1) (addr2,len2) <=>
        nonoverlapping_modulo n (addr1,len1) (addr2,len2)`,
  REWRITE_TAC[nonoverlapping_modulo; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let NONOVERLAPPING_MODULO_RMOD = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2 MOD n,len2) <=>
        nonoverlapping_modulo n (addr1,len1) (addr2,len2)`,
  REWRITE_TAC[nonoverlapping_modulo; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let NONOVERLAPPING_MODULO_MOD2 = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1 MOD n,len1) (addr2 MOD n,len2) <=>
        nonoverlapping_modulo n (addr1,len1) (addr2,len2)`,
  REWRITE_TAC[nonoverlapping_modulo; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let CONTAINED_MODULO_LMOD = prove
 (`!n addr1 len1 addr2 len2.
        contained_modulo n (addr1 MOD n,len1) (addr2,len2) <=>
        contained_modulo n (addr1,len1) (addr2,len2)`,
  REWRITE_TAC[contained_modulo; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let CONTAINED_MODULO_RMOD = prove
 (`!n addr1 len1 addr2 len2.
        contained_modulo n (addr1,len1) (addr2 MOD n,len2) <=>
        contained_modulo n (addr1,len1) (addr2,len2)`,
  REWRITE_TAC[contained_modulo; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let CONTAINED_MODULO_MOD2 = prove
 (`!n addr1 len1 addr2 len2.
        contained_modulo n (addr1 MOD n,len1) (addr2 MOD n,len2) <=>
        contained_modulo n (addr1,len1) (addr2,len2)`,
  REWRITE_TAC[contained_modulo; CONG] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

let NONOVERLAPPING_MODULO_LMIN = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,MIN len1 n) (addr2,len2) <=>
        n = 0 \/ nonoverlapping_modulo n (addr1,len1) (addr2,len2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[NONOVERLAPPING_MODULO_TRIVIAL; ARITH_RULE `MIN n 0 = 0`] THEN
  REWRITE_TAC[nonoverlapping_modulo; CONG; MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(MESON[]
   `!n. (!i j. R i j ==> R' i j) /\ (!i j. R' i j ==> R (i MOD n) j)
        ==> ((?i j. R i j) <=> (?i j. R' i j))`) THEN
  EXISTS_TAC `n:num` THEN CONV_TAC MOD_DOWN_CONV THEN
  SIMP_TAC[MOD_LT_EQ_LT] THEN ASM_ARITH_TAC);;

let NONOVERLAPPING_MODULO_RMIN = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,MIN len2 n) <=>
        n = 0 \/ nonoverlapping_modulo n (addr1,len1) (addr2,len2)`,
  ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
  MESON_TAC[NONOVERLAPPING_MODULO_LMIN]);;

let NONOVERLAPPING_MODULO_MIN2 = prove
 (`!n addr1 len1 addr2 len2.
       nonoverlapping_modulo n (addr1,MIN len1 n) (addr2,MIN len2 n) <=>
       n = 0 \/ nonoverlapping_modulo n (addr1,len1) (addr2,len2)`,
  REWRITE_TAC[NONOVERLAPPING_MODULO_LMIN; NONOVERLAPPING_MODULO_RMIN] THEN
  CONV_TAC TAUT);;

let CONTAINED_MODULO_LMIN = prove
 (`!n addr1 len1 addr2 len2.
        contained_modulo n (addr1,MIN len1 n) (addr2,len2) <=>
        n = 0 \/ contained_modulo n (addr1,len1) (addr2,len2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[CONTAINED_MODULO_TRIVIAL; ARITH_RULE `MIN n 0 = 0`] THEN
  REWRITE_TAC[contained_modulo; CONG; MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `!n. (!i. P' i ==> P i) /\ (!i. P(i MOD n) ==> P' i)
        ==> ((!i. P i) <=> (!i. P' i))`) THEN
  EXISTS_TAC `n:num` THEN CONV_TAC MOD_DOWN_CONV THEN
  ASM_SIMP_TAC[MOD_LT_EQ] THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CONTAINED_MODULO_RMIN = prove
 (`!n addr1 len1 addr2 len2.
        contained_modulo n (addr1,len1) (addr2,MIN len2 n) <=>
        if n = 0 then len1 = 0
        else contained_modulo n (addr1,len1) (addr2,len2)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONTAINED_MODULO_EMPTY; ARITH_RULE `MIN n 0 = 0`] THEN
  REWRITE_TAC[contained_modulo; CONG; MIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
  `!n. (!i j. R i j ==> R' i j) /\ (!i j. R' i j ==> R i (j MOD n))
        ==> ((!i. P i ==> ?j. R i j) <=>
             (!i. P i ==> ?j. R' i j))`) THEN
  EXISTS_TAC `n:num` THEN CONV_TAC MOD_DOWN_CONV THEN
  ASM_SIMP_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC);;

let CONTAINED_MODULO_MIN2 = prove
 (`!n addr1 len1 addr2 len2.
        contained_modulo n (addr1,MIN len1 n) (addr2,MIN len2 n) <=>
        n = 0 \/ contained_modulo n (addr1,len1) (addr2,len2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTAINED_MODULO_RMIN] THEN
  REWRITE_TAC[CONTAINED_MODULO_LMIN] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let NONOVERLAPPING_MODULO_OFFSET_RIGHT = prove
 (`!a1 a2 l1 l2 k.
        nonoverlapping_modulo n (a1 + k,l1) (a2 + k,l2) <=>
        nonoverlapping_modulo n (a1,l1) (a2,l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo] THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUMBER_RULE);;

let NONOVERLAPPING_MODULO_OFFSET_LEFT = prove
 (`!a l1 l2 k1 k2.
        nonoverlapping_modulo n (a + k1,l1) (a + k2,l2) <=>
        nonoverlapping_modulo n (k1,l1) (k2,l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo] THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUMBER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Other misc lemmas we might want.                                          *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_MODULO_MULTIPLE = prove
 (`!m n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2)
        ==> nonoverlapping_modulo (m * n) (addr1,len1) (addr2,len2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo; CONTRAPOS_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  MESON_TAC[NUMBER_RULE `(a:num == b) (mod(m * n)) ==> (a == b) (mod n)`]);;

let NONOVERLAPPING_MODULO_0 = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2)
        ==> nonoverlapping_modulo 0 (addr1,len1) (addr2,len2)`,
  MESON_TAC[NONOVERLAPPING_MODULO_MULTIPLE; MULT_CLAUSES]);;

let NONOVERLAPPING_MODULO_DIFFERENCE = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) <=>
        (len1 = 0 \/ len2 = 0) \/
        ~(?z:int. --(&len2) < z /\ z < &len1 /\
                  (&addr2 - &addr1 == z) (mod &n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo] THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_REWRITE_TAC[CONJUNCT1 LT] THEN
  ASM_CASES_TAC `len2 = 0` THEN ASM_REWRITE_TAC[CONJUNCT1 LT] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_EXISTS_POS] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `?i j k:int. &0 <= i /\ i < &len1 /\ &0 <= j /\ j < &len2 /\ k = i - j /\
                (&addr2 - &addr1 == k) (mod &n)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
    REWRITE_TAC[INTEGER_RULE
      `(x + i == y + j) (mod(n:int)) <=> (y - x == i - j) (mod n)`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:int` THEN REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; CONJ_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  EQ_TAC THENL [INT_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `&0:int <= k` THENL
   [MAP_EVERY EXISTS_TAC [`k:int`; `&0:int`];
    MAP_EVERY EXISTS_TAC [`&0:int`; `--k:int`]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_EQ]) THEN
  ASM_INT_ARITH_TAC);;

let NONOVERLAPPING_NONMODULAR_DIFFERENCE = prove
 (`!addr1 len1 addr2 len2.
        nonoverlapping_modulo 0 (addr1,len1) (addr2,len2) <=>
        (len1 = 0 \/ len2 = 0) \/
        ~(-- &len2:int < &addr2 - &addr1 /\ &addr2 - &addr1:int < &len1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_MODULO_DIFFERENCE] THEN
  REWRITE_TAC[INTEGER_RULE `(x:int == y) (mod &0) <=> (x = y)`] THEN
  MESON_TAC[]);;

let NONOVERLAPPING_NONMODULAR_NUM = prove
 (`!addr1 addr2 len1 len2.
        nonoverlapping_modulo 0 (addr1,len1) (addr2,len2) <=>
        (len1 = 0 \/ len2 = 0) \/
        (addr1 + len1 <= addr2 \/ addr2 + len2 <= addr1)`,
  REWRITE_TAC[NONOVERLAPPING_NONMODULAR_DIFFERENCE] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_LE] THEN
  INT_ARITH_TAC);;

let NONOVERLAPPING_MODULO_OFFSET = prove
 (`!n addr1 addr2 len1 len2 d.
        nonoverlapping_modulo n (addr1 + d,len1) (addr2 + d,len2) <=>
        nonoverlapping_modulo n (addr1,len1) (addr2,len2)`,
  REWRITE_TAC[NONOVERLAPPING_MODULO_DIFFERENCE] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; INT_ARITH
   `(a + d) - (b + d):int = a - b`]);;

let NONOVERLAPPING_MODULO_MODULAR = prove
 (`!n addr1 addr1' addr2 addr2' len1 len2.
        (addr1' == addr1) (mod n) /\ (addr2' == addr2) (mod n)
        ==> (nonoverlapping_modulo n (addr1',len1) (addr2',len2) <=>
             nonoverlapping_modulo n (addr1,len1) (addr2,len2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NONOVERLAPPING_MODULO_DIFFERENCE] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[num_congruent] THEN CONV_TAC INTEGER_RULE);;

let NONOVERLAPPING_MODULO_DIFFERENCE_ALT = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) <=>
        (len1 = 0 \/ len2 = 0) \/
        ~(?z. &0 <= z /\ z <= (&len1 + &len2) - &2 /\
              (&addr2 - &addr1 + &len2 - &1:int == z) (mod &n))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_MODULO_DIFFERENCE] THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `len2 = 0` THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `z:int` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `z + &len2 - &1:int` THEN
    ASM_REWRITE_TAC[INTEGER_RULE
     `(x + a:int == y + a) (mod n) <=> (x == y) (mod n)`] THEN
    ASM_INT_ARITH_TAC;
    EXISTS_TAC `z - (&len2 - &1):int` THEN
    ASM_REWRITE_TAC[INTEGER_RULE
      `(a:int == z - l) (mod n) <=> (a + l == z) (mod n)`] THEN
    ASM_INT_ARITH_TAC]);;

let NONOVERLAPPING_MODULO_DIFFERENCE_NUM = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) <=>
        (len1 = 0 \/ len2 = 0) \/
        !d. (&addr2 - &addr1 + &len2 - &1:int == &d) (mod &n)
            ==> (len1 - 1) + (len2 - 1) < d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_MODULO_DIFFERENCE_ALT] THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `len2 = 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM INT_EXISTS_POS] THEN
  REWRITE_TAC[NOT_EXISTS_THM; INT_LE_SUB_LADD] THEN
  REWRITE_TAC[TAUT `~(a /\ b) <=> b ==> ~a`] THEN
  REWRITE_TAC[INT_NOT_LE; INT_OF_NUM_ADD; INT_OF_NUM_LT] THEN
  ASM_SIMP_TAC[ARITH_RULE
    `~(l1 = 0) /\ ~(l2 = 0)
     ==> (l1 + l2 < n + 2 <=> (l1 - 1) + (l2 - 1) < n)`]);;

let NONOVERLAPPING_MODULO_DIFFERENCE_NUM_RESTRICTED = prove
 (`!n addr1 len1 addr2 len2.
        len1 + len2 <= n + 1
        ==> (nonoverlapping_modulo n (addr1,len1) (addr2,len2) <=>
             (len1 = 0 \/ len2 = 0) \/
             !d. d < n /\ (&addr2 - &addr1 + &len2 - &1:int == &d) (mod &n)
                 ==> (len1 - 1) + (len2 - 1) < d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NONOVERLAPPING_MODULO_DIFFERENCE_NUM] THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `len2 = 0` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `d:num < n` THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Containment generally implies some inequalities between sizes. But        *)
(* this is not always completely trivial in the case of sizes >= n.          *)
(* ------------------------------------------------------------------------- *)

let CONTAINED_MODULO_IMP_NONTRIVIAL = prove
 (`!n a b i j. contained_modulo n (a,i) (b,j) /\ j < n ==> i < n`,
  REWRITE_TAC[CONTAINED_MODULO_SETWISE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CARD_SUBSET)) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; NOT_LE] THEN
  TRANS_TAC LET_TRANS `j:num` THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[CARD_NUMSEG_LT; LE_REFL]] THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; GSYM CONG] THEN
    REWRITE_TAC[NUMBER_RULE
     `(b + x:num == b + y) (mod n) <=> (x == y) (mod n)`] THEN
    ASM_MESON_TAC[CONG_IMP_EQ; LT_TRANS];
    ALL_TAC] THEN
  TRANS_TAC LTE_TRANS `n:num` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&m - &a:int`; `&n:int`] INT_CONG_SOLVE_BOUNDS) THEN
  ASM_REWRITE_TAC[GSYM INT_EXISTS_POS; INT_OF_NUM_EQ] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[INT_ABS_NUM]] THEN
  REWRITE_TAC[INTEGER_RULE `(x:int == y - z) (mod n) <=> (z + x == y) (mod n)`;
              INT_OF_NUM_ADD; INT_OF_NUM_LT; GSYM num_congruent] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[CONG] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MATCH_MP_TAC(GSYM MOD_LT); ALL_TAC] THEN ASM_ARITH_TAC);;

let CONTAINED_MODULO_IMP_LE = prove
 (`!n a b i j. contained_modulo n (a,i) (b,j) /\ i <= n ==> i <= j`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:num <= j` THENL
   [ASM_MESON_TAC[LE_TRANS]; RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN
  REWRITE_TAC[CONTAINED_MODULO_SETWISE] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CARD_SUBSET)) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV) [GSYM CARD_NUMSEG_LT] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; GSYM CONG] THEN
  REWRITE_TAC[NUMBER_RULE
   `(b + x:num == b + y) (mod n) <=> (x == y) (mod n)`] THEN
  ASM_MESON_TAC[CONG_IMP_EQ; LT_TRANS; LTE_TRANS]);;

let CONTAINED_MODULO_IMP_LE_ADD = prove
 (`!n a i j k.
        contained_modulo n (a + i,j) (a,k) /\
        i <= k /\ k < n
        ==> i + j <= k`,
  REWRITE_TAC[CONTAINED_MODULO_SETWISE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTAINED_MODULO_IMP_LE THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `a:num`; `a:num`] THEN
  MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> q /\ p`) THEN CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC LT_IMP_LE THEN
    MATCH_MP_TAC CONTAINED_MODULO_IMP_NONTRIVIAL THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTAINED_MODULO_SETWISE] THEN
  MATCH_MP_TAC(SET_RULE
   `IMAGE f (s DIFF t) SUBSET IMAGE f t
    ==> IMAGE f s SUBSET IMAGE f t`) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        SUBSET_TRANS)) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(a + i) + j:num = a + (j + i)`] THEN
  REWRITE_TAC[SET_RULE
   `IMAGE (\j. (a + j + i) MOD n) s =
    IMAGE (\j. (a + j) MOD n) (IMAGE (\j. j + i) s)`] THEN
  MATCH_MP_TAC IMAGE_SUBSET THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; IN_IMAGE] THEN
  REWRITE_TAC[ARITH_RULE `m:num = n + i <=> m - i = n /\ i <= m`] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Similarly, non-overlap implies some size limitations.                     *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_IMP_SMALL_2 = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) /\
        0 < n /\ 0 < len1 /\ 0 < len2
        ==> len1 + len2 <= n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[MESON[]
   `(!a1 l1 a2 l2. P a1 l1 a2 l2) <=> (!a1 a2 l1 l2. P a1 l1 a2 l2)`] THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [MESON_TAC[ADD_SYM; NONOVERLAPPING_MODULO_SYM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[NONOVERLAPPING_MODULO_DIFFERENCE_NUM; LE_1;
               INT_OF_NUM_SUB; INT_OF_NUM_ADD; GSYM num_congruent] THEN
  DISCH_THEN(MP_TAC o SPEC `(addr2 - addr1 + len2 - 1) MOD n`) THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN ASM_SIMP_TAC[CONG_MOD; LE_1] THEN
  MATCH_MP_TAC(ARITH_RULE
   `d < n ==> a - 1 + b - 1 < d ==> a + b <= n`) THEN
  ASM_SIMP_TAC[DIVISION; LE_1]);;

let NONOVERLAPPING_IMP_SMALL_1 = prove
 (`!n addr1 addr2 len.
        nonoverlapping_modulo n (addr1,len) (addr2,len) /\
        0 < n
        ==> 2 * len <= n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_2)) THEN
  ASM_ARITH_TAC);;

let NONOVERLAPPING_IMP_LT = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) /\
        0 < n /\ 0 < len1 /\ 0 < len2
        ==> len1 < n /\ len2 < n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NONOVERLAPPING_IMP_SMALL_2) THEN
  ASM_ARITH_TAC);;

let NONOVERLAPPING_IMP_LE = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) /\
        0 < n /\ 0 < len1 /\ 0 < len2
        ==> len1 <= n /\ len2 <= n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NONOVERLAPPING_IMP_SMALL_2) THEN
  ASM_ARITH_TAC);;

let NONOVERLAPPING_IMP_SMALL_RIGHT = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) /\ 0 < n /\ 0 < len1
        ==> len2 <= n`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `l <= n <=> (0 < l ==> l <= n)`] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NONOVERLAPPING_IMP_SMALL_2) THEN
  ARITH_TAC);;

let NONOVERLAPPING_IMP_SMALL_LEFT = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) /\ 0 < n /\ 0 < len2
        ==> len1 <= n`,
  ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
  MESON_TAC[NONOVERLAPPING_IMP_SMALL_RIGHT]);;

let NONOVERLAPPING_IMP_SMALL_RIGHT_ALT = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) /\
        0 < n /\ 0 < len1 /\ len1 <= n
        ==> len1 + len2 <= n`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(ARITH_RULE `len2 = 0 \/ 0 < len2`) THEN
  ASM_SIMP_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_2 THEN ASM_MESON_TAC[]);;

let NONOVERLAPPING_IMP_SMALL_LEFT_ALT = prove
 (`!n addr1 len1 addr2 len2.
        nonoverlapping_modulo n (addr1,len1) (addr2,len2) /\
        0 < n /\ 0 < len2 /\ len2 <= n
        ==> len1 + len2 <= n`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM; ADD_SYM] THEN
  REWRITE_TAC[NONOVERLAPPING_IMP_SMALL_RIGHT_ALT]);;

(* ------------------------------------------------------------------------- *)
(* These are some rather (over?)-special lemmas where we assume things fit   *)
(* into the memory range without wrapping round.                             *)
(* ------------------------------------------------------------------------- *)

let NONOVERLAPPING_MODULO_SIMPLE = prove
 (`!n a1 a2 l1 l2.
        a1 + l1 <= a2 /\ a2 + l2 <= a1 + n \/
        a2 + l2 <= a1 /\ a1 + l1 <= a2 + n
        ==> nonoverlapping_modulo n (a1,l1) (a2,l2)`,
  REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN  `a1:num <= a2` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC];
    SUBGOAL_THEN  `a2:num <= a1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]] THEN
  REWRITE_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[nonoverlapping_modulo; GSYM ADD_ASSOC; CONG_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[NOT_EXISTS_THM; CONG] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `~(i = j) /\  j MOD n = j /\ i MOD n = i==> ~(j MOD n = i MOD n)`) THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC MOD_LT) THEN ASM_ARITH_TAC);;

let NONOVERLAPPING_MODULO_OFFSET_SIMPLE_RIGHT = prove
 (`!n a k l1 l2.
        l1 <= k /\ k + l2 <= n ==> nonoverlapping_modulo n (a,l1) (a+k,l2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  ASM_ARITH_TAC);;

let NONOVERLAPPING_MODULO_OFFSET_SIMPLE_LEFT = prove
 (`!n a k l1 l2.
        l2 <= k /\ k + l1 <= n ==> nonoverlapping_modulo n (a+k,l1) (a,l2)`,
  ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
  REWRITE_TAC[NONOVERLAPPING_MODULO_OFFSET_SIMPLE_RIGHT]);;

let NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH = prove
 (`!n a k m l1 l2.
        k + l1 <= m /\ m + l2 <= k + n \/
        m + l2 <= k /\ k + l1 <= m + n
        ==> nonoverlapping_modulo n (a+k,l1) (a+m,l2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NONOVERLAPPING_MODULO_OFFSET_LEFT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONOVERLAPPING_MODULO_SIMPLE THEN
  ASM_ARITH_TAC);;

let CONTAINED_MODULO_SIMPLE = prove
 (`!n a1 a2 l1 l2.
        a2 <= a1 /\ a1 + l1 <= a2 + l2
        ==> contained_modulo n (a1,l1) (a2,l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:num` THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN REWRITE_TAC[contained_modulo] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXISTS_TAC `d + i:num` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ADD_ASSOC; CONG_REFL]]);;

let CONTAINED_MODULO_OFFSET_SIMPLE = prove
 (`!n a k l1 l2.
        k + l1 <= l2 ==> contained_modulo n (a+k,l1) (a,l2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN
  ASM_ARITH_TAC);;

let NONOVERLAPPING_SIMPLE = prove
 (`!pos1 len1 pos2 len2.
        pos1 + len1 <= 2 EXP 64 /\ pos2 + len2 <= 2 EXP 64
        ==> (nonoverlapping_modulo (2 EXP 64) (pos1,len1) (pos2,len2) <=>
             len1 = 0 \/ len2 = 0 \/
              pos1 + len1 <= pos2 \/ pos2 + len2 <= pos1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nonoverlapping_modulo; CONG] THEN
  MATCH_MP_TAC(SET_RULE
   `((!i. P i ==> (f i) MOD p = f i) /\ (!j. Q j ==> (g j) MOD p = g j)) /\
    (DISJOINT (IMAGE f {i | P i}) (IMAGE g {j | Q j}) <=> R)
    ==> (~(?i j. P i /\ Q j /\ (f i) MOD p = (g j) MOD p) <=> R)`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `len1 = 0` THEN
  ASM_SIMP_TAC[CONJUNCT1 LT; EMPTY_GSPEC; DISJOINT_EMPTY; IMAGE_CLAUSES] THEN
  ASM_CASES_TAC `len2 = 0` THEN
  ASM_SIMP_TAC[CONJUNCT1 LT; EMPTY_GSPEC; DISJOINT_EMPTY; IMAGE_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(l = 0) ==> (i < l <=> 0 <= i /\ i <= l - 1)`] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM numseg; GSYM NUMSEG_OFFSET_IMAGE] THEN
  REWRITE_TAC[DISJOINT_NUMSEG] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Word-based versions of containment and nonoverlap, with nicer theorems.   *)
(* ------------------------------------------------------------------------- *)

let nonoverlapping = new_definition
 `nonoverlapping (base1:N word,len1) (base2:N word,len2) <=>
        nonoverlapping_modulo (2 EXP dimindex(:N))
                              (val base1,len1) (val base2,len2)`;;

let contained = new_definition
 `contained (base1:N word,len1) (base2:N word,len2) <=>
        contained_modulo (2 EXP dimindex(:N))
                         (val base1,len1) (val base2,len2)`;;

let NONOVERLAPPING = prove
 (`!(base1:N word) base2 len1 len2.
        nonoverlapping (base1,len1) (base2,len2) <=>
        ~(?i j. i < len1 /\ j < len2 /\
                word_add base1 (word i) = word_add base2 (word j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping; nonoverlapping_modulo] THEN
  REWRITE_TAC[GSYM WORD_EQ; WORD_ADD; WORD_VAL]);;

let CONTAINED = prove
 (`!(base1:N word) base2 len1 len2.
        contained (base1,len1) (base2,len2) <=>
        !i. i < len1
            ==> ?j. j < len2 /\
                    word_add base1 (word i) = word_add base2 (word j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contained; contained_modulo] THEN
  REWRITE_TAC[GSYM WORD_EQ; WORD_ADD; WORD_VAL]);;

let NONOVERLAPPING_MODULO = prove
 (`!base1 base2 len1 len2.
      nonoverlapping_modulo (2 EXP dimindex(:N)) (base1,len1) (base2,len2) <=>
      nonoverlapping(word base1:N word,len1) (word base2:N word,len2)`,
  REWRITE_TAC[nonoverlapping; nonoverlapping_modulo] THEN
  REWRITE_TAC[VAL_WORD; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[]);;

let CONTAINED_MODULO = prove
 (`!base1 base2 len1 len2.
      contained_modulo (2 EXP dimindex(:N)) (base1,len1) (base2,len2) <=>
      contained(word base1:N word,len1) (word base2:N word,len2)`,
  REWRITE_TAC[contained; contained_modulo] THEN
  REWRITE_TAC[VAL_WORD; CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[]);;

let NONOVERLAPPING_SYM = prove
 (`!(base1:N word) base2 len1 len2.
        nonoverlapping (base1,len1) (base2,len2) <=>
        nonoverlapping (base2,len2) (base1,len1)`,
  REWRITE_TAC[nonoverlapping; NONOVERLAPPING_MODULO_SYM]);;

let CONTAINED_TRIVIAL = prove
 (`!(base1:N word) base2 len2. contained (base1,0) (base2,len2)`,
  REWRITE_TAC[contained; CONTAINED_MODULO_TRIVIAL]);;

let NONOVERLAPPING_TRIVIAL = prove
 (`!(base1:N word) base2 len1 len2.
        len1 = 0 \/ len2 = 0
         ==> nonoverlapping (base1,len1) (base2,len2)`,
  SIMP_TAC[nonoverlapping; NONOVERLAPPING_MODULO_TRIVIAL]);;

let NONOVERLAPPING_SUBREGIONS = prove
 (`!(base1:N word) len1 base2 len2 base1' len1' base2' len2'.
        nonoverlapping (base1,len1) (base2,len2) /\
        contained (base1',len1') (base1,len1) /\
        contained (base2',len2') (base2,len2)
        ==> nonoverlapping (base1',len1') (base2',len2')`,
  REWRITE_TAC[nonoverlapping; contained; NONOVERLAPPING_MODULO_SUBREGIONS]);;

let NONOVERLAPPING_QFREE = prove
 (`!(base1:N word) base2 len1 len2.
        nonoverlapping (base1,len1) (base2,len2) <=>
        0 < len1 /\ 0 < len2
        ==> len2 <= val(word_sub base1 base2) /\
            val(word_sub base1 base2) + len1 <= 2 EXP dimindex(:N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING] THEN
  REWRITE_TAC[WORD_RULE
   `word_add b x:N word = word_add c y <=> word_sub y x = word_sub b c`] THEN
  SPEC_TAC(`word_sub base1 base2:N word`,`d:N word`) THEN GEN_TAC THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_SIMP_TAC[CONJUNCT1 LT; LE_1] THEN
  ASM_CASES_TAC `len2 = 0` THEN ASM_SIMP_TAC[CONJUNCT1 LT; LE_1] THEN
  REWRITE_TAC[WORD_RULE `word_sub a b:N word = c <=> a = word_add c b`] THEN
  REWRITE_TAC[WORD_VAL_GALOIS; RIGHT_EXISTS_AND_THM] THEN
  MP_TAC(SPEC `2 EXP dimindex(:N)` (MESON[MOD_LE; LET_TRANS; MOD_LT; MOD_LT_EQ]
   `!n P len. ~(n = 0)
             ==> ((?i. i < len /\ P(i MOD n)) <=>
                  (?i. i < n /\ i < len /\ P i))`)) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[UNWIND_THM2; VAL_BOUND; ARITH_RULE
     `j:num < a /\ j < b /\ j = c <=> j = c /\ c < a /\ c < b`] THEN
  ASM_CASES_TAC `len2 < 2 EXP dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[VAL_BOUND; NOT_LT; LE_1; LTE_TRANS]] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD] THEN CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[GSYM NOT_LT; GSYM DE_MORGAN_THM] THEN
  AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC `val(d:N word) + i < 2 EXP dimindex(:N)` THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC;
    STRIP_TAC THENL
     [EXISTS_TAC `0` THEN ASM_SIMP_TAC[ADD_CLAUSES; VAL_MOD_REFL; LE_1];
      EXISTS_TAC `2 EXP dimindex(:N) - val(d:N word)` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[VAL_BOUND; ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
      ASM_SIMP_TAC[MOD_REFL; LE_1]]]);;

let NONOVERLAPPING_QFREE' = prove
 (`!(base1:N word) base2 len1 len2.
        nonoverlapping (base1,len1) (base2,len2) <=>
        0 < len1 /\ 0 < len2
        ==> len2 <= val(word_sub base1 base2) /\
            len1 <= val(word_sub base2 base1)`,
  REWRITE_TAC[NONOVERLAPPING_QFREE] THEN WORD_ARITH_TAC);;

let CONTAINED_QFREE = prove
 (`!(base1:N word) base2 len1 len2.
        contained (base1,len1) (base2,len2) <=>
        0 < len1 /\ len2 < 2 EXP dimindex(:N)
        ==> val(word_sub base1 base2) + len1 <= len2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTAINED] THEN
  REWRITE_TAC[WORD_RULE
   `word_add b x:N word = word_add c y <=> word_sub y x = word_sub b c`] THEN
  SPEC_TAC(`word_sub base1 base2:N word`,`d:N word`) THEN GEN_TAC THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_SIMP_TAC[CONJUNCT1 LT; LE_1] THEN
  REWRITE_TAC[WORD_RULE `word_sub a b:N word = c <=> a = word_add c b`] THEN
  REWRITE_TAC[WORD_VAL_GALOIS] THEN
  MP_TAC(SPEC `2 EXP dimindex(:N)` (MESON[MOD_LE; LET_TRANS; MOD_LT; MOD_LT_EQ]
   `!n P len. ~(n = 0)
             ==> ((?i. i < len /\ P(i MOD n)) <=>
                  (?i. i < n /\ i < len /\ P i))`)) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[UNWIND_THM2; VAL_BOUND; ARITH_RULE
     `j:num < a /\ j < b /\ j = c <=> j = c /\ c < a /\ c < b`] THEN
  ASM_CASES_TAC `len2 < 2 EXP dimindex(:N)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC; ASM_MESON_TAC[VAL_BOUND; NOT_LT; LTE_TRANS]] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD] THEN CONV_TAC MOD_DOWN_CONV THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC
     `MIN len1 (2 EXP dimindex(:N) - val(d:N word)) - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o lhand o snd) THEN
    MP_TAC(ISPEC `d:N word` VAL_BOUND) THEN ASM_ARITH_TAC;
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH lhand MOD_LE o lhand o snd) THEN ASM_ARITH_TAC]);;

let NONOVERLAPPING_SIMPLE_LEFT = prove
 (`!(base:N word) off1 off2 len1 len2.
      (0 < len1 /\ 0 < len2
       ==> &len2 <= off1 - off2 /\ (off1 - off2) + &len1 <= &2 pow dimindex(:N))
      ==> nonoverlapping (word_add base (iword off1),len1)
                         (word_add base (iword off2),len2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_SIMP_TAC[NONOVERLAPPING_TRIVIAL; LE_1] THEN
  ASM_CASES_TAC `len2 = 0` THEN ASM_SIMP_TAC[NONOVERLAPPING_TRIVIAL; LE_1] THEN
  REWRITE_TAC[NONOVERLAPPING_QFREE; WORD_RULE
  `word_sub (word_add b (iword x)) (word_add b (iword y)) = iword(x - y)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MESON[INT_POS; INT_LE_TRANS]
    `&len:int <= y <=> &0 <= y /\ &len <= y`] THEN
  SPEC_TAC(`off1 - off2:int`,`y:int`) THEN
  REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GSYM WORD_IWORD] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `val(word n:N word) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  INT_ARITH_TAC);;

let NONOVERLAPPING_SIMPLE = prove
 (`!(base:N word) off1 off2 len1 len2.
       (0 < len1 /\ 0 < len2
        ==> &len2 <= off1 - off2 /\
            (off1 - off2) + &len1 <= &2 pow dimindex(:N) \/
            &len1 <= off2 - off1 /\
            (off2 - off1) + &len2 <= &2 pow dimindex(:N))
        ==> nonoverlapping (word_add base (iword off1),len1)
                           (word_add base (iword off2),len2)`,
  MESON_TAC[NONOVERLAPPING_SIMPLE_LEFT; NONOVERLAPPING_SYM]);;

let NONOVERLAPPING_SIMPLE_64 =
  CONV_RULE INT_REDUCE_CONV
   (REWRITE_RULE[DIMINDEX_64] (INST_TYPE [`:64`,`:N`] NONOVERLAPPING_SIMPLE));;

let CONTAINED_SIMPLE = prove
 (`!(base:N word) off1 off2 len1 len2.
        (0 < len1 ==> &0 <= off1 - off2 /\ (off1 - off2) + &len1 <= &len2)
        ==> contained (word_add base (iword off1),len1)
                      (word_add base (iword off2),len2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `len1 = 0` THEN ASM_SIMP_TAC[CONTAINED_TRIVIAL; LE_1] THEN
  REWRITE_TAC[CONTAINED_QFREE; WORD_RULE
  `word_sub (word_add b (iword x)) (word_add b (iword y)) = iword(x - y)`] THEN
  SPEC_TAC(`off1 - off2:int`,`y:int`) THEN
  REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GSYM WORD_IWORD] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE
   `val(word n:N word) <= n /\ n + l1 <= l2
    ==> val(word n:N word) + l1 <= l2`) THEN
  SIMP_TAC[VAL_WORD_LE; LE_REFL] THEN ASM_ARITH_TAC);;

let CONTAINED_SIMPLE_64 = INST_TYPE [`:64`,`:N`] CONTAINED_SIMPLE;;

let NONOVERLAPPING_CLAUSES_GEN = prove
 (`(nonoverlapping (word n1:N word,l1) (a2,l2) <=>
        nonoverlapping_modulo (2 EXP dimindex(:N))
          (n1,l1) (val a2,l2)) /\
   (nonoverlapping (a1:N word,l1) (word n2:N word,l2) <=>
        nonoverlapping_modulo (2 EXP dimindex(:N))
          (val a1,l1) (n2,l2)) /\
   (nonoverlapping (a1:N word,l1) (a2,l2) <=>
        nonoverlapping_modulo (2 EXP dimindex(:N))
          (val a1,l1) (val a2,l2)) /\
   (nonoverlapping_modulo (2 EXP dimindex(:N))
      (val(word n1:N word),l1) (n2,l2) <=>
        nonoverlapping_modulo (2 EXP dimindex(:N))
          (n1,l1) (n2,l2)) /\
   (nonoverlapping_modulo (2 EXP dimindex(:N))
      (n1,l1) (val(word n2:N word),l2) <=>
        nonoverlapping_modulo (2 EXP dimindex(:N))
          (n1,l1) (n2,l2))`,
  REWRITE_TAC[nonoverlapping; VAL_WORD] THEN
  REWRITE_TAC[NONOVERLAPPING_MODULO_LMOD; NONOVERLAPPING_MODULO_RMOD]);;

let NONOVERLAPPING_CLAUSES =
  CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV)
    (INST_TYPE [`:64`,`:N`] NONOVERLAPPING_CLAUSES_GEN);;
