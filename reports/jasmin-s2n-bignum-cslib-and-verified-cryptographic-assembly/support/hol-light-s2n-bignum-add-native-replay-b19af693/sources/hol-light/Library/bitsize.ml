(* ========================================================================= *)
(* Definition of "bitsize", how many bits are needed for a natural number.   *)
(* ========================================================================= *)

let bitsize = new_definition
 `bitsize n = minimal i. n < 2 EXP i`;;

let BITSIZE_0 = prove
 (`bitsize 0 = 0`,
  REWRITE_TAC[bitsize] THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN ARITH_TAC);;

let BITSIZE_POW2 = prove
 (`!k. bitsize (2 EXP k) = k + 1`,
  GEN_TAC THEN REWRITE_TAC[bitsize; LT_EXP] THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN ARITH_TAC);;

let BITSIZE_1 = prove
 (`bitsize 1 = 1`,
  MP_TAC(SPEC `0` BITSIZE_POW2) THEN CONV_TAC NUM_REDUCE_CONV);;

let BITSIZE_2 = prove
 (`bitsize 2 = 2`,
  MP_TAC(SPEC `1` BITSIZE_POW2) THEN CONV_TAC NUM_REDUCE_CONV);;

let BITSIZE_LE = prove
 (`!n k. bitsize n <= k <=> n < 2 EXP k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitsize] THEN
  SIMP_TAC[MINIMAL_LE; MESON[LT_POW2_REFL] `?i. n < 2 EXP i`] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[LE_REFL]] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP; ARITH_EQ]);;

let BITSIZE = prove
 (`!n. n < 2 EXP bitsize n`,
  REWRITE_TAC[GSYM BITSIZE_LE; LE_REFL]);;

let BITSIZE_UNIQUE = prove
 (`!n k. bitsize n = k <=> n < 2 EXP k /\ !j. j < k ==> 2 EXP j <= n`,
  REWRITE_TAC[GSYM NOT_LT; GSYM BITSIZE_LE] THEN
  MESON_TAC[LT_ANTISYM; LT_CASES; LT_TRANS]);;

let BITSIZE_UNIQUE_ALT = prove
 (`!n k. bitsize n = k <=> !j. n < 2 EXP j <=> k <= j`,
  REWRITE_TAC[BITSIZE_UNIQUE] THEN
  MESON_TAC[NOT_LE; LE_EXP; ARITH_RULE `~(2 = 0)`; LE_TRANS; LE_ANTISYM]);;

let BITSIZE_EQ_0 = prove
 (`!n. bitsize n = 0 <=> n = 0`,
  REWRITE_TAC[BITSIZE_UNIQUE; LT] THEN ARITH_TAC);;

let BITSIZE_MONO = prove
 (`!m n. m <= n ==> bitsize m <= bitsize n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BITSIZE_LE] THEN
  TRANS_TAC LET_TRANS `n:num` THEN ASM_REWRITE_TAC[BITSIZE]);;

let BITSIZE_MAX = prove
 (`!m n. bitsize(MAX m n) = MAX (bitsize m) (bitsize n)`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(ARITH_RULE `m:num <= n \/ n <= m`) THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> MAX m n = n`; BITSIZE_MONO;
               ARITH_RULE `n <= m ==> MAX m n = m`]);;

let BITSIZE_MIN = prove
 (`!m n. bitsize(MIN m n) = MIN (bitsize m) (bitsize n)`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(ARITH_RULE `m:num <= n \/ n <= m`) THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> MIN m n = m`; BITSIZE_MONO;
               ARITH_RULE `n <= m ==> MIN m n = n`]);;

let BITSIZE_MULT_LE = prove
 (`!m n. bitsize(m * n) <= bitsize m + bitsize n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BITSIZE_LE; EXP_ADD] THEN
  MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC[BITSIZE]);;

let BITSIZE_REV_EQ = prove
 (`!n. 2 EXP (bitsize n - 1) <= n <=> ~(n = 0)`,
  REWRITE_TAC[GSYM NOT_LT; GSYM BITSIZE_LE] THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`; BITSIZE_EQ_0]);;

let BITSIZE_REV = prove
 (`!n. ~(n = 0) ==> 2 EXP (bitsize n - 1) <= n`,
  REWRITE_TAC[BITSIZE_REV_EQ]);;

let BITSIZE_REV_EQ_ALT = prove
 (`!n. 2 EXP (bitsize n) <= 2 * n <=> ~(n = 0)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[BITSIZE_0; ARITH] THEN
  TRANS_TAC LE_TRANS `2 * 2 EXP (bitsize n - 1)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL; BITSIZE_REV_EQ] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  MATCH_MP_TAC EQ_IMP_LE THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE `n = SUC(n - 1) <=> ~(n = 0)`; BITSIZE_EQ_0]);;

let BITSIZE_REV_ALT = prove
 (`!n. ~(n = 0) ==> 2 EXP bitsize n <= 2 * n`,
  REWRITE_TAC[BITSIZE_REV_EQ_ALT]);;

let LE_BITSIZE = prove
 (`!n k. k <= bitsize n <=> ~(k = 0) ==> 2 EXP (k - 1) <= n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[LE_0; ARITH] THEN
  REWRITE_TAC[GSYM NOT_LT; GSYM BITSIZE_LE] THEN ASM_ARITH_TAC);;

let LE_BITSIZE_ALT = prove
 (`!n k. k <= bitsize n <=> ~(k = 0) ==> 2 EXP k <= 2 * n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_BITSIZE] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 * a = b ==> (a <= n <=> b <= 2 * n)`) THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let BITSIZE_UNIQUE_EQ = prove
 (`!n k. bitsize n = k <=>
         n < 2 EXP k /\ (~(k = 0) ==> 2 EXP k <= 2 * n)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV
   [ARITH_RULE `n = k <=> k <= n /\ ~(k + 1 <= n)`] THEN
  REWRITE_TAC[LE_BITSIZE_ALT; EXP_ADD] THEN ARITH_TAC);;

let BITSIZE_MULT = prove
 (`(!k n. bitsize (2 EXP k * n) = if n = 0 then 0 else k + bitsize n) /\
   (!k n. bitsize (n * 2 EXP k) = if n = 0 then 0 else bitsize n + k)`,
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_SYM; ADD_SYM]; REPEAT GEN_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; BITSIZE_0] THEN
  REWRITE_TAC[GSYM LE_ANTISYM; LE_BITSIZE_ALT; BITSIZE_LE] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 * a * b = a * 2 * b`] THEN
  REWRITE_TAC[EXP_ADD; LT_MULT_LCANCEL; LE_MULT_LCANCEL] THEN
  ASM_REWRITE_TAC[BITSIZE; EXP_EQ_0; ARITH_EQ; BITSIZE_REV_EQ_ALT]);;

let BITSIZE_MULT_ADD = prove
 (`(!k m n. ~(m = 0) /\ n < 2 EXP k
            ==> bitsize (2 EXP k * m + n) = k + bitsize m) /\
   (!k m n. ~(m = 0) /\ n < 2 EXP k
            ==> bitsize (m * 2 EXP k + n) = k + bitsize m) /\
   (!k m n. ~(m = 0) /\ n < 2 EXP k
            ==> bitsize (n + 2 EXP k * m) = k + bitsize m) /\
   (!k m n. ~(m = 0) /\ n < 2 EXP k
            ==> bitsize (n + m * 2 EXP k) = k + bitsize m)`,
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_SYM; ADD_SYM; DISJ_SYM]; REPEAT STRIP_TAC] THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [REWRITE_TAC[BITSIZE_LE] THEN TRANS_TAC LTE_TRANS `2 EXP k * (m + 1)` THEN
    REWRITE_TAC[EXP_ADD; LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `m + 1 <= r <=> m < r`; BITSIZE] THEN
    ASM_ARITH_TAC;
    TRANS_TAC LE_TRANS `bitsize(2 EXP k * m)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[BITSIZE_MULT; LE_REFL];
      MATCH_MP_TAC BITSIZE_MONO THEN ARITH_TAC]]);;

let BITSIZE_DIV = prove
 (`!n k. bitsize(n DIV 2 EXP k) = bitsize n - k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BITSIZE_UNIQUE] THEN
  SIMP_TAC[RDIV_LT_EQ; LE_RDIV_EQ;  EXP_EQ_0; ARITH_EQ] THEN
  ASM_CASES_TAC `bitsize n <= k` THENL
   [ASM_SIMP_TAC[ARITH_RULE `n <= k ==> n - k = 0`] THEN
    REWRITE_TAC[CONJUNCT1 LT; MULT_CLAUSES; EXP] THEN
    TRANS_TAC LTE_TRANS `2 EXP bitsize n` THEN
    ASM_REWRITE_TAC[BITSIZE; LE_EXP] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[GSYM EXP_ADD; BITSIZE;
                 ARITH_RULE `~(n:num <= k) ==> k + n - k = n`] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n:num <= k) ==> (j < n - k <=> k + j < n)`] THEN
    REWRITE_TAC[ARITH_RULE `a < b <=> a + 1 <= b`; LE_BITSIZE] THEN
    REWRITE_TAC[ADD_SUB; ADD_EQ_0; ARITH_EQ]]);;

let BITSIZE_CONV =
  let rec bitfun k n =
    if n =/ num_0 then k
    else bitfun (k + 1) (quo_num n num_2) in
  fun tm ->
   (match tm with
      Comb(Const("bitsize",_),ntm) when is_numeral ntm ->
        let ktm = mk_small_numeral(bitfun 0 (dest_numeral ntm)) in
        let th = SPECL [ntm;ktm] BITSIZE_UNIQUE_EQ in
        EQT_ELIM(CONV_RULE (RAND_CONV NUM_REDUCE_CONV) th)
    | _ -> failwith "BITSIZE_CONV");;
