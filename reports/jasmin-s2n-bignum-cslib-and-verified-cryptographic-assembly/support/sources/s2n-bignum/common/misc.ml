(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Miscellaneous theorems that don't quite fit in the main libraries.        *)
(* ========================================================================= *)

needs "Library/bitsize.ml";;
needs "Library/floor.ml";;
needs "Library/iter.ml";;
needs "Library/pocklington.ml";;
needs "Library/rstc.ml";;
needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Additional list lemmas, operations and conversions.                       *)
(* ------------------------------------------------------------------------- *)

let LIST_OF_SEQ_CLAUSES = prove
 (`(!(f:num->A). list_of_seq f 0 = []) /\
   (!(f:num->A). list_of_seq f 1 = [f 0]) /\
   (!(f:num->A). list_of_seq f 2 = [f 0; f 1]) /\
   (!(f:num->A). list_of_seq f 3 = [f 0; f 1; f 2]) /\
   (!(f:num->A). list_of_seq f 4 = [f 0; f 1; f 2; f 3])`,
  CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN REWRITE_TAC[]);;

let SUB_LIST = define
 `SUB_LIST (0,0) l = [] /\
  SUB_LIST (SUC m,n) [] = [] /\
  SUB_LIST (0,SUC n) [] = [] /\
  SUB_LIST (0,SUC n) (CONS h t) = CONS h (SUB_LIST (0,n) t) /\
  SUB_LIST (SUC m,n) (CONS h t) = SUB_LIST (m,n) t`;;

let SUB_LIST_CLAUSES = prove
 (`SUB_LIST (m,0) (l:A list) = [] /\
   SUB_LIST (m,n) [] = [] /\
   SUB_LIST (SUC m,n) (CONS h t) = SUB_LIST (m,n) t /\
   SUB_LIST (0,SUC n) (CONS h t) = CONS h (SUB_LIST (0,n) t)`,
  REWRITE_TAC[SUB_LIST] THEN CONJ_TAC THENL
   [ALL_TAC; METIS_TAC[SUB_LIST; num_CASES]] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`l:A list`; `m:num`] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST]);;

let SUB_LIST_LENGTH = prove
 (`!l. SUB_LIST(0,LENGTH l) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES; LENGTH]);;

let SUB_LIST_SPLIT = prove
 (`!l m n p. SUB_LIST(p,m+n) l = APPEND (SUB_LIST(p,m) l) (SUB_LIST(p+m,n) l)`,
  LIST_INDUCT_TAC THEN REPEAT
   (INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; ADD_CLAUSES; APPEND]) THEN
  REWRITE_TAC[APPEND_NIL] THEN ASM_MESON_TAC[ADD_CLAUSES]);;

let SUB_LIST_TOPSPLIT = prove
 (`!l n. APPEND (SUB_LIST(0,n) l) (SUB_LIST(n,LENGTH l - n) l) = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES; APPEND] THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; ADD_CLAUSES; APPEND;
                  LENGTH; SUB_0; SUB_SUC; SUB_LIST_LENGTH]);;

let LENGTH_SUB_LIST = prove
 (`!l m n. LENGTH(SUB_LIST(m,n) l) = MIN n (LENGTH l - m)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LENGTH; SUB_0] THEN
  REPEAT
   (INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; ADD_CLAUSES; LENGTH]) THEN
  ARITH_TAC);;

let SUB_LIST_TRIVIAL = prove
 (`!l m n. LENGTH l <= m ==> SUB_LIST(m,n) l = []`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_SUB_LIST] THEN ARITH_TAC);;

let SUB_LIST_IDEMPOTENT = prove(
  `!n (l:(A)list). SUB_LIST (0,n) (SUB_LIST (0,n) l) = SUB_LIST (0,n) l`,
  INDUCT_TAC THENL[
    REWRITE_TAC[SUB_LIST_CLAUSES];

    STRIP_TAC THEN
    DISJ_CASES_TAC (ISPEC `l:(A)list` list_CASES) THENL [
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB_LIST_CLAUSES];
      ALL_TAC
    ] THEN
    FIRST_X_ASSUM MP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_REWRITE_TAC[]
  ]);;

let SUB_LIST_MIN = prove(
  `!(l:(A)list) (n:num) m. SUB_LIST (0,n) (SUB_LIST (0,m) l) = SUB_LIST (0, MIN n m) l`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(m:num) <= n` THENL [
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_LIST_SPLIT;ADD_CLAUSES;ARITH_RULE`MIN ((x:num)+y) x = x`] THEN
    REWRITE_TAC[SUB_LIST_IDEMPOTENT] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM APPEND_NIL] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUB_LIST_TRIVIAL THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC;

    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LE;LT_EXISTS] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_LIST_SPLIT;ADD_CLAUSES;ARITH_RULE`MIN (x:num) (x+y) = x`] THEN
    MAP_EVERY SPEC1_TAC [`n:num`;`l:(A)list`] THEN
    LIST_INDUCT_TAC THENL [
      REWRITE_TAC[APPEND_NIL;SUB_LIST_CLAUSES];

      STRIP_TAC THEN
      DISJ_CASES_TAC (SPEC `n':num` num_CASES) THENL [
        ASM_REWRITE_TAC[SUB_LIST_CLAUSES];

        FIRST_X_ASSUM MP_TAC THEN DISCH_THEN (CHOOSE_THEN SUBST_ALL_TAC) THEN
        REWRITE_TAC[SUB_LIST_CLAUSES;APPEND] THEN
        ASM_REWRITE_TAC[]
      ]
    ]
  ]);;

let SUB_LIST_REFL = prove
 (`!(l:A list) n. LENGTH l <= n ==> SUB_LIST(0,n) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; LE_SUC; LENGTH] THEN
  ARITH_TAC);;

let SUB_LIST_1 = prove
 (`!(l:A list) n. SUB_LIST(n,1) l = if n < LENGTH l then [EL n l] else []`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; SUB_LIST_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:A`; `t:A list`] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LT_0; num_CONV `1`; EL; TL] THEN
  ASM_REWRITE_TAC[GSYM(num_CONV `1`); LT_SUC; HD]);;

let SUB_LIST_APPEND_LEFT = prove
 (`!(l:A list) m n.
        n <= LENGTH l ==> SUB_LIST(0,n) (APPEND l m) = SUB_LIST(0,n) l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; CONJUNCT1 LE; SUB_LIST_CLAUSES] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[SUB_LIST_CLAUSES; APPEND; LE_SUC]);;

let TRIM_LIST = define
 `TRIM_LIST (h,t) l = SUB_LIST (h,LENGTH l - (h + t)) l`;;

let SUB_LIST_CONV =
  let [cth1;cth2;cth3;cth4] = CONJUNCTS SUB_LIST_CLAUSES in
  let conv0 = GEN_REWRITE_CONV I [cth1; cth2]
  and conv1 = GEN_REWRITE_CONV I [cth3]
  and conv2 = GEN_REWRITE_CONV I [cth4] in
  let rec conv tm =
   (conv0 ORELSEC
    (LAND_CONV(LAND_CONV num_CONV) THENC conv1 THENC conv) ORELSEC
    (LAND_CONV(RAND_CONV num_CONV) THENC conv2 THENC RAND_CONV conv)) tm in
  conv;;

let TRIM_LIST_CONV =
  GEN_REWRITE_CONV I [TRIM_LIST] THENC
  LAND_CONV(RAND_CONV
   ((BINOP2_CONV LENGTH_CONV NUM_ADD_CONV) THENC
    NUM_SUB_CONV)) THENC
  SUB_LIST_CONV;;

let CONS_TO_APPEND_CONV (t:term) =
  let elems = ref [] in
  let rec strip_cons (t:term):term = begin
    try
      let the_cons,args = strip_comb t in
      match args with
      | [itm; tail] ->
        if name_of the_cons <> "CONS" then failwith "" else
        elems := itm::!elems;
        strip_cons tail
      | _ -> failwith ""
    with Failure _ -> t
  end in
  let tail = strip_cons t in
  let new_list = mk_list (rev (!elems), type_of (hd !elems)) in
  prove(mk_eq(t, list_mk_icomb "APPEND" [new_list; tail]),
    REWRITE_TAC[APPEND]);;

(* - : thm = |- CONS 1 (CONS 2 e) = APPEND [1; 2] e *)
CONS_TO_APPEND_CONV `CONS 1 (CONS 2 e)`;;

let APPEND_EXISTS = prove(
 `forall (x:(A)list). exists (x1:(A)list) x2. x = APPEND x1 x2`,
    STRIP_TAC THEN EXISTS_TAC `[]:(A)list` THEN MESON_TAC[APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Combined word and number and a few other things reduction.                *)
(* ------------------------------------------------------------------------- *)

let WORD_NUM_RED_CONV =
  WORD_RED_CONV ORELSEC
  NUM_RED_CONV ORELSEC
  INT_RED_CONV ORELSEC
  DIMINDEX_CONV ORELSEC
  GEN_REWRITE_CONV I [BITVAL_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Trivial but requires two distinct library files to be combined.           *)
(* ------------------------------------------------------------------------- *)

let RELPOW_ITER = prove
 (`!f n x y:A. RELPOW n (\a b. f a = b) x y <=> ITER n f x = y`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[RELPOW; ITER] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some specialized lemmas that come up when shifts are masked to 6 bits.    *)
(* ------------------------------------------------------------------------- *)

let MOD_64_CLAUSES = prove
 (`(!c. val(word(c MOD 64):int64) = c MOD 64) /\
   (!c. val(word(c MOD 256):byte) = c MOD 256) /\
   (!c. val(word c:int64) MOD 64 = c MOD 64) /\
   (!n. n MOD 256 MOD 64 = n MOD 64) /\
   (!n. n MOD 64 MOD 64 = n MOD 64) /\
   (!n. n MOD 2 EXP 64 MOD 64 = n MOD 64) /\
   (!n. n MOD 64 MOD 2 EXP 64 = n MOD 64)`,
  REWRITE_TAC[VAL_WORD; DIMINDEX_8; DIMINDEX_64] THEN
  ABBREV_TAC `e = 2 EXP 64` THEN
  REWRITE_TAC[ARITH_RULE `64 = 2 EXP 6 /\ 256 = 2 EXP 8`] THEN
  EXPAND_TAC "e" THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* To undo expansion of the way CSETM is done (should tweak ARM_STEP_TAC?)   *)
(* ------------------------------------------------------------------------- *)

let WORD_UNMASK_64 = prove
 (`(if p then word 18446744073709551615 else word 0):int64 =
   word_neg(word(bitval p)) /\
   (if p then word 0 else word 18446744073709551615):int64 =
   word_neg(word(bitval(~p)))`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Proving equality throwing away some other MSB multiples.                  *)
(* ------------------------------------------------------------------------- *)

let EQUAL_FROM_CONGRUENT_REAL = prove
 (`!n x y z.
        (&0 <= x /\ x < &2 pow n) /\
        (&0 <= y /\ y < &2 pow n) /\
        integer z /\ integer((x - y) / &2 pow n + z)
        ==> x = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`z:real`; `(x - y) / &2 pow n + z:real`]
        REAL_EQ_INTEGERS) THEN
  ASM_REWRITE_TAC[REAL_ARITH `z:real = x + z <=> x = &0`] THEN
  REWRITE_TAC[REAL_ARITH `abs(z - (x + z)):real = abs x`] THEN
  REWRITE_TAC[REAL_DIV_EQ_0; REAL_POW_EQ_0; REAL_SUB_0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN ASM_REAL_ARITH_TAC);;

let EQUAL_FROM_CONGRUENT_MOD = prove
 (`!n x y z.
        &y:real < &2 pow n /\
        integer z /\ integer((&x - &y) / &2 pow n + z)
        ==> x MOD (2 EXP n) = y`,
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; MOD_UNIQUE] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[num_congruent; int_congruent] THEN
  EXISTS_TAC `int_of_real(((&x - &y) / &(2 EXP n) + z) - z)` THEN
  REWRITE_TAC[int_eq; int_mul_th; int_sub_th] THEN
  ASM_SIMP_TAC[REAL_OF_INT_OF_REAL; INTEGER_CLOSED] THEN
  REWRITE_TAC[int_of_num_th; GSYM REAL_OF_NUM_POW] THEN
  CONV_TAC REAL_FIELD);;

let EQUAL_FROM_CONGRUENT_MOD_MOD = prove
 (`!n m r k r'.
        r < 2 EXP k /\ m < 2 EXP k /\ ~(m = 0) /\
        integer((&r - r') / &2 pow k) /\
        &(n MOD m) = r'
        ==> n MOD m = r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
  MP_TAC(SPECL [`(&r - r') / &2 pow k`; `&0`] REAL_EQ_INTEGERS_IMP) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_SUB_RZERO] THEN
  ANTS_TAC THENL [ALL_TAC; CONV_TAC REAL_FIELD] THEN
  SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_POW;
           REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x < e /\ &0 <= y /\ y < e ==> abs(x - y) < &1 * e`) THEN
  EXPAND_TAC "r'" THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LT_TRANS; MOD_LT_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Definition of limbs = general (power of 2 size) digits.                   *)
(* ------------------------------------------------------------------------- *)

let limb = new_definition
 `limb w n i = (n DIV (2 EXP (w * i)) MOD (2 EXP w))`;;

let LIMB_0 = prove
 (`!w i. limb w 0 i = 0`,
  REWRITE_TAC[limb; DIV_0; MOD_0]);;

let LIMB_BOUND = prove
 (`!w n i. limb w n i < 2 EXP w`,
  REWRITE_TAC[limb; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let DIGITSUM_WORDS_LIMB_GEN = prove
 (`!w n k. nsum {i | i < k} (\i. 2 EXP (w * i) * limb w n i) =
           n MOD (2 EXP (w * k))`,
  REWRITE_TAC[limb; EXP_MULT; DIGITSUM_WORKS_GEN]);;

let DIGITSUM_WORKS_LIMB = prove
 (`!w n k. n < 2 EXP (w * k)
           ==> nsum {i | i < k} (\i. 2 EXP (w * i) * limb w n i) = n`,
  REWRITE_TAC[limb; EXP_MULT; DIGITSUM_WORKS]);;

let LIMB_DIGITSUM = prove
 (`!w n k d.
        (!i. i < k ==> d i < 2 EXP w)
        ==> limb w (nsum {i | i < k} (\i. 2 EXP (w * i) * d i)) n =
            if n < k then d n else 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[limb; EXP_MULT] THEN
  ASM_SIMP_TAC[DIGITSUM_DIV_MOD; IN_ELIM_THM; FINITE_NUMSEG_LT]);;

(* ------------------------------------------------------------------------- *)
(* More digit sum lemmas, not needed for Asm/words.ml itself so here.        *)
(* ------------------------------------------------------------------------- *)

let DIGITSUM_LT_STEP = prove
 (`!B b k n.
     0 < B /\ (!i. i < k ==> b i < B)
     ==> (nsum {i | i < k} (\i. B EXP i * b i) < B EXP n <=>
          k <= n \/
          b n = 0 /\ nsum {i | i < k} (\i. B EXP i * b i) < B EXP (n + 1))`,
  REPEAT GEN_TAC THEN SIMP_TAC[LE_1; GSYM DIV_EQ_0; EXP_LT_0] THEN
  SIMP_TAC[DIGITSUM_DIV; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{i | P i /\ Q i} = {i | i IN {j | P j} /\ Q i}`] THEN
  SIMP_TAC[NSUM_EQ_0_IFF; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[ARITH_RULE `0 < b <=> ~(b = 0)`; EXP_EQ_0; MULT_EQ_0] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MP_TAC(ARITH_RULE `!i. n <= i <=> i = n \/ n + 1 <= i`) THEN
  MESON_TAC[LT_REFL; NOT_LE; LE_TRANS; LT_TRANS; LET_TRANS]);;

let VAL_BOUND_64 = prove
 (`!x:int64. val x < 2 EXP 64`,
  GEN_TAC THEN MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64]);;

let VAL_BOUND_128 = prove
  (`!x:int128. val x < 2 EXP 128`,
   GEN_TAC THEN MP_TAC(ISPEC `x:int128` VAL_BOUND) THEN
   REWRITE_TAC[DIMINDEX_128]);;

(* TODO: move to HOL Light *)
new_type_abbrev("int256",`:(256)word`);;

let VAL_BOUND_256 = prove
  (`!x:int256. val x < 2 EXP 256`,
   GEN_TAC THEN MP_TAC(ISPEC `x:int256` VAL_BOUND) THEN
   REWRITE_TAC[DIMINDEX_256]);;

let LEXICOGRAPHIC_LT = prove
 (`!B h l h' l':num.
        l < B /\ l' < B
        ==> (B * h + l < B * h' + l' <=> h < h' \/ h = h' /\ l < l')`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `h:num = h'` THEN
  ASM_REWRITE_TAC[LT_ADD_LCANCEL; LT_REFL] THEN MATCH_MP_TAC(ARITH_RULE
   `~(x = y) /\
   (x < y ==> a + e * x < b + e * y) /\ (y < x ==> b + e * y < a + e * x)
    ==> (e * x + a:num < e * y + b <=> x < y)`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN  MATCH_MP_TAC(ARITH_RULE
   `a < e /\ b < e /\ (x < y ==> e * (x + 1) <= e * y)
    ==> x < y ==> a + e * x < b + e * y`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC);;

let LEXICOGRAPHIC_LE = prove
 (`!B h l h' l':num.
        l < B /\ l' < B
        ==> (B * h + l <= B * h' + l' <=> h < h' \/ h = h' /\ l <= l')`,
  SIMP_TAC[GSYM NOT_LT; LEXICOGRAPHIC_LT] THEN ARITH_TAC);;

let LEXICOGRAPHIC_EQ = prove
 (`!B h l h' l':num.
        l < B /\ l' < B
        ==> (B * h + l = B * h' + l' <=> h = h' /\ l = l')`,
  SIMP_TAC[GSYM LE_ANTISYM; LEXICOGRAPHIC_LE] THEN ARITH_TAC);;

let LEXICOGRAPHIC_LT_64 = prove
 (`!h l h' l'.
        l < 2 EXP 64 /\ l' < 2 EXP 64
        ==> (2 EXP 64 * h + l < 2 EXP 64 * h' + l' <=>
             h < h' \/ h = h' /\ l < l')`,
  REWRITE_TAC[LEXICOGRAPHIC_LT]);;

let LEXICOGRAPHIC_LE_64 = prove
 (`!h l h' l'.
        l < 2 EXP 64 /\ l' < 2 EXP 64
        ==> (2 EXP 64 * h + l <= 2 EXP 64 * h' + l' <=>
             h < h' \/ h = h' /\ l <= l')`,
  REWRITE_TAC[LEXICOGRAPHIC_LE]);;

let LEXICOGRAPHIC_EQ_64 = prove
 (`!h l h' l'.
        l < 2 EXP 64 /\ l' < 2 EXP 64
        ==> (2 EXP 64 * h + l = 2 EXP 64 * h' + l' <=> h = h' /\ l = l')`,
  REWRITE_TAC[LEXICOGRAPHIC_EQ]);;

let LEXICOGRAPHIC_LT_INT64 = prove
 (`!h (l:int64) h' (l':int64).
        2 EXP 64 * h + val l < 2 EXP 64 * h' + val l' <=>
        h < h' \/ h = h' /\ val l < val l'`,
  SIMP_TAC[LEXICOGRAPHIC_LT_64; VAL_BOUND_64]);;

let LEXICOGRAPHIC_LE_INT64 = prove
 (`!h (l:int64) h' (l':int64).
        2 EXP 64 * h + val l <= 2 EXP 64 * h' + val l' <=>
        h < h' \/ h = h' /\ val l <= val l'`,
  SIMP_TAC[LEXICOGRAPHIC_LE_64; VAL_BOUND_64]);;

let LEXICOGRAPHIC_EQ_INT64 = prove
 (`!h (l:int64) h' (l':int64).
        2 EXP 64 * h + val l = 2 EXP 64 * h' + val l' <=> h = h' /\ l = l'`,
  SIMP_TAC[GSYM VAL_EQ; LEXICOGRAPHIC_EQ_64; VAL_BOUND_64]);;

(* ------------------------------------------------------------------------- *)
(* More word lemmas.                                                         *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_EQUAL_SUBWORD_THEN_ZX = prove
  (`!(x:N word) (pos:num) (len1:num) (len2:num).
    len1 >= len2 /\ len1 <= dimindex(:P) /\ len2 = dimindex(:M)
    ==> ((word_subword x (pos,len2)):M word) =
    word_zx ((word_subword x (pos,len1)):P word)`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_ZX] THEN
    REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC );;

let WORD_SUBWORD_N_EQUAL = prove
  (`!(x:N word). (word_subword x (0,dimindex (:N))) = x`,
    REWRITE_TAC[word_subword] THEN
    ASM_REWRITE_TAC(map ARITH_RULE [`2 EXP 0=1`;`x DIV 1=x`]) THEN
    IMP_REWRITE_TAC[MOD_LT] THEN
    REWRITE_TAC[WORD_VAL; VAL_BOUND]
  );;

let WORD_SUBWORD_EQUAL_WORD_ZX_POS0 = prove
  (`!(x:N word) (len:num).
    len = dimindex(:M) /\ len <= dimindex(:N)
    ==> ((word_subword x (0,len)):M word) = word_zx x`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `((word_subword (x:N word) (0,len)):M word) =
      ((word_zx ((word_subword x (0,dimindex(:N))):N word)):M word)`
    ASSUME_TAC THENL
    [MATCH_MP_TAC(ISPECL [`x:N word`;`0:num`;`(dimindex(:N):num)`;`len:num`]
              WORD_SUBWORD_EQUAL_SUBWORD_THEN_ZX) THEN
     ASM_REWRITE_TAC[] THEN
     ASM_ARITH_TAC THEN
     ASM_REWRITE_TAC[WORD_SUBWORD_N_EQUAL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[WORD_SUBWORD_N_EQUAL]
    );;

(* ------------------------------------------------------------------------- *)
(* More word lemmas needing a few other theories so not in library.          *)
(* ------------------------------------------------------------------------- *)

let WORD_CTZ_INDEX = prove
 (`!x:N word.
        word_ctz x = if x = word 0 then dimindex(:N) else index 2 (val x)`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_CTZ_0] THEN
  MATCH_MP_TAC(MESON[LE_ANTISYM] `(!k:num. k <= m <=> k <= n) ==> m = n`) THEN
  REWRITE_TAC[LE_INDEX; WORD_LE_CTZ_VAL] THEN
  X_GEN_TAC `k:num` THEN ASM_REWRITE_TAC[ARITH_EQ; VAL_EQ_0] THEN
  REWRITE_TAC[TAUT `(p /\ q <=> q) <=> q ==> p`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[VAL_EQ_0] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[VAL_BOUND; LET_TRANS]
   `a <= val(x:N word) ==> a < 2 EXP dimindex(:N)`)) THEN
  SIMP_TAC[LT_EXP; ARITH_EQ; LT_IMP_LE]);;

let WORD_CLZ_BITSIZE = prove
 (`!x:N word. word_clz x = dimindex(:N) - bitsize(val x)`,
  REWRITE_TAC[WORD_CLZ; bitsize]);;

(* ------------------------------------------------------------------------- *)
(* More ad hoc lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let WORD_INDEX_WRAP = prove
 (`!i. word(8 * (i + 1) + 18446744073709551608):int64 = word(8 * i)`,
  GEN_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0]);;

let MOD_UNIQ_BALANCED = prove
 (`!n p z q.
        q * p <= n + p /\ n < q * p + p /\
        q * p + z = bitval(n < q * p) * p + n
        ==> n MOD p = z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitval] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THENL
   [EXISTS_TAC `q - 1`; EXISTS_TAC `q:num` THEN ASM_ARITH_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `n + p = (q + 1) * p + z ==> n = q * p + z`) THEN
  ASM_CASES_TAC `q = 0` THENL [ASM_MESON_TAC[LT; MULT_CLAUSES]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1] THEN ASM_ARITH_TAC);;

let MOD_UNIQ_BALANCED_REAL = prove
 (`!n p z q k.
        p < 2 EXP k /\ z < 2 EXP k /\
        q * p <= n + p /\ n < q * p + p /\
        integer((&n - &z - (&q - &(bitval(n < q * p))) * &p) / &2 pow k)
        ==> n MOD p = z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ_BALANCED THEN
  EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [GSYM REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(REAL_FIELD `!k. (y - x) / &2 pow k = &0 ==> x = y`) THEN
  EXISTS_TAC `k:num` THEN MATCH_MP_TAC REAL_EQ_INTEGERS_IMP THEN
  REWRITE_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `integer x ==> x = y ==> integer y`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_SUB_RZERO; REAL_ABS_DIV; REAL_ABS_POW] THEN
    SIMP_TAC[REAL_ABS_NUM; REAL_LT_LDIV_EQ; REAL_LT_POW2]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LT])) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let INT_REM_UNIQ_BALANCED = prove
 (`!n p z q.
      q * p <= n + p /\ n < q * p + p /\
      q * p + z = &(bitval(n < q * p)) * p + n
      ==> n rem p = z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bitval] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
   [EXISTS_TAC `q - &1:int`; EXISTS_TAC `q:int`] THEN
  ASM_INT_ARITH_TAC);;

let INT_REM_UNIQ_BALANCED_MOD = prove
 (`!n p z q k.
      &0 <= p /\ p < &2 pow k /\
      &0 <= z /\ z < &2 pow k /\
      q * p <= n + p /\ n < q * p + p /\
      (q * p + z == &(bitval(n < q * p)) * p + n) (mod (&2 pow k))
      ==> n rem p = z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQ_BALANCED THEN
  EXISTS_TAC `q:int` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[INT_ARITH `a + b:int = c <=> b = c - a`] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow k` THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(b:int == c - a) (mod p) <=> (a + b == c) (mod p)`] THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_INT_ARITH_TAC);;

let VAL_WORD_SUBWORD_JOIN_64 = prove
 (`!(h:int64) (l:int64) k.
    k <= 64
    ==> val(word_subword (word_join h l:int128) (k,64) :int64) =
        2 EXP (64 - k) * val h MOD 2 EXP k + val l DIV (2 EXP k)`,
  REWRITE_TAC[GSYM DIMINDEX_64; VAL_WORD_SUBWORD_JOIN_FULL]);;

(* ------------------------------------------------------------------------- *)
(* Alternative formulations for carry conditions as expressed abstractly.    *)
(* ------------------------------------------------------------------------- *)

let NOCARRY_WORD_ADC = prove
 (`!b x y:N word.
        val x + val y + bitval b =
        val(word_add (word_add x y) (word (bitval b))) <=>
        val x + val y + bitval b < 2 EXP dimindex(:N)`,
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_BITVAL] THEN
  REPEAT GEN_TAC THEN CONV_TAC MOD_DOWN_CONV THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  REWRITE_TAC[GSYM ADD_ASSOC; MOD_EQ_SELF] THEN
  REWRITE_TAC[ARITH_EQ; EXP_EQ_0]);;

let CARRY_WORD_ADC = prove
 (`!b x y:N word.
        ~(val x + val y + bitval b =
          val(word_add (word_add x y) (word (bitval b)))) <=>
        2 EXP dimindex(:N) <= val x + val y + bitval b`,
  REWRITE_TAC[NOCARRY_WORD_ADC; NOT_LT]);;

let NOCARRY_WORD_ADD = prove
 (`!x y:N word.
        val x + val y = val(word_add x y) <=>
        val x + val y < 2 EXP dimindex(:N)`,
  MP_TAC(SPEC `F` NOCARRY_WORD_ADC) THEN
  REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[WORD_RULE `word_add x (word 0) = x`]);;

let CARRY_WORD_ADD = prove
 (`!x y:N word.
        ~(val x + val y = val(word_add x y)) <=>
        2 EXP dimindex(:N) <= val x + val y`,
  REWRITE_TAC[NOCARRY_WORD_ADD; NOT_LT]);;

let NOCARRY_WORD_SBB = prove
 (`!b x y:N word.
        &(val x) - (&(val y) + &(bitval b)):int =
        &(val(word_sub x (word_add y (word(bitval b))))) <=>
        if b then val y < val x else val y <= val x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_ARITH);;

let CARRY_WORD_SBB = prove
 (`!b x y:N word.
        ~(&(val x) - (&(val y) + &(bitval b)):int =
          &(val(word_sub x (word_add y (word(bitval b)))))) <=>
        if b then val x <= val y else val x < val y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_ARITH);;

let NOCARRY_WORD_SUB = prove
 (`!x y:N word.
        &(val x) - &(val y):int = &(val(word_sub x y)) <=>
        val y <= val x`,
  MP_TAC(SPEC `F` NOCARRY_WORD_SBB) THEN
  REWRITE_TAC[BITVAL_CLAUSES; INT_ADD_RID] THEN
  REWRITE_TAC[WORD_RULE `word_add x (word 0) = x`]);;

let CARRY_WORD_SUB = prove
 (`!x y:N word.
        ~(&(val x) - &(val y):int = &(val(word_sub x y))) <=>
        val x < val y`,
  REWRITE_TAC[NOCARRY_WORD_SUB; NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* More concrete versions for 64-bit words etc.                              *)
(* ------------------------------------------------------------------------- *)

let NOCARRY_THM = prove
 (`!x:int64. 2 EXP 64 <= val x <=> F`,
  GEN_TAC THEN REWRITE_TAC[NOT_LE] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC);;

let NOCARRY64_ADC = prove
 (`!b x y:int64.
        (val x + val y + bitval b =
         val(word_add (word_add x y) (word (bitval b)))) <=>
        val x + val y + bitval b < 2 EXP 64`,
  REWRITE_TAC[NOCARRY_WORD_ADC; DIMINDEX_64]);;

let CARRY64_ADC = prove
 (`!b x y:int64.
        ~(val x + val y + bitval b =
          val(word_add (word_add x y) (word (bitval b)))) <=>
        2 EXP 64 <= val x + val y + bitval b`,
  REWRITE_TAC[CARRY_WORD_ADC; DIMINDEX_64]);;

let NOCARRY64_ADD = prove
 (`!x y:int64.
        (val x + val y = val(word_add x y)) <=>
        val x + val y < 2 EXP 64`,
  REWRITE_TAC[NOCARRY_WORD_ADD; DIMINDEX_64]);;

let CARRY64_ADD = prove
 (`!x y:int64.
        ~(val x + val y = val(word_add x y)) <=>
        2 EXP 64 <= val x + val y`,
  REWRITE_TAC[CARRY_WORD_ADD; DIMINDEX_64]);;

let NOCARRY64_ADD_1 = prove
 (`!x:int64.
        (val x + 1 = val(word_add x (word 1))) <=>
        val x + 1 < 2 EXP 64`,
  METIS_TAC[NOCARRY64_ADD; VAL_WORD_1]);;

let CARRY64_ADD_1 = prove
 (`!x:int64.
        ~(val x + 1 = val(word_add x (word 1))) <=>
        2 EXP 64 <= val x + 1`,
  METIS_TAC[CARRY64_ADD; VAL_WORD_1]);;

let NOCARRY64_SBB = prove
 (`!b x y:int64.
        (&(val x) - (&(val y) + &(bitval b)):int =
         &(val(word_sub x (word_add y (word (bitval b)))))) <=>
        val y + bitval b <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NOCARRY_WORD_SBB] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let CARRY64_SBB = prove
 (`!b x y:int64.
        ~(&(val x) - (&(val y) + &(bitval b)):int =
          &(val(word_sub x (word_add y (word (bitval b)))))) <=>
        val x < val y + bitval b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CARRY_WORD_SBB] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let NOCARRY64_SUB = prove
 (`!x y:int64.
        (&(val x) - &(val y):int = &(val(word_sub x y))) <=>
        val y <= val x`,
  REWRITE_TAC[NOCARRY_WORD_SUB]);;

let CARRY64_SUB = prove
 (`!x y:int64.
        ~(&(val x) - &(val y):int = &(val(word_sub x y))) <=>
        val x < val y`,
  REWRITE_TAC[CARRY_WORD_SUB]);;

let ACCUMULATE_ADC = prove
 (`!b x y:int64.
        val(x) + val(y) + val(word(bitval b):int64) =
        2 EXP 64 * bitval(2 EXP 64 <= val x + val y + bitval b) +
        val(word_add (word_add x y) (word (bitval b)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN
  SIMP_TAC[VAL_WORD_ADC_CASES; VAL_WORD_BITVAL; BITVAL_BOUND_ALT] THEN
  REWRITE_TAC[DIMINDEX_64] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_ARITH_TAC);;

let ACCUMULATE_ADC_0 = prove
 (`!b x:int64.
        val(x) + val(word(bitval b):int64) =
        2 EXP 64 * bitval(2 EXP 64 <= val x + bitval b) +
        val(word_add x (word (bitval b)))`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`b:bool`; `x:int64`; `word 0:int64`]
        ACCUMULATE_ADC) THEN
  REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; ADD_CLAUSES]);;

let ACCUMULATE_ADD = prove
 (`!x y:int64.
        val(x) + val(y) =
        2 EXP 64 * bitval(2 EXP 64 <= val x + val y) +
        val(word_add x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN
  SIMP_TAC[VAL_WORD_ADD_CASES; VAL_WORD_BITVAL; BITVAL_BOUND_ALT] THEN
  REWRITE_TAC[DIMINDEX_64] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_ARITH_TAC);;

let ACCUMULATE_SBB = prove
 (`!b x y:int64.
        2 EXP 64 * bitval(val x < val y + bitval b) + val x =
        val(word_sub x (word_add y (word (bitval b)))) + val y + bitval b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_ADD_CASES;
              VAL_WORD_0; VAL_WORD_1] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND) THEN
  MP_TAC(ISPEC `y:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let ACCUMULATE_SBB_RZERO = prove
 (`!b x:int64.
        2 EXP 64 * bitval(val x < bitval b) + val x =
        val(word_sub x (word (bitval b))) + bitval b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`b:bool`; `x:int64`; `word 0:int64`] ACCUMULATE_SBB) THEN
  REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let ACCUMULATE_SBB_LZERO = prove
 (`!b x:int64.
        2 EXP 64 * bitval(0 < val x + bitval b) =
        val(word_neg(word_add x (word (bitval b)))) + val x + bitval b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`b:bool`; `word 0:int64`; `x:int64`] ACCUMULATE_SBB) THEN
  REWRITE_TAC[VAL_WORD_0; ADD_CLAUSES; MULT_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let ACCUMULATE_SUB = prove
 (`!x y:int64.
        2 EXP 64 * bitval(val x < val y) + val x =
        val(word_sub x y) + val y`,
  MP_TAC(SPEC `F` ACCUMULATE_SBB) THEN
  REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; WORD_ADD_0]);;

let ACCUMULATE_MUL_GEN = prove
 (`!(x:N word) (y:N word).
        2 EXP dimindex(:N) *
        val(word_zx (word_ushr
         (word(val x * val y):(N tybit0)word) (dimindex(:N))):N word) +
        val(word_zx (word(val x * val y):(N tybit0)word):N word) =
        val x * val y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR] THEN
  REWRITE_TAC[GSYM MOD_MULT_MOD] THEN
  REWRITE_TAC[VAL_WORD; GSYM EXP_ADD; DIMINDEX_TYBIT0; MULT_2] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[EXP_ADD] THEN MATCH_MP_TAC LT_MULT2 THEN
  REWRITE_TAC[VAL_BOUND]);;

let ACCUMULATE_MUL = prove
 (`!(x:int64) (y:int64).
        2 EXP 64 *
        val(word_zx (word_ushr
         (word(val x * val y):(128)word) 64):int64) +
        val(word_zx (word(val x * val y):(128)word):int64) =
        val x * val y`,
  REWRITE_TAC[GSYM DIMINDEX_64; ACCUMULATE_MUL_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Variants to express in real-number terms with error bounds.               *)
(* ------------------------------------------------------------------------- *)

let APPROXIMATE_WORD_USHR = prove
 (`!(dest:int64) a n.
        dest = word_ushr a n
        ==> ?b e. dest = b /\
                  &0 <= e /\ e <= &1 - inv(&2 pow n) /\
                  &(val b) = &(val a) / &2 pow n - e`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
  REWRITE_TAC[UNWIND_THM1; REAL_ARITH
   `&0 <= e /\ e <= u /\ x:real = y - e <=>
    y - x = e /\ x <= y /\ y <= x + u`] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
  REWRITE_TAC[REAL_FIELD
   `(x + &1 - inv(&2 pow n)) * (&2 pow n) = (x + &1) * &2 pow n - &1`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= y - x * e /\ (y - x * e) + &1 <= e
    ==> x * e <= y /\ y <= (x + &1) * e - &1`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MOD; REAL_OF_NUM_POW] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
  REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let APPROXIMATE_WORD_SHL = prove
 (`!(dest:int64) a n.
        dest = word_shl a n
        ==> &2 pow n * &(val a):real < &2 pow 64
            ==> ?c. dest = c /\
                    &(val c):real = &2 pow n * &(val a)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[VAL_WORD_SHL; REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let APPROXIMATE_WORD_ADD = prove
 (`!(dest:int64) a b.
        dest = word_add a b
        ==> &(val a) + &(val b):real < &2 pow 64
            ==> ?c. dest = c /\
                    &(val c):real = &(val a) + &(val b)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[VAL_WORD_ADD; REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

let APPROXIMATE_WORD_SUB = prove
 (`!(dest:int64) a b.
        dest = word_sub a b
        ==> &0 <= &(val a) - &(val b)
            ==> ?c. dest = c /\
                    &(val c) = &(val a) - &(val b)`,
  REWRITE_TAC[REAL_SUB_LE; REAL_EQ_SUB_LADD; REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN ASM_ARITH_TAC);;

let APPROXIMATE_WORD_MUL = prove
 (`!(dest:int64) (a:int64) (b:int64).
        dest = word(0 + val a * val b)
        ==> &(val a) * &(val b):real < &2 pow 64
            ==> ?c. dest = c /\
                    &(val c):real = &(val a) * &(val b)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; UNWIND_THM1] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]);;

let APPROXIMATE_WORD_MADD = prove
 (`!(dest:int64) (a:int64) (b:int64) (c:int64).
        dest = word(val a + val b * val c)
        ==> &(val a) + &(val b) * &(val c):real < &2 pow 64
            ==> ?d. dest = d /\
                    &(val d):real = &(val a) + &(val b) * &(val c)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64]);;

let APPROXIMATE_WORD_MNEG = prove
 (`!(dest:int64) (a:int64) (b:int64).
        dest = iword(&0 - ival a * ival b)
        ==> &0 < &(val a) * &(val b):real /\
            &(val a) * &(val b):real <= &2 pow 64
            ==> ?c. dest = c /\
                    &(val c):real = &2 pow 64 - &(val a) * &(val b)`,
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[UNWIND_THM1] THEN
  REWRITE_TAC[INT_SUB_LZERO; REAL_EQ_SUB_LADD] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_EQ_SUB_LADD] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN
  EXISTS_TAC `(&2:int) pow 64` THEN CONJ_TAC THENL
   [W(MP_TAC o C SPEC VAL_BOUND_64 o
      rand o rand o lhand o rand o lhand o snd) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_RULE
     `(x:int == n - y) (mod n) <=> (x == --y) (mod n)`] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ; DIMINDEX_64]
                (INST_TYPE [`:64`,`:N`] VAL_IWORD_CONG); GSYM INT_REM_EQ] THEN
    REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
     `(a:int == a') (mod n) /\ (b == b') (mod n)
      ==> (--(a * b) == --(a' * b')) (mod n)`) THEN
    REWRITE_TAC[REWRITE_RULE[DIMINDEX_64]
     (INST_TYPE [`:64`,`:N`]IVAL_VAL_CONG)]]);;

let APPROXIMATE_WORD_IWORD = prove
 (`!(dest:int64) x x'.
        dest = iword x
        ==> &0 <= x' /\ x' < &2 pow 64 /\ (x == x') (mod (&2 pow 64))
            ==> ?c. dest = c /\
                    &(val c) = real_of_int x'`,
  REWRITE_TAC[UNWIND_THM1; GSYM INT_REM_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM int_of_num_th; GSYM int_eq] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 64` THEN
  REWRITE_TAC[GSYM INT_REM_EQ; GSYM DIMINDEX_64] THEN
  REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] VAL_IWORD_CONG] THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN MATCH_MP_TAC(INT_ARITH
   `&0 <= x /\ x < e /\ &0 <= y /\ y < e ==> abs(x - y:int) < e`) THEN
  ASM_REWRITE_TAC[INT_POS] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; VAL_BOUND_64]);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas to get a flag out of a carry setting                          *)
(* ------------------------------------------------------------------------- *)

let FLAG_FROM_CARRY_REAL_LT = prove
 (`!k x (y:real) p.
        &0 <= &2 pow k * &(bitval p) + x - y /\
        &2 pow k * &(bitval p) + x - y < &2 pow k
        ==> (p <=> x < y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN REAL_ARITH_TAC);;

let FLAG_FROM_CARRY_REAL_LE = prove
 (`!k x (y:real) p.
        &0 <= &2 pow k * (&1 - &(bitval p)) + y - x /\
        &2 pow k * (&1 - &(bitval p)) + y - x < &2 pow k
        ==> (p <=> x <= y)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN REAL_ARITH_TAC);;

let FLAG_FROM_CARRY_LT = prove
 (`!k m n p.
        &0:real <= &2 pow k * &(bitval p) + &m - &n /\
        &2 pow k * &(bitval p) + &m - &n:real < &2 pow k
        ==> (p <=> m < n)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; FLAG_FROM_CARRY_REAL_LT]);;

let FLAG_FROM_CARRY_LE = prove
 (`!k m n p.
        &0:real <= &2 pow k * (&1 - &(bitval p)) + &n - &m /\
        &2 pow k * (&1 - &(bitval p)) + &n - &m:real < &2 pow k
        ==> (p <=> m <= n)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; FLAG_FROM_CARRY_REAL_LE]);;

(* ------------------------------------------------------------------------- *)
(* Getting a word in {0,1} in a similar way.                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_FROM_CARRY_REAL_LT = prove
 (`!k x (y:real) (w:N word).
        y - x <= &2 pow k /\
        &0 <= &2 pow k * &(val w) + x - y /\
        &2 pow k * &(val w) + x - y < &2 pow k
        ==> w = word(bitval(x < y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(w:N word)` NUM_AS_BITVAL_ALT))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC `(&2 pow k):real` THEN REWRITE_TAC[REAL_LT_POW2] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VAL_EQ_BITVAL] THEN DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP FLAG_FROM_CARRY_REAL_LT) THEN
    REWRITE_TAC[]]);;

let WORD_FROM_CARRY_REAL_LE = prove
 (`!k x (y:real) (w:N word).
        y - x < &2 pow k /\
        &0 <= &2 pow k * (&1 - &(val w)) + y - x /\
        &2 pow k * (&1 - &(val w)) + y - x < &2 pow k
        ==> w = word(bitval(x <= y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(fst(EQ_IMP_RULE(SPEC `val(w:N word)` NUM_AS_BITVAL_ALT))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
    EXISTS_TAC `(&2 pow k):real` THEN REWRITE_TAC[REAL_LT_POW2] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VAL_EQ_BITVAL] THEN DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_BITVAL]) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP FLAG_FROM_CARRY_REAL_LE) THEN
    REWRITE_TAC[]]);;

let WORD_FROM_CARRY_LT = prove
 (`!k x y (w:N word).
        y - x:real <= &2 pow k /\
        &0:real <= &2 pow k * &(val w) + x - y /\
        &2 pow k * &(val w) + x - y:real < &2 pow k
        ==> w = word(bitval(x < y))`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; WORD_FROM_CARRY_REAL_LT]);;

let WORD_FROM_CARRY_LE = prove
 (`!k x  (w:N word).
        &y - &x < &2 pow k /\
        &0 <= &2 pow k * (&1 - &(val w)) + &y - &x /\
        &2 pow k * (&1 - &(val w)) + &y - &x < &2 pow k
        ==> w = word(bitval(x <= y))`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; WORD_FROM_CARRY_REAL_LE]);;

(* ------------------------------------------------------------------------- *)
(* An elaborated version for getting a flag and a mask word.                 *)
(* ------------------------------------------------------------------------- *)

let FLAG_AND_MASK_FROM_CARRY_REAL_LT = prove
 (`!c (m:int64) k (x:real).
        --(&2 pow k) <= x /\ x < &2 pow k /\
        &0 <= x - &2 pow k * (&(val m) - &2 pow 64 * &(bitval c)) /\
        x - &2 pow k * (&(val m) - &2 pow 64 * &(bitval c)) < &2 pow k
        ==> m = word_neg(word(bitval(x < &0))) /\
            (c <=> x < &0)`,
  REPEAT GEN_TAC THEN  ASM_CASES_TAC `c:bool` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_MUL_RZERO; REAL_MUL_RID;
                  REAL_SUB_RZERO; REAL_NOT_LT] THEN
  STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `x - p * (m - c):real < p ==> p * &1 <= p * (c - m) ==> x < &0`)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_ARITH `&1:real <= x - y <=> y + &1 <= x`] THEN
    SIMP_TAC[GSYM REAL_LT_INTEGERS; INTEGER_CLOSED] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES; GSYM DIMINDEX_64; VAL_BOUND] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    REWRITE_TAC[GSYM VAL_EQ_MAX_MASK; DIMINDEX_64] THEN
    MATCH_MP_TAC(ARITH_RULE `m < e /\ e < m + 2 ==> m = e - 1`) THEN
    REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; DIMINDEX_64] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `(&2:real) pow k` THEN
    REWRITE_TAC[REAL_LT_POW2] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `&0:real <= x - p ==> &0 <= p ==> &0 <= x`)) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; REAL_POS];
      SIMP_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC] THEN
    REWRITE_TAC[BITVAL_CLAUSES; WORD_NEG_0] THEN
    REWRITE_TAC[GSYM VAL_EQ_0; ARITH_RULE `n = 0 <=> ~(1 <= n)`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `&0 <= x - p * m ==> x < p ==> ~(p * &1 <= p * m)`)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LT_POW2]]);;

let FLAG_AND_MASK_FROM_CARRY_LT = prove
 (`!c (m:int64) k x y.
        --(&2 pow k):real <= &x - &y /\ &x - &y:real < &2 pow k /\
        &0:real <= &x - &y - &2 pow k * (&(val m) - &2 pow 64 * &(bitval c)) /\
        &x - &y - &2 pow k * (&(val m) - &2 pow 64 * &(bitval c)):real
        < &2 pow k
        ==> m = word_neg(word(bitval(x < y))) /\
            (c <=> x < y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x:real < y <=> x - y < &0`] THEN
  MATCH_MP_TAC FLAG_AND_MASK_FROM_CARRY_REAL_LT THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Yet more general formulations of similar patterns.                        *)
(* ------------------------------------------------------------------------- *)

let MASK_AND_VALUE_FROM_CARRY_REAL_LT = prove
 (`!(m:int64) l k (x:real).
        (--(&2 pow k) <= x /\ x < &2 pow k) /\
        (&0 <= l /\ l < &2 pow k) /\
        integer(((&2 pow k * &(val m) + l) - x) / &2 pow (k + 64))
        ==> m = word_neg(word(bitval(x < &0))) /\
            l = if x < &0 then x + &2 pow k else x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP
   (MESON[REAL_DIV_RMUL]
     `integer(x / y) ==> ~(y = &0) ==> ?n. integer n /\ x = n * y`)) THEN
  SIMP_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:real` THEN REWRITE_TAC[REAL_POW_ADD; REAL_ARITH
   `(k * m + l) - x:real = n * k * e <=> l - x = k * (n * e - m)`] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THENL
   [REWRITE_TAC[REAL_ARITH `l:real = x + k <=> l - x - k = &0`] THEN
    SUBGOAL_THEN `abs(l - x - &2 pow k) < &2 pow k * &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC];
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    SUBGOAL_THEN `abs(l - x) < &2 pow k * &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM;
                  REAL_ARITH `k * x - k:real = k * (x - &1)`] THEN
  SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_POW2] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [GSYM REAL_EQ_INTEGERS; INTEGER_CLOSED] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_ARITH `x - y:real = &1 <=> x - &1 = y`] THEN
  REWRITE_TAC[GSYM VAL_CONG; DIMINDEX_64; REAL_CONGRUENCE] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let MASK_AND_VALUE_FROM_CARRY_LT = prove
 (`!(m:int64) l k x y.
        (--(&2 pow k):real <= &x - &y /\ &x - &y:real < &2 pow k) /\
        (&0 <= l /\ l < &2 pow k) /\
        integer(((&2 pow k * &(val m) + l) - (&x - &y)) / &2 pow (k + 64))
        ==> m = word_neg(word(bitval(x < y))) /\
            l = if x < y then (&x - &y) + &2 pow k else &x - &y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x:real < y <=> x - y < &0`] THEN
  MATCH_MP_TAC MASK_AND_VALUE_FROM_CARRY_REAL_LT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transformation for a slightly different way multiplication can be done.   *)
(* ------------------------------------------------------------------------- *)

let WORD_MULTIPLICATION_LOHI = prove
 (`!(x:N word) (y:N word).
        word_mul x y = word_zx(word(val x * val y):(N tybit0)word) /\
        word((val x * val y) DIV 2 EXP dimindex(:N)):N word =
        word_zx (word_ushr (word(val x * val y):(N tybit0)word)
                (dimindex(:N)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
              VAL_WORD_USHR; VAL_WORD; DIMINDEX_TYBIT0] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `MIN (2 * n) n = n`; DIV_MOD;
              GSYM EXP_ADD; GSYM MULT_2; ARITH_RULE `MIN n n = n`]);;

let WORD_MULTIPLICATION_LOHI_64 = prove
 (`!(x:int64) (y:int64).
        word_mul x y = word_zx(word(val x * val y):int128) /\
        word((val x * val y) DIV 2 EXP 64):int64 =
        word_zx (word_ushr (word(val x * val y):int128) 64)`,
  REWRITE_TAC[GSYM DIMINDEX_64; WORD_MULTIPLICATION_LOHI]);;

(* ------------------------------------------------------------------------- *)
(* Prove non-triviality |- ?y x1 ... xn. t[x1,...,xn] = y                    *)
(* Used for non-vacuity of transitions even with undefined variables.        *)
(* ------------------------------------------------------------------------- *)

let EXISTS_NONTRIVIAL_CONV =
  let pth = prove (`!s. (?s'. s = s') <=> T`,MESON_TAC[]) in
  let elim_conv = GEN_REWRITE_CONV I [pth]
  and swap_conv = GEN_REWRITE_CONV I [SWAP_EXISTS_THM]
  and deex_conv = GEN_REWRITE_CONV I [EXISTS_SIMP] in
  let rec conv tm =
   ((swap_conv THENC BINDER_CONV conv THENC deex_conv) ORELSEC elim_conv) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Simple fix for "wraparound" of symbolics like "word(pc + n)"              *)
(* by reducing n modulo the concrete word size. This is used for the IP,     *)
(* while the BSID thing works more elaborately.                              *)
(* ------------------------------------------------------------------------- *)

let WORD_PC_PLUS_CONV =
  let pth = prove
    (`word(pc + NUMERAL n):N word =
      word(pc + NUMERAL n MOD 2 EXP dimindex(:N))`,
     REWRITE_TAC[WORD_ADD; WORD_MOD_SIZE]) in
  let conv =
    GEN_REWRITE_CONV I [pth] THENC
    RAND_CONV
     (RAND_CONV
       (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THENC
      GEN_REWRITE_CONV TRY_CONV [ARITH_RULE `n + 0 = n`]) in
  CHANGED_CONV conv;;

(* ------------------------------------------------------------------------- *)
(* Better normalize "bsid" address relative to a given offset register.      *)
(* The additive case works even for variable-containing offsets "a"/"b".     *)
(* The subtractive form only does something for constant offset pairs.       *)
(* ------------------------------------------------------------------------- *)

let NORMALIZE_ADD_SUBTRACT_WORD_CONV =
  let pth = prove
   (`word_add (word_add z (word a)) (word b) =
     word_add z (word_add (word a) (word b))`,
    CONV_TAC WORD_RULE)
  and qth = prove
   (`word_sub (word_add z (word a)) (word b) =
     word_add z (word_sub (word a) (word b))`,
    CONV_TAC WORD_RULE)
  and rth = prove
   (`word_add z (word 0) = z`,
    CONV_TAC WORD_RULE) in
  ((GEN_REWRITE_CONV I [pth] THENC RAND_CONV WORD_ADD_CONV) ORELSEC
   (GEN_REWRITE_CONV I [qth] THENC RAND_CONV WORD_SUB_CONV)) THENC
  GEN_REWRITE_CONV TRY_CONV [rth];;

let NORMALIZE_RELATIVE_ADDRESS_CONV =
  let pth = prove
   (`word_add (word_add z (word a)) (word b) = word_add z (word(a + b))`,
    CONV_TAC WORD_RULE)
  (* when the constant immediate is negative, push it into the 'relative'
     offset part *)
  and qth = prove
   (`word_sub (word_add z (word a)) (word b) =
     word_add z (word_sub (word a) (word b))`,
    CONV_TAC WORD_RULE)
  (* when the constant immediate is negative followed by positive
     (e.g., 'ldp x10, x11, [x1, -16]': x11 is loaded from (x1 - 16) + 8.),
     push it into the 'relative' offset part too *)
  and qth2 = prove
   (`word_add (word_sub (word_add z (word a)) (word b)) (word c) =
     word_add z (word_sub (word a) (word_sub (word b) (word c)))`,
    CONV_TAC WORD_RULE) in
  NORMALIZE_ADD_SUBTRACT_WORD_CONV ORELSEC
  (GEN_REWRITE_CONV I [pth] THENC
   RAND_CONV(RAND_CONV(TRY_CONV NUM_ADD_CONV)) THENC
   GEN_REWRITE_CONV (RAND_CONV o RAND_CONV o TRY_CONV) [ADD_CLAUSES])
  ORELSEC
  (GEN_REWRITE_CONV I [qth2] THENC (RAND_CONV o RAND_CONV) WORD_SUB_CONV
    THENC TRY_CONV (RAND_CONV WORD_SUB_CONV))
  ORELSEC
  (GEN_REWRITE_CONV I [qth] THENC TRY_CONV (RAND_CONV WORD_SUB_CONV));;

(* ------------------------------------------------------------------------- *)
(* Reduce goal ?- !x. P[x] to ?- !x. P[word_add x (word n)]                  *)
(* ------------------------------------------------------------------------- *)

let (WORD_FORALL_OFFSET_TAC:int->tactic) =
  let lemma = prove
   (`!(P:N word->bool) a. (!x. P(word_add x (word a))) ==> (!x. P x)`,
    MESON_TAC[WORD_RULE `word_add (word_sub x a) (a:N word) = x`]) in
  fun n -> MATCH_MP_TAC lemma THEN EXISTS_TAC (mk_small_numeral n) THEN
           CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV);;

(* A rule version of WORD_FORALL_OFFSET_TAC. *)
let (WORD_FORALL_OFFSET_RULE:int->thm->thm) =
  let lemma = prove
   (`!a (P:N word->bool). (!x. P x) ==> (!x. P(word_add x (word a)))`,
    MESON_TAC[WORD_RULE `word_add (word_sub x a) (a:N word) = x`]) in
  fun n th ->
    let th0 = MATCH_MP (SPEC (mk_small_numeral n) lemma) th in
    CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV) th0;;

(* ------------------------------------------------------------------------- *)
(* Do some limited simplification in association with symbolic execution.    *)
(* ------------------------------------------------------------------------- *)

(* Ocaml reference variable for platform specific conversions *)
let extra_word_CONV = ref [NO_CONV];;

(* Delay introduction of extra conversions *)
let apply_extra_word_convs tm = FIRST_CONV (!extra_word_CONV) tm;;

(* Rewrite rules to apply before rewriting reads from previous states *)
let extra_early_rewrite_rules = ref [];;


let ASSEMBLER_SIMPLIFY_TAC =
  let pth = prove
   (`!a b. a < a + bitval b <=> b`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `b:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC) in
  (fun (asl,w) ->
    (* filter assumptions of form 'e = e' because it can make asm_rewrite
       tactics in ASSEMBLER_SIMPLIFY_TAC run forever *)
    let asl = filter (fun (_,th) ->
      let c = concl th in not (is_eq c) || (lhs c <> rhs c)) asl in
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) !extra_early_rewrite_rules
      (asl,w)) THEN
  ASM_REWRITE_TAC[WORD_XOR_REFL; WORD_ADD_0; WORD_AND_REFL; WORD_OR_REFL;
                  WORD_ZX_BITVAL; WORD_SUB_REFL; WORD_OR_0; WORD_ZX_0; NOT_LT;
                  WORD_SX_0; SUB_EQ_0; SUB_REFL; LE_REFL; LT_REFL; NOT_LE;
                  WORD_ZX_TRIVIAL; WORD_SX_TRIVIAL] THEN
  CONV_TAC(LAND_CONV
   (GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [CARRY64_ADC; CARRY64_ADD; CARRY64_ADD_1;
      CARRY64_SBB; CARRY64_SUB] THENC
    DEPTH_CONV
     (GEN_REWRITE_CONV I [BITVAL_CLAUSES] ORELSEC
      WORD_RED_CONV ORELSEC
      apply_extra_word_convs ORELSEC
      NORMALIZE_ADD_SUBTRACT_WORD_CONV ORELSEC
      NUM_RED_CONV ORELSEC
      INT_RED_CONV) THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [WORD_RULE `word_sub x (word_add x y):int64 = word_neg y`;
      pth] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [SYM(NUM_REDUCE_CONV `2 EXP 64`)])) THEN
  ASM (GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)) [];;

(* ------------------------------------------------------------------------- *)
(* Not much commonality to all the ISAs but we do have a uniform             *)
(* notion of code length, with consistent use of length-instruction pairs    *)
(* ------------------------------------------------------------------------- *)

let codelength = new_definition
 `codelength (code:byte list) = LENGTH code`;;

let CODELENGTH_CONV ths =
  GEN_REWRITE_CONV TRY_CONV [codelength] THENC
  GEN_REWRITE_CONV RAND_CONV ths THENC
  GEN_REWRITE_CONV I [LENGTH] THENC
  GEN_REWRITE_CONV (RAND_CONV o TOP_SWEEP_CONV) [LENGTH] THENC
  DEPTH_CONV NUM_SUC_CONV;;

(* ------------------------------------------------------------------------- *)
(* Get a list of intermediate states via numeric schema.                     *)
(* ------------------------------------------------------------------------- *)

let statenames s l = map (fun n -> s^string_of_int n) l;;

(* ------------------------------------------------------------------------- *)
(* Switch quantifier over 64-bit words to over numbers.                      *)
(* ------------------------------------------------------------------------- *)

let W64_GEN_TAC =
  let pth = prove
   (`(!x:int64. P (val x) x) <=>
     (!x. x < 2 EXP 64 /\ val(word x:int64) = x
          ==> P x (word x))`,
    GEN_REWRITE_TAC LAND_CONV [FORALL_VAL_GEN] THEN
    MESON_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64]) in
  let tac = GEN_REWRITE_TAC I [pth] in
  fun w -> tac THEN X_GEN_TAC w THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Handy to pick out or discard matching assumptions.                        *)
(* ------------------------------------------------------------------------- *)

let FIND_ASM_THEN part pat ttac =
  FIRST_X_ASSUM (ttac o check (fun th -> part(concl th) = pat));;

let DISCARD_ASSUMPTIONS_TAC (P:thm -> bool):tactic =
  fun (asl,w) ->
    let asl' = filter (fun (_,th) -> not (P th)) asl in
    ALL_TAC (asl',w);;

let DISCARD_MATCHING_ASSUMPTIONS pats =
  DISCARD_ASSUMPTIONS_TAC
   (fun th -> exists (fun ptm -> can (term_match [] ptm) (concl th)) pats);;

let DISCARD_NONMATCHING_ASSUMPTIONS pats =
  DISCARD_ASSUMPTIONS_TAC
   (fun th ->
      not(exists (fun ptm -> can (term_match [] ptm) (concl th)) pats));;

(* ------------------------------------------------------------------------- *)
(* Re-abbreviating a state component, replacing existing expansion.          *)
(* ------------------------------------------------------------------------- *)

let REABBREV_TAC tm =
  let nv,sc = dest_eq tm in
  let tfn t = is_eq t && lhand t = nv in
    ABBREV_TAC tm THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (tfn o concl)));;

(* ------------------------------------------------------------------------- *)
(* A variant that eliminates existing *variable* for same expression.        *)
(* ------------------------------------------------------------------------- *)

let DEABBREV_TAC tm =
  let nv,sc = dest_eq tm in
  let tfn t = is_eq t && lhand t = nv
  and sfn t = is_eq t && is_var(lhand t) && rand t = nv in
    ABBREV_TAC tm THEN
    REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (tfn o concl))) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (sfn o concl)));;

(* ------------------------------------------------------------------------- *)
(* A slight help for efficiency of justification in some cases.              *)
(* ------------------------------------------------------------------------- *)

let (CLARIFY_TAC:tactic) =
  let rec REASSUME oldasms th =
    match oldasms with
     [(l,oth)] -> LABEL_TAC l th
    | (l,oth)::oasms ->
        CONJUNCTS_THEN2 (LABEL_TAC l) (REASSUME oasms) th
    | [] -> failwith "CLARIFY_TAC: sanity check" in
  fun ((asl,w) as gl) ->
    if asl = [] then ALL_TAC gl else
    (POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
     DISCH_THEN(REASSUME (rev asl))) gl;;

(* ------------------------------------------------------------------------- *)
(* Apply cacheing (memoization) to arbitrary function with naive assoc list. *)
(* ------------------------------------------------------------------------- *)

let cache f =
  let memo = ref [] in
  fun x -> try assoc x (!memo) with Failure _ ->
           (let y = f x in (memo := (x,y) :: (!memo); y));;

(* ------------------------------------------------------------------------- *)
(* Extensions of REPEAT tactic                                               *)
(* ------------------------------------------------------------------------- *)

let rec REPEAT_N (n:int) (t:tactic):tactic =
  if n = 0 then ALL_TAC
  else t THEN (REPEAT_N (n-1) t);;

let rec REPEAT_I_N (i:int) (n:int) (t:int->tactic):tactic =
  if i = n then ALL_TAC
  else (t i) THEN (REPEAT_I_N (i+1) n t);;

let REPEAT_I (t:int->tactic):tactic =
  let rec f (i:int) g =
    ((t i THEN f (i+1)) ORELSE ALL_TAC) g in
  f 0;;

(* ------------------------------------------------------------------------- *)
(* Tactics that break a conjunction/disjunction/etc in assumptions           *)
(* ------------------------------------------------------------------------- *)

let SPLIT_FIRST_CONJ_ASSUM_TAC =
    FIRST_X_ASSUM (fun thm ->
      let t1,t2 = CONJ_PAIR thm in MAP_EVERY ASSUME_TAC [t1;t2]);;

let CASES_FIRST_DISJ_ASSUM_TAC =
    FIRST_X_ASSUM (fun thm ->
      if is_disj (concl thm) then DISJ_CASES_TAC thm else failwith "");;

let STRIP_EXISTS_ASSUM_TAC =
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (check (is_exists o concl)));;

(* ------------------------------------------------------------------------- *)
(* Tactics that prove a subgoal using {ASM_}ARITH_TAC.                       *)
(* ------------------------------------------------------------------------- *)

(* ASSERT_USING_UNDISCH_AND_ARITH_TAC t1 t0 proves t1 using t0 and
   assumes t1 *)
let ASSERT_USING_UNDISCH_AND_ARITH_TAC t t' =
  SUBGOAL_THEN t ASSUME_TAC THENL [UNDISCH_TAC t' THEN ARITH_TAC; ALL_TAC];;

(* ASSERT_USING_ASM_ARITH_TAC t proves t using ASM_ARITH_TAC and
   assumes t *)
let ASSERT_USING_ASM_ARITH_TAC t =
  SUBGOAL_THEN t ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* General interleaving and de-interleaving functions on words.              *)
(* These are poorly supported at the moment, but useful for stating some     *)
(* more intricate SIMD operations.                                           *)
(* ------------------------------------------------------------------------- *)

let word_interleave = define
 `(word_interleave:num->(N word)list->M word) n inps =
    let l = LENGTH inps in
    word_of_bits { i | let q = i DIV n and r = i MOD n in
                       bit (n * q DIV l + r) (EL (q MOD l) inps)}`;;

let word_subdeinterleave = define
 `(word_subdeinterleave:num->num->M word->num->N word) l n z j =
        word_of_bits {i | let q = i DIV n and r = i MOD n in
                          bit ((l * q + j) * n + r) z}`;;

let word_deinterleave = define
 `(word_deinterleave:num->num->M word->(N word)list) l n z =
    list_of_seq (word_subdeinterleave l n z) l`;;

let WORD_DEINTERLEAVE_CLAUSES = prove
 (`(word_deinterleave:num->num->M word->(N word)list) 2 n z =
   [word_subdeinterleave 2 n z 0; word_subdeinterleave 2 n z 1] /\
   (word_deinterleave:num->num->M word->(N word)list) 3 n z =
   [word_subdeinterleave 3 n z 0;
    word_subdeinterleave 3 n z 1;
    word_subdeinterleave 3 n z 2]`,
  REWRITE_TAC[word_deinterleave; LIST_OF_SEQ_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Conversion for word_subdeinterleave and word_interleave. These are very   *)
(* naively implemented and could be made much more efficient.                *)
(* ------------------------------------------------------------------------- *)

let WORD_OF_BITS_AS_WORD_ALT = prove
 (`!s. word_of_bits s : N word =
       word(nsum (0..dimindex (:N) - 1) (\i. 2 EXP i * bitval(i IN s)))`,
  REWRITE_TAC[bitval; COND_RAND; MULT_CLAUSES; GSYM NSUM_RESTRICT_SET] THEN
  REWRITE_TAC[WORD_OF_BITS_AS_WORD] THEN
  SIMP_TAC[IN_NUMSEG; LE_0; DIMINDEX_NONZERO;
           ARITH_RULE `~(d = 0) ==> (i <= d - 1 <=> i < d)`]);;

let WORD_SUBDEINTERLEAVE_CONV =
  let pth = prove
   (`!P. word_of_bits {i | P i}:N word =
         word(nsum (0..dimindex (:N) - 1) (\i. 2 EXP i * bitval(P i)))`,
    REWRITE_TAC[WORD_OF_BITS_AS_WORD_ALT; IN_ELIM_THM]) in
  let conv =
    GEN_REWRITE_CONV I [word_subdeinterleave] THENC
    GEN_REWRITE_CONV I [pth] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    RAND_CONV(LAND_CONV(RAND_CONV
      (LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV))) THENC
    RAND_CONV EXPAND_NSUM_CONV THENC
    DEPTH_CONV WORD_NUM_RED_CONV in
  fun tm ->
    match tm with
      Comb(Comb(Comb(Comb(Const("word_subdeinterleave",_),e),n),
                Comb(Const("word",_),w)),j) ->
      if is_numeral e && is_numeral n && is_numeral w && is_numeral j
      then conv tm else failwith "WORD_SUBDEINTERLEAVE_CONV"
    | _ -> failwith "WORD_SUBDEINTERLEAVE_CONV";;

let WORD_INTERLEAVE_CONV =
  let pth = prove
   (`!P. word_of_bits {i | P i}:N word =
         word(nsum (0..dimindex (:N) - 1) (\i. 2 EXP i * bitval(P i)))`,
    REWRITE_TAC[WORD_OF_BITS_AS_WORD_ALT; IN_ELIM_THM]) in
  let conv =
    GEN_REWRITE_CONV I [word_interleave] THENC
    ONCE_DEPTH_CONV LENGTH_CONV THENC let_CONV THENC
    GEN_REWRITE_CONV I [pth] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    RAND_CONV(LAND_CONV(RAND_CONV
      (LAND_CONV DIMINDEX_CONV THENC NUM_SUB_CONV))) THENC
    RAND_CONV EXPAND_NSUM_CONV THENC
    DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC EL_CONV) in
  let is_wordlit t =
   match t with
     Comb(Const("word",_),n) -> is_numeral n
   | _ -> false in
  let is_wordlist t = is_list t && forall is_wordlit (dest_list t) in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_interleave",_),n),l) ->
        if is_numeral n && is_wordlist l then conv tm
        else failwith "WORD_INTERLEAVE_CONV"
    | _ -> failwith "WORD_INTERLEAVE_CONV";;

extra_word_CONV :=
  WORD_INTERLEAVE_CONV::WORD_SUBDEINTERLEAVE_CONV::(!extra_word_CONV);;

(* ------------------------------------------------------------------------- *)
(* A basic word operation corresponding to x86's exotic PEXT instruction.    *)
(* The definition is a bit clumsy and complicated, but as an extra sanity    *)
(* check and a route to more efficient concrete evaluation we relate it to   *)
(* a natural-number counterpart defined via recursion on binary digits.      *)
(* ------------------------------------------------------------------------- *)

let word_condense = define
 `(word_condense:N word->N word->N word) x y =
  word(nsum {i | i < dimindex(:N)}
            (\i. 2 EXP word_popcount(word_and y (word(2 EXP i - 1))) *
                 bitval(bit i (word_and x y))))`;;

let WORD_CONDENSE_ALT = prove
 (`!x y:N word.
    word_condense x y =
    word(nsum (0..dimindex(:N)-1)
              (\i. 2 EXP word_popcount(word_and y (word(2 EXP i - 1))) *
                   bitval(bit i (word_and x y))))`,
  REWRITE_TAC[word_condense; NUMSEG_LT; DIMINDEX_NONZERO]);;

let num_condense = define
`num_condense n m =
  if m = 0 \/ n = 0 then 0
  else if EVEN m then num_condense (n DIV 2) (m DIV 2)
  else 2 * num_condense (n DIV 2) (m DIV 2) + bitval(ODD n)`;;

let NUM_CONDENSE_0 = prove
 (`(!m. num_condense m 0 = 0) /\
   (!n. num_condense 0 n = 0)`,
  ONCE_REWRITE_TAC[num_condense] THEN REWRITE_TAC[]);;

let NUM_CONDENSE_CLAUSES = prove
 (`(!m n. num_condense (2 * n) (2 * m) = num_condense n m) /\
   (!m n. num_condense (2 * n + 1) (2 * m) = num_condense n m) /\
   (!m n. num_condense (2 * n) (2 * m + 1) = 2 * num_condense n m) /\
   (!m n. num_condense (2 * n + 1) (2 * m + 1) = 2 * num_condense n m + 1)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [num_condense] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EVEN_MULT; EVEN_ADD; ODD_ADD; ODD_MULT;
              BITVAL_CLAUSES; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[NUM_CONDENSE_0; MULT_CLAUSES]);;

let NSUM_CLAUSES_IMAGE = prove
 (`!f k. nsum {i | i < SUC k} f = f 0 + nsum {i | i < k} (f o SUC)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[NUMSEG_LT; NOT_SUC; NSUM_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[NSUM_SING; NUMSEG_SING] THEN
  REWRITE_TAC[SUC_SUB1] THEN
  SIMP_TAC[NSUM_CLAUSES_LEFT; ARITH_RULE `0 <= SUC n`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ADD1; NSUM_OFFSET; o_DEF]);;

let WORD_CONDENSE = prove
 (`!x y:N word. word_condense x y = word(num_condense (val x) (val y))`,
  REWRITE_TAC[FORALL_VAL_GEN; word_condense] THEN
  REWRITE_TAC[BIT_WORD_AND; BIT_MASK_WORD; word_popcount; bits_of_word] THEN
  SIMP_TAC[BIT_WORD] THEN
  REWRITE_TAC[TAUT `p /\ (p /\ q) /\ p /\ r <=> (p /\ r) /\ q`] THEN
  SIMP_TAC[ARITH_RULE `i:num < k ==> (j < k /\ j < i <=> j < i)`] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  DISCH_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN POP_ASSUM MP_TAC THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`m:num`;`n:num`] THEN
  SPEC_TAC(`dimindex(:N)`,`k:num`) THEN INDUCT_TAC THEN
  SIMP_TAC[EXP; ARITH_RULE `n < 1 <=> n = 0`; CONJUNCT1 LT;
           NUM_CONDENSE_0; EMPTY_GSPEC; NSUM_CLAUSES] THEN
  GEN_REWRITE_TAC I [NUM_CASES_BINARY] THEN
  CONJ_TAC THEN X_GEN_TAC `n:num` THEN
  GEN_REWRITE_TAC I [NUM_CASES_BINARY] THEN
  CONJ_TAC THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[ARITH_RULE `2 * m < 2 * n <=> m < n`] THEN
  REWRITE_TAC[ARITH_RULE `2 * m + 1 < 2 * n <=> m < n`] THEN
  ASM_SIMP_TAC[NUM_CONDENSE_CLAUSES] THEN POP_ASSUM(K ALL_TAC) THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`] THEN
  SIMP_TAC[CARD_EQ_NSUM; FINITE_NUMSEG_LT; FINITE_RESTRICT] THEN
  REWRITE_TAC[NSUM_RESTRICT_SET] THEN
  REWRITE_TAC[NSUM_CLAUSES_IMAGE; o_DEF] THEN
  REWRITE_TAC[EXP; DIV_1; GSYM DIV_DIV] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n) DIV 2 = n /\ (2 * n + 1) DIV 2 = n`] THEN
  REWRITE_TAC[ODD_MULT; ODD_ADD; ARITH; BITVAL_CLAUSES; MULT_CLAUSES;
              ADD_CLAUSES; CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
  REWRITE_TAC[CARD_CLAUSES; ARITH_RULE `x + 1 = 1 + y <=> x = y`] THEN
  REWRITE_TAC[EQ_ADD_RCANCEL; GSYM NSUM_LMUL; EXP_ADD; EXP_1] THEN
  REWRITE_TAC[MULT_ASSOC]);;

let NUM_CONDENSE_BINARY = prove
 (`num_condense (NUMERAL(BIT0 n)) (NUMERAL(BIT1 m)) =
   2 * num_condense (NUMERAL n) (NUMERAL m) /\
   num_condense (NUMERAL(BIT1 n)) (NUMERAL(BIT1 m)) =
   2 * num_condense (NUMERAL n) (NUMERAL m) + 1 /\
   num_condense (NUMERAL(BIT0 n)) (NUMERAL(BIT0 m)) =
   num_condense (NUMERAL n) (NUMERAL m) /\
   num_condense (NUMERAL(BIT1 n)) (NUMERAL(BIT0 m)) =
   num_condense (NUMERAL n) (NUMERAL m)`,
  REWRITE_TAC[GSYM ADD1; ARITH_RULE `2 = SUC(SUC 0)`] THEN
  REWRITE_TAC[BIT1; BIT0] THEN
  ABBREV_TAC `zero = 0` THEN REWRITE_TAC[NUMERAL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM MULT_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * n) = 2 * n + 1`; NUM_CONDENSE_CLAUSES]);;

let NUM_CONDENSE_CONV =
  let [pth_even; pth_odd; pth_base0; pth_base1] =
    CONJUNCTS NUM_CONDENSE_BINARY in
  let baseconv = GEN_REWRITE_CONV I [NUM_CONDENSE_0]
  and evenconv = GEN_REWRITE_CONV I [pth_even]
  and oddconv = GEN_REWRITE_CONV I [pth_odd]
  and downconv = GEN_REWRITE_CONV I [pth_base0; pth_base1] in
  let rec conv tm =
    (baseconv ORELSEC
     (downconv THENC conv) ORELSEC
     (evenconv THENC RAND_CONV conv THENC NUM_MULT_CONV) ORELSEC
     (oddconv THENC LAND_CONV(RAND_CONV conv THENC NUM_MULT_CONV) THENC
      NUM_ADD_CONV)) tm in
  fun tm ->
    match tm with
     Comb(Comb(Const("num_condense",_),_),_) -> conv tm
    | _ -> failwith "NUM_CONDENSE_CONV";;

let WORD_CONDENSE_CONV =
  GEN_REWRITE_CONV I [WORD_CONDENSE] THENC
  RAND_CONV(BINOP_CONV WORD_VAL_CONV THENC NUM_CONDENSE_CONV);;

extra_word_CONV := WORD_CONDENSE_CONV::(!extra_word_CONV);;

(* ------------------------------------------------------------------------- *)
(* A few more lemmas about words.                                            *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_ASSOC_CONSTS = prove(
  `!(x:(N)word) n m.
    (word_add (word_add x (word n)) (word m)) = (word_add x (word (n+m)))`,
  CONV_TAC WORD_RULE);;

let WORD_OR_ADD_DISJ = prove(`! (x:(64)word) (y:(64)word).
    word_or (word_shl x 32) (word_and y (word 4294967295)) =
    word_add (word_shl x 32) (word_and y (word 4294967295))`,
  REPEAT GEN_TAC THEN
  IMP_REWRITE_TAC[WORD_ADD_OR] THEN
  CONV_TAC WORD_BLAST);;

let WORD_OF_BITS_32BITMASK = prove(
  `word 4294967295 = word_of_bits {i | i < 32}`,
  REWRITE_TAC [WORD_OF_BITS_MASK; ARITH_RULE `4294967295 = 2 EXP 32 - 1`]);;

let WORD_MUL_EQ = prove(
    `!(x:(64)word) (y:(64)word). word_mul x y = word ((val x * val y) MOD 2 EXP 64)`,
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64; MOD_MOD_REFL; MOD_MOD_EXP_MIN]
    THEN CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN MESON_TAC[]);;

let WORD_SUB_ADD = WORD_RULE `word_sub (word (a + b)) (word b) = word a`;;

let WORD64_NE_ADD = prove(`!x y. 0 < y /\ y < 2 EXP 64 ==> ~((word x:int64) = word (x+y))`,
  REWRITE_TAC[WORD_EQ; DIMINDEX_64] THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN
  REWRITE_TAC[CONG_ADD_LCANCEL_EQ_0] THEN
  REWRITE_TAC[CONG_0] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC DIVIDES_DIV_NOT THEN
  MAP_EVERY EXISTS_TAC [`0`;`y:num`] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WORD64_NE_ADD2 = prove(
  `!x y y2. y < y2 /\ y2 < 2 EXP 64 ==> ~((word (x+y):int64) = word (x+y2))`,
  REWRITE_TAC[WORD_EQ; DIMINDEX_64] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONG_ADD_LCANCEL_EQ] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[CONG_CASE] THEN
  STRIP_TAC THEN ASM_ARITH_TAC);;

let WORD_SUBWORD_MUL = prove
 (`!x y:N word.
        dimindex(:M) = len /\ len <= dimindex(:N)
        ==> word_subword (word_mul x y) (0,len):M word =
            word_mul (word_subword x (0,len))
                     (word_subword y (0,len))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD_SUBWORD] THEN
  ASM_REWRITE_TAC(MOD_MOD_EXP_MIN::
    map ARITH_RULE [`2 EXP 0=1`;`x DIV 1=x`;`MIN x x=x`]) THEN
  CONV_TAC MOD_DOWN_CONV THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[ARITH_RULE `m <= n ==> MIN n m = m`]);;

(* ------------------------------------------------------------------------- *)
(* A few more lemmas about natural numbers.                                  *)
(* ------------------------------------------------------------------------- *)

let GT_REFL = prove(`!(x:num). ~(x > x)`, ARITH_TAC);;

let ADD_MOD_MOD_REFL = prove(`!a b m.
    (a + b MOD m) MOD m = (a + b) MOD m /\
    (a MOD m + b) MOD m = (a + b) MOD m`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM (SPECL [`a:num`; `b:num`] MOD_ADD_MOD)] THEN
  REWRITE_TAC [MOD_MOD_REFL]);;

let ADD_DIV_MOD_SIMP_LEMMA = prove(`!x y m.
    ~(m = 0) ==> (x MOD m + y) DIV m + x DIV m = (x + y) DIV m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun thm -> ASSUME_TAC (MATCH_MP (SPECL [`x:num`; `m:num`] DIVMOD_EXIST) thm)) THEN
  FIRST_X_ASSUM (fun thm -> CHOOSE_THEN (CHOOSE_THEN ASSUME_TAC) thm) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD;DIV_MULT_ADD;MOD_LT;DIV_LT] THEN
  ARITH_TAC);;

let LT_MULT_ADD_MULT = prove(`!(a:num) (b:num) (c:num) (m:num).
    0 < m /\ a < m /\ b < m /\ c <= m ==> c * a + b < m * m`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LET_TRANS `(m:num) * (a:num) + (b:num)` THEN
  CONJ_TAC THENL [
    IMP_REWRITE_TAC[LE_ADD2] THEN
    CONJ_TAC THENL [
      IMP_REWRITE_TAC[LE_MULT2] THEN
      REWRITE_TAC[LE_REFL];
      REWRITE_TAC[LE_REFL]];
    REPEAT STRIP_TAC THEN
    DISJ_CASES_THEN (LABEL_TAC "mcases") (SPECL [`m:num`] num_CASES) THENL [
      (* m = 0 *) SUBST_ALL_TAC (ASSUME `m = 0`) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM ONE]) THEN
      REWRITE_TAC [GSYM ONE] THEN
      ASM_ARITH_TAC;
      (* m = n + 1 *) REMOVE_THEN "mcases" (CHOOSE_THEN (LABEL_TAC "mcases'")) THEN
      SUBST_ALL_TAC (ASSUME `m = SUC n`) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ADD1]) THEN
      REWRITE_TAC [ADD1] THEN
      REWRITE_TAC [ARITH_RULE `(n + 1:num) * (n + 1:num) = (n + 1:num) * n + (n + 1:num)`] THEN
      SUBGOAL_THEN `(a:num) <= (n:num)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LET_ADD2 THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN
      ASM_MESON_TAC[]
    ]]);;

let LT_ADD_MULT_MULT = prove(`!(a:num) (b:num) (c:num) (m:num).
    0 < m /\ a < m /\ b < m /\ c <= m ==> b + c * a < m * m`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LET_TRANS `(c:num) * (a:num) + (b:num)` THEN
  CONJ_TAC THENL
    [ARITH_TAC; ASM_MESON_TAC[LT_MULT_ADD_MULT]]);;

let ADD_DIV_MOD_SIMP2_LEMMA = prove(`!(x:num) (y:num) (m:num).
    ~(m = 0) ==> x DIV m + (y + x MOD m) DIV m = (x + y) DIV m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun thm -> ASSUME_TAC (MATCH_MP (SPECL [`x:num`; `m:num`] DIVMOD_EXIST) thm)) THEN
  FIRST_X_ASSUM (fun thm -> CHOOSE_THEN (CHOOSE_THEN ASSUME_TAC) thm) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD;DIV_MULT_ADD;MOD_LT;DIV_LT;ADD_SYM] THEN
  ARITH_TAC);;

let LE_MULT_ADD = prove(`!(x:num) (x2:num) (y:num). x < x2 ==> x * y + y <= x2 * y`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `x * y + y= (x + 1)*y`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN
    ASM_ARITH_TAC);;

let ADD_SUB_SWAP = prove(
  `!(x:num) (y:num) (z:num). y >= z /\ x >= z ==> x + (y - z) = y + (x - z)`,
  ARITH_TAC);;

let ADD_SUB_SWAP2 = prove(
  `!(x:num) (y:num) (z:num). y >= z /\ z >= x ==> x + (y - z) = y - (z - x)`,
  ARITH_TAC);;

let LE_SUB_RCANCEL = prove(
  `forall (x:num) (y:num) (z:num).
    x <= y /\ y <= z ==> y - x <= z - x`,
  ARITH_TAC);;

let SUB_MOD_EQ_0 = prove(`!(x:num) (y:num).
    ~(x = 0) ==> ((x - y) MOD x = 0 <=> (x <= y \/ y = 0))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(y:num) = 0` THENL
  [ SUBST_ALL_TAC (ASSUME `(y:num) = 0`) THEN
    REWRITE_TAC[SUB_0;MOD_REFL]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(x:num) - y = x` THENL [
    ASM_ARITH_TAC;

    SUBGOAL_THEN `(x:num) - y < x` (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ARITH_TAC
  ]);;

let DIVIDES_MOD2 = prove(
  `!(n:num) (m:num) (k:num).
    n divides k ==> (n divides m <=> n divides (m MOD k))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[divides] THEN
  STRIP_TAC THEN
  EQ_TAC THENL [
    (** SUBGOAL 1 **)
    STRIP_TAC THEN ASM_REWRITE_TAC[MOD_MULT2] THEN MESON_TAC[];

    (** SUBGOAL 2 **)
    STRIP_TAC THEN
    MP_TAC (SPECL [`m:num`;`k:num`] (fst (CONJ_PAIR DIVISION_SIMP))) THEN
    FIRST_X_ASSUM (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    EXISTS_TAC `((m DIV (n * x)) * x) + x'` THEN
    ABBREV_TAC `t = m DIV (n*x)` THEN
    ASM_ARITH_TAC
  ]);;

let BITVAL_LE_DIV = prove(
  `!(x:num) (m:num). x < 2 * m ==> bitval (m <= x) = x DIV m`,
  REWRITE_TAC[bitval] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < m` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (SPECL [`x:num`;`m:num`] DIVISION) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (fun th -> let a,b = CONJ_PAIR th in
    FIRST_X_ASSUM MP_TAC THEN MP_TAC b THEN
    ASSUME_TAC a) THEN
  ABBREV_TAC `xa = x DIV m` THEN
  ABBREV_TAC `xb = x MOD m` THEN
  REPEAT_N 2 (FIRST_X_ASSUM (K ALL_TAC)) THEN
  FIRST_X_ASSUM (fun th -> ONCE_REWRITE_TAC [th]) THEN
  REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL [
    DISJ_CASES_THEN2
      (fun th -> SUBST_ALL_TAC th THEN ASM_ARITH_TAC)
      (fun th -> MP_TAC th)
      (SPEC `xa:num` num_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM (fun th -> SUBST_ALL_TAC (REWRITE_RULE [ADD1] th)) THEN
    MP_TAC (SPEC `n:num` num_CASES) THEN
    DISJ_CASES_THEN2
      (fun th -> REWRITE_TAC[th] THEN ARITH_TAC)
      (fun th -> MP_TAC th)
      (SPEC `n:num` num_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM (fun th -> SUBST_ALL_TAC (REWRITE_RULE [ADD1] th)) THEN
    ASM_ARITH_TAC;

    DISJ_CASES_THEN2
      (fun th -> SUBST_ALL_TAC th THEN ASM_ARITH_TAC)
      (fun th -> MP_TAC th)
      (SPEC `xa:num` num_CASES) THEN
    STRIP_TAC THEN FIRST_X_ASSUM (fun th -> SUBST_ALL_TAC (REWRITE_RULE [ADD1] th)) THEN
    ASM_ARITH_TAC
  ]);;

let BITVAL_LE_MOD_MOD_DIV = prove(
  `!(x1:num) (x2:num) (m:num). ~(m=0) ==>
    bitval (m <= (x1 MOD m + x2 MOD m)) = (x1 MOD m + x2 MOD m) DIV m /\
    (x1 DIV m < m ==> bitval (m <= (x1 DIV m + x2 MOD m)) = (x1 DIV m + x2 MOD m) DIV m) /\
    (x2 DIV m < m ==> bitval (m <= (x1 MOD m + x2 DIV m)) = (x1 MOD m + x2 DIV m) DIV m)`,
  REPEAT STRIP_TAC THEN IMP_REWRITE_TAC[BITVAL_LE_DIV] THEN
  REWRITE_TAC[ARITH_RULE`2*m=m+m`] THEN
  IMP_REWRITE_TAC[LT_ADD2;MOD_LT_EQ]);;

let VAL_MUL_DIV_MOD_SIMP = prove
  (`!(x:int64) (y:int64).
    ((val x * val y) DIV 2 EXP 64) MOD 2 EXP 64 = (val x * val y) DIV 2 EXP 64 /\
    (val x * val y) MOD 2 EXP 128 = val x * val y`,
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(val (x:int64) * val (y:int64) < 2 EXP 64 * 2 EXP 64)` ASSUME_TAC THENL [
      IMP_REWRITE_TAC[LT_MULT2;VAL_BOUND_64]; ALL_TAC
    ] THEN
    IMP_REWRITE_TAC[MOD_LT] THEN
    IMP_REWRITE_TAC[RDIV_LT_EQ] THEN
    ASM_ARITH_TAC);;

let MOD_ADD_MOD_RIGHT = prove
  (`!(a:num) (b:num) (c:num). a MOD d = b MOD d ==> (c + a) MOD d = (c + b) MOD d`,
    REPEAT GEN_TAC THEN
    SUBST1_TAC (GSYM (fst (CONJ_PAIR (SPECL [`c:num`;`a:num`;`d:num`] ADD_MOD_MOD_REFL)))) THEN
    SUBST1_TAC (GSYM (fst (CONJ_PAIR (SPECL [`c:num`;`b:num`;`d:num`] ADD_MOD_MOD_REFL)))) THEN
    MESON_TAC[]);;

let DIV_2_EXP_63 = prove(
  `!(x:num). x DIV 2 EXP 63 = (2 * x) DIV 2 EXP 64`,
  SIMP_TAC[ARITH_RULE`2 EXP 64 = 2*2 EXP 63`;DIV_MULT2;ARITH_RULE`~(2=0)`]);;

let LT_SUB_LT = prove(`!(a:num) (b:num). 0 < b /\ b < a ==> a - b < a`,
  ASM_ARITH_TAC);;

let MULT_ADD_DIV_LT = prove(
  `!(a:num) (b:num) (c:num) (m:num).
    1 < m /\ a < m /\ b < m /\ c <= m ==> (a * b + c) DIV m < m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(m:num) <= m * m - (m - 1)` ASSUME_TAC THENL [
    TRANS_TAC LE_TRANS `(m:num) * m - m` THEN CONJ_TAC THENL [
      TARGET_REWRITE_TAC [ARITH_RULE`(x:num)=x*1`] (GSYM LEFT_SUB_DISTRIB) THEN
      SUBGOAL_THEN `1 <= (m:num)-1` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
      TARGET_REWRITE_TAC [ARITH_RULE`(x:num)=x*1`] LE_MULT_LCANCEL THEN
      ASM_ARITH_TAC;

      ASM_ARITH_TAC
    ];
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `(a:num) * b + c < m * m` ASSUME_TAC THENL [
    TRANS_TAC LET_TRANS `(m - 1) * (m - 1) + m` THEN
    CONJ_TAC THENL [
      MATCH_MP_TAC LE_ADD2 THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_MULT2 THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[LEFT_SUB_DISTRIB;RIGHT_SUB_DISTRIB] THEN
      REWRITE_TAC[MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC[ARITH_RULE`(x:num)-a-b=x-b-a`] THEN
      IMP_REWRITE_TAC[SUB_ADD] THEN
      MATCH_MP_TAC LT_SUB_LT THEN
      CONJ_TAC THENL [ASM_ARITH_TAC;
          TRANS_TAC LET_TRANS `(m - 1) * 1` THEN
          CONJ_TAC THENL [REWRITE_TAC[MULT_CLAUSES; LE_REFL]; ALL_TAC] THEN
          MATCH_MP_TAC LT_MULT2 THEN ASM_ARITH_TAC];
    ];

    ALL_TAC
  ] THEN

  IMP_REWRITE_TAC[RDIV_LT_EQ] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Given a theorem |- l = [x1;...xn], returns |- LENGTH l = n                *)
(* ------------------------------------------------------------------------- *)

let COMPUTE_LENGTH_RULE th =
  let ltm = mk_const("LENGTH",
    [hd(snd(dest_type(type_of(lhand(concl th))))),aty]) in
  CONV_RULE(RAND_CONV
    (REWRITE_CONV [LENGTH_BYTELIST_OF_NUM; LENGTH_BYTELIST_OF_INT;
        LENGTH; LENGTH_APPEND] THENC NUM_REDUCE_CONV))
    (AP_TERM ltm th);;

(* ------------------------------------------------------------------------- *)
(* Normalize (x + m) + n -> x + [m+n] for numerals m and n.                  *)
(* The int variant `&(x + m) + &n -> &x + &[m+n]` is needed for x86 rodata-  *)
(* aware mc bytelists (rip-relative displacement encodings) so that          *)
(* BYTELIST_SUBLIST_CONV can match an outer mc evaluated at `pc` against an  *)
(* inner mc evaluated at `pc + offset`.                                      *)
(* ------------------------------------------------------------------------- *)

let NORMALIZE_ADD_ADD_CONV =
  let nat_pth = ARITH_RULE
   `(pc + NUMERAL m) + NUMERAL n = pc + NUMERAL m + NUMERAL n`
  and int_pth = prove
   (`&(pc + NUMERAL m) + &(NUMERAL n) = &pc + &(NUMERAL m + NUMERAL n):int`,
    REWRITE_TAC[GSYM INT_OF_NUM_ADD;
                INT_ARITH `(a + b:int) + c = a + b + c`]) in
  (GEN_REWRITE_CONV I [nat_pth] THENC RAND_CONV NUM_ADD_CONV) ORELSEC
  (GEN_REWRITE_CONV I [int_pth] THENC RAND_CONV (RAND_CONV NUM_ADD_CONV));;

(* ------------------------------------------------------------------------- *)
(* Prove byte list l2 is an initial sublist of l1, as `?r. l1 = APPEND l2 r` *)
(* modulo some normalization of arithmetic subexpressions if necessary.      *)
(* ------------------------------------------------------------------------- *)

let BYTELIST_SUBLIST_CONV =
  let pth_base = prove
   (`l:byte list = APPEND [] r <=> l = r`,
    REWRITE_TAC[APPEND])
  and pth_step = prove
   (`CONS h t1 = APPEND (CONS h t2) r <=>
      t1:byte list = APPEND t2 r`,
    REWRITE_TAC[APPEND; CONS_11])
  and pth_largestep = prove
   (`APPEND h t1 = APPEND (APPEND h t2) r <=>
      t1:byte list = APPEND t2 r`,
    REWRITE_TAC[GSYM APPEND_ASSOC;APPEND_LCANCEL])
  and pth_fin = prove
   (`(?r:byte list. l = r) <=> T`,
    MESON_TAC[]) in
  let baseconv = GEN_REWRITE_CONV I [pth_base]
  and stepconv = GEN_REWRITE_CONV I [pth_step]
  and largestepconv = GEN_REWRITE_CONV I [pth_largestep]
  and simpconv = ONCE_DEPTH_CONV NORMALIZE_ADD_ADD_CONV THENC
                 GEN_REWRITE_CONV ONCE_DEPTH_CONV
                   [ARITH_RULE `n + 0 = n /\ 0 + n = n`]
  and finrule = GEN_REWRITE_RULE RAND_CONV [pth_fin] in
  let simpstep_conv =
    stepconv ORELSEC
    largestepconv ORELSEC
    (BINOP2_CONV (LAND_CONV simpconv) (LAND_CONV(LAND_CONV simpconv)) THENC
     stepconv) in
  let rec rule th =
    try CONV_RULE(RAND_CONV baseconv) th with Failure _ ->
    let th' = CONV_RULE(RAND_CONV simpstep_conv) th in
    rule th' in
  fun tm ->
    let ev,bod = dest_exists tm in
    let th1 = rule(REFL bod) in
    let th2 = AP_TERM (rator tm) (ABS ev th1) in
    EQT_ELIM(finrule th2);;

(* ------------------------------------------------------------------------- *)
(* Tweak [aligned_]bytes_loaded s (word pc) mc to use word(pc + 0)           *)
(* ------------------------------------------------------------------------- *)

let TWEAK_PC_OFFSET_CONV =
  let conv =
   GEN_REWRITE_CONV (LAND_CONV o RAND_CONV) [ARITH_RULE `pc = pc + 0`] in
  fun tm ->
  match tm with
    Comb(Comb(Comb(Const("bytes_loaded",_),Var(_,_)),
              Comb(Const("word",_),Var(_,_))),_) ->
        conv tm
  | Comb(Comb(Comb(Const("aligned_bytes_loaded",_),Var(_,_)),
              Comb(Const("word",_),Var(_,_))),_) ->
        conv tm
  | _ -> failwith "TWEAK_PC_OFFSET_CONV";;

let TWEAK_PC_OFFSET = CONV_RULE(ONCE_DEPTH_CONV TWEAK_PC_OFFSET_CONV);;

(* ------------------------------------------------------------------------- *)
(* Tactics for using labeled assumptions                                     *)
(* ------------------------------------------------------------------------- *)

let UNDISCH_LABEL_TAC (label:string):tactic =
  USE_THEN label (fun th -> UNDISCH_TAC (concl th));;

let X_CHOOSE_LABEL_TAC (existvar:term) (label:string):tactic =
  REMOVE_THEN label (fun th -> X_CHOOSE_THEN existvar (LABEL_TAC label) th);;

let MATCH_MP_LABEL_TAC (hyp1:string) (hyp2:string):tactic =
  REMOVE_THEN hyp1 (fun th -> USE_THEN hyp2 (fun th2 ->
      LABEL_TAC hyp1 (MATCH_MP th th2)));;

(* ------------------------------------------------------------------------- *)
(* A simple print tac                                                        *)
(* ------------------------------------------------------------------------- *)

let PRINT_TAC (s:string): tactic =
  W (fun (asl,g) -> Printf.printf "%s\n%!" s; ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for using existential variables                                   *)
(* ------------------------------------------------------------------------- *)

(* Given `?x1 x2 ... . t` where t is a conjunction of equalities,
   HINT_EXISTS_REFL_TAC infers an assignment for the outermost quantfier x1.
   This is useful when MESON_TAC[] isn't enough to prove the goal. *)
let HINT_EXISTS_REFL_TAC: tactic =
  fun (asl,g) ->
    let qvars,body = strip_exists g in
    if qvars = [] then failwith "The goal isn't existentially quantified" else
    let qvar_to_match = List.hd qvars in
    let eqterms = conjuncts body in
    let match_from_eq (t:term): term option =
      if not (is_eq t) then None else
      let eqlhs, eqrhs = dest_eq t in
      if eqlhs = qvar_to_match && List.for_all
        (fun qvar -> not (vfree_in qvar eqrhs)) (List.tl qvars)
      then Some eqrhs
      else if eqrhs = qvar_to_match && List.for_all
        (fun qvar -> not (vfree_in qvar eqlhs)) (List.tl qvars)
      then Some eqlhs
      else None in
    let ll = List.map match_from_eq eqterms in
    match List.filter (fun t -> t <> None) ll with
    | [] -> failwith ("Cannot find a hint for " ^ (string_of_term qvar_to_match))
    | (Some t)::_ -> EXISTS_TAC t (asl,g);;

(* 'Safe' versions of META_EXISTS_TAC and UNIFY_REFL_TAC.
   SAFE_META_EXISTS_TAC receives a reference to list of variables that are
   available when META_EXISTS_TAC is run.
   The reference is then passed to SAFE_UNIFY_REFL_TAC, which checks whether
   any unallowed variable is used during instantiation. *)
let SAFE_META_EXISTS_TAC (freevars:term list ref): tactic =
  fun (asl,w) ->
    let fvs = freesl (w::(map (concl o snd) asl)) in
    let _ = freevars := fvs in
    META_EXISTS_TAC (asl,w);;

let SAFE_UNIFY_REFL_TAC (allowed_vars_ref:term list ref)
    (allowed_var_prefixes_ref:string list ref): tactic =
  fun (asl,w) ->
    let allowed_vars = !allowed_vars_ref in
    let allowed_var_prefixes = !allowed_var_prefixes_ref in

    let w_lhs,w_rhs = dest_eq w in
    let vars_to_exclude =
      if is_var w_rhs then []
      else snd (strip_comb w_rhs) in
    (* Check whether there is unlisted usage of free var in LHS of equality *)
    let lhs_vars = subtract (frees w_lhs) vars_to_exclude in
    let used_vars = subtract lhs_vars allowed_vars in
    let used_vars = filter (fun v ->
      let n = name_of v in
      forall (fun pfx -> not (starts_with pfx n))
          allowed_var_prefixes) used_vars in
    if used_vars = [] then
      UNIFY_REFL_TAC (asl,w)
    else
     (let diff = subtract lhs_vars allowed_vars in
      Printf.printf "SAFE_UNIFY_REFL_TAC: uses unaccepted variable(s)\n";
      Printf.printf "Allowed vars: %s\n"
        (String.concat ", " (map string_of_term allowed_vars));
      Printf.printf "Additionally allowed var name prefixes: %s\n"
        (String.concat ", " (allowed_var_prefixes));
      Printf.printf "Disallowed vars that are used: %s\n"
        (String.concat ", " (map string_of_term diff));
      failwith "SAFE_UNIFY_REFL_TAC");;

(* ------------------------------------------------------------------------- *)
(* A tiny checker function printing an informative diagnostic message        *)
(* ------------------------------------------------------------------------- *)

let type_check (t:term) (ty:hol_type): unit =
  if type_of t <> ty then
    failwith (Printf.sprintf "`%s` must have type `%s` but has `%s`"
        (string_of_term t) (string_of_type ty)
        (string_of_type (type_of t)))
  else
    ();;

(* ------------------------------------------------------------------------- *)
(* Extra definitions and theorems for list                                   *)
(* ------------------------------------------------------------------------- *)

let ENUMERATEL =
  define
    `(ENUMERATEL 0 (f:num->A list) = []) /\
     (ENUMERATEL (SUC n) f = APPEND (f n) (ENUMERATEL n f))`;;

let ENUMERATEL_ADD1 = prove(
  `forall n f:num->A list. ENUMERATEL (n + 1) f = APPEND (f n) (ENUMERATEL n f)`,
  REWRITE_TAC [GSYM ADD1; ENUMERATEL]);;

let ENUMERATEL_APPEND_ZERO = prove(
  `forall f:num->A list l.
    APPEND (ENUMERATEL 0 f) l = l /\
    APPEND l (ENUMERATEL 0 f) = l`,
  REWRITE_TAC [ENUMERATEL;APPEND;APPEND_NIL]);;

let ALL_IMP2 = prove(`forall (l:(A)list).
  (forall x. P x ==> Q x) ==> ALL P l ==> ALL Q l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALL_IMP THEN
  EXISTS_TAC `P:A->bool` THEN ASM_METIS_TAC[]);;

let ALL_F = prove(`forall (l:(A)list) h. ALL (\x. false) (CONS h l) <=> F`,
  REWRITE_TAC[ALL]);;

let EX_SUBSET_LIST = prove(`forall (l:(A)list) P l2.
  EX P l /\ ALL (\x. MEM x l2) l ==> EX P l2`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[EX];

    REWRITE_TAC[EX;ALL] THEN
    ASM_MESON_TAC[EX_MEM]
  ]);;

let GEN_EX_SUBSET_LIST = prove(`
  forall (P:A->bool) Q (l:(A)list) l2.
    (forall a b. P a /\ Q a b ==> P b) ==>
    EX (\x. P x) l /\ ALL (\x. EX (\y. Q x y) l2) l ==> EX (\x. P x) l2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY SPEC_TAC [(`l2:(A)list`,`l2:(A)list`);(`l:(A)list`,`l:(A)list`)]
    THEN
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[EX];

    REWRITE_TAC[EX;ALL] THEN
    ASM_MESON_TAC[EX_MEM]
  ]);;

(* ------------------------------------------------------------------------- *)
(* OCaml functions to merge diffs (called 'actions') that are used for       *)
(* equivalence checking, specifically EQUIV_STEPS_TAC.                       *)
(* ------------------------------------------------------------------------- *)

needs "common/actions_merger.ml";;
