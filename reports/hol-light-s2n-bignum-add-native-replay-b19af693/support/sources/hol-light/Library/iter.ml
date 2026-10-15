(* ========================================================================= *)
(* Iterated application of a function, ITER n f x = f^n(x).                  *)
(*                                                                           *)
(* (c) Marco Maggesi, Graziano Gentili and Gianni Ciolli, 2008.              *)
(* ========================================================================= *)

let ITER = define
  `(!f. ITER 0 f x = x) /\
   (!f n. ITER (SUC n) f x = f (ITER n f x))`;;

let ITER_POINTLESS = prove
  (`(!f. ITER 0 f = I) /\
    (!f n. ITER (SUC n) f = f o ITER n f)`,
   REWRITE_TAC [FUN_EQ_THM; I_THM; o_THM; ITER]);;

let ITER_ALT = prove
  (`(!f x. ITER 0 f x = x) /\
    (!f n x. ITER (SUC n) f x = ITER n f (f x))`,
   REWRITE_TAC [ITER] THEN GEN_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC [ITER]);;

let ITER_ALT_POINTLESS = prove
  (`(!f. ITER 0 f = I) /\
    (!f n. ITER (SUC n) f = ITER n f o f)`,
   REWRITE_TAC [FUN_EQ_THM; I_THM; o_THM; ITER_ALT]);;

let ITER_1 = prove
 (`!f x. ITER 1 f x = f x`,
  REWRITE_TAC[num_CONV `1`; ITER]);;

let ITER_ADD = prove
  (`!f n m x. ITER n f (ITER m f x) = ITER (n + m) f x`,
   GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; ADD]);;

let ITER_ADD_POINTLESS = prove
 (`!m n. ITER (m + n) f = ITER m f o ITER n f`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; ITER_ADD]);;

let ITER_MUL = prove
  (`!f n m x. ITER n (ITER m f) x = ITER (n * m) f x`,
   GEN_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC[ITER; MULT; ITER_ADD; ADD_AC]);;

let ITER_FIXPOINT = prove
  (`!f n x. f x = x ==> ITER n f x = x`,
   GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ITER_ALT]);;

(* ------------------------------------------------------------------------- *)
(* Existence of "order" or "characteristic" in a general setting.            *)
(* ------------------------------------------------------------------------- *)

let ORDER_EXISTENCE_GEN = prove
 (`!P f:num->A.
         P(f 0) /\ (!m n. P(f m) /\ ~(m = 0) ==> (P(f(m + n)) <=> P(f n)))
         ==> ?d. !n. P(f n) <=> d divides n`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!n. ~(n = 0) ==> ~P(f n:A)` THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[NUMBER_RULE `0 divides n <=> n = 0`] THEN
    ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM])] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[NOT_IMP] THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN STRIP_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_MESON_TAC[NUMBER_RULE `n divides 0`]; ALL_TAC] THEN
  ASM_CASES_TAC `d <= n:num` THENL
   [ALL_TAC; ASM_MESON_TAC[NOT_LT; DIVIDES_LE]] THEN
  SUBGOAL_THEN `n:num = (n - d) + d` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ABBREV_TAC `m:num = n - d`] THEN
  REWRITE_TAC[NUMBER_RULE `(d:num) divides m + d <=> d divides m`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[ADD_SYM]]);;

let ORDER_EXISTENCE_ITER = prove
 (`!R f z:A.
        R z z /\
        (!x y. R x y ==> R y x) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!x y. R x y ==> R (f x) (f y))
        ==> ?d. !n. R (ITER n f z) z <=> d divides n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (R:A->A->bool) x z`;
                 `\n. ITER n f (z:A)`] ORDER_EXISTENCE_GEN) THEN
  ASM_REWRITE_TAC[ITER] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM ITER_ADD] THEN
  MP_TAC(MESON[]
   `!a b:num->A. (!x y. R x y ==> R y x) /\
          (!x y z. R x y /\ R y z ==> R x z) /\
          (!n. R (a n) (b n))
          ==> (!n. R (a n) z <=> R (b n) z)`) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  ASM_MESON_TAC[]);;

let ORDER_EXISTENCE_CARD = prove
 (`!R f z:A k.
     FINITE { R(ITER n f z) | n IN (:num)} /\
     CARD { R(ITER n f z) | n IN (:num)} <= k /\
     R z z /\
     (!x y. R x y ==> R y x) /\
     (!x y z. R x y /\ R y z ==> R x z) /\
     (!x y. R (f x) (f y) <=> R x y)
     ==> ?d. 0 < d /\ d <= k /\ !n. R (ITER n f z) z <=> d divides n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?m. 0 < m /\ m <= k /\ (R:A->A->bool) (ITER m f z) z`
  STRIP_ASSUME_TAC THENL
    [MP_TAC(ISPECL [`\n. (R:A->A->bool) (ITER n f z)`; `0..k`]
      CARD_IMAGE_EQ_INJ) THEN
     REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG; SUB_0] THEN
     MATCH_MP_TAC(TAUT `~p /\ (~q ==> r) ==> (p <=> q) ==> r`) THEN
     CONJ_TAC THENL
      [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `c <= k ==> s <= c ==> ~(s = k + 1)`)) THEN
       MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
       REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
       MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
       CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
       MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
       REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
       EXISTS_TAC `q - p:num` THEN
       REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
       SUBGOAL_THEN
        `!d. d <= p
             ==> (R:A->A->bool) (ITER (p - d) f z) (ITER (q - d) f z)`
       MP_TAC THENL
        [INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_0] THENL
          [SPEC_TAC(`q:num`,`q:num`) THEN INDUCT_TAC THEN
           ASM_REWRITE_TAC[ITER];
           DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
           ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
           SUBGOAL_THEN `q - d = SUC(q - SUC d) /\ p - d = SUC(p - SUC d)`
            (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
           ASM_REWRITE_TAC[ITER]];
         DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
         REWRITE_TAC[LE_REFL; SUB_REFL; ITER] THEN ASM_MESON_TAC[]]];
     MP_TAC(ISPECL [`R:A->A->bool`; `f:A->A`; `z:A`] ORDER_EXISTENCE_ITER) THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
     X_GEN_TAC `d:num` THEN ASM_CASES_TAC `d = 0` THEN ASM_SIMP_TAC[] THEN
     DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
     ASM_SIMP_TAC[LE_1; NUMBER_RULE `!n. 0 divides n <=> n = 0`] THEN
     DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC]);;

let ORDER_EXISTENCE_FINITE = prove
 (`!R f z:A.
     FINITE { R(ITER n f z) | n IN (:num)} /\
     R z z /\
     (!x y. R x y ==> R y x) /\
     (!x y z. R x y /\ R y z ==> R x z) /\
     (!x y. R (f x) (f y) <=> R x y)
     ==> ?d. 0 < d /\ !n. R (ITER n f z) z <=> d divides n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:A->A->bool`; `f:A->A`; `z:A`;
   `CARD {(R:A->A->bool)(ITER n f z) | n IN (:num)}`]
   ORDER_EXISTENCE_CARD) THEN ASM_REWRITE_TAC[LE_REFL] THEN MESON_TAC[]);;
