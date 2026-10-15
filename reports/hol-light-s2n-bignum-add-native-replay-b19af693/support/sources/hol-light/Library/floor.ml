(* ========================================================================= *)
(* The integer/rational-valued reals, and the "floor" and "frac" functions.  *)
(* ========================================================================= *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Closure theorems and other lemmas for the integer-valued reals.           *)
(* ------------------------------------------------------------------------- *)

let INTEGER_CASES = prove
 (`integer x <=> (?n. x = &n) \/ (?n. x = -- &n)`,
  REWRITE_TAC[is_int; OR_EXISTS_THM]);;

let REAL_ABS_INTEGER_LEMMA = prove
 (`!x. integer(x) /\ ~(x = &0) ==> &1 <= abs(x)`,
  GEN_TAC THEN REWRITE_TAC[integer] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(x = &0) <=> (abs(x) = &0)`] THEN
  POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; REAL_OF_NUM_LE] THEN ARITH_TAC);;

let INTEGER_CLOSED = prove
 (`(!n. integer(&n)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x + y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x - y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x * y)) /\
   (!x r. integer(x) ==> integer(x pow r)) /\
   (!x. integer(x) ==> integer(--x)) /\
   (!x. integer(x) ==> integer(abs x)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(max x y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(min x y))`,
  REWRITE_TAC[integer] THEN
  MATCH_MP_TAC(TAUT
   `g /\ h /\ x /\ c /\ d /\ e /\ f /\ (a /\ e ==> b) /\ a
    ==> x /\ a /\ b /\ c /\ d /\ e /\ f /\ g /\ h`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[real_max] THEN MESON_TAC[];
    REWRITE_TAC[real_min] THEN MESON_TAC[];
    REWRITE_TAC[REAL_ABS_NUM] THEN MESON_TAC[];
    REWRITE_TAC[REAL_ABS_MUL] THEN MESON_TAC[REAL_OF_NUM_MUL];
    REWRITE_TAC[REAL_ABS_POW] THEN MESON_TAC[REAL_OF_NUM_POW];
    REWRITE_TAC[REAL_ABS_NEG]; REWRITE_TAC[REAL_ABS_ABS];
    REWRITE_TAC[real_sub] THEN MESON_TAC[]; ALL_TAC] THEN
  SIMP_TAC[REAL_ARITH `&0 <= a ==> ((abs(x) = a) <=> (x = a) \/ (x = --a))`;
           REAL_POS] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM REAL_NEG_ADD; REAL_OF_NUM_ADD] THENL
   [MESON_TAC[]; ALL_TAC; ALL_TAC; MESON_TAC[]] THEN
  REWRITE_TAC[REAL_ARITH `(--a + b = c) <=> (a + c = b)`;
              REAL_ARITH `(a + --b = c) <=> (b + c = a)`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  MESON_TAC[LE_EXISTS; ADD_SYM; LE_CASES]);;

let INTEGER_ADD = prove
 (`!x y. integer(x) /\ integer(y) ==> integer(x + y)`,
  REWRITE_TAC[INTEGER_CLOSED]);;

let INTEGER_SUB = prove
 (`!x y. integer(x) /\ integer(y) ==> integer(x - y)`,
  REWRITE_TAC[INTEGER_CLOSED]);;

let INTEGER_MUL = prove
 (`!x y. integer(x) /\ integer(y) ==> integer(x * y)`,
  REWRITE_TAC[INTEGER_CLOSED]);;

let INTEGER_POW = prove
 (`!x n. integer(x) ==> integer(x pow n)`,
  REWRITE_TAC[INTEGER_CLOSED]);;

let REAL_LE_INTEGERS = prove
 (`!x y. integer(x) /\ integer(y) ==> (x <= y <=> (x = y) \/ x + &1 <= y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y - x` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let REAL_LE_CASES_INTEGERS = prove
 (`!x y. integer(x) /\ integer(y) ==> x <= y \/ y + &1 <= x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y - x` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let REAL_LE_REVERSE_INTEGERS = prove
 (`!x y. integer(x) /\ integer(y) /\ ~(y + &1 <= x) ==> x <= y`,
  MESON_TAC[REAL_LE_CASES_INTEGERS]);;

let REAL_LT_INTEGERS = prove
 (`!x y. integer(x) /\ integer(y) ==> (x < y <=> x + &1 <= y)`,
  MESON_TAC[REAL_NOT_LT; REAL_LE_CASES_INTEGERS;
            REAL_ARITH `x + &1 <= y ==> x < y`]);;

let REAL_EQ_INTEGERS = prove
 (`!x y. integer x /\ integer y ==> (x = y <=> abs(x - y) < &1)`,
  REWRITE_TAC[REAL_ARITH `x = y <=> ~(x < y \/ y < x)`] THEN
  SIMP_TAC[REAL_LT_INTEGERS] THEN REAL_ARITH_TAC);;

let REAL_EQ_INTEGERS_IMP = prove
 (`!x y. integer x /\ integer y /\ abs(x - y) < &1 ==> x = y`,
  SIMP_TAC[REAL_EQ_INTEGERS]);;

let INTEGER_NEG = prove
 (`!x. integer(--x) <=> integer(x)`,
  MESON_TAC[INTEGER_CLOSED; REAL_NEG_NEG]);;

let INTEGER_ABS = prove
 (`!x. integer(abs x) <=> integer(x)`,
  GEN_TAC THEN REWRITE_TAC[real_abs] THEN COND_CASES_TAC THEN
  REWRITE_TAC[INTEGER_NEG]);;

let INTEGER_POS = prove
 (`!x. &0 <= x ==> (integer(x) <=> ?n. x = &n)`,
  SIMP_TAC[integer; real_abs]);;

let NONNEGATIVE_INTEGER = prove
 (`!x. integer x /\ &0 <= x <=> ?n. x = &n`,
  MESON_TAC[INTEGER_POS; INTEGER_CLOSED; REAL_POS]);;

let NONPOSITIVE_INTEGER = prove
 (`!x. integer x /\ x <= &0 <=> ?n. x = -- &n`,
  GEN_TAC THEN REWRITE_TAC[is_int] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; REAL_ARITH `a + b = &0 <=> a = --b`] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC);;

let NONPOSITIVE_INTEGER_ALT = prove
 (`!x. integer x /\ x <= &0 <=> ?n. x + &n = &0`,
  GEN_TAC THEN REWRITE_TAC[NONPOSITIVE_INTEGER] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC);;

let INTEGER_ADD_EQ = prove
 (`(!x y. integer(x) ==> (integer(x + y) <=> integer(y))) /\
   (!x y. integer(y) ==> (integer(x + y) <=> integer(x)))`,
  MESON_TAC[REAL_ADD_SUB; REAL_ADD_SYM; INTEGER_CLOSED]);;

let INTEGER_SUB_EQ = prove
 (`(!x y. integer(x) ==> (integer(x - y) <=> integer(y))) /\
   (!x y. integer(y) ==> (integer(x - y) <=> integer(x)))`,
  MESON_TAC[REAL_SUB_ADD; REAL_NEG_SUB; INTEGER_CLOSED]);;

let FORALL_INTEGER = prove
 (`!P. (!n. P(&n)) /\ (!x. P x ==> P(--x)) ==> !x. integer x ==> P x`,
  MESON_TAC[INTEGER_CASES]);;

let INTEGER_SUM = prove
 (`!f:A->real s. (!x. x IN s ==> integer(f x)) ==> integer(sum s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_CLOSED THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED]);;

let INTEGER_ABS_MUL_EQ_1 = prove
 (`!x y. integer x /\ integer y
         ==> (abs(x * y) = &1 <=> abs x = &1 /\ abs y = &1)`,
  REWRITE_TAC[integer] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; REAL_OF_NUM_MUL; MULT_EQ_1]);;

let INTEGER_DIV = prove
 (`!m n. integer(&m / &n) <=> n = 0 \/ n divides m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; INTEGER_CLOSED];
    ASM_SIMP_TAC[INTEGER_POS; REAL_POS; REAL_LE_DIV; divides] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `~(n = &0) ==> (x / n = y <=> x = n * y)`] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Similar theorems for rational-valued reals.                               *)
(* ------------------------------------------------------------------------- *)

let rational = new_definition
 `rational x <=> ?m n. integer m /\ integer n /\ ~(n = &0) /\ x = m / n`;;

let RATIONAL_INTEGER = prove
 (`!x. integer x ==> rational x`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[rational] THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `&1`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONV_TAC REAL_FIELD);;

let RATIONAL_NUM = prove
 (`!n. rational(&n)`,
  SIMP_TAC[RATIONAL_INTEGER; INTEGER_CLOSED]);;

let RATIONAL_NEG = prove
 (`!x. rational(x) ==> rational(--x)`,
  REWRITE_TAC[rational; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `m:real`; `n:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`--m:real`; `n:real`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONV_TAC REAL_FIELD);;

let RATIONAL_ABS = prove
 (`!x. rational(x) ==> rational(abs x)`,
  REWRITE_TAC[real_abs] THEN MESON_TAC[RATIONAL_NEG]);;

let RATIONAL_INV = prove
 (`!x. rational(x) ==> rational(inv x)`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_SIMP_TAC[REAL_INV_0; RATIONAL_NUM] THEN
  REWRITE_TAC[rational; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:real`; `n:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`n:real`; `m:real`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let RATIONAL_ADD = prove
 (`!x y. rational(x) /\ rational(y) ==> rational(x + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rational; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m1:real`; `n1:real`; `m2:real`; `n2:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m1 * n2 + m2 * n1:real`; `n1 * n2:real`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let RATIONAL_SUB = prove
 (`!x y. rational(x) /\ rational(y) ==> rational(x - y)`,
  SIMP_TAC[real_sub; RATIONAL_NEG; RATIONAL_ADD]);;

let RATIONAL_MUL = prove
 (`!x y. rational(x) /\ rational(y) ==> rational(x * y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rational; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m1:real`; `n1:real`; `m2:real`; `n2:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m1 * m2:real`; `n1 * n2:real`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let RATIONAL_DIV = prove
 (`!x y. rational(x) /\ rational(y) ==> rational(x / y)`,
  SIMP_TAC[real_div; RATIONAL_INV; RATIONAL_MUL]);;

let RATIONAL_POW = prove
 (`!x n. rational(x) ==> rational(x pow n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; RATIONAL_NUM; RATIONAL_MUL]);;

let RATIONAL_CLOSED = prove
 (`(!n. rational(&n)) /\
   (!x. integer x ==> rational x) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x + y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x - y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x * y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x / y)) /\
   (!x r. rational(x) ==> rational(x pow r)) /\
   (!x. rational(x) ==> rational(--x)) /\
   (!x. rational(x) ==> rational(inv x)) /\
   (!x. rational(x) ==> rational(abs x))`,
  SIMP_TAC[RATIONAL_NUM; RATIONAL_NEG; RATIONAL_ABS; RATIONAL_INV;
           RATIONAL_ADD; RATIONAL_SUB; RATIONAL_MUL; RATIONAL_DIV;
           RATIONAL_POW; RATIONAL_INTEGER]);;

let RATIONAL_NEG_EQ = prove
 (`!x. rational(--x) <=> rational x`,
  MESON_TAC[REAL_NEG_NEG; RATIONAL_NEG]);;

let RATIONAL_ABS_EQ = prove
 (`!x. rational(abs x) <=> rational x`,
  REWRITE_TAC[real_abs] THEN MESON_TAC[RATIONAL_NEG_EQ; RATIONAL_NUM]);;

let RATIONAL_INV_EQ = prove
 (`!x. rational(inv x) <=> rational x`,
  MESON_TAC[REAL_INV_INV; RATIONAL_INV]);;

let RATIONAL_SUM = prove
 (`!s x. (!i. i IN s ==> rational(x i)) ==> rational(sum s x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_CLOSED THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED]);;

let RATIONAL_ALT = prove
 (`!x. rational(x) <=> ?p q. ~(q = 0) /\ abs x = &p / &q`,
  GEN_TAC THEN REWRITE_TAC[rational] THEN EQ_TAC THENL
   [REWRITE_TAC[integer] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_DIV] THEN
    ASM_MESON_TAC[REAL_OF_NUM_EQ; REAL_ABS_ZERO];
    STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
     (REAL_ARITH `abs(x:real) = a ==> x = a \/ x = --a`)) THEN
    ASM_REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_MESON_TAC[INTEGER_CLOSED; REAL_OF_NUM_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* The floor and frac functions.                                             *)
(* ------------------------------------------------------------------------- *)

let REAL_TRUNCATE_POS = prove
 (`!x. &0 <= x ==> ?n r. &0 <= r /\ r < &1 /\ (x = &n + r)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_SUC_LE; CONJUNCT1 LT] THENL
   [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`0`; `&0`] THEN ASM_REAL_ARITH_TAC;
    POP_ASSUM_LIST(K ALL_TAC)] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `n:num`)) THEN
  REWRITE_TAC[LE_REFL; REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o REWRITE_RULE[REAL_LE_LT])
  THENL
   [MAP_EVERY EXISTS_TAC [`n:num`; `x - &n`] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY EXISTS_TAC [`SUC n`; `x - &(SUC n)`] THEN
    REWRITE_TAC[REAL_ADD_SUB; GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC]);;

let REAL_TRUNCATE = prove
 (`!x. ?n r. integer(n) /\ &0 <= r /\ r < &1 /\ (x = n + r)`,
  GEN_TAC THEN DISJ_CASES_TAC(SPECL [`x:real`; `&0`] REAL_LE_TOTAL) THENL
   [MP_TAC(SPEC `--x` REAL_ARCH_SIMPLE) THEN
    REWRITE_TAC[REAL_ARITH `--a <= b <=> &0 <= a + b`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num`
     (MP_TAC o MATCH_MP REAL_TRUNCATE_POS)) THEN
    REWRITE_TAC[REAL_ARITH `(a + b = c + d) <=> (a = (c - b) + d)`];
    ALL_TAC] THEN
  ASM_MESON_TAC[integer; INTEGER_CLOSED; REAL_TRUNCATE_POS]);;

let FLOOR_FRAC =
    new_specification ["floor"; "frac"]
       (REWRITE_RULE[SKOLEM_THM] REAL_TRUNCATE);;

(* ------------------------------------------------------------------------- *)
(* Useful lemmas about floor and frac.                                       *)
(* ------------------------------------------------------------------------- *)

let FLOOR_UNIQUE = prove
 (`!x a. integer(a) /\ a <= x /\ x < a + &1 <=> (floor x = a)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN STRIP_ASSUME_TAC(SPEC `x:real` FLOOR_FRAC) THEN
    SUBGOAL_THEN `abs(floor x - a) < &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INTEGER_CLOSED]; ASM_REAL_ARITH_TAC];
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN
    SIMP_TAC[] THEN REAL_ARITH_TAC]);;

let FLOOR_EQ_0 = prove
 (`!x. (floor x = &0) <=> &0 <= x /\ x < &1`,
  GEN_TAC THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_ADD_LID]);;

let FLOOR = prove
 (`!x. integer(floor x) /\ floor(x) <= x /\ x < floor(x) + &1`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let FLOOR_DOUBLE = prove
 (`!u. &2 * floor(u) <= floor(&2 * u) /\ floor(&2 * u) <= &2 * floor(u) + &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_REVERSE_INTEGERS THEN
  SIMP_TAC[INTEGER_CLOSED; FLOOR] THEN
  MP_TAC(SPEC `u:real` FLOOR) THEN MP_TAC(SPEC `&2 * u` FLOOR) THEN
  REAL_ARITH_TAC);;

let FRAC_FLOOR = prove
 (`!x. frac(x) = x - floor(x)`,
  MP_TAC FLOOR_FRAC THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let FLOOR_NUM = prove
 (`!n. floor(&n) = &n`,
  REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let REAL_LE_FLOOR = prove
 (`!x n. integer(n) ==> (n <= floor x <=> n <= x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[FLOOR; REAL_LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN ASM_SIMP_TAC[REAL_LT_INTEGERS; FLOOR] THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN REAL_ARITH_TAC);;

let REAL_FLOOR_LE = prove
 (`!x n. integer n ==> (floor x <= n <=> x - &1 < n)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x <= y <=> x + &1 <= y + &1`] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_INTEGERS; FLOOR; INTEGER_CLOSED] THEN
  ONCE_REWRITE_TAC[TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
  ASM_SIMP_TAC[REAL_NOT_LT; REAL_LE_FLOOR; INTEGER_CLOSED] THEN
  REAL_ARITH_TAC);;

let REAL_FLOOR_LT = prove
 (`!x n. integer n ==> (floor x < n <=> x < n)`,
  SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_FLOOR]);;

let REAL_LT_FLOOR = prove
 (`!x n. integer n ==> (n < floor x <=> n <= x - &1)`,
  SIMP_TAC[GSYM REAL_NOT_LE; REAL_FLOOR_LE]);;

let FLOOR_POS = prove
 (`!x. &0 <= x ==> ?n. floor(x) = &n`,
  REPEAT STRIP_TAC THEN MP_TAC(CONJUNCT1(SPEC `x:real` FLOOR)) THEN
  REWRITE_TAC[integer] THEN
  ASM_SIMP_TAC[real_abs; REAL_LE_FLOOR; FLOOR; INTEGER_CLOSED]);;

let FLOOR_DIV_DIV = prove
 (`!m n. ~(m = 0) ==> floor(&n / &m) = &(n DIV m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
               REAL_OF_NUM_LE; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; LT_NZ] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIVISION) THEN ARITH_TAC);;

let FLOOR_MONO = prove
 (`!x y. x <= y ==> floor x <= floor y`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  SIMP_TAC[FLOOR; REAL_LT_INTEGERS] THEN
  MAP_EVERY (MP_TAC o C SPEC FLOOR) [`x:real`; `y:real`] THEN REAL_ARITH_TAC);;

let REAL_FLOOR_EQ = prove
 (`!x. floor x = x <=> integer x`,
  REWRITE_TAC[GSYM FLOOR_UNIQUE; REAL_LE_REFL; REAL_ARITH `x < x + &1`]);;

let REAL_FLOOR_LT_REFL = prove
 (`!x. floor x < x <=> ~(integer x)`,
  MESON_TAC[REAL_LT_LE; REAL_FLOOR_EQ; FLOOR]);;

let REAL_FRAC_EQ_0 = prove
 (`!x. frac x = &0 <=> integer x`,
  REWRITE_TAC[FRAC_FLOOR; REAL_SUB_0] THEN MESON_TAC[REAL_FLOOR_EQ]);;

let REAL_FRAC_POS_LT = prove
 (`!x. &0 < frac x <=> ~(integer x)`,
  REWRITE_TAC[FRAC_FLOOR; REAL_SUB_LT; REAL_FLOOR_LT_REFL]);;

let FRAC_NUM = prove
 (`!n. frac(&n) = &0`,
  REWRITE_TAC[REAL_FRAC_EQ_0; INTEGER_CLOSED]);;

let REAL_FLOOR_REFL = prove
 (`!x. integer x ==> floor x = x`,
  REWRITE_TAC[REAL_FLOOR_EQ]);;

let REAL_FRAC_ZERO = prove
 (`!x. integer x ==> frac x = &0`,
  REWRITE_TAC[REAL_FRAC_EQ_0]);;

let REAL_FLOOR_ADD = prove
 (`!x y. floor(x + y) = if frac x + frac y < &1 then floor(x) + floor(y)
                        else (floor(x) + floor(y)) + &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INTEGER_CLOSED; FLOOR]; ALL_TAC] THEN
  MAP_EVERY (MP_TAC o C SPEC FLOOR_FRAC)[`x:real`; `y:real`; `x + y:real`] THEN
  REAL_ARITH_TAC);;

let REAL_FLOOR_TRIANGLE = prove
 (`!x y. floor(x) + floor(y) <= floor(x + y) /\
         floor(x + y) <= (floor x + floor y) + &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_FLOOR_ADD] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let REAL_FLOOR_NEG = prove
 (`!x. floor(--x) = if integer x then --x else --(floor x + &1)`,
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
  MP_TAC(SPEC `x:real` FLOOR) THEN
  MP_TAC(SPEC `x:real` REAL_FLOOR_EQ) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let REAL_FRAC_ADD = prove
 (`!x y. frac(x + y) = if frac x + frac y < &1 then frac(x) + frac(y)
                       else (frac(x) + frac(y)) - &1`,
  REWRITE_TAC[FRAC_FLOOR; REAL_FLOOR_ADD] THEN REAL_ARITH_TAC);;

let FLOOR_POS_LE = prove
 (`!x. &0 <= floor x <=> &0 <= x`,
  SIMP_TAC[REAL_LE_FLOOR; INTEGER_CLOSED]);;

let FRAC_UNIQUE = prove
 (`!x a. integer(x - a) /\ &0 <= a /\ a < &1 <=> frac x = a`,
  REWRITE_TAC[FRAC_FLOOR; REAL_ARITH `x - f:real = a <=> f = x - a`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let REAL_FRAC_EQ = prove
 (`!x. frac x = x <=> &0 <= x /\ x < &1`,
  REWRITE_TAC[GSYM FRAC_UNIQUE; REAL_SUB_REFL; INTEGER_CLOSED]);;

let INTEGER_ROUND = prove
 (`!x. ?n. integer n /\ abs(x - n) <= &1 / &2`,
  GEN_TAC THEN MATCH_MP_TAC(MESON[] `!a. P a \/ P(a + &1) ==> ?x. P x`) THEN
  EXISTS_TAC `floor x` THEN MP_TAC(ISPEC `x:real` FLOOR) THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let FRAC_DIV_MOD = prove
 (`!m n. ~(n = 0) ==> frac(&m / &n) = &(m MOD n) / &n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FRAC_UNIQUE] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; LE_1;
               REAL_ARITH `x / a - y / a:real = (x - y) / a`] THEN
  MP_TAC(SPECL [`m:num`; `n:num`] DIVISION) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LT; REAL_MUL_LID] THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
                    [CONJUNCT1 th]) THEN
  SIMP_TAC[REAL_OF_NUM_SUB; ONCE_REWRITE_RULE[ADD_SYM] LE_ADD; ADD_SUB] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; REAL_OF_NUM_EQ; INTEGER_CLOSED;
               REAL_FIELD `~(n:real = &0) ==> (x * n) / n = x`]);;

let FRAC_NEG = prove
 (`!x. frac(--x) = if integer x then &0 else &1 - frac x`,
  GEN_TAC THEN REWRITE_TAC[FRAC_FLOOR; REAL_FLOOR_NEG] THEN
  COND_CASES_TAC THEN REAL_ARITH_TAC);;

let REAL_FLOOR_FLOOR_DIV = prove
 (`!x n. floor(floor x / &n) = floor(x / &n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM real_div; GSYM FLOOR_UNIQUE; FLOOR] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  SIMP_TAC[REAL_FLOOR_LT; REAL_LE_FLOOR; FLOOR; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; GSYM REAL_LE_RDIV_EQ;
               REAL_OF_NUM_LT; LE_1; FLOOR]);;

(* ------------------------------------------------------------------------- *)
(* Assertions that there are integers between well-spaced reals.             *)
(* ------------------------------------------------------------------------- *)

let INTEGER_EXISTS_BETWEEN_ALT = prove
 (`!x y. x + &1 <= y ==> ?n. integer n /\ x < n /\ n <= y`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `floor y` THEN
  MP_TAC(SPEC `y:real` FLOOR) THEN SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let INTEGER_EXISTS_BETWEEN_LT = prove
 (`!x y. x + &1 < y ==> ?n. integer n /\ x < n /\ n < y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `integer y` THENL
   [EXISTS_TAC `y - &1:real` THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o MATCH_MP INTEGER_EXISTS_BETWEEN_ALT o
      MATCH_MP REAL_LT_IMP_LE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN ASM_MESON_TAC[]]);;

let INTEGER_EXISTS_BETWEEN = prove
 (`!x y. x + &1 <= y ==> ?n. integer n /\ x <= n /\ n < y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `integer y` THENL
   [EXISTS_TAC `y - &1:real` THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM(MP_TAC o MATCH_MP INTEGER_EXISTS_BETWEEN_ALT) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]]);;

let INTEGER_EXISTS_BETWEEN_ABS = prove
 (`!x y. &1 <= abs(x - y)
         ==> ?n. integer n /\ (x <= n /\ n < y \/ y <= n /\ n < x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_abs] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`y:real`; `x:real`] INTEGER_EXISTS_BETWEEN);
    MP_TAC(ISPECL [`x:real`; `y:real`] INTEGER_EXISTS_BETWEEN)] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let INTEGER_EXISTS_BETWEEN_ABS_LT = prove
 (`!x y. &1 < abs(x - y)
         ==> ?n. integer n /\ (x < n /\ n < y \/ y < n /\ n < x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_abs] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`y:real`; `x:real`] INTEGER_EXISTS_BETWEEN_LT);
    MP_TAC(ISPECL [`x:real`; `y:real`] INTEGER_EXISTS_BETWEEN_LT)] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS]) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More trivial theorems about real_of_int.                                  *)
(* ------------------------------------------------------------------------- *)

let REAL_OF_INT_OF_REAL = prove
 (`!x. integer(x) ==> real_of_int(int_of_real x) = x`,
  SIMP_TAC[int_rep]);;

let IMAGE_REAL_OF_INT_UNIV = prove
 (`IMAGE real_of_int (:int) = integer`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[IN] THEN MESON_TAC[int_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Finiteness of bounded set of integers.                                    *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_INTSEG_NUM = prove
 (`!m n. {x | integer(x) /\ &m <= x /\ x <= &n} HAS_SIZE ((n + 1) - m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | integer(x) /\ &m <= x /\ x <= &n} =
                IMAGE real_of_num (m..n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN ASM_CASES_TAC `?k. x = &k` THENL
     [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC) THEN
      REWRITE_TAC[REAL_OF_NUM_LE; INTEGER_CLOSED; REAL_OF_NUM_EQ] THEN
      REWRITE_TAC[UNWIND_THM1; IN_NUMSEG];
      ASM_MESON_TAC[INTEGER_POS; REAL_ARITH `&n <= x ==> &0 <= x`]];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC[HAS_SIZE_NUMSEG] THEN
    SIMP_TAC[REAL_OF_NUM_EQ]]);;

let FINITE_INTSEG = prove
 (`!a b. FINITE {x | integer(x) /\ a <= x /\ x <= b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `max (abs a) (abs b)` REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[REAL_MAX_LE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x | integer(x) /\ abs(x) <= &n}` THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\x. &x) (0..n) UNION IMAGE (\x. --(&x)) (0..n)` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUMSEG] THEN
  REWRITE_TAC[INTEGER_CASES; SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; REAL_OF_NUM_EQ; REAL_EQ_NEG2] THEN
  REWRITE_TAC[UNWIND_THM1; IN_NUMSEG] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_SIZE_INTSEG_INT = prove
 (`!a b. integer a /\ integer b
         ==> {x | integer(x) /\ a <= x /\ x <= b} HAS_SIZE
             if b < a then 0 else num_of_int(int_of_real(b - a + &1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | integer(x) /\ a <= x /\ x <= b} =
    IMAGE (\n. a + &n) {n | &n <= b - a}`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM; INTEGER_CLOSED] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    X_GEN_TAC `c:real` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a + x:real = y <=> y - a = x`] THEN
    ASM_SIMP_TAC[GSYM INTEGER_POS; REAL_SUB_LE; INTEGER_CLOSED];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN

    SIMP_TAC[REAL_EQ_ADD_LCANCEL; REAL_OF_NUM_EQ] THEN
    COND_CASES_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `b < a ==> ~(&n <= b - a)`] THEN
      REWRITE_TAC[HAS_SIZE_0; EMPTY_GSPEC];
      SUBGOAL_THEN `?m. b - a = &m` (CHOOSE_THEN SUBST1_TAC) THENL
       [ASM_MESON_TAC[INTEGER_POS; INTEGER_CLOSED; REAL_NOT_LT; REAL_SUB_LE];
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; GSYM int_of_num;
                    NUM_OF_INT_OF_NUM; HAS_SIZE_NUMSEG_LE]]]]);;

let CARD_INTSEG_INT = prove
 (`!a b. integer a /\ integer b
         ==> CARD {x | integer(x) /\ a <= x /\ x <= b} =
             if b < a then 0 else num_of_int(int_of_real(b - a + &1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_INTSEG_INT) THEN
  SIMP_TAC[HAS_SIZE]);;

let REAL_CARD_INTSEG_INT = prove
 (`!a b. integer a /\ integer b
         ==> &(CARD {x | integer(x) /\ a <= x /\ x <= b}) =
             if b < a then &0 else b - a + &1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARD_INTSEG_INT] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_OF_INT_OF_REAL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM int_of_num_th] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) INT_OF_NUM_OF_INT o
    rand o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[int_le; int_of_num_th; REAL_OF_INT_OF_REAL;
                 INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_OF_INT_OF_REAL THEN
    ASM_SIMP_TAC[INTEGER_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* Yet set of all integers or rationals is infinite.                         *)
(* ------------------------------------------------------------------------- *)

let INFINITE_INTEGER = prove
 (`INFINITE integer`,
  SUBGOAL_THEN `INFINITE(IMAGE real_of_num (:num))` MP_TAC THENL
   [SIMP_TAC[INFINITE_IMAGE_INJ; REAL_OF_NUM_EQ; num_INFINITE]; ALL_TAC] THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[IN; INTEGER_CLOSED]);;

let INFINITE_RATIONAL = prove
 (`INFINITE rational`,
  MP_TAC INFINITE_INTEGER THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN; RATIONAL_INTEGER]);;

(* ------------------------------------------------------------------------- *)
(* Arbitrarily good rational approximations.                                 *)
(* ------------------------------------------------------------------------- *)

let PADIC_RATIONAL_APPROXIMATION_STRADDLE = prove
 (`!p x e. &0 < e /\ &1 < p
           ==> ?n q r. integer q /\ integer r /\
                       q / p pow n < x /\ x < r / p pow n /\
                       abs(q / p pow n - r / p pow n) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real`; `&2 / e:real`] REAL_ARCH_POW) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_POW_LT;
               REAL_ARITH `&1 < p ==> &0 < p`] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC
   [`floor(p pow n * x) - &1`; `floor(p pow n * x) + &1`] THEN
  REWRITE_TAC[REAL_ARITH
   `abs((x - &1) / p - (x + &1) / p) = abs(&2 / p)`] THEN
  ASM_SIMP_TAC[FLOOR; INTEGER_CLOSED; REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ;
               REAL_POW_LT; REAL_ARITH `&1 < p ==> &0 < p`] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&1 < p ==> abs p = p`] THEN
  MP_TAC(ISPEC `p pow n * x:real` FLOOR) THEN REAL_ARITH_TAC);;

let PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS,
    PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE = (CONJ_PAIR o prove)
 (`(!p x e. &0 < e /\ &1 < p /\ &0 < x
            ==> ?n q r. &q / p pow n < x /\ x < &r / p pow n /\
                        abs(&q / p pow n - &r / p pow n) < e) /\
   (!p x e. &0 < e /\ &1 < p /\ &0 <= x
           ==> ?n q r. &q / p pow n <= x /\ x < &r / p pow n /\
                       abs(&q / p pow n - &r / p pow n) < e)`,
  REPEAT STRIP_TAC THEN
 (SUBGOAL_THEN `&0 < p /\ &0 <= p` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real`; `x:real`; `e:real`]
    PADIC_RATIONAL_APPROXIMATION_STRADDLE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_POW_LT;
               REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:real`; `r:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `r:real` integer) THEN
  MP_TAC(ISPEC `max q (&0)` integer) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num` THEN
  REWRITE_TAC[REAL_ARITH `abs(max q (&0)) = max q (&0)`] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a < r ==> &0 <= a ==> &0 < r`)) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`]] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[REAL_ARITH `max q (&0) = if &0 <= q then q else &0`] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_MUL; REAL_POW_LE; REAL_POW_LT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(q - r) < e ==> &0 < --q /\ z = &0 /\ &0 < r
    ==> abs(z - r) < e`)) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; GSYM REAL_MUL_LNEG] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC));;

let RATIONAL_APPROXIMATION = prove
 (`!x e. &0 < e ==> ?r. rational r /\ abs(r - x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&2:real`; `x:real`; `e:real`]
    PADIC_RATIONAL_APPROXIMATION_STRADDLE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q:real`; `r:real`] THEN
  STRIP_TAC THEN EXISTS_TAC `q / &2 pow n` THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED] THEN ASM_REAL_ARITH_TAC);;

let RATIONAL_BETWEEN = prove
 (`!a b. a < b ==> ?q. rational q /\ a < q /\ q < b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(a + b) / &2`; `(b - a) / &4`] RATIONAL_APPROXIMATION) THEN
  ANTS_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]] THEN
  ASM_REAL_ARITH_TAC);;

let RATIONAL_BETWEEN_EQ = prove
 (`!a b. (?q. rational q /\ a < q /\ q < b) <=> a < b`,
  MESON_TAC[RATIONAL_BETWEEN; REAL_LT_TRANS]);;

let RATIONAL_APPROXIMATION_STRADDLE = prove
 (`!x e. &0 < e
         ==> ?a b. rational a /\ rational b /\
                   a < x /\ x < b /\ abs(b - a) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x - e / &4`; `e / &4`] RATIONAL_APPROXIMATION) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`x + e / &4`; `e / &4`] RATIONAL_APPROXIMATION) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RATIONAL_APPROXIMATION_ABOVE = prove
 (`!x e. &0 < e ==> ?q. rational q /\ x < q /\ q < x + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `e:real`] RATIONAL_APPROXIMATION_STRADDLE) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RATIONAL_APPROXIMATION_BELOW = prove
 (`!x e. &0 < e ==> ?q. rational q /\ x - e < q /\ q < x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `e:real`] RATIONAL_APPROXIMATION_STRADDLE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let INFINITE_RATIONAL_IN_RANGE = prove
 (`!a b. a < b ==> INFINITE {q | rational q /\ a < q /\ q < b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?q. (!n. rational(q n) /\ a < q n /\ q n < b) /\ (!n. q(SUC n) < q n)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM REAL_LT_MIN] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RATIONAL_BETWEEN THEN
    ASM_REWRITE_TAC[REAL_LT_MIN];
    MATCH_MP_TAC INFINITE_SUPERSET THEN
    EXISTS_TAC `IMAGE (q:num->real) (:num)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC INFINITE_IMAGE THEN REWRITE_TAC[num_INFINITE; IN_UNIV] THEN
    SUBGOAL_THEN `!m n. m < n ==> (q:num->real) n < q m`
     (fun th -> MESON_TAC[LT_CASES; th; REAL_LT_REFL]) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
    ASM_MESON_TAC[REAL_LT_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* Converting a congruence over N or Z into a real equivalent.               *)
(* ------------------------------------------------------------------------- *)

let REAL_CONGRUENCE = prove
 (`!a b n. (a == b) (mod n) <=>
           if n = 0 then &a:real = &b
           else integer((&a - &b) / &n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THENL
   [CONV_TAC NUMBER_RULE; ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_REAL_OF_INT_UNIV] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM IN] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
   `~(n:real = &0) ==> (x / n = y <=> n * y = x)`] THEN
  REWRITE_TAC[GSYM int_of_num_th] THEN
  REWRITE_TAC[GSYM int_sub_th; GSYM int_mul_th; GSYM int_eq] THEN
  REWRITE_TAC[num_congruent; int_congruent] THEN MESON_TAC[]);;

let REAL_INT_CONGRUENCE = prove
 (`!a b n. (a == b) (mod n) <=>
           if n = &0 then real_of_int a = real_of_int b
           else integer((real_of_int a - real_of_int b) / real_of_int n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM int_eq] THENL
   [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_REAL_OF_INT_UNIV] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM IN] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
  ASM_SIMP_TAC[GSYM int_of_num_th; GSYM int_eq;  REAL_FIELD
   `~(n:real = &0) ==> (x / n = y <=> n * y = x)`] THEN
  REWRITE_TAC[GSYM int_mul_th; GSYM int_sub_th; GSYM int_eq] THEN
  CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* A simple tactic to try and prove that a real expression is integral.      *)
(* ------------------------------------------------------------------------- *)

let (REAL_INTEGER_TAC:tactic) =
  let base = MATCH_ACCEPT_TAC(CONJUNCT1 INTEGER_CLOSED) ORELSE
             MATCH_ACCEPT_TAC INTEGER_REAL_OF_INT
  and step =
    MAP_FIRST MATCH_MP_TAC (CONJUNCTS(CONJUNCT2 INTEGER_CLOSED)) THEN
    TRY CONJ_TAC in
  let tac = REPEAT step THEN base in
  fun (asl,w) ->
   (match w with
     Comb(Const("integer",_),t) ->
      (tac ORELSE
       (CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN tac)) (asl,w)
    | _ -> failwith "REAL_INTEGER_TAC: Goal not of expected form");;
