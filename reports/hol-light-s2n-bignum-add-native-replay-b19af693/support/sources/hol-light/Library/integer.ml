(* ========================================================================= *)
(* Basic divisibility notions over the integers.                             *)
(*                                                                           *)
(* This is similar to stuff in Library/prime.ml etc. for natural numbers.    *)
(* ========================================================================= *)

prioritize_int();;

(* ------------------------------------------------------------------------- *)
(* Basic properties of divisibility.                                         *)
(* ------------------------------------------------------------------------- *)

let INT_DIVIDES_REFL = INTEGER_RULE
  `!d. d divides d`;;

let INT_DIVIDES_TRANS = INTEGER_RULE
  `!x y z. x divides y /\ y divides z ==> x divides z`;;

let INT_DIVIDES_ADD = INTEGER_RULE
  `!d a b. d divides a /\ d divides b ==> d divides (a + b)`;;

let INT_DIVIDES_SUB = INTEGER_RULE
  `!d a b. d divides a /\ d divides b ==> d divides (a - b)`;;

let INT_DIVIDES_0 = INTEGER_RULE
  `!d. d divides &0`;;

let INT_DIVIDES_ZERO = INTEGER_RULE
  `!x. &0 divides x <=> x = &0`;;

let INT_DIVIDES_LNEG = INTEGER_RULE
  `!d x. (--d) divides x <=> d divides x`;;

let INT_DIVIDES_RNEG = INTEGER_RULE
  `!d x. d divides (--x) <=> d divides x`;;

let INT_DIVIDES_RMUL = INTEGER_RULE
  `!d x y. d divides x ==> d divides (x * y)`;;

let INT_DIVIDES_LMUL = INTEGER_RULE
  `!d x y. d divides y ==> d divides (x * y)`;;

let INT_DIVIDES_1 = INTEGER_RULE
  `!x. &1 divides x`;;

let INT_DIVIDES_ADD_REVR = INTEGER_RULE
  `!d a b. d divides a /\ d divides (a + b) ==> d divides b`;;

let INT_DIVIDES_ADD_REVL = INTEGER_RULE
  `!d a b. d divides b /\ d divides (a + b) ==> d divides a`;;

let INT_DIVIDES_MUL_L = INTEGER_RULE
  `!a b c. a divides b ==> (c * a) divides (c * b)`;;

let INT_DIVIDES_MUL_R = INTEGER_RULE
  `!a b c. a divides b ==> (a * c) divides (b * c)`;;

let INT_DIVIDES_LMUL2 = INTEGER_RULE
  `!d a x. (x * d) divides a ==> d divides a`;;

let INT_DIVIDES_RMUL2 = INTEGER_RULE
  `!d a x. (d * x) divides a ==> d divides a`;;

let INT_DIVIDES_CMUL2 = INTEGER_RULE
  `!a b c. (c * a) divides (c * b) /\ ~(c = &0) ==> a divides b`;;

let INT_DIVIDES_LMUL2_EQ = INTEGER_RULE
  `!a b c. ~(c = &0) ==> ((c * a) divides (c * b) <=> a divides b)`;;

let INT_DIVIDES_RMUL2_EQ = INTEGER_RULE
  `!a b c. ~(c = &0) ==> ((a * c) divides (b * c) <=> a divides b)`;;

let INT_DIVIDES_MUL2 = INTEGER_RULE
  `!a b c d. a divides b /\ c divides d ==> (a * c) divides (b * d)`;;

let INT_DIVIDES_POW = prove
 (`!x y n. x divides y ==> (x pow n) divides (y pow n)`,
  REWRITE_TAC[int_divides] THEN MESON_TAC[INT_POW_MUL]);;

let INT_DIVIDES_POW2 = prove
 (`!n x y. ~(n = 0) /\ (x pow n) divides y ==> x divides y`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; INT_POW] THEN INTEGER_TAC);;

let INT_DIVIDES_RPOW = prove
 (`!x y n. x divides y /\ ~(n = 0) ==> x divides (y pow n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[INT_DIVIDES_RMUL; INT_POW]);;

let INT_DIVIDES_RPOW_SUC = prove
 (`!x y n. x divides y ==> x divides (y pow (SUC n))`,
  SIMP_TAC[INT_DIVIDES_RPOW; NOT_SUC]);;

let INT_DIVIDES_POW_LE_IMP = prove
 (`!(p:int) m n. m <= n ==> p pow m divides p pow n`,
  SIMP_TAC[LE_EXISTS; INT_POW_ADD; LEFT_IMP_EXISTS_THM] THEN
  CONV_TAC INTEGER_RULE);;

let INT_DIVIDES_ANTISYM_DIVISORS = prove
 (`!a b:int. a divides b /\ b divides a <=> !d. d divides a <=> d divides b`,
  MESON_TAC[INT_DIVIDES_REFL; INT_DIVIDES_TRANS]);;

let INT_DIVIDES_ANTISYM_MULTIPLES = prove
 (`!a b. a divides b /\ b divides a <=> !d. a divides d <=> b divides d`,
  MESON_TAC[INT_DIVIDES_REFL; INT_DIVIDES_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Now carefully distinguish signs.                                          *)
(* ------------------------------------------------------------------------- *)

let INT_DIVIDES_ONE_POS = prove
 (`!x. &0 <= x ==> (x divides &1 <=> x = &1)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[int_divides]; INTEGER_TAC] THEN
  DISCH_THEN(CHOOSE_THEN(MP_TAC o AP_TERM `abs` o SYM)) THEN
  SIMP_TAC[INT_ABS_NUM; INT_ABS_MUL_1] THEN ASM_SIMP_TAC[INT_ABS]);;

let INT_DIVIDES_ONE_ABS = prove
 (`!d. d divides &1 <=> abs(d) = &1`,
  MESON_TAC[INT_DIVIDES_LABS; INT_DIVIDES_ONE_POS; INT_ABS_POS]);;

let INT_DIVIDES_ONE = prove
 (`!d. d divides &1 <=> d = &1 \/ d = -- &1`,
  REWRITE_TAC[INT_DIVIDES_ONE_ABS] THEN INT_ARITH_TAC);;

let INT_DIVIDES_ANTISYM_ASSOCIATED = prove
 (`!x y. x divides y /\ y divides x <=> ?u. u divides &1 /\ x = y * u`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; INTEGER_TAC] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_SIMP_TAC[INT_DIVIDES_ZERO; INT_MUL_LZERO] THEN
  ASM_MESON_TAC[int_divides; INT_DIVIDES_REFL;
    INTEGER_RULE `y = x * d /\ x = y * e /\ ~(y = &0) ==> d divides &1`]);;

let INT_DIVIDES_ANTISYM = prove
 (`!x y. x divides y /\ y divides x <=> x = y \/ x = --y`,
  REWRITE_TAC[INT_DIVIDES_ANTISYM_ASSOCIATED; INT_DIVIDES_ONE] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  INT_ARITH_TAC);;

let INT_DIVIDES_ANTISYM_ABS = prove
 (`!x y. x divides y /\ y divides x <=> abs(x) = abs(y)`,
  REWRITE_TAC[INT_DIVIDES_ANTISYM] THEN INT_ARITH_TAC);;

let INT_DIVIDES_ANTISYM_POS = prove
 (`!x y. &0 <= x /\ &0 <= y ==> (x divides y /\ y divides x <=> x = y)`,
  REWRITE_TAC[INT_DIVIDES_ANTISYM_ABS] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about GCDs.                                                        *)
(* ------------------------------------------------------------------------- *)

let INT_GCD_POS = prove
 (`!a b. &0 <= gcd(a,b)`,
  REWRITE_TAC[int_gcd]);;

let INT_ABS_GCD = prove
 (`!a b. abs(gcd(a,b)) = gcd(a,b)`,
  REWRITE_TAC[INT_ABS; INT_GCD_POS]);;

let INT_GCD_DIVIDES = prove
 (`!a b. gcd(a,b) divides a /\ gcd(a,b) divides b`,
  INTEGER_TAC);;

let INT_COPRIME_GCD = prove
 (`!a b. coprime(a,b) <=> gcd(a,b) = &1`,
  SIMP_TAC[GSYM INT_DIVIDES_ONE_POS; INT_GCD_POS] THEN INTEGER_TAC);;

let INT_GCD_BEZOUT = prove
 (`!a b. ?x y. gcd(a,b) = a * x + b * y`,
  INTEGER_TAC);;

let INT_DIVIDES_GCD = prove
 (`!a b d. d divides gcd(a,b) <=> d divides a /\ d divides b`,
  INTEGER_TAC);;

let INT_GCD = INTEGER_RULE
  `!a b. (gcd(a,b) divides a /\ gcd(a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides gcd(a,b))`;;

let INT_GCD_UNIQUE = prove
 (`!a b d. gcd(a,b) = d <=> &0 <= d /\ d divides a /\ d divides b /\
                            !e. e divides a /\ e divides b ==> e divides d`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[INT_GCD; INT_GCD_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[INT_GCD_POS; GSYM INT_DIVIDES_ANTISYM_POS; INT_DIVIDES_GCD] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN INTEGER_TAC);;

let INT_GCD_UNIQUE_ABS = prove
 (`!a b d. gcd(a,b) = abs(d) <=>
           d divides a /\ d divides b /\
           !e. e divides a /\ e divides b ==> e divides d`,
  REWRITE_TAC[INT_GCD_UNIQUE; INT_ABS_POS; INT_DIVIDES_ABS]);;

let INT_GCD_REFL = prove
 (`!a. gcd(a,a) = abs(a)`,
  REWRITE_TAC[INT_GCD_UNIQUE_ABS] THEN INTEGER_TAC);;

let INT_GCD_SYM = prove
 (`!a b. gcd(a,b) = gcd(b,a)`,
  SIMP_TAC[INT_GCD_POS; GSYM INT_DIVIDES_ANTISYM_POS] THEN INTEGER_TAC);;

let INT_GCD_ASSOC = prove
 (`!a b c. gcd(a,gcd(b,c)) = gcd(gcd(a,b),c)`,
  SIMP_TAC[INT_GCD_POS; GSYM INT_DIVIDES_ANTISYM_POS] THEN INTEGER_TAC);;

let INT_GCD_1 = prove
 (`!a. gcd(a,&1) = &1 /\ gcd(&1,a) = &1`,
  SIMP_TAC[INT_GCD_UNIQUE; INT_POS; INT_DIVIDES_1]);;

let INT_GCD_0 = prove
 (`!a. gcd(a,&0) = abs(a) /\ gcd(&0,a) = abs(a)`,
  SIMP_TAC[INT_GCD_UNIQUE_ABS] THEN INTEGER_TAC);;

let INT_GCD_EQ_0 = prove
 (`!a b. gcd(a,b) = &0 <=> a = &0 /\ b = &0`,
  INTEGER_TAC);;

let INT_GCD_ABS = prove
 (`!a b. gcd(abs(a),b) = gcd(a,b) /\ gcd(a,abs(b)) = gcd(a,b)`,
  REWRITE_TAC[INT_GCD_UNIQUE; INT_DIVIDES_ABS; INT_GCD_POS; INT_GCD]);;

let INT_GCD_MULTIPLE =
 (`!a b. gcd(a,a * b) = abs(a) /\ gcd(b,a * b) = abs(b)`,
  REWRITE_TAC[INT_GCD_UNIQUE_ABS] THEN INTEGER_TAC);;

let INT_GCD_ADD = prove
 (`(!a b. gcd(a + b,b) = gcd(a,b)) /\
   (!a b. gcd(b + a,b) = gcd(a,b)) /\
   (!a b. gcd(a,a + b) = gcd(a,b)) /\
   (!a b. gcd(a,b + a) = gcd(a,b))`,
  SIMP_TAC[INT_GCD_UNIQUE; INT_GCD_POS] THEN INTEGER_TAC);;

let INT_GCD_SUB = prove
 (`(!a b. gcd(a - b,b) = gcd(a,b)) /\
   (!a b. gcd(b - a,b) = gcd(a,b)) /\
   (!a b. gcd(a,a - b) = gcd(a,b)) /\
   (!a b. gcd(a,b - a) = gcd(a,b))`,
  SIMP_TAC[INT_GCD_UNIQUE; INT_GCD_POS] THEN INTEGER_TAC);;

let INT_DIVIDES_GCD_LEFT = prove
 (`!m n:int. m divides n <=> gcd(m,n) = abs m`,
  SIMP_TAC[INT_GCD_UNIQUE; INT_ABS_POS; INT_DIVIDES_ABS; INT_DIVIDES_REFL] THEN
  MESON_TAC[INT_DIVIDES_REFL; INT_DIVIDES_TRANS]);;

let INT_DIVIDES_GCD_RIGHT = prove
 (`!m n:int. n divides m <=> gcd(m,n) = abs n`,
  SIMP_TAC[INT_GCD_UNIQUE; INT_ABS_POS; INT_DIVIDES_ABS; INT_DIVIDES_REFL] THEN
  MESON_TAC[INT_DIVIDES_REFL; INT_DIVIDES_TRANS]);;

let INT_GCD_EQ = prove
 (`!x y u v:int.
        (!d. d divides x /\ d divides y <=> d divides u /\ d divides v)
        ==> gcd(x,y) = gcd(u,v)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM INT_DIVIDES_ANTISYM_POS; INT_GCD_POS] THEN
  ASM_REWRITE_TAC[INT_DIVIDES_GCD; INT_GCD_DIVIDES] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[INT_GCD_DIVIDES]);;

let INT_GCD_LNEG = prove
 (`!a b:int. gcd(--a,b) = gcd(a,b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INT_GCD_EQ THEN INTEGER_TAC);;

let INT_GCD_RNEG = prove
 (`!a b:int. gcd(a,--b) = gcd(a,b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INT_GCD_EQ THEN INTEGER_TAC);;

let INT_GCD_NEG = prove
 (`(!a b. gcd(--a,b) = gcd(a,b)) /\
   (!a b. gcd(a,--b) = gcd(a,b))`,
  REWRITE_TAC[INT_GCD_LNEG; INT_GCD_RNEG]);;

let INT_GCD_LABS = prove
 (`!a b. gcd(abs a,b) = gcd(a,b)`,
  REWRITE_TAC[INT_ABS] THEN MESON_TAC[INT_GCD_LNEG]);;

let INT_GCD_RABS = prove
 (`!a b. gcd(a,abs b) = gcd(a,b)`,
  REWRITE_TAC[INT_ABS] THEN MESON_TAC[INT_GCD_RNEG]);;

let INT_GCD_ABS = prove
 (`(!a b. gcd(abs a,b) = gcd(a,b)) /\
   (!a b. gcd(a,abs b) = gcd(a,b))`,
  REWRITE_TAC[INT_GCD_LABS; INT_GCD_RABS]);;

let INT_GCD_LMUL = prove
 (`!a b c:int. gcd(c * a,c * b) = abs c * gcd(a,b)`,
  ONCE_REWRITE_TAC[GSYM INT_ABS_GCD] THEN REWRITE_TAC[GSYM INT_ABS_MUL] THEN
  REWRITE_TAC[GSYM INT_DIVIDES_ANTISYM_ABS] THEN CONV_TAC INTEGER_RULE);;

let INT_GCD_RMUL = prove
 (`!a b c:int. gcd(a * c,b * c) = gcd(a,b) * abs c`,
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN REWRITE_TAC[INT_GCD_LMUL]);;

let INT_GCD_COPRIME_LMUL = prove
 (`!a b c:int. coprime(a,b) ==> gcd(a * b,c) = gcd(a,c) * gcd(b,c)`,
  ONCE_REWRITE_TAC[GSYM INT_ABS_GCD] THEN REWRITE_TAC[GSYM INT_ABS_MUL] THEN
  REWRITE_TAC[GSYM INT_DIVIDES_ANTISYM_ABS] THEN CONV_TAC INTEGER_RULE);;

let INT_GCD_COPRIME_RMUL = prove
 (`!a b c:int. coprime(b,c) ==> gcd(a, b * c) = gcd(a,b) * gcd(a,c)`,
  ONCE_REWRITE_TAC[INT_GCD_SYM] THEN REWRITE_TAC[INT_GCD_COPRIME_LMUL]);;

let INT_GCD_COPRIME_DIVIDES_LMUL = prove
 (`!a b c:int. coprime(a,b) /\ a divides c
                ==> gcd(a * b,c) = abs a * gcd(b,c)`,
  ONCE_REWRITE_TAC[GSYM INT_ABS_GCD] THEN REWRITE_TAC[GSYM INT_ABS_MUL] THEN
  REWRITE_TAC[GSYM INT_DIVIDES_ANTISYM_ABS] THEN CONV_TAC INTEGER_RULE);;

let INT_GCD_COPRIME_DIVIDES_RMUL = prove
 (`!a b c:int. coprime(b,c) /\ b divides a
               ==> gcd(a,b * c) = abs b * gcd(a,c)`,
 ONCE_REWRITE_TAC[INT_GCD_SYM] THEN
 REWRITE_TAC[INT_GCD_COPRIME_DIVIDES_LMUL]);;

let INT_GCD_COPRIME_EXISTS = prove
 (`!a b. ?a' b'. a = a' * gcd(a,b) /\ b = b' * gcd(a,b) /\ coprime(a',b')`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `gcd(a,b):int = &0` THENL
   [ALL_TAC; POP_ASSUM MP_TAC THEN CONV_TAC INTEGER_RULE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_GCD_EQ_0]) THEN
  REPEAT(EXISTS_TAC `&1:int`) THEN ASM_REWRITE_TAC[INT_GCD_0] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about lcms.                                                        *)
(* ------------------------------------------------------------------------- *)

let INT_ABS_LCM = prove
 (`!a b. abs(lcm(a,b)) = lcm(a,b)`,
  REWRITE_TAC[INT_ABS; INT_LCM_POS]);;

let INT_LCM_EQ_0 = prove
 (`!m n. lcm(m,n) = &0 <=> m = &0 \/ n = &0`,
  REWRITE_TAC[INTEGER_RULE `n:int = &0 <=> &0 divides n`] THEN
  REWRITE_TAC[INT_DIVIDES_LCM_GCD] THEN INTEGER_TAC);;

let INT_DIVIDES_LCM = prove
 (`!m n r. r divides m \/ r divides n ==> r divides lcm(m,n)`,
  REWRITE_TAC[INT_DIVIDES_LCM_GCD] THEN INTEGER_TAC);;

let INT_LCM_0 = prove
 (`(!n. lcm(&0,n) = &0) /\ (!n. lcm(n,&0) = &0)`,
  REWRITE_TAC[INT_LCM_EQ_0]);;

let INT_LCM_1 = prove
 (`(!n. lcm(&1,n) = abs n) /\ (!n. lcm(n,&1) = abs n)`,
  SIMP_TAC[int_lcm; INT_MUL_LID; INT_MUL_RID; INT_GCD_1] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_DIV_1; INT_ABS_NUM]);;

let INT_LCM_UNIQUE_ABS = prove
 (`!a b m.
        lcm(a,b) = abs m <=>
        a divides m /\
        b divides m /\
        (!n. a divides n /\ b divides n  ==> m divides n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_ABS_LCM] THEN
  REWRITE_TAC[GSYM INT_DIVIDES_ANTISYM_ABS; INT_DIVIDES_ANTISYM_MULTIPLES] THEN
  REWRITE_TAC[INT_LCM_DIVIDES] THEN
  MESON_TAC[INT_DIVIDES_REFL; INT_DIVIDES_TRANS]);;

let INT_LCM_UNIQUE = prove
 (`!a b m.
        lcm(a,b) = m <=>
        &0 <= m /\
        a divides m /\
        b divides m /\
        (!n. a divides n /\ b divides n ==> m divides n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_LCM_UNIQUE_ABS] THEN
  MP_TAC(SPECL [`a:int`; `b:int`] INT_LCM_POS) THEN INT_ARITH_TAC);;

let INT_LCM_EQ = prove
 (`!x y u v.
        (!m. x divides m /\ y divides m <=> u divides m /\ v divides m)
        ==> lcm(x,y) = lcm(u,v)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM INT_ABS_LCM] THEN
  REWRITE_TAC[GSYM INT_DIVIDES_ANTISYM_ABS; INT_DIVIDES_ANTISYM_MULTIPLES] THEN
  ASM_REWRITE_TAC[INT_LCM_DIVIDES]);;

let INT_LCM_REFL = prove
 (`!n. lcm(n,n) = abs n`,
  REWRITE_TAC[int_lcm; INT_GCD_REFL; INT_ENTIRE] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_ABS_NUM; INT_ABS_MUL] THEN
  ASM_SIMP_TAC[INT_DIV_MUL; INT_ABS_ZERO]);;

let INT_LCM_SYM = prove
 (`!m n. lcm(m,n) = lcm(n,m)`,
  REWRITE_TAC[int_lcm; INT_GCD_SYM; INT_MUL_SYM]);;

let INT_LCM_ASSOC = prove
 (`!m n p. lcm(m,lcm(n,p)) = lcm(lcm(m,n),p)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM INT_ABS_LCM] THEN
  REWRITE_TAC[GSYM INT_DIVIDES_ANTISYM_ABS; INT_DIVIDES_ANTISYM_MULTIPLES] THEN
  REWRITE_TAC[INT_LCM_DIVIDES] THEN REWRITE_TAC[CONJ_ASSOC]);;

let INT_LCM_LNEG = prove
 (`!a b:int. lcm(--a,b) = lcm(a,b)`,
  SIMP_TAC[int_lcm; INT_MUL_LNEG; INT_ABS_NEG; INT_GCD_LNEG; INT_NEG_EQ_0]);;

let INT_LCM_RNEG = prove
 (`!a b:int. lcm(a,--b) = lcm(a,b)`,
  SIMP_TAC[int_lcm; INT_MUL_RNEG; INT_ABS_NEG; INT_GCD_RNEG; INT_NEG_EQ_0]);;

let INT_LCM_NEG = prove
 (`(!a b. lcm(--a,b) = lcm(a,b)) /\
   (!a b. lcm(a,--b) = lcm(a,b))`,
  REWRITE_TAC[INT_LCM_LNEG; INT_LCM_RNEG]);;

let INT_LCM_LABS = prove
 (`!a b. lcm(abs a,b) = lcm(a,b)`,
  REWRITE_TAC[INT_ABS] THEN MESON_TAC[INT_LCM_LNEG]);;

let INT_LCM_RABS = prove
 (`!a b. lcm(a,abs b) = lcm(a,b)`,
  REWRITE_TAC[INT_ABS] THEN MESON_TAC[INT_LCM_RNEG]);;

let INT_LCM_ABS = prove
 (`(!a b. lcm(abs a,b) = lcm(a,b)) /\
   (!a b. lcm(a,abs b) = lcm(a,b))`,
  REWRITE_TAC[INT_LCM_LABS; INT_LCM_RABS]);;

let INT_LCM_LMUL = prove
 (`!a b c:int. lcm(c * a,c * b) = abs c * lcm(a,b)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`a:int = &0`; `b:int = &0`; `c:int = &0`] THEN
  ASM_REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO; INT_ABS_NUM; INT_LCM_0] THEN
  MATCH_MP_TAC(INT_RING `!x:int. ~(x = &0) /\ a * x = b * x ==> a = b`) THEN
  EXISTS_TAC `gcd(c * a:int,c * b)` THEN
  ASM_REWRITE_TAC[INT_GCD_EQ_0; INT_ENTIRE; INT_MUL_LCM_GCD] THEN
  REWRITE_TAC[INT_GCD_LMUL; INT_MUL_LCM_GCD;
              INT_ARITH `(x * a) * x * b:int = x * x * a * b`] THEN
  REWRITE_TAC[INT_ABS_MUL; INT_MUL_AC]);;

let INT_LCM_RMUL = prove
 (`!a b c:int. lcm(a * c,b * c) = lcm(a,b) * abs c`,
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN REWRITE_TAC[INT_LCM_LMUL]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas about coprimality.                                            *)
(* ------------------------------------------------------------------------- *)

let INT_COPRIME = prove
 (`!a b. coprime(a,b) <=> !d. d divides a /\ d divides b ==> d divides &1`,
  REWRITE_TAC[INT_COPRIME_GCD; INT_GCD_UNIQUE; INT_POS; INT_DIVIDES_1]);;

let INT_COPRIME_ALT = prove
 (`!a b. coprime(a,b) <=> !d. d divides a /\ d divides b <=> d divides &1`,
  MESON_TAC[INT_DIVIDES_1; INT_DIVIDES_TRANS; INT_COPRIME]);;

let INT_COPRIME_SYM = prove
 (`!a b. coprime(a,b) <=> coprime(b,a)`,
  INTEGER_TAC);;

let INT_COPRIME_DIVPROD = prove
 (`!d a b. d divides (a * b) /\ coprime(d,a) ==> d divides b`,
  INTEGER_TAC);;

let INT_COPRIME_1 = prove
 (`!a. coprime(a,&1) /\ coprime(&1,a)`,
  INTEGER_TAC);;

let INT_GCD_COPRIME = prove
 (`!a b a' b'. ~(gcd(a,b) = &0) /\ a = a' * gcd(a,b) /\ b = b' * gcd(a,b)
               ==> coprime(a',b')`,
  INTEGER_TAC);;

let INT_COPRIME_0 = prove
 (`(!a. coprime(a,&0) <=> a divides &1) /\
   (!a. coprime(&0,a) <=> a divides &1)`,
  INTEGER_TAC);;

let INT_COPRIME_MUL = prove
 (`!d a b. coprime(d,a) /\ coprime(d,b) ==> coprime(d,a * b)`,
  INTEGER_TAC);;

let INT_COPRIME_LMUL2 = prove
 (`!d a b. coprime(d,a * b) ==> coprime(d,b)`,
  INTEGER_TAC);;

let INT_COPRIME_RMUL2 = prove
 (`!d a b.  coprime(d,a * b) ==> coprime(d,a)`,
  INTEGER_TAC);;

let INT_COPRIME_LMUL = prove
 (`!d a b. coprime(a * b,d) <=> coprime(a,d) /\ coprime(b,d)`,
  INTEGER_TAC);;

let INT_COPRIME_RMUL = prove
 (`!d a b. coprime(d,a * b) <=> coprime(d,a) /\ coprime(d,b)`,
  INTEGER_TAC);;

let INT_COPRIME_REFL = prove
 (`!n. coprime(n,n) <=> n divides &1`,
  INTEGER_TAC);;

let INT_COPRIME_PLUS1 = prove
 (`!n. coprime(n + &1,n) /\ coprime(n,n + &1)`,
  INTEGER_TAC);;

let INT_COPRIME_MINUS1 = prove
 (`!n. coprime(n - &1,n) /\ coprime(n,n - &1)`,
  INTEGER_TAC);;

let INT_COPRIME_RPOW = prove
 (`!m n k. coprime(m,n pow k) <=> coprime(m,n) \/ k = 0`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[INT_POW; INT_COPRIME_1; INT_COPRIME_RMUL; NOT_SUC] THEN
  CONV_TAC TAUT);;

let INT_COPRIME_LPOW = prove
 (`!m n k. coprime(m pow k,n) <=> coprime(m,n) \/ k = 0`,
  ONCE_REWRITE_TAC[INT_COPRIME_SYM] THEN REWRITE_TAC[INT_COPRIME_RPOW]);;

let INT_COPRIME_POW2 = prove
 (`!m n k. coprime(m pow k,n pow k) <=> coprime(m,n) \/ k = 0`,
  REWRITE_TAC[INT_COPRIME_RPOW; INT_COPRIME_LPOW; DISJ_ACI]);;

let INT_COPRIME_POW = prove
 (`!n a d. coprime(d,a) ==> coprime(d,a pow n)`,
  SIMP_TAC[INT_COPRIME_RPOW]);;

let INT_COPRIME_POW_IMP = prove
 (`!n a b. coprime(a,b) ==> coprime(a pow n,b pow n)`,
  MESON_TAC[INT_COPRIME_POW; INT_COPRIME_SYM]);;

let INT_GCD_POW = prove
 (`!(a:int) b n. gcd(a pow n,b pow n) = gcd(a,b) pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`] INT_GCD_COPRIME_EXISTS) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a':int`; `b':int`] THEN
  STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_POW_MUL; INT_GCD_RMUL; INT_ABS_POW] THEN
  ASM_SIMP_TAC[fst(EQ_IMP_RULE(SPEC_ALL INT_COPRIME_GCD));
               INT_COPRIME_POW2; INT_POW_ONE]);;

let INT_LCM_POW = prove
 (`!(a:int) b n. lcm(a pow n,b pow n) = lcm(a,b) pow n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[INT_POW; INT_LCM_1; INT_POW_ONE; INT_ABS_NUM] THEN
  MAP_EVERY ASM_CASES_TAC [`a:int = &0`; `b:int = &0`] THEN
  ASM_REWRITE_TAC[INT_POW_ZERO; INT_LCM_0] THEN
  MATCH_MP_TAC(INT_RING `!x:int. ~(x = &0) /\ a * x = b * x ==> a = b`) THEN
  EXISTS_TAC `gcd((a:int) pow n,b pow n)` THEN
  ASM_REWRITE_TAC[INT_GCD_EQ_0; INT_POW_EQ_0; INT_MUL_LCM_GCD] THEN
  REWRITE_TAC[INT_GCD_POW; GSYM INT_POW_MUL] THEN
  REWRITE_TAC[INT_MUL_LCM_GCD; INT_ABS_POW]);;

let INT_DIVISION_DECOMP = prove
 (`!a b c. a divides (b * c)
           ==> ?b' c'. (a = b' * c') /\ b' divides b /\ c' divides c`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `gcd(a,b)` THEN
  ASM_CASES_TAC `gcd(a,b) = &0` THEN REPEAT(POP_ASSUM MP_TAC) THENL
   [SIMP_TAC[INT_GCD_EQ_0; INT_GCD_0; INT_ABS_NUM]; INTEGER_TAC] THEN
  REWRITE_TAC[INT_MUL_LZERO] THEN MESON_TAC[INT_DIVIDES_REFL]);;

let INT_DIVIDES_MUL = prove
 (`!m n r. m divides r /\ n divides r /\ coprime(m,n) ==> (m * n) divides r`,
  INTEGER_TAC);;

let INT_CHINESE_REMAINDER = prove
 (`!a b u v. coprime(a,b) /\ ~(a = &0) /\ ~(b = &0)
             ==> ?x q1 q2. (x = u + q1 * a) /\ (x = v + q2 * b)`,
  INTEGER_TAC);;

let INT_CHINESE_REMAINDER_USUAL = prove
 (`!a b u v. coprime(a,b) ==> ?x. (x == u) (mod a) /\ (x == v) (mod b)`,
  INTEGER_TAC);;

let INT_COPRIME_DIVISORS = prove
 (`!a b d e. d divides a /\ e divides b /\ coprime(a,b) ==> coprime(d,e)`,
  INTEGER_TAC);;

let INT_COPRIME_LNEG = prove
 (`!a b. coprime(--a,b) <=> coprime(a,b)`,
  INTEGER_TAC);;

let INT_COPRIME_RNEG = prove
 (`!a b. coprime(a,--b) <=> coprime(a,b)`,
  INTEGER_TAC);;

let INT_COPRIME_NEG = prove
 (`(!a b. coprime(--a,b) <=> coprime(a,b)) /\
   (!a b. coprime(a,--b) <=> coprime(a,b))`,
  INTEGER_TAC);;

let INT_COPRIME_LABS = prove
 (`!a b. coprime(abs a,b) <=> coprime(a,b)`,
  REWRITE_TAC[INT_ABS] THEN MESON_TAC[INT_COPRIME_LNEG]);;

let INT_COPRIME_RABS = prove
 (`!a b. coprime(a,abs b) <=> coprime(a,b)`,
  REWRITE_TAC[INT_ABS] THEN MESON_TAC[INT_COPRIME_RNEG]);;

let INT_COPRIME_ABS = prove
 (`(!a b. coprime(abs a,b) <=> coprime(a,b)) /\
   (!a b. coprime(a,abs b) <=> coprime(a,b))`,
  REWRITE_TAC[INT_COPRIME_LABS; INT_COPRIME_RABS]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas about congruences.                                            *)
(* ------------------------------------------------------------------------- *)

let INT_CONG_MOD_0 = prove
 (`!x y. (x == y) (mod &0) <=> (x = y)`,
  INTEGER_TAC);;

let INT_CONG_MOD_1 = prove
 (`!x y. (x == y) (mod &1)`,
  INTEGER_TAC);;

let INT_CONG = prove
 (`!x y n. (x == y) (mod n) <=> n divides (x - y)`,
  INTEGER_TAC);;

let INT_CONG_MOD_ABS = prove
 (`!a b n:int. (a == b) (mod (abs n)) <=> (a == b) (mod n)`,
  REWRITE_TAC[INT_CONG; INT_DIVIDES_LABS]);;

let INT_CONG_MUL_LCANCEL = prove
 (`!a n x y. coprime(a,n) /\ (a * x == a * y) (mod n) ==> (x == y) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_MUL_RCANCEL = prove
 (`!a n x y. coprime(a,n) /\ (x * a == y * a) (mod n) ==> (x == y) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_MULT_LCANCEL_ALL = INTEGER_RULE
  `!a x y n:int.
      (a * x == a * y) (mod (a * n)) <=> a = &0 \/ (x == y) (mod n)`;;

let INT_CONG_LMUL = INTEGER_RULE
 `!a x y n:int. (x == y) (mod n) ==> (a * x == a * y) (mod n)`;;

let INT_CONG_RMUL = INTEGER_RULE
 `!x y a n:int. (x == y) (mod n) ==> (x * a == y * a) (mod n)`;;

let INT_CONG_REFL = prove
 (`!x n. (x == x) (mod n)`,
  INTEGER_TAC);;

let INT_EQ_IMP_CONG = prove
 (`!a b n. a = b ==> (a == b) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_SYM = prove
 (`!x y n. (x == y) (mod n) <=> (y == x) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_TRANS = prove
 (`!x y z n. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_ADD = prove
 (`!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) ==> (x + y == x' + y') (mod n)`,
  INTEGER_TAC);;

let INT_CONG_SUB = prove
 (`!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) ==> (x - y == x' - y') (mod n)`,
  INTEGER_TAC);;

let INT_CONG_MUL = prove
 (`!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) ==> (x * y == x' * y') (mod n)`,
  INTEGER_TAC);;

let INT_CONG_POW = prove
 (`!n k x y. (x == y) (mod n) ==> (x pow k == y pow k) (mod n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[INT_CONG_MUL; INT_POW; INT_CONG_REFL]);;

let INT_CONG_MUL_1 = prove
 (`!n x y:int.
        (x == &1) (mod n) /\ (y == &1) (mod n)
        ==> (x * y == &1) (mod n)`,
  MESON_TAC[INT_CONG_MUL; INT_MUL_LID]);;

let INT_CONG_POW_1 = prove
 (`!a k n:int. (a == &1) (mod n) ==> (a pow k == &1) (mod n)`,
  MESON_TAC[INT_CONG_POW; INT_POW_ONE]);;

let INT_CONG_MUL_LCANCEL_EQ = prove
 (`!a n x y. coprime(a,n) ==> ((a * x == a * y) (mod n) <=> (x == y) (mod n))`,
  INTEGER_TAC);;

let INT_CONG_MUL_RCANCEL_EQ = prove
 (`!a n x y. coprime(a,n) ==> ((x * a == y * a) (mod n) <=> (x == y) (mod n))`,
  INTEGER_TAC);;

let INT_CONG_ADD_LCANCEL_EQ = prove
 (`!a n x y. (a + x == a + y) (mod n) <=> (x == y) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_ADD_RCANCEL_EQ = prove
 (`!a n x y. (x + a == y + a) (mod n) <=> (x == y) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_ADD_RCANCEL = prove
 (`!a n x y. (x + a == y + a) (mod n) ==> (x == y) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_ADD_LCANCEL = prove
 (`!a n x y. (a + x == a + y) (mod n) ==> (x == y) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_ADD_LCANCEL_EQ_0 = prove
 (`!a n x y. (a + x == a) (mod n) <=> (x == &0) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_ADD_RCANCEL_EQ_0 = prove
 (`!a n x y. (x + a == a) (mod n) <=> (x == &0) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_INT_DIVIDES_MODULUS = prove
 (`!x y m n. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_0_DIVIDES = prove
 (`!n x. (x == &0) (mod n) <=> n divides x`,
  INTEGER_TAC);;

let INT_CONG_1_DIVIDES = prove
 (`!n x. (x == &1) (mod n) ==> n divides (x - &1)`,
  INTEGER_TAC);;

let INT_CONG_DIVIDES = prove
 (`!x y n. (x == y) (mod n) ==> (n divides x <=> n divides y)`,
  INTEGER_TAC);;

let INT_CONG_COPRIME = prove
 (`!x y n. (x == y) (mod n) ==> (coprime(n,x) <=> coprime(n,y))`,
  INTEGER_TAC);;

let INT_COPRIME_RREM = prove
 (`!m n. coprime(m,n rem m) <=> coprime(m,n)`,
  MESON_TAC[INT_CONG_COPRIME; INT_CONG_RREM; INT_CONG_REFL]);;

let INT_COPRIME_LREM = prove
 (`!a b. coprime(a rem n,n) <=> coprime(a,n)`,
  MESON_TAC[INT_COPRIME_RREM; INT_COPRIME_SYM]);;

let INT_CONG_GCD_RIGHT = prove
 (`!x y n. (x == y) (mod n) ==> gcd(n,x) = gcd(n,y)`,
  REWRITE_TAC[INT_GCD_UNIQUE; INT_GCD_POS] THEN INTEGER_TAC);;

let INT_CONG_GCD_LEFT = prove
 (`!x y n. (x == y) (mod n) ==> gcd(x,n) = gcd(y,n)`,
  REWRITE_TAC[INT_GCD_UNIQUE; INT_GCD_POS] THEN INTEGER_TAC);;

let INT_CONG_TO_1 = prove
 (`!a n. (a == &1) (mod n) <=> ?m. a = &1 + m * n`,
  INTEGER_TAC);;

let INT_CONG_SOLVE = prove
 (`!a b n. coprime(a,n) ==> ?x. (a * x == b) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_SOLVE_EQ = prove
 (`!n a b:int. (?x. (a * x == b) (mod n)) <=> gcd(a,n) divides b`,
  INTEGER_TAC);;

let INT_CONG_SOLVE_UNIQUE = prove
 (`!a b n. coprime(a,n)
           ==> !x y. (a * x == b) (mod n) /\ (a * y == b) (mod n)
                     ==> (x == y) (mod n)`,
  INTEGER_TAC);;

let INT_CONG_CHINESE = prove
 (`coprime(a,b) /\ (x == y) (mod a) /\ (x == y) (mod b)
   ==> (x == y) (mod (a * b))`,
  INTEGER_TAC);;

let INT_CHINESE_REMAINDER_COPRIME = prove
 (`!a b m n.
        coprime(a,b) /\ ~(a = &0) /\ ~(b = &0) /\ coprime(m,a) /\ coprime(n,b)
        ==> ?x. coprime(x,a * b) /\
                (x == m) (mod a) /\ (x == n) (mod b)`,
  INTEGER_TAC);;

let INT_CHINESE_REMAINDER_COPRIME_UNIQUE = prove
 (`!a b m n x y.
        coprime(a,b) /\
        (x == m) (mod a) /\ (x == n) (mod b) /\
        (y == m) (mod a) /\ (y == n) (mod b)
        ==> (x == y) (mod (a * b))`,
  INTEGER_TAC);;

let SOLVABLE_GCD = prove
 (`!a b n. gcd(a,n) divides b ==> ?x. (a * x == b) (mod n)`,
  INTEGER_TAC);;

let INT_LINEAR_CONG_POS = prove
 (`!n a x:int. ~(n = &0) ==> ?y. &0 <= y /\ (a * x == a * y) (mod n)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `x + abs(x * n):int` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `abs(x:int) * &1 <= y ==> &0 <= x + y`) THEN
    REWRITE_TAC[INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_LMUL THEN
    ASM_INT_ARITH_TAC;
    MATCH_MP_TAC(INTEGER_RULE
     `n divides y ==> (a * x:int == a * (x + y)) (mod n)`) THEN
    REWRITE_TAC[INT_DIVIDES_RABS] THEN INTEGER_TAC]);;

let INT_CONG_SOLVE_POS = prove
 (`!a b n:int.
        coprime(a,n) /\ ~(n = &0 /\ abs a = &1)
        ==> ?x. &0 <= x /\ (a * x == b) (mod n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:int = &0` THEN
  ASM_REWRITE_TAC[INT_COPRIME_0; INT_DIVIDES_ONE] THENL
   [INT_ARITH_TAC;
    ASM_MESON_TAC[INT_LINEAR_CONG_POS; INT_CONG_SOLVE; INT_CONG_TRANS;
                  INT_CONG_SYM]]);;

let INT_CONG_IMP_EQ = prove
 (`!x y n:int. abs(x - y) < n /\ (x == y) (mod n) ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[int_congruent; GSYM INT_SUB_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:int` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `abs(n * q) < n ==> abs(n * q) < abs n * &1`)) THEN
  REWRITE_TAC[INT_ABS_MUL; INT_ENTIRE] THEN
  REWRITE_TAC[INT_ARITH
   `abs n * (q:int) < abs n * &1 <=> ~(&0 <= abs n * (q - &1))`] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC);;

let INT_CONG_DIV = prove
 (`!m n a b.
        ~(m = &0) /\ (a == m * b) (mod (m * n)) ==> (a div m == b) (mod n)`,
  METIS_TAC[INT_CONG_DIV2; INT_DIV_MUL; INT_LT_LE]);;

let INT_CONG_DIV_COPRIME = prove
 (`!m n a b:int.
        coprime(m,n) /\ m divides a /\ (a == m * b) (mod n)
        ==> (a div m == b) (mod n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m:int = &0` THEN
  ASM_SIMP_TAC[INT_COPRIME_0; INT_CONG_MOD_1] THENL
   [INTEGER_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INT_CONG_DIV THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* A stronger form of the CRT.                                               *)
(* ------------------------------------------------------------------------- *)

let INT_CRT_STRONG = prove
 (`!a1 a2 n1 n2:int.
        (a1 == a2) (mod (gcd(n1,n2)))
        ==> ?x. (x == a1) (mod n1) /\ (x == a2) (mod n2)`,
  INTEGER_TAC);;

let INT_CRT_STRONG_IFF = prove
 (`!a1 a2 n1 n2:int.
        (?x. (x == a1) (mod n1) /\ (x == a2) (mod n2)) <=>
        (a1 == a2) (mod (gcd(n1,n2)))`,
  INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Other miscellaneous lemmas.                                               *)
(* ------------------------------------------------------------------------- *)

let EVEN_SQUARE_MOD4 = prove
 (`((&2 * n) pow 2 == &0) (mod &4)`,
  INTEGER_TAC);;

let ODD_SQUARE_MOD4 = prove
 (`((&2 * n + &1) pow 2 == &1) (mod &4)`,
  INTEGER_TAC);;

let INT_DIVIDES_LE = prove
 (`!x y. x divides y ==> abs(x) <= abs(y) \/ y = &0`,
  REWRITE_TAC[int_divides; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`; `z:int`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_ABS_MUL; INT_ENTIRE] THEN
  REWRITE_TAC[INT_ARITH `x <= x * z <=> &0 <= x * (z - &1)`] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `z = &0` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC);;

let INT_DIVIDES_POW_LE = prove
 (`!p m n. &2 <= abs p ==> ((p pow m) divides (p pow n) <=> m <= n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
    ASM_SIMP_TAC[INT_POW_EQ_0; INT_ARITH `&2 <= abs p ==> ~(p = &0)`] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[INT_NOT_LE; NOT_LE; INT_ABS_POW] THEN
    ASM_MESON_TAC[INT_POW_MONO_LT; ARITH_RULE `&2 <= x ==> &1 < x`];
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; INT_POW_ADD] THEN INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Integer primality / irreducibility.                                       *)
(* ------------------------------------------------------------------------- *)

let int_prime = new_definition
 `int_prime p <=> abs(p) > &1 /\
                  !x. x divides p ==> abs(x) = &1 \/ abs(x) = abs(p)`;;

let INT_PRIME_NEG = prove
 (`!p. int_prime(--p) <=> int_prime p`,
  REWRITE_TAC[int_prime; INT_DIVIDES_RNEG; INT_ABS_NEG]);;

let INT_PRIME_ABS = prove
 (`!p. int_prime(abs p) <=> int_prime p`,
  GEN_TAC THEN REWRITE_TAC[INT_ABS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_PRIME_NEG]);;

let INT_PRIME_GE_2 = prove
 (`!p. int_prime p ==> &2 <= abs(p)`,
  REWRITE_TAC[int_prime] THEN INT_ARITH_TAC);;

let INT_PRIME_0 = prove
 (`~(int_prime(&0))`,
  REWRITE_TAC[int_prime] THEN INT_ARITH_TAC);;

let INT_PRIME_1 = prove
 (`~(int_prime(&1))`,
  REWRITE_TAC[int_prime] THEN INT_ARITH_TAC);;

let INT_PRIME_2 = prove
 (`int_prime(&2)`,
  REWRITE_TAC[int_prime] THEN CONV_TAC INT_REDUCE_CONV THEN
  X_GEN_TAC `x:int` THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[INT_DIVIDES_ZERO] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC);;

let INT_PRIME_FACTOR = prove
 (`!x. ~(abs x = &1) ==> ?p. int_prime p /\ p divides x`,
  MATCH_MP_TAC WF_INT_MEASURE THEN EXISTS_TAC `abs` THEN
  REWRITE_TAC[INT_ABS_POS] THEN X_GEN_TAC `x:int` THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `int_prime x` THENL
   [EXISTS_TAC `x:int` THEN ASM_REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN INTEGER_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[INT_PRIME_2; INT_DIVIDES_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [int_prime]) THEN
  ASM_SIMP_TAC[INT_ARITH `~(x = &0) /\ ~(abs x = &1) ==> abs x > &1`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:int` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:int`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC[] THEN
    UNDISCH_TAC `y divides x` THEN INTEGER_TAC]);;

let INT_PRIME_FACTOR_LT = prove
 (`!n m p. int_prime(p) /\ ~(n = &0) /\ n = p * m ==> abs m < abs n`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INT_ABS_MUL] THEN
  MATCH_MP_TAC(INT_ARITH `&0 < m * (p - &1) ==> m < p * m`) THEN
  MATCH_MP_TAC INT_LT_MUL THEN
  UNDISCH_TAC `~(n = &0)` THEN ASM_CASES_TAC `m = &0` THEN
  ASM_REWRITE_TAC[INT_MUL_RZERO] THEN DISCH_THEN(K ALL_TAC) THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INT_PRIME_GE_2) THEN INT_ARITH_TAC);;

let INT_PRIME_FACTOR_INDUCT = prove
 (`!P. P(&0) /\ P(&1) /\ P(-- &1) /\
       (!p n. int_prime p /\ ~(n = &0) /\ P n ==> P(p * n))
       ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC WF_INT_MEASURE THEN EXISTS_TAC `abs` THEN
  REWRITE_TAC[INT_ABS_POS] THEN X_GEN_TAC `n:int` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `abs n = &1` THENL
   [ASM_MESON_TAC[INT_ARITH `abs x = &a <=> x = &a \/ x = -- &a`];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:int`
    STRIP_ASSUME_TAC o MATCH_MP INT_PRIME_FACTOR) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:int` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [int_divides]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:int`; `d:int`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_ENTIRE; DE_MORGAN_THM]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[INT_PRIME_FACTOR_LT; INT_ENTIRE]);;

(* ------------------------------------------------------------------------- *)
(* Infinitude.                                                               *)
(* ------------------------------------------------------------------------- *)

let INT_DIVIDES_FACT = prove
 (`!n x. &1 <= abs(x) /\ abs(x) <= &n ==> x divides &(FACT n)`,
  INDUCT_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FACT; INT_ARITH `x <= &n <=> x = &n \/ x < &n`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ARITH `x < &m + &1 <=> x <= &m`] THEN
  REWRITE_TAC[INT_OF_NUM_SUC; GSYM INT_OF_NUM_MUL] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INT_DIVIDES_LMUL] THEN
  MATCH_MP_TAC INT_DIVIDES_RMUL THEN
  ASM_MESON_TAC[INT_DIVIDES_LABS; INT_DIVIDES_REFL]);;

let INT_EUCLID_BOUND = prove
 (`!n. ?p. int_prime(p) /\ &n < p /\ p <= &(FACT n) + &1`,
  GEN_TAC THEN MP_TAC(SPEC `&(FACT n) + &1` INT_PRIME_FACTOR) THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_ABS_NUM; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[EQ_ADD_RCANCEL_0; FACT_NZ; GSYM INT_OF_NUM_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `abs p` THEN ASM_REWRITE_TAC[INT_PRIME_ABS] THEN CONJ_TAC THENL
   [ALL_TAC;
    FIRST_ASSUM(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUC] THEN
    INT_ARITH_TAC] THEN
  REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `p:int`] INT_DIVIDES_FACT) THEN
  ASM_SIMP_TAC[INT_PRIME_GE_2; INT_ARITH `&2 <= p ==> &1 <= p`] THEN
  DISCH_TAC THEN SUBGOAL_THEN `p divides &1` MP_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN INTEGER_TAC;
    REWRITE_TAC[INT_DIVIDES_ONE] THEN
    ASM_MESON_TAC[INT_PRIME_NEG; INT_PRIME_1]]);;

let INT_EUCLID = prove
 (`!n. ?p. int_prime(p) /\ p > n`,
  MP_TAC INT_IMAGE THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `n:int` THEN REWRITE_TAC[INT_GT] THEN
  ASM_REWRITE_TAC[OR_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MP_TAC INT_EUCLID_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN INT_ARITH_TAC);;

let INT_PRIMES_INFINITE = prove
 (`INFINITE {p | int_prime p}`,
  SUBGOAL_THEN `INFINITE {n | int_prime(&n)}` MP_TAC THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THENL
   [REWRITE_TAC[num_FINITE; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; NOT_LE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; INT_EXISTS_POS] THEN
    MP_TAC INT_EUCLID_BOUND THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    SIMP_TAC[] THEN INT_ARITH_TAC;
    MP_TAC(ISPECL [`&`; `{p | int_prime p}`] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[INT_OF_NUM_EQ; IN_ELIM_THM]]);;

let INT_COPRIME_PRIME = prove
 (`!p a b. coprime(a,b) ==> ~(int_prime(p) /\ p divides a /\ p divides b)`,
  REWRITE_TAC[INT_COPRIME] THEN
  MESON_TAC[INT_DIVIDES_ONE; INT_PRIME_NEG; INT_PRIME_1]);;

let INT_COPRIME_PRIME_EQ = prove
 (`!a b. coprime(a,b) <=> !p. ~(int_prime(p) /\ p divides a /\ p divides b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[INT_COPRIME_PRIME]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[INT_COPRIME; INT_DIVIDES_ONE_ABS] THEN
  ONCE_REWRITE_TAC[NOT_FORALL_THM] THEN REWRITE_TAC[NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `p:int` o MATCH_MP INT_PRIME_FACTOR) THEN
  EXISTS_TAC `p:int` THEN ASM_MESON_TAC[INT_DIVIDES_TRANS]);;

let INT_PRIME_COPRIME = prove
 (`!x p. int_prime(p) ==> p divides x \/ coprime(p,x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_COPRIME] THEN
  MATCH_MP_TAC(TAUT `(~b ==> a) ==> a \/ b`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; INT_DIVIDES_ONE_ABS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [int_prime]) THEN
  DISCH_THEN(MP_TAC o SPEC `d:int` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[INT_DIVIDES_TRANS; INT_DIVIDES_LABS; INT_DIVIDES_RABS]);;

let INT_PRIME_COPRIME_EQ = prove
 (`!p n. int_prime p ==> (coprime(p,n) <=> ~(p divides n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(b \/ a) /\ ~(a /\ b) ==> (a <=> ~b)`) THEN
  ASM_SIMP_TAC[INT_PRIME_COPRIME; INT_COPRIME; INT_DIVIDES_ONE_ABS] THEN
  ASM_MESON_TAC[INT_DIVIDES_REFL; INT_PRIME_1; INT_PRIME_ABS]);;

let INT_COPRIME_PRIMEPOW = prove
 (`!p k m. int_prime p /\ ~(k = 0)
           ==> (coprime(m,p pow k) <=> ~(p divides m))`,
  SIMP_TAC[INT_COPRIME_RPOW] THEN ONCE_REWRITE_TAC[INT_COPRIME_SYM] THEN
  SIMP_TAC[INT_PRIME_COPRIME_EQ]);;

let INT_COPRIME_BEZOUT = prove
 (`!a b. coprime(a,b) <=> ?x y. a * x + b * y = &1`,
  INTEGER_TAC);;

let INT_COPRIME_BEZOUT_ALT = prove
 (`!a b. coprime(a,b) ==> ?x y. a * x = b * y + &1`,
  INTEGER_TAC);;

let INT_BEZOUT_PRIME = prove
 (`!a p. int_prime p /\ ~(p divides a) ==> ?x y. a * x = p * y + &1`,
  MESON_TAC[INT_COPRIME_BEZOUT_ALT; INT_COPRIME_SYM; INT_PRIME_COPRIME_EQ]);;

let INT_PRIME_DIVPROD = prove
 (`!p a b. int_prime(p) /\ p divides (a * b) ==> p divides a \/ p divides b`,
  ONCE_REWRITE_TAC[TAUT `a /\ b ==> c \/ d <=> a ==> (~c /\ ~d ==> ~b)`] THEN
  SIMP_TAC[GSYM INT_PRIME_COPRIME_EQ] THEN INTEGER_TAC);;

let INT_PRIME_DIVPROD_EQ = prove
 (`!p a b. int_prime(p)
           ==> (p divides (a * b) <=> p divides a \/ p divides b)`,
  MESON_TAC[INT_PRIME_DIVPROD; INT_DIVIDES_LMUL; INT_DIVIDES_RMUL]);;

let INT_PRIME_DIVPOW = prove
 (`!n p x. int_prime(p) /\ p divides (x pow n) ==> p divides x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  ASM_SIMP_TAC[GSYM INT_PRIME_COPRIME_EQ; INT_COPRIME_POW]);;

let INT_PRIME_DIVPOW_N = prove
 (`!n p x. int_prime p /\ p divides (x pow n) ==> (p pow n) divides (x pow n)`,
  MESON_TAC[INT_PRIME_DIVPOW; INT_DIVIDES_POW]);;

let INT_COPRIME_SOS = prove
 (`!x y. coprime(x,y) ==> coprime(x * y,x pow 2 + y pow 2)`,
  INTEGER_TAC);;

let INT_PRIME_IMP_NZ = prove
 (`!p. int_prime p ==> ~(p = &0)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INT_PRIME_GE_2) THEN
  INT_ARITH_TAC);;

let INT_DISTINCT_PRIME_COPRIME = prove
 (`!p q. int_prime p /\ int_prime q /\ ~(abs p = abs q) ==> coprime(p,q)`,
  REWRITE_TAC[GSYM INT_DIVIDES_ANTISYM_ABS] THEN
  MESON_TAC[INT_COPRIME_SYM; INT_PRIME_COPRIME_EQ]);;

let INT_PRIME_COPRIME_LT = prove
 (`!x p. int_prime p /\ &0 < abs x /\ abs x < abs p ==> coprime(x,p)`,
  ONCE_REWRITE_TAC[INT_COPRIME_SYM] THEN SIMP_TAC[INT_PRIME_COPRIME_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC);;

let INT_DIVIDES_PRIME_PRIME = prove
 (`!p q. int_prime p /\ int_prime q  ==> (p divides q <=> abs p = abs q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    ASM_SIMP_TAC[GSYM INT_PRIME_COPRIME_EQ; INT_DISTINCT_PRIME_COPRIME];
    SIMP_TAC[GSYM INT_DIVIDES_ANTISYM_ABS]]);;

let INT_COPRIME_POW_DIVPROD = prove
 (`!d a b. (d pow n) divides (a * b) /\ coprime(d,a) ==> (d pow n) divides b`,
  MESON_TAC[INT_COPRIME_DIVPROD; INT_COPRIME_POW; INT_COPRIME_SYM]);;

let INT_PRIME_COPRIME_CASES = prove
 (`!p a b. int_prime p /\ coprime(a,b) ==> coprime(p,a) \/ coprime(p,b)`,
  MESON_TAC[INT_COPRIME_PRIME; INT_PRIME_COPRIME_EQ]);;

let INT_PRIME_DIVPROD_POW = prove
 (`!n p a b. int_prime(p) /\ coprime(a,b) /\ (p pow n) divides (a * b)
             ==> (p pow n) divides a \/ (p pow n) divides b`,
  MESON_TAC[INT_COPRIME_POW_DIVPROD; INT_PRIME_COPRIME_CASES; INT_MUL_SYM]);;

let INT_DIVIDES_POW2_REV = prove
 (`!n a b. (a pow n) divides (b pow n) /\ ~(n = 0) ==> a divides b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `gcd(a,b) = &0` THENL
   [ASM_MESON_TAC[INT_GCD_EQ_0; INT_DIVIDES_REFL]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`] INT_GCD_COPRIME_EXISTS) THEN
  STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_POW_MUL] THEN
  ASM_SIMP_TAC[INT_POW_EQ_0; INT_DIVIDES_RMUL2_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
   `a divides b ==> coprime(a,b) ==> a divides &1`)) THEN
  ASM_SIMP_TAC[INT_COPRIME_POW2] THEN
  ASM_MESON_TAC[INT_DIVIDES_POW2; INT_DIVIDES_TRANS; INT_DIVIDES_1]);;

let INT_DIVIDES_POW2_EQ = prove
 (`!n a b. ~(n = 0) ==> ((a pow n) divides (b pow n) <=> a divides b)`,
  MESON_TAC[INT_DIVIDES_POW2_REV; INT_DIVIDES_POW]);;

let INT_POW_MUL_EXISTS = prove
 (`!m n p k. ~(m = &0) /\ m pow k * n = p pow k ==> ?q. n = q pow k`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_SIMP_TAC[INT_POW; INT_MUL_LID] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `m:int`; `p:int`] INT_DIVIDES_POW2_REV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[int_divides; INT_MUL_SYM]; ALL_TAC] THEN
  REWRITE_TAC[int_divides] THEN DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN
  ASM_SIMP_TAC[INT_POW_MUL; INT_EQ_MUL_LCANCEL; INT_POW_EQ_0] THEN
  MESON_TAC[]);;

let INT_COPRIME_POW_ABS = prove
 (`!n a b c. coprime(a,b) /\ a * b = c pow n
             ==> ?r s. abs a = r pow n /\ abs b = s pow n`,
  GEN_TAC THEN GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[INT_POW] THEN MESON_TAC[INT_ABS_MUL_1; INT_ABS_NUM];
    ALL_TAC] THEN
  MATCH_MP_TAC INT_PRIME_FACTOR_INDUCT THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[INT_POW_ZERO; INT_ENTIRE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC DISJ_CASES_TAC) THEN
    ASM_SIMP_TAC[INT_COPRIME_0; INT_DIVIDES_ONE_ABS; INT_ABS_NUM] THEN
    ASM_MESON_TAC[INT_POW_ONE; INT_POW_ZERO];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `abs:int->int`) THEN
    SIMP_TAC[INT_POW_ONE; INT_ABS_NUM; INT_ABS_MUL_1] THEN
    MESON_TAC[INT_POW_ONE];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o AP_TERM `abs:int->int`) THEN
    SIMP_TAC[INT_POW_ONE; INT_ABS_POW; INT_ABS_NEG; INT_ABS_NUM;
             INT_ABS_MUL_1] THEN MESON_TAC[INT_POW_ONE];
    REWRITE_TAC[INT_POW_MUL] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `p pow n divides a \/ p pow n divides b` MP_TAC THENL
     [ASM_MESON_TAC[INT_PRIME_DIVPROD_POW; int_divides]; ALL_TAC] THEN
    REWRITE_TAC[int_divides] THEN
    DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `d:int` SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INT_COPRIME_SYM]) THEN
    ASM_SIMP_TAC[INT_COPRIME_RMUL; INT_COPRIME_LMUL;
                 INT_COPRIME_LPOW; INT_COPRIME_RPOW] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`b:int`; `d:int`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`d:int`; `a:int`])] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [MATCH_MP_TAC(INT_RING `!p. ~(p = &0) /\ a * p = b * p ==> a = b`) THEN
       EXISTS_TAC `p pow n` THEN
       ASM_SIMP_TAC[INT_POW_EQ_0; INT_PRIME_IMP_NZ] THEN
       FIRST_X_ASSUM(MP_TAC o SYM) THEN CONV_TAC INT_RING;
       STRIP_TAC THEN
       ASM_REWRITE_TAC[INT_ABS_POW; GSYM INT_POW_MUL; INT_ABS_MUL] THEN
       MESON_TAC[]])]);;

let INT_COPRIME_POW_ODD = prove
 (`!n a b c. ODD n /\ coprime(a,b) /\ a * b = c pow n
             ==> ?r s. a = r pow n /\ b = s pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `a:int`; `b:int`; `c:int`] INT_COPRIME_POW_ABS) THEN
  ASM_REWRITE_TAC[INT_ABS] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[INT_ABS] THEN
  ASM_MESON_TAC[INT_POW_NEG; INT_NEG_NEG; NOT_ODD]);;

let INT_DIVIDES_PRIME_POW_LE = prove
 (`!p q m n. int_prime p /\ int_prime q
             ==> ((p pow m) divides (q pow n) <=>
                  m = 0 \/ abs p = abs q /\ m <= n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[INT_POW; INT_DIVIDES_1] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM INT_DIVIDES_LABS] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM INT_DIVIDES_RABS] THEN
  REWRITE_TAC[INT_ABS_POW] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`);
    ALL_TAC] THEN
  ASM_MESON_TAC[INT_DIVIDES_POW_LE; INT_PRIME_GE_2; INT_PRIME_DIVPOW;
      INT_ABS_ABS; INT_PRIME_ABS; INT_DIVIDES_POW2; INT_DIVIDES_PRIME_PRIME]);;

let INT_EQ_PRIME_POW_ABS = prove
 (`!p q m n. int_prime p /\ int_prime q
             ==> (abs p pow m = abs q pow n <=>
                  m = 0 /\ n = 0 \/ abs p = abs q /\ m = n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_ABS_POW] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM INT_DIVIDES_ANTISYM_ABS] THEN
  ASM_SIMP_TAC[INT_DIVIDES_PRIME_POW_LE; INT_PRIME_ABS] THEN
  ASM_CASES_TAC `abs p = abs q` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let INT_EQ_PRIME_POW_POS = prove
 (`!p q m n. int_prime p /\ int_prime q /\ &0 <= p /\ &0 <= q
             ==> (p pow m = q pow n <=>
                  m = 0 /\ n = 0 \/ p = q /\ m = n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:int`; `q:int`; `m:num`; `n:num`] INT_EQ_PRIME_POW_ABS) THEN
  ASM_SIMP_TAC[INT_ABS]);;

let INT_DIVIDES_FACT_PRIME = prove
 (`!p. int_prime p ==> !n. p divides &(FACT n) <=> abs p <= &n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[FACT] THENL
   [REWRITE_TAC[INT_ARITH `abs x <= &0 <=> x = &0`] THEN
    ASM_MESON_TAC[INT_DIVIDES_ONE; INT_PRIME_NEG; INT_PRIME_0; INT_PRIME_1];
    ASM_SIMP_TAC[INT_PRIME_DIVPROD_EQ; GSYM INT_OF_NUM_MUL] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
    ASM_MESON_TAC[INT_DIVIDES_LE; INT_ARITH `x <= n ==> x <= n + &1`;
                  INT_DIVIDES_REFL; INT_DIVIDES_LABS;
                  INT_ARITH `p <= n + &1 ==> p <= n \/ p = n + &1`;
                  INT_ARITH `~(&n + &1 = &0)`;
                  INT_ARITH `abs(&n + &1) = &n + &1`]]);;
