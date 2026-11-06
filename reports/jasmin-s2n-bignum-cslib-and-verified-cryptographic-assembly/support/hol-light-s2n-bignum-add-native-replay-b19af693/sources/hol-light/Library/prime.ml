(* ========================================================================= *)
(* Basic theory of divisibility, gcd, coprimality and primality (over N).    *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary theory of divisibility                                         *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_0 = prove
 (`!x. x divides 0`,
  NUMBER_TAC);;

let DIVIDES_ZERO = prove
 (`!x. 0 divides x <=> x = 0`,
  NUMBER_TAC);;

let DIVIDES_1 = prove
 (`!x. 1 divides x`,
  NUMBER_TAC);;

let DIVIDES_REFL = prove
 (`!x. x divides x`,
  NUMBER_TAC);;

let DIVIDES_TRANS = prove
 (`!a b c. a divides b /\ b divides c ==> a divides c`,
  NUMBER_TAC);;

let DIVIDES_ADD = prove
 (`!d a b. d divides a /\ d divides b ==> d divides (a + b)`,
  NUMBER_TAC);;

let DIVIDES_SUB_EQ = prove
 (`!d a b. d divides (a - b) <=> a < b \/ (a == b) (mod d)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN MP_TAC(ARITH_RULE
   `a < b /\ a - b = 0 \/ ~(a < b) /\ (a - b) + b = a`) THEN
  SIMP_TAC[] THEN NUMBER_TAC);;

let DIVIDES_SUB = prove
 (`!d a b. d divides a /\ d divides b ==> d divides (a - b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIVIDES_SUB_EQ] THEN
  DISJ2_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN NUMBER_TAC);;

let DIVIDES_SUB_1 = prove
 (`!d n. d divides n - 1 <=> n = 0 \/ (n == 1) (mod d)`,
  REWRITE_TAC[DIVIDES_SUB_EQ; ARITH_RULE `n < 1 <=> n = 0`]);;

let DIVIDES_LMUL = prove
 (`!d a x. d divides a ==> d divides (x * a)`,
  NUMBER_TAC);;

let DIVIDES_RMUL = prove
 (`!d a x. d divides a ==> d divides (a * x)`,
  NUMBER_TAC);;

let DIVIDES_ADD_REVR = prove
 (`!d a b. d divides a /\ d divides (a + b) ==> d divides b`,
  NUMBER_TAC);;

let DIVIDES_ADD_REVL = prove
 (`!d a b. d divides b /\ d divides (a + b) ==> d divides a`,
  NUMBER_TAC);;

let DIVIDES_MUL_L = prove
 (`!a b c. a divides b ==> (c * a) divides (c * b)`,
  NUMBER_TAC);;

let DIVIDES_MUL_R = prove
 (`!a b c. a divides b ==> (a * c) divides (b * c)`,
  NUMBER_TAC);;

let DIVIDES_LMUL2 = prove
 (`!d a x. (x * d) divides a ==> d divides a`,
  NUMBER_TAC);;

let DIVIDES_RMUL2 = prove
 (`!d a x. (d * x) divides a ==> d divides a`,
  NUMBER_TAC);;

let DIVIDES_CMUL2 = prove
 (`!a b c. (c * a) divides (c * b) /\ ~(c = 0) ==> a divides b`,
  NUMBER_TAC);;

let DIVIDES_LMUL2_EQ = prove
 (`!a b c. ~(c = 0) ==> ((c * a) divides (c * b) <=> a divides b)`,
  NUMBER_TAC);;

let DIVIDES_RMUL2_EQ = prove
 (`!a b c. ~(c = 0) ==> ((a * c) divides (b * c) <=> a divides b)`,
  NUMBER_TAC);;

let DIVIDES_EQ_ZERO = prove
 (`!p n. n < p ==> (p divides n <=> n = 0)`,
  MESON_TAC[DIVIDES_0; DIVIDES_LE_STRONG; NOT_LE; LT]);;

let DIVIDES_CASES = prove
 (`!m n. n divides m ==> m = 0 \/ m = n \/ 2 * n <= m`,
  SIMP_TAC[ARITH_RULE `m = n \/ 2 * n <= m <=> m = n * 1 \/ n * 2 <= m`] THEN
  SIMP_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[MULT_EQ_0; EQ_MULT_LCANCEL; LE_MULT_LCANCEL] THEN ARITH_TAC);;

let DIVIDES_DIV_NOT = prove
 (`!n x q r. x = q * n + r /\ 0 < r /\ r < n ==> ~(n divides x)`,
  SIMP_TAC[NUMBER_RULE `n divides (q * n + r) <=> n divides r`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_ARITH_TAC);;

let DIVIDES_MUL2 = prove
 (`!a b c d. a divides b /\ c divides d ==> (a * c) divides (b * d)`,
  NUMBER_TAC);;

let DIVIDES_EXP = prove
 (`!x y n. x divides y ==> (x EXP n) divides (y EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  EXISTS_TAC `d EXP n` THEN MATCH_ACCEPT_TAC MULT_EXP);;

let DIVIDES_EXP2 = prove
 (`!n x y. ~(n = 0) /\ (x EXP n) divides y ==> x divides y`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; EXP] THEN NUMBER_TAC);;

let DIVIDES_EXP_LE_IMP = prove
 (`!p m n. m <= n ==> (p EXP m) divides (p EXP n)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; EXP_ADD] THEN NUMBER_TAC);;

let DIVIDES_EXP_LE = prove
 (`!p m n. 2 <= p ==> ((p EXP m) divides (p EXP n) <=> m <= n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC[LE_EXP; EXP_EQ_0] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; EXP_ADD] THEN NUMBER_TAC]);;

let DIVIDES_TRIVIAL_UPPERBOUND = prove
 (`!p n. ~(n = 0) /\ 2 <= p ==> ~((p EXP n) divides n)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP n` THEN REWRITE_TAC[LT_POW2_REFL] THEN
  UNDISCH_TAC `~(n = 0)` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP_MONO_LE; NOT_SUC]);;

let DIVIDES_FACT = prove
 (`!n p. 1 <= p /\ p <= n ==> p divides (FACT n)`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; LE] THENL
   [ARITH_TAC; ASM_MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL]]);;

let DIVIDES_2 = prove
 (`!n. 2 divides n <=> EVEN(n)`,
  REWRITE_TAC[divides; EVEN_EXISTS]);;

let DIVIDES_REXP_SUC = prove
 (`!x y n. x divides y ==> x divides (y EXP (SUC n))`,
  REWRITE_TAC[EXP; DIVIDES_RMUL]);;

let DIVIDES_REXP = prove
 (`!x y n. x divides y /\ ~(n = 0) ==> x divides (y EXP n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[DIVIDES_REXP_SUC]);;

let FINITE_DIVISORS = prove
 (`!n. ~(n = 0) ==> FINITE {d | d divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d:num | d <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[DIVIDES_LE]);;

let FINITE_SPECIAL_DIVISORS = prove
 (`!n. ~(n = 0) ==> FINITE {d | P d /\ d divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d | d divides n}` THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
  SET_TAC[]);;

let DIVISORS_EQ = prove
 (`!m n. m = n <=> !d. d divides m <=> d divides n`,
  REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_TRANS]);;

let MULTIPLES_EQ = prove
 (`!m n. m = n <=> !d. m divides d <=> n divides d`,
  REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_TRANS]);;

let DIVIDES_NSUM = prove
 (`!n f s. FINITE s /\ (!i. i IN s ==> n divides (f i))
           ==> n divides nsum s f`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[DIVIDES_0; NSUM_CLAUSES; FORALL_IN_INSERT; DIVIDES_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Greatest common divisor.                                                  *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_GCD = prove
 (`!a b d. d divides gcd(a,b) <=> d divides a /\ d divides b`,
  NUMBER_TAC);;

let GCD_0 = prove
 (`(!a. gcd(0,a) = a) /\ (!a. gcd(a,0) = a)`,
  NUMBER_TAC);;

let GCD_ZERO = prove
 (`!a b. gcd(a,b) = 0 <=> a = 0 /\ b = 0`,
  NUMBER_TAC);;

let GCD_REFL = prove
 (`!a. gcd(a,a) = a`,
  NUMBER_TAC);;

let GCD_1 = prove
  (`(!a. gcd(1,a) = 1) /\ (!a. gcd(a,1) = 1)`,
  NUMBER_TAC);;

let GCD_MULTIPLE = prove
 (`!a b. gcd(b,a * b) = b`,
  NUMBER_TAC);;

let GCD_ADD = prove
 (`(!a b. gcd(a + b,b) = gcd(a,b)) /\
   (!a b. gcd(b + a,b) = gcd(a,b)) /\
   (!a b. gcd(a,a + b) = gcd(a,b)) /\
   (!a b. gcd(a,b + a) = gcd(a,b))`,
  NUMBER_TAC);;

let GCD_SUB = prove
 (`(!a b. b <= a ==> gcd(a - b,b) = gcd(a,b)) /\
   (!a b. a <= b ==> gcd(a,b - a) = gcd(a,b))`,
  MESON_TAC[SUB_ADD; GCD_ADD]);;

let DIVIDES_GCD_LEFT = prove
 (`!m n:num. m divides n <=> gcd(m,n) = m`,
  NUMBER_TAC);;

let DIVIDES_GCD_RIGHT = prove
 (`!m n:num. n divides m <=> gcd(m,n) = n`,
  NUMBER_TAC);;

let GCD_COPRIME_LMUL = prove
 (`!a b c. coprime(a,b) ==> gcd(a * b,c) = gcd(a,c) * gcd(b,c)`,
  NUMBER_TAC);;

let GCD_COPRIME_RMUL = prove
 (`!a b c. coprime(a,b) ==> gcd(c,a * b) = gcd(c,a) * gcd(c,b)`,
  NUMBER_TAC);;

let DIVIDES_LMUL_GCD = prove
 (`(!d a b. d divides gcd(d,a) * b <=> d divides a * b) /\
   (!d a b. d divides gcd(a,d) * b <=> d divides a * b)`,
  NUMBER_TAC);;

let DIVIDES_RMUL_GCD = prove
 (`(!d a b. d divides a * gcd(d,b) <=> d divides a * b) /\
   (!d a b. d divides a * gcd(b,d) <=> d divides a * b)`,
  NUMBER_TAC);;

let GCD_MUL_COPRIME = prove
 (`(!a b c. coprime(a,b) ==> gcd(a,b * c) = gcd(a,c)) /\
   (!a b c. coprime(a,c) ==> gcd(a,b * c) = gcd(a,b)) /\
   (!a b c. coprime(b,c) ==> gcd(a,b * c) = gcd(a,b) * gcd(a,c)) /\
   (!a b c. coprime(a,c) ==> gcd(a * b,c) = gcd(b,c)) /\
   (!a b c. coprime(b,c) ==> gcd(a * b,c) = gcd(a,c)) /\
   (!a b c. coprime(a,b) ==> gcd(a * b,c) = gcd(a,c) * gcd(b,c))`,
  NUMBER_TAC);;

let GCD_SYM = prove
 (`!a b. gcd(a,b) = gcd(b,a)`,
  NUMBER_TAC);;

let GCD_ASSOC = prove
 (`!a b c. gcd(a,gcd(b,c)) = gcd(gcd(a,b),c)`,
  NUMBER_TAC);;

let GCD_LMUL = prove
 (`!a b c. gcd(c * a, c * b) = c * gcd(a,b)`,
  NUMBER_TAC);;

let GCD_RMUL = prove
 (`!a b c. gcd(a * c, b * c) = c * gcd(a,b)`,
  NUMBER_TAC);;

let GCD_BEZOUT_SUM = prove
 (`!a b d x y. a * x + b * y = d ==> gcd(a,b) divides d`,
  NUMBER_TAC);;

let GCD_COPRIME_DIVIDES_LMUL = prove
 (`!a b c:num. coprime(a,b) /\ a divides c ==> gcd(a * b,c) = a * gcd(b,c)`,
  NUMBER_TAC);;

let GCD_COPRIME_DIVIDES_RMUL = prove
 (`!a b c:num. coprime(b,c) /\ b divides a ==> gcd(a,b * c) = b * gcd(a,c)`,
 ONCE_REWRITE_TAC[GCD_SYM] THEN REWRITE_TAC[GCD_COPRIME_DIVIDES_LMUL]);;

let GCD_UNIQUE = prove
 (`!d a b. (d divides a /\ d divides b) /\
           (!e. e divides a /\ e divides b ==> e divides d) <=>
           d = gcd(a,b)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[GCD] THEN
  ONCE_REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  ASM_REWRITE_TAC[DIVIDES_GCD] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GCD]);;

let GCD_EQ = prove
 (`(!d. d divides x /\ d divides y <=> d divides u /\ d divides v)
   ==> gcd(x,y) = gcd(u,v)`,
  REWRITE_TAC[DIVIDES_GCD; GSYM DIVIDES_ANTISYM] THEN MESON_TAC[GCD]);;

let BEZOUT_GCD_STRONG = prove
 (`!a b. ~(a = 0) ==> ?x y. a * x = b * y + gcd(a,b)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  MP_TAC(INTEGER_RULE `?x y. &a * x:int = &b * y + gcd(&a,&b)`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`y:int`; `&a:int`] INT_CONG_NUM_EXISTS) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&a divides (&b * &r + gcd(&a,&b):int)` MP_TAC THENL
   [REPLICATE_TAC 2 (POP_ASSUM MP_TAC) THEN CONV_TAC INTEGER_RULE;
    ASM_REWRITE_TAC[int_divides; EXISTS_INT_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[GSYM NUM_GCD; INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
    REWRITE_TAC[INT_MUL_RNEG; INT_OF_NUM_MUL;
                INT_ARITH `&x:int = -- &y <=> &x:int = &0 /\ &y:int = &0`] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_EQ; ADD_EQ_0; GCD_ZERO]]);;

let BEZOUT_ADD_STRONG = prove
 (`!a b. ~(a = 0)
         ==> ?d x y. d divides a /\ d divides b /\ a * x = b * y + d`,
  MESON_TAC[BEZOUT_GCD_STRONG; GCD]);;

let BEZOUT_GCD = prove
 (`!a b. ?x y. a * x - b * y = gcd(a,b) \/ b * x - a * y = gcd(a,b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 0 /\ b = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; GCD_0; SUB_0] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM]) THENL
   [MP_TAC(SPECL [`a:num`; `b:num`] BEZOUT_GCD_STRONG);
    MP_TAC(SPECL [`b:num`; `a:num`] BEZOUT_GCD_STRONG)] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  REWRITE_TAC[GCD_SYM] THEN ARITH_TAC);;

let BEZOUT_ADD = prove
 (`!a b. ?d x y. (d divides a /\ d divides b) /\
                 (a * x = b * y + d \/ b * x = a * y + d)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 0 /\ b = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; DIVIDES_0; GSYM EXISTS_REFL] THEN
  ASM_MESON_TAC[BEZOUT_ADD_STRONG; MULT_SYM; ADD_SYM]);;

let BEZOUT = prove
 (`!a b. ?d x y. (d divides a /\ d divides b) /\
                 (a * x - b * y = d \/ b * x - a * y = d)`,
  MESON_TAC[BEZOUT_GCD; GCD]);;

let GCD_BEZOUT = prove
 (`!a b d. (?x y. a * x - b * y = d \/ b * x - a * y = d) <=>
           gcd(a,b) divides d`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[GCD];
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    STRIP_ASSUME_TAC(SPECL [`a:num`; `b:num`] BEZOUT_GCD) THEN
    MAP_EVERY EXISTS_TAC [`x * k`; `y * k`] THEN
    ASM_REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB; MULT_ASSOC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[]]);;

let GCD_LE = prove
 (`(!m n. gcd(m,n) <= m <=> (m = 0 ==> n = 0)) /\
   (!m n. gcd(m,n) <= n <=> (n = 0 ==> m = 0))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[GCD_0; LE_REFL; LE] THEN
  MATCH_MP_TAC DIVIDES_LE_IMP THEN
  ASM_REWRITE_TAC[GCD]);;

let GCD_LE_MIN_EQ = prove
 (`!m n. gcd(m,n) <= MIN m n <=> (m = 0 <=> n = 0)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[GCD_0; CONJUNCT1 LE; ARITH_RULE `MIN m 0 = 0`] THEN
  ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[GCD_0; CONJUNCT1 LE; ARITH_RULE `MIN 0 n = 0`] THEN
  REWRITE_TAC[ARITH_RULE `p <= MIN m n <=> p <= m /\ p <= n`] THEN
  CONJ_TAC THEN MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC[GCD]);;

let GCD_LE_MIN = prove
 (`!m n. (m = 0 <=> n = 0) ==> gcd(m,n) <= MIN m n`,
  REWRITE_TAC[GCD_LE_MIN_EQ]);;

let GCD_LE_MAX = prove
 (`!m n. gcd(m,n) <= MAX m n`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[GCD_0; ARITH_RULE `MAX m 0 = m`; LE_REFL] THEN
  ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[GCD_0; ARITH_RULE `MAX 0 n = n`; LE_REFL] THEN
  MATCH_MP_TAC(ARITH_RULE `p <= MIN m n ==> p <= MAX m n`) THEN
  ASM_REWRITE_TAC[GCD_LE_MIN_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Coprimality                                                               *)
(* ------------------------------------------------------------------------- *)

let COPRIME = prove
 (`!a b. coprime(a,b) <=> !d. d divides a /\ d divides b <=> d = 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coprime] THEN
  REPEAT(EQ_TAC ORELSE STRIP_TAC) THEN ASM_REWRITE_TAC[DIVIDES_1] THENL
   [FIRST_ASSUM MATCH_MP_TAC;
    FIRST_ASSUM(CONV_TAC o REWR_CONV o GSYM) THEN CONJ_TAC] THEN
  ASM_REWRITE_TAC[]);;

let COPRIME_GCD = prove
 (`!a b. coprime(a,b) <=> gcd(a,b) = 1`,
  REWRITE_TAC[GSYM DIVIDES_ONE] THEN NUMBER_TAC);;

let GCD_ONE = prove
 (`!a b. coprime(a,b) ==> gcd(a,b) = 1`,
  NUMBER_TAC);;

let COPRIME_SYM = prove
 (`!a b. coprime(a,b) <=> coprime(b,a)`,
  NUMBER_TAC);;

let COPRIME_BEZOUT = prove
 (`!a b. coprime(a,b) <=> ?x y. a * x - b * y = 1 \/ b * x - a * y = 1`,
  REWRITE_TAC[GCD_BEZOUT; DIVIDES_ONE; COPRIME_GCD]);;

let COPRIME_DIVPROD = prove
 (`!d a b. d divides (a * b) /\ coprime(d,a) ==> d divides b`,
  NUMBER_TAC);;

let COPRIME_1 = prove
 (`(!a. coprime(a,1)) /\ (!a. coprime(1,a))`,
  NUMBER_TAC);;

let GCD_COPRIME = prove
 (`!a b a' b'. ~(gcd(a,b) = 0) /\ a = a' * gcd(a,b) /\ b = b' * gcd(a,b)
               ==> coprime(a',b')`,
  NUMBER_TAC);;

let GCD_COPRIME_EXISTS = prove
 (`!a b. ?a' b'. a = a' * gcd(a,b) /\ b = b' * gcd(a,b) /\ coprime(a',b')`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `gcd(a,b) = 0` THENL
   [FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GCD_ZERO]) THEN
    MAP_EVERY EXISTS_TAC [`0`; `1`] THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    CONV_TAC NUMBER_RULE;
    MP_TAC(CONJUNCT1(SPECL [`a:num`; `b:num`] GCD)) THEN
    REWRITE_TAC[divides; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    ASM_MESON_TAC[GCD_COPRIME; MULT_SYM]]);;

let COPRIME_DIVPROD_IFF = prove
 (`!d a. ~(d = 0)
         ==> ((!b. d divides a * b ==> d divides b) <=> coprime(d,a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; CONV_TAC NUMBER_RULE] THEN
  MP_TAC(GSYM(ISPECL [`d:num`; `a:num`] GCD_COPRIME_EXISTS)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a':num`; `b':num`] THEN STRIP_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `a':num`) THEN ANTS_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN NUMBER_TAC);;

let CONG_MULT_LCANCEL_IFF = prove
 (`!a n. ~(n = 0)
         ==> ((!x y. (a * x == a * y) (mod n) ==> (x == y) (mod n)) <=>
              coprime(a,n))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; CONV_TAC NUMBER_RULE] THEN
  DISCH_THEN(MP_TAC o SPEC `0`) THEN
  ASM_SIMP_TAC[MULT_CLAUSES; NUMBER_RULE `(0 == x) (mod n) <=> n divides x`;
               COPRIME_DIVPROD_IFF] THEN
  CONV_TAC NUMBER_RULE);;

let CONG_MULT_RCANCEL_IFF = prove
 (`!a n. ~(n = 0)
         ==> ((!x y. (x * a == y * a) (mod n) ==> (x == y) (mod n)) <=>
              coprime(a,n))`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[CONG_MULT_LCANCEL_IFF]);;

let COPRIME_0 = prove
 (`(!d. coprime(d,0) <=> d = 1) /\
   (!d. coprime(0,d) <=> d = 1)`,
  NUMBER_TAC);;

let COPRIME_MUL = prove
 (`!d a b. coprime(d,a) /\ coprime(d,b) ==> coprime(d,a * b)`,
  NUMBER_TAC);;

let COPRIME_LMUL2 = prove
 (`!d a b. coprime(d,a * b) ==> coprime(d,b)`,
  NUMBER_TAC);;

let COPRIME_RMUL2 = prove
 (`!d a b.  coprime(d,a * b) ==> coprime(d,a)`,
  NUMBER_TAC);;

let COPRIME_LMUL = prove
 (`!d a b. coprime(a * b,d) <=> coprime(a,d) /\ coprime(b,d)`,
  NUMBER_TAC);;

let COPRIME_RMUL = prove
 (`!d a b. coprime(d,a * b) <=> coprime(d,a) /\ coprime(d,b)`,
  NUMBER_TAC);;

let COPRIME_EXP = prove
 (`!n a d. coprime(d,a) ==> coprime(d,a EXP n)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; COPRIME_1] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC COPRIME_MUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let COPRIME_EXP_IMP = prove
 (`!n a b. coprime(a,b) ==> coprime(a EXP n,b EXP n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC COPRIME_EXP THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  MATCH_MP_TAC COPRIME_EXP THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[]);;

let COPRIME_REXP = prove
 (`!m n k. coprime(m,n EXP k) <=> coprime(m,n) \/ k = 0`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[CONJUNCT1 EXP; COPRIME_1] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[COPRIME_EXP; NOT_SUC] THEN
  REWRITE_TAC[EXP] THEN CONV_TAC NUMBER_RULE);;

let COPRIME_LEXP = prove
 (`!m n k. coprime(m EXP k,n) <=> coprime(m,n) \/ k = 0`,
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN REWRITE_TAC[COPRIME_REXP]);;

let COPRIME_EXP2 = prove
 (`!m n k. coprime(m EXP k,n EXP k) <=> coprime(m,n) \/ k = 0`,
  REWRITE_TAC[COPRIME_REXP; COPRIME_LEXP; DISJ_ACI]);;

let COPRIME_EXP2_SUC = prove
 (`!n a b. coprime(a EXP (SUC n),b EXP (SUC n)) <=> coprime(a,b)`,
  REWRITE_TAC[COPRIME_EXP2; NOT_SUC]);;

let COPRIME_NPRODUCT_EQ = prove
 (`(!(f:A->num) a s.
        FINITE s
        ==> (coprime(a,nproduct s f) <=> !i. i IN s ==> coprime(a,f i))) /\
   (!(f:A->num) b s.
        FINITE s
        ==> (coprime(nproduct s f,b) <=> !i. i IN s ==> coprime(f i,b)))`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [COPRIME_SYM] THEN
  REWRITE_TAC[] THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; NOT_IN_EMPTY; COPRIME_1] THEN
  SIMP_TAC[COPRIME_RMUL; FORALL_IN_INSERT]);;

let COPRIME_NPRODUCT = prove
 (`!s n. FINITE s /\ (!x. x IN s ==> coprime(n,a x))
         ==> coprime(n,nproduct s a)`,
  SIMP_TAC[COPRIME_NPRODUCT_EQ]);;

let COPRIME_DIVISORS = prove
 (`!a b d e. d divides a /\ e divides b /\ coprime(a,b) ==> coprime(d,e)`,
  NUMBER_TAC);;

let COPRIME_REFL = prove
 (`!n. coprime(n,n) <=> n = 1`,
  NUMBER_TAC);;

let COPRIME_PLUS1 = prove
 (`!n. coprime(n + 1,n)`,
  NUMBER_TAC);;

let COPRIME_MINUS1 = prove
 (`!n. ~(n = 0) ==> coprime(n - 1,n)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[coprime] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_SUB) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - (n - 1) = 1`; DIVIDES_ONE]);;

let GCD_EXP = prove
 (`!n a b. gcd(a EXP n,b EXP n) = gcd(a,b) EXP n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `b:num`] GCD_COPRIME_EXISTS) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a':num`; `b':num`] THEN
  STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_EXP; GCD_RMUL] THEN
  MATCH_MP_TAC(NUM_RING `x = 1 /\ y = 1 ==> a * x = a * y`) THEN
  ASM_REWRITE_TAC[GSYM COPRIME_GCD; EXP_EQ_1] THEN
  ASM_REWRITE_TAC[COPRIME_LEXP; COPRIME_REXP]);;

let DIVIDES_EXP2_REV = prove
 (`!n a b. (a EXP n) divides (b EXP n) /\ ~(n = 0) ==> a divides b`,
  REWRITE_TAC[DIVIDES_GCD_LEFT; GCD_EXP; EXP_MONO_EQ] THEN MESON_TAC[]);;

let DIVIDES_EXP2_EQ = prove
 (`!n a b. ~(n = 0) ==> ((a EXP n) divides (b EXP n) <=> a divides b)`,
  MESON_TAC[DIVIDES_EXP2_REV; DIVIDES_EXP]);;

let DIVIDES_MUL = prove
 (`!m n r. m divides r /\ n divides r /\ coprime(m,n) ==> (m * n) divides r`,
  NUMBER_TAC);;

let DIVISION_DECOMP = prove
 (`!a b c.
        a divides (b * c)
        ==> ?b' c'. a = b' * c' /\ b' divides b /\ c' divides c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `gcd(a,b)` THEN
  REWRITE_TAC[GCD] THEN ASM_CASES_TAC `gcd(a,b) = 0` THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `1` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GCD_ZERO]) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; DIVIDES_1];
    MP_TAC(SPECL [`a:num`; `b:num`] GCD_COPRIME_EXISTS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUMBER_RULE]);;

(* ------------------------------------------------------------------------- *)
(* Primes.                                                                   *)
(* ------------------------------------------------------------------------- *)

let PRIME_0 = prove
 (`~prime(0)`,
  REWRITE_TAC[prime] THEN
  DISCH_THEN(MP_TAC o SPEC `2` o CONJUNCT2) THEN
  REWRITE_TAC[DIVIDES_0; ARITH]);;

let PRIME_1 = prove
 (`~prime(1)`,
  REWRITE_TAC[prime]);;

let PRIME_ALT = prove
 (`!p. prime p <=>
       ~(p = 0) /\ ~(p = 1) /\ !n. 1 < n /\ n < p ==> ~(n divides p)`,
  GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN
  REWRITE_TAC[prime; LT_LE] THEN
  ASM_MESON_TAC[DIVIDES_LE_STRONG; DIVIDES_0; LE_1]);;

let PRIME_2 = prove
 (`prime(2)`,
  REWRITE_TAC[PRIME_ALT] THEN ARITH_TAC);;

let PRIME_COPRIME_STRONG = prove
 (`!n p. prime(p) ==> p divides n \/ coprime(p,n)`,
  REWRITE_TAC[prime; coprime] THEN MESON_TAC[]);;

let PRIME_COPRIME = prove
 (`!n p. prime(p) ==> n = 1 \/ p divides n \/ coprime(p,n)`,
  MESON_TAC[PRIME_COPRIME_STRONG]);;

let PRIME_COPRIME_EQ = prove
 (`!p n. prime p ==> (coprime(p,n) <=> ~(p divides n))`,
  SIMP_TAC[PRIME_COPRIME_EQ_NONDIVISIBLE]);;

let COPRIME_PRIME = prove
 (`!p a b. coprime(a,b) ==> ~(prime(p) /\ p divides a /\ p divides b)`,
  MESON_TAC[coprime; PRIME_1]);;

let PRIME_DIVPROD = prove
 (`!p a b. prime(p) /\ p divides (a * b) ==> p divides a \/ p divides b`,
  MESON_TAC[PRIME_COPRIME_STRONG; COPRIME_DIVPROD]);;

let PRIME_DIVPROD_EQ = prove
 (`!p a b. prime(p) ==> (p divides (a * b) <=> p divides a \/ p divides b)`,
  MESON_TAC[PRIME_DIVPROD; DIVIDES_LMUL; DIVIDES_RMUL]);;

let PRIME_INT_DIVPROD_EQ = prove
 (`!p a b:int.
        prime p ==> (&p divides a * b <=> &p divides a \/ &p divides b)`,
  REWRITE_TAC[FORALL_INT_CASES; INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG] THEN
  REWRITE_TAC[INTEGER_RULE `(a:int) divides --b <=> a divides b`] THEN
  REWRITE_TAC[GSYM num_divides; PRIME_DIVPROD_EQ; INT_OF_NUM_CLAUSES]);;

let PRIME_GE_2 = prove
 (`!p. prime(p) ==> 2 <= p`,
  REWRITE_TAC[ARITH_RULE `2 <= p <=> ~(p = 0) /\ ~(p = 1)`] THEN
  MESON_TAC[PRIME_0; PRIME_1]);;

let PRIME_FACTOR = prove
 (`!n. ~(n = 1) ==> ?p. prime(p) /\ p divides n`,
  MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `prime(n)` THENL [ASM_MESON_TAC[DIVIDES_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [PRIME_ALT]) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  STRIP_TAC THENL [ASM_MESON_TAC[PRIME_2; DIVIDES_0]; ALL_TAC] THEN
  ASM_MESON_TAC[DIVIDES_TRANS; LT_REFL]);;

let PRIME = prove
 (`!p. prime p <=>
       ~(p = 0) /\ ~(p = 1) /\ !m. 0 < m /\ m < p ==> coprime(p,m)`,
  GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PRIME_1] THEN
  MP_TAC(SPEC `p:num` ONE_OR_PRIME_DIVIDES_OR_COPRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `n:num` THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n MOD p`) THEN
    ASM_REWRITE_TAC[MOD_LT_EQ; COPRIME_RMOD; DIVIDES_MOD] THEN
    MESON_TAC[LE_1]]);;

let PRIME_PRIME_FACTOR = prove
 (`!n. prime n <=> ~(n = 1) /\ !p. prime p /\ p divides n ==> p = n`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [prime] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [MESON_TAC[PRIME_1]; ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `d:num` THEN
  ASM_CASES_TAC `d = 1` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
    MATCH_MP PRIME_FACTOR) THEN
  ASM_MESON_TAC[DIVIDES_TRANS; DIVIDES_ANTISYM]);;

let PRIME_FACTOR_LT = prove
 (`!n m p. prime(p) /\ ~(n = 0) /\ n = p * m ==> m < n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  ASM_SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `m < p * m <=> 1 * m < p * m`] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC);;

let COPRIME_PRIME_EQ = prove
 (`!a b. coprime(a,b) <=> !p. ~(prime(p) /\ p divides a /\ p divides b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP COPRIME_PRIME th]);
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[coprime] THEN
    ONCE_REWRITE_TAC[NOT_FORALL_THM] THEN REWRITE_TAC[NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `p:num` o MATCH_MP PRIME_FACTOR) THEN
    EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[]]);;

let GCD_PRIME_CASES = prove
 (`(!p n. prime p ==> gcd(p,n) = if p divides n then p else 1) /\
   (!p n. prime p ==> gcd(n,p) = if p divides n then p else 1)`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCD_SYM] THEN
  REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM DIVIDES_GCD_LEFT] THEN
  REWRITE_TAC[GSYM COPRIME_GCD] THEN
  ASM_MESON_TAC[PRIME_COPRIME_EQ]);;

let GCD_2_CASES = prove
 (`(!n. gcd(2,n) = if EVEN n then 2 else 1) /\
   (!n. gcd(n,2) = if EVEN n then 2 else 1)`,
  SIMP_TAC[GCD_PRIME_CASES; PRIME_2; DIVIDES_2]);;

let COPRIME_PRIMEPOW = prove
 (`!p k m. prime p /\ ~(k = 0) ==> (coprime(m,p EXP k) <=> ~(p divides m))`,
  SIMP_TAC[COPRIME_REXP] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  SIMP_TAC[PRIME_COPRIME_EQ]);;

let COPRIME_BEZOUT_STRONG = prove
 (`!a b. coprime(a,b) /\ ~(b = 1) ==> ?x y. a * x = b * y + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COPRIME_GCD]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC BEZOUT_GCD_STRONG THEN
  ASM_MESON_TAC[COPRIME_0; COPRIME_SYM]);;

let COPRIME_BEZOUT_ALT = prove
 (`!a b. coprime(a,b) /\ ~(a = 0) ==> ?x y. a * x = b * y + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COPRIME_GCD]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC BEZOUT_GCD_STRONG THEN
  ASM_MESON_TAC[COPRIME_0; COPRIME_SYM]);;

let BEZOUT_PRIME = prove
 (`!a p. prime p /\ ~(p divides a) ==> ?x y. a * x = p * y + 1`,
  MESON_TAC[PRIME_COPRIME_STRONG; COPRIME_SYM;
     COPRIME_BEZOUT_STRONG; PRIME_1]);;

let PRIME_DIVEXP = prove
 (`!n p x. prime(p) /\ p divides (x EXP n) ==> p divides x`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[EXP; DIVIDES_ONE] THENL
   [DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[DIVIDES_1];
    DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP PRIME_DIVPROD) THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let PRIME_DIVEXP_N = prove
 (`!n p x. prime(p) /\ p divides (x EXP n) ==> (p EXP n) divides (x EXP n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PRIME_DIVEXP) THEN
  MATCH_ACCEPT_TAC DIVIDES_EXP);;

let PRIME_DIVEXP_EQ = prove
 (`!n p x. prime p ==> (p divides x EXP n <=> p divides x /\ ~(n = 0))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[EXP; DIVIDES_ONE] THEN
  ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_REXP; PRIME_1]);;

let COPRIME_SOS = prove
 (`!x y. coprime(x,y) ==> coprime(x * y,(x EXP 2) + (y EXP 2))`,
  NUMBER_TAC);;

let PRIME_IMP_NZ = prove
 (`!p. prime(p) ==> ~(p = 0)`,
  MESON_TAC[PRIME_0]);;

let DISTINCT_PRIME_COPRIME = prove
 (`!p q. prime p /\ prime q /\ ~(p = q) ==> coprime(p,q)`,
  MESON_TAC[prime; coprime; PRIME_1]);;

let PRIME_COPRIME_LT = prove
 (`!x p. prime p /\ 0 < x /\ x < p ==> coprime(x,p)`,
  REWRITE_TAC[coprime; prime] THEN
  MESON_TAC[LT_REFL; DIVIDES_LE; NOT_LT; PRIME_0]);;

let DIVIDES_PRIME_PRIME = prove
 (`!p q. prime p /\ prime q  ==> (p divides q <=> p = q)`,
  MESON_TAC[DIVIDES_REFL; DISTINCT_PRIME_COPRIME; PRIME_COPRIME_EQ]);;

let COPRIME_PRIME_PRIME = prove
 (`!p q. prime p /\ prime q ==> (coprime(p,q) <=> ~(p = q))`,
  MESON_TAC[PRIME_COPRIME_EQ; DIVIDES_PRIME_PRIME; COPRIME_SYM]);;

let DIVIDES_PRIME_EXP_LE = prove
 (`!p q m n. prime p /\ prime q
             ==> ((p EXP m) divides (q EXP n) <=> m = 0 \/ p = q /\ m <= n)`,
  GEN_TAC THEN GEN_TAC THEN REPEAT INDUCT_TAC THEN
  ASM_SIMP_TAC[EXP; DIVIDES_1; DIVIDES_ONE; MULT_EQ_1; NOT_SUC] THENL
   [MESON_TAC[PRIME_1; ARITH_RULE `~(SUC m <= 0)`]; ALL_TAC] THEN
  ASM_CASES_TAC `p:num = q` THEN
  ASM_SIMP_TAC[DIVIDES_EXP_LE; PRIME_GE_2; GSYM(CONJUNCT2 EXP)] THEN
  ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_PRIME_PRIME; EXP; DIVIDES_RMUL2]);;

let EQ_PRIME_EXP = prove
 (`!p q m n. prime p /\ prime q
             ==> (p EXP m = q EXP n <=> m = 0 /\ n = 0 \/ p = q /\ m = n)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM DIVIDES_ANTISYM] THEN
  ASM_SIMP_TAC[DIVIDES_PRIME_EXP_LE] THEN ARITH_TAC);;

let PRIME_ODD = prove
 (`!p. prime p ==> p = 2 \/ ODD p`,
  GEN_TAC THEN REWRITE_TAC[prime; GSYM NOT_EVEN; EVEN_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `2`)) THEN
  REWRITE_TAC[divides; ARITH] THEN MESON_TAC[]);;

let ODD_PRIME = prove
 (`!p. prime p ==> (ODD p <=> 3 <= p)`,
  GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PRIME_ODD) THEN
  ASM_CASES_TAC `p = 2` THEN ASM_SIMP_TAC[ARITH] THEN ASM_ARITH_TAC);;

let DIVIDES_FACT_PRIME = prove
 (`!p. prime p ==> !n. p divides (FACT n) <=> p <= n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[FACT; LE] THENL
   [ASM_MESON_TAC[DIVIDES_ONE; PRIME_0; PRIME_1];
    ASM_MESON_TAC[PRIME_DIVPROD_EQ; DIVIDES_LE; NOT_SUC; DIVIDES_REFL;
                  ARITH_RULE `~(p <= n) /\ p <= SUC n ==> p = SUC n`]]);;

let EQ_PRIMEPOW = prove
 (`!p m n. prime p ==> (p EXP m = p EXP n <=> m = n)`,
  ONCE_REWRITE_TAC[GSYM LE_ANTISYM] THEN
  SIMP_TAC[LE_EXP; PRIME_IMP_NZ] THEN MESON_TAC[PRIME_1]);;

let COPRIME_2 = prove
 (`(!n. coprime(2,n) <=> ODD n) /\ (!n. coprime(n,2) <=> ODD n)`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [COPRIME_SYM] THEN
  SIMP_TAC[PRIME_COPRIME_EQ; PRIME_2; DIVIDES_2; NOT_EVEN]);;

let DIVIDES_EXP_PLUS1 = prove
 (`!n k. ODD k ==> (n + 1) divides (n EXP k + 1)`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  INDUCT_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EXP_1; DIVIDES_REFL] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * SUC n) = SUC(2 * n) + 2`] THEN
  REWRITE_TAC[EXP_ADD; EXP_2] THEN POP_ASSUM MP_TAC THEN NUMBER_TAC);;

let DIVIDES_EXP_MINUS1 = prove
 (`!k n. (n - 1) divides (n EXP k - 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
    ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIVIDES_REFL];
    REWRITE_TAC[num_divides] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1; EXP_EQ_0; ARITH] THEN
    POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN
    SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THEN REWRITE_TAC[INT_POW] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN INTEGER_TAC]);;

let PRIME_IRREDUCIBLE = prove
 (`!p. prime p <=>
       p > 1 /\ !a b. p divides (a * b) ==> p divides a \/ p divides b`,
  GEN_TAC THEN REWRITE_TAC[GSYM ZERO_ONE_OR_PRIME] THEN
  REWRITE_TAC[ARITH_RULE `p > 1 <=> ~(p = 0) /\ ~(p = 1)`] THEN
  MESON_TAC[PRIME_0; PRIME_1]);;

let COPRIME_EXP_DIVPROD = prove
 (`!d n a b.
      (d EXP n) divides (a * b) /\ coprime(d,a) ==> (d EXP n) divides b`,
  MESON_TAC[COPRIME_DIVPROD; COPRIME_EXP; COPRIME_SYM]);;

let PRIME_COPRIME_CASES = prove
 (`!p a b. prime p /\ coprime(a,b) ==> coprime(p,a) \/ coprime(p,b)`,
  MESON_TAC[COPRIME_PRIME; PRIME_COPRIME_EQ]);;

let PRIME_DIVPROD_POW_GEN = prove
 (`!n p a b.
        prime p /\ ~(p divides gcd(a,b)) /\ p EXP n divides a * b
        ==> p EXP n divides a \/ p EXP n divides b`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[DISJ_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [DIVIDES_GCD]) THEN
  ASM_SIMP_TAC[DE_MORGAN_THM; GSYM PRIME_COPRIME_EQ] THEN
  ASM_MESON_TAC[COPRIME_LEXP; COPRIME_DIVPROD; MULT_SYM]);;

let PRIME_DIVPROD_POW_GEN_EQ = prove
 (`!n p a b.
        prime p /\ ~(p divides gcd(a,b))
        ==> (p EXP n divides a * b <=>
             p EXP n divides a \/ p EXP n divides b)`,
  MESON_TAC[PRIME_DIVPROD_POW_GEN; DIVIDES_RMUL; DIVIDES_LMUL]);;

let PRIME_DIVPROD_POW = prove
 (`!n p a b. prime(p) /\ coprime(a,b) /\ (p EXP n) divides (a * b)
             ==> (p EXP n) divides a \/ (p EXP n) divides b`,
  MESON_TAC[COPRIME_EXP_DIVPROD; PRIME_COPRIME_CASES; MULT_SYM]);;

let PRIME_DIVPROD_POW_EQ = prove
 (`!n p a b.
        prime p /\ coprime(a,b)
        ==> (p EXP n divides a * b <=>
             p EXP n divides a \/ p EXP n divides b)`,
  MESON_TAC[PRIME_DIVPROD_POW; DIVIDES_RMUL; DIVIDES_LMUL]);;

let PRIME_FACTOR_INDUCT = prove
 (`!P. P 0 /\ P 1 /\
       (!p n. prime p /\ ~(n = 0) /\ P n ==> P(p * n))
       ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN MAP_EVERY ASM_CASES_TAC [`n = 0`; `n = 1`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM(X_CHOOSE_THEN `p:num`
    STRIP_ASSUME_TAC o MATCH_MP PRIME_FACTOR) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [divides]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `d:num`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[PRIME_FACTOR_LT; MULT_EQ_0]);;

let COMPLETE_FACTOR_INDUCT = prove
 (`!P. P 0 /\ P 1 /\
       (!p. prime p ==> P p) /\
       (!m n. P m /\ P n ==> P(m * n))
       ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
  ASM_SIMP_TAC[]);;

let PRIME_FACTOR_PARTITION = prove
 (`!Q n. ~(n = 0)
         ==> ?n1 n2. n1 * n2 = n /\
                     (!p. prime p /\ p divides n1 ==> Q p) /\
                     (!p. prime p /\ p divides n2 ==> ~Q p)`,
  GEN_TAC THEN MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
  REWRITE_TAC[MULT_EQ_1; GSYM CONJ_ASSOC; UNWIND_THM2; RIGHT_EXISTS_AND_THM;
              DIVIDES_ONE] THEN
  CONJ_TAC THENL [MESON_TAC[PRIME_1]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `n:num`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n1:num`; `n2:num`] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(Q:num->bool) p` THENL
   [MAP_EVERY EXISTS_TAC [`p * n1:num`; `n2:num`];
    MAP_EVERY EXISTS_TAC [`n1:num`; `p * n2:num`]] THEN
  ASM_SIMP_TAC[IMP_CONJ; PRIME_DIVPROD_EQ] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[MULT_AC] THEN
  ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN ASM_MESON_TAC[]);;

let COPRIME_PAIR_DECOMP = prove
 (`!n1 n2 m.
        coprime(n1,n2) /\ ~(m = 0)
        ==> ?m1 m2. coprime(m1,n1) /\ coprime(m2,n2) /\
                    coprime(m1,m2) /\ m1 * m2 = m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\p:num. p divides n2`; `m:num`] PRIME_FACTOR_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m1:num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m2:num` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[COPRIME_PRIME_EQ] THEN
  MESON_TAC[]);;

let EXP_MULT_EXISTS = prove
 (`!m n p k. ~(m = 0) /\ m EXP k * n = p EXP k ==> ?q. n = q EXP k`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `m:num`; `p:num`] DIVIDES_EXP2_REV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[divides; MULT_SYM]; ALL_TAC] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN
  ASM_REWRITE_TAC[MULT_EXP; GSYM MULT_ASSOC; EQ_MULT_LCANCEL; EXP_EQ_0] THEN
  MESON_TAC[]);;

let COPRIME_POW = prove
 (`!n a b c. coprime(a,b) /\ a * b = c EXP n
             ==> ?r s. a = r EXP n /\ b = s EXP n`,
  GEN_TAC THEN GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[EXP; MULT_EQ_1] THEN MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[EXP_ZERO; MULT_EQ_0] THEN
    ASM_MESON_TAC[COPRIME_0; EXP_ZERO; COPRIME_0; EXP_ONE];
    SIMP_TAC[EXP_ONE; MULT_EQ_1] THEN MESON_TAC[EXP_ONE];
    REWRITE_TAC[MULT_EXP] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `p EXP n divides a \/ p EXP n divides b` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVPROD_POW; divides]; ALL_TAC] THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COPRIME_SYM]) THEN
    ASM_SIMP_TAC[COPRIME_RMUL; COPRIME_LMUL; COPRIME_LEXP; COPRIME_REXP] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `d:num`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`d:num`; `a:num`])] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [MATCH_MP_TAC(NUM_RING `!p. ~(p = 0) /\ a * p = b * p ==> a = b`) THEN
       EXISTS_TAC `p EXP n` THEN ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN
       FIRST_X_ASSUM(MP_TAC o SYM) THEN CONV_TAC NUM_RING;
       STRIP_TAC THEN ASM_REWRITE_TAC[GSYM MULT_EXP] THEN MESON_TAC[]])]);;

let PRIME_EXP = prove
 (`!p n. prime(p EXP n) <=> prime(p) /\ (n = 1)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EXP; PRIME_1; ARITH_EQ] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN SPEC_TAC(`n:num`,`n:num`) THEN
  ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[PRIME_0; EXP; MULT_CLAUSES]; ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[ARITH; EXP_1; EXP; MULT_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC(SUC n) = 1)`] THEN
  REWRITE_TAC[prime; DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC[MULT_EQ_1; EXP_EQ_1] THEN ASM_CASES_TAC `p = 1` THEN
  ASM_REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL [MESON_TAC[EXP; divides]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `p < pn:num ==> ~(p = pn)`) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  ASM_REWRITE_TAC[LT_EXP; ARITH_EQ] THEN
  MAP_EVERY UNDISCH_TAC [`~(p = 0)`; `~(p = 1)`] THEN ARITH_TAC);;

let PRIME_POWER_MULT = prove
 (`!k x y p. prime p /\ (x * y = p EXP k)
           ==> ?i j. (x = p EXP i) /\ (y = p EXP j)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; MULT_EQ_1] THENL
   [MESON_TAC[EXP]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides x \/ p divides y` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD; divides; MULT_AC]; ALL_TAC] THEN
  REWRITE_TAC[divides] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `(p * d) * y = p * p EXP k`;
    UNDISCH_TAC `x * p * d = p * p EXP k` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM]] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  ASM_REWRITE_TAC[EQ_MULT_LCANCEL] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`d:num`; `y:num`; `p:num`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`d:num`; `x:num`; `p:num`])] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[EXP]);;

let PRIME_POWER_EXP = prove
 (`!n x p k. prime p /\ ~(n = 0) /\ (x EXP n = p EXP k) ==> ?i. x = p EXP i`,
  INDUCT_TAC THEN REWRITE_TAC[EXP] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[EXP] THEN
  ASM_MESON_TAC[PRIME_POWER_MULT]);;

let DIVIDES_PRIMEPOW = prove
 (`!p. prime p ==> !d. d divides (p EXP k) <=> ?i. i <= k /\ d = p EXP i`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `e:num` THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`k:num`; `d:num`; `e:num`; `p:num`] PRIME_POWER_MULT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LE_ANTISYM; LE_EXP] THEN REWRITE_TAC[LE_ANTISYM] THEN
    POP_ASSUM MP_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_SIMP_TAC[PRIME_0] THEN
    ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PRIME_1; LE_ANTISYM] THEN
    MESON_TAC[LE_ADD];
    REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[EXP_ADD] THEN MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]]);;

let PRIMEPOW_DIVIDES_PROD = prove
 (`!p k m n.
        prime p /\ (p EXP k) divides (m * n)
        ==> ?i j. (p EXP i) divides m /\ (p EXP j) divides n /\ k = i + j`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_DECOMP) THEN
  REWRITE_TAC[NUMBER_RULE
   `a = b * c <=> b divides a /\ c divides a /\ b * c = a`] THEN
  ASM_MESON_TAC[EXP_ADD; EQ_PRIMEPOW; DIVIDES_PRIMEPOW]);;

let EUCLID_BOUND = prove
 (`!n. ?p. prime(p) /\ n < p /\ p <= SUC(FACT n)`,
  GEN_TAC THEN MP_TAC(SPEC `FACT n + 1` PRIME_FACTOR) THEN
  SIMP_TAC[ARITH_RULE `0 < n ==> ~(n + 1 = 1)`; ADD1; FACT_LT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[DIVIDES_ADD_REVR; DIVIDES_ONE; PRIME_1; NOT_LT; PRIME_0;
                  ARITH_RULE `(p = 0) \/ 1 <= p`; DIVIDES_FACT];
    ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE `~(x + 1 = 0)`]]);;

let EUCLID = prove
 (`!n. ?p. prime(p) /\ p > n`,
  REWRITE_TAC[GT] THEN MESON_TAC[EUCLID_BOUND]);;

let PRIMES_INFINITE = prove
 (`INFINITE {p | prime p}`,
  REWRITE_TAC[INFINITE; num_FINITE; IN_ELIM_THM] THEN
  MESON_TAC[EUCLID; NOT_LE; GT]);;

let FACTORIZATION_INDEX = prove
 (`!n p. ~(n = 0) /\ 2 <= p
         ==> ?k. (p EXP k) divides n /\
                 !l. k < l ==> ~((p EXP l) divides n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE; CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM num_MAX] THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[EXP; DIVIDES_1];
    EXISTS_TAC `n:num` THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP l` THEN
    SIMP_TAC[LT_POW2_REFL; LT_IMP_LE] THEN
    SPEC_TAC(`l:num`,`l:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[ARITH; CONJUNCT1 EXP; EXP_MONO_LE; NOT_SUC]]);;

let PRIMEPOW_FACTOR = prove
 (`!n. 2 <= n
       ==> ?p k m. prime p /\ 1 <= k /\ coprime(p,m) /\ n = p EXP k * m`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `n:num` PRIME_FACTOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `p:num`] FACTORIZATION_INDEX) THEN
  ASM_SIMP_TAC[PRIME_GE_2; ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[divides; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `k + 1`)) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k < k + 1`; EXP_ADD; GSYM MULT_ASSOC] THEN
  ASM_SIMP_TAC[EQ_MULT_LCANCEL; EXP_EQ_0; PRIME_IMP_NZ] THEN
  REWRITE_TAC[EXP_1; GSYM divides] THEN UNDISCH_TAC `(p:num) divides n` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_SIMP_TAC[EXP; MULT_CLAUSES; LE_1] THEN
  ASM_MESON_TAC[PRIME_COPRIME_STRONG]);;

let PRIMEPOW_DIVISORS_DIVIDES = prove
 (`!m n. m divides n <=>
         !p k. prime p /\ p EXP k divides m ==> p EXP k divides n`,
  REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
   [MESON_TAC[DIVIDES_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(LABEL_TAC "*") THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THENL
   [MP_TAC(SPEC `n:num` EUCLID) THEN REWRITE_TAC[GT] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPECL [`p:num`; `1`]) THEN ASM_REWRITE_TAC[EXP_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC[GSYM NOT_LT; DIVIDES_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[DIVIDES_1] THEN
  MP_TAC(SPEC `m:num` PRIMEPOW_FACTOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `k:num`; `r:num`] THEN STRIP_TAC THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL[`p:num`; `k:num`] th) THEN
    ASM_REWRITE_TAC[NUMBER_RULE `a divides (a * b)`] THEN
    ASSUME_TAC th) THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM divides] THEN
  MATCH_MP_TAC DIVIDES_MUL_L THEN REMOVE_THEN "*" (MP_TAC o SPEC `r:num`) THEN
  ASM_CASES_TAC `r = 0` THENL [ASM_MESON_TAC[MULT_CLAUSES]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `q < p * q <=> 1 * q < p * q`] THEN
  ASM_SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 < p <=> ~(p = 0 \/ p = 1)`] THEN
  REWRITE_TAC[EXP_EQ_0; EXP_EQ_1] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PRIME_0; PRIME_1; LE_1]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY X_GEN_TAC [`q:num`; `l:num`] THEN
  ASM_CASES_TAC `l = 0` THEN ASM_REWRITE_TAC[EXP; DIVIDES_1] THEN
  STRIP_TAC THEN ASM_CASES_TAC `q:num = p` THENL
   [UNDISCH_TAC `coprime(p,r)` THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[coprime] THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    ASM_SIMP_TAC[DIVIDES_REFL; PRIME_GE_2; ARITH_RULE
     `2 <= p ==> ~(p = 1)`] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    TRANS_TAC DIVIDES_TRANS `p EXP l` THEN
    ASM_MESON_TAC[DIVIDES_REXP; DIVIDES_REFL];
    FIRST_X_ASSUM(MP_TAC o SPECL [`q:num`; `l:num`]) THEN
    ASM_SIMP_TAC[DIVIDES_LMUL] THEN DISCH_THEN(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] COPRIME_EXP_DIVPROD)) THEN
    MATCH_MP_TAC COPRIME_EXP THEN ASM_MESON_TAC[DISTINCT_PRIME_COPRIME]]);;

let PRIMEPOW_DIVISORS_EQ = prove
 (`!m n. m = n <=>
         !p k. prime p ==> (p EXP k divides m <=> p EXP k divides n)`,
  MESON_TAC[DIVIDES_ANTISYM; PRIMEPOW_DIVISORS_DIVIDES]);;

(* ------------------------------------------------------------------------- *)
(* A binary form of the Chinese Remainder Theorem.                           *)
(* ------------------------------------------------------------------------- *)

let CHINESE_REMAINDER = prove
 (`!a b u v. coprime(a,b) /\ ~(a = 0) /\ ~(b = 0)
             ==> ?x q1 q2. x = u + q1 * a /\ x = v + q2 * b`,
  let lemma = prove
   (`(?d x y. (d = 1) /\ P x y d) <=> (?x y. P x y 1)`,
    MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:num`; `a:num`] BEZOUT_ADD_STRONG) THEN
  MP_TAC(SPECL [`a:num`; `b:num`] BEZOUT_ADD_STRONG) THEN
  ASM_REWRITE_TAC[CONJ_ASSOC] THEN
  SUBGOAL_THEN `!d. d divides a /\ d divides b <=> (d = 1)`
   (fun th -> REWRITE_TAC[th; ONCE_REWRITE_RULE[CONJ_SYM] th])
  THENL
   [UNDISCH_TAC `coprime(a,b)` THEN
    SIMP_TAC[GSYM DIVIDES_GCD; COPRIME_GCD; DIVIDES_ONE]; ALL_TAC] THEN
  REWRITE_TAC[lemma] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_TAC `y1:num`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:num` (X_CHOOSE_TAC `y2:num`)) THEN
  EXISTS_TAC `v * a * x1 + u * b * x2:num` THEN
  EXISTS_TAC `v * x1 + u * y2:num` THEN
  EXISTS_TAC `v * y1 + u * x2:num` THEN CONJ_TAC THENL
   [SUBST1_TAC(ASSUME `b * x2 = a * y2 + 1`);
    SUBST1_TAC(ASSUME `a * x1 = b * y1 + 1`)] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_AC] THEN REWRITE_TAC[ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* Index of a (usually prime) divisor of a number.                           *)
(* ------------------------------------------------------------------------- *)

let FINITE_EXP_LE = prove
 (`!P p n. 2 <= p ==> FINITE {j | P j /\ p EXP j <= n}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; LE_0; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN TRANS_TAC LE_TRANS `p EXP i` THEN
  ASM_REWRITE_TAC[] THEN TRANS_TAC LE_TRANS `2 EXP i` THEN
  ASM_SIMP_TAC[EXP_MONO_LE_IMP; LT_POW2_REFL; LT_IMP_LE]);;

let FINITE_INDICES = prove
 (`!P p n. 2 <= p /\ ~(n = 0) ==> FINITE {j | P j /\ p EXP j divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{j | P j /\ p EXP j <= n}` THEN
  ASM_SIMP_TAC[FINITE_EXP_LE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[DIVIDES_LE]);;

let index_def = new_definition
 `index p n = if p <= 1 \/ n = 0 then 0
              else CARD {j | 1 <= j /\ p EXP j divides n}`;;

let INDEX_0 = prove
 (`!p. index p 0 = 0`,
  REWRITE_TAC[index_def]);;

let PRIMEPOW_DIVIDES_INDEX = prove
 (`!n p k. p EXP k divides n <=> n = 0 \/ p = 1 \/ k <= index p n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[INDEX_0; DIVIDES_0; EXP_EQ_0] THEN
  ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[EXP_ZERO; COND_RAND; COND_RATOR] THEN
  ASM_SIMP_TAC[LE_0; DIVIDES_1; ARITH; index_def; DIVIDES_ZERO] THEN
  SIMP_TAC[CONJUNCT1 LE; COND_ID] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[EXP_ONE; DIVIDES_1] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]  THEN
  SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL  [ASM_ARITH_TAC; ALL_TAC]  THEN
  MP_TAC(ISPECL [`n:num`; `p:num`] FACTORIZATION_INDEX) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. p EXP k divides n <=> k <= a` ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THENL [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
    DISCH_TAC THEN TRANS_TAC DIVIDES_TRANS `p EXP a` THEN
    ASM_SIMP_TAC[DIVIDES_EXP_LE];
    ASM_REWRITE_TAC[GSYM numseg; CARD_NUMSEG_1]]);;

let LE_INDEX = prove
 (`!n p k. k <= index p n <=> (n = 0 \/ p = 1 ==> k = 0) /\ p EXP k divides n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[INDEX_0; CONJUNCT1 LE] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[index_def; ARITH; CONJUNCT1 LE]);;

let EXP_INDEX_DIVIDES = prove
 (`!p n. p EXP (index p n) divides n`,
  MESON_TAC[LE_INDEX; LE_REFL]);;

let INDEX_LT = prove
 (`!n p k. (~(n = 0) \/ ~(k = 0)) /\ n < p EXP k ==> index p n < k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM NOT_LE; LE_INDEX] THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o MATCH_MP DIVIDES_LE_STRONG)) THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[]);;

let INDEX_1 = prove
 (`!p. index p 1 = 0`,
  GEN_TAC THEN REWRITE_TAC[index_def; ARITH] THEN COND_CASES_TAC THEN
  REWRITE_TAC[DIVIDES_ONE; EXP_EQ_1] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(p <= 1) ==> ~(p = 1)`;
               ARITH_RULE `~(1 <= j /\ j = 0)`;
               EMPTY_GSPEC; CARD_CLAUSES]);;

let INDEX_MUL = prove
 (`!m n. prime p /\ ~(m = 0) /\ ~(n = 0)
         ==> index p (m * n) = index p m + index p n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  SUBGOAL_THEN `~(p = 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[LE_REFL]
     `(!k:num. k <= m ==> k <= n) ==> m <= n`) THEN
    MP_TAC(SPEC `p:num` PRIMEPOW_DIVIDES_PROD) THEN
    ASM_REWRITE_TAC[LE_INDEX; MULT_EQ_0] THEN ASM_MESON_TAC[LE_ADD2; LE_INDEX];
    ASM_REWRITE_TAC[LE_INDEX; MULT_EQ_0; EXP_ADD] THEN
    MATCH_MP_TAC DIVIDES_MUL2 THEN ASM_MESON_TAC[LE_INDEX; LE_REFL]]);;

let INDEX_EXP = prove
 (`!p n k. prime p ==> index p (n EXP k) = k * index p n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[EXP_ZERO; INDEX_0; COND_RAND; COND_RATOR; INDEX_1;
                  MULT_CLAUSES; COND_ID] THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[INDEX_MUL; EXP_EQ_0; EXP; INDEX_1; MULT_CLAUSES] THEN
  ARITH_TAC);;

let INDEX_FACT = prove
 (`!p n. prime p ==> index p (FACT n) = nsum(1..n) (\m. index p m)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[FACT; NSUM_CLAUSES_NUMSEG; INDEX_1; ARITH] THEN
  ASM_SIMP_TAC[INDEX_MUL; NOT_SUC; FACT_NZ] THEN ARITH_TAC);;

let INDEX_FACT_ALT = prove
 (`!p n. prime p
         ==> index p (FACT n) =
             nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV (p EXP j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INDEX_FACT] THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(p = 1) /\ 2 <= p /\ ~(p <= 1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[index_def; LE_1] THEN
  TRANS_TAC EQ_TRANS
   `nsum(1..n) (\m. nsum {j | 1 <= j /\ p EXP j <= n}
                         (\j. if p EXP j divides m then 1 else 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM NSUM_RESTRICT_SET; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[NSUM_CONST; FINITE_INDICES; LE_1; MULT_CLAUSES] THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[DIVIDES_LE; LE_1; LE_TRANS];
    W(MP_TAC o PART_MATCH (lhs o rand) NSUM_SWAP o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_EXP_LE] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM NSUM_RESTRICT_SET] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NSUM_CONST; FINITE_NUMSEG; FINITE_RESTRICT; MULT_CLAUSES] THEN
    SUBGOAL_THEN `{m | m IN 1..n /\ p EXP j divides m} =
                  IMAGE (\q. p EXP j * q) (1..(n DIV p EXP j))`
     (fun th -> ASM_SIMP_TAC[CARD_IMAGE_INJ; FINITE_NUMSEG; EQ_MULT_LCANCEL;
                             th; EXP_EQ_0; PRIME_IMP_NZ; CARD_NUMSEG_1]) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG; IN_ELIM_THM; divides] THEN
    X_GEN_TAC `d:num` THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `q:num` THEN
    ASM_CASES_TAC `d = p EXP j * q` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; EXP_EQ_0; PRIME_IMP_NZ; MULT_EQ_0;
                 ARITH_RULE `1 <= x <=> ~(x = 0)`]]);;

let INDEX_FACT_UNBOUNDED = prove
 (`!p n. prime p
         ==> index p (FACT n) = nsum {j | 1 <= j} (\j. n DIV (p EXP j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INDEX_FACT_ALT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; IMP_CONJ; DIV_EQ_0; EXP_EQ_0;
               PRIME_IMP_NZ; NOT_LE]);;

let PRIMEPOW_DIVIDES_FACT = prove
 (`!p n k. prime p
           ==> (p EXP k divides FACT n <=>
                k <= nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV (p EXP j)))`,
  SIMP_TAC[PRIMEPOW_DIVIDES_INDEX; INDEX_FACT_ALT; FACT_NZ] THEN
  MESON_TAC[PRIME_1]);;

let INDEX_REFL = prove
 (`!n. index n n = if n <= 1 then 0 else 1`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[index_def] THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[MESON[EXP_1] `a divides b <=> a divides b EXP 1`] THEN
  ASM_CASES_TAC `2 <= n` THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  ASM_SIMP_TAC[DIVIDES_EXP_LE; GSYM numseg; CARD_NUMSEG_1]);;

let INDEX_EQ_0 = prove
 (`!p n. index p n = 0 <=> n = 0 \/ p = 1 \/ ~(p divides n)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 0 <=> ~(1 <= n)`] THEN
  REWRITE_TAC[LE_INDEX; EXP_1; ARITH] THEN MESON_TAC[]);;

let INDEX_ZERO = prove
 (`!p n. ~(p divides n) ==> index p n = 0`,
  SIMP_TAC[INDEX_EQ_0]);;

let INDEX_POW = prove
 (`!p n k. index (p EXP k) n = index p n DIV k`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[DIV_ZERO; INDEX_EQ_0; EXP]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [MESON[LE_TRANS; LE_ANTISYM]
   `(m:num = n) <=> !d. d <= m <=> d <= n`] THEN
  X_GEN_TAC `d:num` THEN ASM_SIMP_TAC[LE_INDEX; LE_RDIV_EQ; EXP_EXP] THEN
  ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_1]);;

let INDEX_PRIME = prove
 (`!p a. prime p ==> index a p = if p = a then 1 else 0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INDEX_REFL; INDEX_EQ_0] THEN
  ASM_MESON_TAC[prime; PRIME_0; PRIME_1;
                ARITH_RULE `p <= 1 <=> p = 0 \/ p = 1`]);;

let INDEX_TRIVIAL_BOUND = prove
 (`!n p. index p n <= n`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `p:num`; `n:num`] PRIMEPOW_DIVIDES_INDEX) THEN
  REWRITE_TAC[index_def] THEN COND_CASES_TAC THEN REWRITE_TAC[LE_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < p ==> ~(p = 1)`] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MATCH_MP_TAC(ARITH_RULE `~(m:num <= n) ==> n <= m`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[NOT_LE] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP n` THEN
  REWRITE_TAC[LT_POW2_REFL] THEN
  MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC);;

let INDEX_DECOMPOSITION = prove
 (`!n p. ?m. p EXP (index p n) * m = n /\ (n = 0 \/ p = 1 \/ ~(p divides m))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `p:num`; `index p n`] LE_INDEX) THEN
  REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `p:num`; `index p n + 1`] LE_INDEX) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ARITH_RULE `~(n + 1 <= n)`] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXP_ADD; EXP_1; CONTRAPOS_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  NUMBER_TAC);;

let INDEX_DECOMPOSITION_PRIME = prove
 (`!n p. prime p ==> ?m. p EXP (index p n) * m = n /\ (n = 0 \/ coprime(p,m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PRIME_COPRIME_STRONG]);;

let INDEX_DECOMPOSITION_LE = prove
 (`!p e1 m1 e2 m2.
    p EXP e1 * m1 = p EXP e2 * m2 /\ ~(p = 0) /\ ~(p divides m2) ==> e1 <= e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAUT
   `p /\ ~q /\ ~r ==> s <=> ~q ==> ~s ==> p ==> r`] THEN
  DISCH_TAC THEN REWRITE_TAC[NOT_LE; LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[EXP_ADD; GSYM MULT_ASSOC; EQ_MULT_LCANCEL; EXP_EQ_0] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXP] THEN
  CONV_TAC NUMBER_RULE);;

let INDEX_DECOMPOSITION_UNIQUE = prove
 (`!p e1 m1 e2 m2.
        p EXP e1 * m1 = p EXP e2 * m2 /\
        ~(p = 0) /\ ~(p divides m1) /\ ~(p divides m2)
        ==> e1 = e2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  ASM_MESON_TAC[INDEX_DECOMPOSITION_LE]);;

let INDEX_UNIQUE = prove
 (`!p m n e.
        p EXP e * m = n /\ (p = 0 ==> e = 0) /\ ~(p divides m)
        ==> index p n = e`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `i = e <=> e <= i /\ ~(e + 1 <= i)`] THEN
  REWRITE_TAC[LE_INDEX; ARITH_RULE `~(e + 1 = 0)`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN POP_ASSUM MP_TAC THEN
  UNDISCH_TAC `p = 0 ==> e = 0` THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[DIVIDES_1] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0; MULT_EQ_0] THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[EXP_EQ_0; DIVIDES_ZERO] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[EXP_ZERO; MULT_CLAUSES; ARITH; DIVIDES_1; DIVIDES_ZERO] THEN
  REWRITE_TAC[EXP_ADD; NUMBER_RULE `p divides (p * q:num)`] THEN
  ASM_SIMP_TAC[DIVIDES_LMUL2_EQ; EXP_EQ_0; EXP_1]);;

let INDEX_UNIQUE_EQ = prove
 (`!n p k. index p n = k <=>
           if p = 1 \/ n = 0 then k = 0
           else !j. p EXP j divides n <=> j <= k`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[index_def] THEN ASM_MESON_TAC[LE_REFL];
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM])] THEN
  ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN
  MESON_TAC[LE_ANTISYM]);;

let INDEX_UNIQUE_ALT = prove
 (`!n p k. index p n = k <=>
           if p = 1 \/ n = 0 then k = 0
           else p EXP k divides n /\ ~(p EXP (k + 1) divides n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INDEX_UNIQUE_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[DIVIDES_EXP_LE_IMP; DIVIDES_TRANS]] THEN
  UNDISCH_TAC `~(p EXP (k + 1) divides n)` THEN
  REWRITE_TAC[GSYM NOT_LT; CONTRAPOS_THM] THEN
  REWRITE_TAC[ARITH_RULE `k < j <=> k + 1 <= j`] THEN
  ASM_MESON_TAC[DIVIDES_EXP_LE_IMP; DIVIDES_TRANS]);;

let INDEX_ADD_MIN = prove
 (`!p m n. MIN (index p m) (index p n) <= index p (m + n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 1` THENL
   [ASM_SIMP_TAC[index_def] THEN ARITH_TAC; REWRITE_TAC[LE_INDEX]] THEN
  ASM_SIMP_TAC[ADD_EQ_0; INDEX_EQ_0; ARITH_RULE
   `MIN a b = 0 <=> a = 0 \/ b = 0`] THEN
  MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC THEN MATCH_MP_TAC DIVIDES_TRANS THENL
   [EXISTS_TAC `p EXP (index p m)`; EXISTS_TAC `p EXP (index p n)`] THEN
  REWRITE_TAC[EXP_INDEX_DIVIDES] THEN
  MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ARITH_TAC);;

let INDEX_SUB_MIN = prove
 (`!p m n. n < m ==> MIN (index p m) (index p n) <= index p (m - n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 1` THENL
   [ASM_SIMP_TAC[index_def] THEN ARITH_TAC; REWRITE_TAC[LE_INDEX]] THEN
  ASM_SIMP_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
  MATCH_MP_TAC DIVIDES_ADD_REVL THEN EXISTS_TAC `n:num` THEN
  ASM_SIMP_TAC[SUB_ADD; LT_IMP_LE] THEN
  CONJ_TAC THEN MATCH_MP_TAC DIVIDES_TRANS THENL
   [EXISTS_TAC `p EXP (index p n)`; EXISTS_TAC `p EXP (index p m)`] THEN
  REWRITE_TAC[EXP_INDEX_DIVIDES] THEN
  MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ARITH_TAC);;

let INDEX_ADD = prove
 (`!p n m.
        ~(n = 0) /\ (~(m = 0) ==> index p n < index p m)
        ==> index p (m + n) = index p n`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_CASES_TAC `p = 1` THENL
   [ASM_MESON_TAC[INDEX_EQ_0; LT_REFL]; REPEAT STRIP_TAC] THEN
  ASM_REWRITE_TAC[INDEX_UNIQUE_ALT; ADD_EQ_0] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIVIDES_ADD;
    MATCH_MP_TAC(MESON[DIVIDES_ADD_REVR]
     `(p:num) divides m /\ ~(p divides n) ==> ~(p divides m + n)`)] THEN
  ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN ASM_ARITH_TAC);;

let INDEX_MULT_BASE = prove
 (`(!p n. index p (p * n) = if p <= 1 \/ n = 0 then 0 else index p n + 1) /\
   (!p n. index p (n * p) = if p <= 1 \/ n = 0 then 0 else index p n + 1)`,
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [MESON_TAC[MULT_SYM]; REPEAT GEN_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[index_def] THEN ASM_MESON_TAC[MULT_EQ_0];
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN POP_ASSUM MP_TAC] THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[LE_0] THEN STRIP_TAC THEN
  MATCH_MP_TAC INDEX_UNIQUE THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ONCE_REWRITE_RULE[ADD_SYM] EXP_ADD] THEN
  ASM_REWRITE_TAC[EXP_1; GSYM MULT_ASSOC] THEN
  ASM_MESON_TAC[INDEX_DECOMPOSITION; LE_REFL]);;

let INDEX_MULT_EXP = prove
 (`(!p n k. index p (p EXP k * n) =
            if p <= 1 \/ n = 0 then 0 else k + index p n) /\
   (!p n k. index p (n * p EXP k) =
            if n = 0 \/ p <= 1 then 0 else index p n + k)`,
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_SYM; ADD_SYM; DISJ_SYM]; GEN_TAC THEN GEN_TAC] THEN
  ASM_CASES_TAC `p = 0` THENL [ASM_REWRITE_TAC[index_def; ARITH]; ALL_TAC] THEN
  ASM_CASES_TAC `p <= 1` THENL [ASM_REWRITE_TAC[index_def]; ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[index_def; MULT_CLAUSES]; ASM_REWRITE_TAC[]] THEN
  INDUCT_TAC THEN REWRITE_TAC[EXP; MULT_CLAUSES; GSYM MULT_ASSOC] THEN
  ASM_REWRITE_TAC[INDEX_MULT_BASE; ADD1; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0] THEN ARITH_TAC);;

let INDEX_MULT_ADD = prove
 (`(!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (p EXP k * m + n) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (m * p EXP k + n) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (n + m * p EXP k) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (n + p EXP k * m) = index p n)`,
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_SYM; ADD_SYM; DISJ_SYM]; REPEAT GEN_TAC] THEN
  ASM_CASES_TAC `p <= 1` THENL [ASM_REWRITE_TAC[index_def]; ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC INDEX_ADD THEN
  ASM_SIMP_TAC[MULT_EQ_0; EXP_EQ_0; DE_MORGAN_THM] THEN
  REWRITE_TAC[INDEX_MULT_EXP] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let INDEX_NSUM_LE = prove
 (`!(f:A->num) p n k.
         FINITE k /\ ~(k = {}) /\ (!a. a IN k ==> n <= index p (f a))
         ==> n <= index p (nsum k f)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `\m. n <= index p m`
   NSUM_CLOSED_NONEMPTY) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH rand INDEX_ADD_MIN o rand o snd) THEN ASM_ARITH_TAC);;

let DIVIDES_INDEX = prove
 (`!m n. m divides n <=>
         n = 0 \/ ~(m = 0) /\ !p. prime p ==> index p m <= index p n`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
  ONCE_REWRITE_TAC[MESON[LE_REFL; LE_ANTISYM; LE_TRANS]
   `m <= n <=> !k:num. k <= m ==> k <= n`] THEN
  REWRITE_TAC[LE_INDEX] THEN
  ASM_SIMP_TAC[MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
  GEN_REWRITE_TAC LAND_CONV [PRIMEPOW_DIVISORS_DIVIDES] THEN MESON_TAC[]);;

let EQ_INDEX = prove
 (`!m n. m = n <=> (m = 0 <=> n = 0) /\ !p. prime p ==> index p m = index p n`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM DIVIDES_ANTISYM] THEN
  REWRITE_TAC[DIVIDES_INDEX] THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[LE_ANTISYM]);;

let COPRIME_INDEX = prove
 (`!m n. coprime(m,n) <=>
         (m = 0 ==> n = 1) /\ (n = 0 ==> m = 1) /\
         !p. prime p ==> index p m = 0 \/ index p n = 0`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_SIMP_TAC[INDEX_EQ_0; COPRIME_0;
               MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
  MESON_TAC[COPRIME_PRIME_EQ]);;

let INDEX_GCD = prove
 (`!m n p.
        prime p
        ==> index p (gcd(m,n)) =
            if m = 0 then index p n
            else if n = 0 then index p m
            else MIN (index p m) (index p n)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_SIMP_TAC[GCD_0; INDEX_0] THEN
  REWRITE_TAC[ARITH_RULE `MIN 0 n = 0 /\ MIN m 0 = 0`] THEN
  MP_TAC(GEN `k:num` (SPECL [`m:num`; `n:num`; `p EXP k`] DIVIDES_GCD)) THEN
  ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN
  ASM_SIMP_TAC[MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
  ASM_REWRITE_TAC[GCD_ZERO] THEN
  REWRITE_TAC[ARITH_RULE `k <= m /\ k <= n <=> k <= MIN m n`] THEN
  MESON_TAC[LE_REFL; LE_ANTISYM; LE_TRANS]);;

let FORALL_PRIME_INDEX = prove
 (`(!p. prime p ==> !P. ((!x. P(index p x)) <=> !k. P k)) /\
   (!p. prime p ==> !P. ((!x. ~(x = 0) ==> P(index p x)) <=> !k. P k))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `p EXP k`) THEN
  ASM_SIMP_TAC[INDEX_EXP; INDEX_REFL; EXP_EQ_0; PRIME_IMP_NZ] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC);;

let INDEX_FACT_PRIME_MULT = prove
 (`!p n. prime p ==> index p (FACT(p * n)) = n + index p (FACT n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; FACT; INDEX_1; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[INDEX_FACT; MULT_EQ_0; PRIME_IMP_NZ; INDEX_MUL] THEN
  TRANS_TAC EQ_TRANS `nsum (IMAGE (\i. p * i) (1..n)) (\m. index p m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_SUPERSET THEN MATCH_MP_TAC(SET_RULE
     `(!x. f x IN t <=> x IN s) /\
      (!y. ~P y ==> y IN IMAGE f UNIV)
      ==> IMAGE f s SUBSET t /\ !y. y IN t /\ ~(y IN IMAGE f s) ==> P y`) THEN
    REWRITE_TAC[IN_NUMSEG; LE_MULT_LCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                MULT_EQ_0; IN_IMAGE; IN_UNIV; INDEX_EQ_0; divides] THEN
    ASM_MESON_TAC[PRIME_0];
    ASM_SIMP_TAC[NSUM_IMAGE; EQ_MULT_LCANCEL; PRIME_IMP_NZ; o_DEF] THEN
    ASM_SIMP_TAC[INDEX_MUL; LE_1; PRIME_IMP_NZ; NSUM_ADD_NUMSEG] THEN
    REWRITE_TAC[ETA_AX; EQ_ADD_RCANCEL] THEN
    SIMP_TAC[NSUM_CONST; FINITE_NUMSEG; CARD_NUMSEG_1] THEN
    REWRITE_TAC[INDEX_REFL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC]);;

let PRIME_FACTORIZATION_INDEX = prove
 (`!k. FINITE {p | prime p /\ ~(k p = 0)}
       ==> ?n. ~(n = 0) /\ !p. prime p ==> index p n = k p`,
  SUBGOAL_THEN
   `!s. FINITE s
       ==> !k. {p | prime p /\ ~(k p = 0)} SUBSET s
               ==> ?n. ~(n = 0) /\ !p. prime p ==> index p n = k p`
  MP_TAC THENL [ALL_TAC; MESON_TAC[SUBSET_REFL]] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE
     `{p | prime p /\ ~Z p} SUBSET {} <=> !p. prime p ==> Z p`] THEN
    MESON_TAC[INDEX_1; ARITH_RULE `~(1 = 0)`];
    MAP_EVERY X_GEN_TAC [`p:num`; `s:num->bool`] THEN STRIP_TAC THEN
    X_GEN_TAC `k:num->num` THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC
     `\i. if i = p then 0 else (k:num->num) i`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `prime p` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `p EXP k p * n` THEN
    ASM_SIMP_TAC[INDEX_MUL; MULT_EQ_0; EXP_EQ_0; INDEX_EXP] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[INDEX_REFL] THENL
     [COND_CASES_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC;
      DISCH_TAC THEN REWRITE_TAC[EQ_ADD_RCANCEL_0; MULT_EQ_0] THEN
      ASM_SIMP_TAC[INDEX_EQ_0; DIVIDES_PRIME_PRIME]]]);;

let PRIME_POWER_EXISTS = prove
 (`!n q. prime q
         ==> ((?i. n = q EXP i) <=>
              (!p. prime p /\ p divides n ==> p = q))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [PRIMEPOW_DIVISORS_EQ] THEN
  ASM_SIMP_TAC[DIVIDES_PRIME_EXP_LE] THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` (MP_TAC o SPECL [`p:num`; `1`])) THEN
    ASM_SIMP_TAC[EXP_1; ARITH_EQ];
    EXISTS_TAC `index q n` THEN MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN
    STRIP_TAC THEN ASM_CASES_TAC `k = 0` THEN
    ASM_REWRITE_TAC[EXP; DIVIDES_1; LE_INDEX] THEN
    ASM_CASES_TAC `p EXP k divides n` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_ASSUM(MP_TAC o SPEC `p:num`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[DIVIDES_EXP2]; DISCH_THEN SUBST_ALL_TAC] THEN
    ASM_REWRITE_TAC[DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[PRIME_1]] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `2` th)) THEN
    ASM_REWRITE_TAC[DIVIDES_0; NOT_IMP] THEN
    REWRITE_TAC[PRIME_ALT; IMP_CONJ_ALT; DIVIDES_MOD] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[LT] THEN ARITH_TAC]);;

let PRIME_POWER_EXISTS_ALT = prove
 (`!n p.
         prime p
         ==> ((?i. n = p EXP i) <=>
              (!d. d divides n ==> d = 1 \/ p divides d))`,
  SIMP_TAC[PRIME_POWER_EXISTS] THEN
  MESON_TAC[DIVIDES_TRANS; DIVIDES_PRIME_PRIME; PRIME_FACTOR; PRIME_1]);;

let PRIME_FACTORIZATION_ALT = prove
 (`!n. ~(n = 0) ==> nproduct {p | prime p} (\p. p EXP index p n) = n`,
  MATCH_MP_TAC COMPLETE_FACTOR_INDUCT THEN
  REWRITE_TAC[INDEX_0; INDEX_1; MULT_EQ_0; ARITH_EQ; DE_MORGAN_THM; EXP] THEN
  SIMP_TAC[REWRITE_RULE[GSYM nproduct; NEUTRAL_MUL]
            (MATCH_MP ITERATE_EQ_NEUTRAL MONOIDAL_MUL)] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `p:num` THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC[INDEX_PRIME] THEN
    REWRITE_TAC[COND_RAND; EXP; EXP_1] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REWRITE_RULE[GSYM nproduct; NEUTRAL_MUL]
        (MATCH_MP ITERATE_DELTA MONOIDAL_MUL)];
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `x * y = z ==> x = m /\ y = n ==> z = m * n`) THEN
    W(MP_TAC o PART_MATCH (rand o rand)
      (REWRITE_RULE[GSYM nproduct] (MATCH_MP ITERATE_OP_GEN MONOIDAL_MUL)) o
      lhand o snd) THEN
    REWRITE_TAC[support; NEUTRAL_MUL] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; EXP_EQ_1; INDEX_EQ_0] THEN
      ASM_SIMP_TAC[DE_MORGAN_THM; CONJ_ASSOC; FINITE_SPECIAL_DIVISORS];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC(REWRITE_RULE[GSYM nproduct]
        (MATCH_MP ITERATE_EQ MONOIDAL_MUL)) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; INDEX_MUL; EXP_ADD]]);;

let PRIME_FACTORIZATION = prove
 (`!n. ~(n = 0)
       ==> nproduct {p | prime p /\ p divides n} (\p. p EXP index p n) = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
        [SYM(MATCH_MP PRIME_FACTORIZATION_ALT th)]) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[nproduct] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_SUPERSET MONOIDAL_MUL) THEN
  SIMP_TAC[IN_ELIM_THM; IMP_CONJ; NEUTRAL_MUL; EXP_EQ_1; INDEX_EQ_0] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Least common multiples.                                                   *)
(* ------------------------------------------------------------------------- *)

let lcm = prove
 (`lcm(m,n) = if m * n = 0 then 0 else (m * n) DIV gcd(m,n)`,
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL; NUM_LCM; int_lcm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_DIV; INT_ABS_NUM; GSYM NUM_GCD]);;

let LCM_DIVIDES = prove
 (`!m n d. lcm(m,n) divides d <=> m divides d /\ n divides d`,
  NUMBER_TAC);;

let LCM = prove
 (`!m n. m divides lcm(m,n) /\
         n divides lcm(m,n) /\
         (!d. m divides d /\ n divides d ==> lcm(m,n) divides d)`,
  NUMBER_TAC);;

let LCM_DIVIDES_MUL = prove
 (`!m n. lcm(m,n) divides m * n`,
  REWRITE_TAC[LCM_DIVIDES] THEN CONV_TAC NUMBER_RULE);;

let DIVIDES_LCM = prove
 (`!m n r. r divides m \/ r divides n
           ==> r divides lcm(m,n)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] DIVIDES_TRANS)) THEN
  ASM_MESON_TAC[LCM]);;

let LCM_0 = prove
 (`(!n. lcm(0,n) = 0) /\ (!n. lcm(n,0) = 0)`,
  REWRITE_TAC[lcm; MULT_CLAUSES] THEN ARITH_TAC);;

let LCM_1 = prove
 (`(!n. lcm(1,n) = n) /\ (!n. lcm(n,1) = n)`,
  SIMP_TAC[lcm; MULT_CLAUSES; GCD_1; DIV_1] THEN MESON_TAC[]);;

let LCM_SYM = prove
 (`!m n. lcm(m,n) = lcm(n,m)`,
  REWRITE_TAC[lcm; MULT_SYM; GCD_SYM; ARITH_RULE `MAX m n = MAX n m`]);;

let DIVIDES_LCM_GCD = prove
 (`!m n d. d divides lcm(m,n) <=> d * gcd(m,n) divides m * n`,
  NUMBER_TAC);;

let PRIMEPOW_DIVIDES_LCM = prove
 (`!m n p k.
        prime p
        ==> (p EXP k divides lcm(m,n) <=>
             p EXP k divides m \/ p EXP k divides n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [STRIP_TAC; MESON_TAC[DIVIDES_LCM]] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[LCM_0; DIVIDES_0] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[LCM_0; DIVIDES_0] THEN
  MP_TAC(SPECL [`n:num`; `p:num`] FACTORIZATION_INDEX) THEN
  MP_TAC(SPECL [`m:num`; `p:num`] FACTORIZATION_INDEX) THEN
  ASM_SIMP_TAC[PRIME_GE_2; LEFT_IMP_EXISTS_THM; divides;
               LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `q:num`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`b:num`; `r:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM divides] THEN
  UNDISCH_TAC `p EXP k divides lcm (m,n)` THEN
  ASM_REWRITE_TAC[DIVIDES_LCM_GCD] THEN
  SUBGOAL_THEN
   `gcd(p EXP a * q,p EXP b * r) =
    p EXP (MIN a b) * gcd(p EXP (a - MIN a b) * q,p EXP (b - MIN a b) * r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM GCD_LMUL; MULT_ASSOC; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD]] THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP (NUMBER_RULE `a * b divides c ==> a divides c`)) THEN
  REWRITE_TAC[ARITH_RULE `((a * b) * c) * d:num = (a * c) * b * d`] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
   (ONCE_REWRITE_RULE[MULT_SYM] COPRIME_EXP_DIVPROD))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC COPRIME_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC(MESON[PRIME_COPRIME_STRONG]
      `prime p /\ ~(p divides n) ==> coprime(p,n)`) THEN
    ASM_REWRITE_TAC[divides] THEN STRIP_TAC THENL
     [UNDISCH_TAC `!l. a < l ==> ~(?x. m = p EXP l * x)` THEN
      DISCH_THEN(MP_TAC o SPEC `a + 1`);
      UNDISCH_TAC `!l. b < l ==> ~(?x. n = p EXP l * x)` THEN
      DISCH_THEN(MP_TAC o SPEC `b + 1`)] THEN
    ASM_REWRITE_TAC[ARITH_RULE `a < a + 1`; EXP_ADD; EXP_1] THEN
    MESON_TAC[MULT_AC];
    ASM_SIMP_TAC[DIVIDES_EXP_LE; PRIME_GE_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `k + MIN a b <= a + b ==> k <= a \/ k <= b`)) THEN
    MATCH_MP_TAC MONO_OR THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN ASM_SIMP_TAC[DIVIDES_EXP_LE; PRIME_GE_2]]);;

let PRIME_DIVIDES_LCM = prove
 (`!m n p.
        prime p
        ==> (p divides lcm(m,n) <=> p divides m \/ p divides n)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`m:num`; `n:num`; `p:num`; `1`] PRIMEPOW_DIVIDES_LCM) THEN
  REWRITE_TAC[EXP_1]);;

let LCM_ZERO = prove
 (`!m n. lcm(m,n) = 0 <=> m = 0 \/ n = 0`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MULTIPLES_EQ] THEN
  REWRITE_TAC[LCM_DIVIDES; DIVIDES_ZERO] THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
  ASM_MESON_TAC[DIVIDES_REFL; MULT_EQ_0; DIVIDES_LMUL; DIVIDES_RMUL]);;

let INDEX_LCM = prove
 (`!m n p.
        prime p
        ==> index p (lcm(m,n)) =
            if m = 0 \/ n = 0 then 0
            else MAX (index p m) (index p n)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_SIMP_TAC[LCM_0; INDEX_0] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`] o MATCH_MP
    PRIMEPOW_DIVIDES_LCM) THEN
  ASM_REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX; LCM_ZERO] THEN
  ASM_SIMP_TAC[MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
  REWRITE_TAC[ARITH_RULE `k <= m \/ k <= n <=> k <= MAX m n`] THEN
  MESON_TAC[LE_REFL; LE_ANTISYM; LE_TRANS]);;

let LCM_ASSOC = prove
 (`!m n p. lcm(m,lcm(n,p)) = lcm(lcm(m,n),p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MULTIPLES_EQ] THEN
  REWRITE_TAC[LCM_DIVIDES] THEN X_GEN_TAC `q:num` THEN
  REWRITE_TAC[LCM_ZERO] THEN CONV_TAC TAUT);;

let LCM_REFL = prove
 (`!n. lcm(n,n) = n`,
  REWRITE_TAC[lcm; GCD_REFL; MULT_EQ_0; ARITH_RULE `MAX n n = n`] THEN
  SIMP_TAC[DIV_MULT] THEN MESON_TAC[]);;

let LCM_MULTIPLE = prove
 (`!a b. lcm(b,a * b) = a * b`,
  REWRITE_TAC[MULTIPLES_EQ; LCM_DIVIDES] THEN NUMBER_TAC);;

let LCM_GCD_DISTRIB = prove
 (`!a b c. lcm(a,gcd(b,c)) = gcd(lcm(a,b),lcm(a,c))`,
  REWRITE_TAC[PRIMEPOW_DIVISORS_EQ] THEN
  SIMP_TAC[PRIMEPOW_DIVIDES_LCM; DIVIDES_GCD] THEN CONV_TAC TAUT);;

let GCD_LCM_DISTRIB = prove
 (`!a b c. gcd(a,lcm(b,c)) = lcm(gcd(a,b),gcd(a,c))`,
  REWRITE_TAC[PRIMEPOW_DIVISORS_EQ] THEN
  SIMP_TAC[PRIMEPOW_DIVIDES_LCM; DIVIDES_GCD] THEN CONV_TAC TAUT);;

let LCM_UNIQUE = prove
 (`!d m n.
       m divides d /\ n divides d /\
       (!e. m divides e /\ n divides e ==> d divides e) <=>
       d = lcm(m,n)`,
  REWRITE_TAC[MULTIPLES_EQ; LCM_DIVIDES] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_TRANS]);;

let LCM_EQ = prove
 (`!x y u v. (!d. x divides d /\ y divides d <=> u divides d /\ v divides d)
             ==> lcm(x,y) = lcm(u,v)`,
  SIMP_TAC[MULTIPLES_EQ; LCM_DIVIDES]);;

let LCM_EQ_1 = prove
 (`!m n. lcm(m,n) = 1 <=> m = 1 /\ n = 1`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  REWRITE_TAC[GSYM LCM_UNIQUE; DIVIDES_1; DIVIDES_ONE]);;

let DIVIDES_LCM_LEFT = prove
 (`!m n. n divides m <=> lcm(m,n) = m`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
  SIMP_TAC[GSYM LCM_UNIQUE; DIVIDES_REFL]);;

let DIVIDES_LCM_RIGHT = prove
 (`!m n. m divides n <=> lcm(m,n) = n`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
  SIMP_TAC[GSYM LCM_UNIQUE; DIVIDES_REFL]);;

let MULT_LCM_GCD = prove
 (`!m n. lcm(m,n) * gcd(m,n) = m * n`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[GCD_0; LCM_0; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[lcm; MULT_EQ_0; GSYM DIVIDES_DIV_MULT] THEN
  CONV_TAC NUMBER_RULE);;

let MULT_GCD_LCM = prove
 (`!m n. gcd(m,n) * lcm(m,n) = m * n`,
  MESON_TAC[MULT_SYM; MULT_LCM_GCD]);;

let LCM_LMUL = prove
 (`!a b c. lcm(c * a,c * b) = c * lcm(a,b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LCM_0] THEN
  ASM_REWRITE_TAC[lcm; GCD_LMUL; MULT_EQ_0; DISJ_ACI] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  ASM_SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT2; MULT_EQ_0; GCD_ZERO] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  ASM_SIMP_TAC[ADD_CLAUSES; LE_1; GCD_ZERO] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
    `a * c * b:num = (c * d) * g <=> c * d * g = c * a * b`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
  CONV_TAC NUMBER_RULE);;

let LCM_RMUL = prove
 (`!a b c. lcm(a * c,b * c) = c * lcm(a,b)`,
  MESON_TAC[LCM_LMUL; MULT_SYM]);;

let LCM_EXP = prove
 (`!n a b. lcm(a EXP n,b EXP n) = lcm(a,b) EXP n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcm] THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[EXP; GCD_REFL; DIV_1; MULT_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[num_CASES; EXP_ZERO]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REWRITE_TAC[GCD_EXP; GSYM MULT_EXP] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  ASM_SIMP_TAC[ADD_CLAUSES; LE_1; GCD_ZERO; EXP_EQ_0] THEN
  REWRITE_TAC[GSYM MULT_EXP] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
  CONV_TAC NUMBER_RULE);;

let LCM_COPRIME_DECOMP = prove
 (`!m n:num.
     ?m' n'.
        m' divides m /\ n' divides n /\ coprime(m',n') /\ m' * n' = lcm(m,n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[DIVIDES_0; COPRIME_0; GCD_0; LCM_0] THEN
    MAP_EVERY EXISTS_TAC [`0`; `1`] THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `n:num`] GCD_COPRIME_EXISTS) THEN
  ASM_REWRITE_TAC[GCD_ZERO; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m':num`; `n':num`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  MP_TAC(ISPECL [`m':num`; `n':num`; `gcd(m,n)`] COPRIME_PAIR_DECOMP) THEN
  ASM_REWRITE_TAC[GCD_ZERO; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n'':num`; `m'':num`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`m' * m'':num`; `n' * n'':num`] THEN
  REWRITE_TAC[COPRIME_LMUL; COPRIME_RMUL; GSYM CONJ_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  ASM_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[DIVIDES_MUL_L; DIVIDES_REFL; DIVIDES_RMUL; DIVIDES_LMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC(NUM_RING `!d. ~(d = 0) /\ a * d = b * d ==> a = b`) THEN
  EXISTS_TAC `gcd(m,n):num` THEN
  ASM_REWRITE_TAC[MULT_LCM_GCD; GCD_ZERO] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NUM_RING);;

let LE_LCM = prove
 (`(!m n. m <= lcm(m,n) <=> n = 0 ==> m = 0) /\
   (!m n. n <= lcm(m,n) <=> m = 0 ==> n = 0)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[LCM_0; LE_REFL; LE] THEN
  MATCH_MP_TAC DIVIDES_LE_IMP THEN
  ASM_REWRITE_TAC[LCM; LCM_ZERO]);;

let LCM_LE_MULT = prove
 (`!m n. lcm(m,n) <= m * n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_REFL; DIV_LE]);;

let LCM_EQ_MULT = prove
 (`!m n. lcm(m,n) = m * n <=> m = 0 \/ n = 0 \/ coprime(m,n)`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[LCM_0; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[lcm; DIV_EQ_SELF; MULT_EQ_0; COPRIME_GCD]);;

let MAX_LE_LCM_EQ = prove
 (`!m n. MAX m n <= lcm(m,n) <=> (m = 0 <=> n = 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_LCM] THEN
  ASM_ARITH_TAC);;

let MAX_LE_LCM = prove
 (`!m n. (m = 0 <=> n = 0) ==> MAX m n <= lcm(m,n)`,
  REWRITE_TAC[MAX_LE_LCM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Iterated GCD and LCM over a finite set (or one with finite support).      *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_GCD = prove
 (`neutral (\m n. gcd(m,n)) = 0`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN MESON_TAC[GCD_0]);;

let MONOIDAL_GCD = prove
 (`monoidal (\m n:num. gcd(m,n))`,
  REWRITE_TAC[monoidal; NEUTRAL_GCD; GCD_0] THEN
  MESON_TAC[GCD_ASSOC; GCD_SYM]);;

let NEUTRAL_LCM = prove
 (`neutral (\m n. lcm(m,n)) = 1`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN MESON_TAC[LCM_1]);;

let MONOIDAL_LCM = prove
 (`monoidal (\m n:num. lcm(m,n))`,
  REWRITE_TAC[monoidal; NEUTRAL_LCM; LCM_1] THEN
  MESON_TAC[LCM_ASSOC; LCM_SYM]);;

let ITERATE_GCD_DIVIDES = prove
 (`!f k i:K.
        FINITE k /\ i IN k
        ==> iterate (\m n:num. gcd(m,n)) k f divides f i`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; MATCH_MP ITERATE_CLAUSES MONOIDAL_GCD] THEN
  MESON_TAC[NOT_IN_EMPTY; GCD; DIVIDES_REFL; DIVIDES_TRANS]);;

let ITERATE_GCD_DIVIDES_EQ = prove
 (`!f k i:K.
        i IN k
        ==> (iterate (\m n:num. gcd(m,n)) k f divides f i <=>
             FINITE {j | j IN k /\ ~(f j = 0)} \/ f i = 0)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f(i:K) = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[support; NEUTRAL_GCD] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
  MATCH_MP_TAC ITERATE_GCD_DIVIDES THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let DIVIDES_ITERATE_GCD = prove
 (`!f (k:K->bool) d.
        FINITE k
        ==> (d divides iterate (\m n:num. gcd(m,n)) k f <=>
             !i. i IN k ==> d divides f i)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; MATCH_MP ITERATE_CLAUSES MONOIDAL_GCD] THEN
  SIMP_TAC[NEUTRAL_GCD; DIVIDES_0; NOT_IN_EMPTY; DIVIDES_GCD]);;

let DIVIDES_ITERATE_GCD_GEN = prove
 (`!f (k:K->bool) d.
        d divides iterate (\m n:num. gcd(m,n)) k f <=>
        FINITE {j | j IN k /\ ~(f j = 0)} ==> !i. i IN k ==> d divides f i`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[support; NEUTRAL_GCD] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  ASM_SIMP_TAC[DIVIDES_ITERATE_GCD; IN_ELIM_THM] THEN
  MESON_TAC[DIVIDES_0]);;

let DIVIDES_ITERATE_LCM = prove
 (`!f k i:K.
        FINITE k /\ i IN k
        ==> f i divides iterate (\m n:num. lcm(m,n)) k f`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM] THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; DIVIDES_LCM; DIVIDES_REFL]);;

let DIVIDES_ITERATE_LCM_GEN = prove
 (`!f k i:K.
        i IN k
        ==> (f i divides iterate (\m n:num. lcm(m,n)) k f <=>
             FINITE {j | j IN k /\ ~(f j = 1)} \/ f i = 1)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f(i:K) = 1` THEN ASM_REWRITE_TAC[DIVIDES_1] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[support; NEUTRAL_LCM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DIVIDES_ONE] THEN
  MATCH_MP_TAC DIVIDES_ITERATE_LCM THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

let ITERATE_LCM_DIVIDES = prove
 (`!f (k:K->bool) n.
        FINITE k
        ==> (iterate (\m n:num. lcm(m,n)) k f divides n <=>
             !i. i IN k ==> f i divides n)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM] THEN
  SIMP_TAC[NEUTRAL_LCM; DIVIDES_1; NOT_IN_EMPTY; LCM_DIVIDES]);;

let ITERATE_LCM_DIVIDES_GEN = prove
 (`!f (k:K->bool) n.
        iterate (\m n:num. lcm(m,n)) k f divides n <=>
        FINITE {j | j IN k /\ ~(f j = 1)} ==> !i. i IN k ==> f i divides n`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[support; NEUTRAL_LCM] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ITERATE_LCM_DIVIDES; DIVIDES_1; IN_ELIM_THM] THEN
  MESON_TAC[DIVIDES_1]);;

let PRIMEPOW_DIVIDES_ITERATE_LCM = prove
 (`!f (k:K->bool) p m.
        FINITE k /\ prime p
        ==> (p EXP m divides iterate (\m n:num. lcm(m,n)) k f <=>
             m = 0 \/ ?i. i IN k /\ p EXP m divides (f i))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[EXISTS_IN_INSERT; MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM;
        PRIMEPOW_DIVIDES_LCM; NOT_IN_EMPTY; NEUTRAL_LCM] THEN
  MESON_TAC[DIVIDES_ONE; EXP_EQ_1; PRIME_1]);;

let PRIMEPOW_DIVIDES_ITERATE_LCM_GEN = prove
 (`!f (k:K->bool) p m.
        prime p
        ==> (p EXP m divides iterate (\m n:num. lcm(m,n)) k f <=>
             m = 0 \/
             FINITE {j | j IN k /\ ~(f j = 1)} /\
             ?i. i IN k /\ p EXP m divides (f i))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[EXP; DIVIDES_1] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[support; NEUTRAL_LCM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DIVIDES_ONE; EXP_EQ_1] THEN
  ASM_SIMP_TAC[PRIMEPOW_DIVIDES_ITERATE_LCM; IN_ELIM_THM] THEN
  ASM_MESON_TAC[DIVIDES_1; DIVIDES_ONE; PRIME_1; EXP_EQ_1]);;

let PRIME_DIVIDES_ITERATE_LCM_GEN = prove
 (`!f (k:K->bool) p.
        prime p
        ==> (p divides iterate (\m n:num. lcm(m,n)) k f <=>
             FINITE {j | j IN k /\ ~(f j = 1)} /\
             ?i. i IN k /\ p divides (f i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:K->num`; `k:K->bool`; `p:num`; `1`]
    PRIMEPOW_DIVIDES_ITERATE_LCM_GEN) THEN
  REWRITE_TAC[EXP_1; ARITH_EQ]);;

let PRIME_DIVIDES_ITERATE_LCM = prove
 (`!f (k:K->bool) p.
        FINITE k /\ prime p
        ==> (p divides iterate (\m n:num. lcm(m,n)) k f <=>
             ?i. i IN k /\ p divides (f i))`,
  SIMP_TAC[PRIME_DIVIDES_ITERATE_LCM_GEN; FINITE_RESTRICT]);;

let ITERATE_LCM_EQ_0_GEN = prove
 (`!(k:K->bool) f.
        iterate (\m n. lcm(m,n)) k f = 0 <=>
        FINITE {j | j IN k /\ ~(f j = 1)} /\
        ?j. j IN k /\ f j = 0`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[support; NEUTRAL_LCM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `n = 0 <=> ~(n = 1) /\ n = 0`] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `j IN k /\ ~(f j = 1) /\ f j = 0 <=>
    j IN {j | j IN k /\ ~(f j = 1)} /\ f j = 0`] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`{j:K | j IN k /\ ~(f j = 1)}`,`k:K->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM] THEN
  SIMP_TAC[NEUTRAL_LCM; LCM_ZERO; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ITERATE_LCM_EQ_0 = prove
 (`!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. lcm(m,n)) k f = 0 <=>
             ?j. j IN k /\ f j = 0)`,
  SIMP_TAC[ITERATE_LCM_EQ_0_GEN; FINITE_RESTRICT]);;

let ITERATE_LCM_EQ_1_GEN = prove
 (`!(k:K->bool) f.
        iterate (\m n. lcm(m,n)) k f = 1 <=>
        FINITE {j | j IN k /\ ~(f j = 1)} ==> !j. j IN k ==> f j = 1`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[support; NEUTRAL_LCM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `(!j. j IN k ==> f j = 1) <=>
    !j. j IN {j | j IN k /\ ~(f j = 1)} ==> f j = 1`] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`{j:K | j IN k /\ ~(f j = 1)}`,`k:K->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM] THEN
  SIMP_TAC[NEUTRAL_LCM; LCM_EQ_1; NOT_IN_EMPTY] THEN SET_TAC[]);;

let ITERATE_LCM_EQ_1 = prove
 (`!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. lcm(m,n)) k f = 1 <=>
             !j. j IN k ==> f j = 1)`,
  SIMP_TAC[ITERATE_LCM_EQ_1_GEN; FINITE_RESTRICT]);;

let ITERATE_GCD_EQ_0_GEN = prove
 (`!(k:K->bool) f.
        iterate (\m n. gcd(m,n)) k f = 0 <=>
        FINITE {j | j IN k /\ ~(f j = 0)} ==> !j. j IN k ==> f j = 0`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REWRITE_TAC[support; NEUTRAL_GCD] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `(!j. j IN k ==> f j = 0) <=>
    !j. j IN {j | j IN k /\ ~(f j = 0)} ==> f j = 0`] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`{j:K | j IN k /\ ~(f j = 0)}`,`k:K->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_GCD] THEN
  SIMP_TAC[NEUTRAL_GCD; GCD_ZERO; NOT_IN_EMPTY] THEN SET_TAC[]);;

let ITERATE_GCD_EQ_0 = prove
 (`!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. gcd(m,n)) k f = 0 <=>
             !j. j IN k ==> f j = 0)`,
  SIMP_TAC[ITERATE_GCD_EQ_0_GEN; FINITE_RESTRICT]);;

(* ------------------------------------------------------------------------- *)
(* Induction principle for multiplicative functions etc.                     *)
(* ------------------------------------------------------------------------- *)

let INDUCT_COPRIME = prove
 (`!P. (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p ==> P(p EXP k))
       ==> !n. 1 < n ==> P n`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `1 < n ==> ~(n = 1)`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:num` o MATCH_MP PRIME_FACTOR) THEN
  MP_TAC(SPECL [`n:num`; `p:num`] FACTORIZATION_INDEX) THEN
  ASM_SIMP_TAC[PRIME_GE_2; ARITH_RULE `1 < n ==> ~(n = 0)`] THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `m = 1` THEN ASM_SIMP_TAC[MULT_CLAUSES] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MATCH_MP_TAC MP_TAC) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(TAUT
   `!p. (a /\ b /\ ~p) /\ c /\ (a /\ ~p ==> b ==> d)
        ==> a /\ b /\ c /\ d`) THEN
  EXISTS_TAC `m = 0` THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `0 < 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[EXP; EXP_1; MULT_CLAUSES; divides];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `1 < p EXP k * m` THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 < x <=> ~(x = 0) /\ ~(x = 1)`] THEN
    ASM_REWRITE_TAC[EXP_EQ_0; EXP_EQ_1; MULT_EQ_0; MULT_EQ_1] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2 o CONJUNCT1) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `k < k + 1`)) THEN
    REWRITE_TAC[EXP_ADD; EXP_1; GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
    ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ; GSYM divides] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
    ASM_MESON_TAC[PRIME_COPRIME; COPRIME_SYM];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = 1 * m`] THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL]]);;

let INDUCT_COPRIME_STRONG = prove
 (`!P. (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p /\ ~(k = 0) ==> P(p EXP k))
       ==> !n. 1 < n ==> P n`,
  GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b <=> a ==> a ==> b`] THEN
  MATCH_MP_TAC INDUCT_COPRIME THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN ASM_CASES_TAC `k = 0` THEN
    ASM_REWRITE_TAC[LT_REFL; EXP] THEN ASM_MESON_TAC[]]);;

let INDUCT_COPRIME_ALT = prove
 (`!P. P 0 /\
       (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p ==> P(p EXP k))
       ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(MESON[]
   `(!n. 1 < n ==> P n) /\ (!n. ~(1 < n) ==> P n) ==> !n. P n`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INDUCT_COPRIME THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ARITH_RULE `~(1 < n) <=> n = 0 \/ n = 1`] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[PRIME_2; EXP]]);;

(* ------------------------------------------------------------------------- *)
(* A conversion for divisibility.                                            *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_CONV =
  let pth_0 = SPEC `b:num` DIVIDES_ZERO
  and pth_1 = prove
   (`~(a = 0) ==> (a divides b <=> (b MOD a = 0))`,
    REWRITE_TAC[DIVIDES_MOD])
  and a_tm = `a:num` and b_tm = `b:num` and zero_tm = `0`
  and dest_divides = dest_binop `(divides)` in
  fun tm ->
     let a,b = dest_divides tm in
     if a = zero_tm then
       CONV_RULE (RAND_CONV NUM_EQ_CONV) (INST [b,b_tm] pth_0)
     else
       let th1 = INST [a,a_tm; b,b_tm] pth_1 in
       let th2 = MP th1 (EQF_ELIM(NUM_EQ_CONV(rand(lhand(concl th1))))) in
       CONV_RULE (RAND_CONV (LAND_CONV NUM_MOD_CONV THENC NUM_EQ_CONV)) th2;;

(* ------------------------------------------------------------------------- *)
(* A conversion for coprimality.                                             *)
(* ------------------------------------------------------------------------- *)

let COPRIME_CONV =
  let pth_yes_l = prove
   (`(m * x = n * y + 1) ==> (coprime(m,n) <=> T)`,
    MESON_TAC[coprime; DIVIDES_RMUL; DIVIDES_ADD_REVR; DIVIDES_ONE])
  and pth_yes_r = prove
   (`(m * x = n * y + 1) ==> (coprime(n,m) <=> T)`,
    MESON_TAC[coprime; DIVIDES_RMUL; DIVIDES_ADD_REVR; DIVIDES_ONE])
  and pth_no = prove
   (`(m = x * d) /\ (n = y * d) /\ ~(d = 1) ==> (coprime(m,n) <=> F)`,
    REWRITE_TAC[coprime; divides] THEN MESON_TAC[MULT_AC])
  and pth_oo = prove
   (`coprime(0,0) <=> F`,
    MESON_TAC[coprime; DIVIDES_REFL; NUM_REDUCE_CONV `1 = 0`])
  and m_tm = `m:num` and n_tm = `n:num`
  and x_tm = `x:num` and y_tm = `y:num`
  and d_tm = `d:num` and coprime_tm = `coprime` in
  let rec bezout (m,n) =
    if m =/ num 0 then (num 0,num 1) else if n =/ num 0 then (num 1,num 0)
    else if m <=/ n then
      let q = quo_num n m and r = mod_num n m in
      let (x,y) = bezout(m,r) in
      (x -/ q */ y,y)
    else let (x,y) = bezout(n,m) in (y,x) in
  fun tm ->
   let pop,ptm = dest_comb tm in
   if pop <> coprime_tm then failwith "COPRIME_CONV" else
   let l,r = dest_pair ptm in
   let m = dest_numeral l and n = dest_numeral r in
   if m =/ num 0 && n =/ num 0 then pth_oo else
   let (x,y) = bezout(m,n) in
   let d = x */ m +/ y */ n in
   let th =
     if d =/ num 1 then
       if x >/ num 0 then
          INST [l,m_tm; r,n_tm; mk_numeral x,x_tm;
                mk_numeral(minus_num y),y_tm] pth_yes_l
       else
          INST [r,m_tm; l,n_tm; mk_numeral(minus_num x),y_tm;
                mk_numeral y,x_tm] pth_yes_r
     else
         INST [l,m_tm; r,n_tm; mk_numeral d,d_tm;
              mk_numeral(m // d),x_tm; mk_numeral(n // d),y_tm] pth_no in
    MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))));;

(* ------------------------------------------------------------------------- *)
(* More general (slightly less efficiently coded) GCD_CONV, and LCM_CONV.    *)
(* ------------------------------------------------------------------------- *)

let GCD_CONV =
  let pth0 = prove(`gcd(0,0) = 0`,REWRITE_TAC[GCD_0]) in
  let pth1 = prove
   (`!m n x y d m' n'.
      (m * x = n * y + d) /\ (m = m' * d) /\ (n = n' * d) ==> (gcd(m,n) = d)`,
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
    ASM_MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL;
                  DIVIDES_ADD_REVR; DIVIDES_REFL]) in
  let pth2 = prove
   (`!m n x y d m' n'.
       (n * y = m * x + d) /\ (m = m' * d) /\ (n = n' * d) ==> (gcd(m,n) = d)`,
    MESON_TAC[pth1; GCD_SYM]) in
  let gcd_tm = `gcd` in
  let rec bezout (m,n) =
    if m =/ num 0 then (num 0,num 1) else if n =/ num 0 then (num 1,num 0)
    else if m <=/ n then
      let q = quo_num n m and r = mod_num n m in
      let (x,y) = bezout(m,r) in
      (x -/ q */ y,y)
    else let (x,y) = bezout(n,m) in (y,x) in
  fun tm -> let gt,lr = dest_comb tm in
            if gt <> gcd_tm then failwith "GCD_CONV" else
            let mtm,ntm = dest_pair lr in
            let m = dest_numeral mtm and n = dest_numeral ntm in
            if m =/ num 0 && n =/ num 0 then pth0 else
            let x0,y0 = bezout(m,n) in
            let x = abs_num x0 and y = abs_num y0 in
            let xtm = mk_numeral x and ytm = mk_numeral y in
            let d = abs_num(x */ m -/ y */ n) in
            let dtm = mk_numeral d in
            let m' = m // d and n' = n // d in
            let mtm' = mk_numeral m' and ntm' = mk_numeral n' in
            let th = SPECL [mtm;ntm;xtm;ytm;dtm;mtm';ntm']
             (if m */ x =/ n */ y +/ d then pth1 else pth2) in
            MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))));;

let LCM_CONV =
  GEN_REWRITE_CONV I [lcm] THENC
  RATOR_CONV(LAND_CONV(LAND_CONV NUM_MULT_CONV THENC NUM_EQ_CONV)) THENC
  (GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)] ORELSEC
   (GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] THENC
    COMB2_CONV (RAND_CONV NUM_MULT_CONV) GCD_CONV THENC NUM_DIV_CONV));;
