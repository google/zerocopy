(* ========================================================================= *)
(* Natural number arithmetic.                                                *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2015                         *)
(*      (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018             *)
(*                (c) Copyright, Mario Carneiro 2020                         *)
(* ========================================================================= *)

needs "recursion.ml";;

(* ------------------------------------------------------------------------- *)
(* Note: all the following proofs are intuitionistic and intensional, except *)
(* for the least number principle num_WOP.                                   *)
(* (And except the arith rewrites at the end; these could be done that way   *)
(* but they use the conditional anyway.) In fact, one could very easily      *)
(* write a "decider" returning P \/ ~P for quantifier-free P.                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<",(12,"right"));;
parse_as_infix("<=",(12,"right"));;
parse_as_infix(">",(12,"right"));;
parse_as_infix(">=",(12,"right"));;

parse_as_infix("+",(16,"right"));;
parse_as_infix("-",(18,"left"));;
parse_as_infix("*",(20,"right"));;
parse_as_infix("EXP",(24,"left"));;

parse_as_infix("DIV",(22,"left"));;
parse_as_infix("MOD",(22,"left"));;

(* ------------------------------------------------------------------------- *)
(* The predecessor function.                                                 *)
(* ------------------------------------------------------------------------- *)

let PRE = new_recursive_definition num_RECURSION
 `(PRE 0 = 0) /\
  (!n. PRE (SUC n) = n)`;;

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)

let ADD = new_recursive_definition num_RECURSION
 `(!n. 0 + n = n) /\
  (!m n. (SUC m) + n = SUC(m + n))`;;

let ADD_0 = prove
 (`!m. m + 0 = m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD]);;

let ADD_SUC = prove
 (`!m n. m + (SUC n) = SUC(m + n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD]);;

let ADD_CLAUSES = prove
 (`(!n. 0 + n = n) /\
   (!m. m + 0 = m) /\
   (!m n. (SUC m) + n = SUC(m + n)) /\
   (!m n. m + (SUC n) = SUC(m + n))`,
  REWRITE_TAC[ADD; ADD_0; ADD_SUC]);;

let ADD_SYM = prove
 (`!m n. m + n = n + m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]);;

let ADD_ASSOC = prove
 (`!m n p. m + (n + p) = (m + n) + p`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]);;

let ADD_AC = prove
 (`(m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))`,
  MESON_TAC[ADD_ASSOC; ADD_SYM]);;

let ADD_EQ_0 = prove
 (`!m n. (m + n = 0) <=> (m = 0) /\ (n = 0)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; NOT_SUC]);;

let EQ_ADD_LCANCEL = prove
 (`!m n p. (m + n = m + p) <=> (n = p)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUC_INJ]);;

let EQ_ADD_RCANCEL = prove
 (`!m n p. (m + p = n + p) <=> (m = n)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL);;

let EQ_ADD_LCANCEL_0 = prove
 (`!m n. (m + n = m) <=> (n = 0)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUC_INJ]);;

let EQ_ADD_RCANCEL_0 = prove
 (`!m n. (m + n = n) <=> (m = 0)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL_0);;

(* ------------------------------------------------------------------------- *)
(* Now define "bitwise" binary representation of numerals.                   *)
(* ------------------------------------------------------------------------- *)

let BIT0 = prove
 (`!n. BIT0 n = n + n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[BIT0_DEF; ADD_CLAUSES]);;

let BIT1 = prove
 (`!n. BIT1 n = SUC(n + n)`,
  REWRITE_TAC[BIT1_DEF; BIT0]);;

let BIT0_THM = prove
 (`!n. NUMERAL (BIT0 n) = NUMERAL n + NUMERAL n`,
  REWRITE_TAC[NUMERAL; BIT0]);;

let BIT1_THM = prove
 (`!n. NUMERAL (BIT1 n) = SUC(NUMERAL n + NUMERAL n)`,
  REWRITE_TAC[NUMERAL; BIT1]);;

(* ------------------------------------------------------------------------- *)
(* Following is handy before num_CONV arrives.                               *)
(* ------------------------------------------------------------------------- *)

let ONE = prove
 (`1 = SUC 0`,
  REWRITE_TAC[BIT1; REWRITE_RULE[NUMERAL] ADD_CLAUSES; NUMERAL]);;

let TWO = prove
 (`2 = SUC 1`,
  REWRITE_TAC[BIT0; BIT1; REWRITE_RULE[NUMERAL] ADD_CLAUSES; NUMERAL]);;

(* ------------------------------------------------------------------------- *)
(* One immediate consequence.                                                *)
(* ------------------------------------------------------------------------- *)

let ADD1 = prove
 (`!m. SUC m = m + 1`,
  REWRITE_TAC[BIT1_THM; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

let MULT = new_recursive_definition num_RECURSION
 `(!n. 0 * n = 0) /\
  (!m n. (SUC m) * n = (m * n) + n)`;;

let MULT_0 = prove
 (`!m. m * 0 = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT; ADD_CLAUSES]);;

let MULT_SUC = prove
 (`!m n. m * (SUC n) = m + (m * n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT; ADD_CLAUSES; ADD_ASSOC]);;

let MULT_CLAUSES = prove
 (`(!n. 0 * n = 0) /\
   (!m. m * 0 = 0) /\
   (!n. 1 * n = n) /\
   (!m. m * 1 = m) /\
   (!m n. (SUC m) * n = (m * n) + n) /\
   (!m n. m * (SUC n) = m + (m * n))`,
  REWRITE_TAC[BIT1_THM; MULT; MULT_0; MULT_SUC; ADD_CLAUSES]);;

let MULT_SYM = prove
 (`!m n. m * n = n * m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; EQT_INTRO(SPEC_ALL ADD_SYM)]);;

let LEFT_ADD_DISTRIB = prove
 (`!m n p. m * (n + p) = (m * n) + (m * p)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD; MULT_CLAUSES; ADD_ASSOC]);;

let RIGHT_ADD_DISTRIB = prove
 (`!m n p. (m + n) * p = (m * p) + (n * p)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_ACCEPT_TAC LEFT_ADD_DISTRIB);;

let MULT_ASSOC = prove
 (`!m n p. m * (n * p) = (m * n) * p`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; RIGHT_ADD_DISTRIB]);;

let MULT_AC = prove
 (`(m * n = n * m) /\
   ((m * n) * p = m * (n * p)) /\
   (m * (n * p) = n * (m * p))`,
  MESON_TAC[MULT_ASSOC; MULT_SYM]);;

let MULT_EQ_0 = prove
 (`!m n. (m * n = 0) <=> (m = 0) \/ (n = 0)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; NOT_SUC]);;

let EQ_MULT_LCANCEL = prove
 (`!m n p. (m * n = m * p) <=> (m = 0) \/ (n = p)`,
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; NOT_SUC] THEN
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; GSYM NOT_SUC; NOT_SUC] THEN
  ASM_REWRITE_TAC[SUC_INJ; GSYM ADD_ASSOC; EQ_ADD_LCANCEL]);;

let EQ_MULT_RCANCEL = prove
 (`!m n p. (m * p = n * p) <=> (m = n) \/ (p = 0)`,
  ONCE_REWRITE_TAC[MULT_SYM; DISJ_SYM] THEN MATCH_ACCEPT_TAC EQ_MULT_LCANCEL);;

let MULT_2 = prove
 (`!n. 2 * n = n + n`,
  GEN_TAC THEN REWRITE_TAC[BIT0_THM; MULT_CLAUSES; RIGHT_ADD_DISTRIB]);;

let MULT_EQ_1 = prove
 (`!m n. (m * n = 1) <=> (m = 1) /\ (n = 1)`,
  INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC
    [MULT_CLAUSES; ADD_CLAUSES; BIT0_THM; BIT1_THM; GSYM NOT_SUC] THEN
  REWRITE_TAC[SUC_INJ; ADD_EQ_0; MULT_EQ_0] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Exponentiation.                                                           *)
(* ------------------------------------------------------------------------- *)

let EXP = new_recursive_definition num_RECURSION
 `(!m. m EXP 0 = 1) /\
  (!m n. m EXP (SUC n) = m * (m EXP n))`;;

let EXP_EQ_0 = prove
 (`!m n. (m EXP n = 0) <=> (m = 0) /\ ~(n = 0)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
    [BIT1_THM; NOT_SUC; NOT_SUC; EXP; MULT_CLAUSES; ADD_CLAUSES; ADD_EQ_0]);;

let EXP_EQ_1 = prove
 (`!x n. x EXP n = 1 <=> x = 1 \/ n = 0`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; MULT_EQ_1; NOT_SUC] THEN
  CONV_TAC TAUT);;

let EXP_ZERO = prove
 (`!n. 0 EXP n = if n = 0 then 1 else 0`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[EXP_EQ_0; EXP_EQ_1]);;

let EXP_ADD = prove
 (`!m n p. m EXP (n + p) = (m EXP n) * (m EXP p)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EXP; ADD_CLAUSES; MULT_CLAUSES; MULT_AC]);;

let EXP_ONE = prove
 (`!n. 1 EXP n = 1`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES]);;

let EXP_1 = prove
 (`!n. n EXP 1 = n`,
  REWRITE_TAC[ONE; EXP; MULT_CLAUSES; ADD_CLAUSES]);;

let EXP_2 = prove
 (`!n. n EXP 2 = n * n`,
  REWRITE_TAC[BIT0_THM; BIT1_THM; EXP; EXP_ADD; MULT_CLAUSES; ADD_CLAUSES]);;

let MULT_EXP = prove
 (`!p m n. (m * n) EXP p = m EXP p * n EXP p`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES; MULT_AC]);;

let EXP_MULT = prove
 (`!m n p. m EXP (n * p) = (m EXP n) EXP p`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EXP_ADD; EXP; MULT_CLAUSES] THENL
   [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES];
    REWRITE_TAC[MULT_EXP] THEN MATCH_ACCEPT_TAC MULT_SYM]);;

let EXP_EXP = prove
 (`!x m n. (x EXP m) EXP n = x EXP (m * n)`,
  REWRITE_TAC[EXP_MULT]);;

(* ------------------------------------------------------------------------- *)
(* Define the orderings recursively too.                                     *)
(* ------------------------------------------------------------------------- *)

let LE = new_recursive_definition num_RECURSION
 `(!m. (m <= 0) <=> (m = 0)) /\
  (!m n. (m <= SUC n) <=> (m = SUC n) \/ (m <= n))`;;

let LT = new_recursive_definition num_RECURSION
 `(!m. (m < 0) <=> F) /\
  (!m n. (m < SUC n) <=> (m = n) \/ (m < n))`;;

let GE = new_definition
  `m >= n <=> n <= m`;;

let GT = new_definition
  `m > n <=> n < m`;;

(* ------------------------------------------------------------------------- *)
(* Maximum and minimum of natural numbers.                                   *)
(* ------------------------------------------------------------------------- *)

let MAX = new_definition
  `!m n. MAX m n = if m <= n then n else m`;;

let MIN = new_definition
  `!m n. MIN m n = if m <= n then m else n`;;

(* ------------------------------------------------------------------------- *)
(* Step cases.                                                               *)
(* ------------------------------------------------------------------------- *)

let LE_SUC_LT = prove
 (`!m n. (SUC m <= n) <=> (m < n)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LE; LT; NOT_SUC; SUC_INJ]);;

let LT_SUC_LE = prove
 (`!m n. (m < SUC n) <=> (m <= n)`,
  GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[LT; LE] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LT]);;

let LE_SUC = prove
 (`!m n. (SUC m <= SUC n) <=> (m <= n)`,
  REWRITE_TAC[LE_SUC_LT; LT_SUC_LE]);;

let LT_SUC = prove
 (`!m n. (SUC m < SUC n) <=> (m < n)`,
  REWRITE_TAC[LT_SUC_LE; LE_SUC_LT]);;

(* ------------------------------------------------------------------------- *)
(* Base cases.                                                               *)
(* ------------------------------------------------------------------------- *)

let LE_0 = prove
 (`!n. 0 <= n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LE]);;

let LT_0 = prove
 (`!n. 0 < SUC n`,
  REWRITE_TAC[LT_SUC_LE; LE_0]);;

(* ------------------------------------------------------------------------- *)
(* Reflexivity.                                                              *)
(* ------------------------------------------------------------------------- *)

let LE_REFL = prove
 (`!n. n <= n`,
  INDUCT_TAC THEN REWRITE_TAC[LE]);;

let LT_REFL = prove
 (`!n. ~(n < n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LT_SUC] THEN REWRITE_TAC[LT]);;

let LT_IMP_NE = prove
 (`!m n:num. m < n ==> ~(m = n)`,
  MESON_TAC[LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Antisymmetry.                                                             *)
(* ------------------------------------------------------------------------- *)

let LE_ANTISYM = prove
 (`!m n. (m <= n /\ n <= m) <=> (m = n)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC; SUC_INJ] THEN
  REWRITE_TAC[LE; NOT_SUC; GSYM NOT_SUC]);;

let LT_ANTISYM = prove
 (`!m n. ~(m < n /\ n < m)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LT_SUC] THEN REWRITE_TAC[LT]);;

let LET_ANTISYM = prove
 (`!m n. ~(m <= n /\ n < m)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC; LT_SUC] THEN
  REWRITE_TAC[LE; LT; NOT_SUC]);;

let LTE_ANTISYM = prove
 (`!m n. ~(m < n /\ n <= m)`,
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[LET_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Transitivity.                                                             *)
(* ------------------------------------------------------------------------- *)

let LE_TRANS = prove
 (`!m n p. m <= n /\ n <= p ==> m <= p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE_SUC; LE_0] THEN REWRITE_TAC[LE; NOT_SUC]);;

let LT_TRANS = prove
 (`!m n p. m < n /\ n < p ==> m < p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LT_SUC; LT_0] THEN REWRITE_TAC[LT; NOT_SUC]);;

let LET_TRANS = prove
 (`!m n p. m <= n /\ n < p ==> m < p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE_SUC; LT_SUC; LT_0] THEN REWRITE_TAC[LT; LE; NOT_SUC]);;

let LTE_TRANS = prove
 (`!m n p. m < n /\ n <= p ==> m < p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE_SUC; LT_SUC; LT_0] THEN REWRITE_TAC[LT; LE; NOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Totality.                                                                 *)
(* ------------------------------------------------------------------------- *)

let LE_CASES = prove
 (`!m n. m <= n \/ n <= m`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_0; LE_SUC]);;

let LT_CASES = prove
 (`!m n. (m < n) \/ (n < m) \/ (m = n)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LT_SUC; SUC_INJ] THEN
  REWRITE_TAC[LT; NOT_SUC; GSYM NOT_SUC] THEN
  W(W (curry SPEC_TAC) o hd o frees o snd) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_0]);;

let LET_CASES = prove
 (`!m n. m <= n \/ n < m`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC_LT; LT_SUC_LE; LE_0]);;

let LTE_CASES = prove
 (`!m n. m < n \/ n <= m`,
  ONCE_REWRITE_TAC[DISJ_SYM] THEN MATCH_ACCEPT_TAC LET_CASES);;

(* ------------------------------------------------------------------------- *)
(* Relationship between orderings.                                           *)
(* ------------------------------------------------------------------------- *)

let LE_LT = prove
 (`!m n. (m <= n) <=> (m < n) \/ (m = n)`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE_SUC; LT_SUC; SUC_INJ; LE_0; LT_0] THEN
  REWRITE_TAC[LE; LT]);;

let LT_LE = prove
 (`!m n. (m < n) <=> (m <= n) /\ ~(m = n)`,
  REWRITE_TAC[LE_LT] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[LT_REFL];
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[]]);;

let NOT_LE = prove
 (`!m n. ~(m <= n) <=> (n < m)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC; LT_SUC] THEN
  REWRITE_TAC[LE; LT; NOT_SUC; GSYM NOT_SUC; LE_0] THEN
  W(W (curry SPEC_TAC) o hd o frees o snd) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_0]);;

let NOT_LT = prove
 (`!m n. ~(m < n) <=> n <= m`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC; LT_SUC] THEN
  REWRITE_TAC[LE; LT; NOT_SUC; GSYM NOT_SUC; LE_0] THEN
  W(W (curry SPEC_TAC) o hd o frees o snd) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_0]);;

let LT_IMP_LE = prove
 (`!m n. m < n ==> m <= n`,
  REWRITE_TAC[LT_LE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let EQ_IMP_LE = prove
 (`!m n. (m = n) ==> m <= n`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Often useful to shuffle between different versions of "0 < n".            *)
(* ------------------------------------------------------------------------- *)

let LT_NZ = prove
 (`!n. 0 < n <=> ~(n = 0)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC; LT; EQ_SYM_EQ] THEN
  CONV_TAC TAUT);;

let LE_1 = prove
 (`(!n. ~(n = 0) ==> 0 < n) /\
   (!n. ~(n = 0) ==> 1 <= n) /\
   (!n. 0 < n ==> ~(n = 0)) /\
   (!n. 0 < n ==> 1 <= n) /\
   (!n. 1 <= n ==> 0 < n) /\
   (!n. 1 <= n ==> ~(n = 0))`,
  REWRITE_TAC[LT_NZ; GSYM NOT_LT; ONE; LT]);;

(* ------------------------------------------------------------------------- *)
(* Relate the orderings to arithmetic operations.                            *)
(* ------------------------------------------------------------------------- *)

let LE_EXISTS = prove
 (`!m n. (m <= n) <=> (?d. n = m + d)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LE] THENL
   [REWRITE_TAC[CONV_RULE(LAND_CONV SYM_CONV) (SPEC_ALL ADD_EQ_0)] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL];
    EQ_TAC THENL
     [DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES];
        DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
        EXISTS_TAC `SUC d` THEN REWRITE_TAC[ADD_CLAUSES]];
      ONCE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUC_INJ] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN DISJ2_TAC THEN
      REWRITE_TAC[EQ_ADD_LCANCEL; GSYM EXISTS_REFL]]]);;

let LT_EXISTS = prove
 (`!m n. (m < n) <=> (?d. n = m + SUC d)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT; ADD_CLAUSES; GSYM NOT_SUC] THEN
  ASM_REWRITE_TAC[SUC_INJ] THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
     [EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES];
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
      EXISTS_TAC `SUC d` THEN REWRITE_TAC[ADD_CLAUSES]];
    ONCE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUC_INJ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN DISJ2_TAC THEN
    REWRITE_TAC[SUC_INJ; EQ_ADD_LCANCEL; GSYM EXISTS_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Interaction with addition.                                                *)
(* ------------------------------------------------------------------------- *)

let LE_ADD = prove
 (`!m n. m <= m + n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE; ADD_CLAUSES; LE_REFL]);;

let LE_ADDR = prove
 (`!m n. n <= m + n`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LE_ADD);;

let LT_ADD = prove
 (`!m n. (m < m + n) <=> (0 < n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_SUC]);;

let LT_ADDR = prove
 (`!m n. (n < m + n) <=> (0 < m)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LT_ADD);;

let LE_ADD_LCANCEL = prove
 (`!m n p. (m + n) <= (m + p) <=> n <= p`,
  REWRITE_TAC[LE_EXISTS; GSYM ADD_ASSOC; EQ_ADD_LCANCEL]);;

let LE_ADD_RCANCEL = prove
 (`!m n p. (m + p) <= (n + p) <=> (m <= n)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LE_ADD_LCANCEL);;

let LT_ADD_LCANCEL = prove
 (`!m n p. (m + n) < (m + p) <=> n < p`,
  REWRITE_TAC[LT_EXISTS; GSYM ADD_ASSOC; EQ_ADD_LCANCEL; SUC_INJ]);;

let LT_ADD_RCANCEL = prove
 (`!m n p. (m + p) < (n + p) <=> (m < n)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LT_ADD_LCANCEL);;

let LE_ADD2 = prove
 (`!m n p q. m <= p /\ n <= q ==> m + n <= p + q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `a:num`) (X_CHOOSE_TAC `b:num`)) THEN
  EXISTS_TAC `a + b` THEN ASM_REWRITE_TAC[ADD_AC]);;

let LET_ADD2 = prove
 (`!m n p q. m <= p /\ n < q ==> m + n < p + q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS; LT_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `a:num`) (X_CHOOSE_TAC `b:num`)) THEN
  EXISTS_TAC `a + b` THEN ASM_REWRITE_TAC[SUC_INJ; ADD_CLAUSES; ADD_AC]);;

let LTE_ADD2 = prove
 (`!m n p q. m < p /\ n <= q ==> m + n < p + q`,
  ONCE_REWRITE_TAC[ADD_SYM; CONJ_SYM] THEN
  MATCH_ACCEPT_TAC LET_ADD2);;

let LT_ADD2 = prove
 (`!m n p q. m < p /\ n < q ==> m + n < p + q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_ADD2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* And multiplication.                                                       *)
(* ------------------------------------------------------------------------- *)

let LT_MULT = prove
 (`!m n. (0 < m * n) <=> (0 < m) /\ (0 < n)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT_0]);;

let LE_MULT2 = prove
 (`!m n p q. m <= n /\ p <= q ==> m * p <= n * q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `a:num`) (X_CHOOSE_TAC `b:num`)) THEN
  EXISTS_TAC `a * p + m * b + a * b` THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; ADD_ASSOC]);;

let LT_LMULT = prove
 (`!m n p. ~(m = 0) /\ n < p ==> m * n < m * p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LT_LE] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL];
    ASM_REWRITE_TAC[EQ_MULT_LCANCEL]]);;

let LE_MULT_LCANCEL = prove
 (`!m n p. (m * n) <= (m * p) <=> (m = 0) \/ n <= p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_REFL; LE_0; NOT_SUC] THEN
  REWRITE_TAC[LE_SUC] THEN
  REWRITE_TAC[LE; LE_ADD_LCANCEL; GSYM ADD_ASSOC] THEN
  ASM_REWRITE_TAC[GSYM(el 4(CONJUNCTS MULT_CLAUSES)); NOT_SUC]);;

let LE_MULT_RCANCEL = prove
 (`!m n p. (m * p) <= (n * p) <=> (m <= n) \/ (p = 0)`,
  ONCE_REWRITE_TAC[MULT_SYM; DISJ_SYM] THEN
  MATCH_ACCEPT_TAC LE_MULT_LCANCEL);;

let LT_MULT_LCANCEL = prove
 (`!m n p. (m * n) < (m * p) <=> ~(m = 0) /\ n < p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT_REFL; LT_0; NOT_SUC] THEN
  REWRITE_TAC[LT_SUC] THEN
  REWRITE_TAC[LT; LT_ADD_LCANCEL; GSYM ADD_ASSOC] THEN
  ASM_REWRITE_TAC[GSYM(el 4(CONJUNCTS MULT_CLAUSES)); NOT_SUC]);;

let LT_MULT_RCANCEL = prove
 (`!m n p. (m * p) < (n * p) <=> (m < n) /\ ~(p = 0)`,
  ONCE_REWRITE_TAC[MULT_SYM; CONJ_SYM] THEN
  MATCH_ACCEPT_TAC LT_MULT_LCANCEL);;

let LT_MULT2 = prove
 (`!m n p q. m < n /\ p < q ==> m * p < n * q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `n * p` THEN
  ASM_SIMP_TAC[LE_MULT_RCANCEL; LT_IMP_LE; LT_MULT_LCANCEL] THEN
  UNDISCH_TAC `m < n` THEN CONV_TAC CONTRAPOS_CONV THEN SIMP_TAC[LT]);;

let LE_SQUARE_REFL = prove
 (`!n. n <= n * n`,
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; LE_0; LE_ADDR]);;

let LT_POW2_REFL = prove
 (`!n. n < 2 EXP n`,
  INDUCT_TAC THEN REWRITE_TAC[EXP] THEN REWRITE_TAC[MULT_2; ADD1] THEN
  REWRITE_TAC[ONE; LT] THEN MATCH_MP_TAC LTE_ADD2 THEN
  ASM_REWRITE_TAC[LE_SUC_LT; TWO] THEN
  MESON_TAC[EXP_EQ_0; LE_1; NOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Useful "without loss of generality" lemmas.                               *)
(* ------------------------------------------------------------------------- *)

let WLOG_LE = prove
 (`(!m n. P m n <=> P n m) /\ (!m n. m <= n ==> P m n) ==> !m n. P m n`,
  MESON_TAC[LE_CASES]);;

let WLOG_LT = prove
 (`(!m. P m m) /\ (!m n. P m n <=> P n m) /\ (!m n. m < n ==> P m n)
   ==> !m y. P m y`,
  MESON_TAC[LT_CASES]);;

let WLOG_LE_3 = prove
 (`!P. (!x y z. P x y z ==> P y x z /\ P x z y) /\
       (!x y z. x <= y /\ y <= z ==> P x y z)
       ==> !x y z. P x y z`,
  MESON_TAC[LE_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Existence of least and greatest elements of (finite) set.                 *)
(* ------------------------------------------------------------------------- *)

let num_WF = prove
 (`!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n`,
  GEN_TAC THEN MP_TAC(SPEC `\n. !m. m < n ==> P m` num_INDUCTION) THEN
  REWRITE_TAC[LT; BETA_THM] THEN MESON_TAC[LT]);;

let num_WOP = prove
 (`!P. (?n. P n) <=> (?n. P(n) /\ !m. m < n ==> ~P(m))`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_WF THEN ASM_MESON_TAC[]);;

let num_MAX = prove
 (`!P. (?x. P x) /\ (?M. !x. P x ==> x <= M) <=>
       ?m. P m /\ (!x. P x ==> x <= m)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:num`) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC o ONCE_REWRITE_RULE[num_WOP]) THEN
    DISCH_THEN(fun th -> EXISTS_TAC `m:num` THEN MP_TAC th) THEN
    REWRITE_TAC[TAUT `(a /\ b ==> c /\ a) <=> (a /\ b ==> c)`] THEN
    SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THENL
     [REWRITE_TAC[LE; LT] THEN DISCH_THEN(IMP_RES_THEN SUBST_ALL_TAC) THEN
      POP_ASSUM ACCEPT_TAC;
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `m:num`)) THEN
      REWRITE_TAC[LT] THEN CONV_TAC CONTRAPOS_CONV THEN
      DISCH_TAC THEN REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN
      FIRST_ASSUM(MP_TAC o SPEC `p:num`) THEN REWRITE_TAC[LE] THEN
      ASM_CASES_TAC `p = SUC m` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Other variants of induction.                                              *)
(* ------------------------------------------------------------------------- *)

let LE_INDUCT = prove
 (`!P. (!m:num. P m m) /\
       (!m n. m <= n /\ P m n ==> P m (SUC n))
       ==> (!m n. m <= n ==> P m n)`,
   GEN_TAC THEN REWRITE_TAC[IMP_CONJ; MESON[LE_EXISTS]
    `(!m n:num. m <= n ==> R m n) <=> (!m d. R m (m + d))`] THEN
  REPEAT DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ADD_CLAUSES]);;

let num_INDUCTION_DOWN = prove
 (`!(P:num->bool) m.
        (!n. m <= n ==> P n) /\
        (!n. n < m /\ P(n + 1) ==> P n)
        ==> !n. P n`,
  REWRITE_TAC[GSYM ADD1] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!x. P x) <=> ~(?x. ~P x)`] THEN
  W(MP_TAC o PART_MATCH (lhand o lhand) num_MAX o rand o snd) THEN
  MATCH_MP_TAC(TAUT `q /\ ~r ==> (p /\ q <=> r) ==> ~p`) THEN
  ONCE_REWRITE_TAC[TAUT `~p ==> q <=> ~q ==> p`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(~p /\ q) <=> q ==> p`; NOT_LE] THEN
  ASM_MESON_TAC[LTE_CASES; LT; LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Oddness and evenness (recursively rather than inductively!)               *)
(* ------------------------------------------------------------------------- *)

let EVEN = new_recursive_definition num_RECURSION
  `(EVEN 0 <=> T) /\
   (!n. EVEN (SUC n) <=> ~(EVEN n))`;;

let ODD = new_recursive_definition num_RECURSION
  `(ODD 0 <=> F) /\
   (!n. ODD (SUC n) <=> ~(ODD n))`;;

let NOT_EVEN = prove
 (`!n. ~(EVEN n) <=> ODD n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EVEN; ODD]);;

let NOT_ODD = prove
 (`!n. ~(ODD n) <=> EVEN n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EVEN; ODD]);;

let EVEN_OR_ODD = prove
 (`!n. EVEN n \/ ODD n`,
  INDUCT_TAC THEN REWRITE_TAC[EVEN; ODD; NOT_EVEN; NOT_ODD] THEN
  ONCE_REWRITE_TAC[DISJ_SYM] THEN ASM_REWRITE_TAC[]);;

let EVEN_AND_ODD = prove
 (`!n. ~(EVEN n /\ ODD n)`,
  REWRITE_TAC[GSYM NOT_EVEN; ITAUT `~(p /\ ~p)`]);;

let EVEN_ADD = prove
 (`!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EVEN; ADD_CLAUSES] THEN
  X_GEN_TAC `p:num` THEN
  DISJ_CASES_THEN MP_TAC (SPEC `n:num` EVEN_OR_ODD) THEN
  DISJ_CASES_THEN MP_TAC (SPEC `p:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

let EVEN_MULT = prove
 (`!m n. EVEN(m * n) <=> EVEN(m) \/ EVEN(n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; EVEN_ADD; EVEN] THEN
  X_GEN_TAC `p:num` THEN
  DISJ_CASES_THEN MP_TAC (SPEC `n:num` EVEN_OR_ODD) THEN
  DISJ_CASES_THEN MP_TAC (SPEC `p:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

let EVEN_EXP = prove
 (`!m n. EVEN(m EXP n) <=> EVEN(m) /\ ~(n = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EVEN; EXP; ONE; EVEN_MULT; NOT_SUC] THEN
  CONV_TAC ITAUT);;

let ODD_ADD = prove
 (`!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_EVEN; EVEN_ADD] THEN
  CONV_TAC ITAUT);;

let ODD_MULT = prove
 (`!m n. ODD(m * n) <=> ODD(m) /\ ODD(n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_EVEN; EVEN_MULT] THEN
  CONV_TAC ITAUT);;

let ODD_EXP = prove
 (`!m n. ODD(m EXP n) <=> ODD(m) \/ (n = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ODD; EXP; ONE; ODD_MULT; NOT_SUC] THEN
  CONV_TAC ITAUT);;

let EVEN_DOUBLE = prove
 (`!n. EVEN(2 * n)`,
  GEN_TAC THEN REWRITE_TAC[EVEN_MULT] THEN DISJ1_TAC THEN
  PURE_REWRITE_TAC[BIT0_THM; BIT1_THM] THEN REWRITE_TAC[EVEN; EVEN_ADD]);;

let ODD_DOUBLE = prove
 (`!n. ODD(SUC(2 * n))`,
  REWRITE_TAC[ODD] THEN REWRITE_TAC[NOT_ODD; EVEN_DOUBLE]);;

let EVEN_EXISTS_LEMMA = prove
 (`!n. (EVEN n ==> ?m. n = 2 * m) /\
       (~EVEN n ==> ?m. n = SUC(2 * m))`,
  INDUCT_TAC THEN REWRITE_TAC[EVEN] THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES];
    POP_ASSUM STRIP_ASSUME_TAC THEN CONJ_TAC THEN
    DISCH_THEN(ANTE_RES_THEN(X_CHOOSE_TAC `m:num`)) THENL
     [EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_2] THEN REWRITE_TAC[ADD_CLAUSES];
      EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]]]);;

let EVEN_EXISTS = prove
 (`!n. EVEN n <=> ?m. n = 2 * m`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL EVEN_EXISTS_LEMMA)) THEN ASM_REWRITE_TAC[];
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[EVEN_DOUBLE]]);;

let ODD_EXISTS = prove
 (`!n. ODD n <=> ?m. n = SUC(2 * m)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2(SPEC_ALL EVEN_EXISTS_LEMMA)) THEN
    ASM_REWRITE_TAC[NOT_EVEN];
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[ODD_DOUBLE]]);;

let EVEN_ODD_DECOMPOSITION = prove
 (`!n. (?k m. ODD m /\ (n = 2 EXP k * m)) <=> ~(n = 0)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THENL
   [ALL_TAC; ASM_MESON_TAC[ODD; EXP; MULT_CLAUSES]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_EQ_0] THENL
   [REWRITE_TAC[MULT_CLAUSES; LT] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[EXP_EQ_0; MULT_EQ_0; TWO; NOT_SUC] THEN MESON_TAC[ODD];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(el 2 (CONJUNCTS MULT_CLAUSES))] THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL; TWO; LT];
    ALL_TAC] THEN
  REWRITE_TAC[TWO; NOT_SUC] THEN REWRITE_TAC[GSYM TWO] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[EXP; MULT_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Cutoff subtraction, also defined recursively. (Not the HOL88 defn.)       *)
(* ------------------------------------------------------------------------- *)

let SUB = new_recursive_definition num_RECURSION
 `(!m. m - 0 = m) /\
  (!m n. m - (SUC n) = PRE(m - n))`;;

let SUB_0 = prove
 (`!m. (0 - m = 0) /\ (m - 0 = m)`,
  REWRITE_TAC[SUB] THEN INDUCT_TAC THEN ASM_REWRITE_TAC[SUB; PRE]);;

let SUB_PRESUC = prove
 (`!m n. PRE(SUC m - n) = m - n`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[SUB; PRE]);;

let SUB_SUC = prove
 (`!m n. SUC m - SUC n = m - n`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[SUB; PRE; SUB_PRESUC]);;

let SUB_REFL = prove
 (`!n. n - n = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_SUC; SUB_0]);;

let ADD_SUB = prove
 (`!m n. (m + n) - n = m`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUB_SUC; SUB_0]);;

let ADD_SUB2 = prove
 (`!m n. (m + n) - m = n`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUB);;

let SUB_EQ_0 = prove
 (`!m n. (m - n = 0) <=> m <= n`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_SUC; LE_SUC; SUB_0] THEN
  REWRITE_TAC[LE; LE_0]);;

let ADD_SUBR2 = prove
 (`!m n. m - (m + n) = 0`,
  REWRITE_TAC[SUB_EQ_0; LE_ADD]);;

let ADD_SUBR = prove
 (`!m n. n - (m + n) = 0`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUBR2);;

let SUB_ADD = prove
 (`!m n. n <= m ==> ((m - n) + n = m)`,
  REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
  MATCH_ACCEPT_TAC ADD_SYM);;

let SUB_ADD_LCANCEL = prove
 (`!m n p. (m + n) - (m + p) = n - p`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0; SUB_SUC]);;

let SUB_ADD_RCANCEL = prove
 (`!m n p. (m + p) - (n + p) = m - n`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC SUB_ADD_LCANCEL);;

let LEFT_SUB_DISTRIB = prove
 (`!m n p. m * (n - p) = m * n - m * p`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  DISJ_CASES_TAC(SPECL [`n:num`; `p:num`] LE_CASES) THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[GSYM SUB_EQ_0] th]) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; SUB_EQ_0; LE_MULT_LCANCEL];
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB]]);;

let RIGHT_SUB_DISTRIB = prove
 (`!m n p. (m - n) * p = m * p - n * p`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_ACCEPT_TAC LEFT_SUB_DISTRIB);;

let SUC_SUB1 = prove
 (`!n. SUC n - 1 = n`,
  REWRITE_TAC[ONE; SUB_SUC; SUB_0]);;

let EVEN_SUB = prove
 (`!m n. EVEN(m - n) <=> m <= n \/ (EVEN(m) <=> EVEN(n))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m <= n:num` THENL
   [ASM_MESON_TAC[SUB_EQ_0; EVEN]; ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [`m:num`; `n:num`] LE_CASES) THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `EVEN` o MATCH_MP SUB_ADD) THEN
  ASM_MESON_TAC[EVEN_ADD]);;

let ODD_SUB = prove
 (`!m n. ODD(m - n) <=> n < m /\ ~(ODD m <=> ODD n)`,
  REWRITE_TAC[GSYM NOT_EVEN; EVEN_SUB; DE_MORGAN_THM; NOT_LE] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* The factorial function.                                                   *)
(* ------------------------------------------------------------------------- *)

let FACT = new_recursive_definition num_RECURSION
  `(FACT 0 = 1) /\
   (!n. FACT (SUC n) = (SUC n) * FACT(n))`;;

let FACT_LT = prove
 (`!n. 0 < FACT n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[FACT; LT_MULT] THEN
  REWRITE_TAC[ONE; LT_0]);;

let FACT_LE = prove
 (`!n. 1 <= FACT n`,
  REWRITE_TAC[ONE; LE_SUC_LT; FACT_LT]);;

let FACT_NZ = prove
 (`!n. ~(FACT n = 0)`,
  REWRITE_TAC[GSYM LT_NZ; FACT_LT]);;

let FACT_MONO = prove
 (`!m n. m <= n ==> FACT m <= FACT n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
  REWRITE_TAC[FACT] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `FACT(m + d)` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(el 2 (CONJUNCTS MULT_CLAUSES))] THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN
  REWRITE_TAC[ONE; LE_SUC; LE_0]);;

(* ------------------------------------------------------------------------- *)
(* More complicated theorems about exponential.                              *)
(* ------------------------------------------------------------------------- *)

let EXP_LT_0 = prove
 (`!n x. 0 < x EXP n <=> ~(x = 0) \/ (n = 0)`,
  REWRITE_TAC[GSYM NOT_LE; LE; EXP_EQ_0; DE_MORGAN_THM]);;

let LT_EXP = prove
 (`!x m n. x EXP m < x EXP n <=> 2 <= x /\ m < n \/
                                 (x = 0) /\ ~(m = 0) /\ (n = 0)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[GSYM NOT_LT; TWO; ONE; LT] THEN
    SPEC_TAC (`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[EXP; NOT_SUC; MULT_CLAUSES; LT] THEN
    SPEC_TAC (`m:num`,`m:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[EXP; MULT_CLAUSES; NOT_SUC; LT_REFL; LT] THEN
    REWRITE_TAC[ONE; LT_0]; ALL_TAC] THEN
  EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[NOT_LT; DE_MORGAN_THM; NOT_LE] THEN
    REWRITE_TAC[TWO; ONE; LT] THEN
    ASM_REWRITE_TAC[SYM ONE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[EXP_ONE; LE_REFL] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
      REWRITE_RULE[LE_EXISTS]) THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; EXP; LE_REFL] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 * x EXP (n + d)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES];
      REWRITE_TAC[LE_MULT_RCANCEL] THEN
      DISJ1_TAC THEN UNDISCH_TAC `~(x = 0)` THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LE] THEN
      REWRITE_TAC[ONE; LT]];
    STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
      REWRITE_RULE[LT_EXISTS]) THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; EXP] THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 * x EXP m` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[MULT_2; LT_ADD; EXP_LT_0];
        ASM_REWRITE_TAC[LE_MULT_RCANCEL]];
      MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `x EXP (m + SUC d)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_CLAUSES; EXP; MULT_ASSOC; LE_MULT_RCANCEL] THEN
      DISJ1_TAC THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `x * 1` THEN CONJ_TAC THENL
       [REWRITE_TAC[MULT_CLAUSES; LE_REFL];
        REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
        UNDISCH_TAC `~(x = 0)` THEN
        CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LE] THEN
        REWRITE_TAC[ONE; LT]]]]);;

let LE_EXP = prove
 (`!x m n. x EXP m <= x EXP n <=>
           if x = 0 then (m = 0) ==> (n = 0)
           else (x = 1) \/ m <= n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LT; LT_EXP; DE_MORGAN_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TWO; LT; ONE] THEN
  CONV_TAC(EQT_INTRO o TAUT));;

let EQ_EXP = prove
 (`!x m n. x EXP m = x EXP n <=>
           if x = 0 then (m = 0 <=> n = 0)
           else (x = 1) \/ m = n`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LE_ANTISYM; LE_EXP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_EXP] THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONV_TAC TAUT);;

let EXP_MONO_LE_IMP = prove
 (`!x y n. x <= y ==> x EXP n <= y EXP n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[LE_MULT2; EXP; LE_REFL]);;

let EXP_MONO_LT_IMP = prove
 (`!x y n. x < y /\ ~(n = 0) ==> x EXP n < y EXP n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; EXP] THEN
  DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `x * y EXP n` THEN
  ASM_SIMP_TAC[LT_IMP_LE; LE_MULT_LCANCEL; LT_MULT_RCANCEL; EXP_MONO_LE_IMP;
               EXP_EQ_0] THEN
  ASM_MESON_TAC[CONJUNCT1 LT]);;

let EXP_MONO_LE = prove
 (`!x y n. x EXP n <= y EXP n <=> x <= y \/ n = 0`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EXP; LE_REFL; EXP_MONO_LE_IMP] THEN
  ASM_MESON_TAC[NOT_LE; EXP_MONO_LT_IMP]);;

let EXP_MONO_LT = prove
 (`!x y n. x EXP n < y EXP n <=> x < y /\ ~(n = 0)`,
  REWRITE_TAC[GSYM NOT_LE; EXP_MONO_LE; DE_MORGAN_THM]);;

let EXP_MONO_EQ = prove
 (`!x y n. x EXP n = y EXP n <=> x = y \/ n = 0`,
  REWRITE_TAC[GSYM LE_ANTISYM; EXP_MONO_LE] THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Division and modulus, via existence proof of their basic property.        *)
(* ------------------------------------------------------------------------- *)

let DIVMOD_EXIST = prove
 (`!m n. ~(n = 0) ==> ?q r. (m = q * n + r) /\ r < n`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `\r. ?q. m = q * n + r` num_WOP) THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `0`]) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:num`) MP_TAC) THEN
  DISCH_THEN(fun th ->
    MAP_EVERY EXISTS_TAC [`q:num`; `r:num`] THEN MP_TAC th) THEN
  CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[NOT_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `d:num` THEN
  REWRITE_TAC[NOT_IMP; RIGHT_AND_EXISTS_THM] THEN
  EXISTS_TAC `q + 1` THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_ASSOC; LT_ADDR] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; LE]);;

let DIVMOD_EXIST_0 = prove
 (`!m n. ?q r. if n = 0 then q = 0 /\ r = m
               else m = q * n + r /\ r < n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[DIVMOD_EXIST; RIGHT_EXISTS_AND_THM; EXISTS_REFL]);;

let DIVISION_0 =  new_specification ["DIV"; "MOD"]
  (REWRITE_RULE[SKOLEM_THM] DIVMOD_EXIST_0);;

let DIVISION = prove
 (`!m n. ~(n = 0) ==> (m = m DIV n * n + m MOD n) /\ m MOD n < n`,
  MESON_TAC[DIVISION_0]);;

let DIV_ZERO = prove
 (`!n. n DIV 0 = 0`,
  MESON_TAC[DIVISION_0]);;

let MOD_ZERO = prove
 (`!n. n MOD 0 = n`,
  MESON_TAC[DIVISION_0]);;

let DIVISION_SIMP = prove
 (`(!m n. m DIV n * n + m MOD n = m) /\
   (!m n. n * m DIV n + m MOD n = m)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[DIV_ZERO; MOD_ZERO; MULT_CLAUSES; ADD_CLAUSES] THEN
  ASM_MESON_TAC[DIVISION; MULT_SYM]);;

let EQ_DIVMOD = prove
 (`!p m n. m DIV p = n DIV p /\ m MOD p = n MOD p <=> m = n`,
  MESON_TAC[DIVISION_SIMP]);;

let MOD_LT_EQ = prove
 (`!m n. m MOD n < n <=> ~(n = 0)`,
  MESON_TAC[DIVISION; LE_1; CONJUNCT1 LT]);;

let MOD_LT_EQ_LT = prove
 (`!m n. m MOD n < n <=> 0 < n`,
  MESON_TAC[DIVISION; LE_1; CONJUNCT1 LT]);;

let DIVMOD_UNIQ_LEMMA = prove
 (`!m n q1 r1 q2 r2. ((m = q1 * n + r1) /\ r1 < n) /\
                     ((m = q2 * n + r2) /\ r2 < n)
                     ==> (q1 = q2) /\ (r1 = r2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `r1:num = r2` MP_TAC THENL
   [UNDISCH_TAC `m = q2 * n + r2` THEN
    ASM_REWRITE_TAC[] THEN
    DISJ_CASES_THEN MP_TAC (SPECL [`q1:num`; `q2:num`] LE_CASES) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THENL
     [DISCH_TAC THEN UNDISCH_TAC `r1 < n`;
      DISCH_THEN(ASSUME_TAC o SYM) THEN UNDISCH_TAC `r2 < n`] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES;
      GSYM NOT_LE; LE_ADD; GSYM ADD_ASSOC];
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `m = q1 * n + r2` THEN
    ASM_REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_RCANCEL] THEN
    REPEAT (UNDISCH_TAC `r2 < n`) THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[GSYM NOT_LE; LE_0]]);;

let DIVMOD_UNIQ = prove
 (`!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q) /\ (m MOD n = r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC o GSYM) THEN
  MATCH_MP_TAC DIVMOD_UNIQ_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `n:num`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIVISION THEN
  DISCH_TAC THEN UNDISCH_TAC `r < n` THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; LE_0]);;

let MOD_UNIQ = prove
 (`!m n q r. (m = q * n + r) /\ r < n ==> (m MOD n = r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP DIVMOD_UNIQ th]));;

let DIV_UNIQ = prove
 (`!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP DIVMOD_UNIQ th]));;

let DIV_0,MOD_0 = (CONJ_PAIR o prove)
 (`(!n. 0 DIV n = 0) /\ (!n. 0 MOD n = 0)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIV_ZERO; MOD_ZERO] THEN
  MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT_NZ]);;

let DIV_MULT,MOD_MULT = (CONJ_PAIR o prove)
 (`(!m n. ~(m = 0) ==> (m * n) DIV m = n) /\
   (!m n. (m * n) MOD m = 0)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; MOD_0] THEN
  MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; MULT_AC; LT_NZ]);;

let MOD_LT = prove
 (`!m n. m < n ==> m MOD n = m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let MOD_EQ_SELF = prove
 (`!m n. m MOD n = m <=> n = 0 \/ m < n`,
  MESON_TAC[MOD_ZERO; MOD_LT; DIVISION; LE_1]);;

let MOD_CASES = prove
 (`!n p. n < 2 * p ==> n MOD p = if n < p then n else n - p`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES] THEN ASM_MESON_TAC[SUB_ADD; ADD_SYM];
    ASM_MESON_TAC[LT_ADD_RCANCEL; SUB_ADD; MULT_2; LT_ADD2]]);;

let MOD_ADD_CASES = prove
 (`!m n p.
        m < p /\ n < p
        ==> (m + n) MOD p = if m + n < p then m + n else (m + n) - p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_CASES THEN
  REWRITE_TAC[MULT_2] THEN ASM_MESON_TAC[LT_ADD2]);;

let MOD_EQ = prove
 (`!m n p q. m = n + q * p ==> m MOD p = n MOD p`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOD_UNIQ THEN
    EXISTS_TAC `q + n DIV p` THEN
    POP_ASSUM(MP_TAC o MATCH_MP DIVISION) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
    MATCH_ACCEPT_TAC ADD_SYM]);;

let DIV_LE = prove
 (`!m n. m DIV n <= m`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[DIV_ZERO; LE_0] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [MATCH_MP DIVISION th]) THEN
  UNDISCH_TAC `~(n = 0)` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; GSYM ADD_ASSOC; LE_ADD]);;

let DIV_MUL_LE = prove
 (`!m n. n * (m DIV n) <= m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
  POP_ASSUM(MP_TAC o SPEC `m:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 th]) THEN
  REWRITE_TAC[LE_ADD; MULT_AC]);;

let MOD_LE_TWICE = prove
 (`!m n. 0 < m /\ m <= n ==> 2 * n MOD m <= n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `2 * m <= n` THENL
   [TRANS_TAC LE_TRANS `2 * m` THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL; DIVISION; LT_IMP_LE; LE_1];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN
  TRANS_TAC LE_TRANS `m + n MOD m` THEN
  ASM_SIMP_TAC[MULT_2; LE_ADD_RCANCEL; DIVISION; LT_IMP_LE; LE_1] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  SUBGOAL_THEN `n MOD m = n - m`
   (fun th -> ASM_SIMP_TAC[LE_REFL; SUB_ADD; th]) THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_SIMP_TAC[MULT_CLAUSES; SUB_ADD] THEN
  ONCE_REWRITE_TAC[MESON[LT_ADD_RCANCEL]
   `n - m:num < m <=> (n - m) + m < m + m`] THEN
  ASM_SIMP_TAC[GSYM MULT_2; SUB_ADD]);;

let DIV_1,MOD_1 = (CONJ_PAIR o prove)
 (`(!n. n DIV 1 = n) /\ (!n. n MOD 1 = 0)`,
  SIMP_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN REWRITE_TAC[ONE; LT]);;

let DIV_LT = prove
 (`!m n. m < n ==> m DIV n = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let MOD_MOD = prove
 (`!m n p. (m MOD (n * p)) MOD n = m MOD n`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[MOD_ZERO; MULT_CLAUSES] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MOD_ZERO; MULT_CLAUSES] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
  EXISTS_TAC `m DIV (n * p) * p` THEN
  MP_TAC(SPECL [`m:num`; `n * p:num`] DIVISION) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; MULT_AC; ADD_AC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

let MOD_MOD_REFL = prove
 (`!m n. (m MOD n) MOD n = m MOD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MOD_ZERO] THEN
  MP_TAC(SPECL [`m:num`; `n:num`; `1`] MOD_MOD) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; MULT_EQ_0] THEN
  REWRITE_TAC[ONE; NOT_SUC]);;

let MOD_MOD_LE = prove
 (`!m n p. ~(n = 0) /\ n <= p ==> (m MOD n) MOD p = m MOD n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN
  ASM_MESON_TAC[DIVISION; LTE_TRANS]);;

let MOD_EVEN_2 = prove
 (`!m n. EVEN n ==> m MOD n MOD 2 = m MOD 2`,
  SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; MOD_MOD]);;

let DIV_MULT2 = prove
 (`!m n p. ~(m = 0) ==> ((m * n) DIV (m * p) = n DIV p)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[DIV_ZERO; MULT_CLAUSES] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `m * (n MOD p)` THEN
  ASM_SIMP_TAC[LT_MULT_LCANCEL; DIVISION] THEN
  ONCE_REWRITE_TAC[AC MULT_AC `a * b * c:num = b * a * c`] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; EQ_MULT_LCANCEL] THEN
  ASM_SIMP_TAC[GSYM DIVISION]);;

let MOD_MULT2 = prove
 (`!m n p. (m * n) MOD (m * p) = m * n MOD p`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[MOD_ZERO; MULT_CLAUSES] THEN ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[MOD_ZERO; MULT_CLAUSES] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `n DIV p` THEN
  ASM_SIMP_TAC[LT_MULT_LCANCEL; DIVISION] THEN
  ONCE_REWRITE_TAC[AC MULT_AC `a * b * c:num = b * a * c`] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; EQ_MULT_LCANCEL] THEN
  ASM_SIMP_TAC[GSYM DIVISION]);;

let MOD_EXISTS = prove
 (`!m n. (?q. m = n * q) <=> if n = 0 then (m = 0) else (m MOD n = 0)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MOD_MULT] THEN
  EXISTS_TAC `m DIV n` THEN
  SUBGOAL_THEN `m = (m DIV n) * n + m MOD n`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [ASM_MESON_TAC[DIVISION]; ASM_REWRITE_TAC[ADD_CLAUSES; MULT_AC]]);;

let LE_RDIV_EQ = prove
 (`!a b n. ~(a = 0) ==> (n <= b DIV a <=> a * n <= b)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `a * (b DIV a)` THEN
    ASM_REWRITE_TAC[DIV_MUL_LE; LE_MULT_LCANCEL];
    SUBGOAL_THEN `a * n < a * (b DIV a + 1)` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `(b DIV a) * a + b MOD a` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[DIVISION]; ALL_TAC] THEN
      SIMP_TAC[LEFT_ADD_DISTRIB; MULT_SYM; MULT_CLAUSES; LT_ADD_LCANCEL] THEN
      ASM_MESON_TAC[DIVISION];
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; GSYM ADD1; LT_SUC_LE]]]);;

let RDIV_LT_EQ = prove
 (`!a b n. ~(a = 0) ==> (b DIV a < n <=> b < a * n)`,
  SIMP_TAC[GSYM NOT_LE; LE_RDIV_EQ]);;

let LE_LDIV_EQ = prove
 (`!a b n. ~(a = 0) ==> (b DIV a <= n <=> b < a * (n + 1))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NOT_LT] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LE_SUC_LT] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN REWRITE_TAC[NOT_LT; NOT_LE; ADD1]);;

let LDIV_LT_EQ = prove
 (`!a b n. ~(a = 0) ==> (n < b DIV a <=> a * (n + 1) <= b)`,
  SIMP_TAC[GSYM NOT_LE; LE_LDIV_EQ]);;

let LE_LDIV = prove
 (`!a b n. ~(a = 0) /\ b <= a * n ==> b DIV a <= n`,
  SIMP_TAC[LE_LDIV_EQ; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  MESON_TAC[LT_ADD; LT_NZ; LET_TRANS]);;

let DIV_MONO = prove
 (`!m n p. m <= n ==> m DIV p <= n DIV p`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[DIV_ZERO; LE_REFL] THEN
  MATCH_MP_TAC(MESON[LE_REFL] `(!k:num. k <= a ==> k <= b) ==> a <= b`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN ASM_MESON_TAC[LE_TRANS]);;

let DIV_MONO_LT = prove
 (`!m n p. ~(p = 0) /\ m + p <= n ==> m DIV p < n DIV p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[ADD1; LE_SUC_LT; LE_REFL]
   `(!k:num. k <= a ==> k + 1 <= b) ==> a < b`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  ASM_MESON_TAC[LE_REFL; LE_TRANS; LE_ADD2; ADD_SYM]);;

let DIV_EQ_0 = prove
 (`!m n. ~(n = 0) ==> ((m DIV n = 0) <=> m < n)`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o SPEC `m:num` o MATCH_MP DIVISION) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; DIVISION];
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]]);;

let MOD_DIV_EQ_0 = prove
 (`!m n. ~(n = 0) ==> (m MOD n) DIV n = 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> IMP_REWRITE_TAC [th; DIV_EQ_0; MOD_LT_EQ]));;

let MOD_EQ_0 = prove
 (`!m n. (m MOD n = 0) <=> ?q. m = q * n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; MOD_ZERO] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o SPEC `m:num` o MATCH_MP DIVISION) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; DIVISION] THEN MESON_TAC[];
    MATCH_MP_TAC MOD_UNIQ THEN ASM_SIMP_TAC[ADD_CLAUSES; MULT_AC] THEN
    ASM_MESON_TAC[NOT_LE; CONJUNCT1 LE]]);;

let DIV_EQ_SELF = prove
 (`!m n. m DIV n = m <=> m = 0 \/ n = 1`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIV_0] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[DIV_1] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIV_ZERO] THEN
  MATCH_MP_TAC LT_IMP_NE THEN ASM_SIMP_TAC[RDIV_LT_EQ] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(el 2 (CONJUNCTS MULT_CLAUSES))] THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
  REWRITE_TAC[GSYM NOT_LE; ONE; LE] THEN ASM_REWRITE_TAC[GSYM ONE]);;

let MOD_REFL = prove
 (`!n. n MOD n = 0`,
  SIMP_TAC[MOD_EQ_0] THEN MESON_TAC[MULT_CLAUSES]);;

let EVEN_MOD = prove
 (`!n. EVEN(n) <=> n MOD 2 = 0`,
  REWRITE_TAC[EVEN_EXISTS; MOD_EQ_0] THEN MESON_TAC[MULT_SYM]);;

let ODD_MOD = prove
 (`!n. ODD(n) <=> n MOD 2 = 1`,
  GEN_TAC THEN REWRITE_TAC[GSYM NOT_EVEN; EVEN_MOD] THEN
  SUBGOAL_THEN `n MOD 2 < 2` MP_TAC THENL
   [SIMP_TAC[DIVISION; TWO; NOT_SUC]; ALL_TAC] THEN
  SPEC_TAC(`n MOD 2`,`n:num`) THEN
  REWRITE_TAC[TWO; ONE; LT] THEN MESON_TAC[NOT_SUC]);;

let MOD_2_CASES = prove
 (`!n. n MOD 2 = if EVEN n then 0 else 1`,
  MESON_TAC[EVEN_MOD; ODD_MOD; NOT_ODD]);;

let EVEN_MOD_EVEN = prove
 (`!m n. EVEN n ==> (EVEN(m MOD n) <=> EVEN m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EVEN_MOD] THEN
  ASM_SIMP_TAC[MOD_EVEN_2]);;

let ODD_MOD_EVEN = prove
 (`!m n. EVEN n ==> (ODD(m MOD n) <=> ODD m)`,
  SIMP_TAC[GSYM NOT_EVEN; EVEN_MOD_EVEN]);;

let HALF_DOUBLE = prove
 (`(!n. (2 * n) DIV 2 = n) /\ (!n. (n * 2) DIV 2 = n)`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  SIMP_TAC[DIV_MULT; TWO; NOT_SUC]);;

let DOUBLE_HALF = prove
 (`(!n. EVEN n ==> 2 * n DIV 2 = n) /\
   (!n. EVEN n ==> n DIV 2 * 2 = n)`,
  SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; HALF_DOUBLE] THEN
  REWRITE_TAC[MULT_SYM]);;

let MOD_MULT_RMOD = prove
 (`!m n p. (m * (p MOD n)) MOD n = (m * p) MOD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MOD_ZERO] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC `m * p DIV n` THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL] THEN DISJ2_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_SIMP_TAC[DIVISION]);;

let MOD_MULT_LMOD = prove
 (`!m n p. ((m MOD n) * p) MOD n = (m * p) MOD n`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[MOD_MULT_RMOD]);;

let MOD_MULT_MOD2 = prove
 (`!m n p. ((m MOD n) * (p MOD n)) MOD n = (m * p) MOD n`,
  SIMP_TAC[MOD_MULT_RMOD; MOD_MULT_LMOD]);;

let MOD_EXP_MOD = prove
 (`!m n p. ((m MOD n) EXP p) MOD n = (m EXP p) MOD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MOD_ZERO] THEN SPEC_TAC(`p:num`,`p:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP] THEN ASM_SIMP_TAC[MOD_MULT_LMOD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(m * ((m MOD n) EXP p) MOD n) MOD n` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[MOD_MULT_RMOD]);;

let MOD_MULT_ADD = prove
 (`(!m n p. (m * n + p) MOD n = p MOD n) /\
   (!m n p. (n * m + p) MOD n = p MOD n) /\
   (!m n p. (p + m * n) MOD n = p MOD n) /\
   (!m n p. (p + n * m) MOD n = p MOD n)`,
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN
  CONJ_TAC THENL [SIMP_TAC[MULT_AC; ADD_AC]; REPEAT GEN_TAC] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `m + p DIV n` THEN
  ASM_SIMP_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC; EQ_ADD_LCANCEL; DIVISION]);;

let DIV_MULT_ADD = prove
 (`(!a b n. ~(n = 0) ==> (a * n + b) DIV n = a + b DIV n) /\
   (!a b n. ~(n = 0) ==> (n * a + b) DIV n = a + b DIV n) /\
   (!a b n. ~(n = 0) ==> (b + a * n) DIV n = b DIV n + a) /\
   (!a b n. ~(n = 0) ==> (b + n * a) DIV n = b DIV n + a)`,
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN
  CONJ_TAC THENL [SIMP_TAC[MULT_AC; ADD_AC]; REPEAT STRIP_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `b MOD n` THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  ASM_MESON_TAC[DIVISION]);;

let MOD_ADD_MOD = prove
 (`!a b n. (a MOD n + b MOD n) MOD n = (a + b) MOD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MOD_ZERO] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
  EXISTS_TAC `a DIV n + b DIV n` THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
  ONCE_REWRITE_TAC[AC ADD_AC `(a + b) + (c + d) = (c + a) + (d + b)`] THEN
  BINOP_TAC THEN ASM_SIMP_TAC[DIVISION]);;

let DIV_ADD_MOD = prove
 (`!a b n. ~(n = 0)
           ==> (((a + b) MOD n = a MOD n + b MOD n) <=>
                ((a + b) DIV n = a DIV n + b DIV n))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION) THEN
  DISCH_THEN(fun th -> MAP_EVERY (MP_TAC o CONJUNCT1 o C SPEC th)
    [`a + b:num`; `a:num`; `b:num`]) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    MP_TAC(MK_COMB(AP_TERM `(+)` th2,th1)))) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV) [th]) THEN
  ONCE_REWRITE_TAC[AC ADD_AC `(a + b) + c + d = (a + c) + (b + d)`] THEN
  REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN
  DISCH_THEN(fun th -> EQ_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[EQ_ADD_RCANCEL; EQ_ADD_LCANCEL; EQ_MULT_RCANCEL] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let MOD_ADD_EQ_EQ = prove
 (`!n x y. (x + y) MOD n = x MOD n + y MOD n <=>
           n = 0 \/ x MOD n + y MOD n < n`,
  MESON_TAC[MOD_ZERO; MOD_EQ_SELF; MOD_ADD_MOD]);;

let DIV_ADD_EQ_EQ = prove
 (`!n x y. (x + y) DIV n = x DIV n + y DIV n <=>
           n = 0 \/ x MOD n + y MOD n < n`,
  METIS_TAC[DIV_ZERO; ADD_CLAUSES; DIV_ADD_MOD; MOD_ADD_EQ_EQ]);;

let DIV_ADD_EQ = prove
 (`!n x y. x MOD n + y MOD n < n ==> (x + y) DIV n = x DIV n + y DIV n`,
  SIMP_TAC[DIV_ADD_EQ_EQ]);;

let MOD_ADD_EQ = prove
 (`!n x y. x MOD n + y MOD n < n ==> (x + y) MOD n = x MOD n + y MOD n`,
  SIMP_TAC[MOD_ADD_EQ_EQ]);;

let DIV_REFL = prove
 (`!n. ~(n = 0) ==> (n DIV n = 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_0]);;

let MOD_LE = prove
 (`!m n. m MOD n <= m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MOD_ZERO; LE_REFL] THEN FIRST_ASSUM
  (fun th -> GEN_REWRITE_TAC RAND_CONV
   [MATCH_MP DIVISION th]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LE_ADD]);;

let DIV_MONO2 = prove
 (`!m n p. ~(p = 0) /\ p <= m ==> n DIV m <= n DIV p`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LE_RDIV_EQ] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m * n DIV m` THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MP_TAC(SPECL [`n:num`; `m:num`] DIVISION) THEN ASM_MESON_TAC[LE_ADD; LE]);;

let DIV_LE_EXCLUSION = prove
 (`!a b c d. ~(b = 0) /\ b * c < (a + 1) * d ==> c DIV d <= a DIV b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[LE_REFL] `(!k:num. k <= a ==> k <= b) ==> a <= b`) THEN
  X_GEN_TAC `k:num` THEN
  SUBGOAL_THEN `b * d * k <= b * c ==> (b * k) * d < (a + 1) * d` MP_TAC THENL
   [ASM_MESON_TAC[LET_TRANS; MULT_AC]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_IMP THEN
  ASM_SIMP_TAC[LE_MULT_LCANCEL; LT_MULT_RCANCEL; LE_RDIV_EQ] THEN
  REWRITE_TAC[GSYM ADD1; LT_SUC_LE]);;

let DIV_EQ_EXCLUSION = prove
 (`!a b c d.
        b * c < (a + 1) * d /\ a * d < (c + 1) * b ==> (a DIV b = c DIV d)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN
  ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN
  ASM_MESON_TAC[MULT_SYM; LE_ANTISYM; DIV_LE_EXCLUSION]);;

let MULT_DIV_LE = prove
 (`!m n p. m * (n DIV p) <= (m * n) DIV p`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[LE_REFL; DIV_ZERO; MULT_CLAUSES] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [CONJUNCT1 th]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN REWRITE_TAC[MULT_AC; LE_ADD]);;

let DIV_DIV = prove
 (`!m n p. (m DIV n) DIV p = m DIV (n * p)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; DIV_ZERO] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[DIV_0; MULT_CLAUSES; DIV_ZERO] THEN
  REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[LE_ANTISYM] `(!k. k <= m <=> k <= n) ==> m = n`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; MULT_EQ_0; MULT_ASSOC]);;

let DIV_MOD = prove
 (`!m n p. (m DIV n) MOD p = (m MOD (n * p)) DIV n`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[MOD_ZERO; MULT_CLAUSES] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MOD_0; MULT_CLAUSES; DIV_ZERO] THEN
  MATCH_MP_TAC(MESON[LE_ANTISYM] `(!k. k <= m <=> k <= n) ==> m = n`) THEN
  X_GEN_TAC `k:num` THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `k + p * ((m DIV n) DIV p) <= (m DIV n)` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`m DIV n`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`m:num`; `n * p:num`] DIVISION) THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; MULT_EQ_0; DIV_DIV; LEFT_ADD_DISTRIB]] THEN
  REWRITE_TAC[MULT_AC] THEN MESON_TAC[ADD_SYM; MULT_SYM; LE_ADD_RCANCEL]);;

let MOD_MULT_MOD = prove
 (`!m n p. m MOD (n * p) = n * (m DIV n) MOD p + m MOD n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; MOD_ZERO; ADD_CLAUSES] THEN
  ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; MOD_ZERO] THEN
    ASM_METIS_TAC[DIVISION; MULT_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[EQ_ADD_LCANCEL] `(?a. a + x = a + y) ==> x = y`) THEN
  EXISTS_TAC `m DIV n DIV p * n * p` THEN
  REWRITE_TAC[DIVISION_SIMP; DIV_DIV] THEN
  REWRITE_TAC[AC MULT_AC `d * n * p = n * (d * p)`] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; ADD_ASSOC; GSYM DIV_DIV] THEN
  REWRITE_TAC[DIVISION_SIMP]);;

let MOD_MOD_EXP_MIN = prove
 (`!x p m n. x MOD (p EXP m) MOD (p EXP n) = x MOD (p EXP (MIN m n))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[EXP_ZERO; MIN] THEN ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[MOD_ZERO; MOD_1; MOD_0; LE_0] THEN
    ASM_CASES_TAC `m:num <= n` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE];
    REWRITE_TAC[MIN]] THEN
   ASM_CASES_TAC `m:num <= n` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `p EXP m` THEN
    ASM_SIMP_TAC[DIVISION; EXP_EQ_0; LE_EXP; LE_ADD];
    SUBGOAL_THEN `?d. m = n + d` (CHOOSE_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[LE_CASES; LE_EXISTS];
      ASM_SIMP_TAC[EXP_ADD; MOD_MOD; MULT_EQ_0; EXP_EQ_0]]]);;

let DIV_EXP,MOD_EXP = (CONJ_PAIR o prove)
 (`(!m n p. ~(m = 0)
            ==> (m EXP n) DIV (m EXP p) =
                if p <= n then m EXP (n - p)
                else if m = 1 then 1 else 0) /\
   (!m n p. ~(m = 0)
            ==> (m EXP n) MOD (m EXP p) =
                if p <= n \/ m = 1 then 0 else m EXP n)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_CASES_TAC `p:num <= n` THEN
  ASM_SIMP_TAC[GSYM EXP_ADD; EXP_LT_0; SUB_ADD; ADD_CLAUSES] THEN
  ASM_CASES_TAC `m = 1` THEN
  ASM_REWRITE_TAC[EXP_ONE; ADD_CLAUSES; MULT_CLAUSES; LT_EXP] THEN
  REWRITE_TAC[LT; GSYM NOT_LT; ONE; TWO] THEN
  ASM_REWRITE_TAC[SYM ONE; GSYM NOT_LE]);;

let FORALL_LT_MOD_THM = prove
 (`!P n. (!a. a < n ==> P a) <=> n = 0 \/ !a. P(a MOD n)`,
  MESON_TAC[LT; MOD_EQ_SELF; MOD_LT_EQ]);;

let FORALL_MOD_THM = prove
 (`!P n. ~(n = 0) ==> ((!a. P(a MOD n)) <=> (!a. a < n ==> P a))`,
  SIMP_TAC[FORALL_LT_MOD_THM]);;

let EXISTS_LT_MOD_THM = prove
 (`!P n. (?a. a < n /\ P a) <=> ~(n = 0) /\ ?a. P(a MOD n)`,
  MESON_TAC[LT; MOD_EQ_SELF; MOD_LT_EQ]);;

let EXISTS_MOD_THM = prove
 (`!P n. ~(n = 0) ==> ((?a. P(a MOD n)) <=> (?a. a < n /\ P a))`,
  SIMP_TAC[EXISTS_LT_MOD_THM]);;

(* ------------------------------------------------------------------------- *)
(* Theorems for eliminating cutoff subtraction, predecessor, DIV and MOD.    *)
(* We have versions that introduce universal or existential quantifiers.     *)
(* ------------------------------------------------------------------------- *)

let PRE_ELIM_THM = prove
 (`P(PRE n) <=> !m. n = SUC m \/ m = 0 /\ n = 0 ==> P m`,
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[NOT_SUC; SUC_INJ; PRE] THEN MESON_TAC[]);;

let PRE_ELIM_THM' = prove
 (`P(PRE n) <=> ?m. (n = SUC m \/ m = 0 /\ n = 0) /\ P m`,
  MP_TAC(INST [`\x:num. ~P x`,`P:num->bool`] PRE_ELIM_THM) THEN MESON_TAC[]);;

let SUB_ELIM_THM = prove
 (`P(a - b) <=> !d. a = b + d \/ a < b /\ d = 0 ==> P d`,
  DISJ_CASES_TAC(SPECL [`a:num`; `b:num`] LTE_CASES) THENL
   [ASM_MESON_TAC[NOT_LT; SUB_EQ_0; LT_IMP_LE; LE_ADD]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  SIMP_TAC[ADD_SUB2; GSYM NOT_LE; LE_ADD; EQ_ADD_LCANCEL] THEN MESON_TAC[]);;

let SUB_ELIM_THM' = prove
 (`P(a - b) <=> ?d. (a = b + d \/ a < b /\ d = 0) /\ P d`,
  MP_TAC(INST [`\x:num. ~P x`,`P:num->bool`] SUB_ELIM_THM) THEN MESON_TAC[]);;

let DIVMOD_ELIM_THM = prove
 (`P (m DIV n) (m MOD n) <=>
        !q r. n = 0 /\ q = 0 /\ r = m \/ m = q * n + r /\ r < n ==> P q r`,
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[DIVISION_0; LT];
    FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION) THEN MESON_TAC[DIVMOD_UNIQ]]);;

let DIVMOD_ELIM_THM' = prove
 (`P (m DIV n) (m MOD n) <=>
        ?q r. (n = 0 /\ q = 0 /\ r = m \/ m = q * n + r /\ r < n) /\ P q r`,
  MP_TAC(INST [`\x:num y:num. ~P x y`,`P:num->num->bool`] DIVMOD_ELIM_THM) THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pushing and pulling to combine nested MOD terms into a single MOD.        *)
(* ------------------------------------------------------------------------- *)

let MOD_DOWN_CONV =
  let MOD_SUC_MOD = METIS[ADD1; MOD_ADD_MOD; MOD_MOD_REFL]
   `(SUC(m MOD n)) MOD n = SUC m MOD n` in
  let addmul_conv = GEN_REWRITE_CONV I
    [GSYM MOD_SUC_MOD; GSYM MOD_ADD_MOD; GSYM MOD_MULT_MOD2; GSYM MOD_EXP_MOD]
  and mod_conv = GEN_REWRITE_CONV I [MOD_MOD_REFL] in
  let rec downconv tm =
   ((addmul_conv THENC LAND_CONV downconv) ORELSEC
    (mod_conv THENC downconv) ORELSEC
    SUB_CONV downconv) tm
  and upconv =
    GEN_REWRITE_CONV DEPTH_CONV
     [MOD_SUC_MOD; MOD_ADD_MOD; MOD_MULT_MOD2; MOD_EXP_MOD; MOD_MOD_REFL] in
  downconv THENC upconv;;

(* ------------------------------------------------------------------------- *)
(* Crude but useful conversion for cancelling down equations.                *)
(* ------------------------------------------------------------------------- *)

let NUM_CANCEL_CONV =
  let rec minter i l1' l2' l1 l2 =
    if l1 = [] then (i,l1',l2'@l2)
    else if l2 = [] then (i,l1@l1',l2') else
    let h1 = hd l1 and h2 = hd l2 in
    if h1 = h2 then minter (h1::i) l1' l2' (tl l1) (tl l2)
    else if h1 < h2 then minter i (h1::l1') l2' (tl l1) l2
    else minter i l1' (h2::l2') l1 (tl l2) in
  let add_tm = `(+)` and eq_tm = `(=) :num->num->bool` in
  let EQ_ADD_LCANCEL_0' =
    GEN_REWRITE_RULE (funpow 2 BINDER_CONV o LAND_CONV) [EQ_SYM_EQ]
      EQ_ADD_LCANCEL_0 in
  let AC_RULE = AC ADD_AC in
  fun tm ->
    let l,r = dest_eq tm in
    let lats = sort (<=) (binops `(+)` l)
    and rats = sort (<=) (binops `(+)` r) in
    let i,lats',rats' = minter [] [] [] lats rats in
    let l' = list_mk_binop add_tm (i @ lats')
    and r' = list_mk_binop add_tm (i @ rats') in
    let lth = AC_RULE (mk_eq(l,l'))
    and rth = AC_RULE (mk_eq(r,r')) in
    let eth = MK_COMB(AP_TERM eq_tm lth,rth) in
    GEN_REWRITE_RULE (RAND_CONV o REPEATC)
      [EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; EQ_ADD_LCANCEL_0'] eth;;

(* ------------------------------------------------------------------------- *)
(* This is handy for easing MATCH_MP on inequalities.                        *)
(* ------------------------------------------------------------------------- *)

let LE_IMP =
  let pth = PURE_ONCE_REWRITE_RULE[IMP_CONJ] LE_TRANS in
  fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th));;

(* ------------------------------------------------------------------------- *)
(* Binder for "the minimal n such that".                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_binder "minimal";;

let minimal = new_definition
  `(minimal) (P:num->bool) = @n. P n /\ !m. m < n ==> ~(P m)`;;

let MINIMAL = prove
 (`!P. (?n. P n) <=> P((minimal) P) /\ (!m. m < (minimal) P ==> ~(P m))`,
  GEN_TAC THEN REWRITE_TAC[minimal] THEN CONV_TAC(RAND_CONV SELECT_CONV) THEN
  REWRITE_TAC[GSYM num_WOP]);;

let MINIMAL_UNIQUE = prove
 (`!P n. P n /\ (!m. m < n ==> ~P m) ==> (minimal) P = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[minimal] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[LT_CASES]);;

let LE_MINIMAL = prove
 (`!P n.
        (?r. P r) ==> (n <= (minimal) P <=> !i. P i ==> n <= i)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN
  MESON_TAC[NOT_LE; LE_TRANS]);;

let MINIMAL_LE = prove
 (`!P n. (?r. P r) ==> ((minimal) P <= n <=> ?i. i <= n /\ P i)`,
  REWRITE_TAC[GSYM NOT_LT] THEN REWRITE_TAC[GSYM LE_SUC_LT] THEN
  SIMP_TAC[LE_MINIMAL] THEN MESON_TAC[]);;

let MINIMAL_UBOUND = prove
 (`!P n. P n ==> (minimal) P <= n`,
  MESON_TAC[MINIMAL; NOT_LT]);;

let MINIMAL_LBOUND = prove
 (`!P n. (?r. P r) /\ (!m. m < n ==> ~P m) ==> n <= (minimal) P`,
  SIMP_TAC[LE_MINIMAL] THEN MESON_TAC[NOT_LT]);;

let MINIMAL_MONO = prove
 (`!P Q. (?n. P n) /\ (!n. P n ==> Q n) ==> (minimal) Q <= (minimal) P`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `?n:num. Q n` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[LE_TRANS; LE_REFL]
   `(!p:num. p <= m ==> p <= n) ==> m <= n`) THEN
  ASM_SIMP_TAC[LE_MINIMAL]);;

(* ------------------------------------------------------------------------- *)
(* A common lemma for transitive relations.                                  *)
(* ------------------------------------------------------------------------- *)

let TRANSITIVE_STEPWISE_LT_EQ = prove
 (`!R. (!x y z. R x y /\ R y z ==> R x z)
         ==> ((!m n. m < n ==> R m n) <=> (!n. R n (SUC n)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[LT] THEN
  DISCH_TAC THEN SIMP_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL; ADD_CLAUSES] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[]);;

let TRANSITIVE_STEPWISE_LT = prove
 (`!R. (!x y z. R x y /\ R y z ==> R x z) /\ (!n. R n (SUC n))
       ==> !m n. m < n ==> R m n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(a ==> (c <=> b)) ==> a /\ b ==> c`) THEN
  MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LT_EQ);;

let TRANSITIVE_STEPWISE_LE_EQ = prove
 (`!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z)
       ==> ((!m n. m <= n ==> R m n) <=> (!n. R n (SUC n)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[LE; LE_REFL] THEN

  DISCH_TAC THEN SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL; ADD_CLAUSES] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[]);;

let TRANSITIVE_STEPWISE_LE = prove
 (`!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z) /\
       (!n. R n (SUC n))
       ==> !m n. m <= n ==> R m n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(a /\ a' ==> (c <=> b)) ==> a /\ a' /\ b ==> c`) THEN
  MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LE_EQ);;

(* ------------------------------------------------------------------------- *)
(* A couple of forms of Dependent Choice.                                    *)
(* ------------------------------------------------------------------------- *)

let DEPENDENT_CHOICE_FIXED = prove
 (`!P R a:A.
        P 0 a /\ (!n x. P n x ==> ?y. P (SUC n) y /\ R n x y)
        ==> ?f. f 0 = a /\ (!n. P n (f n)) /\ (!n. R n (f n) (f(SUC n)))`,
  REPEAT STRIP_TAC THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
    `f 0 = (a:A) /\ (!n. f(SUC n) = @y. P (SUC n) y /\ R n (f n) y)` THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV
   [MESON[num_CASES] `(!n. P n) <=> P 0 /\ !n. P(SUC n)`] THEN
  ASM_REWRITE_TAC[AND_FORALL_THM] THEN INDUCT_TAC THEN ASM_MESON_TAC[]);;

let DEPENDENT_CHOICE = prove
 (`!P R:num->A->A->bool.
        (?a. P 0 a) /\ (!n x. P n x ==> ?y. P (SUC n) y /\ R n x y)
        ==> ?f. (!n. P n (f n)) /\ (!n. R n (f n) (f(SUC n)))`,
  MESON_TAC[DEPENDENT_CHOICE_FIXED]);;

(* ------------------------------------------------------------------------- *)
(* Conversion that elimimates every occurrence of `NUMERAL`, `BIT0`,         *)
(* `BIT1`, `_0` that is not part of a well-formed numeral.                   *)
(* ------------------------------------------------------------------------- *)

let BITS_ELIM_CONV : conv =
  let NUMERAL_pth = prove(`m = n <=> NUMERAL m = n`,REWRITE_TAC[NUMERAL])
  and ZERO_pth = GSYM (REWRITE_CONV[NUMERAL] `0`)
  and BIT0_pth,BIT1_pth = CONJ_PAIR
   (prove(`(m = n <=> BIT0 m = 2 * n) /\
           (m = n <=> BIT1 m = 2 * n + 1)`,
    CONJ_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [BIT0; BIT1] THEN
    REWRITE_TAC[ADD1; EQ_ADD_RCANCEL; GSYM MULT_2] THEN
    REWRITE_TAC[EQ_MULT_LCANCEL] THEN
    REWRITE_TAC[TWO; NOT_SUC]))
  and mvar,nvar = `m:num`,`n:num` in
  let rec BITS_ELIM_CONV : conv =
    fun tm -> match tm with
      Const("_0",_) -> ZERO_pth
    | Var _ | Const _ -> REFL tm
    | Comb(Const("NUMERAL",_),mtm) ->
        if is_numeral tm then REFL tm else
        let th = BITS_ELIM_CONV mtm in
        EQ_MP (INST[mtm,mvar;rand(concl th),nvar] NUMERAL_pth) th
    | Comb(Const("BIT0",_),mtm) ->
        let th = BITS_ELIM_CONV mtm in
        EQ_MP (INST [mtm,mvar;rand(concl th),nvar] BIT0_pth) th
    | Comb(Const("BIT1",_),mtm) ->
        let th = BITS_ELIM_CONV mtm in
        EQ_MP (INST [mtm,mvar;rand(concl th),nvar] BIT1_pth) th
    | Comb _ -> COMB_CONV BITS_ELIM_CONV tm
    | Abs _ -> ABS_CONV BITS_ELIM_CONV tm in
  BITS_ELIM_CONV;;
