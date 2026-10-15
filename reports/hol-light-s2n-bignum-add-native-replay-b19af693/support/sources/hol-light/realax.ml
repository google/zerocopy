(* ========================================================================= *)
(* Theory of real numbers.                                                   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "lists.ml";;

(* ------------------------------------------------------------------------- *)
(* The main infix overloaded operations                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("++",(16,"right"));;
parse_as_infix("**",(20,"right"));;
parse_as_infix("<<=",(12,"right"));;
parse_as_infix("===",(10,"right"));;

parse_as_infix ("treal_mul",(20,"right"));;
parse_as_infix ("treal_add",(16,"right"));;
parse_as_infix ("treal_le",(12,"right"));;
parse_as_infix ("treal_eq",(10,"right"));;

make_overloadable "+" `:A->A->A`;;
make_overloadable "-" `:A->A->A`;;
make_overloadable "*" `:A->A->A`;;
make_overloadable "/" `:A->A->A`;;
make_overloadable "<" `:A->A->bool`;;
make_overloadable "<=" `:A->A->bool`;;
make_overloadable ">" `:A->A->bool`;;
make_overloadable ">=" `:A->A->bool`;;
make_overloadable "--" `:A->A`;;
make_overloadable "pow" `:A->num->A`;;
make_overloadable "inv" `:A->A`;;
make_overloadable "abs" `:A->A`;;
make_overloadable "max" `:A->A->A`;;
make_overloadable "min" `:A->A->A`;;
make_overloadable "&" `:num->A`;;

do_list overload_interface
 ["+",`(+):num->num->num`; "-",`(-):num->num->num`;
  "*",`(*):num->num->num`; "<",`(<):num->num->bool`;
  "<=",`(<=):num->num->bool`; ">",`(>):num->num->bool`;
  ">=",`(>=):num->num->bool`];;

let prioritize_num() = prioritize_overload(mk_type("num",[]));;

(* ------------------------------------------------------------------------- *)
(* Absolute distance function on the naturals.                               *)
(* ------------------------------------------------------------------------- *)

let dist = new_definition
  `dist(m,n) = (m - n) + (n - m)`;;

(* ------------------------------------------------------------------------- *)
(* Some easy theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let DIST_REFL = prove
 (`!n. dist(n,n) = 0`,
  REWRITE_TAC[dist; SUB_REFL; ADD_CLAUSES]);;

let DIST_LZERO = prove
 (`!n. dist(0,n) = n`,
  REWRITE_TAC[dist; SUB_0; ADD_CLAUSES]);;

let DIST_RZERO = prove
 (`!n. dist(n,0) = n`,
  REWRITE_TAC[dist; SUB_0; ADD_CLAUSES]);;

let DIST_SYM = prove
 (`!m n. dist(m,n) = dist(n,m)`,
  REWRITE_TAC[dist] THEN MATCH_ACCEPT_TAC ADD_SYM);;

let DIST_LADD = prove
 (`!m p n. dist(m + n,m + p) = dist(n,p)`,
  REWRITE_TAC[dist; SUB_ADD_LCANCEL]);;

let DIST_RADD = prove
 (`!m p n. dist(m + p,n + p) = dist(m,n)`,
  REWRITE_TAC[dist; SUB_ADD_RCANCEL]);;

let DIST_LADD_0 = prove
 (`!m n. dist(m + n,m) = n`,
  REWRITE_TAC[dist; ADD_SUB2; ADD_SUBR2; ADD_CLAUSES]);;

let DIST_RADD_0 = prove
 (`!m n. dist(m,m + n) = n`,
  ONCE_REWRITE_TAC[DIST_SYM] THEN MATCH_ACCEPT_TAC DIST_LADD_0);;

let DIST_LMUL = prove
 (`!m n p. m * dist(n,p) = dist(m * n,m * p)`,
  REWRITE_TAC[dist; LEFT_ADD_DISTRIB; LEFT_SUB_DISTRIB]);;

let DIST_RMUL = prove
 (`!m n p. dist(m,n) * p = dist(m * p,n * p)`,
  REWRITE_TAC[dist; RIGHT_ADD_DISTRIB; RIGHT_SUB_DISTRIB]);;

let DIST_EQ_0 = prove
 (`!m n. (dist(m,n) = 0) <=> (m = n)`,
  REWRITE_TAC[dist; ADD_EQ_0; SUB_EQ_0; LE_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Simplifying theorem about the distance operation.                         *)
(* ------------------------------------------------------------------------- *)

let DIST_ELIM_THM = prove
 (`P(dist(x,y)) <=> !d. ((x = y + d) ==> P(d)) /\ ((y = x + d) ==> P(d))`,
  DISJ_CASES_TAC(SPECL [`x:num`; `y:num`] LE_CASES) THEN
  POP_ASSUM(X_CHOOSE_THEN `e:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[dist; ADD_SUB; ADD_SUB2; ADD_SUBR; ADD_SUBR2] THEN
  REWRITE_TAC[ADD_CLAUSES; EQ_ADD_LCANCEL] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REWRITE_TAC[GSYM ADD_ASSOC; EQ_ADD_LCANCEL_0; ADD_EQ_0] THEN
  ASM_CASES_TAC `e = 0` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Now some more theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

let DIST_LE_CASES,DIST_ADDBOUND,DIST_TRIANGLE,DIST_ADD2,DIST_ADD2_REV =
  let DIST_ELIM_TAC =
    let conv =
      HIGHER_REWRITE_CONV[SUB_ELIM_THM; COND_ELIM_THM; DIST_ELIM_THM] false in
    CONV_TAC conv THEN TRY GEN_TAC THEN CONJ_TAC THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN
                         (let l,r = dest_eq (concl th) in
                          if is_var l && not (vfree_in l r) then ALL_TAC
                          else ASSUME_TAC th)) in
  let DIST_ELIM_TAC' =
    REPEAT STRIP_TAC THEN REPEAT DIST_ELIM_TAC THEN
    REWRITE_TAC[GSYM NOT_LT; LT_EXISTS] THEN
    DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN POP_ASSUM MP_TAC THEN
    CONV_TAC(LAND_CONV NUM_CANCEL_CONV) THEN
    REWRITE_TAC[ADD_CLAUSES; NOT_SUC] in
  let DIST_LE_CASES = prove
   (`!m n p. dist(m,n) <= p <=> (m <= n + p) /\ (n <= m + p)`,
    REPEAT GEN_TAC THEN REPEAT DIST_ELIM_TAC THEN
    REWRITE_TAC[GSYM ADD_ASSOC; LE_ADD; LE_ADD_LCANCEL])
  and DIST_ADDBOUND = prove
   (`!m n. dist(m,n) <= m + n`,
    REPEAT GEN_TAC THEN DIST_ELIM_TAC THENL
     [ONCE_REWRITE_TAC[ADD_SYM]; ALL_TAC] THEN
    REWRITE_TAC[ADD_ASSOC; LE_ADDR])
  and [DIST_TRIANGLE; DIST_ADD2; DIST_ADD2_REV] = (CONJUNCTS o prove)
   (`(!m n p. dist(m,p) <= dist(m,n) + dist(n,p)) /\
     (!m n p q. dist(m + n,p + q) <= dist(m,p) + dist(n,q)) /\
     (!m n p q. dist(m,p) <= dist(m + n,p + q) + dist(n,q))`,
    DIST_ELIM_TAC') in
  DIST_LE_CASES,DIST_ADDBOUND,DIST_TRIANGLE,DIST_ADD2,DIST_ADD2_REV;;

let DIST_TRIANGLE_LE = prove
 (`!m n p q. dist(m,n) + dist(n,p) <= q ==> dist(m,p) <= q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `dist(m,n) + dist(n,p)` THEN ASM_REWRITE_TAC[DIST_TRIANGLE]);;

let DIST_TRIANGLES_LE = prove
 (`!m n p q r s.
        dist(m,n) <= r /\ dist(p,q) <= s ==> dist(m,p) <= dist(n,q) + r + s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_LE THEN
  EXISTS_TAC `n:num` THEN GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN MATCH_MP_TAC LE_ADD2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIST_TRIANGLE_LE THEN
  EXISTS_TAC `q:num` THEN GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
  REWRITE_TAC[LE_ADD_LCANCEL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful lemmas about bounds.                                               *)
(* ------------------------------------------------------------------------- *)

let BOUNDS_LINEAR = prove
 (`!A B C. (!n. A * n <= B * n + C) <=> A <= B`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LE] THEN
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LT_EXISTS]) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; LE_ADD_LCANCEL] THEN
    DISCH_THEN(MP_TAC o SPEC `SUC C`) THEN
    REWRITE_TAC[NOT_LE; MULT_CLAUSES; ADD_CLAUSES; LT_SUC_LE] THEN
    REWRITE_TAC[ADD_ASSOC; LE_ADDR];
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC; LE_ADD]]);;

let BOUNDS_LINEAR_0 = prove
 (`!A B. (!n. A * n <= B) <=> (A = 0)`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`A:num`; `0`; `B:num`] BOUNDS_LINEAR) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE]);;

let BOUNDS_DIVIDED = prove
 (`!P. (?B. !n. P(n) <= B) <=>
       (?A B. !n. n * P(n) <= A * n + B)`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`B:num`; `0`] THEN
    GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    EXISTS_TAC `P(0) + A + B` THEN GEN_TAC THEN
    MP_TAC(SPECL [`n:num`; `(P:num->num) n`; `P(0) + A + B`]
     LE_MULT_LCANCEL) THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[LE_ADD] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `A * n + B` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    REWRITE_TAC[GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `B * n` THEN
    REWRITE_TAC[LE_ADD] THEN UNDISCH_TAC `~(n = 0)` THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; LE_ADD]]);;

let BOUNDS_NOTZERO = prove
 (`!P A B. (P 0 0 = 0) /\ (!m n. P m n <= A * (m + n) + B) ==>
       (?B. !m n. P m n <= B * (m + n))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `A + B` THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m + n = 0` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ADD_EQ_0]) THEN ASM_REWRITE_TAC[LE_0];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `A * (m + n) + B` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[RIGHT_ADD_DISTRIB; LE_ADD_LCANCEL] THEN
    UNDISCH_TAC `~(m + n = 0)` THEN SPEC_TAC(`m + n`,`p:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; LE_ADD]]);;

let BOUNDS_IGNORE = prove
 (`!P Q. (?B. !i. P(i) <= Q(i) + B) <=>
         (?B N. !i. N <= i ==> P(i) <= Q(i) + B)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `B:num` THEN ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN SPEC_TAC(`B:num`,`B:num`) THEN
    SPEC_TAC(`N:num`,`N:num`) THEN INDUCT_TAC THENL
     [REWRITE_TAC[LE_0] THEN GEN_TAC THEN DISCH_TAC THEN
      EXISTS_TAC `B:num` THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `B + P(N:num)` THEN X_GEN_TAC `i:num` THEN
      DISCH_TAC THEN ASM_CASES_TAC `SUC N <= i` THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Q(i:num) + B` THEN
        REWRITE_TAC[LE_ADD; ADD_ASSOC] THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `~(SUC N <= i)` THEN REWRITE_TAC[NOT_LE; LT] THEN
        ASM_REWRITE_TAC[GSYM NOT_LE] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
        REWRITE_TAC[LE_ADD]]]]);;

(* ------------------------------------------------------------------------- *)
(* Define type of nearly-multiplicative functions. This is equivalent to     *)
(* being nearly-additive, hence the name, but it is easier to work with this *)
(* formulation rather than actually derive it from nearly-additivity.        *)
(* ------------------------------------------------------------------------- *)

let is_nadd = new_definition
  `is_nadd x <=> (?B. !m n. dist(m * x(n),n * x(m)) <= B * (m + n))`;;

let is_nadd_0 = prove
 (`is_nadd (\n. 0)`,
  REWRITE_TAC[is_nadd; MULT_CLAUSES; DIST_REFL; LE_0]);;

let nadd_abs,nadd_rep =
  new_basic_type_definition "nadd" ("mk_nadd","dest_nadd") is_nadd_0;;

override_interface ("fn",`dest_nadd`);;
override_interface ("afn",`mk_nadd`);;

(* ------------------------------------------------------------------------- *)
(* Properties of nearly-multiplicative / nearly-additive functions.          *)
(* ------------------------------------------------------------------------- *)

let NADD_CAUCHY = prove
 (`!x. ?B. !m n. dist(m * fn x n,n * fn x m) <= B * (m + n)`,
  REWRITE_TAC[GSYM is_nadd; nadd_rep; nadd_abs; ETA_AX]);;

let NADD_BOUND = prove
 (`!x. ?A B. !n. fn x n <= A * n + B`,
  GEN_TAC THEN X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
  MAP_EVERY EXISTS_TAC [`B + fn x 1`; `B:num`] THEN GEN_TAC THEN
  POP_ASSUM(MP_TAC o SPECL [`n:num`; `1`]) THEN
  REWRITE_TAC[DIST_LE_CASES; MULT_CLAUSES] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[ADD_AC; MULT_AC]);;

let NADD_MULTIPLICATIVE = prove
 (`!x. ?B. !m n. dist(fn x (m * n),m * fn x n) <= B * m + B`,
  GEN_TAC THEN X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
  EXISTS_TAC `B + fn x 0` THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [MATCH_MP_TAC (LE_IMP DIST_ADDBOUND) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; RIGHT_ADD_DISTRIB; MULT_AC] THEN
    REWRITE_TAC[LE_EXISTS] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_CANCEL_CONV) THEN
    REWRITE_TAC[GSYM EXISTS_REFL]; UNDISCH_TAC `~(n = 0)`] THEN
  REWRITE_TAC[TAUT `(~a ==> b) <=> a \/ b`; GSYM LE_MULT_LCANCEL;
              DIST_LMUL] THEN
  REWRITE_TAC[MULT_ASSOC] THEN GEN_REWRITE_TAC
   (LAND_CONV o RAND_CONV o RAND_CONV o LAND_CONV) [MULT_SYM] THEN
  POP_ASSUM(MATCH_MP_TAC o LE_IMP) THEN
  REWRITE_TAC[LE_EXISTS; RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; MULT_AC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_CANCEL_CONV) THEN
  REWRITE_TAC[GSYM EXISTS_REFL]);;

let NADD_ADDITIVE = prove
 (`!x. ?B. !m n. dist(fn x (m + n),fn x m + fn x n) <= B`,
  GEN_TAC THEN X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
  EXISTS_TAC `3 * B + fn x 0` THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m + n = 0` THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ADD_EQ_0]) THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; DIST_LADD_0; LE_ADDR];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `3 * B` THEN
    REWRITE_TAC[LE_ADD] THEN UNDISCH_TAC `~(m + n = 0)`] THEN
  REWRITE_TAC[TAUT `(~a ==> b) <=> a \/ b`; GSYM LE_MULT_LCANCEL] THEN
  REWRITE_TAC[DIST_LMUL; LEFT_ADD_DISTRIB] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [RIGHT_ADD_DISTRIB] THEN
  MATCH_MP_TAC(LE_IMP DIST_ADD2) THEN
  SUBGOAL_THEN `(m + n) * 3 * B = B * (m + m + n) + B * (n + m + n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SYM(REWRITE_CONV [ARITH] `1 + 1 + 1`)] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
    REWRITE_TAC[MULT_AC] THEN CONV_TAC NUM_CANCEL_CONV THEN REFL_TAC;
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[]]);;

let NADD_SUC = prove
 (`!x. ?B. !n. dist(fn x (SUC n),fn x n) <= B`,
  GEN_TAC THEN X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_ADDITIVE) THEN
  EXISTS_TAC `B + fn x 1` THEN GEN_TAC THEN
  MATCH_MP_TAC(LE_IMP DIST_TRIANGLE) THEN
  EXISTS_TAC `fn x n + fn x 1` THEN
  ASM_REWRITE_TAC[ADD1] THEN MATCH_MP_TAC LE_ADD2 THEN
  ASM_REWRITE_TAC[DIST_LADD_0; LE_REFL]);;

let NADD_DIST_LEMMA = prove
 (`!x. ?B. !m n. dist(fn x (m + n),fn x m) <= B * n`,
  GEN_TAC THEN X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_SUC) THEN
  EXISTS_TAC `B:num` THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; DIST_REFL; LE_0] THEN
  MATCH_MP_TAC(LE_IMP DIST_TRIANGLE) THEN
  EXISTS_TAC `fn x (m + n)` THEN
  REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB] THEN
  GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
  MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[GSYM ADD1; MULT_CLAUSES]);;

let NADD_DIST = prove
 (`!x. ?B. !m n. dist(fn x m,fn x n) <= B * dist(m,n)`,
  GEN_TAC THEN X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_DIST_LEMMA) THEN
  EXISTS_TAC `B:num` THEN REPEAT GEN_TAC THEN
  DISJ_CASES_THEN MP_TAC (SPECL [`m:num`; `n:num`] LE_CASES) THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o ONCE_REWRITE_RULE[LE_EXISTS]) THENL
   [ONCE_REWRITE_TAC[DIST_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIST_LADD_0]);;

let NADD_ALTMUL = prove
 (`!x y. ?A B. !n. dist(n * fn x (fn y n),fn x n * fn y n) <= A * n + B`,
  REPEAT GEN_TAC THEN X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
  MP_TAC(SPEC `y:nadd` NADD_BOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (X_CHOOSE_TAC `L:num`)) THEN
  MAP_EVERY EXISTS_TAC [`B * (1 + M)`; `B * L`] THEN GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [MULT_SYM] THEN
  MATCH_MP_TAC LE_TRANS THEN  EXISTS_TAC `B * (n + fn y n)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[MULT_CLAUSES; GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
  ASM_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC; LE_MULT_LCANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the equivalence relation and proof that it *is* one.        *)
(* ------------------------------------------------------------------------- *)

override_interface ("===",`(nadd_eq):nadd->nadd->bool`);;

let nadd_eq = new_definition
  `x === y <=> ?B. !n. dist(fn x n,fn y n) <= B`;;

let NADD_EQ_REFL = prove
 (`!x. x === x`,
  GEN_TAC THEN REWRITE_TAC[nadd_eq; DIST_REFL; LE_0]);;

let NADD_EQ_SYM = prove
 (`!x y. x === y <=> y === x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [DIST_SYM] THEN REFL_TAC);;

let NADD_EQ_TRANS = prove
 (`!x y z. x === y /\ y === z ==> x === z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `B1:num`) (X_CHOOSE_TAC `B2:num`)) THEN
  EXISTS_TAC `B1 + B2` THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC (LE_IMP DIST_TRIANGLE) THEN EXISTS_TAC `fn y n` THEN
  MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Injection of the natural numbers.                                         *)
(* ------------------------------------------------------------------------- *)

override_interface ("&",`nadd_of_num:num->nadd`);;

let nadd_of_num = new_definition
  `&k = afn(\n. k * n)`;;

let NADD_OF_NUM = prove
 (`!k. fn(&k) = \n. k * n`,
  REWRITE_TAC[nadd_of_num; GSYM nadd_rep; is_nadd] THEN
  REWRITE_TAC[DIST_REFL; LE_0; MULT_AC]);;

let NADD_OF_NUM_WELLDEF = prove
 (`!m n. (m = n) ==> &m === &n`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC NADD_EQ_REFL);;

let NADD_OF_NUM_EQ = prove
 (`!m n. (&m === &n) <=> (m = n)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[NADD_OF_NUM_WELLDEF] THEN
  REWRITE_TAC[nadd_eq; NADD_OF_NUM] THEN
  REWRITE_TAC[GSYM DIST_RMUL; BOUNDS_LINEAR_0; DIST_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Definition of (reflexive) ordering and the only special property needed.  *)
(* ------------------------------------------------------------------------- *)

override_interface ("<<=",`nadd_le:nadd->nadd->bool`);;

let nadd_le = new_definition
  `x <<= y <=> ?B. !n. fn x n <= fn y n + B`;;

let NADD_LE_WELLDEF_LEMMA = prove
 (`!x x' y y'. x === x' /\ y === y' /\ x <<= y ==> x' <<= y'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq; nadd_le] THEN
  REWRITE_TAC[DIST_LE_CASES; FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B1:num`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B2:num`) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN
  EXISTS_TAC `(B2 + B) + B1` THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MATCH_MP_TAC o LE_IMP o CONJUNCT2) THEN
  REWRITE_TAC[ADD_ASSOC; LE_ADD_RCANCEL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o LE_IMP) THEN ASM_REWRITE_TAC[LE_ADD_RCANCEL]);;

let NADD_LE_WELLDEF = prove
 (`!x x' y y'. x === x' /\ y === y' ==> (x <<= y <=> x' <<= y')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC NADD_LE_WELLDEF_LEMMA THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`x:nadd`; `y:nadd`];
    MAP_EVERY EXISTS_TAC [`x':nadd`; `y':nadd`] THEN
    ONCE_REWRITE_TAC[NADD_EQ_SYM]] THEN
  ASM_REWRITE_TAC[]);;

let NADD_LE_REFL = prove
 (`!x. x <<= x`,
  REWRITE_TAC[nadd_le; LE_ADD]);;

let NADD_LE_TRANS = prove
 (`!x y z. x <<= y /\ y <<= z ==> x <<= z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_le] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B1:num`) MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `B2:num`) THEN
  EXISTS_TAC `B2 + B1` THEN GEN_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o LE_IMP) THEN
  ASM_REWRITE_TAC[ADD_ASSOC; LE_ADD_RCANCEL]);;

let NADD_LE_ANTISYM = prove
 (`!x y. x <<= y /\ y <<= x <=> (x === y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_le; nadd_eq; DIST_LE_CASES] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B1:num`)
      (X_CHOOSE_TAC `B2:num`)) THEN
    EXISTS_TAC `B1 + B2` THEN GEN_TAC THEN CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o LE_IMP) THEN
    ASM_REWRITE_TAC[ADD_ASSOC; LE_ADD_RCANCEL; LE_ADD; LE_ADDR];
    DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN
    CONJ_TAC THEN EXISTS_TAC `B:num` THEN ASM_REWRITE_TAC[]]);;

let NADD_LE_TOTAL_LEMMA = prove
 (`!x y. ~(x <<= y) ==> !B. ?n. ~(n = 0) /\ fn y n + B < fn x n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_le; NOT_FORALL_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[NOT_LE] THEN DISCH_TAC THEN GEN_TAC THEN
  POP_ASSUM(X_CHOOSE_TAC `n:num` o SPEC `B + fn x 0`) THEN
  EXISTS_TAC `n:num` THEN POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[NOT_LT; ADD_ASSOC; LE_ADDR] THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LT] THEN
  DISCH_THEN(MATCH_MP_TAC o LE_IMP) THEN REWRITE_TAC[ADD_ASSOC; LE_ADD]);;

let NADD_LE_TOTAL = prove
 (`!x y. x <<= y \/ y <<= x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [TAUT `a <=> ~ ~ a`] THEN
  X_CHOOSE_TAC `B1:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
  X_CHOOSE_TAC `B2:num` (SPEC `y:nadd` NADD_CAUCHY) THEN
  PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o
    map (MATCH_MP NADD_LE_TOTAL_LEMMA) o CONJUNCTS) THEN
  REWRITE_TAC[AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o SPEC `B1 + B2`) THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `n:num` MP_TAC)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (ITAUT `(~a /\ b) /\ (~c /\ d) ==> ~(c \/ ~b) /\ ~(a \/ ~d)`)) THEN
  REWRITE_TAC[NOT_LT; GSYM LE_MULT_LCANCEL] THEN REWRITE_TAC[NOT_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LT_ADD2) THEN REWRITE_TAC[NOT_LT] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
  ONCE_REWRITE_TAC[AC ADD_AC
    `(a + b + c) + (d + e + f) = (d + b + e) + (a + c + f)`] THEN
  MATCH_MP_TAC LE_ADD2 THEN REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MULT_SYM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIST_LE_CASES]) THEN ASM_REWRITE_TAC[]);;

let NADD_ARCH = prove
 (`!x. ?n. x <<= &n`,
  REWRITE_TAC[nadd_le; NADD_OF_NUM; NADD_BOUND]);;

let NADD_OF_NUM_LE = prove
 (`!m n. (&m <<= &n) <=> m <= n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_le; NADD_OF_NUM] THEN
  REWRITE_TAC[BOUNDS_LINEAR]);;

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)

override_interface ("++",`nadd_add:nadd->nadd->nadd`);;

let nadd_add = new_definition
  `x ++ y = afn(\n. fn x n + fn y n)`;;

let NADD_ADD = prove
 (`!x y. fn(x ++ y) = \n. fn x n + fn y n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nadd_add; GSYM nadd_rep; is_nadd] THEN
  X_CHOOSE_TAC `B1:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
  X_CHOOSE_TAC `B2:num` (SPEC `y:nadd` NADD_CAUCHY) THEN
  EXISTS_TAC `B1 + B2` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC (LE_IMP DIST_ADD2) THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
  MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[]);;

let NADD_ADD_WELLDEF = prove
 (`!x x' y y'. x === x' /\ y === y' ==> (x ++ y === x' ++ y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq; NADD_ADD] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `B1:num`) (X_CHOOSE_TAC `B2:num`)) THEN
  EXISTS_TAC `B1 + B2` THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC (LE_IMP DIST_ADD2) THEN
  MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties of addition.                                             *)
(* ------------------------------------------------------------------------- *)

let NADD_ADD_SYM = prove
 (`!x y. (x ++ y) === (y ++ x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_add] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  REWRITE_TAC[NADD_EQ_REFL]);;

let NADD_ADD_ASSOC = prove
 (`!x y z. (x ++ (y ++ z)) === ((x ++ y) ++ z)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[nadd_add] THEN
  REWRITE_TAC[NADD_ADD; ADD_ASSOC; NADD_EQ_REFL]);;

let NADD_ADD_LID = prove
 (`!x. (&0 ++ x) === x`,
  GEN_TAC THEN REWRITE_TAC[nadd_eq; NADD_ADD; NADD_OF_NUM] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; DIST_REFL; LE_0]);;

let NADD_ADD_LCANCEL = prove
 (`!x y z. (x ++ y) === (x ++ z) ==> y === z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq; NADD_ADD; DIST_LADD]);;

let NADD_LE_ADD = prove
 (`!x y. x <<= (x ++ y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_le; NADD_ADD] THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; LE_ADD]);;

let NADD_LE_EXISTS = prove
 (`!x y. x <<= y ==> ?d. y === x ++ d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_le] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` MP_TAC) THEN
  REWRITE_TAC[LE_EXISTS; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->num` (ASSUME_TAC o GSYM)) THEN
  EXISTS_TAC `afn d` THEN REWRITE_TAC[nadd_eq; NADD_ADD] THEN
  EXISTS_TAC `B:num` THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN `fn(afn d) = d` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM nadd_rep; is_nadd] THEN
    X_CHOOSE_TAC `B1:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
    X_CHOOSE_TAC `B2:num` (SPEC `y:nadd` NADD_CAUCHY) THEN
    EXISTS_TAC `B1 + (B2 + B)` THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC(LE_IMP DIST_ADD2_REV) THEN
    MAP_EVERY EXISTS_TAC [`m * fn x n`; `n * fn x m`] THEN
    ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    ASM_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [LEFT_ADD_DISTRIB] THEN
    MATCH_MP_TAC(LE_IMP DIST_ADD2) THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
    GEN_REWRITE_TAC RAND_CONV [ADD_SYM] THEN MATCH_MP_TAC LE_ADD2 THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    REWRITE_TAC[GSYM DIST_LMUL; DIST_ADDBOUND; LE_MULT_LCANCEL];
    ASM_REWRITE_TAC[DIST_RADD_0; LE_REFL]]);;

let NADD_OF_NUM_ADD = prove
 (`!m n. &m ++ &n === &(m + n)`,
  REWRITE_TAC[nadd_eq; NADD_OF_NUM; NADD_ADD] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; DIST_REFL; LE_0]);;

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

override_interface ("**",`nadd_mul:nadd->nadd->nadd`);;

let nadd_mul = new_definition
  `x ** y = afn(\n. fn x (fn y n))`;;

let NADD_MUL = prove
 (`!x y. fn(x ** y) = \n. fn x (fn y n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nadd_mul; GSYM nadd_rep; is_nadd] THEN
  X_CHOOSE_TAC `B:num` (SPEC `y:nadd` NADD_CAUCHY) THEN
  X_CHOOSE_TAC `C:num` (SPEC `x:nadd` NADD_DIST) THEN
  X_CHOOSE_TAC `D:num` (SPEC `x:nadd` NADD_MULTIPLICATIVE) THEN
  MATCH_MP_TAC BOUNDS_NOTZERO THEN
  REWRITE_TAC[MULT_CLAUSES; DIST_REFL] THEN
  MAP_EVERY EXISTS_TAC [`D + C * B`; `D + D`] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(D * m + D) + (D * n + D) + C * B * (m + n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC (LE_IMP DIST_TRIANGLE) THEN
    EXISTS_TAC `fn x (m * fn y n)` THEN
    MATCH_MP_TAC LE_ADD2 THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC (LE_IMP DIST_TRIANGLE) THEN
    EXISTS_TAC `fn x (n * fn y m)` THEN
    MATCH_MP_TAC LE_ADD2 THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `C * dist(m * fn y n,n * fn y m)` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    MATCH_MP_TAC EQ_IMP_LE THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_ASSOC; ADD_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Properties of multiplication.                                             *)
(* ------------------------------------------------------------------------- *)

let NADD_MUL_SYM = prove
 (`!x y. (x ** y) === (y ** x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq; NADD_MUL] THEN
  X_CHOOSE_THEN `A1:num` MP_TAC (SPECL [`x:nadd`; `y:nadd`] NADD_ALTMUL) THEN
  DISCH_THEN(X_CHOOSE_TAC `B1:num`) THEN
  X_CHOOSE_THEN `A2:num` MP_TAC (SPECL [`y:nadd`; `x:nadd`] NADD_ALTMUL) THEN
  DISCH_THEN(X_CHOOSE_TAC `B2:num`) THEN REWRITE_TAC[BOUNDS_DIVIDED] THEN
  REWRITE_TAC[DIST_LMUL] THEN MAP_EVERY EXISTS_TAC [`A1 + A2`; `B1 + B2`] THEN
  GEN_TAC THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
  ONCE_REWRITE_TAC[AC ADD_AC `(a + b) + (c + d) = (a + c) + (b + d)`] THEN
  MATCH_MP_TAC (LE_IMP DIST_TRIANGLE) THEN
  EXISTS_TAC `fn x n * fn y n` THEN
  MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC [DIST_SYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [MULT_SYM] THEN
  ASM_REWRITE_TAC[]);;

let NADD_MUL_ASSOC = prove
 (`!x y z. (x ** (y ** z)) === ((x ** y) ** z)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[nadd_mul] THEN
  REWRITE_TAC[NADD_MUL; NADD_EQ_REFL]);;

let NADD_MUL_LID = prove
 (`!x. (&1 ** x) === x`,
  REWRITE_TAC[NADD_OF_NUM; nadd_mul; MULT_CLAUSES] THEN
  REWRITE_TAC[nadd_abs; NADD_EQ_REFL; ETA_AX]);;

let NADD_LDISTRIB = prove
 (`!x y z. x ** (y ++ z) === (x ** y) ++ (x ** z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq] THEN
  REWRITE_TAC[NADD_ADD; NADD_MUL] THEN
  X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_ADDITIVE) THEN
  EXISTS_TAC `B:num` THEN ASM_REWRITE_TAC[]);;

let NADD_MUL_WELLDEF_LEMMA = prove
 (`!x y y'. y === y' ==> (x ** y) === (x ** y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq; NADD_MUL] THEN
  DISCH_THEN(X_CHOOSE_TAC `B1:num`) THEN
  X_CHOOSE_TAC `B2:num` (SPEC `x:nadd` NADD_DIST) THEN
  EXISTS_TAC `B2 * B1` THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `B2 * dist(fn y n,fn y' n)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL]);;

let NADD_MUL_WELLDEF = prove
 (`!x x' y y'. x === x' /\ y === y'
               ==> (x ** y) === (x' ** y')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NADD_EQ_TRANS THEN
  EXISTS_TAC `x' ** y` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NADD_EQ_TRANS THEN EXISTS_TAC `y ** x'` THEN
    REWRITE_TAC[NADD_MUL_SYM] THEN MATCH_MP_TAC NADD_EQ_TRANS THEN
    EXISTS_TAC `y ** x` THEN REWRITE_TAC[NADD_MUL_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC NADD_MUL_WELLDEF_LEMMA THEN ASM_REWRITE_TAC[]);;

let NADD_OF_NUM_MUL = prove
 (`!m n. &m ** &n === &(m * n)`,
  REWRITE_TAC[nadd_eq; NADD_OF_NUM; NADD_MUL] THEN
  REWRITE_TAC[MULT_ASSOC; DIST_REFL; LE_0]);;

(* ------------------------------------------------------------------------- *)
(* A few handy lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let NADD_LE_0 = prove
 (`!x. &0 <<= x`,
  GEN_TAC THEN
  REWRITE_TAC[nadd_le; NADD_OF_NUM; MULT_CLAUSES; LE_0]);;

let NADD_EQ_IMP_LE = prove
 (`!x y. x === y ==> x <<= y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nadd_eq; nadd_le; DIST_LE_CASES] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN EXISTS_TAC `B:num` THEN
  ASM_REWRITE_TAC[]);;

let NADD_LE_LMUL = prove
 (`!x y z. y <<= z ==> (x ** y) <<= (x ** z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `d:nadd` o MATCH_MP NADD_LE_EXISTS) THEN
  MATCH_MP_TAC NADD_LE_TRANS THEN
  EXISTS_TAC `x ** y ++ x ** d` THEN REWRITE_TAC[NADD_LE_ADD] THEN
  MATCH_MP_TAC NADD_EQ_IMP_LE THEN
  MATCH_MP_TAC NADD_EQ_TRANS THEN
  EXISTS_TAC `x ** (y ++ d)` THEN
  ONCE_REWRITE_TAC[NADD_EQ_SYM] THEN
  REWRITE_TAC[NADD_LDISTRIB] THEN
  MATCH_MP_TAC NADD_MUL_WELLDEF THEN
  ASM_REWRITE_TAC[NADD_EQ_REFL]);;

let NADD_LE_RMUL = prove
 (`!x y z. x <<= y ==> (x ** z) <<= (y ** z)`,
  MESON_TAC[NADD_LE_LMUL; NADD_LE_WELLDEF; NADD_MUL_SYM]);;

let NADD_LE_RADD = prove
 (`!x y z. x ++ z <<= y ++ z <=> x <<= y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_le; NADD_ADD] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 BINDER_CONV o RAND_CONV)
    [ADD_SYM] THEN
  REWRITE_TAC[ADD_ASSOC; LE_ADD_RCANCEL] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 BINDER_CONV o RAND_CONV)
    [ADD_SYM] THEN REFL_TAC);;

let NADD_LE_LADD = prove
 (`!x y z. x ++ y <<= x ++ z <=> y <<= z`,
  MESON_TAC[NADD_LE_RADD; NADD_ADD_SYM; NADD_LE_WELLDEF]);;

let NADD_RDISTRIB = prove
 (`!x y z. (x ++ y) ** z === x ** z ++ y ** z`,
  MESON_TAC[NADD_LDISTRIB; NADD_MUL_SYM; NADD_ADD_WELLDEF;
    NADD_EQ_TRANS; NADD_EQ_REFL; NADD_EQ_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The Archimedean property in a more useful form.                           *)
(* ------------------------------------------------------------------------- *)

let NADD_ARCH_MULT = prove
 (`!x k. ~(x === &0) ==> ?N. &k <<= &N ** x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nadd_eq; nadd_le; NOT_EXISTS_THM] THEN
  X_CHOOSE_TAC `B:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
  DISCH_THEN(MP_TAC o SPEC `B + k`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NADD_OF_NUM] THEN
  REWRITE_TAC[MULT_CLAUSES; DIST_RZERO; NOT_LE] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MAP_EVERY EXISTS_TAC [`N:num`; `B * N`] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[NADD_MUL; NADD_OF_NUM] THEN
  MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_ADD_RCANCEL)))) THEN
  EXISTS_TAC `B * i` THEN
  REWRITE_TAC[GSYM ADD_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `i * fn x N` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIST_LE_CASES]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN
  GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
  MATCH_MP_TAC LT_IMP_LE THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  FIRST_ASSUM ACCEPT_TAC);;

let NADD_ARCH_ZERO = prove
 (`!x k. (!n. &n ** x <<= k) ==> (x === &0)`,
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  X_CHOOSE_TAC `p:num` (SPEC `k:nadd` NADD_ARCH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NADD_ARCH_MULT) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num` o SPEC `p:num`) THEN
  EXISTS_TAC `N + 1` THEN DISCH_TAC THEN UNDISCH_TAC `~(x === &0)` THEN
  REWRITE_TAC[GSYM NADD_LE_ANTISYM; NADD_LE_0] THEN
  MATCH_MP_TAC(GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL NADD_LE_RADD)))) THEN
  EXISTS_TAC `&N ** x` THEN MATCH_MP_TAC NADD_LE_TRANS THEN
  EXISTS_TAC `k:nadd` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&(N + 1) ** x === x ++ &N ** x` MP_TAC THENL
     [ONCE_REWRITE_TAC[ADD_SYM] THEN
      MATCH_MP_TAC NADD_EQ_TRANS THEN
      EXISTS_TAC `&1 ** x ++ &N ** x` THEN CONJ_TAC THENL
       [MATCH_MP_TAC NADD_EQ_TRANS THEN
        EXISTS_TAC `(&1 ++ &N) ** x` THEN CONJ_TAC THENL
         [MESON_TAC[NADD_OF_NUM_ADD; NADD_MUL_WELLDEF; NADD_EQ_REFL;
            NADD_EQ_SYM];
          MESON_TAC[NADD_RDISTRIB; NADD_MUL_SYM; NADD_EQ_SYM; NADD_EQ_TRANS]];
        MESON_TAC[NADD_ADD_WELLDEF; NADD_EQ_REFL; NADD_MUL_LID]];
      ASM_MESON_TAC[NADD_LE_WELLDEF; NADD_EQ_REFL]];
    ASM_MESON_TAC[NADD_LE_TRANS; NADD_LE_WELLDEF; NADD_EQ_REFL;
      NADD_ADD_LID]]);;

let NADD_ARCH_LEMMA = prove
 (`!x y z. (!n. &n ** x <<= &n ** y ++ z) ==> x <<= y`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`x:nadd`; `y:nadd`] NADD_LE_TOTAL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `d:nadd` o MATCH_MP NADD_LE_EXISTS) THEN
  MATCH_MP_TAC NADD_EQ_IMP_LE THEN
  MATCH_MP_TAC NADD_EQ_TRANS THEN EXISTS_TAC `y ++ d` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NADD_EQ_TRANS THEN EXISTS_TAC `y ++ &0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NADD_ADD_WELLDEF THEN REWRITE_TAC[NADD_EQ_REFL] THEN
    MATCH_MP_TAC NADD_ARCH_ZERO THEN EXISTS_TAC `z:nadd` THEN
    ASM_MESON_TAC[NADD_MUL_WELLDEF; NADD_LE_WELLDEF; NADD_LDISTRIB;
      NADD_LE_LADD; NADD_EQ_REFL];
    ASM_MESON_TAC[NADD_ADD_LID; NADD_ADD_WELLDEF; NADD_EQ_TRANS;
      NADD_ADD_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness.                                                             *)
(* ------------------------------------------------------------------------- *)

let NADD_COMPLETE = prove
 (`!P. (?x. P x) /\ (?M. !x. P x ==> x <<= M) ==>
       ?M. (!x. P x ==> x <<= M) /\
           !M'. (!x. P x ==> x <<= M') ==> M <<= M'`,
  GEN_TAC THEN DISCH_THEN
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:nadd`) (X_CHOOSE_TAC `m:nadd`)) THEN
  SUBGOAL_THEN
    `!n. ?r. (?x. P x /\ &r <<= &n ** x) /\
             !r'. (?x. P x /\ &r' <<= &n ** x) ==> r' <= r` MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM num_MAX] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`0`; `a:nadd`] THEN ASM_REWRITE_TAC[NADD_LE_0];
      X_CHOOSE_TAC `N:num` (SPEC `m:nadd` NADD_ARCH) THEN
      EXISTS_TAC `n * N` THEN X_GEN_TAC `p:num` THEN
      DISCH_THEN(X_CHOOSE_THEN `w:nadd` STRIP_ASSUME_TAC) THEN
      ONCE_REWRITE_TAC[GSYM NADD_OF_NUM_LE] THEN
      MATCH_MP_TAC NADD_LE_TRANS THEN EXISTS_TAC `&n ** w` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NADD_LE_TRANS THEN
      EXISTS_TAC `&n ** &N` THEN CONJ_TAC THENL
       [MATCH_MP_TAC NADD_LE_LMUL THEN MATCH_MP_TAC NADD_LE_TRANS THEN
        EXISTS_TAC `m:nadd` THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC NADD_EQ_IMP_LE THEN
        MATCH_ACCEPT_TAC NADD_OF_NUM_MUL]];
    ONCE_REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num->num`
     (fun th -> let th1,th2 = CONJ_PAIR(SPEC `n:num` th) in
                MAP_EVERY (MP_TAC o GEN `n:num`) [th1; th2])) THEN
    DISCH_THEN(MP_TAC o GEN `n:num` o SPECL [`n:num`; `SUC(r(n:num))`]) THEN
    REWRITE_TAC[LE_SUC_LT; LT_REFL; NOT_EXISTS_THM] THEN
    DISCH_THEN(ASSUME_TAC o GENL [`n:num`; `x:nadd`] o MATCH_MP
     (ITAUT `(a \/ b) /\ ~(c /\ b) ==> c ==> a`) o CONJ
      (SPECL [`&n ** x`; `&(SUC(r(n:num)))`] NADD_LE_TOTAL) o SPEC_ALL) THEN
    DISCH_TAC] THEN
  SUBGOAL_THEN `!n i. i * r(n) <= n * r(i) + n` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `x:nadd` STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ONCE_REWRITE_TAC[GSYM NADD_OF_NUM_LE] THEN
    MATCH_MP_TAC NADD_LE_TRANS THEN
    EXISTS_TAC `&i ** &n ** x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NADD_LE_TRANS THEN
      EXISTS_TAC `&i ** &(r(n:num))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC NADD_EQ_IMP_LE THEN
        ONCE_REWRITE_TAC[NADD_EQ_SYM] THEN MATCH_ACCEPT_TAC NADD_OF_NUM_MUL;
        MATCH_MP_TAC NADD_LE_LMUL THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC NADD_LE_TRANS THEN
      EXISTS_TAC `&n ** &(SUC(r(i:num)))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC NADD_LE_TRANS THEN EXISTS_TAC `&n ** &i ** x` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC NADD_EQ_IMP_LE THEN
          MATCH_MP_TAC NADD_EQ_TRANS THEN
          EXISTS_TAC `(&i ** &n) ** x` THEN
          REWRITE_TAC[NADD_MUL_ASSOC] THEN
          MATCH_MP_TAC NADD_EQ_TRANS THEN
          EXISTS_TAC `(&n ** &i) ** x` THEN
          REWRITE_TAC[ONCE_REWRITE_RULE[NADD_EQ_SYM] NADD_MUL_ASSOC] THEN
          MATCH_MP_TAC NADD_MUL_WELLDEF THEN
          REWRITE_TAC[NADD_MUL_SYM; NADD_EQ_REFL];
          MATCH_MP_TAC NADD_LE_LMUL THEN
          FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM MULT_SUC] THEN
        MATCH_MP_TAC NADD_EQ_IMP_LE THEN
        REWRITE_TAC[NADD_OF_NUM_MUL]]]; ALL_TAC] THEN
  EXISTS_TAC `afn r` THEN SUBGOAL_THEN `fn(afn r) = r` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM nadd_rep] THEN REWRITE_TAC[is_nadd; DIST_LE_CASES] THEN
    EXISTS_TAC `1` THEN REWRITE_TAC[MULT_CLAUSES] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 BINDER_CONV o
      funpow 2 RAND_CONV) [ADD_SYM] THEN
    REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:num`; `n:num`] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n * r(i:num) + n` THEN
    ASM_REWRITE_TAC[ADD_ASSOC; LE_ADD]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:nadd` THEN DISCH_TAC THEN
    MATCH_MP_TAC NADD_ARCH_LEMMA THEN
    EXISTS_TAC `&2` THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC NADD_LE_TRANS THEN
    EXISTS_TAC `&(SUC(r(n:num)))` THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[nadd_le; NADD_ADD; NADD_MUL; NADD_OF_NUM] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD1; RIGHT_ADD_DISTRIB] THEN
      REWRITE_TAC[MULT_2; MULT_CLAUSES; ADD_ASSOC; LE_ADD_RCANCEL] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      ONCE_REWRITE_TAC[BOUNDS_IGNORE] THEN
      MAP_EVERY EXISTS_TAC [`0`; `n:num`] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n * r(i:num) + n` THEN
      ASM_REWRITE_TAC[LE_ADD_LCANCEL; ADD_CLAUSES]];
    X_GEN_TAC `z:nadd` THEN DISCH_TAC THEN
    MATCH_MP_TAC NADD_ARCH_LEMMA THEN EXISTS_TAC `&1` THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC NADD_LE_TRANS THEN
    EXISTS_TAC `&(r(n:num)) ++ &1` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[nadd_le; NADD_ADD; NADD_MUL; NADD_OF_NUM] THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
      GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [MULT_SYM] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[NADD_LE_RADD] THEN
      FIRST_ASSUM(X_CHOOSE_THEN `x:nadd` MP_TAC o SPEC `n:num`) THEN
      DISCH_THEN STRIP_ASSUME_TAC THEN
      MATCH_MP_TAC NADD_LE_TRANS THEN EXISTS_TAC `&n ** x` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NADD_LE_LMUL THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* A bit more on nearly-multiplicative functions.                            *)
(* ------------------------------------------------------------------------- *)

let NADD_UBOUND = prove
 (`!x. ?B N. !n. N <= n ==> fn x n <= B * n`,
  GEN_TAC THEN X_CHOOSE_THEN `A1:num`
    (X_CHOOSE_TAC `A2:num`) (SPEC `x:nadd` NADD_BOUND) THEN
  EXISTS_TAC `A1 + A2` THEN EXISTS_TAC `1` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `A1 * n + A2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; LE_ADD_LCANCEL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(el 3 (CONJUNCTS MULT_CLAUSES))] THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL]);;

let NADD_NONZERO = prove
 (`!x. ~(x === &0) ==> ?N. !n. N <= n ==> ~(fn x n = 0)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NADD_ARCH_MULT) THEN
  DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[nadd_le; NADD_MUL; NADD_OF_NUM; MULT_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:num` (X_CHOOSE_TAC `A2:num`)) THEN
  EXISTS_TAC `A2 + 1` THEN X_GEN_TAC `n:num` THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_LE; GSYM LE_SUC_LT; ADD1] THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let NADD_LBOUND = prove
 (`!x. ~(x === &0) ==> ?A N. !n. N <= n ==> n <= A * fn x n`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `N:num` o MATCH_MP NADD_NONZERO) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NADD_ARCH_MULT) THEN
  DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[nadd_le; NADD_MUL; NADD_OF_NUM; MULT_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:num` (X_CHOOSE_TAC `A2:num`)) THEN
  EXISTS_TAC `A1 + A2` THEN EXISTS_TAC `N:num` THEN GEN_TAC THEN
  DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `A1 * fn x n + A2` THEN
  ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; LE_ADD_LCANCEL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(el 3 (CONJUNCTS MULT_CLAUSES))] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
  REWRITE_TAC[GSYM(REWRITE_CONV[ARITH_SUC] `SUC 0`)] THEN
  ASM_REWRITE_TAC[GSYM NOT_LT; LT]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary function for the multiplicative inverse.                        *)
(* ------------------------------------------------------------------------- *)

let nadd_rinv = new_definition
 `nadd_rinv(x) = \n. (n * n) DIV (fn x n)`;;

let NADD_MUL_LINV_LEMMA0 = prove
 (`!x. ~(x === &0) ==> ?A B. !n. nadd_rinv x n <= A * n + B`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[BOUNDS_IGNORE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NADD_LBOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:num` (X_CHOOSE_TAC `N:num`)) THEN
  MAP_EVERY EXISTS_TAC [`A:num`; `0`; `SUC N`] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
  MP_TAC(SPECL [`nadd_rinv x n`; `A * n`; `n:num`] LE_MULT_RCANCEL) THEN
  UNDISCH_TAC `SUC N <= n` THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[LE; NOT_SUC] THEN DISCH_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `nadd_rinv x n * A * fn x n` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `SUC N` THEN ASM_REWRITE_TAC[LE; LE_REFL];
    GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN ASM_CASES_TAC `fn x n = 0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; LE_0; nadd_rinv] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION) THEN
    DISCH_THEN(fun t -> GEN_REWRITE_TAC RAND_CONV [CONJUNCT1(SPEC_ALL t)]) THEN
    GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN REWRITE_TAC[LE_ADD]]);;

let NADD_MUL_LINV_LEMMA1 = prove
 (`!x n. ~(fn x n = 0) ==> dist(fn x n * nadd_rinv(x) n, n * n) <= fn x n`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DIVISION) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC o SPEC `n * n`) THEN
  REWRITE_TAC[nadd_rinv] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [MULT_SYM] THEN
  REWRITE_TAC[DIST_RADD_0] THEN MATCH_MP_TAC LT_IMP_LE THEN
  FIRST_ASSUM MATCH_ACCEPT_TAC);;

let NADD_MUL_LINV_LEMMA2 = prove
 (`!x. ~(x === &0) ==> ?N. !n. N <= n ==>
         dist(fn x n * nadd_rinv(x) n, n * n) <= fn x n`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NADD_NONZERO) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NADD_MUL_LINV_LEMMA1 THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let NADD_MUL_LINV_LEMMA3 = prove
 (`!x. ~(x === &0) ==> ?N. !m n. N <= n ==>
        dist(m * fn x m * fn x n * nadd_rinv(x) n,
             m * fn x m * n * n) <= m * fn x m * fn x n`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NADD_MUL_LINV_LEMMA2) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DIST_LMUL; MULT_ASSOC] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let NADD_MUL_LINV_LEMMA4 = prove
 (`!x. ~(x === &0) ==> ?N. !m n. N <= m /\ N <= n ==>
        (fn x m * fn x n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
          (m * n) * dist(m * fn x n,n * fn x m) + (fn x m * fn x n) * (m + n)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NADD_MUL_LINV_LEMMA3) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIST_LMUL; LEFT_ADD_DISTRIB] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [DIST_SYM] THEN
  MATCH_MP_TAC DIST_TRIANGLES_LE THEN CONJ_TAC THENL
   [ANTE_RES_THEN(MP_TAC o SPEC `m:num`) (ASSUME `N <= n`);
    ANTE_RES_THEN(MP_TAC o SPEC `n:num`) (ASSUME `N <= m`)] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[MULT_AC]);;

let NADD_MUL_LINV_LEMMA5 = prove
 (`!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        (fn x m * fn x n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
        B * (m * n) * (m + n)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NADD_MUL_LINV_LEMMA4) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  X_CHOOSE_TAC `B1:num` (SPEC `x:nadd` NADD_CAUCHY) THEN
  X_CHOOSE_THEN `B2:num` (X_CHOOSE_TAC `N2:num`)
    (SPEC `x:nadd` NADD_UBOUND) THEN
  EXISTS_TAC `B1 + B2 * B2` THEN EXISTS_TAC `N1 + N2` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(m * n) * dist(m * fn x n,n * fn x m) +
              (fn x m * fn x n) * (m + n)` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N1 + N2` THEN
    ASM_REWRITE_TAC[LE_ADD; LE_ADDR];
    REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN MATCH_MP_TAC LE_ADD2] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM MULT_ASSOC] THEN
    GEN_REWRITE_TAC (funpow 2 RAND_CONV) [MULT_SYM] THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ONCE_REWRITE_TAC[AC MULT_AC
      `(a * b) * (c * d) * e = ((a * c) * (b * d)) * e`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N1 + N2` THEN
    ASM_REWRITE_TAC[LE_ADD; LE_ADDR]]);;

let NADD_MUL_LINV_LEMMA6 = prove
 (`!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        (m * n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=
        B * (m * n) * (m + n)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NADD_MUL_LINV_LEMMA5) THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:num` (X_CHOOSE_TAC `N1:num`)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NADD_LBOUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:num` (X_CHOOSE_TAC `N2:num`)) THEN
  EXISTS_TAC `B1 * B2 * B2` THEN EXISTS_TAC `N1 + N2` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(B2 * B2) * (fn x m * fn x n) *
              dist (m * nadd_rinv x n,n * nadd_rinv x m)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    ONCE_REWRITE_TAC[AC MULT_AC `((a * b) * c) * d = (a * c) * (b * d)`] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC;
    ONCE_REWRITE_TAC[AC MULT_AC
      `(a * b * c) * (d * e) * f = (b * c) * (a * (d * e) * f)`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N1 + N2` THEN
  ASM_REWRITE_TAC[LE_ADD; LE_ADDR]);;

let NADD_MUL_LINV_LEMMA7 = prove
 (`!x. ~(x === &0) ==> ?B N. !m n. N <= m /\ N <= n ==>
        dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= B * (m + n)`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NADD_MUL_LINV_LEMMA6) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` (X_CHOOSE_TAC `N:num`)) THEN
  MAP_EVERY EXISTS_TAC [`B:num`; `N + 1`] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `N <= m /\ N <= n` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N + 1` THEN
    ASM_REWRITE_TAC[LE_ADD];
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    ONCE_REWRITE_TAC[AC MULT_AC `a * b * c = b * a * c`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN
    DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ACCEPT_TAC) THEN
    CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
    ONCE_REWRITE_TAC[GSYM(CONJUNCT1 LE)] THEN
    REWRITE_TAC[NOT_LE; GSYM LE_SUC_LT] THEN
    REWRITE_TAC[EQT_ELIM(REWRITE_CONV[ARITH] `SUC 0 = 1 * 1`)] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `N + 1` THEN
    ASM_REWRITE_TAC[LE_ADDR]]);;

let NADD_MUL_LINV_LEMMA7a = prove
 (`!x. ~(x === &0) ==> !N. ?A B. !m n. m <= N ==>
        dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= A * n + B`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NADD_MUL_LINV_LEMMA0) THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:num` (X_CHOOSE_TAC `B0:num`)) THEN
  INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`nadd_rinv x 0`; `0`] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MULT_CLAUSES; DIST_LZERO; ADD_CLAUSES] THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN MATCH_ACCEPT_TAC LE_REFL;
    FIRST_ASSUM(X_CHOOSE_THEN `A:num` (X_CHOOSE_TAC `B:num`)) THEN
    EXISTS_TAC `A + (nadd_rinv(x)(SUC N) + SUC N * A0)` THEN
    EXISTS_TAC `SUC N * B0 + B` THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[LE] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `SUC N * nadd_rinv x n + n * nadd_rinv x (SUC N)` THEN
      REWRITE_TAC[DIST_ADDBOUND] THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
      ONCE_REWRITE_TAC[AC ADD_AC
        `(a + b + c) + d + e = (c + d) + (b + a + e)`] THEN
      MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL];
        GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
        MATCH_ACCEPT_TAC LE_ADD];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `A * n + B` THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[ADD_ASSOC; LE_ADD_RCANCEL] THEN
        REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC; LE_ADD]]]]);;

let NADD_MUL_LINV_LEMMA8 = prove
 (`!x. ~(x === &0) ==>
        ?B. !m n. dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= B * (m + n)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NADD_MUL_LINV_LEMMA7) THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:num` (X_CHOOSE_TAC `N:num`)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `N:num` o MATCH_MP NADD_MUL_LINV_LEMMA7a) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:num` (X_CHOOSE_TAC `B:num`)) THEN
  MATCH_MP_TAC BOUNDS_NOTZERO THEN REWRITE_TAC[DIST_REFL] THEN
  EXISTS_TAC `A + B0` THEN EXISTS_TAC `B:num` THEN REPEAT GEN_TAC THEN
  DISJ_CASES_THEN2 ASSUME_TAC MP_TAC (SPECL [`N:num`; `m:num`] LE_CASES) THENL
   [DISJ_CASES_THEN2 ASSUME_TAC MP_TAC (SPECL [`N:num`; `n:num`] LE_CASES)
    THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `B0 * (m + n)` THEN CONJ_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC (RAND_CONV o funpow 2 LAND_CONV) [ADD_SYM] THEN
        REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC; LE_ADD]];
      DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `A * m + B` THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[LE_ADD_RCANCEL] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC;
        LE_ADD]];
    DISCH_THEN(ANTE_RES_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `A * n + B` THEN
    ASM_REWRITE_TAC[LE_ADD_RCANCEL] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ADD_SYM] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC;
      LE_ADD]]);;

(* ------------------------------------------------------------------------- *)
(* Now the multiplicative inverse proper.                                    *)
(* ------------------------------------------------------------------------- *)

let nadd_inv = new_definition
  `nadd_inv(x) = if x === &0 then &0 else afn(nadd_rinv x)`;;

override_interface ("inv",`nadd_inv:nadd->nadd`);;

let NADD_INV = prove
 (`!x. fn(nadd_inv x) = if x === &0 then (\n. 0) else nadd_rinv x`,
  GEN_TAC THEN REWRITE_TAC[nadd_inv] THEN
  ASM_CASES_TAC `x === &0` THEN ASM_REWRITE_TAC[NADD_OF_NUM; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM nadd_rep; is_nadd] THEN
  MATCH_MP_TAC NADD_MUL_LINV_LEMMA8 THEN POP_ASSUM ACCEPT_TAC);;

let NADD_MUL_LINV = prove
 (`!x. ~(x === &0) ==> inv(x) ** x === &1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[nadd_eq; NADD_MUL] THEN
  ONCE_REWRITE_TAC[BOUNDS_DIVIDED] THEN
  X_CHOOSE_THEN `A1:num` (X_CHOOSE_TAC `B1:num`)
   (SPECL [`inv(x)`; `x:nadd`] NADD_ALTMUL) THEN
  REWRITE_TAC[DIST_LMUL; NADD_OF_NUM; MULT_CLAUSES] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `N:num` o MATCH_MP NADD_MUL_LINV_LEMMA2) THEN
  X_CHOOSE_THEN `A':num` (X_CHOOSE_TAC `B':num`)
    (SPEC `x:nadd` NADD_BOUND) THEN
  SUBGOAL_THEN `?A2 B2. !n. dist(fn x n * nadd_rinv x n,n * n) <= A2 * n + B2`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `A':num` THEN ONCE_REWRITE_TAC[BOUNDS_IGNORE] THEN
    MAP_EVERY EXISTS_TAC [`B':num`; `N:num`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `fn x n` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`A1 + A2`; `B1 + B2`] THEN
    GEN_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_LE THEN
    EXISTS_TAC `fn (inv x) n * fn x n` THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
    ONCE_REWRITE_TAC[AC ADD_AC `(a + b) + c + d = (a + c) + (b + d)`] THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [MULT_SYM] THEN
    ASM_REWRITE_TAC[NADD_INV]]);;

let NADD_INV_0 = prove
 (`inv(&0) === &0`,
  REWRITE_TAC[nadd_inv; NADD_EQ_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Welldefinedness follows from already established principles because if    *)
(* x = y then y' = y' 1 = y' (x' x) = y' (x' y) = (y' y) x' = 1 x' = x'      *)
(* ------------------------------------------------------------------------- *)

let NADD_INV_WELLDEF = prove
 (`!x y. x === y ==> inv(x) === inv(y)`,
  let TAC tm ths =
    MATCH_MP_TAC NADD_EQ_TRANS THEN EXISTS_TAC tm THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC ths] in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x === &0` THENL
   [SUBGOAL_THEN `y === &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[NADD_EQ_TRANS; NADD_EQ_SYM];
      ASM_REWRITE_TAC[nadd_inv; NADD_EQ_REFL]];
    SUBGOAL_THEN `~(y === &0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[NADD_EQ_TRANS; NADD_EQ_SYM]; ALL_TAC]] THEN
  TAC `inv(y) ** &1`
      [NADD_MUL_SYM; NADD_MUL_LID; NADD_EQ_TRANS] THEN
  TAC `inv(y) ** (inv(x) ** x)`
      [NADD_MUL_LINV; NADD_MUL_WELLDEF; NADD_EQ_REFL] THEN
  TAC `inv(y) ** (inv(x) ** y)`
      [NADD_MUL_WELLDEF; NADD_EQ_REFL; NADD_EQ_SYM] THEN
  TAC `(inv(y) ** y) ** inv(x)`
      [NADD_MUL_ASSOC; NADD_MUL_SYM; NADD_EQ_TRANS;
       NADD_MUL_WELLDEF; NADD_EQ_REFL] THEN
  ASM_MESON_TAC[NADD_MUL_LINV; NADD_MUL_WELLDEF; NADD_EQ_REFL;
    NADD_MUL_LID; NADD_EQ_TRANS; NADD_EQ_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the new type.                                               *)
(* ------------------------------------------------------------------------- *)

let hreal_tybij =
  define_quotient_type "hreal" ("mk_hreal","dest_hreal") `(===)`;;

do_list overload_interface
 ["+",`hreal_add:hreal->hreal->hreal`;
  "*",`hreal_mul:hreal->hreal->hreal`;
  "<=",`hreal_le:hreal->hreal->bool`];;

do_list override_interface
 ["&",`hreal_of_num:num->hreal`;
  "inv",`hreal_inv:hreal->hreal`];;

let hreal_of_num,hreal_of_num_th =
  lift_function (snd hreal_tybij) (NADD_EQ_REFL,NADD_EQ_TRANS)
  "hreal_of_num" NADD_OF_NUM_WELLDEF;;

let hreal_add,hreal_add_th =
  lift_function (snd hreal_tybij) (NADD_EQ_REFL,NADD_EQ_TRANS)
  "hreal_add" NADD_ADD_WELLDEF;;

let hreal_mul,hreal_mul_th =
  lift_function (snd hreal_tybij) (NADD_EQ_REFL,NADD_EQ_TRANS)
  "hreal_mul" NADD_MUL_WELLDEF;;

let hreal_le,hreal_le_th =
  lift_function (snd hreal_tybij) (NADD_EQ_REFL,NADD_EQ_TRANS)
  "hreal_le" NADD_LE_WELLDEF;;

let hreal_inv,hreal_inv_th =
  lift_function (snd hreal_tybij) (NADD_EQ_REFL,NADD_EQ_TRANS)
  "hreal_inv" NADD_INV_WELLDEF;;

let HREAL_COMPLETE =
  let th1 = ASSUME `(P:nadd->bool) = (\x. Q(mk_hreal((===) x)))` in
  let th2 = BETA_RULE(AP_THM th1 `x:nadd`) in
  let th3 = lift_theorem hreal_tybij
              (NADD_EQ_REFL,NADD_EQ_SYM,NADD_EQ_TRANS)
              [hreal_of_num_th; hreal_add_th; hreal_mul_th; hreal_le_th; th2]
              (SPEC_ALL NADD_COMPLETE) in
  let th4 = MATCH_MP (DISCH_ALL th3) (REFL `\x. Q(mk_hreal((===) x)):bool`) in
  CONV_RULE(GEN_ALPHA_CONV `P:hreal->bool`) (GEN_ALL th4);;

let [HREAL_OF_NUM_EQ; HREAL_OF_NUM_LE; HREAL_OF_NUM_ADD; HREAL_OF_NUM_MUL;
     HREAL_LE_REFL; HREAL_LE_TRANS; HREAL_LE_ANTISYM; HREAL_LE_TOTAL;
     HREAL_LE_ADD; HREAL_LE_EXISTS; HREAL_ARCH; HREAL_ADD_SYM; HREAL_ADD_ASSOC;
     HREAL_ADD_LID; HREAL_ADD_LCANCEL; HREAL_MUL_SYM; HREAL_MUL_ASSOC;
     HREAL_MUL_LID; HREAL_ADD_LDISTRIB; HREAL_MUL_LINV; HREAL_INV_0] =
  map (lift_theorem hreal_tybij
         (NADD_EQ_REFL,NADD_EQ_SYM,NADD_EQ_TRANS)
             [hreal_of_num_th; hreal_add_th; hreal_mul_th;
              hreal_le_th; hreal_inv_th])
 [NADD_OF_NUM_EQ; NADD_OF_NUM_LE; NADD_OF_NUM_ADD; NADD_OF_NUM_MUL;
  NADD_LE_REFL; NADD_LE_TRANS; NADD_LE_ANTISYM; NADD_LE_TOTAL; NADD_LE_ADD;
  NADD_LE_EXISTS; NADD_ARCH; NADD_ADD_SYM; NADD_ADD_ASSOC; NADD_ADD_LID;
  NADD_ADD_LCANCEL; NADD_MUL_SYM; NADD_MUL_ASSOC; NADD_MUL_LID; NADD_LDISTRIB;
  NADD_MUL_LINV; NADD_INV_0];;

(* ------------------------------------------------------------------------- *)
(* Consequential theorems needed later.                                      *)
(* ------------------------------------------------------------------------- *)

let HREAL_LE_EXISTS_DEF = prove
 (`!m n. m <= n <=> ?d. n = m + d`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[HREAL_LE_EXISTS] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[HREAL_LE_ADD]);;

let HREAL_EQ_ADD_LCANCEL = prove
 (`!m n p. (m + n = m + p) <=> (n = p)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[HREAL_ADD_LCANCEL] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let HREAL_EQ_ADD_RCANCEL = prove
 (`!m n p. (m + p = n + p) <=> (m = n)`,
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN REWRITE_TAC[HREAL_EQ_ADD_LCANCEL]);;

let HREAL_LE_ADD_LCANCEL = prove
 (`!m n p. (m + n <= m + p) <=> (n <= p)`,
  REWRITE_TAC[HREAL_LE_EXISTS_DEF; GSYM HREAL_ADD_ASSOC;
    HREAL_EQ_ADD_LCANCEL]);;

let HREAL_LE_ADD_RCANCEL = prove
 (`!m n p. (m + p <= n + p) <=> (m <= n)`,
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN MATCH_ACCEPT_TAC HREAL_LE_ADD_LCANCEL);;

let HREAL_ADD_RID = prove
 (`!n. n + &0 = n`,
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN MATCH_ACCEPT_TAC HREAL_ADD_LID);;

let HREAL_ADD_RDISTRIB = prove
 (`!m n p. (m + n) * p = m * p + n * p`,
  ONCE_REWRITE_TAC[HREAL_MUL_SYM] THEN MATCH_ACCEPT_TAC HREAL_ADD_LDISTRIB);;

let HREAL_MUL_LZERO = prove
 (`!m. &0 * m = &0`,
  GEN_TAC THEN MP_TAC(SPECL [`&0`; `&1`; `m:hreal`] HREAL_ADD_RDISTRIB) THEN
  REWRITE_TAC[HREAL_ADD_LID] THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM HREAL_ADD_LID] THEN
  REWRITE_TAC[HREAL_EQ_ADD_RCANCEL] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let HREAL_MUL_RZERO = prove
 (`!m. m * &0 = &0`,
  ONCE_REWRITE_TAC[HREAL_MUL_SYM] THEN MATCH_ACCEPT_TAC HREAL_MUL_LZERO);;

let HREAL_ADD_AC = prove
 (`(m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))`,
  REWRITE_TAC[HREAL_ADD_ASSOC; EQT_INTRO(SPEC_ALL HREAL_ADD_SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC HREAL_ADD_SYM);;

let HREAL_LE_ADD2 = prove
 (`!a b c d. a <= b /\ c <= d ==> a + c <= b + d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LE_EXISTS_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d1:hreal`)
    (X_CHOOSE_TAC `d2:hreal`)) THEN
  EXISTS_TAC `d1 + d2` THEN ASM_REWRITE_TAC[HREAL_ADD_AC]);;

let HREAL_LE_MUL_RCANCEL_IMP = prove
 (`!a b c. a <= b ==> a * c <= b * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_LE_EXISTS_DEF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:hreal` SUBST1_TAC) THEN
  EXISTS_TAC `d * c` THEN REWRITE_TAC[HREAL_ADD_RDISTRIB]);;

(* ------------------------------------------------------------------------- *)
(* Define operations on representatives of signed reals.                     *)
(* ------------------------------------------------------------------------- *)

let treal_of_num = new_definition
  `treal_of_num n = (&n, &0)`;;

let treal_neg = new_definition
  `treal_neg ((x:hreal),(y:hreal)) = (y,x)`;;

let treal_add = new_definition
  `(x1,y1) treal_add (x2,y2) = (x1 + x2, y1 + y2)`;;

let treal_mul = new_definition
  `(x1,y1) treal_mul (x2,y2) = ((x1 * x2) + (y1 * y2),(x1 * y2) + (y1 * x2))`;;

let treal_le = new_definition
  `(x1,y1) treal_le (x2,y2) <=> x1 + y2 <= x2 + y1`;;

let treal_inv = new_definition
  `treal_inv(x,y) = if x = y then (&0, &0)
                    else if y <= x then (inv(@d. x = y + d), &0)
                    else (&0, inv(@d. y = x + d))`;;

(* ------------------------------------------------------------------------- *)
(* Define the equivalence relation and prove it *is* one.                    *)
(* ------------------------------------------------------------------------- *)

let treal_eq = new_definition
  `(x1,y1) treal_eq (x2,y2) <=> (x1 + y2 = x2 + y1)`;;

let TREAL_EQ_REFL = prove
 (`!x. x treal_eq x`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_eq]);;

let TREAL_EQ_SYM = prove
 (`!x y. x treal_eq y <=> y treal_eq x`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_eq; EQ_SYM_EQ]);;

let TREAL_EQ_TRANS = prove
 (`!x y z. x treal_eq y /\ y treal_eq z ==> x treal_eq z`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_eq] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MK_COMB o (AP_TERM `(+)` F_F I) o CONJ_PAIR) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [HREAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC; HREAL_EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[HREAL_ADD_ASSOC; HREAL_EQ_ADD_RCANCEL] THEN
  DISCH_THEN(MATCH_ACCEPT_TAC o ONCE_REWRITE_RULE[HREAL_ADD_SYM]));;

(* ------------------------------------------------------------------------- *)
(* Useful to avoid unnecessary use of the equivalence relation.              *)
(* ------------------------------------------------------------------------- *)

let TREAL_EQ_AP = prove
 (`!x y. (x = y) ==> x treal_eq y`,
  SIMP_TAC[TREAL_EQ_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Commutativity properties for injector.                                    *)
(* ------------------------------------------------------------------------- *)

let TREAL_OF_NUM_EQ = prove
 (`!m n. (treal_of_num m treal_eq treal_of_num n) <=> (m = n)`,
  REWRITE_TAC[treal_of_num; treal_eq; HREAL_OF_NUM_EQ; HREAL_ADD_RID]);;

let TREAL_OF_NUM_LE = prove
 (`!m n. (treal_of_num m treal_le treal_of_num n) <=> m <= n`,
  REWRITE_TAC[treal_of_num; treal_le; HREAL_OF_NUM_LE; HREAL_ADD_RID]);;

let TREAL_OF_NUM_ADD = prove
 (`!m n. (treal_of_num m treal_add treal_of_num n) treal_eq
         (treal_of_num(m + n))`,
  REWRITE_TAC[treal_of_num; treal_eq; treal_add;
   HREAL_OF_NUM_ADD; HREAL_ADD_RID; ADD_CLAUSES]);;

let TREAL_OF_NUM_MUL = prove
 (`!m n. (treal_of_num m treal_mul treal_of_num n) treal_eq
         (treal_of_num(m * n))`,
  REWRITE_TAC[treal_of_num; treal_eq; treal_mul;
   HREAL_OF_NUM_MUL; HREAL_MUL_RZERO; HREAL_MUL_LZERO; HREAL_ADD_RID;
   HREAL_ADD_LID; HREAL_ADD_RID; MULT_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Strong forms of equality are useful to simplify welldefinedness proofs.   *)
(* ------------------------------------------------------------------------- *)

let TREAL_ADD_SYM_EQ = prove
 (`!x y. x treal_add y = y treal_add x`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_add; PAIR_EQ; HREAL_ADD_SYM]);;

let TREAL_MUL_SYM_EQ = prove
 (`!x y. x treal_mul y = y treal_mul x`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_mul; HREAL_MUL_SYM; HREAL_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Prove the properties of operations on representatives.                    *)
(* ------------------------------------------------------------------------- *)

let TREAL_ADD_SYM = prove
 (`!x y. (x treal_add y) treal_eq (y treal_add x)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC TREAL_EQ_AP THEN
  MATCH_ACCEPT_TAC TREAL_ADD_SYM_EQ);;

let TREAL_ADD_ASSOC = prove
 (`!x y z. (x treal_add (y treal_add z)) treal_eq
           ((x treal_add y) treal_add z)`,
  SIMP_TAC[FORALL_PAIR_THM; TREAL_EQ_AP; treal_add; HREAL_ADD_ASSOC]);;

let TREAL_ADD_LID = prove
 (`!x. ((treal_of_num 0) treal_add x) treal_eq x`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_of_num; treal_add; treal_eq;
              HREAL_ADD_LID]);;

let TREAL_ADD_LINV = prove
 (`!x. ((treal_neg x) treal_add x) treal_eq (treal_of_num 0)`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_neg; treal_add; treal_eq; treal_of_num;
              HREAL_ADD_LID; HREAL_ADD_RID; HREAL_ADD_SYM]);;

let TREAL_MUL_SYM = prove
 (`!x y. (x treal_mul y) treal_eq (y treal_mul x)`,
  SIMP_TAC[TREAL_EQ_AP; TREAL_MUL_SYM_EQ]);;

let TREAL_MUL_ASSOC = prove
 (`!x y z. (x treal_mul (y treal_mul z)) treal_eq
           ((x treal_mul y) treal_mul z)`,
  SIMP_TAC[FORALL_PAIR_THM; TREAL_EQ_AP; treal_mul; HREAL_ADD_LDISTRIB;
           HREAL_ADD_RDISTRIB; GSYM HREAL_MUL_ASSOC; HREAL_ADD_AC]);;

let TREAL_MUL_LID = prove
 (`!x. ((treal_of_num 1) treal_mul x) treal_eq x`,
  SIMP_TAC[FORALL_PAIR_THM; treal_of_num; treal_mul; treal_eq] THEN
  REWRITE_TAC[HREAL_MUL_LZERO; HREAL_MUL_LID; HREAL_ADD_LID; HREAL_ADD_RID]);;

let TREAL_ADD_LDISTRIB = prove
 (`!x y z. (x treal_mul (y treal_add z)) treal_eq
           ((x treal_mul y) treal_add (x treal_mul z))`,
  SIMP_TAC[FORALL_PAIR_THM; TREAL_EQ_AP; treal_mul; treal_add;
           HREAL_ADD_LDISTRIB; PAIR_EQ; HREAL_ADD_AC]);;

let TREAL_LE_REFL = prove
 (`!x. x treal_le x`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_le; HREAL_LE_REFL]);;

let TREAL_LE_ANTISYM = prove
 (`!x y. x treal_le y /\ y treal_le x <=> (x treal_eq y)`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_le; treal_eq; HREAL_LE_ANTISYM]);;

let TREAL_LE_TRANS = prove
 (`!x y z. x treal_le y /\ y treal_le z ==> x treal_le z`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_le] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HREAL_LE_ADD2) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [HREAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC; HREAL_LE_ADD_LCANCEL] THEN
  REWRITE_TAC[HREAL_ADD_ASSOC; HREAL_LE_ADD_RCANCEL] THEN
  DISCH_THEN(MATCH_ACCEPT_TAC o ONCE_REWRITE_RULE[HREAL_ADD_SYM]));;

let TREAL_LE_TOTAL = prove
 (`!x y. x treal_le y \/ y treal_le x`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_le; HREAL_LE_TOTAL]);;

let TREAL_LE_LADD_IMP = prove
 (`!x y z. (y treal_le z) ==> (x treal_add y) treal_le (x treal_add z)`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_le; treal_add] THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC; HREAL_LE_ADD_LCANCEL] THEN
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN
  REWRITE_TAC[GSYM HREAL_ADD_ASSOC; HREAL_LE_ADD_LCANCEL]);;

let TREAL_LE_MUL = prove
 (`!x y. (treal_of_num 0) treal_le x /\ (treal_of_num 0) treal_le y
         ==> (treal_of_num 0) treal_le (x treal_mul y)`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_of_num; treal_le; treal_mul] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[HREAL_ADD_LID; HREAL_ADD_RID] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP HREAL_LE_EXISTS) THEN
  REWRITE_TAC[HREAL_ADD_LDISTRIB; HREAL_LE_ADD_LCANCEL;
    GSYM HREAL_ADD_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [HREAL_ADD_SYM] THEN
  ASM_REWRITE_TAC[HREAL_LE_ADD_LCANCEL] THEN
  MATCH_MP_TAC HREAL_LE_MUL_RCANCEL_IMP THEN ASM_REWRITE_TAC[]);;

let TREAL_INV_0 = prove
 (`treal_inv (treal_of_num 0) treal_eq (treal_of_num 0)`,
  REWRITE_TAC[treal_inv; treal_eq; treal_of_num]);;

let TREAL_MUL_LINV = prove
 (`!x. ~(x treal_eq treal_of_num 0) ==>
        (treal_inv(x) treal_mul x) treal_eq (treal_of_num 1)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:hreal`; `y:hreal`] THEN
  PURE_REWRITE_TAC[treal_eq; treal_of_num; treal_mul; treal_inv] THEN
  PURE_REWRITE_TAC[HREAL_ADD_LID; HREAL_ADD_RID] THEN DISCH_TAC THEN
  PURE_ASM_REWRITE_TAC[COND_CLAUSES] THEN COND_CASES_TAC THEN
  PURE_REWRITE_TAC[treal_mul; treal_eq] THEN
  REWRITE_TAC[HREAL_ADD_LID; HREAL_ADD_RID;
              HREAL_MUL_LZERO; HREAL_MUL_RZERO] THENL
   [ALL_TAC;
    DISJ_CASES_THEN MP_TAC(SPECL [`x:hreal`; `y:hreal`] HREAL_LE_TOTAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HREAL_LE_EXISTS) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN
  DISCH_THEN(fun th -> ASSUME_TAC (SYM th) THEN
                       GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[HREAL_ADD_LDISTRIB] THEN
  GEN_REWRITE_TAC RAND_CONV [HREAL_ADD_SYM] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC HREAL_MUL_LINV THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN
  ASM_REWRITE_TAC[HREAL_ADD_RID] THEN
  PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Show that the operations respect the equivalence relation.                *)
(* ------------------------------------------------------------------------- *)

let TREAL_OF_NUM_WELLDEF = prove
 (`!m n. (m = n) ==> (treal_of_num m) treal_eq (treal_of_num n)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC TREAL_EQ_REFL);;

let TREAL_NEG_WELLDEF = prove
 (`!x1 x2. x1 treal_eq x2 ==> (treal_neg x1) treal_eq (treal_neg x2)`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_neg; treal_eq] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN ASM_REWRITE_TAC[]);;

let TREAL_ADD_WELLDEFR = prove
 (`!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_add y) treal_eq (x2 treal_add y)`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_add; treal_eq] THEN
  REWRITE_TAC[HREAL_EQ_ADD_RCANCEL; HREAL_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN
  REWRITE_TAC[HREAL_EQ_ADD_RCANCEL; HREAL_ADD_ASSOC]);;

let TREAL_ADD_WELLDEF = prove
 (`!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_add y1) treal_eq (x2 treal_add y2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC `x1 treal_add y2` THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TREAL_ADD_SYM_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC TREAL_ADD_WELLDEFR THEN ASM_REWRITE_TAC[]);;

let TREAL_MUL_WELLDEFR = prove
 (`!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_mul y) treal_eq (x2 treal_mul y)`,
  REWRITE_TAC[FORALL_PAIR_THM; treal_mul; treal_eq] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[AC HREAL_ADD_AC
    `(a + b) + (c + d) = (a + d) + (b + c)`] THEN
  REWRITE_TAC[GSYM HREAL_ADD_RDISTRIB] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[HREAL_ADD_SYM] THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);;

let TREAL_MUL_WELLDEF = prove
 (`!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_mul y1) treal_eq (x2 treal_mul y2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TREAL_EQ_TRANS THEN EXISTS_TAC `x1 treal_mul y2` THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TREAL_MUL_SYM_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC TREAL_MUL_WELLDEFR THEN ASM_REWRITE_TAC[]);;

let TREAL_EQ_IMP_LE = prove
 (`!x y. x treal_eq y ==> x treal_le y`,
  SIMP_TAC[FORALL_PAIR_THM; treal_eq; treal_le; HREAL_LE_REFL]);;

let TREAL_LE_WELLDEF = prove
 (`!x1 x2 y1 y2. x1 treal_eq x2 /\ y1 treal_eq y2 ==>
     (x1 treal_le y1 <=> x2 treal_le y2)`,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
   [MATCH_MP_TAC TREAL_LE_TRANS THEN EXISTS_TAC `y1:hreal#hreal` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TREAL_LE_TRANS THEN EXISTS_TAC `x1:hreal#hreal` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TREAL_EQ_IMP_LE THEN
      ONCE_REWRITE_TAC[TREAL_EQ_SYM];
      MATCH_MP_TAC TREAL_EQ_IMP_LE];
    MATCH_MP_TAC TREAL_LE_TRANS THEN EXISTS_TAC `y2:hreal#hreal` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC TREAL_LE_TRANS THEN EXISTS_TAC `x2:hreal#hreal` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TREAL_EQ_IMP_LE;
      MATCH_MP_TAC TREAL_EQ_IMP_LE THEN ONCE_REWRITE_TAC[TREAL_EQ_SYM]]] THEN
  ASM_REWRITE_TAC[]);;

let TREAL_INV_WELLDEF = prove
 (`!x y. x treal_eq y ==> (treal_inv x) treal_eq (treal_inv y)`,
  let lemma = prove
   (`(@d. x = x + d) = &0`,
    MATCH_MP_TAC SELECT_UNIQUE THEN BETA_TAC THEN
    GEN_TAC THEN GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM HREAL_ADD_RID] THEN
    REWRITE_TAC[HREAL_EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC EQ_SYM_EQ) in
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x1:hreal`; `x2:hreal`; `y1:hreal`; `y2:hreal`] THEN
  PURE_REWRITE_TAC[treal_eq; treal_inv] THEN
  ASM_CASES_TAC `x1 :hreal = x2` THEN
  ASM_CASES_TAC `y1 :hreal = y2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TREAL_EQ_REFL] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE RAND_CONV [HREAL_ADD_SYM]) THEN
  REWRITE_TAC[HREAL_EQ_ADD_LCANCEL; HREAL_EQ_ADD_RCANCEL] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[HREAL_LE_REFL; lemma; HREAL_INV_0;TREAL_EQ_REFL] THEN
  ASM_CASES_TAC `x2 <= x1` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(ASSUME_TAC o SYM o SELECT_RULE o MATCH_MP HREAL_LE_EXISTS) THEN
    UNDISCH_TAC `x1 + y2 = x2 + y1` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[HREAL_EQ_ADD_LCANCEL; GSYM HREAL_ADD_ASSOC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[HREAL_ADD_SYM] HREAL_LE_ADD] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o BINDER_CONV o
      LAND_CONV) [HREAL_ADD_SYM] THEN
    REWRITE_TAC[HREAL_EQ_ADD_LCANCEL; TREAL_EQ_REFL];
    DISJ_CASES_THEN MP_TAC
      (SPECL [`x1:hreal`; `x2:hreal`] HREAL_LE_TOTAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o SYM o SELECT_RULE o MATCH_MP HREAL_LE_EXISTS) THEN
    UNDISCH_TAC `x1 + y2 = x2 + y1` THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[HREAL_EQ_ADD_LCANCEL; GSYM HREAL_ADD_ASSOC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[HREAL_ADD_SYM] HREAL_LE_ADD] THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC `(@d. x2 = x1 + d) + y1 <= y1:hreal` THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM HREAL_ADD_LID] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[HREAL_ADD_SYM] HREAL_LE_ADD_LCANCEL] THEN
      DISCH_TAC THEN SUBGOAL_THEN `(@d. x2 = x1 + d) = &0` MP_TAC THENL
       [ASM_REWRITE_TAC[GSYM HREAL_LE_ANTISYM] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM HREAL_ADD_LID] THEN
        REWRITE_TAC[HREAL_LE_ADD];
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `x1 + &0 = x2` THEN
        ASM_REWRITE_TAC[HREAL_ADD_RID]];
      GEN_REWRITE_TAC (funpow 3 RAND_CONV o BINDER_CONV o LAND_CONV)
        [HREAL_ADD_SYM] THEN
      REWRITE_TAC[HREAL_EQ_ADD_LCANCEL; TREAL_EQ_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Now define the quotient type -- the reals at last!                        *)
(* ------------------------------------------------------------------------- *)

let real_tybij =
  define_quotient_type "real" ("mk_real","dest_real") `(treal_eq)`;;

let real_of_num,real_of_num_th =
  lift_function (snd real_tybij) (TREAL_EQ_REFL,TREAL_EQ_TRANS)
  "real_of_num" TREAL_OF_NUM_WELLDEF;;

let real_neg,real_neg_th =
  lift_function (snd real_tybij) (TREAL_EQ_REFL,TREAL_EQ_TRANS)
  "real_neg" TREAL_NEG_WELLDEF;;

let real_add,real_add_th =
  lift_function (snd real_tybij) (TREAL_EQ_REFL,TREAL_EQ_TRANS)
  "real_add" TREAL_ADD_WELLDEF;;

let real_mul,real_mul_th =
  lift_function (snd real_tybij) (TREAL_EQ_REFL,TREAL_EQ_TRANS)
  "real_mul" TREAL_MUL_WELLDEF;;

let real_le,real_le_th =
  lift_function (snd real_tybij) (TREAL_EQ_REFL,TREAL_EQ_TRANS)
  "real_le" TREAL_LE_WELLDEF;;

let real_inv,real_inv_th =
  lift_function (snd real_tybij) (TREAL_EQ_REFL,TREAL_EQ_TRANS)
  "real_inv" TREAL_INV_WELLDEF;;

let [REAL_ADD_SYM; REAL_ADD_ASSOC; REAL_ADD_LID; REAL_ADD_LINV;
     REAL_MUL_SYM; REAL_MUL_ASSOC; REAL_MUL_LID;
     REAL_ADD_LDISTRIB;
     REAL_LE_REFL; REAL_LE_ANTISYM; REAL_LE_TRANS; REAL_LE_TOTAL;
     REAL_LE_LADD_IMP; REAL_LE_MUL;
     REAL_INV_0; REAL_MUL_LINV;
     REAL_OF_NUM_EQ; REAL_OF_NUM_LE; REAL_OF_NUM_ADD; REAL_OF_NUM_MUL] =
  map
    (lift_theorem real_tybij (TREAL_EQ_REFL,TREAL_EQ_SYM,TREAL_EQ_TRANS)
      [real_of_num_th; real_neg_th; real_add_th;
       real_mul_th; real_le_th; real_inv_th])
    [TREAL_ADD_SYM; TREAL_ADD_ASSOC; TREAL_ADD_LID; TREAL_ADD_LINV;
     TREAL_MUL_SYM; TREAL_MUL_ASSOC; TREAL_MUL_LID;
     TREAL_ADD_LDISTRIB;
     TREAL_LE_REFL; TREAL_LE_ANTISYM; TREAL_LE_TRANS; TREAL_LE_TOTAL;
     TREAL_LE_LADD_IMP; TREAL_LE_MUL;
     TREAL_INV_0; TREAL_MUL_LINV;
     TREAL_OF_NUM_EQ; TREAL_OF_NUM_LE; TREAL_OF_NUM_ADD; TREAL_OF_NUM_MUL];;

(* ------------------------------------------------------------------------- *)
(* Set up a friendly interface.                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "--";;
parse_as_infix ("/",(22,"left"));;
parse_as_infix ("pow",(24,"left"));;

do_list overload_interface
 ["+",`real_add:real->real->real`; "-",`real_sub:real->real->real`;
  "*",`real_mul:real->real->real`; "/",`real_div:real->real->real`;
  "<",`real_lt:real->real->bool`; "<=",`real_le:real->real->bool`;
  ">",`real_gt:real->real->bool`; ">=",`real_ge:real->real->bool`;
  "--",`real_neg:real->real`; "pow",`real_pow:real->num->real`;
  "inv",`real_inv:real->real`; "abs",`real_abs:real->real`;
  "max",`real_max:real->real->real`; "min",`real_min:real->real->real`;
  "&",`real_of_num:num->real`];;

let prioritize_real() = prioritize_overload(mk_type("real",[]));;

(* ------------------------------------------------------------------------- *)
(* Additional definitions.                                                   *)
(* ------------------------------------------------------------------------- *)

let real_sub = new_definition
  `x - y = x + --y`;;

let real_lt = new_definition
  `x < y <=> ~(y <= x)`;;

let real_ge = new_definition
  `x >= y <=> y <= x`;;

let real_gt = new_definition
  `x > y <=> y < x`;;

let real_abs = new_definition
  `abs(x) = if &0 <= x then x else --x`;;

let real_pow = new_recursive_definition num_RECURSION
  `(x pow 0 = &1) /\
   (!n. x pow (SUC n) = x * (x pow n))`;;

let real_div = new_definition
  `x / y = x * inv(y)`;;

let real_max = new_definition
  `real_max m n = if m <= n then n else m`;;

let real_min = new_definition
  `real_min m n = if m <= n then m else n`;;

(*----------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set         *)
(*----------------------------------------------------------------------------*)

let REAL_HREAL_LEMMA1 = prove
 (`?r:hreal->real.
       (!x. &0 <= x <=> ?y. x = r y) /\
       (!y z. y <= z <=> r y <= r z)`,
  EXISTS_TAC `\y. mk_real((treal_eq)(y,hreal_of_num 0))` THEN
  REWRITE_TAC[GSYM real_le_th] THEN
  REWRITE_TAC[treal_le; HREAL_ADD_LID; HREAL_ADD_RID] THEN
  GEN_TAC THEN EQ_TAC THENL
   [MP_TAC(INST [`dest_real x`,`r:hreal#hreal->bool`] (snd real_tybij)) THEN
    REWRITE_TAC[fst real_tybij] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:hreal#hreal` MP_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `mk_real`) THEN
    REWRITE_TAC[fst real_tybij] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM real_of_num_th; GSYM real_le_th] THEN
    SUBST1_TAC(GSYM(ISPEC `p:hreal#hreal` PAIR)) THEN
    PURE_REWRITE_TAC[treal_of_num; treal_le] THEN
    PURE_REWRITE_TAC[HREAL_ADD_LID; HREAL_ADD_RID] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:hreal` SUBST1_TAC o
      MATCH_MP HREAL_LE_EXISTS) THEN
    EXISTS_TAC `d:hreal` THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `q:hreal#hreal` THEN
    SUBST1_TAC(GSYM(ISPEC `q:hreal#hreal` PAIR)) THEN
    PURE_REWRITE_TAC[treal_eq] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [HREAL_ADD_SYM] THEN
    REWRITE_TAC[GSYM HREAL_ADD_ASSOC; HREAL_EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[HREAL_ADD_RID];
    DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM real_of_num_th; GSYM real_le_th] THEN
    REWRITE_TAC[treal_of_num; treal_le] THEN
    REWRITE_TAC[HREAL_ADD_LID; HREAL_ADD_RID] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM HREAL_ADD_LID] THEN
    REWRITE_TAC[HREAL_LE_ADD]]);;

let REAL_HREAL_LEMMA2 = prove
 (`?h r. (!x:hreal. h(r x) = x) /\
         (!x. &0 <= x ==> (r(h x) = x)) /\
         (!x:hreal. &0 <= r x) /\
         (!x y. x <= y <=> r x <= r y)`,
  STRIP_ASSUME_TAC REAL_HREAL_LEMMA1 THEN
  EXISTS_TAC `\x:real. @y:hreal. x = r y` THEN
  EXISTS_TAC `r:hreal->real` THEN
  ASM_REWRITE_TAC[BETA_THM] THEN
  SUBGOAL_THEN `!y z. ((r:hreal->real) y = r z) <=> (y = z)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM; GSYM HREAL_LE_ANTISYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GEN_REWRITE_RULE (LAND_CONV o BINDER_CONV) [EQ_SYM_EQ]
    (SPEC_ALL SELECT_REFL); GSYM EXISTS_REFL] THEN
  GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o SYM o SELECT_RULE));;

let REAL_COMPLETE_SOMEPOS = prove
 (`!P. (?x. P x /\ &0 <= x) /\
       (?M. !x. P x ==> x <= M)
       ==> ?M. (!x. P x ==> x <= M) /\
               !M'. (!x. P x ==> x <= M') ==> M <= M'`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC REAL_HREAL_LEMMA2 THEN
  MP_TAC(SPEC `\y:hreal. (P:real->bool)(r y)` HREAL_COMPLETE) THEN
  BETA_TAC THEN
  W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `(h:real->hreal) x` THEN
      UNDISCH_TAC `(P:real->bool) x` THEN
      MATCH_MP_TAC(TAUT `(b <=> a) ==> a ==> b`) THEN
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(h:real->hreal) M` THEN
      X_GEN_TAC `y:hreal` THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `(b <=> a) ==> a ==> b`) THEN
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real` THEN
      ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(TAUT `(b ==> c) ==> a ==> (a ==> b) ==> c`) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:hreal` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `(r:hreal->real) B` THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real` THEN DISCH_TAC THEN
    DISJ_CASES_TAC(SPECL [`&0`; `z:real`] REAL_LE_TOTAL) THENL
     [ANTE_RES_THEN(SUBST1_TAC o SYM) (ASSUME `&0 <= z`) THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(P:real->bool) z` THEN
      MATCH_MP_TAC(TAUT `(b <=> a) ==> a ==> b`) THEN
      AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `C:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `B:hreal <= (h(C:real))` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(r:hreal->real)(h C) = C` (fun th -> ASM_REWRITE_TAC[th]);
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x:real` THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let REAL_COMPLETE = prove
 (`!P. (?x. P x) /\
       (?M. !x. P x ==> x <= M)
       ==> ?M. (!x. P x ==> x <= M) /\
               !M'. (!x. P x ==> x <= M') ==> M <= M'`,
  let lemma = prove
   (`y = (y - x) + x`,
    REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC; REAL_ADD_LINV] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_ADD_LID]) in
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC (SPECL [`&0`; `x:real`] REAL_LE_TOTAL) THENL
   [MATCH_MP_TAC REAL_COMPLETE_SOMEPOS THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real`; EXISTS_TAC `M:real`] THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP REAL_LE_LADD_IMP) THEN
    DISCH_THEN(MP_TAC o SPEC `--x`) THEN
    REWRITE_TAC[REAL_ADD_LINV] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[REAL_ADD_LID] THEN
    DISCH_TAC THEN
    MP_TAC(SPEC `\y. P(y + x) :bool` REAL_COMPLETE_SOMEPOS) THEN
    BETA_TAC THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_LID];
        EXISTS_TAC `M + --x` THEN GEN_TAC THEN
        DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        DISCH_THEN(MP_TAC o SPEC `--x` o MATCH_MP REAL_LE_LADD_IMP) THEN
        DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[REAL_ADD_SYM]) THEN
        REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LINV] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID]];
      MATCH_MP_TAC(TAUT `(b ==> c) ==> a ==> (a ==> b) ==> c`) THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `B + x` THEN CONJ_TAC THENL
     [GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [lemma] THEN
      DISCH_THEN(ANTE_RES_THEN
        (MP_TAC o SPEC `x:real` o MATCH_MP REAL_LE_LADD_IMP)) THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      REWRITE_TAC[real_sub; GSYM REAL_ADD_ASSOC; REAL_ADD_LINV] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID] THEN
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN SUBGOAL_THEN `B <= M' - x` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `z:real` THEN DISCH_TAC THEN
        SUBGOAL_THEN `z + x <= M'` MP_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          DISCH_THEN(MP_TAC o SPEC `--x` o MATCH_MP REAL_LE_LADD_IMP) THEN
          ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
          REWRITE_TAC[real_sub] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
          AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
          REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LINV] THEN
          REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID]];
         DISCH_THEN(MP_TAC o SPEC `x:real` o MATCH_MP REAL_LE_LADD_IMP) THEN
         MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
          [MATCH_ACCEPT_TAC REAL_ADD_SYM;
           ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[real_sub] THEN
           REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_ADD_LINV] THEN
           REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_ADD_LID]]]]]);;

do_list reduce_interface
 ["+",`hreal_add:hreal->hreal->hreal`;
  "*",`hreal_mul:hreal->hreal->hreal`;
  "<=",`hreal_le:hreal->hreal->bool`;
  "inv",`hreal_inv:hreal->hreal`];;

do_list remove_interface ["**"; "++"; "<<="; "==="; "fn"; "afn"];;
