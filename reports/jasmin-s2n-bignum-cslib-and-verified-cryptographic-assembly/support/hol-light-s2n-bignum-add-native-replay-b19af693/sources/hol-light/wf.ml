(* ========================================================================= *)
(* Theory of wellfounded relations.                                          *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "arith.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of wellfoundedness for arbitrary (infix) relation <<           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<<",(12,"right"));;

let WF = new_definition
  `WF(<<) <=> !P:A->bool. (?x. P(x)) ==> (?x. P(x) /\ !y. y << x ==> ~P(y))`;;

(* ------------------------------------------------------------------------- *)
(* Strengthen it to equality.                                                *)
(* ------------------------------------------------------------------------- *)

let WF_EQ = prove
 (`WF(<<) <=> !P:A->bool. (?x. P(x)) <=> (?x. P(x) /\ !y. y << x ==> ~P(y))`,
  REWRITE_TAC[WF] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence of wellfounded induction.                                     *)
(* ------------------------------------------------------------------------- *)

let WF_IND = prove
 (`WF(<<) <=> !P:A->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)`,
  REWRITE_TAC[WF] THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  POP_ASSUM(MP_TAC o SPEC `\x:A. ~P(x)`) THEN REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence of the "infinite descending chains" version.                  *)
(* ------------------------------------------------------------------------- *)

let WF_DCHAIN = prove
 (`WF(<<) <=> ~(?s:num->A. !n. s(SUC n) << s(n))`,
  REWRITE_TAC[WF; TAUT `(a <=> ~b) <=> (~a <=> b)`; NOT_FORALL_THM] THEN
  EQ_TAC THEN DISCH_THEN CHOOSE_TAC THENL
   [POP_ASSUM(MP_TAC o REWRITE_RULE[NOT_IMP]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) ASSUME_TAC) THEN
    SUBGOAL_THEN `!x:A. ?y. P(x) ==> P(y) /\ y << x` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[SKOLEM_THM]] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:A->A` STRIP_ASSUME_TAC) THEN
    CHOOSE_TAC(prove_recursive_functions_exist num_RECURSION
     `(s(0) = a:A) /\ (!n. s(SUC n) = f(s n))`) THEN
    EXISTS_TAC `s:num->A` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!n. P(s n) /\ s(SUC n):A << s(n)`
      (fun th -> ASM_MESON_TAC[th]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    EXISTS_TAC `\y:A. ?n:num. y = s(n)` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

let WF_DHAIN_TRANSITIVE = prove
 (`!(<<):A->A->bool.
        (!x y z. x << y /\ y << z ==> x << z)
        ==> (WF(<<) <=> ~(?s:num->A. !i j. i < j ==> s j << s i))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN
  AP_TERM_TAC THEN EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `s:num->A` THEN SIMP_TAC[LT] THEN DISCH_TAC THEN
  MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *uniqueness* part of recursion.                        *)
(* ------------------------------------------------------------------------- *)

let WF_UREC = prove
 (`WF(<<) ==>
       !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
            ==> !(f:A->B) g. (!x. f x = H f x) /\ (!x. g x = H g x)
                              ==> (f = g)`,
  REWRITE_TAC[WF_IND] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[]);;

let WF_UREC_WF = prove
 (`(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
        ==> !(f:A->bool) g. (!x. f x = H f x) /\ (!x. g x = H g x)
                          ==> (f = g))
   ==> WF(<<)`,
  REWRITE_TAC[WF_IND] THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\f x. P(x:A) \/ !z:A. z << x ==> f(z)`) THEN
  REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
   [MESON_TAC[]; DISCH_THEN(MP_TAC o SPECL [`P:A->bool`; `\x:A. T`]) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Stronger form of recursion with "inductive invariant" (Krstic/Matthews).  *)
(* ------------------------------------------------------------------------- *)

let WF_REC_INVARIANT = prove
 (`WF(<<)
   ==> !H S. (!f g x. (!z. z << x ==> (f z = g z) /\ S z (f z))
                      ==> (H f x = H g x) /\ S x (H f x))
             ==> ?f:A->B. !x. (f x = H f x)`,
  let lemma = prove_inductive_relations_exist
    `!f:A->B x. (!z. z << x ==> R z (f z)) ==> R x (H f x)` in
  REWRITE_TAC[WF_IND] THEN REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `R:A->B->bool` STRIP_ASSUME_TAC lemma THEN
  SUBGOAL_THEN `!x:A. ?!y:B. R x y` (fun th -> ASM_MESON_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC BINDER_CONV [th]) THEN
  SUBGOAL_THEN `!x:A y:B. R x y ==> S x y` MP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *existence* part of recursion.                         *)
(* ------------------------------------------------------------------------- *)

let WF_REC = prove
 (`WF(<<)
   ==> !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
           ==> ?f:A->B. !x. f x = H f x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP WF_REC_INVARIANT) THEN
  EXISTS_TAC `\x:A y:B. T` THEN ASM_REWRITE_TAC[]);;

let WF_REC_WF = prove
 (`(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
                 ==> ?f:A->num. !x. f x = H f x)
   ==> WF(<<)`,
  DISCH_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:num->A`) THEN
  SUBGOAL_THEN `!n. (x:num->A)(@m. x(m) << x(n)) << x(n)` ASSUME_TAC THENL
   [CONV_TAC(BINDER_CONV SELECT_CONV) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `\f:A->num. \y:A. if ?p:num. y = x(p)
                     then SUC(f(x(@m. x(m) << y)))
                     else 0`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->num` MP_TAC) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `(x:num->A) n`) THEN
  SUBGOAL_THEN `!n. ?p. (x:num->A) n = x p` (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!n:num. ?k. f(x(k):A) < f(x(n))` ASSUME_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `@m:num. x(m):A << x(n)` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN REWRITE_TAC[LT];
    MP_TAC(SPEC `\n:num. ?i:num. n = f(x(i):A)` num_WOP) THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Combine the two versions of the recursion theorem.                        *)
(* ------------------------------------------------------------------------- *)

let WF_EREC = prove
 (`WF(<<) ==>
       !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))
            ==> ?!f:A->B. !x. f x = H f x`,
  MESON_TAC[WF_REC; WF_UREC]);;

(* ------------------------------------------------------------------------- *)
(* Defining a recursive function via an existence condition.                 *)
(* ------------------------------------------------------------------------- *)

let WF_REC_EXISTS = prove
 (`WF((<<):A->A->bool)
   ==> !P. (!f g x y. (!z. z << x ==> f z = g z) ==> (P f x y <=> P g x y)) /\
           (!f x. (!z. z << x ==> P f z (f z)) ==> ?y. P f x y)
           ==> ?f:A->B. !x. P f x (f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?f:A->B. !x. f x = @y. P f x y` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WF_REC) THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:A->B` THEN
    DISCH_THEN(fun th ->
      ONCE_REWRITE_TAC[th] THEN ASSUME_TAC(GSYM th)) THEN
    CONV_TAC(BINDER_CONV SELECT_CONV) THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [WF_IND]) THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Some preservation theorems for wellfoundedness.                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<<<",(12,"right"));;

let WF_SUBSET = prove
 (`!(<<) (<<<). (!(x:A) y. x << y ==> x <<< y) /\ WF(<<<) ==> WF(<<)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[WF] THEN
  DISCH_TAC THEN GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  UNDISCH_TAC `!(x:A) (y:A). x << y ==> x <<< y` THEN MESON_TAC[]);;

let WF_RESTRICT = prove
 (`!(<<) P:A->bool. WF(<<) ==> WF(\x y. P x /\ P y /\ x << y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] WF_SUBSET) THEN
  SIMP_TAC[]);;

let WF_MEASURE_GEN = prove
 (`!(<<) (m:A->B). WF(<<) ==> WF(\x x'. m x << m x')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WF_IND] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\y:B. !x:A. (m(x) = y) ==> P x`) THEN
  UNDISCH_TAC `!x. (!y. (m:A->B) y << m x ==> P y) ==> P x` THEN
  REWRITE_TAC[] THEN MESON_TAC[]);;

let WF_LEX_DEPENDENT = prove
 (`!R:A->A->bool S:A->B->B->bool. WF(R) /\ (!a. WF(S a))
         ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S r1 s1 s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WF] THEN STRIP_TAC THEN
  X_GEN_TAC `P:A#B->bool` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a0:A`; `b0:B`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\a:A. ?b:B. P(a,b)`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`a0:A`; `b0:B`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_TAC `b1:B`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `\b. (P:A#B->bool) (a,b)`]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `b1:B`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_TAC THEN EXISTS_TAC `(a:A,b:B)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[]);;

let WF_LEX = prove
 (`!R:A->A->bool S:B->B->bool. WF(R) /\ WF(S)
         ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S s1 s2)`,
  SIMP_TAC[WF_LEX_DEPENDENT; ETA_AX]);;

let WF_POINTWISE = prove
 (`WF((<<) :A->A->bool) /\ WF((<<<) :B->B->bool)
   ==> WF(\(x1,y1) (x2,y2). x1 << x2 /\ y1 <<< y2)`,
  STRIP_TAC THEN MATCH_MP_TAC WF_SUBSET THEN EXISTS_TAC
   `\(x1,y1) (x2,y2). x1 << x2 \/ (x1:A = x2) /\ (y1:B) <<< (y2:B)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC TAUT;
    MATCH_MP_TAC WF_LEX THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Wellfoundedness properties of natural numbers.                            *)
(* ------------------------------------------------------------------------- *)

let WF_num = prove
 (`WF(<)`,
  REWRITE_TAC[WF_IND; num_WF]);;

let WF_REC_num = prove
 (`!H. (!f g n. (!m. m < n ==> (f m = g m)) ==> (H f n = H g n))
        ==> ?f:num->A. !n. f n = H f n`,
  MATCH_ACCEPT_TAC(MATCH_MP WF_REC WF_num));;

(* ------------------------------------------------------------------------- *)
(* Natural number measures (useful in program verification).                 *)
(* ------------------------------------------------------------------------- *)

let MEASURE = new_definition
  `MEASURE (m:A->num) = \x y. m(x) < m(y)`;;

let WF_MEASURE = prove
 (`!m:A->num. WF(MEASURE m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MEASURE] THEN
  MATCH_MP_TAC WF_MEASURE_GEN THEN
  MATCH_ACCEPT_TAC WF_num);;

let MEASURE_LE = prove
 (`!m:A->num. (!y. MEASURE m y a ==> MEASURE m y b) <=> m(a) <= m(b)`,
  REWRITE_TAC[MEASURE] THEN MESON_TAC[NOT_LE; LTE_TRANS; LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Trivially, a WF relation is irreflexive and antisymmetric.                *)
(* ------------------------------------------------------------------------- *)

let WF_ANTISYM = prove
 (`!(<<) x y:A. WF(<<) ==> ~(x << y /\ y << x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [WF]) THEN
  DISCH_THEN(MP_TAC o SPEC `\z:A. z = x \/ z = y`) THEN
  ASM_MESON_TAC[]);;

let WF_REFL = prove
 (`!x:A. WF(<<) ==> ~(x << x)`,
  MESON_TAC[WF_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Even more trivially, the everywhere-false relation is wellfounded.        *)
(* ------------------------------------------------------------------------- *)

let WF_FALSE = prove
 (`WF(\x y:A. F)`,
  REWRITE_TAC[WF]);;

(* ------------------------------------------------------------------------- *)
(* The Nash-Williams minimal bad sequence argument for some predicate `bad`  *)
(* that is a "safety property" in the Lamport/Alpern/Schneider sense.        *)
(* ------------------------------------------------------------------------- *)

let MINIMAL_BAD_SEQUENCE = prove
 (`!(<<) (bad:(num->A)->bool).
        WF(<<) /\
        (!x. ~bad x ==> ?n. !y. (!k. k < n ==> y k = x k) ==> ~bad y) /\
        (?x. bad x)
         ==> ?y. bad y /\
                 !z n. bad z /\ (!k. k < n ==> z k = y k) ==> ~(z n << y n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN
   `?x:num->A. !n. (?y. bad y /\ (!k. k < n ==> y k = x k) /\ y n = x n) /\
                   !z. bad z /\ (!k. k < n ==> z k = x k) ==> ~(z n << x n)`
  MP_TAC THENL
   [MATCH_MP_TAC(MATCH_MP WF_REC_EXISTS WF_num) THEN SIMP_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`x:num->A`; `n:num`] THEN
  DISCH_TAC THEN REWRITE_TAC[MESON[]
    `(?a. (?y. P y /\ Q y /\ f y = a) /\ (!z. A z ==> ~B a z)) <=>
     ?y. (P y /\ Q y) /\ (!z. B (f y) z ==> ~A z)`] THEN
  MP_TAC(ISPECL [`(<<):A->A->bool`; `\x:num->A. x n`] WF_MEASURE_GEN) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[WF] THEN DISCH_THEN MATCH_MP_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN SIMP_TAC[LT] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tail recursion.                                                           *)
(* ------------------------------------------------------------------------- *)

let WF_REC_TAIL = prove
 (`!P g h. ?f:A->B. !x. f x = if P(x) then f(g x) else h x`,
  let lemma1 = prove
   (`~(P 0) ==> ((?n. P(SUC n)) <=> (?n. P(n)))`,
    MESON_TAC[num_CASES; NOT_SUC])
  and lemma2 = prove
   (`(P 0) ==> ((!m. m < n ==> P(SUC m)) <=> (!m. m < SUC n ==> P(m)))`,
    REPEAT(DISCH_TAC ORELSE EQ_TAC) THEN INDUCT_TAC THEN
    ASM_MESON_TAC[LT_SUC; LT_0]) in
  REPEAT GEN_TAC THEN
  MP_TAC(GEN `x:A` (ISPECL [`x:A`; `\y:A n:num. g(y):A`] num_RECURSION)) THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:A. if ?n:num. ~P(s x n)
                    then (h:A->B)(@y. ?n. (y = s x n) /\ ~P(s x n) /\
                                          !m. m < n ==> P(s x m))
                    else something_arbitrary:B` THEN
  X_GEN_TAC `x:A` THEN
  SUBGOAL_THEN `!n x:A. s (g x) n :A = s x (SUC n)` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_THEN `!x:A n. s x (SUC n) :A = g (s x n)` (K ALL_TAC)] THEN
  ASM_CASES_TAC `(P:A->bool) x` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[lemma1] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[lemma2; lemma1];
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN EQ_TAC THENL
     [SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LT_0];
      ASM_MESON_TAC[LT]]]);;

(* ------------------------------------------------------------------------- *)
(* A more general mix of tail and wellfounded recursion.                     *)
(* ------------------------------------------------------------------------- *)

let WF_REC_TAIL_GENERAL = prove
 (`!P G H. WF(<<) /\
           (!f g x. (!z. z << x ==> (f z = g z))
                    ==> (P f x <=> P g x) /\ G f x = G g x /\ H f x = H g x) /\
           (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x)) /\
           (!f x y. P f x /\ y << G f x ==> y << x)
           ==> ?f:A->B. !x. f x = if P f x then f(G f x) else H f x`,
  REPEAT STRIP_TAC THEN
  CHOOSE_THEN MP_TAC
   (prove_inductive_relations_exist
     `(!x:A. ~(P f x) ==> terminates f x) /\
      (!x. P (f:A->B) x /\ terminates f (G f x) ==> terminates f x)`) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  SUBGOAL_THEN
   `?while. !f:A->B x:A. while f x = if P f x then while f (G f x) else x`
   (STRIP_ASSUME_TAC o GSYM)
  THENL [REWRITE_TAC[GSYM SKOLEM_THM; WF_REC_TAIL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?f:A->B. !x. f x = if terminates f x then H f (while f x :A) else anything`
  MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WF_REC) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[]
     `(a = b) /\ (a /\ b ==> (x = y) /\ (f x = g x))
      ==> ((if a then f x else d) = (if b then g y else d))`) THEN
    REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
       `!f g x.
           (!x y. P f x /\ y << G (f:A->B) x ==> y << x) /\
           (!y:A. (!z:A. z << y ==> z << x)
                  ==> (P f y = P g y) /\ (G f y = G g y))
               ==> terminates f x ==> terminates g x`
       (fun th -> EQ_TAC THEN MATCH_MP_TAC th THEN ASM_MESON_TAC[]) THEN
      GEN_TAC THEN GEN_TAC THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      SUBGOAL_THEN
       `!x:A. terminates (f:A->B) x /\
              (!y:A. (!z:A. z << y ==> z << x)
                     ==> (P f y <=> P g y) /\ (G f y :A = G g y))
              ==> (while f x :A = while g x)`
       (fun th -> MATCH_MP_TAC th THEN ASM_MESON_TAC[]) THEN
      REWRITE_TAC[IMP_CONJ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SUBGOAL_THEN
       `!f:A->B. (!x:A y:A. P f x /\ y << G f x ==> y << x)
         ==> !x. terminates f x ==> !y. y << while f x ==> y << x`
       (fun th -> ASM_MESON_TAC[th]) THEN
      GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    DISCH_THEN(fun th -> ASSUME_TAC(GSYM th) THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `P (f:A->B) (x:A) :bool` THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to apply WF induction on a free "measured" term in the goal.       *)
(* ------------------------------------------------------------------------- *)

let WF_INDUCT_TAC =
  let qqconv =
    let pth = prove
     (`(!x. P x ==> !y. Q x y) <=> !y x. P x ==> Q x y`, MESON_TAC[]) in
    GEN_REWRITE_CONV I [pth]
  and eqconv =
    let pth = prove
     (`(!m. P m ==> (m = e) ==> Q) <=> (P e ==> Q)`, MESON_TAC[]) in
    REWR_CONV pth in
  let rec qqconvs tm =
    try (qqconv THENC BINDER_CONV qqconvs) tm
    with Failure _ -> eqconv tm in
  fun tm (asl,w as gl) ->
    let fvs = frees tm
    and gv = genvar(type_of tm) in
    let pat = list_mk_forall(gv::fvs,mk_imp(mk_eq(gv,tm),w)) in
    let th0 = UNDISCH(PART_MATCH rand num_WF pat) in
    let th1 = MP (SPECL (tm::fvs) th0) (REFL tm) in
    let th2 = CONV_RULE(LAND_CONV qqconvs) (DISCH_ALL th1) in
    (MATCH_MP_TAC th2 THEN MAP_EVERY X_GEN_TAC fvs THEN
     CONV_TAC(LAND_CONV qqconvs) THEN DISCH_THEN ASSUME_TAC) gl;;
