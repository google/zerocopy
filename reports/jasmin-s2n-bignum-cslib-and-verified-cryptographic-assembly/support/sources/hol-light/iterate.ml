(* ========================================================================= *)
(* Generic iterated operations and special cases of sums over N and R.       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*              (c) Copyright, Lars Schewe 2007                              *)
(* ========================================================================= *)

needs "sets.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* A natural notation for segments of the naturals.                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("..",(15,"right"));;

let numseg = new_definition
  `m..n = {x:num | m <= x /\ x <= n}`;;

let FINITE_NUMSEG = prove
 (`!m n. FINITE(m..n)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:num | x <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM; numseg]);;

let NUMSEG_COMBINE_R = prove
 (`!m p n. m <= p + 1 /\ p <= n ==> ((m..p) UNION ((p+1)..n) = m..n)`,
  REWRITE_TAC[EXTENSION; IN_UNION; numseg; IN_ELIM_THM] THEN ARITH_TAC);;

let NUMSEG_COMBINE_L = prove
 (`!m p n. m <= p /\ p <= n + 1 ==> ((m..(p-1)) UNION (p..n) = m..n)`,
  REWRITE_TAC[EXTENSION; IN_UNION; numseg; IN_ELIM_THM] THEN ARITH_TAC);;

let NUMSEG_LREC = prove
 (`!m n. m <= n ==> (m INSERT ((m+1)..n) = m..n)`,
  REWRITE_TAC[EXTENSION; IN_INSERT; numseg; IN_ELIM_THM] THEN ARITH_TAC);;

let NUMSEG_RREC = prove
 (`!m n. m <= n ==> (n INSERT (m..(n-1)) = m..n)`,
  REWRITE_TAC[EXTENSION; IN_INSERT; numseg; IN_ELIM_THM] THEN ARITH_TAC);;

let NUMSEG_REC = prove
 (`!m n. m <= SUC n ==> (m..SUC n = (SUC n) INSERT (m..n))`,
  SIMP_TAC[GSYM NUMSEG_RREC; SUC_SUB1]);;

let IN_NUMSEG = prove
 (`!m n p. p IN (m..n) <=> m <= p /\ p <= n`,
  REWRITE_TAC[numseg; IN_ELIM_THM]);;

let IN_NUMSEG_0 = prove
 (`!m n. m IN (0..n) <=> m <= n`,
  REWRITE_TAC[IN_NUMSEG; LE_0]);;

let NUMSEG_SING = prove
 (`!n. n..n = {n}`,
  REWRITE_TAC[EXTENSION; IN_SING; IN_NUMSEG] THEN ARITH_TAC);;

let NUMSEG_EMPTY = prove
 (`!m n. (m..n = {}) <=> n < m`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_NUMSEG] THEN
  MESON_TAC[NOT_LE; LE_TRANS; LE_REFL]);;

let EMPTY_NUMSEG = prove
 (`!m n. n < m ==> m..n = {}`,
  REWRITE_TAC[NUMSEG_EMPTY]);;

let FINITE_SUBSET_NUMSEG = prove
 (`!s:num->bool. FINITE s <=> ?n. s SUBSET 0..n`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_NUMSEG; LE_0] THEN
    SPEC_TAC(`s:num->bool`,`s:num->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[LE_CASES; LE_REFL; LE_TRANS];
    MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]]);;

let CARD_NUMSEG_LEMMA = prove
 (`!m d. CARD(m..(m+d)) = d + 1`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[ADD_CLAUSES; NUMSEG_REC; NUMSEG_SING; FINITE_RULES;
               ARITH_RULE `m <= SUC(m + d)`; CARD_CLAUSES; FINITE_NUMSEG;
               NOT_IN_EMPTY; ARITH; IN_NUMSEG; ARITH_RULE `~(SUC n <= n)`]);;

let CARD_NUMSEG = prove
 (`!m n. CARD(m..n) = (n + 1) - m`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_THEN MP_TAC (ARITH_RULE `n:num < m \/ m <= n`) THENL
   [ASM_MESON_TAC[NUMSEG_EMPTY; CARD_CLAUSES;
                  ARITH_RULE `n < m ==> ((n + 1) - m = 0)`];
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; CARD_NUMSEG_LEMMA] THEN
    REPEAT STRIP_TAC THEN ARITH_TAC]);;

let HAS_SIZE_NUMSEG = prove
 (`!m n. (m..n) HAS_SIZE ((n + 1) - m)`,
  REWRITE_TAC[HAS_SIZE; FINITE_NUMSEG; CARD_NUMSEG]);;

let CARD_NUMSEG_1 = prove
 (`!n. CARD(1..n) = n`,
  REWRITE_TAC[CARD_NUMSEG] THEN ARITH_TAC);;

let HAS_SIZE_NUMSEG_1 = prove
 (`!n. (1..n) HAS_SIZE n`,
  REWRITE_TAC[CARD_NUMSEG; HAS_SIZE; FINITE_NUMSEG] THEN ARITH_TAC);;

let NUMSEG_CLAUSES = prove
 (`(!m. m..0 = if m = 0 then {0} else {}) /\
   (!m n. m..SUC n = if m <= SUC n then (SUC n) INSERT (m..n) else m..n)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_NUMSEG; NOT_IN_EMPTY; IN_INSERT] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let FINITE_INDEX_NUMSEG = prove
 (`!s:A->bool.
        FINITE s <=>
        ?f. (!i j. i IN 1..CARD s /\ j IN 1..CARD s /\ f i = f j ==> i = j) /\
            s = IMAGE f (1..CARD s)`,
  GEN_TAC THEN
  EQ_TAC THENL [DISCH_TAC; MESON_TAC[FINITE_IMAGE; FINITE_NUMSEG]] THEN
  MP_TAC(ISPECL [`1..CARD(s:A->bool)`; `s:A->bool`]
        CARD_EQ_BIJECTIONS) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

let FINITE_INDEX_NUMBERS = prove
 (`!s:A->bool.
        FINITE s <=>
        ?k:num->bool f. (!i j. i IN k /\ j IN k /\ f i = f j ==> i = j) /\
                        FINITE k /\ s = IMAGE f k`,
  MESON_TAC[FINITE_INDEX_NUMSEG; FINITE_NUMSEG; FINITE_IMAGE]);;

let INTER_NUMSEG = prove
 (`!m n p q. (m..n) INTER (p..q) = (MAX m p)..(MIN n q)`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_NUMSEG] THEN ARITH_TAC);;

let DISJOINT_NUMSEG = prove
 (`!m n p q. DISJOINT (m..n) (p..q) <=> n < p \/ q < m \/ n < m \/ q < p`,
  REWRITE_TAC[DISJOINT; NUMSEG_EMPTY; INTER_NUMSEG] THEN ARITH_TAC);;

let NUMSEG_ADD_SPLIT = prove
 (`!m n p. m <= n + 1 ==> (m..(n+p) = (m..n) UNION (n+1..n+p))`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_NUMSEG] THEN ARITH_TAC);;

let NUMSEG_OFFSET_IMAGE = prove
 (`!m n p. (m+p..n+p) = IMAGE (\i. i + p) (m..n)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> EXISTS_TAC `x - p:num` THEN MP_TAC th); ALL_TAC] THEN
  ARITH_TAC);;

let SUBSET_NUMSEG = prove
 (`!m n p q. (m..n) SUBSET (p..q) <=> n < m \/ p <= m /\ n <= q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
  EQ_TAC THENL [MESON_TAC[LE_TRANS; NOT_LE; LE_REFL]; ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence with the more ad-hoc comprehension notation.                  *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_LE = prove
 (`!n. {x | x <= n} = 0..n`,
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC);;

let NUMSEG_LT = prove
 (`!n. {x | x < n} = if n = 0 then {} else 0..(n-1)`,
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Conversion to evaluate m..n for specific numerals.                        *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_CONV =
  let pth_0 = MESON[NUMSEG_EMPTY] `n < m ==> m..n = {}`
  and pth_1 = MESON[NUMSEG_SING] `m..m = {m}`
  and pth_2 = MESON[NUMSEG_LREC; ADD1] `m <= n ==> m..n = m INSERT (SUC m..n)`
  and ns_tm = `(..)` and m_tm = `m:num` and n_tm = `n:num` in
  let rec NUMSEG_CONV tm =
    let nstm,nt = dest_comb tm in
    let nst,mt = dest_comb nstm in
    if nst <> ns_tm then failwith "NUMSEG_CONV" else
    let m = dest_numeral mt and n = dest_numeral nt in
    if n </ m then MP_CONV NUM_LT_CONV (INST [mt,m_tm; nt,n_tm] pth_0)
    else if n =/ m then INST [mt,m_tm] pth_1
    else let th = MP_CONV NUM_LE_CONV (INST [mt,m_tm; nt,n_tm] pth_2) in
         CONV_RULE(funpow 2 RAND_CONV
          (LAND_CONV NUM_SUC_CONV THENC NUMSEG_CONV)) th in
  NUMSEG_CONV;;

(* ------------------------------------------------------------------------- *)
(* Topological sorting of a finite set.                                      *)
(* ------------------------------------------------------------------------- *)

let TOPOLOGICAL_SORT = prove
 (`!(<<). (!x y:A. x << y /\ y << x ==> x = y) /\
          (!x y z. x << y /\ y << z ==> x << z)
          ==> !n s. s HAS_SIZE n
                    ==> ?f. s = IMAGE f (1..n) /\
                            (!j k. j IN 1..n /\ k IN 1..n /\ j < k
                                   ==> ~(f k << f j))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n s. s HAS_SIZE n /\ ~(s = {})
                      ==> ?a:A. a IN s /\ !b. b IN (s DELETE a) ==> ~(b << a)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[HAS_SIZE_0; HAS_SIZE_SUC; TAUT `~(a /\ ~a)`] THEN
    X_GEN_TAC `s:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A)`) THEN
    ASM_SIMP_TAC[SET_RULE `a IN s ==> (s DELETE a = {} <=> s = {a})`] THEN
    ASM_CASES_TAC `s = {a:A}` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `a:A` THEN SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `((a:A) << (b:A)) :bool` THENL
     [EXISTS_TAC `a:A`; EXISTS_TAC `b:A`] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [SIMP_TAC[HAS_SIZE_0; NUMSEG_CLAUSES; ARITH; IMAGE_CLAUSES; NOT_IN_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE_SUC] THEN X_GEN_TAC `s:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`SUC n`; `s:A->bool`]) THEN
  ASM_REWRITE_TAC[HAS_SIZE_SUC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` MP_TAC) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A)`) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\k. if k = 1 then a:A else f(k - 1)` THEN
  SIMP_TAC[ARITH_RULE `1 <= k ==> ~(SUC k = 1)`; SUC_SUB1] THEN
  SUBGOAL_THEN `!i. i IN 1..SUC n <=> i = 1 \/ 1 < i /\ (i - 1) IN 1..n`
   (fun th -> REWRITE_TAC[EXTENSION; IN_IMAGE; th])
  THENL [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `b:A` THEN ASM_CASES_TAC `b:A = a` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP
     (SET_RULE `~(b = a) ==> (b IN s <=> b IN (s DELETE a))`) th]) THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN
    EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN EXISTS_TAC `i + 1` THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= x ==> 1 < x + 1 /\ ~(x + 1 = 1)`; ADD_SUB];
    MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN
    MAP_EVERY ASM_CASES_TAC [`j = 1`; `k = 1`] THEN
    ASM_REWRITE_TAC[LT_REFL] THENL
     [STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ARITH_TAC;
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Analogous finiteness theorem for segments of integers.                    *)
(* ------------------------------------------------------------------------- *)

let FINITE_INT_SEG = prove
 (`(!l r. FINITE {x:int | l <= x /\ x <= r}) /\
   (!l r. FINITE {x:int | l <= x /\ x < r}) /\
   (!l r. FINITE {x:int | l < x /\ x <= r}) /\
   (!l r. FINITE {x:int | l < x /\ x < r})`,
  MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THEN POP_ASSUM MP_TAC THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN INT_ARITH_TAC;
    REPEAT GEN_TAC THEN ASM_CASES_TAC `&0:int <= r - l` THEN
    ASM_SIMP_TAC[INT_ARITH `~(&0 <= r - l:int) ==> ~(l <= x /\ x <= r)`] THEN
    ASM_SIMP_TAC[EMPTY_GSPEC; FINITE_EMPTY] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\n. l + &n) (0..num_of_int(r - l))` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; IN_NUMSEG] THEN
    X_GEN_TAC `x:int` THEN STRIP_TAC THEN EXISTS_TAC `num_of_int(x - l)` THEN
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_SUB_LE] THEN ASM_INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Generic iteration of operation over set with finite support.              *)
(* ------------------------------------------------------------------------- *)

let neutral = new_definition
  `neutral op = @x:A. !y. (op x y = y) /\ (op y x = y)`;;

let monoidal = new_definition
  `monoidal op <=> (!x y. op x y = op y x) /\
                   (!x y z. op x (op y z) = op (op x y) z) /\
                   (!x:A. op (neutral op) x = x)`;;

let MONOIDAL_AC = prove
 (`!op. monoidal op
        ==> (!a:A. op (neutral op) a = a) /\
            (!a. op a (neutral op) = a) /\
            (!a b. op a b = op b a) /\
            (!a b c. op (op a b) c = op a (op b c)) /\
            (!a b c. op a (op b c) = op b (op a c))`,
  REWRITE_TAC[monoidal] THEN MESON_TAC[]);;

let support = new_definition
  `support op (f:A->B) s = {x | x IN s /\ ~(f x = neutral op)}`;;

let iterate = new_definition
  `iterate op s (f:A->B) =
        if FINITE(support op f s)
        then ITSET (\x a. op (f x) a) (support op f s) (neutral op)
        else neutral op`;;

let IN_SUPPORT = prove
 (`!op (f:A->B) x s. x IN (support op f s) <=> x IN s /\ ~(f x = neutral op)`,
  REWRITE_TAC[support; IN_ELIM_THM]);;

let SUPPORT_SUPPORT = prove
 (`!op (f:A->B) s. support op f (support op f s) = support op f s`,
  REWRITE_TAC[support; IN_ELIM_THM; EXTENSION] THEN REWRITE_TAC[CONJ_ACI]);;

let SUPPORT_EMPTY = prove
 (`!op (f:A->B) s. (!x. x IN s ==> f(x) = neutral op) <=> support op f s = {}`,
  REWRITE_TAC[IN_SUPPORT; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let SUPPORT_SUBSET = prove
 (`!op (f:A->B) s. (support op f s) SUBSET s`,
  SIMP_TAC[SUBSET; IN_SUPPORT]);;

let FINITE_SUPPORT = prove
 (`!op (f:A->B) s. FINITE s ==> FINITE(support op f s)`,
  MESON_TAC[SUPPORT_SUBSET; FINITE_SUBSET]);;

let SUPPORT_CLAUSES = prove
 (`(!(f:A->C). support op f {} = {}) /\
   (!(f:A->C) x s. support op f (x INSERT s) =
        if f(x) = neutral op then support op f s
        else x INSERT (support op f s)) /\
   (!(f:A->C) x s. support op f (s DELETE x) = (support op f s) DELETE x) /\
   (!(f:A->C) s t. support op f (s UNION t) =
                   (support op f s) UNION (support op f t)) /\
   (!(f:A->C) s t. support op f (s INTER t) =
                   (support op f s) INTER (support op f t)) /\
   (!(f:A->C) s t. support op f (s DIFF t) =
                   (support op f s) DIFF (support op f t)) /\
   (!(f:A->B) (g:B->C) s.
                   support op g (IMAGE f s) = IMAGE f (support op (g o f) s))`,
  REWRITE_TAC[support; EXTENSION; IN_ELIM_THM; IN_INSERT; IN_DELETE; o_THM;
    IN_IMAGE; NOT_IN_EMPTY; IN_UNION; IN_INTER; IN_DIFF; COND_RAND] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN ASM_MESON_TAC[]);;

let SUPPORT_DELTA = prove
 (`!op s (f:A->B) a.
        support op (\x. if x = a then f(x) else neutral op) s =
        if a IN s then support op f {a} else {}`,
  REWRITE_TAC[EXTENSION; support; IN_ELIM_THM; IN_SING] THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY]);;

let FINITE_SUPPORT_DELTA = prove
 (`!op (f:A->B) a.
        FINITE(support op (\x. if x = a then f(x) else neutral op) s)`,
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN SIMP_TAC[FINITE_RULES; FINITE_SUPPORT]);;

(* ------------------------------------------------------------------------- *)
(* Key lemmas about the generic notion.                                      *)
(* ------------------------------------------------------------------------- *)

let ITERATE_SUPPORT = prove
 (`!op (f:A->B) s. iterate op (support op f s) f = iterate op s f`,
  SIMP_TAC[iterate; SUPPORT_SUPPORT]);;

let ITERATE_EXPAND_CASES = prove
 (`!op (f:A->B) s.
        iterate op s f =
        if FINITE(support op f s) then iterate op (support op f s) f
        else neutral op`,
  SIMP_TAC[iterate; SUPPORT_SUPPORT]);;

let ITERATE_CLAUSES_GEN = prove
 (`!op. monoidal op
        ==> (!(f:A->B). iterate op {} f = neutral op) /\
            (!f x s. FINITE(support op (f:A->B) s)
                     ==> (iterate op (x INSERT s) f =
                                if x IN s then iterate op s f
                                else op (f x) (iterate op s f)))`,
  GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MP_TAC(ISPECL [`\x a. (op:B->B->B) ((f:A->B)(x)) a`; `neutral op :B`]
   FINITE_RECURSION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[monoidal]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[iterate; SUPPORT_CLAUSES; FINITE_RULES] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [COND_RAND] THEN
  ASM_REWRITE_TAC[SUPPORT_CLAUSES; FINITE_INSERT; COND_ID] THEN
  ASM_CASES_TAC `(f:A->B) x = neutral op` THEN
  ASM_SIMP_TAC[IN_SUPPORT] THEN COND_CASES_TAC THEN ASM_MESON_TAC[monoidal]);;

let ITERATE_CLAUSES = prove
 (`!op. monoidal op
        ==> (!(f:A->C). iterate op {} f = neutral op) /\
            (!(f:B->C) x s.
                FINITE(s)
                ==> (iterate op (x INSERT s) f =
                     if x IN s then iterate op s f
                     else op (f x) (iterate op s f)))`,
  SIMP_TAC[ITERATE_CLAUSES_GEN; FINITE_SUPPORT]);;

let ITERATE_UNION = prove
 (`!op. monoidal op
        ==> !(f:A->B) s t.
                FINITE s /\ FINITE t /\ DISJOINT s t
                ==> (iterate op (s UNION t) f =
                     op (iterate op s f) (iterate op t f))`,
  let lemma = prove
   (`(s UNION (x INSERT t) = x INSERT (s UNION t)) /\
     (DISJOINT s (x INSERT t) <=> ~(x IN s) /\ DISJOINT s t)`,
    SET_TAC[]) in
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; IN_UNION; UNION_EMPTY; REAL_ADD_RID; lemma;
               FINITE_UNION] THEN
  ASM_MESON_TAC[monoidal]);;

let ITERATE_UNION_GEN = prove
 (`!op. monoidal op
        ==> !(f:A->B) s t. FINITE(support op f s) /\ FINITE(support op f t) /\
                           DISJOINT (support op f s) (support op f t)
                           ==> (iterate op (s UNION t) f =
                                op (iterate op s f) (iterate op t f))`,
  ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  SIMP_TAC[SUPPORT_CLAUSES; ITERATE_UNION]);;

let ITERATE_DIFF = prove
 (`!op. monoidal op
        ==> !(f:A->B) s t.
                FINITE s /\ t SUBSET s
                ==> (op (iterate op (s DIFF t) f) (iterate op t f) =
                     iterate op s f)`,
  let lemma = prove
   (`t SUBSET s ==> (s = (s DIFF t) UNION t) /\ DISJOINT (s DIFF t) t`,
    SET_TAC[]) in
  MESON_TAC[lemma; ITERATE_UNION; FINITE_UNION; FINITE_SUBSET; SUBSET_DIFF]);;

let ITERATE_DIFF_GEN = prove
 (`!op. monoidal op
        ==> !f:A->B s t. FINITE (support op f s) /\
                         (support op f t) SUBSET (support op f s)
                         ==> (op (iterate op (s DIFF t) f) (iterate op t f) =
                              iterate op s f)`,
  ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  SIMP_TAC[SUPPORT_CLAUSES; ITERATE_DIFF]);;

let ITERATE_INCL_EXCL = prove
 (`!op. monoidal op
        ==> !s t (f:A->B).
                FINITE s /\ FINITE t
                ==> op (iterate op s f) (iterate op t f) =
                    op (iterate op (s UNION t) f)
                       (iterate op (s INTER t) f)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
    `a UNION b = ((a DIFF b) UNION (b DIFF a)) UNION (a INTER b)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
    [SET_RULE `s:A->bool = s DIFF t UNION s INTER t`] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
    [SET_RULE `t:A->bool = t DIFF s UNION s INTER t`] THEN
  ASM_SIMP_TAC[ITERATE_UNION; FINITE_UNION; FINITE_DIFF; FINITE_INTER;
    SET_RULE `DISJOINT (s DIFF s' UNION s' DIFF s) (s INTER s')`;
    SET_RULE `DISJOINT (s DIFF s') (s' DIFF s)`;
    SET_RULE `DISJOINT (s DIFF s') (s' INTER s)`;
    SET_RULE `DISJOINT (s DIFF s') (s INTER s')`] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MONOIDAL_AC th]));;

let ITERATE_CLOSED = prove
 (`!op. monoidal op
        ==> !P. P(neutral op) /\ (!x y. P x /\ P y ==> P (op x y))
                ==> !f:A->B s. (!x. x IN s /\ ~(f x = neutral op) ==> P(f x))
                               ==> P(iterate op s f)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM IN_SUPPORT] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`support op (f:A->B) s`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; FINITE_INSERT; IN_INSERT]);;

let ITERATE_RELATED = prove
 (`!op. monoidal op
        ==> !R. R (neutral op) (neutral op) /\
                (!x1 y1 x2 y2. R x1 x2 /\ R y1 y2 ==> R (op x1 y1) (op x2 y2))
                ==> !f:A->B g s.
                      FINITE s /\
                      (!x. x IN s ==> R (f x) (g x))
                      ==> R (iterate op s f) (iterate op s g)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; FINITE_INSERT; IN_INSERT]);;

let ITERATE_EQ_NEUTRAL = prove
 (`!op. monoidal op
        ==> !f:A->B s. (!x. x IN s ==> (f(x) = neutral op))
                       ==> (iterate op s f = neutral op)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `support op (f:A->B) s = {}` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTENSION; NOT_IN_EMPTY; IN_SUPPORT];
    ASM_MESON_TAC[ITERATE_CLAUSES; FINITE_RULES; ITERATE_SUPPORT]]);;

let ITERATE_SING = prove
 (`!op. monoidal op ==> !f:A->B x. (iterate op {x} f = f x)`,
  SIMP_TAC[ITERATE_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
  MESON_TAC[monoidal]);;

let ITERATE_CLOSED_NONEMPTY = prove
 (`!op. monoidal op
        ==> !P. (!x y. P x /\ P y ==> P (op x y))
                ==> !f:A->B s. FINITE s /\ ~(s = {}) /\
                               (!x. x IN s ==> P(f x))
                               ==> P(iterate op s f)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; NOT_INSERT_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  ASM_CASES_TAC `t:A->bool = {}` THEN
  ASM_SIMP_TAC[ITERATE_SING] THEN  ASM_SIMP_TAC[ITERATE_CLAUSES]);;

let ITERATE_RELATED_NONEMPTY = prove
 (`!op. monoidal op
        ==> !R. (!x1 y1 x2 y2. R x1 x2 /\ R y1 y2 ==> R (op x1 y1) (op x2 y2))
                ==> !f:A->B g s.
                      FINITE s /\
                      ~(s = {}) /\
                      (!x. x IN s ==> R (f x) (g x))
                      ==> R (iterate op s f) (iterate op s g)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; NOT_INSERT_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  ASM_CASES_TAC `t:A->bool = {}` THEN
  ASM_SIMP_TAC[ITERATE_SING] THEN  ASM_SIMP_TAC[ITERATE_CLAUSES]);;

let ITERATE_DELETE = prove
 (`!op. monoidal op
        ==> !f:A->B s a. FINITE s /\ a IN s
                         ==> op (f a) (iterate op (s DELETE a) f) =
                             iterate op s f`,
  MESON_TAC[ITERATE_CLAUSES; FINITE_DELETE; IN_DELETE; INSERT_DELETE]);;

let ITERATE_DELTA = prove
 (`!op. monoidal op
        ==> !(f:A->B) a s.
                iterate op s (\x. if x = a then f(x) else neutral op) =
                if a IN s then f(a) else neutral op`,
  GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_DELTA] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES] THEN REWRITE_TAC[SUPPORT_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ITERATE_CLAUSES; ITERATE_SING]);;

let ITERATE_IMAGE = prove
 (`!op. monoidal op
       ==> !f:A->B g:B->C s.
                (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
                ==> (iterate op (IMAGE f s) g = iterate op s (g o f))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
   `!s. FINITE s /\
        (!x y:A. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (iterate op (IMAGE f s) (g:B->C) = iterate op s (g o f))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[ITERATE_CLAUSES; IMAGE_CLAUSES; FINITE_IMAGE] THEN
    REWRITE_TAC[o_THM; IN_INSERT] THEN ASM_MESON_TAC[IN_IMAGE];
    GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT
     `(a <=> a') /\ (a' ==> (b = b'))
      ==> (if a then b else c) = (if a' then b' else c)`) THEN
    REWRITE_TAC[SUPPORT_CLAUSES] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN ASM_MESON_TAC[IN_SUPPORT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[IN_SUPPORT]]]);;

let ITERATE_BIJECTION = prove
 (`!op. monoidal op
        ==>  !f:A->B p s.
                (!x. x IN s ==> p(x) IN s) /\
                (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
                ==> iterate op s f = iterate op s (f o p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `iterate op (IMAGE (p:A->A) s) (f:A->B)` THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
      (INST_TYPE [aty,bty] ITERATE_IMAGE))] THEN
  ASM_MESON_TAC[]);;

let ITERATE_ITERATE_PRODUCT = prove
 (`!op. monoidal op
        ==> !s:A->bool t:A->B->bool x:A->B->C.
                FINITE s /\ (!i. i IN s ==> FINITE(t i))
                ==> iterate op s (\i. iterate op (t i) (x i)) =
                    iterate op {i,j | i IN s /\ j IN t i} (\(i,j). x i j)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; SET_RULE `{a,b | F} = {}`; ITERATE_CLAUSES] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN a INSERT s /\ j IN t i} =
            IMAGE (\j. a,j) (t a) UNION {i,j | i IN s /\ j IN t i}`] THEN
  ASM_SIMP_TAC[FINITE_INSERT; ITERATE_CLAUSES; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_UNION th) o
   rand o snd)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_PRODUCT_DEPENDENT; IN_INSERT] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_IMAGE; IN_INTER; NOT_IN_EMPTY;
                IN_ELIM_THM; EXISTS_PAIR_THM; FORALL_PAIR_THM; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) (MATCH_MP ITERATE_IMAGE th) o
   rand o snd)) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FORALL_PAIR_THM] THEN CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_SIMP_TAC[PAIR_EQ];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[ETA_AX]]);;

let ITERATE_EQ = prove
 (`!op. monoidal op
        ==> !f:A->B g s.
              (!x. x IN s ==> f x = g x) ==> iterate op s f = iterate op s g`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN `support op g s = support op (f:A->B) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SUPPORT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `FINITE(support op (f:A->B) s) /\
    (!x. x IN (support op f s) ==> f x = g x)`
  MP_TAC THENL [ASM_MESON_TAC[IN_SUPPORT]; REWRITE_TAC[IMP_CONJ]] THEN
  SPEC_TAC(`support op (f:A->B) s`,`t:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_SIMP_TAC[ITERATE_CLAUSES] THEN
  MESON_TAC[IN_INSERT]);;

let ITERATE_RESTRICT_SET = prove
 (`!op. monoidal op
        ==> !P s f:A->B. iterate op {x | x IN s /\ P x} f =
                         iterate op s (\x. if P x then f x else neutral op)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[support; IN_ELIM_THM] THEN
  REWRITE_TAC[MESON[] `~((if P x then f x else a) = a) <=> P x /\ ~(f x = a)`;
              GSYM CONJ_ASSOC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
  SIMP_TAC[IN_ELIM_THM]);;

let ITERATE_EQ_GENERAL = prove
 (`!op. monoidal op
        ==> !s:A->bool t:B->bool f:A->C g h.
                (!y. y IN t ==> ?!x. x IN s /\ h(x) = y) /\
                (!x. x IN s ==> h(x) IN t /\ g(h x) = f x)
                ==> iterate op s f = iterate op t g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (h:A->B) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `iterate op s ((g:B->C) o (h:A->B))` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ITERATE_EQ; o_THM];
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_IMAGE) THEN
    ASM_MESON_TAC[]]);;

let ITERATE_EQ_GENERAL_INVERSES = prove
 (`!op. monoidal op
        ==> !s:A->bool t:B->bool f:A->C g h k.
                (!y. y IN t ==> k(y) IN s /\ h(k y) = y) /\
                (!x. x IN s ==> h(x) IN t /\ k(h x) = x /\ g(h x) = f x)
                ==> iterate op s f = iterate op t g`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL) THEN
  EXISTS_TAC `h:A->B` THEN ASM_MESON_TAC[]);;

let ITERATE_INJECTION = prove
 (`!op. monoidal op
          ==> !f:A->B p:A->A s.
                      FINITE s /\
                      (!x. x IN s ==> p x IN s) /\
                      (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
                      ==> iterate op s (f o p) = iterate op s f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_BIJECTION) THEN
  MP_TAC(ISPECL [`s:A->bool`; `p:A->A`] SURJECTIVE_IFF_INJECTIVE) THEN
  ASM_REWRITE_TAC[SUBSET; IN_IMAGE] THEN ASM_MESON_TAC[]);;

let ITERATE_UNION_NONZERO = prove
 (`!op. monoidal op
        ==> !f:A->B s t.
                FINITE(s) /\ FINITE(t) /\
                (!x. x IN (s INTER t) ==> f x = neutral(op))
                ==> iterate op (s UNION t) f =
                    op (iterate op s f) (iterate op t f)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[SUPPORT_CLAUSES] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_UNION) THEN
  ASM_SIMP_TAC[FINITE_SUPPORT; DISJOINT; IN_INTER; IN_SUPPORT; EXTENSION] THEN
  ASM_MESON_TAC[IN_INTER; NOT_IN_EMPTY]);;

let ITERATE_OP = prove
 (`!op. monoidal op
        ==> !(f:A->B) g s.
                FINITE s
                ==> iterate op s (\x. op (f x) (g x)) =
                    op (iterate op s f) (iterate op s g)`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_AC]);;

let ITERATE_SUPERSET = prove
 (`!op. monoidal op
        ==> !f:A->B u v.
                u SUBSET v /\
                (!x. x IN v /\ ~(x IN u) ==> f(x) = neutral op)
                ==> iterate op v f = iterate op u f`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[support; EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET]);;

let ITERATE_UNIV = prove
 (`!op. monoidal op
        ==> !f:A->B s. support op f UNIV SUBSET s
                  ==> iterate op s f = iterate op UNIV f`,
  REWRITE_TAC[support; SUBSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN
  ASM SET_TAC[]);;

let ITERATE_SWAP = prove
 (`!op. monoidal op
        ==> !f:A->B->C s t.
                FINITE s /\ FINITE t
                ==> iterate op s (\i. iterate op t (f i)) =
                    iterate op t (\j. iterate op s (\i. f i j))`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES] THEN
  ASM_SIMP_TAC[ITERATE_EQ_NEUTRAL; GSYM ITERATE_OP]);;

let ITERATE_IMAGE_NONZERO = prove
 (`!op. monoidal op
        ==> !g:B->C f:A->B s.
                    FINITE s /\
                    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ f x = f y
                           ==> g(f x) = neutral op)
                    ==> iterate op (IMAGE f s) g = iterate op s (g o f)`,
  GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; ITERATE_CLAUSES; FINITE_IMAGE] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `iterate op s ((g:B->C) o (f:A->B)) = iterate op (IMAGE f s) g`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(g:B->C) ((f:A->B) a) = neutral op` SUBST1_TAC THEN
  ASM_MESON_TAC[MONOIDAL_AC]);;

let ITERATE_IMAGE_GEN = prove
 (`!op. monoidal op
        ==> !f:A->B g:A->C s.
                FINITE s
                ==> iterate op s g =
                    iterate op (IMAGE f s)
                       (\y. iterate op {x | x IN s /\ f x = y} g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `iterate op s (\x:A. iterate op {y:B | y IN IMAGE f s /\ (f x = y)}
       (\y. (g:A->C) x))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{y | y IN IMAGE (f:A->B) s /\ f x = y} = {(f x)}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[ITERATE_SING]];
    ASM_SIMP_TAC[ITERATE_RESTRICT_SET] THEN
    FIRST_ASSUM(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
     (MATCH_MP ITERATE_SWAP th) o lhand o snd)) THEN
    ASM_SIMP_TAC[FINITE_IMAGE]]);;

let ITERATE_CASES = prove
 (`!op. monoidal op
        ==> !s P f g:A->B.
                FINITE s
                ==> iterate op s (\x. if P x then f x else g x) =
                    op (iterate op {x | x IN s /\ P x} f)
                       (iterate op {x | x IN s /\ ~P x} g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `op (iterate op {x | x IN s /\ P x} (\x. if P x then f x else (g:A->B) x))
       (iterate op {x | x IN s /\ ~P x} (\x. if P x then f x else g x))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> ASM_SIMP_TAC[GSYM(MATCH_MP ITERATE_UNION th);
      FINITE_RESTRICT;
      SET_RULE `DISJOINT {x | x IN s /\ P x} {x | x IN s /\ ~P x}`]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[];
    BINOP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ) THEN
    SIMP_TAC[IN_ELIM_THM]]);;

let ITERATE_OP_GEN = prove
 (`!op. monoidal op
        ==> !f g:A->B s.
                FINITE(support op f s) /\ FINITE(support op g s)
                ==> iterate op s (\x. op (f x) (g x)) =
                    op (iterate op s f) (iterate op s g)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `iterate op (support op f s UNION support op g s)
                         (\x. op ((f:A->B) x) (g x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV;
    ASM_SIMP_TAC[ITERATE_OP; FINITE_UNION] THEN BINOP_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN
  REWRITE_TAC[support; IN_ELIM_THM; SUBSET; IN_UNION] THEN
  ASM_MESON_TAC[monoidal]);;

let ITERATE_CLAUSES_NUMSEG = prove
 (`!op. monoidal op
        ==> (!m. iterate op (m..0) f = if m = 0 then f(0) else neutral op) /\
            (!m n. iterate op (m..SUC n) f :A =
                   if m <= SUC n then op (iterate op (m..n) f) (f(SUC n))
                   else iterate op (m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; FINITE_NUMSEG; IN_NUMSEG; FINITE_EMPTY] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[monoidal]);;

let ITERATE_CLAUSES_NUMSEG_LT = prove
 (`!op. monoidal op
        ==> iterate op {i | i < 0} f :A = neutral op /\
            (!k. iterate op {i | i < SUC k} f =
                 op (iterate op {i | i < k} f) (f k))`,
  SIMP_TAC[NUMSEG_CLAUSES_LT; ITERATE_CLAUSES; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_ELIM_THM; LT_REFL; monoidal] THEN MESON_TAC[]);;

let ITERATE_CLAUSES_NUMSEG_LE = prove
 (`!op. monoidal op
        ==> iterate op {i | i <= 0} f :A = f 0 /\
            (!k. iterate op {i | i <= SUC k} f =
                 op (iterate op {i | i <= k} f) (f(SUC k)))`,
  SIMP_TAC[NUMSEG_CLAUSES_LE; ITERATE_CLAUSES;
           FINITE_NUMSEG_LE; ITERATE_SING] THEN
  REWRITE_TAC[monoidal; IN_ELIM_THM; ARITH_RULE `~(SUC k <= k)`] THEN
  MESON_TAC[]);;

let ITERATE_PAIR = prove
 (`!op. monoidal op
        ==> !f m n. iterate op (2*m..2*n+1) f :A =
                    iterate op (m..n) (\i. op (f(2*i)) (f(2*i+1)))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN CONV_TAC NUM_REDUCE_CONV THENL
   [ASM_SIMP_TAC[num_CONV `1`; ITERATE_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `2 * m <= SUC 0 <=> m = 0`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_EQ_0; ARITH];
    REWRITE_TAC[ARITH_RULE `2 * SUC n + 1 = SUC(SUC(2 * n + 1))`] THEN
    ASM_SIMP_TAC[ITERATE_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `2 * m <= SUC(SUC(2 * n + 1)) <=> m <= SUC n`;
                ARITH_RULE `2 * m <= SUC(2 * n + 1) <=> m <= SUC n`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * SUC n = SUC(2 * n + 1)`;
                ARITH_RULE `2 * SUC n + 1 = SUC(SUC(2 * n + 1))`] THEN
    ASM_MESON_TAC[monoidal]]);;

let ITERATE_REFLECT = prove
 (`!op:A->A->A.
        monoidal op
        ==> !x m n. iterate op (m..n) x =
                    if n < m then neutral op
                    else iterate op (0..n-m) (\i. x(n - i))`,
  REWRITE_TAC[GSYM NUMSEG_EMPTY] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[ITERATE_CLAUSES];
    RULE_ASSUM_TAC(REWRITE_RULE[NUMSEG_EMPTY; NOT_LT])] THEN
  FIRST_ASSUM(MP_TAC o
   ISPECL [`\i:num. n - i`; `x:num->A`; `0..n-m`] o
   MATCH_MP (INST_TYPE [`:X`,`:A`] ITERATE_IMAGE)) THEN
  REWRITE_TAC[o_DEF; IN_NUMSEG] THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  REWRITE_TAC[UNWIND_THM2; ARITH_RULE
    `x = n - y /\ 0 <= y /\ y <= n - m <=>
     y = n - x /\ x <= n /\ y <= n - m`] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A more general notion of iteration, using a specific order (<<=)          *)
(* and hence applying to non-commutative operations, as well as giving       *)
(* more refined notions of domain ("dom") and neutral element ("neut").      *)
(* Otherwise it tries to be stylistically similar to "iterate" above.        *)
(* ------------------------------------------------------------------------- *)

let iterato = (new_specification ["iterato"] o prove)
 (`?itty.
      !dom neut op (<<=) k (f:K->A).
         itty dom neut op (<<=) k f =
         if FINITE {i | i IN k /\ f i IN dom DIFF {neut}} /\
            ~({i | i IN k /\ f i IN dom DIFF {neut}} = {})
         then let i = if ?i. i IN k /\ f i IN dom DIFF {neut} /\
                             !j. j <<= i /\ j IN k /\ f j IN dom DIFF {neut}
                                 ==> j = i
                       then @i. i IN k /\ f i IN dom DIFF {neut} /\
                                !j. j <<= i /\ j IN k /\
                                    f j IN dom DIFF {neut}
                                    ==> j = i
                       else @i. i IN k /\ f i IN dom DIFF {neut} in
              op (f i) (itty dom neut op (<<=)
                          {j | j IN k DELETE i /\ f j IN dom DIFF {neut}} f)
         else neut`,
  REPLICATE_TAC 4 (ONCE_REWRITE_TAC[GSYM SKOLEM_THM]) THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [EXISTS_SWAP_FUN_THM] THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC(MATCH_MP WF_REC (ISPEC
   `\k. CARD {i | i IN k /\ (f:K->A) i IN dom DIFF {neut}}` WF_MEASURE)) THEN
  REWRITE_TAC[MEASURE] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[SET_RULE
   `{i | i IN k DIFF {a} /\ P i} = {i | i IN k /\ P i} DELETE a`] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[PSUBSET_ALT] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DELETE; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[SET_RULE `p /\ q /\ ~(p /\ ~r /\ q) <=> r /\ p /\ q`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o CONJUNCT2) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN ASM_MESON_TAC[]);;

let ITERATO_SUPPORT = prove
 (`!dom neut op (<<=) k (f:K->A).
        iterato dom neut op (<<=) {i | i IN k /\ f i IN dom DIFF {neut}} f =
        iterato dom neut op (<<=) k f`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[iterato] THEN
  REWRITE_TAC[CONJ_ASSOC; SET_RULE `y IN {x | x IN s /\ P x} /\ P y <=>
                        y IN {x | x IN s /\ P x}`] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN LET_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let ITERATO_EXPAND_CASES = prove
 (`!dom neut op (<<=) k (f:K->A).
        iterato dom neut op (<<=) k f =
        if FINITE {i | i IN k /\ f i IN dom DIFF {neut}}
        then iterato dom neut op (<<=) {i | i IN k /\ f i IN dom DIFF {neut}} f
        else neut`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[ITERATO_SUPPORT];
    GEN_REWRITE_TAC LAND_CONV [iterato] THEN ASM_REWRITE_TAC[]]);;

let ITERATO_CLAUSES_GEN = prove
 (`!dom neut op (<<=) (f:K->A).
        (iterato dom neut op (<<=) {} f = neut) /\
        (!i k. FINITE {j | j IN k /\ f j IN dom DIFF {neut}} /\
               (!j. j IN k ==> i = j \/ i <<= j \/ j <<= i) /\
               (!j. j <<= i /\ j IN k /\ f j IN dom DIFF {neut} ==> j = i)
               ==> iterato dom neut op (<<=) (i INSERT k) f =
                   if f i IN dom ==> f i = neut \/ i IN k
                   then iterato dom neut op (<<=) k f
                   else op (f i) (iterato dom neut op (<<=) k f))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [iterato] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC];
    REPEAT GEN_TAC THEN STRIP_TAC] THEN
  ASM_CASES_TAC `(i:K) IN k` THEN
  ASM_SIMP_TAC[COND_SWAP; SET_RULE `i IN k ==> i INSERT k = k`] THEN
  REWRITE_TAC[SET_RULE `x IN dom ==> x = a <=> ~(x IN dom DIFF {a})`] THEN
  REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [iterato] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_DIFF]) THEN
    REWRITE_TAC[IN_SING] THEN STRIP_TAC;
    ONCE_REWRITE_TAC[GSYM ITERATO_SUPPORT] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC(MESON[]
   `q /\ p /\ x = z ==> (if p /\ q then x else y) = z`) THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `i INSERT {j | j IN k /\ (f:K->A) j IN dom DIFF {neut}}` THEN
    ASM_REWRITE_TAC[FINITE_INSERT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(K ALL_TAC o check (is_exists o concl));
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM SET_TAC[]] THEN
  SUBGOAL_THEN
   `(@i'. i' IN i INSERT k /\
          (f:K->A) i' IN dom DIFF {neut} /\
          (!j. j <<= i' /\ j IN i INSERT k /\ f j IN dom DIFF {neut}
               ==> j = i')) = i`
  SUBST1_TAC THENL
   [ALL_TAC;
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC[SET_RULE `~(i IN k) ==> (i INSERT k) DELETE i = k`] THEN
    REWRITE_TAC[ITERATO_SUPPORT]] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `j:K` THEN
  REWRITE_TAC[] THEN EQ_TAC THEN SIMP_TAC[] THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_CASES_TAC `j:K = i` THEN ASM_REWRITE_TAC[IN_INSERT] THEN ASM SET_TAC[]);;

let ITERATO_CLAUSES = prove
 (`!dom neut op (<<=) (f:K->A).
        (iterato dom neut op (<<=) {} f = neut) /\
        (!i k. FINITE {i | i IN k /\ f i IN dom DIFF {neut}} /\
               (!j. j IN k ==> i <<= j /\ ~(j <<= i))
               ==> iterato dom neut op (<<=) (i INSERT k) f =
                   if f i IN dom ==> f i = neut \/ i IN k
                   then iterato dom neut op (<<=) k f
                   else op (f i) (iterato dom neut op (<<=) k f))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ITERATO_CLAUSES_GEN] THEN
  MATCH_MP_TAC(CONJUNCT2(SPEC_ALL ITERATO_CLAUSES_GEN)) THEN
  ASM_MESON_TAC[]);;

let ITERATO_CLAUSES_EXISTS = prove
 (`!dom neut op (<<=) (f:K->A).
        (iterato dom neut op (<<=) {} f = neut) /\
        (!k. FINITE {i | i IN k /\ f i IN dom DIFF {neut}} /\
             ~({i | i IN k /\ f i IN dom DIFF {neut}} = {})
             ==> ?i. i IN k /\ f i IN dom DIFF {neut} /\
                     iterato dom neut op (<<=) k f =
                     op (f i) (iterato dom neut op (<<=) (k DELETE i) f))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [iterato] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC];
    REPEAT GEN_TAC THEN STRIP_TAC] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o RAND_CONV o LAND_CONV)
   [iterato] THEN
  ASM_REWRITE_TAC[] THEN LET_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o funpow 4 RAND_CONV)
   [GSYM ITERATO_SUPPORT] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `t = i ==> (t = i ==> P i) ==> ?j. P j`)) THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THENL [DISCH_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let ITERATO_EQ = prove
 (`!dom neut op (<<=) k f (g:K->A).
        (!i. i IN k ==> f i = g i)
        ==> iterato dom neut op (<<=) k f = iterato dom neut op (<<=) k g`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ITERATO_EXPAND_CASES] THEN
  ASM_SIMP_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  REWRITE_TAC[NOT_IMP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i. i IN {i | i IN k /\ (g:K->A) i IN dom DIFF {neut}} ==> f i = g i`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `FINITE {i | i IN k /\ (g:K->A) i IN dom DIFF {neut}}` THEN
  SPEC_TAC(`{i | i IN k /\ (g:K->A) i IN dom DIFF {neut}}`,`k:K->bool`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN MATCH_MP_TAC(MESON[]
   `(!n k. FINITE k /\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)`) THEN
  REWRITE_TAC[IMP_IMP] THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `k:K->bool` THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE
   [IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM CONJ_ASSOC]) THEN
  ASM_CASES_TAC `k:K->bool = {}` THEN
  ASM_REWRITE_TAC[ITERATO_CLAUSES_EXISTS] THEN ONCE_REWRITE_TAC[iterato] THEN
    SUBGOAL_THEN `!s i. i IN k /\ (f:K->A) i IN s <=> i IN k /\ g i IN s`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[CONJ_ASSOC]] THEN
  ASM_REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN LET_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(i:K) IN k` ASSUME_TAC THENL
   [EXPAND_TAC "i" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM]) THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN MESON_TAC[];
    ALL_TAC] THEN
  BINOP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SET_RULE
   `{j | j IN s DELETE i /\ P j} = {j | j IN s /\ P j} DELETE i`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_RESTRICT; IN_DELETE; IN_ELIM_THM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[]);;

let ITERATO_INDUCT = prove
 (`!dom neut op (<<=) k (f:K->A) P.
        P neut /\
        (!i x. i IN k /\ f i IN dom /\ ~(f i = neut) /\ P x ==> P (op (f i) x))
        ==> P(iterato dom neut op (<<=) k f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SET_RULE
   `i IN k /\ f i IN s /\ ~(f i = z) /\ Q <=>
    i IN {j | j IN k /\ f j IN s DIFF {z}} /\ Q`] THEN
  ONCE_REWRITE_TAC[ITERATO_EXPAND_CASES] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN SIMP_TAC[] THEN
  REWRITE_TAC[TAUT
   `(a /\ p ==> if q then r else T) <=> a ==> q ==> p ==> r`] THEN
  STRIP_TAC THEN
  SPEC_TAC(`{i | i IN k /\ (f:K->A) i IN dom DIFF {neut}}`,`k:K->bool`) THEN
  MATCH_MP_TAC(MESON[]
   `(!n k. FINITE k /\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)`) THEN
  REWRITE_TAC[IMP_IMP] THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `k:K->bool` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM CONJ_ASSOC]) THEN
  ASM_CASES_TAC `k:K->bool = {}` THEN
  ASM_REWRITE_TAC[ITERATO_CLAUSES_EXISTS] THEN
  MP_TAC(ISPECL
   [`dom:A->bool`; `neut:A`; `op:A->A->A`; `(<<=):K->K->bool`; `f:K->A`]
   ITERATO_CLAUSES_EXISTS) THEN
  DISCH_THEN(MP_TAC o SPEC `k:K->bool` o CONJUNCT2) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN MATCH_MP_TAC(TAUT
   `(p ==> r) /\ (q ==> r) ==> (~p ==> q) ==> r`) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ITERATO_SUPPORT] THEN SIMP_TAC[] THEN
    ASM_REWRITE_TAC[ITERATO_CLAUSES_EXISTS];
    DISCH_THEN(X_CHOOSE_THEN `i:K` MP_TAC)] THEN
  REWRITE_TAC[IN_DIFF; IN_SING] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `n - 1` THEN
  ASM_SIMP_TAC[CARD_DELETE; FINITE_DELETE; IN_DELETE] THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_MESON_TAC[CARD_EQ_0]);;

let ITERATO_CLOSED = prove
 (`!dom neut op (<<=) k (f:K->A) P.
        P neut /\
        (!x y. P x /\ P y ==> P(op x y)) /\
        (!i. i IN k /\ f i IN dom /\ ~(f i = neut) ==> P(f i))
        ==> P(iterato dom neut op (<<=) k f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ITERATO_INDUCT THEN ASM_SIMP_TAC[]);;

let ITERATO_ITERATE = prove
 (`!(op:A->A->A) ((<<=):K->K->bool).
        monoidal op ==> iterato (:A) (neutral op) op (<<=) = iterate op`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:K->bool`; `f:K->A`] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES; ITERATO_EXPAND_CASES] THEN
  REWRITE_TAC[support; IN_UNIV; IN_DIFF; IN_SING] THEN MATCH_MP_TAC(MESON[]
   `(p ==> x = y) ==> (if p then x else z) = (if p then y else z)`) THEN
  SPEC_TAC(`{i | i IN k /\ ~((f:K->A) i = neutral op)}`,`k:K->bool`) THEN
  MATCH_MP_TAC(MESON[]
   `(!n k. FINITE k /\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)`) THEN
  REWRITE_TAC[IMP_IMP] THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `k:K->bool` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM CONJ_ASSOC]) THEN
  ASM_CASES_TAC `k:K->bool = {}` THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; ITERATO_CLAUSES_EXISTS] THEN
  MP_TAC(ISPECL
   [`(:A)`; `neutral op:A`; `op:A->A->A`; `(<<=):K->K->bool`; `f:K->A`]
   ITERATO_CLAUSES_EXISTS) THEN
  DISCH_THEN(MP_TAC o SPEC `k:K->bool` o CONJUNCT2) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN MATCH_MP_TAC(TAUT
   `(p ==> r) /\ (q ==> r) ==> (~p ==> q) ==> r`) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ITERATO_SUPPORT; GSYM ITERATE_SUPPORT] THEN
    REWRITE_TAC[support; IN_UNIV; IN_DIFF; IN_SING] THEN
    ASM_SIMP_TAC[ITERATE_CLAUSES; ITERATO_CLAUSES_EXISTS];
    DISCH_THEN(X_CHOOSE_THEN `i:K` MP_TAC)] THEN
  REWRITE_TAC[IN_DIFF; IN_SING] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `k DELETE (i:K)`]) THEN
  REWRITE_TAC[ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CARD_EQ_0]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL [`f:K->A`; `i:K`; `k DELETE (i:K)`] o
    CONJUNCT2 o MATCH_MP ITERATE_CLAUSES) THEN
  ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[SET_RULE `i IN k ==> i INSERT (k DELETE i) = k`]);;

let ITERATO_CLAUSES_NUMSEG_LEFT = prove
 (`!dom neut op (f:num->A) m n.
       iterato dom neut op (<=) (m..n) f =
         if m <= n then
           if f m IN dom ==> f m = neut
           then iterato dom neut op (<=) (m+1..n) f
           else op (f m) (iterato dom neut op (<=) (m+1..n) f)
         else neut`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
     [`dom:A->bool`; `neut:A`; `op:A->A->A`;
      `(<=):num->num->bool`; `f:num->A`] ITERATO_CLAUSES_GEN) THEN
  COND_CASES_TAC THENL
   [DISCH_THEN(fun th -> ASM_SIMP_TAC[GSYM NUMSEG_LREC] THEN MP_TAC th);
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_MESON_TAC[NUMSEG_EMPTY; NOT_LE]] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `m+1..n`] o CONJUNCT2) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG; IN_NUMSEG] THEN ARITH_TAC;
    REWRITE_TAC[IN_NUMSEG; ARITH_RULE `~(m + 1 <= m)`]]);;

(* ------------------------------------------------------------------------- *)
(* Four iterated operations where we just more or less express the basic     *)
(* definition and clausal form of the recursion, but don't develop any       *)
(* more lemmas; for products load "Library/products.ml" and for sums of      *)
(* intgers load "Library/isum.ml".                                           *)
(* ------------------------------------------------------------------------- *)

let nproduct = new_definition
  `nproduct:(A->bool)->(A->num)->num = iterate(( * ):num->num->num)`;;

let NEUTRAL_MUL = prove
 (`neutral(( * ):num->num->num) = 1`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[MULT_CLAUSES; MULT_EQ_1]);;

let MONOIDAL_MUL = prove
 (`monoidal(( * ):num->num->num)`,
  REWRITE_TAC[monoidal; NEUTRAL_MUL] THEN ARITH_TAC);;

let NPRODUCT_CLAUSES = prove
 (`(!f:A->num. nproduct {} f = 1) /\
   (!x (f:B->num) s.
        FINITE(s)
        ==> (nproduct (x INSERT s) f =
             if x IN s then nproduct s f else f(x) * nproduct s f))`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_MUL]);;

let iproduct = new_definition
  `iproduct:(A->bool)->(A->int)->int = iterate (( * ):int->int->int)`;;

let NEUTRAL_INT_MUL = prove
 (`neutral(( * ):int->int->int) = &1`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[INT_MUL_LID; INT_MUL_RID]);;

let MONOIDAL_INT_MUL = prove
 (`monoidal(( * ):int->int->int)`,
  REWRITE_TAC[monoidal; NEUTRAL_INT_MUL] THEN INT_ARITH_TAC);;

let IPRODUCT_CLAUSES = prove
 (`(!f:A->int. iproduct {} f = &1) /\
   (!x (f:B->int) s.
        FINITE(s)
        ==> (iproduct (x INSERT s) f =
             if x IN s then iproduct s f else f(x) * iproduct s f))`,
  REWRITE_TAC[iproduct; GSYM NEUTRAL_INT_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_INT_MUL]);;

let product = new_definition
  `product:(A->bool)->(A->real)->real = iterate (( * ):real->real->real)`;;

let NEUTRAL_REAL_MUL = prove
 (`neutral(( * ):real->real->real) = &1`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[REAL_MUL_LID; REAL_MUL_RID]);;

let MONOIDAL_REAL_MUL = prove
 (`monoidal(( * ):real->real->real)`,
  REWRITE_TAC[monoidal; NEUTRAL_REAL_MUL] THEN REAL_ARITH_TAC);;

let PRODUCT_CLAUSES = prove
 (`(!f:A->real. product {} f = &1) /\
   (!x (f:B->real) s.
        FINITE(s)
        ==> (product (x INSERT s) f =
             if x IN s then product s f else f(x) * product s f))`,
  REWRITE_TAC[product; GSYM NEUTRAL_REAL_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_REAL_MUL]);;

let isum = new_definition
 `isum:(A->bool)->(A->int)->int = iterate((+):int->int->int)`;;

let NEUTRAL_INT_ADD = prove
 (`neutral((+):int->int->int) = &0`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[INT_ADD_LID; INT_ADD_RID]);;

let MONOIDAL_INT_ADD = prove
 (`monoidal((+):int->int->int)`,
  REWRITE_TAC[monoidal; NEUTRAL_INT_ADD] THEN INT_ARITH_TAC);;

let ISUM_CLAUSES = prove
 (`(!f:A->int. isum {} f = &0) /\
   (!x (f:B->int) s.
        FINITE(s)
        ==> (isum (x INSERT s) f =
             if x IN s then isum s f else f(x) + isum s f))`,
  REWRITE_TAC[isum; GSYM NEUTRAL_INT_ADD] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_INT_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Sums of natural numbers.                                                  *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

let nsum = new_definition
  `nsum:(A->bool)->(A->num)->num = iterate (+)`;;

let NEUTRAL_ADD = prove
 (`neutral((+):num->num->num) = 0`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[ADD_CLAUSES]);;

let MONOIDAL_ADD = prove
 (`monoidal((+):num->num->num)`,
  REWRITE_TAC[monoidal; NEUTRAL_ADD] THEN ARITH_TAC);;

let NSUM_DEGENERATE = prove
 (`!f s:A->bool. ~(FINITE {x | x IN s /\ ~(f x = 0)}) ==> nsum s f = 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nsum] THEN
  SIMP_TAC[iterate; support; NEUTRAL_ADD]);;

let NSUM_CLAUSES = prove
 (`(!f:A->num. nsum {} f = 0) /\
   (!x (f:B->num) s.
        FINITE(s)
        ==> (nsum (x INSERT s) f =
             if x IN s then nsum s f else f(x) + nsum s f))`,
  REWRITE_TAC[nsum; GSYM NEUTRAL_ADD] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_UNION = prove
 (`!f s t:A->bool.
        FINITE s /\ FINITE t /\ DISJOINT s t
        ==> nsum (s UNION t) f = nsum s f + nsum t f`,
  SIMP_TAC[nsum; ITERATE_UNION; MONOIDAL_ADD]);;

let NSUM_DIFF = prove
 (`!f s t:A->bool.
        FINITE s /\ t SUBSET s
        ==> nsum (s DIFF t) f = nsum s f - nsum t f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `(x + z = y:num) ==> (x = y - z)`) THEN
  ASM_SIMP_TAC[nsum; ITERATE_DIFF; MONOIDAL_ADD]);;

let NSUM_INCL_EXCL = prove
 (`!s t (f:A->num).
     FINITE s /\ FINITE t
     ==> nsum s f + nsum t f = nsum (s UNION t) f + nsum (s INTER t) f`,
  REWRITE_TAC[nsum; GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_INCL_EXCL THEN REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_SUPPORT = prove
 (`!f s:A->bool. nsum (support (+) f s) f = nsum s f`,
  SIMP_TAC[nsum; iterate; SUPPORT_SUPPORT]);;

let NSUM_ADD = prove
 (`!f g s:A->bool.
        FINITE s ==> (nsum s (\x. f(x) + g(x)) = nsum s f + nsum s g)`,
  SIMP_TAC[nsum; ITERATE_OP; MONOIDAL_ADD]);;

let NSUM_ADD_GEN = prove
 (`!f g s:A->bool.
        FINITE {x | x IN s /\ ~(f x = 0)} /\ FINITE {x | x IN s /\ ~(g x = 0)}
        ==> nsum s (\x. f x + g x) = nsum s f + nsum s g`,
  REWRITE_TAC[GSYM NEUTRAL_ADD; GSYM support; nsum] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_ADD);;

let NSUM_EQ_0 = prove
 (`!f s:A->bool. (!x. x IN s ==> f(x) = 0) ==> nsum s f = 0`,
  REWRITE_TAC[nsum; GSYM NEUTRAL_ADD] THEN
  SIMP_TAC[ITERATE_EQ_NEUTRAL; MONOIDAL_ADD]);;

let NSUM_0 = prove
 (`!s:A->bool. nsum s (\n. 0) = 0`,
  SIMP_TAC[NSUM_EQ_0]);;

let NSUM_LMUL = prove
 (`!f c s:A->bool. nsum s (\x. c * f(x)) = c * nsum s f`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; NSUM_0] THEN REWRITE_TAC[nsum] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN `support (+) (\x:A. c * f(x)) s = support (+) f s` SUBST1_TAC
  THENL [ASM_SIMP_TAC[support; MULT_EQ_0; NEUTRAL_ADD]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NEUTRAL_ADD; MULT_CLAUSES] THEN
  UNDISCH_TAC `FINITE (support (+) f (s:A->bool))` THEN
  SPEC_TAC(`support (+) f (s:A->bool)`,`t:A->bool`) THEN
  REWRITE_TAC[GSYM nsum] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; MULT_CLAUSES; LEFT_ADD_DISTRIB]);;

let NSUM_RMUL = prove
 (`!f c s:A->bool. nsum s (\x. f(x) * c) = nsum s f * c`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[NSUM_LMUL]);;

let NSUM_LE = prove
 (`!f g s:A->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x))
        ==> nsum s f <= nsum s g`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; LE_REFL; LE_ADD2; IN_INSERT]);;

let NSUM_LT = prove
 (`!f g s:A->bool.
         FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) /\
         (?x. x IN s /\ f(x) < g(x))
         ==> nsum s f < nsum s g`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s = (a:A) INSERT (s DELETE a)` SUBST1_TAC THENL
   [UNDISCH_TAC `a:A IN s` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[LTE_ADD2; NSUM_LE; IN_DELETE; FINITE_DELETE]);;

let NSUM_LT_ALL = prove
 (`!f g s:A->bool.
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < g(x))
        ==> nsum s f < nsum s g`,
  MESON_TAC[MEMBER_NOT_EMPTY; LT_IMP_LE; NSUM_LT]);;

let NSUM_EQ = prove
 (`!f g s:A->bool. (!x. x IN s ==> f x = g x) ==> nsum s f = nsum s g`,
  REWRITE_TAC[nsum] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_CONST = prove
 (`!c s:A->bool. FINITE s ==> (nsum s (\n. c) = (CARD s) * c)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; CARD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ARITH_TAC);;

let NSUM_POS_BOUND = prove
 (`!f b s:A->bool. FINITE s /\ nsum s f <= b ==> !x:A. x IN s ==> f x <= b`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; NOT_IN_EMPTY; IN_INSERT] THEN
  MESON_TAC[LE_0; ARITH_RULE
   `0 <= x /\ 0 <= y /\ x + y <= b ==> x <= b /\ y <= b`]);;

let NSUM_EQ_0_IFF = prove
 (`!s:A->bool. FINITE s ==> (nsum s f = 0 <=> !x. x IN s ==> f x = 0)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[NSUM_EQ_0] THEN
  ASM_MESON_TAC[ARITH_RULE `n = 0 <=> n <= 0`; NSUM_POS_BOUND]);;

let NSUM_POS_LT = prove
 (`!f s:A->bool.
        FINITE s /\ (?x. x IN s /\ 0 < f x)
        ==> 0 < nsum s f`,
  SIMP_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`; NSUM_EQ_0_IFF] THEN MESON_TAC[]);;

let NSUM_POS_LT_ALL = prove
 (`!s f:A->num.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> 0 < f i) ==> 0 < nsum s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_POS_LT THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; REAL_LT_IMP_LE]);;

let NSUM_DELETE = prove
 (`!f s a:A. FINITE s /\ a IN s ==> f(a) + nsum(s DELETE a) f = nsum s f`,
  SIMP_TAC[nsum; ITERATE_DELETE; MONOIDAL_ADD]);;

let NSUM_SING = prove
 (`!f x:A. nsum {x} f = f(x)`,
  SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ADD_CLAUSES]);;

let NSUM_DELTA = prove
 (`!s a. nsum s (\x. if x = a:A then b else 0) = if a IN s then b else 0`,
  REWRITE_TAC[nsum; GSYM NEUTRAL_ADD] THEN
  SIMP_TAC[ITERATE_DELTA; MONOIDAL_ADD]);;

let NSUM_SWAP = prove
 (`!f:A->B->num s t.
      FINITE(s) /\ FINITE(t)
      ==> (nsum s (\i. nsum t (f i)) = nsum t (\j. nsum s (\i. f i j)))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; NSUM_0; NSUM_ADD; ETA_AX]);;

let NSUM_IMAGE = prove
 (`!(f:A->B) g s.
        (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
        ==> (nsum (IMAGE f s) g = nsum s (g o f))`,
  REWRITE_TAC[nsum; GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_SUPERSET = prove
 (`!f:A->num u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 0))
        ==> (nsum v f = nsum u f)`,
  SIMP_TAC[nsum; GSYM NEUTRAL_ADD; ITERATE_SUPERSET; MONOIDAL_ADD]);;

let NSUM_UNIV = prove
 (`!f:A->num s. support (+) f (:A) SUBSET s ==> nsum s f = nsum (:A) f`,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_UNIV THEN
  REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_UNION_RZERO = prove
 (`!f:A->num u v.
        FINITE u /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = 0))
        ==> nsum (u UNION v) f = nsum u f`,
  let lemma = prove(`u UNION v = u UNION (v DIFF u)`,SET_TAC[]) in
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[lemma] THEN
  MATCH_MP_TAC NSUM_SUPERSET THEN ASM_MESON_TAC[IN_UNION; IN_DIFF; SUBSET]);;

let NSUM_UNION_LZERO = prove
 (`!f:A->num u v.
        FINITE v /\ (!x. x IN u /\ ~(x IN v) ==> (f(x) = 0))
        ==> nsum (u UNION v) f = nsum v f`,
  MESON_TAC[NSUM_UNION_RZERO; UNION_COMM]);;

let NSUM_RESTRICT = prove
 (`!f s:A->bool.
        FINITE s ==> nsum s (\x. if x IN s then f(x) else 0) = nsum s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[]);;

let NSUM_BOUND = prove
 (`!s f b. FINITE s /\ (!x:A. x IN s ==> f(x) <= b)
           ==> nsum s f <= (CARD s) * b`,
  SIMP_TAC[GSYM NSUM_CONST; NSUM_LE]);;

let NSUM_BOUND_GEN = prove
 (`!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) <= b DIV (CARD s))
           ==> nsum s f <= b`,
  SIMP_TAC[IMP_CONJ; CARD_EQ_0; LE_RDIV_EQ] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nsum s (\x. CARD(s:A->bool) * f x) <= CARD s * b` MP_TAC THENL
   [ASM_SIMP_TAC[NSUM_BOUND];
    ASM_SIMP_TAC[NSUM_LMUL; LE_MULT_LCANCEL; CARD_EQ_0]]);;

let NSUM_BOUND_LT = prove
 (`!s f b. FINITE s /\ (!x:A. x IN s ==> f x <= b) /\ (?x. x IN s /\ f x < b)
           ==> nsum s f < (CARD s) * b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `nsum s (\x:A. b)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[NSUM_CONST; LE_REFL]]);;

let NSUM_BOUND_LT_ALL = prove
 (`!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) < b)
           ==> nsum s f < (CARD s) * b`,
  MESON_TAC[MEMBER_NOT_EMPTY; LT_IMP_LE; NSUM_BOUND_LT]);;

let NSUM_BOUND_LT_GEN = prove
 (`!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) < b DIV (CARD s))
           ==> nsum s f < b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `nsum (s:A->bool) (\a. f(a) + 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LT_ALL THEN ASM_SIMP_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC NSUM_BOUND_GEN THEN
    ASM_REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`]]);;

let NSUM_UNION_EQ = prove
 (`!s t u:A->bool.
        FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
        ==> nsum s f + nsum t f = nsum u f`,
  MESON_TAC[NSUM_UNION; DISJOINT; FINITE_SUBSET; SUBSET_UNION]);;

let NSUM_EQ_SUPERSET = prove
 (`!f s t:A->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> (f(x) = 0))
        ==> (nsum s f = nsum t g)`,
  MESON_TAC[NSUM_SUPERSET; NSUM_EQ]);;

let NSUM_RESTRICT_SET = prove
 (`!P s f. nsum {x:A | x IN s /\ P x} f = nsum s (\x. if P x then f(x) else 0)`,
  REWRITE_TAC[nsum; GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_RESTRICT_SET THEN REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_NSUM_RESTRICT = prove
 (`!(R:A->B->bool) f s t.
        FINITE s /\ FINITE t
        ==> (nsum s (\x. nsum {y | y IN t /\ R x y} (\y. f x y)) =
             nsum t (\y. nsum {x | x IN s /\ R x y} (\x. f x y)))`,
  REPEAT GEN_TAC THEN SIMP_TAC[NSUM_RESTRICT_SET] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP NSUM_SWAP th]));;

let CARD_EQ_NSUM = prove
 (`!s:A->bool. FINITE s ==> ((CARD s) = nsum s (\x. 1))`,
  SIMP_TAC[NSUM_CONST; MULT_CLAUSES]);;

let NSUM_MULTICOUNT_GEN = prove
 (`!R:A->B->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k(j)))
        ==> (nsum s (\i. (CARD {j | j IN t /\ R i j})) =
             nsum t (\i. (k i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum s (\i:A. nsum {j:B | j IN t /\ R i j} (\j. 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT];
    FIRST_ASSUM(fun t -> ONCE_REWRITE_TAC[MATCH_MP NSUM_NSUM_RESTRICT t]) THEN
    MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT] THEN
    REWRITE_TAC[MULT_CLAUSES]]);;

let NSUM_MULTICOUNT = prove
 (`!R:A->B->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k))
        ==> (nsum s (\i. (CARD {j | j IN t /\ R i j})) = (k * CARD t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum t (\i:B. k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_MULTICOUNT_GEN THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[NSUM_CONST] THEN REWRITE_TAC[MULT_AC]]);;

let NSUM_IMAGE_GEN = prove
 (`!f:A->B g s.
        FINITE s
        ==> nsum s g =
            nsum (IMAGE f s) (\y. nsum {x | x IN s /\ f x = y} g)`,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_IMAGE_GEN THEN
  REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_GROUP = prove
 (`!f:A->B g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> nsum t (\y. nsum {x | x IN s /\ f(x) = y} g) = nsum s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `g:A->num`; `s:A->bool`] NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NSUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ_0 THEN ASM SET_TAC[]);;

let NSUM_GROUP_RELATION = prove
 (`!R:A->B->bool g s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> nsum t (\y. nsum {x | x IN s /\ R x y} g) = nsum s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:A. @y:B. y IN t /\ R x y`; `g:A->num`;
                 `s:A->bool`; `t:B->bool`]
        NSUM_GROUP) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC NSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let NSUM_SUBSET = prove
 (`!u v f. FINITE u /\ FINITE v /\ (!x:A. x IN (u DIFF v) ==> f(x) = 0)
           ==> nsum u f <= nsum v f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->num`; `u INTER v :A->bool`] NSUM_UNION) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `v DIFF u :A->bool` th) THEN
                       MP_TAC(SPEC `u DIFF v :A->bool` th)) THEN
  REWRITE_TAC[SET_RULE `(u INTER v) UNION (u DIFF v) = u`;
              SET_RULE `(u INTER v) UNION (v DIFF u) = v`] THEN
  ASM_SIMP_TAC[FINITE_DIFF; FINITE_INTER] THEN
  REPEAT(ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  ASM_SIMP_TAC[NSUM_EQ_0] THEN ARITH_TAC);;

let NSUM_SUBSET_SIMPLE = prove
 (`!u v f:A->num. FINITE v /\ u SUBSET v ==> nsum u f <= nsum v f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_SUBSET THEN
  ASM_MESON_TAC[IN_DIFF; SUBSET; FINITE_SUBSET]);;

let NSUM_LE_GEN = prove
 (`!f g s. (!x:A. x IN s ==> f x <= g x) /\ FINITE {x | x IN s /\ ~(g x = 0)}
           ==> nsum s f <= nsum s g`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NSUM_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_ADD] THEN
  TRANS_TAC LE_TRANS `nsum {x | x IN s /\ ~(g(x:A) = 0)} f` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_SUBSET THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      FINITE_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LE];
    MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[IN_ELIM_THM]]);;

let NSUM_MUL_BOUND = prove
 (`!a b s:A->bool.
        FINITE s
        ==> nsum s (\i. a i * b i) <= nsum s a * nsum s b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
  MATCH_MP_TAC NSUM_LE THEN ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN DISJ1_TAC THEN
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM NSUM_SING] THEN
  MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[SING_SUBSET; IN_DIFF]);;

let NSUM_IMAGE_NONZERO = prove
 (`!d:B->num i:A->B s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = 0)
    ==> nsum (IMAGE i s) d = nsum s (d o i)`,
  REWRITE_TAC[GSYM NEUTRAL_ADD; nsum] THEN
  MATCH_MP_TAC ITERATE_IMAGE_NONZERO THEN REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_BIJECTION = prove
 (`!f p s:A->bool.
        (!x. x IN s ==> p(x) IN s) /\
        (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
        ==> nsum s f = nsum s (f o p)`,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_BIJECTION THEN
  REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_NSUM_PRODUCT = prove
 (`!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> nsum s (\i. nsum (t i) (x i)) =
            nsum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)`,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
  REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_EQ_GENERAL = prove
 (`!s:A->bool t:B->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ h(x) = y) /\
        (!x. x IN s ==> h(x) IN t /\ g(h x) = f x)
        ==> nsum s f = nsum t g`,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
  REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_EQ_GENERAL_INVERSES = prove
 (`!s:A->bool t:B->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ h(k y) = y) /\
        (!x. x IN s ==> h(x) IN t /\ k(h x) = x /\ g(h x) = f x)
        ==> nsum s f = nsum t g`,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
  REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_INJECTION = prove
 (`!f p s:A->bool.
        FINITE s /\
        (!x. x IN s ==> p x IN s) /\
        (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
        ==> nsum s (f o p) = nsum s f`,
  REWRITE_TAC[nsum] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
  REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_UNION_NONZERO = prove
 (`!f s t:A->bool.
        FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = 0)
        ==> nsum (s UNION t) f = nsum s f + nsum t f`,
  REWRITE_TAC[nsum; GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_UNION_NONZERO THEN REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_UNIONS_NONZERO = prove
 (`!f s. FINITE s /\ (!t:A->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> f x = 0)
         ==> nsum (UNIONS s) f = nsum s (\t. nsum t f)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; NSUM_CLAUSES; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `s:(A->bool)->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ASM_SIMP_TAC[NSUM_CLAUSES] THEN
  ANTS_TAC THENL  [ASM_MESON_TAC[]; DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  STRIP_TAC THEN MATCH_MP_TAC NSUM_UNION_NONZERO THEN
  ASM_SIMP_TAC[FINITE_UNIONS; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[]);;

let NSUM_CASES = prove
 (`!s P f g. FINITE s
             ==> nsum s (\x:A. if P x then f x else g x) =
                 nsum {x | x IN s /\ P x} f + nsum {x | x IN s /\ ~P x} g`,
  REWRITE_TAC[nsum; GSYM NEUTRAL_ADD] THEN
  MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC[MONOIDAL_ADD]);;

let NSUM_CLOSED = prove
 (`!P f:A->num s.
        P(0) /\ (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nsum s f)`,
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `P:num->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_ADD; GSYM nsum]);;

let NSUM_RELATED = prove
 (`!R (f:A->num) g s.
        R 0 0 /\
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (nsum s f) (nsum s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:num->num->bool`
    (MATCH_MP ITERATE_RELATED MONOIDAL_ADD)) THEN
  ASM_REWRITE_TAC[GSYM nsum; NEUTRAL_ADD] THEN ASM_MESON_TAC[]);;

let NSUM_CLOSED_NONEMPTY = prove
 (`!P f:A->num s.
        FINITE s /\ ~(s = {}) /\
        (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nsum s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP ITERATE_CLOSED_NONEMPTY MONOIDAL_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `P:num->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_ADD; GSYM nsum]);;

let NSUM_RELATED_NONEMPTY = prove
 (`!R (f:A->num) g s.
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (nsum s f) (nsum s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:num->num->bool`
    (MATCH_MP ITERATE_RELATED_NONEMPTY MONOIDAL_ADD)) THEN
  ASM_REWRITE_TAC[GSYM nsum; NEUTRAL_ADD] THEN ASM_MESON_TAC[]);;

let NSUM_ADD_NUMSEG = prove
 (`!f g m n. nsum(m..n) (\i. f(i) + g(i)) = nsum(m..n) f + nsum(m..n) g`,
  SIMP_TAC[NSUM_ADD; FINITE_NUMSEG]);;

let NSUM_LE_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i <= n ==> f(i) <= g(i))
             ==> nsum(m..n) f <= nsum(m..n) g`,
  SIMP_TAC[NSUM_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let NSUM_EQ_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (nsum(m..n) f = nsum(m..n) g)`,
  MESON_TAC[NSUM_EQ; FINITE_NUMSEG; IN_NUMSEG]);;

let NSUM_CONST_NUMSEG = prove
 (`!c m n. nsum(m..n) (\n. c) = ((n + 1) - m) * c`,
  SIMP_TAC[NSUM_CONST; FINITE_NUMSEG; CARD_NUMSEG]);;

let NSUM_EQ_0_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> (f(i) = 0)) ==> (nsum(m..n) f = 0)`,
  SIMP_TAC[NSUM_EQ_0; IN_NUMSEG]);;

let NSUM_EQ_0_IFF_NUMSEG = prove
 (`!f m n. nsum (m..n) f = 0 <=> !i. m <= i /\ i <= n ==> f i = 0`,
  SIMP_TAC[NSUM_EQ_0_IFF; FINITE_NUMSEG; IN_NUMSEG]);;

let NSUM_TRIV_NUMSEG = prove
 (`!f m n. n < m ==> (nsum(m..n) f = 0)`,
  MESON_TAC[NSUM_EQ_0_NUMSEG; LE_TRANS; NOT_LT]);;

let NSUM_SING_NUMSEG = prove
 (`!f n. nsum(n..n) f = f(n)`,
  SIMP_TAC[NSUM_SING; NUMSEG_SING]);;

let NSUM_CLAUSES_NUMSEG = prove
 (`(!m. nsum(m..0) f = if m = 0 then f(0) else 0) /\
   (!m n. nsum(m..SUC n) f = if m <= SUC n then nsum(m..n) f + f(SUC n)
                             else nsum(m..n) f)`,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_ADD; nsum]);;

let NSUM_CLAUSES_NUMSEG_LT = prove
 (`nsum {i | i < 0} f = 0 /\
   (!k. nsum {i | i < SUC k} f = nsum {i | i < k} f + f k)`,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG_LT MONOIDAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_ADD; nsum]);;

let NSUM_CLAUSES_NUMSEG_LE = prove
 (`nsum {i | i <= 0} f = f 0 /\
   (!k. nsum {i | i <= SUC k} f = nsum {i | i <= k} f + f(SUC k))`,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG_LE MONOIDAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_ADD; nsum]);;

let NSUM_SWAP_NUMSEG = prove
 (`!a b c d f.
     nsum(a..b) (\i. nsum(c..d) (f i)) =
     nsum(c..d) (\j. nsum(a..b) (\i. f i j))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_SWAP THEN REWRITE_TAC[FINITE_NUMSEG]);;

let NSUM_ADD_SPLIT = prove
 (`!f m n p.
        m <= n + 1 ==> (nsum (m..(n+p)) f = nsum(m..n) f + nsum(n+1..n+p) f)`,
  SIMP_TAC[NUMSEG_ADD_SPLIT; NSUM_UNION; DISJOINT_NUMSEG; FINITE_NUMSEG;
           ARITH_RULE `x < x + 1`]);;

let NSUM_OFFSET = prove
 (`!p f m n. nsum(m+p..n+p) f = nsum(m..n) (\i. f(i + p))`,
  SIMP_TAC[NUMSEG_OFFSET_IMAGE; NSUM_IMAGE; EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF]);;

let NSUM_OFFSET_0 = prove
 (`!f m n. m <= n ==> (nsum(m..n) f = nsum(0..n-m) (\i. f(i + m)))`,
  SIMP_TAC[GSYM NSUM_OFFSET; ADD_CLAUSES; SUB_ADD]);;

let NSUM_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> nsum(m..n) f = f(m) + nsum(m+1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; NSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let NSUM_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> nsum(m..n) f = nsum(m..n-1) f + f(n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; NSUM_CLAUSES_NUMSEG; SUC_SUB1]);;

let NSUM_PAIR = prove
 (`!f m n. nsum(2*m..2*n+1) f = nsum(m..n) (\i. f(2*i) + f(2*i+1))`,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_ADD) THEN
  REWRITE_TAC[nsum; NEUTRAL_ADD]);;

let NSUM_REFLECT = prove
 (`!x m n. nsum(m..n) x = if n < m then 0 else nsum(0..n-m) (\i. x(n - i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nsum] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP ITERATE_REFLECT MONOIDAL_ADD] THEN
  REWRITE_TAC[NEUTRAL_ADD]);;

let MOD_NSUM_MOD = prove
 (`!f:A->num n s.
        FINITE s ==> (nsum s f) MOD n = nsum s (\i. f(i) MOD n) MOD n`,
  GEN_TAC THEN GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MOD_ZERO; ETA_AX] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[NSUM_CLAUSES] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM MOD_ADD_MOD] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let MOD_NSUM_MOD_NUMSEG = prove
 (`!f a b n.
        (nsum(a..b) f) MOD n = nsum(a..b) (\i. f i MOD n) MOD n`,
  MESON_TAC[MOD_NSUM_MOD; FINITE_NUMSEG]);;

let CONG_NSUM = prove
 (`!n (f:A->num) g s.
        FINITE s /\ (!x. x IN s ==> (f x == g x) (mod n))
        ==> (nsum s f == nsum s g) (mod n)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\x y:num. (x == y) (mod n)`; `f:A->num`; `g:A->num`; `s:A->bool`]
        NSUM_RELATED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC NUMBER_RULE);;

let th = prove
 (`(!f g s:A->bool.
        (!x. x IN s ==> f(x) = g(x))
        ==> nsum s (\i. f(i)) = nsum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> nsum(a..b) (\i. f(i)) = nsum(a..b) g) /\
   (!f g p. (!x. p x ==> f x = g x)
            ==> nsum {y | p y} (\i. f(i)) = nsum {y | p y} g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
  extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* Thanks to finite sums, we can express cardinality of finite union.        *)
(* ------------------------------------------------------------------------- *)

let CARD_UNIONS = prove
 (`!s:(A->bool)->bool.
        FINITE s /\ (!t. t IN s ==> FINITE t) /\
        (!t u. t IN s /\ u IN s /\ ~(t = u) ==> t INTER u = {})
        ==> CARD(UNIONS s) = nsum s CARD`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; NOT_IN_EMPTY; IN_INSERT] THEN
  REWRITE_TAC[CARD_CLAUSES; NSUM_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `f:(A->bool)->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[NSUM_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_SIMP_TAC[FINITE_UNIONS; FINITE_UNION; INTER_UNIONS] THEN
  REWRITE_TAC[EMPTY_UNIONS; IN_ELIM_THM] THEN ASM MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Expand "nsum (m..n) f" where m and n are numerals.                        *)
(* ------------------------------------------------------------------------- *)

let EXPAND_NSUM_CONV =
  let [pth_0; pth_1; pth_2] = (CONJUNCTS o prove)
   (`(n < m ==> nsum(m..n) f = 0) /\
     nsum(m..m) f = f m /\
     (m <= n ==> nsum (m..n) f = f m + nsum (m + 1..n) f)`,
    REWRITE_TAC[NSUM_CLAUSES_LEFT; NSUM_SING_NUMSEG; NSUM_TRIV_NUMSEG])
  and ns_tm = `..` and f_tm = `f:num->num`
  and m_tm = `m:num` and n_tm = `n:num` in
  let rec conv tm =
    let smn,ftm = dest_comb tm in
    let s,mn = dest_comb smn in
    if not(is_const s && fst(dest_const s) = "nsum")
    then failwith "EXPAND_NSUM_CONV" else
    let mtm,ntm = dest_binop ns_tm mn in
    let m = dest_numeral mtm and n = dest_numeral ntm in
    if n </ m then
      let th1 = INST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_0 in
      MP th1 (EQT_ELIM(NUM_LT_CONV(lhand(concl th1))))
    else if n =/ m then CONV_RULE (RAND_CONV(TRY_CONV BETA_CONV))
                                 (INST [ftm,f_tm; mtm,m_tm] pth_1)
    else
      let th1 = INST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_2 in
      let th2 = MP th1 (EQT_ELIM(NUM_LE_CONV(lhand(concl th1)))) in
      CONV_RULE (RAND_CONV(COMB2_CONV (RAND_CONV(TRY_CONV BETA_CONV))
       (LAND_CONV(LAND_CONV NUM_ADD_CONV) THENC conv))) th2 in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Sums of real numbers.                                                     *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let sum = new_definition
  `sum:(A->bool)->(A->real)->real = iterate (+)`;;

let NEUTRAL_REAL_ADD = prove
 (`neutral((+):real->real->real) = &0`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[REAL_ADD_LID; REAL_ADD_RID]);;

let MONOIDAL_REAL_ADD = prove
 (`monoidal((+):real->real->real)`,
  REWRITE_TAC[monoidal; NEUTRAL_REAL_ADD] THEN REAL_ARITH_TAC);;

let SUM_DEGENERATE = prove
 (`!f s:A->bool. ~(FINITE {x | x IN s /\ ~(f x = &0)}) ==> sum s f = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sum] THEN
  SIMP_TAC[iterate; support; NEUTRAL_REAL_ADD]);;

let SUM_CLAUSES = prove
 (`(!f:A->real. sum {} f = &0) /\
   (!x (f:B->real) s.
        FINITE(s)
        ==> (sum (x INSERT s) f =
             if x IN s then sum s f else f(x) + sum s f))`,
  REWRITE_TAC[sum; GSYM NEUTRAL_REAL_ADD] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_UNION = prove
 (`!f s t:A->bool.
        FINITE s /\ FINITE t /\ DISJOINT s t
        ==> sum (s UNION t) f = sum s f + sum t f`,
  SIMP_TAC[sum; ITERATE_UNION; MONOIDAL_REAL_ADD]);;

let SUM_DIFF = prove
 (`!f s t:A->bool. FINITE s /\ t SUBSET s ==> (sum (s DIFF t) f = sum s f - sum t f)`,
  SIMP_TAC[REAL_EQ_SUB_LADD; sum; ITERATE_DIFF; MONOIDAL_REAL_ADD]);;

let SUM_INCL_EXCL = prove
 (`!s t (f:A->real).
     FINITE s /\ FINITE t
     ==> sum s f + sum t f = sum (s UNION t) f + sum (s INTER t) f`,
  REWRITE_TAC[sum; GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_INCL_EXCL THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_SUPPORT = prove
 (`!f s:A->bool. sum (support (+) f s) f = sum s f`,
  SIMP_TAC[sum; iterate; SUPPORT_SUPPORT]);;

let SUM_ADD = prove
 (`!f g s:A->bool. FINITE s ==> (sum s (\x. f(x) + g(x)) = sum s f + sum s g)`,
  SIMP_TAC[sum; ITERATE_OP; MONOIDAL_REAL_ADD]);;

let SUM_ADD_GEN = prove
 (`!f g s:A->bool.
       FINITE {x | x IN s /\ ~(f x = &0)} /\ FINITE {x | x IN s /\ ~(g x = &0)}
       ==> sum s (\x. f x + g x) = sum s f + sum s g`,
  REWRITE_TAC[GSYM NEUTRAL_REAL_ADD; GSYM support; sum] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_REAL_ADD);;

let SUM_EQ_0 = prove
 (`!f s. (!x:A. x IN s ==> (f(x) = &0)) ==> (sum s f = &0)`,
  REWRITE_TAC[sum; GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC[ITERATE_EQ_NEUTRAL; MONOIDAL_REAL_ADD]);;

let SUM_0 = prove
 (`!s:A->bool. sum s (\n. &0) = &0`,
  SIMP_TAC[SUM_EQ_0]);;

let SUM_LMUL = prove
 (`!f c s:A->bool. sum s (\x. c * f(x)) = c * sum s f`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; SUM_0] THEN REWRITE_TAC[sum] THEN
  ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
  SUBGOAL_THEN `support (+) (\x:A. c * f(x)) s = support (+) f s` SUBST1_TAC
  THENL [ASM_SIMP_TAC[support; REAL_ENTIRE; NEUTRAL_REAL_ADD]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NEUTRAL_REAL_ADD; REAL_MUL_RZERO] THEN
  UNDISCH_TAC `FINITE (support (+) f (s:A->bool))` THEN
  SPEC_TAC(`support (+) f (s:A->bool)`,`t:A->bool`) THEN
  REWRITE_TAC[GSYM sum] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; REAL_MUL_RZERO; REAL_MUL_LZERO;
           REAL_ADD_LDISTRIB]);;

let SUM_RMUL = prove
 (`!f c s:A->bool. sum s (\x. f(x) * c) = sum s f * c`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[SUM_LMUL]);;

let SUM_NEG = prove
 (`!f s:A->bool. sum s (\x. --(f(x))) = --(sum s f)`,
  ONCE_REWRITE_TAC[REAL_ARITH `--x = --(&1) * x`] THEN
  SIMP_TAC[SUM_LMUL]);;

let SUM_SUB = prove
 (`!f g s:A->bool. FINITE s ==> sum s (\x. f(x) - g(x)) = sum s f - sum s g`,
  ONCE_REWRITE_TAC[real_sub] THEN SIMP_TAC[SUM_NEG; SUM_ADD]);;

let SUM_LE = prove
 (`!f g s:A->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) ==> sum s f <= sum s g`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; REAL_LE_REFL; REAL_LE_ADD2; IN_INSERT]);;

let SUM_LT = prove
 (`!f g s:A->bool.
        FINITE(s) /\ (!x. x IN s ==> f(x) <= g(x)) /\
        (?x. x IN s /\ f(x) < g(x))
         ==> sum s f < sum s g`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s = (a:A) INSERT (s DELETE a)` SUBST1_TAC THENL
   [UNDISCH_TAC `a:A IN s` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[REAL_LTE_ADD2; SUM_LE; IN_DELETE; FINITE_DELETE]);;

let SUM_LT_ALL = prove
 (`!f g s:A->bool.
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> f(x) < g(x))
        ==> sum s f < sum s g`,
  MESON_TAC[MEMBER_NOT_EMPTY; REAL_LT_IMP_LE; SUM_LT]);;

let SUM_POS_LT = prove
 (`!f s:A->bool.
        FINITE s /\
        (!x. x IN s ==> &0 <= f x) /\
        (?x. x IN s /\ &0 < f x)
        ==> &0 < sum s f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum (s:A->bool) (\i. &0)` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_0; REAL_LE_REFL]; MATCH_MP_TAC SUM_LT] THEN
  ASM_MESON_TAC[]);;

let SUM_POS_LT_ALL = prove
 (`!s f:A->real.
     FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> &0 < f i) ==> &0 < sum s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LT THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY; REAL_LT_IMP_LE]);;

let SUM_EQ = prove
 (`!f g s:A->bool. (!x. x IN s ==> (f x = g x)) ==> (sum s f = sum s g)`,
  REWRITE_TAC[sum] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_ABS = prove
 (`!f s:A->bool. FINITE(s) ==> abs(sum s f) <= sum s (\x. abs(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; REAL_ABS_NUM; REAL_LE_REFL;
           REAL_ARITH `abs(a) <= b ==> abs(x + a) <= abs(x) + b`]);;

let SUM_ABS_LE = prove
 (`!f:A->real g s:A->bool.
        FINITE s /\ (!x. x IN s ==> abs(f x) <= g x)
        ==> abs(sum s f) <= sum s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x:A. abs(f x))` THEN
  ASM_SIMP_TAC[SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_REWRITE_TAC[]);;

let SUM_CONST = prove
 (`!c s:A->bool. FINITE s ==> (sum s (\n. c) = &(CARD s) * c)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; CARD_CLAUSES; GSYM REAL_OF_NUM_SUC] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let SUM_POS_LE = prove
 (`!s:A->bool. (!x. x IN s ==> &0 <= f x) ==> &0 <= sum s f`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `FINITE {x:A | x IN s /\ ~(f x = &0)}` THEN
  ASM_SIMP_TAC[SUM_DEGENERATE; REAL_LE_REFL] THEN
  ONCE_REWRITE_TAC[GSYM SUM_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_REAL_ADD] THEN
  MP_TAC(ISPECL [`\x:A. &0`; `f:A->real`; `{x:A | x IN s /\ ~(f x = &0)}`]
        SUM_LE) THEN
  ASM_SIMP_TAC[SUM_0; IN_ELIM_THM]);;

let SUM_POS_BOUND = prove
 (`!f b s:A->bool.
        FINITE s /\ (!x. x IN s ==> &0 <= f x) /\ sum s f <= b
        ==> !x:A. x IN s ==> f x <= b`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; NOT_IN_EMPTY; IN_INSERT] THEN
  MESON_TAC[SUM_POS_LE;
   REAL_ARITH `&0 <= x /\ &0 <= y /\ x + y <= b ==> x <= b /\ y <= b`]);;

let SUM_POS_EQ_0 = prove
 (`!f s:A->bool.
        FINITE s /\ (!x. x IN s ==> &0 <= f x) /\ (sum s f = &0)
        ==> !x. x IN s ==> f x = &0`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  MESON_TAC[SUM_POS_BOUND; SUM_POS_LE]);;

let SUM_ZERO_EXISTS = prove
 (`!(u:A->real) s.
         FINITE s /\ sum s u = &0
         ==> (!i. i IN s ==> u i = &0) \/
             (?j k. j IN s /\ u j < &0 /\ k IN s /\ u k > &0)`,
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (MESON[REAL_ARITH `(&0 <= --u <=> ~(u > &0)) /\ (&0 <= u <=> ~(u < &0))`]
     `(?j k:A. j IN s /\ u j < &0 /\ k IN s /\ u k > &0) \/
      (!i. i IN s ==> &0 <= u i) \/ (!i. i IN s ==> &0 <= --(u i))`) THEN
  ASM_REWRITE_TAC[] THEN DISJ1_TAC THENL
   [ALL_TAC; ONCE_REWRITE_TAC[REAL_ARITH `x = &0 <=> --x = &0`]] THEN
  MATCH_MP_TAC SUM_POS_EQ_0 THEN ASM_REWRITE_TAC[SUM_NEG; REAL_NEG_0]);;

let SUM_DELETE = prove
 (`!f s a:A. FINITE s /\ a IN s ==> sum (s DELETE a) f = sum s f - f(a)`,
  SIMP_TAC[REAL_ARITH `y = z - x <=> x + y = z:real`; sum; ITERATE_DELETE;
           MONOIDAL_REAL_ADD]);;

let SUM_DELETE_CASES = prove
 (`!f s a:A. FINITE s
             ==> sum (s DELETE a) f = if a IN s then sum s f - f(a)
                                      else sum s f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> (s DELETE a = s)`; SUM_DELETE]);;

let SUM_SING = prove
 (`!f x:A. sum {x} f = f(x)`,
  SIMP_TAC[SUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; REAL_ADD_RID]);;

let SUM_DELTA = prove
 (`!s a. sum s (\x. if x = a:A then b else &0) = if a IN s then b else &0`,
  REWRITE_TAC[sum; GSYM NEUTRAL_REAL_ADD] THEN
  SIMP_TAC[ITERATE_DELTA; MONOIDAL_REAL_ADD]);;

let SUM_SWAP = prove
 (`!f:A->B->real s t.
      FINITE(s) /\ FINITE(t)
      ==> (sum s (\i. sum t (f i)) = sum t (\j. sum s (\i. f i j)))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; SUM_0; SUM_ADD; ETA_AX]);;

let SUM_IMAGE = prove
 (`!(f:A->B) g s.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> sum (IMAGE f s) g = sum s (g o f)`,
  REWRITE_TAC[sum; GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_SUPERSET = prove
 (`!f:A->real u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = &0))
        ==> (sum v f = sum u f)`,
  SIMP_TAC[sum; GSYM NEUTRAL_REAL_ADD; ITERATE_SUPERSET; MONOIDAL_REAL_ADD]);;

let SUM_UNIV = prove
 (`!f:A->real s. support (+) f (:A) SUBSET s ==> sum s f = sum (:A) f`,
  REWRITE_TAC[sum] THEN MATCH_MP_TAC ITERATE_UNIV THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_UNION_RZERO = prove
 (`!f:A->real u v.
        FINITE u /\ (!x. x IN v /\ ~(x IN u) ==> (f(x) = &0))
        ==> sum (u UNION v) f = sum u f`,
  let lemma = prove(`u UNION v = u UNION (v DIFF u)`,SET_TAC[]) in
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[lemma] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  ASM_MESON_TAC[IN_UNION; IN_DIFF; SUBSET]);;

let SUM_UNION_LZERO = prove
 (`!f:A->real u v.
        FINITE v /\ (!x. x IN u /\ ~(x IN v) ==> (f(x) = &0))
        ==> sum (u UNION v) f = sum v f`,
  MESON_TAC[SUM_UNION_RZERO; UNION_COMM]);;

let SUM_RESTRICT = prove
 (`!f s:A->bool.
        FINITE s ==> sum s (\x. if x IN s then f(x) else &0) = sum s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]);;

let SUM_BOUND = prove
 (`!s f b. FINITE s /\ (!x:A. x IN s ==> f(x) <= b)
           ==> sum s f <= &(CARD s) * b`,
  SIMP_TAC[GSYM SUM_CONST; SUM_LE]);;

let SUM_BOUND_GEN = prove
 (`!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) <= b / &(CARD s))
           ==> sum s f <= b`,
  MESON_TAC[SUM_BOUND; REAL_DIV_LMUL; REAL_OF_NUM_EQ; HAS_SIZE_0;
            HAS_SIZE]);;

let SUM_ABS_BOUND = prove
 (`!s f b. FINITE s /\ (!x:A. x IN s ==> abs(f(x)) <= b)
           ==> abs(sum s f) <= &(CARD s) * b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\x:A. abs(f x))` THEN
  ASM_SIMP_TAC[SUM_BOUND; SUM_ABS]);;

let SUM_BOUND_LT = prove
 (`!s f b. FINITE s /\ (!x:A. x IN s ==> f x <= b) /\ (?x. x IN s /\ f x < b)
           ==> sum s f < &(CARD s) * b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `sum s (\x:A. b)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LT THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[SUM_CONST; REAL_LE_REFL]]);;

let SUM_BOUND_LT_ALL = prove
 (`!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) < b)
           ==> sum s f <  &(CARD s) * b`,
  MESON_TAC[MEMBER_NOT_EMPTY; REAL_LT_IMP_LE; SUM_BOUND_LT]);;

let SUM_BOUND_LT_GEN = prove
 (`!s f b. FINITE s /\ ~(s = {}) /\ (!x:A. x IN s ==> f(x) < b / &(CARD s))
           ==> sum s f < b`,
  MESON_TAC[SUM_BOUND_LT_ALL; REAL_DIV_LMUL; REAL_OF_NUM_EQ; HAS_SIZE_0;
            HAS_SIZE]);;

let SUM_UNION_EQ = prove
 (`!s t u:A->bool.
        FINITE u /\ s INTER t = {} /\ s UNION t = u
        ==> sum s f + sum t f = sum u f`,
  MESON_TAC[SUM_UNION; DISJOINT; FINITE_SUBSET; SUBSET_UNION]);;

let SUM_EQ_SUPERSET = prove
 (`!f s t:A->bool.
        FINITE t /\ t SUBSET s /\
        (!x. x IN t ==> (f x = g x)) /\
        (!x. x IN s /\ ~(x IN t) ==> (f(x) = &0))
        ==> (sum s f = sum t g)`,
  MESON_TAC[SUM_SUPERSET; SUM_EQ]);;

let SUM_RESTRICT_SET = prove
 (`!P s f. sum {x:A | x IN s /\ P x} f = sum s (\x. if P x then f x else &0)`,
  REWRITE_TAC[sum; GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_RESTRICT_SET THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_SUM_RESTRICT = prove
 (`!(R:A->B->bool) f s t.
        FINITE s /\ FINITE t
        ==> (sum s (\x. sum {y | y IN t /\ R x y} (\y. f x y)) =
             sum t (\y. sum {x | x IN s /\ R x y} (\x. f x y)))`,
  REPEAT GEN_TAC THEN SIMP_TAC[SUM_RESTRICT_SET] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SUM_SWAP th]));;

let CARD_EQ_SUM = prove
 (`!s:A->bool. FINITE s ==> (&(CARD s) = sum s (\x. &1))`,
  SIMP_TAC[SUM_CONST; REAL_MUL_RID]);;

let SUM_MULTICOUNT_GEN = prove
 (`!R:A->B->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k(j)))
        ==> (sum s (\i. &(CARD {j | j IN t /\ R i j})) =
             sum t (\i. &(k i)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum s (\i:A. sum {j:B | j IN t /\ R i j} (\j. &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT];
    FIRST_ASSUM(fun th ->
      ONCE_REWRITE_TAC[MATCH_MP SUM_SUM_RESTRICT th]) THEN
    MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
    REWRITE_TAC[REAL_MUL_RID]]);;

let SUM_MULTICOUNT = prove
 (`!R:A->B->bool s t k.
        FINITE s /\ FINITE t /\
        (!j. j IN t ==> (CARD {i | i IN s /\ R i j} = k))
        ==> (sum s (\i. &(CARD {j | j IN t /\ R i j})) = &(k * CARD t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum t (\i:B. &k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_MULTICOUNT_GEN THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUM_CONST; REAL_OF_NUM_MUL] THEN REWRITE_TAC[MULT_AC]]);;

let SUM_IMAGE_GEN = prove
 (`!f:A->B g s.
        FINITE s
        ==> sum s g =
            sum (IMAGE f s) (\y. sum {x | x IN s /\ f x = y} g)`,
  REWRITE_TAC[sum] THEN MATCH_MP_TAC ITERATE_IMAGE_GEN THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_GROUP = prove
 (`!f:A->B g s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> sum t (\y. sum {x | x IN s /\ f(x) = y} g) = sum s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `g:A->real`; `s:A->bool`] SUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN ASM SET_TAC[]);;

let SUM_GROUP_RELATION = prove
 (`!R:A->B->bool g s t.
         FINITE s /\
         (!x. x IN s ==> ?!y. y IN t /\ R x y)
         ==> sum t (\y. sum {x | x IN s /\ R x y} g) = sum s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:A. @y:B. y IN t /\ R x y`; `g:A->real`;
                 `s:A->bool`; `t:B->bool`]
        SUM_GROUP) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let REAL_OF_NUM_SUM = prove
 (`!f s:A->bool. FINITE s ==> (&(nsum s f) = sum s (\x. &(f x)))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; NSUM_CLAUSES; GSYM REAL_OF_NUM_ADD]);;

let SUM_SUBSET = prove
 (`!u v f. FINITE u /\ FINITE v /\
           (!x. x IN (u DIFF v) ==> f(x) <= &0) /\
           (!x:A. x IN (v DIFF u) ==> &0 <= f(x))
           ==> sum u f <= sum v f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real`; `u INTER v :A->bool`] SUM_UNION) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `v DIFF u :A->bool` th) THEN
                       MP_TAC(SPEC `u DIFF v :A->bool` th)) THEN
  REWRITE_TAC[SET_RULE `(u INTER v) UNION (u DIFF v) = u`;
              SET_RULE `(u INTER v) UNION (v DIFF u) = v`] THEN
  ASM_SIMP_TAC[FINITE_DIFF; FINITE_INTER] THEN
  REPEAT(ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= --x /\ &0 <= y ==> a + x <= a + y`) THEN
  ASM_SIMP_TAC[GSYM SUM_NEG; FINITE_DIFF] THEN CONJ_TAC THEN
  MATCH_MP_TAC SUM_POS_LE THEN
  ASM_SIMP_TAC[FINITE_DIFF; REAL_LE_RNEG; REAL_ADD_LID]);;

let SUM_SUBSET_SIMPLE = prove
 (`!u v f.
        FINITE v /\ u SUBSET v /\ (!x:A. x IN (v DIFF u) ==> &0 <= f(x))
        ==> sum u f <= sum v f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUBSET THEN
  ASM_MESON_TAC[IN_DIFF; SUBSET; FINITE_SUBSET]);;

let SUM_MUL_BOUND = prove
 (`!a b s:A->bool.
        FINITE s /\ (!i. i IN s ==> &0 <= a i /\ &0 <= b i)
        ==> sum s (\i. a i * b i) <= sum s a * sum s b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM SUM_SING] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[SING_SUBSET; IN_DIFF]);;

let SUM_IMAGE_NONZERO = prove
 (`!d:B->real i:A->B s.
    FINITE s /\
    (!x y. x IN s /\ y IN s /\ ~(x = y) /\ i x = i y ==> d(i x) = &0)
    ==> sum (IMAGE i s) d = sum s (d o i)`,
  REWRITE_TAC[GSYM NEUTRAL_REAL_ADD; sum] THEN
  MATCH_MP_TAC ITERATE_IMAGE_NONZERO THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_BIJECTION = prove
 (`!f p s:A->bool.
        (!x. x IN s ==> p(x) IN s) /\
        (!y. y IN s ==> ?!x. x IN s /\ p(x) = y)
        ==> sum s f = sum s (f o p)`,
  REWRITE_TAC[sum] THEN MATCH_MP_TAC ITERATE_BIJECTION THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_SUM_PRODUCT = prove
 (`!s:A->bool t:A->B->bool x.
        FINITE s /\ (!i. i IN s ==> FINITE(t i))
        ==> sum s (\i. sum (t i) (x i)) =
            sum {i,j | i IN s /\ j IN t i} (\(i,j). x i j)`,
  REWRITE_TAC[sum] THEN MATCH_MP_TAC ITERATE_ITERATE_PRODUCT THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_EQ_GENERAL = prove
 (`!s:A->bool t:B->bool f g h.
        (!y. y IN t ==> ?!x. x IN s /\ h(x) = y) /\
        (!x. x IN s ==> h(x) IN t /\ g(h x) = f x)
        ==> sum s f = sum t g`,
  REWRITE_TAC[sum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_EQ_GENERAL_INVERSES = prove
 (`!s:A->bool t:B->bool f g h k.
        (!y. y IN t ==> k(y) IN s /\ h(k y) = y) /\
        (!x. x IN s ==> h(x) IN t /\ k(h x) = x /\ g(h x) = f x)
        ==> sum s f = sum t g`,
  REWRITE_TAC[sum] THEN MATCH_MP_TAC ITERATE_EQ_GENERAL_INVERSES THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_INJECTION = prove
 (`!f p s:A->bool.
           FINITE s /\
           (!x. x IN s ==> p x IN s) /\
           (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
           ==> sum s (f o p) = sum s f`,
  REWRITE_TAC[sum] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
  REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_UNION_NONZERO = prove
 (`!f s t:A->bool.
        FINITE s /\ FINITE t /\ (!x. x IN s INTER t ==> f(x) = &0)
        ==> sum (s UNION t) f = sum s f + sum t f`,
  REWRITE_TAC[sum; GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_UNION_NONZERO THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_UNIONS_NONZERO = prove
 (`!f s. FINITE s /\ (!t:A->bool. t IN s ==> FINITE t) /\
         (!t1 t2 x. t1 IN s /\ t2 IN s /\ ~(t1 = t2) /\ x IN t1 /\ x IN t2
                    ==> f x = &0)
         ==> sum (UNIONS s) f = sum s (\t. sum t f)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; SUM_CLAUSES; IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `s:(A->bool)->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ASM_SIMP_TAC[SUM_CLAUSES] THEN
  ANTS_TAC THENL  [ASM_MESON_TAC[]; DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_NONZERO THEN
  ASM_SIMP_TAC[FINITE_UNIONS; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[]);;

let SUM_CASES = prove
 (`!s P f g. FINITE s
             ==> sum s (\x:A. if P x then f x else g x) =
                 sum {x | x IN s /\ P x} f + sum {x | x IN s /\ ~P x} g`,
  REWRITE_TAC[sum; GSYM NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC ITERATE_CASES THEN REWRITE_TAC[MONOIDAL_REAL_ADD]);;

let SUM_CASES_1 = prove
 (`!s a:A. FINITE s /\ a IN s
           ==> sum s (\x. if x = a then y else f(x)) = sum s f + (y - f a)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUM_CASES] THEN
  ASM_SIMP_TAC[GSYM DELETE; SUM_DELETE] THEN
  ASM_SIMP_TAC[SET_RULE `a IN s ==> {x | x IN s /\ x = a} = {a}`] THEN
  REWRITE_TAC[SUM_SING] THEN REAL_ARITH_TAC);;

let SUM_LE_INCLUDED = prove
 (`!f:A->real g:B->real s t i.
        FINITE s /\ FINITE t /\
        (!y. y IN t ==> &0 <= g y) /\
        (!x. x IN s ==> ?y. y IN t /\ i y = x /\ f(x) <= g(y))
        ==> sum s f <= sum t g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE (i:B->A) t) (\y. sum {x | x IN t /\ i x = y} g)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC(GSYM SUM_IMAGE_GEN) THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum s (\y. sum {x | x IN t /\ (i:B->A) x = y} g)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `y:B` THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {y:B} g` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUM_SING]; ALL_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  ASM_SIMP_TAC[SUM_POS_LE; FINITE_RESTRICT; IN_ELIM_THM] THEN
  ASM SET_TAC[]);;

let SUM_IMAGE_LE = prove
 (`!f:A->B g s.
        FINITE s /\
        (!x. x IN s ==> &0 <= g(f x))
        ==> sum (IMAGE f s) g <= sum s (g o f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_LE_INCLUDED THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[o_THM] THEN EXISTS_TAC `f:A->B` THEN
  MESON_TAC[REAL_LE_REFL]);;

let SUM_CLOSED = prove
 (`!P f:A->real s.
        P(&0) /\ (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(sum s f)`,
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_REAL_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `P:real->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_REAL_ADD; GSYM sum]);;

let SUM_RELATED = prove
 (`!R (f:A->real) g s.
        R (&0) (&0) /\
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (sum s f) (sum s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:real->real->bool`
    (MATCH_MP ITERATE_RELATED MONOIDAL_REAL_ADD)) THEN
  ASM_REWRITE_TAC[GSYM sum; NEUTRAL_REAL_ADD] THEN ASM_MESON_TAC[]);;

let SUM_CLOSED_NONEMPTY = prove
 (`!P f:A->real s.
        FINITE s /\ ~(s = {}) /\
        (!x y. P x /\ P y ==> P(x + y)) /\ (!a. a IN s ==> P(f a))
        ==> P(sum s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP ITERATE_CLOSED_NONEMPTY MONOIDAL_REAL_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `P:real->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_REAL_ADD; GSYM sum]);;

let SUM_RELATED_NONEMPTY = prove
 (`!R (f:A->real) g s.
        (!m n m' n'. R m n /\ R m' n' ==> R (m + m') (n + n')) /\
        FINITE s /\ ~(s = {}) /\ (!x. x IN s ==> R (f x) (g x))
        ==> R (sum s f) (sum s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:real->real->bool`
    (MATCH_MP ITERATE_RELATED_NONEMPTY MONOIDAL_REAL_ADD)) THEN
  ASM_REWRITE_TAC[GSYM sum; NEUTRAL_REAL_ADD] THEN ASM_MESON_TAC[]);;

let REAL_OF_NUM_SUM_GEN = prove
 (`!f s:A->bool.
       FINITE {i | i IN s /\ ~(f i = 0)} ==> &(nsum s f) = sum s (\x. &(f x))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM SUM_SUPPORT; GSYM NSUM_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_ADD; NEUTRAL_REAL_ADD; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_SUM]);;

(* ------------------------------------------------------------------------- *)
(* Specialize them to sums over intervals of numbers.                        *)
(* ------------------------------------------------------------------------- *)

let SUM_ADD_NUMSEG = prove
 (`!f g m n. sum(m..n) (\i. f(i) + g(i)) = sum(m..n) f + sum(m..n) g`,
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG]);;

let SUM_SUB_NUMSEG = prove
 (`!f g m n. sum(m..n) (\i. f(i) - g(i)) = sum(m..n) f - sum(m..n) g`,
   SIMP_TAC[SUM_SUB; FINITE_NUMSEG]);;

let SUM_LE_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i <= n ==> f(i) <= g(i))
             ==> sum(m..n) f <= sum(m..n) g`,
  SIMP_TAC[SUM_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let SUM_EQ_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (sum(m..n) f = sum(m..n) g)`,
  MESON_TAC[SUM_EQ; FINITE_NUMSEG; IN_NUMSEG]);;

let SUM_ABS_NUMSEG = prove
 (`!f m n. abs(sum(m..n) f) <= sum(m..n) (\i. abs(f i))`,
  SIMP_TAC[SUM_ABS; FINITE_NUMSEG]);;

let SUM_CONST_NUMSEG = prove
 (`!c m n. sum(m..n) (\n. c) = &((n + 1) - m) * c`,
  SIMP_TAC[SUM_CONST; FINITE_NUMSEG; CARD_NUMSEG]);;

let SUM_EQ_0_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> (f(i) = &0)) ==> (sum(m..n) f = &0)`,
  SIMP_TAC[SUM_EQ_0; IN_NUMSEG]);;

let SUM_TRIV_NUMSEG = prove
 (`!f m n. n < m ==> (sum(m..n) f = &0)`,
  MESON_TAC[SUM_EQ_0_NUMSEG; LE_TRANS; NOT_LT]);;

let SUM_POS_LE_NUMSEG = prove
 (`!m n f. (!p. m <= p /\ p <= n ==> &0 <= f(p)) ==> &0 <= sum(m..n) f`,
  SIMP_TAC[SUM_POS_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let SUM_POS_EQ_0_NUMSEG = prove
 (`!f m n. (!p. m <= p /\ p <= n ==> &0 <= f(p)) /\ (sum(m..n) f = &0)
           ==> !p. m <= p /\ p <= n ==> (f(p) = &0)`,
  MESON_TAC[SUM_POS_EQ_0; FINITE_NUMSEG; IN_NUMSEG]);;

let SUM_SING_NUMSEG = prove
 (`!f n. sum(n..n) f = f(n)`,
  SIMP_TAC[SUM_SING; NUMSEG_SING]);;

let SUM_CLAUSES_NUMSEG = prove
 (`(!m. sum(m..0) f = if m = 0 then f(0) else &0) /\
   (!m n. sum(m..SUC n) f = if m <= SUC n then sum(m..n) f + f(SUC n)
                            else sum(m..n) f)`,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_REAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_REAL_ADD; sum]);;

let SUM_CLAUSES_NUMSEG_LT = prove
 (`sum {i | i < 0} f = &0 /\
   (!k. sum {i | i < SUC k} f = sum {i | i < k} f + f k)`,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG_LT MONOIDAL_REAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_REAL_ADD; sum]);;

let SUM_CLAUSES_NUMSEG_LE = prove
 (`sum {i | i <= 0} f = f 0 /\
   (!k. sum {i | i <= SUC k} f = sum {i | i <= k} f + f(SUC k))`,
  MP_TAC(MATCH_MP ITERATE_CLAUSES_NUMSEG_LE MONOIDAL_REAL_ADD) THEN
  REWRITE_TAC[NEUTRAL_REAL_ADD; sum]);;

let SUM_SWAP_NUMSEG = prove
 (`!a b c d f.
     sum(a..b) (\i. sum(c..d) (f i)) = sum(c..d) (\j. sum(a..b) (\i. f i j))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN
  REWRITE_TAC[FINITE_NUMSEG]);;

let SUM_ADD_SPLIT = prove
 (`!f m n p.
        m <= n + 1 ==> (sum (m..(n+p)) f = sum(m..n) f + sum(n+1..n+p) f)`,
  SIMP_TAC[NUMSEG_ADD_SPLIT; SUM_UNION; DISJOINT_NUMSEG; FINITE_NUMSEG;
           ARITH_RULE `x < x + 1`]);;

let SUM_OFFSET = prove
 (`!p f m n. sum(m+p..n+p) f = sum(m..n) (\i. f(i + p))`,
  SIMP_TAC[NUMSEG_OFFSET_IMAGE; SUM_IMAGE;
           EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF]);;

let SUM_OFFSET_0 = prove
 (`!f m n. m <= n ==> (sum(m..n) f = sum(0..n-m) (\i. f(i + m)))`,
  SIMP_TAC[GSYM SUM_OFFSET; ADD_CLAUSES; SUB_ADD]);;

let SUM_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> sum(m..n) f = f(m) + sum(m+1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; SUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let SUM_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> sum(m..n) f = sum(m..n-1) f + f(n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; SUM_CLAUSES_NUMSEG; SUC_SUB1]);;

let SUM_PAIR = prove
 (`!f m n. sum(2*m..2*n+1) f = sum(m..n) (\i. f(2*i) + f(2*i+1))`,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_REAL_ADD) THEN
  REWRITE_TAC[sum; NEUTRAL_REAL_ADD]);;

let SUM_REFLECT = prove
 (`!x m n. sum(m..n) x = if n < m then &0 else sum(0..n-m) (\i. x(n - i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sum] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP ITERATE_REFLECT MONOIDAL_REAL_ADD] THEN
  REWRITE_TAC[NEUTRAL_REAL_ADD]);;

let REAL_OF_NUM_SUM_NUMSEG = prove
 (`!f m n. (&(nsum(m..n) f) = sum (m..n) (\i. &(f i)))`,
  SIMP_TAC[REAL_OF_NUM_SUM; FINITE_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* Partial summation and other theorems specific to number segments.         *)
(* ------------------------------------------------------------------------- *)

let SUM_PARTIAL_SUC = prove
 (`!f g m n.
        sum (m..n) (\k. f(k) * (g(k + 1) - g(k))) =
            if m <= n then f(n + 1) * g(n + 1) - f(m) * g(m) -
                           sum (m..n) (\k. g(k + 1) * (f(k + 1) - f(k)))
            else &0`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[SUM_TRIV_NUMSEG; GSYM NOT_LE] THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN ASM_SIMP_TAC[] THENL [REAL_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[GSYM NOT_LT; SUM_TRIV_NUMSEG; ARITH_RULE `n < SUC n`] THEN
  ASM_SIMP_TAC[GSYM ADD1; ADD_CLAUSES] THEN REAL_ARITH_TAC);;

let SUM_PARTIAL_PRE = prove
 (`!f g m n.
        sum (m..n) (\k. f(k) * (g(k) - g(k - 1))) =
            if m <= n then f(n + 1) * g(n) - f(m) * g(m - 1) -
                           sum (m..n) (\k. g k * (f(k + 1) - f(k)))
            else &0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `\k. (g:num->real)(k - 1)`;
                 `m:num`; `n:num`] SUM_PARTIAL_SUC) THEN
  REWRITE_TAC[ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let SUM_DIFFS = prove
 (`!m n. sum(m..n) (\k. f(k) - f(k + 1)) =
          if m <= n then f(m) - f(n + 1) else &0`,
  ONCE_REWRITE_TAC[REAL_ARITH `a - b = -- &1 * (b - a)`] THEN
  ONCE_REWRITE_TAC[SUM_PARTIAL_SUC] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0] THEN
  REAL_ARITH_TAC);;

let SUM_DIFFS_ALT = prove
 (`!m n. sum(m..n) (\k. f(k + 1) - f(k)) =
          if m <= n then f(n + 1) - f(m) else &0`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  SIMP_TAC[SUM_NEG; SUM_DIFFS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_NEG_SUB; REAL_NEG_0]);;

let SUM_COMBINE_R = prove
 (`!f m n p. m <= n + 1 /\ n <= p
             ==> sum(m..n) f + sum(n+1..p) f = sum(m..p) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_EQ THEN
  REWRITE_TAC[FINITE_NUMSEG; EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY;
              IN_NUMSEG] THEN
  ASM_ARITH_TAC);;

let SUM_COMBINE_L = prove
 (`!f m n p. 0 < n /\ m <= n /\ n <= p + 1
             ==> sum(m..n-1) f + sum(n..p) f = sum(m..p) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_UNION_EQ THEN
  REWRITE_TAC[FINITE_NUMSEG; EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY;
              IN_NUMSEG] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extend congruences to deal with sum. Note that we must have the eta       *)
(* redex or we'll get a loop since f(x) will lambda-reduce recursively.      *)
(* ------------------------------------------------------------------------- *)

let th = prove
 (`(!f g s:A->bool.
        (!x. x IN s ==> f(x) = g(x))
        ==> sum s (\i. f(i)) = sum s g) /\
   (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
              ==> sum(a..b) (\i. f(i)) = sum(a..b) g) /\
   (!f g p. (!x. p x ==> f x = g x)
            ==> sum {y | p y} (\i. f(i)) = sum {y | p y} g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
  extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* Expand "sum (m..n) f" where m and n are numerals.                         *)
(* ------------------------------------------------------------------------- *)

let EXPAND_SUM_CONV =
  let [pth_0; pth_1; pth_2] = (CONJUNCTS o prove)
   (`(n < m ==> sum(m..n) f = &0) /\
     sum(m..m) f = f m /\
     (m <= n ==> sum (m..n) f = f m + sum (m + 1..n) f)`,
    REWRITE_TAC[SUM_CLAUSES_LEFT; SUM_SING_NUMSEG; SUM_TRIV_NUMSEG])
  and ns_tm = `..` and f_tm = `f:num->real`
  and m_tm = `m:num` and n_tm = `n:num` in
  let rec conv tm =
    let smn,ftm = dest_comb tm in
    let s,mn = dest_comb smn in
    if not(is_const s && fst(dest_const s) = "sum")
    then failwith "EXPAND_SUM_CONV" else
    let mtm,ntm = dest_binop ns_tm mn in
    let m = dest_numeral mtm and n = dest_numeral ntm in
    if n </ m then
      let th1 = INST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_0 in
      MP th1 (EQT_ELIM(NUM_LT_CONV(lhand(concl th1))))
    else if n =/ m then CONV_RULE (RAND_CONV(TRY_CONV BETA_CONV))
                                 (INST [ftm,f_tm; mtm,m_tm] pth_1)
    else
      let th1 = INST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_2 in
      let th2 = MP th1 (EQT_ELIM(NUM_LE_CONV(lhand(concl th1)))) in
      CONV_RULE (RAND_CONV(COMB2_CONV (RAND_CONV(TRY_CONV BETA_CONV))
       (LAND_CONV(LAND_CONV NUM_ADD_CONV) THENC conv))) th2 in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Some special algebraic rearrangements.                                    *)
(* ------------------------------------------------------------------------- *)

let REAL_SUB_POW = prove
 (`!x y n.
        1 <= n ==> x pow n - y pow n =
                   (x - y) * sum(0..n-1) (\i. x pow i * y pow (n - 1 - i))`,
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  REWRITE_TAC[REAL_ARITH
   `(x - y) * (a * b):real = (x * a) * b - a * (y * b)`] THEN
  SIMP_TAC[GSYM real_pow; ADD1; ARITH_RULE
    `1 <= n /\ x <= n - 1
     ==> n - 1 - x = n - (x + 1) /\ SUC(n - 1 - x) = n - x`] THEN
  REWRITE_TAC[SUM_DIFFS_ALT; LE_0] THEN
  SIMP_TAC[SUB_0; SUB_ADD; SUB_REFL; real_pow; REAL_MUL_LID; REAL_MUL_RID]);;

let REAL_SUB_POW_R1 = prove
 (`!x n. 1 <= n ==> x pow n - &1 = (x - &1) * sum(0..n-1) (\i. x pow i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real`; `&1`] o MATCH_MP REAL_SUB_POW) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID]);;

let REAL_SUB_POW_L1 = prove
 (`!x n. 1 <= n ==> &1 - x pow n = (&1 - x) * sum(0..n-1) (\i. x pow i)`,
  ONCE_REWRITE_TAC[GSYM REAL_NEG_SUB] THEN
  SIMP_TAC[REAL_SUB_POW_R1] THEN REWRITE_TAC[REAL_MUL_LNEG]);;

(* ------------------------------------------------------------------------- *)
(* Some useful facts about real polynomial functions.                        *)
(* ------------------------------------------------------------------------- *)

let REAL_SUB_POLYFUN = prove
 (`!a x y n.
    1 <= n
    ==> sum(0..n) (\i. a i * x pow i) - sum(0..n) (\i. a i * y pow i) =
        (x - y) *
        sum(0..n-1) (\j. sum(j+1..n) (\i. a i * y pow (i - j - 1)) * x pow j)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_LDISTRIB] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP SUM_CLAUSES_LEFT (SPEC_ALL LE_0)] THEN
  REWRITE_TAC[REAL_SUB_REFL; real_pow; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  SIMP_TAC[REAL_SUB_POW; ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * x * s:real = x * a * s`] THEN
  REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL; SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  REPEAT(EXISTS_TAC `\(x:num,y:num). (y,x)`) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `a - b - c:num = a - (b + c)`; ADD_SYM] THEN
  REWRITE_TAC[REAL_MUL_AC] THEN ARITH_TAC);;

let REAL_SUB_POLYFUN_ALT = prove
 (`!a x y n.
    1 <= n
    ==> sum(0..n) (\i. a i * x pow i) - sum(0..n) (\i. a i * y pow i) =
        (x - y) *
        sum(0..n-1) (\j. sum(0..n-j-1) (\k. a(j+k+1) * y pow k) * x pow j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_SUB_POLYFUN] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC
   [`\i. i - (j + 1)`; `\k. j + k + 1`] THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  TRY(BINOP_TAC THEN AP_TERM_TAC) THEN ASM_ARITH_TAC);;

let REAL_POLYFUN_ROOTBOUND = prove
 (`!n c. ~(!i. i IN 0..n ==> c i = &0)
         ==> FINITE {x | sum(0..n) (\i. c i * x pow i) = &0} /\
             CARD {x | sum(0..n) (\i. c i * x pow i) = &0} <= n`,
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN INDUCT_TAC THENL
   [REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2; SUM_CLAUSES_NUMSEG] THEN
    SIMP_TAC[real_pow; REAL_MUL_RID; EMPTY_GSPEC; CARD_CLAUSES; FINITE_EMPTY;
             LE_REFL];
    X_GEN_TAC `c:num->real` THEN REWRITE_TAC[IN_NUMSEG] THEN
    DISCH_TAC THEN ASM_CASES_TAC `(c:num->real) (SUC n) = &0` THENL
     [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0; REAL_MUL_LZERO; REAL_ADD_RID] THEN
      REWRITE_TAC[LE; LEFT_OR_DISTRIB] THEN DISJ2_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[IN_NUMSEG; LE];
      ASM_CASES_TAC `{x | sum (0..SUC n) (\i. c i * x pow i) = &0} = {}` THEN
      ASM_REWRITE_TAC[FINITE_RULES; CARD_CLAUSES; LE_0] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      MP_TAC(GEN `x:real` (ISPECL [`c:num->real`; `x:real`; `r:real`; `SUC n`]
        REAL_SUB_POLYFUN)) THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`; REAL_SUB_RZERO] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; REAL_ENTIRE; REAL_SUB_0]) THEN
      REWRITE_TAC[SET_RULE `{x | x = c \/ P x} = c INSERT {x | P x}`] THEN
      MATCH_MP_TAC(MESON[FINITE_INSERT; CARD_CLAUSES;
                         ARITH_RULE `x <= n ==> SUC x <= SUC n /\ x <= SUC n`]
        `FINITE s /\ CARD s <= n
         ==> FINITE(r INSERT s) /\ CARD(r INSERT s) <= SUC n`) THEN
      REWRITE_TAC[SUC_SUB1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG; ADD1; LE_REFL; LE_0] THEN
      REWRITE_TAC[SUM_SING_NUMSEG; ARITH_RULE `(n + 1) - n - 1 = 0`] THEN
      ASM_REWRITE_TAC[GSYM ADD1; real_pow; REAL_MUL_RID]]]);;

let REAL_POLYFUN_FINITE_ROOTS = prove
 (`!n c. FINITE {x | sum(0..n) (\i. c i * x pow i) = &0} <=>
         ?i. i IN 0..n /\ ~(c i = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAUT `a /\ ~b <=> ~(a ==> b)`] THEN
  REWRITE_TAC[GSYM NOT_FORALL_THM] THEN EQ_TAC THEN
  SIMP_TAC[REAL_POLYFUN_ROOTBOUND] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[REAL_MUL_LZERO; SUM_0] THEN
  REWRITE_TAC[SET_RULE `{x | T} = (:real)`; real_INFINITE; GSYM INFINITE]);;

let REAL_POLYFUN_EQ_0 = prove
 (`!n c. (!x. sum(0..n) (\i. c i * x pow i) = &0) <=>
         (!i. i IN 0..n ==> c i = &0)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_THEN(MP_TAC o MATCH_MP
     REAL_POLYFUN_ROOTBOUND) THEN
    ASM_REWRITE_TAC[real_INFINITE; GSYM INFINITE; DE_MORGAN_THM;
                    SET_RULE `{x | T} = (:real)`];
    ASM_SIMP_TAC[IN_NUMSEG; LE_0; REAL_MUL_LZERO; SUM_0]]);;

let REAL_POLYFUN_EQ_CONST = prove
 (`!n c k. (!x. sum(0..n) (\i. c i * x pow i) = k) <=>
           c 0 = k /\ (!i. i IN 1..n ==> c i = &0)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `!x. sum(0..n) (\i. (if i = 0 then c 0 - k else c i) * x pow i) = &0` THEN
  CONJ_TAC THENL
   [SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; real_pow; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `(c - k) + s = &0 <=> c + s = k`] THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH];
    REWRITE_TAC[REAL_POLYFUN_EQ_0; IN_NUMSEG; LE_0] THEN
    GEN_REWRITE_TAC LAND_CONV [MESON[]
     `(!n. P n) <=> P 0 /\ (!n. ~(n = 0) ==> P n)`] THEN
    SIMP_TAC[LE_0; REAL_SUB_0] THEN MESON_TAC[LE_1]]);;

(* ------------------------------------------------------------------------- *)
(* A general notion of polynomial function.                                  *)
(* ------------------------------------------------------------------------- *)

let polynomial_function = new_definition
 `polynomial_function p <=> ?m c. !x. p x = sum(0..m) (\i. c i * x pow i)`;;

let POLYNOMIAL_FUNCTION_CONST = prove
 (`!c. polynomial_function (\x. c)`,
  GEN_TAC THEN REWRITE_TAC[polynomial_function] THEN
  MAP_EVERY EXISTS_TAC [`0`; `(\i. c):num->real`] THEN
  REWRITE_TAC[SUM_SING_NUMSEG; real_pow; REAL_MUL_RID]);;

let POLYNOMIAL_FUNCTION_ID = prove
 (`polynomial_function (\x. x)`,
  REWRITE_TAC[polynomial_function] THEN
  MAP_EVERY EXISTS_TAC [`SUC 0`; `\i. if i = 1 then &1 else &0`] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; ARITH] THEN REAL_ARITH_TAC);;

let POLYNOMIAL_FUNCTION_I = prove
 (`polynomial_function I`,
  REWRITE_TAC[I_DEF; POLYNOMIAL_FUNCTION_ID]);;

let POLYNOMIAL_FUNCTION_ADD = prove
 (`!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x + q x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; polynomial_function; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC  [`m:num`; `a:num->real`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `b:num->real`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `MAX m n` THEN EXISTS_TAC
   `\i:num. (if i <= m then a i else &0) + (if i <= n then b i else &0)` THEN
  GEN_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN BINOP_TAC THEN
  BINOP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC);;

let POLYNOMIAL_FUNCTION_LMUL = prove
 (`!p c. polynomial_function p ==> polynomial_function (\x. c * p x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; polynomial_function; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC  [`n:num`; `a:num->real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `\i. c * (a:num->real) i`] THEN
  ASM_REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC]);;

let POLYNOMIAL_FUNCTION_RMUL = prove
 (`!p c. polynomial_function p ==> polynomial_function (\x. p x * c)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[POLYNOMIAL_FUNCTION_LMUL]);;

let POLYNOMIAL_FUNCTION_NEG = prove
 (`!p. polynomial_function(\x. --(p x)) <=> polynomial_function p`,
  GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `--(&1)` o MATCH_MP POLYNOMIAL_FUNCTION_LMUL) THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; ETA_AX; REAL_NEG_NEG]);;

let POLYNOMIAL_FUNCTION_SUB = prove
 (`!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x - q x)`,
  SIMP_TAC[real_sub; POLYNOMIAL_FUNCTION_NEG; POLYNOMIAL_FUNCTION_ADD]);;

let POLYNOMIAL_FUNCTION_MUL = prove
 (`!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (\x. p x * q x)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [polynomial_function] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[] `(!q m c. P q m c) <=> (!m c q. P q m c)`] THEN
  ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[SUM_SING_NUMSEG; real_pow; POLYNOMIAL_FUNCTION_RMUL] THEN
  X_GEN_TAC `c:num->real` THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD1] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; real_pow] THEN
  MATCH_MP_TAC POLYNOMIAL_FUNCTION_ADD THEN
  ASM_SIMP_TAC[POLYNOMIAL_FUNCTION_RMUL] THEN
  REWRITE_TAC[SPEC `1` SUM_OFFSET] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_ASSOC; SUM_RMUL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i. (c:num->real)(i + 1)`) THEN
  ABBREV_TAC `q = \x. p x * sum (0..m) (\i. c (i + 1) * x pow i)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[polynomial_function; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `a:num->real`] THEN STRIP_TAC THEN
  EXISTS_TAC `n + 1` THEN
  EXISTS_TAC `\i. if i = 0 then &0 else (a:num->real)(i - 1)` THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  ASM_REWRITE_TAC[SPEC `1` SUM_OFFSET; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC; SUM_RMUL] THEN REAL_ARITH_TAC);;

let POLYNOMIAL_FUNCTION_SUM = prove
 (`!s:A->bool p.
        FINITE s /\ (!i. i IN s ==> polynomial_function(\x. p x i))
        ==> polynomial_function (\x. sum s (p x))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; POLYNOMIAL_FUNCTION_CONST] THEN
  SIMP_TAC[FORALL_IN_INSERT; POLYNOMIAL_FUNCTION_ADD]);;

let POLYNOMIAL_FUNCTION_POW = prove
 (`!p n. polynomial_function p ==> polynomial_function (\x. p x pow n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; POLYNOMIAL_FUNCTION_CONST; POLYNOMIAL_FUNCTION_MUL]);;

let POLYNOMIAL_FUNCTION_INDUCT = prove
 (`!P. P (\x. x) /\ (!c. P (\x. c)) /\
      (!p q. P p /\ P q ==> P (\x. p x + q x)) /\
      (!p q. P p /\ P q ==> P (\x. p x * q x))
      ==> !p. polynomial_function p ==> P p`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[polynomial_function; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[] `(!q m c. P q m c) <=> (!m c q. P q m c)`] THEN
  ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_SING_NUMSEG; real_pow] THEN
  GEN_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; ADD1; LE_0] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[real_pow] THEN
  REWRITE_TAC[SPEC `1` SUM_OFFSET] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_ASSOC; SUM_RMUL] THEN
  ASM_SIMP_TAC[]);;

let POLYNOMIAL_FUNCTION_o = prove
 (`!p q. polynomial_function p /\ polynomial_function q
         ==> polynomial_function (p o q)`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ_ALT; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC POLYNOMIAL_FUNCTION_INDUCT THEN
  SIMP_TAC[o_DEF; POLYNOMIAL_FUNCTION_ADD; POLYNOMIAL_FUNCTION_MUL] THEN
  ASM_REWRITE_TAC[ETA_AX; POLYNOMIAL_FUNCTION_CONST]);;

let POLYNOMIAL_FUNCTION_FINITE_ROOTS = prove
 (`!p a. polynomial_function p
         ==> (FINITE {x | p x = a} <=> ~(!x. p x = a))`,
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  SUBGOAL_THEN
   `!p. polynomial_function p ==> (FINITE {x | p x = &0} <=> ~(!x. p x = &0))`
   (fun th ->
      SIMP_TAC[th; POLYNOMIAL_FUNCTION_SUB; POLYNOMIAL_FUNCTION_CONST]) THEN
  GEN_TAC THEN REWRITE_TAC[polynomial_function] THEN
  STRIP_TAC THEN EQ_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THENL
   [SIMP_TAC[UNIV_GSPEC; GSYM INFINITE; real_INFINITE];
    ASM_REWRITE_TAC[REAL_POLYFUN_FINITE_ROOTS] THEN
    SIMP_TAC[NOT_EXISTS_THM; TAUT `~(p /\ ~q) <=> p ==> q`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; SUM_0]]);;

(* ------------------------------------------------------------------------- *)
(* Make natural numbers the default again.                                   *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;
