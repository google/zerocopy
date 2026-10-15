(* ========================================================================= *)
(* Theory of lists, plus characters and strings as lists of characters.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2014                         *)
(* ========================================================================= *)

needs "ind_types.ml";;

(* ------------------------------------------------------------------------- *)
(* Standard tactic for list induction using MATCH_MP_TAC list_INDUCT         *)
(* ------------------------------------------------------------------------- *)

let LIST_INDUCT_TAC =
  let list_INDUCT = prove
   (`!P:(A)list->bool. P [] /\ (!h t. P t ==> P (CONS h t)) ==> !l. P l`,
    MATCH_ACCEPT_TAC list_INDUCT) in
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN GEN_TAC THEN DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* Basic definitions.                                                        *)
(* ------------------------------------------------------------------------- *)

let HD = new_recursive_definition list_RECURSION
  `HD(CONS (h:A) t) = h`;;

let TL = new_recursive_definition list_RECURSION
  `TL(CONS (h:A) t) = t`;;

let APPEND = new_recursive_definition list_RECURSION
  `(!l:(A)list. APPEND [] l = l) /\
   (!h t l. APPEND (CONS h t) l = CONS h (APPEND t l))`;;

let REVERSE = new_recursive_definition list_RECURSION
  `(REVERSE [] = []) /\
   (REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x])`;;

let LENGTH = new_recursive_definition list_RECURSION
  `(LENGTH [] = 0) /\
   (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t))`;;

let MAP = new_recursive_definition list_RECURSION
  `(!f:A->B. MAP f NIL = NIL) /\
   (!f h t. MAP f (CONS h t) = CONS (f h) (MAP f t))`;;

let LAST = new_recursive_definition list_RECURSION
  `LAST (CONS (h:A) t) = if t = [] then h else LAST t`;;

let BUTLAST = new_recursive_definition list_RECURSION
 `(BUTLAST [] = []) /\
  (BUTLAST (CONS (h:A) t) = if t = [] then [] else CONS h (BUTLAST t))`;;

let REPLICATE = new_recursive_definition num_RECURSION
  `(REPLICATE 0 (x:A) = []) /\
   (REPLICATE (SUC n) x = CONS x (REPLICATE n x))`;;

let NULL = new_recursive_definition list_RECURSION
  `(NULL [] = T) /\
   (NULL (CONS (h:A) t) = F)`;;

let ALL = new_recursive_definition list_RECURSION
  `(ALL P [] = T) /\
   (ALL P (CONS (h:A) t) <=> P h /\ ALL P t)`;;

let EX = new_recursive_definition list_RECURSION
  `(EX P [] = F) /\
   (EX P (CONS (h:A) t) <=> P h \/ EX P t)`;;

let ITLIST = new_recursive_definition list_RECURSION
  `(ITLIST (f:A->B->B) [] b = b) /\
   (ITLIST f (CONS h t) b = f h (ITLIST f t b))`;;

let MEM = new_recursive_definition list_RECURSION
  `(MEM (x:A) [] <=> F) /\
   (MEM x (CONS h t) <=> (x = h) \/ MEM x t)`;;

let ALL2_DEF = new_recursive_definition list_RECURSION
  `(ALL2 (P:A->B->bool) [] l2 <=> (l2 = [])) /\
   (ALL2 P (CONS h1 t1) l2 <=>
        if l2 = [] then F
        else P h1 (HD l2) /\ ALL2 P t1 (TL l2))`;;

let ALL2 = prove
 (`(ALL2 (P:A->B->bool) [] [] <=> T) /\
   (ALL2 P (CONS h1 t1) [] <=> F) /\
   (ALL2 P [] (CONS h2 t2) <=> F) /\
   (ALL2 P (CONS h1 t1) (CONS h2 t2) <=> P h1 h2 /\ ALL2 P t1 t2)`,
  REWRITE_TAC[distinctness "list"; ALL2_DEF; HD; TL]);;

let MAP2_DEF = new_recursive_definition list_RECURSION
  `(MAP2 (f:A->B->C) [] l = []) /\
   (MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l)))`;;

let MAP2 = prove
 (`(MAP2 (f:A->B->C) [] [] = []) /\
   (MAP2 f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (MAP2 f t1 t2))`,
  REWRITE_TAC[MAP2_DEF; HD; TL]);;

let EL = new_recursive_definition num_RECURSION
  `(EL 0 l :A = HD l) /\
   (EL (SUC n) l = EL n (TL l))`;;

let FILTER = new_recursive_definition list_RECURSION
  `(FILTER (P:A->bool) [] = []) /\
   (FILTER P (CONS h t) = if P h then CONS h (FILTER P t) else FILTER P t)`;;

let ASSOC = new_recursive_definition list_RECURSION
  `ASSOC a (CONS (h:A#B) t) = if FST h = a then SND h else ASSOC a t`;;

let ITLIST2_DEF = new_recursive_definition list_RECURSION
  `(ITLIST2 (f:A->B->C->C) [] l2 b = b) /\
   (ITLIST2 f (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b))`;;

let ITLIST2 = prove
 (`(ITLIST2 (f:A->B->C->C) [] [] b = b) /\
   (ITLIST2 f (CONS h1 t1) (CONS h2 t2) b = f h1 h2 (ITLIST2 f t1 t2 b))`,
  REWRITE_TAC[ITLIST2_DEF; HD; TL]);;

let ZIP_DEF = new_recursive_definition list_RECURSION
  `(ZIP [] l2 :(A#B)list = []) /\
   (ZIP (CONS h1 t1) l2:(A#B)list = CONS (h1,HD l2) (ZIP t1 (TL l2)))`;;

let ZIP = prove
 (`(ZIP [] [] :(A#B)list = []) /\
   (ZIP (CONS h1 t1) (CONS h2 t2) :(A#B)list = CONS (h1,h2) (ZIP t1 t2))`,
  REWRITE_TAC[ZIP_DEF; HD; TL]);;

let ALLPAIRS = new_recursive_definition list_RECURSION
  `(ALLPAIRS (f:A->B->bool) [] l <=> T) /\
   (ALLPAIRS f (CONS h t) l <=> ALL (f h) l /\ ALLPAIRS f t l)`;;

let PAIRWISE = new_recursive_definition list_RECURSION
  `(PAIRWISE (r:A->A->bool) [] <=> T) /\
   (PAIRWISE (r:A->A->bool) (CONS h t) <=> ALL (r h) t /\ PAIRWISE r t)`;;

let list_of_seq = new_recursive_definition num_RECURSION
 `list_of_seq (s:num->A) 0 = [] /\
  list_of_seq s (SUC n) = APPEND (list_of_seq s n) [s n]`;;

(* ------------------------------------------------------------------------- *)
(* Various trivial theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

let NOT_CONS_NIL = prove
 (`!(h:A) t. ~(CONS h t = [])`,
  REWRITE_TAC[distinctness "list"]);;

let LAST_CLAUSES = prove
 (`(LAST [h:A] = h) /\
   (LAST (CONS h (CONS k t)) = LAST (CONS k t))`,
  REWRITE_TAC[LAST; NOT_CONS_NIL]);;

let APPEND_NIL = prove
 (`!l:A list. APPEND l [] = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let APPEND_ASSOC = prove
 (`!(l:A list) m n. APPEND l (APPEND m n) = APPEND (APPEND l m) n`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let REVERSE_APPEND = prove
 (`!(l:A list) m. REVERSE (APPEND l m) = APPEND (REVERSE m) (REVERSE l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; REVERSE; APPEND_NIL; APPEND_ASSOC]);;

let REVERSE_REVERSE = prove
 (`!l:A list. REVERSE(REVERSE l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; REVERSE_APPEND; APPEND]);;

let REVERSE_EQ_EMPTY = prove
 (`!l:A list. REVERSE l = [] <=> l = []`,
  MESON_TAC[REVERSE_REVERSE; REVERSE]);;

let CONS_11 = prove
 (`!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)`,
  REWRITE_TAC[injectivity "list"]);;

let list_CASES = prove
 (`!l:(A)list. (l = []) \/ ?h t. l = CONS h t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CONS_11; NOT_CONS_NIL] THEN
  MESON_TAC[]);;

let LIST_EQ = prove
 (`!l1 l2:A list.
        l1 = l2 <=>
        LENGTH l1 = LENGTH l2 /\ !n. n < LENGTH l2 ==> EL n l1 = EL n l2`,
  REPEAT LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; CONS_11; LENGTH; CONJUNCT1 LT; NOT_SUC] THEN
  ASM_REWRITE_TAC[SUC_INJ] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [MESON[num_CASES] `(!n. P n) <=> P 0 /\ (!n. P(SUC n))`] THEN
  REWRITE_TAC[EL; HD; TL; LT_0; LT_SUC; CONJ_ACI]);;

let LENGTH_APPEND = prove
 (`!(l:A list) m. LENGTH(APPEND l m) = LENGTH l + LENGTH m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES]);;

let MAP_APPEND = prove
 (`!f:A->B. !l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]);;

let LENGTH_MAP = prove
 (`!l. !f:A->B. LENGTH (MAP f l) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH]);;

let LENGTH_EQ_NIL = prove
 (`!l:A list. (LENGTH l = 0) <=> (l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_CONS_NIL; NOT_SUC]);;

let LENGTH_EQ_CONS = prove
 (`!(l:A list) n. LENGTH l = SUC n <=> ?h t. (l = CONS h t) /\ (LENGTH t = n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[SUC_INJ; CONS_11] THEN MESON_TAC[]);;

let LENGTH_REVERSE = prove
 (`!l:A list. LENGTH(REVERSE l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REVERSE; LENGTH_APPEND; LENGTH] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES]);;

let MAP_o = prove
 (`!f:A->B. !g:B->C. !l. MAP (g o f) l = MAP g (MAP f l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; o_THM]);;

let MAP_EQ = prove
 (`!(f:A->B) g l. ALL (\x. f x = g x) l ==> (MAP f l = MAP g l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL] THEN ASM_MESON_TAC[]);;

let ALL_IMP = prove
 (`!P Q l:A list. (!x. MEM x l /\ P x ==> Q x) /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; ALL] THEN ASM_MESON_TAC[]);;

let NOT_EX = prove
 (`!P l:A list. ~(EX P l) <=> ALL (\x. ~(P x)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; ALL; DE_MORGAN_THM]);;

let NOT_ALL = prove
 (`!P l:A list. ~(ALL P l) <=> EX (\x. ~(P x)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; ALL; DE_MORGAN_THM]);;

let ALL_MAP = prove
 (`!P (f:A->B) l. ALL P (MAP f l) <=> ALL (P o f) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; MAP; o_THM]);;

let ALL_EQ = prove
 (`!l:A list.
        ALL R l /\ (!x. R x ==> (P x <=> Q x)) ==> (ALL P l <=> ALL Q l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  STRIP_TAC THEN BINOP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let ALL_T = prove
 (`!l:A list. ALL (\x. T) l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL]);;

let MAP_EQ_ALL2 = prove
 (`!(f:A->B) l m. ALL2 (\x y. f x = f y) l m ==> MAP f l = MAP f m`,
  GEN_TAC THEN
  REPEAT LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; ALL2; CONS_11] THEN
  ASM_MESON_TAC[]);;

let ALL2_MAP = prove
 (`!P (f:A->B) l. ALL2 P (MAP f l) l <=> ALL (\a. P (f a) a) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP; ALL]);;

let MAP_EQ_DEGEN = prove
 (`!l (f:A->A). ALL (\x. f(x) = x) l ==> (MAP f l = l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; CONS_11] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let ALL2_AND_RIGHT = prove
 (`!l m P Q. ALL2 (\(x:A) (y:B). P x /\ Q x y) l m <=> ALL P l /\ ALL2 Q l m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; ALL2] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; ALL2] THEN
  REWRITE_TAC[CONJ_ACI]);;

let ITLIST_APPEND = prove
 (`!(f:A->B->B) a l1 l2.
        ITLIST f (APPEND l1 l2) a = ITLIST f l1 (ITLIST f l2 a)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; APPEND]);;

let ITLIST_EXTRA = prove
 (`!(f:A->B->B) l. ITLIST f (APPEND l [a]) b = ITLIST f l (f a b)`,
  REWRITE_TAC[ITLIST_APPEND; ITLIST]);;

let ALL_MP = prove
 (`!P Q (l:A list). ALL (\x. P x ==> Q x) l /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

let AND_ALL = prove
 (`!l:A list. ALL P l /\ ALL Q l <=> ALL (\x. P x /\ Q x) l`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; CONJ_ACI]);;

let EX_IMP = prove
 (`!P Q (l:A list). (!x. MEM x l /\ P x ==> Q x) /\ EX P l ==> EX Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; EX] THEN ASM_MESON_TAC[]);;

let ALL_MEM = prove
 (`!P (l:A list). (!x. MEM x l ==> P x) <=> ALL P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MEM] THEN
  ASM_MESON_TAC[]);;

let LENGTH_REPLICATE = prove
 (`!n x:A. LENGTH(REPLICATE n x) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; REPLICATE]);;

let MEM_REPLICATE = prove
 (`!n x y:A. MEM x (REPLICATE n y) <=> x = y /\ ~(n = 0)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; REPLICATE; NOT_SUC] THEN
  MESON_TAC[]);;

let EX_MAP = prove
 (`!P (f:A->B) l. EX P (MAP f l) <=> EX (P o f) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; EX; o_THM]);;

let EXISTS_EX = prove
 (`!(P:A->B->bool) l. (?x. EX (P x) l) <=> EX (\s. ?x. P x s) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX] THEN
  ASM_MESON_TAC[]);;

let FORALL_ALL = prove
 (`!(P:A->B->bool) l. (!x. ALL (P x) l) <=> ALL (\s. !x. P x s) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[]);;

let MEM_APPEND = prove
 (`!(x:A) l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \/ MEM x l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; APPEND; DISJ_ACI]);;

let MEM_MAP = prove
 (`!(f:A->B) y l. MEM y (MAP f l) <=> ?x. MEM x l /\ (y = f x)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MEM; MAP] THEN MESON_TAC[]);;

let FILTER_APPEND = prove
 (`!(P:A->bool) l1 l2.
        FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

let FILTER_MAP = prove
 (`!P (f:A->B) l. FILTER P (MAP f l) = MAP f (FILTER (P o f) l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; FILTER; o_THM] THEN COND_CASES_TAC THEN
  REWRITE_TAC[MAP]);;

let MEM_FILTER = prove
 (`!P l (x:A). MEM x (FILTER P l) <=> P x /\ MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; FILTER] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

let LENGTH_FILTER = prove
 (`!P l:A list. LENGTH(FILTER P l) <= LENGTH l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; LE_REFL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; LE_SUC] THEN
  ASM_MESON_TAC[LE_TRANS; LE]);;

let EX_MEM = prove
 (`!P (l:A list). (?x. P x /\ MEM x l) <=> EX P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX; MEM] THEN
  ASM_MESON_TAC[]);;

let MAP_FST_ZIP = prove
 (`!(l1:A list) (l2:B list).
    LENGTH l1 = LENGTH l2 ==> MAP FST (ZIP l1 l2) = l1`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; SUC_INJ; MAP; FST; ZIP; NOT_SUC]);;

let MAP_SND_ZIP = prove
 (`!(l1:A list) (l2:B list).
    LENGTH l1 = LENGTH l2 ==> MAP SND (ZIP l1 l2) = l2`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; SUC_INJ; MAP; FST; ZIP; NOT_SUC]);;

let LENGTH_ZIP = prove
 (`!(l1:A list) (l2:B list).
    LENGTH l1 = LENGTH l2 ==> LENGTH(ZIP l1 l2) = LENGTH l2`,
  REPEAT(LIST_INDUCT_TAC ORELSE GEN_TAC) THEN
  ASM_SIMP_TAC[LENGTH; NOT_SUC; ZIP; SUC_INJ]);;

let MEM_ASSOC = prove
 (`!(l:(A#B)list) x. MEM (x,ASSOC x l) l <=> MEM x (MAP FST l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; MAP; ASSOC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PAIR; FST]);;

let ALL_APPEND = prove
 (`!P l1 l2:A list. ALL P (APPEND l1 l2) <=> ALL P l1 /\ ALL P l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; APPEND; GSYM CONJ_ASSOC]);;

let MEM_EL = prove
 (`!(l:A list) n. n < LENGTH l ==> MEM (EL n l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJUNCT1 LT; LENGTH] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; LT_SUC; TL]);;

let MEM_EXISTS_EL = prove
 (`!(l:A list) x. MEM x l <=> ?i. i < LENGTH l /\ x = EL i l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; EL; MEM; CONJUNCT1 LT] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV
   [MESON[num_CASES] `(?i. P i) <=> P 0 \/ (?i. P(SUC i))`] THEN
  REWRITE_TAC[LT_SUC; LT_0; EL; HD; TL]);;

let ALL_EL = prove
 (`!P (l:A list). (!i. i < LENGTH l ==> P (EL i l)) <=> ALL P l`,
  REWRITE_TAC[GSYM ALL_MEM; MEM_EXISTS_EL] THEN MESON_TAC[]);;

let ALL2_MAP2 = prove
 (`!(f:A->B) (g:C->D) l m.
        ALL2 P (MAP f l) (MAP g m) = ALL2 (\x y. P (f x) (g y)) l m`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP]);;

let AND_ALL2 = prove
 (`!(P:A->B->bool) Q l m.
        ALL2 P l m /\ ALL2 Q l m <=> ALL2 (\x y. P x y /\ Q x y) l m`,
  GEN_TAC THEN GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[CONJ_ACI]);;

let ALLPAIRS_SYM = prove
 (`!(P:A->B->bool) l m. ALLPAIRS P l m <=> ALLPAIRS (\x y. P y x) m l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALLPAIRS] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALLPAIRS; ALL] THEN
  ASM_MESON_TAC[]);;

let ALLPAIRS_MEM = prove
 (`!(P:A->B->bool) l m.
        (!x y. MEM x l /\ MEM y m ==> P x y) <=> ALLPAIRS P l m`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALLPAIRS; GSYM ALL_MEM; MEM] THEN
  ASM_MESON_TAC[]);;

let ALLPAIRS_MAP = prove
 (`!P (f:A->B) (g:C->D) l m.
        ALLPAIRS P (MAP f l) (MAP g m) <=>
        ALLPAIRS (\x y. P (f x) (g y)) l m`,
  REWRITE_TAC[GSYM ALLPAIRS_MEM; MEM_MAP] THEN MESON_TAC[]);;

let ALLPAIRS_EQ = prove
 (`!l m. !P Q. ALL P (l:A list) /\ ALL Q (m:B list) /\
               (!p q. P p /\ Q q ==> (R p q <=> R' p q))
               ==> (ALLPAIRS R l m <=> ALLPAIRS R' l m)`,
  REWRITE_TAC[GSYM ALLPAIRS_MEM; GSYM ALL_MEM] THEN MESON_TAC[]);;

let ALL2_ALL = prove
 (`!P (l:A list). ALL2 P l l <=> ALL (\x. P x x) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL]);;

let APPEND_EQ_NIL = prove
 (`!l m:A list. (APPEND l m = []) <=> (l = []) /\ (m = [])`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_APPEND; ADD_EQ_0]);;

let APPEND_LCANCEL = prove
 (`!l1 l2 l3:A list. APPEND l1 l2 = APPEND l1 l3 <=> l2 = l3`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; CONS_11]);;

let APPEND_RCANCEL = prove
 (`!l1 l2 l3:A list. APPEND l1 l3 = APPEND l2 l3 <=> l1 = l2`,
  ONCE_REWRITE_TAC[MESON[REVERSE_REVERSE]
   `l = l' <=> REVERSE l = REVERSE l'`] THEN
  REWRITE_TAC[REVERSE_APPEND; APPEND_LCANCEL]);;

let LENGTH_MAP2 = prove
 (`!(f:A->B->C) l m. LENGTH l = LENGTH m ==> LENGTH(MAP2 f l m) = LENGTH m`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_CONS_NIL; NOT_SUC; MAP2; SUC_INJ]);;

let EL_MAP2 = prove
 (`!(f:A->B->C) l m k.
        k < LENGTH l /\ k < LENGTH m
        ==> EL k (MAP2 f l m) = f (EL k l) (EL k m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; CONJUNCT1 LT] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[LENGTH; MAP2; EL; HD; TL; LT_SUC]);;

let MAP_EQ_NIL  = prove
 (`!(f:A->B) l. MAP f l = [] <=> l = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL]);;

let INJECTIVE_MAP = prove
 (`!f:A->B. (!l m. MAP f l = MAP f m ==> l = m) <=>
            (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[x:A]`; `[y:A]`]) THEN
    ASM_REWRITE_TAC[MAP; CONS_11];
    REPEAT LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
    ASM_MESON_TAC[]]);;

let SURJECTIVE_MAP = prove
 (`!f:A->B. (!m. ?l. MAP f l = m) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `y:B` THEN FIRST_X_ASSUM(MP_TAC o SPEC `[y:B]`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; CONS_11; NOT_CONS_NIL; MAP_EQ_NIL];
    MATCH_MP_TAC list_INDUCT] THEN
  ASM_MESON_TAC[MAP]);;

let MAP_ID = prove
 (`!l. MAP (\x:A. x) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]);;

let MAP_I = prove
 (`MAP (I:A->A) = I`,
  REWRITE_TAC[FUN_EQ_THM; I_DEF; MAP_ID]);;

let BUTLAST_CLAUSES = prove
 (`BUTLAST([]:A list) = [] /\
   (!a:A. BUTLAST [a] = []) /\
   (!(a:A) h t. BUTLAST(CONS a (CONS h t)) = CONS a (BUTLAST(CONS h t)))`,
  REWRITE_TAC[BUTLAST; NOT_CONS_NIL]);;

let BUTLAST_APPEND = prove
 (`!l m:A list. BUTLAST(APPEND l m) =
                if m = [] then BUTLAST l else APPEND l (BUTLAST m)`,
  SIMP_TAC[COND_RAND; APPEND_NIL; MESON[]
   `(if p then T else q) <=> ~p ==> q`] THEN
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[APPEND; BUTLAST; APPEND_EQ_NIL]);;

let APPEND_BUTLAST_LAST = prove
 (`!l:A list. ~(l = []) ==> APPEND (BUTLAST l) [LAST l] = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LAST; BUTLAST; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[APPEND]);;

let LAST_APPEND = prove
 (`!p q:A list. LAST(APPEND p q) = if q = [] then LAST p else LAST q`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LAST; APPEND_EQ_NIL] THEN
  MESON_TAC[]);;

let LENGTH_TL = prove
 (`!l:A list. ~(l = []) ==> LENGTH(TL l) = LENGTH l - 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; TL; ARITH; SUC_SUB1]);;

let LAST_REVERSE = prove
 (`!l:A list. ~(l = []) ==> LAST(REVERSE l) = HD l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[HD; REVERSE; LAST; LAST_APPEND; NOT_CONS_NIL]);;

let HD_REVERSE = prove
 (`!l:A list. ~(l = []) ==> HD(REVERSE l) = LAST l`,
  MESON_TAC[LAST_REVERSE; REVERSE_REVERSE; REVERSE_EQ_EMPTY]);;

let EL_APPEND = prove
 (`!k l m:A list.
        EL k (APPEND l m) = if k < LENGTH l then EL k l
                            else EL (k - LENGTH l) m`,
  INDUCT_TAC THEN REWRITE_TAC[EL] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[HD; APPEND; LENGTH; SUB_0; EL; LT_0; CONJUNCT1 LT] THEN
  ASM_REWRITE_TAC[TL; LT_SUC; SUB_SUC]);;

let EL_TL = prove
 (`!n. EL n (TL l):A = EL (n + 1) l`,
  REWRITE_TAC[GSYM ADD1; EL]);;

let EL_CONS = prove
 (`!n (h:A) t. EL n (CONS h t) = if n = 0 then h else EL (n - 1) t`,
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; NOT_SUC; SUC_SUB1]);;

let LAST_EL = prove
 (`!l:A list. ~(l = []) ==> LAST l = EL (LENGTH l - 1) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LAST; LENGTH; SUC_SUB1] THEN
  DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[LENGTH; EL; HD; EL_CONS; LENGTH_EQ_NIL]);;

let HD_APPEND = prove
 (`!l m:A list. HD(APPEND l m) = if l = [] then HD m else HD l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HD; APPEND; NOT_CONS_NIL]);;

let CONS_HD_TL = prove
 (`!l:A list. ~(l = []) ==> l = CONS (HD l) (TL l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL;HD;TL]);;

let EL_MAP = prove
 (`!(f:A->B) n l. n < LENGTH l ==> EL n (MAP f l) = f(EL n l)`,
  GEN_TAC THEN INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; CONJUNCT1 LT; LT_0; EL; HD; TL; MAP; LT_SUC]);;

let MAP_REVERSE = prove
 (`!(f:A->B) l. REVERSE(MAP f l) = MAP f (REVERSE l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; REVERSE; MAP_APPEND]);;

let ALL_FILTER = prove
 (`!P Q l:A list. ALL P (FILTER Q l) <=> ALL (\x. Q x ==> P x) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; FILTER] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL]);;

let APPEND_SING = prove
 (`!(h:A) t. APPEND [h] t = CONS h t`,
  REWRITE_TAC[APPEND]);;

let MEM_APPEND_DECOMPOSE_LEFT = prove
 (`!x:A l. MEM x l <=> ?l1 l2. ~(MEM x l1) /\ l = APPEND l1 (CONS x l2)`,
  REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; MEM_APPEND; MEM] THEN X_GEN_TAC `x:A` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[MEM] THEN
  MAP_EVERY X_GEN_TAC [`y:A`; `l:A list`] THEN
  ASM_CASES_TAC `x:A = y` THEN ASM_MESON_TAC[MEM; APPEND]);;

let MEM_APPEND_DECOMPOSE = prove
 (`!x:A l. MEM x l <=> ?l1 l2. l = APPEND l1 (CONS x l2)`,
  REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; MEM_APPEND; MEM] THEN
  ONCE_REWRITE_TAC[MEM_APPEND_DECOMPOSE_LEFT] THEN MESON_TAC[]);;

let PAIRWISE_APPEND = prove
 (`!R:A->A->bool l m.
        PAIRWISE R (APPEND l m) <=>
        PAIRWISE R l /\ PAIRWISE R m /\ (!x y. MEM x l /\ MEM y m ==> R x y)`,
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[APPEND; PAIRWISE; MEM; ALL_APPEND; GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let PAIRWISE_MAP = prove
 (`!R f:A->B l.
        PAIRWISE R (MAP f l) <=> PAIRWISE (\x y. R (f x) (f y)) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[PAIRWISE; MAP; ALL_MAP; o_DEF]);;

let PAIRWISE_IMPLIES = prove
 (`!R:A->A->bool R' l.
        PAIRWISE R l /\ (!x y. MEM x l /\ MEM y l /\ R x y ==> R' x y)
        ==> PAIRWISE R' l`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[PAIRWISE; GSYM ALL_MEM; MEM] THEN MESON_TAC[]);;

let PAIRWISE_TRANSITIVE = prove
 (`!R x y:A l.
      (!x y z. R x y /\ R y z ==> R x z)
      ==> (PAIRWISE R (CONS x (CONS y l)) <=> R x y /\ PAIRWISE R (CONS y l))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PAIRWISE; ALL; GSYM CONJ_ASSOC;
              TAUT `(p /\ q /\ r /\ s <=> p /\ r /\ s) <=>
                    p /\ s ==> r ==> q`] THEN
  STRIP_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ALL_IMP) THEN
  ASM_MESON_TAC[]);;

let LENGTH_LIST_OF_SEQ = prove
 (`!s:num->A n. LENGTH(list_of_seq s n) = n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[list_of_seq; LENGTH; LENGTH_APPEND; ADD_CLAUSES]);;

let EL_LIST_OF_SEQ = prove
 (`!s:num->A m n. m < n ==> EL m (list_of_seq s n) = s m`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; LT; EL_APPEND; LENGTH_LIST_OF_SEQ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUB_REFL; EL; HD; LT_REFL]);;

let LIST_OF_SEQ_EQ_NIL = prove
 (`!s:num->A n. list_of_seq s n = [] <=> n = 0`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_LIST_OF_SEQ; LENGTH]);;

let LIST_OF_SEQ_EQ_SELF = prove
 (`!l:A list. list_of_seq (\i. EL i l) (LENGTH l) = l`,
  SIMP_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ]);;

let LENGTH_EQ_LIST_OF_SEQ = prove
 (`!(l:A list) n. LENGTH l = n <=> l = list_of_seq (\i. EL i l) n`,
  MESON_TAC[LIST_OF_SEQ_EQ_SELF; LENGTH_LIST_OF_SEQ]);;

let MAP_LIST_OF_SEQ = prove
 (`!f (g:A->B) n. MAP g (list_of_seq f n) = list_of_seq (g o f) n`,
  GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; list_of_seq; MAP_APPEND; o_THM]);;

let LIST_OF_SEQ = prove
 (`(!(f:num->A). list_of_seq f 0 = []) /\
   (!(f:num->A) n.
        list_of_seq f (SUC n) = CONS (f 0) (list_of_seq (f o SUC) n))`,
  REWRITE_TAC[CONJUNCT1 list_of_seq] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH; EL_CONS] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[NOT_SUC; EL_LIST_OF_SEQ] THEN
  ASM_SIMP_TAC[LT_SUC; SUC_SUB1; EL_LIST_OF_SEQ; o_THM]);;

(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

let mk_cons h t =
  try let cons = mk_const("CONS",[type_of h,aty]) in
      mk_comb(mk_comb(cons,h),t)
  with Failure _ -> failwith "mk_cons";;

let mk_list (tms,ty) =
  try let nil = mk_const("NIL",[ty,aty]) in
      if tms = [] then nil else
      let cons = mk_const("CONS",[ty,aty]) in
      itlist (mk_binop cons) tms nil
  with Failure _ -> failwith "mk_list";;

let mk_flist tms =
  try mk_list(tms,type_of(hd tms))
  with Failure _ -> failwith "mk_flist";;

(* ------------------------------------------------------------------------- *)
(* Extra monotonicity theorems for inductive definitions.                    *)
(* ------------------------------------------------------------------------- *)

let MONO_ALL = prove
 (`(!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l`,
  DISCH_TAC THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

let MONO_ALL2 = prove
 (`(!x y. (P:A->B->bool) x y ==> Q x y) ==> ALL2 P l l' ==> ALL2 Q l l'`,
  DISCH_TAC THEN
  SPEC_TAC(`l':B list`,`l':B list`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2_DEF] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

monotonicity_theorems := [MONO_ALL; MONO_ALL2] @ !monotonicity_theorems;;

(* ------------------------------------------------------------------------- *)
(* Apply a conversion down a list.                                           *)
(* ------------------------------------------------------------------------- *)

let rec LIST_CONV conv tm =
  if is_cons tm then
    COMB2_CONV (RAND_CONV conv) (LIST_CONV conv) tm
  else if fst(dest_const tm) = "NIL" then REFL tm
  else failwith "LIST_CONV";;

(* ------------------------------------------------------------------------- *)
(* Some relatively efficient and tail-recursive (though very long and        *)
(* explicit) evaluation conversions for a subset of the list operations.     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_CONV:conv =
  let pthc = prove
   (`LENGTH(t:A list) = LENGTH t + 0 /\
     LENGTH([]:A list) + n = n /\
     LENGTH(CONS (h:A) t) + n = LENGTH t + SUC n`,
    REWRITE_TAC[LENGTH; ADD_CLAUSES]) in
  let pths = CONJUNCTS pthc
  and avars = sort (<) (frees(concl pthc)) in
  fun tm ->
    match tm with
      Comb(Const("LENGTH",_),ltm) when is_list ltm ->
        let tyin = [hd(snd(dest_type(type_of ltm))),aty] in
        let [h_tm;n_tm;t_tm] = map (inst tyin) avars
        and [pth_init;pth_base;pth_step] = map (INST_TYPE tyin) pths in
        let rec conv th =
          let altm,ntm = dest_comb(rand(concl th)) in
          let ltm = rand(rand altm) in
          if is_cons ltm then
            let htm,ttm = dest_cons ltm in
            let th1 = INST [htm,h_tm; ttm,t_tm; ntm,n_tm] pth_step in
            let ftm,stm = dest_comb(rand(concl th1)) in
            let th2 = TRANS th1 (AP_TERM ftm (NUM_SUC_CONV stm)) in
            conv (TRANS th th2)
          else
            TRANS th (INST [ntm,n_tm] pth_base) in
         (try conv (INST [rand tm,t_tm] pth_init)
          with Failure _ -> failwith "LENGTH_CONV")
    | _ -> failwith "LENGTH_CONV";;

let EL_CONV:conv =
  let pthc = prove
    (`EL 0 (CONS (h:A) t) = h /\
      (n = SUC m ==> EL n (CONS h t) = EL m t)`,
    SIMP_TAC[EL; HD; TL]) in
  let pths = map UNDISCH_ALL (CONJUNCTS pthc)
  and avars = sort (<) (frees(concl pthc)) in
  fun tm ->
    match tm with
      Comb(Comb(Const("EL",_),ntm),ltm) when is_list ltm ->
        let tyin = [hd(snd(dest_type(type_of ltm))),aty] in
        let [h_tm;m_tm;n_tm;t_tm] = map (inst tyin) avars
        and [pth_base;pth_step] = map (INST_TYPE tyin) pths in
        let rec conv th =
          let entm,ltm = dest_comb(rand(concl th)) in
          let htm,ttm = dest_cons ltm in
          let etm,ntm = dest_comb entm in
          let n = dest_numeral ntm in
          if n =/ num_0 then
            TRANS th (INST [htm,h_tm; ttm,t_tm] pth_base)
          else
            let th1 = num_CONV ntm in
            let th2 = INST [ntm,n_tm; rand(rand(concl th1)),m_tm;
                            htm,h_tm; ttm,t_tm] pth_step in
            let th3 = TRANS th (PROVE_HYP th1 th2) in
            conv th3 in
        (try conv(REFL tm) with Failure _ -> failwith "EL_CONV")
    | _ -> failwith "EL_CONV";;

let REVERSE_CONV:conv =
  let pthc = prove
   (`l:A list = APPEND l [] /\
     APPEND (REVERSE []) l:A list = l /\
     APPEND (REVERSE (CONS h t)) l = APPEND (REVERSE t) (CONS h l)`,
    SIMP_TAC[APPEND; APPEND_NIL; REVERSE; GSYM APPEND_ASSOC]) in
  let pths = map UNDISCH_ALL (CONJUNCTS pthc)
  and avars = sort (<) (frees(concl pthc)) in
  fun tm ->
    match tm with
      Comb(Const("REVERSE",_),ltm) ->
        let tyin = [hd(snd(dest_type(type_of ltm))),aty] in
        let [h_tm;l_tm;t_tm] = map (inst tyin) avars
        and [pth_init;pth_base;pth_step] = map (INST_TYPE tyin) pths in
        let rec conv th =
          let ahtm,ltm = dest_comb(rand(concl th)) in
          let httm = rand(rand ahtm) in
          if is_cons httm then
            let htm,ttm = dest_cons httm in
            let th1 = INST [htm,h_tm; ltm,l_tm; ttm,t_tm] pth_step in
            conv (TRANS th th1)
          else
            TRANS th (INST [ltm,l_tm] pth_base) in
         (try conv (INST [tm,l_tm] pth_init)
          with Failure _ -> failwith "REVERSE_CONV")
    | _ -> failwith "REVERSE_CONV";;

let LIST_OF_SEQ_CONV:conv =
  let pthc = prove
   (`l:A list = APPEND l [] /\
     APPEND (list_of_seq f 0) l:A list = l /\
     (n = SUC m
      ==> APPEND (list_of_seq f n) l =
          APPEND (list_of_seq f m) (CONS (f m) l))`,
    SIMP_TAC[APPEND; APPEND_NIL; list_of_seq; GSYM APPEND_ASSOC]) in
  let pths = map UNDISCH_ALL (CONJUNCTS pthc)
  and avars = sort (<) (frees(concl pthc)) in
  fun tm ->
    match tm with
      Comb(Comb(Const("list_of_seq",_),ftm),ntm) ->
        let tyin = [snd(dest_fun_ty (type_of ftm)),aty] in
        let [f_tm;l_tm;m_tm;n_tm] = map (inst tyin) avars
        and [pth_init;pth_base;pth_step] = map (INST_TYPE tyin) pths
        and bflag = is_abs ftm in
        let rec conv th =
          let nftm,ltm = dest_comb(rand(concl th)) in
          let lftm,ntm = dest_comb (rand nftm) in
          let ftm = rand lftm in
          let n = dest_numeral ntm in
          if n =/ num_0 then
            TRANS th (INST [ftm,f_tm; ltm,l_tm] pth_base)
          else
            let th1 = num_CONV ntm in
            let th2 = INST [ntm,n_tm; rand(rand(concl th1)),m_tm;
                            ftm,f_tm; ltm,l_tm] pth_step in
            let th3 = TRANS th (PROVE_HYP th1 th2) in
            let th4 = if not bflag then th3 else
              let jtm,ctxtm = dest_comb(rand(concl th3)) in
              let cttm,xtm = dest_comb ctxtm in
              let ctm,ttm = dest_comb cttm in
              TRANS th3
                (AP_TERM jtm (AP_THM (AP_TERM ctm (BETA_CONV ttm)) xtm)) in
            conv th4 in
        (try conv (INST [tm,l_tm] pth_init)
         with Failure _ -> failwith "LIST_OF_SEQ_CONV")
    | _ -> failwith "LIST_OF_SEQ_CONV";;

(* ------------------------------------------------------------------------- *)
(* Type of characters, like the HOL88 "ascii" type, with syntax              *)
(* constructors and equality conversions for chars and strings.              *)
(* ------------------------------------------------------------------------- *)

let char_INDUCT,char_RECURSION = define_type
 "char = ASCII bool bool bool bool bool bool bool bool";;

new_type_abbrev("string",`:char list`);;

let dest_char,mk_char,dest_string,mk_string,CHAR_EQ_CONV,STRING_EQ_CONV =
  let bool_of_term t =
    match t with
      Const("T",_) -> true
    | Const("F",_) -> false
    | _ -> failwith "bool_of_term" in
  let code_of_term t =
    let f,tms = strip_comb t in
    if not(is_const f && fst(dest_const f) = "ASCII")
       || not(length tms = 8) then failwith "code_of_term"
    else
       itlist (fun b f -> if b then 1 + 2 * f else 2 * f)
              (map bool_of_term (rev tms)) 0 in
  let char_of_term = Char.chr o code_of_term in
  let dest_string tm =
    try let tms = dest_list tm in
        if fst(dest_type(hd(snd(dest_type(type_of tm))))) <> "char"
        then fail() else
        let ccs = map (String.make 1 o char_of_term) tms in
        String.escaped (implode ccs)
    with Failure _ -> failwith "dest_string" in
  let mk_bool b =
    let true_tm,false_tm = `T`,`F` in
    if b then true_tm else false_tm in
  let mk_code =
    let ascii_tm = `ASCII` in
    let mk_code c =
      let lis = map (fun i -> mk_bool((c / (1 lsl i)) mod 2 = 1)) (0--7) in
      itlist (fun x y -> mk_comb(y,x)) lis ascii_tm in
    let codes = Array.map mk_code (Array.of_list (0--255)) in
    fun c -> Array.get codes c in
  let mk_char = mk_code o Char.code in
  let mk_string s =
    let ns = map (fun i -> Char.code(String.get s i))
                 (0--(String.length s - 1)) in
    mk_list(map mk_code ns,`:char`) in
  let CHAR_DISTINCTNESS =
    let avars,bvars,cvars =
     [`a0:bool`;`a1:bool`;`a2:bool`;`a3:bool`;`a4:bool`;`a5:bool`;`a6:bool`],
     [`b1:bool`;`b2:bool`;`b3:bool`;`b4:bool`;`b5:bool`;`b6:bool`;`b7:bool`],
     [`c1:bool`;`c2:bool`;`c3:bool`;`c4:bool`;`c5:bool`;`c6:bool`;`c7:bool`] in
    let ASCII_NEQS_FT = (map EQF_INTRO o CONJUNCTS o prove)
     (`~(ASCII F b1 b2 b3 b4 b5 b6 b7 = ASCII T c1 c2 c3 c4 c5 c6 c7) /\
       ~(ASCII a0 F b2 b3 b4 b5 b6 b7 = ASCII a0 T c2 c3 c4 c5 c6 c7) /\
       ~(ASCII a0 a1 F b3 b4 b5 b6 b7 = ASCII a0 a1 T c3 c4 c5 c6 c7) /\
       ~(ASCII a0 a1 a2 F b4 b5 b6 b7 = ASCII a0 a1 a2 T c4 c5 c6 c7) /\
       ~(ASCII a0 a1 a2 a3 F b5 b6 b7 = ASCII a0 a1 a2 a3 T c5 c6 c7) /\
       ~(ASCII a0 a1 a2 a3 a4 F b6 b7 = ASCII a0 a1 a2 a3 a4 T c6 c7) /\
       ~(ASCII a0 a1 a2 a3 a4 a5 F b7 = ASCII a0 a1 a2 a3 a4 a5 T c7) /\
       ~(ASCII a0 a1 a2 a3 a4 a5 a6 F = ASCII a0 a1 a2 a3 a4 a5 a6 T)`,
      REWRITE_TAC[injectivity "char"]) in
    let ASCII_NEQS_TF =
      let ilist = zip bvars cvars @ zip cvars bvars in
      let f = EQF_INTRO o INST ilist o GSYM o EQF_ELIM in
      map f ASCII_NEQS_FT in
    let rec prefix n l =
      if n = 0 then [] else
      match l with
        h::t -> h :: prefix (n-1) t
      | _ -> l in
    let rec findneq n prefix a b =
      match a,b with
        b1::a, b2::b -> if b1 <> b2 then n,rev prefix,bool_of_term b2,a,b else
                        findneq (n+1) (b1 :: prefix) a b
      | _, _ -> fail() in
    fun c1 c2 ->
      let _,a = strip_comb c1
      and _,b = strip_comb c2 in
      let n,p,b,s1,s2 = findneq 0 [] a b in
      let ss1 = funpow n tl bvars
      and ss2 = funpow n tl cvars in
      let pp = prefix n avars in
      let pth = if b then ASCII_NEQS_FT else ASCII_NEQS_TF in
      INST (zip p pp @ zip s1 ss1 @ zip s2 ss2) (el n pth) in
  let STRING_DISTINCTNESS =
    let xtm,xstm = `x:char`,`xs:string`
    and ytm,ystm = `y:char`,`ys:string`
    and niltm = `[]:string` in
    let NIL_EQ_THM = EQT_INTRO (REFL niltm)
    and CONS_EQ_THM,CONS_NEQ_THM = (CONJ_PAIR o prove)
     (`(CONS x xs:string = CONS x ys <=> xs = ys) /\
       ((x = y <=> F) ==> (CONS x xs:string = CONS y ys <=> F))`,
      REWRITE_TAC[CONS_11] THEN MESON_TAC[])
    and NIL_NEQ_CONS,CONS_NEQ_NIL = (CONJ_PAIR o prove)
     (`(NIL:string = CONS x xs <=> F) /\
       (CONS x xs:string = NIL <=> F)`,
      REWRITE_TAC[NOT_CONS_NIL]) in
    let rec STRING_DISTINCTNESS s1 s2 =
      if s1 = niltm
      then if s2 = niltm then NIL_EQ_THM
           else let c2,s2 = rand (rator s2),rand s2 in
                INST [c2,xtm;s2,xstm] NIL_NEQ_CONS
      else let c1,s1 = rand (rator s1),rand s1 in
           if s2 = niltm then INST [c1,xtm;s1,xstm] CONS_NEQ_NIL
           else let c2,s2 = rand (rator s2),rand s2 in
           if c1 = c2
           then let th1 = INST [c1,xtm; s1,xstm; s2,ystm] CONS_EQ_THM
                and th2 = STRING_DISTINCTNESS s1 s2 in
                TRANS th1 th2
           else let ilist = [c1,xtm; c2,ytm; s1,xstm; s2,ystm] in
                let itm = INST ilist CONS_NEQ_THM in
                MP itm (CHAR_DISTINCTNESS c1 c2) in
    STRING_DISTINCTNESS in
  let CHAR_EQ_CONV : conv =
    fun tm ->
      let c1,c2 = dest_eq tm in
      if compare c1 c2 = 0 then EQT_INTRO (REFL c1) else
      CHAR_DISTINCTNESS c1 c2
  and STRING_EQ_CONV tm =
    let ltm,rtm = dest_eq tm in
    if compare ltm rtm = 0 then EQT_INTRO (REFL ltm) else
    STRING_DISTINCTNESS ltm rtm in
  char_of_term,mk_char,dest_string,mk_string,CHAR_EQ_CONV,STRING_EQ_CONV;;
