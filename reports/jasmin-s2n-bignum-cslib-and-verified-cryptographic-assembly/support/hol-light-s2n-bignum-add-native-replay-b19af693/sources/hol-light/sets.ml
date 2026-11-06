(* ========================================================================= *)
(* Very basic set theory (using predicates as sets).                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2016                       *)
(*              (c) Copyright, Marco Maggesi 2012-2017                       *)
(*             (c) Copyright, Andrea Gabrielli 2012-2017                     *)
(* ========================================================================= *)

needs "int.ml";;

(* ------------------------------------------------------------------------- *)
(* Infix symbols for set operations.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("IN",(11,"right"));;
parse_as_infix("SUBSET",(12,"right"));;
parse_as_infix("PSUBSET",(12,"right"));;
parse_as_infix("INTER",(20,"right"));;
parse_as_infix("UNION",(16,"right"));;
parse_as_infix("DIFF",(18,"left"));;
parse_as_infix("INSERT",(21,"right"));;
parse_as_infix("DELETE",(21,"left"));;

parse_as_infix("HAS_SIZE",(12,"right"));;
parse_as_infix("<=_c",(12,"right"));;
parse_as_infix("<_c",(12,"right"));;
parse_as_infix(">=_c",(12,"right"));;
parse_as_infix(">_c",(12,"right"));;
parse_as_infix("=_c",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Set membership.                                                           *)
(* ------------------------------------------------------------------------- *)

let IN = new_definition
  `!P:A->bool. !x. x IN P <=> P x`;;

(* ------------------------------------------------------------------------- *)
(* Axiom of extensionality in this framework.                                *)
(* ------------------------------------------------------------------------- *)

let EXTENSION = prove
 (`!s t. (s = t) <=> !x:A. x IN s <=> x IN t`,
  REWRITE_TAC[IN; FUN_EQ_THM]);;

(* ------------------------------------------------------------------------- *)
(* General specification.                                                    *)
(* ------------------------------------------------------------------------- *)

let GSPEC = new_definition
  `GSPEC (p:A->bool) = p`;;

let SETSPEC = new_definition
  `SETSPEC (v:A) P t <=> P /\ (v = t)`;;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for eliminating set-comprehension membership assertions.     *)
(* ------------------------------------------------------------------------- *)

let IN_ELIM_THM = prove
 (`(!P x:A. x IN GSPEC (\v. P (SETSPEC v)) <=> P (\p t. p /\ (x = t))) /\
   (!p x:A. x IN GSPEC (\v. ?y. SETSPEC v (p y) y) <=> p x) /\
   (!P x:A. GSPEC (\v. P (SETSPEC v)) x <=> P (\p t. p /\ (x = t))) /\
   (!p x:A. GSPEC (\v. ?y. SETSPEC v (p y) y) x <=> p x) /\
   (!p x:A. x IN (\y. p y) <=> p x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN; GSPEC] THEN
  TRY(AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]) THEN
  REWRITE_TAC[SETSPEC] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* These two definitions are needed first, for the parsing of enumerations.  *)
(* ------------------------------------------------------------------------- *)

let EMPTY = new_definition
  `EMPTY = (\x:A. F)`;;

let INSERT_DEF = new_definition
  `x INSERT s = \y:A. y IN s \/ (y = x)`;;

(* ------------------------------------------------------------------------- *)
(* The other basic operations.                                               *)
(* ------------------------------------------------------------------------- *)

let UNIV = new_definition
  `UNIV = (\x:A. T)`;;

let UNION = new_definition
  `s UNION t = {x:A | x IN s \/ x IN t}`;;

let UNIONS = new_definition
  `UNIONS s = {x:A | ?u. u IN s /\ x IN u}`;;

let INTER = new_definition
  `s INTER t = {x:A | x IN s /\ x IN t}`;;

let INTERS = new_definition
  `INTERS s = {x:A | !u. u IN s ==> x IN u}`;;

let DIFF = new_definition
  `s DIFF t =  {x:A | x IN s /\ ~(x IN t)}`;;

let INSERT = prove
 (`x INSERT s = {y:A | y IN s \/ (y = x)}`,
  REWRITE_TAC[EXTENSION; INSERT_DEF; IN_ELIM_THM]);;

let DELETE = new_definition
  `s DELETE x = {y:A | y IN s /\ ~(y = x)}`;;

(* ------------------------------------------------------------------------- *)
(* Other basic predicates.                                                   *)
(* ------------------------------------------------------------------------- *)

let SUBSET = new_definition
  `s SUBSET t <=> !x:A. x IN s ==> x IN t`;;

let PSUBSET = new_definition
  `(s:A->bool) PSUBSET t <=> s SUBSET t /\ ~(s = t)`;;

let DISJOINT = new_definition
  `DISJOINT (s:A->bool) t <=> (s INTER t = EMPTY)`;;

let SING = new_definition
  `SING s = ?x:A. s = {x}`;;

(* ------------------------------------------------------------------------- *)
(* Finiteness.                                                               *)
(* ------------------------------------------------------------------------- *)

let FINITE_RULES,FINITE_INDUCT,FINITE_CASES =
  new_inductive_definition
    `FINITE (EMPTY:A->bool) /\
     !(x:A) s. FINITE s ==> FINITE (x INSERT s)`;;

let INFINITE = new_definition
  `INFINITE (s:A->bool) <=> ~(FINITE s)`;;

(* ------------------------------------------------------------------------- *)
(* Stuff concerned with functions.                                           *)
(* ------------------------------------------------------------------------- *)

let IMAGE = new_definition
  `IMAGE (f:A->B) s = { y | ?x. x IN s /\ (y = f x)}`;;

let INJ = new_definition
  `INJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))`;;

let SURJ = new_definition
  `SURJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))`;;

let BIJ = new_definition
  `BIJ (f:A->B) s t <=> INJ f s t /\ SURJ f s t`;;

(* ------------------------------------------------------------------------- *)
(* Another funny thing.                                                      *)
(* ------------------------------------------------------------------------- *)

let CHOICE = new_definition
  `CHOICE s = @x:A. x IN s`;;

let REST = new_definition
  `REST (s:A->bool) = s DELETE (CHOICE s)`;;

(* ------------------------------------------------------------------------- *)
(* Basic membership properties.                                              *)
(* ------------------------------------------------------------------------- *)

let NOT_IN_EMPTY = prove
 (`!x:A. ~(x IN EMPTY)`,
  REWRITE_TAC[IN; EMPTY]);;

let IN_UNIV = prove
 (`!x:A. x IN UNIV`,
  REWRITE_TAC[UNIV; IN]);;

let IN_UNION = prove
 (`!s t (x:A). x IN (s UNION t) <=> x IN s \/ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; UNION]);;

let IN_UNIONS = prove
 (`!s (x:A). x IN (UNIONS s) <=> ?t. t IN s /\ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; UNIONS]);;

let IN_INTER = prove
 (`!s t (x:A). x IN (s INTER t) <=> x IN s /\ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; INTER]);;

let IN_INTERS = prove
 (`!s (x:A). x IN (INTERS s) <=> !t. t IN s ==> x IN t`,
  REWRITE_TAC[IN_ELIM_THM; INTERS]);;

let IN_DIFF = prove
 (`!(s:A->bool) t x. x IN (s DIFF t) <=> x IN s /\ ~(x IN t)`,
  REWRITE_TAC[IN_ELIM_THM; DIFF]);;

let IN_INSERT = prove
 (`!x:A. !y s. x IN (y INSERT s) <=> (x = y) \/ x IN s`,
  ONCE_REWRITE_TAC[DISJ_SYM] THEN REWRITE_TAC[IN_ELIM_THM; INSERT]);;

let IN_DELETE = prove
 (`!s. !x:A. !y. x IN (s DELETE y) <=> x IN s /\ ~(x = y)`,
  REWRITE_TAC[IN_ELIM_THM; DELETE]);;

let IN_SING = prove
 (`!x y. x IN {y:A} <=> (x = y)`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

let IN_IMAGE = prove
 (`!y:B. !s f. (y IN (IMAGE f s)) <=> ?x:A. (y = f x) /\ x IN s`,
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[IN_ELIM_THM; IMAGE]);;

let IN_REST = prove
 (`!x:A. !s. x IN (REST s) <=> x IN s /\ ~(x = CHOICE s)`,
  REWRITE_TAC[REST; IN_DELETE]);;

let FORALL_IN_INSERT = prove
 (`!P a s. (!x:A. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x)`,
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

let EXISTS_IN_INSERT = prove
 (`!P a s. (?x:A. x IN (a INSERT s) /\ P x) <=> P a \/ ?x. x IN s /\ P x`,
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

let FORALL_IN_UNION = prove
 (`!P s t:A->bool.
        (!x. x IN s UNION t ==> P x) <=>
        (!x. x IN s ==> P x) /\ (!x. x IN t ==> P x)`,
  REWRITE_TAC[IN_UNION] THEN MESON_TAC[]);;

let EXISTS_IN_UNION = prove
 (`!P s t:A->bool.
        (?x. x IN s UNION t /\ P x) <=>
        (?x. x IN s /\ P x) \/ (?x. x IN t /\ P x)`,
  REWRITE_TAC[IN_UNION] THEN MESON_TAC[]);;

let FORALL_IN_IMAGE = prove
 (`!(f:A->B) s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let EXISTS_IN_IMAGE = prove
 (`!(f:A->B) s. (?y. y IN IMAGE f s /\ P y) <=> ?x. x IN s /\ P(f x)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let FORALL_IN_GSPEC = prove
 (`(!P Q (f:A->B). (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\
   (!P Q (f:A->B->C).
        (!z. z IN {f x y | P x y} ==> Q z) <=>
        (!x y. P x y ==> Q(f x y))) /\
   (!P Q (f:A->B->C->D).
        (!z. z IN {f w x y | P w x y} ==> Q z) <=>
        (!w x y. P w x y ==> Q(f w x y))) /\
   (!P Q (f:A->B->C->D->E).
        (!z. z IN {f v w x y | P v w x y} ==> Q z) <=>
        (!v w x y. P v w x y ==> Q(f v w x y)))`,
  REWRITE_TAC[GSPEC; IN_ELIM_THM] THEN MESON_TAC[]);;

let EXISTS_IN_GSPEC = prove
 (`(!P Q (f:A->B). (?z. z IN {f x | P x} /\ Q z) <=> (?x. P x /\ Q(f x))) /\
   (!P Q (f:A->B->C).
        (?z. z IN {f x y | P x y} /\ Q z) <=>
        (?x y. P x y /\ Q(f x y))) /\
   (!P Q (f:A->B->C->D).
        (?z. z IN {f w x y | P w x y} /\ Q z) <=>
        (?w x y. P w x y /\ Q(f w x y))) /\
   (!P Q (f:A->B->C->D->E).
        (?z. z IN {f v w x y | P v w x y} /\ Q z) <=>
        (?v w x y. P v w x y /\ Q(f v w x y)))`,
  REWRITE_TAC[GSPEC; IN_ELIM_THM] THEN MESON_TAC[]);;

let UNIONS_IMAGE = prove
 (`!(f:A->B->bool) s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}`,
  REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERS_IMAGE = prove
 (`!(f:A->B->bool) s. INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}`,
  REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let UNIONS_GSPEC = prove
 (`(!P (f:A->B->bool).
        UNIONS {f x | P x} = {a | ?x. P x /\ a IN (f x)}) /\
   (!P (f:A->B->C->bool).
        UNIONS {f x y | P x y} = {a | ?x y. P x y /\ a IN (f x y)}) /\
   (!P (f:A->B->C->D->bool).
        UNIONS {f x y z | P x y z} =
        {a | ?x y z. P x y z /\ a IN (f x y z)})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERS_GSPEC = prove
 (`(!P (f:A->B->bool).
        INTERS {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\
   (!P (f:A->B->C->bool).
        INTERS {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\
   (!P (f:A->B->C->D->bool).
        INTERS {f x y z | P x y z} =
        {a | !x y z. P x y z ==> a IN (f x y z)})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic property of the choice function.                                    *)
(* ------------------------------------------------------------------------- *)

let CHOICE_DEF = prove
 (`!s:A->bool. ~(s = EMPTY) ==> (CHOICE s) IN s`,
  REWRITE_TAC[CHOICE; EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM; EXISTS_THM]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to automate some routine set theory by reduction to FOL.           *)
(* ------------------------------------------------------------------------- *)

let SET_TAC =
  let PRESET_CONV =
    REWRITE_CONV[INTERS_IMAGE; INTERS_GSPEC; UNIONS_IMAGE; UNIONS_GSPEC] THENC
    REWRITE_CONV[EXTENSION; SUBSET; PSUBSET; DISJOINT; SING;
                 BIJ; INJ; SURJ] THENC
    REWRITE_CONV[NOT_IN_EMPTY; IN_UNIV; IN_UNION; IN_INTER; IN_DIFF; IN_INSERT;
                 IN_DELETE; IN_REST; IN_INTERS; IN_UNIONS; IN_IMAGE;
                 IN_ELIM_THM; IN] in
  fun ths ->
    MAP_EVERY MP_TAC ths THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REPEAT(COND_CASES_TAC THEN POP_ASSUM MP_TAC) THEN
    CONV_TAC PRESET_CONV THEN MAP_EVERY MP_TAC
     (filter (fun th -> CONV_RULE PRESET_CONV th = TRUTH) ths) THEN
    REWRITE_TAC[IN] THEN MESON_TAC[];;

let SET_RULE tm = prove(tm,SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc. theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

let NOT_EQUAL_SETS = prove
 (`!s:A->bool. !t. ~(s = t) <=> ?x. x IN t <=> ~(x IN s)`,
  SET_TAC[]);;

let INSERT_RESTRICT = prove
 (`!P s a:A.
        {x | x IN a INSERT s /\ P x} =
        if P a then a INSERT {x | x IN s /\ P x} else {x | x IN s /\ P x}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM SET_TAC[]);;

let UNIV_1 = prove
 (`(:1) = {one}`,
  SET_TAC[one]);;

(* ------------------------------------------------------------------------- *)
(* The empty set.                                                            *)
(* ------------------------------------------------------------------------- *)

let MEMBER_NOT_EMPTY = prove
 (`!s:A->bool. (?x. x IN s) <=> ~(s = EMPTY)`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The universal set.                                                        *)
(* ------------------------------------------------------------------------- *)

let UNIV_NOT_EMPTY = prove
 (`~(UNIV:A->bool = EMPTY)`,
  SET_TAC[]);;

let EMPTY_NOT_UNIV = prove
 (`~(EMPTY:A->bool = UNIV)`,
  SET_TAC[]);;

let EQ_UNIV = prove
 (`(!x:A. x IN s) <=> (s = UNIV)`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set inclusion.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUBSET_TRANS = prove
 (`!(s:A->bool) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u`,
  SET_TAC[]);;

let SUBSET_REFL = prove
 (`!s:A->bool. s SUBSET s`,
  SET_TAC[]);;

let SUBSET_ANTISYM = prove
 (`!(s:A->bool) t. s SUBSET t /\ t SUBSET s ==> s = t`,
  SET_TAC[]);;

let SUBSET_ANTISYM_EQ = prove
 (`!(s:A->bool) t. s SUBSET t /\ t SUBSET s <=> s = t`,
  SET_TAC[]);;

let EMPTY_SUBSET = prove
 (`!s:A->bool. EMPTY SUBSET s`,
  SET_TAC[]);;

let SUBSET_EMPTY = prove
 (`!s:A->bool. s SUBSET EMPTY <=> (s = EMPTY)`,
  SET_TAC[]);;

let SUBSET_UNIV = prove
 (`!s:A->bool. s SUBSET UNIV`,
  SET_TAC[]);;

let UNIV_SUBSET = prove
 (`!s:A->bool. UNIV SUBSET s <=> (s = UNIV)`,
  SET_TAC[]);;

let SING_SUBSET = prove
 (`!s x:A. {x} SUBSET s <=> x IN s`,
  SET_TAC[]);;

let SUBSET_RESTRICT = prove
 (`!s P. {x:A | x IN s /\ P x} SUBSET s`,
  SIMP_TAC[SUBSET; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Proper subset.                                                            *)
(* ------------------------------------------------------------------------- *)

let PSUBSET_TRANS = prove
 (`!(s:A->bool) t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

let PSUBSET_SUBSET_TRANS = prove
 (`!(s:A->bool) t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

let SUBSET_PSUBSET_TRANS = prove
 (`!(s:A->bool) t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

let PSUBSET_IRREFL = prove
 (`!s:A->bool. ~(s PSUBSET s)`,
  SET_TAC[]);;

let NOT_PSUBSET_EMPTY = prove
 (`!s:A->bool. ~(s PSUBSET EMPTY)`,
  SET_TAC[]);;

let NOT_UNIV_PSUBSET = prove
 (`!s:A->bool. ~(UNIV PSUBSET s)`,
  SET_TAC[]);;

let PSUBSET_UNIV = prove
 (`!s:A->bool. s PSUBSET UNIV <=> ?x. ~(x IN s)`,
  SET_TAC[]);;

let PSUBSET_ALT = prove
 (`!s t:A->bool. s PSUBSET t <=> s SUBSET t /\ (?a. a IN t /\ ~(a IN s))`,
  REWRITE_TAC[PSUBSET] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let UNION_ASSOC = prove
 (`!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)`,
  SET_TAC[]);;

let UNION_IDEMPOT = prove
 (`!s:A->bool. s UNION s = s`,
  SET_TAC[]);;

let UNION_COMM = prove
 (`!(s:A->bool) t. s UNION t = t UNION s`,
  SET_TAC[]);;

let SUBSET_UNION = prove
 (`(!s:A->bool. !t. s SUBSET (s UNION t)) /\
   (!s:A->bool. !t. s SUBSET (t UNION s))`,
  SET_TAC[]);;

let SUBSET_UNION_ABSORPTION = prove
 (`!s:A->bool. !t. s SUBSET t <=> (s UNION t = t)`,
  SET_TAC[]);;

let UNION_EMPTY = prove
 (`(!s:A->bool. EMPTY UNION s = s) /\
   (!s:A->bool. s UNION EMPTY = s)`,
  SET_TAC[]);;

let UNION_UNIV = prove
 (`(!s:A->bool. UNIV UNION s = UNIV) /\
   (!s:A->bool. s UNION UNIV = UNIV)`,
  SET_TAC[]);;

let EMPTY_UNION = prove
 (`!s:A->bool. !t. (s UNION t = EMPTY) <=> (s = EMPTY) /\ (t = EMPTY)`,
  SET_TAC[]);;

let UNION_SUBSET = prove
 (`!s t u:A->bool. (s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`,
  SET_TAC[]);;

let UNION_RESTRICT = prove
 (`!P s t:A->bool.
        {x | x IN (s UNION t) /\ P x} =
        {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`,
  SET_TAC[]);;

let FORALL_SUBSET_UNION = prove
 (`!t u:A->bool.
        (!s. s SUBSET t UNION u ==> P s) <=>
        (!t' u'. t' SUBSET t /\ u' SUBSET u ==> P(t' UNION u'))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`s INTER t:A->bool`; `s INTER u:A->bool`]) THEN
    ANTS_TAC THENL [ALL_TAC; MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC] THEN
    ASM SET_TAC[]]);;

let EXISTS_SUBSET_UNION = prove
 (`!t u:A->bool.
        (?s. s SUBSET t UNION u /\ P s) <=>
        (?t' u'. t' SUBSET t /\ u' SUBSET u /\ P(t' UNION u'))`,
  REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  REWRITE_TAC[FORALL_SUBSET_UNION] THEN MESON_TAC[]);;

let FORALL_SUBSET_INSERT = prove
 (`!a:A t. (!s. s SUBSET a INSERT t ==> P s) <=>
           (!s. s SUBSET t ==> P s /\ P (a INSERT s))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[FORALL_SUBSET_UNION; SET_RULE
   `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
  MESON_TAC[UNION_EMPTY]);;

let EXISTS_SUBSET_INSERT = prove
 (`!a:A t. (?s. s SUBSET a INSERT t /\ P s) <=>
           (?s. s SUBSET t /\ (P s \/ P (a INSERT s)))`,
  REWRITE_TAC[MESON[] `(?x. P x /\ Q x) <=> ~(!x. P x ==> ~Q x)`] THEN
  REWRITE_TAC[FORALL_SUBSET_INSERT] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* ------------------------------------------------------------------------- *)

let INTER_ASSOC = prove
 (`!(s:A->bool) t u. (s INTER t) INTER u = s INTER (t INTER u)`,
  SET_TAC[]);;

let INTER_IDEMPOT = prove
 (`!s:A->bool. s INTER s = s`,
  SET_TAC[]);;

let INTER_COMM = prove
 (`!(s:A->bool) t. s INTER t = t INTER s`,
  SET_TAC[]);;

let INTER_SUBSET = prove
 (`(!s:A->bool. !t. (s INTER t) SUBSET s) /\
   (!s:A->bool. !t. (t INTER s) SUBSET s)`,
  SET_TAC[]);;

let SUBSET_INTER_ABSORPTION = prove
 (`!s:A->bool. !t. s SUBSET t <=> (s INTER t = s)`,
  SET_TAC[]);;

let INTER_EMPTY = prove
 (`(!s:A->bool. EMPTY INTER s = EMPTY) /\
   (!s:A->bool. s INTER EMPTY = EMPTY)`,
  SET_TAC[]);;

let INTER_UNIV = prove
 (`(!s:A->bool. UNIV INTER s = s) /\
   (!s:A->bool. s INTER UNIV = s)`,
  SET_TAC[]);;

let SUBSET_INTER = prove
 (`!s t u:A->bool. s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`,
  SET_TAC[]);;

let INTER_RESTRICT = prove
 (`!P s (t:A->bool).
        {x | x IN (s INTER t) /\ P x} =
        {x | x IN s /\ P x} INTER {x | x IN t /\ P x}`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Distributivity.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNION_OVER_INTER = prove
 (`!s:A->bool. !t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`,
  SET_TAC[]);;

let INTER_OVER_UNION = prove
 (`!s:A->bool. !t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let IN_DISJOINT = prove
 (`!s:A->bool. !t. DISJOINT s t <=> ~(?x. x IN s /\ x IN t)`,
  SET_TAC[]);;

let DISJOINT_SYM = prove
 (`!s:A->bool. !t. DISJOINT s t <=> DISJOINT t s`,
  SET_TAC[]);;

let DISJOINT_EMPTY = prove
 (`!s:A->bool. DISJOINT EMPTY s /\ DISJOINT s EMPTY`,
  SET_TAC[]);;

let DISJOINT_EMPTY_REFL = prove
 (`!s:A->bool. (s = EMPTY) <=> (DISJOINT s s)`,
  SET_TAC[]);;

let DISJOINT_UNION = prove
 (`!s:A->bool. !t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u`,
  SET_TAC[]);;

let DISJOINT_SING = prove
 (`(!s a:A. DISJOINT s {a} <=> ~(a IN s)) /\
   (!s a:A. DISJOINT {a} s <=> ~(a IN s))`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

let DIFF_EMPTY = prove
 (`!s:A->bool. s DIFF EMPTY = s`,
  SET_TAC[]);;

let EMPTY_DIFF = prove
 (`!s:A->bool. EMPTY DIFF s = EMPTY`,
  SET_TAC[]);;

let DIFF_UNIV = prove
 (`!s:A->bool. s DIFF UNIV = EMPTY`,
  SET_TAC[]);;

let DIFF_DIFF = prove
 (`!s:A->bool. !t. (s DIFF t) DIFF t = s DIFF t`,
  SET_TAC[]);;

let DIFF_EQ_EMPTY = prove
 (`!s:A->bool. s DIFF s = EMPTY`,
  SET_TAC[]);;

let SUBSET_DIFF = prove
 (`!s t:A->bool. (s DIFF t) SUBSET s`,
  SET_TAC[]);;

let COMPL_COMPL = prove
 (`!s. (:A) DIFF ((:A) DIFF s) = s`,
  SET_TAC[]);;

let DIFF_RESTRICT = prove
 (`!P s (t:A->bool).
        {x | x IN (s DIFF t) /\ P x} =
        {x | x IN s /\ P x} DIFF {x | x IN t /\ P x}`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Insertion and deletion.                                                   *)
(* ------------------------------------------------------------------------- *)

let COMPONENT = prove
 (`!x:A. !s. x IN (x INSERT s)`,
  SET_TAC[]);;

let DECOMPOSITION = prove
 (`!s:A->bool. !x. x IN s <=> ?t. (s = x INSERT t) /\ ~(x IN t)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN EXISTS_TAC `s DELETE x:A` THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let SET_CASES = prove
 (`!s:A->bool. (s = EMPTY) \/ ?x:A. ?t. (s = x INSERT t) /\ ~(x IN t)`,
  MESON_TAC[MEMBER_NOT_EMPTY; DECOMPOSITION]);;

let ABSORPTION = prove
 (`!x:A. !s. x IN s <=> (x INSERT s = s)`,
  SET_TAC[]);;

let INSERT_INSERT = prove
 (`!x:A. !s. x INSERT (x INSERT s) = x INSERT s`,
  SET_TAC[]);;

let INSERT_COMM = prove
 (`!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)`,
  SET_TAC[]);;

let INSERT_UNIV = prove
 (`!x:A. x INSERT UNIV = UNIV`,
  SET_TAC[]);;

let NOT_INSERT_EMPTY = prove
 (`!x:A. !s. ~(x INSERT s = EMPTY)`,
  SET_TAC[]);;

let NOT_EMPTY_INSERT = prove
 (`!x:A. !s. ~(EMPTY = x INSERT s)`,
  SET_TAC[]);;

let INSERT_UNION = prove
 (`!x:A. !s t. (x INSERT s) UNION t =
               if x IN t then s UNION t else x INSERT (s UNION t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let INSERT_UNION_EQ = prove
 (`!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)`,
  SET_TAC[]);;

let INSERT_INTER = prove
 (`!x:A. !s t. (x INSERT s) INTER t =
               if x IN t then x INSERT (s INTER t) else s INTER t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let DISJOINT_INSERT = prove
 (`!(x:A) s t. DISJOINT (x INSERT s) t <=> (DISJOINT s t) /\ ~(x IN t)`,
  SET_TAC[]);;

let INSERT_SUBSET = prove
 (`!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\ s SUBSET t)`,
  SET_TAC[]);;

let SUBSET_INSERT = prove
 (`!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t`,
  SET_TAC[]);;

let INSERT_DIFF = prove
 (`!s t. !x:A. (x INSERT s) DIFF t =
               if x IN t then s DIFF t else x INSERT (s DIFF t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let INSERT_AC = prove
 (`(x:A) INSERT (y INSERT s) = y INSERT (x INSERT s) /\
   x INSERT (x INSERT s) = x INSERT s`,
  REWRITE_TAC[INSERT_COMM; INSERT_INSERT]);;

let INTER_ACI = prove
 (`((p:A->bool) INTER q = q INTER p) /\
   ((p INTER q) INTER r = p INTER q INTER r) /\
   (p INTER q INTER r = q INTER p INTER r) /\
   (p INTER p = p) /\
   (p INTER p INTER q = p INTER q)`,
  SET_TAC[]);;

let UNION_ACI = prove
 (`((p:A->bool) UNION q = q UNION p) /\
   ((p UNION q) UNION r = p UNION q UNION r) /\
   (p UNION q UNION r = q UNION p UNION r) /\
   (p UNION p = p) /\
   (p UNION p UNION q = p UNION q)`,
  SET_TAC[]);;

let DELETE_NON_ELEMENT = prove
 (`!x:A. !s. ~(x IN s) <=> (s DELETE x = s)`,
  SET_TAC[]);;

let IN_DELETE_EQ = prove
 (`!s x. !x':A.
     (x IN s <=> x' IN s) <=> (x IN (s DELETE x') <=> x' IN (s DELETE x))`,
  SET_TAC[]);;

let EMPTY_DELETE = prove
 (`!x:A. EMPTY DELETE x = EMPTY`,
  SET_TAC[]);;

let DELETE_DELETE = prove
 (`!x:A. !s. (s DELETE x) DELETE x = s DELETE x`,
  SET_TAC[]);;

let DELETE_COMM = prove
 (`!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x`,
  SET_TAC[]);;

let DELETE_SUBSET = prove
 (`!x:A. !s. (s DELETE x) SUBSET s`,
  SET_TAC[]);;

let SUBSET_DELETE = prove
 (`!x:A. !s t. s SUBSET (t DELETE x) <=> ~(x IN s) /\ (s SUBSET t)`,
  SET_TAC[]);;

let SUBSET_INSERT_DELETE = prove
 (`!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)`,
  SET_TAC[]);;

let DIFF_INSERT = prove
 (`!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t`,
  SET_TAC[]);;

let PSUBSET_INSERT_SUBSET = prove
 (`!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\ (x INSERT s) SUBSET t`,
  SET_TAC[]);;

let DELETE_INSERT = prove
 (`!x:A. !y s.
      (x INSERT s) DELETE y =
        if x = y then s DELETE y else x INSERT (s DELETE y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let INSERT_DELETE = prove
 (`!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)`,
  SET_TAC[]);;

let DELETE_INTER = prove
 (`!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x`,
  SET_TAC[]);;

let DISJOINT_DELETE_SYM = prove
 (`!s t. !x:A. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Multiple union.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNIONS_0 = prove
 (`UNIONS {}:A->bool = {}`,
  SET_TAC[]);;

let UNIONS_1 = prove
 (`!s:A->bool. UNIONS {s} = s`,
  SET_TAC[]);;

let UNIONS_2 = prove
 (`!s (t:A->bool). UNIONS {s,t} = s UNION t`,
  SET_TAC[]);;

let UNIONS_INSERT = prove
 (`!(s:A->bool) u. UNIONS (s INSERT u) = s UNION (UNIONS u)`,
  SET_TAC[]);;

let FORALL_IN_UNIONS = prove
 (`!P s. (!x:A. x IN UNIONS s ==> P x) <=> !t x. t IN s /\ x IN t ==> P x`,
  SET_TAC[]);;

let EXISTS_IN_UNIONS = prove
 (`!P s. (?x:A. x IN UNIONS s /\ P x) <=> (?t x. t IN s /\ x IN t /\ P x)`,
  SET_TAC[]);;

let EMPTY_UNIONS = prove
 (`!s. (UNIONS s = {}) <=> !t:A->bool. t IN s ==> t = {}`,
  SET_TAC[]);;

let INTER_UNIONS = prove
 (`(!s (t:A->bool). UNIONS s INTER t = UNIONS {x INTER t | x IN s}) /\
   (!s (t:A->bool). t INTER UNIONS s = UNIONS {t INTER x | x IN s})`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
  MESON_TAC[IN_INTER]);;

let UNIONS_SUBSET = prove
 (`!f (t:A->bool). UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t`,
  SET_TAC[]);;

let SUBSET_UNIONS = prove
 (`!(f:(A->bool)->bool) g. f SUBSET g ==> UNIONS f SUBSET UNIONS g`,
  SET_TAC[]);;

let UNIONS_UNION = prove
 (`!s t:(A->bool)->bool. UNIONS(s UNION t) = (UNIONS s) UNION (UNIONS t)`,
  SET_TAC[]);;

let INTERS_UNION = prove
 (`!s t:(A->bool)->bool. INTERS (s UNION t) = INTERS s INTER INTERS t`,
  SET_TAC[]);;

let UNIONS_MONO = prove
 (`!s t:(A->bool)->bool.
    (!x. x IN s ==> ?y. y IN t /\ x SUBSET y) ==> UNIONS s SUBSET UNIONS t`,
  SET_TAC[]);;

let UNIONS_MONO_IMAGE = prove
 (`!(f:A->B->bool) g s.
        (!x. x IN s ==> f x SUBSET g x)
        ==> UNIONS(IMAGE f s) SUBSET UNIONS(IMAGE g s)`,
  SET_TAC[]);;

let UNIONS_UNIV = prove
 (`UNIONS (:A->bool) = (:A)`,
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV] THEN
  MESON_TAC[IN_SING]);;

let UNIONS_INSERT_EMPTY = prove
 (`!s:(A->bool)->bool. UNIONS({} INSERT s) = UNIONS s`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_INSERT] THEN MESON_TAC[NOT_IN_EMPTY]);;

let UNIONS_DELETE_EMPTY = prove
 (`!s:(A->bool)->bool. UNIONS(s DELETE {}) = UNIONS s`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN MESON_TAC[NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Multiple intersection.                                                    *)
(* ------------------------------------------------------------------------- *)

let INTERS_0 = prove
 (`INTERS {} = (:A)`,
  SET_TAC[]);;

let INTERS_1 = prove
 (`!s:A->bool. INTERS {s} = s`,
  SET_TAC[]);;

let INTERS_2 = prove
 (`!s (t:A->bool). INTERS {s,t} = s INTER t`,
  SET_TAC[]);;

let INTERS_INSERT = prove
 (`!(s:A->bool) u. INTERS (s INSERT u) = s INTER (INTERS u)`,
  SET_TAC[]);;

let SUBSET_INTERS = prove
 (`!(s:A->bool) f. s SUBSET INTERS f <=> (!t. t IN f ==> s SUBSET t)`,
  SET_TAC[]);;

let INTERS_SUBSET = prove
 (`!u s:A->bool.
    ~(u = {}) /\ (!t. t IN u ==> t SUBSET s) ==> INTERS u SUBSET s`,
  SET_TAC[]);;

let INTERS_SUBSET_STRONG = prove
 (`!u s:A->bool. (?t. t IN u /\ t SUBSET s) ==> INTERS u SUBSET s`,
  SET_TAC[]);;

let INTERS_ANTIMONO = prove
 (`!(f:(A->bool)->bool) g. g SUBSET f ==> INTERS f SUBSET INTERS g`,
  SET_TAC[]);;

let INTERS_EQ_UNIV = prove
 (`!f. INTERS f = (:A) <=> !s. s IN f ==> s = (:A)`,
  SET_TAC[]);;

let INTERS_ANTIMONO_GEN = prove
 (`!s (t:(A->bool)->bool).
        (!y. y IN t ==> ?x. x IN s /\ x SUBSET y)
        ==> INTERS s SUBSET INTERS t`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

let IMAGE_CLAUSES = prove
 (`(IMAGE (f:A->B) {} = {}) /\
   (IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s))`,
  REWRITE_TAC[IMAGE; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT; EXTENSION] THEN
  MESON_TAC[]);;

let IMAGE_UNION = prove
 (`!(f:A->B) s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION] THEN MESON_TAC[]);;

let IMAGE_ID = prove
 (`!s:A->bool. IMAGE (\x. x) s = s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; UNWIND_THM1]);;

let IMAGE_I = prove
 (`!s:A->bool. IMAGE I s = s`,
  REWRITE_TAC[I_DEF; IMAGE_ID]);;

let IMAGE_o = prove
 (`!(f:B->C) (g:A->B) s. IMAGE (f o g) s = IMAGE f (IMAGE g s)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN MESON_TAC[]);;

let IMAGE_SUBSET = prove
 (`!(f:A->B) s t. s SUBSET t ==> (IMAGE f s) SUBSET (IMAGE f t)`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

let IMAGE_INTER_INJ = prove
 (`!(f:A->B) s t.
        (!x y. f(x) = f(y) ==> x = y)
        ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN MESON_TAC[]);;

let IMAGE_DIFF_INJ = prove
 (`!f:A->B s t.
        (!x y. x IN s /\ y IN t /\ f x = f y ==> x = y)
        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`,
  SET_TAC[]);;

let IMAGE_DIFF_INJ_ALT = prove
 (`!f:A->B s t.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ t SUBSET s
        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`,
  SET_TAC[]);;

let IMAGE_DELETE_INJ = prove
 (`!f:A->B s a.
        (!x. x IN s /\ f x = f a ==> x = a)
        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a`,
  SET_TAC[]);;

let IMAGE_DELETE_INJ_ALT = prove
 (`!f:A->B s a.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ a IN s
        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a`,
  SET_TAC[]);;

let IMAGE_EQ_EMPTY = prove
 (`!(f:A->B) s. (IMAGE f s = {}) <=> (s = {})`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_IMAGE] THEN MESON_TAC[]);;

let FORALL_IN_IMAGE_2 = prove
 (`!(f:A->B) P s. (!x y. x IN IMAGE f s /\ y IN IMAGE f s ==> P x y) <=>
                 (!x y. x IN s /\ y IN s ==> P (f x) (f y))`,
  SET_TAC[]);;

let IMAGE_CONST = prove
 (`!(s:A->bool) (c:B). IMAGE (\x. c) s = if s = {} then {} else {c}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

let SIMPLE_IMAGE = prove
 (`!(f:A->B) s. {f x | x IN s} = IMAGE f s`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

let SIMPLE_IMAGE_GEN = prove
 (`!(f:A->B) P. {f x | P x} = IMAGE f {x | P x}`,
  SET_TAC[]);;

let IMAGE_UNIONS = prove
 (`!(f:A->B) s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)`,
  ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_IMAGE] THEN
  MESON_TAC[]);;

let FUN_IN_IMAGE = prove
 (`!(f:A->B) s x. x IN s ==> f(x) IN IMAGE f s`,
  SET_TAC[]);;

let SURJECTIVE_IMAGE_EQ = prove
 (`!(f:A->B) s t.
        (!y. y IN t ==> ?x. f x = y) /\ (!x. (f x) IN t <=> x IN s)
        ==> IMAGE f s = t`,
  SET_TAC[]);;

let IMAGE_EQ = prove
 (`!(f:A->B) g s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let EMPTY_GSPEC = prove
 (`{x:A | F} = {}`,
  SET_TAC[]);;

let UNIV_GSPEC = prove
 (`{x | T} = (:A)`,
  SET_TAC[]);;

let SING_GSPEC = prove
 (`(!a:A. {x | x = a} = {a}) /\
   (!a:A. {x | a = x} = {a})`,
  SET_TAC[]);;

let SING_ALT = prove
 (`!s:A->bool. (?x. s = {x}) <=> ?!x. x IN s`,
  SET_TAC[]);;

let IN_GSPEC = prove
 (`!s:A->bool. {x | x IN s} = s`,
  SET_TAC[]);;

let IN_ELIM_PAIR_THM = prove
 (`!(P:A->B->bool) a b. (a,b) IN {(x,y) | P x y} <=> P a b`,
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PAIR_EQ]);;

let IN_ELIM_TRIPLE_THM = prove
 (`(!(P:A->B->C->bool) a b c. (a,b,c) IN {(x,y,z) | P x y z} <=> P a b c) /\
   (!(P:A->B->C->bool) a b c. ((a,b),c) IN {((x,y),z) | P x y z} <=> P a b c)`,
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let IN_ELIM_QUAD_THM = prove
 (`(!(P:A->B->C->D->bool) a b c d.
        (a,b,c,d) IN {w,x,y,z | P w x y z} <=> P a b c d) /\
   (!(P:A->B->C->D->bool) a b c d.
        ((a,b),(c,d)) IN {(w,x),(y,z) | P w x y z} <=> P a b c d) /\
   (!(P:A->B->C->D->bool) a b c d.
        (((a,b),c),d) IN {(((w,x),y),z) | P w x y z} <=> P a b c d)`,
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

let SET_PAIR_THM = prove
 (`!(P:A#B->bool). {p | P p} = {(a,b) | P(a,b)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; IN_ELIM_PAIR_THM]);;

let SET_PROVE_CASES = prove
 (`!P:(A->bool)->bool.
       P {} /\ (!a s. ~(a IN s) ==> P(a INSERT s))
       ==> !s. P s`,
  MESON_TAC[SET_CASES]);;

let UNIONS_SINGS_GEN = prove
 (`!P:A->bool. UNIONS {{x} | P x} = {x | P x}`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

let UNIONS_SINGS = prove
 (`!s:A->bool. UNIONS {{x} | x IN s} = s`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

let IMAGE_INTERS = prove
 (`!(f:A->B) s.
        ~(s = {}) /\
        (!x y. x IN UNIONS s /\ y IN UNIONS s /\ f x = f y ==> x = y)
        ==> IMAGE f (INTERS s) = INTERS(IMAGE (IMAGE f) s)`,
  REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]);;

let DIFF_INTERS = prove
 (`!(u:A->bool) s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

let INTERS_UNIONS = prove
 (`!s. INTERS s = UNIV DIFF (UNIONS {(:A) DIFF t | t IN s})`,
  REWRITE_TAC[GSYM DIFF_INTERS] THEN SET_TAC[]);;

let UNIONS_INTERS = prove
 (`!s. UNIONS s = UNIV DIFF (INTERS {(:A) DIFF t | t IN s})`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_UNIV; IN_DIFF; INTERS_GSPEC; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let UNIONS_DIFF = prove
 (`!s t:A->bool. UNIONS s DIFF t = UNIONS {x DIFF t | x IN s}`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

let DIFF_UNIONS = prove
 (`!(u:A->bool) s. u DIFF UNIONS s = u INTER INTERS {u DIFF t | t IN s}`,
  REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[]);;

let DIFF_UNIONS_NONEMPTY = prove
 (`!(u:A->bool) s. ~(s = {}) ==> u DIFF UNIONS s = INTERS {u DIFF t | t IN s}`,
  REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[]);;

let INTERS_OVER_UNIONS = prove
 (`!f:A->(B->bool)->bool s.
        INTERS { UNIONS(f x) | x IN s} =
        UNIONS { INTERS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[SIMPLE_IMAGE; INTERS_IMAGE; UNIONS_IMAGE; UNIONS_GSPEC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `b:B` THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  MESON_TAC[]);;

let INTER_INTERS = prove
 (`(!f s:A->bool.
        s INTER INTERS f =
        if f = {} then s else INTERS {s INTER t | t IN f}) /\
   (!f s:A->bool.
        INTERS f INTER s =
        if f = {} then s else INTERS {t INTER s | t IN f})`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INTERS_0; INTER_UNIV; INTERS_GSPEC] THEN
  ASM SET_TAC[]);;

let UNIONS_OVER_INTERS = prove
 (`!f:A->(B->bool)->bool s.
        UNIONS { INTERS(f x) | x IN s} =
        INTERS { UNIONS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[SIMPLE_IMAGE; INTERS_IMAGE; UNIONS_IMAGE; INTERS_GSPEC] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  REWRITE_TAC[AND_FORALL_THM; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let UNIONS_EQ_INTERS = prove
 (`!f:(A->bool)->bool. UNIONS f = INTERS f <=> ?s. f = {s}`,
  REWRITE_TAC[SET_RULE
   `(?s. f = {s}) <=> ~(f = {}) /\ !s t. s IN f /\ t IN f ==> s = t`] THEN
  SET_TAC[]);;

let EXISTS_UNIQUE_UNIONS_INTERS = prove
 (`!P. (?!s:A->bool. P s) <=> UNIONS {s | P s} = INTERS {s | P s}`,
  REWRITE_TAC[UNIONS_EQ_INTERS] THEN SET_TAC[]);;

let IMAGE_INTERS_SUBSET = prove
 (`!(f:A->B) g. IMAGE f (INTERS g) SUBSET INTERS (IMAGE (IMAGE f) g)`,
  REWRITE_TAC[INTERS_IMAGE] THEN SET_TAC[]);;

let IMAGE_INTER_SUBSET = prove
 (`!(f:A->B) s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t`,
  SET_TAC[]);;

let IMAGE_INTER_SATURATED_GEN = prove
 (`!f:A->B s t u.
        {x | x IN u /\ f(x) IN IMAGE f s} SUBSET s /\ t SUBSET u \/
        {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t /\ s SUBSET u
        ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`,
  SET_TAC[]);;

let IMAGE_INTERS_SATURATED_GEN = prove
 (`!f:A->B g s u.
        ~(g = {}) /\
        (!t. t IN g ==> t SUBSET u) /\
        (!t. t IN g DELETE s ==> {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t)
        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)`,
  let lemma = prove
   (`~(g = {}) /\
     (!t. t IN g ==> t SUBSET u /\ {x | x IN u /\ f(x) IN IMAGE f t} SUBSET t)
     ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)`,
    ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[INTERS_IMAGE; IN_INTERS; IN_IMAGE] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_UNWIND_THM2] THEN SET_TAC[]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(s:A->bool) IN g` THEN
  ASM_SIMP_TAC[SET_RULE `~(s IN g) ==> g DELETE s = g`] THENL
   [ALL_TAC; MESON_TAC[lemma]] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_INSERT_EMPTY] THEN
  STRIP_TAC THEN ASM_CASES_TAC `g DELETE (s:A->bool) = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0; INTERS_1] THEN
  REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT] THEN
  MATCH_MP_TAC(SET_RULE
   `IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t /\
    IMAGE f t = u ==> IMAGE f (s INTER t) = IMAGE f s INTER u`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_INTER_SATURATED_GEN THEN
    EXISTS_TAC `u:A->bool` THEN ASM SET_TAC[];
    MATCH_MP_TAC lemma THEN ASM SET_TAC[]]);;

let IMAGE_INTER_SATURATED = prove
 (`!f:A->B s t.
        {x | f(x) IN IMAGE f s} SUBSET s \/ {x | f(x) IN IMAGE f t} SUBSET t
         ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t`,
  SET_TAC[]);;

let IMAGE_INTERS_SATURATED = prove
 (`!f:A->B g s.
        ~(g = {}) /\ (!t. t IN g DELETE s ==> {x | f(x) IN IMAGE f t} SUBSET t)
        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_INTERS_SATURATED_GEN THEN
  MAP_EVERY EXISTS_TAC [`s:A->bool`; `(:A)`] THEN
  ASM_REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Stronger form of induction is sometimes handy.                            *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_STRONG = prove
 (`!P:(A->bool)->bool.
        P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
        ==> !s. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:A->bool. FINITE s ==> FINITE s /\ P s` MP_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN ASM_SIMP_TAC[FINITE_RULES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `x:A IN s` THENL
   [SUBGOAL_THEN `x:A INSERT s = s` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `x:A IN s` THEN SET_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Useful general properties of functions.                                   *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_ON_ALT = prove
 (`!P f:A->B.
        (!x y. P x /\ P y /\ f x = f y ==> x = y) <=>
        (!x y. P x /\ P y ==> (f x = f y <=> x = y))`,
  MESON_TAC[]);;

let INJECTIVE_ALT = prove
 (`!f:A->B. (!x y. f x = f y ==> x = y) <=> (!x y. f x = f y <=> x = y)`,
  MESON_TAC[]);;

let SURJECTIVE_ON_RIGHT_INVERSE = prove
 (`!(f:A->B) t.
        (!y. y IN t ==> ?x. x IN s /\ (f(x) = y)) <=>
        (?g. !y. y IN t ==> g(y) IN s /\ (f(g(y)) = y))`,
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]);;

let INJECTIVE_ON_LEFT_INVERSE = prove
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) <=>
         (?g. !x. x IN s ==> (g(f(x)) = x))`,
  let lemma = MESON[]
   `(!x. x IN s ==> (g(f(x)) = x)) <=>
    (!y x. x IN s /\ (y = (f:A->B) x) ==> (g y = x))` in
  REWRITE_TAC[lemma; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let BIJECTIVE_ON_LEFT_RIGHT_INVERSE = prove
 (`!(f:A->B) s t.
        (!x. x IN s ==> f(x) IN t)
        ==> ((!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
             (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
            ?g. (!y. y IN t ==> g(y) IN s) /\
                (!y. y IN t ==> (f(g(y)) = y)) /\
                (!x. x IN s ==> (g(f(x)) = x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  EQ_TAC THEN ASM_MESON_TAC[]);;

let SURJECTIVE_RIGHT_INVERSE = prove
 (`!f:A->B. (!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)`,
  MESON_TAC[SURJECTIVE_ON_RIGHT_INVERSE; IN_UNIV]);;

let INJECTIVE_LEFT_INVERSE = prove
 (`!f:A->B. (!x y. f x = f y ==> x = y) <=> (?g. !x. g(f(x)) = x)`,
  let th = REWRITE_RULE[IN_UNIV]
   (ISPECL [`f:A->B`; `UNIV:A->bool`] INJECTIVE_ON_LEFT_INVERSE) in
  REWRITE_TAC[th]);;

let BIJECTIVE_LEFT_RIGHT_INVERSE = prove
 (`!f:A->B.
       (!x y. f(x) = f(y) ==> x = y) /\ (!y. ?x. f x = y) <=>
       ?g. (!y. f(g(y)) = y) /\ (!x. g(f(x)) = x)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`] BIJECTIVE_ON_LEFT_RIGHT_INVERSE) THEN
  REWRITE_TAC[IN_UNIV]);;

let FUNCTION_FACTORS_LEFT_GEN = prove
 (`!P (f:A->B) (g:A->C).
        (!x y. P x /\ P y /\ g x = g y ==> f x = f y) <=>
        (?h. !x. P x ==> f(x) = h(g x))`,
  ONCE_REWRITE_TAC[MESON[]
   `(!x. P x ==> f(x) = g(k x)) <=> (!y x. P x /\ y = k x ==> f x = g y)`] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let FUNCTION_FACTORS_LEFT = prove
 (`!(f:A->B) (g:A->C). (!x y. g x = g y ==> f x = f y) <=> ?h. f = h o g`,
  REWRITE_TAC[FUN_EQ_THM; o_THM;
   GSYM(REWRITE_RULE[] (ISPEC `\x. T` FUNCTION_FACTORS_LEFT_GEN))]);;

let FUNCTION_FACTORS_RIGHT_GEN = prove
 (`!P (f:A->C) (g:B->C).
        (!x. P x ==> ?y. g(y) = f(x)) <=>
        (?h. !x. P x ==> f(x) = g(h x))`,
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let FUNCTION_FACTORS_RIGHT = prove
 (`!(f:A->C) (g:B->C). (!x. ?y. g(y) = f(x)) <=> ?h. f = g o h`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let SURJECTIVE_FORALL_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. (!x. P(f x)) <=> (!y. P y))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN MESON_TAC[]);;

let SURJECTIVE_EXISTS_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. (?x. P(f x)) <=> (?y. P y))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:B. !x:A. ~(f x = y)`) THEN MESON_TAC[]);;

let SURJECTIVE_IMAGE_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `\y:B. T`)] THEN
  MESON_TAC[]);;

let IMAGE_INJECTIVE_IMAGE_OF_SUBSET = prove
 (`!f:A->B s.
     ?t. t SUBSET s /\
         IMAGE f s = IMAGE f t /\
         (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `?g. !y. y IN IMAGE (f:A->B) s ==> g(y) IN s /\ f(g(y)) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SURJECTIVE_ON_RIGHT_INVERSE] THEN SET_TAC[];
    EXISTS_TAC `IMAGE (g:B->A) (IMAGE (f:A->B) s)` THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for finite sets.                                 *)
(* ------------------------------------------------------------------------- *)

let FINITE_EMPTY = prove
 (`FINITE ({}:A->bool)`,
  REWRITE_TAC[FINITE_RULES]);;

let FINITE_SUBSET = prove
 (`!(s:A->bool) t. FINITE t /\ s SUBSET t ==> FINITE s`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [MESON_TAC[SUBSET_EMPTY; FINITE_RULES]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE((x:A) INSERT (t DELETE x))` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `t SUBSET (x:A INSERT u)` THEN SET_TAC[];
    ASM_CASES_TAC `x:A IN t` THENL
     [SUBGOAL_THEN `x:A INSERT (t DELETE x) = t` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `x:A IN t` THEN SET_TAC[]; ASM_REWRITE_TAC[]];
      FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `t SUBSET x:A INSERT u` THEN
      UNDISCH_TAC `~(x:A IN t)` THEN SET_TAC[]]]);;

let FINITE_RESTRICT = prove
 (`!s:A->bool P. FINITE s ==> FINITE {x | x IN s /\ P x}`,
  MESON_TAC[SUBSET_RESTRICT; FINITE_SUBSET]);;

let FINITE_UNION_IMP = prove
 (`!(s:A->bool) t. FINITE s /\ FINITE t ==> FINITE (s UNION t)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[UNION_EMPTY] THEN
  SUBGOAL_THEN `!x s t. (x:A INSERT s) UNION t = x INSERT (s UNION t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [SET_TAC[];
    MESON_TAC[FINITE_RULES]]);;

let FINITE_UNION = prove
 (`!(s:A->bool) t. FINITE(s UNION t) <=> FINITE(s) /\ FINITE(t)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(s:A->bool) UNION t` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_ACCEPT_TAC FINITE_UNION_IMP]);;

let FINITE_INTER = prove
 (`!(s:A->bool) t. FINITE s \/ FINITE t ==> FINITE (s INTER t)`,
  MESON_TAC[INTER_SUBSET; FINITE_SUBSET]);;

let FINITE_INSERT = prove
 (`!(s:A->bool) x. FINITE (x INSERT s) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `x:A INSERT s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN
    ASM_REWRITE_TAC[]]);;

let FINITE_SING = prove
 (`!a:A. FINITE {a}`,
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

let FINITE_DELETE_IMP = prove
 (`!(s:A->bool) x. FINITE s ==> FINITE (s DELETE x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let FINITE_DELETE = prove
 (`!(s:A->bool) x. FINITE (s DELETE x) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FINITE_DELETE_IMP] THEN
  ASM_CASES_TAC `x:A IN s` THENL
   [SUBGOAL_THEN `s = x INSERT (s DELETE x:A)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[FINITE_INSERT] THEN POP_ASSUM MP_TAC THEN SET_TAC[];
    SUBGOAL_THEN `s DELETE x:A = s` (fun th -> REWRITE_TAC[th]) THEN
    POP_ASSUM MP_TAC THEN SET_TAC[]]);;

let FINITE_FINITE_UNIONS = prove
 (`!s:(A->bool)->bool.
        FINITE(s) ==> (FINITE(UNIONS s) <=> (!t. t IN s ==> FINITE(t)))`,
  MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; UNIONS_0; UNIONS_INSERT] THEN
  REWRITE_TAC[FINITE_UNION; FINITE_RULES] THEN MESON_TAC[]);;

let FINITE_IMAGE_EXPAND = prove
 (`!(f:A->B) s. FINITE s ==> FINITE {y | ?x. x IN s /\ (y = f x)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[NOT_IN_EMPTY; REWRITE_RULE[] EMPTY_GSPEC; FINITE_RULES] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y | ?z. z IN (x INSERT s) /\ (y = (f:A->B) z)} =
                {y | ?z. z IN s /\ (y = f z)} UNION {(f x)}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    REWRITE_TAC[FINITE_UNION; FINITE_INSERT; FINITE_RULES]]);;

let FINITE_IMAGE = prove
 (`!(f:A->B) s. FINITE s ==> FINITE (IMAGE f s)`,
  REWRITE_TAC[IMAGE; FINITE_IMAGE_EXPAND]);;

let FINITE_IMAGE_INJ_GENERAL = prove
 (`!(f:A->B) A s.
        (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
        FINITE A
        ==> FINITE {x | x IN s /\ f(x) IN A}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `IMAGE (g:B->A) A` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN ASM SET_TAC[]);;

let FINITE_FINITE_PREIMAGE_GENERAL = prove
 (`!f:A->B s t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | x IN s /\ f(x) = y})
        ==> FINITE {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ (f:A->B)(x) IN t} =
    UNIONS (IMAGE (\a. {x | x IN s /\ f x = a}) t)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN SET_TAC[];
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE]]);;

let FINITE_FINITE_PREIMAGE = prove
 (`!f:A->B t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | f(x) = y})
        ==> FINITE {x | f(x) IN t}`,
  REPEAT GEN_TAC THEN MP_TAC
   (ISPECL [`f:A->B`; `(:A)`; `t:B->bool`] FINITE_FINITE_PREIMAGE_GENERAL) THEN
  REWRITE_TAC[IN_UNIV]);;

let FINITE_IMAGE_INJ_EQ = prove
 (`!(f:A->B) s.
        (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y)
        ==> (FINITE(IMAGE f s) <=> FINITE s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMAGE_INJ_GENERAL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

let FINITE_IMAGE_INJ = prove
 (`!(f:A->B) A.
        (!x y. f(x) = f(y) ==> x = y) /\ FINITE A
        ==> FINITE {x | f(x) IN A}`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`f:A->B`; `A:B->bool`; `UNIV:A->bool`]
    FINITE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC[IN_UNIV]);;

let FINITE_IMAGE_GEN = prove
 (`!(f:A->B) (g:A->C) s t.
        IMAGE f s SUBSET t /\ FINITE t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> g x = g y)
        ==> FINITE(IMAGE g s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUNCTION_FACTORS_LEFT_GEN]) THEN
  DISCH_THEN(X_CHOOSE_TAC `h:B->C`) THEN
  SUBGOAL_THEN `IMAGE g s = IMAGE (h:B->C) (IMAGE (f:A->B) s)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET]]);;

let INFINITE_IMAGE = prove
 (`!f:A->B s.
        INFINITE s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> INFINITE (IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ_ALT; INJECTIVE_ON_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `s = IMAGE (g:B->A) (IMAGE f s)` SUBST1_TAC THENL
   [ASM SET_TAC[]; MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]]);;

let INFINITE_IMAGE_INJ = prove
 (`!f:A->B. (!x y. (f x = f y) ==> (x = y))
            ==> !s. INFINITE s ==> INFINITE(IMAGE f s)`,
  MESON_TAC[INFINITE_IMAGE]);;

let INFINITE_NONEMPTY = prove
 (`!s:A->bool. INFINITE(s) ==> ~(s = EMPTY)`,
  MESON_TAC[INFINITE; FINITE_RULES]);;

let INFINITE_DIFF_FINITE = prove
 (`!s:A->bool t. INFINITE(s) /\ FINITE(t) ==> INFINITE(s DIFF t)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(b /\ ~c ==> ~a) ==> a /\ b ==> c`) THEN
  REWRITE_TAC[INFINITE] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(t:A->bool) UNION (s DIFF t)` THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN SET_TAC[]);;

let SUBSET_IMAGE_INJ = prove
 (`!f:A->B s t.
        s SUBSET (IMAGE f t) <=>
        ?u. u SUBSET t /\
            (!x y. x IN u /\ y IN u ==> (f x = f y <=> x = y)) /\
            s = IMAGE f u`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[IMAGE_SUBSET]] THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `s SUBSET IMAGE f t ==> !x. x IN s ==> ?y. y IN t /\ f y = x`)) THEN
  REWRITE_TAC[SURJECTIVE_ON_RIGHT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN
  EXISTS_TAC `IMAGE (g:B->A) s` THEN ASM SET_TAC[]);;

let SUBSET_IMAGE = prove
 (`!f:A->B s t. s SUBSET (IMAGE f t) <=> ?u. u SUBSET t /\ (s = IMAGE f u)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[IMAGE_SUBSET]] THEN
  REWRITE_TAC[SUBSET_IMAGE_INJ] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

let EXISTS_SUBSET_IMAGE = prove
 (`!P (f:A->B) s.
    (?t. t SUBSET IMAGE f s /\ P t) <=> (?t. t SUBSET s /\ P (IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]);;

let FORALL_SUBSET_IMAGE = prove
 (`!P (f:A->B) s.
        (!t. t SUBSET IMAGE f s ==> P t) <=>
        (!t. t SUBSET s ==> P(IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]);;

let EXISTS_SUBSET_IMAGE_INJ = prove
 (`!P (f:A->B) s.
    (?t. t SUBSET IMAGE f s /\ P t) <=>
    (?t. t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE_INJ] THEN MESON_TAC[]);;

let FORALL_SUBSET_IMAGE_INJ = prove
 (`!P (f:A->B) s.
        (!t. t SUBSET IMAGE f s ==> P t) <=>
        (!t. t SUBSET s /\
             (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
             ==> P(IMAGE f t))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!t. p t) <=> ~(?t. ~p t)`] THEN
  REWRITE_TAC[NOT_IMP; EXISTS_SUBSET_IMAGE_INJ; GSYM CONJ_ASSOC]);;

let EXISTS_FINITE_SUBSET_IMAGE_INJ = prove
 (`!P (f:A->B) s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))`,
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[EXISTS_SUBSET_IMAGE_INJ] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MESON_TAC[FINITE_IMAGE_INJ_EQ]);;

let FORALL_FINITE_SUBSET_IMAGE_INJ = prove
 (`!P (f:A->B) s.
        (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
        (!t. FINITE t /\ t SUBSET s /\
             (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
             ==> P(IMAGE f t))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!t. p t) <=> ~(?t. ~p t)`] THEN
  REWRITE_TAC[NOT_IMP; EXISTS_FINITE_SUBSET_IMAGE_INJ; GSYM CONJ_ASSOC]);;

let EXISTS_FINITE_SUBSET_IMAGE = prove
 (`!P (f:A->B) s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE_INJ] THEN MESON_TAC[];
    MESON_TAC[FINITE_IMAGE; IMAGE_SUBSET]]);;

let FORALL_FINITE_SUBSET_IMAGE = prove
 (`!P (f:A->B) s.
        (!t. FINITE t /\ t SUBSET IMAGE f s ==> P t) <=>
        (!t. FINITE t /\ t SUBSET s ==> P(IMAGE f t))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!x. P x) <=> ~(?x. ~P x)`] THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; EXISTS_FINITE_SUBSET_IMAGE]);;

let FINITE_SUBSET_IMAGE = prove
 (`!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[FINITE_IMAGE; IMAGE_SUBSET]] THEN
  SPEC_TAC(`t:B->bool`,`t:B->bool`) THEN
  REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN MESON_TAC[]);;

let FINITE_SUBSET_IMAGE_IMP = prove
 (`!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s)
        ==> ?s'. FINITE s' /\ s' SUBSET s /\ t SUBSET (IMAGE f s')`,
  MESON_TAC[SUBSET_REFL; FINITE_SUBSET_IMAGE]);;

let FINITE_IMAGE_EQ = prove
 (`!(f:A->B) s. FINITE(IMAGE f s) <=>
                ?t. FINITE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t`,
  MESON_TAC[FINITE_SUBSET_IMAGE; FINITE_IMAGE; SUBSET_REFL]);;

let FINITE_IMAGE_EQ_INJ = prove
 (`!(f:A->B) s. FINITE(IMAGE f s) <=>
                ?t. FINITE t /\ t SUBSET s /\ IMAGE f s = IMAGE f t /\
                    (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[FINITE_IMAGE]] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `IMAGE (f:A->B) s`; `s:A->bool`]
        SUBSET_IMAGE_INJ) THEN
  REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_METIS_TAC[FINITE_IMAGE_INJ_EQ]);;

let FINITE_DIFF = prove
 (`!s t:A->bool. FINITE s ==> FINITE(s DIFF t)`,
  MESON_TAC[FINITE_SUBSET; SUBSET_DIFF]);;

let INFINITE_SUPERSET = prove
 (`!s t:A->bool. INFINITE s /\ s SUBSET t ==> INFINITE t`,
  REWRITE_TAC[INFINITE] THEN MESON_TAC[FINITE_SUBSET]);;

let FINITE_TRANSITIVITY_CHAIN = prove
 (`!R s:A->bool.
        FINITE s /\
        (!x. ~(R x x)) /\
        (!x y z. R x y /\ R y z ==> R x z) /\
        (!x. x IN s ==> ?y. y IN s /\ R x y)
        ==> s = {}`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
  SET_TAC[]);;

let UNIONS_MAXIMAL_SETS = prove
 (`!f. FINITE f
       ==> UNIONS {t:A->bool | t IN f /\ !u. u IN f ==> ~(t PSUBSET u)} =
           UNIONS f`,
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_UNIONS; SUBSET_RESTRICT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC UNIONS_MONO THEN
  X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_IN_GSPEC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~ p`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t u:A->bool. s SUBSET t /\ t PSUBSET u`;
    `{t:A->bool | t IN f /\ s SUBSET t}`]FINITE_TRANSITIVITY_CHAIN) THEN
  ASM_SIMP_TAC[NOT_IMP; FINITE_RESTRICT; FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
  REPEAT CONJ_TAC THENL [SET_TAC[]; SET_TAC[]; ALL_TAC; ASM SET_TAC[]] THEN
  ASM_MESON_TAC[PSUBSET_TRANS; SUBSET_PSUBSET_TRANS; PSUBSET]);;

let FINITE_SUBSET_UNIONS = prove
 (`!f s:A->bool.
        FINITE s /\ s SUBSET UNIONS f
        ==> ?f'. FINITE f' /\ f' SUBSET f /\ s SUBSET UNIONS f'`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [IN_UNIONS; RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:A->A->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE (u:A->A->bool) s` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; UNIONS_IMAGE] THEN ASM SET_TAC[]);;

let UNIONS_IN_CHAIN = prove
 (`!f:(A->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> UNIONS f IN f`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT; UNIONS_INSERT] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`;
              NOT_INSERT_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; IN_INSERT; UNION_EMPTY] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `s UNION t = s \/ s UNION t = t
    ==> t IN f ==> s UNION t = s \/ s UNION t IN f`) THEN
  ASM SET_TAC[]);;

let INTERS_IN_CHAIN = prove
 (`!f:(A->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)
        ==> INTERS f IN f`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT; INTERS_INSERT] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`;
              NOT_INSERT_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; IN_INSERT; INTER_UNIV] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `s INTER t = s \/ s INTER t = t
    ==> t IN f ==> s INTER t = s \/ s INTER t IN f`) THEN
  ASM SET_TAC[]);;

let FINITE_SUBSET_UNIONS_DIRECTED_EQ = prove
 (`!f s:A->bool.
        ~(f = {}) /\
        (!t u. t IN f /\ u IN f
               ==> ?v. v IN f /\ t SUBSET v /\ u SUBSET v) /\
        FINITE s
        ==> (s SUBSET UNIONS f <=> ?t. t IN f /\ s SUBSET t)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[INSERT_SUBSET] THEN ASM SET_TAC[]);;

let FINITE_SUBSET_UNIONS_CHAIN_EQ = time prove
 (`!f s:A->bool.
        ~(f = {}) /\
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t) /\
        FINITE s
        ==> (s SUBSET UNIONS f <=> ?t. t IN f /\ s SUBSET t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET_UNIONS_DIRECTED_EQ THEN
  ASM_MESON_TAC[SUBSET_REFL]);;

let FINITE_SUBSET_UNIONS_CHAIN = prove
 (`!f s:A->bool.
        FINITE s /\ s SUBSET UNIONS f /\ ~(f = {}) /\
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t)
        ==> ?t. t IN f /\ s SUBSET t`,
  MESON_TAC[FINITE_SUBSET_UNIONS_CHAIN_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

let FINREC = new_recursive_definition num_RECURSION
  `(FINREC (f:A->B->B) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (FINREC (f:A->B->B) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n  /\
                      (a = f x c))`;;

let FINREC_1_LEMMA = prove
 (`!(f:A->B->B) b s a. FINREC f b s a (SUC 0) <=> ?x. s = {x} /\ a = f x b`,
  REWRITE_TAC[FINREC] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN SET_TAC[]);;

let FINREC_SUC_LEMMA = prove
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n s z.
                FINREC f b s z (SUC n)
                ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                       (z = f x w)`,
  let lem = prove(`s DELETE (x:A) DELETE y = s DELETE y DELETE x`,SET_TAC[]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FINREC_1_LEMMA] THEN REWRITE_TAC[FINREC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `b:B` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [FINREC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `c:B` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `FINREC (f:A->B->B) b (s DELETE y) c (SUC n)` THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:B` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(f:A->B->B) y v` THEN ASM_REWRITE_TAC[FINREC] THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`y:A`; `v:B`] THEN
        ONCE_REWRITE_TAC[lem] THEN ASM_REWRITE_TAC[IN_DELETE];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

let FINREC_UNIQUE_LEMMA = prove
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n1 n2 s a1 a2.
                FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                ==> (a1 = a2) /\ (n1 = n2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
    REWRITE_TAC[FINREC] THEN STRIP_TAC THEN ASM_MESON_TAC[]]);;

let FINREC_EXISTS_LEMMA = prove
 (`!(f:A->B->B) b s. FINITE s ==> ?a n. FINREC f b s a n`,
  let lem = prove(`~(x IN s ) ==> ((x:A INSERT s) DELETE x = s)`,SET_TAC[]) in
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:B`; `0`] THEN REWRITE_TAC[FINREC];
    MAP_EVERY EXISTS_TAC [`(f:A->B->B) x a`; `SUC n`] THEN
    REWRITE_TAC[FINREC] THEN MAP_EVERY EXISTS_TAC [`x:A`; `a:B`] THEN
    FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP lem th; IN_INSERT])]);;

let FINREC_FUN_LEMMA = prove
 (`!P (R:A->B->C->bool).
       (!s. P s ==> ?a n. R s a n) /\
       (!n1 n2 s a1 a2. R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2))
       ==> ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `\s:A. @a:B. ?n:C. R s a n` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN
    ASM_MESON_TAC[]]);;

let FINREC_FUN = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !s x. FINITE s /\ x IN s
                      ==> (g s = f x (g (s DELETE x)))`,
  REPEAT STRIP_TAC THEN IMP_RES_THEN MP_TAC FINREC_UNIQUE_LEMMA THEN
  DISCH_THEN(MP_TAC o SPEC `b:B`) THEN DISCH_THEN
   (MP_TAC o CONJ (SPECL [`f:A->B->B`; `b:B`] FINREC_EXISTS_LEMMA)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINREC_FUN_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:(A->bool)->B`) THEN
  EXISTS_TAC `g:(A->bool)->B` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `FINITE(EMPTY:A->bool)`
    (ANTE_RES_THEN (fun th -> GEN_REWRITE_TAC I [GSYM th])) THENL
     [REWRITE_TAC[FINITE_RULES];
      EXISTS_TAC `0` THEN REWRITE_TAC[FINREC]];
    REPEAT STRIP_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME `FINITE(s:A->bool)`) THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(g:(A->bool)->B) s`) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    INDUCT_TAC THENL
     [ASM_REWRITE_TAC[FINREC] THEN DISCH_TAC THEN UNDISCH_TAC `x:A IN s` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY];
      IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:B` (CONJUNCTS_THEN ASSUME_TAC)) THEN
      SUBGOAL_THEN `(g (s DELETE x:A) = w:B)` SUBST1_TAC THENL
       [SUBGOAL_THEN `FINITE(s DELETE x:A)` MP_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          DISCH_THEN(ANTE_RES_THEN (MP_TAC o GSYM)) THEN
          DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
          EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]]]]);;

let SET_RECURSION_LEMMA = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `b:B` o MATCH_MP FINREC_FUN) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:(A->bool)->B` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM ABSORPTION] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `FINITE(x:A INSERT s) /\ x IN (x INSERT s)` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[FINITE_RULES];
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN
      REPEAT AP_TERM_TAC THEN UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]]);;

let ITSET = new_definition
  `ITSET (f:A->B->B) s b =
        (@g. (g {} = b) /\
             !x s. FINITE s
                   ==> (g (x INSERT s) = if x IN s then g s else f x (g s)))
        s`;;

let FINITE_RECURSION = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f (x INSERT s) b =
                       if x IN s then ITSET f s b
                                 else f x (ITSET f s b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ITSET] THEN
  CONV_TAC SELECT_CONV THEN MATCH_MP_TAC SET_RECURSION_LEMMA THEN
  ASM_REWRITE_TAC[]);;

let FINITE_RECURSION_DELETE = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f s b =
                       if x IN s then f x (ITSET f (s DELETE x) b)
                                 else ITSET f (s DELETE x) b)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FINITE_RECURSION) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o SPEC `b:B`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:A IN s` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o MATCH_MP FINITE_DELETE_IMP) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC o SPEC `x:A`) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    REWRITE_TAC[IN_DELETE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `x:A IN s` THEN SET_TAC[];
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]);;

let ITSET_EQ = prove
 (`!s (f:A->B->B) g b.
        FINITE(s) /\ (!x. x IN s ==> (f x = g x)) /\
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\
        (!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s)))
        ==> (ITSET f s b = ITSET g s b)`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FINITE_RECURSION; NOT_IN_EMPTY; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality.                                                              *)
(* ------------------------------------------------------------------------- *)

let CARD = new_definition
 `CARD (s:A->bool) = ITSET (\x n. SUC n) s 0`;;

let CARD_CLAUSES = prove
 (`(CARD ({}:A->bool) = 0) /\
   (!(x:A) s. FINITE s ==>
                 (CARD (x INSERT s) =
                      if x IN s then CARD s else SUC(CARD s)))`,
  MP_TAC(ISPECL [`\(x:A) n. SUC n`; `0`] FINITE_RECURSION) THEN
  REWRITE_TAC[CARD]);;

let CARD_UNION = prove
 (`!(s:A->bool) t. FINITE(s) /\ FINITE(t) /\ (s INTER t = EMPTY)
         ==> (CARD (s UNION t) = CARD s + CARD t)`,
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> b /\ c ==> d`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNION_EMPTY; CARD_CLAUSES; INTER_EMPTY; ADD_CLAUSES] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `s:A->bool` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A INSERT s) UNION t = x INSERT (s UNION t)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE ((s:A->bool) UNION t) /\ FINITE s`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_UNION_IMP THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:A`; `s:A->bool`] (CONJUNCT2 CARD_CLAUSES)) THEN
  MP_TAC(ISPECL [`x:A`; `s:A->bool UNION t`] (CONJUNCT2 CARD_CLAUSES)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x:A IN (s UNION t))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN
    UNDISCH_TAC `(x:A INSERT s) INTER t = EMPTY` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[SUC_INJ; ADD_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x:A INSERT s INTER t = EMPTY` THEN SET_TAC[]]);;

let CARD_DELETE = prove
 (`!x:A s. FINITE(s)
           ==> (CARD(s DELETE x) = if x IN s then CARD(s) - 1 else CARD(s))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `s = x:A INSERT (s DELETE x)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL [UNDISCH_TAC `x:A IN s` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; IN_DELETE; SUC_SUB1];
    AP_TERM_TAC THEN UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]);;

let CARD_UNION_EQ = prove
 (`!s t u:A->bool.
        FINITE u /\ s INTER t = {} /\ s UNION t = u
        ==> (CARD s + CARD t = CARD u)`,
  MESON_TAC[CARD_UNION; FINITE_SUBSET; SUBSET_UNION]);;

let CARD_DIFF = prove
 (`!s t:A->bool. FINITE s /\ t SUBSET s ==> CARD(s DIFF t) = CARD s - CARD t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a + b:num = c ==> a = c - b`) THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let CARD_EQ_0 = prove
 (`!s:A->bool. FINITE s ==> ((CARD s = 0) <=> (s = {}))`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES; NOT_INSERT_EMPTY; NOT_SUC]);;

let CARD_SING = prove
 (`!a:A. CARD {a} = 1`,
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; NOT_IN_EMPTY; ARITH]);;

let CARD_LE_2 = prove
 (`!a (b:A). CARD{a,b} <= 2`,
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT(GEN_TAC ORELSE COND_CASES_TAC) THEN ARITH_TAC);;

let CARD_LE_3 = prove
 (`!a b (c:A). CARD{a,b,c} <= 3`,
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT(GEN_TAC ORELSE COND_CASES_TAC) THEN ARITH_TAC);;

let CARD_LE_4 = prove
 (`!a b c (d:A). CARD{a,b,c,d} <= 4`,
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT(GEN_TAC ORELSE COND_CASES_TAC) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A stronger still form of induction where we get to choose the element.    *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_DELETE = prove
 (`!P. P {} /\
       (!s. FINITE s /\ ~(s = {}) ==> ?x. x IN s /\ (P(s DELETE x) ==> P s))
       ==> !s:A->bool. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `CARD(s:A->bool)` THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!s. FINITE s /\ ~(s = {}) ==> ?x:A. x IN s /\ (P(s DELETE x) ==> P s)` THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (x:A)`) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; CARD_EQ_0;
               ARITH_RULE `n - 1 < n <=> ~(n = 0)`]);;

(* ------------------------------------------------------------------------- *)
(* Relational form is often more useful.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE = new_definition
  `(s:A->bool) HAS_SIZE n <=> FINITE s /\ CARD s = n`;;

let HAS_SIZE_CARD = prove
 (`!(s:A->bool) n. s HAS_SIZE n ==> CARD s = n`,
  SIMP_TAC[HAS_SIZE]);;

let HAS_SIZE_0 = prove
 (`!(s:A->bool). s HAS_SIZE 0 <=> (s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[FINITE_RULES; CARD_CLAUSES] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
  ASM_REWRITE_TAC[NOT_SUC]);;

let HAS_SIZE_SUC = prove
 (`!(s:A->bool) n. s HAS_SIZE (SUC n) <=>
                   ~(s = {}) /\ !a. a IN s ==> (s DELETE a) HAS_SIZE n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; NOT_SUC] THEN
  REWRITE_TAC[FINITE_DELETE] THEN
  ASM_CASES_TAC `FINITE(s:A->bool)` THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; MEMBER_NOT_EMPTY] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`a:A`; `s DELETE a:A`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:A) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:A IN s` THEN SET_TAC[];
      ASM_REWRITE_TAC[SUC_INJ] THEN MESON_TAC[]];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    MP_TAC(ISPECL [`a:A`; `s DELETE a:A`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:A) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:A IN s` THEN SET_TAC[];
      ASM_MESON_TAC[]]]);;

let HAS_SIZE_UNION = prove
 (`!(s:A->bool) t m n.
        s HAS_SIZE m /\ t HAS_SIZE n /\ DISJOINT s t
        ==> (s UNION t) HAS_SIZE (m + n)`,
  SIMP_TAC[HAS_SIZE; FINITE_UNION; DISJOINT; CARD_UNION]);;

let HAS_SIZE_DIFF = prove
 (`!(s:A->bool) t m n.
        s HAS_SIZE m /\ t HAS_SIZE n /\ t SUBSET s
        ==> (s DIFF t) HAS_SIZE (m - n)`,
  SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF]);;

let HAS_SIZE_UNIONS = prove
 (`!s t:A->B->bool m n.
        s HAS_SIZE m /\
        (!x. x IN s ==> t(x) HAS_SIZE n) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (t x) (t y))
        ==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CARD_CLAUSES] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0; EMPTY_UNIONS] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:A->B->bool`; `m:num`; `n:num`] THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE
   `UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}`] THEN
  REWRITE_TAC[ARITH_RULE `SUC a * b = b + a * b`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN ASM_SIMP_TAC[IN_INSERT] THEN
  REWRITE_TAC[SET_RULE
   `DISJOINT a (UNIONS s) <=> !x. x IN s ==> DISJOINT a x`] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  ASM_MESON_TAC[IN_INSERT]);;

let FINITE_HAS_SIZE = prove
 (`!s:A->bool. FINITE s <=> s HAS_SIZE CARD s`,
  REWRITE_TAC[HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* This is often more useful as a rewrite.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CLAUSES = prove
 (`(s HAS_SIZE 0 <=> s = {}) /\
   (s HAS_SIZE (SUC n) <=>
        ?(a:A) t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))`,
  let lemma = SET_RULE `a IN s ==> (s = a INSERT (s DELETE a))` in
  REWRITE_TAC[HAS_SIZE_0] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC[lemma; IN_DELETE];
    SIMP_TAC[LEFT_IMP_EXISTS_THM; HAS_SIZE; CARD_CLAUSES; FINITE_INSERT]]);;

(* ------------------------------------------------------------------------- *)
(* Produce an explicit expansion for "s HAS_SIZE n" for numeral n.           *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CONV =
  let pth = prove
   (`(~((a:A) IN {}) /\ P <=> P) /\
     (~(a IN {b}) /\ P <=> ~(a = b) /\ P) /\
     (~(a IN (b INSERT cs)) /\ P <=> ~(a = b) /\ ~(a IN cs) /\ P)`,
    SET_TAC[])
  and qth = prove
   (`((?s. s HAS_SIZE 0 /\ P s) <=> P {}) /\
     ((?s. s HAS_SIZE (SUC n) /\ P s) <=>
      (?(a:A) s. s HAS_SIZE n /\ ~(a IN s) /\ P(a INSERT s)))`,
    REWRITE_TAC[HAS_SIZE_CLAUSES] THEN MESON_TAC[]) in
  let qconv_0 = GEN_REWRITE_CONV I [CONJUNCT1 qth]
  and qconv_1 = GEN_REWRITE_CONV I [CONJUNCT2 qth]
  and rconv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and rconv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec EXISTS_HAS_SIZE_AND_CONV tm =
   (qconv_0 ORELSEC
    (BINDER_CONV(LAND_CONV(RAND_CONV num_CONV)) THENC
     qconv_1 THENC
     BINDER_CONV EXISTS_HAS_SIZE_AND_CONV)) tm in
  let rec NOT_IN_INSERT_CONV tm =
   ((rconv_0 THENC NOT_IN_INSERT_CONV) ORELSEC
    (rconv_1 THENC RAND_CONV NOT_IN_INSERT_CONV) ORELSEC
    ALL_CONV) tm in
  let HAS_SIZE_CONV =
    GEN_REWRITE_CONV I [CONJUNCT1 HAS_SIZE_CLAUSES] ORELSEC
    (RAND_CONV num_CONV THENC
     GEN_REWRITE_CONV I [CONJUNCT2 HAS_SIZE_CLAUSES] THENC
     BINDER_CONV EXISTS_HAS_SIZE_AND_CONV) in
  fun tm ->
    let th = HAS_SIZE_CONV tm in
    let tm' = rand(concl th) in
    let evs,bod = strip_exists tm' in
    if evs = [] then th else
    let th' = funpow (length evs) BINDER_CONV NOT_IN_INSERT_CONV tm' in
    TRANS th th';;

(* ------------------------------------------------------------------------- *)
(* Various useful lemmas about cardinalities of unions etc.                  *)
(* ------------------------------------------------------------------------- *)

let CARD_SUBSET_EQ = prove
 (`!(a:A->bool) b. FINITE b /\ a SUBSET b /\ (CARD a = CARD b) ==> (a = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:A->bool`; `b DIFF (a:A->bool)`] CARD_UNION) THEN
  SUBGOAL_THEN `FINITE(a:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(b:A->bool DIFF a)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a:A->bool INTER (b DIFF a) = EMPTY` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a UNION (b:A->bool DIFF a) = b` ASSUME_TAC THENL
   [UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(a = a + b) <=> (b = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `b:A->bool DIFF a = EMPTY` MP_TAC THENL
   [REWRITE_TAC[GSYM HAS_SIZE_0] THEN
    ASM_REWRITE_TAC[HAS_SIZE];
    UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]]);;

let CARD_SUBSET = prove
 (`!(a:A->bool) b. a SUBSET b /\ FINITE(b) ==> CARD(a) <= CARD(b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b:A->bool = a UNION (b DIFF a)` SUBST1_TAC THENL
   [UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD (a UNION b DIFF a) = CARD(a:A->bool) + CARD(b DIFF a)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[]];
    ARITH_TAC]);;

let CARD_SUBSET_LE = prove
 (`!(a:A->bool) b. FINITE b /\ a SUBSET b /\ CARD b <= CARD a ==> a = b`,
  MESON_TAC[CARD_SUBSET; CARD_SUBSET_EQ; LE_ANTISYM]);;

let SUBSET_CARD_EQ = prove
 (`!s t:A->bool. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)`,
  MESON_TAC[CARD_SUBSET_EQ; LE_ANTISYM; CARD_SUBSET]);;

let FINITE_CARD_LE_SUBSET = prove
 (`!s (t:A->bool) n.
        s SUBSET t /\ FINITE t /\ CARD t <= n
        ==> FINITE s /\ CARD s <= n`,
  MESON_TAC[FINITE_SUBSET; CARD_SUBSET; LE_TRANS]);;

let CARD_PSUBSET = prove
 (`!(a:A->bool) b. a PSUBSET b /\ FINITE(b) ==> CARD(a) < CARD(b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SET_RULE
   `a PSUBSET b <=> ?x. x IN b /\ ~(x IN a) /\ a SUBSET (b DELETE x)` ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(b DELETE (x:A))` THEN
  ASM_SIMP_TAC[CARD_SUBSET; FINITE_DELETE] THEN
  ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY]);;

let CARD_PSUBSET_IMP = prove
 (`!a b:A->bool. a SUBSET b /\ ~(CARD a = CARD b) ==> a PSUBSET b`,
  REWRITE_TAC[PSUBSET] THEN MESON_TAC[]);;

let CARD_PSUBSET_EQ = prove
 (`!a b:A->bool. FINITE b /\ a SUBSET b ==> (a PSUBSET b <=> CARD a < CARD b)`,
  MESON_TAC[CARD_PSUBSET_IMP; CARD_PSUBSET; LT_REFL]);;

let CARD_UNION_LE = prove
 (`!s t:A->bool.
        FINITE s /\ FINITE t ==> CARD(s UNION t) <= CARD(s) + CARD(t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(s:A->bool) + CARD(t DIFF s)` THEN
  ASM_SIMP_TAC[LE_ADD_LCANCEL; CARD_SUBSET; SUBSET_DIFF; FINITE_DIFF] THEN
  MATCH_MP_TAC EQ_IMP_LE THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

let FINITE_CARD_LE_UNION = prove
 (`!s (t:A->bool) m n.
        (FINITE s /\ CARD s <= m) /\
        (FINITE t /\ CARD t <= n)
        ==> FINITE(s UNION t) /\ CARD(s UNION t) <= m + n`,
  MESON_TAC[FINITE_UNION; CARD_UNION_LE; LE_ADD2; LE_TRANS]);;

let CARD_UNIONS_LE = prove
 (`!s t:A->B->bool m n.
        s HAS_SIZE m /\ (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n)
        ==> CARD(UNIONS {t(x) | x IN s}) <= m * n`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THEN
  REWRITE_TAC[SET_RULE `UNIONS {t x | x IN {}} = {}`; CARD_CLAUSES; LE_0] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE
   `UNIONS {t x | x IN a INSERT s} = t(a) UNION UNIONS {t x | x IN s}`] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC
   `CARD((t:A->B->bool) x) + CARD(UNIONS {(t:A->B->bool) y | y IN s})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION_LE THEN ASM_SIMP_TAC[IN_INSERT] THEN
    REWRITE_TAC[SET_RULE `{t x | x IN s} = IMAGE t s`] THEN
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE;
                 IN_INSERT];
    MATCH_MP_TAC(ARITH_RULE `a <= n /\ b <= x * n ==> a + b <= SUC x * n`) THEN
    ASM_SIMP_TAC[IN_INSERT]]);;

let CARD_UNION_GEN = prove
 (`!s t:A->bool.
        FINITE s /\ FINITE t
        ==> CARD(s UNION t) = (CARD(s) + CARD(t)) - CARD(s INTER t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `x:num <= y ==> (a + y) - x = a + (y - x)`;
               CARD_SUBSET; INTER_SUBSET; GSYM CARD_DIFF] THEN
  REWRITE_TAC[SET_RULE `t DIFF (s INTER t) = t DIFF s`] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

let CARD_UNION_OVERLAP_EQ = prove
 (`!s t:A->bool.
        FINITE s /\ FINITE t
        ==> (CARD(s UNION t) = CARD s + CARD t <=> s INTER t = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_UNION_GEN] THEN
  REWRITE_TAC[ARITH_RULE `a - b = a <=> b = 0 \/ a = 0`] THEN
  ASM_SIMP_TAC[ADD_EQ_0; CARD_EQ_0; FINITE_INTER] THEN SET_TAC[]);;

let CARD_UNION_OVERLAP = prove
 (`!s t:A->bool.
        FINITE s /\ FINITE t /\ CARD(s UNION t) < CARD(s) + CARD(t)
        ==> ~(s INTER t = {})`,
  SIMP_TAC[GSYM CARD_UNION_OVERLAP_EQ] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of image under maps, injective or general.                    *)
(* ------------------------------------------------------------------------- *)

let CARD_IMAGE_INJ = prove
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                FINITE s ==> (CARD (IMAGE f s) = CARD s)`,
  GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b ==> c <=> b ==> a ==> c`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; IMAGE_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE; IN_IMAGE] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[IN_INSERT]);;

let HAS_SIZE_IMAGE_INJ = prove
 (`!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ s HAS_SIZE n
        ==> (IMAGE f s) HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE; FINITE_IMAGE] THEN MESON_TAC[CARD_IMAGE_INJ]);;

let CARD_IMAGE_LE = prove
 (`!(f:A->B) s. FINITE s ==> CARD(IMAGE f s) <= CARD s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; CARD_CLAUSES; FINITE_IMAGE; LE_REFL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ARITH_TAC);;

let FINITE_CARD_LE_IMAGE = prove
 (`!(f:A->B) s n.
        FINITE s /\ CARD s <= n ==> FINITE(IMAGE f s) /\ CARD(IMAGE f s) <= n`,
  MESON_TAC[CARD_IMAGE_LE; LE_TRANS; FINITE_IMAGE]);;

let CARD_IMAGE_INJ_EQ = prove
 (`!f:A->B s t.
        FINITE s /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> ?!x. x IN s /\ f(x) = y)
        ==> CARD t = CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[]]);;

let CARD_SUBSET_IMAGE = prove
 (`!(f:A->B) s t. FINITE t /\ s SUBSET IMAGE f t ==> CARD s <= CARD t`,
  MESON_TAC[LE_TRANS; FINITE_IMAGE; CARD_IMAGE_LE; CARD_SUBSET]);;

let HAS_SIZE_IMAGE_INJ_EQ = prove
 (`!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC(TAUT
   `(a' <=> a) /\ (a ==> (b' <=> b)) ==> (a' /\ b' <=> a /\ b)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ;
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CARD_IMAGE_INJ] THEN
  ASM_REWRITE_TAC[]);;

let CARD_IMAGE_EQ_INJ = prove
 (`!f:A->B s.
        FINITE s
        ==> (CARD(IMAGE f s) = CARD s <=>
             !x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[CARD_IMAGE_INJ]] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `CARD(IMAGE (f:A->B) s) = CARD s` THEN
  SUBGOAL_THEN `IMAGE  (f:A->B) s = IMAGE f (s DELETE y)` SUBST1_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[]] THEN
  MATCH_MP_TAC(ARITH_RULE `!n. m <= n /\ n < p ==> ~(m:num = p)`) THEN
  EXISTS_TAC `CARD(s DELETE (y:A))` THEN
  ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE] THEN
  ASM_SIMP_TAC[CARD_DELETE; CARD_EQ_0;
               ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM SET_TAC[]);;

let EXISTS_SMALL_SUBSET_IMAGE_INJ = prove
 (`!P (f:A->B) s n.
    (?t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y)) /\
         P (IMAGE f t))`,
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> r /\ s /\ p /\ q`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[EXISTS_SUBSET_IMAGE_INJ] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT
   `(p ==> (q <=> s)) /\ (p /\ s ==> (r <=> t))
    ==> ((p /\ q) /\ r <=> (p /\ s) /\ t)`) THEN
  MESON_TAC[CARD_IMAGE_INJ; FINITE_IMAGE_INJ_EQ]);;

let FORALL_SMALL_SUBSET_IMAGE_INJ = prove
 (`!P (f:A->B) s n.
    (!t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s ==> P t) <=>
    (!t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         (!x y. x IN t /\ y IN t ==> (f x = f y <=> x = y))
         ==> P (IMAGE f t))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!t. p t) <=> ~(?t. ~p t)`] THEN
  REWRITE_TAC[NOT_IMP; EXISTS_SMALL_SUBSET_IMAGE_INJ; GSYM CONJ_ASSOC]);;

let EXISTS_SMALL_SUBSET_IMAGE = prove
 (`!P (f:A->B) s n.
    (?t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ CARD t < n /\ t SUBSET s /\
         P (IMAGE f t))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[EXISTS_SMALL_SUBSET_IMAGE_INJ] THEN MESON_TAC[];
    MESON_TAC[FINITE_IMAGE; CARD_IMAGE_LE; LET_TRANS; IMAGE_SUBSET]]);;

let FORALL_SMALL_SUBSET_IMAGE = prove
 (`!P (f:A->B) s n.
    (!t. FINITE t /\ CARD t < n /\ t SUBSET IMAGE f s ==> P t) <=>
    (!t. FINITE t /\ CARD t < n /\ t SUBSET s ==> P (IMAGE f t))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!t. p t) <=> ~(?t. ~p t)`] THEN
  REWRITE_TAC[NOT_IMP; EXISTS_SMALL_SUBSET_IMAGE; GSYM CONJ_ASSOC]);;

let CARD_IMAGE_LE2 = prove
 (`!(f:A->B) (g:A->C) s.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ g x = g y ==> f x = f y)
        ==> CARD(IMAGE f s) <= CARD(IMAGE g s)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `h:C->B` o
    GEN_REWRITE_RULE I [FUNCTION_FACTORS_LEFT_GEN]) THEN
  TRANS_TAC LE_TRANS `CARD(IMAGE ((h:C->B) o (g:A->C)) s)` THEN
  ASM_SIMP_TAC[IMAGE_o; CARD_IMAGE_LE; FINITE_IMAGE] THEN
  MATCH_MP_TAC EQ_IMP_LE THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let CARD_IMAGE_LT2 = prove
 (`!(f:A->B) (g:A->C) s.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ g x = g y ==> f x = f y) /\
        ~(!x y. x IN s /\ y IN s /\ f x = f y ==> g x = g y)
        ==> CARD(IMAGE f s) < CARD(IMAGE g s)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `h:C->B` o
    GEN_REWRITE_RULE I [FUNCTION_FACTORS_LEFT_GEN]) THEN
  SUBGOAL_THEN `IMAGE f s = IMAGE (h:C->B) (IMAGE (g:A->C) s)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LT_LE; CARD_IMAGE_LE; FINITE_IMAGE; CARD_IMAGE_EQ_INJ] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_SUBSET_STRONG = prove
 (`!n s:A->bool.
        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  INDUCT_TAC THEN REWRITE_TAC[HAS_SIZE_0; HAS_SIZE_SUC] THENL
   [MESON_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN
  REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; ARITH_RULE `~(SUC n <= 0)`] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; LE_SUC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a:A) INSERT t` THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[HAS_SIZE; CARD_DELETE; FINITE_INSERT; FINITE_DELETE;
               CARD_CLAUSES] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
  ASM SET_TAC[]);;

let CHOOSE_SUBSET_EQ = prove
 (`!n s:A->bool.
     (FINITE s ==> n <= CARD s) <=> (?t. t SUBSET s /\ t HAS_SIZE n)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CHOOSE_SUBSET_STRONG] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  TRANS_TAC LE_TRANS `CARD(t:A->bool)` THEN
  ASM_MESON_TAC[CARD_SUBSET; HAS_SIZE; LE_REFL]);;

let CHOOSE_SUBSET = prove
 (`!s:A->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  MESON_TAC[CHOOSE_SUBSET_STRONG]);;

let CHOOSE_SUBSET_BETWEEN = prove
 (`!n s u:A->bool.
        s SUBSET u /\ FINITE s /\ CARD s <= n /\ (FINITE u ==> n <= CARD u)
        ==> ?t. s SUBSET t /\ t SUBSET u /\ t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n - CARD(s:A->bool)`; `u DIFF s:A->bool`]
        CHOOSE_SUBSET_STRONG) THEN
  ANTS_TAC THENL
   [ASM_CASES_TAC `FINITE(u:A->bool)` THEN
    ASM_SIMP_TAC[CARD_DIFF; ARITH_RULE `n:num <= m ==> n - x <= m - x`] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    ASM_MESON_TAC[FINITE_UNION; FINITE_SUBSET; SET_RULE
     `u SUBSET (u DIFF s) UNION s`];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s UNION t:A->bool` THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    SUBGOAL_THEN `n:num = CARD(s) + (n - CARD(s:A->bool))` SUBST1_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC HAS_SIZE_UNION] THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[HAS_SIZE] THEN ASM SET_TAC[]]);;

let CARD_LE_UNIONS_CHAIN = prove
 (`!(f:(A->bool)->bool) n.
        (!t u. t IN f /\ u IN f ==> t SUBSET u \/ u SUBSET t) /\
        (!t. t IN f ==> FINITE t /\ CARD t <= n)
        ==> FINITE(UNIONS f) /\ CARD(UNIONS f) <= n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; FINITE_EMPTY; CARD_CLAUSES; LE_0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  REWRITE_TAC[ARITH_RULE `~(x <= n) <=> SUC n <= x`] THEN
  REWRITE_TAC[CHOOSE_SUBSET_EQ] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:A->bool` THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET_UNIONS_CHAIN THEN
  ASM_REWRITE_TAC[]);;

let CARD_LE_1 = prove
 (`!s:A->bool. FINITE s /\ CARD s <= 1 <=> ?a. s SUBSET {a}`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `c <= 1 <=> c = 0 \/ c = 1`] THEN
  REWRITE_TAC[LEFT_OR_DISTRIB; GSYM HAS_SIZE] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the parity of the set of fixed points of an involution.      *)
(* ------------------------------------------------------------------------- *)

let INVOLUTION_EVEN_NOFIXPOINTS = prove
 (`!f (s:A->bool).
        FINITE s /\ (!x. x IN s ==> f x IN s /\ ~(f x = x) /\ f(f x) = x)
        ==> EVEN(CARD s)`,
  REPEAT GEN_TAC THEN ABBREV_TAC `n = CARD(s:A->bool)` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[TAUT `p ==> q /\ r ==> s <=> (q /\ p) /\ r ==> s`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`s:A->bool`; `n:num`] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN ASM_REWRITE_TAC[CARD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  SIMP_TAC[FINITE_INSERT; IMP_CONJ; CARD_CLAUSES; FORALL_IN_INSERT] THEN
  REWRITE_TAC[IN_INSERT] THEN ASM_CASES_TAC `f(a:A) = a` THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `n = 1` THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC n = 1 <=> n = 0`; CARD_EQ_0; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n - 2`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s DELETE (f:A->A) a`) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; EVEN_SUB; ARITH] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= 2 <=> n = 0 \/ n = 1 \/ n = 2`] THEN
  ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; ASM SET_TAC[]]);;

let INVOLUTION_EVEN_FIXPOINTS = prove
 (`!f (s:A->bool).
        FINITE s /\ (!x. x IN s ==> f x IN s /\ f(f x) = x)
        ==> (EVEN(CARD {x | x IN s /\ f x = x}) <=> EVEN(CARD s))`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
  `EVEN(CARD({x:A | x IN s /\ f x = x} UNION {x | x IN s /\ ~(f x = x)}))` THEN
  CONJ_TAC THENL [ALL_TAC; AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[]] THEN
  ASM_SIMP_TAC[EVEN_ADD; CARD_UNION; FINITE_RESTRICT; SET_RULE
   `{x | x IN s /\ P x} INTER {x | x IN s /\ ~P x} = {}`] THEN
  REWRITE_TAC[TAUT `(p <=> (p <=> q)) <=> q`] THEN
  MATCH_MP_TAC INVOLUTION_EVEN_NOFIXPOINTS THEN
  EXISTS_TAC `f:A->A` THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of product.                                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_PRODUCT_DEPENDENT = prove
 (`!s m t n.
         s HAS_SIZE m /\ (!x. x IN s ==> t(x) HAS_SIZE n)
         ==> {(x:A,y:B) | x IN s /\ y IN t(x)} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES; NOT_IN_EMPTY; IN_INSERT] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MAP_EVERY X_GEN_TAC [`t:A->B->bool`; `n:num`] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `CARD(s:A->bool)`) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[SET_RULE
    `{(x,y) | (x = a \/ x IN s) /\ y IN t(x)} =
     {(x,y) | x IN s /\ y IN t(x)} UNION
     IMAGE (\y. (a,y)) (t a)`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN
  ASM_SIMP_TAC[HAS_SIZE_IMAGE_INJ; PAIR_EQ] THEN
  REWRITE_TAC[DISJOINT; IN_IMAGE; IN_ELIM_THM; IN_INTER; EXTENSION;
              NOT_IN_EMPTY; EXISTS_PAIR_THM; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[PAIR_EQ]);;

let FINITE_PRODUCT_DEPENDENT = prove
 (`!f:A->B->C s t.
        FINITE s /\ (!x. x IN s ==> FINITE(t x))
        ==> FINITE {f x y | x IN s /\ y IN (t x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(x,y). (f:A->B->C) x y) {x,y | x IN s /\ y IN t x}` THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE; MESON_TAC[]] THEN
  MAP_EVERY UNDISCH_TAC
   [`!x:A. x IN s ==> FINITE(t x :B->bool)`; `FINITE(s:A->bool)`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`t:A->B->bool`; `s:A->bool`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [GEN_TAC THEN SUBGOAL_THEN `{(x:A,y:B) | x IN {} /\ y IN (t x)} = {}`
     (fun th -> REWRITE_TAC[th; FINITE_RULES]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `t:A->B->bool` THEN
  SUBGOAL_THEN
   `{(x:A,y:B) | x IN (a INSERT s) /\ y IN (t x)} =
    IMAGE (\y. a,y) (t a) UNION {(x,y) | x IN s /\ y IN (t x)}`
   (fun th -> ASM_SIMP_TAC[IN_INSERT; FINITE_IMAGE; FINITE_UNION; th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INSERT; IN_UNION] THEN
  MESON_TAC[]);;

let FINITE_PRODUCT = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\ y IN t}`,
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT]);;

let CARD_PRODUCT = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {(x:A,y:B) | x IN s /\ y IN t} = CARD s * CARD t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:A->bool`; `CARD(s:A->bool)`; `\x:A. t:B->bool`;
                  `CARD(t:B->bool)`] HAS_SIZE_PRODUCT_DEPENDENT) THEN
  ASM_SIMP_TAC[HAS_SIZE]);;

let HAS_SIZE_PRODUCT = prove
 (`!s m t n. s HAS_SIZE m /\ t HAS_SIZE n
             ==> {(x:A,y:B) | x IN s /\ y IN t} HAS_SIZE (m * n)`,
  SIMP_TAC[HAS_SIZE; CARD_PRODUCT; FINITE_PRODUCT]);;

(* ------------------------------------------------------------------------- *)
(* Actually introduce a Cartesian product operation.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("CROSS",(22,"right"));;

let CROSS = new_definition
 `(s:A->bool) CROSS (t:B->bool) = {x,y | x IN s /\ y IN t}`;;

let IN_CROSS = prove
 (`!(x:A) (y:B) s t. (x,y) IN (s CROSS t) <=> x IN s /\ y IN t`,
  REWRITE_TAC[CROSS; IN_ELIM_PAIR_THM]);;

let HAS_SIZE_CROSS = prove
 (`!(s:A->bool) (t:B->bool) m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)`,
  REWRITE_TAC[CROSS; HAS_SIZE_PRODUCT]);;

let FINITE_CROSS = prove
 (`!(s:A->bool) (t:B->bool). FINITE s /\ FINITE t ==> FINITE(s CROSS t)`,
  SIMP_TAC[CROSS; FINITE_PRODUCT]);;

let CARD_CROSS = prove
 (`!(s:A->bool) (t:B->bool). FINITE s /\ FINITE t ==> CARD(s CROSS t) = CARD s * CARD t`,
  SIMP_TAC[CROSS; CARD_PRODUCT]);;

let CROSS_EQ_EMPTY = prove
 (`!(s:A->bool) (t:B->bool). s CROSS t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let CROSS_EMPTY = prove
 (`(!s:A->bool. s CROSS {} = {}) /\ (!t:B->bool. {} CROSS t = {})`,
  REWRITE_TAC[CROSS_EQ_EMPTY]);;

let CROSS_SING = prove
 (`!x:A y:B. {x} CROSS {y} = {(x,y)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_SING; IN_CROSS; PAIR_EQ]);;

let CROSS_UNIV = prove
 (`(:A) CROSS (:B) = (:A#B)`,
  REWRITE_TAC[CROSS; EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM; IN_UNIV]);;

let FINITE_CROSS_EQ = prove
 (`!s:A->bool t:B->bool.
        FINITE(s CROSS t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; FINITE_EMPTY] THEN
  ASM_CASES_TAC `t:B->bool = {}` THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; FINITE_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[FINITE_CROSS] THEN REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP(ISPEC `FST:A#B->A` FINITE_IMAGE));
    FIRST_ASSUM(MP_TAC o MATCH_MP(ISPEC `SND:A#B->B` FINITE_IMAGE))] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
  ASM SET_TAC[]);;

let INFINITE_CROSS_EQ = prove
 (`!(s:A->bool) (t:B->bool).
        INFINITE(s CROSS t) <=>
        ~(s = {}) /\ INFINITE t \/ INFINITE s /\ ~(t = {})`,
  REWRITE_TAC[INFINITE; FINITE_CROSS_EQ] THEN MESON_TAC[FINITE_EMPTY]);;

let FINITE_CROSS_UNIV = prove
 (`FINITE(:A#B) <=> FINITE(:A) /\ FINITE(:B)`,
  REWRITE_TAC[GSYM CROSS_UNIV; FINITE_CROSS_EQ; UNIV_NOT_EMPTY]);;

let INFINITE_CROSS_UNIV = prove
 (`INFINITE(:A#B) <=> INFINITE(:A) \/ INFINITE(:B)`,
  REWRITE_TAC[GSYM CROSS_UNIV; INFINITE_CROSS_EQ; UNIV_NOT_EMPTY] THEN
  MESON_TAC[]);;

let FINITE_UNIV_PAIR = prove
 (`FINITE(:A#A) <=> FINITE(:A)`,
  REWRITE_TAC[FINITE_CROSS_UNIV]);;

let INFINITE_UNIV_PAIR = prove
 (`INFINITE(:A#A) <=> INFINITE(:A)`,
  REWRITE_TAC[INFINITE_CROSS_UNIV]);;

let FORALL_IN_CROSS = prove
 (`!P s t. (!z:A#B. z IN s CROSS t ==> P z) <=>
           (!x y. x IN s /\ y IN t ==> P(x,y))`,
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS]);;

let EXISTS_IN_CROSS = prove
 (`!P s t. (?z:A#B. z IN s CROSS t /\ P z) <=>
           (?x y. x IN s /\ y IN t /\ P(x,y))`,
  REWRITE_TAC[EXISTS_PAIR_THM; GSYM CONJ_ASSOC; IN_CROSS]);;

let SUBSET_CROSS = prove
 (`!(s:A->bool) (t:B->bool) s' t'.
        s CROSS t SUBSET s' CROSS t' <=>
        s = {} \/ t = {} \/ s SUBSET s' /\ t SUBSET t'`,
  SIMP_TAC[CROSS; EXTENSION; IN_ELIM_PAIR_THM; SUBSET;
   FORALL_PAIR_THM; IN_CROSS; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let CROSS_MONO = prove
 (`!(s:A->bool) (t:B->bool) s' t'. s SUBSET s' /\ t SUBSET t' ==> s CROSS t SUBSET s' CROSS t'`,
  SIMP_TAC[SUBSET_CROSS]);;

let CROSS_EQ = prove
 (`!s s':A->bool t t':B->bool.
        s CROSS t = s' CROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/ s = s' /\ t = t'`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_CROSS] THEN SET_TAC[]);;

let IMAGE_FST_CROSS = prove
 (`!s:A->bool t:B->bool.
        IMAGE FST (s CROSS t) = if t = {} then {} else s`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EXISTS_IN_CROSS; FST] THEN ASM SET_TAC[]);;

let IMAGE_SND_CROSS = prove
 (`!s:A->bool t:B->bool.
        IMAGE SND (s CROSS t) = if s = {} then {} else t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EXISTS_IN_CROSS; SND] THEN ASM SET_TAC[]);;

let IMAGE_PAIRED_CROSS = prove
 (`!(f:A->B) (g:C->D) s t.
         IMAGE (\(x,y). f x,g y) (s CROSS t) = (IMAGE f s) CROSS (IMAGE g t)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; FORALL_PAIR_THM;
              PAIR_EQ] THEN
  MESON_TAC[]);;

let CROSS_INTER = prove
 (`(!(s:A->bool) (t:B->bool) u.
        s CROSS (t INTER u) = (s CROSS t) INTER (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s INTER t) CROSS u = (s CROSS u) INTER (t CROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_INTER; IN_CROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let CROSS_UNION = prove
 (`(!(s:A->bool) (t:B->bool) u.
        s CROSS (t UNION u) = (s CROSS t) UNION (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s UNION t) CROSS u = (s CROSS u) UNION (t CROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_UNION; IN_CROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let CROSS_DIFF = prove
 (`(!(s:A->bool) (t:B->bool) u.
        s CROSS (t DIFF u) = (s CROSS t) DIFF (s CROSS u)) /\
   (!(s:A->bool) t (u:B->bool).
        (s DIFF t) CROSS u = (s CROSS u) DIFF (t CROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_DIFF; IN_CROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let INTER_CROSS = prove
 (`!(s:A->bool) s' (t:B->bool) t'.
      (s CROSS t) INTER (s' CROSS t') = (s INTER s') CROSS (t INTER t')`,
  REWRITE_TAC[EXTENSION; IN_INTER; FORALL_PAIR_THM; IN_CROSS] THEN
  CONV_TAC TAUT);;

let CROSS_UNIONS_UNIONS,CROSS_UNIONS = (CONJ_PAIR o prove)
 (`(!(f:(A->bool)->bool) (g:(B->bool)->bool).
        (UNIONS f) CROSS (UNIONS g) =
        UNIONS {s CROSS t | s IN f /\ t IN g}) /\
   (!(s:A->bool) (f:(A->bool)->bool).
        s CROSS (UNIONS f) = UNIONS {s CROSS t | t IN f}) /\
   (!(f:(A->bool)->bool) (t:B->bool).
        (UNIONS f) CROSS t = UNIONS {s CROSS t | s IN f})`,
  REWRITE_TAC[UNIONS_GSPEC; EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM;
              IN_CROSS] THEN
  SET_TAC[]);;

let CROSS_INTERS_INTERS,CROSS_INTERS = (CONJ_PAIR o prove)
 (`(!(f:(A->bool)->bool) (g:(B->bool)->bool).
        (INTERS f) CROSS (INTERS g) =
        if f = {} then INTERS {UNIV CROSS t | t IN g}
        else if g = {} then INTERS {s CROSS UNIV | s IN f}
        else INTERS {s CROSS t | s IN f /\ t IN g}) /\
   (!(s:A->bool) (f:(A->bool)->bool).
        s CROSS (INTERS f) =
        if f = {} then s CROSS UNIV else INTERS {s CROSS t | t IN f}) /\
   (!(f:(A->bool)->bool) (t:B->bool).
        (INTERS f) CROSS t =
        if f = {} then UNIV CROSS t else INTERS {s CROSS t | s IN f})`,
  REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN REWRITE_TAC[]) THEN
  ASM_REWRITE_TAC[INTERS_GSPEC; EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM;
                  IN_CROSS; NOT_IN_EMPTY] THEN
  ASM SET_TAC[]);;

let DISJOINT_CROSS = prove
 (`!s:A->bool t:B->bool s' t'.
        DISJOINT (s CROSS t) (s' CROSS t') <=>
        DISJOINT s s' \/ DISJOINT t t'`,
  REWRITE_TAC[DISJOINT; INTER_CROSS; CROSS_EQ_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* "Extensional" functions, mapping to a fixed value ARB outside the domain. *)
(* Even though these are still total, they're a conveniently better model    *)
(* of the partial function space (e.g. the space has the right cardinality). *)
(* ------------------------------------------------------------------------- *)

let ARB = new_definition
  `ARB = (@x:A. F)`;;

let EXTENSIONAL = new_definition
  `EXTENSIONAL s = {f:A->B | !x. ~(x IN s) ==> f x = ARB}`;;

let IN_EXTENSIONAL = prove
 (`!s f:A->B. f IN EXTENSIONAL s <=> (!x. ~(x IN s) ==> f x = ARB)`,
  REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM]);;

let IN_EXTENSIONAL_UNDEFINED = prove
 (`!s f:A->B x. f IN EXTENSIONAL s /\ ~(x IN s) ==> f x = ARB`,
  SIMP_TAC[IN_EXTENSIONAL]);;

let EXTENSIONAL_EMPTY = prove
 (`EXTENSIONAL {} = {\x:A. ARB:B}`,
  REWRITE_TAC[EXTENSION; IN_EXTENSIONAL; IN_SING; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FUN_EQ_THM]);;

let EXTENSIONAL_UNIV = prove
 (`!f:A->B. EXTENSIONAL (:A) f`,
  REWRITE_TAC[EXTENSIONAL; IN_UNIV; IN_ELIM_THM]);;

let EXTENSIONAL_EQ = prove
 (`!s f g:A->B.
     f IN EXTENSIONAL s /\ g IN EXTENSIONAL s /\ (!x. x IN s ==> f x = g x)
     ==> f = g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  ASM_CASES_TAC `x:A IN s` THENL
  [ASM_SIMP_TAC[]; ASM_MESON_TAC[IN_EXTENSIONAL_UNDEFINED]]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of a function to an EXTENSIONAL one on a subset.              *)
(* ------------------------------------------------------------------------- *)

let RESTRICTION = new_definition
  `RESTRICTION s (f:A->B) x = if x IN s then f x else ARB`;;

let RESTRICTION_THM = prove
 (`!s (f:A->B). RESTRICTION s f = \x. if x IN s then f x else ARB`,
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION]);;

let RESTRICTION_DEFINED = prove
 (`!s f:A->B x. x IN s ==> RESTRICTION s f x = f x`,
  SIMP_TAC[RESTRICTION]);;

let RESTRICTION_UNDEFINED = prove
 (`!s f:A->B x. ~(x IN s) ==> RESTRICTION s f x = ARB`,
  SIMP_TAC[RESTRICTION]);;

let RESTRICTION_EQ = prove
 (`!s f:A->B x y. x IN s /\ f x = y ==> RESTRICTION s f x = y`,
  SIMP_TAC[RESTRICTION_DEFINED]);;

let RESTRICTION_IN_EXTENSIONAL = prove
 (`!s f:A->B. RESTRICTION s f IN EXTENSIONAL s`,
  SIMP_TAC[IN_EXTENSIONAL; RESTRICTION]);;

let RESTRICTION_EXTENSION = prove
 (`!s f g:A->B. RESTRICTION s f = RESTRICTION s g <=>
                (!x. x IN s ==> f x = g x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RESTRICTION; FUN_EQ_THM] THEN MESON_TAC[]);;

let RESTRICTION_FIXPOINT = prove
 (`!s f:A->B. RESTRICTION s f = f <=> f IN EXTENSIONAL s`,
  REWRITE_TAC[IN_EXTENSIONAL; FUN_EQ_THM; RESTRICTION] THEN MESON_TAC[]);;

let RESTRICTION_UNIV = prove
 (`!f:A->B. RESTRICTION UNIV f = f`,
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION; IN_UNIV]);;

let RESTRICTION_RESTRICTION = prove
 (`!s t f:A->B.
        s SUBSET t ==> RESTRICTION s (RESTRICTION t f) = RESTRICTION s f`,
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN SET_TAC[]);;

let RESTRICTION_IDEMP = prove
 (`!s f:A->B. RESTRICTION s (RESTRICTION s f) = RESTRICTION s f`,
  REWRITE_TAC[RESTRICTION_FIXPOINT; RESTRICTION_IN_EXTENSIONAL]);;

let IMAGE_RESTRICTION = prove
 (`!f:A->B s t. s SUBSET t ==> IMAGE (RESTRICTION t f) s = IMAGE f s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; RESTRICTION] THEN SET_TAC[]);;

let RESTRICTION_COMPOSE_RIGHT = prove
 (`!f:A->B g:B->C s.
        RESTRICTION s (g o RESTRICTION s f) =
        RESTRICTION s (g o f)`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; RESTRICTION] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN SET_TAC[]);;

let RESTRICTION_COMPOSE_LEFT = prove
 (`!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o f) =
            RESTRICTION s (g o f)`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; RESTRICTION] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN SET_TAC[]);;

let RESTRICTION_COMPOSE = prove
 (`!f:A->B g:B->C s t.
        IMAGE f s SUBSET t
        ==> RESTRICTION s (RESTRICTION t g o RESTRICTION s f) =
            RESTRICTION s (g o f)`,
  SIMP_TAC[RESTRICTION_COMPOSE_LEFT; RESTRICTION_COMPOSE_RIGHT]);;

let RESTRICTION_UNIQUE = prove
 (`!s (f:A->B) g.
        RESTRICTION s f = g <=> EXTENSIONAL s g /\ !x. x IN s ==> f x = g x`,
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION; EXTENSIONAL; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let RESTRICTION_UNIQUE_ALT = prove
 (`!s (f:A->B) g.
        f = RESTRICTION s g <=> EXTENSIONAL s f /\ !x. x IN s ==> f x = g x`,
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION; EXTENSIONAL; IN_ELIM_THM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* General Cartesian product / dependent function space.                     *)
(* ------------------------------------------------------------------------- *)

let cartesian_product = new_definition
 `cartesian_product k s =
        {f:K->A | EXTENSIONAL k f /\ !i. i IN k ==> f i IN s i}`;;

let IN_CARTESIAN_PRODUCT = prove
 (`!k s (x:K->A).
        x IN cartesian_product k s <=>
        EXTENSIONAL k x /\ (!i. i IN k ==> x i IN s i)`,
  REWRITE_TAC[cartesian_product; IN_ELIM_THM]);;

let CARTESIAN_PRODUCT = prove
 (`!k s. cartesian_product k s =
         {f:K->A | !i. f i IN (if i IN k then s i else {ARB})}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
  MESON_TAC[IN_SING]);;

let RESTRICTION_IN_CARTESIAN_PRODUCT = prove
 (`!k s (f:K->A).
        RESTRICTION k f IN cartesian_product k s <=>
        !i. i IN k ==> (f i) IN (s i)`,
  REWRITE_TAC[RESTRICTION; cartesian_product; EXTENSIONAL; IN_ELIM_THM] THEN
  SET_TAC[]);;

let CARTESIAN_PRODUCT_AS_RESTRICTIONS = prove
 (`!k (s:K->A->bool).
      cartesian_product k s =
      {RESTRICTION k f |f| !i. i IN k ==> f i IN s i}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
  X_GEN_TAC `x:K->A` THEN
  REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
  STRIP_TAC THEN EXISTS_TAC `x:K->A` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN ASM_MESON_TAC[]);;

let CARTESIAN_PRODUCT_EQ_EMPTY = prove
 (`!k s:K->A->bool.
        cartesian_product k s = {} <=> ?i. i IN k /\ s i = {}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  REWRITE_TAC[SET_RULE
   `(?i. i IN k /\ s i = {}) <=> ~(!i. ?a. i IN k ==> a IN s i)`] THEN
  REWRITE_TAC[SKOLEM_THM; NOT_EXISTS_THM; cartesian_product] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `f:K->A` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i. if i IN k then (f:K->A) i else ARB`) THEN
  REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN SIMP_TAC[]);;

let CARTESIAN_PRODUCT_EMPTY = prove
 (`!(s:K->A->bool). cartesian_product {} s = {(\i. ARB)}`,
  REWRITE_TAC[CARTESIAN_PRODUCT; NOT_IN_EMPTY; EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN REWRITE_TAC[FUN_EQ_THM]);;

let CARTESIAN_PRODUCT_EQ_MEMBERS = prove
 (`!k s x y:K->A.
        x IN cartesian_product k s /\ y IN cartesian_product k s /\
        (!i. i IN k ==> x i = y i)
        ==> x = y`,
  REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXTENSIONAL_EQ THEN
  EXISTS_TAC `k:K->bool` THEN ASM_REWRITE_TAC[IN]);;

let CARTESIAN_PRODUCT_EQ_MEMBERS_EQ = prove
 (`!k s x y:K->A.
        x IN cartesian_product k s /\
        y IN cartesian_product k s
        ==> (x = y <=> !i. i IN k ==> x i = y i)`,
  MESON_TAC[CARTESIAN_PRODUCT_EQ_MEMBERS]);;

let SUBSET_CARTESIAN_PRODUCT = prove
 (`!k s t:K->A->bool.
        cartesian_product k s SUBSET cartesian_product k t <=>
        cartesian_product k s = {} \/ !i. i IN k ==> s i SUBSET t i`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `cartesian_product k (s:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  REWRITE_TAC[SUBSET; cartesian_product; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE RAND_CONV [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
  REWRITE_TAC[SET_RULE
   `~(?i. i IN k /\ s i = {}) <=> (!i. ?a. i IN k ==> a IN s i)`] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:K->A` THEN DISCH_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `i:K` THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(\j. if j IN k then if j = i then x else z j else ARB):K->A`) THEN
  REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN SIMP_TAC[] THEN
  ASM_MESON_TAC[]);;

let CARTESIAN_PRODUCT_EQ = prove
 (`!k s t:K->A->bool.
        cartesian_product k s = cartesian_product k t <=>
        cartesian_product k s = {} /\ cartesian_product k t = {} \/
        !i. i IN k ==> s i = t i`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `!i. i IN k ==> (s:K->A->bool) i = t i` THEN
  ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[cartesian_product; EXTENSION; IN_ELIM_THM];
    ASM_CASES_TAC `cartesian_product k (t:K->A->bool) = {}` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `cartesian_product k (s:K->A->bool) = {}` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_CARTESIAN_PRODUCT] THEN
    ASM SET_TAC[]]);;

let INTER_CARTESIAN_PRODUCT = prove
 (`!k s t:K->A->bool.
        (cartesian_product k s) INTER (cartesian_product k t) =
        cartesian_product k (\i. s i INTER t i)`,
  REWRITE_TAC[EXTENSION; cartesian_product; IN_INTER; IN_ELIM_THM] THEN
  SET_TAC[]);;

let CARTESIAN_PRODUCT_UNIV = prove
 (`cartesian_product (:K) (\i. (:A)) = (:K->A)`,
  REWRITE_TAC[EXTENSION; IN_UNIV; cartesian_product; IN_ELIM_THM] THEN
  REWRITE_TAC[EXTENSIONAL_UNIV]);;

let CARTESIAN_PRODUCT_SINGS = prove
 (`!k x:K->A. EXTENSIONAL k x ==> cartesian_product k (\i. {x i}) = {x}`,
  REWRITE_TAC[cartesian_product; IN_SING] THEN
  REWRITE_TAC[EXTENSION; EXTENSIONAL; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let CARTESIAN_PRODUCT_SINGS_GEN = prove
 (`!k (x:K->A). cartesian_product k (\i. {x i}) = {RESTRICTION k x}`,
  REWRITE_TAC[cartesian_product; IN_SING] THEN
  REWRITE_TAC[EXTENSION; EXTENSIONAL; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN MESON_TAC[]);;

let IMAGE_PROJECTION_CARTESIAN_PRODUCT = prove
 (`!k s:K->A->bool i.
        IMAGE (\x. x i) (cartesian_product k s) =
        if cartesian_product k s = {} then {}
        else if i IN k then s i else {ARB}`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `cartesian_product k (s:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[CARTESIAN_PRODUCT; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE RAND_CONV [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
  REWRITE_TAC[SET_RULE
   `~(?i. i IN k /\ s i = {}) <=> (!i. ?a. i IN k ==> a IN s i)`] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:K->A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC
   `\j. if j = i then x else if j IN k then (z:K->A) j else ARB` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_SING]);;

let FORALL_CARTESIAN_PRODUCT_ELEMENTS = prove
 (`!P k s:K->A->bool.
        (!z i. z IN cartesian_product k s /\ i IN k ==> P i (z i)) <=>
        cartesian_product k s = {} \/
        (!i x. i IN k /\ x IN s i ==> P i x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `cartesian_product k (s:K->A->bool) = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC; MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [CARTESIAN_PRODUCT_EQ_EMPTY]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; SET_RULE
     `~(?i. i IN k /\ s i = {}) <=> (!i. ?x. i IN k ==> x IN s i)`] THEN
  X_GEN_TAC `z:K->A` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:K`; `x:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\j. if j = i then x else if j IN k then (z:K->A) j else ARB`; `i:K`]) THEN
  ASM_REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ = prove
 (`!P k (s:K->A->bool).
        ~(cartesian_product k s = {})
        ==> ((!i x. i IN k /\ x IN s i ==> P i x) <=>
             !z i. z IN cartesian_product k s /\ i IN k ==> P i (z i))`,
  SIMP_TAC[FORALL_CARTESIAN_PRODUCT_ELEMENTS]);;

let EXISTS_CARTESIAN_PRODUCT_ELEMENT = prove
 (`!P k s:K->A->bool.
        (?z. z IN cartesian_product k s /\ (!i. i IN k ==> P i (z i))) <=>
        (!i. i IN k ==> ?x. x IN (s i) /\ P i x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_AS_RESTRICTIONS; EXISTS_IN_GSPEC] THEN
  SIMP_TAC[RESTRICTION] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Product of a family of maps.                                              *)
(* ------------------------------------------------------------------------- *)

let product_map = new_definition
 `product_map k (f:K->A->B) = \x. RESTRICTION k (\i. f i (x i))`;;

let PRODUCT_MAP_RESTRICTION = prove
 (`!(f:K->A->B) k x.
        product_map k f (RESTRICTION k x) = RESTRICTION k (\i. f i (x i))`,
  SIMP_TAC[product_map; RESTRICTION; o_THM; FUN_EQ_THM]);;

let IMAGE_PRODUCT_MAP = prove
 (`!(f:K->A->B) k s.
        IMAGE (product_map k f) (cartesian_product k s) =
        cartesian_product k (\i. IMAGE (f i) (s i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CARTESIAN_PRODUCT_AS_RESTRICTIONS] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[product_map; GSYM IMAGE_o; o_DEF] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `g:K->B` THEN
  REWRITE_TAC[IN_IMAGE; RESTRICTION; IN_ELIM_THM] THEN
  EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RESTRICTION_EXTENSION] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint union construction for a family of sets.                         *)
(* ------------------------------------------------------------------------- *)

let disjoint_union = new_definition
 `disjoint_union (k:K->bool) (s:K->A->bool) = { (i,x) | i IN k /\ x IN s i}`;;

let SUBSET_DISJOINT_UNION = prove
 (`!k (s:K->A->bool) t.
        disjoint_union k s SUBSET disjoint_union k t <=>
        !i. i IN k ==> s i SUBSET t i`,
  REWRITE_TAC[SUBSET; disjoint_union; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN SET_TAC[]);;

let DISJOINT_UNION_EQ = prove
 (`!k (s:K->A->bool) t.
        disjoint_union k s = disjoint_union k t <=>
        !i. i IN k ==> s i = t i`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_DISJOINT_UNION] THEN
  SET_TAC[]);;

let SUBSET_DISJOINT_UNION_EXISTS = prove
 (`!k (s:K->A->bool) u.
        u SUBSET disjoint_union k s <=>
        ?t. u = disjoint_union k t /\ !i. i IN k ==> t i SUBSET s i`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC; MESON_TAC[SUBSET_DISJOINT_UNION]] THEN
  EXISTS_TAC `\i. {x | (i,x) IN (u:K#A->bool)}` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[SUBSET; EXTENSION] THEN
  REWRITE_TAC[disjoint_union; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  SET_TAC[]);;

let INTER_DISJOINT_UNION = prove
 (`!k s t:K->A->bool.
        (disjoint_union k s) INTER (disjoint_union k t) =
        disjoint_union k (\i. s i INTER t i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; disjoint_union; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[PAIR_EQ]);;

let UNION_DISJOINT_UNION = prove
 (`!k s t:K->A->bool.
        (disjoint_union k s) UNION (disjoint_union k t) =
        disjoint_union k (\i. s i UNION t i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; disjoint_union; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[PAIR_EQ]);;

let DISJOINT_UNION_EQ_EMPTY = prove
 (`!k s:K->A->bool.
        disjoint_union k s = {} <=> !i. i IN k ==> s i = {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; disjoint_union; IN_ELIM_PAIR_THM;
              NOT_IN_EMPTY] THEN
  SET_TAC[]);;

let DISJOINT_DISJOINT_UNION = prove
 (`!k s t:K->A->bool.
        DISJOINT (disjoint_union k s) (disjoint_union k t) =
        !i. i IN k ==> DISJOINT (s i) (t i)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DISJOINT; INTER_DISJOINT_UNION; DISJOINT_UNION_EQ_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of functions with bounded domain (support) and range.         *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_FUNSPACE = prove
 (`!d n t:B->bool m s:A->bool.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | (!x. x IN s ==> f(x) IN t) /\ (!x. ~(x IN s) ==> (f x = d))}
            HAS_SIZE (n EXP m)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; EXP] THEN
    CONV_TAC HAS_SIZE_CONV THEN EXISTS_TAC `(\x. d):A->B` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN REWRITE_TAC[FUN_EQ_THM];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`s0:A->bool`; `a:A`; `s:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{f:A->B | (!x. x IN a INSERT s ==> f x IN t) /\
              (!x. ~(x IN a INSERT s) ==> (f x = d))} =
    IMAGE (\(b,g) x. if x = a then b else g(x))
          {b,g | b IN t /\
                 g IN {f | (!x. x IN s ==> f x IN t) /\
                           (!x. ~(x IN s) ==> (f x = d))}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_THM;
                EXISTS_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ; CONJ_ASSOC; ONCE_REWRITE_RULE[CONJ_SYM]
     UNWIND_THM1] THEN
    X_GEN_TAC `f:A->B` THEN REWRITE_TAC[IN_INSERT] THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) a`; `\x. if x IN s then (f:A->B) x else d`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `g:A->B`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC[EXP; HAS_SIZE_PRODUCT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_EQ; CONJ_ASSOC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_MESON_TAC[]]);;

let CARD_FUNSPACE = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                             (!x. ~(x IN s) ==> (f x = d))} =
             (CARD t) EXP (CARD s))`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

let FINITE_FUNSPACE = prove
 (`!s t. FINITE s /\ FINITE t
         ==> FINITE {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                              (!x. ~(x IN s) ==> (f x = d))}`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

let HAS_SIZE_FUNSPACE_UNIV = prove
 (`!m n. (:A) HAS_SIZE m /\ (:B) HAS_SIZE n ==> (:A->B) HAS_SIZE (n EXP m)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_FUNSPACE) THEN
  REWRITE_TAC[IN_UNIV; UNIV_GSPEC]);;

let CARD_FUNSPACE_UNIV = prove
 (`FINITE(:A) /\ FINITE(:B) ==> CARD(:A->B) = CARD(:B) EXP CARD(:A)`,
  MESON_TAC[HAS_SIZE_FUNSPACE_UNIV; HAS_SIZE]);;

let FINITE_FUNSPACE_UNIV = prove
 (`FINITE(:A) /\ FINITE(:B) ==> FINITE(:A->B)`,
  MESON_TAC[HAS_SIZE_FUNSPACE_UNIV; HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of type bool.                                                 *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_BOOL = prove
 (`(:bool) HAS_SIZE 2`,
  SUBGOAL_THEN `(:bool) = {F,T}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT] THEN CONV_TAC TAUT;
    SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; ARITH;
             IN_SING; NOT_IN_EMPTY]]);;

let CARD_BOOL = prove
 (`CARD(:bool) = 2`,
  MESON_TAC[HAS_SIZE_BOOL; HAS_SIZE]);;

let FINITE_BOOL = prove
 (`FINITE(:bool)`,
  MESON_TAC[HAS_SIZE_BOOL; HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Hence cardinality of powerset.                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_POWERSET = prove
 (`!(s:A->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `{t | t SUBSET s} =
    {f | (!x:A. x IN s ==> f(x) IN UNIV) /\ (!x. ~(x IN s) ==> (f x = F))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; SUBSET; IN; CONTRAPOS_THM];
    MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [`T`; `F`] THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC TAUT]);;

let CARD_POWERSET = prove
 (`!s:A->bool. FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))`,
  MESON_TAC[HAS_SIZE_POWERSET; HAS_SIZE]);;

let FINITE_POWERSET = prove
 (`!s:A->bool. FINITE s ==> FINITE {t | t SUBSET s}`,
  MESON_TAC[HAS_SIZE_POWERSET; HAS_SIZE]);;

let FINITE_POWERSET_EQ = prove
 (`!s:A->bool. FINITE {t | t SUBSET s} <=> FINITE s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FINITE_POWERSET] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(IMAGE (\x:A. {x}) s)` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
    SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_SING];
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    SET_TAC[]]);;

let FINITE_RESTRICTED_SUBSETS = prove
 (`!P s:A->bool. FINITE s ==> FINITE {t | t SUBSET s /\ P t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

let FINITE_UNIONS = prove
 (`!s:(A->bool)->bool.
        FINITE(UNIONS s) <=> FINITE s /\ (!t. t IN s ==> FINITE t)`,
  GEN_TAC THEN ASM_CASES_TAC `FINITE(s:(A->bool)->bool)` THEN
  ASM_SIMP_TAC[FINITE_FINITE_UNIONS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_POWERSET) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN SET_TAC[]);;

let FINITE_CARD_LE_UNIONS = prove
 (`!s (t:A->B->bool) m n.
        (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n) /\
        FINITE s /\ CARD s <= m
        ==> FINITE(UNIONS {t x | x IN s}) /\
            CARD(UNIONS {t x | x IN s}) <= m * n`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FINITE_UNIONS; FORALL_IN_GSPEC; FINITE_IMAGE; SIMPLE_IMAGE] THEN
  TRANS_TAC LE_TRANS `CARD(s:A->bool) * n` THEN
  ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE; LE_MULT_RCANCEL] THEN
  MATCH_MP_TAC CARD_UNIONS_LE THEN ASM_REWRITE_TAC[HAS_SIZE]);;

let POWERSET_CLAUSES = prove
 (`{s:A->bool | s SUBSET {}} = {{}} /\
   (!a:A t. {s | s SUBSET (a INSERT t)} =
            {s | s SUBSET t} UNION IMAGE (\s. a INSERT s) {s | s SUBSET t})`,
  REWRITE_TAC[SUBSET_INSERT_DELETE; SUBSET_EMPTY; SING_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
  ONCE_REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  X_GEN_TAC `s:A->bool` THEN
  ASM_CASES_TAC `(a:A) IN s` THENL [ALL_TAC; ASM SET_TAC[]] THEN
  STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `s DELETE (a:A)` THEN
  ASM SET_TAC[]);;

let FINITE_IMAGE_INFINITE = prove
 (`!f:A->B s.
        INFINITE s /\ FINITE(IMAGE f s)
        ==> ?a. a IN s /\ INFINITE {x | x IN s /\ f x = f a}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; INFINITE; TAUT `~(p /\ q) <=> p ==> ~q`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s = UNIONS {{x | x IN s /\ (f:A->B) x = y} |y| y IN IMAGE f s}`
  SUBST1_TAC THENL [REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_UNIONS; SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE]);;

let FINITE_RESTRICTED_POWERSET = prove
 (`!(s:A->bool) n.
        FINITE {t | t SUBSET s /\ t HAS_SIZE n} <=>
        FINITE s \/ n = 0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[HAS_SIZE_0; SET_RULE `t SUBSET s /\ t = {} <=> t = {}`] THEN
    REWRITE_TAC[SING_GSPEC; FINITE_SING];
    ASM_CASES_TAC `FINITE(s:A->bool)` THEN ASM_REWRITE_TAC[] THENL
     [ONCE_REWRITE_TAC[SET_RULE
       `{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`] THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_POWERSET];
      DISCH_TAC THEN SUBGOAL_THEN `FINITE(s:A->bool)`
      MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `UNIONS {t:A->bool | t SUBSET s /\ t HAS_SIZE n}` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[FINITE_UNIONS; FORALL_IN_GSPEC] THEN SIMP_TAC[HAS_SIZE];
        GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
        ONCE_REWRITE_TAC[SET_RULE `P /\ x IN t <=> {x} SUBSET t /\ P`] THEN
        MATCH_MP_TAC CHOOSE_SUBSET_BETWEEN THEN
        ASM_REWRITE_TAC[SING_SUBSET; FINITE_SING; CARD_SING] THEN
        ASM_SIMP_TAC[LE_1]]]]);;

let FINITE_RESTRICTED_FUNSPACE = prove
 (`!s:A->bool t:B->bool k.
        FINITE s /\ FINITE t
        ==> FINITE {f | IMAGE f s SUBSET t /\ {x | ~(f x = k x)} SUBSET s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\u:(A#B)->bool x. if ?y. (x,y) IN u then @y. (x,y) IN u else k x)
          {u | u SUBSET (s CROSS t)}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_CROSS; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `f:A->B` THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (\x. x,(f:A->B) x) {x | ~(f x = k x)}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_CROSS] THEN
    ASM SET_TAC[]] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; PAIR_EQ] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1; UNWIND_THM2] THEN
  ASM_CASES_TAC `(f:A->B) x = k x` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set of numbers is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_CLAUSES_LT = prove
 (`{i | i < 0} = {} /\
   (!k. {i | i < SUC k} = k INSERT {i | i < k})`,
  REWRITE_TAC[LT] THEN SET_TAC[]);;

let HAS_SIZE_NUMSEG_LT = prove
 (`!n. {m | m < n} HAS_SIZE n`,
  REWRITE_TAC[HAS_SIZE] THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[NUMSEG_CLAUSES_LT; FINITE_EMPTY; CARD_CLAUSES; FINITE_INSERT;
               IN_ELIM_THM; LT_REFL]);;

let CARD_NUMSEG_LT = prove
 (`!n. CARD {m | m < n} = n`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

let FINITE_NUMSEG_LT = prove
 (`!n:num. FINITE {m | m < n}`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

let NUMSEG_CLAUSES_LE = prove
 (`{i | i <= 0} = {0} /\
   (!k. {i | i <= SUC k} = SUC k INSERT {i | i <= k})`,
  REWRITE_TAC[LE] THEN SET_TAC[]);;

let HAS_SIZE_NUMSEG_LE = prove
 (`!n. {m | m <= n} HAS_SIZE (n + 1)`,
  REWRITE_TAC[GSYM LT_SUC_LE; HAS_SIZE_NUMSEG_LT; ADD1]);;

let FINITE_NUMSEG_LE = prove
 (`!n. FINITE {m | m <= n}`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

let CARD_NUMSEG_LE = prove
 (`!n. CARD {m | m <= n} = n + 1`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

let num_FINITE = prove
 (`!s:num->bool. FINITE s <=> ?a. !x. x IN s ==> x <= a`,
  GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`s:num->bool`,`s:num->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[LE_CASES; LE_TRANS];
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:num | m <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]]);;

let num_FINITE_AVOID = prove
 (`!s:num->bool. FINITE(s) ==> ?a. ~(a IN s)`,
  MESON_TAC[num_FINITE; LT; NOT_LT]);;

let num_INFINITE_EQ = prove
 (`!s:num->bool. INFINITE s <=> !N. ?n. N <= n /\ n IN s`,
  GEN_TAC THEN REWRITE_TAC[INFINITE; num_FINITE] THEN
  MESON_TAC[NOT_LE; LT_IMP_LE; LE_SUC_LT]);;

let num_INFINITE = prove
 (`INFINITE(:num)`,
  REWRITE_TAC[INFINITE] THEN MESON_TAC[num_FINITE_AVOID; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Set of strings is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let string_INFINITE = prove
 (`INFINITE(:string)`,
  MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o ISPEC `LENGTH:string->num` o MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN MESON_TAC[LENGTH_REPLICATE]);;

(* ------------------------------------------------------------------------- *)
(* Non-trivial intervals of reals are infinite.                              *)
(* ------------------------------------------------------------------------- *)

let FINITE_REAL_INTERVAL = prove
 (`(!a. ~FINITE {x:real | a < x}) /\
   (!a. ~FINITE {x:real | a <= x}) /\
   (!b. ~FINITE {x:real | x < b}) /\
   (!b. ~FINITE {x:real | x <= b}) /\
   (!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a < x /\ x <= b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x <= b} <=> b <= a)`,
  SUBGOAL_THEN `!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    ASM_CASES_TAC `a:real < b` THEN
    ASM_SIMP_TAC[REAL_ARITH `~(a:real < b) ==> ~(a < x /\ x < b)`] THEN
    REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (\n. a + (b - a) / (&n + &2)) (:num)`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LT_ADDR; REAL_ARITH `a + x / y < b <=> x / y < b - a`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_LDIV_EQ; NOT_IMP;
                 REAL_ARITH `&0:real < &n + &2`] THEN
    REWRITE_TAC[REAL_ARITH `x:real < x * (n + &2) <=> &0 < x * (n + &1)`] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_MUL; REAL_ARITH `&0:real < &n + &1`] THEN
    MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `a < b ==> (a + (b - a) / (&n + &2) = a + (b - a) / (&m + &2) <=>
                 &n:real = &m)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `{x:real | a < x /\ x < a + &1}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | a < x /\ x < a + &1}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | b - &1 < x /\ x < b}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | b - &1 < x /\ x < b}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH
     `a:real <= x /\ x < b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a`];
    REWRITE_TAC[REAL_ARITH
     `a:real < x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = b`];
    ASM_CASES_TAC `b:real = a` THEN
    ASM_SIMP_TAC[REAL_LE_ANTISYM; REAL_LE_REFL; SING_GSPEC; FINITE_SING] THEN
    ASM_SIMP_TAC[REAL_ARITH
     `~(b:real = a) ==>
        (a <= x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a \/
        ~(b <= a) /\ x = b)`]] THEN
  ASM_REWRITE_TAC[FINITE_UNION; SET_RULE
   `{x | p x \/ q x} = {x | p x} UNION {x | q x}`] THEN
  ASM_CASES_TAC `b:real <= a` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]);;

let real_INFINITE = prove
 (`INFINITE(:real)`,
  REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(MP_TAC o SPEC `{x:real | &0 <= x}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  REWRITE_TAC[FINITE_REAL_INTERVAL; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Indexing of finite sets and enumeration of subsets of N in order.         *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_INDEX = prove
 (`!s n. s HAS_SIZE n
         ==> ?f:num->A. (!m. m < n ==> f(m) IN s) /\
                        (!x. x IN s ==> ?!m. m < n /\ (f m = x))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  SIMP_TAC[HAS_SIZE_0; HAS_SIZE_SUC; LT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `s:A->bool` THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) (MP_TAC o SPEC `a:A`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\m:num. if m < n then f(m) else a:A` THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
  ASM_CASES_TAC `a:A = x` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[LT_REFL; IN_DELETE]);;

let INFINITE_ENUMERATE = prove
 (`!s:num->bool.
       INFINITE s
       ==> ?r:num->num. (!m n. m < n ==> r(m) < r(n)) /\
                        IMAGE r (:num) = s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n:num. ?x. n <= x /\ x IN s` MP_TAC THENL
   [ASM_MESON_TAC[INFINITE; num_FINITE; LT_IMP_LE; NOT_LE];
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [num_WOP]] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  REWRITE_TAC[TAUT `p ==> ~(q /\ r) <=> q /\ p ==> ~r`] THEN
  X_GEN_TAC `next:num->num` THEN STRIP_TAC THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(f(0) = next 0) /\ (!n. f(SUC n) = next(f n + 1))` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT] THEN
    ASM_MESON_TAC[ARITH_RULE `m <= n /\ n + 1 <= p ==> m < p`; LE_LT];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; FORALL_IN_IMAGE; SUBSET] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN CONJ_TAC THENL
   [INDUCT_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?m:num. m < n /\ m IN s` THENL
   [MP_TAC(SPEC `\m:num. m < n /\ m IN s` num_MAX) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
     `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
    CONJ_TAC THENL [MESON_TAC[LT_IMP_LE]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?q. p = (r:num->num) q` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[]; EXISTS_TAC `SUC q`] THEN
    ASM_REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN
    ASM_MESON_TAC[NOT_LE; ARITH_RULE `r < p <=> r + 1 <= p`];
    EXISTS_TAC `0` THEN ASM_REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN
    ASM_MESON_TAC[LE_0]]);;

let INFINITE_ENUMERATE_EQ = prove
 (`!s:num->bool.
     INFINITE s <=> ?r. (!m n:num. m < n ==> r m < r n) /\ IMAGE r (:num) = s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[INFINITE_ENUMERATE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFINITE_IMAGE THEN
  REWRITE_TAC[num_INFINITE; IN_UNIV] THEN
  MATCH_MP_TAC WLOG_LT THEN ASM_MESON_TAC[LT_REFL]);;

let INFINITE_ENUMERATE_SUBSET = prove
 (`!s. INFINITE s <=>
       ?f:num->A. (!x. f x IN s) /\ (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `?f:num->A. !n. f n IN s /\ !m. m < n ==> ~(f m = f n)`
    MP_TAC THENL
     [MATCH_MP_TAC(MATCH_MP WF_REC_EXISTS WF_num) THEN SIMP_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`f:num->A`; `n:num`] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `IMAGE (f:num->A) {m | m < n}` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] INFINITE_DIFF_FINITE)) THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
      DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WLOG_LT THEN ASM SET_TAC[]];
     MATCH_MP_TAC INFINITE_SUPERSET THEN
     EXISTS_TAC `IMAGE (f:num->A) (:num)` THEN
     ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
     ASM_MESON_TAC[INFINITE_IMAGE_INJ; num_INFINITE]]);;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let set_of_list = new_recursive_definition list_RECURSION
  `(set_of_list ([]:A list) = {}) /\
   (set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))`;;

let list_of_set = new_definition
  `list_of_set s = @l:A list. set_of_list l = s /\ LENGTH l = CARD s`;;

let LIST_OF_SET_PROPERTIES = prove
 (`!s:A->bool. FINITE(s)
               ==> (set_of_list(list_of_set s) = s) /\
                   (LENGTH(list_of_set s) = CARD s)`,
  REWRITE_TAC[list_of_set] THEN
  CONV_TAC(BINDER_CONV(RAND_CONV SELECT_CONV)) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `[]:A list` THEN REWRITE_TAC[CARD_CLAUSES; LENGTH; set_of_list];
    EXISTS_TAC `CONS (x:A) l` THEN ASM_REWRITE_TAC[LENGTH] THEN
    ASM_REWRITE_TAC[set_of_list] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC
     [MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
    ASM_REWRITE_TAC[]]);;

let SET_OF_LIST_OF_SET = prove
 (`!s:A->bool. FINITE(s) ==> (set_of_list(list_of_set s) = s)`,
  MESON_TAC[LIST_OF_SET_PROPERTIES]);;

let LENGTH_LIST_OF_SET = prove
 (`!s:A->bool. FINITE(s) ==> (LENGTH(list_of_set s) = CARD s)`,
  MESON_TAC[LIST_OF_SET_PROPERTIES]);;

let MEM_LIST_OF_SET = prove
 (`!s:A->bool. FINITE(s) ==> !x. MEM x (list_of_set s) <=> x IN s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SET_OF_LIST_OF_SET) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (BINDER_CONV o funpow 2 RAND_CONV)
    [GSYM th]) THEN
  SPEC_TAC(`list_of_set(s:A->bool)`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; set_of_list; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let FINITE_SET_OF_LIST = prove
 (`!l:A list. FINITE(set_of_list l)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[set_of_list; FINITE_RULES]);;

let IN_SET_OF_LIST = prove
 (`!x l:A list. x IN (set_of_list l) <=> MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; MEM; set_of_list] THEN
  ASM_MESON_TAC[]);;

let SET_OF_LIST_APPEND = prove
 (`!l1 l2:A list.
        set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_UNION; MEM_APPEND]);;

let SET_OF_LIST_MAP = prove
 (`!(f:A->B) l. set_of_list(MAP f l) = IMAGE f (set_of_list l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[set_of_list; MAP; IMAGE_CLAUSES]);;

let SET_OF_LIST_EQ_EMPTY = prove
 (`!l:A list. set_of_list l = {} <=> l = []`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[set_of_list; NOT_CONS_NIL; NOT_INSERT_EMPTY]);;

let LIST_OF_SET_EMPTY = prove
 (`list_of_set {}:A list = []`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
  SIMP_TAC[LENGTH_LIST_OF_SET; FINITE_EMPTY; CARD_CLAUSES]);;

let LIST_OF_SET_SING = prove
 (`!a:A. list_of_set {a} = [a]`,
  GEN_TAC THEN REWRITE_TAC[list_of_set] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  SIMP_TAC[LENGTH; CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY; NOT_SUC] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[LENGTH; set_of_list; CONS_11; SUC_INJ; NOT_CONS_NIL; NOT_SUC] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Mappings from finite set enumerations to lists (no "setification").       *)
(* ------------------------------------------------------------------------- *)

let dest_setenum =
  let fn = splitlist (dest_binary "INSERT") in
  fun tm -> let l,n = fn tm in
            if is_const n && fst(dest_const n) = "EMPTY" then l
            else failwith "dest_setenum: not a finite set enumeration";;

let is_setenum = can dest_setenum;;

let mk_setenum =
  let insert_atm = `(INSERT):A->(A->bool)->(A->bool)`
  and nil_atm = `(EMPTY):A->bool` in
  fun (l,ty) ->
    let insert_tm = inst [ty,aty] insert_atm
    and nil_tm = inst [ty,aty] nil_atm in
    itlist (mk_binop insert_tm) l nil_tm;;

let mk_fset l = mk_setenum(l,type_of(hd l));;

(* ------------------------------------------------------------------------- *)
(* Pairwise property over sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let pairwise = new_definition
  `pairwise r (s:A->bool) <=> !x y. x IN s /\ y IN s /\ ~(x = y) ==> r x y`;;

let PAIRWISE_EMPTY = prove
 (`!r:A->A->bool. pairwise r {} <=> T`,
  REWRITE_TAC[pairwise; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let PAIRWISE_SING = prove
 (`!r x:A. pairwise r {x} <=> T`,
  REWRITE_TAC[pairwise; IN_SING] THEN MESON_TAC[]);;

let PAIRWISE_IMP = prove
 (`!P Q s:A->bool.
        pairwise P s /\
        (!x y. x IN s /\ y IN s /\ P x y /\ ~(x = y) ==> Q x y)
        ==> pairwise Q s`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

let PAIRWISE_MONO = prove
 (`!(r:A->A->bool) s t. pairwise r s /\ t SUBSET s ==> pairwise r t`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

let PAIRWISE_AND = prove
 (`!R R' s. pairwise R s /\ pairwise R' s <=>
            pairwise (\x y:A. R x y /\ R' x y) s`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

let PAIRWISE_INSERT = prove
 (`!r x s.
        pairwise r (x INSERT s) <=>
        (!y:A. y IN s /\ ~(y = x) ==> r x y /\ r y x) /\
        pairwise r s`,
  REWRITE_TAC[pairwise; IN_INSERT] THEN MESON_TAC[]);;

let PAIRWISE_INSERT_SYMMETRIC = prove
 (`!r (x:A) s.
        (!y. y IN s ==> (r x y <=> r y x))
        ==> (pairwise r (x INSERT s) <=>
             (!y. y IN s /\ ~(y = x) ==> r x y) /\ pairwise r s)`,
  REWRITE_TAC[PAIRWISE_INSERT] THEN MESON_TAC[]);;

let PAIRWISE_IMAGE = prove
 (`!r (f:A->B).
        pairwise r (IMAGE f s) <=>
        pairwise (\x y. ~(f x = f y) ==> r (f x) (f y)) s`,
  REWRITE_TAC[pairwise; IN_IMAGE] THEN MESON_TAC[]);;

let PAIRWISE_UNION = prove
 (`!R s t. pairwise R (s UNION t) <=>
           pairwise R s /\ pairwise R t /\
           (!x y:A. x IN s DIFF t /\ y IN t DIFF s ==> R x y /\ R y x)`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

let PAIRWISE_CHAIN_UNIONS = prove
 (`!R:A->A->bool c.
        (!s. s IN c ==> pairwise R s) /\
        (!s t. s IN c /\ t IN c ==> s SUBSET t \/ t SUBSET s)
        ==> pairwise R (UNIONS c)`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

let DIFF_UNIONS_PAIRWISE_DISJOINT = prove
 (`!s t:(A->bool)->bool.
        pairwise DISJOINT s /\ t SUBSET s
        ==> UNIONS s DIFF UNIONS t = UNIONS(s DIFF t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `t UNION u = s /\ DISJOINT t u ==> s DIFF t = u`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM UNIONS_UNION] THEN AP_TERM_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
    REWRITE_TAC[DISJOINT; IN_DIFF] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN ASM_MESON_TAC[]]);;

let INTER_UNIONS_PAIRWISE_DISJOINT = prove
 (`!s t:(A->bool)->bool.
        pairwise DISJOINT (s UNION t)
        ==> UNIONS s INTER UNIONS t = UNIONS(s INTER t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE; UNIONS_IMAGE] THEN
  GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
  REWRITE_TAC[pairwise; IN_UNIONS; IN_INTER; IN_ELIM_THM; IN_UNION] THEN
  DISCH_TAC THEN X_GEN_TAC `z:A` THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THENL [REWRITE_TAC[LEFT_IMP_EXISTS_THM]; MESON_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `v:A->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:A->bool`; `v:A->bool`]) THEN
  ASM_CASES_TAC `u:A->bool = v` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM SET_TAC[]]);;

let PSUBSET_UNIONS_PAIRWISE_DISJOINT = prove
 (`!u v:(A->bool)->bool.
        pairwise DISJOINT v /\ u PSUBSET (v DELETE {})
        ==> UNIONS u PSUBSET UNIONS v`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `u SUBSET v /\ ~(v DIFF u = {}) ==> u PSUBSET v`) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
      DIFF_UNIONS_PAIRWISE_DISJOINT o lhand o rand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EMPTY_UNIONS] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [PSUBSET_ALT]) THEN
  REWRITE_TAC[IN_DELETE; IN_DIFF] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful idioms for being a suitable union/intersection of somethings.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("UNION_OF",(20,"right"));;
parse_as_infix("INTERSECTION_OF",(20,"right"));;

let UNION_OF = new_definition
 `P UNION_OF Q =
   \s:A->bool. ?u. P u /\ (!c. c IN u ==> Q c) /\ UNIONS u = s`;;

let INTERSECTION_OF = new_definition
 `P INTERSECTION_OF Q =
   \s:A->bool. ?u. P u /\ (!c. c IN u ==> Q c) /\ INTERS u = s`;;

let UNION_OF_INC = prove
 (`!P Q s:A->bool. P {s} /\ Q s ==> (P UNION_OF Q) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_OF] THEN
  EXISTS_TAC `{s:A->bool}` THEN ASM_SIMP_TAC[UNIONS_1; IN_SING]);;

let INTERSECTION_OF_INC = prove
 (`!P Q s:A->bool. P {s} /\ Q s ==> (P INTERSECTION_OF Q) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERSECTION_OF] THEN
  EXISTS_TAC `{s:A->bool}` THEN ASM_SIMP_TAC[INTERS_1; IN_SING]);;

let UNION_OF_MONO = prove
 (`!P Q Q' s:A->bool.
        (P UNION_OF Q) s /\ (!x. Q x ==> Q' x) ==> (P UNION_OF Q') s`,
  REWRITE_TAC[UNION_OF] THEN MESON_TAC[]);;

let INTERSECTION_OF_MONO = prove
 (`!P Q Q' s:A->bool.
        (P INTERSECTION_OF Q) s /\ (!x. Q x ==> Q' x)
        ==> (P INTERSECTION_OF Q') s`,
  REWRITE_TAC[INTERSECTION_OF] THEN MESON_TAC[]);;

let FORALL_UNION_OF = prove
 (`(!s:A->bool. (P UNION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(UNIONS t))`,
  REWRITE_TAC[UNION_OF] THEN MESON_TAC[]);;

let FORALL_INTERSECTION_OF = prove
 (`(!s:A->bool. (P INTERSECTION_OF Q) s ==> R s) <=>
   (!t. P t /\ (!c. c IN t ==> Q c) ==> R(INTERS t))`,
  REWRITE_TAC[INTERSECTION_OF] THEN MESON_TAC[]);;

let UNION_OF_EMPTY = prove
 (`!P Q:(A->bool)->bool. P {} ==> (P UNION_OF Q) {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_OF] THEN
  EXISTS_TAC `{}:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY]);;

let INTERSECTION_OF_EMPTY = prove
 (`!P Q:(A->bool)->bool. P {} ==> (P INTERSECTION_OF Q) UNIV`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERSECTION_OF] THEN
  EXISTS_TAC `{}:(A->bool)->bool` THEN
  ASM_REWRITE_TAC[INTERS_0; NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* The ARBITRARY and FINITE cases of UNION_OF / INTERSECTION_OF              *)
(* ------------------------------------------------------------------------- *)

let ARBITRARY = new_definition
 `ARBITRARY (s:(A->bool)->bool) <=> T`;;

let ARBITRARY_UNION_OF_ALT = prove
 (`!B s:A->bool.
        (ARBITRARY UNION_OF B) s <=>
        !x. x IN s ==>  ?u. u IN B /\ x IN u /\ u SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[FORALL_AND_THM; TAUT
   `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  REWRITE_TAC[FORALL_UNION_OF; ARBITRARY] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[ARBITRARY; UNION_OF] THEN
  EXISTS_TAC `{u:A->bool | u IN B /\ u SUBSET s}` THEN ASM SET_TAC[]);;

let ARBITRARY_UNION_OF_EMPTY = prove
 (`!P:(A->bool)->bool. (ARBITRARY UNION_OF P) {}`,
  SIMP_TAC[UNION_OF_EMPTY; ARBITRARY]);;

let ARBITRARY_INTERSECTION_OF_EMPTY = prove
 (`!P:(A->bool)->bool. (ARBITRARY INTERSECTION_OF P) UNIV`,
  SIMP_TAC[INTERSECTION_OF_EMPTY; ARBITRARY]);;

let ARBITRARY_UNION_OF_INC = prove
 (`!P s:A->bool. P s ==> (ARBITRARY UNION_OF P) s`,
  SIMP_TAC[UNION_OF_INC; ARBITRARY]);;

let ARBITRARY_INTERSECTION_OF_INC = prove
 (`!P s:A->bool. P s ==> (ARBITRARY INTERSECTION_OF P) s`,
  SIMP_TAC[INTERSECTION_OF_INC; ARBITRARY]);;

let ARBITRARY_UNION_OF_COMPLEMENT = prove
 (`!P s. (ARBITRARY UNION_OF P) s <=>
         (ARBITRARY INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNION_OF; INTERSECTION_OF] THEN
  EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\c. (:A) DIFF c) u` THEN
  ASM_SIMP_TAC[ARBITRARY; FORALL_IN_IMAGE; COMPL_COMPL] THEN
  ONCE_REWRITE_TAC[UNIONS_INTERS; INTERS_UNIONS] THEN
  REWRITE_TAC[SET_RULE `{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s`] THEN
  ASM_REWRITE_TAC[IMAGE_ID; COMPL_COMPL]);;

let ARBITRARY_INTERSECTION_OF_COMPLEMENT = prove
 (`!P s. (ARBITRARY INTERSECTION_OF P) s <=>
         (ARBITRARY UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`,
  REWRITE_TAC[ARBITRARY_UNION_OF_COMPLEMENT] THEN
  REWRITE_TAC[ETA_AX; COMPL_COMPL]);;

let ARBITRARY_UNION_OF_IDEMPOT = prove
 (`!P:(A->bool)->bool.
        ARBITRARY UNION_OF ARBITRARY UNION_OF P = ARBITRARY UNION_OF P`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:A->bool` THEN
  EQ_TAC THEN REWRITE_TAC[ARBITRARY_UNION_OF_INC] THEN
  REWRITE_TAC[UNION_OF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:(A->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(A->bool)->(A->bool)->bool` THEN DISCH_TAC THEN
  EXISTS_TAC
    `IMAGE SND {s,t | s IN u /\ t IN (f:(A->bool)->(A->bool)->bool) s}` THEN
  ASM_SIMP_TAC[ARBITRARY] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[UNIONS_IMAGE]] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM SET_TAC[]);;

let ARBITRARY_INTERSECTION_OF_IDEMPOT = prove
 (`!P:(A->bool)->bool.
        ARBITRARY INTERSECTION_OF ARBITRARY INTERSECTION_OF P =
        ARBITRARY INTERSECTION_OF P`,
  REWRITE_TAC[COMPL_COMPL; ETA_AX; REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX]
              ARBITRARY_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[ARBITRARY_UNION_OF_IDEMPOT]);;

let ARBITRARY_UNION_OF_UNIONS = prove
 (`!P u:(A->bool)->bool.
        (!s. s IN u ==> (ARBITRARY UNION_OF P) s)
        ==> (ARBITRARY UNION_OF P) (UNIONS u)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ARBITRARY_UNION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[UNION_OF] THEN REWRITE_TAC[] THEN
  EXISTS_TAC `u:(A->bool)->bool` THEN ASM_REWRITE_TAC[ARBITRARY]);;

let ARBITRARY_UNION_OF_UNION = prove
 (`!P s t:A->bool.
        (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
        ==> (ARBITRARY UNION_OF P) (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
  ASM_REWRITE_TAC[ARBITRARY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[ARBITRARY; NOT_IN_EMPTY]);;

let ARBITRARY_INTERSECTION_OF_INTERS = prove
 (`!P u:(A->bool)->bool.
        (!s. s IN u ==> (ARBITRARY INTERSECTION_OF P) s)
        ==> (ARBITRARY INTERSECTION_OF P) (INTERS u)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM ARBITRARY_INTERSECTION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[INTERSECTION_OF] THEN REWRITE_TAC[] THEN
  EXISTS_TAC `u:(A->bool)->bool` THEN ASM_REWRITE_TAC[ARBITRARY]);;

let ARBITRARY_INTERSECTION_OF_INTER = prove
 (`!P s t:A->bool.
        (ARBITRARY INTERSECTION_OF P) s /\ (ARBITRARY INTERSECTION_OF P) t
        ==> (ARBITRARY INTERSECTION_OF P) (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC ARBITRARY_INTERSECTION_OF_INTERS THEN
  ASM_REWRITE_TAC[ARBITRARY; FORALL_IN_INSERT] THEN
  REWRITE_TAC[ARBITRARY; NOT_IN_EMPTY]);;

let ARBITRARY_UNION_OF_INTER_EQ = prove
 (`!P:(A->bool)->bool.
        (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
               ==> (ARBITRARY UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY UNION_OF P) (s INTER t))`,
  GEN_TAC THEN
  EQ_TAC THENL [MESON_TAC[ARBITRARY_UNION_OF_INC]; DISCH_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_OF] THEN
  REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[INTER_UNIONS] THEN
  REPLICATE_TAC 2
   (MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; ARBITRARY; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC));;

let ARBITRARY_UNION_OF_INTER = prove
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
                   ==> (ARBITRARY UNION_OF P) (s INTER t))`,
  REWRITE_TAC[ARBITRARY_UNION_OF_INTER_EQ] THEN
  MESON_TAC[ARBITRARY_UNION_OF_INC]);;

let ARBITRARY_INTERSECTION_OF_UNION_EQ = prove
 (`!P:(A->bool)->bool.
        (!s t. (ARBITRARY INTERSECTION_OF P) s /\
               (ARBITRARY INTERSECTION_OF P) t
               ==> (ARBITRARY INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))`,
  ONCE_REWRITE_TAC[ARBITRARY_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE
    `UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)`] THEN
  REWRITE_TAC[MESON[COMPL_COMPL] `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[ARBITRARY_UNION_OF_INTER_EQ] THEN
  REWRITE_TAC[SET_RULE
   `s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))`] THEN
  REWRITE_TAC[MESON[COMPL_COMPL] `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[COMPL_COMPL]);;

let ARBITRARY_INTERSECTION_OF_UNION = prove
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (ARBITRARY INTERSECTION_OF P) s /\
                   (ARBITRARY INTERSECTION_OF P) t
                   ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))`,
  REWRITE_TAC[ARBITRARY_INTERSECTION_OF_UNION_EQ] THEN
  MESON_TAC[ARBITRARY_INTERSECTION_OF_INC]);;

let FINITE_UNION_OF_EMPTY = prove
 (`!P:(A->bool)->bool. (FINITE UNION_OF P) {}`,
  SIMP_TAC[UNION_OF_EMPTY; FINITE_EMPTY]);;

let FINITE_INTERSECTION_OF_EMPTY = prove
 (`!P:(A->bool)->bool. (FINITE INTERSECTION_OF P) UNIV`,
  SIMP_TAC[INTERSECTION_OF_EMPTY; FINITE_EMPTY]);;

let FINITE_UNION_OF_INC = prove
 (`!P s:A->bool. P s ==> (FINITE UNION_OF P) s`,
  SIMP_TAC[UNION_OF_INC; FINITE_SING]);;

let FINITE_INTERSECTION_OF_INC = prove
 (`!P s:A->bool. P s ==> (FINITE INTERSECTION_OF P) s`,
  SIMP_TAC[INTERSECTION_OF_INC; FINITE_SING]);;

let FINITE_UNION_OF_COMPLEMENT = prove
 (`!P s. (FINITE UNION_OF P) s <=>
         (FINITE INTERSECTION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNION_OF; INTERSECTION_OF] THEN
  EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\c. (:A) DIFF c) u` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; COMPL_COMPL] THEN
  ONCE_REWRITE_TAC[UNIONS_INTERS; INTERS_UNIONS] THEN
  REWRITE_TAC[SET_RULE `{f y | y IN IMAGE g s} = IMAGE (\x. f(g x)) s`] THEN
  ASM_REWRITE_TAC[IMAGE_ID; COMPL_COMPL]);;

let FINITE_INTERSECTION_OF_COMPLEMENT = prove
 (`!P s. (FINITE INTERSECTION_OF P) s <=>
         (FINITE UNION_OF (\s. P((:A) DIFF s))) ((:A) DIFF s)`,
  REWRITE_TAC[FINITE_UNION_OF_COMPLEMENT] THEN
  REWRITE_TAC[ETA_AX; COMPL_COMPL]);;

let FINITE_UNION_OF_IDEMPOT = prove
 (`!P:(A->bool)->bool.
        FINITE UNION_OF FINITE UNION_OF P = FINITE UNION_OF P`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:A->bool` THEN
  EQ_TAC THEN REWRITE_TAC[FINITE_UNION_OF_INC] THEN
  REWRITE_TAC[UNION_OF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:(A->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (SUBST1_TAC o SYM)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(A->bool)->(A->bool)->bool` THEN DISCH_TAC THEN
  EXISTS_TAC
    `IMAGE SND {s,t | s IN u /\ t IN (f:(A->bool)->(A->bool)->bool) s}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_PRODUCT_DEPENDENT] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[UNIONS_IMAGE]] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM SET_TAC[]);;

let FINITE_INTERSECTION_OF_IDEMPOT = prove
 (`!P:(A->bool)->bool.
        FINITE INTERSECTION_OF FINITE INTERSECTION_OF P =
        FINITE INTERSECTION_OF P`,
  REWRITE_TAC[COMPL_COMPL; ETA_AX; REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX]
              FINITE_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[FINITE_UNION_OF_IDEMPOT]);;

let FINITE_UNION_OF_UNIONS = prove
 (`!P u:(A->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE UNION_OF P) s)
        ==> (FINITE UNION_OF P) (UNIONS u)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM FINITE_UNION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[UNION_OF] THEN REWRITE_TAC[] THEN
  EXISTS_TAC `u:(A->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let FINITE_UNION_OF_UNION = prove
 (`!P s t:A->bool.
        (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
        ==> (FINITE UNION_OF P) (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC FINITE_UNION_OF_UNIONS THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
  REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY]);;

let FINITE_INTERSECTION_OF_INTERS = prove
 (`!P u:(A->bool)->bool.
        FINITE u /\ (!s. s IN u ==> (FINITE INTERSECTION_OF P) s)
        ==> (FINITE INTERSECTION_OF P) (INTERS u)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM FINITE_INTERSECTION_OF_IDEMPOT] THEN
  ONCE_REWRITE_TAC[INTERSECTION_OF] THEN REWRITE_TAC[] THEN
  EXISTS_TAC `u:(A->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let FINITE_INTERSECTION_OF_INTER = prove
 (`!P s t:A->bool.
        (FINITE INTERSECTION_OF P) s /\ (FINITE INTERSECTION_OF P) t
        ==> (FINITE INTERSECTION_OF P) (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC FINITE_INTERSECTION_OF_INTERS THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN
  REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY]);;

let FINITE_UNION_OF_INTER_EQ = prove
 (`!P:(A->bool)->bool.
        (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t)) <=>
        (!s t. P s /\ P t ==> (FINITE UNION_OF P) (s INTER t))`,
  GEN_TAC THEN
  EQ_TAC THENL [MESON_TAC[FINITE_UNION_OF_INC]; DISCH_TAC] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [UNION_OF] THEN
  REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[INTER_UNIONS] THEN
  REPLICATE_TAC 2
   (MATCH_MP_TAC FINITE_UNION_OF_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC));;

let FINITE_UNION_OF_INTER = prove
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> (!s t. (FINITE UNION_OF P) s /\ (FINITE UNION_OF P) t
                   ==> (FINITE UNION_OF P) (s INTER t))`,
  REWRITE_TAC[FINITE_UNION_OF_INTER_EQ] THEN
  MESON_TAC[FINITE_UNION_OF_INC]);;

let FINITE_INTERSECTION_OF_UNION_EQ = prove
 (`!P:(A->bool)->bool.
        (!s t. (FINITE INTERSECTION_OF P) s /\
               (FINITE INTERSECTION_OF P) t
               ==> (FINITE INTERSECTION_OF P) (s UNION t)) <=>
        (!s t. P s /\ P t ==> (FINITE INTERSECTION_OF P) (s UNION t))`,
  ONCE_REWRITE_TAC[FINITE_INTERSECTION_OF_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE
    `UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)`] THEN
  REWRITE_TAC[MESON[COMPL_COMPL] `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[FINITE_UNION_OF_INTER_EQ] THEN
  REWRITE_TAC[SET_RULE
   `s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))`] THEN
  REWRITE_TAC[MESON[COMPL_COMPL] `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[COMPL_COMPL]);;

let FINITE_INTERSECTION_OF_UNION = prove
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s UNION t))
        ==> (!s t. (FINITE INTERSECTION_OF P) s /\
                   (FINITE INTERSECTION_OF P) t
                   ==> (FINITE INTERSECTION_OF P) (s UNION t))`,
  REWRITE_TAC[FINITE_INTERSECTION_OF_UNION_EQ] THEN
  MESON_TAC[FINITE_INTERSECTION_OF_INC]);;

(* ------------------------------------------------------------------------- *)
(* Some additional properties of "set_of_list".                              *)
(* ------------------------------------------------------------------------- *)

let CARD_SET_OF_LIST_LE = prove
 (`!l:A list. CARD(set_of_list l) <= LENGTH l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; set_of_list; CARD_CLAUSES; FINITE_SET_OF_LIST] THEN
  ASM_ARITH_TAC);;

let HAS_SIZE_SET_OF_LIST = prove
 (`!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\x y:A. ~(x = y)) l`,
  REWRITE_TAC[HAS_SIZE; FINITE_SET_OF_LIST] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LENGTH; set_of_list; PAIRWISE; ALL;
               FINITE_SET_OF_LIST; GSYM ALL_MEM; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  ASM_MESON_TAC[CARD_SET_OF_LIST_LE; ARITH_RULE `~(SUC n <= n)`]);;

(* ------------------------------------------------------------------------- *)
(* Classic result on function of finite set into itself.                     *)
(* ------------------------------------------------------------------------- *)

let SURJECTIVE_IFF_INJECTIVE_GEN = prove
 (`!s t f:A->B.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\ (IMAGE f s) SUBSET t
        ==> ((!y. y IN t ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `CARD s <= CARD (IMAGE (f:A->B) (s DELETE y))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_DELETE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `CARD(s DELETE (y:A))` THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE] THEN
      ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `x - 1 < x <=> ~(x = 0)`] THEN
      ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY]];
    SUBGOAL_THEN `IMAGE (f:A->B) s = t` MP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[EXTENSION; IN_IMAGE]] THEN
    ASM_MESON_TAC[CARD_SUBSET_EQ; CARD_IMAGE_INJ]]);;

let SURJECTIVE_IFF_INJECTIVE = prove
 (`!s f:A->A.
        FINITE s /\ (IMAGE f s) SUBSET s
        ==> ((!y. y IN s ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN]);;

let IMAGE_IMP_INJECTIVE_GEN = prove
 (`!s t f:A->B.
        FINITE s /\ (CARD s = CARD t) /\ (IMAGE f s = t)
        ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  MP_TAC(ISPECL [`s:A->bool`; `t:B->bool`; `f:A->B`]
                SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC[SUBSET_REFL; FINITE_IMAGE] THEN
  ASM_MESON_TAC[EXTENSION; IN_IMAGE]);;

let IMAGE_IMP_INJECTIVE = prove
 (`!s f:A->A.
        FINITE s /\ IMAGE f s = s
        ==> !x y. x IN s /\ y IN s /\ f x = f y ==> x = y`,
  MESON_TAC[IMAGE_IMP_INJECTIVE_GEN]);;

let HAS_SIZE_IMAGE_INJ_RESTRICT = prove
 (`!(f:A->B) s t P n.
      FINITE s /\ FINITE t /\ CARD s = CARD t /\
      IMAGE f s SUBSET t /\
      (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
      {x | x IN s /\ P(f x)} HAS_SIZE n
      ==> {x | x IN t /\ P x} HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN t /\ P x} = IMAGE (f:A->B) {x | x IN s /\ P(f x)}`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`s:A->bool`; `t:B->bool`; `f:A->B`]
        SURJECTIVE_IFF_INJECTIVE_GEN) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Converse relation between cardinality and injection.                      *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_INJ = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s <= CARD t
   ==> ?f:A->B. (IMAGE f s) SUBSET t /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[CARD_CLAUSES; LE; NOT_SUC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `t:B->bool`] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LE_SUC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:B->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:A. if z = x then (y:B) else f(z)` THEN
  REWRITE_TAC[IN_INSERT; SUBSET; IN_IMAGE] THEN
  ASM_MESON_TAC[SUBSET; IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Occasionally handy rewrites.                                              *)
(* ------------------------------------------------------------------------- *)

let FORALL_IN_CLAUSES = prove
 (`(!P. (!x:A. x IN {} ==> P x) <=> T) /\
   (!P a s. (!x:A. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let EXISTS_IN_CLAUSES = prove
 (`(!P. (?x:A. x IN {} /\ P x) <=> F) /\
   (!P a s. (?x:A. x IN (a INSERT s) /\ P x) <=> P a \/ (?x. x IN s /\ P x))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Injectivity and surjectivity of image and preimage under a function.      *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_ON_IMAGE = prove
 (`!f:A->B u.
    (!s t. s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t ==> s = t) <=>
    (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC; SET_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{x:A}`; `{y:A}`]) THEN
  ASM_REWRITE_TAC[SING_SUBSET; IMAGE_CLAUSES] THEN SET_TAC[]);;

let INJECTIVE_IMAGE = prove
 (`!f:A->B.
    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN MP_TAC(ISPECL [`f:A->B`; `(:A)`] INJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

let SURJECTIVE_ON_IMAGE = prove
 (`!f:A->B u v.
        (!t. t SUBSET v ==> ?s. s SUBSET u /\ IMAGE f s = t) <=>
        (!y. y IN v ==> ?x. x IN u /\ f x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{y:B}`) THEN ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `t:B->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{x | x IN u /\ (f:A->B) x IN t}` THEN ASM SET_TAC[]]);;

let SURJECTIVE_IMAGE = prove
 (`!f:A->B. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`] SURJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

let INJECTIVE_ON_PREIMAGE = prove
 (`!f:A->B s u.
        (!t t'. t SUBSET u /\ t' SUBSET u /\
                {x | x IN s /\ f x IN t} = {x | x IN s /\ f x IN t'}
                ==> t = t') <=>
        u SUBSET IMAGE f s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:B` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{y:B}`; `{}:B->bool`]) THEN ASM SET_TAC[]);;

let SURJECTIVE_ON_PREIMAGE = prove
 (`!f:A->B s u.
        (!k. k SUBSET s
             ==> ?t. t SUBSET u /\ {x | x IN s /\ f x IN t} = k) <=>
        IMAGE f s SUBSET u /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `{x:A}`) THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `{x:A}`) THEN ASM SET_TAC[]];
    X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN
    EXISTS_TAC `IMAGE (f:A->B) k` THEN ASM SET_TAC[]]);;

let INJECTIVE_PREIMAGE = prove
 (`!f:A->B.
        (!t t'. {x | f x IN t} = {x | f x IN t'} ==> t = t') <=>
        IMAGE f UNIV = UNIV`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`]
        INJECTIVE_ON_PREIMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN SET_TAC[]);;

let SURJECTIVE_PREIMAGE = prove
 (`!f:A->B. (!k. ?t. {x | f x IN t} = k) <=> (!x y. f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`]
        SURJECTIVE_ON_PREIMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Existence of bijections between two finite sets of same size.             *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_BIJECTION = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
                (!y. y IN t ==> ?x. x IN s /\ f x = y) /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  MP_TAC CARD_LE_INJ THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN] THEN
  MESON_TAC[SUBSET; IN_IMAGE]);;

let CARD_EQ_BIJECTIONS = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B g. (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
                  (!y. y IN t ==> g(y) IN s /\ f(g y) = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_BIJECTION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SURJECTIVE_ON_RIGHT_INVERSE] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

let CARD_EQ_BIJECTIONS_SPECIAL = prove
 (`!s t (a:A) (b:B).
         FINITE s /\ FINITE t /\ CARD s = CARD t /\ a IN s /\ b IN t
         ==> ?f g. f a = b /\ g b = a /\
                   (!x. x IN s ==> f x IN t /\ g (f x) = x) /\
                   (!y. y IN t ==> g y IN s /\ f (g y) = y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s DELETE (a:A)`; `t DELETE (b:B)`]
        CARD_EQ_BIJECTIONS) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; IN_DELETE; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:A->B`; `g:B->A`] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. if x = a then b else (f:A->B) x` THEN
  EXISTS_TAC `\y. if y = b then a else (g:B->A) y` THEN
  ASM_MESON_TAC[]);;

let BIJECTIONS_HAS_SIZE = prove
 (`!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        s HAS_SIZE n
        ==> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST_ALL_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_MESON_TAC[]]);;

let BIJECTIONS_HAS_SIZE_EQ = prove
 (`!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE
  [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] BIJECTIONS_HAS_SIZE) THENL
   [MAP_EVERY EXISTS_TAC [`f:A->B`; `g:B->A`];
    MAP_EVERY EXISTS_TAC [`g:B->A`; `f:A->B`]] THEN
  ASM_MESON_TAC[]);;

let BIJECTIONS_CARD_EQ = prove
 (`!s t f:A->B g.
        (FINITE s \/ FINITE t) /\
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> CARD s = CARD t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   MP_TAC (MP_TAC o MATCH_MP BIJECTIONS_HAS_SIZE_EQ)) THEN
  MESON_TAC[HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Transitive relation with finitely many predecessors is wellfounded.       *)
(* ------------------------------------------------------------------------- *)

let WF_FINITE = prove
 (`!(<<). (!x. ~(x << x)) /\ (!x y z. x << y /\ y << z ==> x << z) /\
          (!x:A. FINITE {y | y << x})
          ==> WF(<<)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!m n. m < n ==> (s:num->A) n << s m` ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:num->A` INFINITE_IMAGE_INJ) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[LT_CASES]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(:num)`) THEN
  REWRITE_TAC[num_INFINITE] THEN REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s(0) INSERT {y:A | y << s(0)}` THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_INSERT] THEN
  INDUCT_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[LT_0]);;

let WF_PSUBSET = prove
 (`!s:A->bool. FINITE s ==> WF (\t1 t2. t1 PSUBSET t2 /\ t2 SUBSET s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WF_FINITE THEN SIMP_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [SET_TAC[]; X_GEN_TAC `t:A->bool`] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons (more theory in Library/card.ml)                     *)
(* ------------------------------------------------------------------------- *)

let le_c = new_definition
  `s <=_c t <=>
   ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
            (!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y)`;;

let lt_c = new_definition
  `(s:A->bool) <_c (t:B->bool) <=> s <=_c t /\ ~(t <=_c s)`;;

let eq_c = new_definition
  `(s:A->bool) =_c (t:B->bool) <=>
   ?f. (!x. x IN s ==> f(x) IN t) /\
       !y. y IN t ==> ?!x. x IN s /\ (f x = y)`;;

let ge_c = new_definition
 `(s:A->bool) >=_c (t:B->bool) <=> t <=_c s`;;

let gt_c = new_definition
 `(s:A->bool) >_c (t:B->bool) <=> t <_c s`;;

let LE_C = prove
 (`!s t. s <=_c t <=> ?g:A->B. !x. x IN s ==> ?y. y IN t /\ g y = x`,
  REWRITE_TAC[le_c; INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE;
              RIGHT_IMP_EXISTS_THM; SKOLEM_THM; RIGHT_AND_EXISTS_THM] THEN
  MESON_TAC[]);;

let GE_C = prove
 (`!s t. s >=_c t <=> ?f:A->B. !y. y IN t ==> ?x. x IN s /\ (y = f x)`,
  REWRITE_TAC[ge_c; LE_C] THEN MESON_TAC[]);;

let COUNTABLE = new_definition
  `COUNTABLE (t:A->bool) <=> (:num) >=_c t`;;

(* ------------------------------------------------------------------------- *)
(* Supremum and infimum.                                                     *)
(* ------------------------------------------------------------------------- *)

let sup = new_definition
  `sup s = @a:real. (!x. x IN s ==> x <= a) /\
                    !b. (!x. x IN s ==> x <= b) ==> a <= b`;;

let SUP_EQ = prove
 (`!s t. (!b. (!x. x IN s ==> x <= b) <=> (!x. x IN t ==> x <= b))
         ==> sup s = sup t`,
  SIMP_TAC[sup]);;

let SUP = prove
 (`!s. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
       ==> (!x. x IN s ==> x <= sup s) /\
           !b. (!x. x IN s ==> x <= b) ==> sup s <= b`,
  REWRITE_TAC[sup] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_COMPLETE THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

let SUP_FINITE_LEMMA = prove
 (`!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> x <= b`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_TRANS]);;

let SUP_FINITE = prove
 (`!s. FINITE s /\ ~(s = {}) ==> (sup s) IN s /\ !x. x IN s ==> x <= sup s`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUP_FINITE_LEMMA) THEN
  ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TOTAL; SUP]);;

let REAL_LE_SUP_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (a <= sup s <=> ?x. x IN s /\ a <= x)`,
  MESON_TAC[SUP_FINITE; REAL_LE_TRANS]);;

let REAL_SUP_LE_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (sup s <= a <=> !x. x IN s ==> x <= a)`,
  MESON_TAC[SUP_FINITE; REAL_LE_TRANS]);;

let REAL_LT_SUP_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (a < sup s <=> ?x. x IN s /\ a < x)`,
  MESON_TAC[SUP_FINITE; REAL_LTE_TRANS]);;

let REAL_SUP_LT_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (sup s < a <=> !x. x IN s ==> x < a)`,
  MESON_TAC[SUP_FINITE; REAL_LET_TRANS]);;

let REAL_SUP_UNIQUE = prove
 (`!s b. (!x. x IN s ==> x <= b) /\
         (!b'. b' < b ==> ?x. x IN s /\ b' < x)
         ==> sup s = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sup] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[REAL_NOT_LE; REAL_LE_ANTISYM]);;

let REAL_SUP_LE = prove
 (`!b. ~(s = {}) /\ (!x. x IN s ==> x <= b) ==> sup s <= b`,
  MESON_TAC[SUP]);;

let REAL_SUP_LE_SUBSET = prove
 (`!s t. ~(s = {}) /\ s SUBSET t /\ (?b. !x. x IN t ==> x <= b)
         ==> sup s <= sup t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN
  MP_TAC(SPEC `t:real->bool` SUP) THEN ASM SET_TAC[]);;

let REAL_SUP_BOUNDS = prove
 (`!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= sup s /\ sup s <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` SUP) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let REAL_ABS_SUP_LE = prove
 (`!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(sup s) <= a`,
  REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_SUP_BOUNDS]);;

let REAL_SUP_ASCLOSE = prove
 (`!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(sup s - l) <= e`,
  SIMP_TAC[REAL_ARITH `abs(x - l):real <= e <=> l - e <= x /\ x <= l + e`] THEN
  REWRITE_TAC[REAL_SUP_BOUNDS]);;

let SUP_UNIQUE_FINITE = prove
 (`!s. FINITE s /\ ~(s = {})
       ==> (sup s = a <=> a IN s /\ !y. y IN s ==> y <= a)`,
   ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_LE_SUP_FINITE; REAL_SUP_LE_FINITE;
               NOT_INSERT_EMPTY; FINITE_INSERT; FINITE_EMPTY] THEN
   MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS; REAL_LE_ANTISYM]);;

let SUP_INSERT_FINITE = prove
 (`!x s. FINITE s ==> sup(x INSERT s) = if s = {} then x else max x (sup s)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SUP_UNIQUE_FINITE;  FINITE_INSERT; FINITE_EMPTY;
               NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING; REAL_LE_REFL] THEN
  REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SUP_FINITE; IN_INSERT; REAL_LE_REFL] THEN
  ASM_MESON_TAC[SUP_FINITE; REAL_LE_TOTAL; REAL_LE_TRANS]);;

let SUP_SING = prove
 (`!a. sup {a} = a`,
  SIMP_TAC[SUP_INSERT_FINITE; FINITE_EMPTY]);;

let SUP_INSERT_INSERT = prove
 (`!a b s. sup (b INSERT a INSERT s) = sup (max a b INSERT s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUP_EQ THEN
  X_GEN_TAC `c:real` THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
  ASM_CASES_TAC `!x:real. x IN s ==> x <= c` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let REAL_LE_SUP = prove
 (`!s a b y. y IN s /\ a <= y /\ (!x. x IN s ==> x <= b) ==> a <= sup s`,
  MESON_TAC[SUP; MEMBER_NOT_EMPTY; REAL_LE_TRANS]);;

let REAL_SUP_LE_EQ = prove
 (`!s y. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
         ==> (sup s <= y <=> !x. x IN s ==> x <= y)`,
  MESON_TAC[SUP; REAL_LE_TRANS]);;

let SUP_UNIQUE = prove
 (`!s b. (!c. (!x. x IN s ==> x <= c) <=> b <= c) ==> sup s = b`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM SUP_SING] THEN
  MATCH_MP_TAC SUP_EQ THEN ASM SET_TAC[]);;

let SUP_UNION = prove
 (`!s t. ~(s = {}) /\ ~(t = {}) /\
         (?b. !x. x IN s ==> x <= b) /\ (?c. !x. x IN t ==> x <= c)
         ==> sup(s UNION t) = max (sup s) (sup t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUP_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_UNION; REAL_MAX_LE] THEN
  ASM_MESON_TAC[SUP; REAL_LE_TRANS]);;

let ELEMENT_LE_SUP = prove
 (`!s a. (?b. !x. x IN s ==> x <= b) /\ a IN s ==> a <= sup s`,
  MESON_TAC[REAL_LE_SUP; REAL_LE_REFL]);;

let SUP_APPROACH = prove
 (`!s c. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b) /\ c < sup s
         ==> ?x. x IN s /\ c < x`,
  INTRO_TAC "!s c; npty bound lt" THEN
  REFUTE_THEN (LABEL_TAC "hp" o
    REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  REMOVE_THEN "lt" MP_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN
  HYP (MP_TAC o MATCH_MP SUP o end_itlist CONJ) "npty bound" [] THEN
  INTRO_TAC "_ sup" THEN REMOVE_THEN "sup" MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let REAL_MAX_SUP = prove
 (`!x y. max x y = sup {x,y}`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_SUP_LE_FINITE; REAL_LE_SUP_FINITE;
           FINITE_RULES; NOT_INSERT_EMPTY; REAL_MAX_LE; REAL_LE_MAX] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LE_TOTAL]);;

let inf = new_definition
  `inf s = @a:real. (!x. x IN s ==> a <= x) /\
                    !b. (!x. x IN s ==> b <= x) ==> b <= a`;;

let INF_EQ = prove
 (`!s t. (!a. (!x. x IN s ==> a <= x) <=> (!x. x IN t ==> a <= x))
         ==> inf s = inf t`,
  SIMP_TAC[inf]);;

let INF = prove
 (`!s. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
       ==> (!x. x IN s ==> inf s <= x) /\
           !b. (!x. x IN s ==> b <= x) ==> b <= inf s`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[inf] THEN
  CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
  EXISTS_TAC `--(sup (IMAGE (--) s))` THEN
  MP_TAC(SPEC `IMAGE (--) (s:real->bool)` SUP) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  ABBREV_TAC `a = sup (IMAGE (--) s)` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_IMAGE] THEN
  ASM_MESON_TAC[REAL_NEG_NEG; MEMBER_NOT_EMPTY; REAL_LE_NEG2]);;

let INF_FINITE_LEMMA = prove
 (`!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> b <= x`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_TRANS]);;

let INF_FINITE = prove
 (`!s. FINITE s /\ ~(s = {}) ==> (inf s) IN s /\ !x. x IN s ==> inf s <= x`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INF_FINITE_LEMMA) THEN
  ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TOTAL; INF]);;

let REAL_LE_INF_FINITE = prove
(`!s a. FINITE s /\ ~(s = {}) ==> (a <= inf s <=> !x. x IN s ==> a <= x)`,
  MESON_TAC[INF_FINITE; REAL_LE_TRANS]);;

let REAL_INF_LE_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (inf s <= a <=> ?x. x IN s /\ x <= a)`,
  MESON_TAC[INF_FINITE; REAL_LE_TRANS]);;

let REAL_LT_INF_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (a < inf s <=> !x. x IN s ==> a < x)`,
  MESON_TAC[INF_FINITE; REAL_LTE_TRANS]);;

let REAL_INF_LT_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (inf s < a <=> ?x. x IN s /\ x < a)`,
  MESON_TAC[INF_FINITE; REAL_LET_TRANS]);;

let REAL_INF_UNIQUE = prove
 (`!s b. (!x. x IN s ==> b <= x) /\
         (!b'. b < b' ==> ?x. x IN s /\ x < b')
         ==> inf s = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inf] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[REAL_NOT_LE; REAL_LE_ANTISYM]);;

let REAL_LE_INF = prove
 (`!b. ~(s = {}) /\ (!x. x IN s ==> b <= x) ==> b <= inf s`,
  MESON_TAC[INF]);;

let REAL_LE_INF_SUBSET = prove
 (`!s t. ~(t = {}) /\ t SUBSET s /\ (?b. !x. x IN s ==> b <= x)
         ==> inf s <= inf t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF THEN
  MP_TAC(SPEC `s:real->bool` INF) THEN ASM SET_TAC[]);;

let REAL_INF_BOUNDS = prove
 (`!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= inf s /\ inf s <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` INF) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let REAL_ABS_INF_LE = prove
 (`!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(inf s) <= a`,
  REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_INF_BOUNDS]);;

let REAL_INF_ASCLOSE = prove
 (`!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(inf s - l) <= e`,
  SIMP_TAC[REAL_ARITH `abs(x - l):real <= e <=> l - e <= x /\ x <= l + e`] THEN
  REWRITE_TAC[REAL_INF_BOUNDS]);;

let INF_UNIQUE_FINITE = prove
 (`!s. FINITE s /\ ~(s = {})
       ==> (inf s = a <=> a IN s /\ !y. y IN s ==> a <= y)`,
   ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_LE_INF_FINITE; REAL_INF_LE_FINITE;
               NOT_INSERT_EMPTY; FINITE_INSERT; FINITE_EMPTY] THEN
   MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS; REAL_LE_ANTISYM]);;

let INF_INSERT_FINITE = prove
 (`!x s. FINITE s ==> inf(x INSERT s) = if s = {} then x else min x (inf s)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INF_UNIQUE_FINITE;  FINITE_INSERT; FINITE_EMPTY;
               NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING; REAL_LE_REFL] THEN
  REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INF_FINITE; IN_INSERT; REAL_LE_REFL] THEN
  ASM_MESON_TAC[INF_FINITE; REAL_LE_TOTAL; REAL_LE_TRANS]);;

let INF_SING = prove
 (`!a. inf {a} = a`,
  SIMP_TAC[INF_INSERT_FINITE; FINITE_EMPTY]);;

let INF_INSERT_INSERT = prove
 (`!a b s. inf (b INSERT a INSERT s) = inf (min a b INSERT s)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INF_EQ THEN
  X_GEN_TAC `c:real` THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
  ASM_CASES_TAC `!x:real. x IN s ==> c <= x` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let REAL_SUP_EQ_INF = prove
 (`!s. ~(s = {}) /\ (?B. !x. x IN s ==> abs(x) <= B)
       ==> (sup s = inf s <=> ?a. s = {a})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `sup s` THEN MATCH_MP_TAC
     (SET_RULE `~(s = {}) /\ (!x. x IN s ==> x = a) ==> s = {a}`) THEN
    ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    ASM_MESON_TAC[SUP; REAL_ABS_BOUNDS; INF];
    STRIP_TAC THEN
    ASM_SIMP_TAC[SUP_INSERT_FINITE; INF_INSERT_FINITE; FINITE_EMPTY]]);;

let REAL_INF_LE = prove
 (`!s a b y. y IN s /\ y <= b /\ (!x. x IN s ==> a <= x) ==> inf s <= b`,
  MESON_TAC[INF; MEMBER_NOT_EMPTY; REAL_LE_TRANS]);;

let REAL_LE_INF_EQ = prove
 (`!s y. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
         ==> (y <= inf s <=> !x. x IN s ==> y <= x)`,
  MESON_TAC[INF; REAL_LE_TRANS]);;

let INF_UNIQUE = prove
 (`!s b. (!c. (!x. x IN s ==> c <= x) <=> c <= b) ==> inf s = b`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM INF_SING] THEN
  MATCH_MP_TAC INF_EQ THEN ASM SET_TAC[]);;

let INF_UNION = prove
 (`!s t. ~(s = {}) /\ ~(t = {}) /\
         (?b. !x. x IN s ==> b <= x) /\ (?c. !x. x IN t ==> c <= x)
         ==> inf(s UNION t) = min (inf s) (inf t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INF_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_UNION; REAL_LE_MIN] THEN
  ASM_MESON_TAC[INF; REAL_LE_TRANS]);;

let INF_LE_ELEMENT = prove
 (`!s a. (?b. !x. x IN s ==> b <= x) /\ a IN s ==> inf s <= a`,
  MESON_TAC[REAL_INF_LE; REAL_LE_REFL]);;

let INF_APPROACH = prove
 (`!s c. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x) /\ inf s < c
         ==> ?x. x IN s /\ x < c`,
  INTRO_TAC "!s c; npty bound lt" THEN
  REFUTE_THEN (LABEL_TAC "hp" o
    REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  REMOVE_THEN "lt" MP_TAC THEN REWRITE_TAC[REAL_NOT_LT] THEN
  HYP (MP_TAC o MATCH_MP INF o end_itlist CONJ) "npty bound" [] THEN
  INTRO_TAC "_ inf" THEN REMOVE_THEN "inf" MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let REAL_MIN_INF = prove
 (`!x y. min x y = inf {x,y}`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_INF_LE_FINITE; REAL_LE_INF_FINITE;
           FINITE_RULES; NOT_INSERT_EMPTY; REAL_MIN_LE; REAL_LE_MIN] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LE_TOTAL]);;

(* ------------------------------------------------------------------------- *)
(* Relational counterparts of sup and inf.                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_inf",(12,"right"));;
parse_as_infix ("has_sup",(12,"right"));;

let has_inf = new_definition
  `s has_inf b <=> (!c. (!x:real. x IN s ==> c <= x) <=> c <= b)`;;

let has_sup = new_definition
  `s has_sup b <=> (!c. (!x:real. x IN s ==> x <= c) <=> b <= c)`;;

let HAS_INF_LBOUND = prove
 (`!s b x. s has_inf b /\ x IN s ==> b <= x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_inf] THEN MESON_TAC[REAL_LE_REFL]);;

let HAS_SUP_UBOUND = prove
 (`!s b x. s has_sup b /\ x IN s ==> x <= b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_sup] THEN MESON_TAC[REAL_LE_REFL]);;

let HAS_INF_INF = prove
 (`!s l. s has_inf l <=>
         ~(s = {}) /\
         (?b. !x. x IN s ==> b <= x) /\
         inf s = l`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[has_inf] THEN
  EQ_TAC THEN STRIP_TAC THENL
  [CONJ_TAC THENL
   [REFUTE_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `l + &1:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
   MATCH_MP_TAC INF_UNIQUE THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN MP_TAC (SPEC `s:real->bool` INF) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   POP_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN EQ_TAC THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   TRANS_TAC REAL_LE_TRANS `l:real` THEN ASM_SIMP_TAC[]]);;

let HAS_SUP_SUP = prove
 (`!s l. s has_sup l <=>
         ~(s = {}) /\
         (?b. !x. x IN s ==> x <= b) /\
         sup s = l`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[has_sup] THEN
  EQ_TAC THEN STRIP_TAC THENL
  [CONJ_TAC THENL
   [REFUTE_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `l - &1:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
   MATCH_MP_TAC SUP_UNIQUE THEN ASM_REWRITE_TAC[];
   GEN_TAC THEN MP_TAC (SPEC `s:real->bool` SUP) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   POP_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN EQ_TAC THEN
   ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   TRANS_TAC REAL_LE_TRANS `l:real` THEN ASM_SIMP_TAC[]]);;

let INF_EXISTS = prove
 (`!s. (?l. s has_inf l) <=> ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)`,
  MESON_TAC[HAS_INF_INF]);;

let SUP_EXISTS = prove
 (`!s. (?l. s has_sup l) <=> ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)`,
  MESON_TAC[HAS_SUP_SUP]);;

let HAS_INF_APPROACH = prove
 (`!s l c. s has_inf l /\ l < c ==> ?x. x IN s /\ x < c`,
  REWRITE_TAC[HAS_INF_INF] THEN MESON_TAC[INF_APPROACH]);;

let HAS_SUP_APPROACH = prove
 (`!s l c. s has_sup l /\ c < l ==> ?x. x IN s /\ c < x`,
  REWRITE_TAC[HAS_SUP_SUP] THEN MESON_TAC[SUP_APPROACH]);;

let HAS_INF = prove
 (`!s l. s has_inf l <=>
         ~(s = {}) /\
         (!x. x IN s ==> l <= x) /\
         (!c. l < c ==> ?x. x IN s /\ x < c)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "hp" THEN CONJ_TAC THENL
   [HYP_TAC "hp" (REWRITE_RULE[HAS_INF_INF]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[HAS_INF_LBOUND]; ASM_MESON_TAC[HAS_INF_APPROACH]];
   ALL_TAC] THEN
  INTRO_TAC "ne bound approach" THEN ASM_REWRITE_TAC[has_inf] THEN
  GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "hp" THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN INTRO_TAC "lc" THEN
   REMOVE_THEN "approach" (MP_TAC o SPEC `(l + c) / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; INTRO_TAC "@x0. x0 +"] THEN
   USE_THEN "x0" (HYP_TAC "hp" o C MATCH_MP) THEN ASM_REAL_ARITH_TAC;
   INTRO_TAC "hp; !x; x" THEN TRANS_TAC REAL_LE_TRANS `l:real` THEN
   ASM_SIMP_TAC[]]);;

let HAS_SUP = prove
 (`!s l. s has_sup l <=>
         ~(s = {}) /\
         (!x. x IN s ==> x <= l) /\
         (!c. c < l ==> ?x. x IN s /\ c < x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "hp" THEN CONJ_TAC THENL
   [HYP_TAC "hp" (REWRITE_RULE[HAS_SUP_SUP]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[HAS_SUP_UBOUND]; ASM_MESON_TAC[HAS_SUP_APPROACH]];
   ALL_TAC] THEN
  INTRO_TAC "ne bound approach" THEN ASM_REWRITE_TAC[has_sup] THEN
  GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "hp" THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN INTRO_TAC "lc" THEN
   REMOVE_THEN "approach" (MP_TAC o SPEC `(l + c) / &2`) THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; INTRO_TAC "@x0. x0 +"] THEN
   USE_THEN "x0" (HYP_TAC "hp" o C MATCH_MP) THEN ASM_REAL_ARITH_TAC;
   INTRO_TAC "hp; !x; x" THEN TRANS_TAC REAL_LE_TRANS `l:real` THEN
   ASM_SIMP_TAC[]]);;

let HAS_INF_LE = prove
 (`!s t l m. s has_inf l /\ t has_inf m /\
             (!y. y IN t ==> ?x. x IN s /\ x <= y)
             ==> l <= m`,
  INTRO_TAC "!s t l m; l m le" THEN
  HYP_TAC "l: s l1 l2" (REWRITE_RULE[HAS_INF]) THEN
  HYP_TAC "m: t m1 m2" (REWRITE_RULE[HAS_INF]) THEN
  REFUTE_THEN (LABEL_TAC "lt" o REWRITE_RULE[REAL_NOT_LE]) THEN
  CLAIM_TAC "@c. c1 c2" `?c:real. m < c /\ c < l` THENL
  [EXISTS_TAC `(l + m) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  HYP_TAC "m2: +" (SPEC `c:real`) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  INTRO_TAC "!x; x xc" THEN
  CLAIM_TAC "@y. y yx" `?y:real. y IN s /\ y <= x` THENL
  [HYP MESON_TAC "le x" []; ALL_TAC] THEN
  HYP_TAC "l1: +" (SPEC `y:real`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_SUP_LE = prove
 (`!s t l m. s has_sup l /\ t has_sup m /\
             (!y. y IN t ==> ?x. x IN s /\ y <= x)
             ==> m <= l`,
  INTRO_TAC "!s t l m; l m le" THEN
  HYP_TAC "l: s l1 l2" (REWRITE_RULE[HAS_SUP]) THEN
  HYP_TAC "m: t m1 m2" (REWRITE_RULE[HAS_SUP]) THEN
  REFUTE_THEN (LABEL_TAC "lt" o REWRITE_RULE[REAL_NOT_LE]) THEN
  CLAIM_TAC "@c. c1 c2" `?c:real. l < c /\ c < m` THENL
  [EXISTS_TAC `(l + m) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  HYP_TAC "m2: +" (SPEC `c:real`) THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  INTRO_TAC "!x; x xc" THEN
  CLAIM_TAC "@y. y yx" `?y:real. y IN s /\ x <= y` THENL
  [HYP MESON_TAC "le x" []; ALL_TAC] THEN
  HYP_TAC "l1: +" (SPEC `y:real`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Inductive definition of sets, by reducing them to inductive relations.    *)
(* ------------------------------------------------------------------------- *)

let new_inductive_set =
  let const_of_var v = mk_mconst(name_of v,type_of v) in
  let comb_all =
    let rec f (n:int) (tm:term) : hol_type list -> term = function
      | [] -> tm
      | ty::tys ->
          let v = variant (variables tm) (mk_var("x"^string_of_int n,ty)) in
          f (n+1) (mk_comb(tm,v)) tys in
    fun tm -> let tys = fst (splitlist dest_fun_ty (type_of tm)) in
              f 0 tm tys in
  let mk_eqin = REWR_CONV (GSYM IN) o comb_all in
  let transf conv = rhs o concl o conv in
  let remove_in_conv ptm : conv =
    let rconv = REWR_CONV(SYM(mk_eqin ptm)) in
    fun tm -> let htm = fst(strip_comb(snd(dest_binary "IN" tm))) in
              if htm = ptm then rconv tm else fail() in
  let remove_in_transf =
    transf o ONCE_DEPTH_CONV o FIRST_CONV o map remove_in_conv in
  let rule_head tm =
    let tm = snd(strip_forall tm) in
    let tm = snd(splitlist(dest_binop `(==>)`) tm) in
    let tm = snd(dest_binary "IN" tm) in
    fst(strip_comb tm) in
  let find_pvars = setify o map rule_head o binops `(/\)` in
  fun tm ->
    let pvars = find_pvars tm in
    let dtm = remove_in_transf pvars tm in
    let th_rules, th_induct, th_cases = new_inductive_definition dtm in
    let insert_in_rule = REWRITE_RULE(map (mk_eqin o const_of_var) pvars) in
    insert_in_rule th_rules,
    insert_in_rule th_induct,
    insert_in_rule th_cases;;
