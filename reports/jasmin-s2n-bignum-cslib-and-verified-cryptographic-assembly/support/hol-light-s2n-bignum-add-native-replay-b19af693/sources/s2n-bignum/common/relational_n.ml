(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*     Hoare Logic with the number of small steps explicitly annotated.      *)
(*                                                                           *)
(*                         Abdalrhman M Mohamed (2024)                       *)
(*                                Juneyoung Lee                              *)
(* ========================================================================= *)

needs "common/components.ml";;

(* ------------------------------------------------------------------------- *)
(* A definition of steps and its properties.                                 *)
(* ------------------------------------------------------------------------- *)

let steps_RULES,steps_INDUCT,steps_CASES = new_inductive_definition
  `(!s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (!s s'' n. (?s'. step s s' /\ steps step n s' s'') ==> steps step (n+1) s s'')`;;

let STEPS_TRIVIAL = prove(
  `!(s:S) s' step. steps step 0 s s' <=> s = s'`,
  ONCE_REWRITE_TAC[steps_CASES] THEN REWRITE_TAC[ARITH_RULE`~(0=n+1)`] THEN MESON_TAC[]);;

(* Trivial, but to help pattern matcher... *)
let STEPS_SYM = prove(
  `!(step:S->S->bool) m n s s'. steps step (m+n) s s' <=> steps step (n+m) s s'`,
  REWRITE_TAC[ADD_SYM]);;

let STEPS_STEP_LEFT_RIGHT = prove(
  `!(step:S->S->bool) n s s'.
      (?s''. step s s'' /\ steps step n s'' s') <=> (?s''. steps step n s s'' /\ step s'' s')`,
  GEN_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
    MESON_TAC[STEPS_TRIVIAL];

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE`SUC n=1+n`] THEN
    ONCE_REWRITE_TAC [steps_CASES] THEN
    REWRITE_TAC[ARITH_RULE`~(1+n = 0)`] THEN
    SUBGOAL_THEN `!k (P:num->bool). (?n'. 1+k = n'+1 /\ P n') <=> P k`
        (fun th -> REWRITE_TAC[th]) THENL [
      REPEAT GEN_TAC THEN EQ_TAC THENL [
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `k:num=n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[ADD_SYM];

        REPEAT STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[ADD_SYM]
      ];
      ALL_TAC
    ] THEN
    let tt1 = `!P Q. (?a. P a /\ (?b. Q a b)) <=> (?a b. P a /\ Q a b)` in
    let tt2 = `!P Q. (?a. (?b. Q a b) /\ P a) <=> (?a b. Q a b /\ P a)` in
    REWRITE_TAC(map ITAUT [tt1;tt2]) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    let tt3 = `!P Q. (?b a. P a /\ Q a b) <=> (?a. P a /\ (?b. Q a b))` in
    REWRITE_TAC[ITAUT tt3] THEN
    ASM_MESON_TAC[]
  ]);;

let STEPS_ADD =
  let lemma = prove(`!k (P:num->bool). (?n'. k+1 = n'+1 /\ P n') <=> P k`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `k:num=n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];

    REPEAT STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]
  ]) in
  prove(
    `!(step:S->S->bool) m n s s'.
    steps step (m+n) s s' <=> ?s''. steps step m s s'' /\ steps step n s'' s'`,
    REPEAT_N 2 GEN_TAC THEN
    MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
      REWRITE_TAC[ADD_0;STEPS_TRIVIAL] THEN MESON_TAC[];

      REWRITE_TAC[ARITH_RULE`m + SUC n = (m + n) + 1`;ARITH_RULE`SUC n = n + 1`] THEN
      REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
      ASM_REWRITE_TAC[ARITH_RULE`!m n. ~((m+n)+1 = 0)`;lemma] THEN
      SUBGOAL_THEN `!(s'':S).
          (steps (step:S->S->bool) (n + 1) s'' s' <=>
          ?s'''. step s'' s''' /\ steps step n s''' s')`
          (fun th -> REWRITE_TAC[th]) THENL [
        REPEAT STRIP_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
        REWRITE_TAC[ARITH_RULE`!n. ~(n+1=0)`;lemma];
        ALL_TAC
      ] THEN
      REWRITE_TAC[CONJ_ASSOC;
        ITAUT `!P Q. (?a. P a /\ (?b. Q a b)) <=> (?a b. P a /\ Q a b)`;
        ITAUT `!P Q. (?a b. P a b /\ Q b) <=> (?b. (?a. P a b) /\ Q b)`] THEN
      REWRITE_TAC[STEPS_STEP_LEFT_RIGHT]
    ]);;

(* Again trivial, but for pattern matching... *)
let STEPS_STEP = prove(
  `!n (s:S) s' step.
     steps step (1+n) s s' <=> ?s''. step s s'' /\ steps step n s'' s'`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
  REWRITE_TAC[ARITH_RULE`~(1+n=0)`] THEN
  EQ_TAC THENL [
    STRIP_TAC THEN
    SUBGOAL_THEN `n:num = n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];

    STRIP_TAC THEN
    EXISTS_TAC `n:num` THEN
    REWRITE_TAC[ADD_SYM] THEN ASM_MESON_TAC[]]);;

let STEPS_ONE = prove(
  `!(s:S) s' step. steps step 1 s s' <=> step s s'`,
  METIS_TAC[ARITH_RULE`1=1+0`;STEPS_STEP;STEPS_TRIVIAL]);;

let STEPS_NOSTUCK = prove(
  `!(step:S->S->bool) (n:num) (s:S).
    (!s' n'. (n' < n /\ steps step n' s s') ==> ?s''. step s' s'')
    ==> ?s'. steps step n s s'`,
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
    MESON_TAC[STEPS_TRIVIAL];

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE`SUC n=1+n`;STEPS_STEP;STEPS_STEP_LEFT_RIGHT] THEN
    SUBGOAL_THEN
        `(!(s':S) n'. (n' < n /\ steps (step:S->S->bool) n' s s' ==> (?s''. step s' s''))) /\
        (!(s':S). steps (step:S->S->bool) n s s' ==> (?s''. step s' s''))`
        MP_TAC THENL [
      CONJ_TAC THENL [
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC`n':num` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC`n:num` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th -> let th1,th2 = CONJ_PAIR th in
      LABEL_TAC "H1" th1 THEN LABEL_TAC "H2" th2) THEN
    SUBGOAL_THEN `?(s':S). steps step n s s'` MP_TAC THENL [
      ASM_MESON_TAC[]; ALL_TAC
    ] THEN STRIP_TAC THEN
    ASM_MESON_TAC[]
  ]);;


(* ------------------------------------------------------------------------- *)
(* A definition of eventually with # steps.                                  *)
(* ------------------------------------------------------------------------- *)

let eventually_n = new_definition
  `eventually_n (step:S->S->bool) (n:num) (P:S->bool) s <=>
   ((!s'. steps step n s s' ==> P s') /\
    // There isn't a 'stuck' state at the end of a trace shorter than n
    (!s' n'. (n' < n /\ steps step n' s s') ==> ?s''. step s' s''))`;;


(* ------------------------------------------------------------------------- *)
(* Properties of eventually_n                                                *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_N_TRIVIAL = prove(
  `!(step:S->S->bool) s (P:S->bool). eventually_n step 0 P s <=> P s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually_n;ARITH_RULE`!x. ~(x<0)`] THEN
  MESON_TAC[STEPS_TRIVIAL]);;

let EVENTUALLY_N_CONJ = prove(
  `!(step:S->S->bool) (P:S->bool) (Q:S->bool) n s.
    eventually_n step n P s /\ eventually_n step n Q s ==>
    eventually_n step n (\s. P s /\ Q s) s`,
  REWRITE_TAC[eventually_n] THEN MESON_TAC[]);;

let EVENTUALLY_N_NESTED = prove(
  `!(step:S->S->bool) (s0:S).
    eventually_n step n (\s. eventually_n step n (\s2. P s s2) s0) s0 ==>
    eventually_n step n (\s. P s s) s0`,
  REWRITE_TAC[eventually_n] THEN
  REPEAT STRIP_TAC THENL
  replicate (ASM_MESON_TAC[]) 2);;

let EVENTUALLY_N_COMPOSE = prove(
  `forall (step:S->S->bool) (s0:S) n1 n2 P Q.
    eventually_n step n1 P s0 /\
    (forall s. P s ==> eventually_n step n2 Q s)
    ==> eventually_n step (n1+n2) Q s0`,
  REWRITE_TAC[eventually_n] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "(H0 H1) H2" THEN REPEAT STRIP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[STEPS_ADD] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];

    ASM_CASES_TAC `(n':num) < n1` THENL [
      ASM_MESON_TAC[];

      SUBGOAL_THEN `(n':num) = n1 + (n' - n1)` ASSUME_TAC THENL [
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      ABBREV_TAC `(k:num) = n' - n1` THEN
      UNDISCH_THEN `(n':num) = n1 + k` SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(k:num) < n2` ASSUME_TAC THENL [SIMPLE_ARITH_TAC;ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[STEPS_ADD]) THEN ASM_MESON_TAC[]
    ]
  ]);;

let EVENTUALLY_N_STEP =
  prove(
    `!(step:S->S->bool) (P:S->bool) n s.
      eventually_n step (1+n) P s <=>
      ((?s'. step s s') /\
       (!s'. step s s' ==> eventually_n step n P s'))`,
    REWRITE_TAC[eventually_n;STEPS_ADD;STEPS_ONE] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THENL [
      REPEAT STRIP_TAC THENL [
        FIRST_X_ASSUM (fun th -> MP_TAC (SPECL [`s:S`;`0`] th)) THEN
        MESON_TAC[ARITH_RULE`0<1+n`; STEPS_TRIVIAL];

        ASM_MESON_TAC[];

        FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `1+n':num` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_MESON_TAC[STEPS_STEP]
      ];

      REPEAT STRIP_TAC THENL [
        ASM_MESON_TAC[];

        MP_TAC (SPEC `n':num` num_CASES) THEN
        STRIP_TAC THENL [
          ASM_MESON_TAC[STEPS_TRIVIAL];
          UNDISCH_TAC `n' = SUC n''` THEN REWRITE_TAC[ARITH_RULE`!k. SUC k = 1+k`] THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC (REWRITE_RULE[STEPS_ADD;STEPS_ONE]) THEN
          SUBGOAL_THEN `n'':num < n` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
          ASM_MESON_TAC[]
        ]
      ]
    ]);;

let EVENTUALLY_N_STEPS =
  prove(
    `!(step:S->S->bool) P (n:num) s. eventually_n step n P s ==> ?s'. steps step n s s'`,
    MESON_TAC[eventually_n;STEPS_NOSTUCK]);;

let EVENTUALLY_N_MONO =
  prove(
    `!(step:S->S->bool) (P:S->bool) (Q:S->bool) n s.
      (!s'. P s' ==> Q s') ==>
      eventually_n step n P s ==> eventually_n step n Q s`,
    REWRITE_TAC[eventually_n] THEN MESON_TAC[]);;

let EVENTUALLY_N_IMP_EVENTUALLY_N = prove
 (`!(step:S->S->bool) (P:S->bool) (Q:S->bool) n2.
    (!s n1. eventually_n step n1 P s ==> eventually_n step (n1 + n2) Q s) <=>
    (!s. P s ==> eventually_n step n2 Q s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    MESON_TAC[EVENTUALLY_N_TRIVIAL; ARITH_RULE `0 + n = n`];
    REWRITE_TAC [eventually_n] THEN
    REPEAT STRIP_TAC THENL [
      ASM_MESON_TAC[STEPS_ADD];
      DISJ_CASES_TAC (ARITH_RULE `n':num < n1 \/ n' >= n1`) THENL [
        ASM_MESON_TAC[STEPS_ADD];
        FIRST_X_ASSUM (fun th -> CHOOSE_THEN ASSUME_TAC (REWRITE_RULE [GE; LE_EXISTS] th)) THEN
        ASM_MESON_TAC [LT_ADD_LCANCEL; STEPS_ADD]]]]);;

let EVENTUALLY_N_EVENTUALLY =
  prove(
    `!(step:S->S->bool) (P:S->bool) n s.
      eventually_n step n P s ==> eventually step P s`,
    REPEAT_N 2 GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
      REWRITE_TAC[eventually_n; STEPS_TRIVIAL] THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN MESON_TAC[];

      REWRITE_TAC[ARITH_RULE`SUC n=1+n`] THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> MP_TAC (GEN_REWRITE_RULE I [EVENTUALLY_N_STEP] th)) THEN
      STRIP_TAC THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN
      DISJ2_TAC THEN
      UNDISCH_TAC `eventually_n (step:S->S->bool) (1+n) P s` THEN
      REWRITE_TAC[eventually_n;STEPS_ADD;STEPS_ONE] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP STEPS_NOSTUCK th)) THEN
      STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[STEPS_ADD;STEPS_ONE]) THEN
      ASM_MESON_TAC[eventually_n]
    ]);;

let EVENTUALLY_N_P_INOUT = prove(
  `!(step:S->S->bool) P Q n s0.
    P /\ eventually_n step n (\s. Q s s0) s0 <=>
    eventually_n step n (\s. P /\ Q s s0) s0`,
  REWRITE_TAC[eventually_n] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
  replicate (MESON_TAC[STEPS_NOSTUCK]) 2);;

(* Inverse direction of this lemma (EVENTUALLY_N_EVENTUALLY_STEPS) is not true.
   Consider three states s0, s1, s2 that forms a triangle:
   (1) s0 -> s1 -> s2
   (2) s0 -> s2
   If P(s2) is true and P(s1) is false, then
   `eventually step (\s'. steps step 1 s s' /\ P s') s0` is true because
   `steps step 1 s0 s0` holds.
   However, `eventually_n step 1 P s` is false because P(s1) is false. *)
let EVENTUALLY_N_EVENTUALLY_STEPS = prove(
  `!(step:S->S->bool) P n s.
    eventually_n step n P s ==> eventually step (\s'. steps step n s s' /\ P s') s`,

  REPEAT_N 2 GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[eventually_n] THEN
    ONCE_REWRITE_TAC[eventually_CASES] THEN
    REWRITE_TAC[STEPS_TRIVIAL;ARITH_RULE`!n. ~(n<0)`] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[];

    REWRITE_TAC[ARITH_RULE`SUC n = 1 + n`] THEN
    GEN_TAC THEN
    DISCH_THEN (fun th -> MP_TAC (GEN_REWRITE_RULE I [EVENTUALLY_N_STEP] th)) THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[STEPS_ADD;STEPS_ONE] THEN GEN_TAC THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (fun evth -> ASSUME_TAC (MATCH_MP evth (ASSUME `(step:S->S->bool) s s''`))) THEN
    REWRITE_TAC[ITAUT`((?(x:S). P x) /\ Q) <=> (?x. P x /\ Q)`] THEN
    MATCH_MP_TAC EVENTUALLY_EXISTS THEN
    REWRITE_TAC[GSYM CONJ_ASSOC;GSYM EVENTUALLY_P_INOUT] THEN
    EXISTS_TAC `s'':S` THEN ASM_MESON_TAC[]
  ]);;

(* If the language has deterministic small-step semantics, eventually can be
   used to prove eventually_n. *)
let EVENTUALLY_EVENTUALLY_N = prove(
  `!(step:S->S->bool). (!x y z. step x y /\ step x z ==> y = z) ==>
   !P s. eventually step P s ==> ?n. eventually_n step n P s`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC eventually_INDUCT THEN
  CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[EVENTUALLY_N_TRIVIAL];
    INTRO_TAC "!s; (@s'. HS) IH" THEN
    REMOVE_THEN "IH" (fun ih -> USE_THEN "HS" (CHOOSE_TAC o MATCH_MP ih)) THEN
    EXISTS_TAC `1 + n` THEN
    ASM_MESON_TAC[EVENTUALLY_N_STEP]]);;

(* ------------------------------------------------------------------------- *)
(* Definition and properties of ensures_n.                                   *)
(* ------------------------------------------------------------------------- *)

(* eventually_n version of ensures. *)
let ensures_n = new_definition
  `ensures_n (step:S->S->bool) (precond:S->bool) (postcond:S->bool) (frame:S->S->bool)
             (step_calc:S->num) <=>
    !s. precond s ==> eventually_n step (step_calc s) (\s'. postcond s' /\ frame s s') s`;;

let SEQ_PAIR_SPLIT = prove(
  `!(P:A->A->bool) (Q:A->A->bool) (R:A->A->bool) (S:A->A->bool) p1 p2 p1' p2'.
    ((\(s,s2) (s',s2'). P s s' /\ Q s2 s2') ,, (\(s,s2) (s',s2'). R s s' /\ S s2 s2'))
    (p1,p2) (p1',p2')
    <=>
    ((P ,, R) p1 p1' /\ (Q ,, S) p2 p2')`,
  REWRITE_TAC[seq;EXISTS_PAIR_THM] THEN MESON_TAC[]);;

let ENSURES_N_ENSURES = prove(
  `!(step:S->S->bool) P Q C f_n.
      ensures_n step P Q C f_n ==> ensures step P Q C`,
  REWRITE_TAC[ensures_n;ensures] THEN ASM_MESON_TAC[EVENTUALLY_N_EVENTUALLY]);;

let NSUM_REFLECT' = prove(`!x n. nsum (0..n) (\i. x(n - i)) = nsum (0..n) x`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC (SPECL [`x:num->num`; `0`; `n:num`] NSUM_REFLECT) THEN
  REWRITE_TAC[ARITH_RULE `~(n < 0) /\ (n - 0 = n)`]);;

let ENSURES_N_TRIVIAL = prove(
  `!step q f fn. ensures_n step (\x. F) q f fn`,
  REWRITE_TAC[ensures_n]);;

let ENSURES_N_ALREADY = prove(
  `!(step:A->A->bool) P Q C.
    (!s. P s ==> Q s) /\ (=) subsumed C ==> ensures_n step P Q C (\s. 0)`,
  REWRITE_TAC[ensures_n; subsumed; EVENTUALLY_N_TRIVIAL] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]);;

(* If the language has deterministic small-step semantics, ensures can be
   used to prove ensures_n. *)
let ENSURES_ENSURES_N = prove(
  `!(step:S->S->bool) P Q C. (!x y z. step x y /\ step x z ==> y = z) ==>
    ensures step P Q C ==> ?fn. ensures_n step P Q C fn`,
  REWRITE_TAC[ensures; ensures_n; GSYM SKOLEM_THM_GEN] THEN
  SEQ_IMP_REWRITE_TAC[EVENTUALLY_EVENTUALLY_N] THEN
  MESON_TAC[]);;

let ENSURES_N_CONJ = prove(
  `forall (step:S->S->bool) P Q C f_n Q'.
      ensures_n step P Q C f_n /\ ensures_n step P Q' C f_n
      ==> ensures_n step P (\s. Q s /\ Q' s) C f_n`,
  REWRITE_TAC[ensures_n] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th -> REPEAT (FIRST_X_ASSUM (fun th' -> ASSUME_TAC (MATCH_MP th' th)))) THEN
  POP_ASSUM (fun th -> POP_ASSUM (fun th' -> ASSUME_TAC (MATCH_MP EVENTUALLY_N_CONJ (CONJ th th')))) THEN
  MATCH_MP_TAC (REWRITE_RULE[GSYM IMP_CONJ] EVENTUALLY_N_MONO) THEN
  ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Classic precondition strengthening and postcondition weakening.           *)
(* Implement also (essentially trivial) tactics to apply it.                 *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_PRECONDITION_THM_GEN = prove
 (`!P P' C C' Q fn.
        (!x. P' x ==> P x) /\
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q C' fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_PRECONDITION_THM = prove
 (`!P P' C Q fn.
        (!x. P' x ==> P x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q C fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let ENSURES_N_POSTCONDITION_THM_GEN = prove
 (`!P C C' Q Q' fn.
        (!x. Q x ==> Q' x) /\
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q' C' fn`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_POSTCONDITION_THM = prove
 (`!P C Q Q' fn.
        (!x. Q x ==> Q' x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q' C fn`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_PREPOSTCONDITION_THM = prove
 (`!P P' C Q Q' fn.
        (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q' C fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The analogous monotonicity result for the frame.                          *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_FRAME_MONO = prove
 (`!P Q C C' fn.
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q C' fn`,
   REPEAT GEN_TAC THEN
   REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
   MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
   ASM_SIMP_TAC[]);;

let ENSURES_N_FRAME_SUBSUMED = prove
 (`!(P:S->bool) Q C C' fn.
        C subsumed C' /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q C' fn`,
   REWRITE_TAC[subsumed; ENSURES_N_FRAME_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Classic Hoare sequencing / Transitivity rule.                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_TRANS = prove(
  `!step (P:S->bool) (Q:S->bool) (R:S->bool) C1 C2 n1 n2.
    ensures_n step P Q C1 (\s. n1) /\ ensures_n step Q R C2 (\s. n2)
    ==> ensures_n step P R (C1 ,, C2) (\s. n1 + n2)`,
  REWRITE_TAC [ensures_n; eventually_n] THEN
  REPEAT_N 11 STRIP_TAC THEN
  CONJ_TAC THENL [
    ASM_MESON_TAC [STEPS_ADD; seq];
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (ARITH_RULE `n':num < n1 \/ n' >= n1`) THENL [
      ASM_MESON_TAC [];
      FIRST_X_ASSUM (fun th -> CHOOSE_THEN ASSUME_TAC (REWRITE_RULE [GE; LE_EXISTS] th)) THEN
      ASM_MESON_TAC [LT_ADD_LCANCEL; STEPS_ADD]]]);;

let ENSURES_N_TRANS_SIMPLE = prove(
  `!step (P:S->bool) (Q:S->bool) (R:S->bool) C n1 n2.
    C ,, C = C /\
    ensures_n step P Q C (\s. n1) /\ ensures_n step Q R C (\s. n2)
    ==> ensures_n step P R C (\s. n1 + n2)`,
  MESON_TAC[ENSURES_N_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* A way of using a lemma for a subroutine or subcomponent.                  *)
(* Tactic supports the basic templating and leaves two user subgoals.        *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_SUBLEMMA_THM = prove
  (`!t (P:A->bool) Q R fn.
         (!s. P s ==> P' s) /\
         R' subsumed R /\
         (!s s'. P s /\ Q' s' /\ R' s s' ==> Q s')
         ==> ensures_n t P' Q' R' fn ==> ensures_n t P Q R fn`,
   REPEAT GEN_TAC THEN REWRITE_TAC[subsumed] THEN STRIP_TAC THEN
   REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN
   X_GEN_TAC `s:A` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
   ASM_SIMP_TAC[] THEN
   MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]
         EVENTUALLY_N_MONO) THEN
   ASM_MESON_TAC[]);;
  
let ENSURES_N_CONSTANT_PRECONDITION = prove
 (`!step p (q:A->bool) r n.
        ensures_n step (\s. p) q r n <=> p ==> ensures_n step (\s. T) q r n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[ENSURES_N_TRIVIAL]);;

let ENSURES_N_CONSTANT_PRECONDITION_CONJUNCTS = prove
 (`(!step p p' (q:A->bool) r n.
        ensures_n step (\s. p /\ p' s) q r n <=>
        p ==> ensures_n step (\s. p' s) q r n) /\
   (!step p p' (q:A->bool) r n.
        ensures_n step (\s. p' s /\ p) q r n <=>
        p ==> ensures_n step (\s. p' s) q r n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p:bool` THEN
  ASM_REWRITE_TAC[ENSURES_N_TRIVIAL]);;